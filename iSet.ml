type range = Range of int * int
type amount = Double of int * int
type t =
	| Node of t * range * t * int * Int64.t
	| Empty

let comp range_one range_two = 
	let Range(a, b) = range_one
	in let Range(c, d) = range_two
	in
		if b < c then -1
		else if a > d then 1
		else 0

let height = function
	| Node (_, _, _, h, _) -> h
	| Empty -> 0

let get_count = function
	| Node (_, _, _, _, count) -> count
	| Empty -> Int64.zero

let get_range_sum a b = 
	let q = Int64.add (Int64.of_int b) Int64.one
	in Int64.sub q (Int64.of_int a)

let make l k r =
	let Range(a, b) = k
	in Node (
	l,
	k,
	r,
	max (height l) (height r) + 1,
	Int64.add (get_range_sum a b) (Int64.add (get_count l) (get_count r))
)

let bal l k r =
	let hl = height l in
	let hr = height r in
	if hl > hr + 2 then
	match l with
	| Node (ll, lk, lr, _, _) ->
		if height ll >= height lr then make ll lk (make lr k r)
		else
		(match lr with
			| Node (lrl, lrk, lrr, _, _) ->
				make (make ll lk lrl) lrk (make lrr k r)
			| Empty -> assert false)
	| Empty -> assert false
	else if hr > hl + 2 then
	match r with
	| Node (rl, rk, rr, _, _) ->
		if height rr >= height rl then make (make l k rl) rk rr
		else
		(match rl with
			| Node (rll, rlk, rlr, _, _) ->
				make (make l k rll) rlk (make rlr rk rr)
			| Empty -> assert false)
	| Empty -> assert false
	else make l k r

let rec min_elt = function
	| Node (Empty, k, _, _, _) -> k
	| Node (l, _, _, _, _) -> min_elt l
	| Empty -> raise Not_found

let rec remove_min_elt = function
	| Node (Empty, _, r, _, _) -> r
	| Node (l, k, r, _, _) -> bal (remove_min_elt l) k r
	| Empty -> invalid_arg "PSet.remove_min_elt"

let merge t1 t2 =
	match t1, t2 with
	| Empty, _ -> t2
	| _, Empty -> t1
	| _ ->
		let k = min_elt t2 in
		bal t1 k (remove_min_elt t2)

let empty = Empty

let is_empty x = x = Empty

let rec add_one x = function
	| Node (l, k, r, h, num) ->
		let c = comp x k in
			if c = 0 then
				Node (l, x, r, h, num)
			else if c < 0 then
				let nl = add_one x l in bal nl k r
			else
				let nr = add_one x r in bal l k nr
	| Empty ->
		let Range(a, b) = x
		in Node (Empty, x, Empty, 1, get_range_sum a b)

let rec join l v r =
	match (l, r) with
	| (Empty, _) -> add_one v r
	| (_, Empty) -> add_one v l
	| (Node(ll, lv, lr, lh, _), Node(rl, rv, rr, rh, _)) ->
		if lh > rh + 2 then bal ll lv (join lr v r) else
		if rh > lh + 2 then bal (join l v rl) rv rr else
			make l v r


let old_split x set =
	let rec loop x = function
	| Empty ->
		(Empty, false, Empty)
	| Node (l, v, r, _, _) ->
		let c = comp x v in
			if c = 0 then
				(l, true, r)
			else if c < 0 then
				let (ll, pres, rl) = loop x l in (ll, pres, join rl v r)
			else
				let (lr, pres, rr) = loop x r
				in (join l v lr, pres, rr)
				in
					let setl, pres, setr = loop x set
					in setl, pres, setr

let rec find x = function
	| Empty -> Range(1, -1)
	| Node(left, value, right, _, _) ->
		let c = comp x value
		in
			if c = 0 then value
			else if c < 0 then find x left
			else find x right

let add (a, b) set = 
	let (res_left, _, _) =
		if a = min_int then empty, false, empty else old_split (Range(a - 1, a - 1)) set
	in let (_, _, res_right) = 
		if b = max_int then empty, false, empty else old_split (Range(b + 1, b + 1)) set
	in let Range(low, low_check) = find (Range(a - 1, a - 1)) set
	in let Range(high_check, high) = find (Range(b + 1, b + 1)) set
	in let low = if a = min_int || low > low_check then a else low
	in let high = if b = max_int || high < high_check then b else high
	in let new_set = merge res_left res_right
	in 
		add_one (Range(low, high)) new_set

let add_conditional (a, b) set = 
	if a > b then set
	else add (a, b) set

let remove (a, b) set = 
	let set = add (a, b) set
	in let Range(curr_low, curr_high) = find (Range(a, b)) set
	in let (left, _, right) = old_split (Range(a, b)) set
	in let set = merge left right
	in let set =
		if a = min_int then set else add_conditional (curr_low, a - 1) set
	in 
		if b = max_int then set else add_conditional (b + 1, curr_high) set

let mem x set =
	let rec loop = function
		| Node (l, k, r, _, _) ->
			let c = comp (Range(x, x)) k
			in c = 0 || loop (if c < 0 then l else r)
		| Empty -> false
	in loop set

let split x set = 
	let pres = mem x set
	in let set = remove (x, x) set
	in let left, _, right = old_split (Range(x, x)) set
	in left, pres, right
;;

let iter f set =
	let rec loop = function
		| Empty -> ()
		| Node (l, Range(a, b), r, _, _) ->
			loop l;
			f (a, b);
			loop r
	in loop set

let fold f set acc =
	let rec loop acc = function
		| Empty -> acc
		| Node (l, Range(a, b), r, _, _) ->
			loop (f (a, b) (loop acc l)) r
	in loop acc set

let elements set = 
	let rec loop acc = function
		| Empty -> acc
		| Node(l, Range(a, b), r, _, _) ->
			loop ((a, b) :: loop acc r) l
	in loop [] set

let below x set = 
	let rec loop acc = function
		| Empty -> acc
		| Node(left, Range(a, b), right, _, number) ->
			let c = comp (Range(a, b)) (Range(x, x))
			in
				if c = 0 then 
					Int64.add acc (Int64.add (get_range_sum a x) (get_count left))
				else if c < 0 then
					let acc = Int64.add acc (get_count left)
					in let acc = Int64.add acc (get_range_sum a b)
					in loop acc right
				else loop acc left
	in let res = loop Int64.zero set
	in
		if compare res Int64.zero < 0 then max_int
		else if compare res (Int64.of_int max_int) >= 0 then max_int
		else Int64.to_int res
