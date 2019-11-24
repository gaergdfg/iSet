type range = Range of int * int
type amount = Double of int * int
type t =
	| Node of t * range * t * int * amount
	| Empty

let comp range_one range_two = 
	let Range(a, b) = range_one
	in let Range(c, d) = range_two
	in
		if b < c then -1
		else if a > d then 1
		else 0



let print = Printf.printf "%d "



let height = function
	| Node (_, _, _, h, _) -> h
	| Empty -> 0

let get_number_set = function
	| Node(_, _, _, _, number) -> number
	| Empty -> Double(0, 0)

let add_number number_a x = 
	let Double(a, b) = number_a
	in 
		(* print a; print b; print_string "\n"; *)
		if a > min_int then Double(min_int, x - (max_int - a))
		else Double(a + x, b)
let add_two_numbers number_a number_b = 
	let Double(x, y) = number_b
	in
		let sum = add_number number_a x
		in add_number sum y

let sub_numbers number_a x =
	let Double(a, b) = number_a
	in
		if b > 0 then
			let new_x = max 0 (b - x)
			in Double(a - new_x, b - x)
		else
			Double(a - x, b)
let get_number_range curr_range = 
	let Range(a, b) = curr_range
	in
		let sum1 = add_number (Double(0, 0)) b
		in let sum2 = sub_numbers sum1 a
		in add_number sum2 1

let make l k r =
	let sum_lr = add_two_numbers (get_number_set l) (get_number_set r)
	in let sum = add_two_numbers sum_lr (get_number_range k)
	in Node (l, k, r, max (height l) (height r) + 1, sum)

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
	| Empty -> Node (Empty, x, Empty, 1, get_number_range x)

let rec join l v r =
	match (l, r) with
	| (Empty, _) -> add_one v r
	| (_, Empty) -> add_one v l
	| (Node(ll, lv, lr, lh, _), Node(rl, rv, rr, rh, _)) ->
		if lh > rh + 2 then bal ll lv (join lr v r) else
		if rh > lh + 2 then bal (join l v rl) rv rr else
			make l v r


let real_split x set =
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

let split a = real_split (Range(a, a))

let rec find x = function
	| Empty -> Range(1, -1)
	| Node(left, value, right, _, _) ->
		let c = comp x value
		in
			if c = 0 then value
			else if c < 0 then find x left
			else find x right

let add (a, b) set = 
	let (res_left, _, _) = real_split (Range(a - 1, a - 1)) set
	in let (_, _, res_right) = real_split (Range(b + 1, b + 1)) set
	in let Range(low, low_check) = find (Range(a - 1, a - 1)) set
	in let Range(high_check, high) = find (Range(b + 1, b + 1)) set
	in let low = if low > low_check then a else low
	in let high = if high < high_check then b else high
	in let new_set = merge res_left res_right
	in add_one (Range(low, high)) new_set

let add_conditional (a, b) set = 
	if a > b then set
	else add (a, b) set

let remove (a, b) set = 
	let set = add (a, b) set
	in let Range(curr_low, curr_high) = find (Range(a, b)) set
	in let (left, _, right) = real_split (Range(a, b)) set
	in let set = merge left right
	in let set = add_conditional (curr_low, a - 1) set
	in add_conditional (b + 1, curr_high) set

let mem x set =
	let rec loop = function
		| Node (l, k, r, _, _) ->
			let c = comp (Range(x, x)) k		(* zmienione z x na Range(x, x) *)
			in c = 0 || loop (if c < 0 then l else r)
		| Empty -> false
	in loop set

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
				(* print a; print b; print x; print_string " - "; print c; print_string "\n"; *)
				if c = 0 then
					add_two_numbers
						(add_number acc (x - a + 1))
						(get_number_set left)
				else if c < 0 then
					let acc = add_two_numbers acc (get_number_set left)
					in let acc = add_number acc (b - a + 1)
					in loop acc right
				else loop acc left
	in let Double(a, _) = loop (Double(0, 0)) set
	in a




(*  ---------------------------------------------------------------------------  *)

let s = add (-min_int, max_int) empty;;
(* test 57 (below max_int s = max_int) true;;
test 58 (below min_int s = 1) true;; *)
below max_int s;;
below min_int s;;