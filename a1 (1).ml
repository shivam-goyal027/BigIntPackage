open Signature_a0
	module A0:BigInt=struct

type bigint=sign*int list
and sign= Neg | NonNeg

(*convert a positive integer to int list*) 
let rec mk_Big n l= if n<10 then n::l
	else mk_Big (n/10) ((n mod 10)::l)

(*convert integer to bigint*)
let mk_big n=if n<0 then ((Neg,mk_Big ((-1)*n) []):bigint)
	else (NonNeg,mk_Big n [])

(*convert int list to string*)
let rec print_list l s= match l with
	[x]->s^(string_of_int x)
	| x::xs-> print_list xs (s^(string_of_int x))
	|[]->""

(*convert bigint to string*)
let print_num (bg:bigint)= match bg with
	(Neg,l)-> ("-"^(print_list l ""))
	| (NonNeg,l)->print_list l ""

(*check if two intlist are same*)
let rec equal (l1:int list) (l2:int list)=match l1 with
	[x1]->(match l2 with
		[x2]-> (x1=x2)
		| _->false
	)
	| x1::xs1->(match l2 with
		[x2]->false
		|x2::xs2->((x1=x2) && (equal xs1 xs2))
	)
	|[]->(match l2 with
		[]-> true
		| _->false
	)

(*check if two bigint are same*)
let eq (a:bigint) (b:bigint)= match (a,b) with
				((Neg,l1),(NonNeg,l2))->false
				| ((NonNeg,l1),(Neg,l2))->false
				| ((Neg,l1),(Neg,l2))->(equal l1 l2)
				| ((NonNeg,l1),(NonNeg,l2))->(equal l1 l2)

(*reverse int list*)
let rev_list (l:int list) =
  let rec list_rev l2 l1=match l1 with
    [] -> l2
    | x::xs -> list_rev (x::l2) xs
  in 
  list_rev [] l

(*returns size of int list*)
let rec size (l:int list)=match l with
	[]->0
	|x::xs->1+(size xs)

(*check for absolute greater comparison of int list*)
let rec greater (l1:int list) (l2:int list)= if ((size l1) > (size l2)) then true
					else if ((size l1) < (size l2)) then false
					else(match l1 with
					[x1]->(match l2 with
						[x2]->(x1>x2)
						)
					|x1::xs1->(match l2 with
						x2::xs2->if (x1>x2) then true
							else if (x1<x2) then false
							else (greater xs1 xs2)
						)
					|[]->false
					)

(*check for int list greater comparison*)
let great (l1:int list) (l2:int list)=greater (l1) (l2)

(*check for bigint greater comparison*)
let gt (a:bigint) (b:bigint)= match (a,b) with
				((Neg,l1),(NonNeg,l2))->false
				| ((NonNeg,l1),(Neg,l2))->true

				| ((Neg,l1),(Neg,l2))->(great l2 l1)
				| ((NonNeg,l1),(NonNeg,l2))->(great l1 l2)

(*check for bigint greater or equal comparison*)
let geq (a:bigint) (b:bigint)= (gt a b) || (eq a b)

(*check for bigint lesser comparison*)
let lt (a:bigint) (b:bigint)= not (geq a b)

(*check for bigint lesser or equal comparison*)
let leq (a:bigint) (b:bigint)= (lt a b) || (eq a b)

(*inverts sign of bigint*)
let minus (a:bigint)=match a with
	(Neg,l1)->((NonNeg,l1):bigint)
	|(NonNeg,l1)->(Neg,l1)

(*finds absolute of bigint*)
let abs (a:bigint)=match a with
	(Neg,l1)->((NonNeg,l1):bigint)
	|(NonNeg,l1)->(NonNeg,l1)

(*adds carry to the remaining part (helper) *)
let rec carry_fun (carry:int) (l:int list) (l0:int list)=match carry with
		0->(rev_list l)@l0
		|1->(match l with
			[x]->[((x+carry)/10);((x+carry) mod 10)]@l0
			|x::xs-> carry_fun ((x+carry)/10) xs (((x+carry) mod 10)::l0)
			|[]->1::l0)

(*adds carry to the remaining part *)
let carry_accumulator (carry:int) (l:int list)= carry_fun carry l []

(*adds using reverse list*)
let rec sum (l1:int list) (l2:int list) (l:int list) (carry:int)=match l1 with
		[x1]->(match l2 with
			[x2]-> [((x1+x2+carry)/10);((x1+x2+carry) mod 10)]@l
			|x2::xs2 -> (carry_accumulator ((x1+x2+carry)/10) xs2)@(((x1+x2+carry) mod 10)::l)
			|[]->[((x1+carry)/10);((x1+carry) mod 10)]@l)
		| x1::xs1->( match l2 with 
		        [x2]-> (carry_accumulator ((x1+x2+carry)/10) xs1)@(((x1+x2+carry) mod 10)::l)
			|x2::xs2-> sum xs1 xs2 (((x1+x2+carry) mod 10)::l) ((x1+x2+carry)/10)
			|[]->(carry_accumulator carry (x1::xs1))@l)
		|[]->(match l2 with
			[]->[0]
			|_->(rev_list l2))

(*gives reverse list to the above function *)
let add_list (l1:int list) (l2:int list)=sum (rev_list l1) (rev_list l2) [] 0

(*removes extra starting zeros*)
let rec shave_zero (l:int list)=match l with
			[0]->[0]
			|0::xs-> shave_zero xs
			|_->l

(*subtracts using reverse list*)
let rec dif (l1:int list) (l2:int list) (l:int list) (carry:int)=match l1 with
		[x1]->(match l2 with 
			[x2]->(((x1-carry)-x2)::l)
			|[]->((x1-carry)::l))
		|x1::xs1->(match l2 with 
			[x2]->if ((x1-carry)>=x2) then (rev_list xs1)@(((x1-carry)-x2)::l)
			      else (dif xs1 [1] (((x1-carry+10)-x2)::l) 0) 
			|x2::xs2->if((x1-carry)>=x2) then (dif xs1 xs2 ((x1-carry-x2)::l) 0)
				else (dif xs1 xs2 (((x1-carry+10)-x2)::l) 1))

(*provides reverse lists l1 and l2,here l1 is always bigger in magnitude than l2*)
let sub_list (l1:int list) (l2:int list)=(dif (rev_list l1) (rev_list l2) [] 0)

(*adds 2 bigints*)
let add (a:bigint) (b:bigint)=match a with
			     (NonNeg,l1)->(match b with
					 (NonNeg,l2)->((NonNeg,(shave_zero(add_list l1 l2))):bigint)
					 |(Neg,l2)->if (great l1 l2) then (NonNeg,(shave_zero (sub_list l1 l2)))
						    else if (equal l1 l2) then (NonNeg,[0])
						    else if (great l2 l1) then (Neg,(shave_zero(sub_list l2 l1)))
						    else (NonNeg,shave_zero(l1))
					)
			     |(Neg,l1)->(match b with
					 (Neg,l2)->(Neg,(shave_zero(add_list l1 l2)))
					 |(NonNeg,l2)->if (great l1 l2) then (Neg,(shave_zero (sub_list l1 l2)))
						    else if (equal l1 l2) then (NonNeg,[0])
						    else if (great l2 l1) then (NonNeg,(shave_zero(sub_list l2 l1)))
						    else (Neg,shave_zero(l1))
					)

(*subtracts 2 bigints*)
let sub (a:bigint) (b:bigint)=match a with
			     (NonNeg,l1)->(match b with
					 (Neg,l2)->(((NonNeg,(shave_zero(add_list l1 l2)))):bigint)
					 |(NonNeg,l2)->if (great l1 l2) then (NonNeg,(shave_zero (sub_list l1 l2)))
						    else if (equal l1 l2) then (NonNeg,[0])
						    else if (great l2 l1) then (Neg,(shave_zero(sub_list l2 l1)))
						    else (NonNeg,shave_zero(l1))
					)
			     |(Neg,l1)->(match b with
					 (NonNeg,l2)->(Neg,(shave_zero(add_list l1 l2)))
					 |(Neg,l2)->if (great l1 l2) then (Neg,(shave_zero (sub_list l1 l2)))
						    else if (equal l1 l2) then (NonNeg,[0])
						    else if (great l2 l1) then (NonNeg,(shave_zero(sub_list l2 l1)))
						    else (Neg,shave_zero(l1))
					)

(*multiplies int list with a digit*)
let rec mul_dig (l:int list) (d:int) (l0:int list) (carry:int)=match l with
		[x]-> [((carry+(d*x))/10);((carry+(d*x)) mod 10)]@l0
		|x::xs-> (mul_dig xs d (((carry+(d*x)) mod 10)::l0) ((carry+(d*x))/10))

(*helper function to accumulate result of multiplication*)
let rec times_list (l1:int list) (l2:int list) (l:int list)=match l2 with
			[x2]->(add_list (mul_dig l1 x2 [] 0 ) l)
			|x2::xs2->(times_list l1 xs2 ((add_list (mul_dig l1 x2 [] 0) l)@[0]))

(*provides l1 reversed and non-reversed l2 to get multiplied*)
let mul_list (l1:int list) (l2:int list)=(times_list (rev_list l1) l2 [])

(*multiply function for bigints*)
let mult (a:bigint) (b:bigint)=match a with
	(NonNeg,l1)->(match b with
		(NonNeg,l2)->((NonNeg,shave_zero(mul_list l1 l2)):bigint)
		|(Neg,l2)->(Neg,shave_zero(mul_list l1 l2)))
	|(Neg,l1)->(match b with
		(NonNeg,l2)->(Neg,shave_zero(mul_list l1 l2))
		|(Neg,l2)->(NonNeg,shave_zero(mul_list l1 l2)))

(*division using shift and subtract*)
let rec comp (l1:int list) (l2:int list) (k:int) =match l1 with
		_->if(great (l1@[0]) l2) then (k,l1)
		else (comp (l1@[0]) l2 (k+1))                                        
let real_comp (l1:int list) (l2:int list)=(comp l1 l2 0)
let rec find_index (l1:int list) (l2:int list) (k:int)=match real_comp l1 l2 with
		(c,l)->if (great (shave_zero (mul_dig (rev_list l) (k+1) [] 0)) l2) then (k,c,(shave_zero (mul_dig (rev_list l) (k) [] 0)))
			else (find_index l1 l2 (k+1))
let rec compute (k:int) c l=if(c<=0) then l
			else (compute k (c-1) l@[0])
let real_compute k c=(compute k c [k])

(*divides list l2/l1 *)
let rec div_list (l1:int list) (l2:int list) (l:int list)=match (find_index l1 l2 0) with
		(count,zeros,build)->if(greater l1 (shave_zero (sub_list l2 build))) then (add_list l (real_compute count zeros))
				else (div_list l1 (shave_zero (sub_list l2 build)) (add_list l (real_compute count zeros)))
(*divides(gives quotient) bigint a/b*)
let div (a:bigint) (b:bigint)=
	(match (a,b) with
	(_,(NonNeg,[0]))->failwith "Divide_by_zero_exception"
	|(_,(_,[]))->failwith "Divide_by_zero_exception"
	|((NonNeg,l1),(NonNeg,l2))->((NonNeg,(div_list l2 l1 [])):bigint)
	|((Neg,l1),(Neg,l2))->(NonNeg,(div_list l2 l1 []))
	|((Neg,l1),(NonNeg,l2))->(Neg,(div_list l2 l1 []))
	|((NonNeg,l1),(Neg,l2))->(Neg,(div_list l2 l1 []))
	)

(*gives remainder using (r=a-b*q) *)
let rem (a:bigint) (b:bigint) = (sub a (mult b (div a b)))

end
