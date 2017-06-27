module HOL : sig
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let rec eq _A a b = equal _A a b;;

end;; (*struct HOL*)

module Fun : sig
  val fun_upd : 'a HOL.equal -> ('a -> 'b) -> 'a -> 'b -> 'a -> 'b
end = struct

let rec fun_upd _A f a b = (fun x -> (if HOL.eq _A x a then b else f x));;

end;; (*struct Fun*)

module List : sig
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val filter : ('a -> bool) -> 'a list -> 'a list
  val member : 'a HOL.equal -> 'a list -> 'a -> bool
  val insert : 'a HOL.equal -> 'a -> 'a list -> 'a list
  val removeAll : 'a HOL.equal -> 'a -> 'a list -> 'a list
  val list_all : ('a -> bool) -> 'a list -> bool
end = struct

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec filter
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec member _A x0 y = match x0, y with [], y -> false
                    | x :: xs, y -> HOL.eq _A x y || member _A xs y;;

let rec insert _A x xs = (if member _A xs x then xs else x :: xs);;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if HOL.eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

end;; (*struct List*)

module Set : sig
  type 'a set
  val equal_set : 'a HOL.equal -> 'a set HOL.equal
  val insert : 'a HOL.equal -> 'a -> 'a set -> 'a set
  val bot_set : 'a set
  val sup_set : 'a HOL.equal -> 'a set -> 'a set -> 'a set
  val minus_set : 'a HOL.equal -> 'a set -> 'a set -> 'a set
end = struct

type 'a set = Set of 'a list | Coset of 'a list;;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (List.member _A xs x)
    | x, Set xs -> List.member _A xs x;;

let rec less_eq_set _A
  a b = match a, b with Coset [], Set [] -> false
    | a, Coset ys -> List.list_all (fun y -> not (member _A y a)) ys
    | Set xs, b -> List.list_all (fun x -> member _A x b) xs;;

let rec equal_seta _A a b = less_eq_set _A a b && less_eq_set _A b a;;

let rec equal_set _A = ({HOL.equal = equal_seta _A} : 'a set HOL.equal);;

let rec insert _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (List.removeAll _A x xs)
    | x, Set xs -> Set (List.insert _A x xs);;

let rec remove _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (List.insert _A x xs)
    | x, Set xs -> Set (List.removeAll _A x xs);;

let bot_set : 'a set = Set [];;

let rec sup_set _A
  x0 a = match x0, a with
    Coset xs, a -> Coset (List.filter (fun x -> not (member _A x a)) xs)
    | Set xs, a -> List.fold (insert _A) xs a;;

let rec minus_set _A
  a x1 = match a, x1 with
    a, Coset xs -> Set (List.filter (fun x -> member _A x a) xs)
    | a, Set xs -> List.fold (remove _A) xs a;;

end;; (*struct Set*)

module ORSet : sig
  type ('a, 'b) operation = Add of 'a * 'b | Rem of 'a Set.set * 'b
  val interpret_op :
    'a HOL.equal -> 'b HOL.equal ->
      ('a, 'b) operation -> ('b -> 'a Set.set) -> ('b -> 'a Set.set) option
  val valid_behaviours :
    'b HOL.equal -> ('a -> 'b Set.set) -> 'b * ('b, 'a) operation -> bool
end = struct

type ('a, 'b) operation = Add of 'a * 'b | Rem of 'a Set.set * 'b;;

let rec op_elem oper = (match oper with Add (_, e) -> e | Rem (_, e) -> e);;

let rec interpret_op _A _B
  oper state =
    (let before = state (op_elem oper) in
     let after =
       (match oper
         with Add (i, _) -> Set.sup_set _A before (Set.insert _A i Set.bot_set)
         | Rem (is, _) -> Set.minus_set _A before is)
       in
      Some (Fun.fun_upd _B state (op_elem oper) after));;

let rec valid_behaviours _B
  state msg =
    (match msg with (i, Add (j, _)) -> HOL.eq _B i j
      | (_, Rem (is, e)) -> HOL.eq (Set.equal_set _B) is (state e));;

end;; (*struct ORSet*)
