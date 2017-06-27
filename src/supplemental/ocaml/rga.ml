module HOL : sig
  type 'a equal
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let rec eq _A a b = equal _A a b;;

end;; (*struct HOL*)

module Product_Type : sig
  val fst : 'a * 'b -> 'a
end = struct

let rec fst (x1, x2) = x1;;

end;; (*struct Product_Type*)

module Orderings : sig
  type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool}
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  type 'a preorder = {ord_preorder : 'a ord}
  type 'a order = {preorder_order : 'a preorder}
  type 'a linorder = {order_linorder : 'a order}
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

type 'a linorder = {order_linorder : 'a order};;

end;; (*struct Orderings*)

module Option : sig
  val bind : 'a option -> ('a -> 'b option) -> 'b option
end = struct

let rec bind x0 f = match x0, f with None, f -> None
               | Some x, f -> f x;;

end;; (*struct Option*)

module Ordered_List : sig
  val delete :
    'a HOL.equal * 'a Orderings.linorder ->
      ('a * ('b * bool)) list -> 'a -> (('a * ('b * bool)) list) option
  val insert :
    'a HOL.equal * 'a Orderings.linorder ->
      ('a * ('b * bool)) list ->
        'a * ('b * bool) -> 'a option -> (('a * ('b * bool)) list) option
end = struct

let rec delete (_A1, _A2)
  x0 i = match x0, i with [], i -> None
    | (ia, (v, flag)) :: xs, i ->
        (if HOL.eq _A1 ia i then Some ((ia, (v, true)) :: xs)
          else Option.bind (delete (_A1, _A2) xs i)
                 (fun t -> Some ((ia, (v, flag)) :: t)));;

let rec insert_body _A
  x0 e = match x0, e with [], e -> [e]
    | x :: xs, e ->
        (if Orderings.less
              _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
              (Product_Type.fst x) (Product_Type.fst e)
          then e :: x :: xs else x :: insert_body _A xs e);;

let rec insert (_A1, _A2)
  xs e x2 = match xs, e, x2 with xs, e, None -> Some (insert_body _A2 xs e)
    | [], e, Some i -> None
    | x :: xs, e, Some i ->
        (if HOL.eq _A1 (Product_Type.fst x) i
          then Some (x :: insert_body _A2 xs e)
          else Option.bind (insert (_A1, _A2) xs e (Some i))
                 (fun t -> Some (x :: t)));;

end;; (*struct Ordered_List*)

module List : sig
  val member : 'a HOL.equal -> 'a list -> 'a -> bool
  val map : ('a -> 'b) -> 'a list -> 'b list
end = struct

let rec member _A x0 y = match x0, y with [], y -> false
                    | x :: xs, y -> HOL.eq _A x y || member _A xs y;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

end;; (*struct List*)

module Set : sig
  type 'a set = Set of 'a list | Coset of 'a list
  val member : 'a HOL.equal -> 'a -> 'a set -> bool
end = struct

type 'a set = Set of 'a list | Coset of 'a list;;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (List.member _A xs x)
    | x, Set xs -> List.member _A xs x;;

end;; (*struct Set*)

module RGA : sig
  type ('a, 'b) operation = Insert of ('a * ('b * bool)) * 'a option |
    Delete of 'a
  val valid_rga_msg :
    'a HOL.equal * 'a Orderings.linorder ->
      ('a * ('b * bool)) list -> 'a * ('a, 'b) operation -> bool
  val interpret_opers :
    'a HOL.equal * 'a Orderings.linorder ->
      ('a, 'b) operation ->
        ('a * ('b * bool)) list -> (('a * ('b * bool)) list) option
end = struct

type ('a, 'b) operation = Insert of ('a * ('b * bool)) * 'a option |
  Delete of 'a;;

let rec element_ids lista = Set.Set (List.map Product_Type.fst lista);;

let rec valid_rga_msg (_A1, _A2)
  lista msg =
    (match msg with (i, Insert (e, None)) -> HOL.eq _A1 (Product_Type.fst e) i
      | (i, Insert (e, Some pos)) ->
        HOL.eq _A1 (Product_Type.fst e) i &&
          Set.member _A1 pos (element_ids lista)
      | (_, Delete pos) -> Set.member _A1 pos (element_ids lista));;

let rec interpret_opers (_A1, _A2)
  x0 xs = match x0, xs with
    Insert (e, n), xs -> Ordered_List.insert (_A1, _A2) xs e n
    | Delete n, xs -> Ordered_List.delete (_A1, _A2) xs n;;

end;; (*struct RGA*)
