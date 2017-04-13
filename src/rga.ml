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

module RGA : sig
  type ('a, 'b) operation = Insert of ('a * ('b * bool)) * 'a option |
    Delete of 'a
  val interpret_opers :
    'a HOL.equal * 'a Orderings.linorder ->
      ('a, 'b) operation ->
        ('a * ('b * bool)) list -> (('a * ('b * bool)) list) option
end = struct

type ('a, 'b) operation = Insert of ('a * ('b * bool)) * 'a option |
  Delete of 'a;;

let rec interpret_opers (_A1, _A2)
  x0 xs = match x0, xs with
    Insert (e, n), xs -> Ordered_List.insert (_A1, _A2) xs e n
    | Delete n, xs -> Ordered_List.delete (_A1, _A2) xs n;;

end;; (*struct RGA*)
