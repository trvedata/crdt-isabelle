open Counter.Counter

let _ =
  Js.export_all
    (object%js
      method counter_op = counter_op
    end)
