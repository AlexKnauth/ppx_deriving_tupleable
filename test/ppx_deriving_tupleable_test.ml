open Ppx_deriving_tupleable_test_data
open OUnit2

let check_convert_tuple to_tuple of_tuple ~ctxt:ctxt data tup =
  (* assert_equal expected actual *)
  assert_equal ~ctxt tup (to_tuple data);
  assert_equal ~ctxt data (of_tuple tup)

let check_full_name_tup = check_convert_tuple full_name_to_tuple full_name_of_tuple

let test1 ctxt = check_full_name_tup ~ctxt { first_name = "Alice"; middle_name = "Andrea"; last_name = "Anderson" } ("Alice", "Andrea", "Anderson")
let test2 ctxt = check_full_name_tup ~ctxt { last_name = "Carpenter"; middle_name = "Oakenshield"; first_name = "Bob" } ("Bob", "Oakenshield", "Carpenter")
let test3 ctxt = check_full_name_tup ~ctxt { last_name = "Smith"; first_name = "Charlie"; middle_name = "Otis" } ("Charlie", "Otis", "Smith")


let suite =
"ppx_deriving_tupleable_test">:::
 ["test1">:: test1;
  "test2">:: test2;
  "test3">:: test3]

let () = run_test_tt_main suite
