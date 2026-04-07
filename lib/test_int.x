-- Test file for Int
namespace TestInt

def test_val : Int := zero

theorem test_add_comm (a b : Int) : Eq (add a b) (add b a) :=
  by
    exact sorry

end TestInt
