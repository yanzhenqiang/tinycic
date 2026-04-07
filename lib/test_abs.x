namespace TestAbs

def abs (z : Int) : Int := z
def zero : Int := Int.zero

theorem abs_zero : abs zero = zero :=
  by
    exact sorry

end TestAbs
