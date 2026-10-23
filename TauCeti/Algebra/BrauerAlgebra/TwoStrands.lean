/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerAlgebra.Basic
public import TauCeti.Combinatorics.Brauer.TwoStrands

/-!
# The Brauer algebra on two strands, by generators and relations

The Brauer algebra `TauCeti.BrauerAlgebra R δ k` is the free `R`-module on the Brauer diagrams on
`k` strands (`TauCeti.BrauerAlgebra.basis`), multiplied by the loop-weighted stacking
`TauCeti.BrauerAlgebra.of_mul_of`. On two strands there are only the three diagrams

`1` (two through strands), `s` (the crossing), and `e` (the bottom cap with the top cup)

(`TauCeti.BrauerDiagram.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup`), and the loop
count is known outright (`TauCeti.middleLoopCount_two`): a loop closes up in the middle in the
product `e * e` alone, where exactly one does. So the whole multiplication table of `B₂(δ)` is

`s * s = 1`,  `e * e = δ • e`,  `s * e = e`,  `e * s = e`,

these four being the two-strand readings of the general relations of
`TauCeti/Algebra/BrauerAlgebra/Basic.lean`.

This file proves that those four relations **present** `B₂(δ)`: a pair of elements of an
`R`-algebra satisfying them extends to an algebra map out of `B₂(δ)` carrying `s` and `e` to them
(`TauCeti.BrauerAlgebra.liftTwo`), and it extends in only one way
(`TauCeti.BrauerAlgebra.algHom_ext_two`). That is what makes `B₂(δ)` usable as a source of
operators: the general `TauCeti.BrauerAlgebra.lift` asks for a value at every diagram obeying the
loop rule at every pair of them, whereas on two strands it is enough to exhibit two elements and
check four identities. The presentation is a two-strand phenomenon -- it is the exact knowledge of
the three diagrams and of their loop counts that reduces the loop rule to four relations -- so it
is stated here and not for general `k`.

## Main definitions

* `TauCeti.BrauerAlgebra.liftTwo`: the algebra map out of `B₂(δ)` extending a pair of elements
  satisfying the four relations.

## Main results

* `TauCeti.BrauerAlgebra.liftTwo_of_permToBrauer_swap` and
  `TauCeti.BrauerAlgebra.liftTwo_of_capCup`: the extension carries the crossing and the cap-cup
  diagram to the two given elements.
* `TauCeti.BrauerAlgebra.algHom_ext_two`: **an algebra map out of `B₂(δ)` is determined by its
  values on the crossing and on the cap-cup diagram**, so the extension is unique and the four
  relations are a presentation.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
-/

public section

namespace TauCeti

namespace BrauerAlgebra

variable {R : Type*} [CommSemiring R] {δ : R}

section Lift

variable {A : Type*} [Semiring A] [Algebra R A]

/-- **The presentation of `B₂(δ)` by generators and relations**: a crossing element `x` and a
cap-cup element `y` of an `R`-algebra satisfying the four relations `x * x = 1`, `y * y = δ • y`,
`x * y = y` and `y * x = y` extend to an algebra map out of the Brauer algebra on two strands.
The extension sends the three Brauer diagrams on two strands to `1`, `x` and `y`, which obeys the
loop rule because those four relations are the whole multiplication table of `B₂(δ)`. -/
noncomputable def liftTwo (x y : A) (hx : x * x = 1) (hy : y * y = δ • y) (hxy : x * y = y)
    (hyx : y * x = y) : BrauerAlgebra R δ 2 →ₐ[R] A :=
  lift (fun D => if D = capCup 0 1 then y else if D = permToBrauer (Equiv.swap 0 1) then x else 1)
    (by simp [permToBrauer_one_ne_capCup, permToBrauer_one_ne_permToBrauer_swap])
    (fun D₁ D₂ => by
      rcases D₁.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup with rfl | rfl | rfl <;>
        rcases D₂.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup with rfl | rfl | rfl <;>
          simp [permToBrauer_one_ne_capCup, permToBrauer_swap_ne_capCup,
            permToBrauer_one_ne_permToBrauer_swap, hx, hy, hxy, hyx])

@[simp]
theorem liftTwo_of_permToBrauer_swap (x y : A) (hx : x * x = 1) (hy : y * y = δ • y)
    (hxy : x * y = y) (hyx : y * x = y) :
    liftTwo (δ := δ) x y hx hy hxy hyx (of (permToBrauer (Equiv.swap 0 1))) = x :=
  (lift_of _ _ _ _).trans (by simp [permToBrauer_swap_ne_capCup])

@[simp]
theorem liftTwo_of_capCup (x y : A) (hx : x * x = 1) (hy : y * y = δ • y) (hxy : x * y = y)
    (hyx : y * x = y) : liftTwo (δ := δ) x y hx hy hxy hyx (of (capCup 0 1)) = y :=
  (lift_of _ _ _ _).trans (by simp)

/-- **An algebra map out of `B₂(δ)` is determined by its values on the crossing and on the cap-cup
diagram.** Together with `TauCeti.BrauerAlgebra.liftTwo` this says that the Brauer algebra on two
strands is presented by those two generators subject to the four relations: the identity diagram
is the unit, so it carries no further information. -/
theorem algHom_ext_two {f g : BrauerAlgebra R δ 2 →ₐ[R] A}
    (hs : f (of (permToBrauer (Equiv.swap 0 1))) = g (of (permToBrauer (Equiv.swap 0 1))))
    (he : f (of (capCup 0 1)) = g (of (capCup 0 1))) : f = g :=
  algHom_ext fun D => by
    rcases D.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup with rfl | rfl | rfl
    · rw [← one_def, map_one, map_one]
    · exact hs
    · exact he

end Lift

/-! ### The two-strand multiplication table

The four relations that `TauCeti.BrauerAlgebra.liftTwo` asks for are instances of the general
relations of `TauCeti/Algebra/BrauerAlgebra/Basic.lean`, so no name is claimed for them; what the
`example`s record is that those general relations do assemble, on two strands, into the
multiplication table the presentation rests on, and that the three diagrams span three
dimensions. -/

-- `s * s = 1`.
example : (of (permToBrauer (Equiv.swap (0 : Fin 2) 1)) *
    of (permToBrauer (Equiv.swap 0 1)) : BrauerAlgebra R δ 2) = 1 := by
  rw [of_permToBrauer_mul_of_permToBrauer, Equiv.swap_mul_self, one_def]

-- `e * e = δ • e`.
example : (of (capCup (0 : Fin 2) 1) * of (capCup 0 1) : BrauerAlgebra R δ 2) =
    δ • of (capCup 0 1) :=
  of_capCup_mul_of_capCup (by decide)

-- `s * e = e`.
example : (of (permToBrauer (Equiv.swap (0 : Fin 2) 1)) *
    of (capCup 0 1) : BrauerAlgebra R δ 2) = of (capCup 0 1) :=
  of_permToBrauer_swap_mul_of_capCup 0 1

-- `e * s = e`.
example : (of (capCup (0 : Fin 2) 1) *
    of (permToBrauer (Equiv.swap 0 1)) : BrauerAlgebra R δ 2) = of (capCup 0 1) :=
  of_capCup_mul_of_permToBrauer_swap 0 1

-- `B₂(δ)` has dimension `(2 * 2 - 1)‼ = 3`, the number of Brauer diagrams on two strands.
example [StrongRankCondition R] : Module.finrank R (BrauerAlgebra R δ 2) = 3 := by
  rw [finrank_eq_doubleFactorial R δ 2]
  decide

end BrauerAlgebra

end TauCeti
