/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.HalfSpin.Basic
-- Private: `CliffordAlgebra.finrank_evenOdd` is used only inside proofs; it is not named by
-- an exported statement.
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension

/-!
# The dimensions of the half-spin summands

`TauCeti.spinRep` realizes the spinor module of a polarized quadratic space `(V, Q)` on the
exterior algebra `S = ⋀·W` of the isotropic summand `W` of the polarization, and
`TauCeti.spinPlus` and `TauCeti.spinMinus` cut it into its even and odd halves. This file counts
those halves.

The count of `S` itself needs nothing new: it is `TauCeti.ExteriorAlgebra.finrank_eq_two_pow` read
on the module `⋀·W` that carries the spin representation, giving `dim S = 2 ^ dim W`. The count of
the two halves is not a formality, because `⋀·W` is the Clifford algebra of the *zero* form, where
the classical argument — multiply by an anisotropic vector, which is odd and invertible — has
nothing to multiply by. The odd invertible operator is instead multiplication corrected by a
contraction, Mathlib's `CliffordAlgebra.changeFormAux`, turned into an automorphism of the grading
in `TauCeti/LinearAlgebra/CliffordAlgebra/ParitySwap.lean`; here the count it yields,
`CliffordAlgebra.finrank_evenOdd`, is only consumed. So each half is exactly half of `S`, of
dimension `2 ^ (dim W - 1)` — the dimension of a half-spin representation.

For `W = 0` the spinor module is the ground field, sitting entirely in the even half, and there is
no half-spin splitting to speak of. The even half still has dimension `1 = 2 ^ (0 - 1)` by truncated
subtraction, so `TauCeti.finrank_spinPlus` needs no hypothesis, whereas the odd half is `0` and
`TauCeti.finrank_spinMinus` requires `W ≠ ⊥`.

A polarization also fixes `dim W` in terms of `dim V`, by the dimension count that comes with the
polarization data itself (`TauCeti/RepresentationTheory/Spin/Polarization/Basic.lean`): `dim W = l`
both in even dimension `2l`, the type `Dₗ` case, where the remainder of the polarization vanishes
(`TauCeti.SpinPolarizationData.line_eq_bot_of_even_finrank`) so that the two halves are
subrepresentations of dimension `2 ^ (l - 1)`, and in odd dimension `2l + 1`, the type `Bₗ` case,
where the remainder is a line, the splitting is not one of representations (see
`TauCeti/RepresentationTheory/Spin/HalfSpin/Basic.lean`) and the spin module of dimension `2 ^ l`
is the one that matters.

## Main results

* `TauCeti.finrank_spinPlus` and `TauCeti.finrank_spinMinus`: **each half-spin summand has
  dimension `2 ^ (dim W - 1)`.**

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1: the spin module
  `S = ⋀·W` of dimension `2ˡ` and its half-spin summands `S⁺`, `S⁻` of dimension `2ˡ⁻¹`.
-/

public section

open Module CliffordAlgebra

namespace TauCeti

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q) [FiniteDimensional K P.W]

/-- **The even half-spin summand has dimension `2 ^ (dim W - 1)`.**

Half the dimension `2 ^ dim W` of the spinor module `⋀·W`, so `2 ^ (l - 1)` for a polarization of
a `2l`-dimensional space, where `dim W = l` by
`TauCeti.SpinPolarizationData.finrank_W_eq_of_finrank_eq_two_mul`. In the degenerate case `W = ⊥`
the spinor module `⋀·W = K` is entirely even, of dimension `1 = 2 ^ (0 - 1)` by truncated
subtraction. -/
theorem finrank_spinPlus :
    finrank K (spinPlus Q P) = 2 ^ (finrank K P.W - 1) := by
  rw [spinPlus_def]
  rcases subsingleton_or_nontrivial P.W with h | h
  · have hW : finrank K P.W = 0 := Module.finrank_zero_of_subsingleton
    have htop : finrank K (CliffordAlgebra (0 : QuadraticForm K P.W)) = 1 := by
      rw [finrank_eq_two_pow, hW, pow_zero]
    have : Nontrivial (CliffordAlgebra (0 : QuadraticForm K P.W)) :=
      Module.nontrivial_of_finrank_pos (R := K)
        (M := CliffordAlgebra (0 : QuadraticForm K P.W)) (by omega)
    have hone : (1 : CliffordAlgebra (0 : QuadraticForm K P.W)) ∈
        evenOdd (0 : QuadraticForm K P.W) 0 := by
      rw [← even_toSubmodule]
      exact (even (0 : QuadraticForm K P.W)).one_mem
    have : Nontrivial (evenOdd (0 : QuadraticForm K P.W) 0) :=
      Submodule.nontrivial_iff_ne_bot.2 ((Submodule.ne_bot_iff _).2 ⟨1, hone, one_ne_zero⟩)
    have hle := Submodule.finrank_le (R := K) (evenOdd (0 : QuadraticForm K P.W) 0)
    have hpos := Module.finrank_pos (R := K) (M := evenOdd (0 : QuadraticForm K P.W) 0)
    rw [hW, Nat.zero_sub, pow_zero]
    exact le_antisymm (hle.trans htop.le) hpos
  · exact finrank_evenOdd 0 0

/-- **The odd half-spin summand has dimension `2 ^ (dim W - 1)`**, the same as the even one:
`TauCeti.finrank_spinPlus` for the other parity. -/
theorem finrank_spinMinus (hW : P.W ≠ ⊥) :
    finrank K (spinMinus Q P) = 2 ^ (finrank K P.W - 1) := by
  have : Nontrivial P.W := Submodule.nontrivial_iff_ne_bot.2 hW
  rw [spinMinus_def]
  exact finrank_evenOdd 0 1

end TauCeti
