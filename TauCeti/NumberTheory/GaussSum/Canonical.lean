/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.AddCharacter.FiniteField
public import TauCeti.NumberTheory.GaussSum.Basic

/-!
# The canonical Gauss sum of a finite field

For a multiplicative character `χ` of a finite field of characteristic `p`, `χ.gauss` uses
the additive character `x ↦ exp(2πi Tr(x)/p)`. This fixes the sign of the phase and allows
Gauss sums over different finite fields to be compared without choosing additive characters.
Over a prime field this is the Gauss sum of the Dirichlet character against `ZMod.stdAddChar`.

The trivial multiplicative character has canonical Gauss sum `-1`. The multiplicative shift
`ψ.mulShift a` of the additive character `ψ` sends `x` to `ψ (a * x)`. For `a ≠ 0` this
multiplies the Gauss sum by `χ⁻¹ a`. The shift by zero gives the sum of the multiplicative
character alone (`MulChar.gaussSum_mulShift_stdAddChar`). The shifted sums add to zero even for
the trivial multiplicative character. Switching the sign of the phase multiplies the sum by
`χ (-1)` (`gaussSum_inv_right`).

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Ch. 8, §2.
-/

public section

namespace MulChar

open TauCeti.FiniteField

variable {F : Type*} [Field F]

/-- The Gauss sum of `χ` against the canonical additive character of its finite field. -/
noncomputable def gauss [Finite F] (χ : MulChar F ℂ) : ℂ :=
  letI := Fintype.ofFinite F
  gaussSum χ (stdAddChar F)

/-- Compute the canonical Gauss sum using any enumeration of the finite field. -/
theorem gauss_def [inst : Fintype F] (χ : MulChar F ℂ) :
    χ.gauss = gaussSum χ (stdAddChar F) := by
  unfold gauss
  rw [Subsingleton.elim (Fintype.ofFinite F) inst]

open scoped Classical in
/-- A multiplicative shift by `a` gives `χ⁻¹ a * χ.gauss`, except at zero for the trivial
multiplicative character, where it is `Nat.card F - 1` cast into `ℂ`. -/
theorem gaussSum_mulShift_stdAddChar [Fintype F] (χ : MulChar F ℂ) (a : F) :
    gaussSum χ ((stdAddChar F).mulShift a) =
      if a = 0 ∧ χ = 1 then ↑(Nat.card F - 1) else χ⁻¹ a * χ.gauss := by
  rw [gauss_def, gaussSum_mulShift_eq_ite]

/-- The Gauss sums over all multiplicative shifts of the canonical additive character add to zero,
including when the multiplicative character is trivial. -/
@[simp↓] theorem sum_gaussSum_mulShift_stdAddChar [Fintype F] (χ : MulChar F ℂ) :
    ∑ a : F, gaussSum χ ((stdAddChar F).mulShift a) = 0 :=
  χ.sum_gaussSum_mulShift_eq_zero_of_ne_one_right (stdAddChar_ne_one F)

/-- The trivial multiplicative character has canonical Gauss sum `-1`. -/
@[simp] theorem gauss_one [Finite F] : (1 : MulChar F ℂ).gauss = -1 := by
  let := Fintype.ofFinite F
  rw [gauss_def, gaussSum_one_left (stdAddChar_ne_one F)]

/-- Over a prime field the canonical Gauss sum uses the standard additive character
of the residue ring. -/
theorem gauss_zmod {p : ℕ} [Fact p.Prime] (χ : MulChar (ZMod p) ℂ) :
    χ.gauss = gaussSum χ ZMod.stdAddChar := by
  rw [gauss_def, stdAddChar_zmod]

end MulChar
