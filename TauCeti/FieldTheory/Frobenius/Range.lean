/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Frobenius power subfields over perfect constants

If `k` is perfect of exponential characteristic `p`, the `p^n`-th powers in an extension `F`
form an intermediate field of `F / k`. Iterated Frobenius identifies `F` with this field,
semilinearly over the corresponding Frobenius automorphism of `k`. The construction uses
Mathlib's `RingHom.fieldRange` and `RingHom.rangeRestrictFieldEquiv`.

This distinguishes an isomorphism of abstract fields preserving the constant subfield from a
`k`-algebra isomorphism: Frobenius need not fix each element of `k`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.10.
-/

public section

namespace TauCeti

variable (k F : Type*) [Field k] [Field F] [Algebra k F]
variable (p : ℕ) [ExpChar k p] [PerfectRing k p] (n : ℕ)

/-- The intermediate field `F^{p^n}` of iterated Frobenius powers. Perfectness ensures that
it contains every constant from `k`. -/
noncomputable def frobeniusPowers : IntermediateField k F := by
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
  exact (iterateFrobenius F p n).fieldRange.toIntermediateField fun c ↦ by
    refine ⟨algebraMap k F ((iterateFrobeniusEquiv k p n).symm c), ?_⟩
    rw [← RingHom.map_iterateFrobenius, ← coe_iterateFrobeniusEquiv,
      RingEquiv.apply_symm_apply]

/-- The underlying subfield is Mathlib's field range of iterated Frobenius. -/
theorem frobeniusPowers_toSubfield :
    letI : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
    (frobeniusPowers k F p n).toSubfield = (iterateFrobenius F p n).fieldRange := by
  unfold frobeniusPowers
  exact Subfield.toIntermediateField_toSubfield _ _

/-- Membership in the Frobenius power subfield means being a `p^n`-th power in `F`. -/
@[simp]
theorem mem_frobeniusPowers (z : F) :
    z ∈ frobeniusPowers k F p n ↔ ∃ x : F, x ^ p ^ n = z := by
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
  rw [← IntermediateField.mem_toSubfield, frobeniusPowers_toSubfield, RingHom.mem_fieldRange]
  simp only [iterateFrobenius_def]

/-- Iterated Frobenius as an isomorphism from `F` onto its power subfield. It is semilinear,
not generally linear, over `k`. -/
noncomputable def iterateFrobeniusEquivPowers : F ≃+* frobeniusPowers k F p n := by
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
  -- Adding the proof that the range contains `k` does not change its underlying field.
  unfold frobeniusPowers
  exact (iterateFrobenius F p n).rangeRestrictFieldEquiv

/-- The field isomorphism onto the power subfield sends `x` to `x^{p^n}`. -/
@[simp]
theorem coe_iterateFrobeniusEquivPowers (x : F) :
    (iterateFrobeniusEquivPowers k F p n x : F) = x ^ p ^ n := by
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
  exact (RingHom.rangeRestrictFieldEquiv_apply_coe (iterateFrobenius F p n) x).trans
    (iterateFrobenius_def p n x)

/-- On constants, the power-subfield isomorphism acts by the Frobenius automorphism of `k`. -/
@[simp]
theorem iterateFrobeniusEquivPowers_algebraMap (c : k) :
    iterateFrobeniusEquivPowers k F p n (algebraMap k F c) =
      algebraMap k (frobeniusPowers k F p n) (iterateFrobeniusEquiv k p n c) := by
  apply Subtype.ext
  simp [iterateFrobenius_def]

/-- The ambient field is purely inseparable over its iterated Frobenius power subfield. -/
instance isPurelyInseparable_frobeniusPowers :
    IsPurelyInseparable (frobeniusPowers k F p n) F := by
  have : ExpChar (frobeniusPowers k F p n) p :=
    expChar_of_injective_algebraMap (algebraMap k _).injective p
  rw [isPurelyInseparable_iff_pow_mem _ p]
  intro x
  exact ⟨n, ⟨x ^ p ^ n, (mem_frobeniusPowers k F p n _).mpr ⟨x, rfl⟩⟩, rfl⟩

end TauCeti
