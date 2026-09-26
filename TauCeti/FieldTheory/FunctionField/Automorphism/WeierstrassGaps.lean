/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.WeierstrassGaps
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Galois

/-!
# Automorphisms preserve Weierstrass gaps

An automorphism of a function field transports a function with order `-n` at `P` and
nonnegative order elsewhere to one with the same property at the image of `P`. Thus pole
numbers, gaps, and the finite set of gaps are invariant under the action on places. This is
the invariance needed to make the exceptional Weierstrass places an invariant set.

The transport uses only the order functions at places; it needs no function-field or
exact-constant hypothesis.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.6 and III.5.
-/

public section

namespace TauCeti

namespace Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (σ : F ≃ₐ[k] F) (P : Place k F) (n : ℕ)

/-- An automorphism carries each pole number at a place to the same pole number at its image. -/
theorem IsPoleNumber.smul (h : P.IsPoleNumber n) : (σ • P).IsPoleNumber n := by
  obtain ⟨x, hx, hxP, hxQ⟩ := (P.isPoleNumber_iff n).mp h
  apply ((σ • P).isPoleNumber_iff n).mpr
  refine ⟨σ x, (map_ne_zero σ).mpr hx, ?_, ?_⟩
  · simpa only [ord_smul_apply] using hxP
  · intro Q hQP
    have hne : σ⁻¹ • Q ≠ P := by
      intro heq
      apply hQP
      have heq' := congrArg (σ • ·) heq
      simpa only [smul_inv_smul] using heq'
    have h := hxQ (σ⁻¹ • Q) hne
    calc
      0 ≤ (σ⁻¹ • Q).ord x := h
      _ = (σ • (σ⁻¹ • Q)).ord (σ x) := (ord_smul_apply σ (σ⁻¹ • Q) x).symm
      _ = Q.ord (σ x) := by rw [smul_inv_smul]

/-- Pole numbers at the image of a place are precisely its original pole numbers. -/
@[simp]
theorem isPoleNumber_smul_iff : (σ • P).IsPoleNumber n ↔ P.IsPoleNumber n := by
  constructor
  · intro h
    have := h.smul σ⁻¹
    simpa only [inv_smul_smul] using this
  · exact IsPoleNumber.smul σ P n

/-- Gaps at the image of a place are precisely its original gaps. -/
theorem isGap_smul_iff : (σ • P).IsGap n ↔ P.IsGap n := by
  simp only [isGap_iff_not_isPoleNumber, isPoleNumber_smul_iff σ P n]

/-- The finite set of gaps up to any bound is unchanged by an automorphism. -/
@[simp]
theorem gapNumbersUpTo_smul (m : ℕ) :
    (σ • P).gapNumbersUpTo m = P.gapNumbersUpTo m := by
  ext n
  simp only [mem_gapNumbersUpTo_iff, isGap_smul_iff σ P n]

/-- The finite set of Weierstrass gaps is unchanged by an automorphism. -/
@[simp]
theorem weierstrassGaps_smul :
    (σ • P).weierstrassGaps = P.weierstrassGaps := by
  ext n
  simp only [mem_weierstrassGaps_iff, isGap_smul_iff σ P n]

end Place

end TauCeti
