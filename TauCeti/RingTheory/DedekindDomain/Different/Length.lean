/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Different.Basic
public import Mathlib.RingTheory.LocalRing.Length
public import TauCeti.RingTheory.DiscreteValuationRing.Length

/-!
# Length of the complementary-module quotient

For an extension of discrete valuation rings with finite separable fraction fields, the
complementary module `C` is the inverse of the different ideal `𝔡`. Multiplication by a
generator of `𝔡` identifies `C/B` with `B/𝔡`. Its length over the lower valuation ring is
therefore the different exponent times the full residue degree. In particular the residue
degree includes its inseparable factor; no separability of residue fields is required.

The quotient comparison only requires that the different be principal, and is proved for
Dedekind domains before specializing to discrete valuation rings.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §3 (the complementary module and the different).
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

variable {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A B] [Algebra A K] [Algebra K L] [Algebra A L] [Algebra B L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsDedekindDomain B] [IsFractionRing A K] [IsFractionRing B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L] [Module.IsTorsionFree A B]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- If `δ` generates the different, division by `δ` identifies `B/𝔡` with the
complementary module modulo the integral elements. -/
noncomputable def quotientDifferentIdealEquivTraceDualQuotient {δ : B}
    (hδ : differentIdeal A B = Ideal.span {δ}) :
    (B ⧸ differentIdeal A B) ≃ₗ[B]
      ((Submodule.traceDual A K (1 : Submodule B L)) ⧸
        (1 : Submodule B L).comap (Submodule.traceDual A K (1 : Submodule B L)).subtype) := by
  let e := equivTraceDualOfDifferentIdealEqSpan (K := K) (L := L) hδ
  have hδ0 : δ ≠ 0 := by
    intro h
    exact differentIdeal_ne_bot_of_isSeparable (K := K) (L := L) (by simpa [h] using hδ)
  have hδL : algebraMap B L δ ≠ 0 := by
    simpa using (IsFractionRing.injective B L).ne hδ0
  refine Submodule.Quotient.equiv _ _ e ?_
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp (hδ ▸ hb)
    exact Submodule.mem_one.mpr ⟨c, by
      simp [e, map_mul, hδL]⟩
  · intro hx
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp hx
    refine ⟨δ * b, hδ.symm ▸ Ideal.mem_span_singleton.mpr ⟨b, rfl⟩, ?_⟩
    apply Subtype.ext
    simpa [e, map_mul, hδL] using hb

/-- On representatives, the quotient comparison divides an integral element by a generator
of the different. The equality in the hypothesis specifies the resulting fraction without
unfolding its membership proof. -/
theorem quotientDifferentIdealEquivTraceDualQuotient_mk {δ : B}
    (hδ : differentIdeal A B = Ideal.span {δ}) (b : B)
    (x : Submodule.traceDual A K (1 : Submodule B L))
    (hx : (x : L) * algebraMap B L δ = algebraMap B L b) :
    quotientDifferentIdealEquivTraceDualQuotient hδ (Ideal.Quotient.mk _ b) =
      Submodule.Quotient.mk x := by
  have hδ0 : δ ≠ 0 := by
    intro h
    exact differentIdeal_ne_bot_of_isSeparable (K := K) (L := L) (by simpa [h] using hδ)
  have hδL : algebraMap B L δ ≠ 0 := by
    simpa using (IsFractionRing.injective B L).ne hδ0
  have he : equivTraceDualOfDifferentIdealEqSpan (K := K) (L := L) hδ b = x := by
    apply Subtype.ext
    rw [equivTraceDualOfDifferentIdealEqSpan_apply, ← hx, mul_div_cancel_right₀ _ hδL]
  -- The quotient map is induced by the division equivalence.
  exact congrArg Submodule.Quotient.mk he

/-- The inverse quotient comparison multiplies a complementary element by a generator of
the different. -/
theorem quotientDifferentIdealEquivTraceDualQuotient_symm_mk {δ : B}
    (hδ : differentIdeal A B = Ideal.span {δ}) (b : B)
    (x : Submodule.traceDual A K (1 : Submodule B L))
    (hx : (x : L) * algebraMap B L δ = algebraMap B L b) :
    (quotientDifferentIdealEquivTraceDualQuotient hδ).symm (Submodule.Quotient.mk x) =
      Ideal.Quotient.mk _ b :=
  (LinearEquiv.symm_apply_eq _).mpr
    (quotientDifferentIdealEquivTraceDualQuotient_mk hδ b x hx).symm

/-- The complementary-module quotient and the quotient by the different have the same length
over the base ring `A` whenever the different is principal. -/
theorem length_traceDual_quotient_eq_length_quotient_differentIdeal
    [Submodule.IsPrincipal (differentIdeal A B)] :
    Module.length A ((Submodule.traceDual A K (1 : Submodule B L)) ⧸
        (1 : Submodule B L).comap (Submodule.traceDual A K (1 : Submodule B L)).subtype) =
      Module.length A (B ⧸ differentIdeal A B) := by
  let δ := Submodule.IsPrincipal.generator (differentIdeal A B)
  have hδ : differentIdeal A B = Ideal.span {δ} :=
    (Ideal.span_singleton_generator _).symm
  exact ((quotientDifferentIdealEquivTraceDualQuotient (K := K) (L := L) hδ).restrictScalars
    A).length_eq.symm

/-- **The complementary-module length formula.** Over a local base and a discrete valuation
ring upstairs, `length_A(C/B) = d * [κ(B) : κ(A)]`, with `d` the multiplicity of the maximal
ideal in the different. The residue degree is the full degree, not just its separable part. -/
theorem length_traceDual_quotient_eq_multiplicity_mul_finrank
    [IsLocalRing A] [IsDiscreteValuationRing B] [IsLocalHom (algebraMap A B)]
    [Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
    Module.length A ((Submodule.traceDual A K (1 : Submodule B L)) ⧸
        (1 : Submodule B L).comap (Submodule.traceDual A K (1 : Submodule B L)).subtype) =
      (multiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B) : ℕ∞) *
        Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
  rw [length_traceDual_quotient_eq_length_quotient_differentIdeal,
    IsLocalRing.length_restrictScalars A B,
    Ideal.length_quotient_eq_multiplicity _
      (differentIdeal_ne_bot_of_isSeparable (K := K) (L := L)), Module.length_eq_finrank]

end TauCeti
