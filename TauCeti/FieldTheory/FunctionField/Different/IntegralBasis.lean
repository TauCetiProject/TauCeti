/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Unramified
import TauCeti.FieldTheory.FunctionField.Different.Complementary
import TauCeti.FieldTheory.FunctionField.Different.Tame
import TauCeti.RingTheory.Discriminant.TraceDual

/-!
# Discriminants of local integral bases at unramified places

Let `E / F` be a finite separable extension of algebraic function fields over `k`, and let `P` be a
place of `F / k`. If `P` is unramified in `E`, then every place `P'` of `E` above `P` has vanishing
different exponent (`TauCeti.Place.differentExponent_eq_zero_iff`), so the complementary module
`Submodule.traceDual 𝒪_P F 1` coincides with the local integral closure `𝒪'_P`
(`TauCeti.Place.mem_traceDual_iff_forall_valuation_le`).

Consequently, for any integral basis `b` of `E / F` at `P`, its trace-dual basis `b.traceDual` is
also integral over `𝒪_P`. Since both `discr F b` and `discr F b.traceDual` lie in `𝒪_P` and their
product is `1` (`Module.Basis.discr_mul_discr_traceDual`), the discriminant of `b` is a unit of
`𝒪_P`, that is, `ord_P(discr F b) = 0`.

## Main results

* `TauCeti.Place.IsIntegralBasis.ord_discr_eq_zero`: at an unramified place `P`, every local
  integral basis has unit discriminant (`ord_P(discr F b) = 0`).
* `TauCeti.Place.ord_discr_localIntegralBasis_eq_zero`: specialization to
  `TauCeti.Place.localIntegralBasis E P`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections 3.3–3.5.
-/

public section

namespace TauCeti

namespace Place

variable {k F E : Type*} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- **At an unramified place, every local integral basis has unit discriminant**:
`ord_P(disc b) = 0`. Because every place of `E` above `P` has vanishing different exponent, the
complementary module equals the local integral closure, making the trace-dual basis integral at `P`
as well. -/
theorem IsIntegralBasis.ord_discr_eq_zero (hF : IsFunctionField k F) {P : Place k F}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {b : Module.Basis ι F E}
    (his : P.IsIntegralBasis E b) (hP : P.IsUnramified (k' := k) (F' := E)) :
    P.ord (Algebra.discr F b) = 0 := by
  have hb_int : ∀ i, IsIntegral P.integers (b i) := his.isIntegral
  have hspan : (1 : Submodule (integralClosure P.integers E) E).restrictScalars P.integers =
      Submodule.span P.integers (Set.range b) := by
    ext x
    rw [Submodule.restrictScalars_mem, his.mem_span_iff_isIntegral, ← mem_integralClosure_iff,
      Submodule.mem_one]
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  have hbdual_int : ∀ i, IsIntegral P.integers (b.traceDual i) := fun i ↦ by
    have hmem : b.traceDual i ∈
        Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers E) E) := by
      rw [← Submodule.restrictScalars_mem P.integers,
        Submodule.traceDual_span_of_basis P.integers _ b hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    refine (isIntegral_iff_forall_restrict_eq_mem_integers hF.finite_extension P).mpr
      fun P' hP' ↦ ?_
    have hd0 : differentExponent k F P' = 0 :=
      (differentExponent_eq_zero_iff k F P').mpr
        ((ramificationIdx_eq_one_and_isSeparable_iff_isUnramifiedAt k F P').mp
          ⟨hP.ramificationIdx_eq_one hP', hP.isSeparable hP'⟩)
    have hval := (mem_traceDual_iff_forall_valuation_le k F hF.finite_extension P).mp hmem P' hP'
    rw [hd0, Nat.cast_zero, WithZero.exp_zero] at hval
    exact P'.mem_integers_iff.mpr hval
  obtain ⟨d₁, hd₁⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.discr_isIntegral F hb_int)
  obtain ⟨d₂, hd₂⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.discr_isIntegral F hbdual_int)
  have hnn₁ : 0 ≤ P.ord (Algebra.discr F b) :=
    P.mem_integers_iff_ord_nonneg.mp (by rw [← hd₁]; exact d₁.2)
  have hnn₂ : 0 ≤ P.ord (Algebra.discr F b.traceDual) :=
    P.mem_integers_iff_ord_nonneg.mp (by rw [← hd₂]; exact d₂.2)
  have hsum : P.ord (Algebra.discr F b) + P.ord (Algebra.discr F b.traceDual) = 0 := by
    rw [← P.ord_mul (Algebra.discr_not_zero_of_basis F b)
      (Algebra.discr_not_zero_of_basis F b.traceDual), b.discr_mul_discr_traceDual, P.ord_one]
  omega

/-- **At an unramified place, the local integral basis has unit discriminant**:
`ord_P(disc (localIntegralBasis E P)) = 0`. -/
theorem ord_discr_localIntegralBasis_eq_zero (hF : IsFunctionField k F) {P : Place k F}
    (hP : P.IsUnramified (k' := k) (F' := E)) :
    P.ord (Algebra.discr F (localIntegralBasis E P)) = 0 := by
  classical
  exact (isIntegralBasis_localIntegralBasis E P).ord_discr_eq_zero hF hP

end Place

end TauCeti
