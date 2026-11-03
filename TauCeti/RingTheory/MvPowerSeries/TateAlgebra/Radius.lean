/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map

/-!
# Restriction to smaller polyradii

A series restricted at polyradii `s` is restricted at any nonnegative polyradii `r ≤ s`.
The resulting ring homomorphism leaves the coefficients unchanged. At positive polyradii
it is injective, contractive for the Gauss norms, and has dense image: every polynomial
extends to the larger polydisc. No finiteness of the variable set or completeness of the
coefficient ring is required.

The restriction maps compose and commute with bounded coefficient maps and variable
renaming. For commutative coefficients they are coefficient-algebra homomorphisms and, at
positive polyradii, continuous linear maps.
These maps compare algebras of functions on nested closed polydiscs.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

namespace TauCeti.MvPowerSeries

open Filter _root_.MvPowerSeries

section Restrictedness

variable {σ R : Type*} [NormedRing R] {r s : σ → ℝ}

/-- Restrictedness passes to smaller nonnegative polyradii. -/
theorem isRestricted_of_le {f : MvPowerSeries σ R} (hf : IsRestricted s f)
    (hr : ∀ i, 0 ≤ r i) (hrs : r ≤ s) : IsRestricted r f := by
  refine squeeze_zero (fun t ↦ mul_nonneg (norm_nonneg _) ?_) (fun t ↦ ?_) hf
  · exact Finset.prod_nonneg fun i _ ↦ pow_nonneg (hr i) _
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Finset.prod_le_prod₀ (fun i _ ↦ pow_nonneg (hr i) _) fun i _ ↦
      pow_le_pow_left₀ (hr i) (hrs i) _

end Restrictedness

section Ring

variable {σ R : Type*} [NormedRing R] [IsUltrametricDist R] {r s t : σ → ℝ}
  (hr : ∀ i, 0 ≤ r i) (hrs : r ≤ s)

/-- Restrict a series to smaller nonnegative polyradii, leaving its coefficients unchanged. -/
noncomputable def restrictedRadiusHom :
    IsRestricted.subring (R := R) s →+* IsRestricted.subring (R := R) r :=
  Subring.inclusion fun _ hf ↦ isRestricted_of_le hf hr hrs

/-- Radius restriction leaves the underlying formal series unchanged. -/
@[simp]
theorem coe_restrictedRadiusHom (f : IsRestricted.subring (R := R) s) :
    (restrictedRadiusHom hr hrs f : MvPowerSeries σ R) = f :=
  Subring.coe_inclusion _ f

/-- Radius restriction is injective. -/
theorem restrictedRadiusHom_injective :
    Function.Injective (restrictedRadiusHom (R := R) hr hrs) :=
  Subring.inclusion_injective _

/-- Restriction to the same radii is the identity. -/
@[simp]
theorem restrictedRadiusHom_refl :
    restrictedRadiusHom (R := R) hr le_rfl = RingHom.id _ :=
  RingHom.ext fun _ ↦ Subtype.ext (by simp)

/-- Restriction along nested polyradii is the composite of the two restrictions. -/
theorem restrictedRadiusHom_comp (hs : ∀ i, 0 ≤ s i) (hst : s ≤ t) :
    (restrictedRadiusHom (R := R) hr hrs).comp (restrictedRadiusHom hs hst) =
      restrictedRadiusHom hr (hrs.trans hst) :=
  RingHom.ext fun _ ↦ Subtype.ext (by simp)

/-- Restricting twice agrees with direct restriction. -/
@[simp]
theorem restrictedRadiusHom_restrictedRadiusHom (hs : ∀ i, 0 ≤ s i) (hst : s ≤ t)
    (f : IsRestricted.subring (R := R) t) :
    restrictedRadiusHom hr hrs (restrictedRadiusHom hs hst f) =
      restrictedRadiusHom hr (hrs.trans hst) f :=
  DFunLike.congr_fun (restrictedRadiusHom_comp hr hrs hs hst) f

/-- Radius restriction commutes with bounded maps of coefficients. -/
theorem restrictedRadiusHom_restrictedMap {S : Type*} [NormedRing S] [IsUltrametricDist S]
    (φ : R →+* S) {C : ℝ} (hφ : ∀ a, ‖φ a‖ ≤ C * ‖a‖)
    (f : IsRestricted.subring (R := R) s) :
    restrictedRadiusHom hr hrs (restrictedMap φ hφ f) =
      restrictedMap φ hφ (restrictedRadiusHom hr hrs f) := by
  apply Subtype.ext
  simp only [coe_restrictedRadiusHom, coe_restrictedMap]

section Norm

variable [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)]

/-- Radius restriction is contractive for the Gauss norms. -/
theorem norm_restrictedRadiusHom_le (f : IsRestricted.subring (R := R) s) :
    ‖restrictedRadiusHom hr hrs f‖ ≤ ‖f‖ := by
  rw [norm_le_iff (norm_nonneg f)]
  intro n
  rw [coe_restrictedRadiusHom]
  refine le_trans ?_ (norm_coeff_mul_prod_le f n)
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Finset.prod_le_prod₀ (fun i _ ↦ pow_nonneg (hr i) _) fun i _ ↦
    pow_le_pow_left₀ (hr i) (hrs i) _

/-- Radius restriction is a Lipschitz map with constant one. -/
theorem lipschitzWith_restrictedRadiusHom :
    LipschitzWith 1 (restrictedRadiusHom (R := R) hr hrs) := by
  simpa only [Real.toNNReal_one] using
    AddMonoidHomClass.lipschitz_of_bound (restrictedRadiusHom (R := R) hr hrs) 1
      (fun f ↦ by simpa only [one_mul] using norm_restrictedRadiusHom_le hr hrs f)

/-- Radius restriction is continuous in the Gauss norm topologies. -/
@[continuity]
theorem continuous_restrictedRadiusHom : Continuous (restrictedRadiusHom (R := R) hr hrs) :=
  (lipschitzWith_restrictedRadiusHom hr hrs).continuous

omit [∀ i, Fact (0 < s i)] in
/-- Radius restriction has dense image, since every restricted monomial extends to any radii. -/
theorem denseRange_restrictedRadiusHom : DenseRange (restrictedRadiusHom (R := R) hr hrs) := by
  apply (dense_closure_monomial (c := r) (s := Set.univ) dense_univ).mono
  apply (AddSubgroup.closure_le (restrictedRadiusHom (R := R) hr hrs).range.toAddSubgroup).mpr
  rintro _ ⟨⟨n, a⟩, _, rfl⟩
  exact ⟨⟨monomial n a, isRestricted_monomial s n a⟩, Subtype.ext (by simp)⟩

end Norm

end Ring

section Algebra

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] {r s : σ → ℝ}
  (hr : ∀ i, 0 ≤ r i) (hrs : r ≤ s)

/-- Radius restriction as a homomorphism of coefficient algebras. -/
noncomputable def restrictedRadiusAlgHom :
    IsRestricted.subring (R := R) s →ₐ[R] IsRestricted.subring (R := R) r where
  __ := restrictedRadiusHom hr hrs
  commutes' a := Subtype.ext (by simp)

/-- The algebra homomorphism of radius restriction has the same underlying ring map. -/
@[simp]
theorem coe_restrictedRadiusAlgHom :
    (restrictedRadiusAlgHom (R := R) hr hrs :
      IsRestricted.subring (R := R) s →+* IsRestricted.subring (R := R) r) =
        restrictedRadiusHom hr hrs := (rfl)

/-- The algebra form of radius restriction agrees with its ring form on each series. -/
@[simp]
theorem restrictedRadiusAlgHom_apply (f : IsRestricted.subring (R := R) s) :
    restrictedRadiusAlgHom hr hrs f = restrictedRadiusHom hr hrs f := (rfl)

/-- Polynomial inclusion commutes with radius restriction. -/
@[simp]
theorem restrictedRadiusHom_polynomial (p : MvPolynomial σ R) :
    restrictedRadiusHom hr hrs ⟨(p : MvPowerSeries σ R), p.isRestricted s⟩ =
      ⟨(p : MvPowerSeries σ R), p.isRestricted r⟩ :=
  Subtype.ext (by simp)

/-- Radius restriction commutes with renaming variables along an equivalence. -/
theorem restrictedRadiusHom_renameAlgEquiv {τ : Type*} (e : τ ≃ σ)
    (f : IsRestricted.subring (R := R) (s ∘ e)) :
    restrictedRadiusHom hr hrs (IsRestricted.renameAlgEquiv e s f) =
      IsRestricted.renameAlgEquiv e r
        (restrictedRadiusHom (fun i ↦ hr (e i)) (fun i ↦ hrs (e i)) f) := by
  apply Subtype.ext
  simp only [coe_restrictedRadiusHom, IsRestricted.coe_renameAlgEquiv]

end Algebra

section ContinuousLinearMap

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] {r s : σ → ℝ}
  [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)]

/-- Radius restriction as a continuous linear map over the coefficient ring. It is contractive
for the Gauss norms (`TauCeti.MvPowerSeries.norm_restrictedRadiusHom_le`). -/
noncomputable def restrictedRadiusCLM (hrs : r ≤ s) :
    IsRestricted.subring (R := R) s →L[R] IsRestricted.subring (R := R) r where
  toLinearMap := (restrictedRadiusAlgHom (fun i ↦ (Fact.out : 0 < r i).le) hrs).toLinearMap
  cont := continuous_restrictedRadiusHom (fun i ↦ (Fact.out : 0 < r i).le) hrs

/-- The continuous linear form of radius restriction agrees with its ring form. -/
@[simp]
theorem restrictedRadiusCLM_apply (hrs : r ≤ s) (f : IsRestricted.subring (R := R) s) :
    restrictedRadiusCLM hrs f = restrictedRadiusHom (fun i ↦ (Fact.out : 0 < r i).le) hrs f :=
  (rfl)

end ContinuousLinearMap

end TauCeti.MvPowerSeries
