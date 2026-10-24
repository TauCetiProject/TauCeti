/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.AbsoluteValue.FractionRing
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs

/-!
# The Gauss-normed fraction field of a Tate algebra

`GaussFractionField σ K c` is Mathlib's fraction field of the native Tate algebra at
positive polyradius `c`, equipped with the extended Gauss norm through `WithAbs`. Its norm is
multiplicative and ultrametric, and both the Tate algebra and coefficient field embed isometrically.
For an empty variable type the coefficient embedding is an algebra equivalence.

This is the normed fraction field, not its completion. Neither completeness of the coefficient
field nor finiteness of the variable type is needed for the construction.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.3.1, for the Gauss-normed
  fraction field used in weak stability.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable (σ K : Type*) [NormedField K] [IsUltrametricDist K]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)]

local notation "Tate" => IsRestricted.subring (R := K) c

/-- The absolute value on the fraction field extending the native multiplicative Gauss norm. -/
noncomputable def gaussFractionNorm : AbsoluteValue (FractionRing Tate) ℝ :=
  fractionRingAbsoluteValue (R := Tate) (FractionRing Tate)
    (IsAbsoluteValue.toAbsoluteValue (norm : Tate → ℝ))

/-- The extended Gauss norm restricts to the original Gauss norm. -/
@[simp]
theorem gaussFractionNorm_algebraMap (f : Tate) :
    gaussFractionNorm σ K c (algebraMap Tate (FractionRing Tate) f) = ‖f‖ := by
  simp [gaussFractionNorm]

/-- The extended Gauss norm is nonarchimedean. -/
theorem isNonarchimedean_gaussFractionNorm : IsNonarchimedean (gaussFractionNorm σ K c) := by
  unfold gaussFractionNorm
  exact isNonarchimedean_fractionRingAbsoluteValue _ _
    (fun f g ↦ IsUltrametricDist.norm_add_le_max f g)

/-- The fraction field of a Tate algebra with the extended Gauss norm, without completion. -/
abbrev GaussFractionField := WithAbs (gaussFractionNorm σ K c)

instance : IsFractionRing Tate (GaussFractionField σ K c) :=
  IsFractionRing.of_algEquiv (WithAbs.algEquiv Tate (gaussFractionNorm σ K c)).symm

/-- The norm on the Tate algebra is unchanged by its embedding in the fraction field. -/
@[simp]
theorem norm_algebraMap_gaussFractionField (f : Tate) :
    ‖algebraMap Tate (GaussFractionField σ K c) f‖ = ‖f‖ := by
  rw [WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq, gaussFractionNorm_algebraMap]

/-- The Tate algebra embeds isometrically into its Gauss-normed fraction field. -/
theorem isometry_algebraMap_gaussFractionField :
    Isometry (algebraMap Tate (GaussFractionField σ K c)) :=
  (AddMonoidHomClass.isometry_iff_norm _).mpr (norm_algebraMap_gaussFractionField σ K c)

instance : IsUltrametricDist (GaussFractionField σ K c) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simpa only [WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_add] using
      isNonarchimedean_gaussFractionNorm σ K c x.ofAbs y.ofAbs

noncomputable instance : NormedAlgebra K (GaussFractionField σ K c) where
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul,
      IsScalarTower.algebraMap_apply K Tate (GaussFractionField σ K c),
      norm_algebraMap_gaussFractionField, norm_algebraMap_isRestrictedSubring]

section Empty

variable [IsEmpty σ]

/-- With no variables, every fraction is the image of a coefficient. -/
theorem surjective_algebraMap_gaussFractionField :
    Function.Surjective (algebraMap K (GaussFractionField σ K c)) := by
  intro x
  obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective Tate x
  obtain ⟨a, ha⟩ := C_surjective (f : _root_.MvPowerSeries σ K)
  obtain ⟨b, hb⟩ := C_surjective (g : _root_.MvPowerSeries σ K)
  have hf : f = algebraMap K Tate a := Subtype.ext ha.symm
  have hg : g = algebraMap K Tate b := Subtype.ext hb.symm
  refine ⟨a / b, ?_⟩
  simp only [hf, hg, ← IsScalarTower.algebraMap_apply, map_div₀]

/-- With no variables, the Gauss-normed fraction field is the coefficient field. -/
noncomputable def gaussFractionFieldIsEmptyAlgEquiv : GaussFractionField σ K c ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K (GaussFractionField σ K c))
    ⟨(algebraMap K (GaussFractionField σ K c)).injective,
      surjective_algebraMap_gaussFractionField σ K c⟩).symm

/-- The inverse zero-variable comparison is the coefficient embedding. -/
@[simp]
theorem gaussFractionFieldIsEmptyAlgEquiv_symm_apply (a : K) :
    (gaussFractionFieldIsEmptyAlgEquiv σ K c).symm a =
      algebraMap K (GaussFractionField σ K c) a :=
  AlgEquiv.ofBijective_apply _
    ⟨(algebraMap K (GaussFractionField σ K c)).injective,
      surjective_algebraMap_gaussFractionField σ K c⟩ a

end Empty

end TauCeti.MvPowerSeries
