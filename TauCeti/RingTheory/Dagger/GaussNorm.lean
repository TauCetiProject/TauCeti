/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WashnitzerAlgebra

/-!
# The Gauss norm on overconvergent series

The Monsky–Washnitzer algebra carries the unit-radius Gauss norm, induced by its inclusion
into the Tate algebra. This makes it an ultrametric normed commutative ring, with
multiplicative norm when the coefficient norm is multiplicative. Over a normed field it is
a normed algebra. This is the norm used to form residue norms of dagger algebras.

The inclusion `toTate` is an isometry. Coefficient bounds characterize the norm, constants
retain their norm, and the variables have norm one. Polynomials are dense for this norm.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- The unit-radius Gauss norm on overconvergent power series. -/
noncomputable instance : NormedCommRing (washnitzerAlgebra σ R) :=
  NormedCommRing.induced _ _ (toTate σ R) toTate_injective

/-- The inclusion into the Tate algebra preserves the Gauss norm. -/
@[simp]
theorem norm_toTate (f : washnitzerAlgebra σ R) : ‖toTate σ R f‖ = ‖f‖ := (rfl)

/-- The norm on the Monsky–Washnitzer algebra is the unit-radius Gauss norm. -/
theorem norm_eq_gaussNorm (f : washnitzerAlgebra σ R) :
    ‖f‖ = MvPowerSeries.gaussNorm norm (fun _ ↦ 1) (f : MvPowerSeries σ R) := by
  rw [← norm_toTate, MvPowerSeries.norm_eq_gaussNorm, coe_toTate]

/-- The inclusion into the Tate algebra is an isometry for the Gauss norms. -/
theorem isometry_toTate : Isometry (toTate σ R) :=
  AddMonoidHomClass.isometry_of_norm _ norm_toTate

/-- The Gauss norm on overconvergent series is ultrametric. -/
instance : IsUltrametricDist (washnitzerAlgebra σ R) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g ↦ by
    simpa only [← norm_toTate, map_add] using
      IsUltrametricDist.norm_add_le_max (toTate σ R f) (toTate σ R g)

/-- The Gauss norm is multiplicative when the coefficient norm is. -/
instance [NormMulClass R] : NormMulClass (washnitzerAlgebra σ R) :=
  NormMulClass.induced _ _ (toTate σ R)

/-- The Gauss norm of one agrees with that of the coefficient ring. -/
instance [NormOneClass R] : NormOneClass (washnitzerAlgebra σ R) :=
  NormOneClass.induced _ _ (toTate σ R)

/-- Every coefficient is bounded by the Gauss norm of an overconvergent series. -/
theorem norm_coeff_le (f : washnitzerAlgebra σ R) (t : σ →₀ ℕ) :
    ‖coeff t (f : MvPowerSeries σ R)‖ ≤ ‖f‖ := by
  simpa [Finsupp.prod_pow_eq_pow_degree] using
    MvPowerSeries.norm_coeff_mul_prod_le (toTate σ R f) t

/-- A nonnegative bound on the Gauss norm is equivalent to the same bound on all coefficients. -/
theorem norm_le_iff {f : washnitzerAlgebra σ R} {r : ℝ} (hr : 0 ≤ r) :
    ‖f‖ ≤ r ↔ ∀ t, ‖coeff t (f : MvPowerSeries σ R)‖ ≤ r := by
  simpa [Finsupp.prod_pow_eq_pow_degree] using
    (MvPowerSeries.norm_le_iff (f := toTate σ R f) hr)

/-- A strict bound on the Gauss norm is equivalent to a strict bound on all coefficients. -/
theorem norm_lt_iff {f : washnitzerAlgebra σ R} {r : ℝ} :
    ‖f‖ < r ↔ ∀ t, ‖coeff t (f : MvPowerSeries σ R)‖ < r := by
  simpa [Finsupp.prod_pow_eq_pow_degree] using
    (MvPowerSeries.norm_lt_iff (f := toTate σ R f) (r := r))

/-- Constants retain their coefficient norm. -/
@[simp]
theorem norm_algebraMap (a : R) : ‖algebraMap R (washnitzerAlgebra σ R) a‖ = ‖a‖ := by
  rw [← norm_toTate, AlgHom.commutes, MvPowerSeries.norm_algebraMap_isRestrictedSubring]

/-- Each coordinate variable has Gauss norm one. -/
@[simp]
theorem norm_X [NormOneClass R] (i : σ) : ‖X σ R i‖ = 1 := by
  rw [← norm_toTate]
  have h : toTate σ R (X σ R i) =
      ⟨MvPowerSeries.X i, isRestricted_X _ i⟩ := Subtype.ext (by simp)
  rw [h, MvPowerSeries.norm_X]

/-- Polynomials are dense in the Monsky–Washnitzer algebra for the Gauss norm. -/
theorem denseRange_ofMvPolynomial : DenseRange (ofMvPolynomial σ R) := by
  have hd : DenseRange ((toTate σ R).comp (ofMvPolynomial σ R)) := by
    apply (MvPowerSeries.dense_closure_monomial (c := fun _ : σ ↦ (1 : ℝ))
      (R := R) (s := Set.univ) dense_univ).mono
    apply (AddSubgroup.closure_le
      ((toTate σ R).comp (ofMvPolynomial σ R)).range.toSubring.toAddSubgroup).mpr
    rintro _ ⟨⟨t, a⟩, _, rfl⟩
    exact ⟨MvPolynomial.monomial t a, Subtype.ext (by simp)⟩
  exact isometry_toTate.isEmbedding.isInducing.dense_iff.mpr fun f ↦ by
    simpa only [← Set.range_comp, ← AlgHom.coe_comp] using hd (toTate σ R f)

section NormedAlgebra

variable {K : Type*} [NormedField K] [NormedAlgebra K R]

/-- Overconvergent series over a normed algebra carry the induced normed-algebra structure. -/
noncomputable instance : NormedAlgebra K (washnitzerAlgebra σ R) :=
  NormedAlgebra.induced K _ _ ((toTate σ R).restrictScalars K)

end NormedAlgebra

end TauCeti.Dagger.washnitzerAlgebra
