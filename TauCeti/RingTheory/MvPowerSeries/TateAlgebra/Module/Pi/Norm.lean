/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Pi.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Norm

/-!
# Gauss isometries for finite-coordinate restricted modules

Taking restricted series with coefficients in a finite product commutes isometrically with
that product, with its maximum seminorm. The equivalence `Gauss.piLinearIsometryEquiv`
upgrades the algebraic coordinate comparison to the Gauss topologies at every positive real
polyradius. It commutes with bounded coordinate maps and finite-support inclusions.

For ultrametric coefficients the comparison is linear over the restricted-series ring acting
by convolution. In particular, `Gauss.piRingLinearIsometryEquiv` identifies series with
coefficients in a finite free coefficient module with a finite free module over the scalar
restricted algebra, preserving norms. These comparisons provide the norm-compatible free
terms used in presentations of restricted coefficient modules. The variable set can be
arbitrary; neither completeness nor scalars realizing the radii are required. Empty products
are included.

The construction uses the algebraic comparisons in `Module.Pi.Basic` and the weighted Gauss
norm in `Module.Norm`.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

noncomputable section

namespace TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss

open _root_.MvPowerSeries

variable {σ ι R : Type*} [Fintype ι] {E F : ι → Type*}
  [∀ i, SeminormedAddCommGroup (E i)] {c : σ → ℝ} [∀ i, Fact (0 < c i)]

section Coefficients

variable [SeminormedRing R] [∀ i, Module R (E i)] [∀ i, IsBoundedSMul R (E i)]

variable (R c) in
/-- Separating a finite product of coefficient modules is an isometry for the weighted Gauss
seminorm and the maximum product seminorm. -/
def piLinearIsometryEquiv : Gauss c (∀ i, E i) ≃ₗᵢ[R] ∀ i, Gauss c (E i) where
  toLinearEquiv :=
    (toAddSubgroupLinearEquiv R).trans
      ((IsRestrictedFamily.piLinearEquiv R c).trans
        (LinearEquiv.piCongrRight fun _ ↦ (toAddSubgroupLinearEquiv R).symm))
  norm_map' a := by
    simp only [LinearEquiv.trans_apply, toAddSubgroupLinearEquiv_apply]
    let b : ∀ i, Gauss c (E i) :=
      (LinearEquiv.piCongrRight fun _ ↦ (toAddSubgroupLinearEquiv R).symm)
        (IsRestrictedFamily.piLinearEquiv R c a.toAddSubgroup)
    have hb (i : ι) (t : σ →₀ ℕ) : b i t = a t i := by
      simp [b]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr
      intro i
      apply norm_le_iff.mpr
      intro t
      rw [hb]
      exact (mul_le_mul_of_nonneg_right (norm_le_pi_norm (a t) i)
        (prod_pow_pos t).le).trans (norm_coeff_mul_prod_le a t)
    · apply norm_le_iff.mpr
      intro t
      apply (le_div_iff₀ (prod_pow_pos t)).mp
      apply (pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg b) (prod_pow_pos t).le)).mpr
      intro i
      apply (le_div_iff₀ (prod_pow_pos t)).mpr
      rw [← hb]
      exact (norm_coeff_mul_prod_le (b i) t).trans (norm_le_pi_norm b i)

/-- The coordinate isometry takes each coordinate of every coefficient. -/
@[simp]
theorem piLinearIsometryEquiv_apply (a : Gauss c (∀ i, E i)) (i : ι) (t : σ →₀ ℕ) :
    piLinearIsometryEquiv R c a i t = a t i := by
  simp [piLinearIsometryEquiv]

/-- The inverse coordinate isometry assembles the coefficient vectors. -/
@[simp]
theorem piLinearIsometryEquiv_symm_apply (a : ∀ i, Gauss c (E i))
    (t : σ →₀ ℕ) (i : ι) :
    (piLinearIsometryEquiv R c).symm a t i = a i t := by
  have h := congrArg (fun b : ∀ i, Gauss c (E i) ↦ b i t)
    ((piLinearIsometryEquiv R c).apply_symm_apply a)
  simpa only [piLinearIsometryEquiv_apply] using h

/-- Finite-support inclusion commutes with the coordinate isometry. -/
@[simp]
theorem piLinearIsometryEquiv_ofFinsupp (a : (σ →₀ ℕ) →₀ ∀ i, E i) (i : ι) :
    piLinearIsometryEquiv R c (ofFinsupp R c a) i =
      ofFinsupp R c (Finsupp.mapRange.linearMap (LinearMap.proj (R := R) i) a) := by
  ext t
  simp

variable [∀ i, SeminormedAddCommGroup (F i)] [∀ i, Module R (F i)]
  [∀ i, IsBoundedSMul R (F i)]

/-- Bounded coordinate maps commute with separating the coefficient coordinates. A uniform
bound on the coordinate maps bounds their product for the maximum seminorm. -/
theorem piLinearIsometryEquiv_mapLinearMap (φ : ∀ i, E i →ₗ[R] F i) {C : ℝ}
    (hC : 0 ≤ C) (hφ : ∀ i e, ‖φ i e‖ ≤ C * ‖e‖)
    (a : Gauss c (∀ i, E i)) (i : ι) :
    piLinearIsometryEquiv R c
        (mapLinearMap (LinearMap.pi fun i ↦ (φ i).comp (LinearMap.proj i))
          (fun e ↦ (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg e))).mpr
            fun j ↦ (hφ j (e j)).trans
              (mul_le_mul_of_nonneg_left (norm_le_pi_norm e j) hC)) a) i =
      mapLinearMap (φ i) (hφ i) (piLinearIsometryEquiv R c a i) := by
  ext t
  simp

end Coefficients

section Convolution

variable [NormedRing R] [IsUltrametricDist R] [∀ i, IsUltrametricDist (E i)]
  [∀ i, Module R (E i)] [∀ i, IsBoundedSMul R (E i)]

variable (R c) in
/-- The coordinate isometry is linear over the restricted-series ring acting by convolution. -/
def piSeriesLinearIsometryEquiv :
    Gauss c (∀ i, E i) ≃ₗᵢ[IsRestricted.subring (R := R) c] ∀ i, Gauss c (E i) where
  toLinearEquiv :=
    (toAddSubgroupAddEquiv.linearEquiv (IsRestricted.subring (R := R) c)).trans
      ((IsRestrictedFamily.piSeriesLinearEquiv R c).trans
        (LinearEquiv.piCongrRight fun _ ↦
          (toAddSubgroupAddEquiv.linearEquiv (IsRestricted.subring (R := R) c)).symm))
  norm_map' a := by
    convert (piLinearIsometryEquiv (E := E) R c).norm_map a using 2
    ext i t
    simp [piLinearIsometryEquiv]

/-- The restricted-series bundling has the same coordinate map. -/
@[simp]
theorem coe_piSeriesLinearIsometryEquiv :
    ⇑(piSeriesLinearIsometryEquiv (E := E) R c) = piLinearIsometryEquiv R c := by
  funext a
  ext i t
  simp [piSeriesLinearIsometryEquiv]

/-- The inverse restricted-series bundling assembles the same coordinates. -/
@[simp]
theorem coe_piSeriesLinearIsometryEquiv_symm :
    ⇑(piSeriesLinearIsometryEquiv (E := E) R c).symm =
      (piLinearIsometryEquiv (E := E) R c).symm := by
  funext a
  apply (piLinearIsometryEquiv (E := E) R c).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simpa only [coe_piSeriesLinearIsometryEquiv] using
    (piSeriesLinearIsometryEquiv (E := E) R c).apply_symm_apply a

end Convolution

section FiniteFree

variable [NormedRing R] [IsUltrametricDist R]

variable (R c) in
/-- Restricted series with finite free coefficients identify isometrically with a finite free
module over the scalar restricted-series ring. -/
def piRingLinearIsometryEquiv :
    Gauss c (ι → R) ≃ₗᵢ[IsRestricted.subring (R := R) c]
      ι → IsRestricted.subring (R := R) c where
  toLinearEquiv :=
    (toAddSubgroupAddEquiv.linearEquiv (IsRestricted.subring (R := R) c)).trans
      (IsRestrictedFamily.piRingLinearEquiv R c)
  norm_map' a := by
    simp only [LinearEquiv.trans_apply, AddEquiv.linearEquiv_apply,
      toAddSubgroupAddEquiv_apply]
    have h := (piLinearIsometryEquiv (E := fun _ : ι ↦ R) R c).norm_map a
    have heq : (fun i ↦ ofAddSubgroup
        (IsRestrictedFamily.subringLinearEquiv (IsRestrictedFamily.piRingLinearEquiv R c
          a.toAddSubgroup i))) = piLinearIsometryEquiv R c a := by
      ext i t
      simp
    rw [← heq] at h
    have hn (f : IsRestricted.subring (R := R) c) :
        ‖ofAddSubgroup (IsRestrictedFamily.subringLinearEquiv f)‖₊ = ‖f‖₊ :=
      Subtype.ext (norm_subringLinearEquiv f)
    simpa only [Pi.norm_def, hn] using h

/-- Each coordinate scalar series has the indicated coordinate of each coefficient. -/
@[simp]
theorem coeff_piRingLinearIsometryEquiv (a : Gauss c (ι → R)) (i : ι) (t : σ →₀ ℕ) :
    _root_.MvPowerSeries.coeff t (piRingLinearIsometryEquiv R c a i : MvPowerSeries σ R) =
      a t i := by
  simp [piRingLinearIsometryEquiv]

/-- The inverse finite free isometry assembles scalar coefficients into coefficient vectors. -/
@[simp]
theorem piRingLinearIsometryEquiv_symm_apply (a : ι → IsRestricted.subring (R := R) c)
    (t : σ →₀ ℕ) (i : ι) :
    (piRingLinearIsometryEquiv R c).symm a t i =
      _root_.MvPowerSeries.coeff t (a i : MvPowerSeries σ R) := by
  have h := congrArg (fun b : ι → IsRestricted.subring (R := R) c ↦
      _root_.MvPowerSeries.coeff t (b i : MvPowerSeries σ R))
    ((piRingLinearIsometryEquiv R c).apply_symm_apply a)
  simpa only [coeff_piRingLinearIsometryEquiv] using h

end FiniteFree

end TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss
