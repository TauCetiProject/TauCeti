/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.PosDef
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Topology.Instances.Matrix

/-!
# Inversion and the change of variables on the positive-definite cone

The inverse of a symmetric matrix is symmetric, so matrix inversion is a self-map
`TauCeti.symmetricInv` of the symmetric subspace, and an involution of the positive-definite cone.
Its derivative at an invertible `A` is `H ↦ -A⁻¹ H A⁻¹`, that is, minus the congruence by `A⁻¹`,
whose determinant `Matrix.det_symmetricCongruenceLinearMap` already computes. Hence the absolute
Jacobian of inversion is `|det A| ^ (-(p + 1))`, and
`TauCeti.map_symmetricInv_symmetricLebesgue` records the resulting change of variables: inversion
carries `TauCeti.symmetricLebesgue` restricted to the cone to the same restriction weighted by
`(det B) ^ (-(p + 1))`.

This is the change of variables behind the inverse-Wishart density: it reads the density of the
image of a Wishart law under inversion off the density of the law itself.

## Main declarations

* `TauCeti.symmetricInv` — matrix inversion as a self-map of the symmetric subspace.
* `TauCeti.hasFDerivAt_symmetricInv` — its derivative at an invertible matrix is minus the
  congruence by the inverse.
* `TauCeti.map_symmetricInv_symmetricLebesgue` — the change of variables on the
  positive-definite cone.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapter 2
  (the Jacobian of symmetric inversion and the inverse-Wishart density).
-/

public section

noncomputable section

open MeasureTheory Module

open scoped Matrix ENNReal

namespace TauCeti

variable {p : ℕ}

/-! ### Inversion as a self-map of the symmetric subspace -/

/-- Matrix inversion as a self-map of the symmetric subspace. Mathlib's totalized inverse is zero
on singular matrices and that value is kept here; on the positive-definite cone, where the
Wishart laws live, the map is an involution. -/
def symmetricInv (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
  ⟨(A : Matrix (Fin p) (Fin p) ℝ)⁻¹,
    Matrix.isHermitian_iff_isSelfAdjoint.1 (selfAdjoint.isHermitian_coe A).inv⟩

/-- The underlying matrix of the inverse is the inverse of the underlying matrix. -/
@[simp]
theorem coe_symmetricInv (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (symmetricInv A : Matrix (Fin p) (Fin p) ℝ) = (A : Matrix (Fin p) (Fin p) ℝ)⁻¹ :=
  (rfl)

/-- Inversion is an involution at an invertible matrix. -/
@[simp]
theorem symmetricInv_symmetricInv {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hA : (A : Matrix (Fin p) (Fin p) ℝ).det ≠ 0) : symmetricInv (symmetricInv A) = A :=
  Subtype.ext <| by
    rw [coe_symmetricInv, coe_symmetricInv, Matrix.nonsing_inv_nonsing_inv _ hA.isUnit]

/-- The inverse of a positive-definite symmetric matrix is positive definite. -/
theorem posDef_coe_symmetricInv {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hA : (A : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    (symmetricInv A : Matrix (Fin p) (Fin p) ℝ).PosDef :=
  hA.inv

/-- Inversion is measurable, being a rational expression in the entries: Mathlib's totalized
inverse is `(det A)⁻¹ • adjugate A` everywhere. -/
@[fun_prop]
theorem measurable_symmetricInv : Measurable (symmetricInv (p := p)) := by
  refine Measurable.subtype_mk ?_
  have hdet : Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (A : Matrix (Fin p) (Fin p) ℝ).det :=
    continuous_subtype_val.matrix_det.measurable
  have hadj : Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (A : Matrix (Fin p) (Fin p) ℝ).adjugate :=
    continuous_subtype_val.matrix_adjugate.measurable
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact hdet.inv.smul hadj

/-! ### The derivative of inversion -/

open scoped Matrix.Norms.Frobenius in
/-- The derivative of inversion at an invertible symmetric matrix `A` is `H ↦ -A⁻¹ H A⁻¹`, minus
the congruence by `A⁻¹`. -/
theorem hasFDerivAt_symmetricInv {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hA : IsUnit (A : Matrix (Fin p) (Fin p) ℝ).det) :
    HasFDerivAt symmetricInv
      (-(Matrix.symmetricCongruenceLinearMap
        ((A : Matrix (Fin p) (Fin p) ℝ)⁻¹)).toContinuousLinearMap) A := by
  have hAT : (A : Matrix (Fin p) (Fin p) ℝ)ᵀ = (A : Matrix (Fin p) (Fin p) ℝ) :=
    (Matrix.isHermitian_iff_isSymm.1 (selfAdjoint.isHermitian_coe A)).eq
  -- The ambient inversion is differentiable at `A`, with derivative `H ↦ -A⁻¹ H A⁻¹`.
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det (A : Matrix (Fin p) (Fin p) ℝ)).2 hA
  have hu' : ((u⁻¹ : (Matrix (Fin p) (Fin p) ℝ)ˣ) : Matrix (Fin p) (Fin p) ℝ) =
      (A : Matrix (Fin p) (Fin p) ℝ)⁻¹ := by
    rw [Matrix.coe_units_inv, hu]
  have hambient : HasFDerivAt (Ring.inverse (M₀ := Matrix (Fin p) (Fin p) ℝ))
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin p) (Fin p) ℝ)
        ((A : Matrix (Fin p) (Fin p) ℝ)⁻¹) ((A : Matrix (Fin p) (Fin p) ℝ)⁻¹))
      (A : Matrix (Fin p) (Fin p) ℝ) := by
    have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rwa [hu', hu] at h
  -- Restrict the source to the symmetric subspace and corestrict the target along the symmetric
  -- part, which is the identity on symmetric matrices.
  set ι : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →L[ℝ] Matrix (Fin p) (Fin p) ℝ :=
    LinearMap.toContinuousLinearMap
      (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)).subtype with hι
  set π : Matrix (Fin p) (Fin p) ℝ →L[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
    LinearMap.toContinuousLinearMap (selfAdjointPart ℝ)
  -- Mathlib states `selfAdjointPart` into the additive subgroup `selfAdjoint`, which carries the
  -- same subtype and the same module structure as `selfAdjoint.submodule`; Mathlib itself reads
  -- the two interchangeably, as in `selfAdjointPart_comp_subtype_selfAdjoint`. Its lemmas
  -- therefore apply to `π` after `Subtype.ext`.
  have hπ_apply : ∀ X : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
      π (X : Matrix (Fin p) (Fin p) ℝ) = X := fun X =>
    Subtype.ext (IsSelfAdjoint.coe_selfAdjointPart_apply ℝ X.2)
  have hπ_coe : ∀ M : Matrix (Fin p) (Fin p) ℝ,
      (π M : Matrix (Fin p) (Fin p) ℝ) = (2 : ℝ)⁻¹ • (M + Mᵀ) := fun M => by
    have h : (π M : Matrix (Fin p) (Fin p) ℝ) = (⅟2 : ℝ) • (M + star M) :=
      selfAdjointPart_apply_coe ℝ M
    rw [h, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      invOf_eq_inv]
  have hι_apply : ∀ X : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
      ι X = (X : Matrix (Fin p) (Fin p) ℝ) := fun X => by
    rw [hι, LinearMap.coe_toContinuousLinearMap', Submodule.subtype_apply]
  have hcomp : HasFDerivAt (fun X : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      π (Ring.inverse (ι X)))
      (π.comp (((-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin p) (Fin p) ℝ)
        ((A : Matrix (Fin p) (Fin p) ℝ)⁻¹) ((A : Matrix (Fin p) (Fin p) ℝ)⁻¹)).comp ι))) A :=
    π.hasFDerivAt.comp A (hambient.comp A ι.hasFDerivAt)
  have hfun : (fun X : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      π (Ring.inverse (ι X))) = symmetricInv := by
    funext X
    rw [hι_apply, ← Matrix.nonsing_inv_eq_ringInverse, ← coe_symmetricInv X, hπ_apply]
  rw [hfun] at hcomp
  refine hcomp.congr_fderiv (ContinuousLinearMap.ext fun H => ?_)
  have hHT : (H : Matrix (Fin p) (Fin p) ℝ)ᵀ = (H : Matrix (Fin p) (Fin p) ℝ) :=
    (Matrix.isHermitian_iff_isSymm.1 (selfAdjoint.isHermitian_coe H)).eq
  -- Both sides are the symmetric part of `-A⁻¹ H A⁻¹`: on the left the composite of continuous
  -- linear maps evaluates to it definitionally, and on the right the matrix is already symmetric.
  have hvalue : π (-((A : Matrix (Fin p) (Fin p) ℝ)⁻¹ *
        (H : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)⁻¹)) =
      -(Matrix.symmetricCongruenceLinearMap
        ((A : Matrix (Fin p) (Fin p) ℝ)⁻¹)).toContinuousLinearMap H := by
    refine Subtype.ext ?_
    simp only [hπ_coe, LinearMap.coe_toContinuousLinearMap',
      NegMemClass.coe_neg, Matrix.coe_symmetricCongruenceLinearMap_apply, Matrix.transpose_neg,
      Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hAT, hHT, Matrix.mul_assoc]
    module
  exact hvalue

/-- The absolute Jacobian of inversion at an invertible symmetric matrix `A` is
`|det A| ^ (-(p + 1))`. -/
theorem abs_det_fderiv_symmetricInv {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hA : IsUnit (A : Matrix (Fin p) (Fin p) ℝ).det) :
    |(fderiv ℝ symmetricInv A).det| = |(A : Matrix (Fin p) (Fin p) ℝ).det| ^ (-((p : ℝ) + 1)) := by
  have habs : 0 < |(A : Matrix (Fin p) (Fin p) ℝ).det| := abs_pos.2 hA.ne_zero
  have hcoe : (fderiv ℝ symmetricInv A).det =
      LinearMap.det (-Matrix.symmetricCongruenceLinearMap
        ((A : Matrix (Fin p) (Fin p) ℝ)⁻¹)) := by
    rw [(hasFDerivAt_symmetricInv hA).fderiv, ContinuousLinearMap.det,
      ContinuousLinearMap.toLinearMap_neg, LinearMap.coe_toContinuousLinearMap]
  have hrpow : |(A : Matrix (Fin p) (Fin p) ℝ).det| ^ (-((p : ℝ) + 1)) =
      |(A : Matrix (Fin p) (Fin p) ℝ).det|⁻¹ ^ (p + 1) := by
    rw [show -((p : ℝ) + 1) = -((p + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg habs.le,
      Real.rpow_natCast, ← inv_pow]
  rw [hcoe, hrpow, ← neg_one_smul ℝ (Matrix.symmetricCongruenceLinearMap
      ((A : Matrix (Fin p) (Fin p) ℝ)⁻¹)), LinearMap.det_smul,
    Matrix.det_symmetricCongruenceLinearMap, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  simp [abs_mul, abs_pow, abs_inv]

/-! ### The change of variables -/

/-- **The change of variables for inversion on the positive-definite cone.** The pushforward of
`TauCeti.symmetricLebesgue` restricted to the cone under inversion is the same restriction
weighted by `(det B) ^ (-(p + 1))`. This is what turns the Wishart density into the
inverse-Wishart density. -/
theorem map_symmetricInv_symmetricLebesgue (p : ℕ) :
    ((symmetricLebesgue p).restrict
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosDef}).map symmetricInv =
      ((symmetricLebesgue p).restrict
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosDef}).withDensity
        fun B => ENNReal.ofReal ((B : Matrix (Fin p) (Fin p) ℝ).det ^ (-((p : ℝ) + 1))) := by
  set s : Set (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
    {A | (A : Matrix (Fin p) (Fin p) ℝ).PosDef}
  set g : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) → ℝ≥0∞ :=
    fun B => ENNReal.ofReal ((B : Matrix (Fin p) (Fin p) ℝ).det ^ (-((p : ℝ) + 1))) with hg_def
  have hs : MeasurableSet s := measurableSet_posDefMatrix p
  have hdet : ∀ A ∈ s, (A : Matrix (Fin p) (Fin p) ℝ).det ≠ 0 := fun _ hA =>
    (Matrix.PosDef.det_pos hA).ne'
  have himg : symmetricInv '' s = s := by
    refine Set.Subset.antisymm ?_ fun A hA => ⟨symmetricInv A, posDef_coe_symmetricInv hA, ?_⟩
    · rintro _ ⟨A, hA, rfl⟩
      exact posDef_coe_symmetricInv hA
    · exact symmetricInv_symmetricInv (hdet A hA)
  have hinj : Set.InjOn symmetricInv s := fun A hA B hB h => by
    rw [← symmetricInv_symmetricInv (hdet A hA), h, symmetricInv_symmetricInv (hdet B hB)]
  have hderiv : ∀ A ∈ s, HasFDerivWithinAt symmetricInv (fderiv ℝ symmetricInv A) s A :=
    fun A hA => by
      rw [(hasFDerivAt_symmetricInv (hdet A hA).isUnit).fderiv]
      exact (hasFDerivAt_symmetricInv (hdet A hA).isUnit).hasFDerivWithinAt
  have key := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar (symmetricLebesgue p)
    hs.nullMeasurableSet hderiv hinj
  rw [himg] at key
  -- On the cone the Jacobian weight is the asserted density.
  have hweight : ((symmetricLebesgue p).restrict s).withDensity
      (fun A => ENNReal.ofReal |(fderiv ℝ symmetricInv A).det|) =
      ((symmetricLebesgue p).restrict s).withDensity g :=
    withDensity_congr_ae <| (ae_restrict_mem hs).mono fun A hA => by
      simp only [hg_def, abs_det_fderiv_symmetricInv (hdet A hA).isUnit,
        abs_of_pos (Matrix.PosDef.det_pos hA)]
  rw [hweight] at key
  -- Inversion is an involution on the cone, so applying it to both sides of `key` inverts it.
  have hmem : ∀ᵐ A ∂((symmetricLebesgue p).restrict s).withDensity g, A ∈ s :=
    (withDensity_absolutelyContinuous _ g).ae_le (ae_restrict_mem hs)
  have hinvol : symmetricInv ∘ symmetricInv
      =ᵐ[((symmetricLebesgue p).restrict s).withDensity g] id :=
    hmem.mono fun A hA => symmetricInv_symmetricInv (hdet A hA)
  calc ((symmetricLebesgue p).restrict s).map symmetricInv
      = ((((symmetricLebesgue p).restrict s).withDensity g).map symmetricInv).map symmetricInv := by
        rw [key]
    _ = (((symmetricLebesgue p).restrict s).withDensity g).map (symmetricInv ∘ symmetricInv) :=
        Measure.map_map measurable_symmetricInv measurable_symmetricInv
    _ = ((symmetricLebesgue p).restrict s).withDensity g := by
        rw [Measure.map_congr hinvol, Measure.map_id]

end TauCeti
