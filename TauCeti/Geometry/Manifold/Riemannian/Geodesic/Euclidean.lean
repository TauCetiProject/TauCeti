/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory
public import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Geodesics in inner-product spaces

This file identifies the Riemannian geodesics of a finite-dimensional real inner-product space.
Its standard Riemannian metric is constant, so the Levi-Civita connection has vanishing
Christoffel map and affine lines are geodesics. Consequently their maximal intervals are all of
`ℝ`, and the chosen maximal geodesic with initial point `p` and velocity `v` is `t ↦ p + t • v`.

These formulas include the zero-dimensional space. They provide the flat model against which the
domain and value of the Riemannian exponential map can be checked.

## Main results

* `TauCeti.Manifold.christoffelMap_leviCivita_modelSpace`: the Christoffel map of the standard
  Riemannian metric vanishes.
* `TauCeti.Manifold.isGeodesicCurve_add_smul`: an affine line is an all-time geodesic.
* `TauCeti.Manifold.isGeodesicCurve_iff_exists_eq_add_smul`: the geodesics are exactly the
  affine lines.
* `TauCeti.Manifold.geodesicInterval_modelSpace`: every affine initial condition exists for all
  time.
* `TauCeti.Manifold.maximalGeodesic_modelSpace`: the chosen maximal geodesic is the affine line.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 3, §2.
-/

public section

open Bundle CovariantDerivative Function Manifold Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

private theorem leviCivitaConnection_const_apply (u v : F) (x : F) :
    leviCivitaConnection 𝓘(ℝ, F) F (fun _ : F ↦ v) x u = 0 := by
  let C (a : F) : ∀ y : F, TangentSpace 𝓘(ℝ, F) y := fun _ ↦ a
  -- Writing the constant sections dependently keeps all Koszul-formula terms well typed.
  change leviCivitaConnection 𝓘(ℝ, F) F (C v) x (C u x) = 0
  have hconst (a : F) :
      MDiffAt (fun y : F ↦ (TotalSpace.mk' F y (C a y) : TangentBundle 𝓘(ℝ, F) F)) x := by
    simpa only [C] using
      ((contMDiffAt_vectorSpace_iff_contDiffAt (n := (1 : ℕ∞ω))
        (V := fun _ : F ↦ a)).2 contDiffAt_const).mdifferentiableAt one_ne_zero
  -- The inner product of two constant fields is constant, so its differential vanishes.
  have hinner (a b : F) : d% (fun y : F ↦ inner ℝ (C a y) (C b y)) x = 0 :=
    mvfderiv_const (I := 𝓘(ℝ, F)) (c := inner ℝ a b)
  -- Constant fields commute, so every bracket term of the Koszul formula vanishes.
  have hbracket (a b c : F) :
      inner ℝ (C a x) (VectorField.mlieBracket 𝓘(ℝ, F) (C b) (C c) x) = 0 := by
    have h : VectorField.mlieBracket 𝓘(ℝ, F) (C b) (C c) x = 0 := by
      simpa only [C] using TauCeti.mlieBracket_const_modelSpace b c x
    rw [h]
    exact inner_zero_right (𝕜 := ℝ) (C a x)
  let w : F := leviCivitaConnection 𝓘(ℝ, F) F (C v) x (C u x)
  -- `w` abbreviates a tangent vector represented in the model vector space.
  change w = 0
  rw [← inner_self_eq_zero (𝕜 := ℝ)]
  -- Re-expose the dependent constant section so the Koszul formula applies directly.
  change inner ℝ (leviCivitaConnection 𝓘(ℝ, F) F (C v) x (C u x)) (C w x) = 0
  rw [leviCivitaConnection_apply_inner 𝓘(ℝ, F)
    (X := C u) (Y := C v) (Z := C w) (hconst u) (hconst v) (hconst w)]
  simp [hinner, hbracket]

/-- The Levi-Civita connection of the standard Riemannian metric differentiates a constant vector
field to zero. -/
@[simp]
theorem leviCivitaConnection_const_modelSpace (v : F) (x : F) :
    leviCivitaConnection 𝓘(ℝ, F) F (fun _ : F ↦ v) x = 0 := by
  ext u
  simpa using leviCivitaConnection_const_apply (F := F) u v x

/-- The Christoffel map of the standard Riemannian metric on an inner-product space vanishes in
its canonical coordinates. -/
@[simp]
theorem christoffelMap_leviCivita_modelSpace (x : F) :
    christoffelMap (Module.finBasis ℝ F)
      ((leviCivitaConnection 𝓘(ℝ, F) F).isCovariantDerivativeOn
        (s := (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).baseSet)) x = 0 := by
  let b := Module.finBasis ℝ F
  let e := trivializationAt F (TangentSpace 𝓘(ℝ, F)) x
  -- Unfold the two local abbreviations to match the public statement of `christoffelMap`.
  change christoffelMap b
    ((leviCivitaConnection 𝓘(ℝ, F) F).isCovariantDerivativeOn (s := e.baseSet)) x = 0
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F (TangentSpace 𝓘(ℝ, F)) x
  have hframe (i : Fin (finrank ℝ F)) : e.localFrame b i = fun _ : F ↦ b i := by
    funext y
    have hy : y ∈ e.baseSet := by
      -- `e` is the model-space tangent trivialization, whose base set is all of `F`.
      change y ∈ (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).baseSet
      rw [TangentBundle.trivializationAt_baseSet]
      rw [chartAt_self_eq]
      exact mem_univ y
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet _ _ hy,
      Bundle.Trivialization.basisAt, Basis.map_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply, ← e.symmL_apply (R := ℝ) hy]
    -- Its fiber equivalence is the identity on the model vector space.
    change (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).symmL ℝ y (b i) = b i
    rw [TangentBundle.symmL_model_space]
    rfl
  apply ContinuousLinearMap.coe_injective
  apply b.ext
  intro i
  apply ContinuousLinearMap.coe_injective
  apply b.ext
  intro j
  -- Evaluate the bilinear Christoffel map on the chosen basis vectors.
  change christoffelMap b
    ((leviCivitaConnection 𝓘(ℝ, F) F).isCovariantDerivativeOn (s := e.baseSet)) x
      (b i) (b j) = 0
  have hz : (0 : TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x) (b j) = 0 :=
    rfl
  rw [christoffelMap_apply_basis b _ hx j i]
  simp only [christoffelSymbol_apply, hframe, leviCivitaConnection_const_modelSpace,
    hz, map_zero, zero_smul, Finset.sum_const_zero]

/-- Every affine line in a finite-dimensional real inner-product space is a geodesic for the
standard Riemannian metric, with its evident initial point and velocity. -/
theorem isGeodesicCurveOnFrom_add_smul (p v : F) :
    IsGeodesicCurveOnFrom 𝓘(ℝ, F) (fun t : ℝ ↦ p + t • v) univ p v := by
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ ↦ p + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have hderiv : deriv (fun t : ℝ ↦ p + t • v) = fun _ : ℝ ↦ v :=
    funext fun t ↦ (hline t).deriv
  refine ⟨?_, mem_univ 0, ?_⟩
  · rw [isGeodesicCurveOn_iff_chart (I := 𝓘(ℝ, F)) uniqueDiffOn_univ]
    refine ⟨?_, fun r _ ↦ ?_⟩
    · rw [contMDiffOn_univ, contMDiff_iff_contDiff]
      fun_prop
    · simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_comp, derivWithin_univ,
        hderiv, deriv_const', christoffelMap_leviCivita_modelSpace, zero_apply, add_zero]
  · apply TotalSpace.ext
    · simp
    · refine heq_of_eq ?_
      rw [curveVelocityWithin_univ, curveVelocity_apply, mfderiv_eq_fderiv]
      exact (hline 0).deriv

/-- Every affine line in a finite-dimensional real inner-product space is a geodesic for the
standard Riemannian metric. -/
theorem isGeodesicCurve_add_smul (p v : F) :
    IsGeodesicCurve 𝓘(ℝ, F) (fun t : ℝ ↦ p + t • v) :=
  (isGeodesicCurveOn_univ (I := 𝓘(ℝ, F))).1
    (isGeodesicCurveOnFrom_add_smul p v).isGeodesicCurveOn

/-- Geodesics in a finite-dimensional inner-product space exist for every real parameter. -/
@[simp]
theorem geodesicInterval_modelSpace (p v : F) :
    geodesicInterval 𝓘(ℝ, F) F p v = univ := by
  apply eq_univ_of_forall
  intro t
  let a := -(|t| + 1)
  let b := |t| + 1
  have h0 : (0 : ℝ) ∈ Ioo a b := by
    simp only [a, b, mem_Ioo]
    constructor <;> linarith [abs_nonneg t]
  have ht : t ∈ Ioo a b := by
    simp only [a, b, mem_Ioo]
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  have hline := (isGeodesicCurveOnFrom_add_smul p v).mono
    (uniqueDiffOn_Ioo a b) (subset_univ _) h0
  exact (mem_geodesicInterval_iff (I := 𝓘(ℝ, F)) (M := F)).2
    ⟨fun s : ℝ ↦ p + s • v, a, b, hline, ht⟩

private theorem IsGeodesicCurveOnFrom.eq_maximalGeodesic_of_univ
    {p v : F} {γ : ℝ → F} (hγ : IsGeodesicCurveOnFrom 𝓘(ℝ, F) γ univ p v) (t : ℝ) :
    maximalGeodesic 𝓘(ℝ, F) F p v t = γ t := by
  let _ : T2Space (ModelProd F F) := Prod.t2Space
  let _ : T2Space (TangentBundle 𝓘(ℝ, F) F) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).symm.t2Space
  let a := -(|t| + 1)
  let b := |t| + 1
  have h0 : (0 : ℝ) ∈ Ioo a b := by
    simp only [a, b, mem_Ioo]
    constructor <;> linarith [abs_nonneg t]
  have ht : t ∈ Ioo a b := by
    simp only [a, b, mem_Ioo]
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  exact (hγ.mono (uniqueDiffOn_Ioo a b) (subset_univ _) h0).eqOn_maximalGeodesic ht

/-- The chosen maximal geodesic in an inner-product space is its affine line. -/
@[simp]
theorem maximalGeodesic_modelSpace (p v : F) (t : ℝ) :
    maximalGeodesic 𝓘(ℝ, F) F p v t = p + t • v := by
  exact (isGeodesicCurveOnFrom_add_smul p v).eq_maximalGeodesic_of_univ t

/-- The geodesics in a finite-dimensional real inner-product space are exactly the affine
lines. -/
theorem isGeodesicCurve_iff_exists_eq_add_smul {γ : ℝ → F} :
    IsGeodesicCurve 𝓘(ℝ, F) γ ↔ ∃ p v : F, γ = fun t : ℝ ↦ p + t • v := by
  constructor
  · intro hγ
    let p := γ 0
    let v : F := curveVelocityWithin 𝓘(ℝ, F) γ univ 0
    refine ⟨p, v, funext fun t ↦ ?_⟩
    have hfrom : IsGeodesicCurveOnFrom 𝓘(ℝ, F) γ univ p v :=
      ((isGeodesicCurveOn_univ (I := 𝓘(ℝ, F))).2 hγ).isGeodesicCurveOnFrom
        (mem_univ 0)
    have heq := hfrom.eq_maximalGeodesic_of_univ t
    rw [maximalGeodesic_modelSpace] at heq
    exact heq.symm
  · rintro ⟨p, v, rfl⟩
    exact isGeodesicCurve_add_smul p v

end TauCeti.Manifold

end
