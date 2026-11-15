/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Space
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Extension
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Flow
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Reparametrization
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.InitialData
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Jacobi fields with prescribed initial data

Along any geodesic on a preconnected parameter set, every pair of initial value and initial
covariant derivative at a chosen parameter is attained by a Jacobi field on that set. The proof
first solves the initial-value problem on the entire natural interval of a maximal geodesic by
differentiating the geodesic flow along a curve of initial tangent vectors supplied by
`CovariantDerivative.exists_contMDiffAt_tangentCurve_initialData`, and then transfers the solution
to an arbitrary geodesic via `IsGeodesicCurveOn.maximalGeodesic_sub_eq_of_isPreconnected` and
affine time translation.

Together with initial-data uniqueness, evaluation of the value and covariant derivative at any
parameter identifies `jacobiFieldSpace` on a nonempty preconnected parameter set with two copies of
the tangent space there, so its dimension is `2 * dim M`. Representing interval sections by their
canonical zero extensions avoids any unconstrained values outside the parameter set. Expanding the
inverse equivalence in a basis of the initial-data space shows that both the Jacobi field and its
covariant derivative depend smoothly on the initial data and parameter jointly. Neither
completeness of the metric nor a curvature bound is assumed.

## Main definitions and results

* `TauCeti.Manifold.IsGeodesicCurveOn.exists_isJacobiFieldOn` and
  `TauCeti.Manifold.IsGeodesicCurveOn.exists_isJacobiFieldOn_Icc`: global solvability of the Jacobi
  equation with prescribed initial data on any preconnected geodesic parameter set, and in
  particular at the left endpoint of `[a, b]`.
* `TauCeti.Manifold.jacobiInitialData_surjective` and `TauCeti.Manifold.jacobiInitialDataEquiv`:
  the initial-data map at any parameter of a preconnected geodesic is a linear equivalence onto two
  copies of the tangent space there.
* `TauCeti.Manifold.finrank_jacobiFieldSpace`: the space of Jacobi fields on a nonempty
  preconnected parameter set has dimension `2 * Module.finrank ℝ E`.
* `TauCeti.Manifold.contMDiffOn_jacobiInitialDataEquiv_symm` and
  `TauCeti.Manifold.contMDiffOn_alongCurveWithin_jacobiInitialDataEquiv_symm`: joint smoothness of
  the initial-data solution and its covariant derivative in the initial data and time.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 10
  (existence and uniqueness of Jacobi fields, and realization by geodesic variations).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press (1963),
  §14, p. 77 (identification of Jacobi fields on an interval with two copies of the initial tangent
  space; note Milnor writes `R(γ', X)γ'` where we write `R(X, γ')γ'`).
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Arbitrary initial value and covariant velocity are realized on the whole natural interval
of a maximal geodesic, without assuming completeness of the metric. -/
private theorem exists_isJacobiFieldOn_maximalGeodesic_initialData
    (p : M) (v u w : TangentSpace I p) :
    ∃ V : ∀ t, TangentSpace I (maximalGeodesic I M p v t),
      IsJacobiFieldOn I (maximalGeodesic I M p v) V (geodesicInterval I M p v) ∧
      V 0 = u ∧
      alongCurveWithin (leviCivitaConnection I M) (maximalGeodesic I M p v) V
        (geodesicInterval I M p v) 0 = w := by
  obtain ⟨σ, hσ₀, hσ, hu, hw⟩ :=
    (leviCivitaConnection I M).exists_contMDiffAt_tangentCurve_initialData p v u w 0
  have hJ := isJacobiFieldOn_variationField_maximalGeodesic (hσ.of_le (by norm_num))
  have hD := alongCurveWithin_variationField_maximalGeodesic_zero (hσ.of_le (by norm_num))
  rw [hw] at hD
  rw [hσ₀] at hJ hD
  refine ⟨variationField I (fun q ↦ maximalGeodesic I M (σ q).proj (σ q).2), hJ, ?_, hD⟩
  rw [variationField_maximalGeodesic_zero, hu]

/-! ### Arbitrary geodesics on preconnected parameter sets -/

/-- **Existence of Jacobi fields with prescribed initial data.** Along any geodesic `γ` on a
preconnected parameter set `s`, every initial value `u` and initial covariant derivative `w` at any
parameter `a ∈ s` is attained by a Jacobi field on `s`. -/
theorem IsGeodesicCurveOn.exists_isJacobiFieldOn
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) (u w : TangentSpace I (γ a)) :
    ∃ X : ∀ t, TangentSpace I (γ t),
      IsJacobiFieldOn I γ X s ∧ X a = u ∧
      alongCurveWithin (leviCivitaConnection I M) γ X s a = w := by
  let cov := leviCivitaConnection I M
  let p := γ a
  let v := curveVelocityWithin I γ s a
  obtain ⟨V₀, hV₀, hu₀, hw₀⟩ := exists_isJacobiFieldOn_maximalGeodesic_initialData p v u w
  have hmaps : MapsTo (fun t : ℝ ↦ 1 * t + (-a)) s (geodesicInterval I M p v) := fun t ht ↦ by
    simpa only [one_mul, ← sub_eq_add_neg] using
      hγ.sub_mem_geodesicInterval_of_isPreconnected hs ha ht
  have hcurve : EqOn γ (maximalGeodesic I M p v ∘ fun t : ℝ ↦ 1 * t + (-a)) s := fun t ht ↦ by
    simpa only [Function.comp_apply, one_mul, ← sub_eq_add_neg] using
      (hγ.maximalGeodesic_sub_eq_of_isPreconnected hs ha ht).symm
  let X : ∀ t, TangentSpace I (γ t) := fun t ↦
    tangentSpaceCast I (maximalGeodesic I M p v (1 * t + (-a))) (γ t) (V₀ (1 * t + (-a)))
  have hX : IsJacobiFieldOn I γ X s :=
    hV₀.comp_affine_of_eqOn 1 (-a) hγ.uniqueDiffOn hmaps hcurve
  have hzero : 1 * a + (-a) = 0 := by ring
  have hXa : X a = u := by
    have h1 : HEq (X a) (V₀ (1 * a + (-a))) :=
      TauCeti.heq_tangentSpaceCast (hcurve ha).symm _
    have h2 : HEq (V₀ (1 * a + (-a))) u := by
      rw [hzero]
      exact heq_of_eq hu₀
    exact eq_of_heq (h1.trans h2)
  have hDXa : alongCurveWithin cov γ X s a = w := by
    have hD1 := hV₀.heq_alongCurveWithin_comp_affine_of_eqOn 1 (-a) hγ.uniqueDiffOn hmaps hcurve ha
    rw [one_smul] at hD1
    have hD2 : HEq (alongCurveWithin cov (maximalGeodesic I M p v) V₀
        (geodesicInterval I M p v) (1 * a + (-a))) w := by
      rw [hzero]
      exact heq_of_eq hw₀
    exact eq_of_heq (hD1.trans hD2)
  exact ⟨X, hX, hXa, hDXa⟩

/-- Along a geodesic on a nondegenerate closed interval `[a, b]`, every initial value and initial
covariant derivative at `a` is attained by a Jacobi field on `[a, b]`. -/
theorem IsGeodesicCurveOn.exists_isJacobiFieldOn_Icc
    {γ : ℝ → M} {a b : ℝ} (hab : a < b) (hγ : IsGeodesicCurveOn I γ (Icc a b))
    (u w : TangentSpace I (γ a)) :
    ∃ X : ∀ t, TangentSpace I (γ t),
      IsJacobiFieldOn I γ X (Icc a b) ∧ X a = u ∧
      alongCurveWithin (leviCivitaConnection I M) γ X (Icc a b) a = w :=
  hγ.exists_isJacobiFieldOn isPreconnected_Icc (left_mem_Icc.2 hab.le) u w

/-- The initial-data map at any parameter of a geodesic on a preconnected parameter set is
surjective. -/
theorem jacobiInitialData_surjective
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) :
    Function.Surjective (jacobiInitialData hγ ha) := by
  rintro ⟨u, w⟩
  obtain ⟨X, hX, hu, hw⟩ := hγ.exists_isJacobiFieldOn hs ha u w
  refine ⟨hX.toJacobiFieldSpace, ?_⟩
  rw [jacobiInitialData_apply, hX.toJacobiFieldSpace_apply ha,
    hX.alongCurveWithin_toJacobiFieldSpace ha, hu, hw]

/-- **Initial-data equivalence for Jacobi fields.** Initial value and covariant derivative at any
parameter identify the space of Jacobi fields along a geodesic on a preconnected parameter set with
two copies of the tangent space at that parameter. -/
def jacobiInitialDataEquiv
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) :
    jacobiFieldSpace hγ ≃ₗ[ℝ] TangentSpace I (γ a) × TangentSpace I (γ a) :=
  LinearEquiv.ofBijective (jacobiInitialData hγ ha)
    ⟨jacobiInitialData_injective hγ hs ha, jacobiInitialData_surjective hγ hs ha⟩

/-- Coercing `jacobiInitialDataEquiv` to a linear map recovers `jacobiInitialData`. -/
@[simp]
theorem toLinearMap_jacobiInitialDataEquiv
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) :
    (jacobiInitialDataEquiv hγ hs ha).toLinearMap = jacobiInitialData hγ ha :=
  (rfl)

/-- The initial-data equivalence evaluates to the value and covariant derivative of the field. -/
@[simp]
theorem jacobiInitialDataEquiv_apply
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) (V : jacobiFieldSpace hγ) :
    jacobiInitialDataEquiv hγ hs ha V =
      (V.val a, alongCurveWithin (leviCivitaConnection I M) γ V.val s a) :=
  jacobiInitialData_apply hγ ha V

/-- The inverse initial-data equivalence has the prescribed value at the initial parameter. -/
@[simp]
theorem jacobiInitialDataEquiv_symm_apply_self
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) (d : TangentSpace I (γ a) × TangentSpace I (γ a)) :
    ((jacobiInitialDataEquiv hγ hs ha).symm d).val a = d.1 := by
  have h := (jacobiInitialDataEquiv hγ hs ha).apply_symm_apply d
  rw [jacobiInitialDataEquiv_apply] at h
  exact congrArg Prod.fst h

/-- The inverse initial-data equivalence has the prescribed covariant derivative at the initial
parameter. -/
@[simp]
theorem alongCurveWithin_jacobiInitialDataEquiv_symm_self
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) (d : TangentSpace I (γ a) × TangentSpace I (γ a)) :
    alongCurveWithin (leviCivitaConnection I M) γ
      ((jacobiInitialDataEquiv hγ hs ha).symm d).val s a = d.2 := by
  have h := (jacobiInitialDataEquiv hγ hs ha).apply_symm_apply d
  rw [jacobiInitialDataEquiv_apply] at h
  exact congrArg Prod.snd h

/-- **Dimension of the space of Jacobi fields.** On any nonempty preconnected parameter set, the
space of Jacobi fields along a geodesic has dimension `2 * dim M`, including zero-dimensional
manifolds and constant geodesics. -/
theorem finrank_jacobiFieldSpace
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) :
    Module.finrank ℝ (jacobiFieldSpace hγ) = 2 * Module.finrank ℝ E := by
  simpa [Module.finrank_prod, TauCeti.finrank_tangentSpace, two_mul] using
    (jacobiInitialDataEquiv hγ hs ha).finrank_eq

/-! ### Smooth dependence on initial data -/

omit [T2Space M] in
/-- Any family of sections along a geodesic `γ` on `s` depending linearly on a finite-dimensional
parameter space `D`, whose evaluations at fixed parameters in `D` are smooth along `γ`, is jointly
smooth on `univ ×ˢ s`. -/
private theorem contMDiffOn_totalSpaceMk_of_linear_sectionAlong
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s)
    (W : D → ∀ t, TangentSpace I (γ t))
    (L : (t : ℝ) → t ∈ s → D →ₗ[ℝ] TangentSpace I (γ t))
    (hWL : ∀ (d : D) (t : ℝ) (ht : t ∈ s), W d t = L t ht d)
    (hsec : ∀ d : D, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t ↦ TotalSpace.mk' E (γ t) (W d t)) s) :
    ContMDiffOn 𝓘(ℝ, D × ℝ) I.tangent ∞
      (fun q : D × ℝ ↦ TotalSpace.mk' E (γ q.2) (W q.1 q.2)) (univ ×ˢ s) := by
  let b := Module.finBasis ℝ D
  have hbase : ContMDiffOn 𝓘(ℝ, D × ℝ) I ∞ (fun q : D × ℝ ↦ γ q.2) (univ ×ˢ s) :=
    hγ.contMDiffOn_infty.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hq ↦ hq.2)
  have hterm (i : Fin (Module.finrank ℝ D)) :
      ContMDiffOn 𝓘(ℝ, D × ℝ) I.tangent ∞
        (fun q : D × ℝ ↦ TotalSpace.mk' E (γ q.2) (b.repr q.1 i • W (b i) q.2))
        (univ ×ˢ s) := by
    have hcoeff : ContMDiffOn 𝓘(ℝ, D × ℝ) 𝓘(ℝ, ℝ) ∞ (fun q : D × ℝ ↦ b.repr q.1 i) (univ ×ˢ s) :=
      (((b.coord i).toContinuousLinearMap.comp
        (ContinuousLinearMap.fst ℝ D ℝ)).contMDiff).contMDiffOn
    exact hcoeff.smul_totalSpace ((hsec (b i)).comp
      contDiff_snd.contMDiff.contMDiffOn (fun _ hq ↦ hq.2))
  refine (ContMDiffOn.sum_sectionAlong (b := fun q : D × ℝ ↦ γ q.2) Finset.univ
    (fun i q ↦ b.repr q.1 i • W (b i) q.2) hbase fun i _ ↦ hterm i).congr ?_
  intro q hq
  refine congrArg (TotalSpace.mk' E (γ q.2)) ?_
  rw [hWL q.1 q.2 hq.2]
  conv_lhs => rw [← b.sum_repr q.1]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, hWL (b i) q.2 hq.2]

/-- **Smooth dependence of Jacobi fields on initial data.** Along a geodesic on a preconnected
parameter set `s`, the tangent-bundle lift of the Jacobi field with prescribed initial data at
`a ∈ s` is jointly smooth in the initial data and the parameter on `univ ×ˢ s`. -/
theorem contMDiffOn_jacobiInitialDataEquiv_symm
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) :
    ContMDiffOn 𝓘(ℝ, (TangentSpace I (γ a) × TangentSpace I (γ a)) × ℝ) I.tangent ∞
      (fun q : (TangentSpace I (γ a) × TangentSpace I (γ a)) × ℝ ↦
        TotalSpace.mk' E (γ q.2) (((jacobiInitialDataEquiv hγ hs ha).symm q.1).val q.2))
      (univ ×ˢ s) :=
  contMDiffOn_totalSpaceMk_of_linear_sectionAlong hγ
    (fun d t ↦ ((jacobiInitialDataEquiv hγ hs ha).symm d).val t)
    (fun t ht ↦ ((LinearMap.fst ℝ _ _).comp (jacobiInitialData hγ ht)).comp
      (jacobiInitialDataEquiv hγ hs ha).symm.toLinearMap)
    (fun _ _ _ ↦ by simp)
    (fun _ ↦ (isJacobiFieldOn_of_mem_jacobiFieldSpace _).contMDiffOn_infty)

/-- **Smooth dependence of the covariant derivative on Jacobi initial data.** Along a geodesic on
a preconnected parameter set `s`, the tangent-bundle lift of the covariant derivative of the
initial-data Jacobi field is jointly smooth in the initial data and the parameter on
`univ ×ˢ s`. -/
theorem contMDiffOn_alongCurveWithin_jacobiInitialDataEquiv_symm
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) :
    ContMDiffOn 𝓘(ℝ, (TangentSpace I (γ a) × TangentSpace I (γ a)) × ℝ) I.tangent ∞
      (fun q : (TangentSpace I (γ a) × TangentSpace I (γ a)) × ℝ ↦
        TotalSpace.mk' E (γ q.2)
          (alongCurveWithin (leviCivitaConnection I M) γ
            ((jacobiInitialDataEquiv hγ hs ha).symm q.1).val s q.2))
      (univ ×ˢ s) :=
  contMDiffOn_totalSpaceMk_of_linear_sectionAlong hγ
    (fun d t ↦ alongCurveWithin (leviCivitaConnection I M) γ
      ((jacobiInitialDataEquiv hγ hs ha).symm d).val s t)
    (fun t ht ↦ ((LinearMap.snd ℝ _ _).comp (jacobiInitialData hγ ht)).comp
      (jacobiInitialDataEquiv hγ hs ha).symm.toLinearMap)
    (fun _ _ _ ↦ by simp)
    (fun _ ↦ (isJacobiFieldOn_of_mem_jacobiFieldSpace _).contMDiffOn_alongCurveWithin_infty)

end TauCeti.Manifold
