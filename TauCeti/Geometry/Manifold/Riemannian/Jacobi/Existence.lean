/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Space
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Extension
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Flow
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Reparametrization
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.InitialData
import TauCeti.Geometry.Manifold.VectorBundle.Section.LinearFamily

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
  refine ⟨variationField I (fun q ↦ maximalGeodesic I M (σ q).proj (σ q).snd), hJ, ?_, hD⟩
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
  let p := γ a
  let v := curveVelocityWithin I γ s a
  obtain ⟨V₀, hV₀, hu₀, hw₀⟩ := exists_isJacobiFieldOn_maximalGeodesic_initialData p v u w
  have hmaps : MapsTo (fun t : ℝ ↦ t - a) s (geodesicInterval I M p v) :=
    fun _ ht ↦ hγ.sub_mem_geodesicInterval_of_isPreconnected hs ha ht
  have hcurve : EqOn γ (fun t ↦ maximalGeodesic I M p v (t - a)) s :=
    fun _ ht ↦ (hγ.maximalGeodesic_sub_eq_of_isPreconnected hs ha ht).symm
  have h0 : γ a = maximalGeodesic I M p v 0 := by simpa only [sub_self] using hcurve ha
  have hXa : tangentSpaceCast I (maximalGeodesic I M p v (a - a)) (γ a) (V₀ (a - a)) = u := by
    rw [congrArg (fun x ↦ tangentSpaceCast I (maximalGeodesic I M p v x) (γ a) (V₀ x)) (sub_self a)]
    exact eq_of_heq ((TauCeti.heq_tangentSpaceCast h0.symm _).trans (heq_of_eq hu₀))
  have hDXa : alongCurveWithin (leviCivitaConnection I M) γ
      (fun t ↦ tangentSpaceCast I (maximalGeodesic I M p v (t - a)) (γ t) (V₀ (t - a))) s a =
        w := by
    rw [hV₀.alongCurveWithin_comp_sub_const_of_eqOn a (hγ.uniqueDiffOn a ha) hmaps hcurve ha,
      congrArg (fun x ↦ tangentSpaceCast I (maximalGeodesic I M p v x) (γ a)
        (alongCurveWithin (leviCivitaConnection I M) (maximalGeodesic I M p v) V₀
          (geodesicInterval I M p v) x)) (sub_self a)]
    exact eq_of_heq ((TauCeti.heq_tangentSpaceCast h0.symm _).trans (heq_of_eq hw₀))
  exact ⟨fun t ↦ tangentSpaceCast I (maximalGeodesic I M p v (t - a)) (γ t) (V₀ (t - a)),
    hV₀.comp_sub_const_of_eqOn a hγ.uniqueDiffOn hmaps hcurve, hXa, hDXa⟩

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
  TauCeti.contMDiffOn_totalSpaceMk_of_linear
    (fun d t ↦ ((jacobiInitialDataEquiv hγ hs ha).symm d).val t)
    (fun _ ht ↦ ⟨((LinearMap.fst ℝ _ _).comp (jacobiInitialData hγ ht)).comp
      (jacobiInitialDataEquiv hγ hs ha).symm.toLinearMap, fun _ ↦ by simp⟩)
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
  TauCeti.contMDiffOn_totalSpaceMk_of_linear
    (fun d t ↦ alongCurveWithin (leviCivitaConnection I M) γ
      ((jacobiInitialDataEquiv hγ hs ha).symm d).val s t)
    (fun _ ht ↦ ⟨((LinearMap.snd ℝ _ _).comp (jacobiInitialData hγ ht)).comp
      (jacobiInitialDataEquiv hγ hs ha).symm.toLinearMap, fun _ ↦ by simp⟩)
    (fun _ ↦ (isJacobiFieldOn_of_mem_jacobiFieldSpace _).contMDiffOn_alongCurveWithin_infty)

end TauCeti.Manifold
