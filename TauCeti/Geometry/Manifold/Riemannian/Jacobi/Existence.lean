/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory
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

/-- Surjectivity at zero on the full natural interval is the starting point for changing the
initial time by finite-dimensional linear algebra. -/
private theorem jacobiInitialData_surjective_maximalGeodesic_zero
    (p : M) (v : TangentSpace I p) :
    Function.Surjective (jacobiInitialData
      (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn
      zero_mem_geodesicInterval) := by
  rintro ⟨u, w⟩
  obtain ⟨V, hV, hu, hw⟩ := exists_isJacobiFieldOn_maximalGeodesic_initialData p v u w
  refine ⟨hV.toJacobiFieldSpace, ?_⟩
  rw [jacobiInitialData_apply, hV.toJacobiFieldSpace_apply zero_mem_geodesicInterval,
    hV.alongCurveWithin_toJacobiFieldSpace zero_mem_geodesicInterval, hu, hw]

/-- The full natural interval has the expected dimension, before choosing any initial time. -/
private theorem finrank_jacobiFieldSpace_maximalGeodesic_full
    (p : M) (v : TangentSpace I p) :
    Module.finrank ℝ (jacobiFieldSpace
      (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn) =
        2 * Module.finrank ℝ E := by
  let e := LinearEquiv.ofBijective (jacobiInitialData
    (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn zero_mem_geodesicInterval)
    ⟨jacobiInitialData_injective _ isPreconnected_geodesicInterval zero_mem_geodesicInterval,
      jacobiInitialData_surjective_maximalGeodesic_zero p v⟩
  simpa [Module.finrank_prod, TauCeti.finrank_tangentSpace, two_mul] using e.finrank_eq

/-- At every initial time, arbitrary Jacobi data are realized on any subset of the maximal
geodesic interval having unique derivatives. The subset need not contain time zero or be
preconnected: restrict the solution from the full natural interval. -/
theorem jacobiInitialData_surjective_maximalGeodesic
    (p : M) (v : TangentSpace I p) {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hsub : s ⊆ geodesicInterval I M p v) {a : ℝ} (ha : a ∈ s) :
    Function.Surjective (jacobiInitialData
      ((isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.mono hs hsub) ha) := by
  let hγ := (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn
  let := finiteDimensional_jacobiFieldSpace hγ isPreconnected_geodesicInterval
    zero_mem_geodesicInterval
  have hdim : Module.finrank ℝ (jacobiFieldSpace hγ) =
      Module.finrank ℝ (TangentSpace I (maximalGeodesic I M p v a) ×
        TangentSpace I (maximalGeodesic I M p v a)) := by
    rw [finrank_jacobiFieldSpace_maximalGeodesic_full, Module.finrank_prod,
      TauCeti.finrank_tangentSpace, two_mul]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (jacobiInitialData_injective hγ isPreconnected_geodesicInterval (hsub ha))
  rintro ⟨u, w⟩
  obtain ⟨V, hV⟩ := hsurj (u, w)
  have hJ := isJacobiFieldOn_of_mem_jacobiFieldSpace V
  have hJs := hJ.mono hs hsub
  refine ⟨hJs.toJacobiFieldSpace, ?_⟩
  rw [jacobiInitialData_apply, hJs.toJacobiFieldSpace_apply ha,
    hJs.alongCurveWithin_toJacobiFieldSpace ha, hJ.alongCurveWithin_subset (hs a ha) hsub ha]
  simpa only [jacobiInitialData_apply] using hV

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
  have hW := hV₀.comp_affine 1 (-a) hγ.uniqueDiffOn hmaps
  have hcurve : EqOn γ (maximalGeodesic I M p v ∘ fun t : ℝ ↦ 1 * t + (-a)) s := fun t ht ↦ by
    simpa only [Function.comp_apply, one_mul, ← sub_eq_add_neg] using
      (hγ.maximalGeodesic_sub_eq_of_isPreconnected hs ha ht).symm
  let X : ∀ t, TangentSpace I (γ t) := fun t ↦
    tangentSpaceCast I (maximalGeodesic I M p v (1 * t + (-a))) (γ t) (V₀ (1 * t + (-a)))
  have hEq (t : ℝ) (ht : t ∈ s) :
      TotalSpace.mk' E (γ t) (X t) =
        TotalSpace.mk' E (maximalGeodesic I M p v (1 * t + (-a))) (V₀ (1 * t + (-a))) :=
    TotalSpace.ext (hcurve ht) (TauCeti.heq_tangentSpaceCast (hcurve ht).symm _)
  have hX : IsJacobiFieldOn I γ X s := hW.congr_totalSpace hEq
  have hzero : 1 * a + (-a) = 0 := by ring
  have hXa : X a = u := by
    have h1 : HEq (X a) (V₀ (1 * a + (-a))) := (TotalSpace.ext_iff.mp (hEq a ha)).2
    have h2 : HEq (V₀ (1 * a + (-a))) u := by
      rw [hzero]
      exact heq_of_eq hu₀
    exact eq_of_heq (h1.trans h2)
  have hDXa : alongCurveWithin cov γ X s a = w := by
    have hheq : ∀ t ∈ s, HEq (X t) (V₀ (1 * t + (-a))) :=
      fun t ht ↦ (TotalSpace.ext_iff.mp (hEq t ht)).2
    have hD1 : HEq (alongCurveWithin cov γ X s a)
        (alongCurveWithin cov (maximalGeodesic I M p v ∘ fun t : ℝ ↦ 1 * t + (-a))
          (fun r ↦ V₀ (1 * r + (-a))) s a) :=
      alongCurveWithin_congr_heq cov X (hcurve.eventuallyEq_of_mem self_mem_nhdsWithin)
        (hcurve ha) (mem_of_superset self_mem_nhdsWithin hheq) (hheq a ha)
    rw [hV₀.alongCurveWithin_comp_affine 1 (-a) hγ.uniqueDiffOn hmaps ha, one_smul] at hD1
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
theorem jacobiInitialDataEquiv_symm_apply_value
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) (u w : TangentSpace I (γ a)) :
    ((jacobiInitialDataEquiv hγ hs ha).symm (u, w)).val a = u := by
  have h := (jacobiInitialDataEquiv hγ hs ha).apply_symm_apply (u, w)
  rw [jacobiInitialDataEquiv_apply] at h
  exact congrArg Prod.fst h

/-- The inverse initial-data equivalence has the prescribed covariant derivative at the initial
parameter. -/
@[simp]
theorem alongCurveWithin_jacobiInitialDataEquiv_symm
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) (u w : TangentSpace I (γ a)) :
    alongCurveWithin (leviCivitaConnection I M) γ
      ((jacobiInitialDataEquiv hγ hs ha).symm (u, w)).val s a = w := by
  have h := (jacobiInitialDataEquiv hγ hs ha).apply_symm_apply (u, w)
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

/-- Expanding an element of the Jacobi-field space in the basis transported from `finBasis` of the
initial-data space expresses it pointwise as a linear combination of the basis Jacobi fields. -/
private theorem jacobiInitialDataEquiv_symm_eq_sum
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) :
    let D := TangentSpace I (γ a) × TangentSpace I (γ a)
    let b := Module.finBasis ℝ D
    ∀ (d : D) (t : ℝ),
      ((jacobiInitialDataEquiv hγ hs ha).symm d).val t =
        ∑ i, b.repr d i • ((jacobiInitialDataEquiv hγ hs ha).symm (b i)).val t := by
  intro D b d t
  conv_lhs => rw [← b.sum_repr d]
  rw [map_sum]
  simp only [map_smul, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul_of_tower,
    Pi.smul_apply]

/-- **Smooth dependence of Jacobi fields on initial data.** Along a geodesic on a preconnected
parameter set `s`, the tangent-bundle lift of the Jacobi field with prescribed initial data at
`a ∈ s` is jointly smooth in the initial data and the parameter on `univ ×ˢ s`. -/
theorem contMDiffOn_jacobiInitialDataEquiv_symm
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s)
    {a : ℝ} (ha : a ∈ s) :
    ContMDiffOn 𝓘(ℝ, (TangentSpace I (γ a) × TangentSpace I (γ a)) × ℝ) I.tangent ∞
      (fun q : (TangentSpace I (γ a) × TangentSpace I (γ a)) × ℝ ↦
        TotalSpace.mk' E (γ q.2) (((jacobiInitialDataEquiv hγ hs ha).symm q.1).val q.2))
      (univ ×ˢ s) := by
  let D := TangentSpace I (γ a) × TangentSpace I (γ a)
  let b := Module.finBasis ℝ D
  let e := (jacobiInitialDataEquiv hγ hs ha).symm
  have hbase : ContMDiffOn 𝓘(ℝ, D × ℝ) I ∞ (fun q : D × ℝ ↦ γ q.2) (univ ×ˢ s) :=
    hγ.contMDiffOn_infty.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hq ↦ hq.2)
  have hterm (i : Fin (Module.finrank ℝ D)) :
      ContMDiffOn 𝓘(ℝ, D × ℝ) I.tangent ∞
        (fun q : D × ℝ ↦ TotalSpace.mk' E (γ q.2) (b.repr q.1 i • (e (b i)).val q.2))
        (univ ×ˢ s) := by
    have hcoeff : ContMDiffOn 𝓘(ℝ, D × ℝ) 𝓘(ℝ, ℝ) ∞ (fun q : D × ℝ ↦ b.repr q.1 i) (univ ×ˢ s) :=
      (((b.coord i).toContinuousLinearMap.comp
        (ContinuousLinearMap.fst ℝ D ℝ)).contMDiff).contMDiffOn
    have hsec : ContMDiffOn 𝓘(ℝ, D × ℝ) I.tangent ∞
        (fun q : D × ℝ ↦ TotalSpace.mk' E (γ q.2) ((e (b i)).val q.2)) (univ ×ˢ s) :=
      (isJacobiFieldOn_of_mem_jacobiFieldSpace (e (b i))).contMDiffOn_infty.comp
        contDiff_snd.contMDiff.contMDiffOn (fun _ hq ↦ hq.2)
    exact hcoeff.smul_totalSpace hsec
  refine (ContMDiffOn.sum_sectionAlong (b := fun q : D × ℝ ↦ γ q.2) Finset.univ
    (fun i q ↦ b.repr q.1 i • (e (b i)).val q.2) hbase fun i _ ↦ hterm i).congr ?_
  intro q _
  exact congrArg (TotalSpace.mk' E (γ q.2))
    (jacobiInitialDataEquiv_symm_eq_sum hγ hs ha q.1 q.2)

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
      (univ ×ˢ s) := by
  let cov := leviCivitaConnection I M
  let D := TangentSpace I (γ a) × TangentSpace I (γ a)
  let b := Module.finBasis ℝ D
  let e := (jacobiInitialDataEquiv hγ hs ha).symm
  have hbase : ContMDiffOn 𝓘(ℝ, D × ℝ) I ∞ (fun q : D × ℝ ↦ γ q.2) (univ ×ˢ s) :=
    hγ.contMDiffOn_infty.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hq ↦ hq.2)
  have hterm (i : Fin (Module.finrank ℝ D)) :
      ContMDiffOn 𝓘(ℝ, D × ℝ) I.tangent ∞
        (fun q : D × ℝ ↦ TotalSpace.mk' E (γ q.2)
          (b.repr q.1 i • alongCurveWithin cov γ (e (b i)).val s q.2))
        (univ ×ˢ s) := by
    have hcoeff : ContMDiffOn 𝓘(ℝ, D × ℝ) 𝓘(ℝ, ℝ) ∞ (fun q : D × ℝ ↦ b.repr q.1 i) (univ ×ˢ s) :=
      (((b.coord i).toContinuousLinearMap.comp
        (ContinuousLinearMap.fst ℝ D ℝ)).contMDiff).contMDiffOn
    have hsec : ContMDiffOn 𝓘(ℝ, D × ℝ) I.tangent ∞
        (fun q : D × ℝ ↦ TotalSpace.mk' E (γ q.2)
          (alongCurveWithin cov γ (e (b i)).val s q.2)) (univ ×ˢ s) :=
      (isJacobiFieldOn_of_mem_jacobiFieldSpace (e (b i))).contMDiffOn_alongCurveWithin_infty.comp
        contDiff_snd.contMDiff.contMDiffOn (fun _ hq ↦ hq.2)
    exact hcoeff.smul_totalSpace hsec
  refine (ContMDiffOn.sum_sectionAlong (b := fun q : D × ℝ ↦ γ q.2) Finset.univ
    (fun i q ↦ b.repr q.1 i • alongCurveWithin cov γ (e (b i)).val s q.2)
    hbase fun i _ ↦ hterm i).congr ?_
  intro q hq
  have hexp (r : ℝ) : (e q.1).val r = ∑ i, b.repr q.1 i • (e (b i)).val r :=
    jacobiInitialDataEquiv_symm_eq_sum hγ hs ha q.1 r
  refine congrArg (TotalSpace.mk' E (γ q.2)) ?_
  rw [funext hexp, alongCurveWithin_sum cov γ Finset.univ
    (fun i r ↦ b.repr q.1 i • (e (b i)).val r)]
  · refine Finset.sum_congr rfl fun i _ ↦ alongCurveWithin_const_smul cov γ _ _ s q.2
  · intro i _
    rw [sectionCoord_smul (F := E) γ (e (b i)).val (fun _ ↦ b.repr q.1 i) (γ q.2)]
    exact ((isJacobiFieldOn_of_mem_jacobiFieldSpace
      (e (b i))).differentiableWithinAt_sectionCoord hq.2).const_smul (b.repr q.1 i)

end TauCeti.Manifold
