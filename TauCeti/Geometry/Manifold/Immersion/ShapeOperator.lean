/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.ShapeOperator
public import TauCeti.Geometry.Manifold.Immersion.SecondFundamentalForm
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Hessian
import TauCeti.Analysis.InnerProductSpace.PointSpectrum.Transport
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.LinearAlgebra.Eigenspace.Transport

/-!
# The shape operator and focal points of a map from a manifold into a real inner product space

Let `i : M → V` be a map from a manifold modelled on a finite-dimensional real normed space `E`
into a real inner product space `V`. For a vector `ν : V`, its **shape operator**
`TauCeti.manifoldShapeOperator I i x ν` at `x : M` is the endomorphism of `TangentSpace I x`
obtained by transporting `TauCeti.shapeOperator` of the preferred coordinate expression
`i ∘ (extChartAt I x).symm` at `extChartAt I x x` along `tangentSpaceCastModel I x`.

When `I` is boundaryless and `mvfderiv I i x` is injective, `manifoldShapeOperator I i x ν` is the
unique endomorphism `S` of `TangentSpace I x` satisfying the Weingarten / defining identity

`⟪mvfderiv I i x (S v), mvfderiv I i x w⟫ = ⟪ν, manifoldSecondFundamentalForm I i x v w⟫`

for the induced metric on `TangentSpace I x`. It is linear in `ν` and depends only on the
orthogonal projection of `ν` onto `TauCeti.normalSubspace I i x`. When `i` is `C²` at `x`
(`ContMDiffAt I 𝓘(ℝ, V) 2 i x`), it is self-adjoint for the induced metric, is independent of the
choice of chart in `IsManifold.maximalAtlas I 2 M`, and transforms equivariantly under `C²` local
diffeomorphisms and diffeomorphisms.

For the squared-distance function `ρ_a(y) = ‖i y - a‖²` along a `C²` immersion `i : M → V`:

* `x` is a critical point of `ρ_a` if and only if `i x - a ∈ normalSubspace I i x`;
* at such a critical point, `criticalHessian I ρ_a x v w` equals
  `2 * ⟪mvfderiv I i x (v - S_{a - i x} v), mvfderiv I i x w⟫`, whose kernel is the `1`-eigenspace
  of `S_{a - i x}` (and along a normal ray `i x + t • ν` with `t ≠ 0`, the `t⁻¹`-eigenspace of
  `S_ν`);
* `x` is a nondegenerate critical point of `ρ_a` if and only if `i x - a ∈ normalSubspace I i x` and
  `1` is not an eigenvalue of `S_{a - i x}`;
* the manifold Morse index of `ρ_a` at any critical point `x` equals the dimension of
  `(S_{a - i x}).pointSpectralSubspace (Set.Ioi 1)`, equivalently the sum over `t ∈ (0, 1)` of the
  focal multiplicities of `i x + t • (a - i x)` at `x` (Milnor, *Morse Theory*, Lemma 6.5).

No completeness or finite-dimensionality is assumed on the ambient inner product space `V`.

## Main definitions

* `TauCeti.manifoldShapeOperator I i x ν`: the shape operator of `i : M → V` at `x : M` in the
  direction `ν : V`, as an endomorphism of `TangentSpace I x`.

## Main results

* `TauCeti.inner_mvfderiv_manifoldShapeOperator_apply` and `TauCeti.eq_manifoldShapeOperator_iff`:
  characterisation by the induced metric and `TauCeti.manifoldSecondFundamentalForm`.
* `TauCeti.manifoldShapeOperator_starProjection_normalSubspace`: the shape operator depends only on
  the normal component in `TauCeti.normalSubspace I i x`.
* `ContMDiffAt.inner_mvfderiv_manifoldShapeOperator_apply_comm`: self-adjointness for the induced
  metric.
* `ContMDiffAt.mvfderiv_extend_manifoldShapeOperator_apply_of_mem_maximalAtlas`,
  `ContMDiffAt.mfderiv_manifoldShapeOperator_comp`, and
  `Diffeomorph.mfderiv_manifoldShapeOperator_comp`: chart independence and reparametrisation
  invariance.
* `TauCeti.mem_criticalPoints_norm_sq_sub_comp_iff`,
  `TauCeti.criticalHessian_norm_sq_sub_comp_apply_eq_inner_manifoldShapeOperator`,
  `TauCeti.ker_criticalHessian_norm_sq_sub_comp`, and
  `TauCeti.ker_criticalHessian_norm_sq_sub_add_smul_comp`: critical points, critical Hessian, and
  focal multiplicities of squared distance.
* `TauCeti.isManifoldNondegenerateCriticalPoint_norm_sq_sub_comp_iff`,
  `TauCeti.manifoldMorseIndex_norm_sq_sub_comp`, and
  `TauCeti.manifoldMorseIndex_norm_sq_sub_comp_eq_finsum_finrank_ker`: nondegeneracy and Milnor's
  focal-point formula for `TauCeti.manifoldMorseIndex`.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §6, Lemma 6.5.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Chapter IX.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer, 2018, Chapter 8.
-/

public section

open Filter Function Module Module.End Set Topology
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

section General

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] {i j : M → V} {x : M}

/-- The **shape operator** of a map `i : M → V` from a manifold into a real inner product space at
`x : M` in the direction `ν : V`: the shape operator of the preferred coordinate expression
`i ∘ (extChartAt I x).symm` at `extChartAt I x x`, transported to `TangentSpace I x` along
`tangentSpaceCastModel I x`.

When `I` is boundaryless and `mvfderiv I i x` is injective, it is characterized intrinsically by
`TauCeti.eq_manifoldShapeOperator_iff`; when `mvfderiv I i x` is not injective it is `0`. When `I`
is boundaryless and `ContMDiffAt I 𝓘(ℝ, V) 2 i x`, it is independent of the choice of `C²` chart
(`ContMDiffAt.mvfderiv_extend_manifoldShapeOperator_apply_of_mem_maximalAtlas`). -/
def manifoldShapeOperator (I : ModelWithCorners ℝ E H) (i : M → V) (x : M) (ν : V) :
    Module.End ℝ (TangentSpace I x) :=
  (tangentSpaceCastModel I x).toLinearEquiv.symm.conj
    (shapeOperator (i ∘ (extChartAt I x).symm) (extChartAt I x x) ν)

/-- Reading `manifoldShapeOperator` on the model space `E` via `tangentSpaceCastModel I x` gives
`shapeOperator` of the preferred coordinate expression. -/
theorem tangentSpaceCastModel_manifoldShapeOperator_apply (ν : V) (v : TangentSpace I x) :
    tangentSpaceCastModel I x (manifoldShapeOperator I i x ν v) =
      shapeOperator (i ∘ (extChartAt I x).symm) (extChartAt I x x) ν
        (tangentSpaceCastModel I x v) := by
  simp [manifoldShapeOperator]

/-- On a normed space with its self-model, `manifoldShapeOperator` is `shapeOperator`. -/
@[simp]
theorem manifoldShapeOperator_modelSpace {g : E → V} {y : E} (ν : V) :
    manifoldShapeOperator 𝓘(ℝ, E) g y ν = shapeOperator g y ν := by
  ext v
  simp only [manifoldShapeOperator, LinearEquiv.conj_apply_apply, extChartAt_model_space_eq_id,
    PartialEquiv.refl_symm, PartialEquiv.refl_coe, comp_id, id_eq]
  -- `tangentSpaceCastModel 𝓘(ℝ, E) y` is the identity on `E`.
  rfl

/-- `manifoldShapeOperator` depends only on the germ of the map at the base point. -/
theorem manifoldShapeOperator_congr_of_eventuallyEq (hij : i =ᶠ[𝓝 x] j) (ν : V) :
    manifoldShapeOperator I i x ν = manifoldShapeOperator I j x ν := by
  set z := extChartAt I x x
  have hchart : (extChartAt I x).symm z = x := by simp [z]
  have hij' : i ∘ (extChartAt I x).symm =ᶠ[𝓝 z] j ∘ (extChartAt I x).symm :=
    (hchart ▸ hij).comp_tendsto (continuousAt_extChartAt_symm (I := I) x)
  have hdf : fderiv ℝ (i ∘ (extChartAt I x).symm) z =
      fderiv ℝ (j ∘ (extChartAt I x).symm) z := hij'.fderiv_eq
  have hsff : secondFundamentalForm ℝ (i ∘ (extChartAt I x).symm) z =
      secondFundamentalForm ℝ (j ∘ (extChartAt I x).symm) z := by
    ext v w
    rw [secondFundamentalForm_apply, secondFundamentalForm_apply, (hij'.fderiv (𝕜 := ℝ)).fderiv_eq]
    simp only [hdf]
  have hso : shapeOperator (i ∘ (extChartAt I x).symm) z ν =
      shapeOperator (j ∘ (extChartAt I x).symm) z ν := by
    by_cases h : Injective (fderiv ℝ (i ∘ (extChartAt I x).symm) z)
    · have hj_inj : Injective (fderiv ℝ (j ∘ (extChartAt I x).symm) z) := hdf ▸ h
      refine (eq_shapeOperator_iff hj_inj).mpr fun v w ↦ ?_
      rw [← hdf, inner_fderiv_shapeOperator_apply h, hsff]
    · have hj_ninj : ¬Injective (fderiv ℝ (j ∘ (extChartAt I x).symm) z) := hdf ▸ h
      rw [shapeOperator_of_not_injective h, shapeOperator_of_not_injective hj_ninj]
  simp only [manifoldShapeOperator, z, hso]

/-- `manifoldShapeOperator` is additive in the normal vector. -/
@[simp]
theorem manifoldShapeOperator_add (ν ν' : V) :
    manifoldShapeOperator I i x (ν + ν') =
      manifoldShapeOperator I i x ν + manifoldShapeOperator I i x ν' := by
  simp [manifoldShapeOperator]

/-- `manifoldShapeOperator` is homogeneous in the normal vector. -/
@[simp]
theorem manifoldShapeOperator_smul (c : ℝ) (ν : V) :
    manifoldShapeOperator I i x (c • ν) = c • manifoldShapeOperator I i x ν := by
  simp [manifoldShapeOperator]

@[simp]
theorem manifoldShapeOperator_zero : manifoldShapeOperator I i x 0 = 0 := by
  simp [manifoldShapeOperator]

@[simp]
theorem manifoldShapeOperator_neg (ν : V) :
    manifoldShapeOperator I i x (-ν) = -manifoldShapeOperator I i x ν := by
  simp [manifoldShapeOperator]

@[simp]
theorem manifoldShapeOperator_sub (ν ν' : V) :
    manifoldShapeOperator I i x (ν - ν') =
      manifoldShapeOperator I i x ν - manifoldShapeOperator I i x ν' := by
  simp [manifoldShapeOperator]

/-! ### Boundaryless manifolds: defining identity, normal projection, and chart independence -/

section Boundaryless

variable [I.Boundaryless]

/-- **The defining identity of `manifoldShapeOperator`.** When `mvfderiv I i x` is injective, the
induced metric pairs `manifoldShapeOperator I i x ν v` with `w` as `ν` pairs with
`manifoldSecondFundamentalForm I i x v w`. -/
theorem inner_mvfderiv_manifoldShapeOperator_apply (h : Injective (mvfderiv I i x)) (ν : V)
    (v w : TangentSpace I x) :
    ⟪mvfderiv I i x (manifoldShapeOperator I i x ν v), mvfderiv I i x w⟫ =
      ⟪ν, manifoldSecondFundamentalForm I i x v w⟫ := by
  rw [mvfderiv_apply_eq_fderiv_comp_extChartAt_symm,
    mvfderiv_apply_eq_fderiv_comp_extChartAt_symm i x w,
    tangentSpaceCastModel_manifoldShapeOperator_apply,
    manifoldSecondFundamentalForm_eq_secondFundamentalForm_comp_extChartAt_symm]
  exact inner_fderiv_shapeOperator_apply (injective_fderiv_comp_extChartAt_symm_iff.mpr h) ν _ _

/-- When `mvfderiv I i x` is not injective, `manifoldShapeOperator I i x ν` is `0`. -/
theorem manifoldShapeOperator_of_not_injective (h : ¬Injective (mvfderiv I i x)) (ν : V) :
    manifoldShapeOperator I i x ν = 0 := by
  rw [manifoldShapeOperator,
    shapeOperator_of_not_injective (mt injective_fderiv_comp_extChartAt_symm_iff.mp h), map_zero]

/-- **Uniqueness of `manifoldShapeOperator`.** When `mvfderiv I i x` is injective,
`manifoldShapeOperator I i x ν` is the unique endomorphism satisfying the Weingarten pairing
identity against `manifoldSecondFundamentalForm I i x`. -/
theorem eq_manifoldShapeOperator_iff (h : Injective (mvfderiv I i x)) {ν : V}
    {S : Module.End ℝ (TangentSpace I x)} :
    S = manifoldShapeOperator I i x ν ↔
      ∀ v w, ⟪mvfderiv I i x (S v), mvfderiv I i x w⟫ =
        ⟪ν, manifoldSecondFundamentalForm I i x v w⟫ := by
  refine ⟨fun hS ↦ hS ▸ inner_mvfderiv_manifoldShapeOperator_apply h ν, fun hS ↦ ?_⟩
  refine LinearMap.ext fun v ↦
    eq_of_forall_inner_comp (L := (mvfderiv I i x : TangentSpace I x →ₗ[ℝ] V)) h fun w ↦ ?_
  simp only [ContinuousLinearMap.coe_coe, hS, inner_mvfderiv_manifoldShapeOperator_apply h]

/-- Vectors in the tangent image `(mvfderiv I i x).range` have zero shape operator. -/
theorem manifoldShapeOperator_of_mem_range {ν : V} (hν : ν ∈ (mvfderiv I i x).range) :
    manifoldShapeOperator I i x ν = 0 := by
  rw [range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm] at hν
  rw [manifoldShapeOperator, shapeOperator_of_mem_range hν, map_zero]

/-- `manifoldShapeOperator` depends only on the orthogonal projection of `ν` onto
`TauCeti.normalSubspace I i x`. -/
@[simp]
theorem manifoldShapeOperator_starProjection_normalSubspace (ν : V) :
    manifoldShapeOperator I i x ((normalSubspace I i x).starProjection ν) =
      manifoldShapeOperator I i x ν := by
  have : FiniteDimensional ℝ (TangentSpace I x) :=
    Module.Finite.equiv (tangentSpaceCastModel I x).symm.toLinearEquiv
  have hfg : FiniteDimensional ℝ (mvfderiv I i x).range :=
    Module.Finite.range (mvfderiv I i x : TangentSpace I x →ₗ[ℝ] V)
  have hdecomp : ν = (mvfderiv I i x).range.starProjection ν +
      (normalSubspace I i x).starProjection ν := by
    simpa only [orthogonal_range_mvfderiv_eq_normalSubspace] using
      ((mvfderiv I i x).range.starProjection_add_starProjection_orthogonal ν).symm
  conv_rhs => rw [hdecomp]
  rw [manifoldShapeOperator_add,
    manifoldShapeOperator_of_mem_range (Submodule.starProjection_apply_mem _ _), zero_add]

/-- The shape operator of a map which is `C²` at `x` is self-adjoint for the induced metric. -/
theorem _root_.ContMDiffAt.inner_mvfderiv_manifoldShapeOperator_apply_comm
    (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i x) (ν : V) (v w : TangentSpace I x) :
    ⟪mvfderiv I i x (manifoldShapeOperator I i x ν v), mvfderiv I i x w⟫ =
      ⟪mvfderiv I i x v, mvfderiv I i x (manifoldShapeOperator I i x ν w)⟫ := by
  by_cases h : Injective (mvfderiv I i x)
  swap
  · rw [manifoldShapeOperator_of_not_injective h, LinearMap.zero_apply, LinearMap.zero_apply,
      map_zero, inner_zero_left, inner_zero_right]
  rw [real_inner_comm (mvfderiv I i x (manifoldShapeOperator I i x ν w)),
    inner_mvfderiv_manifoldShapeOperator_apply h, inner_mvfderiv_manifoldShapeOperator_apply h,
    hi.manifoldSecondFundamentalForm_apply_comm]

/-- **Equivariance under reparametrisation.** If `φ : N → M` is `C²` at `y` between boundaryless
manifolds with bijective differential at `y` (for instance, a local diffeomorphism at `y`), and
`i : M → V` is `C²` at `φ y`, then `mfderiv J I φ y` intertwines the shape operators of `i ∘ φ` at
`y` and of `i` at `φ y`. -/
theorem _root_.ContMDiffAt.mfderiv_manifoldShapeOperator_comp
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H' N] {φ : N → M} {y : N}
    (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i (φ y)) (hφ : ContMDiffAt J I 2 φ y)
    (hbij : Bijective (mfderiv J I φ y)) (ν : V) (v : TangentSpace J y) :
    mfderiv J I φ y (manifoldShapeOperator J (i ∘ φ) y ν v) =
      manifoldShapeOperator I i (φ y) ν (mfderiv J I φ y v) := by
  have hcomp : mvfderiv J (i ∘ φ) y = (mvfderiv I i (φ y)).comp (mfderiv J I φ y) :=
    mvfderiv_comp y (hi.mdifferentiableAt two_ne_zero) (hφ.mdifferentiableAt two_ne_zero)
  have hinj_iff : Injective (mvfderiv J (i ∘ φ) y) ↔ Injective (mvfderiv I i (φ y)) := by
    rw [hcomp, ContinuousLinearMap.coe_comp]
    refine ⟨fun h u w huw ↦ ?_, fun h ↦ h.comp hbij.1⟩
    obtain ⟨u', rfl⟩ := hbij.2 u
    obtain ⟨w', rfl⟩ := hbij.2 w
    exact congrArg (mfderiv J I φ y) (h huw)
  by_cases h : Injective (mvfderiv I i (φ y))
  · have hJ : Injective (mvfderiv J (i ∘ φ) y) := hinj_iff.mpr h
    let eφ : TangentSpace J y ≃ₗ[ℝ] TangentSpace I (φ y) :=
      LinearEquiv.ofBijective (mfderiv J I φ y : TangentSpace J y →ₗ[ℝ] TangentSpace I (φ y)) hbij
    have coe_eφ (u : TangentSpace J y) : eφ u = mfderiv J I φ y u := by simp [eφ]
    suffices eφ.symm.conj (manifoldShapeOperator I i (φ y) ν) = manifoldShapeOperator J (i ∘ φ) y ν
      from (congrArg eφ (LinearMap.congr_fun this v)).symm.trans (eφ.apply_symm_apply _)
    refine (eq_manifoldShapeOperator_iff hJ).mpr fun u w ↦ ?_
    rw [hcomp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← coe_eφ,
      LinearEquiv.conj_apply_apply, eφ.apply_symm_apply, eφ.symm_symm, coe_eφ,
      inner_mvfderiv_manifoldShapeOperator_apply h,
      hi.manifoldSecondFundamentalForm_comp hφ hbij.surjective]
  · have hJ : ¬Injective (mvfderiv J (i ∘ φ) y) := mt hinj_iff.mp h
    simp [manifoldShapeOperator_of_not_injective h, manifoldShapeOperator_of_not_injective hJ]

/-- Precomposing with a `C^n` diffeomorphism (`2 ≤ n`) between boundaryless manifolds conjugates
the shape operator by the differential of the diffeomorphism. -/
theorem _root_.Diffeomorph.mfderiv_manifoldShapeOperator_comp
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω} (Φ : N ≃ₘ^n⟮J, I⟯ M) (hn : 2 ≤ n)
    {y : N} (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i (Φ y)) (ν : V) (v : TangentSpace J y) :
    mfderiv J I Φ y (manifoldShapeOperator J (i ∘ Φ) y ν v) =
      manifoldShapeOperator I i (Φ y) ν (mfderiv J I Φ y v) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hbij : Bijective (mfderiv J I Φ y) := by
    rw [← Φ.mfderivToContinuousLinearEquiv_coe hn0 (x := y)]
    exact (Φ.mfderivToContinuousLinearEquiv hn0 y).bijective
  exact hi.mfderiv_manifoldShapeOperator_comp ((Φ.contMDiff.of_le hn).contMDiffAt) hbij ν v

/-- **The shape operator in an arbitrary chart.** For a map `i : M → V` which is `C²` at `x` on a
boundaryless manifold and any chart `e ∈ IsManifold.maximalAtlas I 2 M` with `x ∈ e.source`,
`mvfderiv I (e.extend I) x` intertwines `manifoldShapeOperator I i x ν` with the coordinate
`shapeOperator` of `i ∘ (e.extend I).symm` at `e.extend I x`. -/
theorem _root_.ContMDiffAt.mvfderiv_extend_manifoldShapeOperator_apply_of_mem_maximalAtlas
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 2 M) (hx : x ∈ e.source)
    (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i x) (ν : V) (v : TangentSpace I x) :
    mvfderiv I (e.extend I) x (manifoldShapeOperator I i x ν v) =
      shapeOperator (i ∘ (e.extend I).symm) (e.extend I x) ν (mvfderiv I (e.extend I) x v) := by
  have he1 : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) he
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extend he1 hx
  have hbij : Bijective (mfderiv I 𝓘(ℝ, E) (e.extend I) x) := hL ▸ L.bijective
  have hi_ext : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, V) 2 (i ∘ (e.extend I).symm) (e.extend I x) :=
    ((contMDiffAt_iff_contDiffAt_comp_extend_symm he hx).mp hi).contMDiffAt
  have hev : i =ᶠ[𝓝 x] (i ∘ (e.extend I).symm) ∘ e.extend I := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    rw [comp_apply, comp_apply, (e.extend I).left_inv (by rwa [e.extend_source])]
  rw [manifoldShapeOperator_congr_of_eventuallyEq hev, mvfderiv_apply_eq_mfderiv_apply,
    hi_ext.mfderiv_manifoldShapeOperator_comp (e.contMDiffAt_extend he hx) hbij,
    manifoldShapeOperator_modelSpace]
  exact congrArg (shapeOperator (i ∘ (e.extend I).symm) (e.extend I x) ν)
    (mvfderiv_apply_eq_mfderiv_apply (e.extend I) x v).symm

end Boundaryless

end General

/-! ### Squared distance, critical Hessian, nondegeneracy, and focal points -/

section SquaredDistance

section FirstDerivative

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] {i : M → V} {x : M} {a : V}

/-- The vector-valued manifold derivative of `y ↦ ‖i y - a‖²` along a differentiable map
`i : M → V`. -/
theorem mvfderiv_norm_sq_sub_comp (hi : MDifferentiableAt I 𝓘(ℝ, V) i x) :
    mvfderiv I (fun y ↦ ‖i y - a‖ ^ 2) x = 2 • (innerSL ℝ (i x - a)).comp (mvfderiv I i x) := by
  have hd : DifferentiableAt ℝ (fun z : V ↦ ‖z - a‖ ^ 2) (i x) :=
    DifferentiableAt.norm_sq ℝ (differentiableAt_id.sub (differentiableAt_const a))
  have hfderiv : fderiv ℝ (fun z : V ↦ ‖z - a‖ ^ 2) (i x) = 2 • innerSL ℝ (i x - a) := by
    simpa using fderiv_norm_sq_sub_comp (a := a) differentiableAt_id (x := i x)
  ext v
  exact (mvfderiv_comp_apply_of_differentiableAt (φ := fun z : V ↦ ‖z - a‖ ^ 2) hd hi v).trans
    (by simp only [hfderiv, ContinuousLinearMap.comp_apply, smul_apply])

/-- **Normal-vector test for critical points of squared distance.** Along a differentiable map
`i : M → V`, the manifold differential of `y ↦ ‖i y - a‖²` vanishes at `x` if and only if
`i x - a ∈ normalSubspace I i x`. -/
theorem mvfderiv_norm_sq_sub_comp_eq_zero_iff (hi : MDifferentiableAt I 𝓘(ℝ, V) i x) :
    mvfderiv I (fun y ↦ ‖i y - a‖ ^ 2) x = 0 ↔ i x - a ∈ normalSubspace I i x := by
  rw [mvfderiv_norm_sq_sub_comp hi, ContinuousLinearMap.ext_iff, mem_normalSubspace_iff_mvfderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, zero_apply, innerSL_apply_apply,
    smul_eq_zero, OfNat.ofNat_ne_zero, false_or]

/-- A point `x` at which `i : M → V` is differentiable is in `criticalPoints I (y ↦ ‖i y - a‖²)`
if and only if `i x - a ∈ normalSubspace I i x`. -/
theorem mem_criticalPoints_norm_sq_sub_comp_iff (hi : MDifferentiableAt I 𝓘(ℝ, V) i x) :
    x ∈ criticalPoints I (fun y ↦ ‖i y - a‖ ^ 2) ↔ i x - a ∈ normalSubspace I i x := by
  rw [mem_criticalPoints, mvfderiv_norm_sq_sub_comp_eq_zero_iff hi]

end FirstDerivative

section SecondOrder

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] {i : M → V} {x : M} {a : V}

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- `criticalHessian I f x` evaluated on `v, w` equals the second Fréchet derivative of
`f ∘ (extChartAt I x).symm` at `extChartAt I x x` evaluated on `tangentSpaceCastModel I x v` and
`tangentSpaceCastModel I x w`, since `tangentSpaceCastModel I x` is the identity on `E`. -/
private theorem criticalHessian_apply_eq_fderiv_fderiv (f : M → ℝ) (x : M)
    (v w : TangentSpace I x) :
    criticalHessian I f x v w =
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x)
        (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w) := by
  rw [criticalHessian_def]
  rfl

omit [I.Boundaryless] in
/-- Transporting `eigenspace` between `manifoldShapeOperator` and the preferred coordinate
`shapeOperator` along `tangentSpaceCastModel I x`. -/
private theorem eigenspace_manifoldShapeOperator_eq_comap (ν : V) (μ : ℝ) :
    eigenspace (manifoldShapeOperator I i x ν) μ =
      (eigenspace (shapeOperator (i ∘ (extChartAt I x).symm) (extChartAt I x x) ν) μ).comap
        (tangentSpaceCastModel I x).toLinearMap :=
  eigenspace_eq_comap_of_intertwine (e := (tangentSpaceCastModel I x).toLinearEquiv)
    (f := manifoldShapeOperator I i x ν)
    (g := shapeOperator (i ∘ (extChartAt I x).symm) (extChartAt I x x) ν)
    (fun v ↦ tangentSpaceCastModel_manifoldShapeOperator_apply ν v) μ

omit [I.Boundaryless] in
private theorem hasEigenvalue_manifoldShapeOperator_iff (ν : V) (μ : ℝ) :
    (manifoldShapeOperator I i x ν).HasEigenvalue μ ↔
      (shapeOperator (i ∘ (extChartAt I x).symm) (extChartAt I x x) ν).HasEigenvalue μ := by
  simp only [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff,
    eigenspace_manifoldShapeOperator_eq_comap, Submodule.mem_comap]
  let e := (tangentSpaceCastModel I x).toLinearEquiv
  exact ⟨fun ⟨v, hv, hv0⟩ ↦ ⟨e v, hv, e.map_ne_zero_iff.mpr hv0⟩,
    fun ⟨u, hu, hu0⟩ ↦ ⟨e.symm u, by simpa [e] using hu, e.symm.map_ne_zero_iff.mpr hu0⟩⟩

omit [I.Boundaryless] in
private theorem finrank_pointSpectralSubspace_manifoldShapeOperator (ν : V) (Ω : Set ℝ) :
    finrank ℝ ((manifoldShapeOperator I i x ν).pointSpectralSubspace Ω) =
      finrank ℝ
        ((shapeOperator (i ∘ (extChartAt I x).symm) (extChartAt I x x) ν).pointSpectralSubspace
          Ω) := by
  rw [manifoldShapeOperator,
    ← map_pointSpectralSubspace_conj (tangentSpaceCastModel I x).toLinearEquiv.symm,
    LinearEquiv.finrank_map_eq]

/-- **Critical Hessian of squared distance in terms of `manifoldSecondFundamentalForm`.** At a
critical point (`i x - a ∈ normalSubspace I i x`) of `y ↦ ‖i y - a‖²` along a map `i : M → V`
which is `C²` at `x`, the critical Hessian is twice the sum of the pullback inner product and the
pairing of `i x - a` with `manifoldSecondFundamentalForm I i x` (without assuming injectivity of
`mvfderiv I i x`). -/
theorem criticalHessian_norm_sq_sub_comp_apply_of_mem_normalSubspace
    (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i x) (ha : i x - a ∈ normalSubspace I i x)
    (v w : TangentSpace I x) :
    criticalHessian I (fun y ↦ ‖i y - a‖ ^ 2) x v w =
      2 * (⟪mvfderiv I i x v, mvfderiv I i x w⟫ +
        ⟪i x - a, manifoldSecondFundamentalForm I i x v w⟫) := by
  have hgx : (i ∘ (extChartAt I x).symm) (extChartAt I x x) = i x := by simp
  rw [criticalHessian_apply_eq_fderiv_fderiv,
    mvfderiv_apply_eq_fderiv_comp_extChartAt_symm i x v,
    mvfderiv_apply_eq_fderiv_comp_extChartAt_symm i x w,
    inner_manifoldSecondFundamentalForm_apply_of_mem_normalSubspace ha, ← hgx]
  exact fderiv_fderiv_norm_sq_sub_comp_apply hi.contDiffAt_comp_extChartAt_symm _ _

/-- **Critical Hessian of squared distance in terms of `manifoldShapeOperator`.** At a critical
point (`i x - a ∈ normalSubspace I i x`) along a `C²` immersion, `criticalHessian` of
`y ↦ ‖i y - a‖²` at `x` is `2 g((1 - S_{a - i x}) v, w)` for the induced metric `g`. -/
theorem criticalHessian_norm_sq_sub_comp_apply_eq_inner_manifoldShapeOperator
    (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i x) (h : Injective (mvfderiv I i x))
    (ha : i x - a ∈ normalSubspace I i x) (v w : TangentSpace I x) :
    criticalHessian I (fun y ↦ ‖i y - a‖ ^ 2) x v w =
      2 * ⟪mvfderiv I i x (v - manifoldShapeOperator I i x (a - i x) v), mvfderiv I i x w⟫ := by
  rw [criticalHessian_norm_sq_sub_comp_apply_of_mem_normalSubspace hi ha, map_sub,
    inner_sub_left (mvfderiv I i x v), inner_mvfderiv_manifoldShapeOperator_apply h,
    ← neg_sub a (i x), inner_neg_left]
  ring

/-- **Null space of the squared-distance critical Hessian.** If `i x - a ∈ normalSubspace I i x`,
the kernel of `criticalHessian I (y ↦ ‖i y - a‖²) x` is the `1`-eigenspace of
`manifoldShapeOperator I i x (a - i x)`. -/
theorem ker_criticalHessian_norm_sq_sub_comp (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i x)
    (h : Injective (mvfderiv I i x)) (ha : i x - a ∈ normalSubspace I i x) :
    LinearMap.ker
        (criticalHessian I (fun y ↦ ‖i y - a‖ ^ 2) x :
          TangentSpace I x →ₗ[ℝ] TangentSpace I x →L[ℝ] ℝ) =
      eigenspace (manifoldShapeOperator I i x (a - i x)) 1 := by
  ext v
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, mem_eigenspace_iff, one_smul,
    eq_comm (a := manifoldShapeOperator I i x (a - i x) v), ← sub_eq_zero (a := v)]
  refine ⟨fun hv ↦ sub_eq_zero.2 <|
      eq_of_forall_inner_comp (L := (mvfderiv I i x : TangentSpace I x →ₗ[ℝ] V)) h fun w ↦ ?_,
    fun hv ↦ ContinuousLinearMap.ext fun w ↦ ?_⟩
  · have hw := DFunLike.congr_fun hv w
    rw [zero_apply,
      criticalHessian_norm_sq_sub_comp_apply_eq_inner_manifoldShapeOperator hi h ha, map_sub,
      inner_sub_left] at hw
    simp only [ContinuousLinearMap.coe_coe]
    linarith
  · rw [zero_apply,
      criticalHessian_norm_sq_sub_comp_apply_eq_inner_manifoldShapeOperator hi h ha, hv, map_zero,
      inner_zero_left, mul_zero]

/-- **Focal points along a normal ray.** For `ν ∈ normalSubspace I i x` and `t ≠ 0`, the kernel of
`criticalHessian` at `x` of squared distance from `i x + t • ν` is the `t⁻¹`-eigenspace of
`manifoldShapeOperator I i x ν`. -/
theorem ker_criticalHessian_norm_sq_sub_add_smul_comp (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i x)
    (h : Injective (mvfderiv I i x)) {ν : V} (hν : ν ∈ normalSubspace I i x) {t : ℝ}
    (ht : t ≠ 0) :
    LinearMap.ker
        (criticalHessian I (fun y ↦ ‖i y - (i x + t • ν)‖ ^ 2) x :
          TangentSpace I x →ₗ[ℝ] TangentSpace I x →L[ℝ] ℝ) =
      eigenspace (manifoldShapeOperator I i x ν) t⁻¹ := by
  rw [ker_criticalHessian_norm_sq_sub_comp hi h (by simpa using Submodule.smul_mem _ (-t) hν),
    add_sub_cancel_left, manifoldShapeOperator_smul, eigenspace, genEigenspace_smul _ ht, mul_one]

/-- The base point `i x` is not a focal point: squared distance from `i x` has trivial critical
Hessian kernel at `x` along a `C²` immersion. -/
theorem ker_criticalHessian_norm_sq_sub_self_comp (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i x)
    (h : Injective (mvfderiv I i x)) :
    LinearMap.ker
        (criticalHessian I (fun y ↦ ‖i y - i x‖ ^ 2) x :
          TangentSpace I x →ₗ[ℝ] TangentSpace I x →L[ℝ] ℝ) = ⊥ := by
  rw [ker_criticalHessian_norm_sq_sub_comp hi h (by simp), sub_self, manifoldShapeOperator_zero,
    eigenspace_def]
  simp only [zero_sub, one_smul, LinearMap.ker_neg, Module.End.one_eq_id, LinearMap.ker_id]

/-- **Nondegenerate critical points of squared distance on a manifold.** Along a `C²` immersion
`i : M → V`, `x` is a nondegenerate critical point of `y ↦ ‖i y - a‖²` if and only if
`i x - a ∈ normalSubspace I i x` and `1` is not an eigenvalue of
`manifoldShapeOperator I i x (a - i x)`. -/
theorem isManifoldNondegenerateCriticalPoint_norm_sq_sub_comp_iff
    (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i x) (h : Injective (mvfderiv I i x)) :
    IsManifoldNondegenerateCriticalPoint I (fun y ↦ ‖i y - a‖ ^ 2) x ↔
      i x - a ∈ normalSubspace I i x ∧
        ¬(manifoldShapeOperator I i x (a - i x)).HasEigenvalue 1 := by
  have hcomp : ((fun y ↦ ‖i y - a‖ ^ 2) ∘ (extChartAt I x).symm) =
      fun u ↦ ‖(i ∘ (extChartAt I x).symm) u - a‖ ^ 2 := rfl
  have hg : ContDiffAt ℝ 2 (i ∘ (extChartAt I x).symm) (extChartAt I x x) :=
    hi.contDiffAt_comp_extChartAt_symm
  have hginj : Injective (fderiv ℝ (i ∘ (extChartAt I x).symm) (extChartAt I x x)) :=
    injective_fderiv_comp_extChartAt_symm_iff.mpr h
  have hgx : (i ∘ (extChartAt I x).symm) (extChartAt I x x) = i x := by simp
  rw [isManifoldNondegenerateCriticalPoint_iff, hcomp,
    isNondegenerateCriticalPoint_norm_sq_sub_comp_iff hg hginj,
    hgx, ← range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm,
    orthogonal_range_mvfderiv_eq_normalSubspace, hasEigenvalue_manifoldShapeOperator_iff]

/-- Along a normal ray `i x + t • ν` (`ν ∈ normalSubspace I i x`, `t ≠ 0`), `x` is a nondegenerate
critical point of `y ↦ ‖i y - (i x + t • ν)‖²` if and only if `t⁻¹` is not an eigenvalue of
`manifoldShapeOperator I i x ν`. -/
theorem isManifoldNondegenerateCriticalPoint_norm_sq_sub_add_smul_comp_iff
    (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i x) (h : Injective (mvfderiv I i x)) {ν : V}
    (hν : ν ∈ normalSubspace I i x) {t : ℝ} (ht : t ≠ 0) :
    IsManifoldNondegenerateCriticalPoint I (fun y ↦ ‖i y - (i x + t • ν)‖ ^ 2) x ↔
      ¬(manifoldShapeOperator I i x ν).HasEigenvalue t⁻¹ := by
  rw [isManifoldNondegenerateCriticalPoint_norm_sq_sub_comp_iff hi h]
  have hmem : i x - (i x + t • ν) ∈ normalSubspace I i x := by
    simpa using Submodule.smul_mem _ (-t) hν
  simp only [hmem, true_and, add_sub_cancel_left, manifoldShapeOperator_smul,
    Module.End.hasEigenvalue_iff, eigenspace, genEigenspace_smul _ ht, mul_one]

/-- Squared distance from `i x` has a nondegenerate critical point at `x` along any `C²`
immersion. -/
theorem isManifoldNondegenerateCriticalPoint_norm_sq_sub_self_comp
    (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i x) (h : Injective (mvfderiv I i x)) :
    IsManifoldNondegenerateCriticalPoint I (fun y ↦ ‖i y - i x‖ ^ 2) x := by
  rw [isManifoldNondegenerateCriticalPoint_norm_sq_sub_comp_iff hi h]
  simp [Module.End.hasEigenvalue_iff, eigenspace_def, Module.End.one_eq_id]

/-- **Spectral formula for `manifoldMorseIndex` of squared distance.** At any critical point `x`
(`i x - a ∈ normalSubspace I i x`) of `y ↦ ‖i y - a‖²` along a `C²` immersion `i : M → V`
(degenerate or not), `manifoldMorseIndex` equals the dimension of the point-spectral subspace of
`manifoldShapeOperator I i x (a - i x)` for eigenvalues strictly greater than `1`. -/
theorem manifoldMorseIndex_norm_sq_sub_comp (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i x)
    (h : Injective (mvfderiv I i x)) (ha : i x - a ∈ normalSubspace I i x) :
    manifoldMorseIndex I (fun y ↦ ‖i y - a‖ ^ 2) x =
      finrank ℝ ((manifoldShapeOperator I i x (a - i x)).pointSpectralSubspace (Ioi 1)) := by
  have hcomp : ((fun y ↦ ‖i y - a‖ ^ 2) ∘ (extChartAt I x).symm) =
      fun u ↦ ‖(i ∘ (extChartAt I x).symm) u - a‖ ^ 2 := rfl
  have hgx : (i ∘ (extChartAt I x).symm) (extChartAt I x x) = i x := by simp
  have ha' : (i ∘ (extChartAt I x).symm) (extChartAt I x x) - a ∈
      (fderiv ℝ (i ∘ (extChartAt I x).symm) (extChartAt I x x)).rangeᗮ := by
    rwa [hgx, ← range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm,
      orthogonal_range_mvfderiv_eq_normalSubspace]
  rw [manifoldMorseIndex_def, hcomp, finrank_pointSpectralSubspace_manifoldShapeOperator, ← hgx]
  exact morseIndex_norm_sq_sub_comp hi.contDiffAt_comp_extChartAt_symm
    (injective_fderiv_comp_extChartAt_symm_iff.mpr h) ha'

/-- **Milnor's focal-point formula for `manifoldMorseIndex` (Lemma 6.5).** At any critical point
`x` (`i x - a ∈ normalSubspace I i x`) of `y ↦ ‖i y - a‖²` along a `C²` immersion `i : M → V`
(degenerate or not), the manifold Morse index equals the sum over `t ∈ (0, 1)` of the focal
multiplicities of `i x + t • (a - i x)` at `x`, measured by the nullity of `criticalHessian`. -/
theorem manifoldMorseIndex_norm_sq_sub_comp_eq_finsum_finrank_ker
    (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i x) (h : Injective (mvfderiv I i x))
    (ha : i x - a ∈ normalSubspace I i x) :
    manifoldMorseIndex I (fun y ↦ ‖i y - a‖ ^ 2) x =
      ∑ᶠ t ∈ Ioo (0 : ℝ) 1,
        finrank ℝ (LinearMap.ker
          (criticalHessian I (fun y ↦ ‖i y - (i x + t • (a - i x))‖ ^ 2) x :
            TangentSpace I x →ₗ[ℝ] TangentSpace I x →L[ℝ] ℝ)) := by
  let g := i ∘ (extChartAt I x).symm
  let z := extChartAt I x x
  have hcomp : ((fun y ↦ ‖i y - a‖ ^ 2) ∘ (extChartAt I x).symm) = fun u ↦ ‖g u - a‖ ^ 2 := rfl
  have hz : extChartAt I x x = z := rfl
  have hgz : g z = i x := by simp [g, z]
  have hg : ContDiffAt ℝ 2 g z := hi.contDiffAt_comp_extChartAt_symm
  have hginj : Injective (fderiv ℝ g z) := injective_fderiv_comp_extChartAt_symm_iff.mpr h
  have ha' : g z - a ∈ (fderiv ℝ g z).rangeᗮ := by
    rwa [hgz, ← range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm,
      orthogonal_range_mvfderiv_eq_normalSubspace]
  have hν : a - i x ∈ normalSubspace I i x := by simpa using Submodule.neg_mem _ ha
  have hν' : a - g z ∈ (fderiv ℝ g z).rangeᗮ := by simpa using Submodule.neg_mem _ ha'
  rw [manifoldMorseIndex_def, hcomp, hz,
    morseIndex_norm_sq_sub_comp_eq_finsum_finrank_ker hg hginj ha']
  refine finsum_congr fun t ↦ finsum_congr fun ht ↦ ?_
  rw [ker_fderiv_fderiv_norm_sq_sub_add_smul_comp hg hginj hν' ht.1.ne',
    ker_criticalHessian_norm_sq_sub_add_smul_comp hi h hν ht.1.ne', hgz,
    eigenspace_manifoldShapeOperator_eq_comap]
  let e := (tangentSpaceCastModel I x).toLinearEquiv
  have hcomap : (eigenspace (shapeOperator g z (a - i x)) t⁻¹).comap
      (tangentSpaceCastModel I x).toLinearMap =
      (eigenspace (shapeOperator g z (a - i x)) t⁻¹).map e.symm.toLinearMap := by
    ext v
    simp [e]
  rw [hcomap, LinearEquiv.finrank_map_eq]

/-- Squared distance from `i x` along any `C²` map has manifold Morse index `0` at `x` (without
assuming injectivity of `mvfderiv I i x`). -/
@[simp]
theorem manifoldMorseIndex_norm_sq_sub_self_comp (hi : ContMDiffAt I 𝓘(ℝ, V) 2 i x) :
    manifoldMorseIndex I (fun y ↦ ‖i y - i x‖ ^ 2) x = 0 := by
  have hcomp : ((fun y ↦ ‖i y - i x‖ ^ 2) ∘ (extChartAt I x).symm) =
      fun u ↦ ‖(i ∘ (extChartAt I x).symm) u - i x‖ ^ 2 := rfl
  have hgx : (i ∘ (extChartAt I x).symm) (extChartAt I x x) = i x := by simp
  rw [manifoldMorseIndex_def, hcomp, ← hgx]
  exact morseIndex_norm_sq_sub_self_comp hi.contDiffAt_comp_extChartAt_symm

end SecondOrder

end SquaredDistance

end TauCeti

end

