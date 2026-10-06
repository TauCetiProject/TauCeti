/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Analysis.InnerProductSpace.LinearIsometry
public import TauCeti.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Sphere.LinearIsometry

import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# The stereographic charts of the sphere, and the smooth embeddings of spheres induced by
linear isometries

Mathlib charts the unit sphere of an `(n + 1)`-dimensional real inner product space by
stereographic projection, the preferred chart at `v` projecting from the antipode `-v`
(`EuclideanSpace.instChartedSpaceSphere`). This file records the two facts about these charts
that computations in a chart at a chosen point use: which stereographic projection the preferred
chart is, and that the extended chart at `v` sends `v` to the origin of the model space.

It then uses the charts to show that a linear isometry `ι : F →ₗᵢ[ℝ] E` restricts to a smooth
embedding of unit spheres, `LinearIsometry.unitSphereMap`. Stereographic projection is defined
from inner products and orthogonal projections, both of which `ι` preserves, so `ι` carries the
stereographic chart at `v` to the stereographic chart at `ι v`: in those two charts, `ι` reads as a
linear isometry `LinearIsometry.stereographicModelMap` of the model Euclidean spaces, and a linear
isometry is the inclusion of a factor in a product decomposition
(`LinearIsometry.prodOrthogonalRangeEquiv`). That is the normal form Mathlib's
`Manifold.IsImmersionAt` asks for, and together with the isometric embedding of the spheres it
makes the restriction a smooth embedding. Great circles, the geometric presentation of the unknot,
are the case of a linear isometry `ℂ →ₗᵢ[ℝ] E`.

Finally, the covering map `Circle.exp : ℝ → S¹` has injective derivative everywhere, so that a
loop and its lift to `ℝ` have the same tangent lines. A differentiable loop in a sphere of dimension
at least two omits a point, allowing the entire loop to be read in one stereographic chart.

## Main results

* `TauCeti.chartAt_sphere`: the preferred chart at `v` is `stereographic' n (-v)`.
* `TauCeti.extChartAt_sphere_apply_self`: the preferred extended chart at `v` sends `v` to `0`.
* `LinearIsometry.stereographic'_unitSphereMap`: the stereographic charts read a linear isometry
  of unit spheres as a linear isometry of the model spaces.
* `LinearIsometry.isSmoothEmbedding_unitSphereMap`: the restriction of a linear isometry to the
  unit spheres is a smooth embedding, at every differentiability order.
* `TauCeti.injective_mfderiv_circleExp`: the derivative of `Circle.exp : ℝ → S¹` is injective.
* `TauCeti.deriv_comp_circleExp_ne_zero_and_range_mfderiv`: lifting a `C¹` immersed circle
  along `Circle.exp` gives a nonzero derivative spanning its tangent line.
* `TauCeti.exists_notMem_range_circle_sphere`: a differentiable loop in a sphere of dimension
  at least two omits a point.
-/

public section

noncomputable section

open Function Manifold Metric Module Set
open scoped Manifold InnerProductSpace ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The preferred chart of the sphere at `v` is the stereographic projection from `-v`. -/
theorem chartAt_sphere (v : sphere (0 : E) 1) :
    chartAt (EuclideanSpace ℝ (Fin n)) v = stereographic' n (-v) :=
  rfl

-- Not `@[simp]`: simp unfolds `extChartAt (𝓡 n) v v` to `chartAt _ v v` before this lemma can
-- fire, so it fails `simpNF`.
/-- The preferred extended chart of the sphere at `v` sends `v` to the origin. -/
theorem extChartAt_sphere_apply_self (v : sphere (0 : E) 1) : extChartAt (𝓡 n) v v = 0 := by
  rw [extChartAt_coe, modelWithCornersSelf_coe, id_comp, chartAt_sphere, stereographic',
    OpenPartialHomeomorph.trans_apply, stereographic_neg_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, LinearIsometryEquiv.coe_toHomeomorph, map_zero]

end TauCeti

/-! ### Smooth embeddings of spheres induced by linear isometries -/

namespace LinearIsometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {m : ℕ}
  [Fact (finrank ℝ F = m + 1)] (ι : F →ₗᵢ[ℝ] E)

/-- Stereographic projection commutes with a linear isometry `ι`: the projection from `ι v` of the
image of `x` is the image of the projection from `v` of `x`, read in the orthogonal complement
of `ι v` through `LinearIsometry.orthogonalComplementSingletonMap`. -/
theorem stereographic_unitSphereMap (v x : sphere (0 : F) 1) :
    stereographic (norm_eq_of_mem_sphere (ι.unitSphereMap v)) (ι.unitSphereMap x) =
      ι.orthogonalComplementSingletonMap (ι.coe_unitSphereMap_apply v).symm
        (stereographic (norm_eq_of_mem_sphere v) x) := by
  -- `ι` maps the line `ℝ ∙ v` onto the line `ℝ ∙ ι v`, so it commutes with the orthogonal
  -- projections onto the orthogonal complements of these lines.
  have key : (ℝ ∙ (ι v : E))ᗮ.starProjection (ι x) = ι ((ℝ ∙ (v : F))ᗮ.starProjection x) := by
    have h := ι.map_starProjection (ℝ ∙ (v : F)) x
    simp only [Submodule.map_span, Set.image_singleton, coe_toLinearMap] at h
    simp only [Submodule.starProjection_orthogonal_val, map_sub, h]
  apply Subtype.ext
  simp only [stereographic_apply, Submodule.coe_smul, Submodule.coe_orthogonalProjectionOnto_apply,
    coe_unitSphereMap_apply, coe_orthogonalComplementSingletonMap_apply, ι.inner_map_map, key,
    map_smul]

/-- The linear isometry of model Euclidean spaces through which the stereographic charts at `v`
and at `ι v` read the map `ι` of unit spheres: conjugate the restriction of `ι` to the orthogonal
complement of `v` by the orthonormal bases that `stereographic'` uses. -/
def stereographicModelMap (v : sphere (0 : F) 1) :
    EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton n
      (ne_zero_of_mem_unit_sphere (ι.unitSphereMap v))).repr.toLinearIsometry.comp
    ((ι.orthogonalComplementSingletonMap (ι.coe_unitSphereMap_apply v).symm).comp
      (OrthonormalBasis.fromOrthogonalSpanSingleton m
        (ne_zero_of_mem_unit_sphere v)).repr.symm.toLinearIsometry)

/-- In the stereographic charts at `v` and at `ι v`, the map of unit spheres induced by `ι` reads
as the linear isometry `LinearIsometry.stereographicModelMap` of the model spaces. -/
theorem stereographic'_unitSphereMap (v x : sphere (0 : F) 1) :
    stereographic' n (ι.unitSphereMap v) (ι.unitSphereMap x) =
      ι.stereographicModelMap v (stereographic' m v x) := by
  simp only [stereographic', stereographicModelMap, OpenPartialHomeomorph.trans_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, LinearIsometryEquiv.coe_toHomeomorph, coe_comp,
    comp_apply, LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply,
    stereographic_unitSphereMap]

variable {k : ℕ∞ω}

/-- The restriction of a linear isometry to the unit spheres is an immersion at every point: in
the preferred stereographic charts it is a linear isometry of model spaces, hence the inclusion
of a factor of a product decomposition of the target model. -/
theorem isImmersionAt_unitSphereMap (x : sphere (0 : F) 1) :
    IsImmersionAt (𝓡 m) (𝓡 n) k ι.unitSphereMap x := by
  refine (IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt
    ι.continuous_unitSphereMap.continuousAt (ι.stereographicModelMap (-x)).prodOrthogonalRangeEquiv
    fun u _ ↦ ?_).isImmersionAt
  simp only [comp_apply, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, id_eq, TauCeti.chartAt_sphere, ← ι.unitSphereMap_neg,
    prodOrthogonalRangeEquiv_apply_zero]
  rw [ι.stereographic'_unitSphereMap (m := m), (stereographic' m (-x)).right_inv (by simp)]

/-- The restriction of a linear isometry to the unit spheres is a `C^k` immersion. -/
theorem isImmersion_unitSphereMap : IsImmersion (𝓡 m) (𝓡 n) k ι.unitSphereMap :=
  TauCeti.isImmersion_iff_forall_isImmersionAt.2 (ι.isImmersionAt_unitSphereMap)

/-- The restriction of a linear isometry to the unit spheres is a `C^k` smooth embedding. -/
theorem isSmoothEmbedding_unitSphereMap : IsSmoothEmbedding (𝓡 m) (𝓡 n) k ι.unitSphereMap :=
  ⟨ι.isImmersion_unitSphereMap, ι.isEmbedding_unitSphereMap⟩

end LinearIsometry

/-! ### The derivative of the circle exponential -/

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

/-- The derivative of `Circle.exp : ℝ → S¹` is injective at every point. -/
theorem injective_mfderiv_circleExp (t : ℝ) :
    Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) := by
  -- Composed with the inclusion `S¹ → ℂ`, it is the derivative `i exp (t i) ≠ 0` of `exp (t i)`.
  have he0 : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t ≠ 0 := by
    intro h0
    have hcoe : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) (Circle.exp t) :=
      (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
    have hcomp := mfderiv_comp t hcoe
      ((contMDiff_circleExp (m := 1)).mdifferentiableAt one_ne_zero)
    rw [h0, ContinuousLinearMap.comp_zero, mfderiv_eq_fderiv] at hcomp
    have hd : HasDerivAt (fun s : ℝ => ((Circle.exp s : Circle) : ℂ))
        (Complex.exp (t * Complex.I) * Complex.I) t := by
      simp only [Circle.coe_exp]
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).cexp
    have h1 := congrArg (fun L => L (1 : ℝ)) hcomp
    -- `fromTangentSpace` identifies the tangent spaces of `ℝ` and `ℂ` with `ℝ` and `ℂ` by the
    -- identity map, and has no simp lemmas, so `change` unfolds it.
    change fderiv ℝ (fun s : ℝ => ((Circle.exp s : Circle) : ℂ)) t 1 = 0 at h1
    rw [hd.hasFDerivAt.fderiv] at h1
    simp [Complex.exp_ne_zero] at h1
  set e : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t
  have hne : e 1 ≠ 0 := fun h0 => he0 (ContinuousLinearMap.ext_ring (by rw [h0]; rfl))
  refine (injective_iff_map_eq_zero e).mpr fun s hs => ?_
  have hs' : s • e 1 = 0 := by rw [← map_smul, smul_eq_mul, mul_one]; exact hs
  exact (smul_eq_zero.mp hs').resolve_right hne

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- For a `C¹` immersion `f` of the circle, the derivative of `t ↦ f (exp (t i))` is nonzero and
spans the range of the derivative of `f`. -/
theorem deriv_comp_circleExp_ne_zero_and_range_mfderiv {f : Circle → V}
    (hf : ContMDiff (𝓡 1) 𝓘(ℝ, V) 1 f) (himm : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, V) f z))
    (t : ℝ) :
    deriv (f ∘ Circle.exp) t ≠ 0 ∧
      (mfderiv (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t) : EuclideanSpace ℝ (Fin 1) →L[ℝ] V).range =
        ℝ ∙ deriv (f ∘ Circle.exp) t := by
  set D : EuclideanSpace ℝ (Fin 1) →L[ℝ] V := mfderiv (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t)
  set e : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t
  have he_inj : Injective e := injective_mfderiv_circleExp t
  have he_surj : Surjective e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := ℝ)
      (V₂ := EuclideanSpace ℝ (Fin 1)) (by simp)).mp he_inj
  have hD_inj : Injective D := himm _
  have hγ : ContDiff ℝ 1 (f ∘ Circle.exp) :=
    contMDiff_iff_contDiff.mp (hf.comp contMDiff_circleExp)
  -- The chain rule, with the derivative of the curve `f ∘ exp` written as a span map.
  have hD : ContinuousLinearMap.toSpanSingleton ℝ (deriv (f ∘ Circle.exp) t) = D.comp e := by
    have hcomp := mfderiv_comp t (hf.mdifferentiableAt one_ne_zero)
      ((contMDiff_circleExp (m := 1)).mdifferentiableAt one_ne_zero)
    rw [mfderiv_eq_fderiv, ((hγ.differentiable one_ne_zero) t).hasDerivAt.hasFDerivAt.fderiv]
      at hcomp
    exact hcomp
  have hDe : D (e 1) = deriv (f ∘ Circle.exp) t := by
    simpa using (congrArg (fun L => L 1) hD).symm
  refine ⟨fun h0 => one_ne_zero (he_inj (hD_inj (by rw [hDe, h0, map_zero, map_zero]))), ?_⟩
  rw [← LinearMap.range_toSpanSingleton]
  have := congrArg (fun L : ℝ →L[ℝ] V => (L : ℝ →ₗ[ℝ] V).range) hD
  simp only [ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr he_surj)] at this
  exact this.symm

/-! ### Points omitted by differentiable loops -/

/-- A differentiable loop in a sphere of dimension at least two omits a point.
No immersion or injectivity assumption is needed. -/
theorem exists_notMem_range_circle_sphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (finrank ℝ E = n + 1)] (hn : 2 ≤ n)
    {f : Circle → sphere (0 : E) 1} (hf : MDifferentiable (𝓡 1) (𝓡 n) f) :
    ∃ p : sphere (0 : E) 1, p ∉ range f := by
  -- The cone over the loop is the image of a differentiable map from a plane.
  have hγ : Differentiable ℝ (fun t => (f (Circle.exp t) : E)) :=
    mdifferentiable_iff_differentiable.mp <|
      ((contMDiff_coe_sphere (m := 1)).mdifferentiable one_ne_zero).comp
        (hf.comp ((contMDiff_circleExp (m := 1)).mdifferentiable one_ne_zero))
  let F : ℝ × ℝ → E := fun q => q.1 • (f (Circle.exp q.2) : E)
  have hF : Differentiable ℝ F := differentiable_fst.smul (hγ.comp differentiable_snd)
  obtain ⟨a, ha⟩ := (hF.dense_compl_range_of_finrank_lt_finrank (by
    rw [Module.finrank_prod, Module.finrank_self, (Fact.out : finrank ℝ E = n + 1)]
    omega)).nonempty
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨(0, 0), by simp [F]⟩
  have hnorm : ‖‖a‖⁻¹ • a‖ = 1 := norm_smul_inv_norm ha0
  refine ⟨⟨‖a‖⁻¹ • a, mem_sphere_zero_iff_norm.mpr hnorm⟩, ?_⟩
  rintro ⟨z, hz⟩
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  have hz' := congrArg Subtype.val hz
  refine ha ⟨(‖a‖, t), ?_⟩
  simp only [F, hz', smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha0), one_smul]

end TauCeti
