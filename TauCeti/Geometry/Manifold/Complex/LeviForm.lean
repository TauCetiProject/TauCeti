/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pseudoconvex
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
public import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
public import TauCeti.Geometry.Manifold.Morse.Hessian

/-!
# The Levi form on a complex manifold

Let `M` be a complex manifold modelled on `𝓘(ℂ, E)`, and let `f : M → ℝ`. The **Levi form**
`TauCeti.manifoldLeviForm E f x` of `f` at `x` is the Levi form `TauCeti.leviForm` of the
coordinate expression of `f` in the preferred chart at `x`. It is a sesquilinear form on the model
space `E`, which is the tangent space at `x`.

Unlike the real Hessian, the Levi form of a function which is real `C²` at `x` is intrinsic at
every point: in any chart `e` at `x` of the holomorphic `C²` maximal atlas, the Levi form of the
coordinate expression `f ∘ e.symm`, evaluated on the images of tangent vectors under the derivative
of `e`, is `TauCeti.manifoldLeviForm E f x`. This is because the second derivative of a holomorphic
chart transition is complex bilinear and does not contribute to the Levi form.

The underlying real manifold of `M` is modelled on `𝓘(ℝ, E)`, with the same charts, and its
holomorphic charts are real `C²` charts (`IsManifold.maximalAtlas_subset_restrictScalars`). Its
critical Hessian `TauCeti.criticalHessian 𝓘(ℝ, E) f x` is the real second derivative in the
preferred chart, and the Levi form of `f` is the Levi form of this real bilinear form. In
particular, for `C²` `f` the diagonal of the Levi form is one quarter of
`Hess f(v, v) + Hess f(I • v, I • v)`. At a critical point the critical Hessian is intrinsic as
well, and this diagonal may be computed from the real Hessian in any real `C²` chart.
Strict plurisubharmonicity and strong `q`-pseudoconvexity of `f` at `x` are positivity conditions
on `TauCeti.manifoldLeviForm E f x`, so for `f` real `C²` at `x` they may be checked in any
holomorphic chart. Consequently the index bounds of strongly `q`-pseudoconvex functions hold for
the manifold Morse index: at a critical point where `f` is strongly `q`-pseudoconvex, the Morse
index is at most `dim_ℂ E + q`.

## Main definitions

* `TauCeti.manifoldLeviForm E f x`: the Levi form of `f` at `x`, computed in the preferred chart.
* `TauCeti.IsManifoldStrictlyPlurisubharmonicAt E f x`,
  `TauCeti.IsManifoldStronglyPseudoconvexAt E q f x`: positive definiteness of the Levi form at
  `x`, on all of `E` or on a complex subspace of codimension at most `q`.

## Main results

* `TauCeti.leviForm_comp_symm_apply_of_mem_maximalAtlas`: for `f` real `C²` at `x`, the Levi
  form of the coordinate expression in any holomorphic `C²` chart at `x` is the manifold Levi
  form.
* `TauCeti.re_manifoldLeviForm_apply`, `TauCeti.im_manifoldLeviForm_apply`: the real and imaginary
  parts of the Levi form in terms of the real critical Hessian.
* `TauCeti.manifoldLeviForm_apply_self`: for `C²` `f`, its diagonal is the real number
  `(Hess f(v, v) + Hess f(I • v, I • v)) / 4`.
* `TauCeti.manifoldLeviForm_add`, `TauCeti.manifoldLeviForm_neg`,
  `TauCeti.manifoldLeviForm_mul_apply`, `TauCeti.manifoldLeviForm_scalar_comp_apply`: the sum,
  negation, product and composition rules.
* `TauCeti.manifoldLeviForm_comp_apply`: the pullback rule under a complex `C²` map.
* `TauCeti.le_re_manifoldLeviForm_scalar_comp_apply_self`: post-composition with an increasing
  convex function preserves positivity of the Levi form.
* `TauCeti.isManifoldStrictlyPlurisubharmonicAt_iff_criticalHessian`: strict plurisubharmonicity
  in terms of the real critical Hessian.
* `TauCeti.IsManifoldStrictlyPlurisubharmonicAt.scalar_comp` and
  `TauCeti.IsManifoldStronglyPseudoconvexAt.scalar_comp`: increasing convex post-composition
  preserves the corresponding positivity conditions.
* `TauCeti.IsManifoldStrictlyPlurisubharmonicAt.comp` and
  `TauCeti.IsManifoldStronglyPseudoconvexAt.comp`: the positivity conditions restrict along
  holomorphic immersions.
* `TauCeti.re_manifoldLeviForm_apply_of_mem_maximalAtlas` and
  `TauCeti.im_manifoldLeviForm_apply_of_mem_maximalAtlas`: at a critical point, the real and
  imaginary parts may be computed from the real Hessian in any real `C²` chart.
* `TauCeti.manifoldLeviForm_apply_self_of_mem_maximalAtlas`: at a critical point the same holds
  with the real Hessian computed in any real `C²` chart.
* `TauCeti.isManifoldStrictlyPlurisubharmonicAt_iff_of_mem_maximalAtlas` and
  `TauCeti.isManifoldStronglyPseudoconvexAt_iff_of_mem_maximalAtlas`: for `f` real `C²` at `x`,
  these positivity conditions may be checked in any holomorphic chart.
* `TauCeti.IsManifoldStronglyPseudoconvexAt.manifoldMorseIndex_le` and
  `TauCeti.IsManifoldStrictlyPlurisubharmonicAt.manifoldMorseIndex_le`: the manifold Morse index
  bounds `λ ≤ n + q` and `λ ≤ n` at critical points.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

open Complex Filter Function Module Set Topology
open scoped ComplexConjugate ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M]
  [ChartedSpace E M] {f : M → ℝ} {x : M}

variable (E) in
/-- The **Levi form** of a real function `f` on a complex manifold at `x`: the Levi form of the
coordinate expression of `f` in the preferred chart at `x`. It is a sesquilinear form on the model
space `E`, which is the tangent space `TangentSpace 𝓘(ℂ, E) x`. By
`TauCeti.leviForm_comp_symm_apply_of_mem_maximalAtlas`, when `f` is real `C²` at `x` it may be
computed in any chart at `x` of the holomorphic `C²` maximal atlas. -/
def manifoldLeviForm (f : M → ℝ) (x : M) : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ :=
  leviForm (f ∘ (chartAt E x).symm) (chartAt E x x)

/-- The manifold Levi form is the Levi form of the coordinate expression in the preferred chart. -/
theorem manifoldLeviForm_def :
    manifoldLeviForm E f x = leviForm (f ∘ (chartAt E x).symm) (chartAt E x x) :=
  (rfl)

/-- The Levi form of a function depends only on its germ. -/
theorem manifoldLeviForm_congr_of_eventuallyEq {g : M → ℝ} (hfg : f =ᶠ[𝓝 x] g) :
    manifoldLeviForm E f x = manifoldLeviForm E g x := by
  have hchart : (chartAt E x).symm (chartAt E x x) = x :=
    (chartAt E x).left_inv (mem_chart_source E x)
  have hfg' : f ∘ (chartAt E x).symm =ᶠ[𝓝 (chartAt E x x)] g ∘ (chartAt E x).symm :=
    (hchart ▸ hfg).comp_tendsto ((chartAt E x).continuousAt_symm (mem_chart_target E x))
  rw [manifoldLeviForm_def, manifoldLeviForm_def, leviForm_congr_of_eventuallyEq hfg']

/-! ### Comparison with the real critical Hessian -/

/-- The real part of the Levi form is one quarter of the sum
`Hess f(v, w) + Hess f(I • v, I • w)` of critical-Hessian values, that is, one half of the
`I`-invariant part of the critical Hessian. -/
@[simp]
theorem re_manifoldLeviForm_apply (v w : E) :
    (manifoldLeviForm E f x v w).re =
      (criticalHessian 𝓘(ℝ, E) f x v w + criticalHessian 𝓘(ℝ, E) f x (I • v) (I • w)) / 4 := by
  rw [manifoldLeviForm_def, re_leviForm_apply, fderiv_fderiv_comp_chartAt_symm,
    fderiv_fderiv_comp_chartAt_symm]

/-- The imaginary part of the Levi form is one quarter of the mixed difference
`Hess f(I • v, w) - Hess f(v, I • w)` of critical-Hessian values. Only the `I`-invariant part of
the critical Hessian contributes; its `I`-anti-invariant part cancels in this difference. -/
@[simp]
theorem im_manifoldLeviForm_apply (v w : E) :
    (manifoldLeviForm E f x v w).im =
      (criticalHessian 𝓘(ℝ, E) f x (I • v) w - criticalHessian 𝓘(ℝ, E) f x v (I • w)) / 4 := by
  rw [manifoldLeviForm_def, im_leviForm_apply, fderiv_fderiv_comp_chartAt_symm,
    fderiv_fderiv_comp_chartAt_symm]

/-- **The diagonal of the Levi form.** For a function which is `C²` at `x`, the diagonal value of
the Levi form on `v` is the real number `(Hess f(v, v) + Hess f(I • v, I • v)) / 4`, where `Hess`
is the critical Hessian of `f` on the real manifold underlying `M`. -/
theorem manifoldLeviForm_apply_self (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) (v : E) :
    manifoldLeviForm E f x v v =
      ((criticalHessian 𝓘(ℝ, E) f x v v + criticalHessian 𝓘(ℝ, E) f x (I • v) (I • v)) / 4 :
        ℝ) := by
  rw [manifoldLeviForm_def, leviForm_apply_self hf.contDiffAt_comp_chartAt_symm,
    hessianQuadraticForm_apply, hessianQuadraticForm_apply, fderiv_fderiv_comp_chartAt_symm,
    fderiv_fderiv_comp_chartAt_symm]

/-- The Levi form of a function which is `C²` at `x` is Hermitian. -/
theorem isSymm_manifoldLeviForm (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) :
    (manifoldLeviForm E f x).IsSymm :=
  isSymm_leviForm hf.contDiffAt_comp_chartAt_symm

/-! ### Algebraic rules -/

/-- **The sum rule** for the Levi form on a complex manifold. -/
theorem manifoldLeviForm_add {g : M → ℝ} (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x)
    (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 g x) :
    manifoldLeviForm E (f + g) x = manifoldLeviForm E f x + manifoldLeviForm E g x :=
  leviForm_add hf.contDiffAt_comp_chartAt_symm hg.contDiffAt_comp_chartAt_symm

/-- Negating a function negates its Levi form on a complex manifold. -/
@[simp]
theorem manifoldLeviForm_neg (f : M → ℝ) (x : M) :
    manifoldLeviForm E (-f) x = -manifoldLeviForm E f x :=
  leviForm_neg (f ∘ (chartAt E x).symm) (chartAt E x x)

/-- **The product rule** for the Levi form on a complex manifold. Writing `∂f` for the
complex-linear extension `StrongDual.extendRCLike` of the real differential `mvfderiv 𝓘(ℝ, E) f x`,
the Levi form of `f g` at `x` is `f(x) L g + g(x) L f + (conj (∂f v) ∂g w + conj (∂g v) ∂f w) / 4`.
-/
theorem manifoldLeviForm_mul_apply {g : M → ℝ} (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x)
    (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 g x) (v w : E) :
    manifoldLeviForm E (f * g) x v w =
      f x * manifoldLeviForm E g x v w + g x * manifoldLeviForm E f x v w +
        (4 : ℂ)⁻¹ *
          (conj ((StrongDual.extendRCLike (F := E) (mvfderiv 𝓘(ℝ, E) f x) : StrongDual ℂ E) v) *
              (StrongDual.extendRCLike (F := E) (mvfderiv 𝓘(ℝ, E) g x) : StrongDual ℂ E) w +
            conj ((StrongDual.extendRCLike (F := E) (mvfderiv 𝓘(ℝ, E) g x) : StrongDual ℂ E) v) *
              (StrongDual.extendRCLike (F := E) (mvfderiv 𝓘(ℝ, E) f x) : StrongDual ℂ E) w) := by
  have h := leviForm_mul_apply hf.contDiffAt_comp_chartAt_symm
    hg.contDiffAt_comp_chartAt_symm v w
  rwa [(hf.mdifferentiableAt (by norm_num)).fderiv_comp_chartAt_symm,
    (hg.mdifferentiableAt (by norm_num)).fderiv_comp_chartAt_symm, comp_apply, comp_apply,
    (chartAt E x).left_inv (mem_chart_source E x)] at h

/-- **The composition rule** for the Levi form on a complex manifold, for post-composition with a
function of one real variable. Writing `∂f` for the complex-linear extension
`StrongDual.extendRCLike` of `mvfderiv 𝓘(ℝ, E) f x`, the Levi form of `φ ∘ f` at `x` is
`φ'(f x) L f + φ''(f x) conj (∂f v) ∂f w / 4`. -/
theorem manifoldLeviForm_scalar_comp_apply {φ : ℝ → ℝ} (hφ : ContDiffAt ℝ 2 φ (f x))
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) (v w : E) :
    manifoldLeviForm E (φ ∘ f) x v w =
      deriv φ (f x) * manifoldLeviForm E f x v w +
        iteratedDeriv 2 φ (f x) * ((4 : ℂ)⁻¹ *
          (conj ((StrongDual.extendRCLike (F := E) (mvfderiv 𝓘(ℝ, E) f x) : StrongDual ℂ E) v) *
            (StrongDual.extendRCLike (F := E) (mvfderiv 𝓘(ℝ, E) f x) : StrongDual ℂ E) w)) := by
  have hφ' : ContDiffAt ℝ 2 φ ((f ∘ (chartAt E x).symm) (chartAt E x x)) := by
    rwa [comp_apply, (chartAt E x).left_inv (mem_chart_source E x)]
  have h := leviForm_scalar_comp_apply hφ' hf.contDiffAt_comp_chartAt_symm v w
  rwa [(hf.mdifferentiableAt (by norm_num)).fderiv_comp_chartAt_symm, comp_apply,
    (chartAt E x).left_inv (mem_chart_source E x)] at h

/-- **Post-composition with a convex function** on a complex manifold. If `φ'' ≥ 0` at `f x`, then
the diagonal of the Levi form of `φ ∘ f` dominates `φ'(f x)` times the diagonal of the Levi form
of `f`. In particular, if moreover `φ'(f x) > 0`, post-composition with `φ` preserves strict
positivity of the Levi form at `x`. -/
theorem le_re_manifoldLeviForm_scalar_comp_apply_self {φ : ℝ → ℝ} (hφ : ContDiffAt ℝ 2 φ (f x))
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) (hφ₂ : 0 ≤ iteratedDeriv 2 φ (f x)) (v : E) :
    deriv φ (f x) * (manifoldLeviForm E f x v v).re ≤
      (manifoldLeviForm E (φ ∘ f) x v v).re := by
  have hfx : (f ∘ (chartAt E x).symm) (chartAt E x x) = f x := by
    rw [comp_apply, (chartAt E x).left_inv (mem_chart_source E x)]
  have h := le_re_leviForm_scalar_comp_apply_self (hfx ▸ hφ) hf.contDiffAt_comp_chartAt_symm
    (hfx ▸ hφ₂) v
  rwa [hfx] at h

section Pullback

variable {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace N]
  [ChartedSpace F N] {g : M → N} {u : N → ℝ}

/-- **The holomorphic pullback rule** for the Levi form on complex manifolds. If `g` is complex
`C²` at `x` and `u` is real `C²` at `g x`, then the Levi form of `u ∘ g` is the pullback of the
Levi form of `u` by the complex manifold derivative of `g`. -/
theorem manifoldLeviForm_comp_apply (hu : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ) 2 u (g x))
    (hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 g x) (v w : E) :
    manifoldLeviForm E (u ∘ g) x v w =
      manifoldLeviForm F u (g x) (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) g x v)
        (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) g x w) := by
  let G : E → F := chartAt F (g x) ∘ g ∘ (chartAt E x).symm
  have hx' : (chartAt E x).symm (chartAt E x x) = x :=
    (chartAt E x).left_inv (mem_chart_source E x)
  have hG : ContDiffAt ℂ 2 G (chartAt E x x) := by
    rw [← contDiffWithinAt_univ]
    simpa only [G, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, id_comp, comp_id, Set.range_id] using
      (contMDiffAt_iff.mp hg).2
  have hGx : G (chartAt E x x) = chartAt F (g x) (g x) := by
    simp only [G, Function.comp_apply, hx']
  have hD : fderiv ℂ G (chartAt E x x) = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) g x := by
    rw [(hg.mdifferentiableAt (by norm_num)).mfderiv_abuse]
    have hcoord : writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, F) x g = G := by
      ext z
      rfl
    have hpoint : extChartAt 𝓘(ℂ, E) x x = chartAt E x x := by rfl
    rw [hcoord, modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ, hpoint]
  have hcomp : (u ∘ g) ∘ (chartAt E x).symm =ᶠ[𝓝 (chartAt E x x)]
      (u ∘ (chartAt F (g x)).symm) ∘ G := by
    have hcont : Tendsto (g ∘ (chartAt E x).symm) (𝓝 (chartAt E x x)) (𝓝 (g x)) := by
      simpa only [ContinuousAt, Function.comp_apply, hx'] using hg.continuousAt.comp_of_eq
        ((chartAt E x).continuousAt_symm (mem_chart_target E x)) hx'
    have hmem : (g ∘ (chartAt E x).symm) ⁻¹' (chartAt F (g x)).source ∈
        𝓝 (chartAt E x x) :=
      hcont ((chartAt F (g x)).open_source.mem_nhds (mem_chart_source F (g x)))
    filter_upwards [hmem] with z hz
    simp only [G, Function.comp_apply]
    have hz' : g ((chartAt E x).symm z) ∈ (chartAt F (g x)).source := hz
    rw [(chartAt F (g x)).left_inv hz']
  rw [manifoldLeviForm_def, manifoldLeviForm_def, leviForm_congr_of_eventuallyEq hcomp]
  rw [TauCeti.leviForm_comp_apply (hGx ▸ hu.contDiffAt_comp_chartAt_symm) hG, hGx, hD]
  rfl

end Pullback

/-! ### Independence of the holomorphic chart -/

section Chart

variable [IsManifold 𝓘(ℂ, E) 2 M] {e : OpenPartialHomeomorph M E}

/-- **The Levi form in an arbitrary holomorphic chart.** Let `e` be a chart of the `C²` maximal
atlas of the complex manifold `M`, with `x` in its source, and let `f` be `C²` at `x`. The Levi
form of the coordinate expression `f ∘ e.symm` at `e x`, evaluated on the images of `v` and `w`
under the derivative of `e`, is the Levi form of `f` at `x`. Unlike the real Hessian, the Levi form
thus transforms as a Hermitian form under holomorphic changes of coordinates at every point. -/
theorem leviForm_comp_symm_apply_of_mem_maximalAtlas
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 2 M) (hx : x ∈ e.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) (v w : E) :
    leviForm (f ∘ e.symm) (e x) (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) e x v)
        (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) e x w) =
      manifoldLeviForm E f x v w := by
  set y := chartAt E x x
  have hy : (chartAt E x).symm y = x := (chartAt E x).left_inv (mem_chart_source E x)
  -- The holomorphic transition map from the preferred chart to `e`.
  set φ : E → E := e ∘ (chartAt E x).symm
  have hφy : φ y = e x := by simp only [φ, comp_apply, hy]
  have hφ : ContDiffAt ℂ 2 φ y := by
    have h := (contMDiffAt_of_mem_maximalAtlas he hx).comp_of_eq
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_target E x)) hy
    exact contMDiffAt_iff_contDiffAt.mp h
  have hDφ : fderiv ℂ φ y = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) e x := by
    rw [(mdifferentiableAt_of_mem_maximalAtlas
      (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hx).mfderiv_abuse]
    simp [writtenInExtChartAt, φ, y]
  -- The coordinate expression in `e` is `C²`, as `e` is a real `C²` chart.
  have hfe : ContDiffAt ℝ 2 (f ∘ e.symm) (φ y) := by
    have h := (contMDiffAt_iff_contDiffAt_comp_extend_symm
      (IsManifold.maximalAtlas_subset_restrictScalars ℝ he) hx).mp hf
    simpa only [hφy, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id] using h
  -- Near `y`, the preferred coordinate expression factors through `φ`.
  have hfg : f ∘ (chartAt E x).symm =ᶠ[𝓝 y] (f ∘ e.symm) ∘ φ := by
    have hmem : (chartAt E x).symm ⁻¹' e.source ∈ 𝓝 y :=
      ((chartAt E x).continuousAt_symm (mem_chart_target E x)).preimage_mem_nhds
        (by rw [hy]; exact e.open_source.mem_nhds hx)
    filter_upwards [hmem] with z hz
    simp only [φ, comp_apply, e.left_inv hz]
  rw [manifoldLeviForm_def, leviForm_congr_of_eventuallyEq hfg,
    leviForm_comp_apply (hφy ▸ hfe) hφ, hDφ, hφy]
  -- The two sides differ only in reading the model space `E` as the tangent spaces of `M`.
  rfl

end Chart

/-! ### Strict plurisubharmonicity and strong pseudoconvexity -/

section Positivity

variable (E) in
/-- A real function `f` on a complex manifold is **strictly plurisubharmonic** at `x` if its Levi
form at `x` is positive definite: `0 < Re (manifoldLeviForm E f x v v)` for every nonzero `v`
(`TauCeti.isManifoldStrictlyPlurisubharmonicAt_iff`). As for `TauCeti.manifoldLeviForm`, it is
defined in the preferred chart at `x`; by
`TauCeti.isManifoldStrictlyPlurisubharmonicAt_iff_of_mem_maximalAtlas`, for `f` real `C²` at `x` it
may be checked in any chart at `x` of the holomorphic `C²` maximal atlas. -/
def IsManifoldStrictlyPlurisubharmonicAt (f : M → ℝ) (x : M) : Prop :=
  IsStrictlyPlurisubharmonicAt (f ∘ (chartAt E x).symm) (chartAt E x x)

variable (E) in
/-- A real function `f` on a complex manifold modelled on a finite-dimensional space `E` is
**strongly `q`-pseudoconvex** at `x` if its Levi form at `x` is positive definite on a complex
subspace `P` of `E` with `dim_ℂ E ≤ dim_ℂ P + q` (`TauCeti.isManifoldStronglyPseudoconvexAt_iff`).
As for `TauCeti.manifoldLeviForm`, it is defined in the preferred chart at `x`; by
`TauCeti.isManifoldStronglyPseudoconvexAt_iff_of_mem_maximalAtlas`, for `f` real `C²` at `x` it
may be checked in any chart at `x` of the holomorphic `C²` maximal atlas. -/
def IsManifoldStronglyPseudoconvexAt [FiniteDimensional ℂ E] (q : ℕ) (f : M → ℝ) (x : M) :
    Prop :=
  IsStronglyPseudoconvexAt q (f ∘ (chartAt E x).symm) (chartAt E x x)

/-- Strict plurisubharmonicity on a complex manifold is positive definiteness of the Levi form. -/
theorem isManifoldStrictlyPlurisubharmonicAt_iff :
    IsManifoldStrictlyPlurisubharmonicAt E f x ↔
      ∀ v : E, v ≠ 0 → 0 < (manifoldLeviForm E f x v v).re :=
  isStrictlyPlurisubharmonicAt_iff

/-- Strong `q`-pseudoconvexity on a complex manifold is positive definiteness of the Levi form on
a complex subspace of codimension at most `q`. -/
theorem isManifoldStronglyPseudoconvexAt_iff [FiniteDimensional ℂ E] {q : ℕ} :
    IsManifoldStronglyPseudoconvexAt E q f x ↔ ∃ P : Submodule ℂ E,
      finrank ℂ E ≤ finrank ℂ P + q ∧ ∀ v ∈ P, v ≠ 0 → 0 < (manifoldLeviForm E f x v v).re :=
  isStronglyPseudoconvexAt_iff

/-- Strict plurisubharmonicity on a complex manifold in terms of the real critical Hessian: `f` is
strictly plurisubharmonic at `x` exactly when `Hess f(v, v) + Hess f(I • v, I • v) > 0` for every
`v ≠ 0`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_iff_criticalHessian :
    IsManifoldStrictlyPlurisubharmonicAt E f x ↔ ∀ v : E, v ≠ 0 →
      0 < criticalHessian 𝓘(ℝ, E) f x v v + criticalHessian 𝓘(ℝ, E) f x (I • v) (I • v) := by
  simp only [isManifoldStrictlyPlurisubharmonicAt_iff, re_manifoldLeviForm_apply]
  exact forall₂_congr fun _ _ ↦ div_pos_iff_of_pos_right (by norm_num)

/-- Strong `q`-pseudoconvexity on a complex manifold is weaker for larger `q`. -/
theorem IsManifoldStronglyPseudoconvexAt.mono [FiniteDimensional ℂ E] {q r : ℕ}
    (h : IsManifoldStronglyPseudoconvexAt E q f x) (hqr : q ≤ r) :
    IsManifoldStronglyPseudoconvexAt E r f x := by
  rw [isManifoldStronglyPseudoconvexAt_iff] at h ⊢
  obtain ⟨P, hP, hpos⟩ := h
  exact ⟨P, by omega, hpos⟩

/-- Strong `0`-pseudoconvexity on a complex manifold is strict plurisubharmonicity. -/
@[simp]
theorem isManifoldStronglyPseudoconvexAt_zero_iff [FiniteDimensional ℂ E] :
    IsManifoldStronglyPseudoconvexAt E 0 f x ↔
      IsManifoldStrictlyPlurisubharmonicAt E f x := by
  rw [isManifoldStronglyPseudoconvexAt_iff, isManifoldStrictlyPlurisubharmonicAt_iff]
  constructor
  · rintro ⟨P, hP, hpos⟩ v hv
    have hP : P = ⊤ := Submodule.eq_top_of_finrank_eq (le_antisymm P.finrank_le hP)
    exact hpos v (hP ▸ Submodule.mem_top) hv
  · exact fun h ↦ ⟨⊤, by simp, fun v _ hv ↦ h v hv⟩

/-- A strictly plurisubharmonic function on a complex manifold is strongly `q`-pseudoconvex for
every `q`. -/
theorem IsManifoldStrictlyPlurisubharmonicAt.isManifoldStronglyPseudoconvexAt
    [FiniteDimensional ℂ E] (h : IsManifoldStrictlyPlurisubharmonicAt E f x) (q : ℕ) :
    IsManifoldStronglyPseudoconvexAt E q f x :=
  IsStrictlyPlurisubharmonicAt.isStronglyPseudoconvexAt h q

/-- Post-composition with a function `φ` of one real variable with `φ'(f x) > 0` and
`φ''(f x) ≥ 0` preserves strict plurisubharmonicity on a complex manifold at `x`. -/
theorem IsManifoldStrictlyPlurisubharmonicAt.scalar_comp {φ : ℝ → ℝ}
    (h : IsManifoldStrictlyPlurisubharmonicAt E f x) (hφ : ContDiffAt ℝ 2 φ (f x))
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) (hφ₁ : 0 < deriv φ (f x))
    (hφ₂ : 0 ≤ iteratedDeriv 2 φ (f x)) :
    IsManifoldStrictlyPlurisubharmonicAt E (φ ∘ f) x := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff] at h ⊢
  exact fun v hv ↦ (mul_pos hφ₁ (h v hv)).trans_le
    (le_re_manifoldLeviForm_scalar_comp_apply_self hφ hf hφ₂ v)

/-- Post-composition with a function `φ` of one real variable with `φ'(f x) > 0` and
`φ''(f x) ≥ 0` preserves strong `q`-pseudoconvexity on a complex manifold at `x`. -/
theorem IsManifoldStronglyPseudoconvexAt.scalar_comp [FiniteDimensional ℂ E] {q : ℕ}
    {φ : ℝ → ℝ} (h : IsManifoldStronglyPseudoconvexAt E q f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x)
    (hφ₁ : 0 < deriv φ (f x)) (hφ₂ : 0 ≤ iteratedDeriv 2 φ (f x)) :
    IsManifoldStronglyPseudoconvexAt E q (φ ∘ f) x := by
  rw [isManifoldStronglyPseudoconvexAt_iff] at h ⊢
  obtain ⟨P, hP, hpos⟩ := h
  exact ⟨P, hP, fun v hv hv0 ↦ (mul_pos hφ₁ (hpos v hv hv0)).trans_le
    (le_re_manifoldLeviForm_scalar_comp_apply_self hφ hf hφ₂ v)⟩

/-- Strict plurisubharmonicity on a complex manifold at `x` depends only on the germ of the
function at `x`. -/
theorem IsManifoldStrictlyPlurisubharmonicAt.congr_of_eventuallyEq {g : M → ℝ}
    (h : IsManifoldStrictlyPlurisubharmonicAt E f x) (hfg : g =ᶠ[𝓝 x] f) :
    IsManifoldStrictlyPlurisubharmonicAt E g x := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff, manifoldLeviForm_congr_of_eventuallyEq hfg]
  exact isManifoldStrictlyPlurisubharmonicAt_iff.mp h

/-- Strong `q`-pseudoconvexity on a complex manifold at `x` depends only on the germ of the
function at `x`. -/
theorem IsManifoldStronglyPseudoconvexAt.congr_of_eventuallyEq [FiniteDimensional ℂ E] {q : ℕ}
    {g : M → ℝ} (h : IsManifoldStronglyPseudoconvexAt E q f x) (hfg : g =ᶠ[𝓝 x] f) :
    IsManifoldStronglyPseudoconvexAt E q g x := by
  rw [isManifoldStronglyPseudoconvexAt_iff, manifoldLeviForm_congr_of_eventuallyEq hfg]
  exact isManifoldStronglyPseudoconvexAt_iff.mp h

/-- The sum of two `C²` functions strictly plurisubharmonic at `x` on a complex manifold is
strictly plurisubharmonic at `x`. -/
theorem IsManifoldStrictlyPlurisubharmonicAt.add {g : M → ℝ}
    (hf : IsManifoldStrictlyPlurisubharmonicAt E f x)
    (hg : IsManifoldStrictlyPlurisubharmonicAt E g x) (hf' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x)
    (hg' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 g x) :
    IsManifoldStrictlyPlurisubharmonicAt E (f + g) x := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff] at hf hg ⊢
  intro v hv
  rw [manifoldLeviForm_add hf' hg']
  simpa using add_pos (hf v hv) (hg v hv)

section Pullback

variable {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace N]
  [ChartedSpace F N] {g : M → N} {u : N → ℝ}

/-- **Restriction along a holomorphic immersion** of complex manifolds. If `u` is strictly
plurisubharmonic at `g x` and the complex manifold derivative of the complex `C²` map `g` at `x` is
injective, then `u ∘ g` is strictly plurisubharmonic at `x`. -/
theorem IsManifoldStrictlyPlurisubharmonicAt.comp
    (h : IsManifoldStrictlyPlurisubharmonicAt F u (g x))
    (hu : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ) 2 u (g x)) (hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 g x)
    (hg' : Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) g x)) :
    IsManifoldStrictlyPlurisubharmonicAt E (u ∘ g) x := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff] at h ⊢
  intro v hv
  rw [manifoldLeviForm_comp_apply hu hg]
  exact h _ ((map_ne_zero_iff _ hg').2 hv)

/-- **Restriction along a holomorphic immersion** of complex manifolds. If `u` is strongly
`q`-pseudoconvex at `g x` and the complex manifold derivative of the complex `C²` map `g` at `x` is
injective, then `u ∘ g` is strongly `q`-pseudoconvex at `x`: the preimage of a positive subspace of
codimension at most `q` is a positive subspace of codimension at most `q`. -/
theorem IsManifoldStronglyPseudoconvexAt.comp [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {q : ℕ} (h : IsManifoldStronglyPseudoconvexAt F q u (g x))
    (hu : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ) 2 u (g x)) (hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 g x)
    (hg' : Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) g x)) :
    IsManifoldStronglyPseudoconvexAt E q (u ∘ g) x := by
  rw [isManifoldStronglyPseudoconvexAt_iff] at h ⊢
  obtain ⟨P, hP, hpos⟩ := h
  -- The manifold derivative of `g`, typed on the model spaces.
  let D : E →L[ℂ] F := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) g x
  refine ⟨P.comap (D : E →ₗ[ℂ] F), ?_, fun v hv hv0 ↦ ?_⟩
  · have := Submodule.finrank_add_finrank_le_finrank_comap_add_finrank (D : E →ₗ[ℂ] F) P
    omega
  · rw [manifoldLeviForm_comp_apply hu hg]
    exact hpos _ hv ((map_ne_zero_iff _ hg').2 hv0)

end Pullback

variable [IsManifold 𝓘(ℂ, E) 2 M] {e : OpenPartialHomeomorph M E}

/-- **Strict plurisubharmonicity in an arbitrary holomorphic chart.** For `f` real `C²` at `x` and
a chart `e` at `x` of the holomorphic `C²` maximal atlas, `f` is strictly plurisubharmonic at `x`
if and only if its coordinate expression `f ∘ e.symm` is strictly plurisubharmonic at `e x`. -/
theorem isManifoldStrictlyPlurisubharmonicAt_iff_of_mem_maximalAtlas
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 2 M) (hx : x ∈ e.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) :
    IsManifoldStrictlyPlurisubharmonicAt E f x ↔
      IsStrictlyPlurisubharmonicAt (f ∘ e.symm) (e x) := by
  -- The invertible chart derivative, typed on the model space `E`.
  obtain ⟨D, hD⟩ : ∃ D : E ≃L[ℂ] E, (D : E →L[ℂ] E) = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) e x :=
    isInvertible_mfderiv_chart (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hx
  have key (v : E) : leviForm (f ∘ e.symm) (e x) (D v) (D v) = manifoldLeviForm E f x v v := by
    rw [← leviForm_comp_symm_apply_of_mem_maximalAtlas he hx hf, ← hD]
    -- The two sides differ only in reading `D` as a map between tangent spaces of `M`.
    rfl
  rw [isManifoldStrictlyPlurisubharmonicAt_iff, isStrictlyPlurisubharmonicAt_iff]
  refine ⟨fun h u hu ↦ ?_, fun h v hv ↦ ?_⟩
  · obtain ⟨v, rfl⟩ := D.surjective u
    rw [key]
    exact h v (by simpa using hu)
  · rw [← key]
    exact h (D v) (by simpa using hv)

/-- **Strong `q`-pseudoconvexity in an arbitrary holomorphic chart.** For `f` real `C²` at `x` and
a chart `e` at `x` of the holomorphic `C²` maximal atlas, `f` is strongly `q`-pseudoconvex at `x`
if and only if its coordinate expression `f ∘ e.symm` is strongly `q`-pseudoconvex at `e x`. -/
theorem isManifoldStronglyPseudoconvexAt_iff_of_mem_maximalAtlas [FiniteDimensional ℂ E]
    {q : ℕ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 2 M) (hx : x ∈ e.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) :
    IsManifoldStronglyPseudoconvexAt E q f x ↔
      IsStronglyPseudoconvexAt q (f ∘ e.symm) (e x) := by
  -- The invertible chart derivative, typed on the model space `E`.
  obtain ⟨D, hD⟩ : ∃ D : E ≃L[ℂ] E, (D : E →L[ℂ] E) = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) e x :=
    isInvertible_mfderiv_chart (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hx
  have key (v : E) : leviForm (f ∘ e.symm) (e x) (D v) (D v) = manifoldLeviForm E f x v v := by
    rw [← leviForm_comp_symm_apply_of_mem_maximalAtlas he hx hf, ← hD]
    -- The two sides differ only in reading `D` as a map between tangent spaces of `M`.
    rfl
  rw [isManifoldStronglyPseudoconvexAt_iff, isStronglyPseudoconvexAt_iff]
  constructor
  · rintro ⟨P, hP, hpos⟩
    refine ⟨P.map (D.toLinearEquiv : E →ₗ[ℂ] E), by rwa [LinearEquiv.finrank_map_eq], ?_⟩
    rintro _ ⟨v, hv, rfl⟩ hv0
    simp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] at hv0 ⊢
    rw [key]
    exact hpos v hv (by simpa using hv0)
  · rintro ⟨Q, hQ, hpos⟩
    refine ⟨Q.map (D.symm.toLinearEquiv : E →ₗ[ℂ] E), by rwa [LinearEquiv.finrank_map_eq], ?_⟩
    rintro _ ⟨u, hu, rfl⟩ hu0
    simp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] at hu0 ⊢
    rw [← key, D.apply_symm_apply]
    exact hpos u hu (by simpa using hu0)

end Positivity

/-! ### Critical points -/

section Critical

variable {e : OpenPartialHomeomorph M E}

/-- **The real part of the Levi form at a critical point, in an arbitrary real chart.** For a
real `C²` chart `e`, it is the quarter-sum of the real Hessian on the chart derivatives of
`(v, w)` and `(I • v, I • w)`. -/
theorem re_manifoldLeviForm_apply_of_mem_maximalAtlas
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M) (hx : x ∈ e.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) (hcrit : mvfderiv 𝓘(ℝ, E) f x = 0) (v w : E) :
    (manifoldLeviForm E f x v w).re =
      (fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x w) +
        fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (I • v))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (I • w))) / 4 := by
  have h₁ := criticalHessian_apply_eq_of_mem_maximalAtlas he hx hf hcrit v w
  have h₂ := criticalHessian_apply_eq_of_mem_maximalAtlas he hx hf hcrit (I • v) (I • w)
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id] at h₁ h₂
  rw [re_manifoldLeviForm_apply]
  -- On the model space `E`, `mvfderiv 𝓘(ℝ, E) e x` is `mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x` by definition.
  exact congrArg₂ (fun a b : ℝ ↦ (a + b) / 4) h₁ h₂

/-- **The imaginary part of the Levi form at a critical point, in an arbitrary real chart.** For
a real `C²` chart `e`, it is one quarter of the difference of the two mixed real-Hessian terms on
the chart derivatives of `(I • v, w)` and `(v, I • w)`. -/
theorem im_manifoldLeviForm_apply_of_mem_maximalAtlas
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M) (hx : x ∈ e.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) (hcrit : mvfderiv 𝓘(ℝ, E) f x = 0) (v w : E) :
    (manifoldLeviForm E f x v w).im =
      (fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (I • v))
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x w) -
        fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (I • w))) / 4 := by
  have h₁ := criticalHessian_apply_eq_of_mem_maximalAtlas he hx hf hcrit (I • v) w
  have h₂ := criticalHessian_apply_eq_of_mem_maximalAtlas he hx hf hcrit v (I • w)
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id] at h₁ h₂
  rw [im_manifoldLeviForm_apply]
  -- On the model space `E`, `mvfderiv 𝓘(ℝ, E) e x` is `mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x` by definition.
  exact congrArg₂ (fun a b : ℝ ↦ (a - b) / 4) h₁ h₂

/-- **The Levi form at a critical point, from the real Hessian in any chart.** At a critical point
`x` of a function `f` which is `C²` at `x`, the diagonal value of the Levi form on `v` is
`(Hess f(v, v) + Hess f(I • v, I • v)) / 4`, where the real Hessian may be computed in any chart
`e` of the real `C²` maximal atlas, holomorphic or not, after transporting the tangent vectors by
the derivative of `e`. -/
theorem manifoldLeviForm_apply_self_of_mem_maximalAtlas
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M) (hx : x ∈ e.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) (hcrit : mvfderiv 𝓘(ℝ, E) f x = 0) (v : E) :
    manifoldLeviForm E f x v v =
      ((hessianQuadraticForm (f ∘ e.symm) (e x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v) +
        hessianQuadraticForm (f ∘ e.symm) (e x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (I • v))) / 4 :
          ℝ) := by
  apply Complex.ext
  · have h := re_manifoldLeviForm_apply_of_mem_maximalAtlas he hx hf hcrit v v
    have hq₁ := hessianQuadraticForm_apply (f ∘ e.symm) (e x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)
    have hq₂ := hessianQuadraticForm_apply (f ∘ e.symm) (e x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (I • v))
    simp only [Complex.ofReal_re]
    exact h.trans (congrArg (fun z : ℝ ↦ z / 4) (congrArg₂ (· + ·) hq₁.symm hq₂.symm))
  · rw [manifoldLeviForm_apply_self hf]
    simp

variable [FiniteDimensional ℂ E]

/-- **The index bound for strongly `q`-pseudoconvex functions on a complex manifold.** At a
critical point `x` of a function `f` which is `C²` at `x` and strongly `q`-pseudoconvex at `x`, the
Morse index of `f` is at most `dim_ℂ E + q`. -/
theorem IsManifoldStronglyPseudoconvexAt.manifoldMorseIndex_le [IsManifold 𝓘(ℂ, E) 2 M] {q : ℕ}
    (h : IsManifoldStronglyPseudoconvexAt E q f x) (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x)
    (hcrit : mvfderiv 𝓘(ℝ, E) f x = 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f x ≤ finrank ℂ E + q := by
  have he : chartAt E x ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 2 M :=
    IsManifold.chart_mem_maximalAtlas x
  rw [manifoldMorseIndex_eq_morseIndex_of_mem_maximalAtlas
    (IsManifold.maximalAtlas_subset_restrictScalars ℝ he) (mem_chart_source E x) hf hcrit]
  simpa only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id] using
    IsStronglyPseudoconvexAt.morseIndex_le h

/-- **The index bound for strictly plurisubharmonic functions on a complex manifold.** At a
critical point `x` of a function `f` which is `C²` at `x` and strictly plurisubharmonic at `x`, the
Morse index of `f` is at most `dim_ℂ E`. -/
theorem IsManifoldStrictlyPlurisubharmonicAt.manifoldMorseIndex_le [IsManifold 𝓘(ℂ, E) 2 M]
    (h : IsManifoldStrictlyPlurisubharmonicAt E f x) (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x)
    (hcrit : mvfderiv 𝓘(ℝ, E) f x = 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f x ≤ finrank ℂ E := by
  simpa using (h.isManifoldStronglyPseudoconvexAt 0).manifoldMorseIndex_le hf hcrit

end Critical

end TauCeti
