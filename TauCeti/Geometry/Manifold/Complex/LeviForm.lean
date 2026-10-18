/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pseudoconvex
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
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
Consequently the index bounds of strongly `q`-pseudoconvex functions hold for the manifold Morse
index: at a critical point where `f` is strongly `q`-pseudoconvex in some holomorphic chart, the
Morse index is at most `dim_ℂ E + q`.

## Main definitions

* `TauCeti.manifoldLeviForm E f x`: the Levi form of `f` at `x`, computed in the preferred chart.

## Main results

* `TauCeti.leviForm_comp_symm_apply_of_mem_maximalAtlas`: for `f` real `C²` at `x`, the Levi
  form of the coordinate expression in any holomorphic `C²` chart at `x` is the manifold Levi
  form.
* `TauCeti.re_manifoldLeviForm_apply`, `TauCeti.im_manifoldLeviForm_apply`: the real and imaginary
  parts of the Levi form in terms of the real critical Hessian.
* `TauCeti.manifoldLeviForm_apply_self`: for `C²` `f`, its diagonal is the real number
  `(Hess f(v, v) + Hess f(I • v, I • v)) / 4`.
* `TauCeti.re_manifoldLeviForm_apply_of_mem_maximalAtlas` and
  `TauCeti.im_manifoldLeviForm_apply_of_mem_maximalAtlas`: at a critical point, the real and
  imaginary parts may be computed from the real Hessian in any real `C²` chart.
* `TauCeti.manifoldLeviForm_apply_self_of_mem_maximalAtlas`: at a critical point the same holds
  with the real Hessian computed in any real `C²` chart.
* `TauCeti.IsStronglyPseudoconvexAt.manifoldMorseIndex_le` and
  `TauCeti.IsStrictlyPlurisubharmonicAt.manifoldMorseIndex_le`: the manifold Morse index bounds
  `λ ≤ n + q` and `λ ≤ n` at critical points.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
-/

public section

open Complex Filter Function Module Set Topology
open scoped ContDiff Manifold

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

/-- The real second derivative of `f` in the preferred chart is the critical Hessian of `f` on the
real manifold underlying `M`. -/
private theorem fderiv_fderiv_comp_chartAt_symm (v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ (chartAt E x).symm)) (chartAt E x x) v w =
      criticalHessian 𝓘(ℝ, E) f x v w := by
  have hext : ((extChartAt 𝓘(ℝ, E) x).symm : E → M) = (chartAt E x).symm := by ext; simp
  have hext' : extChartAt 𝓘(ℝ, E) x x = chartAt E x x := by simp
  have h : fderiv ℝ (fderiv ℝ (f ∘ (chartAt E x).symm)) (chartAt E x x) =
      criticalHessian 𝓘(ℝ, E) f x := by
    rw [criticalHessian_def, hext, hext']
  -- `criticalHessian` is a form on `TangentSpace 𝓘(ℝ, E) x`, which is `E` by definition.
  exact congr($h v w)

/-- The coordinate expression in the preferred chart of a function which is `C²` at `x` is `C²`
at the chart image of `x`. -/
private theorem contDiffAt_comp_chartAt_symm (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) :
    ContDiffAt ℝ 2 (f ∘ (chartAt E x).symm) (chartAt E x x) := by
  have hext : ((extChartAt 𝓘(ℝ, E) x).symm : E → M) = (chartAt E x).symm := by ext; simp
  have hext' : extChartAt 𝓘(ℝ, E) x x = chartAt E x x := by simp
  simpa only [hext, hext'] using hf.contDiffAt_comp_extChartAt_symm

/-- The real part of the Levi form is one quarter of the `I`-invariant part of the critical
Hessian. -/
@[simp]
theorem re_manifoldLeviForm_apply (v w : E) :
    (manifoldLeviForm E f x v w).re =
      (criticalHessian 𝓘(ℝ, E) f x v w + criticalHessian 𝓘(ℝ, E) f x (I • v) (I • w)) / 4 := by
  rw [manifoldLeviForm_def, re_leviForm_apply, fderiv_fderiv_comp_chartAt_symm,
    fderiv_fderiv_comp_chartAt_symm]

/-- The imaginary part of the Levi form is one quarter of the part of the critical Hessian which
anticommutes with `I`. -/
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
  rw [manifoldLeviForm_def, leviForm_apply_self (contDiffAt_comp_chartAt_symm hf),
    hessianQuadraticForm_apply, hessianQuadraticForm_apply, fderiv_fderiv_comp_chartAt_symm,
    fderiv_fderiv_comp_chartAt_symm]

/-- The Levi form of a function which is `C²` at `x` is Hermitian. -/
theorem isSymm_manifoldLeviForm (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) :
    (manifoldLeviForm E f x).IsSymm :=
  isSymm_leviForm (contDiffAt_comp_chartAt_symm hf)

/-! ### Algebraic rules -/

/-- **The sum rule** for the Levi form on a complex manifold. -/
theorem manifoldLeviForm_add {g : M → ℝ} (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x)
    (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 g x) :
    manifoldLeviForm E (f + g) x = manifoldLeviForm E f x + manifoldLeviForm E g x :=
  leviForm_add (contDiffAt_comp_chartAt_symm hf) (contDiffAt_comp_chartAt_symm hg)

/-- Negating a function negates its Levi form on a complex manifold. -/
@[simp]
theorem manifoldLeviForm_neg (f : M → ℝ) (x : M) :
    manifoldLeviForm E (-f) x = -manifoldLeviForm E f x :=
  leviForm_neg (f ∘ (chartAt E x).symm) (chartAt E x x)

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
critical point `x` of a function `f` which is `C²` at `x` and strongly `q`-pseudoconvex in some
holomorphic chart `e` at `x`, the Morse index of `f` is at most `dim_ℂ E + q`. -/
theorem IsStronglyPseudoconvexAt.manifoldMorseIndex_le {q : ℕ}
    (h : IsStronglyPseudoconvexAt q (f ∘ e.symm) (e x))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 2 M) (hx : x ∈ e.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) (hcrit : mvfderiv 𝓘(ℝ, E) f x = 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f x ≤ finrank ℂ E + q := by
  rw [manifoldMorseIndex_eq_morseIndex_of_mem_maximalAtlas
    (IsManifold.maximalAtlas_subset_restrictScalars ℝ he) hx hf hcrit]
  simpa only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id] using
    h.morseIndex_le

/-- **The index bound for strictly plurisubharmonic functions on a complex manifold.** At a
critical point `x` of a function `f` which is `C²` at `x` and strictly plurisubharmonic in some
holomorphic chart `e` at `x`, the Morse index of `f` is at most `dim_ℂ E`. -/
theorem IsStrictlyPlurisubharmonicAt.manifoldMorseIndex_le
    (h : IsStrictlyPlurisubharmonicAt (f ∘ e.symm) (e x))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 2 M) (hx : x ∈ e.source)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) (hcrit : mvfderiv 𝓘(ℝ, E) f x = 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f x ≤ finrank ℂ E := by
  simpa using (h.isStronglyPseudoconvexAt 0).manifoldMorseIndex_le he hx hf hcrit

end Critical

end TauCeti
