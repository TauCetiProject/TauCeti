/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.QuadraticLeviForm
public import TauCeti.Analysis.Normed.Module.Alternating.Bilinear
public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# The real (1,1)-form `i∂∂bar u` on a complex manifold

Let `M` be a complex manifold modelled on `𝓘(ℂ, E)`, and let `u : M → ℝ`. The Hermitian form of
the real (1,1)-form `i∂∂bar u` at `x` is `2·L_u(x)`, where `L_u(x)` is the Levi form
`TauCeti.manifoldLeviForm E u x`, and `i∂∂bar u` itself is the imaginary part of this Hermitian
form: `(i∂∂bar u)(v, w) = 2·Im L_u(x)(v, w)`. With this normalization
`i∂∂bar |z|² = i Σ dz_j ∧ dzbar_j` on `ℂⁿ`, twice the standard Kähler form.

This file defines `TauCeti.ddbarForm E u`, a rough real two-form on the underlying real manifold
(`TauCeti.RoughForm 𝓘(ℝ, E) M ℝ 2`), by `(v, w) ↦ Im L_u(x)(v, w) - Im L_u(x)(w, v)`. This
expression is alternating for every `u`, and it is `2·Im L_u(x)(v, w)` as soon as `u` is `C²` at
`x`, since `L_u(x)` is then Hermitian (`TauCeti.isSymm_manifoldLeviForm`).

## Main definitions

* `TauCeti.ddbarForm E u`: the real two-form `i∂∂bar u`.

## Main results

* `TauCeti.ddbarForm_apply_of_contMDiffAt`: `(i∂∂bar u)(v, w) = 2·Im L_u(v, w)` for `C²` `u`.
* `TauCeti.ddbarForm_apply_I_smul`: `i∂∂bar u` is invariant under the complex structure, that is,
  of type (1,1).
* `TauCeti.mk_ddbarForm_apply_eq_two_mul_manifoldLeviForm`: the Hermitian form
  `(i∂∂bar u)(v, J w) + i·(i∂∂bar u)(v, w)` of `i∂∂bar u` is `2·L_u`.
* `TauCeti.ddbarForm_apply_of_mem_maximalAtlas`: `i∂∂bar u` may be computed in any holomorphic
  chart.
* `TauCeti.isSmoothForm_ddbarForm`: for `C²` `u`, the form `i∂∂bar u` is continuous.
* `TauCeti.ddbarForm_const`, `TauCeti.ddbarForm_add`, `TauCeti.ddbarForm_neg`,
  `TauCeti.ddbarForm_smul`: `i∂∂bar c = 0` and `i∂∂bar` is real linear on `C²` functions.
* `TauCeti.ddbarForm_norm_sq`: on a complex inner product space,
  `(i∂∂bar |z|²)(v, w) = 2·Im ⟪v, w⟫`.

## References

* G. Székelyhidi, *Fully non-linear elliptic equations on compact Hermitian manifolds*,
  J. Differential Geom. 109 (2018), Section 2.
* B. Guo, D. H. Phong and F. Tong, *On L∞ estimates for complex Monge–Ampère equations*,
  Ann. of Math. 198 (2023), Section 2.
-/

public section

open Complex Filter Function Set Topology
open scoped ComplexConjugate ContDiff Manifold TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M]
  [ChartedSpace E M] {u w : M → ℝ} {x : M}

variable (E) in
/-- The real (1,1)-form `i∂∂bar u` of a real function `u` on a complex manifold, as a rough two-form
on the underlying real manifold: at `x`, `(v, w) ↦ Im L_u(x)(v, w) - Im L_u(x)(w, v)`, where
`L_u(x)` is the Levi form `TauCeti.manifoldLeviForm E u x`. It is alternating for every `u`, and
equals `2·Im L_u(x)(v, w)` when `u` is `C²` at `x` (`TauCeti.ddbarForm_apply_of_contMDiffAt`). -/
def ddbarForm (u : M → ℝ) : RoughForm 𝓘(ℝ, E) M ℝ 2 := fun x ↦
  ContinuousAlternatingMap.alternatizeBilinCLM ℝ E ℝ
    (imLeviFormCLM (u ∘ (chartAt E x).symm) (chartAt E x x))

/-- `i∂∂bar u` at `x` is the alternation of the imaginary part of the Levi form of the coordinate
expression of `u` in the preferred chart at `x`. -/
theorem ddbarForm_def (u : M → ℝ) (x : M) :
    ddbarForm E u x = ContinuousAlternatingMap.alternatizeBilinCLM ℝ E ℝ
      (imLeviFormCLM (u ∘ (chartAt E x).symm) (chartAt E x x)) :=
  (rfl)

/-- The value of `i∂∂bar u` on two tangent vectors, in terms of the Levi form. -/
theorem ddbarForm_apply (u : M → ℝ) (x : M) (v : Fin 2 → E) :
    ddbarForm E u x v =
      (manifoldLeviForm E u x (v 0) (v 1)).im - (manifoldLeviForm E u x (v 1) (v 0)).im :=
  (ContinuousAlternatingMap.alternatizeBilinCLM_apply _ v).trans (by
    rw [imLeviFormCLM_apply, imLeviFormCLM_apply, manifoldLeviForm_def])

/-- The value of `i∂∂bar u` on the pair `(v, w)`, in terms of the Levi form. -/
theorem ddbarForm_apply_vecCons (u : M → ℝ) (x : M) (v w : E) :
    ddbarForm E u x ![v, w] =
      (manifoldLeviForm E u x v w).im - (manifoldLeviForm E u x w v).im :=
  ddbarForm_apply u x _

/-- For `u` which is `C²` at `x`, `(i∂∂bar u)(v, w) = 2·Im L_u(x)(v, w)`. -/
theorem ddbarForm_apply_of_contMDiffAt (hu : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 u x) (v w : E) :
    ddbarForm E u x ![v, w] = 2 * (manifoldLeviForm E u x v w).im := by
  rw [ddbarForm_apply_vecCons, ← (isSymm_manifoldLeviForm hu).eq v w]
  simp only [conj_im]
  ring

/-- **`i∂∂bar u` has type (1,1).** It is invariant under the complex structure `J = I • ·`, because
the Levi form is sesquilinear. -/
@[simp]
theorem ddbarForm_apply_I_smul (u : M → ℝ) (x : M) (v w : E) :
    ddbarForm E u x ![I • v, I • w] = ddbarForm E u x ![v, w] := by
  rw [ddbarForm_apply_vecCons, ddbarForm_apply_vecCons, manifoldLeviForm_I_smul_I_smul,
    manifoldLeviForm_I_smul_I_smul]

/-- **The Hermitian form of `i∂∂bar u` is `2·L_u`.** For `u` which is `C²` at `x`, the Hermitian
form `H(v, w) = (i∂∂bar u)(v, J w) + i·(i∂∂bar u)(v, w)` of the real (1,1)-form `i∂∂bar u` at `x`
is twice the Levi form of `u` at `x`. -/
theorem mk_ddbarForm_apply_eq_two_mul_manifoldLeviForm (hu : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 u x)
    (v w : E) :
    (⟨ddbarForm E u x ![v, I • w], ddbarForm E u x ![v, w]⟩ : ℂ) =
      2 * manifoldLeviForm E u x v w := by
  rw [ddbarForm_apply_of_contMDiffAt hu, ddbarForm_apply_of_contMDiffAt hu]
  apply Complex.ext <;> simp

/-- `i∂∂bar u` at `x` depends only on the germ of `u` at `x`. -/
theorem ddbarForm_congr_of_eventuallyEq (h : u =ᶠ[𝓝 x] w) :
    ddbarForm E u x = ddbarForm E w x := by
  rw [ddbarForm_def, ddbarForm_def]
  congr 1
  ext a b
  rw [imLeviFormCLM_apply, imLeviFormCLM_apply, ← manifoldLeviForm_def, ← manifoldLeviForm_def,
    manifoldLeviForm_congr_of_eventuallyEq h]

/-- **`i∂∂bar c = 0`** for every constant `c`. -/
@[simp]
theorem ddbarForm_const (c : ℝ) : ddbarForm E (fun _ : M ↦ c) = 0 := by
  funext x
  simp only [ddbarForm_def, Function.comp_def, imLeviFormCLM_const]
  exact map_zero _

/-- **The sum rule** `i∂∂bar (u + w) = i∂∂bar u + i∂∂bar w` at a point where both functions are
`C²`. -/
theorem ddbarForm_add (hu : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 u x)
    (hw : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 w x) :
    ddbarForm E (u + w) x = ddbarForm E u x + ddbarForm E w x := by
  rw [ddbarForm_def, ddbarForm_def, ddbarForm_def, Pi.add_comp,
    imLeviFormCLM_add hu.contDiffAt_comp_chartAt_symm hw.contDiffAt_comp_chartAt_symm]
  exact map_add _ _ _

/-- `i∂∂bar (-u) = -i∂∂bar u`. -/
@[simp]
theorem ddbarForm_neg (u : M → ℝ) : ddbarForm E (-u) = -ddbarForm E u := by
  funext x
  rw [Pi.neg_apply, ddbarForm_def, ddbarForm_def, Pi.neg_comp, imLeviFormCLM_neg]
  exact map_neg _ _

/-- `i∂∂bar (a • u) = a • i∂∂bar u` for a real constant `a`. -/
@[simp]
theorem ddbarForm_smul (a : ℝ) (u : M → ℝ) : ddbarForm E (a • u) = a • ddbarForm E u := by
  funext x
  rw [Pi.smul_apply, ddbarForm_def, ddbarForm_def, Pi.smul_comp, imLeviFormCLM_smul]
  exact map_smul _ _ _

/-! ### Charts and continuity -/

section Chart

variable {e : OpenPartialHomeomorph M E}

/-- **`i∂∂bar u` in a holomorphic chart.** Let `e` be a chart of the holomorphic `C²` maximal atlas
with `x` in its source, and let `u` be `C²` at `x`. Then `(i∂∂bar u)(x)(v, w)` is computed from the
Levi form of the coordinate expression `u ∘ e.symm` at `e x`, evaluated on the images of `v` and
`w` under the derivative of `e`. -/
theorem ddbarForm_apply_of_mem_maximalAtlas (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 2 M)
    (hx : x ∈ e.source) (hu : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 u x) (v w : E) :
    ddbarForm E u x ![v, w] =
      (leviForm (u ∘ e.symm) (e x) (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) e x v)
          (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) e x w)).im -
        (leviForm (u ∘ e.symm) (e x) (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) e x w)
          (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) e x v)).im := by
  rw [ddbarForm_apply_vecCons, leviForm_comp_symm_apply_of_mem_maximalAtlas he hx hu,
    leviForm_comp_symm_apply_of_mem_maximalAtlas he hx hu]

/-- In the preferred chart at `x₀`, the coordinate expression of `i∂∂bar u` is, on the chart target,
the alternation of the imaginary part of the Levi form of `u ∘ (chartAt E x₀).symm`. -/
theorem inChartAt_ddbarForm [IsManifold 𝓘(ℂ, E) 2 M] (x₀ : M) {z : E}
    (hz : z ∈ (chartAt E x₀).target)
    (hu : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 u ((chartAt E x₀).symm z)) :
    (ddbarForm E u).inChartAt x₀ z =
      ContinuousAlternatingMap.alternatizeBilinCLM ℝ E ℝ
        (imLeviFormCLM (u ∘ (chartAt E x₀).symm) z) := by
  set c := chartAt E x₀
  set y := (extChartAt 𝓘(ℝ, E) x₀).symm z
  have hyc : y = c.symm z := by simp [y, c]
  have hy : y ∈ c.source := hyc ▸ c.map_target hz
  have hcy : c y = z := hyc ▸ c.right_inv hz
  have hzt : z ∈ (extChartAt 𝓘(ℝ, E) x₀).target := by simpa using hz
  have hmd : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) c y :=
    mdifferentiableAt_of_mem_maximalAtlas (IsManifold.maximalAtlas_subset_of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2) (IsManifold.chart_mem_maximalAtlas x₀)) hy
  -- The complex derivative of the chart at `y`, which is its real derivative, inverts the real
  -- derivative of its inverse.
  have hinv (v : E) : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) c y
      (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm (range 𝓘(ℝ, E)) z v) = v := by
    have h := congr($(mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
      (I := 𝓘(ℝ, E)) hzt) v)
    simp only [extChartAt_coe, modelWithCornersSelf_coe, id_comp, comp_apply] at h
    exact (hmd.mfderiv_modelWithCornersSelf_restrictScalars_apply ℝ _).symm.trans h
  have key (a b : E) : manifoldLeviForm E u y
      (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm (range 𝓘(ℝ, E)) z a)
      (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm (range 𝓘(ℝ, E)) z b) =
        leviForm (u ∘ c.symm) z a b :=
    (leviForm_comp_symm_apply_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x₀) hy
      (hyc ▸ hu) _ _).symm.trans (by rw [hinv, hinv, hcy])
  refine _root_.ContinuousAlternatingMap.ext fun v ↦
    (RoughForm.inChartAt_apply _ _ _ _).trans <| (ddbarForm_apply u y _).trans ?_
  rw [ContinuousAlternatingMap.alternatizeBilinCLM_apply, imLeviFormCLM_apply, imLeviFormCLM_apply,
    key, key]

/-- **`i∂∂bar u` is continuous for `C²` `u`.** For a `C²` function `u` on a complex manifold, the
real (1,1)-form `i∂∂bar u` is a continuous section: in a holomorphic chart its coefficients are the
continuous second derivatives of the coordinate expression of `u`. -/
theorem isSmoothForm_ddbarForm [IsManifold 𝓘(ℂ, E) 2 M] (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 u) :
    IsSmoothForm 𝓘(ℝ, E) 0 (ddbarForm E u) := by
  refine IsSmoothForm.of_contDiffWithinAt_inChartAt_self fun x₀ ↦ ?_
  set c := chartAt E x₀
  have hC2 : ContDiffOn ℝ 2 (u ∘ c.symm) c.target :=
    contMDiffOn_iff_contDiffOn.1 (hu.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℝ, E))))
  have hcont : ContinuousOn (fun z ↦ ContinuousAlternatingMap.alternatizeBilinCLM ℝ E ℝ
      (imLeviFormCLM (u ∘ c.symm) z)) c.target :=
    (ContinuousAlternatingMap.alternatizeBilinCLM ℝ E ℝ).continuous.comp_continuousOn
      (continuousOn_imLeviFormCLM c.open_target hC2)
  simp only [extChartAt_coe, modelWithCornersSelf_coe, id_comp, range_id, contDiffWithinAt_univ]
  exact contDiffAt_zero.2 ⟨c.target, c.open_target.mem_nhds (mem_chart_target E x₀),
    hcont.congr fun z hz ↦ inChartAt_ddbarForm x₀ hz (hu _)⟩

end Chart

/-! ### On a complex vector space -/

/-- On the model space, `i∂∂bar u` is the alternation of the imaginary part of the Levi form. -/
theorem ddbarForm_modelSpace_apply (u : E → ℝ) (z v w : E) :
    ddbarForm E u z ![v, w] = (leviForm u z v w).im - (leviForm u z w v).im := by
  simp [ddbarForm_apply_vecCons]

/-- **`i∂∂bar |z|² = 2ω`.** On a complex inner product space,
`(i∂∂bar |z|²)(v, w) = 2·Im ⟪v, w⟫`, twice the standard Kähler form `Im ⟪v, w⟫`. -/
theorem ddbarForm_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (z v w : V) :
    ddbarForm V (fun y ↦ ‖y‖ ^ 2) z ![v, w] = 2 * (inner ℂ v w).im := by
  rw [ddbarForm_modelSpace_apply, leviForm_norm_sq, innerₛₗ_apply_apply, innerₛₗ_apply_apply,
    ← inner_conj_symm v w, conj_im]
  ring

end TauCeti
