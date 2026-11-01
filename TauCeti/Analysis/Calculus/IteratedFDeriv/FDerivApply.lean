/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# Iterated derivatives of a directional derivative

For a sufficiently smooth map `f`, the `i`-th iterated derivative of the directional derivative
`y ↦ Df(y) v` is the derivative of the `i`-th iterated derivative of `f` in the direction `v`:

`Dⁱ (y ↦ Df(y) v) (x) = D(Dⁱ f)(x) v`.

The two sides place the direction `v` in the last and in the first slot of `D^{i+1} f`
respectively, so the identity is a consequence of the symmetry of second derivatives. It is the
form in which a fixed directional derivative commutes with all higher derivatives.

As an application, every derivative of the first-order Taylor remainder
`z ↦ f (z - h) - f z + Df(z) h` of a compactly supported `C^{i+1}` map is `o(‖h‖)` uniformly on the
whole space. This controls every derivative of the difference quotients of translates of a
compactly supported smooth function at once. The same holds for the first-order Taylor remainder
`x ↦ g (p + h, x) - g (p, x) - Dg(p, x) (h, 0)` of a compactly supported map `g` on a product in
its first variable, with derivatives taken in the second: this controls the difference quotients
of a smooth family of compactly supported functions with respect to a parameter.

## Main declarations

* `ContDiff.iteratedFDeriv_fderiv_apply`: `Dⁱ (y ↦ Df(y) v) = D(Dⁱ f)(·) v`.
* `TauCeti.tsupport_sub_sub_add_fderiv_subset`: the support of the first-order Taylor remainder.
* `HasCompactSupport.exists_norm_iteratedFDeriv_sub_sub_add_fderiv_le`: the uniform estimate on
  the derivatives of the first-order Taylor remainder.
* `HasCompactSupport.exists_norm_iteratedFDeriv_prod_right_sub_sub_le`: the same estimate for the
  Taylor remainder in a parameter.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Iterated derivatives commute with a directional derivative.** For a map which is
`C^{minSmoothness 𝕜 (i + 1)}` (so `C^{i+1}` over `ℝ` or `ℂ`), the `i`-th iterated derivative of
`y ↦ Df(y) v` is the derivative of `Dⁱ f` in the direction `v`. -/
theorem ContDiff.iteratedFDeriv_fderiv_apply {n : WithTop ℕ∞} {f : E → F} (hf : ContDiff 𝕜 n f)
    {i : ℕ} (hi : minSmoothness 𝕜 (i + 1) ≤ n) (v x : E) :
    iteratedFDeriv 𝕜 i (fun y ↦ fderiv 𝕜 f y v) x = fderiv 𝕜 (iteratedFDeriv 𝕜 i f) x v := by
  induction i generalizing x with
  | zero =>
    ext m
    simp [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.comp_fderiv]
  | succ i ih =>
    have hi' : minSmoothness 𝕜 (i + 1) ≤ n :=
      (minSmoothness_monotone (by norm_cast; omega)).trans hi
    -- The `i`-th derivative of `f` is `C^{minSmoothness 𝕜 2}`, hence has symmetric second
    -- derivatives and a differentiable first derivative.
    have hg : ContDiff 𝕜 (minSmoothness 𝕜 2) (iteratedFDeriv 𝕜 i f) := by
      refine hf.iteratedFDeriv_right ?_
      rw [← minSmoothness_add]
      exact le_of_eq_of_le (by push_cast; ring_nf) hi
    have hD : DifferentiableAt 𝕜 (fderiv 𝕜 (iteratedFDeriv 𝕜 i f)) x :=
      ((hg.fderiv_right (m := 1) (le_minSmoothness.trans' (by norm_num))).differentiable
        one_ne_zero) x
    have hfun : iteratedFDeriv 𝕜 i (fun y ↦ fderiv 𝕜 f y v) =
        fun y ↦ fderiv 𝕜 (iteratedFDeriv 𝕜 i f) y v :=
      funext (ih hi')
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
      hfun]
    -- The isometry must be given explicitly: its normed-group instances are found through a
    -- different path from the one `LinearIsometryEquiv.comp_fderiv` unifies with.
    have hcomp := LinearIsometryEquiv.comp_fderiv (𝕜 := 𝕜)
      (iso := (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (i + 1) => E) F).symm)
      (f := fderiv 𝕜 (iteratedFDeriv 𝕜 i f)) (x := x)
    rw [hcomp, ContinuousLinearMap.comp_apply]
    simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    congr 1
    ext w : 1
    rw [TauCeti.fderiv_clm_apply_const_apply hD]
    exact (hg.contDiffAt (x := x)).isSymmSndFDerivAt le_rfl w v

namespace TauCeti

/-- The first-order Taylor remainder `z ↦ f (z - h) - f z + Df(z) h` is supported in every closed
`δ`-thickening of the support of `f` with `‖h‖ ≤ δ`. -/
theorem tsupport_sub_sub_add_fderiv_subset (f : E → F) {h : E} {δ : ℝ} (hh : ‖h‖ ≤ δ) :
    (tsupport fun z ↦ f (z - h) - f z + fderiv 𝕜 f z h) ⊆ Metric.cthickening δ (tsupport f) := by
  refine closure_minimal (Function.support_subset_iff'.2 fun z hz ↦ ?_) Metric.isClosed_cthickening
  have hz₀ : z ∉ tsupport f := fun h' ↦ hz (Metric.self_subset_cthickening _ h')
  have hzh : z - h ∉ tsupport f := fun h' ↦ hz (Metric.mem_cthickening_of_dist_le z (z - h) δ _ h'
    (by rwa [dist_eq_norm, sub_sub_cancel]))
  rw [image_eq_zero_of_notMem_tsupport hz₀, image_eq_zero_of_notMem_tsupport hzh,
    Function.notMem_support.1 fun h' ↦ hz₀ (support_fderiv_subset 𝕜 h')]
  simp

end TauCeti

/-- **Uniform first-order Taylor estimate for all derivatives.** If `f` is `C^{i+1}` with compact
support, then the `i`-th derivative of the first-order Taylor remainder
`z ↦ f (z - h) - f z + Df(z) h` is `o(‖h‖)` as `h → 0`, uniformly on the whole space. -/
theorem HasCompactSupport.exists_norm_iteratedFDeriv_sub_sub_add_fderiv_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : WithTop ℕ∞} {f : E → F} (hfc : HasCompactSupport f)
    (hf : ContDiff ℝ n f) {i : ℕ} (hi : i + 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : E, ‖h‖ < δ → ∀ y,
      ‖iteratedFDeriv ℝ i (fun z ↦ f (z - h) - f z + fderiv ℝ f z h) y‖ ≤ ε * ‖h‖ := by
  set g := iteratedFDeriv ℝ i f
  have hg : ContDiff ℝ 1 g := hf.iteratedFDeriv_right (by rwa [add_comm])
  have hgu : UniformContinuous (fderiv ℝ g) :=
    ((hfc.iteratedFDeriv (𝕜 := ℝ) i).fderiv (𝕜 := ℝ)).uniformContinuous_of_continuous
      (hg.continuous_fderiv one_ne_zero)
  obtain ⟨δ, hδ, hδε⟩ :=
    (Metric.uniformContinuous_iff (α := E) (β := E →L[ℝ] E [×i]→L[ℝ] F)).1 hgu ε hε
  refine ⟨δ, hδ, fun h hh y => ?_⟩
  have hin : (i : WithTop ℕ∞) ≤ n := le_trans (by norm_cast; omega) hi
  have hsub : ContDiff ℝ n fun z ↦ f (z - h) := hf.comp (contDiff_id.sub contDiff_const)
  have hder : ContDiff ℝ i fun z ↦ fderiv ℝ f z h :=
    (hf.fderiv_right hi).clm_apply contDiff_const
  rw [fun_iteratedFDeriv_add_apply (((hsub.sub hf).of_le hin).contDiffAt) hder.contDiffAt,
    fun_iteratedFDeriv_sub_apply ((hsub.of_le hin).contDiffAt) ((hf.of_le hin).contDiffAt),
    iteratedFDeriv_comp_sub, hf.iteratedFDeriv_fderiv_apply (by simpa using hi)]
  have hmv := (convex_ball y δ).norm_image_sub_le_of_norm_fderiv_le' (f := g)
    (φ := fderiv ℝ g y) (C := ε) (fun z _ ↦ hg.differentiable one_ne_zero z)
    (fun z hz ↦ by
      rw [← dist_eq_norm]
      exact (hδε (Metric.mem_ball.1 hz)).le)
    (Metric.mem_ball_self hδ)
    (by rwa [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg])
  simpa only [sub_sub_cancel_left, map_neg, sub_neg_eq_add, norm_neg] using hmv

/-- **Uniform first-order Taylor estimate in a parameter.** If `g : P × E → F` is `C^{i+1}` with
compact support, then the `i`-th derivative in the second variable of the first-order Taylor
remainder `x ↦ g (p + h, x) - g (p, x) - Dg(p, x) (h, 0)` in the first variable is `o(‖h‖)` as
`h → 0`, uniformly on the whole space. -/
theorem HasCompactSupport.exists_norm_iteratedFDeriv_prod_right_sub_sub_le
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞}
    {g : P × E → F} (hgc : HasCompactSupport g) (hg : ContDiff ℝ n g) {i : ℕ} (hi : i + 1 ≤ n)
    (p : P) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : P, ‖h‖ < δ → ∀ y,
      ‖iteratedFDeriv ℝ i (fun x ↦ g (p + h, x) - g (p, x) - fderiv ℝ g (p, x) (h, 0)) y‖ ≤
        ε * ‖h‖ := by
  obtain ⟨δ, hδ, hrem⟩ := hgc.exists_norm_iteratedFDeriv_sub_sub_add_fderiv_le hg hi hε
  refine ⟨δ, hδ, fun h hh y ↦ ?_⟩
  have hw : ‖((-h, 0) : P × E)‖ = ‖h‖ := by simp
  -- The remainder in `p` is the slice at `p` of the Taylor remainder of `g` on the product with
  -- displacement `(-h, 0)`, whose derivatives in the second variable are its total derivatives
  -- restricted to the second factor.
  set R := fun q : P × E ↦ g (q - (-h, 0)) - g q + fderiv ℝ g q (-h, 0)
  have hin : (i : WithTop ℕ∞) ≤ n := le_trans (by norm_cast; omega) hi
  have hR : ContDiff ℝ i R :=
    (((hg.comp (contDiff_id.sub contDiff_const)).sub hg).of_le hin).add
      ((hg.fderiv_right hi).clm_apply contDiff_const)
  have hslice : (fun x ↦ g (p + h, x) - g (p, x) - fderiv ℝ g (p, x) (h, 0)) =
      fun x ↦ R (p, x) := by
    funext x
    have hn : ((-h, 0) : P × E) = -(h, 0) := by simp
    simp only [R, hn, sub_neg_eq_add, Prod.mk_add_mk, add_zero, map_neg, ← sub_eq_add_neg]
  rw [hslice, _root_.ContDiff.iteratedFDeriv_prod_right hR i le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _ : Fin i, ‖ContinuousLinearMap.inr ℝ P E‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ..)
  calc _ ≤ ‖iteratedFDeriv ℝ i R (p, y)‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ ε * ‖h‖ := by rw [mul_one, ← hw]; exact hrem _ (hw ▸ hh) _
