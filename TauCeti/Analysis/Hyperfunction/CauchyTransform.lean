/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Hyperfunction.OneDimensional
public import TauCeti.Basic.Complex.OfRealSub
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Distribution.Order
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft

/-!
# The Cauchy transform of a distribution on the real line

Let `u` be a complex-valued distribution on an open set `Ω ⊆ ℝ` and `χ` a real test function on
`Ω`. The **Cauchy transform** of `u` with cutoff `χ` is

`C(z) = (2πi)⁻¹ ⟨u_t, χ(t) / (t - z)⟩`, `z ∉ ℝ`,

where `u` is paired with the complex test function `t ↦ χ(t) / (t - z)` through its complex-linear
extension `Distribution.complexPairing`. When `u` has compact support and `χ` equals one near it,
`C` is the classical representative of `u` as a one-dimensional hyperfunction: `u` is the
difference of the boundary values of `C` from the upper and the lower half-plane. This file
proves the facts about `C` that do not involve boundary values:

* `C` is holomorphic on `ℂ ∖ ℝ`, with derivative `(2πi)⁻¹ ⟨u_t, χ(t) / (t - z)²⟩`;
* `C` extends holomorphically across every real open set `V` disjoint from
  `dsupport u ∩ tsupport χ`, so its hyperfunction class vanishes on `V`;
* `C` depends only on the germ of `χ` along the support of `u`, so for compactly supported `u` it
  does not depend on the choice of a cutoff equal to one near the support;
* `C` is complex-linear in `u`;
* for the Dirac distribution at `a`, `C(z) = (2πi)⁻¹ χ(a) / (a - z)`; in particular
  `C(z) = -(2πiz)⁻¹` for `δ₀` and `χ(0) = 1`.

For a measure `μ` on `ℝ`, the analogous transform `∫ (t - z)⁻¹ dμ(t)` without cutoff is Mathlib's
`MeasureTheory.resolventTransform` (the Stieltjes transform). A distribution need not be a measure,
and it can only be paired with the kernel after the kernel is cut off to a test function.

Extended by zero to `ℝ`, the Cauchy transform is a holomorphic section over `ℂ ∖ ℝ` in
the ambient-function encoding of `TauCeti/Analysis/Hyperfunction/OneDimensional.lean`
(`Distribution.cauchyTransform_mem_holomorphicSections`).

## Holomorphy

The kernel `t ↦ χ(t) / (t - z)` is a test function for every `z ∈ ℂ` off the real support
`tsupport χ`, real or not, and its pairing with `u` is holomorphic in `z` there. The difference
quotients of the kernels converge in every `C^k` norm. To see this uniformly in the derivatives,
the kernel is multiplied by a bump in `z` that equals one near a given point `z₀ ∉ tsupport χ` and
vanishes near `tsupport χ`. The product is a smooth compactly supported function
of `(z, t)`, so all `t`-derivatives of its first-order Taylor remainder in `z` are `o(|h|)`
uniformly in `t` (`HasCompactSupport.exists_norm_iteratedFDeriv_prod_right_sub_sub_le`). Since `u`
has finite order on the support of `χ` (`Distribution.exists_norm_complexPairing_le`), its pairing
with the remainder is `o(|h|)` as well.

Near a real point outside `dsupport u` the cutoff can be changed, without changing `C`, to one that
vanishes near the point. The pairing with the modified kernel then continues `C` holomorphically
across that point, and these local continuations glue (`TauCeti.Hyperfunction.throughReal_iSup`).

## Main declarations

* `TestFunction.cauchyKernel χ k hz`: the complex test function `t ↦ χ(t) / (t - z) ^ k`
  for `z` off the real support of `χ`.
* `Distribution.cauchyTransform u χ`: the Cauchy transform, extended by zero to `ℝ`.
* `Distribution.hasDerivAt_cauchyTransform`: its complex derivative off `ℝ`.
* `Distribution.cauchyTransform_mem_holomorphicSections`: it is a holomorphic section
  over `ℂ ∖ ℝ`.
* `Distribution.cauchyTransform_congr`: independence of the cutoff near the support.
* `Distribution.cauchyTransform_mem_throughReal`: holomorphic extension across the real points
  off `dsupport u ∩ tsupport χ`.
* `Distribution.cauchyTransform_delta`: the transform of a Dirac distribution.

## References

* H. Komatsu, *An introduction to the theory of hyperfunctions*, in *Hyperfunctions and
  pseudo-differential equations*, Lecture Notes in Mathematics 287 (1973), 3–40, §1.
* L. Hörmander, *The analysis of linear partial differential operators I*, §3.1 and §9.1.
-/

public section

noncomputable section

open Complex Filter Metric Set TopologicalSpace TestFunction Distribution TauCeti.Hyperfunction
open scoped ContDiff Distributions Real Topology

variable {Ω : Opens ℝ}

namespace TestFunction

/-- For a real test function `χ`, a natural number `k` and a point `z ∈ ℂ` off the real support
of `χ`, the complex test function `t ↦ χ(t) / (t - z) ^ k`. For `k = 1` this is the cutoff Cauchy
kernel. Every non-real `z` is admissible (`Complex.notMem_image_ofReal_of_im_ne_zero`), and so is
every real `z` outside `tsupport χ`. -/
def cauchyKernel (χ : 𝓓(Ω, ℝ)) (k : ℕ) {z : ℂ} (hz : z ∉ ((↑) : ℝ → ℂ) '' tsupport χ) :
    𝓓(Ω, ℂ) where
  toFun t := (χ t : ℂ) * (((t : ℂ) - z) ^ k)⁻¹
  contDiff' := contDiff_iff_contDiffAt.2 fun t ↦ by
    by_cases ht : t ∈ tsupport χ
    · exact (ofRealCLM.contDiff.comp χ.contDiff).contDiffAt.mul
        (((ofRealCLM.contDiff.sub contDiff_const).pow k).contDiffAt.inv
          (pow_ne_zero k (sub_ne_zero.2 fun h ↦ hz ⟨t, ht, h⟩)))
    · exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        ((notMem_tsupport_iff_eventuallyEq.1 ht).mono fun s hs ↦ by simp [hs])
  hasCompactSupport' := (χ.hasCompactSupport.comp_left ofReal_zero).mul_right
  tsupport_subset' :=
    (tsupport_mul_subset_left.trans (tsupport_comp_subset ofReal_zero χ)).trans χ.tsupport_subset

@[simp]
theorem cauchyKernel_apply (χ : 𝓓(Ω, ℝ)) (k : ℕ) {z : ℂ}
    (hz : z ∉ ((↑) : ℝ → ℂ) '' tsupport χ) (t : ℝ) :
    cauchyKernel χ k hz t = χ t / ((t : ℂ) - z) ^ k :=
  (div_eq_mul_inv _ _).symm

end TestFunction

namespace Distribution

/-- The **Cauchy transform** of a complex-valued distribution `u` on an open set `Ω ⊆ ℝ`, with
cutoff `χ`: the function `z ↦ (2πi)⁻¹ ⟨u_t, χ(t) / (t - z)⟩` on `ℂ ∖ ℝ`, extended by zero to `ℝ`.
-/
def cauchyTransform (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) (z : ℂ) : ℂ :=
  (2 * π * I)⁻¹ * if hz : z.im ≠ 0 then
    u.complexPairing (cauchyKernel χ 1 (notMem_image_ofReal_of_im_ne_zero hz)) else 0

theorem cauchyTransform_of_im_ne_zero (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) {z : ℂ} (hz : z.im ≠ 0) :
    cauchyTransform u χ z = (2 * π * I)⁻¹ *
      u.complexPairing (cauchyKernel χ 1 (notMem_image_ofReal_of_im_ne_zero hz)) := by
  simp [cauchyTransform, hz]

@[simp]
theorem cauchyTransform_of_im_eq_zero (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) {z : ℂ} (hz : z.im = 0) :
    cauchyTransform u χ z = 0 := by
  simp [cauchyTransform, hz]

/-! ### Holomorphy -/

/-- The kernel `(z, t) ↦ ρ(z) χ(t) / (t - z)`, cut off by a bump `ρ` in `z` whose support avoids
the real support of `χ`, is smooth with compact support. -/
private theorem contDiff_hasCompactSupport_bump_mul_cauchyKernel (χ : 𝓓(Ω, ℝ)) {z : ℂ}
    (ρ : ContDiffBump z) (hρ : Disjoint (closedBall z ρ.rOut) (((↑) : ℝ → ℂ) '' tsupport χ)) :
    ContDiff ℝ ∞ (fun q : ℂ × ℝ ↦ (ρ q.1 : ℂ) * ((χ q.2 : ℂ) * ((q.2 : ℂ) - q.1)⁻¹)) ∧
      HasCompactSupport (fun q : ℂ × ℝ ↦ (ρ q.1 : ℂ) * ((χ q.2 : ℂ) * ((q.2 : ℂ) - q.1)⁻¹)) := by
  refine ⟨contDiff_iff_contDiffAt.2 fun q ↦ ?_, ?_⟩
  · by_cases hq : (q.2 : ℂ) - q.1 = 0
    · -- On the real diagonal one of the two cutoffs vanishes near `q`.
      have hq' : q.1 ∉ tsupport ρ ∨ q.2 ∉ tsupport χ := by
        rw [ρ.tsupport_eq, ← not_and_or]
        exact fun h ↦ hρ.ne_of_mem h.1 ⟨q.2, h.2, rfl⟩ (sub_eq_zero.1 hq).symm
      refine contDiffAt_const (c := (0 : ℂ)) |>.congr_of_eventuallyEq ?_
      rcases hq' with h | h
      · filter_upwards [(continuous_fst.tendsto q).eventually
          (notMem_tsupport_iff_eventuallyEq.1 h)] with w hw
        simp [hw]
      · filter_upwards [(continuous_snd.tendsto q).eventually
          (notMem_tsupport_iff_eventuallyEq.1 h)] with w hw
        simp [hw]
    · exact ((ofRealCLM.contDiff.comp ρ.contDiff).comp contDiff_fst).contDiffAt.mul
        (((ofRealCLM.contDiff.comp χ.contDiff).comp contDiff_snd).contDiffAt.mul
          (ContDiffAt.inv (f := fun q : ℂ × ℝ ↦ (q.2 : ℂ) - q.1)
            ((ofRealCLM.contDiff.comp contDiff_snd).sub contDiff_fst).contDiffAt hq))
  · refine HasCompactSupport.intro ((isCompact_closedBall z ρ.rOut).prod
      χ.hasCompactSupport.isCompact) fun q hq ↦ ?_
    rw [mem_prod, not_and_or] at hq
    rcases hq with hq | hq
    · rw [ρ.zero_of_le_dist (by rw [mem_closedBall, not_le] at hq; exact hq.le)]
      simp
    · simp [image_eq_zero_of_notMem_tsupport hq]

/-- The real derivative of `(w, t) ↦ χ(t) / (t - w)` at a point `(z, t)` where it is
differentiable, in the direction `(h, 0)`, is `h χ(t) / (t - z)²`. -/
private theorem fderiv_cauchyKernel_apply_inl (χ : 𝓓(Ω, ℝ)) {z : ℂ}
    (hz : z ∉ ((↑) : ℝ → ℂ) '' tsupport χ) (t : ℝ)
    (hG : DifferentiableAt ℝ (fun q : ℂ × ℝ ↦ (χ q.2 : ℂ) * ((q.2 : ℂ) - q.1)⁻¹) (z, t))
    (h : ℂ) :
    fderiv ℝ (fun q : ℂ × ℝ ↦ (χ q.2 : ℂ) * ((q.2 : ℂ) - q.1)⁻¹) (z, t) (h, 0) =
      h * cauchyKernel χ 2 hz t := by
  -- The complex derivative of the slice `w ↦ χ(t) / (t - w)` at `z`.
  have hslice : HasDerivAt (fun w : ℂ ↦ (χ t : ℂ) * ((t : ℂ) - w)⁻¹)
      ((χ t : ℂ) * (((t : ℂ) - z) ^ 2)⁻¹) z := by
    by_cases ht : χ t = 0
    · simpa [ht] using hasDerivAt_const z (0 : ℂ)
    have htz : (t : ℂ) - z ≠ 0 := sub_ne_zero.2 fun h ↦ hz ⟨t, subset_tsupport _ ht, h⟩
    have h1 : HasDerivAt (fun w : ℂ ↦ ((t : ℂ) - w)⁻¹) (((t : ℂ) - z) ^ 2)⁻¹ z := by
      convert ((hasDerivAt_id z).const_sub (t : ℂ)).inv htz using 1
      · rfl
      · simp
    exact h1.const_mul _
  have hcomp := hG.hasFDerivAt.comp z (hasFDerivAt_prodMk_left (𝕜 := ℝ) z t)
  have huniq := hcomp.unique (hslice.hasFDerivAt.restrictScalars ℝ)
  have := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L h) huniq
  simpa [cauchyKernel_apply, div_eq_mul_inv, mul_comm] using this

/-- Around a point `z` off the real support of `χ`, the Cauchy kernels `t ↦ χ(t) / (t - w)` with
`w` near `z` are the slices of one smooth compactly supported function `g` of `(w, t)`, whose
derivative in `w` at `z` is given by the squared kernel. -/
private theorem exists_contDiff_slice_eq_cauchyKernel (χ : 𝓓(Ω, ℝ)) {z : ℂ}
    (hz : z ∉ ((↑) : ℝ → ℂ) '' tsupport χ) :
    ∃ g : ℂ × ℝ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∃ r > 0,
      ∃ hS : ∀ w : ℂ, ‖w - z‖ < r → w ∉ ((↑) : ℝ → ℂ) '' tsupport χ,
        (∀ w (hw : ‖w - z‖ < r) t, g (w, t) = cauchyKernel χ 1 (hS w hw) t) ∧
        ∀ t (h : ℂ), fderiv ℝ g (z, t) (h, 0) = h * cauchyKernel χ 2 hz t := by
  -- The real support of `χ` is compact in `ℂ`, so a ball around `z` avoids it.
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.1
    ((χ.hasCompactSupport.isCompact.image continuous_ofReal).isClosed.isOpen_compl) z hz
  -- A bump in the parameter equal to one on `closedBall z (d / 4)`, supported in `ball z d`.
  let ρ : ContDiffBump z := ⟨d / 4, d / 2, by positivity, by linarith⟩
  obtain ⟨hgs, hgc⟩ := contDiff_hasCompactSupport_bump_mul_cauchyKernel χ ρ
    (subset_compl_iff_disjoint_right.1
      ((closedBall_subset_ball (show d / 2 < d by linarith)).trans hball))
  have hρ1 (w : ℂ) (hw : ‖w - z‖ < d / 4) : ρ w = 1 :=
    ρ.one_of_mem_closedBall (by rw [mem_closedBall, dist_eq_norm]; exact hw.le)
  refine ⟨_, hgs, hgc, d / 4, by positivity, fun w hw ↦ hball ?_, fun w hw t ↦ ?_, fun t h ↦ ?_⟩
  · rw [mem_ball, dist_eq_norm]
    linarith
  · simp [hρ1 w hw, cauchyKernel_apply, div_eq_mul_inv]
  · have hloc : (fun q : ℂ × ℝ ↦ (ρ q.1 : ℂ) * ((χ q.2 : ℂ) * ((q.2 : ℂ) - q.1)⁻¹)) =ᶠ[𝓝 (z, t)]
        fun q : ℂ × ℝ ↦ (χ q.2 : ℂ) * ((q.2 : ℂ) - q.1)⁻¹ :=
      ((continuous_fst.tendsto (z, t)).eventually
        (ball_mem_nhds z (by positivity : 0 < d / 4))).mono fun q hq ↦ by
          simp [hρ1 q.1 (by rwa [dist_eq_norm] at hq)]
    rw [hloc.fderiv_eq]
    exact fderiv_cauchyKernel_apply_inl χ hz t
      ((hgs.differentiable (by simp) (z, t)).congr_of_eventuallyEq hloc.symm) h

open scoped Classical in
/-- The pairing `w ↦ ⟨u_t, χ(t) / (t - w)⟩` at the points `w` off the real support of `χ`,
extended by zero. On `ℂ ∖ ℝ` it is `2πi` times the Cauchy transform. -/
private def cauchyPairing (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) (w : ℂ) : ℂ :=
  if hw : w ∉ ((↑) : ℝ → ℂ) '' tsupport χ then u.complexPairing (cauchyKernel χ 1 hw) else 0

/-- **Holomorphy of the pairing with the Cauchy kernel.** The map
`z ↦ ⟨u_t, χ(t) / (t - z)⟩` is complex differentiable at every point `z` off the real support of
`χ`, with derivative `⟨u_t, χ(t) / (t - z)²⟩`. -/
private theorem hasDerivAt_cauchyPairing (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) {z : ℂ}
    (hz : z ∉ ((↑) : ℝ → ℂ) '' tsupport χ) :
    HasDerivAt (cauchyPairing u χ) (u.complexPairing (cauchyKernel χ 2 hz)) z := by
  classical
  obtain ⟨g, hgs, hgc, d, hd, hS, hgw, hgd⟩ := exists_contDiff_slice_eq_cauchyKernel χ hz
  have hz' : ‖z - z‖ < d := by simpa using hd
  let K : Compacts ℝ := ⟨tsupport χ, χ.hasCompactSupport.isCompact⟩
  obtain ⟨N, C, hC, hu⟩ := u.exists_norm_complexPairing_le (K := K) χ.tsupport_subset
  -- For `z + h` near `z`, the Taylor remainder of the kernels; its pairing with `u` is `o(|h|)`.
  let R (h : ℂ) : 𝓓(Ω, ℂ) := if hzh : z + h ∉ ((↑) : ℝ → ℂ) '' tsupport χ then
    cauchyKernel χ 1 hzh - cauchyKernel χ 1 hz - h • cauchyKernel χ 2 hz else 0
  have hd' : ∀ᶠ h in 𝓝 (0 : ℂ), ‖z + h - z‖ < d := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hd] with h hh
    rwa [add_sub_cancel_left, ← mem_ball_zero_iff]
  have hR (h : ℂ) (hhd : ‖z + h - z‖ < d) :
      (R h : ℝ → ℂ) = fun t ↦ g (z + h, t) - g (z, t) - fderiv ℝ g (z, t) (h, 0) := by
    funext t
    rw [hgw _ hhd t, hgw z hz' t, hgd t h]
    simp only [R, hS _ hhd, not_false_eq_true, ↓reduceDIte]
    simp
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine (isLittleO_apply_of_norm_iteratedFDeriv_le (R := R) hC hu (.of_forall fun h ↦ ?_)
    fun i _ ε hε ↦ ?_).congr' ?_ EventuallyEq.rfl
  · refine closure_mono (Function.support_subset_iff'.2 fun t ht ↦ ?_)
    simp only [R]
    split_ifs <;> simp [cauchyKernel_apply, Function.notMem_support.1 ht]
  · obtain ⟨r, hr, hrem⟩ := hgc.exists_norm_iteratedFDeriv_prod_right_sub_sub_le hgs (i := i)
      (by exact_mod_cast le_top) z hε
    filter_upwards [hd', ball_mem_nhds (0 : ℂ) hr] with h hhd hh
    rw [hR h hhd]
    exact hrem h (mem_ball_zero_iff.1 hh)
  · filter_upwards [hd'] with h hhd
    simp only [R, cauchyPairing, hS _ hhd, hz, not_false_eq_true, ↓reduceDIte]
    simp

/-- On `ℂ ∖ ℝ` the Cauchy transform is `(2πi)⁻¹` times the pairing with the Cauchy kernel. -/
private theorem cauchyTransform_eq_cauchyPairing (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) {z : ℂ}
    (hz : z.im ≠ 0) : cauchyTransform u χ z = (2 * π * I)⁻¹ * cauchyPairing u χ z := by
  simp [cauchyTransform_of_im_ne_zero u χ hz, cauchyPairing,
    notMem_image_ofReal_of_im_ne_zero hz]

/-- **The Cauchy transform is holomorphic off the real line**, with derivative
`(2πi)⁻¹ ⟨u_t, χ(t) / (t - z)²⟩`. -/
theorem hasDerivAt_cauchyTransform (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (cauchyTransform u χ)
      ((2 * π * I)⁻¹ * u.complexPairing
        (cauchyKernel χ 2 (notMem_image_ofReal_of_im_ne_zero hz))) z :=
  ((hasDerivAt_cauchyPairing u χ _).const_mul _).congr_of_eventuallyEq <|
    eventually_of_mem (nonRealOpen.isOpen.mem_nhds (mem_nonRealOpen_iff.2 hz)) fun _ hw ↦
      cauchyTransform_eq_cauchyPairing u χ (mem_nonRealOpen_iff.1 hw)

theorem differentiableOn_cauchyTransform (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) :
    DifferentiableOn ℂ (cauchyTransform u χ) nonRealOpen := fun _ hz ↦
  (hasDerivAt_cauchyTransform u χ (mem_nonRealOpen_iff.1 hz)).differentiableAt
    |>.differentiableWithinAt

/-- The Cauchy transform, extended by zero to `ℝ`, is a holomorphic section over `ℂ ∖ ℝ`. -/
theorem cauchyTransform_mem_holomorphicSections (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) :
    cauchyTransform u χ ∈ holomorphicSections nonRealOpen :=
  mem_holomorphicSections_iff.2 ⟨differentiableOn_cauchyTransform u χ, fun _ hz ↦
    cauchyTransform_of_im_eq_zero u χ (not_not.1 (mt mem_nonRealOpen_iff.2 hz))⟩

/-! ### Cutoff independence, linearity and the Dirac distribution -/

/-- **Independence of the cutoff.** The Cauchy transform depends only on the germ of the cutoff
along the support of `u`: two cutoffs that agree near `dsupport u`, such as two cutoffs equal to
one near a compact support, give the same transform. -/
theorem cauchyTransform_congr (u : 𝓓'(Ω, ℂ)) {χ₁ χ₂ : 𝓓(Ω, ℝ)}
    (h : (χ₁ : ℝ → ℝ) =ᶠ[𝓝ˢ (dsupport u)] χ₂) :
    cauchyTransform u χ₁ = cauchyTransform u χ₂ := by
  ext z
  by_cases hz : z.im ≠ 0
  · rw [cauchyTransform_of_im_ne_zero u χ₁ hz, cauchyTransform_of_im_ne_zero u χ₂ hz,
      u.complexPairing_eq_of_eventuallyEq
        (ψ := cauchyKernel χ₂ 1 (notMem_image_ofReal_of_im_ne_zero hz))
        (h.mono fun t ht ↦ by simp [cauchyKernel_apply, ht])]
  · rw [cauchyTransform_of_im_eq_zero u χ₁ (not_not.1 hz),
      cauchyTransform_of_im_eq_zero u χ₂ (not_not.1 hz)]

@[simp]
theorem cauchyTransform_add (u v : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) :
    cauchyTransform (u + v) χ = cauchyTransform u χ + cauchyTransform v χ := by
  ext z
  by_cases hz : z.im ≠ 0
  · simp [cauchyTransform_of_im_ne_zero _ χ hz, mul_add]
  · simp [cauchyTransform_of_im_eq_zero _ χ (not_not.1 hz)]

@[simp]
theorem cauchyTransform_smul (c : ℂ) (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) :
    cauchyTransform (c • u) χ = c • cauchyTransform u χ := by
  ext z
  by_cases hz : z.im ≠ 0
  · simp only [cauchyTransform_of_im_ne_zero _ χ hz, complexPairing_smul, Pi.smul_apply,
      smul_eq_mul]
    ring
  · simp [cauchyTransform_of_im_eq_zero _ χ (not_not.1 hz)]

/-- The Cauchy transform of the Dirac distribution at `a` is `(2πi)⁻¹ χ(a) / (a - z)`. -/
theorem cauchyTransform_delta (a : ℝ) (χ : 𝓓(Ω, ℝ)) {z : ℂ} (hz : z.im ≠ 0) :
    cauchyTransform (mapCLM ofRealCLM (delta a : 𝓓'(Ω, ℝ))) χ z =
      (2 * π * I)⁻¹ * (χ a / ((a : ℂ) - z)) := by
  rw [cauchyTransform_of_im_ne_zero _ χ hz, complexPairing_mapCLM_ofRealCLM_delta]
  simp only [cauchyKernel_apply, pow_one]

/-- **The normalization of the Cauchy transform.** For a cutoff with `χ(0) = 1`, the Cauchy
transform of `δ₀` is `-(2πiz)⁻¹` on both half-planes. -/
theorem cauchyTransform_delta_zero {χ : 𝓓(Ω, ℝ)} (hχ : χ 0 = 1) {z : ℂ} (hz : z.im ≠ 0) :
    cauchyTransform (mapCLM ofRealCLM (delta 0 : 𝓓'(Ω, ℝ))) χ z = -(2 * π * I * z)⁻¹ := by
  rw [cauchyTransform_delta 0 χ hz, hχ]
  simp [div_eq_mul_inv]
  ring

/-! ### Extension across the real points off the support -/

/-- On `W(U)` for an open `U ⊆ ℝ` disjoint from `tsupport χ`, the pairing with the Cauchy kernel is
defined and holomorphic, so the Cauchy transform extends holomorphically across `U`. -/
private theorem cauchyTransform_mem_throughReal_of_disjoint_tsupport (u : 𝓓'(Ω, ℂ))
    (χ : 𝓓(Ω, ℝ)) {U : Opens ℝ} (hU : Disjoint (U : Set ℝ) (tsupport χ)) :
    ⟨cauchyTransform u χ, cauchyTransform_mem_holomorphicSections u χ⟩ ∈ throughReal U := by
  have hW (z : ℂ) (hz : z ∈ complexNeighborhood U) : z ∉ ((↑) : ℝ → ℂ) '' tsupport χ := by
    rintro ⟨t, ht, rfl⟩
    rcases mem_complexNeighborhood_iff.1 hz with h | h
    · exact h (ofReal_im t)
    · exact hU.ne_of_mem (by simpa using h) ht rfl
  refine mem_throughReal_iff.2 ⟨(complexNeighborhood U : Set ℂ).indicator
    fun z ↦ (2 * π * I)⁻¹ * cauchyPairing u χ z,
    mem_holomorphicSections_iff.2 ⟨?_, fun z hz ↦ indicator_of_notMem hz _⟩, fun z hz ↦ ?_⟩
  · exact (DifferentiableOn.congr (fun z hz ↦ ((hasDerivAt_cauchyPairing u χ
      (hW z hz)).const_mul _).differentiableAt.differentiableWithinAt)
      fun z hz ↦ indicator_of_mem hz _)
  · rw [indicator_of_mem (nonRealOpen_le_complexNeighborhood U hz)]
    exact (cauchyTransform_eq_cauchyPairing u χ (mem_nonRealOpen_iff.1 hz)).symm

/-- Near a real point `t₀` outside `dsupport u ∩ tsupport χ`, the cutoff `χ` can be replaced by
one vanishing near `t₀` without changing the Cauchy transform. -/
private theorem exists_cauchyTransform_eq_and_notMem_tsupport (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ))
    {t₀ : ℝ} (ht₀ : t₀ ∉ dsupport u ∩ tsupport χ) :
    ∃ χ' : 𝓓(Ω, ℝ), cauchyTransform u χ' = cauchyTransform u χ ∧ t₀ ∉ tsupport χ' := by
  by_cases hχ : t₀ ∈ tsupport χ
  swap
  · exact ⟨χ, rfl, hχ⟩
  -- `u` vanishes near `t₀`: multiply `χ` by `1 - β` for a bump `β` around `t₀` supported there.
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.1 isClosed_dsupport.isOpen_compl t₀ fun h ↦ ht₀ ⟨h, hχ⟩
  let β : ContDiffBump t₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hβ : ContDiff ℝ (⊤ : ℕ∞) fun t ↦ 1 - β t := contDiff_const.sub β.contDiff
  refine ⟨smulLeftCLM hβ χ, cauchyTransform_congr u ?_, ?_⟩
  · have hnhds : (closedBall t₀ (r / 2))ᶜ ∈ 𝓝ˢ (dsupport u) :=
      isClosed_closedBall.isOpen_compl.mem_nhdsSet.2 fun t ht htβ ↦
        hball (closedBall_subset_ball (by linarith) htβ) ht
    filter_upwards [hnhds] with t ht
    rw [mem_compl_iff, mem_closedBall, not_le] at ht
    simp [β.zero_of_le_dist (show β.rOut ≤ dist t t₀ from ht.le)]
  · rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [ball_mem_nhds t₀ (by positivity : 0 < r / 4)] with t ht
    simp [β.one_of_mem_closedBall (ball_subset_closedBall ht)]

/-- **The Cauchy transform extends across the real points off the support.** If an open set
`V ⊆ ℝ` does not meet `dsupport u ∩ tsupport χ`, the Cauchy transform of `u` with cutoff `χ`
extends holomorphically from `ℂ ∖ ℝ` across `V`, that is, to `W(V) = ℂ ∖ (ℝ ∖ V)`. Equivalently,
its class in the space `O(ℂ ∖ ℝ) / O(W(V))` of hyperfunctions on `V` is zero. -/
theorem cauchyTransform_mem_throughReal (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) {V : Opens ℝ}
    (hV : Disjoint (V : Set ℝ) (dsupport u ∩ tsupport χ)) :
    ⟨cauchyTransform u χ, cauchyTransform_mem_holomorphicSections u χ⟩ ∈ throughReal V := by
  choose χ' hχ' ht using fun t : V ↦
    exists_cauchyTransform_eq_and_notMem_tsupport u χ (disjoint_left.1 hV t.2)
  refine mem_throughReal_of_le_iSup
    (U := fun t ↦ ⟨(tsupport (χ' t))ᶜ, (isClosed_tsupport _).isOpen_compl⟩)
    (fun t ht' ↦ Opens.mem_iSup.2 ⟨⟨t, ht'⟩, ht ⟨t, ht'⟩⟩) fun t ↦ ?_
  convert cauchyTransform_mem_throughReal_of_disjoint_tsupport u (χ' t)
    (U := ⟨(tsupport (χ' t))ᶜ, (isClosed_tsupport _).isOpen_compl⟩) disjoint_compl_left using 2
  exact (hχ' t).symm

end Distribution
