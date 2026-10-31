/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Hyperfunction.OneDimensional
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply

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
(`TauCeti.Hyperfunction.cauchyTransform_mem_holomorphicSections`).

## Holomorphy

The difference quotients of the kernels `t ↦ χ(t) / (t - z)` converge in every `C^k` norm. To see
this uniformly in the derivatives, the kernel is multiplied by a bump in `z` that equals one near
a given point `z₀ ∉ ℝ` and vanishes near `ℝ`. The product is a smooth compactly supported function
of `(z, t)`, so all `t`-derivatives of its first-order Taylor remainder in `z` are `o(|h|)`
uniformly in `t` (`HasCompactSupport.exists_norm_iteratedFDeriv_prod_right_sub_sub_le`). Since `u`
has finite order on the support of `χ` (`Distribution.exists_norm_complexPairing_le`), its pairing
with the remainder is `o(|h|)` as well.

## Main declarations

* `TauCeti.Hyperfunction.cauchyKernel χ k hz`: the complex test function `t ↦ χ(t) / (t - z) ^ k`
  for `z ∉ ℝ`.
* `TauCeti.Hyperfunction.cauchyTransform u χ`: the Cauchy transform, extended by zero to `ℝ`.
* `TauCeti.Hyperfunction.hasDerivAt_cauchyTransform`: its complex derivative off `ℝ`.
* `TauCeti.Hyperfunction.cauchyTransform_mem_holomorphicSections`: it is a holomorphic section
  over `ℂ ∖ ℝ`.
* `TauCeti.Hyperfunction.cauchyTransform_congr`: independence of the cutoff near the support.
* `TauCeti.Hyperfunction.cauchyTransform_delta`: the transform of a Dirac distribution.

## References

* H. Komatsu, *An introduction to the theory of hyperfunctions*, in *Hyperfunctions and
  pseudo-differential equations*, Lecture Notes in Mathematics 287 (1973), 3–40, §1.
* L. Hörmander, *The analysis of linear partial differential operators I*, §3.1 and §9.1.
-/

public section

noncomputable section

open Complex Filter Metric Set TopologicalSpace TestFunction Distribution
open scoped ContDiff Distributions Real Topology

namespace TauCeti.Hyperfunction

variable {Ω : Opens ℝ}

/-- For non-real `z`, the point `t - z` is nonzero for every real `t`. -/
private theorem ofReal_sub_ne_zero {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) : (t : ℂ) - z ≠ 0 := fun h ↦
  hz (by simpa using congrArg im h)

/-- For a real test function `χ`, a natural number `k` and a non-real `z`, the complex test
function `t ↦ χ(t) / (t - z) ^ k`. For `k = 1` this is the cutoff Cauchy kernel. -/
def cauchyKernel (χ : 𝓓(Ω, ℝ)) (k : ℕ) {z : ℂ} (hz : z.im ≠ 0) : 𝓓(Ω, ℂ) where
  toFun t := (χ t : ℂ) * (((t : ℂ) - z) ^ k)⁻¹
  contDiff' := (ofRealCLM.contDiff.comp χ.contDiff).mul
    (((ofRealCLM.contDiff.sub contDiff_const).pow k).inv fun t ↦
      pow_ne_zero k (ofReal_sub_ne_zero hz t))
  hasCompactSupport' := (χ.hasCompactSupport.comp_left ofReal_zero).mul_right
  tsupport_subset' :=
    (tsupport_mul_subset_left.trans (tsupport_comp_subset ofReal_zero χ)).trans χ.tsupport_subset

@[simp]
theorem cauchyKernel_apply (χ : 𝓓(Ω, ℝ)) (k : ℕ) {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    cauchyKernel χ k hz t = χ t / ((t : ℂ) - z) ^ k :=
  (div_eq_mul_inv _ _).symm

/-- The **Cauchy transform** of a complex-valued distribution `u` on an open set `Ω ⊆ ℝ`, with
cutoff `χ`: the function `z ↦ (2πi)⁻¹ ⟨u_t, χ(t) / (t - z)⟩` on `ℂ ∖ ℝ`, extended by zero to `ℝ`.
-/
def cauchyTransform (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) (z : ℂ) : ℂ :=
  (2 * π * I)⁻¹ * if hz : z.im ≠ 0 then u.complexPairing (cauchyKernel χ 1 hz) else 0

theorem cauchyTransform_of_im_ne_zero (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) {z : ℂ} (hz : z.im ≠ 0) :
    cauchyTransform u χ z = (2 * π * I)⁻¹ * u.complexPairing (cauchyKernel χ 1 hz) := by
  simp [cauchyTransform, hz]

theorem cauchyTransform_of_im_eq_zero (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) {z : ℂ} (hz : z.im = 0) :
    cauchyTransform u χ z = 0 := by
  simp [cauchyTransform, hz]

/-! ### Holomorphy -/

/-- The kernel `(z, t) ↦ ρ(z) χ(t) / (t - z)`, cut off by a bump `ρ` in `z` around a non-real
point whose support stays away from the real line, is smooth with compact support. -/
private theorem contDiff_hasCompactSupport_bump_mul_cauchyKernel (χ : 𝓓(Ω, ℝ)) {z : ℂ}
    (ρ : ContDiffBump z) (hρ : ρ.rOut < |z.im|) :
    ContDiff ℝ ∞ (fun q : ℂ × ℝ ↦ (ρ q.1 : ℂ) * ((χ q.2 : ℂ) * ((q.2 : ℂ) - q.1)⁻¹)) ∧
      HasCompactSupport (fun q : ℂ × ℝ ↦ (ρ q.1 : ℂ) * ((χ q.2 : ℂ) * ((q.2 : ℂ) - q.1)⁻¹)) := by
  -- On the closed support of `ρ` the imaginary part stays away from zero.
  have him {w : ℂ} (hw : w ∈ tsupport ρ) : w.im ≠ 0 := by
    rw [ρ.tsupport_eq, mem_closedBall, dist_eq_norm] at hw
    intro h0
    have := abs_im_le_norm (w - z)
    rw [sub_im, h0, zero_sub, abs_neg] at this
    linarith
  refine ⟨contDiff_iff_contDiffAt.2 fun q ↦ ?_, ?_⟩
  · by_cases hq : q.1 ∈ tsupport ρ
    · exact ((ofRealCLM.contDiff.comp ρ.contDiff).comp contDiff_fst).contDiffAt.mul
        (((ofRealCLM.contDiff.comp χ.contDiff).comp contDiff_snd).contDiffAt.mul
          (ContDiffAt.inv (f := fun q : ℂ × ℝ ↦ (q.2 : ℂ) - q.1)
            ((ofRealCLM.contDiff.comp contDiff_snd).sub contDiff_fst).contDiffAt
            (ofReal_sub_ne_zero (him hq) q.2)))
    · have hρ0 : ∀ᶠ w : ℂ × ℝ in 𝓝 q, ρ w.1 = 0 :=
        (continuous_fst.tendsto q).eventually
          ((notMem_tsupport_iff_eventuallyEq.1 hq).mono fun w hw ↦ by simpa using hw)
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        (hρ0.mono fun w hw ↦ by simp [hw])
  · refine HasCompactSupport.intro ((isCompact_closedBall z ρ.rOut).prod
      χ.hasCompactSupport.isCompact) fun q hq ↦ ?_
    rw [mem_prod, not_and_or] at hq
    rcases hq with hq | hq
    · rw [ρ.zero_of_le_dist (by rw [mem_closedBall, not_le] at hq; exact hq.le)]
      simp
    · simp [image_eq_zero_of_notMem_tsupport hq]

/-- The real derivative of `(w, t) ↦ χ(t) / (t - w)` at a non-real `w = z`, in the direction
`(h, 0)`, is `h χ(t) / (t - z)²`. -/
private theorem fderiv_cauchyKernel_apply_inl (χ : 𝓓(Ω, ℝ)) {z : ℂ} (hz : z.im ≠ 0) (t : ℝ)
    (h : ℂ) :
    fderiv ℝ (fun q : ℂ × ℝ ↦ (χ q.2 : ℂ) * ((q.2 : ℂ) - q.1)⁻¹) (z, t) (h, 0) =
      h * cauchyKernel χ 2 hz t := by
  set G := fun q : ℂ × ℝ ↦ (χ q.2 : ℂ) * ((q.2 : ℂ) - q.1)⁻¹
  have hG : DifferentiableAt ℝ G (z, t) :=
    (((ofRealCLM.contDiff.comp χ.contDiff).comp contDiff_snd).contDiffAt.mul
      (ContDiffAt.inv (f := fun q : ℂ × ℝ ↦ (q.2 : ℂ) - q.1) (x := (z, t))
        ((ofRealCLM.contDiff.comp contDiff_snd).sub contDiff_fst).contDiffAt
        (ofReal_sub_ne_zero hz t))).differentiableAt (by simp)
  -- The complex derivative of the slice `w ↦ χ(t) / (t - w)` at `z`.
  have hslice : HasDerivAt (fun w : ℂ ↦ (χ t : ℂ) * ((t : ℂ) - w)⁻¹)
      ((χ t : ℂ) * (((t : ℂ) - z) ^ 2)⁻¹) z := by
    have h1 : HasDerivAt (fun w : ℂ ↦ ((t : ℂ) - w)⁻¹) (((t : ℂ) - z) ^ 2)⁻¹ z := by
      convert ((hasDerivAt_id z).const_sub (t : ℂ)).inv (ofReal_sub_ne_zero hz t) using 1
      · rfl
      · simp
    exact h1.const_mul _
  have hcomp := hG.hasFDerivAt.comp z (hasFDerivAt_prodMk_left (𝕜 := ℝ) z t)
  have huniq := hcomp.unique (hslice.hasFDerivAt.restrictScalars ℝ)
  have := congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L h) huniq
  simpa [G, cauchyKernel_apply, div_eq_mul_inv, mul_comm] using this

/-- Around a non-real point `z`, the Cauchy kernels `t ↦ χ(t) / (t - w)` with `w` near `z` are the
slices of one smooth compactly supported function `g` of `(w, t)`, whose derivative in `w` at `z`
is given by the squared kernel. -/
private theorem exists_contDiff_slice_eq_cauchyKernel (χ : 𝓓(Ω, ℝ)) {z : ℂ} (hz : z.im ≠ 0) :
    ∃ g : ℂ × ℝ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∃ r > 0,
      ∃ him : ∀ w : ℂ, ‖w - z‖ < r → w.im ≠ 0,
        (∀ w (hw : ‖w - z‖ < r) t, g (w, t) = cauchyKernel χ 1 (him w hw) t) ∧
        ∀ t (h : ℂ), fderiv ℝ g (z, t) (h, 0) = h * cauchyKernel χ 2 hz t := by
  set d := |z.im|
  have hd : 0 < d := abs_pos.2 hz
  -- A bump in the parameter equal to one on `closedBall z (d / 4)`, supported away from `ℝ`.
  let ρ : ContDiffBump z := ⟨d / 4, d / 2, by positivity, by linarith⟩
  obtain ⟨hgs, hgc⟩ := contDiff_hasCompactSupport_bump_mul_cauchyKernel χ ρ
    (show d / 2 < d by linarith)
  have hρ1 (w : ℂ) (hw : ‖w - z‖ < d / 4) : ρ w = 1 :=
    ρ.one_of_mem_closedBall (by rw [mem_closedBall, dist_eq_norm]; exact hw.le)
  refine ⟨_, hgs, hgc, d / 4, by positivity, fun w hw h0 ↦ ?_, fun w hw t ↦ ?_, fun t h ↦ ?_⟩
  · have := abs_im_le_norm (w - z)
    rw [sub_im, h0, zero_sub, abs_neg] at this
    linarith
  · simp [hρ1 w hw, cauchyKernel_apply, div_eq_mul_inv]
  · have hloc : (fun q : ℂ × ℝ ↦ (ρ q.1 : ℂ) * ((χ q.2 : ℂ) * ((q.2 : ℂ) - q.1)⁻¹)) =ᶠ[𝓝 (z, t)]
        fun q : ℂ × ℝ ↦ (χ q.2 : ℂ) * ((q.2 : ℂ) - q.1)⁻¹ :=
      ((continuous_fst.tendsto (z, t)).eventually
        (ball_mem_nhds z (by positivity : 0 < d / 4))).mono fun q hq ↦ by
          simp [hρ1 q.1 (by rwa [dist_eq_norm] at hq)]
    rw [hloc.fderiv_eq]
    exact fderiv_cauchyKernel_apply_inl χ hz t h

/-- **Holomorphy of the pairing with the Cauchy kernel.** The map
`z ↦ ⟨u_t, χ(t) / (t - z)⟩` is complex differentiable at every non-real `z`, with derivative
`⟨u_t, χ(t) / (t - z)²⟩`. -/
private theorem hasDerivAt_complexPairing_cauchyKernel (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) {z : ℂ}
    (hz : z.im ≠ 0) :
    HasDerivAt (fun w ↦ if hw : w.im ≠ 0 then u.complexPairing (cauchyKernel χ 1 hw) else 0)
      (u.complexPairing (cauchyKernel χ 2 hz)) z := by
  obtain ⟨g, hgs, hgc, d, hd, him, hgw, hgd⟩ := exists_contDiff_slice_eq_cauchyKernel χ hz
  have hz' : ‖z - z‖ < d := by simpa using hd
  -- The pairing of `u` with the Taylor remainder of the kernels is `o(|h|)`.
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  let K : Compacts ℝ := ⟨tsupport χ, χ.hasCompactSupport.isCompact⟩
  obtain ⟨N, C, hC, hu⟩ := u.exists_norm_complexPairing_le (K := K) χ.tsupport_subset
  have hε : 0 < c / (C + 1) := div_pos hc (by linarith)
  have hrem := fun i ↦ hgc.exists_norm_iteratedFDeriv_prod_right_sub_sub_le hgs (i := i)
    (by exact_mod_cast le_top) z hε
  choose r hr hrem using hrem
  let r₀ := min d ((Finset.range (N + 1)).inf' (by simp) r)
  have hr₀ : 0 < r₀ := lt_min (by positivity) ((Finset.lt_inf'_iff _).2 fun i _ ↦ hr i)
  filter_upwards [ball_mem_nhds (0 : ℂ) hr₀] with h hh
  rw [mem_ball_zero_iff] at hh
  have hhd : ‖z + h - z‖ < d := by
    rw [add_sub_cancel_left]
    exact hh.trans_le (min_le_left _ _)
  have hzh : (z + h).im ≠ 0 := him _ hhd
  set R : 𝓓(Ω, ℂ) := cauchyKernel χ 1 hzh - cauchyKernel χ 1 hz - h • cauchyKernel χ 2 hz
  have hR : (R : ℝ → ℂ) = fun t ↦ g (z + h, t) - g (z, t) - fderiv ℝ g (z, t) (h, 0) := by
    funext t
    rw [hgw _ hhd t, hgw z hz' t, hgd t h]
    simp [R]
  have hRK : tsupport R ⊆ K := closure_mono (Function.support_subset_iff'.2 fun t ht ↦ by
    simp [R, cauchyKernel_apply, Function.notMem_support.1 ht])
  have hRbound : ∀ i ≤ N, ∀ t, ‖iteratedFDeriv ℝ i R t‖ ≤ c / (C + 1) * ‖h‖ := by
    intro i hi t
    have hri : ‖h‖ < r i := hh.trans_le ((min_le_right _ _).trans
      (Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hi))))
    rw [hR]
    exact hrem i h hri t
  have hval : u.complexPairing R = u.complexPairing (cauchyKernel χ 1 hzh) -
      u.complexPairing (cauchyKernel χ 1 hz) - h • u.complexPairing (cauchyKernel χ 2 hz) := by
    simp [R]
  simp only [ne_eq, hzh, hz, not_false_eq_true, ↓reduceDIte]
  rw [← hval]
  calc ‖u.complexPairing R‖ ≤ C * (c / (C + 1) * ‖h‖) := hu R hRK _ (by positivity) hRbound
    _ = C / (C + 1) * (c * ‖h‖) := by ring
    _ ≤ c * ‖h‖ :=
      mul_le_of_le_one_left (by positivity) ((div_le_one (by linarith)).2 (by linarith))

/-- **The Cauchy transform is holomorphic off the real line**, with derivative
`(2πi)⁻¹ ⟨u_t, χ(t) / (t - z)²⟩`. -/
theorem hasDerivAt_cauchyTransform (u : 𝓓'(Ω, ℂ)) (χ : 𝓓(Ω, ℝ)) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (cauchyTransform u χ)
      ((2 * π * I)⁻¹ * u.complexPairing (cauchyKernel χ 2 hz)) z :=
  (hasDerivAt_complexPairing_cauchyKernel u χ hz).const_mul _

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
      u.complexPairing_eq_of_eventuallyEq (ψ := cauchyKernel χ₂ 1 hz)
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
  rw [cauchyTransform_of_im_ne_zero _ χ hz, complexPairing_apply]
  simp only [mapCLM_apply, delta_apply, postcompCLM_apply, Function.comp_apply, ofRealCLM_apply,
    reCLM_apply, imCLM_apply, mul_comm I, re_add_im, cauchyKernel_apply, pow_one]

/-- **The normalization of the Cauchy transform.** For a cutoff with `χ(0) = 1`, the Cauchy
transform of `δ₀` is `-(2πiz)⁻¹` on both half-planes. -/
theorem cauchyTransform_delta_zero {χ : 𝓓(Ω, ℝ)} (hχ : χ 0 = 1) {z : ℂ} (hz : z.im ≠ 0) :
    cauchyTransform (mapCLM ofRealCLM (delta 0 : 𝓓'(Ω, ℝ))) χ z = -(2 * π * I * z)⁻¹ := by
  rw [cauchyTransform_delta 0 χ hz, hχ]
  simp [div_eq_mul_inv]
  ring

end TauCeti.Hyperfunction
