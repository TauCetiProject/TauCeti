/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.LocalExtr

/-!
# The weak maximum principle on a rectangle with a Neumann condition

Let `Q = [a, b] × [c, d]` be a closed rectangle in `ℂ = ℝ²`, with `c < d`, and let `v : ℂ → ℝ` be
continuous on `Q`. Suppose that wherever `v` exceeds a level `m`

* `v` is `C²` and subharmonic, `Δ v ≥ 0`, at the interior points of `Q`;
* `v` is differentiable on the open horizontal sides of `Q` and its outward normal derivative is
  nonpositive there: `∂ₜ v ≥ 0` on the bottom side `im z = c` and `∂ₜ v ≤ 0` on the top side
  `im z = d`.

If `v ≤ m` on the two vertical sides `re z = a` and `re z = b`, then `v ≤ m` on all of `Q`
(`TauCeti.le_of_laplacian_nonneg_of_lt_of_neumann`). Thus a subharmonic function with a Neumann
(or one-sided Neumann) condition on two opposite sides attains its maximum on the other two.
Nothing is assumed at the points where `v ≤ m`.

This is the form of the maximum principle used for holomorphic strips `ℝ × [0, 1]` whose
boundary lines satisfy a Neumann condition and whose ends are controlled: the radial coordinate
of a holomorphic strip with boundary on Lagrangians that are conical at infinity is such a
function.

The proof perturbs `v` by `ε φ` for the barrier `φ(z) = 3/2 (re z - a)² - 1/2 (im z - y₀)²`,
`y₀ = (c + d) / 2`, which is strictly subharmonic, `Δ φ = 2`, and whose normal derivative is
strictly inward on both horizontal sides. A maximizer of `v + ε φ` over `Q` at which `v > m` can
then lie neither in the interior of `Q` nor on a horizontal side, so it lies on a vertical side;
letting `ε → 0` gives the bound.

## Main results

* `TauCeti.le_of_laplacian_nonneg_of_lt_of_neumann`: the weak maximum principle on a rectangle
  with a Neumann condition on its horizontal sides and a bound on its vertical sides.
-/

public section

namespace TauCeti

open Complex InnerProductSpace Laplacian Set Topology

/-- The barrier `3/2 (re z - re z₀)² - 1/2 (im z - im z₀)²`, strictly subharmonic with normal
derivative `-(im z - im z₀)` in the direction `i`. -/
private noncomputable def neumannBarrier (z₀ z : ℂ) : ℝ :=
  3 / 2 * (z.re - z₀.re) ^ 2 - 1 / 2 * (z.im - z₀.im) ^ 2

private theorem contDiff_neumannBarrier (z₀ : ℂ) : ContDiff ℝ 2 (neumannBarrier z₀) := by
  unfold neumannBarrier
  have hre : ContDiff ℝ 2 fun z : ℂ ↦ z.re := reCLM.contDiff
  have him : ContDiff ℝ 2 fun z : ℂ ↦ z.im := imCLM.contDiff
  fun_prop

private theorem laplacian_neumannBarrier (z₀ z : ℂ) : Δ (neumannBarrier z₀) z = 2 := by
  -- `φ` is the harmonic function `re ((z - z₀)²)` plus half the squared distance to `z₀`.
  have hfun : neumannBarrier z₀ =
      (fun w : ℂ ↦ ((w - z₀) ^ 2).re) + (1 / 2 : ℝ) • fun w : ℂ ↦ ‖w + -z₀‖ ^ 2 := by
    ext w
    simp only [neumannBarrier, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← sub_eq_add_neg,
      Complex.sq_norm, normSq_apply]
    simp only [sq, mul_re, sub_re, sub_im]
    ring
  have hre : HarmonicAt (fun w : ℂ ↦ ((w - z₀) ^ 2).re) z :=
    AnalyticAt.harmonicAt_re (by fun_prop)
  have hsq : ContDiffAt ℝ 2 (fun w : ℂ ↦ ‖w + -z₀‖ ^ 2) z :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.add contDiff_const)).contDiffAt
  have hsq' : ContDiffAt ℝ 2 ((1 / 2 : ℝ) • fun w : ℂ ↦ ‖w + -z₀‖ ^ 2) z :=
    (hsq.const_smul (1 / 2 : ℝ) :)
  have htr := congrFun (laplacian_comp_add_right (fun w : ℂ ↦ ‖w‖ ^ 2) (-z₀)) z
  simp only [laplacian_norm_sq, Complex.finrank_real_complex] at htr
  rw [hfun, hre.1.laplacian_add hsq', laplacian_smul _ hsq, hre.2.self_of_nhds, htr]
  norm_num

private theorem fderiv_neumannBarrier_I (z₀ z : ℂ) :
    fderiv ℝ (neumannBarrier z₀) z I = -(z.im - z₀.im) := by
  have h₁ := (((reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt (x := z)).sub_const z₀.re).pow 2 |>.const_mul
    (3 / 2 : ℝ)
  have h₂ := (((imCLM : ℂ →L[ℝ] ℝ).hasFDerivAt (x := z)).sub_const z₀.im).pow 2 |>.const_mul
    (1 / 2 : ℝ)
  have h : HasFDerivAt (neumannBarrier z₀) _ z := h₁.sub h₂
  rw [h.fderiv]
  simp

/-- On the rectangle `[a, b] × [c, d]`, the barrier with `z₀ = a + i (c + d) / 2` varies by at
most `3/2 (b - a)² + 1/2 (d - c)²`. -/
private theorem neumannBarrier_sub_le {a b c d : ℝ} {y z : ℂ} (hy : y ∈ Icc a b ×ℂ Icc c d)
    (hz : z ∈ Icc a b ×ℂ Icc c d) :
    neumannBarrier ⟨a, (c + d) / 2⟩ y - neumannBarrier ⟨a, (c + d) / 2⟩ z ≤
      3 / 2 * (b - a) ^ 2 + 1 / 2 * (d - c) ^ 2 := by
  obtain ⟨⟨hya, hyb⟩, hyc, hyd⟩ := hy
  obtain ⟨⟨hza, hzb⟩, hzc, hzd⟩ := hz
  simp only [neumannBarrier]
  nlinarith [mul_nonneg (sub_nonneg.2 hya) (sub_nonneg.2 hyb),
    mul_nonneg (sub_nonneg.2 hzc) (sub_nonneg.2 hzd), sq_nonneg (z.re - a)]

/-- The maximizer step: at a maximizer `y` over the rectangle of `v` perturbed by a positive
multiple of the barrier, `v y ≤ m`. A maximizer with `v y > m` can lie neither on a vertical side,
where `v ≤ m`, nor on a horizontal side, where `v + ε φ` would increase in the inward vertical
direction, nor in the interior, where `v + ε φ` is strictly subharmonic. -/
private theorem le_of_isMaxOn_add_smul_neumannBarrier {v : ℂ → ℝ} {a b c d m ε : ℝ}
    (hcd : c < d) (hC2 : ∀ z ∈ Ioo a b ×ℂ Ioo c d, m < v z → ContDiffAt ℝ 2 v z)
    (hlap : ∀ z ∈ Ioo a b ×ℂ Ioo c d, m < v z → 0 ≤ Δ v z)
    (hdiff : ∀ z ∈ Ioo a b ×ℂ {c, d}, m < v z → DifferentiableAt ℝ v z)
    (hbot : ∀ z ∈ Ioo a b ×ℂ {c}, m < v z → 0 ≤ fderiv ℝ v z I)
    (htop : ∀ z ∈ Ioo a b ×ℂ {d}, m < v z → fderiv ℝ v z I ≤ 0)
    (hside : ∀ z ∈ {a, b} ×ℂ Icc c d, v z ≤ m) (hε : 0 < ε) {y : ℂ}
    (hyQ : y ∈ Icc a b ×ℂ Icc c d)
    (hymax : IsMaxOn (v + ε • neumannBarrier ⟨a, (c + d) / 2⟩) (Icc a b ×ℂ Icc c d) y) :
    v y ≤ m := by
  set Q := Icc a b ×ℂ Icc c d
  set φ := neumannBarrier ⟨a, (c + d) / 2⟩
  have hφc : ContDiff ℝ 2 φ := contDiff_neumannBarrier _
  by_contra! hmy
  obtain ⟨⟨hya, hyb⟩, hyc, hyd⟩ := hyQ
  rcases hya.eq_or_lt with hya | hya
  · exact (hside y ⟨Or.inl hya.symm, hyc, hyd⟩).not_gt hmy
  rcases hyb.eq_or_lt with hyb | hyb
  · exact (hside y ⟨Or.inr hyb, hyc, hyd⟩).not_gt hmy
  -- On a horizontal side, the derivative of `v + ε φ` in an inward vertical direction `e`
  -- would be positive, contradicting maximality.
  have hside_nonpos : ∀ e : ℂ, segment ℝ y (y + e) ⊆ Q → DifferentiableAt ℝ v y →
      fderiv ℝ v y e + ε * fderiv ℝ φ y e ≤ 0 := fun e he hvd ↦ by
    have hder := hvd.hasFDerivAt.add
      ((hφc.differentiable (by norm_num) y).hasFDerivAt.const_smul ε)
    simpa using hymax.isLocalMaxOn.hasFDerivWithinAt_nonpos hder.hasFDerivWithinAt
      (mem_posTangentConeAt_of_segment_subset he)
  have hseg : ∀ t : ℝ, c ≤ y.im + t → y.im + t ≤ d → segment ℝ y (y + t • I) ⊆ Q := by
    intro t hct htd w hw
    rw [segment_eq_image'] at hw
    obtain ⟨θ, ⟨hθ₀, hθ₁⟩, rfl⟩ := hw
    refine ⟨⟨by simpa using hya.le, by simpa using hyb.le⟩, ?_, ?_⟩ <;> simp <;> nlinarith
  rcases hyc.eq_or_lt with hyc | hyc
  · -- Bottom side: the direction `(d - c) i` points into `Q`.
    have h := hside_nonpos ((d - c) • I) (hseg _ (by linarith) (by linarith))
      (hdiff y ⟨⟨hya, hyb⟩, Or.inl hyc.symm⟩ hmy)
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, fderiv_neumannBarrier_I] at h
    have hb := hbot y ⟨⟨hya, hyb⟩, hyc.symm⟩ hmy
    simp only [← hyc] at h
    nlinarith [mul_nonneg (sub_nonneg.2 hcd.le) hb, mul_pos (sub_pos.2 hcd) hε]
  rcases hyd.eq_or_lt with hyd | hyd
  · -- Top side: the direction `-(d - c) i` points into `Q`.
    have h := hside_nonpos ((c - d) • I) (hseg _ (by linarith) (by linarith))
      (hdiff y ⟨⟨hya, hyb⟩, Or.inr hyd⟩ hmy)
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, fderiv_neumannBarrier_I] at h
    have ht := htop y ⟨⟨hya, hyb⟩, hyd⟩ hmy
    simp only [hyd] at h
    nlinarith [mul_nonneg (sub_nonneg.2 hcd.le) (neg_nonneg.2 ht), mul_pos (sub_pos.2 hcd) hε]
  -- Interior: `v + ε φ` is strictly subharmonic at `y`, so `y` is not a local maximum.
  have hyint : y ∈ Ioo a b ×ℂ Ioo c d := ⟨⟨hya, hyb⟩, hyc, hyd⟩
  have hmem : Q ∈ 𝓝 y := by
    rw [← mem_interior_iff_mem_nhds, interior_reProdIm, interior_Icc, interior_Icc]
    exact hyint
  have hφ : ContDiffAt ℝ 2 (ε • φ) y := hφc.contDiffAt.const_smul ε
  refine not_isLocalMax_of_laplacian_pos (f := v + ε • φ) ((hC2 y hyint hmy).add hφ) ?_
    (hymax.isLocalMax hmem)
  rw [(hC2 y hyint hmy).laplacian_add hφ, laplacian_smul _ hφc.contDiffAt,
    laplacian_neumannBarrier, smul_eq_mul]
  nlinarith [hlap y hyint hmy]

/-- **The weak maximum principle on a rectangle with a Neumann condition.** Let `c < d` and let
`v` be continuous on the rectangle `Q = [a, b] × [c, d]`. Suppose that, at the points where
`v > m`, the function `v` is `C²` and subharmonic in the interior of `Q`, and differentiable with
nonpositive outward normal derivative on the open horizontal sides of `Q`: `∂ₜ v ≥ 0` where
`im z = c` and `∂ₜ v ≤ 0` where `im z = d`. If `v ≤ m` on the vertical sides `re z = a` and
`re z = b`, then `v ≤ m` on `Q`. -/
theorem le_of_laplacian_nonneg_of_lt_of_neumann {v : ℂ → ℝ} {a b c d m : ℝ} (hcd : c < d)
    (hcont : ContinuousOn v (Icc a b ×ℂ Icc c d))
    (hC2 : ∀ z ∈ Ioo a b ×ℂ Ioo c d, m < v z → ContDiffAt ℝ 2 v z)
    (hlap : ∀ z ∈ Ioo a b ×ℂ Ioo c d, m < v z → 0 ≤ Δ v z)
    (hdiff : ∀ z ∈ Ioo a b ×ℂ {c, d}, m < v z → DifferentiableAt ℝ v z)
    (hbot : ∀ z ∈ Ioo a b ×ℂ {c}, m < v z → 0 ≤ fderiv ℝ v z I)
    (htop : ∀ z ∈ Ioo a b ×ℂ {d}, m < v z → fderiv ℝ v z I ≤ 0)
    (hside : ∀ z ∈ {a, b} ×ℂ Icc c d, v z ≤ m) {z : ℂ} (hz : z ∈ Icc a b ×ℂ Icc c d) :
    v z ≤ m := by
  set φ := neumannBarrier ⟨a, (c + d) / 2⟩
  set B := 3 / 2 * (b - a) ^ 2 + 1 / 2 * (d - c) ^ 2
  have hB : 0 ≤ B := by positivity
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  set ε := δ / (B + 1)
  have hε : 0 < ε := div_pos hδ (by positivity)
  obtain ⟨y, hyQ, hymax⟩ := (isCompact_Icc.reProdIm isCompact_Icc).exists_isMaxOn ⟨z, hz⟩
    (hcont.add ((contDiff_neumannBarrier ⟨a, (c + d) / 2⟩).continuous.continuousOn.const_smul ε))
  have hvy : v y ≤ m := le_of_isMaxOn_add_smul_neumannBarrier hcd hC2 hlap hdiff hbot htop hside
    hε hyQ hymax
  have hmax : v z + ε * φ z ≤ v y + ε * φ y := by simpa using hymax hz
  have hφ : φ y - φ z ≤ B := neumannBarrier_sub_le hyQ hz
  have hεB : ε * B ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hφ hε.le]

end TauCeti
