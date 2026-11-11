/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Perturbation
public import TauCeti.Analysis.Calculus.ContDiff.Cutoff
public import TauCeti.Analysis.Calculus.ContDiff.Compact
public import TauCeti.Analysis.Calculus.FDeriv.UniformConvergence

/-!
# Cutoff corrections of nearby coordinate maps

A `C^n` compactly supported cutoff extends local maps converging to the identity in value
and first derivative to global `C^n` diffeomorphisms. Composing with an inverse limiting
transition gives corrections that preserve the overlap domain. The construction works along
an arbitrary filter of indices and any regularity order `n ≥ 1`.

## Main results

* `ContDiff.eventually_exists_cutoff_diffeomorph_of_contDiffAt`: a fixed cutoff extends
  sufficiently close local maps to diffeomorphisms, with exact inner and outer agreement.
* `TauCeti.eventually_exists_local_transition_correction`: correct convergent transition maps
  and preserve their overlap domain.

## References

* [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Filter
open scoped ContDiff Topology NNReal Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {n : WithTop ℕ∞}

/-- Eventually along the index filter, the cutoff perturbation
`x ↦ x + χ x • (f k x - x)` is a global `C^n` diffeomorphism. It agrees with `f k`
where `χ = 1` and is the identity off `tsupport χ`. -/
theorem _root_.ContDiff.eventually_exists_cutoff_diffeomorph_of_contDiffAt
    {χ : E → ℝ} (hχ : ContDiff ℝ n χ) (hχcompact : HasCompactSupport χ)
    (hn : 1 ≤ n)
    {ι : Type*} {l : Filter ι} {f : ι → E → E}
    (hf : ∀ᶠ k in l, ∀ x ∈ tsupport χ, ContDiffAt ℝ n (f k) x)
    (hzero : TendstoUniformlyOn f id l (tsupport χ))
    (hone : TendstoUniformlyOn (fun k ↦ fderiv ℝ (f k))
      (fun _ ↦ ContinuousLinearMap.id ℝ E) l (tsupport χ)) :
    ∀ᶠ k in l, ∃ e : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E,
      (∀ x, e x = x + χ x • (f k x - x)) ∧
      (∀ x, χ x = 1 → e x = f k x) ∧ (∀ x, x ∉ tsupport χ → e x = x) := by
  -- Choose an error threshold from bounds for the cutoff and its derivative.
  obtain ⟨B₀, hB₀⟩ := hχcompact.isCompact.exists_bound_of_continuousOn hχ.continuous.continuousOn
  obtain ⟨B₁, hB₁⟩ := hχcompact.isCompact.exists_bound_of_continuousOn
    (hχ.continuous_fderiv (zero_lt_one.trans_le hn).ne').continuousOn
  let B := max B₀ 0 + max B₁ 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let ε := 1 / (4 * B)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεB : B * ε = 1 / 4 := by dsimp [ε]; field_simp
  filter_upwards [hf, Metric.tendstoUniformlyOn_iff.mp hzero ε hε,
    Metric.tendstoUniformlyOn_iff.mp hone ε hε] with k hk hk₀ hk₁
  have hclose (x : E) :
      ‖fderiv ℝ (fun y ↦ y + χ y • (f k y - y)) x - ContinuousLinearMap.id ℝ E‖ ≤
        (1 / 2 : ℝ≥0) := by
    by_cases hx : x ∈ tsupport χ
    · have hfx := (hk x hx).differentiableAt (zero_lt_one.trans_le hn).ne'
      have h₀ : ‖f k x - x‖ < ε := by simpa only [id_eq, dist_eq_norm, norm_sub_rev] using hk₀ x hx
      have h₁ : ‖fderiv ℝ (f k) x - ContinuousLinearMap.id ℝ E‖ < ε := by
        simpa only [dist_eq_norm, norm_sub_rev] using hk₁ x hx
      have hbound := norm_fderiv_cutoff_perturbation_sub_id_le_of_bounds
        (hχ.differentiable (zero_lt_one.trans_le hn).ne' x) hfx
        ((hB₀ x hx).trans (le_max_left B₀ 0))
        ((hB₁ x hx).trans (le_max_left B₁ 0)) h₀.le h₁.le
      have hsum : (max B₀ 0 + max B₁ 0) * ε ≤ B * ε := by
        dsimp [B]
        nlinarith
      norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at ⊢
      linarith
    · rw [fderiv_cutoff_perturbation_eq_id_of_notMem_tsupport hx, sub_self, norm_zero]
      positivity
  -- The derivative bound gives a global diffeomorphism.
  obtain ⟨e, he⟩ := ContDiff.exists_diffeomorph_apply_eq_of_norm_fderiv_sub_id_le
    (hχ.contDiff_cutoff_perturbation_of_contDiffAt hk) hn (by norm_num : (1 / 2 : ℝ≥0) < 1) hclose
  refine ⟨e, he, ?_, ?_⟩
  · intro x hx
    rw [he, hx, one_smul, add_sub_cancel]
  · intro x hx
    rw [he, image_eq_zero_of_notMem_tsupport hx, zero_smul, add_zero]

/-- If `fseq` converges to `f` in value and first derivative uniformly on compact subsets of `U`,
and `g : V → U` is a `C^n` right inverse of `f`, a cutoff supported in `V` eventually gives a
`C^n` diffeomorphism `e = id + χ • (fseq k ∘ g - id)`. It agrees with `fseq k ∘ g` where `χ = 1`,
fixes the complement of `tsupport χ`, and maps `V` onto itself. -/
theorem eventually_exists_local_transition_correction
    {ι : Type*} {l : Filter ι} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f g : E → E} (hf : DifferentiableOn ℝ f U) (hg : ContDiffOn ℝ n g V)
    (hgU : MapsTo g V U) (hfg : EqOn (f ∘ g) id V)
    {fseq : ι → E → E}
    (hlocal : ∀ x ∈ U, ∃ W : Set E, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in l, ContDiffOn ℝ n (fseq k) W)
    (hzero : ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn fseq f l K)
    (hone : ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k ↦ fderiv ℝ (fseq k)) (fderiv ℝ f) l K)
    {χ : E → ℝ} (hχ : ContDiff ℝ n χ) (hχcompact : HasCompactSupport χ)
    (hn : 1 ≤ n)
    (hχV : tsupport χ ⊆ V) :
    ∀ᶠ k in l, ∃ e : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E,
      (∀ x, e x = x + χ x • (fseq k (g x) - x)) ∧
      (∀ x, χ x = 1 → e x = fseq k (g x)) ∧
      (∀ x, x ∉ tsupport χ → e x = x) ∧ e '' V = V := by
  -- Compactness supplies a common regularity threshold on the image of the support.
  have hK := hχcompact.isCompact.image_of_continuousOn (hg.continuousOn.mono hχV)
  have hKU : g '' tsupport χ ⊆ U := image_subset_iff.mpr (fun _ hx ↦ hgU (hχV hx))
  have hs := hK.eventually_forall_contDiffAt_of_eventually_contDiffOn
    (fun x hx ↦ hlocal x (hKU hx))
  have hscomp : ∀ᶠ k in l, ∀ x ∈ tsupport χ, ContDiffAt ℝ n (fseq k ∘ g) x :=
    hs.mono fun _ hk x hx ↦ (hk _ (mem_image_of_mem g hx)).comp x
      (hg.contDiffAt (hV.mem_nhds (hχV hx)))
  have hz : TendstoUniformlyOn (fun k ↦ fseq k ∘ g) id l (tsupport χ) :=
    (((hzero _ hK hKU).comp g).mono (subset_preimage_image g (tsupport χ))).congr_right
      (hfg.mono hχV)
  -- Composition with the limiting inverse preserves uniform derivative convergence.
  obtain ⟨B, hB⟩ := hχcompact.isCompact.exists_bound_of_continuousOn
    ((hg.continuousOn_fderiv_of_isOpen hV hn).mono hχV)
  have ho := (hone _ hK hKU).fderiv_comp_of_rightInverse
    (fun x hx ↦ (hf _ (hgU (hχV hx))).differentiableAt
      (hU.mem_nhds (hgU (hχV hx))))
    (fun x hx ↦ (hg.contDiffAt (hV.mem_nhds (hχV hx))).differentiableAt
      (zero_lt_one.trans_le hn).ne')
    (hs.mono fun _ hk x hx ↦ (hk _ (mem_image_of_mem g hx)).differentiableAt
      (zero_lt_one.trans_le hn).ne')
    (fun x hx ↦ Filter.eventuallyEq_of_mem (hV.mem_nhds (hχV hx)) hfg) hB
  -- Apply the cutoff construction and use the fixed complement to preserve `V`.
  filter_upwards [ContDiff.eventually_exists_cutoff_diffeomorph_of_contDiffAt
    hχ hχcompact hn hscomp hz ho] with k hk
  obtain ⟨e, he, heone, hefix⟩ := hk
  refine ⟨e, he, heone, hefix, ?_⟩
  have hfix : EqOn e.toEquiv id Vᶜ := fun x hx ↦ hefix x (fun h ↦ hx (hχV h))
  have hc := e.toEquiv.image_compl Vᶜ
  rw [compl_compl, hfix.image_eq_self, compl_compl] at hc
  simpa only [Diffeomorph.coe_toEquiv] using hc

end TauCeti
