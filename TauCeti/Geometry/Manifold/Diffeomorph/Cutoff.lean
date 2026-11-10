/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Perturbation
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Algebra.Support

/-!
# Cutoff corrections of nearby coordinate maps

A smooth compactly supported cutoff extends local maps converging to the identity in value
and first derivative to global smooth diffeomorphisms. Composing with an inverse limiting
transition gives corrections that preserve the overlap domain. The construction works along
an arbitrary filter of indices and any regularity order `n ≥ 1`.

## Main results

* `ContDiff.eventually_exists_cutoff_diffeomorphism_of_contDiffAt`: a fixed cutoff extends
  sufficiently close local maps to diffeomorphisms, with exact inner and outer agreement.
* `ContDiff.eventually_exists_local_transition_correction`: correct convergent transition maps
  and preserve their overlap domain.

## References

* [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Filter
open scoped ContDiff Topology NNReal Manifold

namespace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {n : WithTop ℕ∞}

omit [CompleteSpace E] in
private theorem cutoff_smul_eventually_zero {χ : E → ℝ} {f : E → E} {x : E}
    (hx : x ∉ tsupport χ) : (fun y ↦ χ y • f y) =ᶠ[𝓝 x] 0 := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
  simp only [Pi.zero_apply] at hy ⊢
  rw [hy, zero_smul]

omit [CompleteSpace E] in
/-- A smooth scalar cutoff turns a map smooth near its closed support into a globally smooth
perturbation of the identity; no completeness is needed. -/
theorem contDiff_cutoff_perturbation_of_contDiffAt
    {χ : E → ℝ} (hχ : ContDiff ℝ n χ) {f : E → E}
    (hf : ∀ x ∈ tsupport χ, ContDiffAt ℝ n f x) :
    ContDiff ℝ n (fun x ↦ x + χ x • (f x - x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact contDiffAt_id.add (hχ.contDiffAt.smul ((hf x hx).sub contDiffAt_id))
  · apply contDiffAt_id.add
    exact contDiffAt_const.congr_of_eventuallyEq (cutoff_smul_eventually_zero hx)

omit [CompleteSpace E] in
/-- Smoothness on an open set containing the cutoff support suffices for the cutoff perturbation to
be globally smooth. -/
theorem contDiff_cutoff_perturbation
    {U : Set E} (hU : IsOpen U) {χ : E → ℝ} (hχ : ContDiff ℝ n χ)
    (hχU : tsupport χ ⊆ U) {f : E → E} (hf : ContDiffOn ℝ n f U) :
    ContDiff ℝ n (fun x ↦ x + χ x • (f x - x)) := by
  exact contDiff_cutoff_perturbation_of_contDiffAt hχ
    (fun _ hx ↦ hf.contDiffAt (hU.mem_nhds (hχU hx)))

omit [CompleteSpace E] in
/-- Product-rule bound for the derivative error of a cutoff perturbation, in terms of the value and
derivative errors of the local map. -/
theorem norm_fderiv_cutoff_perturbation_sub_id_le
    {χ : E → ℝ} {f : E → E} {x : E}
    (hχ : DifferentiableAt ℝ χ x) (hf : DifferentiableAt ℝ f x) :
    ‖fderiv ℝ (fun y ↦ y + χ y • (f y - y)) x - ContinuousLinearMap.id ℝ E‖ ≤
      ‖χ x‖ * ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ +
        ‖fderiv ℝ χ x‖ * ‖f x - x‖ := by
  have hd := (hasFDerivAt_id x).add
    (hχ.hasFDerivAt.smul (hf.hasFDerivAt.sub (hasFDerivAt_id x)))
  change HasFDerivAt (fun y ↦ y + χ y • (f y - y))
    (ContinuousLinearMap.id ℝ E +
      (χ x • (fderiv ℝ f x - ContinuousLinearMap.id ℝ E) +
        (fderiv ℝ χ x).smulRight (f x - x))) x at hd
  rw [hd.fderiv, add_sub_cancel_left]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply])

/-- A local coordinate perturbation tending to the identity in value and first
derivative extends, through a fixed cutoff, to global smooth diffeomorphisms. -/
theorem eventually_exists_cutoff_diffeomorphism_of_contDiffAt
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
      have hbound := norm_fderiv_cutoff_perturbation_sub_id_le
        (hχ.differentiable (zero_lt_one.trans_le hn).ne' x) hfx
      have ha : ‖χ x‖ ≤ max B₀ 0 := (hB₀ x hx).trans (le_max_left _ _)
      have hb : ‖fderiv ℝ χ x‖ ≤ max B₁ 0 := (hB₁ x hx).trans (le_max_left _ _)
      have ha' := mul_le_mul ha h₁.le (norm_nonneg _) (le_max_right B₀ 0)
      have hb' := mul_le_mul hb h₀.le (norm_nonneg _) (le_max_right B₁ 0)
      have hsum : max B₀ 0 * ε + max B₁ 0 * ε ≤ B * ε := by
        dsimp [B]
        nlinarith
      norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at ⊢
      linarith
    · have heq : (fun y ↦ y + χ y • (f k y - y)) =ᶠ[𝓝 x] id := by
        filter_upwards [cutoff_smul_eventually_zero (f := fun y ↦ f k y - y) hx] with y hy
        simp only [Pi.zero_apply] at hy
        simp only [hy, add_zero, id_eq]
      rw [heq.fderiv_eq, fderiv_id, sub_self, norm_zero]
      positivity
  obtain ⟨e, he⟩ := ContDiff.exists_diffeomorph_of_fderiv_close_id
    (contDiff_cutoff_perturbation_of_contDiffAt hχ hk) hn (by norm_num : (1 / 2 : ℝ≥0) < 1) hclose
  refine ⟨e, he, ?_, ?_⟩
  · intro x hx
    rw [he, hx, one_smul, add_sub_cancel]
  · intro x hx
    have hz := (cutoff_smul_eventually_zero (f := fun y ↦ f k y - y) hx).self_of_nhds
    rw [he]
    simpa only [Pi.zero_apply, add_zero] using congrArg (fun v ↦ x + v) hz

/-- Uniform value and first-derivative convergence on the compact cutoff support gives eventual
smooth global inverse corrections, with the stated exact inside and outside agreement. -/
theorem eventually_exists_cutoff_diffeomorphism
    {U : Set E} (hU : IsOpen U) {χ : E → ℝ} (hχ : ContDiff ℝ n χ)
    (hχcompact : HasCompactSupport χ) (hn : 1 ≤ n) (hχU : tsupport χ ⊆ U)
    {ι : Type*} {l : Filter ι} {f : ι → E → E} (hf : ∀ᶠ k in l, ContDiffOn ℝ n (f k) U)
    (hzero : TendstoUniformlyOn f id l (tsupport χ))
    (hone : TendstoUniformlyOn (fun k ↦ fderiv ℝ (f k))
      (fun _ ↦ ContinuousLinearMap.id ℝ E) l (tsupport χ)) :
    ∀ᶠ k in l, ∃ e : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E,
      (∀ x, e x = x + χ x • (f k x - x)) ∧
      (∀ x, χ x = 1 → e x = f k x) ∧ (∀ x, x ∉ tsupport χ → e x = x) :=
  eventually_exists_cutoff_diffeomorphism_of_contDiffAt hχ hχcompact hn
    (hf.mono fun _ hk _ hx ↦ hk.contDiffAt (hU.mem_nhds (hχU hx))) hzero hone

omit [CompleteSpace E] in
/-- A compact subset admits one eventual threshold for pointwise smoothness when each point has an
eventually smooth neighborhood. -/
theorem eventually_contDiffAt_on_compact_of_locally_eventually_smooth
    {Ω K : Set E} {ι : Type*} {l : Filter ι} {f : ι → E → E} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hlocal : ∀ x ∈ Ω, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
      ∀ᶠ k in l, ContDiffOn ℝ n (f k) V) :
    ∀ᶠ k in l, ∀ x ∈ K, ContDiffAt ℝ n (f k) x := by
  refine hK.induction_on (p := fun S ↦ ∀ᶠ k in l,
    ∀ x ∈ S, ContDiffAt ℝ n (f k) x) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (by simp)
  · intro S T hST hT
    exact hT.mono fun _ hk x hx ↦ hk x (hST hx)
  · intro S T hS hT
    filter_upwards [hS, hT] with k hkS hkT x hx
    exact hx.elim (hkS x) (hkT x)
  · intro x hx
    obtain ⟨V, hV, hxV, hVsmooth⟩ := hlocal x (hKΩ hx)
    exact ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV),
      hVsmooth.mono fun _ hk _ hy ↦ hk.contDiffAt (hV.mem_nhds hy)⟩

/-- The inverse limiting transition turns a convergent family of local
transitions into a perturbation of the identity on the cutoff support. -/
theorem eventually_exists_local_transition_correction
    {ι : Type*} {l : Filter ι} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f g : E → E} (hf : ContDiffOn ℝ n f U) (hg : ContDiffOn ℝ n g V)
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
  have hK := hχcompact.isCompact.image_of_continuousOn (hg.continuousOn.mono hχV)
  have hKU : g '' tsupport χ ⊆ U := image_subset_iff.mpr (fun _ hx ↦ hgU (hχV hx))
  have hs := eventually_contDiffAt_on_compact_of_locally_eventually_smooth hK hKU hlocal
  have hscomp : ∀ᶠ k in l, ∀ x ∈ tsupport χ, ContDiffAt ℝ n (fseq k ∘ g) x :=
    hs.mono fun _ hk x hx ↦ (hk _ (mem_image_of_mem g hx)).comp x
      (hg.contDiffAt (hV.mem_nhds (hχV hx)))
  have hz : TendstoUniformlyOn (fun k ↦ fseq k ∘ g) id l (tsupport χ) :=
    (((hzero _ hK hKU).comp g).mono (subset_preimage_image g (tsupport χ))).congr_right
      (hfg.mono hχV)
  obtain ⟨B, hB⟩ := hχcompact.isCompact.exists_bound_of_continuousOn
    ((hg.continuousOn_fderiv_of_isOpen hV hn).mono hχV)
  have ho : TendstoUniformlyOn (fun k ↦ fderiv ℝ (fseq k ∘ g))
      (fun _ ↦ ContinuousLinearMap.id ℝ E) l (tsupport χ) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have hden : 0 < max B 0 + 1 := by positivity
    have hε' : 0 < ε / (max B 0 + 1) := div_pos hε hden
    filter_upwards [hs, Metric.tendstoUniformlyOn_iff.mp (hone _ hK hKU) _ hε']
      with k hk hsmall x hx
    have hgx := (hg.contDiffAt (hV.mem_nhds (hχV hx))).differentiableAt
      (zero_lt_one.trans_le hn).ne'
    have hfx := (hf.contDiffAt (hU.mem_nhds (hgU (hχV hx)))).differentiableAt
      (zero_lt_one.trans_le hn).ne'
    have heq : f ∘ g =ᶠ[𝓝 x] id := by
      filter_upwards [hV.mem_nhds (hχV hx)] with y hy
      exact hfg hy
    have hder : (fderiv ℝ f (g x)).comp (fderiv ℝ g x) = ContinuousLinearMap.id ℝ E := by
      rw [← fderiv_comp x hfx hgx, heq.fderiv_eq, fderiv_id]
    rw [dist_eq_norm, norm_sub_rev,
      fderiv_comp x ((hk _ (mem_image_of_mem g hx)).differentiableAt
        (zero_lt_one.trans_le hn).ne') hgx,
      ← hder, ← ContinuousLinearMap.sub_comp]
    have hd : ‖fderiv ℝ (fseq k) (g x) - fderiv ℝ f (g x)‖ < ε / (max B 0 + 1) := by
      simpa only [dist_eq_norm, norm_sub_rev] using hsmall _ (mem_image_of_mem g hx)
    have hb : ‖fderiv ℝ g x‖ ≤ max B 0 := (hB x hx).trans (le_max_left _ _)
    calc
      _ ≤ ‖fderiv ℝ (fseq k) (g x) - fderiv ℝ f (g x)‖ * ‖fderiv ℝ g x‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ (fseq k) (g x) - fderiv ℝ f (g x)‖ * (max B 0 + 1) := by
        gcongr
        linarith
      _ < ε := (lt_div_iff₀ hden).mp hd
  filter_upwards [eventually_exists_cutoff_diffeomorphism_of_contDiffAt
    hχ hχcompact hn hscomp hz ho] with k hk
  obtain ⟨e, he, heone, hefix⟩ := hk
  refine ⟨e, he, heone, hefix, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_contra hy
    have heey := hefix (e x) (fun h ↦ hy (hχV h))
    have hxy := e.injective heey
    exact hy (hxy.symm ▸ hx)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    by_contra hx
    have hey := hefix (e.symm y) (fun h ↦ hx (hχV h))
    rw [e.apply_symm_apply] at hey
    exact hx (hey ▸ hy)

end ContDiff
