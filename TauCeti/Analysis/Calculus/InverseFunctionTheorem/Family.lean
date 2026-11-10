/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ApproximatesLinearOn
public import TauCeti.Analysis.Calculus.ContDiff.TaylorInverse
public import TauCeti.Analysis.Calculus.ContDiff.TendstoAt
public import TauCeti.Analysis.Calculus.FDeriv.Equiv
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem

/-!
# The inverse function theorem for converging families

Let `Φ i → Φ₀` in `C^n` near `x₀`, with `1 ≤ n` and `D Φ₀ (x₀)` invertible. The inverse
function theorem applies to every `Φ i` with `i` close enough to the limit with *uniform*
constants: on a fixed ball `B` around `x₀` each `Φ i` approximates the linear map `D Φ₀ (x₀)`
with the same constant, so all these maps restrict to partial homeomorphisms with the common
source `B`, whose targets all contain a fixed neighbourhood `T` of `Φ₀ (x₀)`. On `T` the local
inverses converge to the inverse of `Φ₀` in `C^n`
(`TauCeti.exists_openPartialHomeomorph_tendstoContDiffAt_symm`).

The order-zero convergence comes from the uniform antilipschitz bound of the approximation.
Higher derivatives of the inverses are then recovered from the Faà di Bruno formula for
`(Φ i)⁻¹ ∘ Φ i = id`, whose singleton-partition term is the only one that involves the top
derivative of the inverse (`TauCeti.TendstoContDiffAt.symm`); this is the argument by which
inversion is continuous in `C^n` topologies.

## Main declarations

* `TauCeti.TendstoContDiffAt.symm`: if partial homeomorphisms converge in `C^n` and their
  inverses converge continuously, the inverses converge in `C^n`.
* `TauCeti.exists_openPartialHomeomorph_tendstoContDiffAt_symm`: the inverse function theorem
  with a common domain and `C^n` convergence of the local inverses.
-/

public section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ι : Type*} {l : Filter ι} {n : ℕ}

/-- **`C^n` convergence of inverses.** Let `e i` be partial homeomorphisms converging in `C^n`
to `e₀` at `e₀⁻¹ (y₀)`, with `e i` and its inverse `C^n` near the relevant points. If the
inverses converge continuously at `y₀`, then they converge in `C^n` at `y₀`. -/
theorem TendstoContDiffAt.symm [CompleteSpace E] {e : ι → OpenPartialHomeomorph E F}
    {e₀ : OpenPartialHomeomorph E F} {y₀ : F} (hy₀ : y₀ ∈ e₀.target)
    (he : TendstoContDiffAt 𝕜 n (fun i ↦ ⇑(e i)) e₀ l (e₀.symm y₀))
    (hsymm : Tendsto (fun p : ι × F ↦ (e p.1).symm p.2) (l ×ˢ 𝓝 y₀) (𝓝 (e₀.symm y₀)))
    (hd : ∀ᶠ p in l ×ˢ 𝓝 y₀, p.2 ∈ (e p.1).target ∧
      ContDiffAt 𝕜 n (e p.1) ((e p.1).symm p.2) ∧ ContDiffAt 𝕜 n (e p.1).symm p.2)
    (hd₀ : ContDiffAt 𝕜 n e₀ (e₀.symm y₀)) (hds₀ : ContDiffAt 𝕜 n e₀.symm y₀) :
    TendstoContDiffAt 𝕜 n (fun i ↦ ⇑(e i).symm) e₀.symm l y₀ := by
  have hlim : Tendsto (fun p : ι × F ↦ (p.1, (e p.1).symm p.2)) (l ×ˢ 𝓝 y₀)
      (l ×ˢ 𝓝 (e₀.symm y₀)) :=
    tendsto_fst.prodMk hsymm
  -- The composite `(e i)⁻¹ ∘ e i` is the identity near the moving point `(e i)⁻¹ y`.
  have hcomp (k : ℕ) (hk : k ≤ n) : Tendsto (fun p : ι × F ↦
      (ftaylorSeries 𝕜 (e p.1).symm p.2).taylorComp
        (ftaylorSeries 𝕜 (e p.1) ((e p.1).symm p.2)) k) (l ×ˢ 𝓝 y₀)
      (𝓝 ((ftaylorSeries 𝕜 e₀.symm y₀).taylorComp (ftaylorSeries 𝕜 e₀ (e₀.symm y₀)) k)) := by
    have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ n := by exact_mod_cast hk
    rw [e₀.taylorComp_ftaylorSeries_symm hy₀ (hd₀.of_le hk') (hds₀.of_le hk')]
    refine ((((contDiff_id (𝕜 := 𝕜) (E := E) (n := k)).continuous_iteratedFDeriv
      le_rfl).tendsto _).comp hsymm).congr' ?_
    filter_upwards [hd] with p hp
    exact ((e p.1).taylorComp_ftaylorSeries_symm hp.1 (hp.2.1.of_le hk') (hp.2.2.of_le hk')).symm
  -- The derivatives of the inverses are the inverses of the derivatives.
  have hA (hn : 1 ≤ n) : Tendsto (fun p : ι × F ↦ fderiv 𝕜 (e p.1).symm p.2) (l ×ˢ 𝓝 y₀)
      (𝓝 (fderiv 𝕜 e₀.symm y₀)) := by
    have hn' : ((n : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have h₁ := e₀.fderiv_comp_fderiv_symm hy₀ (hd₀.differentiableAt hn')
      (hds₀.differentiableAt hn')
    have h₂ := e₀.fderiv_symm_comp_fderiv hy₀ (hd₀.differentiableAt hn')
      (hds₀.differentiableAt hn')
    have hcont : ContinuousAt ContinuousLinearMap.inverse (fderiv 𝕜 e₀ (e₀.symm y₀)) := by
      simpa using (contDiffAt_map_inverse (n := 0)
        (ContinuousLinearEquiv.equivOfInverse' _ _ h₁ h₂)).continuousAt
    rw [← ContinuousLinearMap.inverse_eq h₁ h₂]
    refine (hcont.tendsto.comp ((he.tendsto_fderiv hn).comp hlim)).congr' ?_
    filter_upwards [hd] with p hp
    exact ContinuousLinearMap.inverse_eq
      ((e p.1).fderiv_comp_fderiv_symm hp.1 (hp.2.1.differentiableAt hn')
        (hp.2.2.differentiableAt hn'))
      ((e p.1).fderiv_symm_comp_fderiv hp.1 (hp.2.1.differentiableAt hn')
        (hp.2.2.differentiableAt hn'))
  refine tendstoContDiffAt_iff.2 fun k hk ↦ ?_
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact (tendstoContDiffAt_zero_iff (f := fun i ↦ ⇑(e i).symm) (f₀ := e₀.symm).2
        hsymm).tendsto_iteratedFDeriv le_rfl
    have hn : 1 ≤ n := hk0.trans_le hk
    have hn' : ((n : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    -- Recover the `k`-th inverse coefficient from the lower ones and the identity composite.
    refine Filter.Tendsto.of_taylorComp (q := fun p : ι × F ↦ ftaylorSeries 𝕜 (e p.1).symm p.2)
      (p := fun p : ι × F ↦ ftaylorSeries 𝕜 (e p.1) ((e p.1).symm p.2))
      (q₀ := ftaylorSeries 𝕜 e₀.symm y₀) (p₀ := ftaylorSeries 𝕜 e₀ (e₀.symm y₀))
      (A := fun p : ι × F ↦ fderiv 𝕜 (e p.1).symm p.2) (A₀ := fderiv 𝕜 e₀.symm y₀) hk0
      (fun j _ hj ↦ ih j hj (hj.le.trans hk))
      (fun j _ hj ↦ (he.tendsto_iteratedFDeriv (hj.trans hk)).comp hlim)
      (hcomp k hk) (hA hn) ?_ ?_
    · filter_upwards [hd] with p hp
      simpa only [ftaylorSeries, continuousMultilinearCurryFin1_iteratedFDeriv_one] using
        (e p.1).fderiv_comp_fderiv_symm hp.1 (hp.2.1.differentiableAt hn')
          (hp.2.2.differentiableAt hn')
    · simpa only [ftaylorSeries, continuousMultilinearCurryFin1_iteratedFDeriv_one] using
        e₀.fderiv_comp_fderiv_symm hy₀ (hd₀.differentiableAt hn') (hds₀.differentiableAt hn')

section Existence

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ι : Type*} {l : Filter ι} {n : ℕ}

/-- A map approximating `L` on `ball x₀ r` with half the critical constant `c` has, in the target
of its partial homeomorphism, the ball of radius `c * (r / 2) / 2` about every point within that
distance of its value at `x₀`. -/
private theorem ball_subset_toOpenPartialHomeomorph_target {g : E → F} {L : E ≃L[𝕜] F} {x₀ : E}
    {r : ℝ} {c : ℝ≥0} (hr : 0 < r) (hcL : c = ‖(L.symm : F →L[𝕜] E)‖₊⁻¹ / 2)
    (hga : ApproximatesLinearOn g (L : E →L[𝕜] F) (ball x₀ r) c)
    (hc : Subsingleton E ∨ c < ‖(L.symm : F →L[𝕜] E)‖₊⁻¹) {y₀ : F}
    (hy₀ : dist (g x₀) y₀ < c * (r / 2) / 2) :
    ball y₀ (c * (r / 2) / 2) ⊆
      (hga.toOpenPartialHomeomorph g (ball x₀ r) hc isOpen_ball).target := by
  intro y hy
  have hsub := hga.closedBall_subset_target hc isOpen_ball (b := x₀) (ε := r / 2)
    (by positivity) (closedBall_subset_ball (by linarith))
  have hcc : ((‖(L.symm : F →L[𝕜] E)‖₊⁻¹ : ℝ≥0) : ℝ) - c = c := by
    rw [hcL, NNReal.coe_div, NNReal.coe_two]
    ring
  rw [hcc] at hsub
  refine hsub (mem_closedBall.mpr ?_)
  rw [mem_ball] at hy
  linarith [dist_triangle_right y (g x₀) y₀]

/-- **The inverse function theorem for a converging family.** Let `Φ i → Φ₀` in `C^n` at every
point of an open set `s`, with `1 ≤ n`, the maps `Φ i` eventually `C^n` on `s`, and `D Φ₀`
invertible at `x₀ ∈ s`. Then `Φ₀` and, eventually along `l`, all the `Φ i` restrict to partial
homeomorphisms with one common source inside `s`, whose targets contain a common open
neighbourhood `T` of `Φ₀ (x₀)` and whose inverses are `C^n` on their targets. On `T` the inverses
converge to the inverse of `Φ₀` in `C^n`. -/
theorem exists_openPartialHomeomorph_tendstoContDiffAt_symm {Φ : ι → E → F} {Φ₀ : E → F}
    {s : Set E} {x₀ : E} (hs : IsOpen s) (hx₀ : x₀ ∈ s) (hn : 1 ≤ n)
    (hΦ : ∀ᶠ i in l, ContDiffOn 𝕜 n (Φ i) s) (hΦ₀ : ContDiffOn 𝕜 n Φ₀ s)
    (hconv : ∀ x ∈ s, TendstoContDiffAt 𝕜 n Φ Φ₀ l x)
    (hinv : (fderiv 𝕜 Φ₀ x₀).IsInvertible) :
    ∃ (e₀ : OpenPartialHomeomorph E F) (e : ι → OpenPartialHomeomorph E F) (T : Set F),
      IsOpen T ∧ Φ₀ x₀ ∈ T ∧ ⇑e₀ = Φ₀ ∧ x₀ ∈ e₀.source ∧ e₀.source ⊆ s ∧ T ⊆ e₀.target ∧
      ContDiffOn 𝕜 n e₀.symm e₀.target ∧
      (∀ᶠ i in l, ⇑(e i) = Φ i ∧ (e i).source = e₀.source ∧ T ⊆ (e i).target ∧
        ContDiffOn 𝕜 n (e i).symm (e i).target) ∧
      ∀ y ∈ T, TendstoContDiffAt 𝕜 n (fun i ↦ ⇑(e i).symm) e₀.symm l y := by
  classical
  obtain ⟨L, hL⟩ := hinv
  have hn' : ((n : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  set c : ℝ≥0 := ‖(L.symm : F →L[𝕜] E)‖₊⁻¹ / 2 with hc_def
  have hc : Subsingleton E ∨ c < ‖(L.symm : F →L[𝕜] E)‖₊⁻¹ :=
    L.subsingleton_or_nnnorm_symm_pos.imp id fun h ↦ NNReal.half_lt_self (inv_ne_zero h.ne')
  -- The derivatives of the family and of the limit stay within `c` of `L` near `x₀`.
  have hnear : ∀ᶠ q in 𝓝 (L : E →L[𝕜] F), ‖q - (L : E →L[𝕜] F)‖₊ ≤ c := by
    rcases L.subsingleton_or_nnnorm_symm_pos with hE | hpos
    · refine Eventually.of_forall fun q ↦ ?_
      have : q - L = 0 := ContinuousLinearMap.ext fun v ↦ by simp [Subsingleton.elim v 0]
      simp [this]
    · filter_upwards [closedBall_mem_nhds (L : E →L[𝕜] F)
        (show (0 : ℝ) < c by positivity)] with q hq
      rw [← NNReal.coe_le_coe, coe_nnnorm, ← dist_eq_norm]
      exact hq
  have hev : ∀ᶠ p in l ×ˢ 𝓝 x₀, ‖fderiv 𝕜 (Φ p.1) p.2 - (L : E →L[𝕜] F)‖₊ ≤ c := by
    have h := (hconv x₀ hx₀).tendsto_fderiv hn
    rw [← hL] at h
    exact h.eventually hnear
  have hev₀ : ∀ᶠ x in 𝓝 x₀, ‖fderiv 𝕜 Φ₀ x - (L : E →L[𝕜] F)‖₊ ≤ c := by
    have h := ((hΦ₀.contDiffAt (hs.mem_nhds hx₀)).continuousAt_fderiv hn').tendsto
    rw [← hL] at h
    exact h.eventually hnear
  obtain ⟨pa, hpa, pb, hpb, hpab⟩ := eventually_prod_iff.mp hev
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hpb.and hev₀).and (hs.mem_nhds hx₀))
  have hrs : ball x₀ r ⊆ s := fun x hx ↦ (hrb x hx).2
  -- Every map that is `C^n` on `s` with derivative near `L` on the ball is a chart there.
  have key (g : E → F) (hg : ContDiffOn 𝕜 n g s)
      (hgb : ∀ x ∈ ball x₀ r, ‖fderiv 𝕜 g x - (L : E →L[𝕜] F)‖₊ ≤ c) :
      ∃ hga : ApproximatesLinearOn g (L : E →L[𝕜] F) (ball x₀ r) c,
        ContDiffOn 𝕜 n (hga.toOpenPartialHomeomorph g (ball x₀ r) hc isOpen_ball).symm
          (hga.toOpenPartialHomeomorph g (ball x₀ r) hc isOpen_ball).target := by
    have hgd (x) (hx : x ∈ ball x₀ r) : ContDiffAt 𝕜 n g x := hg.contDiffAt (hs.mem_nhds (hrs hx))
    let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    have hga := (convex_ball x₀ r).approximatesLinearOn_of_nnnorm_fderiv_sub_le
      (fun x hx ↦ (hgd x hx).differentiableAt hn') hgb
    refine ⟨hga, OpenPartialHomeomorph.contDiffOn_symm_of_isInvertible_fderiv _
      (fun x hx ↦ (hgd x hx).contDiffWithinAt) fun x hx ↦ ?_⟩
    exact ContinuousLinearMap.isInvertible_of_norm_sub_le_half L (hgb x hx)
  obtain ⟨h₀a, h₀c⟩ := key Φ₀ hΦ₀ fun x hx ↦ (hrb x hx).1.2
  set e₀ := h₀a.toOpenPartialHomeomorph Φ₀ (ball x₀ r) hc isOpen_ball with he₀_def
  have he₀c : ⇑e₀ = Φ₀ := by rw [he₀_def, ApproximatesLinearOn.toOpenPartialHomeomorph_coe]
  have he₀s : e₀.source = ball x₀ r := by
    rw [he₀_def, ApproximatesLinearOn.toOpenPartialHomeomorph_source]
  have hrs₀ : e₀.source ⊆ s := he₀s ▸ hrs
  let e : ι → OpenPartialHomeomorph E F := fun i ↦
    if h : ApproximatesLinearOn (Φ i) (L : E →L[𝕜] F) (ball x₀ r) c then
      h.toOpenPartialHomeomorph (Φ i) (ball x₀ r) hc isOpen_ball else e₀
  -- A common radius `ρ` of target balls around `Φ₀ x₀`.
  obtain ⟨ρ, hρ, hρT⟩ : ∃ ρ > 0, ∀ (g : E → F)
      (hga : ApproximatesLinearOn g (L : E →L[𝕜] F) (ball x₀ r) c), ‖g x₀ - Φ₀ x₀‖ < ρ →
        ball (Φ₀ x₀) ρ ⊆ (hga.toOpenPartialHomeomorph g (ball x₀ r) hc isOpen_ball).target := by
    rcases L.subsingleton_or_nnnorm_symm_pos with hE | hpos
    · have hF : Subsingleton F := L.symm.toEquiv.subsingleton
      refine ⟨1, one_pos, fun g hga _ y _ ↦ ?_⟩
      rw [Subsingleton.elim y (g x₀), ApproximatesLinearOn.toOpenPartialHomeomorph_target]
      exact mem_image_of_mem g (mem_ball_self hr)
    · refine ⟨c * (r / 2) / 2, by positivity, fun g hga hg ↦ ?_⟩
      exact ball_subset_toOpenPartialHomeomorph_target hr hc_def hga hc (by rwa [dist_eq_norm])
  have hΦx₀ : Tendsto (fun i ↦ Φ i x₀) l (𝓝 (Φ₀ x₀)) :=
    (hconv x₀ hx₀).tendsto.comp (tendsto_id.prodMk tendsto_const_nhds)
  have hgood : ∀ᶠ i in l, ContDiffOn 𝕜 n (Φ i) s ∧ pa i ∧ ‖Φ i x₀ - Φ₀ x₀‖ < ρ := by
    filter_upwards [hΦ, hpa, hΦx₀.eventually (ball_mem_nhds _ hρ)] with i h1 h2 h3
    exact ⟨h1, h2, by rw [← dist_eq_norm]; exact h3⟩
  -- Properties of the good members of the family.
  have hgood' : ∀ i, ContDiffOn 𝕜 n (Φ i) s ∧ pa i ∧ ‖Φ i x₀ - Φ₀ x₀‖ < ρ →
      ∃ hia : ApproximatesLinearOn (Φ i) (L : E →L[𝕜] F) (ball x₀ r) c,
        ⇑(e i) = Φ i ∧ (e i).source = ball x₀ r ∧
        ContDiffOn 𝕜 n (e i).symm (e i).target ∧ ball (Φ₀ x₀) ρ ⊆ (e i).target := by
    rintro i ⟨h1, h2, h3⟩
    obtain ⟨hia, hic⟩ := key (Φ i) h1 fun x hx ↦ hpab h2 (hrb x hx).1.1
    have hei : e i = hia.toOpenPartialHomeomorph (Φ i) (ball x₀ r) hc isOpen_ball := by
      simp [e, hia]
    refine ⟨hia, ?_, ?_, hei ▸ hic, hei ▸ hρT (Φ i) hia h3⟩
    · rw [hei, ApproximatesLinearOn.toOpenPartialHomeomorph_coe]
    · rw [hei, ApproximatesLinearOn.toOpenPartialHomeomorph_source]
  have hT₀ : ball (Φ₀ x₀) ρ ⊆ e₀.target := hρT Φ₀ h₀a (by simpa using hρ)
  -- Order zero: the inverses converge continuously, by the uniform antilipschitz bound.
  have hsymm (y : F) (hy : y ∈ ball (Φ₀ x₀) ρ) :
      Tendsto (fun p : ι × F ↦ (e p.1).symm p.2) (l ×ˢ 𝓝 y) (𝓝 (e₀.symm y)) := by
    set K : ℝ≥0 := (‖(L.symm : F →L[𝕜] E)‖₊⁻¹ - c)⁻¹
    have hyt := hT₀ hy
    have hb : Tendsto (fun p : ι × F ↦ e₀.symm p.2) (l ×ˢ 𝓝 y) (𝓝 (e₀.symm y)) :=
      (e₀.continuousAt_symm hyt).tendsto.comp tendsto_snd
    have hbs : e₀.symm y ∈ s := hrs₀ (e₀.map_target hyt)
    have h₁ : Tendsto (fun p : ι × F ↦ Φ p.1 (e₀.symm p.2)) (l ×ˢ 𝓝 y)
        (𝓝 (Φ₀ (e₀.symm y))) :=
      (hconv _ hbs).tendsto.comp (tendsto_fst.prodMk hb)
    have h₂ : Tendsto (fun p : ι × F ↦ Φ₀ (e₀.symm p.2)) (l ×ˢ 𝓝 y) (𝓝 (Φ₀ (e₀.symm y))) :=
      ((hΦ₀.continuousOn.continuousAt (hs.mem_nhds hbs)).tendsto).comp hb
    have hd : Tendsto (fun p : ι × F ↦
        K * dist (Φ₀ (e₀.symm p.2)) (Φ p.1 (e₀.symm p.2)) + dist (e₀.symm p.2) (e₀.symm y))
        (l ×ˢ 𝓝 y) (𝓝 0) := by
      simpa using ((h₂.dist h₁).const_mul (K : ℝ)).add
        (hb.dist (tendsto_const_nhds (x := e₀.symm y)))
    refine tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ ↦
      dist_nonneg) ?_ hd)
    filter_upwards [tendsto_fst.eventually hgood,
      tendsto_snd.eventually (isOpen_ball.mem_nhds hy)] with p hp hpT
    obtain ⟨hia, hec, hes, -, hiT⟩ := hgood' p.1 hp
    have hpt := hiT hpT
    have ha : (e p.1).symm p.2 ∈ ball x₀ r := hes ▸ (e p.1).map_target hpt
    have hb' : e₀.symm p.2 ∈ ball x₀ r := he₀s ▸ e₀.map_target (hT₀ hpT)
    have hanti := (hia.antilipschitzWith hc).le_mul_dist ⟨_, ha⟩ ⟨_, hb'⟩
    have hΦa : Φ p.1 ((e p.1).symm p.2) = p.2 := by
      rw [← hec]
      exact (e p.1).right_inv hpt
    have hΦb : Φ₀ (e₀.symm p.2) = p.2 := by
      rw [← he₀c]
      exact e₀.right_inv (hT₀ hpT)
    simp only [Subtype.dist_eq, Set.domRestrict_apply, hΦa] at hanti
    have hanti' : dist ((e p.1).symm p.2) (e₀.symm p.2) ≤
        K * dist (Φ₀ (e₀.symm p.2)) (Φ p.1 (e₀.symm p.2)) := by
      rw [hΦb]
      exact hanti
    calc dist ((e p.1).symm p.2) (e₀.symm y)
        ≤ dist ((e p.1).symm p.2) (e₀.symm p.2) + dist (e₀.symm p.2) (e₀.symm y) :=
          dist_triangle _ _ _
      _ ≤ _ := by gcongr
  refine ⟨e₀, e, ball (Φ₀ x₀) ρ, isOpen_ball, mem_ball_self hρ, he₀c, he₀s ▸ mem_ball_self hr,
    hrs₀, hT₀, h₀c, ?_, fun y hy ↦ ?_⟩
  · filter_upwards [hgood] with i hi
    obtain ⟨hia, hec, hes, hic, hiT⟩ := hgood' i hi
    exact ⟨hec, hes.trans he₀s.symm, hiT, hic⟩
  · have hyt := hT₀ hy
    have hconv' : TendstoContDiffAt 𝕜 n (fun i ↦ ⇑(e i)) e₀ l (e₀.symm y) := by
      rw [he₀c]
      refine (hconv _ (hrs₀ (e₀.map_target hyt))).congr ?_
      filter_upwards [hgood] with i hi
      obtain ⟨hia, hec, -⟩ := hgood' i hi
      exact hec.symm
    refine hconv'.symm hyt (hsymm y hy) ?_ ?_ ?_
    · filter_upwards [tendsto_fst.eventually hgood,
        tendsto_snd.eventually (isOpen_ball.mem_nhds hy)] with p hp hpT
      obtain ⟨hia, hec, hes, hic, hiT⟩ := hgood' p.1 hp
      have hpt := hiT hpT
      refine ⟨hpt, ?_, hic.contDiffAt ((e p.1).open_target.mem_nhds hpt)⟩
      rw [hec]
      exact hp.1.contDiffAt (hs.mem_nhds (hrs (hes ▸ (e p.1).map_target hpt)))
    · rw [he₀c]
      exact hΦ₀.contDiffAt (hs.mem_nhds (hrs₀ (e₀.map_target hyt)))
    · exact h₀c.contDiffAt (e₀.open_target.mem_nhds hyt)

end Existence

end TauCeti
