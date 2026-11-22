/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import TauCeti.Analysis.Analytic.Constructions
public import TauCeti.Analysis.Analytic.Hadamard

/-!
# Constant order of vanishing in a distinguished variable

Let `G (x, y)` be analytic near `(x₀, y₀)`, over `ℝ` or `ℂ`, with `y` a distinguished scalar
variable. This file shows that `G` vanishes to order exactly `m` in `y` along `y = y₀` for every
`x` near `x₀` if and only if `G (x, y) = (y - y₀) ^ m • u (x, y)` near `(x₀, y₀)` with `u` analytic
and `u (x₀, y₀) ≠ 0` (`AnalyticAt.eventually_analyticOrderAt_eq_natCast_iff`). This is
McCallum–Parusiński–Paunescu, Lemma 4.4. Since `u` is then nonzero near `(x₀, y₀)`, the
factorization holds on a product of balls `ball x₀ r ×ˢ ball y₀ r`, a polydisc when `E` is `ι → 𝕜`,
on which `u` is analytic and nowhere zero (`AnalyticAt.exists_ball_prod_eq_pow_smul` and
`AnalyticAt.eventually_analyticOrderAt_eq_natCast_iff_exists_ball`). This writes a function of
constant order in a distinguished variable as a centered power `(y - y₀) ^ m` times a
nowhere-vanishing analytic factor, the form of the hypotheses of the Puiseux theorem with
parameters (op. cit., §4).

The version with `m ≤` the order in place of equality, and no condition on `u`, is
`AnalyticAt.eventually_natCast_le_analyticOrderAt_iff`. It rests on Hadamard's lemma in a
distinguished variable (`AnalyticAt.exists_eventuallyEq_sub_smul`): a function analytic at
`(x₀, y₀)` that vanishes on `y = y₀` near `x₀` is `(y - y₀) • H` near `(x₀, y₀)` with `H` analytic.
Applied in both variables, it shows that a function of two variables vanishing on two crossing
lines is divisible by the product of their equations
(`AnalyticAt.exists_eventuallyEq_mul_smul`). After straightening, the same holds along the graph
`y = g x` of an analytic function: a function vanishing there is `(y - g x) • H`
(`AnalyticAt.exists_eventuallyEq_sub_smul_of_graph`). In particular a function of `(b, x, y)`
vanishing on the hypersurface `xy = S(b)` away from `x = y = 0` is a multiple of `xy - S(b)`
(`AnalyticAt.exists_eventuallyEq_mul_sub_smul_of_fst_ne_zero` and
`AnalyticAt.exists_eventuallyEq_mul_sub_smul_of_snd_ne_zero`).

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, J. Symbolic Comput. 92 (2019), 52–69, Lemma 4.4.
-/

public section

open Filter Set Topology

section NontriviallyNormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Shrinking to a nowhere-vanishing unit.** A local factorization
`G (x, y) = (y - y₀) ^ m • u (x, y)` with `u` analytic at `(x₀, y₀)` and `u (x₀, y₀) ≠ 0` holds on
a product of balls `ball x₀ r ×ˢ ball y₀ r` on which `u` is analytic and nowhere zero. When `E` is
`ι → 𝕜` with its sup norm, this product is a polydisc. -/
theorem AnalyticAt.exists_ball_prod_eq_pow_smul {G u : E × 𝕜 → F} {x₀ : E} {y₀ : 𝕜} {m : ℕ}
    (hu : AnalyticAt 𝕜 u (x₀, y₀)) (hu0 : u (x₀, y₀) ≠ 0)
    (hGu : ∀ᶠ p in 𝓝 (x₀, y₀), G p = (p.2 - y₀) ^ m • u p) :
    ∃ r > 0, AnalyticOnNhd 𝕜 u (Metric.ball x₀ r ×ˢ Metric.ball y₀ r) ∧
      ∀ p ∈ Metric.ball x₀ r ×ˢ Metric.ball y₀ r, u p ≠ 0 ∧ G p = (p.2 - y₀) ^ m • u p := by
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff_ball.1
    (hu.eventually_analyticAt.and ((hu.continuousAt.eventually_ne hu0).and hGu))
  rw [← ball_prod_same] at h
  exact ⟨r, hr, fun p hp ↦ (h p hp).1, fun p hp ↦ (h p hp).2⟩

end NontriviallyNormedField

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Hadamard's lemma along a graph**: a function `G` analytic at `(x₀, g x₀)` that vanishes on
the graph `y = g x` of a function `g` analytic at `x₀` is `(y - g x) • H (x, y)` near
`(x₀, g x₀)`, with `H` analytic at `(x₀, g x₀)`. -/
theorem AnalyticAt.exists_eventuallyEq_sub_smul_of_graph {G : E × 𝕜 → F} {g : E → 𝕜} {x₀ : E}
    (hG : AnalyticAt 𝕜 G (x₀, g x₀)) (hg : AnalyticAt 𝕜 g x₀)
    (h0 : ∀ᶠ x in 𝓝 x₀, G (x, g x) = 0) :
    ∃ H : E × 𝕜 → F, AnalyticAt 𝕜 H (x₀, g x₀) ∧
      ∀ᶠ p in 𝓝 (x₀, g x₀), G p = (p.2 - g p.1) • H p := by
  -- `Φ` straightens the graph onto the hyperplane `y = 0`, and `Ψ` is its inverse.
  set Φ : E × 𝕜 → E × 𝕜 := fun q ↦ (q.1, q.2 + g q.1)
  set Ψ : E × 𝕜 → E × 𝕜 := fun q ↦ (q.1, q.2 - g q.1)
  have hΦ : AnalyticAt 𝕜 Φ (x₀, 0) :=
    analyticAt_fst.prod (analyticAt_snd.add (hg.comp analyticAt_fst))
  have hΨ : AnalyticAt 𝕜 Ψ (x₀, g x₀) :=
    analyticAt_fst.prod (analyticAt_snd.sub (hg.comp analyticAt_fst))
  have hΨ₀ : Ψ (x₀, g x₀) = (x₀, 0) := by simp [Ψ]
  obtain ⟨K, hK, hGK⟩ := (hG.comp_of_eq hΦ (by simp [Φ])).exists_eventuallyEq_sub_smul
    (h0.mono fun x hx ↦ by simpa [Φ] using hx)
  refine ⟨K ∘ Ψ, hK.comp_of_eq hΨ hΨ₀, ?_⟩
  have hΨt : Tendsto Ψ (𝓝 (x₀, g x₀)) (𝓝 (x₀, 0)) := hΨ₀ ▸ hΨ.continuousAt.tendsto
  filter_upwards [hΨt.eventually hGK] with p hp
  simpa [Φ, Ψ] using hp

/-- **Functions vanishing on two crossing lines.** A function of two scalar variables which is
analytic at `(a, b)` and vanishes near `(a, b)` on the lines `y = b` and `x = a` is
`(x - a) (y - b)` times a function analytic at `(a, b)`. -/
theorem AnalyticAt.exists_eventuallyEq_mul_smul {G : 𝕜 × 𝕜 → F} {a b : 𝕜}
    (hG : AnalyticAt 𝕜 G (a, b)) (h₁ : ∀ᶠ x in 𝓝 a, G (x, b) = 0)
    (h₂ : ∀ᶠ y in 𝓝 b, G (a, y) = 0) :
    ∃ K : 𝕜 × 𝕜 → F, AnalyticAt 𝕜 K (a, b) ∧
      ∀ᶠ p in 𝓝 (a, b), G p = ((p.1 - a) * (p.2 - b)) • K p := by
  -- Divide by `y - b`: `G (x, y) = (y - b) • g (x, y)`.
  obtain ⟨g, hg, hGg⟩ := hG.exists_eventuallyEq_sub_smul h₁
  have hla : Tendsto (fun y : 𝕜 ↦ (a, y)) (𝓝 b) (𝓝 (a, b)) :=
    (Continuous.prodMk_right a).tendsto' b (a, b) rfl
  -- The quotient `g` vanishes on `x = a`: off `y = b` because `G` does, then by continuity.
  have hga : ∀ᶠ y in 𝓝 b, g (a, y) = 0 := by
    refine ((hg.continuousAt.comp hla).eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (g := fun _ ↦ 0) continuousAt_const).1 ?_
    filter_upwards [nhdsWithin_le_nhds (hla.eventually hGg), nhdsWithin_le_nhds h₂,
      self_mem_nhdsWithin] with y hy hy₂ hne
    rw [hy₂, eq_comm, smul_eq_zero] at hy
    exact hy.resolve_left (sub_ne_zero.2 hne)
  -- Divide `g` by `x - a`: `g (x, y) = (x - a) • k (y, x)`.
  have hswap : AnalyticAt 𝕜 Prod.swap (a, b) := analyticAt_snd.prod analyticAt_fst
  obtain ⟨k, hk, hgk⟩ := (hg.comp (f := Prod.swap) (x := (b, a))
    (analyticAt_snd.prod analyticAt_fst)).exists_eventuallyEq_sub_smul (h0 := hga)
  refine ⟨k ∘ Prod.swap, hk.comp (f := Prod.swap) (x := (a, b)) hswap, ?_⟩
  filter_upwards [hGg, (continuous_swap.tendsto (a, b)).eventually hgk] with p hp hpk
  rw [Function.comp_apply, Prod.swap_swap, Prod.snd_swap] at hpk
  rw [hp, hpk, smul_smul, mul_comm (p.2 - b), Function.comp_apply]

/-- **Functions vanishing on `xy = S(b)` where `x ≠ 0`.** A function `G (b, x, y)` analytic at a
point `p` of the hypersurface `xy = S(b)` with `x ≠ 0`, for `S` analytic at the base point of `p`,
that vanishes near `p` on the hypersurface (written as the graph `y = S(b)/x`), is
`(xy - S(b)) • K` near `p` with `K` analytic at `p`. -/
theorem AnalyticAt.exists_eventuallyEq_mul_sub_smul_of_fst_ne_zero {G : E × 𝕜 × 𝕜 → F}
    {S : E → 𝕜} {p : E × 𝕜 × 𝕜} (hG : AnalyticAt 𝕜 G p) (hS : AnalyticAt 𝕜 S p.1)
    (hx : p.2.1 ≠ 0) (hp : S p.1 = p.2.1 * p.2.2)
    (h0 : ∀ᶠ w in 𝓝 (p.1, p.2.1), G (w.1, w.2, S w.1 / w.2) = 0) :
    ∃ K : E × 𝕜 × 𝕜 → F, AnalyticAt 𝕜 K p ∧
      ∀ᶠ q in 𝓝 p, G q = (q.2.1 * q.2.2 - S q.1) • K q := by
  -- Regroup the coordinates as `((b, x), y)` and apply Hadamard's lemma along the graph.
  set A : E × 𝕜 × 𝕜 → (E × 𝕜) × 𝕜 := fun q ↦ ((q.1, q.2.1), q.2.2)
  set B : (E × 𝕜) × 𝕜 → E × 𝕜 × 𝕜 := fun q ↦ (q.1.1, q.1.2, q.2)
  set g : E × 𝕜 → 𝕜 := fun w ↦ S w.1 / w.2
  have hg : AnalyticAt 𝕜 g (p.1, p.2.1) :=
    (hS.comp (x := (p.1, p.2.1)) analyticAt_fst).div analyticAt_snd hx
  have hAp : A p = ((p.1, p.2.1), g (p.1, p.2.1)) := by
    simp only [A, g, hp, mul_div_cancel_left₀ _ hx]
  have hB : AnalyticAt 𝕜 B ((p.1, p.2.1), g (p.1, p.2.1)) :=
    (analyticAt_fst.comp analyticAt_fst).prod
      ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)
  obtain ⟨H, hH, hGH⟩ := (hG.comp_of_eq hB (by rw [← hAp])).exists_eventuallyEq_sub_smul_of_graph
    hg h0
  have hA : AnalyticAt 𝕜 A p :=
    (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)).prod
      (analyticAt_snd.comp analyticAt_snd)
  refine ⟨fun q ↦ (q.2.1)⁻¹ • H (A q),
    ((analyticAt_fst.comp analyticAt_snd).inv hx).smul (hH.comp_of_eq hA hAp), ?_⟩
  have hAt : Tendsto A (𝓝 p) (𝓝 ((p.1, p.2.1), g (p.1, p.2.1))) := by
    simpa only [hAp] using hA.continuousAt.tendsto
  filter_upwards [hAt.eventually hGH,
    (continuous_fst.comp continuous_snd).continuousAt.eventually_ne hx] with q hq hqx
  simp only [Function.comp_apply, Prod.mk.eta, A, B, g] at hq hqx ⊢
  rw [hq, smul_smul]
  congr 1
  field_simp

/-- **Functions vanishing on `xy = S(b)` where `y ≠ 0`.** A function `G (b, x, y)` analytic at a
point `p` of the hypersurface `xy = S(b)` with `y ≠ 0`, for `S` analytic at the base point of `p`,
that vanishes near `p` on the hypersurface (written as the graph `x = S(b)/y`), is
`(xy - S(b)) • K` near `p` with `K` analytic at `p`. -/
theorem AnalyticAt.exists_eventuallyEq_mul_sub_smul_of_snd_ne_zero {G : E × 𝕜 × 𝕜 → F}
    {S : E → 𝕜} {p : E × 𝕜 × 𝕜} (hG : AnalyticAt 𝕜 G p) (hS : AnalyticAt 𝕜 S p.1)
    (hy : p.2.2 ≠ 0) (hp : S p.1 = p.2.1 * p.2.2)
    (h0 : ∀ᶠ w in 𝓝 (p.1, p.2.2), G (w.1, S w.1 / w.2, w.2) = 0) :
    ∃ K : E × 𝕜 × 𝕜 → F, AnalyticAt 𝕜 K p ∧
      ∀ᶠ q in 𝓝 p, G q = (q.2.1 * q.2.2 - S q.1) • K q := by
  -- Exchange the two branch coordinates.
  set τ : E × 𝕜 × 𝕜 → E × 𝕜 × 𝕜 := fun q ↦ (q.1, q.2.2, q.2.1)
  have hτ (q : E × 𝕜 × 𝕜) : AnalyticAt 𝕜 τ q :=
    analyticAt_fst.prod ((analyticAt_snd.comp analyticAt_snd).prod
      (analyticAt_fst.comp analyticAt_snd))
  obtain ⟨K, hK, hGK⟩ := (hG.comp (hτ (τ p))).exists_eventuallyEq_mul_sub_smul_of_fst_ne_zero
    (p := τ p) hS hy (by rw [hp, mul_comm]) h0
  refine ⟨K ∘ τ, hK.comp (hτ _), ?_⟩
  filter_upwards [(hτ p).continuousAt.tendsto.eventually hGK] with q hq
  simpa only [Function.comp_apply, τ, mul_comm q.2.2] using hq

/-- **Order in a distinguished variable**, lower bound: a function `G` analytic at `(x₀, y₀)`
vanishes to order at least `m` in `y` at `y₀` along every slice `x = const` near `x₀` if and only
if `G (x, y) = (y - y₀) ^ m • u (x, y)` near `(x₀, y₀)` for some `u` analytic at `(x₀, y₀)`. -/
theorem AnalyticAt.eventually_natCast_le_analyticOrderAt_iff {G : E × 𝕜 → F} {x₀ : E} {y₀ : 𝕜}
    (hG : AnalyticAt 𝕜 G (x₀, y₀)) {m : ℕ} :
    (∀ᶠ x in 𝓝 x₀, (m : ℕ∞) ≤ analyticOrderAt (fun y ↦ G (x, y)) y₀) ↔
      ∃ u : E × 𝕜 → F, AnalyticAt 𝕜 u (x₀, y₀) ∧
        ∀ᶠ p in 𝓝 (x₀, y₀), G p = (p.2 - y₀) ^ m • u p := by
  refine ⟨fun h ↦ ?_, fun ⟨u, hu, hGu⟩ ↦ ?_⟩
  · induction m generalizing G with
    | zero => exact ⟨G, hG, by simp⟩
    | succ m ih =>
      have h0 : ∀ᶠ x in 𝓝 x₀, G (x, y₀) = 0 := h.mono fun x hx ↦
        apply_eq_zero_of_analyticOrderAt_ne_zero (f := fun y ↦ G (x, y)) fun h0 ↦ by
          simp [h0] at hx
      obtain ⟨H, hH, hGH⟩ := hG.exists_eventuallyEq_sub_smul h0
      have hHm : ∀ᶠ x in 𝓝 x₀, (m : ℕ∞) ≤ analyticOrderAt (fun y ↦ H (x, y)) y₀ := by
        rw [nhds_prod_eq] at hGH
        filter_upwards [h, hGH.curry, hH.eventually_analyticAt_curry_right] with x hx hGHx hHx
        rw [analyticOrderAt_congr (g := (· - y₀) • fun y ↦ H (x, y)) hGHx,
          analyticOrderAt_smul (by fun_prop) hHx, analyticOrderAt_id_sub_const_self,
          Nat.cast_succ, add_comm 1] at hx
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 hx
      obtain ⟨u, hu, hHu⟩ := ih hH hHm
      refine ⟨u, hu, ?_⟩
      filter_upwards [hGH, hHu] with p hGp hHp
      rw [hGp, hHp, smul_smul, pow_succ']
  · rw [nhds_prod_eq] at hGu
    filter_upwards [hGu.curry, hG.eventually_analyticAt_curry_right,
      hu.eventually_analyticAt_curry_right] with x hGux hGx hux
    exact (natCast_le_analyticOrderAt hGx).2 ⟨_, hux, hGux⟩

/-- **Order in a distinguished variable** (McCallum–Parusiński–Paunescu, Lemma 4.4): a function
`G` analytic at `(x₀, y₀)` vanishes to order exactly `m` in `y` at `y₀` along every slice
`x = const` near `x₀` if and only if `G (x, y) = (y - y₀) ^ m • u (x, y)` near `(x₀, y₀)` for some
`u` analytic at `(x₀, y₀)` with `u (x₀, y₀) ≠ 0`. -/
theorem AnalyticAt.eventually_analyticOrderAt_eq_natCast_iff {G : E × 𝕜 → F} {x₀ : E} {y₀ : 𝕜}
    (hG : AnalyticAt 𝕜 G (x₀, y₀)) {m : ℕ} :
    (∀ᶠ x in 𝓝 x₀, analyticOrderAt (fun y ↦ G (x, y)) y₀ = m) ↔
      ∃ u : E × 𝕜 → F, AnalyticAt 𝕜 u (x₀, y₀) ∧ u (x₀, y₀) ≠ 0 ∧
        ∀ᶠ p in 𝓝 (x₀, y₀), G p = (p.2 - y₀) ^ m • u p := by
  refine ⟨fun h ↦ ?_, fun ⟨u, hu, hu0, hGu⟩ ↦ ?_⟩
  · obtain ⟨u, hu, hGu⟩ :=
      hG.eventually_natCast_le_analyticOrderAt_iff.1 (h.mono fun _ hx ↦ hx.ge)
    refine ⟨u, hu, fun hu0 ↦ ?_, hGu⟩
    -- at `x₀` the order of `G` is `m` plus the order of `u`, so `u` has order zero there
    have hux : AnalyticAt 𝕜 (fun y ↦ u (x₀, y)) y₀ := hu.curry_right
    have hGx₀ := h.self_of_nhds
    rw [nhds_prod_eq] at hGu
    rw [analyticOrderAt_congr (g := (· - y₀) ^ m • fun y ↦ u (x₀, y)) hGu.curry.self_of_nhds,
      analyticOrderAt_smul (by fun_prop) hux, analyticOrderAt_centeredMonomial] at hGx₀
    have h0 : analyticOrderAt (fun y ↦ u (x₀, y)) y₀ = 0 := by
      refine nonpos_iff_eq_zero.1 ((ENat.add_le_add_iff_left (ENat.natCast_ne_top m)).1 ?_)
      rw [add_zero, hGx₀]
    exact (hux.analyticOrderAt_eq_zero.1 h0) hu0
  · have hne : ∀ᶠ x in 𝓝 x₀, u (x, y₀) ≠ 0 :=
      ((continuous_id.prodMk continuous_const).tendsto x₀).eventually
        (hu.continuousAt.eventually_ne hu0)
    rw [nhds_prod_eq] at hGu
    filter_upwards [hGu.curry, hG.eventually_analyticAt_curry_right,
      hu.eventually_analyticAt_curry_right, hne] with x hGux hGx hux hnex
    exact hGx.analyticOrderAt_eq_natCast.2 ⟨_, hux, hnex, hGux⟩

/-- **Order in a distinguished variable on a product of balls.** A function `G` analytic at
`(x₀, y₀)` vanishes to order exactly `m` in `y` at `y₀` along every slice `x = const` near `x₀` if
and only if, on some product of balls around `(x₀, y₀)`, `G (x, y) = (y - y₀) ^ m • u (x, y)` with
`u` analytic and nowhere zero there. When `E` is `ι → 𝕜` with its sup norm, this product is a
polydisc. -/
theorem AnalyticAt.eventually_analyticOrderAt_eq_natCast_iff_exists_ball {G : E × 𝕜 → F}
    {x₀ : E} {y₀ : 𝕜} (hG : AnalyticAt 𝕜 G (x₀, y₀)) {m : ℕ} :
    (∀ᶠ x in 𝓝 x₀, analyticOrderAt (fun y ↦ G (x, y)) y₀ = m) ↔
      ∃ r > 0, ∃ u : E × 𝕜 → F, AnalyticOnNhd 𝕜 u (Metric.ball x₀ r ×ˢ Metric.ball y₀ r) ∧
        ∀ p ∈ Metric.ball x₀ r ×ˢ Metric.ball y₀ r, u p ≠ 0 ∧ G p = (p.2 - y₀) ^ m • u p := by
  rw [hG.eventually_analyticOrderAt_eq_natCast_iff]
  refine ⟨fun ⟨u, hu, hu0, hGu⟩ ↦ ?_, fun ⟨r, hr, u, hu, h⟩ ↦ ?_⟩
  · obtain ⟨r, hr, h⟩ := hu.exists_ball_prod_eq_pow_smul hu0 hGu
    exact ⟨r, hr, u, h⟩
  · have hc : (x₀, y₀) ∈ Metric.ball x₀ r ×ˢ Metric.ball y₀ r :=
      ⟨Metric.mem_ball_self hr, Metric.mem_ball_self hr⟩
    exact ⟨u, hu _ hc, (h _ hc).1, eventually_of_mem
      ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hc) fun p hp ↦ (h p hp).2⟩
