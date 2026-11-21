/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.ConstantOrder.Basic
public import TauCeti.Analysis.Complex.Weierstrass
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Holomorphic functions vanishing on `xy = S(b)`

Let `S` be holomorphic near a point of a finite-dimensional complex normed space `E`. The
hypersurface `N_S = {(b, x, y) ∈ E × ℂ × ℂ | xy = S(b)}` is the local model for smoothing a node
over the base `E`. This file shows that `xy - S(b)` generates the ideal of holomorphic functions
vanishing on `N_S`, near every point: a function `G (b, x, y)`, holomorphic at `p`, which vanishes
at the points of `N_S` near `p` is `(xy - S(b)) * K` near `p` with `K` holomorphic at `p`
(`AnalyticAt.exists_eventuallyEq_mul_sub_mul`). No condition is imposed on `S`: it may vanish
identically, as for a permanent node, or to higher order, as in `xy = b²`; in both cases `N_S` is
singular at its points with `x = y = 0`.

Away from `x = y = 0` the hypersurface is a graph and this is Hadamard's lemma along the graph
(`AnalyticAt.exists_eventuallyEq_mul_sub_smul_of_fst_ne_zero`). At the node `(b, 0, 0)` the
coordinates `x = u + v`, `y = u - v` turn the equation into `u² = v² + S(b)`, a Weierstrass
polynomial of degree two in `u`. Weierstrass division (`AnalyticAt.exists_weierstrassDivision`)
writes `G` as a multiple of `u² - v² - S(b)` plus `A(b, v) + B(b, v) u`. Both square roots `±u` of
`v² + S(b)` give points of `N_S`, so `A = 0` and `B (b, v) u = 0`. Since `v² + S(b)` is not
identically zero, the identity theorem gives `B = 0`. This is the analytic Nullstellensatz for
`N_S`, proved directly for this hypersurface.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, for the local models `xy = a` of nodal families.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II,
  for Weierstrass division and the ideals of analytic hypersurfaces.
-/

public section

open Filter Metric Set Topology

namespace AnalyticAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An analytic function `B` on `E × ℂ` with `B (b, v) (v² + S(b)) = 0` near `(b₀, 0)`, where
`S(b₀) = 0`, vanishes near `(b₀, 0)`: the factor `v² + S(b)` does not vanish identically on any
ball about `(b₀, 0)`, so the identity theorem forces `B = 0` there. -/
private theorem eventually_eq_zero_of_mul_sq_add {B : E × ℂ → ℂ} {S : E → ℂ} {b₀ : E}
    (hB : AnalyticAt ℂ B (b₀, 0)) (hS : AnalyticAt ℂ S b₀) (hb₀ : S b₀ = 0)
    (hBR : ∀ᶠ w in 𝓝 (b₀, (0 : ℂ)), B w * (w.2 ^ 2 + S w.1) = 0) :
    ∀ᶠ w in 𝓝 (b₀, (0 : ℂ)), B w = 0 := by
  have hR : AnalyticAt ℂ (fun w : E × ℂ ↦ w.2 ^ 2 + S w.1) (b₀, 0) :=
    (analyticAt_snd.pow 2).add (hS.comp analyticAt_fst)
  obtain ⟨ε, hε, hball⟩ := eventually_nhds_iff_ball.1
    (hB.eventually_analyticAt.and (hR.eventually_analyticAt.and hBR))
  refine eventually_nhds_iff_ball.2 ⟨ε, hε, fun w₁ hw₁ ↦ ?_⟩
  by_contra hBw₁
  -- Near `w₁` the factor `B` is nonzero, so `v² + S(b)` vanishes near `w₁`, hence on the ball.
  have hR0 : (fun w : E × ℂ ↦ w.2 ^ 2 + S w.1) =ᶠ[𝓝 w₁] 0 := by
    filter_upwards [(hball w₁ hw₁).1.continuousAt.eventually_ne hBw₁,
      isOpen_ball.mem_nhds hw₁] with w hw hwU
    exact (mul_eq_zero.1 (hball w hwU).2.2).resolve_left hw
  have hEq := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (fun w hw ↦ (hball w hw).2.1) (convex_ball _ _).isPreconnected hw₁ hR0
  -- But at `(b₀, ε / 2)` the factor is `(ε / 2)²`.
  have hmem : (b₀, ((ε / 2 : ℝ) : ℂ)) ∈ ball (b₀, (0 : ℂ)) ε := by
    rw [mem_ball, Prod.dist_eq, dist_self, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε), max_eq_right (half_pos hε).le]
    exact half_lt_self hε
  have h := hEq hmem
  simp only [hb₀, add_zero, Pi.zero_apply, pow_eq_zero_iff two_ne_zero,
    Complex.ofReal_eq_zero] at h
  exact (half_pos hε).ne' h

/-- **The remainder vanishes.** Let `S` be analytic at `b₀` with `S(b₀) = 0`, and let `B` be
analytic at `(b₀, 0)`. If `A(b, v) + B(b, v) u = 0` at the points `((b, v), u)` near `((b₀, 0), 0)`
with `u² = v² + S(b)`, then `A` and `B` vanish near `(b₀, 0)`. Indeed every square root `u` of
`v² + S(b)` is small when `(b, v)` is close to `(b₀, 0)`, and the two roots `±u` give `A = 0` and
`B (v² + S(b)) = 0`. -/
private theorem eventually_eq_zero_of_add_mul_eq_zero {A B : E × ℂ → ℂ} {S : E → ℂ} {b₀ : E}
    (hB : AnalyticAt ℂ B (b₀, 0)) (hS : AnalyticAt ℂ S b₀) (hb₀ : S b₀ = 0)
    (h : ∀ᶠ z in 𝓝 ((b₀, (0 : ℂ)), (0 : ℂ)), z.2 ^ 2 = z.1.2 ^ 2 + S z.1.1 →
      A z.1 + B z.1 * z.2 = 0) :
    (∀ᶠ w in 𝓝 (b₀, (0 : ℂ)), A w = 0) ∧ ∀ᶠ w in 𝓝 (b₀, (0 : ℂ)), B w = 0 := by
  have hW : ∀ᶠ w in 𝓝 (b₀, (0 : ℂ)), ∀ u : ℂ, u ^ 2 = w.2 ^ 2 + S w.1 →
      A w + B w * u = 0 := by
    obtain ⟨ε, hε, hball⟩ := eventually_nhds_iff_ball.1 h
    have hR : ContinuousAt (fun w : E × ℂ ↦ w.2 ^ 2 + S w.1) (b₀, 0) :=
      (continuousAt_snd.pow 2).add (hS.continuousAt.comp_of_eq continuousAt_fst rfl)
    have hRε : ball (0 : ℂ) (ε ^ 2) ∈ 𝓝 ((0 : ℂ) ^ 2 + S b₀) := by
      rw [hb₀, zero_pow two_ne_zero, add_zero]
      exact ball_mem_nhds _ (pow_pos hε 2)
    filter_upwards [ball_mem_nhds (b₀, (0 : ℂ)) hε, hR.eventually_mem hRε] with w hw hwR u hu
    refine hball (w, u) ?_ hu
    rw [mem_ball_zero_iff, ← hu, norm_pow] at hwR
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right]
    exact ⟨hw, (pow_lt_pow_iff_left₀ (norm_nonneg u) hε.le two_ne_zero).1 hwR⟩
  have hA : ∀ᶠ w in 𝓝 (b₀, (0 : ℂ)), A w = 0 := by
    filter_upwards [hW] with w hw
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (w.2 ^ 2 + S w.1) two_pos
    linear_combination (hw u hu + hw (-u) (by rw [neg_sq, hu])) / 2
  refine ⟨hA, eventually_eq_zero_of_mul_sq_add hB hS hb₀ ?_⟩
  filter_upwards [hW, hA] with w hw hw0
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (w.2 ^ 2 + S w.1) two_pos
  have hBu := hw u hu
  rw [hw0, zero_add] at hBu
  rw [← hu]
  linear_combination u * hBu

variable [FiniteDimensional ℂ E]

/-- **Functions vanishing on `xy = S(b)` at the node.** A function `G (b, x, y)` analytic at
`(b₀, 0, 0)`, where `S` is analytic with `S(b₀) = 0`, which vanishes near `(b₀, 0, 0)` on the
hypersurface `xy = S(b)`, is `(xy - S(b)) * K` near `(b₀, 0, 0)` with `K` analytic there. -/
private theorem exists_eventuallyEq_mul_sub_mul_of_node {G : E × ℂ × ℂ → ℂ} {S : E → ℂ}
    {b₀ : E} (hG : AnalyticAt ℂ G (b₀, 0, 0)) (hS : AnalyticAt ℂ S b₀) (hb₀ : S b₀ = 0)
    (h0 : ∀ᶠ q in 𝓝 (b₀, (0 : ℂ), (0 : ℂ)), q.2.1 * q.2.2 = S q.1 → G q = 0) :
    ∃ K : E × ℂ × ℂ → ℂ, AnalyticAt ℂ K (b₀, 0, 0) ∧
      ∀ᶠ q in 𝓝 (b₀, (0 : ℂ), (0 : ℂ)), G q = (q.2.1 * q.2.2 - S q.1) * K q := by
  -- The coordinates `x = u + v`, `y = u - v`, written `((b, v), u)`, and their inverse.
  set ψ : (E × ℂ) × ℂ → E × ℂ × ℂ := fun z ↦ (z.1.1, z.2 + z.1.2, z.2 - z.1.2)
  set φ : E × ℂ × ℂ → (E × ℂ) × ℂ := fun q ↦ ((q.1, (q.2.1 - q.2.2) / 2), (q.2.1 + q.2.2) / 2)
  have hψ : AnalyticAt ℂ ψ ((b₀, 0), 0) :=
    (analyticAt_fst.comp analyticAt_fst).prod
      ((analyticAt_snd.add (analyticAt_snd.comp analyticAt_fst)).prod
        (analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst)))
  have hψ0 : ψ ((b₀, 0), 0) = (b₀, 0, 0) := by simp [ψ]
  have hφ : AnalyticAt ℂ φ (b₀, 0, 0) :=
    (analyticAt_fst.prod ((analyticAt_fst.comp analyticAt_snd).sub
      (analyticAt_snd.comp analyticAt_snd)).div_const).prod
      ((analyticAt_fst.comp analyticAt_snd).add (analyticAt_snd.comp analyticAt_snd)).div_const
  have hφ0 : φ (b₀, 0, 0) = ((b₀, 0), 0) := by simp [φ]
  have hφt : Tendsto φ (𝓝 (b₀, 0, 0)) (𝓝 ((b₀, 0), 0)) := by
    simpa only [hφ0] using hφ.continuousAt.tendsto
  -- Divide `G ∘ ψ` by the Weierstrass polynomial `u² - (v² + S(b))` of degree two in `u`.
  have hf : AnalyticAt ℂ (fun z : (E × ℂ) × ℂ ↦ z.2 ^ 2 - (z.1.2 ^ 2 + S z.1.1)) ((b₀, 0), 0) :=
    (analyticAt_snd.pow 2).sub (((analyticAt_snd.comp analyticAt_fst).pow 2).add
      (hS.comp_of_eq (analyticAt_fst.comp analyticAt_fst) rfl))
  have hd : analyticOrderAt (fun u ↦ u ^ 2 - ((b₀, (0 : ℂ)).2 ^ 2 + S (b₀, (0 : ℂ)).1)) 0 =
      (2 : ℕ) := by
    simp only [hb₀, zero_pow two_ne_zero, add_zero, sub_zero]
    have hsq : (fun u : ℂ ↦ u ^ 2) = (· - 0) ^ 2 := by
      funext u
      simp
    rw [hsq, analyticOrderAt_centeredMonomial]
  obtain ⟨Q, r, hQ, hr, hdiv⟩ := (hG.comp_of_eq hψ hψ0).exists_weierstrassDivision hf hd
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, sub_zero, pow_zero, mul_one,
    pow_one] at hdiv
  -- On `u² = v² + S(b)` the remainder `r₀(b, v) + r₁(b, v) u` vanishes, so `r₀ = r₁ = 0`.
  obtain ⟨hA, hB⟩ := eventually_eq_zero_of_add_mul_eq_zero (hr 1) hS hb₀ (by
    have hψt : Tendsto ψ (𝓝 ((b₀, 0), 0)) (𝓝 (b₀, 0, 0)) := by
      simpa only [hψ0] using hψ.continuousAt.tendsto
    filter_upwards [hψt.eventually h0, hdiv] with z hz hzd hzR
    have hG0 : G (ψ z) = 0 := hz (by simp only [ψ]; linear_combination hzR)
    simp only [Function.comp_apply, hG0, hzR, sub_self, zero_mul, zero_add] at hzd
    exact hzd.symm)
  -- Hence `G ∘ ψ = (u² - v² - S(b)) Q`; return to the coordinates `(b, x, y)`.
  have hφ1 : Tendsto (fun q ↦ (φ q).1) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
    (continuous_fst.tendsto _).comp hφt
  refine ⟨Q ∘ φ, hQ.comp_of_eq hφ hφ0, ?_⟩
  filter_upwards [hφt.eventually hdiv, hφ1.eventually hA, hφ1.eventually hB] with q hq hqA hqB
  have hψφ : ψ (φ q) = q := by
    ext <;> simp only [ψ, φ] <;> ring
  simp only [Function.comp_apply, hψφ, hqA, hqB, zero_mul, add_zero] at hq
  rw [hq]
  congr 1
  simp only [φ]
  ring

/-- **Functions vanishing on `xy = S(b)`.** Let `S` be analytic at the base point of
`p ∈ E × ℂ × ℂ`. A function `G (b, x, y)` analytic at `p` which vanishes at the points of the
hypersurface `xy = S(b)` near `p` is `(xy - S(b)) * K` near `p` with `K` analytic at `p`. This holds
at every point `p`, including the nodes `x = y = 0`, `S(b) = 0`, and for every `S`, including
`S = 0` and `S` vanishing to higher order. Off the hypersurface the hypothesis is vacuous near `p`
and `xy - S(b)` is invertible near `p`. -/
theorem exists_eventuallyEq_mul_sub_mul {G : E × ℂ × ℂ → ℂ} {S : E → ℂ} {p : E × ℂ × ℂ}
    (hG : AnalyticAt ℂ G p) (hS : AnalyticAt ℂ S p.1)
    (h0 : ∀ᶠ q in 𝓝 p, q.2.1 * q.2.2 = S q.1 → G q = 0) :
    ∃ K : E × ℂ × ℂ → ℂ, AnalyticAt ℂ K p ∧
      ∀ᶠ q in 𝓝 p, G q = (q.2.1 * q.2.2 - S q.1) * K q := by
  have hd : AnalyticAt ℂ (fun q : E × ℂ × ℂ ↦ q.2.1 * q.2.2 - S q.1) p :=
    ((analyticAt_fst.comp analyticAt_snd).mul (analyticAt_snd.comp analyticAt_snd)).sub
      (hS.comp analyticAt_fst)
  by_cases hp : S p.1 = p.2.1 * p.2.2
  · by_cases hx : p.2.1 = 0
    · by_cases hy : p.2.2 = 0
      · obtain ⟨b, x, y⟩ := p
        dsimp only at hx hy hp hS h0 hG ⊢
        subst hx hy
        exact exists_eventuallyEq_mul_sub_mul_of_node hG hS (by rw [hp, mul_zero]) h0
      · -- Where `y ≠ 0` the hypersurface is the graph `x = S(b) / y`.
        have hSc : ContinuousAt (fun w : E × ℂ ↦ S w.1) (p.1, p.2.2) :=
          hS.continuousAt.comp_of_eq continuousAt_fst rfl
        have hσ : ContinuousAt (fun w : E × ℂ ↦ (w.1, S w.1 / w.2, w.2)) (p.1, p.2.2) :=
          continuousAt_fst.prodMk ((hSc.div continuousAt_snd hy).prodMk continuousAt_snd)
        have hσp : (p.1, S p.1 / p.2.2, p.2.2) = p := by
          rw [hp, mul_div_cancel_right₀ _ hy]
        rw [← hσp] at h0
        simpa only [smul_eq_mul] using hG.exists_eventuallyEq_mul_sub_smul_of_snd_ne_zero hS hy hp
          (by filter_upwards [hσ.eventually h0, continuousAt_snd.eventually_ne hy] with w hw hw0
              exact hw (div_mul_cancel₀ _ hw0))
    · -- Where `x ≠ 0` the hypersurface is the graph `y = S(b) / x`.
      have hSc : ContinuousAt (fun w : E × ℂ ↦ S w.1) (p.1, p.2.1) :=
        hS.continuousAt.comp_of_eq continuousAt_fst rfl
      have hσ : ContinuousAt (fun w : E × ℂ ↦ (w.1, w.2, S w.1 / w.2)) (p.1, p.2.1) :=
        continuousAt_fst.prodMk (continuousAt_snd.prodMk (hSc.div continuousAt_snd hx))
      have hσp : (p.1, p.2.1, S p.1 / p.2.1) = p := by
        rw [hp, mul_div_cancel_left₀ _ hx]
      rw [← hσp] at h0
      simpa only [smul_eq_mul] using hG.exists_eventuallyEq_mul_sub_smul_of_fst_ne_zero hS hx hp
        (by filter_upwards [hσ.eventually h0, continuousAt_snd.eventually_ne hx] with w hw hw0
            exact hw (mul_div_cancel₀ _ hw0))
  · -- Off the hypersurface `xy - S(b)` is invertible near `p`.
    have hd0 : p.2.1 * p.2.2 - S p.1 ≠ 0 := sub_ne_zero.2 (Ne.symm hp)
    refine ⟨fun q ↦ G q / (q.2.1 * q.2.2 - S q.1), hG.div hd hd0, ?_⟩
    filter_upwards [hd.continuousAt.eventually_ne hd0] with q hq
    rw [mul_div_cancel₀ _ hq]

end AnalyticAt
