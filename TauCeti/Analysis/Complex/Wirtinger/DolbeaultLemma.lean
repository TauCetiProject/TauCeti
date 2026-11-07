/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IsLUB
import TauCeti.Analysis.Complex.PowerSeries.Approximation
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Complex.Wirtinger.Potential

/-!
# The Dolbeault lemma on discs

Let `D ⊆ ℂ` be an open disc of radius `R ≤ ∞` and let `f : ℂ → W` be `Cⁿ` on `D`, for `n ≥ 1`, with
values in a complex Banach space. Then the inhomogeneous Cauchy–Riemann equation `\bar∂ g = f` has
a `Cⁿ` solution `g` on all of `D`. Here `\bar∂ g` is the conjugate Wirtinger derivative
`TauCeti.conjWirtingerDeriv g z 1 = (∂ₓ g + i ∂ᵧ g) / 2`.

For compactly supported `f` the Cauchy transform solves the equation on the whole plane
(`TauCeti.exists_contDiff_conjWirtingerDeriv_apply_one_eq_of_hasCompactSupport`); cutting `f` off
gives a solution `h k` on each disc of an exhaustion of `D` by concentric discs `B k`
(`TauCeti.exists_contDiff_conjWirtingerDeriv_apply_one_eq_on_closedBall`). These local solutions
do not converge, but consecutive ones differ by a function `h (k + 1) - h k` that is holomorphic
on a neighbourhood of the closure of `B k`. An entire function `P k`, a partial sum of the Taylor
series of that difference, approximates it within `2⁻ᵏ` on `B k`
(`DifferentiableOn.exists_differentiable_norm_sub_lt`). The corrected solutions
`h k - ∑_{j < k} P j` then converge locally uniformly on `D`: on `B m` the limit is `h m` plus a
locally uniform limit of holomorphic functions, so it is `Cⁿ` and has the same `\bar∂` as `h m`,
namely `f`.

This is the local `\bar∂`-lemma behind the vanishing of `H¹(D, 𝒪)` on discs, which makes discs
acyclic for the structure sheaf of a Riemann surface.

## Main results

* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball`: the Dolbeault lemma on a
  disc `Metric.eball c R`, `R ≤ ∞`.
* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_ball`: the same for a disc of
  real radius.
* `TauCeti.exists_contDiff_conjWirtingerDeriv_apply_one_eq`: every `Cⁿ` function on the plane is
  `\bar∂` of a `Cⁿ` function, without any support condition.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Lemma 13.1 and Theorem 13.2 (Dolbeault's lemma).
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.4.4.
-/

public section

open Complex Filter Metric Set Topology
open scoped NNReal ENNReal

namespace TauCeti

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {n : ℕ∞}

/-- Gluing step: if near each point of `U` the function `G` is a global `Cⁿ` function with
`\bar∂ = f` there plus a holomorphic function, then `G` is `Cⁿ` on `U` with `\bar∂ G = f`. -/
private theorem contDiffOn_and_conjWirtingerDeriv_eq_of_locally_eq_add {G f : ℂ → W}
    {U : Set ℂ} (hn : 1 ≤ n)
    (hG : ∀ z ∈ U, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ ∃ a K : ℂ → W, ContDiff ℝ n a ∧
      (∀ w ∈ V, conjWirtingerDeriv a w 1 = f w) ∧ DifferentiableOn ℂ K V ∧ EqOn G (a + K) V) :
    ContDiffOn ℝ n G U ∧ ∀ z ∈ U, conjWirtingerDeriv G z 1 = f z := by
  refine ⟨contDiffOn_of_locally_contDiffOn fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨V, hV, hzV, a, K, ha, -, hK, hGK⟩ := hG z hz
    exact ⟨V, hV, hzV, ((ha.contDiffOn.add ((hK.contDiffOn hV).restrict_scalars ℝ)).congr
      hGK).mono inter_subset_right⟩
  · obtain ⟨V, hV, hzV, a, K, ha, haf, hK, hGK⟩ := hG z hz
    have hKz := hK.differentiableAt (hV.mem_nhds hzV)
    have haz : DifferentiableAt ℝ a z :=
      ha.differentiable (by exact_mod_cast (zero_lt_one.trans_le hn).ne') z
    rw [(hGK.eventuallyEq_of_mem (hV.mem_nhds hzV)).conjWirtingerDeriv_eq,
      conjWirtingerDeriv_add haz (hKz.restrictScalars ℝ), hKz.conjWirtingerDeriv_eq_zero,
      add_zero, haf z hzV]

/-- **The Dolbeault lemma on a disc.** Let `f` be `Cⁿ`, `n ≥ 1`, on the open disc `eball c R`
of radius `R ≤ ∞`. Then there is a function `g`, `Cⁿ` on the disc, with `\bar∂ g = f` on the
disc. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball {f : ℂ → W} {c : ℂ}
    {R : ℝ≥0∞} (hn : 1 ≤ n) (hf : ContDiffOn ℝ n f (eball c R)) :
    ∃ g : ℂ → W, ContDiffOn ℝ n g (eball c R) ∧
      ∀ z ∈ eball c R, conjWirtingerDeriv g z 1 = f z := by
  rcases eq_zero_or_pos R with rfl | hR
  · exact ⟨0, by simp, by simp⟩
  -- An exhaustion of the disc by the discs `ball c (r k)`.
  obtain ⟨u, hu_mono, hu_mem, hu_lim⟩ := exists_seq_strictMono_tendsto' hR
  have hu_top (k : ℕ) : u k ≠ ⊤ := ((hu_mem k).2.trans_le le_top).ne
  set r : ℕ → ℝ := fun k ↦ (u k).toReal
  have hr_mono : StrictMono r := fun i j hij ↦
    (ENNReal.toReal_lt_toReal (hu_top i) (hu_top j)).2 (hu_mono hij)
  have hr_pos (k : ℕ) : 0 < r k := ENNReal.toReal_pos (hu_mem k).1.ne' (hu_top k)
  have hball (k : ℕ) : ball c (r k) = eball c (u k) := by
    rw [← eball_ofReal, ENNReal.ofReal_toReal (hu_top k)]
  -- Intermediate radii `r k < s k < r (k + 1)`.
  set s : ℕ → ℝ := fun k ↦ (r k + r (k + 1)) / 2
  have hrs (k : ℕ) : r k < s k := by have := hr_mono k.lt_succ_self; simp only [s]; linarith
  have hsr (k : ℕ) : s k < r (k + 1) := by
    have := hr_mono k.lt_succ_self; simp only [s]; linarith
  have hs_mono : StrictMono s := strictMono_nat_of_lt_succ fun k ↦ (hsr k).trans (hrs (k + 1))
  -- Local solutions `h k`, with `\bar∂ (h k) = f` on `closedBall c (s k)`.
  have hloc (k : ℕ) : ∃ h : ℂ → W, ContDiff ℝ n h ∧
      ∀ z ∈ closedBall c (s k), conjWirtingerDeriv h z 1 = f z :=
    exists_contDiff_conjWirtingerDeriv_apply_one_eq_on_closedBall hn
      (hf.mono ((hball (k + 1)).trans_subset (eball_subset_eball (hu_mem (k + 1)).2.le)))
      ((hr_pos k).trans (hrs k)) (hsr k)
  choose h hh hh_eq using hloc
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hn).ne'
  have hd (k : ℕ) : Differentiable ℝ (h k) := (hh k).differentiable hn0
  -- Consecutive local solutions differ by a holomorphic function.
  have hdiff (k : ℕ) : DifferentiableOn ℂ (h (k + 1) - h k) (ball c (s k)) := fun z hz ↦ by
    refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero
      ((hd (k + 1)).sub (hd k) z)).2 ?_).differentiableWithinAt
    rw [conjWirtingerDeriv_sub (hd (k + 1) z) (hd k z), sub_apply,
      hh_eq (k + 1) z (ball_subset_closedBall (ball_subset_ball (hs_mono k.lt_succ_self).le hz)),
      hh_eq k z (ball_subset_closedBall hz), sub_self]
  -- Taylor corrections `P k`, approximating the differences within `2⁻ᵏ`.
  have happrox (k : ℕ) : ∃ P : ℂ → W, Differentiable ℂ P ∧
      ∀ z ∈ closedBall c (r k), ‖(h (k + 1) - h k) z - P z‖ < (1 / 2 : ℝ) ^ k :=
    (hdiff k).exists_differentiable_norm_sub_lt (hrs k) (by positivity)
  choose P hP hP_lt using happrox
  set e : ℕ → ℂ → W := fun k ↦ h (k + 1) - h k - P k
  have he_le {m k : ℕ} (hmk : m ≤ k) {z : ℂ} (hz : z ∈ ball c (r m)) :
      ‖e k z‖ ≤ (1 / 2 : ℝ) ^ k :=
    (hP_lt k z (closedBall_subset_closedBall (hr_mono.monotone hmk)
      (ball_subset_closedBall hz))).le
  have hsumm (m : ℕ) : Summable fun k ↦ (1 / 2 : ℝ) ^ (k + m) :=
    (summable_nat_add_iff m).2 summable_geometric_two
  -- On `ball c (r m)`, the limit is `h m` plus a holomorphic function.
  set G : ℂ → W := fun z ↦ h 0 z + ∑' k, e k z
  have hkey (m : ℕ) : ∃ K : ℂ → W, DifferentiableOn ℂ K (ball c (r m)) ∧
      EqOn G (h m + K) (ball c (r m)) := by
    refine ⟨fun z ↦ ∑' k, e (k + m) z - ∑ k ∈ Finset.range m, P k z, ?_, fun z hz ↦ ?_⟩
    · refine DifferentiableOn.sub ?_ (DifferentiableOn.fun_sum fun k _ ↦ (hP k).differentiableOn)
      refine differentiableOn_tsum_of_summable_norm (hsumm m) (fun k ↦ ?_) isOpen_ball
        fun k z hz ↦ he_le (Nat.le_add_left m k) hz
      exact ((hdiff (k + m)).sub (hP (k + m)).differentiableOn).mono (ball_subset_ball
        ((hr_mono.monotone (Nat.le_add_left m k)).trans (hrs (k + m)).le))
    · have hs : Summable fun k ↦ e k z := (summable_nat_add_iff m).1 <|
        .of_norm_bounded (hsumm m) fun k ↦ he_le (Nat.le_add_left m k) hz
      have htel : ∑ k ∈ Finset.range m, e k z = h m z - h 0 z - ∑ k ∈ Finset.range m, P k z := by
        simp only [e, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_range_sub fun k ↦ h k z]
      simp only [G, Pi.add_apply, ← hs.sum_add_tsum_nat_add m, htel]
      abel
  -- Every point of the disc lies in some `ball c (r m)`, where `\bar∂ (h m) = f`.
  refine ⟨G, contDiffOn_and_conjWirtingerDeriv_eq_of_locally_eq_add hn fun z hz ↦ ?_⟩
  obtain ⟨m, hm⟩ := (hu_lim.eventually (lt_mem_nhds hz)).exists
  obtain ⟨K, hK, hGK⟩ := hkey m
  exact ⟨ball c (r m), isOpen_ball, (hball m).symm ▸ hm, h m, K, hh m,
    fun w hw ↦ hh_eq m w (ball_subset_closedBall (ball_subset_ball (hrs m).le hw)), hK, hGK⟩

/-- **The Dolbeault lemma on a disc of real radius.** If `f` is `Cⁿ`, `n ≥ 1`, on `ball c R`,
there is a function `g`, `Cⁿ` on `ball c R`, with `\bar∂ g = f` there. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_ball {f : ℂ → W} {c : ℂ} {R : ℝ}
    (hn : 1 ≤ n) (hf : ContDiffOn ℝ n f (ball c R)) :
    ∃ g : ℂ → W, ContDiffOn ℝ n g (ball c R) ∧
      ∀ z ∈ ball c R, conjWirtingerDeriv g z 1 = f z := by
  rw [← eball_ofReal] at hf ⊢
  exact exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball hn hf

/-- **The Dolbeault lemma on the plane.** Every `Cⁿ` function `f : ℂ → W`, `n ≥ 1`, is `\bar∂ g`
for a `Cⁿ` function `g`; no support condition on `f` is needed. -/
theorem exists_contDiff_conjWirtingerDeriv_apply_one_eq {f : ℂ → W} (hn : 1 ≤ n)
    (hf : ContDiff ℝ n f) :
    ∃ g : ℂ → W, ContDiff ℝ n g ∧ ∀ z, conjWirtingerDeriv g z 1 = f z := by
  obtain ⟨g, hg, hgf⟩ := exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball
    (c := 0) (R := ⊤) hn (by simpa using hf.contDiffOn)
  exact ⟨g, contDiffOn_univ.1 (by simpa using hg), fun z ↦ hgf z (by simp)⟩

end TauCeti
