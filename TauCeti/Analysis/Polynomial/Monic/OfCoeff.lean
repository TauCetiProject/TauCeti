/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
public import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Root bounds in monic coefficient coordinates

A root of `TauCeti.Polynomial.monicOfCoeff c` has norm strictly less than
`‖c‖ + 1`. Thus locally bounded coefficient tuples give locally bounded roots,
without choosing or continuously labelling them. This is the bound used to remove
singularities of analytic root branches. When all lower coefficients are small,
the roots are correspondingly small (`norm_lt_of_isRoot_monicOfCoeff_of_norm_le`),
so a continuous family of monic polynomials whose lower coefficients vanish at `x₀`
eventually has all its roots inside any prescribed ball around `0`
(`eventually_norm_lt_of_isRoot_monicOfCoeff`).

The coarse estimate specializes Mathlib's `Polynomial.IsRoot.norm_lt_cauchyBound`
(Daniel Weber's formalization of Cauchy's root bound) to the finite coefficient tuple.
-/

public section

open Filter Polynomial Topology

namespace TauCeti.Polynomial

/-- Every root of the monic polynomial with lower coefficients `c` has norm
strictly less than `‖c‖ + 1`. -/
theorem norm_lt_of_isRoot_monicOfCoeff {K : Type*} [NormedField K] {d : ℕ}
    (c : Fin d → K) {z : K} (hz : (monicOfCoeff c).IsRoot z) : ‖z‖ < ‖c‖ + 1 := by
  have hsup : (Finset.range d).sup (fun i => ‖(monicOfCoeff c).coeff i‖₊) ≤ ‖c‖₊ := by
    refine Finset.sup_le fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [coeff_monicOfCoeff c ⟨i, hi⟩]
    exact nnNorm_le_pi_nnNorm c ⟨i, hi⟩
  have hb : (monicOfCoeff c).cauchyBound ≤ ‖c‖₊ + 1 := by
    rw [cauchyBound, (monic_monicOfCoeff c).leadingCoeff, nnNorm_one, div_one,
      natDegree_monicOfCoeff]
    exact add_le_add hsup le_rfl
  exact_mod_cast (hz.norm_lt_cauchyBound (monic_monicOfCoeff c).ne_zero).trans_le hb

/-- If each lower coefficient `c i` of `TauCeti.Polynomial.monicOfCoeff c` is bounded in norm by
`R ^ (d - i) / (d + 1)` for `R > 0`, then every root of `monicOfCoeff c` has norm strictly less
than `R`. -/
theorem norm_lt_of_isRoot_monicOfCoeff_of_norm_le {K : Type*} [NormedField K] {d : ℕ}
    {c : Fin d → K} {R : ℝ} (hR : 0 < R)
    (hc : ∀ i : Fin d, ‖c i‖ ≤ R ^ (d - (i : ℕ)) / (d + 1))
    {z : K} (hz : (monicOfCoeff c).IsRoot z) : ‖z‖ < R := by
  by_contra! hzR
  have hz0 : 0 < ‖z‖ := hR.trans_le hzR
  have heq : z ^ d = -∑ i : Fin d, c i * z ^ (i : ℕ) :=
    eq_neg_of_add_eq_zero_left (by simpa only [IsRoot.def, eval_monicOfCoeff] using hz)
  have hle : ‖z‖ ^ d ≤ d * (‖z‖ ^ d / (d + 1)) := by
    calc ‖z‖ ^ d
        = ‖z ^ d‖ := (norm_pow z d).symm
      _ = ‖∑ i : Fin d, c i * z ^ (i : ℕ)‖ := by rw [heq, norm_neg]
      _ ≤ ∑ i : Fin d, ‖c i * z ^ (i : ℕ)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin d, ‖z‖ ^ d / (d + 1) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [norm_mul, norm_pow]
          calc ‖c i‖ * ‖z‖ ^ (i : ℕ)
              ≤ R ^ (d - (i : ℕ)) / (d + 1) * ‖z‖ ^ (i : ℕ) :=
                mul_le_mul_of_nonneg_right (hc i) (pow_nonneg (norm_nonneg z) _)
            _ ≤ ‖z‖ ^ (d - (i : ℕ)) / (d + 1) * ‖z‖ ^ (i : ℕ) := by gcongr
            _ = ‖z‖ ^ (d - (i : ℕ) + (i : ℕ)) / (d + 1) := by rw [div_mul_eq_mul_div, ← pow_add]
            _ = ‖z‖ ^ d / (d + 1) := by rw [Nat.sub_add_cancel i.is_lt.le]
      _ = d * (‖z‖ ^ d / (d + 1)) := by simp
  have hpos : 0 < ‖z‖ ^ d / (d + 1 : ℝ) := div_pos (pow_pos hz0 d) (by positivity)
  have hlt : (d : ℝ) * (‖z‖ ^ d / (d + 1)) < ‖z‖ ^ d := by
    calc (d : ℝ) * (‖z‖ ^ d / (d + 1))
        < (d + 1 : ℝ) * (‖z‖ ^ d / (d + 1)) := by linarith
      _ = ‖z‖ ^ d := mul_div_cancel₀ _ (by positivity)
  exact hlt.not_ge hle

/-- If the lower coefficients `c i` are continuous at `x₀` and vanish at `x₀`, then for every
`R > 0`, all roots of `TauCeti.Polynomial.monicOfCoeff (fun i ↦ c i x)` eventually have norm
strictly less than `R` for `x` near `x₀`. -/
theorem eventually_norm_lt_of_isRoot_monicOfCoeff {K X : Type*} [NormedField K]
    [TopologicalSpace X] {d : ℕ} {c : Fin d → X → K} {x₀ : X}
    (hc : ∀ i, ContinuousAt (c i) x₀) (hc0 : ∀ i, c i x₀ = 0) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ x in 𝓝 x₀, ∀ z : K, (monicOfCoeff fun i ↦ c i x).IsRoot z → ‖z‖ < R := by
  have hbound (i : Fin d) : ∀ᶠ x in 𝓝 x₀, ‖c i x‖ ≤ R ^ (d - (i : ℕ)) / (d + 1) := by
    have hpos : 0 < R ^ (d - (i : ℕ)) / (d + 1 : ℝ) := by positivity
    simpa only [hc0 i, Metric.mem_closedBall, dist_zero_right] using
      (hc i).eventually (Metric.closedBall_mem_nhds (c i x₀) hpos)
  filter_upwards [Filter.eventually_all.2 hbound] with x hx z hz
  exact norm_lt_of_isRoot_monicOfCoeff_of_norm_le hR hx hz

/-- Evaluating a monic coefficient family at a continuous function is continuous. -/
@[fun_prop]
theorem continuousOn_eval_monicOfCoeff {R B : Type*} [CommSemiring R]
    [TopologicalSpace R] [IsTopologicalSemiring R] [TopologicalSpace B] {d : ℕ}
    (c : B → Fin d → R) {r : B → R} {t : Set B}
    (hc : ContinuousOn c t) (hr : ContinuousOn r t) :
    ContinuousOn (fun x => (monicOfCoeff (c x)).eval (r x)) t := by
  simp_rw [eval_monicOfCoeff]
  exact (hr.pow d).add (continuousOn_finsetSum _ fun i _ =>
    (continuousOn_pi.1 hc i).mul (hr.pow i.val))

end TauCeti.Polynomial
