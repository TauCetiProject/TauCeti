/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.SimplexVolume.LatticePoints
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform counting bounds for weighted-index conditions

For a fixed positive threshold `t`, the number of exponent tuples in the box
`∀ j, Fin (d j + 1)` with `∑ j, I j / d j ≤ t` is at most
`(1 + ε) * simplexVolume m t * ∏ j, d j` once every partial degree is sufficiently large.
The threshold is uniform in the degree vector: no bound on the ratios between its entries is
needed.

For several prescribed indices, `exists_bound_sum_ncard_lt_prod` gives the resulting strict
coefficient budget. If `r * ∑ k, simplexVolume m (t k) < 1`, then, for all sufficiently large
partial degrees, `r` times the total number of strict weighted-index conditions is less than
`∏ j, (d j + 1)`, the number of coefficients. Here `r` can be the degree of the extension
containing the interpolation points. This separates the counting input for auxiliary
polynomials from the linear algebra and height estimates used to construct them.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press,
  2006, §6.3.3 and Lemma 6.3.4.
-/

public section

open Filter Finset
open scoped Topology

namespace TauCeti

/-- The lattice-point upper bound approaches its volume prediction uniformly as every
partial degree grows. The dimension and positive threshold are fixed, but the degrees may
grow at unrelated rates. -/
theorem exists_bound_ncard_le_simplexVolume_mul_prod {m : ℕ} {t ε : ℝ}
    (ht : 0 < t) (hε : 0 < ε) :
    ∃ D : ℕ, 0 < D ∧ ∀ d : Fin m → ℕ, (∀ j, D ≤ d j) →
      ({I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j ≤ t}.ncard : ℝ) ≤
        (1 + ε) * simplexVolume m t * ∏ j, (d j : ℝ) := by
  have hlim : Tendsto (fun n : ℕ ↦ (1 + max 1 t⁻¹ * ((m : ℝ) / n)) ^ m)
      atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)).const_mul (max 1 t⁻¹))).pow m
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually_lt_const (by linarith : 1 < 1 + ε))
  refine ⟨max N 1, by omega, fun d hd ↦ ?_⟩
  have hD : (0 : ℝ) < max N 1 := by exact_mod_cast (show 0 < max N 1 by omega)
  have hdpos (j) : 0 < d j := lt_of_lt_of_le (by omega : 0 < max N 1) (hd j)
  have hinv (j) : (d j : ℝ)⁻¹ ≤ ((max N 1 : ℕ) : ℝ)⁻¹ := by
    exact inv_anti₀ hD (by exact_mod_cast hd j)
  have hsum : ∑ j, (d j : ℝ)⁻¹ ≤ (m : ℝ) / max N 1 := by
    simpa [div_eq_mul_inv] using sum_le_sum (fun j (_ : j ∈ univ) ↦ hinv j)
  have hpow : (1 + max 1 t⁻¹ * ∑ j, (d j : ℝ)⁻¹) ^ m ≤ 1 + ε := by
    calc
      _ ≤ (1 + max 1 t⁻¹ * ((m : ℝ) / max N 1)) ^ m := by gcongr
      _ ≤ 1 + ε := (hN _ (le_max_left _ _)).le
  calc
    _ ≤ simplexVolume m t * (1 + max 1 t⁻¹ * ∑ j, (d j : ℝ)⁻¹) ^ m *
        ∏ j, (d j : ℝ) := ncard_le_simplexVolume_mul_pow_mul_prod d hdpos ht
    _ ≤ simplexVolume m t * (1 + ε) * ∏ j, (d j : ℝ) := by
      gcongr
      exact simplexVolume_nonneg m t
    _ = (1 + ε) * simplexVolume m t * ∏ j, (d j : ℝ) := by ring

/-- If the volume budget is strictly less than one, then the simultaneous strict
weighted-index conditions, each charged `r` times, use fewer equations than there are
coefficients in the box, uniformly for all sufficiently large partial degrees. -/
theorem exists_bound_sum_ncard_lt_prod {m : ℕ} {κ : Type*} [Fintype κ]
    (r : ℕ) (t : κ → ℝ) (ht : ∀ k, 0 < t k)
    (hbudget : (r : ℝ) * ∑ k, simplexVolume m (t k) < 1) :
    ∃ D : ℕ, 0 < D ∧ ∀ d : Fin m → ℕ, (∀ j, D ≤ d j) →
      r * ∑ k, {I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j < t k}.ncard <
        ∏ j, (d j + 1) := by
  classical
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr hbudget)
    ((r : ℝ) * ∑ k, simplexVolume m (t k))
  have hmargin : (r : ℝ) * ((1 + ε) * ∑ k, simplexVolume m (t k)) < 1 := by
    nlinarith
  choose D _ hD using fun k ↦
    exists_bound_ncard_le_simplexVolume_mul_prod (ht k) hε
  refine ⟨max 1 (univ.sup D), by omega, fun d hd ↦ ?_⟩
  have hdk (k) (j) : D k ≤ d j :=
    (le_sup (mem_univ k)).trans ((le_max_right _ _).trans (hd j))
  have hprod : ∏ j, (d j : ℝ) ≤ ∏ j, ((d j : ℝ) + 1) := by
    gcongr with j
    exact le_add_of_nonneg_right zero_le_one
  have hcount (k) :
      ({I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j < t k}.ncard : ℝ) ≤
        (1 + ε) * simplexVolume m (t k) * ∏ j, ((d j : ℝ) + 1) := by
    calc
      _ ≤ ({I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j ≤ t k}.ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard (show
          {I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j < t k} ⊆
          {I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j ≤ t k} from by
            intro I hI
            simp only [Set.mem_ofPred_eq] at hI ⊢
            exact hI.le)
      _ ≤ (1 + ε) * simplexVolume m (t k) * ∏ j, (d j : ℝ) := hD k d (hdk k)
      _ ≤ (1 + ε) * simplexVolume m (t k) * ∏ j, ((d j : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_left hprod
          (mul_nonneg (by positivity) (simplexVolume_nonneg m (t k)))
  have hsum := sum_le_sum (fun k (_ : k ∈ univ) ↦ hcount k)
  have hcoeff : 0 < ∏ j, ((d j : ℝ) + 1) := prod_pos fun _ _ ↦ by positivity
  have htotal : (r : ℝ) *
      ∑ k, ({I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j < t k}.ncard : ℝ) <
        ∏ j, ((d j : ℝ) + 1) := by
    calc
      _ ≤ (r : ℝ) * ∑ k, ((1 + ε) * simplexVolume m (t k) *
          ∏ j, ((d j : ℝ) + 1)) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg r)
      _ = ((r : ℝ) * ((1 + ε) * ∑ k, simplexVolume m (t k))) *
          ∏ j, ((d j : ℝ) + 1) := by rw [← sum_mul, ← mul_sum]; ring
      _ < ∏ j, ((d j : ℝ) + 1) := by simpa using mul_lt_mul_of_pos_right hmargin hcoeff
  exact_mod_cast htotal

/-- Two conditions per jet at index `1/4` still leave a nonzero coefficient budget in
one variable, for every sufficiently large degree. -/
example : ∃ D : ℕ, 0 < D ∧ ∀ d : Fin 1 → ℕ, (∀ j, D ≤ d j) →
    2 * {I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j < 1 / 4}.ncard <
      ∏ j, (d j + 1) := by
  simpa using exists_bound_sum_ncard_lt_prod (κ := Unit) (m := 1) 2 (fun _ ↦ 1 / 4)
    (by norm_num) (by norm_num [simplexVolume_one])

/-- Beyond the dimension, every exponent tuple is counted. Thus a volume budget equal to
one does not in general yield strictly fewer conditions than coefficients. -/
example {d : Fin 1 → ℕ} (hd : ∀ j, 0 < d j) :
    {I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j < 2}.ncard = ∏ j, (d j + 1) := by
  have hall : {I : ∀ j, Fin (d j + 1) | ∑ j, (I j : ℝ) / d j < 2} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro I
    simp only [Set.mem_ofPred_eq, Fin.sum_univ_one]
    have hI : (I 0 : ℝ) ≤ d 0 := by exact_mod_cast Nat.le_of_lt_succ (I 0).isLt
    exact ((div_le_one (by exact_mod_cast hd 0)).mpr hI).trans_lt (by norm_num)
  rw [hall, Set.ncard_univ]
  simp

end TauCeti
