/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Calculus.IteratedFDeriv.Flat

/-!
# Cut-offs of flat functions are small in `C^r`

Let `u` be a `C^{r+1}` function whose derivatives of order at most `r` vanish at a point `y`, and
let `χ` be a `C^r` function supported in the closed unit ball. The localizations
`z ↦ χ (ε⁻¹ • (z - y)) • u z` of `u` to the balls `closedBall y ε` are small in `C^r`: their
derivatives of order at most `r` are bounded by `C * ε` for `0 < ε ≤ 1`
(`TauCeti.exists_norm_iteratedFDeriv_smul_le_mul`). The rescaled cut-off is supported in
`closedBall y ε` (`TauCeti.tsupport_comp_inv_smul_sub_subset_closedBall`, from the rescaling
`TauCeti.inv_smul_sub_mem_closedBall_zero_iff`) and each of its derivatives of order `l` costs
`ε⁻ˡ`, while on `closedBall y ε` the derivative of order `j ≤ r` of `u` is `O(ε ^ (r + 1 - j))`;
the Leibniz rule balances these.

This is the estimate behind Peetre's theorem on local operators: an operator that sees only the
`C^r` size of its input near a point cannot see a function that is flat to order `r` there.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §19.
-/

public section

open Set Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace TauCeti

/-- For `0 < ε`, the rescaled point `ε⁻¹ • (z - y)` lies in `closedBall 0 R` exactly when `z` lies
in `closedBall y (ε * R)`. -/
theorem inv_smul_sub_mem_closedBall_zero_iff {ε : ℝ} (hε : 0 < ε) {R : ℝ} {y z : E} :
    ε⁻¹ • (z - y) ∈ closedBall (0 : E) R ↔ z ∈ closedBall y (ε * R) := by
  simp [norm_smul, abs_of_pos hε, dist_eq_norm, inv_mul_le_iff₀ hε]

/-- Rescaling a function supported in the closed unit ball to `z ↦ χ (ε⁻¹ • (z - y))` gives a
function supported in `closedBall y ε`. -/
theorem tsupport_comp_inv_smul_sub_subset_closedBall {α : Type*} [Zero α] {χ : E → α}
    (hχs : tsupport χ ⊆ closedBall 0 1) {ε : ℝ} (hε : 0 < ε) (y : E) :
    tsupport (fun z ↦ χ (ε⁻¹ • (z - y))) ⊆ closedBall y ε := by
  intro z hz
  have h := hχs (tsupport_comp_subset_preimage χ (f := fun z ↦ ε⁻¹ • (z - y)) (by fun_prop) hz)
  rwa [inv_smul_sub_mem_closedBall_zero_iff hε, mul_one] at h

/-- Cut-offs of a function that is flat to order `r` at `y` are small in `C^r`: if the derivatives
of the `C^{r+1}` function `u` of order at most `r` vanish at `y` and `χ` is a `C^r` function
supported in the closed unit ball, then the derivatives of order at most `r` of
`z ↦ χ (ε⁻¹ • (z - y)) • u z` are bounded by `C * ε` for `0 < ε ≤ 1`. -/
theorem exists_norm_iteratedFDeriv_smul_le_mul [FiniteDimensional ℝ E] {χ : E → ℝ} {r : ℕ}
    (hχ : ContDiff ℝ r χ) (hχs : tsupport χ ⊆ closedBall 0 1) {u : E → F}
    (hu : ContDiff ℝ (r + 1 : ℕ) u) {y : E} (hflat : ∀ i ≤ r, iteratedFDeriv ℝ i u y = 0) :
    ∃ C, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ i ≤ r, ∀ z,
      ‖iteratedFDeriv ℝ i (fun z ↦ χ (ε⁻¹ • (z - y)) • u z) z‖ ≤ C * ε := by
  -- A bound `M` for `D^{r+1} u` near `y` gives `‖D^j u z‖ ≤ M * ‖z - y‖ ^ (r + 1 - j)`.
  obtain ⟨M, hM⟩ := (isCompact_closedBall y 1).exists_bound_of_continuousOn
    (hu.continuous_iteratedFDeriv le_rfl).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y (mem_closedBall_self zero_le_one))
  have htaylor : ∀ j ≤ r, ∀ z ∈ closedBall y 1,
      ‖iteratedFDeriv ℝ j u z‖ ≤ M * ‖z - y‖ ^ (r + 1 - j) := by
    intro j hj z hz
    have h := norm_iteratedFDeriv_sub_le_of_iteratedFDeriv_eq_zero (k := r)
      (fun w _ ↦ hu.contDiffAt) (convex_closedBall y 1) (mem_closedBall_self zero_le_one) hM
      (fun i _ hi ↦ hflat i hi) (r - j) (Nat.sub_le r j) z hz
    rwa [Nat.sub_sub_self hj, hflat j hj, sub_zero, show r - j + 1 = r + 1 - j by omega] at h
  -- A common bound `c'` for the derivatives of `χ` of order at most `r`.
  have hχc : HasCompactSupport χ :=
    (isCompact_closedBall 0 1).of_isClosed_subset (isClosed_tsupport χ) hχs
  choose! c hc using fun l (hl : l ≤ r) ↦
    (hχ.continuous_iteratedFDeriv (by exact_mod_cast hl)).bounded_above_of_compact_support
      (hχc.iteratedFDeriv l)
  set c' := ∑ l ∈ Finset.range (r + 1), c l
  have hc0 : ∀ l ∈ Finset.range (r + 1), 0 ≤ c l := fun l hl ↦
    (norm_nonneg _).trans (hc l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)) 0)
  have hc' : ∀ l ≤ r, c l ≤ c' := fun l hl ↦
    Finset.single_le_sum hc0 (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
  have hc'0 : 0 ≤ c' := Finset.sum_nonneg hc0
  refine ⟨2 ^ r * c' * M, fun ε hε hε1 i hi z ↦ ?_⟩
  by_cases hz : z ∈ closedBall y ε
  swap
  · -- Away from `closedBall y ε` the function vanishes identically near `z`.
    have hsupp : z ∉ tsupport fun z ↦ χ (ε⁻¹ • (z - y)) • u z := fun hz' ↦
      hz (tsupport_comp_inv_smul_sub_subset_closedBall hχs hε y
        (tsupport_smul_subset_left _ u hz'))
    rw [Function.notMem_support.mp fun h ↦ hsupp (support_iteratedFDeriv_subset i h), norm_zero]
    positivity
  have hzy : ‖z - y‖ ≤ ε := by rwa [mem_closedBall, dist_eq_norm] at hz
  have hz1 : z ∈ closedBall y 1 := closedBall_subset_closedBall hε1 hz
  have hχε : ContDiff ℝ r fun z ↦ χ (ε⁻¹ • (z - y)) := hχ.comp (by fun_prop)
  refine (norm_iteratedFDeriv_smul_le hχε (hu.of_le (by norm_cast; omega)) z
    (by exact_mod_cast hi)).trans ?_
  -- Each Leibniz term is at most `(i choose l) * c' * M * ε`.
  have hterm : ∀ l ∈ Finset.range (i + 1),
      (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun z ↦ χ (ε⁻¹ • (z - y))) z‖ *
        ‖iteratedFDeriv ℝ (i - l) u z‖ ≤ (i.choose l : ℝ) * (c' * M * ε) := by
    intro l hl
    have hli : l ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rw [iteratedFDeriv_comp_sub (f := fun w ↦ χ (ε⁻¹ • w)) l y z,
      iteratedFDeriv_comp_const_smul ε⁻¹ (hχ.of_le (by exact_mod_cast hli.trans hi)), norm_smul,
      norm_pow, norm_inv, Real.norm_of_nonneg hε.le, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc (ε⁻¹ ^ l * ‖iteratedFDeriv ℝ l χ (ε⁻¹ • (z - y))‖) * ‖iteratedFDeriv ℝ (i - l) u z‖
        ≤ (ε⁻¹ ^ l * c') * (M * ε ^ (r + 1 - (i - l))) := by
          gcongr
          · exact (hc l (hli.trans hi) _).trans (hc' l (hli.trans hi))
          · exact (htaylor (i - l) ((Nat.sub_le i l).trans hi) z hz1).trans (by gcongr)
      _ = c' * M * (ε ^ (r - i) * ε) := by
          rw [show r + 1 - (i - l) = (r - i) + 1 + l by omega, pow_add, pow_add, pow_one,
            inv_pow]
          field_simp
      _ ≤ c' * M * ε := by
          gcongr
          exact mul_le_of_le_one_left hε.le (pow_le_one₀ hε.le hε1)
  calc ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) *
        ‖iteratedFDeriv ℝ l (fun z ↦ χ (ε⁻¹ • (z - y))) z‖ * ‖iteratedFDeriv ℝ (i - l) u z‖
      ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * (c' * M * ε) := Finset.sum_le_sum hterm
    _ = 2 ^ i * (c' * M * ε) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ 2 ^ r * c' * M * ε := by
        rw [mul_assoc, mul_assoc, mul_assoc]
        gcongr
        norm_num

end TauCeti
