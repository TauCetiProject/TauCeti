/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Products of geometric series

A finite product of geometric series is an unconditionally convergent series indexed by
multi-indices. This is the expansion of the Cauchy kernel on a polydisc.
-/

public section

namespace TauCeti

/-- The product of finitely many geometric series, indexed by all exponent vectors.
The index type may be empty. -/
theorem hasSum_prod_geometric_of_norm_lt_one {𝕜 ι : Type*} [NormedField 𝕜]
    [Fintype ι] {r : ι → 𝕜} (hr : ∀ i, ‖r i‖ < 1) :
    HasSum (fun α : ι → ℕ ↦ ∏ i, r i ^ α i) (∏ i, (1 - r i)⁻¹) := by
  classical
  -- First obtain the nonnegative majorant needed for absolute summability.
  have hnonneg : ∀ n (q : Fin n → ℝ), (∀ i, 0 ≤ q i) → (∀ i, q i < 1) →
      Summable (fun α : Fin n → ℕ ↦ ∏ i, q i ^ α i) := by
    intro n
    induction n with
    | zero => intro q _ _; exact (hasSum_fintype _).summable
    | succ n ih =>
      intro q hq hq'
      apply (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ℕ)).summable_iff.mp
      simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ] using
        (summable_geometric_of_lt_one (hq 0) (hq' 0)).mul_of_nonneg
          (ih (fun i ↦ q i.succ) (fun i ↦ hq i.succ) (fun i ↦ hq' i.succ))
          (fun k ↦ pow_nonneg (hq 0) k)
          (fun α ↦ Finset.prod_nonneg fun i _ ↦ pow_nonneg (hq i.succ) (α i))
  -- Multiply the geometric sums one coordinate at a time.
  have hfin : ∀ n (q : Fin n → 𝕜), (∀ i, ‖q i‖ < 1) →
      HasSum (fun α : Fin n → ℕ ↦ ∏ i, q i ^ α i) (∏ i, (1 - q i)⁻¹) := by
    intro n
    induction n with
    | zero => intro q _; simp
    | succ n ih =>
      intro q hq
      have h₀ := hasSum_geometric_of_norm_lt_one (hq 0)
      have ht := ih (fun i ↦ q i.succ) (fun i ↦ hq i.succ)
      have hn₀ : Summable (fun k : ℕ ↦ ‖q 0 ^ k‖) := by
        simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hq 0)
      have hnt : Summable (fun α : Fin n → ℕ ↦ ‖∏ i, q i.succ ^ α i‖) := by
        simpa only [norm_prod, norm_pow] using
          hnonneg n (fun i ↦ ‖q i.succ‖) (fun i ↦ norm_nonneg _) (fun i ↦ hq i.succ)
      have hm : Summable (fun a : ℕ × (Fin n → ℕ) ↦
          q 0 ^ a.1 * ∏ i, q i.succ ^ a.2 i) :=
        summable_mul_of_summable_norm'
          (f := fun k : ℕ ↦ q 0 ^ k) (g := fun α : Fin n → ℕ ↦ ∏ i, q i.succ ^ α i)
          hn₀ h₀.summable hnt ht.summable
      have hmul := h₀.mul ht hm
      apply (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ℕ)).hasSum_iff.mp
      simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ] using
        hmul
  -- Reindex the result from finite tuples to the requested finite index type.
  let e := Fintype.equivFin ι
  have hp (α : ι → ℕ) : (∏ i, r i ^ α i) = ∏ j, r (e.symm j) ^ α (e.symm j) :=
    Fintype.prod_equiv e _ _ (fun i ↦ by simp)
  have hc : (∏ i, (1 - r i)⁻¹) = ∏ j, (1 - r (e.symm j))⁻¹ :=
    Fintype.prod_equiv e _ _ (fun i ↦ by simp)
  rw [hc]
  apply (Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) ↦ ℕ) e).symm.hasSum_iff.mp
  simpa only [Function.comp_def, hp, Equiv.piCongrLeft_symm_apply,
    Equiv.apply_symm_apply] using hfin (Fintype.card ι) (fun j ↦ r (e.symm j))
      (fun j ↦ hr (e.symm j))

end TauCeti
