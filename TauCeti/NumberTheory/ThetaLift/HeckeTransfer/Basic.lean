/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.LinearMap.ScaledTransfer

/-!
# Clearing powers in triangular Hecke transfers

For residue norm `q = (p ^ h) ^ 2`, the triangular Hecke transfer at index `i` comes with
scalar `(p ^ h)^((t + 1) * i) * q^(i.choose 2)`. The bound `r ≤ t` permits using a single
clearing power for all indices `i ≤ r`. Over a chain of lifts the exponents add, and if the
single-step coefficients are shared across a family of lifts, so are the final coefficients.

The powers and transfer identity follow `New.Data.pow_mul_pow_choose_two_dvd` and
`New.Data.IsWeakChainDatum.exists_sum_heckeSplit_chain_eq_pow_smul` in
`New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open Finset Submodule

namespace TauCeti

/-- If the residue degree `2 * h` is bounded by `f`, the coefficient at index `i ≤ r ≤ t`
of the lower Hecke polynomial after rescaling divides the common clearing power. -/
theorem heckeTransferScalar_dvd_pow {M : Type*} [Monoid M] (p : M) {h f i r t : ℕ}
    (hf : 2 * h ≤ f) (hi : i ≤ r) (hr : r ≤ t) :
    (p ^ h) ^ ((t + 1) * i) * ((p ^ h) ^ 2) ^ i.choose 2 ∣ p ^ (f * r * t) := by
  have hchoose : 2 * i.choose 2 = i * (i - 1) := by
    rw [mul_comm 2, Nat.choose_two_right,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self i)]
  have heq : (t + 1) * i + 2 * i.choose 2 = i * (t + i) := by
    rw [hchoose]
    cases i with
    | zero => simp
    | succ i => simp only [Nat.add_one_sub_one]; ring
  rw [← pow_mul (p ^ h), ← pow_add, heq, ← pow_mul]
  apply pow_dvd_pow
  calc
    h * (i * (t + i)) ≤ h * (r * (t + t)) := by gcongr; exact hi.trans hr
    _ = (2 * h) * r * t := by ring
    _ ≤ f * r * t := by gcongr

/-- Transfer the Hecke operator of index `r` through `n` lifts. Each step has a triangular
identity for all `i ≤ r` with one family of coefficients shared over the parameter `x`.
After clearing powers, the composite still has coefficients independent of `x` (and of the
input vector), with indices at most `r` and total exponent `n * (f * r * t)`. -/
theorem exists_sum_heckeTransfer_eq_pow_smul
    {R ι : Type*} [CommSemiring R] {V : ℕ → Type*} [∀ j, AddCommMonoid (V j)]
    [∀ j, Module R (V j)] {n h f r t : ℕ} (p : R) (hf : 2 * h ≤ f) (hr : r ≤ t)
    (C : ∀ j, ι → V 0 →ₗ[R] V j) (L : ∀ j, ι → V j →ₗ[R] V (j + 1))
    (T : ∀ j, ℕ → Module.End R (V j))
    (h0 : ∀ x, C 0 x = LinearMap.id)
    (hC : ∀ j < n, ∀ x, C (j + 1) x = (L j x).comp (C j x))
    (hL : ∀ j < n, ∀ i ≤ r, ∃ c : Fin (i + 1) → R, ∀ x,
      (∑ k, c k • (T (j + 1) k).comp (L j x)) =
        ((p ^ h) ^ ((t + 1) * i) * ((p ^ h) ^ 2) ^ i.choose 2) • (L j x).comp (T j i)) :
    ∃ c : Fin (r + 1) → R, ∀ x,
      (∑ i, c i • (T n i).comp (C n x)) = p ^ (n * (f * r * t)) • (C n x).comp (T 0 r) := by
  classical
  let D (j : ℕ) := LinearMap.piMap (C j)
  let F (j : ℕ) := LinearMap.piMap (L j)
  let A (j : ℕ) (i : Fin (r + 1)) : Module.End R (ι → V j) :=
    LinearMap.piMap (fun _ ↦ T j i)
  let S (j : ℕ) := Set.range (A j)
  have hD₀ : D 0 = LinearMap.id := by ext v x; simp [D, h0]
  have hD (j : ℕ) (hj : j < n) : D (j + 1) = (F j).comp (D j) := by
    ext v x; simp [D, F, hC j hj]
  have hF (j : ℕ) (hj : j < n) (s : Module.End R (ι → V j)) (hs : s ∈ S j) :
      p ^ (f * r * t) • (F j).comp s ∈ span R ((fun u ↦ u.comp (F j)) '' S (j + 1)) := by
    obtain ⟨i, rfl⟩ := hs
    obtain ⟨c, hc⟩ := hL j hj i i.is_le
    obtain ⟨a, ha⟩ := heckeTransferScalar_dvd_pow p hf i.is_le hr
    rw [ha, mul_comm, ← smul_smul]
    apply Submodule.smul_mem
    let ι' (k : Fin ((i : ℕ) + 1)) : Fin (r + 1) := Fin.castLE (Nat.succ_le_succ i.is_le) k
    have hsum : (∑ k, c k • (A (j + 1) (ι' k)).comp (F j)) =
        ((p ^ h) ^ ((t + 1) * (i : ℕ)) * ((p ^ h) ^ 2) ^ (i : ℕ).choose 2) •
          (F j).comp (A j i) := by
      ext v x
      simpa [A, F, ι'] using DFunLike.congr_fun (hc x) (v x)
    rw [← hsum]
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (subset_span ⟨_, ⟨ι' k, rfl⟩, rfl⟩)
  have H := LinearMap.prod_smul_comp_mem_span_of_smul_comp_mem_span D F S
    (fun _ ↦ p ^ (f * r * t)) (T := A 0 (Fin.last r)) ⟨_, rfl⟩ hD₀ hD hF
  dsimp only [S] at H
  rw [Finset.prod_const, Finset.card_range, ← pow_mul, mul_comm (f * r * t) n,
    ← Set.range_comp] at H
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp H
  refine ⟨c, fun x ↦ ?_⟩
  ext v
  simpa [D, A] using congrFun (DFunLike.congr_fun hc (fun _ ↦ v)) x

end TauCeti
