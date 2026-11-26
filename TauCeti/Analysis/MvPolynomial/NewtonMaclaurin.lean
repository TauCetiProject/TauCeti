/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import TauCeti.Analysis.Convex.Sequence.DiscreteConcave
import TauCeti.Analysis.MeanInequalities
import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
import TauCeti.RingTheory.MvPolynomial.Symmetric.NewtonMaclaurin

/-!
# The Newton–Maclaurin inequalities on the cones `Γ_k`

For `λ ∈ ℝⁿ` write `σ_k(λ)` for the elementary symmetric polynomial `MvPolynomial.esymm` evaluated
at `λ` and `S_k = σ_k / binom(n, k)` for the normalized function `TauCeti.normalizedEsymm`. The
cone `Γ_k = {λ | σ_1(λ) > 0, …, σ_k(λ) > 0}` is `TauCeti.hessianCone n k`.

## Main results

* `TauCeti.normalizedEsymm_mul_normalizedEsymm_le_sq`: **Newton's inequalities**
  `S_k S_{k+2} ≤ S_{k+1}²` for every `λ ∈ ℝⁿ`, and
  `TauCeti.eq_of_normalizedEsymm_mul_normalizedEsymm_eq_sq`: equality with `S_{k+2} ≠ 0` (for
  instance on `Γ_n` when `k + 2 ≤ n`) forces all `λ_i` to be equal.
* `TauCeti.normalizedEsymm_div_rpow_le`: the **generalized Newton–Maclaurin inequality**
  `(S_r / S_s)^{1/(r - s)} ≤ (S_k / S_l)^{1/(k - l)}` on `Γ_r` for `s < r`, `l < k ≤ r`, `l ≤ s`.
* `TauCeti.normalizedEsymm_rpow_le`: **Maclaurin's inequalities** `S_l^{1/l} ≤ S_k^{1/k}` on `Γ_l`
  for `1 ≤ k ≤ l`, with `TauCeti.normalizedEsymm_rpow_le_of_mem_closure` on the closure of `Γ_l`
  and `TauCeti.normalizedEsymm_rpow_le_of_nonneg` on the closed positive orthant.

## Implementation notes

Newton's inequalities, their equality case and Maclaurin's inequalities on the orthant are the
multiset versions `Multiset.esymm_div_choose_mul_esymm_div_choose_le_sq`,
`Multiset.eq_of_esymm_div_choose_mul_esymm_div_choose_eq_sq` and
`Multiset.esymm_div_choose_rpow_le_rpow_of_nonneg`, applied to the multiset of entries of `λ`. The
generalized Newton–Maclaurin inequality follows from the concavity of `j ↦ log S_j` on `[0, r]`.

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, Global
  theory of minimal surfaces, Clay Math. Proc. 2 (2005), Proposition 2.7, Corollary 2.8 and
  Lemma 2.10.
* S. Dinew and S. Kołodziej, *A priori estimates for complex Hessian equations*, Anal. PDE 7
  (2014), §1.
-/

public section

open Finset MvPolynomial

namespace TauCeti

section Normalized

variable {ι : Type*} [Fintype ι]

/-- The **normalized elementary symmetric function** `S_k(λ) = σ_k(λ) / binom(n, k)` of
`λ : ι → ℝ`, where `n` is the cardinality of `ι`. -/
noncomputable def normalizedEsymm (k : ℕ) (μ : ι → ℝ) : ℝ :=
  eval μ (esymm ι ℝ k) / (Fintype.card ι).choose k

/-- The defining formula of `TauCeti.normalizedEsymm`. -/
theorem normalizedEsymm_def (k : ℕ) (μ : ι → ℝ) :
    normalizedEsymm k μ = eval μ (esymm ι ℝ k) / (Fintype.card ι).choose k := by
  rw [normalizedEsymm]

/-- `S_0 = 1`. -/
@[simp]
theorem normalizedEsymm_zero (μ : ι → ℝ) : normalizedEsymm 0 μ = 1 := by
  simp [normalizedEsymm]

/-- `S_k = 0` for `k > n`. -/
@[simp]
theorem normalizedEsymm_of_card_lt {k : ℕ} (h : Fintype.card ι < k) (μ : ι → ℝ) :
    normalizedEsymm k μ = 0 := by
  rw [normalizedEsymm, Nat.choose_eq_zero_of_lt h, Nat.cast_zero, div_zero]

private theorem eval_esymm_eq_esymm_map (μ : ι → ℝ) (k : ℕ) :
    eval μ (esymm ι ℝ k) = (univ.val.map μ).esymm k :=
  aeval_esymm_eq_multiset_esymm ι ℝ k μ

private theorem normalizedEsymm_eq_esymm_div_choose (k : ℕ) (μ : ι → ℝ) :
    normalizedEsymm k μ =
      (univ.val.map μ).esymm k / (Multiset.card (univ.val.map μ)).choose k := by
  rw [normalizedEsymm, eval_esymm_eq_esymm_map, Multiset.card_map, Finset.card_val,
    Finset.card_univ]

private theorem forall_mem_map_univ_val {μ : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i) :
    ∀ a ∈ univ.val.map μ, 0 ≤ a := fun a ha ↦ by
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp ha
  exact hμ i

/-- `S_k` is continuous. -/
@[fun_prop]
theorem continuous_normalizedEsymm (k : ℕ) : Continuous (normalizedEsymm (ι := ι) k) :=
  (MvPolynomial.continuous_eval _).div_const _

/-- `S_k(λ) ≥ 0` when every entry of `λ` is nonnegative. -/
theorem normalizedEsymm_nonneg {μ : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i) (k : ℕ) :
    0 ≤ normalizedEsymm k μ := by
  rw [normalizedEsymm_eq_esymm_div_choose]
  exact div_nonneg (Multiset.esymm_nonneg (forall_mem_map_univ_val hμ) k) (Nat.cast_nonneg _)

/-- **Newton's inequality** `S_k S_{k+2} ≤ S_{k+1}²`, for every `λ ∈ ℝⁿ` and every `k`. -/
theorem normalizedEsymm_mul_normalizedEsymm_le_sq (μ : ι → ℝ) (k : ℕ) :
    normalizedEsymm k μ * normalizedEsymm (k + 2) μ ≤ normalizedEsymm (k + 1) μ ^ 2 := by
  simpa only [normalizedEsymm_eq_esymm_div_choose] using
    Multiset.esymm_div_choose_mul_esymm_div_choose_le_sq _ k

/-- The equality case of Newton's inequality: if `S_{k+2}(λ) ≠ 0` and
`S_k(λ) S_{k+2}(λ) = S_{k+1}(λ)²`, then all `λ_i` are equal. The hypothesis `S_{k+2} ≠ 0` holds on
`Γ_{k+2}`, in particular on `Γ_n` when `k + 2 ≤ n`
(`TauCeti.normalizedEsymm_pos_of_mem_hessianCone`); without it
`λ = (1, 0, 0)` and `k = 1` give equality with unequal entries. -/
theorem eq_of_normalizedEsymm_mul_normalizedEsymm_eq_sq {μ : ι → ℝ} {k : ℕ}
    (hne : normalizedEsymm (k + 2) μ ≠ 0)
    (h : normalizedEsymm k μ * normalizedEsymm (k + 2) μ = normalizedEsymm (k + 1) μ ^ 2)
    (i j : ι) : μ i = μ j := by
  simp only [normalizedEsymm_eq_esymm_div_choose] at hne h
  exact Multiset.eq_of_esymm_div_choose_mul_esymm_div_choose_eq_sq (div_ne_zero_iff.mp hne).1 h
    _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)) _
    (Multiset.mem_map_of_mem _ (Finset.mem_univ_val j))

/-- **Maclaurin's inequality** `S_l^{1/l} ≤ S_k^{1/k}` for `1 ≤ k ≤ l` and `λ` with nonnegative
entries. -/
theorem normalizedEsymm_rpow_le_of_nonneg {k l : ℕ} {μ : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i)
    (hk : 1 ≤ k) (hkl : k ≤ l) :
    normalizedEsymm l μ ^ (1 / (l : ℝ)) ≤ normalizedEsymm k μ ^ (1 / (k : ℝ)) := by
  simpa only [normalizedEsymm_eq_esymm_div_choose] using
    Multiset.esymm_div_choose_rpow_le_rpow_of_nonneg _ hk hkl (forall_mem_map_univ_val hμ)

end Normalized

section Cone

/-- The cone `Γ_k = {λ | σ_1(λ) > 0, …, σ_k(λ) > 0}` of `ℝⁿ`. -/
def hessianCone (n k : ℕ) : Set (Fin n → ℝ) :=
  {μ | ∀ j ∈ Finset.Icc 1 k, 0 < eval μ (esymm (Fin n) ℝ j)}

/-- The defining property of `TauCeti.hessianCone`. -/
@[simp]
theorem mem_hessianCone {n k : ℕ} {μ : Fin n → ℝ} :
    μ ∈ hessianCone n k ↔ ∀ j ∈ Finset.Icc 1 k, 0 < eval μ (esymm (Fin n) ℝ j) :=
  Iff.rfl

/-- A vector with positive entries lies in `Γ_k` for every `k ≤ n`. -/
theorem mem_hessianCone_of_pos {n k : ℕ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 < μ i) (hk : k ≤ n) :
    μ ∈ hessianCone n k := fun j hj ↦ by
  rw [eval_esymm_eq_esymm_map, Finset.esymm_map_val]
  exact Finset.sum_pos (fun A _ ↦ Finset.prod_pos fun i _ ↦ hμ i)
    (Finset.powersetCard_nonempty.mpr (by simpa using (Finset.mem_Icc.mp hj).2.trans hk))

/-- On `Γ_k`, `S_j > 0` for every `j ≤ k`, including `S_0 = 1`. -/
theorem normalizedEsymm_pos_of_mem_hessianCone {n k j : ℕ} {μ : Fin n → ℝ}
    (hμ : μ ∈ hessianCone n k) (hj : j ≤ k) : 0 < normalizedEsymm j μ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  have hσ := hμ j (Finset.mem_Icc.mpr ⟨hj0, hj⟩)
  rw [eval_esymm_eq_esymm_map] at hσ
  rw [normalizedEsymm_eq_esymm_div_choose]
  exact Multiset.esymm_div_choose_pos _ hσ

/-- The **generalized Newton–Maclaurin inequality**: for `0 ≤ s < r`, `0 ≤ l < k ≤ r` with `l ≤ s`
and `λ ∈ Γ_r`, `(S_r / S_s)^{1/(r - s)} ≤ (S_k / S_l)^{1/(k - l)}`. -/
theorem normalizedEsymm_div_rpow_le {n r s k l : ℕ} {μ : Fin n → ℝ}
    (hμ : μ ∈ hessianCone n r) (hsr : s < r) (hlk : l < k) (hkr : k ≤ r) (hls : l ≤ s) :
    (normalizedEsymm r μ / normalizedEsymm s μ) ^ (1 / ((r : ℝ) - s)) ≤
      (normalizedEsymm k μ / normalizedEsymm l μ) ^ (1 / ((k : ℝ) - l)) := by
  have hpos : ∀ j ≤ r, 0 < normalizedEsymm j μ := fun j hj ↦
    normalizedEsymm_pos_of_mem_hessianCone hμ hj
  have ha : ∀ j, j + 2 ≤ r → Real.log (normalizedEsymm j μ) +
      Real.log (normalizedEsymm (j + 2) μ) ≤ 2 * Real.log (normalizedEsymm (j + 1) μ) := by
    intro j hj
    have h2 : 2 * Real.log (normalizedEsymm (j + 1) μ) =
        Real.log (normalizedEsymm (j + 1) μ ^ 2) := by
      rw [Real.log_pow, Nat.cast_ofNat]
    rw [← Real.log_mul (hpos j (by omega)).ne' (hpos (j + 2) hj).ne', h2]
    exact Real.log_le_log (mul_pos (hpos j (by omega)) (hpos (j + 2) hj))
      (normalizedEsymm_mul_normalizedEsymm_le_sq μ j)
  have key := div_sub_le_div_sub_of_add_le_two_mul (a := fun j ↦ Real.log (normalizedEsymm j μ))
    ha hsr hlk hkr hls
  rw [Real.rpow_def_of_pos (div_pos (hpos r le_rfl) (hpos s hsr.le)),
    Real.rpow_def_of_pos (div_pos (hpos k hkr) (hpos l (by omega))), Real.exp_le_exp,
    Real.log_div (hpos r le_rfl).ne' (hpos s hsr.le).ne',
    Real.log_div (hpos k hkr).ne' (hpos l (by omega)).ne', mul_one_div, mul_one_div]
  exact key

/-- **Maclaurin's inequality** `S_l^{1/l} ≤ S_k^{1/k}` for `1 ≤ k ≤ l` and `λ ∈ Γ_l`. -/
theorem normalizedEsymm_rpow_le {n k l : ℕ} {μ : Fin n → ℝ} (hμ : μ ∈ hessianCone n l)
    (hk : 1 ≤ k) (hkl : k ≤ l) :
    normalizedEsymm l μ ^ (1 / (l : ℝ)) ≤ normalizedEsymm k μ ^ (1 / (k : ℝ)) := by
  simpa using normalizedEsymm_div_rpow_le hμ (s := 0) (l := 0) (by omega) (by omega) hkl le_rfl

/-- On the closure of `Γ_l`, `S_j ≥ 0` for `j ≤ l`. -/
theorem normalizedEsymm_nonneg_of_mem_closure {n l j : ℕ} {μ : Fin n → ℝ}
    (hμ : μ ∈ closure (hessianCone n l)) (hj : j ≤ l) : 0 ≤ normalizedEsymm j μ :=
  closure_minimal (fun _ hν ↦ (normalizedEsymm_pos_of_mem_hessianCone hν hj).le)
    (isClosed_le continuous_const (continuous_normalizedEsymm j)) hμ

/-- **Maclaurin's inequality** on the closure of `Γ_l`. -/
theorem normalizedEsymm_rpow_le_of_mem_closure {n k l : ℕ} {μ : Fin n → ℝ}
    (hμ : μ ∈ closure (hessianCone n l)) (hk : 1 ≤ k) (hkl : k ≤ l) :
    normalizedEsymm l μ ^ (1 / (l : ℝ)) ≤ normalizedEsymm k μ ^ (1 / (k : ℝ)) := by
  have hc : ∀ j : ℕ, 1 ≤ j → Continuous fun ν : Fin n → ℝ ↦ normalizedEsymm j ν ^ (1 / (j : ℝ)) :=
    fun j hj ↦ (continuous_normalizedEsymm j).rpow_const fun _ ↦ Or.inr (by positivity)
  exact closure_minimal (fun _ hν ↦ normalizedEsymm_rpow_le hν hk hkl)
    (isClosed_le (hc l (hk.trans hkl)) (hc k hk)) hμ

/-- The closed positive orthant lies in the closure of `Γ_k` for `k ≤ n`. -/
theorem mem_closure_hessianCone_of_nonneg {n k : ℕ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 ≤ μ i)
    (hk : k ≤ n) : μ ∈ closure (hessianCone n k) := by
  have ht : Filter.Tendsto (fun ε : ℝ ↦ μ + ε • (1 : Fin n → ℝ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds μ) := by
    have : Continuous fun ε : ℝ ↦ μ + ε • (1 : Fin n → ℝ) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε ↦ ?_)
  exact mem_hessianCone_of_pos (fun i ↦ by simpa using add_pos_of_nonneg_of_pos (hμ i) hε) hk

end Cone

end TauCeti
