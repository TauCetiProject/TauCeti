/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import TauCeti.Probability.FreeProbability.FreePoisson.Basic

/-!
# The free Poisson limit theorem

For each `N`, let `b N 0, …, b N (N - 1)` be freely independent elements of an algebra `A N` with
a normalised linear functional `φ N` over `𝕜 = ℝ` or `ℂ`, all with the same moments
`φ N (b N j ^ k) = m N k` for `k ≥ 1`. If `N * m N k → κ k` for every `k ≥ 1`, then the moments of
the row sums `S_N = b N 0 + ⋯ + b N (N - 1)` converge to the moments of an element whose free
cumulants are the `κ k`:

`φ N (S_N ^ n) → ∑_{π ∈ NC(n)} ∏_{B ∈ π} κ #B`.

Indeed, the free cumulants of `S_N` are `N` times those of a summand, and the `n`-th free cumulant
of a summand is `m N n` plus products of at least two moments, each of order `1 / N`.

The *free Poisson limit theorem* is the case of summands with the moments of the Bernoulli law
`(1 - r / N) δ₀ + (r / N) δ_c`, that is `φ N (b N j ^ k) = r / N * c ^ k` for `k ≥ 1`: the moments
of `S_N`, the `N`-fold free additive convolution power of this law, converge to the moments
`c ^ n * ∑_{π ∈ NC(n)} r ^ |π|` of a free Poisson element of rate `r` and jump size `c`.

No positivity or traciality of the functionals is assumed, the algebras may depend on `N`, and the
conclusion is convergence of moments.

## Main results

* `TauCeti.tendsto_apply_sum_pow_of_tendsto_natCast_mul` — the limit theorem for the row sums of a
  triangular array of free, identically distributed elements.
* `TauCeti.tendsto_apply_sum_pow_of_apply_pow_eq_div_mul_pow` — the free Poisson limit theorem.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Theorem 13.1 for the
  limit theorem for sums of free, identically distributed elements, and Proposition 12.11 for the
  free Poisson limit theorem.
-/

public section

open Finset Filter Topology IncidenceAlgebra

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]

/-- If `N * m N k → κ k` for every `k ≥ 1`, then for a nonempty set `B` of positions, `N` times
the free cumulant of an element with moments `m N`, written by Möbius inversion as
`∑_{σ ∈ NC(B)} μ(σ, 1̂) ∏_{D ∈ σ} m N #D`, tends to `κ #B`: the term of `σ = 1̂` is
`N * m N #B`, and every other term has at least two parts, so it is `O(1 / N)`. -/
private theorem tendsto_natCast_mul_sum_mu_mul_prod {α : Type*} [LinearOrder α] {m : ℕ → ℕ → 𝕜}
    {κ : ℕ → 𝕜} (hm : ∀ k, k ≠ 0 → Tendsto (fun N : ℕ => (N : 𝕜) * m N k) atTop (𝓝 (κ k)))
    {B : Finset α} (hB : B.Nonempty) :
    Tendsto (fun N : ℕ => (N : 𝕜) *
        ∑ σ : NoncrossingPartition B, mu 𝕜 σ ⊤ * ∏ D ∈ σ.1.parts, m N #D) atTop (𝓝 (κ #B)) := by
  have hD (σ : NoncrossingPartition B) :
      Tendsto (fun N : ℕ => ∏ D ∈ σ.1.parts, (N : 𝕜) * m N #D) atTop
        (𝓝 (∏ D ∈ σ.1.parts, κ #D)) :=
    tendsto_finsetProd _ fun D hD => hm _ (σ.1.nonempty_of_mem_parts hD).card_pos.ne'
  -- Each term tends to `κ #B` for `σ = 1̂` and to `0` otherwise.
  have hσ (σ : NoncrossingPartition B) :
      Tendsto (fun N : ℕ => (N : 𝕜) * (mu 𝕜 σ ⊤ * ∏ D ∈ σ.1.parts, m N #D)) atTop
        (𝓝 (if σ = ⊤ then κ #B else 0)) := by
    have hp : #σ.1.parts ≠ 0 := (σ.1.parts_nonempty (bot_eq_empty ▸ hB.ne_empty)).card_pos.ne'
    have h1 := ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := 𝕜)).pow (#σ.1.parts - 1)).mul (hD σ)
    refine Tendsto.congr' (f₁ := fun N : ℕ => mu 𝕜 σ ⊤ *
        (((N : 𝕜)⁻¹ ^ (#σ.1.parts - 1)) * ∏ D ∈ σ.1.parts, (N : 𝕜) * m N #D)) ?_ ?_
    · filter_upwards [eventually_ne_atTop 0] with N hN
      have hN' : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 hN
      have hinv : (N : 𝕜)⁻¹ ^ (#σ.1.parts - 1) * (N : 𝕜) ^ (#σ.1.parts - 1) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hN', one_pow]
      rw [prod_mul_distrib, prod_const, ← pow_sub_one_mul hp]
      linear_combination (mu 𝕜 σ ⊤ * N * ∏ D ∈ σ.1.parts, m N #D) * hinv
    split_ifs with htop
    · subst htop
      simpa [Finpartition.parts_top hB.ne_empty] using h1
    · -- A partition other than `1̂` has at least two parts.
      have hp2 : #σ.1.parts - 1 ≠ 0 := by
        refine Nat.sub_ne_zero_of_lt (lt_of_not_ge fun hle => htop ?_)
        obtain ⟨C, hC⟩ := Finset.card_eq_one.1 (le_antisymm hle (Nat.pos_of_ne_zero hp))
        have hCB : C = B := by simpa [hC] using σ.1.sup_parts
        exact Subtype.ext (Finpartition.eq_top_of_mem_parts (hCB ▸ hC ▸ mem_singleton_self C))
      simpa [zero_pow hp2] using h1.const_mul (mu 𝕜 σ ⊤)
  have := tendsto_finsetSum univ fun σ _ => hσ σ
  rw [Fintype.sum_ite_eq'] at this
  exact this.congr fun N => by rw [mul_sum]

variable {A : ℕ → Type*} [∀ N, Semiring (A N)] [∀ N, Algebra 𝕜 (A N)] {φ : ∀ N, A N →ₗ[𝕜] 𝕜}
  {b : ∀ N, Fin N → A N}

/-- *The limit theorem for sums of free, identically distributed elements*: for each `N`, let
`b N 0, …, b N (N - 1)` be freely independent for a normalised `φ N`, with common moments
`φ N (b N j ^ k) = m N k` for `k ≥ 1`. If `N * m N k → κ k` for every `k ≥ 1`, then the moments of
the row sums converge to `∑_{π ∈ NC(n)} ∏_{B ∈ π} κ #B`, the moments of an element whose free
cumulants are the `κ k`. -/
theorem tendsto_apply_sum_pow_of_tendsto_natCast_mul
    (h : ∀ N, IsFreelyIndependentElements (φ N) (b N)) (hφ : ∀ N, φ N 1 = 1)
    {m : ℕ → ℕ → 𝕜} (hb : ∀ N j k, k ≠ 0 → φ N (b N j ^ k) = m N k) {κ : ℕ → 𝕜}
    (hm : ∀ k, k ≠ 0 → Tendsto (fun N : ℕ => (N : 𝕜) * m N k) atTop (𝓝 (κ k))) (n : ℕ) :
    Tendsto (fun N => φ N ((∑ j, b N j) ^ n)) atTop
      (𝓝 (∑ π : NoncrossingPartition (univ : Finset (Fin n)), ∏ B ∈ π.1.parts, κ #B)) := by
  -- The free cumulants of the row sum are `N` times the common free cumulants of the summands,
  -- which are given by Möbius inversion of their moments.
  refine (tendsto_finsetSum _ fun π _ => tendsto_finsetProd _ fun B hB =>
    tendsto_natCast_mul_sum_mu_mul_prod hm (π.1.nonempty_of_mem_parts hB)).congr fun N => ?_
  have hκ (j : Fin N) (B : Finset (Fin n)) : freeCumulant (φ N) (fun _ => b N j) B =
      ∑ σ : NoncrossingPartition B, mu 𝕜 σ ⊤ * ∏ D ∈ σ.1.parts, m N #D := by
    refine (freeCumulant_eq_sum_mu_mul_partitionMoment _ _ B).trans (sum_congr rfl fun σ _ => ?_)
    rw [partitionMoment_const]
    exact congrArg _ (prod_congr rfl fun D hD =>
      hb N j _ (σ.1.nonempty_of_mem_parts hD).card_pos.ne')
  rw [(h N).apply_sum_pow_eq_sum_prod_sum_freeCumulant (hφ N)]
  simp_rw [hκ, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- *The free Poisson limit theorem*: for each `N`, let `b N 0, …, b N (N - 1)` be freely
independent for a normalised `φ N`, each with the moments `φ N (b N j ^ k) = r / N * c ^ k`,
`k ≥ 1`, of the Bernoulli law `(1 - r / N) δ₀ + (r / N) δ_c`. Then the moments of the row sums
converge to `c ^ n * ∑_{π ∈ NC(n)} r ^ |π|`, the moments of a free Poisson element of rate `r` and
jump size `c`. -/
theorem tendsto_apply_sum_pow_of_apply_pow_eq_div_mul_pow
    (h : ∀ N, IsFreelyIndependentElements (φ N) (b N)) (hφ : ∀ N, φ N 1 = 1) {r c : 𝕜}
    (hb : ∀ N j k, k ≠ 0 → φ N (b N j ^ k) = r / N * c ^ k) (n : ℕ) :
    Tendsto (fun N => φ N ((∑ j, b N j) ^ n)) atTop
      (𝓝 (c ^ n * ∑ π : NoncrossingPartition (univ : Finset (Fin n)), r ^ #π.1.parts)) := by
  have hm (k : ℕ) (_ : k ≠ 0) :
      Tendsto (fun N : ℕ => (N : 𝕜) * (r / N * c ^ k)) atTop (𝓝 (r * c ^ k)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    field_simp [Nat.cast_ne_zero.2 hN]
  have := tendsto_apply_sum_pow_of_tendsto_natCast_mul h hφ hb hm n
  rwa [NoncrossingPartition.sum_prod_mul_pow_card, card_univ, Fintype.card_fin] at this

end TauCeti
