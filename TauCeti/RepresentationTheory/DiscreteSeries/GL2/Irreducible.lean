/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.DiscreteSeries.GL2

/-!
# Irreducibility of the discrete series of `GL₂(ℝ)`

The `𝔤𝔩₂(ℂ)`-module `D_k(μ)` (`TauCeti.discreteSeries k μ`), `k ≥ 1`, is irreducible for the full
group `GL₂(ℝ)`: its only Lie submodules stable under the reflection `A = diag(1, -1)` of `O(2)`
are `⊥` and `D_k(μ)` (`TauCeti.eq_bot_or_eq_discreteSeries`). As a `𝔤𝔩₂(ℂ)`-module alone it is the
sum of the two rays `D_k^±(μ)`, which the reflection interchanges.

The proof has two steps. First, every Lie submodule `N` of the module of all compact weights is
spanned by weight vectors (`TauCeti.CompactWeightModule.smul_weightVector_mem`). Second, the
coefficients `(k + ℓ) / 2` of `X_c` and `(k - ℓ) / 2` of `Y_c` vanish on a ray only at its end, so
one weight vector of a ray generates every weight vector of that ray, and the reflection passes
from one ray to the other.

## Main results

* `TauCeti.eq_bot_or_eq_discreteSeries`: for `k ≥ 1`, a reflection-stable Lie submodule of
  `D_k(μ)` is `⊥` or `D_k(μ)`.

## References

* A. W. Knapp, *Local Langlands correspondence: the Archimedean case*, in *Motives*, Proc. Sympos.
  Pure Math. 55, part 2, Amer. Math. Soc., 1994, pp. 393–410, §2, pp. 398–400.
-/

public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

open CompactWeightModule

variable {μ : ℂ}

/-- One weight vector of the positive ray generates every weight vector of the positive ray, for
`k ≥ 1`: lowering reaches `v_k` and raising then reaches every `v_{k + 2t}`. -/
private theorem weightVector_mem_of_positive {k : ℕ} (hk : 1 ≤ k)
    {N : LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule (k : ℂ) μ)} {ℓ : ℤ}
    (hℓ : ℓ ∈ positiveDiscreteSeriesWeights k) (hN : weightVector (k : ℂ) μ ℓ ∈ N)
    {j : ℤ} (hj : j ∈ positiveDiscreteSeriesWeights k) : weightVector (k : ℂ) μ j ∈ N := by
  rw [mem_positiveDiscreteSeriesWeights] at hℓ hj
  -- Lowering from `v_{k + 2t}` reaches `v_k`.
  have hdown (t : ℕ) (h : weightVector (k : ℂ) μ ((k : ℤ) + 2 * t) ∈ N) :
      weightVector (k : ℂ) μ k ∈ N := by
    induction t with
    | zero => simpa using h
    | succ t ih =>
      refine ih ?_
      have h' := N.lie_mem (x := compactCartanY) h
      have hc : ((k : ℂ) - (((k : ℤ) + 2 * ((t + 1 : ℕ) : ℤ) : ℤ) : ℂ)) / 2 = -((t : ℂ) + 1) := by
        push_cast
        ring
      rw [lie_compactCartanY_weightVector, hc,
        show (k : ℤ) + 2 * ((t + 1 : ℕ) : ℤ) - 2 = k + 2 * t by push_cast; ring] at h'
      have hne : -((t : ℂ) + 1) ≠ 0 := neg_ne_zero.mpr (Nat.cast_add_one_ne_zero t)
      exact (N.toSubmodule.smul_mem_iff hne).mp h'
  -- Raising from `v_k` reaches every `v_{k + 2t}`.
  have hup (t : ℕ) : weightVector (k : ℂ) μ ((k : ℤ) + 2 * t) ∈ N := by
    induction t with
    | zero => simpa using hdown ((ℓ - k) / 2).toNat (by
        rw [show (k : ℤ) + 2 * (((ℓ - k) / 2).toNat : ℕ) = ℓ by omega]
        exact hN)
    | succ t ih =>
      have h' := N.lie_mem (x := compactCartanX) ih
      have hc : ((k : ℂ) + (((k : ℤ) + 2 * (t : ℤ) : ℤ) : ℂ)) / 2 = ((k + t : ℕ) : ℂ) := by
        push_cast
        ring
      have hne : ((k + t : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [lie_compactCartanX_weightVector, hc,
        show (k : ℤ) + 2 * (t : ℤ) + 2 = k + 2 * ((t + 1 : ℕ) : ℤ) by push_cast; ring] at h'
      exact (N.toSubmodule.smul_mem_iff hne).mp h'
  rw [show j = (k : ℤ) + 2 * (((j - k) / 2).toNat : ℕ) by omega]
  exact hup _

/-- **Irreducibility of `D_k(μ)` for the full group.** For `k ≥ 1`, a Lie submodule of `D_k(μ)`
stable under the reflection `A = diag(1, -1)` is `⊥` or `D_k(μ)`. -/
theorem eq_bot_or_eq_discreteSeries {k : ℕ} (hk : 1 ≤ k)
    {N : LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule (k : ℂ) μ)}
    (hN : N ≤ discreteSeries k μ) (hrefl : ∀ v ∈ N, reflection (k : ℂ) μ v ∈ N) :
    N = ⊥ ∨ N = discreteSeries k μ := by
  refine or_iff_not_imp_left.mpr fun hbot ↦ le_antisymm hN ?_
  obtain ⟨v, hv, hv0⟩ : ∃ v ∈ N, v ≠ 0 := by
    by_contra! h
    exact hbot ((LieSubmodule.eq_bot_iff N).mpr h)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, equivFinsupp (k : ℂ) μ v ℓ ≠ 0 := by
    by_contra! h
    exact hv0 ((equivFinsupp (k : ℂ) μ).injective (by ext ℓ; simp [h ℓ]))
  have hvℓ := weightVector_mem_of_mem hv hℓ
  have hℓw : ℓ ∈ discreteSeriesWeights k := by
    by_contra h
    exact hℓ ((Finsupp.mem_supported' _ _).mp (mem_discreteSeries_iff.mp (hN hv)) ℓ h)
  -- Some weight vector of the positive ray lies in `N`.
  obtain ⟨ℓ', hℓ', hNℓ'⟩ : ∃ ℓ' ∈ positiveDiscreteSeriesWeights k,
      weightVector (k : ℂ) μ ℓ' ∈ N := by
    rw [discreteSeriesWeights_eq_union] at hℓw
    rcases hℓw with h | h
    · exact ⟨ℓ, h, hvℓ⟩
    · exact ⟨-ℓ, neg_mem_positiveDiscreteSeriesWeights_iff.mpr h, by simpa using hrefl _ hvℓ⟩
  -- Hence every weight vector of `D_k(μ)` lies in `N`.
  have hall (j : ℤ) (hj : j ∈ discreteSeriesWeights k) : weightVector (k : ℂ) μ j ∈ N := by
    rw [discreteSeriesWeights_eq_union] at hj
    rcases hj with h | h
    · exact weightVector_mem_of_positive hk hℓ' hNℓ' h
    · simpa using hrefl _ (weightVector_mem_of_positive hk hℓ' hNℓ'
        (neg_mem_positiveDiscreteSeriesWeights_iff.mpr h))
  intro w hw
  rw [← sum_smul_weightVector w]
  refine sum_mem fun j hj ↦ N.smul_mem _ (hall j ?_)
  by_contra h
  exact Finsupp.mem_support_iff.mp hj
    ((Finsupp.mem_supported' _ _).mp (mem_discreteSeries_iff.mp hw) j h)

end TauCeti
