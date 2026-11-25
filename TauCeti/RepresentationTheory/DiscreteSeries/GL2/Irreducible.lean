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
spanned by weight vectors: since `H_c` acts on `v_ℓ` by the distinct scalars `ℓ`, applying
`H_c - ℓ` to a vector of `N` removes its `ℓ`-component, and an induction on the size of the support
puts every component of a vector of `N` in `N`
(`TauCeti.CompactWeightModule.smul_weightVector_mem`). Second, the coefficients `(k + ℓ) / 2` of
`X_c` and `(k - ℓ) / 2` of `Y_c` vanish on a ray only at its end, so one weight vector of a ray
generates every weight vector of that ray, and the reflection passes from one ray to the other.

## Main results

* `TauCeti.CompactWeightModule.smul_weightVector_mem`: the weight components of a vector of a Lie
  submodule lie in it.
* `TauCeti.eq_bot_or_eq_discreteSeries`: for `k ≥ 1`, a reflection-stable Lie submodule of
  `D_k(μ)` is `⊥` or `D_k(μ)`.

## References

* A. W. Knapp, *Local Langlands correspondence: the Archimedean case*, in *Motives*, Proc. Sympos.
  Pure Math. 55, part 2, Amer. Math. Soc., 1994, pp. 393–410, §2, pp. 398–400.
-/

public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

namespace CompactWeightModule

variable {k μ : ℂ}

/-- A vector is the sum of its weight components. -/
theorem sum_smul_weightVector (v : CompactWeightModule k μ) :
    ∑ j ∈ (equivFinsupp k μ v).support, equivFinsupp k μ v j • weightVector k μ j = v := by
  apply (equivFinsupp k μ).injective
  simp only [map_sum, map_smul, equivFinsupp_weightVector, Finsupp.smul_single_one]
  exact Finsupp.sum_single _

/-- The coordinates of `H_c v`: `H_c` multiplies the `j`-th coordinate by `j`. -/
theorem equivFinsupp_lie_compactCartanH_apply (v : CompactWeightModule k μ) (j : ℤ) :
    equivFinsupp k μ ⁅compactCartanH, v⁆ j = j * equivFinsupp k μ v j := by
  conv_lhs => rw [← sum_smul_weightVector v]
  simp only [lie_sum, lie_smul, lie_compactCartanH_weightVector, smul_smul, map_sum, map_smul,
    equivFinsupp_weightVector]
  rw [Finset.sum_apply']
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq']
  split_ifs with h
  · rw [mul_comm]
  · rw [Finsupp.notMem_support_iff.mp h, mul_zero]

/-- **Lie submodules are spanned by weight vectors.** The `ℓ`-component of a vector of a Lie
submodule `N` lies in `N`. -/
theorem smul_weightVector_mem
    {N : LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ)}
    {v : CompactWeightModule k μ} (hv : v ∈ N) (ℓ : ℤ) :
    equivFinsupp k μ v ℓ • weightVector k μ ℓ ∈ N := by
  classical
  induction hn : (equivFinsupp k μ v).support.card using Nat.strong_induction_on
    generalizing v ℓ with
  | _ n ih =>
  by_cases hℓ : equivFinsupp k μ v ℓ = 0
  · rw [hℓ, zero_smul]
    exact N.zero_mem
  -- `u = (H_c - ℓ) v` has the coordinates `(j - ℓ) v_j`, and no `ℓ`-coordinate.
  set u := ⁅compactCartanH, v⁆ - (ℓ : ℂ) • v with hu_def
  have hu : u ∈ N := sub_mem (N.lie_mem hv) (N.smul_mem _ hv)
  have hcoord (j : ℤ) : equivFinsupp k μ u j = (j - ℓ) * equivFinsupp k μ v j := by
    rw [hu_def, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
      equivFinsupp_lie_compactCartanH_apply, smul_eq_mul, sub_mul]
  have hsupp : (equivFinsupp k μ u).support = (equivFinsupp k μ v).support.erase ℓ := by
    ext j
    simp only [Finsupp.mem_support_iff, Finset.mem_erase, hcoord, ne_eq, mul_eq_zero, not_or,
      sub_eq_zero, Int.cast_inj]
  have hcard : (equivFinsupp k μ u).support.card < n := by
    rw [hsupp, ← hn]
    exact Finset.card_erase_lt_of_mem (Finsupp.mem_support_iff.mpr hℓ)
  -- The other components of `v` lie in `N`.
  have hother (j : ℤ) (hj : j ≠ ℓ) : equivFinsupp k μ v j • weightVector k μ j ∈ N := by
    have h := N.smul_mem ((j : ℂ) - ℓ)⁻¹ (ih _ hcard hu j rfl)
    have hne : (j : ℂ) - ℓ ≠ 0 := sub_ne_zero.mpr (Int.cast_injective.ne hj)
    rwa [hcoord, smul_smul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul] at h
  -- The `ℓ`-component is `v` minus the others.
  have hsum := sum_smul_weightVector v
  rw [← Finset.add_sum_erase _ _ (Finsupp.mem_support_iff.mpr hℓ)] at hsum
  rw [eq_sub_of_add_eq hsum]
  exact sub_mem hv (sum_mem fun j hj ↦ hother j (Finset.ne_of_mem_erase hj))

/-- A weight vector with a nonzero coordinate of a vector of `N` lies in `N`. -/
theorem weightVector_mem_of_mem
    {N : LieSubmodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (CompactWeightModule k μ)}
    {v : CompactWeightModule k μ} (hv : v ∈ N) {ℓ : ℤ} (hℓ : equivFinsupp k μ v ℓ ≠ 0) :
    weightVector k μ ℓ ∈ N := by
  simpa [smul_smul, inv_mul_cancel₀ hℓ] using
    N.smul_mem (equivFinsupp k μ v ℓ)⁻¹ (smul_weightVector_mem hv ℓ)

end CompactWeightModule

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
      have h'' := N.smul_mem (-((t : ℂ) + 1))⁻¹ h'
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h''
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
      have h'' := N.smul_mem ((k + t : ℕ) : ℂ)⁻¹ h'
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h''
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
    · refine ⟨-ℓ, ?_, by simpa using hrefl _ hvℓ⟩
      rw [mem_negativeDiscreteSeriesWeights] at h
      rw [mem_positiveDiscreteSeriesWeights]
      omega
  -- Hence every weight vector of `D_k(μ)` lies in `N`.
  have hall (j : ℤ) (hj : j ∈ discreteSeriesWeights k) : weightVector (k : ℂ) μ j ∈ N := by
    rw [discreteSeriesWeights_eq_union] at hj
    rcases hj with h | h
    · exact weightVector_mem_of_positive hk hℓ' hNℓ' h
    · have h' : -j ∈ positiveDiscreteSeriesWeights k := by
        rw [mem_negativeDiscreteSeriesWeights] at h
        rw [mem_positiveDiscreteSeriesWeights]
        omega
      simpa using hrefl _ (weightVector_mem_of_positive hk hℓ' hNℓ' h')
  intro w hw
  rw [← sum_smul_weightVector w]
  refine sum_mem fun j hj ↦ N.smul_mem _ (hall j ?_)
  by_contra h
  exact Finsupp.mem_support_iff.mp hj
    ((Finsupp.mem_supported' _ _).mp (mem_discreteSeries_iff.mp hw) j h)

end TauCeti
