/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card

/-!
# Weight multiplicities of exterior powers

For an integer weight list, the multiplicity of a weight in an exterior power
counts subsets of the basis indices having that size and weight sum. Complementing
the indices and adding a common integer to all weights give the two symmetries
used in Lawrence and Sawin, *The Shafarevich conjecture for hypersurfaces in
abelian varieties*, Lemma 3.14, equation (3) and Appendix B, equation (10).
-/

public section

namespace TauCeti

variable {m : ℕ}

/-- Number of size-`k` subsets of the weight list `w` whose weights sum to `t`. -/
@[expose] def wedgeMultiplicity (w : Fin m → ℤ) (k : ℕ) (t : ℤ) : ℕ :=
  ((Finset.univ.powersetCard k).filter (fun s => ∑ i ∈ s, w i = t)).card

/-- A positive multiplicity is witnessed by a set of `k` indices of total weight `t`. -/
theorem wedgeMultiplicity_pos_iff (w : Fin m → ℤ) (k : ℕ) (t : ℤ) :
    0 < wedgeMultiplicity w k t ↔ ∃ s : Finset (Fin m), s.card = k ∧ ∑ i ∈ s, w i = t := by
  simp [wedgeMultiplicity, Finset.card_pos, Finset.Nonempty, Finset.mem_powersetCard]

/-- The finite set of weights in degree `k`. -/
@[expose] def wedgeWeightSupport (w : Fin m → ℤ) (k : ℕ) : Finset ℤ :=
  (Finset.univ.powersetCard k).image (fun s => ∑ i ∈ s, w i)

/-- The weight support consists exactly of weights with positive multiplicity. -/
@[simp] theorem mem_wedgeWeightSupport (w : Fin m → ℤ) (k : ℕ) (t : ℤ) :
    t ∈ wedgeWeightSupport w k ↔ 0 < wedgeMultiplicity w k t := by
  simp [wedgeWeightSupport, wedgeMultiplicity_pos_iff, Finset.mem_powersetCard]

/-- As a function of the total weight, the exterior-power multiplicity has finite support. -/
theorem finite_support_wedgeMultiplicity (w : Fin m → ℤ) (k : ℕ) :
    (Function.support (wedgeMultiplicity w k)).Finite :=
  (wedgeWeightSupport w k).finite_toSet.subset fun t ht =>
    (mem_wedgeWeightSupport w k t).mpr (Nat.pos_of_ne_zero ht)

/-- The sum of the weight multiplicities in degree `k` is the dimension of the exterior power. -/
theorem sum_wedgeMultiplicity (w : Fin m → ℤ) (k : ℕ) :
    ∑ t ∈ wedgeWeightSupport w k, wedgeMultiplicity w k t = m.choose k := by
  rw [wedgeWeightSupport]
  simp only [wedgeMultiplicity, ← Finset.card_eq_sum_card_image, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]

/-- Adding a constant to every weight translates each degree-`k` sum by `k * b`. -/
theorem wedgeMultiplicity_add (w : Fin m → ℤ) (k : ℕ) (t b : ℤ) :
    wedgeMultiplicity (fun i => w i + b) k (t + (k : ℤ) * b) = wedgeMultiplicity w k t := by
  unfold wedgeMultiplicity
  congr 1
  apply Finset.filter_congr
  intro s hs
  simp [Finset.sum_add_distrib, (Finset.mem_powersetCard.mp hs).2]

/-- Taking complements identifies degree `m-k`, weight `t`, with degree `k` and
weight equal to the total weight minus `t`. -/
theorem wedgeMultiplicity_compl (w : Fin m → ℤ) {k : ℕ} (hk : k ≤ m) (t : ℤ) :
    wedgeMultiplicity w (m - k) t = wedgeMultiplicity w k ((∑ i, w i) - t) := by
  unfold wedgeMultiplicity
  have h (s : Finset (Fin m)) :
      s ∈ (Finset.univ.powersetCard (m - k)).filter (fun s => ∑ i ∈ s, w i = t) ↔
      sᶜ ∈ (Finset.univ.powersetCard k).filter (fun s => ∑ i ∈ s, w i = (∑ i, w i) - t) := by
    have hcard : s.card ≤ m := by simpa using s.card_le_univ
    have hsum := s.sum_add_sum_compl w
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.card_compl, Fintype.card_fin]
    omega
  refine Finset.card_bij' (fun s _ => sᶜ) (fun s _ => sᶜ) ?_ ?_ ?_ ?_
  · exact fun s hs => (h s).mp hs
  · exact fun s hs => (h sᶜ).mpr (by simpa using hs)
  · exact fun s _ => compl_compl s
  · exact fun s _ => compl_compl s

/-- In degree zero only the empty subset contributes, with weight zero. -/
@[simp] theorem wedgeMultiplicity_zero (w : Fin m → ℤ) (t : ℤ) :
    wedgeMultiplicity w 0 t = if t = 0 then 1 else 0 := by
  by_cases h : t = 0 <;>
    simp [wedgeMultiplicity, Finset.powersetCard_zero, Finset.filter_singleton, h, eq_comm]

/-- In top degree the only weight is the sum of all weights. -/
@[simp] theorem wedgeMultiplicity_top (w : Fin m → ℤ) (t : ℤ) :
    wedgeMultiplicity w m t = if t = ∑ i, w i then 1 else 0 := by
  have h : (Finset.univ : Finset (Fin m)).powersetCard m = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin m))
  by_cases ht : t = ∑ i, w i <;> simp [wedgeMultiplicity, h, Finset.filter_singleton, ht, eq_comm]

/-- Above top degree no subset contributes. -/
theorem wedgeMultiplicity_eq_zero_of_lt (w : Fin m → ℤ) {k : ℕ} (hk : m < k) (t : ℤ) :
    wedgeMultiplicity w k t = 0 := by
  have h : (Finset.univ : Finset (Fin m)).powersetCard k = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simpa using hk)
  simp [wedgeMultiplicity, h]

/-- When all weights vanish, every degree-`k` subset contributes to weight zero. -/
@[simp] theorem wedgeMultiplicity_zero_weights (m k : ℕ) :
    wedgeMultiplicity (fun _ : Fin m => 0) k 0 = m.choose k := by
  simp [wedgeMultiplicity, Finset.card_powersetCard]

end TauCeti
