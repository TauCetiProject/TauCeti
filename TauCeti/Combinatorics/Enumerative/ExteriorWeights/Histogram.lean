/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.ExteriorWeights.Basic
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Powerset

/-!
# Weight histograms for exterior powers

Partition the indices by their integer weights. If a subset selects `h j`
indices of weight `j`, it has one independent choice of a subset of that
cardinality in each fiber. Summing the resulting products of binomial
coefficients gives the multiplicity of an exterior weight. This is the binomial
count in Lawrence and Sawin, *The Shafarevich conjecture for hypersurfaces in
abelian varieties*, Lemma 3.14, equation (3), and Appendix B, equation (10).
-/

public section

namespace TauCeti

variable {m : ℕ}

/-- The distinct weights among the indexed entries of a weight list. -/
def weightSupport (w : Fin m → ℤ) : Finset ℤ := Finset.univ.image w

/-- The support is the image of the whole index set under the weight function. -/
theorem weightSupport_def (w : Fin m → ℤ) : weightSupport w = Finset.univ.image w := by
  rfl

/-- A weight belongs to the support exactly when some index carries it. -/
@[simp] theorem mem_weightSupport {w : Fin m → ℤ} {j : ℤ} :
    j ∈ weightSupport w ↔ ∃ i, w i = j := by
  simp [weightSupport_def]

/-- All indices carrying a given weight. -/
def weightFiber (w : Fin m → ℤ) (j : weightSupport w) : Finset (Fin m) :=
  Finset.univ.filter fun i => w i = j.val

/-- The fiber is the subset of all indices whose weights equal its label. -/
theorem weightFiber_def (w : Fin m → ℤ) (j : weightSupport w) :
    weightFiber w j = Finset.univ.filter fun i => w i = j.val := by
  rfl

/-- Membership in a weight fiber is equality with the indexed weight. -/
@[simp] theorem mem_weightFiber {w : Fin m → ℤ} {j : weightSupport w} {i : Fin m} :
    i ∈ weightFiber w j ↔ w i = j.val := by
  simp [weightFiber_def]

/-- A histogram chooses an occupancy between zero and the size of each weight fiber. -/
abbrev WeightHistogram (w : Fin m → ℤ) :=
  (j : weightSupport w) → Fin ((weightFiber w j).card + 1)

private def weightPart (w : Fin m → ℤ) (s : Finset (Fin m)) (j : weightSupport w) :=
  s.filter fun i => w i = j.val

/-- The histogram of a subset records how many indices it selects at each weight. -/
def weightHistogram (w : Fin m → ℤ) (s : Finset (Fin m)) : WeightHistogram w := fun j =>
  ⟨(s.filter fun i => w i = j.val).card, Nat.lt_succ_of_le
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s)))⟩

/-- The occupancy of a subset at a weight is its number of selected indices of that weight. -/
@[simp] theorem weightHistogram_apply (w : Fin m → ℤ) (s : Finset (Fin m)) (j : weightSupport w) :
    (weightHistogram w s j : ℕ) = (s.filter fun i => w i = j.val).card := by
  rfl

private theorem weightHistogram_eq_card_weightPart (w : Fin m → ℤ) (s : Finset (Fin m))
    (j : weightSupport w) : (weightHistogram w s j : ℕ) = (weightPart w s j).card := by
  rw [weightHistogram_apply, weightPart]

private def indexWeight (w : Fin m → ℤ) (i : Fin m) : weightSupport w :=
  ⟨w i, mem_weightSupport.mpr ⟨i, rfl⟩⟩

private theorem indexWeight_eq_iff {w : Fin m → ℤ} {i : Fin m} {j : weightSupport w} :
    indexWeight w i = j ↔ w i = j.val :=
  Subtype.ext_iff

private theorem indexWeight_val (w : Fin m → ℤ) (i : Fin m) : (indexWeight w i).val = w i := rfl

-- Simplify both totals before individual occupancies expand to filtered cardinalities.
/-- The sum of the occupancies recovers the selected cardinality. -/
@[simp↓] theorem sum_weightHistogram (w : Fin m → ℤ) (s : Finset (Fin m)) :
    ∑ j, (weightHistogram w s j : ℕ) = s.card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter s Finset.univ (indexWeight w)
  simpa [weightHistogram_apply, indexWeight_eq_iff] using h

/-- Weighting each occupancy by its weight recovers the sum over the selected indices. -/
@[simp↓] theorem sum_weight_mul_weightHistogram (w : Fin m → ℤ) (s : Finset (Fin m)) :
    ∑ j, (weightHistogram w s j : ℤ) * j.val = ∑ i ∈ s, w i := by
  have h := Finset.sum_fiberwise_of_maps_to' (s := s) (t := Finset.univ) (g := indexWeight w)
    (fun i _ => Finset.mem_univ _) (fun j => j.val)
  simpa [weightHistogram_apply, indexWeight_eq_iff, indexWeight_val, nsmul_eq_mul] using h

private def joinWeightParts (w : Fin m → ℤ) (p : weightSupport w → Finset (Fin m)) :=
  Finset.univ.filter fun i => i ∈ p (indexWeight w i)

private theorem joinWeightParts_weightPart (w : Fin m → ℤ) (s : Finset (Fin m)) :
    joinWeightParts w (weightPart w s) = s := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).2).1
  · intro hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩

private theorem weightPart_joinWeightParts (w : Fin m → ℤ)
    (p : weightSupport w → Finset (Fin m)) (hp : ∀ j, p j ⊆ weightFiber w j) :
    weightPart w (joinWeightParts w p) = p := by
  funext j
  ext i
  simp only [weightPart, joinWeightParts, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hi, hj⟩
    rwa [indexWeight_eq_iff.mpr hj] at hi
  · intro hi
    have hj := mem_weightFiber.mp (hp j hi)
    exact ⟨by rwa [indexWeight_eq_iff.mpr hj], hj⟩

private theorem card_histogram_fiber (w : Fin m → ℤ) (h : WeightHistogram w) :
    (Finset.univ.filter fun s => weightHistogram w s = h).card =
      ∏ j, (weightFiber w j).card.choose (h j) := by
  classical
  let choices := Fintype.piFinset fun j => (weightFiber w j).powersetCard (h j)
  calc
    _ = choices.card := by
      apply Finset.card_bij (fun s _ => weightPart w s)
      · intro s hs
        have hh := (Finset.mem_filter.mp hs).2
        exact Fintype.mem_piFinset.mpr fun j =>
          Finset.mem_powersetCard.mpr
            ⟨Finset.filter_subset_filter _ (Finset.subset_univ s),
              (weightHistogram_eq_card_weightPart w s j).symm.trans
                (congrArg Fin.val (congrFun hh j))⟩
      · intro s _ t _ heq
        simpa only [joinWeightParts_weightPart] using congrArg (joinWeightParts w) heq
      · intro p hp
        have hmem := Fintype.mem_piFinset.mp hp
        have heq := weightPart_joinWeightParts w p fun j => (Finset.mem_powersetCard.mp (hmem j)).1
        refine ⟨joinWeightParts w p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
        funext j
        apply Fin.ext
        rw [weightHistogram_eq_card_weightPart, heq]
        exact (Finset.mem_powersetCard.mp (hmem j)).2
    _ = _ := by simp [choices]

/-- Every bounded histogram is realized by a subset of indices. -/
theorem exists_weightHistogram_eq (w : Fin m → ℤ) (u : WeightHistogram w) :
    ∃ s, weightHistogram w s = u := by
  classical
  have hpos : 0 < ∏ j, (weightFiber w j).card.choose (u j) :=
    Finset.prod_pos fun j _ => Nat.choose_pos (Nat.le_of_lt_succ (u j).isLt)
  rw [← card_histogram_fiber] at hpos
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  exact ⟨s, (Finset.mem_filter.mp hs).2⟩

/-- The multiplicity of weight `t` in the `k`th exterior power is the sum over histograms
of total occupancy `k` and total weight `t`. Each fiber contributes a binomial coefficient. -/
theorem wedgeMultiplicity_eq_sum_histograms (w : Fin m → ℤ) (k : ℕ) (t : ℤ) :
    wedgeMultiplicity w k t =
      ∑ h : WeightHistogram w with (∑ j, (h j : ℕ)) = k ∧ (∑ j, (h j : ℤ) * j.val) = t,
        ∏ j, (weightFiber w j).card.choose (h j) := by
  classical
  let H := Finset.univ.filter fun h : WeightHistogram w =>
    (∑ j, (h j : ℕ)) = k ∧ (∑ j, (h j : ℤ) * j.val) = t
  calc
    _ = (Finset.univ.filter fun s => weightHistogram w s ∈ H).card := by
      rw [wedgeMultiplicity_def]
      congr 1
      ext s
      simp only [H, Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.subset_univ, sum_weightHistogram, sum_weight_mul_weightHistogram]
    _ = ∑ h ∈ H, (Finset.univ.filter fun s => weightHistogram w s = h).card :=
      (Finset.sum_card_fiberwise_eq_card_filter Finset.univ H (weightHistogram w)).symm
    _ = _ := Finset.sum_congr rfl fun h _ => card_histogram_fiber w h

end TauCeti
