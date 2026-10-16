/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Basic
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.ProperSubgraph
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Five-component genus-one forks

A minimal numerical type of genus one whose components form the fork
`0 - 1 - 2`, with leaves `3` and `4` attached to `2`, has precisely two possible
weight and multiplicity patterns. In the displayed order these are
`(2w, w, w, w, w)` with multiplicities `(m, 2m, 2m, m, m)`, and
`(w, 2w, 2w, 2w, 2w)` with multiplicities `(2m, 2m, 2m, m, m)`.

The classification records every component genus and the entire intersection matrix,
as well as the weights and multiplicities. The indexing equivalence is arbitrary, so the
result applies without any assumption on the type used to index the components.

The proper three-leaf-star classification
`TauCeti.NumericalType.exists_weight_intersection_star_four_eq` fixes the data on
components `1, 2, 3, 4`. The fibre relations determine the remaining edge and the
multiplicity vector.

## References

* [Stacks Project, Tag 0C8T, cases (23)--(24)](https://stacks.math.columbia.edu/tag/0C8T).
-/

public section

namespace TauCeti.NumericalType

open Finset Matrix

universe u

variable {T : NumericalType.{u}}

/-- Fibre relations for a five-component fork, after identifying its four equal weights
and its three simply laced edges. -/
private lemma fiveFork_multiplicity_relations (e : Fin 5 ≃ T.Component)
    (hself : ∀ i, T.intersection (e i) (e i) = -(2 * (T.weight (e i) : ℤ)))
    (hw : ∀ i : Fin 5, i ≠ 0 → (T.weight (e i) : ℤ) = T.weight (e 2))
    (ha : T.intersection (e 1) (e 2) = T.weight (e 2))
    (hb : T.intersection (e 2) (e 3) = T.weight (e 2))
    (hc : T.intersection (e 2) (e 4) = T.weight (e 2))
    (hz02 : T.intersection (e 0) (e 2) = 0)
    (hz03 : T.intersection (e 0) (e 3) = 0)
    (hz04 : T.intersection (e 0) (e 4) = 0)
    (hz13 : T.intersection (e 1) (e 3) = 0)
    (hz14 : T.intersection (e 1) (e 4) = 0)
    (hz34 : T.intersection (e 3) (e 4) = 0) :
    (T.multiplicity (e 2) : ℤ) = 2 * T.multiplicity (e 3) ∧
      (T.multiplicity (e 4) : ℤ) = T.multiplicity (e 3) ∧
      (T.multiplicity (e 1) : ℤ) = T.multiplicity (e 2) ∧
      (T.multiplicity (e 0) : ℤ) * T.intersection (e 0) (e 1) =
        T.multiplicity (e 2) * T.weight (e 2) ∧
      (T.multiplicity (e 1) : ℤ) * T.intersection (e 0) (e 1) =
        2 * T.multiplicity (e 0) * T.weight (e 0) := by
  have hr (i : Fin 5) := T.fiber_relation (e i)
  simp only [← e.sum_comp, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc] at hr
  have h₀ := hr 0
  have h₁ := hr 1
  have h₂ := hr 2
  have h₃ := hr 3
  have h₄ := hr 4
  simp only [hself, hz02, hz03, hz04, hz13, hz14, hz34, ha, hb, hc,
    T.intersection_comm (e 1) (e 0), T.intersection_comm (e 2) (e 0),
    T.intersection_comm (e 2) (e 1), T.intersection_comm (e 3) (e 0),
    T.intersection_comm (e 3) (e 1), T.intersection_comm (e 3) (e 2),
    T.intersection_comm (e 4) (e 0), T.intersection_comm (e 4) (e 1),
    T.intersection_comm (e 4) (e 2), T.intersection_comm (e 4) (e 3),
    hw 1 (by decide), hw 3 (by decide), hw 4 (by decide), mul_zero, add_zero,
    zero_add] at h₀ h₁ h₂ h₃ h₄
  have hne : (T.weight (e 2) : ℤ) ≠ 0 := by simp
  have hm₂ : (T.multiplicity (e 2) : ℤ) = 2 * T.multiplicity (e 3) :=
    mul_left_cancel₀ hne (by linear_combination h₃)
  have hm₄ : (T.multiplicity (e 4) : ℤ) = T.multiplicity (e 3) := by
    have : (2 * T.multiplicity (e 4) : ℤ) = 2 * T.multiplicity (e 3) :=
      mul_left_cancel₀ hne (by linear_combination h₃ - h₄)
    omega
  have hm₁ : (T.multiplicity (e 1) : ℤ) = T.multiplicity (e 2) := by
    have : (2 * T.multiplicity (e 1) : ℤ) = 2 * T.multiplicity (e 2) :=
      mul_left_cancel₀ hne (by linear_combination 2 * h₂ + h₃ + h₄)
    omega
  refine ⟨hm₂, hm₄, hm₁, ?_, ?_⟩
  · rw [hm₁] at h₁
    linear_combination h₁
  · linear_combination h₀

/-- **The five-component fork classification.** For a minimal genus-one numerical type,
the fork `0 - 1 - 2` with leaves `3, 4` at `2` has exactly the numerical data of cases
(23) or (24) of Stacks, Tag 0C8T. All component genera vanish. The equivalence `e`
preserves the displayed component labels. -/
theorem IsMinimal.exists_weight_multiplicity_intersection_eq_fiveFork
    (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1) (e : Fin 5 ≃ T.Component)
    (h01 : 0 < T.intersection (e 0) (e 1))
    (h12 : 0 < T.intersection (e 1) (e 2))
    (h23 : 0 < T.intersection (e 2) (e 3))
    (h24 : 0 < T.intersection (e 2) (e 4))
    (hz02 : T.intersection (e 0) (e 2) = 0)
    (hz03 : T.intersection (e 0) (e 3) = 0)
    (hz04 : T.intersection (e 0) (e 4) = 0) :
    (∀ i, T.genus (e i) = 0) ∧
      ∃ w m : ℕ+,
        ((∀ i, (T.weight (e i) : ℤ) = ![2 * (w : ℤ), w, w, w, w] i) ∧
          (∀ i, (T.multiplicity (e i) : ℤ) = ![(m : ℤ), 2 * m, 2 * m, m, m] i) ∧
          (∀ i j, T.intersection (e i) (e j) =
            !![-4 * (w : ℤ), 2 * w, 0, 0, 0;
               2 * w, -2 * w, w, 0, 0;
               0, w, -2 * w, w, w;
               0, 0, w, -2 * w, 0;
               0, 0, w, 0, -2 * w] i j)) ∨
        ((∀ i, (T.weight (e i) : ℤ) = ![(w : ℤ), 2 * w, 2 * w, 2 * w, 2 * w] i) ∧
          (∀ i, (T.multiplicity (e i) : ℤ) = ![2 * (m : ℤ), 2 * m, 2 * m, m, m] i) ∧
          (∀ i j, T.intersection (e i) (e j) =
            !![-2 * (w : ℤ), 2 * w, 0, 0, 0;
               2 * w, -4 * w, 2 * w, 0, 0;
               0, 2 * w, -4 * w, 2 * w, 2 * w;
               0, 0, 2 * w, -4 * w, 0;
               0, 0, 2 * w, 0, -4 * w] i j)) := by
  -- Minimality and genus one identify every component as a (-2)-index.
  have hcard : Fintype.card T.Component = 5 := by
    simpa using (Fintype.card_congr e).symm
  have h₂ := (T.isMinimal_and_arithmeticGenus_eq_one_iff (by omega)).mp ⟨hT, hg⟩
  have hself (i : Fin 5) := (T.isMinusTwoIndex_iff.mp (h₂ (e i))).2
  refine ⟨fun i ↦ (T.isMinusTwoIndex_iff.mp (h₂ (e i))).1, ?_⟩
  -- The proper star on the last four components is simply laced.
  obtain ⟨w, hw₂, hw₁, hw₃, hw₄, ha, hb, hc, hz13, hz14, hz34⟩ :=
    T.exists_weight_intersection_star_four_eq (by omega) (hself 2) (hself 1)
      (hself 3) (hself 4) (e.injective.ne (by decide))
      (e.injective.ne (by decide)) (e.injective.ne (by decide))
      (by simpa only [T.intersection_comm] using h12) h23 h24
  have hw (i : Fin 5) (hi : i ≠ 0) : (T.weight (e i) : ℤ) = T.weight (e 2) := by
    fin_cases i
    · exact (hi rfl).elim
    · exact hw₁.trans hw₂.symm
    · rfl
    · exact hw₃.trans hw₂.symm
    · exact hw₄.trans hw₂.symm
  have ha' : T.intersection (e 1) (e 2) = T.weight (e 2) := by
    rw [T.intersection_comm]; exact ha.trans hw₂.symm
  obtain ⟨hm₂, hm₄, hm₁, he₁, he₀⟩ := fiveFork_multiplicity_relations e hself hw ha'
    (hb.trans hw₂.symm) (hc.trans hw₂.symm) hz02 hz03 hz04 hz13 hz14 hz34
  -- Of the five possible endpoint weight ratios, the fibre relations leave only two.
  obtain ⟨v, hv⟩ := T.exists_weight_intersection_triple_mem (by omega)
    (hself 0) (hself 1) h01
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hv
  have hmpos : (0 : ℤ) < T.multiplicity (e 2) := by simp
  have hvpos : (0 : ℤ) < v := by simp
  have hcases :
      ((T.weight (e 0) : ℤ) = 2 * w ∧ T.intersection (e 0) (e 1) = 2 * w ∧
        (T.multiplicity (e 0) : ℤ) = T.multiplicity (e 3)) ∨
      ((w : ℤ) = 2 * T.weight (e 0) ∧ T.intersection (e 0) (e 1) = w ∧
        (T.multiplicity (e 0) : ℤ) = T.multiplicity (e 2)) := by
    rcases hv with ⟨hv₀, hv₁, hvₐ⟩ | ⟨hv₀, hv₁, hvₐ⟩ | ⟨hv₀, hv₁, hvₐ⟩ |
      ⟨hv₀, hv₁, hvₐ⟩ | ⟨hv₀, hv₁, hvₐ⟩
    · exfalso
      nlinarith only [he₀, he₁, hm₁, hw₂, hw₁, hv₀, hv₁, hvₐ, hmpos, hvpos]
    · right
      refine ⟨by omega, by omega, ?_⟩
      nlinarith only [he₁, hw₂, hw₁, hv₁, hvₐ, hvpos, hm₂]
    · left
      refine ⟨by omega, by omega, ?_⟩
      nlinarith only [he₁, hw₂, hw₁, hv₁, hvₐ, hvpos, hm₂]
    · exfalso
      nlinarith only [he₀, he₁, hm₁, hw₂, hw₁, hv₀, hv₁, hvₐ, hmpos, hvpos]
    · exfalso
      nlinarith only [he₀, he₁, hm₁, hw₂, hw₁, hv₀, hv₁, hvₐ, hmpos, hvpos]
  -- Assemble the full numerical data in each case, retaining the given labels.
  rcases hcases with ⟨hw₀, ha₀, hm₀⟩ | ⟨hw₀, ha₀, hm₀⟩
  · refine ⟨w, T.multiplicity (e 3), Or.inl ⟨?_, ?_, ?_⟩⟩
    · intro i
      fin_cases i
      · exact hw₀
      · exact hw₁
      · exact hw₂
      · exact hw₃
      · exact hw₄
    · intro i
      fin_cases i
      · exact hm₀
      · exact hm₁.trans hm₂
      · exact hm₂
      · rfl
      · exact hm₄
    · intro i j
      fin_cases i <;> fin_cases j <;>
        norm_num [hself, hw₁, hw₂, hw₃, hw₄] <;>
        first | omega | rw [T.intersection_comm]; omega
  · refine ⟨T.weight (e 0), T.multiplicity (e 3), Or.inr ⟨?_, ?_, ?_⟩⟩
    · intro i
      fin_cases i
      · rfl
      · exact hw₁.trans hw₀
      · exact hw₂.trans hw₀
      · exact hw₃.trans hw₀
      · exact hw₄.trans hw₀
    · intro i
      fin_cases i
      · exact hm₀.trans hm₂
      · exact hm₁.trans hm₂
      · exact hm₂
      · rfl
      · exact hm₄
    · intro i j
      fin_cases i <;> fin_cases j <;>
        norm_num [hself, hw₁, hw₂, hw₃, hw₄] <;>
        first | omega | rw [T.intersection_comm]; omega

end TauCeti.NumericalType
