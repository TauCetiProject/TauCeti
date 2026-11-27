/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal.Essential

/-!
# Annihilators and essential ideals in C⋆-algebras

C⋆-algebra annihilator theory for arbitrary two-sided ideals `I` (left/right symmetry,
`I ⊓ I.annihilator = ⊥`, double annihilator, and `I.IsClosedEssential ↔ I.IsEssential ↔
I.annihilator = ⊥`).

## Main declarations

* `TwoSidedIdeal.annihilator_eq_rightAnnihilator`, `TwoSidedIdeal.inf_annihilator_eq_bot`,
  `TwoSidedIdeal.isClosedEssential_iff_annihilator_eq_bot`.
-/

public section

open scoped CStarAlgebra

namespace TwoSidedIdeal

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- In any C⋆-algebra, the left and right annihilators of a two-sided ideal `I` coincide. -/
theorem annihilator_eq_rightAnnihilator (I : TwoSidedIdeal A) :
    I.annihilator = I.rightAnnihilator := by
  -- Passing to `I.topologicalClosure` preserves both annihilators and yields a `star`-closed ideal.
  have _ : IsClosed (I.topologicalClosure : Set A) := I.isClosed_topologicalClosure
  rw [← I.annihilator_topologicalClosure, ← I.rightAnnihilator_topologicalClosure]
  exact annihilator_eq_rightAnnihilator_of_star_mem
    fun _ => I.topologicalClosure.star_mem_of_isClosed

theorem mem_annihilator_iff_mul_eq_zero_right {I : TwoSidedIdeal A} {a : A} :
    a ∈ I.annihilator ↔ ∀ x ∈ I, x * a = 0 := by
  rw [I.annihilator_eq_rightAnnihilator, mem_rightAnnihilator]

/-- Every two-sided ideal of a C⋆-algebra has trivial intersection with its annihilator. -/
@[simp]
theorem inf_annihilator_eq_bot (I : TwoSidedIdeal A) : I ⊓ I.annihilator = ⊥ := by
  have _ : IsClosed (I.topologicalClosure : Set A) := I.isClosed_topologicalClosure
  refine le_bot_iff.mp ((inf_le_inf_right I.annihilator I.le_topologicalClosure).trans ?_)
  rw [← I.annihilator_topologicalClosure,
    inf_annihilator fun _ => I.topologicalClosure.star_mem_of_isClosed]

@[simp]
theorem annihilator_inf_eq_bot (I : TwoSidedIdeal A) : I.annihilator ⊓ I = ⊥ := by
  rw [inf_comm, I.inf_annihilator_eq_bot]

@[simp]
theorem inf_rightAnnihilator_eq_bot (I : TwoSidedIdeal A) : I ⊓ I.rightAnnihilator = ⊥ := by
  rw [← I.annihilator_eq_rightAnnihilator, I.inf_annihilator_eq_bot]

@[simp]
theorem rightAnnihilator_inf_eq_bot (I : TwoSidedIdeal A) : I.rightAnnihilator ⊓ I = ⊥ := by
  rw [inf_comm, I.inf_rightAnnihilator_eq_bot]

/-- The topological closure of `I` is contained in its double annihilator. -/
theorem topologicalClosure_le_annihilator_annihilator (I : TwoSidedIdeal A) :
    I.topologicalClosure ≤ I.annihilator.annihilator := by
  have _ : IsClosed (I.topologicalClosure : Set A) := I.isClosed_topologicalClosure
  simpa only [I.annihilator_topologicalClosure] using
    le_annihilator_annihilator fun _ => I.topologicalClosure.star_mem_of_isClosed

@[simp]
theorem annihilator_annihilator_annihilator_of_cstar (I : TwoSidedIdeal A) :
    I.annihilator.annihilator.annihilator = I.annihilator :=
  (congrArg annihilator I.annihilator.annihilator_eq_rightAnnihilator).trans
    I.annihilator_rightAnnihilator_annihilator

/-- In a C⋆-algebra, a two-sided ideal `J` annihilates `I` if and only if `I ⊓ J = ⊥`. -/
theorem le_annihilator_iff_inf_eq_bot {I J : TwoSidedIdeal A} :
    J ≤ I.annihilator ↔ I ⊓ J = ⊥ :=
  ⟨fun h => le_bot_iff.mp ((inf_le_inf_left I h).trans I.inf_annihilator_eq_bot.le),
   le_annihilator_of_inf_eq_bot⟩

/-- A two-sided ideal of a C⋆-algebra is essential among closed ideals if and only if its left
annihilator is `⊥`. -/
theorem isClosedEssential_iff_annihilator_eq_bot {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ I.annihilator = ⊥ :=
  ⟨fun h => isClosedEssential_iff.mp h I.annihilator I.isClosed_annihilator
      I.inf_annihilator_eq_bot,
   isClosedEssential_of_annihilator_eq_bot⟩

theorem isClosedEssential_iff_rightAnnihilator_eq_bot {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ I.rightAnnihilator = ⊥ := by
  rw [isClosedEssential_iff_annihilator_eq_bot, I.annihilator_eq_rightAnnihilator]

/-- In a C⋆-algebra, essentiality among closed two-sided ideals and algebraic essentiality among all
two-sided ideals are equivalent. -/
theorem isClosedEssential_iff_isEssential {I : TwoSidedIdeal A} :
    I.IsClosedEssential ↔ I.IsEssential :=
  ⟨fun h => isEssential_of_annihilator_eq_bot
      (isClosedEssential_iff_annihilator_eq_bot.mp h),
   IsEssential.isClosedEssential⟩

theorem isEssential_iff_annihilator_eq_bot {I : TwoSidedIdeal A} :
    I.IsEssential ↔ I.annihilator = ⊥ := by
  rw [← isClosedEssential_iff_isEssential, isClosedEssential_iff_annihilator_eq_bot]

theorem isEssential_iff_rightAnnihilator_eq_bot {I : TwoSidedIdeal A} :
    I.IsEssential ↔ I.rightAnnihilator = ⊥ := by
  rw [isEssential_iff_annihilator_eq_bot, I.annihilator_eq_rightAnnihilator]

theorem IsClosedEssential.inf {I J : TwoSidedIdeal A}
    (hI : I.IsClosedEssential) (hJ : J.IsClosedEssential) : (I ⊓ J).IsClosedEssential :=
  isClosedEssential_iff_isEssential.mpr
    ((isClosedEssential_iff_isEssential.mp hI).inf (isClosedEssential_iff_isEssential.mp hJ))

@[simp]
theorem isClosedEssential_inf_iff {I J : TwoSidedIdeal A} :
    (I ⊓ J).IsClosedEssential ↔ I.IsClosedEssential ∧ J.IsClosedEssential :=
  ⟨fun h => ⟨h.mono inf_le_left, h.mono inf_le_right⟩, fun ⟨hI, hJ⟩ => hI.inf hJ⟩

@[simp]
theorem isClosedEssential_topologicalClosure_iff {I : TwoSidedIdeal A} :
    I.topologicalClosure.IsClosedEssential ↔ I.IsClosedEssential := by
  rw [isClosedEssential_iff_annihilator_eq_bot, isClosedEssential_iff_annihilator_eq_bot,
    I.annihilator_topologicalClosure]

@[simp]
theorem isEssential_topologicalClosure_iff {I : TwoSidedIdeal A} :
    I.topologicalClosure.IsEssential ↔ I.IsEssential := by
  rw [← isClosedEssential_iff_isEssential, ← isClosedEssential_iff_isEssential,
    isClosedEssential_topologicalClosure_iff]

/-- Pulling back along a ring equivalence between C⋆-algebras preserves and reflects
closed-essentiality. -/
@[simp]
theorem isClosedEssential_comap_iff {B E : Type*} [NonUnitalCStarAlgebra B]
    [EquivLike E A B] [NonUnitalRingHomClass E A B] (e : E) {I : TwoSidedIdeal B} :
    (I.comap e).IsClosedEssential ↔ I.IsClosedEssential := by
  rw [isClosedEssential_iff_isEssential, isClosedEssential_iff_isEssential, isEssential_comap_iff]

end NonUnitalCStarAlgebra

end TwoSidedIdeal
