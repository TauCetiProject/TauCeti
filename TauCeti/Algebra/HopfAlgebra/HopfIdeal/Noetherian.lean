/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic

/-!
# Suprema of Hopf ideals in a noetherian Hopf algebra

In a Hopf algebra whose underlying ring is noetherian, every supremum of Hopf ideals is already
the supremum of finitely many of them. Contravariantly, for an affine algebraic group `G`, the
intersection of any family of closed subgroups of `G` is the intersection of finitely many
members of the family.

Hopf ideals have arbitrary suprema (`TauCeti.HopfIdeal.instCompleteSemilatticeSup`), and
constructions such as the largest Hopf ideal killed by a morphism are defined as suprema of
infinite sets. This file lets such a construction be replaced by a finite one.

## Main results

* `TauCeti.HopfIdeal.exists_finset_sup_eq_sSup`: in a noetherian Hopf algebra, the supremum of a
  set of Hopf ideals is the supremum of a finite subset.
-/

public section

namespace TauCeti.HopfIdeal

variable {R H : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- **Finiteness of suprema of Hopf ideals.** In a noetherian Hopf algebra the supremum of a set
of Hopf ideals is the supremum of a finite subset. -/
theorem exists_finset_sup_eq_sSup [IsNoetherianRing H] (S : Set (HopfIdeal R H)) :
    ∃ t : Finset (HopfIdeal R H), ↑t ⊆ S ∧ t.sup id = sSup S := by
  classical
  -- The underlying ideals of the finite partial suprema have a maximal member, and that member
  -- already contains every Hopf ideal of the set.
  obtain ⟨_, ⟨t, ht, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr ‹IsNoetherianRing H›
    ((fun t : Finset (HopfIdeal R H) ↦ (t.sup id).toIdeal) '' {t | ↑t ⊆ S})
    ⟨_, ∅, by simp, rfl⟩
  refine ⟨t, ht, le_antisymm (Finset.sup_le fun I hI ↦ le_sSup (ht hI)) (sSup_le fun I hI ↦ ?_)⟩
  have hle : t.sup id ≤ (insert I t).sup id := Finset.sup_mono (Finset.subset_insert I t)
  have heq := (toIdeal_le_toIdeal.mpr hle).eq_of_not_lt
    (hmax _ ⟨insert I t, by
      rw [Set.mem_ofPred_eq, Finset.coe_insert]
      exact Set.insert_subset hI ht, rfl⟩)
  exact (Finset.le_sup (f := id) (Finset.mem_insert_self I t)).trans
    (toIdeal_le_toIdeal.mp heq.ge)

end TauCeti.HopfIdeal
