/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CentralIdempotent
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The regular module of a connected ring

A ring `A` is connected when its only central idempotents are `0` and `1`. The endomorphism ring of
a module isomorphic to the regular module of `A` is the opposite ring `Aᵐᵒᵖ`, so it is connected
too (`TauCeti.centralIdempotents_end_subset_of_linearEquiv`). Together with
`TauCeti.forall_or_forall_not_of_forall_hom_eq_zero`, this rules out Hom-orthogonal splittings of
the regular module of a connected ring into nonzero summands, the connectedness step in Auslander's
theorem on classes of bounded length closed under irreducible maps,
`TauCeti/Algebra/Category/ModuleCat/AuslanderReiten/Component.lean`.
-/

public section

open CategoryTheory

universe v w

namespace TauCeti

variable {A : Type v} [Ring A]

/-- **The regular module of a connected ring has a connected endomorphism ring.** If `A` has no
central idempotents other than `0` and `1`, neither has the endomorphism ring of a module `G`
isomorphic to the regular module of `A`. -/
theorem centralIdempotents_end_subset_of_linearEquiv (hA : centralIdempotents A ⊆ {0, 1})
    {G : ModuleCat.{w} A} (eG : A ≃ₗ[A] G) : centralIdempotents (End G) ⊆ {0, 1} := by
  intro x hx
  -- The endomorphism ring of `G` is `Aᵐᵒᵖ`.
  let φ : End G ≃+* Aᵐᵒᵖ := (ModuleCat.endRingEquiv G).trans
    (eG.symm.conjRingEquiv.trans (RingEquiv.moduleEndSelf A).symm)
  obtain ⟨hφi, hφc⟩ := mem_centralIdempotents.mp (φ.map_mem_centralIdempotents hx)
  have hunop : (φ x).unop ∈ centralIdempotents A := mem_centralIdempotents.mpr
    ⟨congrArg MulOpposite.unop hφi, Subring.mem_center_iff.mpr fun a ↦
      congrArg MulOpposite.unop (Subring.mem_center_iff.mp hφc (MulOpposite.op a)).symm⟩
  rcases hA hunop with h | h
  · exact Or.inl ((map_eq_zero_iff φ φ.injective).mp (MulOpposite.unop_eq_zero_iff _ |>.mp h))
  · exact Or.inr ((map_eq_one_iff φ φ.injective).mp
      (MulOpposite.unop_eq_one_iff _ |>.mp (Set.mem_singleton_iff.mp h)))

end TauCeti
