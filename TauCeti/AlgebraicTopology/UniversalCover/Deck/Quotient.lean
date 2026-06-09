/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular

/-!
# The orbit quotient of a regular deck action

For any map `p : E → B`, deck transformations preserve the value of `p`, so `p` factors
through the quotient of `E` by the orbit relation for the deck action. If the deck action is
regular, the induced map from the orbit quotient to the base is an equivalence.

This is algebraic bookkeeping for the universal-covers roadmap. Later quotient-cover and
regular-cover statements need to compare the base with the orbit space of the deck action,
but the basic equivalence only uses `Deck.IsRegular p`: surjectivity of `p` and transitivity
of the deck action on each fibre.

## Main declarations

* `TauCeti.Deck.orbitQuotientToBase`: the map `E / Deck p → B` induced by `p`.
* `TauCeti.Deck.orbitQuotientEquivBase`: for a regular deck action, `E / Deck p` is
  equivalent to the base.

## References

This supplies a prerequisite for the Tau Ceti universal-covers roadmap, Stage 2, especially
the regular-cover milestones where fibres are deck orbits and quotient covers are compared
with the original base.
-/

namespace TauCeti

namespace Deck

variable {E F B : Type*} [TopologicalSpace E] [TopologicalSpace F]
  {p : E → B} {q : F → B}

/-- Points in the same deck orbit have the same projection under `p`. -/
lemma eq_proj_of_orbitRel {e e' : E} (h : MulAction.orbitRel (Deck p) E e e') :
    p e = p e' := by
  rw [MulAction.orbitRel_apply] at h
  rcases h with ⟨φ, hφ⟩
  rw [← hφ]
  simpa [smul_eq_apply] using map_proj φ e'

/-- The projection map factors through the quotient of `E` by deck orbits. -/
def orbitQuotientToBase (p : E → B) : MulAction.orbitRel.Quotient (Deck p) E → B :=
  Quotient.lift p fun _ _ h => eq_proj_of_orbitRel h

/-- The map from the deck-orbit quotient to the base evaluates on representatives by `p`. -/
@[simp]
lemma orbitQuotientToBase_mk (e : E) :
    orbitQuotientToBase p (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) =
      p e :=
  rfl

/-- The orbit quotient map is surjective exactly when the original projection map is
surjective. -/
lemma orbitQuotientToBase_surjective_iff :
    Function.Surjective (orbitQuotientToBase p) ↔ Function.Surjective p := by
  constructor
  · intro h b
    rcases h b with ⟨x, hx⟩
    revert hx
    refine Quotient.inductionOn' x ?_
    intro e hx
    exact ⟨e, by simpa [orbitQuotientToBase_mk] using hx⟩
  · intro hp b
    rcases hp b with ⟨e, he⟩
    exact ⟨Quotient.mk'' e, by simpa [orbitQuotientToBase_mk] using he⟩

/-- If deck orbits are exactly fibres of `p`, the orbit quotient map to the base is
injective. -/
lemma orbitQuotientToBase_injective_of_exists_apply_eq
    (hpoint : ∀ {e e' : E}, p e = p e' → ∃ φ : Deck p, φ.1 e = e') :
    Function.Injective (orbitQuotientToBase p) := by
  intro x y hxy
  induction x using Quotient.inductionOn' with
  | h e =>
      induction y using Quotient.inductionOn' with
      | h e' =>
          simp only [orbitQuotientToBase_mk] at hxy
          rcases hpoint hxy with ⟨φ, hφ⟩
          exact Quotient.sound
            ⟨φ⁻¹, by
              have hinv : φ.1.symm e' = e := by
                rw [← hφ, Homeomorph.symm_apply_apply]
              simpa [smul_eq_apply] using hinv⟩

namespace IsRegular

/-- For a regular deck action, the map from deck-orbit quotient to the base is surjective. -/
lemma orbitQuotientToBase_surjective (hreg : IsRegular p) :
    Function.Surjective (orbitQuotientToBase p) :=
  orbitQuotientToBase_surjective_iff.mpr hreg.1

/-- For a regular deck action, the map from deck-orbit quotient to the base is injective. -/
lemma orbitQuotientToBase_injective (hreg : IsRegular p) :
    Function.Injective (orbitQuotientToBase p) :=
  orbitQuotientToBase_injective_of_exists_apply_eq
    (isRegular_iff_exists_apply_eq.mp hreg).2

/-- A regular deck action identifies the quotient of the total space by deck orbits with the
base. -/
noncomputable def orbitQuotientEquivBase (hreg : IsRegular p) :
    MulAction.orbitRel.Quotient (Deck p) E ≃ B :=
  Equiv.ofBijective (orbitQuotientToBase p)
    ⟨hreg.orbitQuotientToBase_injective, hreg.orbitQuotientToBase_surjective⟩

/-- The equivalence from the deck-orbit quotient to the base evaluates on representatives by
the projection map. -/
@[simp]
lemma orbitQuotientEquivBase_mk (hreg : IsRegular p) (e : E) :
    hreg.orbitQuotientEquivBase
      (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) = p e :=
  rfl

/-- The inverse of the orbit-quotient equivalence chooses a deck orbit over the requested
base point. -/
@[simp]
lemma orbitQuotientEquivBase_apply_symm (hreg : IsRegular p)
    (x : MulAction.orbitRel.Quotient (Deck p) E) :
    hreg.orbitQuotientEquivBase.symm (hreg.orbitQuotientEquivBase x) = x :=
  hreg.orbitQuotientEquivBase.left_inv x

/-- Applying the orbit-quotient equivalence after its inverse gives back the base point. -/
@[simp]
lemma orbitQuotientEquivBase_symm_apply (hreg : IsRegular p) (b : B) :
    hreg.orbitQuotientEquivBase (hreg.orbitQuotientEquivBase.symm b) = b :=
  hreg.orbitQuotientEquivBase.right_inv b

/-- Transporting a regular deck action along an over-base homeomorphism is compatible with
the corresponding orbit-quotient equivalences. -/
lemma orbitQuotientEquivBase_conj (hreg : IsRegular p) (h : E ≃ₜ F)
    (hpq : ∀ e, q (h e) = p e) (f : F) :
    (hreg.conj h hpq).orbitQuotientEquivBase
      (Quotient.mk'' f : MulAction.orbitRel.Quotient (Deck q) F) =
        hreg.orbitQuotientEquivBase
          (Quotient.mk'' (h.symm f) : MulAction.orbitRel.Quotient (Deck p) E) := by
  rw [orbitQuotientEquivBase_mk, orbitQuotientEquivBase_mk]
  exact (map_symm_eq_of_map_eq h hpq f).symm

end IsRegular

end Deck

end TauCeti
