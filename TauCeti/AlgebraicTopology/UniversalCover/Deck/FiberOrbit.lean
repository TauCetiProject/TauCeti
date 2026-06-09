/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import TauCeti.AlgebraicTopology.UniversalCover.Deck.FiberTransport
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular

/-!
# Deck orbits on fibres

This file packages the quotient of a single fibre by the restricted deck action. Mathlib
already provides the generic orbit quotient `MulAction.orbitRel.Quotient`; the declarations
here are the deck-specific spelling and transport API needed by the universal-covers roadmap
when pointed covers are compared with unpointed covers.

For a map `p : E → B` and a base point `b : B`, `Deck.FiberOrbitQuotient p b` is the set of
orbits of the action of `Deck p` on the fibre `p ⁻¹' {b}`. An over-base homeomorphism
identifies the corresponding quotients by transporting fibre points and conjugating deck
transformations. Regularity of the deck action is equivalently surjectivity of `p` together
with each of these fibre-orbit quotients being a subsingleton.

## Main declarations

* `TauCeti.Deck.FiberOrbitQuotient`: the deck-orbit quotient of one fibre.
* `TauCeti.Deck.fiberOrbitClass`: the quotient map from a fibre to its deck orbit.
* `TauCeti.Deck.fiberOrbitQuotientEquiv`: fibre-orbit quotients are invariant under an
  over-base homeomorphism.
* `TauCeti.Deck.isRegular_iff_surjective_subsingleton_fiberOrbitQuotient`: regularity is
  surjectivity plus subsingleton fibre-orbit quotients.

## References

This supplies a bookkeeping prerequisite for the Tau Ceti universal-covers roadmap, Stage 2:
the pointed/unpointed connected-cover correspondence records how chosen lifts vary up to the
deck action, and regular covers are exactly those whose deck action is transitive on fibres.
-/

namespace TauCeti

namespace Deck

variable {E F G B : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
  {p : E → B} {q : F → B} {r : G → B} {b : B}

/-- The quotient of the fibre over `b` by the restricted action of the deck group. -/
abbrev FiberOrbitQuotient (p : E → B) (b : B) : Type _ :=
  MulAction.orbitRel.Quotient (Deck p) (p ⁻¹' {b})

/-- The deck orbit class of a point in one fibre. -/
def fiberOrbitClass (e : p ⁻¹' {b}) : FiberOrbitQuotient p b :=
  Quotient.mk'' e

/-- The deck-orbit quotient map sends a fibre point to its own class. -/
@[simp]
lemma fiberOrbitClass_eq_mk (e : p ⁻¹' {b}) :
    fiberOrbitClass e = (Quotient.mk'' e : FiberOrbitQuotient p b) :=
  rfl

/-- Two fibre points have the same deck-orbit class exactly when the first belongs to the
deck orbit of the second. -/
lemma fiberOrbitClass_eq_iff_mem_orbit (e e' : p ⁻¹' {b}) :
    fiberOrbitClass e = fiberOrbitClass e' ↔ e ∈ MulAction.orbit (Deck p) e' := by
  exact Quotient.eq''.trans MulAction.orbitRel_apply

/-- A deck transform of a fibre point has the same deck-orbit class. -/
@[simp]
lemma fiberOrbitClass_smul (φ : Deck p) (e : p ⁻¹' {b}) :
    fiberOrbitClass (φ • e) = fiberOrbitClass e := by
  rw [fiberOrbitClass_eq_iff_mem_orbit]
  exact MulAction.mem_orbit _ φ

/-- Membership in the orbit represented by a fibre-orbit class. -/
lemma mem_orbit_fiberOrbitClass_iff (e e' : p ⁻¹' {b}) :
    e' ∈ MulAction.orbitRel.Quotient.orbit (fiberOrbitClass e) ↔
      fiberOrbitClass e' = fiberOrbitClass e := by
  exact MulAction.orbitRel.Quotient.mem_orbit

/-- The fibre-orbit class of a deck transform of a point is the original class, in the
orientation useful for rewriting hypotheses. -/
lemma fiberOrbitClass_eq_of_mem_orbit {e e' : p ⁻¹' {b}}
    (h : e' ∈ MulAction.orbit (Deck p) e) :
    fiberOrbitClass e' = fiberOrbitClass e :=
  (fiberOrbitClass_eq_iff_mem_orbit e' e).mpr h

/-- An over-base homeomorphism identifies deck-orbit quotients of corresponding fibres. -/
def fiberOrbitQuotientEquiv (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (b : B) :
    FiberOrbitQuotient p b ≃ FiberOrbitQuotient q b where
  toFun :=
    Quotient.map' (fiberMap h hpq b) fun e e' hee' => by
      rw [MulAction.orbitRel_apply] at hee' ⊢
      exact (mem_orbit_fiberMap_iff h hpq e' e).mpr hee'
  invFun :=
    Quotient.map' (fiberMap h.symm (map_symm_eq_of_map_eq h hpq) b) fun f f' hff' => by
      rw [MulAction.orbitRel_apply] at hff' ⊢
      exact (mem_orbit_fiberMap_iff h.symm (map_symm_eq_of_map_eq h hpq) f' f).mpr hff'
  left_inv := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro e
    change Quotient.mk'' ((fiberMap h.symm (map_symm_eq_of_map_eq h hpq) b)
        (fiberMap h hpq b e)) = Quotient.mk'' e
    have heq :
        (fiberMap h.symm (map_symm_eq_of_map_eq h hpq) b) (fiberMap h hpq b e) = e := by
      ext
      simp
    exact congrArg Quotient.mk'' heq
  right_inv := by
    intro y
    refine Quotient.inductionOn' y ?_
    intro f
    change Quotient.mk'' ((fiberMap h hpq b)
        (fiberMap h.symm (map_symm_eq_of_map_eq h hpq) b f)) = Quotient.mk'' f
    have heq :
        (fiberMap h hpq b) (fiberMap h.symm (map_symm_eq_of_map_eq h hpq) b f) = f := by
      ext
      simp
    exact congrArg Quotient.mk'' heq

/-- The induced equivalence on fibre-orbit quotients sends the class of a point to the class
of its transported point. -/
@[simp]
lemma fiberOrbitQuotientEquiv_apply (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (e : p ⁻¹' {b}) :
    fiberOrbitQuotientEquiv h hpq b (fiberOrbitClass e) =
      fiberOrbitClass (fiberMap h hpq b e) :=
  rfl

/-- The inverse induced equivalence on fibre-orbit quotients sends the class of a target
fibre point to the class of its inverse transport. -/
@[simp]
lemma fiberOrbitQuotientEquiv_symm_apply (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (f : q ⁻¹' {b}) :
    (fiberOrbitQuotientEquiv h hpq b).symm (fiberOrbitClass f) =
      fiberOrbitClass ((fiberMap h hpq b).symm f) := by
  rfl

/-- The identity over-base homeomorphism induces the identity on fibre-orbit quotients. -/
@[simp]
lemma fiberOrbitQuotientEquiv_refl :
    fiberOrbitQuotientEquiv (Homeomorph.refl E) (p := p) (q := p) (fun _ => rfl) b =
      Equiv.refl (FiberOrbitQuotient p b) := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro e
  rfl

/-- Fibre-orbit quotient equivalences compose as the underlying over-base homeomorphisms
compose. -/
@[simp]
lemma fiberOrbitQuotientEquiv_trans (h : E ≃ₜ F) (k : F ≃ₜ G)
    (hpq : ∀ e, q (h e) = p e) (hqr : ∀ f, r (k f) = q f) :
    fiberOrbitQuotientEquiv (h.trans k) (fun e => by rw [Homeomorph.trans_apply, hqr, hpq]) b =
      (fiberOrbitQuotientEquiv h hpq b).trans (fiberOrbitQuotientEquiv k hqr b) := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro e
  rfl

/-- Regularity can be read from the orbit quotients of the fibre actions: the map is
surjective, and each fibre has at most one deck orbit. -/
lemma isRegular_iff_surjective_subsingleton_fiberOrbitQuotient :
    IsRegular p ↔ Function.Surjective p ∧ ∀ b : B, Subsingleton (FiberOrbitQuotient p b) := by
  rw [isRegular_iff]
  refine and_congr_right fun _ => forall_congr' fun b => ?_
  exact MulAction.pretransitive_iff_subsingleton_quotient (Deck p) (p ⁻¹' {b})

namespace IsRegular

/-- A regular deck action has a subsingleton quotient of each fibre by deck orbits. -/
lemma subsingleton_fiberOrbitQuotient (hreg : IsRegular p) (b : B) :
    Subsingleton (FiberOrbitQuotient p b) :=
  (isRegular_iff_surjective_subsingleton_fiberOrbitQuotient.mp hreg).2 b

/-- For a regular deck action, all points in the same fibre have the same deck-orbit class. -/
lemma fiberOrbitClass_eq (hreg : IsRegular p) (e e' : p ⁻¹' {b}) :
    fiberOrbitClass e = fiberOrbitClass e' :=
  @Subsingleton.elim (FiberOrbitQuotient p b) (hreg.subsingleton_fiberOrbitQuotient b)
    (fiberOrbitClass e) (fiberOrbitClass e')

end IsRegular

end Deck

end TauCeti
