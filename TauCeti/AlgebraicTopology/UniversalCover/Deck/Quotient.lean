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
* `TauCeti.Deck.IsRegular.orbitQuotientEquivBase`: for a regular deck action,
  `E / Deck p` is equivalent to the base.

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
              have hsmul : (φ⁻¹ : Deck p) • e' = φ.1.symm e' := rfl
              change (φ⁻¹ : Deck p) • e' = e
              exact hsmul.trans hinv⟩

/-- An over-base homeomorphism identifies the corresponding deck-orbit quotients. -/
def orbitQuotientEquiv (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) :
    MulAction.orbitRel.Quotient (Deck p) E ≃ MulAction.orbitRel.Quotient (Deck q) F where
  toFun := Quotient.map' h fun e e' hee' => by
    rw [MulAction.orbitRel_apply] at hee' ⊢
    rcases hee' with ⟨φ, hφ⟩
    refine ⟨conjMulEquiv h hpq φ, ?_⟩
    have hφ' : φ • e' = e := hφ
    rw [smul_eq_apply] at hφ'
    change (conjMulEquiv h hpq φ) • h e' = h e
    rw [smul_eq_apply, conjMulEquiv_apply_coe, h.symm_apply_apply, ← hφ']
  invFun := Quotient.map' h.symm fun f f' hff' => by
    rw [MulAction.orbitRel_apply] at hff' ⊢
    rcases hff' with ⟨ψ, hψ⟩
    refine ⟨(conjMulEquiv h hpq).symm ψ, ?_⟩
    have hψ' : ψ • f' = f := hψ
    rw [smul_eq_apply] at hψ'
    change ((conjMulEquiv h hpq).symm ψ) • h.symm f' = h.symm f
    rw [smul_eq_apply, conjMulEquiv_symm_apply_coe, h.apply_symm_apply, ← hψ']
  left_inv x := by
    induction x using Quotient.inductionOn' with
    | h e => simp [Quotient.map'_mk'']
  right_inv x := by
    induction x using Quotient.inductionOn' with
    | h f => simp [Quotient.map'_mk'']

/-- The over-base equivalence on orbit quotients evaluates on representatives by the
homeomorphism. -/
@[simp]
lemma orbitQuotientEquiv_mk (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e : E) :
    orbitQuotientEquiv h hpq
      (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) =
        (Quotient.mk'' (h e) : MulAction.orbitRel.Quotient (Deck q) F) :=
  rfl

/-- The inverse over-base equivalence on orbit quotients evaluates on representatives by the
inverse homeomorphism. -/
@[simp]
lemma orbitQuotientEquiv_symm_mk (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (f : F) :
    (orbitQuotientEquiv h hpq).symm
      (Quotient.mk'' f : MulAction.orbitRel.Quotient (Deck q) F) =
        (Quotient.mk'' (h.symm f) : MulAction.orbitRel.Quotient (Deck p) E) :=
  rfl

namespace IsRegular

/-- For a regular deck action, the map from deck-orbit quotient to the base is surjective. -/
lemma orbitQuotientToBase_surjective (hreg : IsRegular p) :
    Function.Surjective (orbitQuotientToBase p) :=
  Quotient.lift_surjective p _ hreg.1

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

/-- Transporting a regular deck action along an over-base homeomorphism is compatible with
the corresponding orbit-quotient equivalences. -/
lemma orbitQuotientEquivBase_conj (hreg : IsRegular p) (h : E ≃ₜ F)
    (hpq : ∀ e, q (h e) = p e) (x : MulAction.orbitRel.Quotient (Deck p) E) :
    (hreg.conj h hpq).orbitQuotientEquivBase
      (orbitQuotientEquiv h hpq x) = hreg.orbitQuotientEquivBase x := by
  induction x using Quotient.inductionOn' with
  | h e =>
      rw [orbitQuotientEquiv_mk, orbitQuotientEquivBase_mk, orbitQuotientEquivBase_mk]
      exact hpq e

/-- Representative form of compatibility between over-base homeomorphisms and the regular
orbit-quotient equivalences. -/
@[simp]
lemma orbitQuotientEquivBase_conj_mk (hreg : IsRegular p) (h : E ≃ₜ F)
    (hpq : ∀ e, q (h e) = p e) (f : F) :
    (hreg.conj h hpq).orbitQuotientEquivBase
      (Quotient.mk'' f : MulAction.orbitRel.Quotient (Deck q) F) =
        hreg.orbitQuotientEquivBase
          (Quotient.mk'' (h.symm f) : MulAction.orbitRel.Quotient (Deck p) E) := by
  rw [← orbitQuotientEquiv_symm_mk h hpq f,
    ← hreg.orbitQuotientEquivBase_conj h hpq ((orbitQuotientEquiv h hpq).symm
      (Quotient.mk'' f : MulAction.orbitRel.Quotient (Deck q) F)),
    (orbitQuotientEquiv h hpq).apply_symm_apply]

end IsRegular

end Deck

end TauCeti
