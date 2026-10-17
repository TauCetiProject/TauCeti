/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Unramified.Section.Idempotent
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Henselian

/-!
# Tests for sections of unramified algebras

Finite split algebras supply nontrivial sections. The identity section includes the case of an
empty complementary component. The Jacobson-radical uniqueness theorem applies to henselian pairs;
agreement modulo a proper ideal not in the Jacobson radical need not determine a map.
-/

open TauCeti.Algebra.FormallyUnramified

namespace TauCeti

variable (R : Type*) [CommRing R]

-- A two-sheet split algebra has a section selecting its first sheet.
example : ∃ (e : Fin 2 → R) (_ : IsIdempotentElem e)
    (E : (Fin 2 → R) ≃ₐ[R] R × ((Fin 2 → R) ⧸ Ideal.span {e})),
    ∀ s, E s = (s 0, Ideal.Quotient.mk _ s) :=
  exists_algEquiv_prod_of_section R _ (Pi.evalAlgHom R (fun _ : Fin 2 ↦ R) 0)

-- The identity section has zero kernel, so its complementary component is empty.
example : ∃ e : R, IsIdempotentElem e ∧ e = 1 ∧ Ideal.span {1 - e} = ⊥ := by
  obtain ⟨e, he, hσe, _⟩ := exists_isIdempotentElem_ker_eq_span R R (AlgHom.id R R)
  have heq : e = 1 := hσe
  exact ⟨e, he, heq, by simp [heq]⟩

-- In particular, the zero ring is allowed as a base and as a section component.
example : ∃ e : Fin 2 → ZMod 1, IsIdempotentElem e ∧
    let _ := (Pi.evalAlgHom (ZMod 1) (fun _ : Fin 2 ↦ ZMod 1) 0).toRingHom.toAlgebra
    IsLocalization.Away e (ZMod 1) :=
  (exists_isIdempotentElem_isLocalizationAway (ZMod 1) _
    (Pi.evalAlgHom (ZMod 1) (fun _ : Fin 2 ↦ ZMod 1) 0)).imp
      (fun _ h ↦ ⟨h.1, h.2.2⟩)

-- Residue sections over a henselian pair have unique lifts, with no adic separation assumption.
example (J : Ideal R) [HenselianRing R J] {S : Type*} [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (f g : S →ₐ[R] R)
    (h : (Ideal.Quotient.mkₐ R J).comp f = (Ideal.Quotient.mkₐ R J).comp g) : f = g :=
  ext_of_quotient_eq R S J HenselianRing.jac h

-- A proper ideal is not enough: the second sheet can still move.
example [Nontrivial R] :
    let f : (Fin 2 → R) →ₐ[R] (Fin 2 → R) := AlgHom.id R _
    let g : (Fin 2 → R) →ₐ[R] (Fin 2 → R) :=
      (Algebra.ofId R _).comp (Pi.evalAlgHom R (fun _ : Fin 2 ↦ R) 0)
    let J := RingHom.ker (Pi.evalRingHom (fun _ : Fin 2 ↦ R) 0)
    J ≠ ⊤ ∧ (Ideal.Quotient.mkₐ R J).comp f = (Ideal.Quotient.mkₐ R J).comp g ∧ f ≠ g := by
  dsimp only
  refine ⟨RingHom.ker_ne_top _, ?_, ?_⟩
  · ext s
    apply Ideal.Quotient.eq.mpr
    simp
  · intro h
    have hval := congrArg (fun k : (Fin 2 → R) →ₐ[R] (Fin 2 → R) ↦
      k (fun i ↦ if i = 0 then 0 else 1) 1) h
    simp at hval

end TauCeti
