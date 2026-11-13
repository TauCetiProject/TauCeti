/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import TauCeti.Algebra.Module.PseudoCoherent.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Faithfully flat descent of module finite presentation and rank

Finite presentation descends from the scalar extension of a module. For finite flat modules,
a constant rank at all primes of a faithfully flat algebra descends to the base ring.
These are the module-theoretic inputs to descent of finite locally free sheaves; effectiveness
of sheaf descent and the identification of pullback sections are separate constructions.

## Main results

* `Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`
* `Module.rankAtStalk_eq_of_rankAtStalk_tensorProduct_eq`
-/

public section

open TensorProduct

variable {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]

/-- Finite presentation of modules descends along faithfully flat maps. -/
lemma Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
    [Module.FaithfullyFlat A B] [Module.FinitePresentation B (B ⊗[A] M)] :
    Module.FinitePresentation A M := by
  exact TauCeti.Huber.IsPseudoCoherentOver.one_iff.mp
    (TauCeti.Huber.IsPseudoCoherentOver.of_baseChange B
      (TauCeti.Huber.IsPseudoCoherentOver.one_iff.mpr inferInstance))

/-- Constant local rank descends along faithfully flat maps: if `B ⊗[A] M` has rank `r`
at every prime of `B`, then `M` has rank `r` at every prime of `A`. -/
lemma Module.rankAtStalk_eq_of_rankAtStalk_tensorProduct_eq [Module.FaithfullyFlat A B]
    [Module.Finite A M] [Module.Flat A M] {r : ℕ}
    (h : ∀ q : PrimeSpectrum B, Module.rankAtStalk (B ⊗[A] M) q = r) (p : PrimeSpectrum A) :
    Module.rankAtStalk M p = r := by
  obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) p
  rw [← Module.rankAtStalk_baseChange, h]
