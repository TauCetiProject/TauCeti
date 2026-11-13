/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.Algebra.Module.FinitePresentation
import TauCeti.Algebra.Module.PseudoCoherent.Descent

/-!
# Faithfully flat descent of module finite presentation

A module is finitely presented if its scalar extension along a faithfully flat algebra is
finitely presented. This is degree-one pseudocoherence descent, and supplies the module input
to descent of finite locally free sheaves.
-/

public section

open TensorProduct

/-- Finite presentation of modules descends along faithfully flat maps. -/
lemma Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (B : Type*) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    [Module.FinitePresentation B (B ⊗[A] M)] : Module.FinitePresentation A M := by
  exact TauCeti.Huber.IsPseudoCoherentOver.one_iff.mp
    (TauCeti.Huber.IsPseudoCoherentOver.of_baseChange B
      (TauCeti.Huber.IsPseudoCoherentOver.one_iff.mpr inferInstance))
