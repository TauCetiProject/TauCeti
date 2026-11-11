/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WeilRestriction.Smooth
public import Mathlib.RingTheory.Etale.Basic

import TauCeti.Algebra.TensorProduct.Ideal

/-!
# Unramifiedness and étaleness of Weil restrictions

Weil restriction along a finite projective algebra sends a finitely presented, formally unramified
algebra to a formally unramified algebra. Combined with the preservation of finite presentation
(`WeilRestriction.instFinitePresentation`) and formal smoothness
(`WeilRestriction.instFormallySmooth`), Weil restriction along a finite projective algebra
preserves unramifiedness, formal étaleness, and étaleness.

For uniqueness of infinitesimal lifts through `WeilRestriction.homEquiv`, tensoring a quotient map
by a square-zero ideal with the base algebra yields a homomorphism whose kernel is again
square-zero (`Ideal.ker_tensorProduct_map_id_quotient`).

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, §7.6, Proposition 5.
* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local II*, §1.5.9, p. 28.
-/

public section

open Algebra

namespace TauCeti.Algebra.WeilRestriction

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation B C]

/-- Weil restriction of a formally unramified finitely presented algebra along a finite
projective algebra is formally unramified. -/
instance instFormallyUnramified [FormallyUnramified B C] :
    FormallyUnramified A (WeilRestriction A B C) := by
  rw [FormallyUnramified.iff_comp_injective]
  intro T _ _ I hI f₁ f₂ h
  let q := Algebra.TensorProduct.lTensor (S := B) B (Ideal.Quotient.mkₐ A I)
  have hker_eq : RingHom.ker q.toRingHom = Ideal.rightTensorIdeal A B I :=
    Ideal.ker_tensorProduct_map_id_quotient (R := A) (A := B) I
  have hker : RingHom.ker q.toRingHom ^ 2 = ⊥ := by
    rw [hker_eq, Ideal.rightTensorIdeal_def, ← Ideal.map_pow, hI, Ideal.map_bot]
  apply (homEquiv A B C T).injective
  refine FormallyUnramified.lift_unique' q ⟨2, hker⟩ _ _ ?_
  rw [← homEquiv_comp, ← homEquiv_comp, h]

/-- Weil restriction of a finitely presented unramified algebra along a finite projective algebra
is unramified. -/
instance instUnramified [Unramified B C] : Unramified A (WeilRestriction A B C) where

/-- Weil restriction of a formally étale finitely presented algebra along a finite projective
algebra is formally étale. -/
instance instFormallyEtale [FormallyEtale B C] :
    FormallyEtale A (WeilRestriction A B C) :=
  .of_formallyUnramified_and_formallySmooth

/-- Weil restriction along a finite projective algebra preserves étaleness. -/
instance instEtale [Etale B C] : Etale A (WeilRestriction A B C) where

end TauCeti.Algebra.WeilRestriction
