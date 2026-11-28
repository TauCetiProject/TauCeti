/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Padics.Complex.Basic
import TauCeti.RingTheory.Perfectoid.Cyclotomic.SpecializationKernel
import TauCeti.RingTheory.Perfectoid.IsAlgClosed
import TauCeti.RingTheory.Perfectoid.Padic

/-!
# Checks for the infinite Witt specialization kernel

For any complete algebraically closed ultrametric field `C` with `‖p‖ < 1` (and in particular for
`ℂ_p`), `TauCeti.Perfectoid.isPerfectoidTateRing_of_isAlgClosed` synthesizes the perfectoid Tate
ring structure used by
`TauCeti.WittVector.span_cyclotomicMu_eq_of_isPrimitiveRoot_powerBoundedSubring`.
-/

open TauCeti.Huber TauCeti.Perfectoid TauCeti.WittVector

namespace TauCeti.Examples

variable (p : ℕ) [Fact p.Prime]

example {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [IsAlgClosed C] [hpC : Fact (‖(p : C)‖ < 1)] [Fact ¬IsUnit (p : powerBoundedSubring C)] :
    haveI : IsPerfectoidTateRing p C := isPerfectoidTateRing_of_isAlgClosed hpC.out
    ∀ {ε ε' : PreTilt (powerBoundedSubring C) p},
      IsPrimitiveRoot
        (((_root_.frobeniusEquiv (PreTilt (powerBoundedSubring C) p) p).symm ε).untilt) p →
      IsPrimitiveRoot
        (((_root_.frobeniusEquiv (PreTilt (powerBoundedSubring C) p) p).symm ε').untilt) p →
      Ideal.span {cyclotomicMu p ε} = Ideal.span {cyclotomicMu p ε'} := by
  have : IsPerfectoidTateRing p C := isPerfectoidTateRing_of_isAlgClosed hpC.out
  intro ε ε' hζ hζ'
  exact span_cyclotomicMu_eq_of_isPrimitiveRoot_powerBoundedSubring hζ hζ'

example [Fact ¬IsUnit (p : powerBoundedSubring ℂ_[p])]
    {ε ε' : PreTilt (powerBoundedSubring ℂ_[p]) p}
    (hζ : IsPrimitiveRoot
      (((_root_.frobeniusEquiv (PreTilt (powerBoundedSubring ℂ_[p]) p) p).symm ε).untilt) p)
    (hζ' : IsPrimitiveRoot
      (((_root_.frobeniusEquiv (PreTilt (powerBoundedSubring ℂ_[p]) p) p).symm ε').untilt) p) :
    Ideal.span {cyclotomicMu p ε} = Ideal.span {cyclotomicMu p ε'} :=
  span_cyclotomicMu_eq_of_isPrimitiveRoot_powerBoundedSubring hζ hζ'

end TauCeti.Examples
