/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Subfunctor.Equalizer

/-!
# Equality locus of relative effective Cartier divisors

For each test scheme over `S`, pairs of relative effective Cartier divisors on the base change of
`X` form a functor. Equality of the two divisors defines a subfunctor, constructed as the
equalizer of the projection maps using Mathlib's general equalizer construction for subfunctors.
This is the moduli-level equality locus whose representability and scheme structure can be
studied when the divisor functor is represented. The incidence locus is a separate construction.
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The equality locus of pairs of relative effective Cartier divisors, constructed as the
equalizer of the two projections from the pair functor. -/
abbrev relativeEffectiveCartierEqualitySubfunctor :
    Subfunctor (FunctorToTypes.prod (relativeEffectiveCartierSubfunctor f).toFunctor
      (relativeEffectiveCartierSubfunctor f).toFunctor) :=
  Subfunctor.equalizer ((⊤ : Subfunctor (FunctorToTypes.prod
      (relativeEffectiveCartierSubfunctor f).toFunctor
      (relativeEffectiveCartierSubfunctor f).toFunctor)).ι ≫ FunctorToTypes.prod.fst)
    ((⊤ : Subfunctor (FunctorToTypes.prod (relativeEffectiveCartierSubfunctor f).toFunctor
      (relativeEffectiveCartierSubfunctor f).toFunctor)).ι ≫ FunctorToTypes.prod.snd)

/-- A pair lies in the equality locus exactly when its two divisors agree. -/
@[simp]
lemma mem_relativeEffectiveCartierEqualitySubfunctor_obj_iff
    {T : (Over S)ᵒᵖ} {p : (FunctorToTypes.prod (relativeEffectiveCartierSubfunctor f).toFunctor
      (relativeEffectiveCartierSubfunctor f).toFunctor).obj T} :
    p ∈ (relativeEffectiveCartierEqualitySubfunctor f).obj T ↔ p.1 = p.2 := by
  let A : Subfunctor (FunctorToTypes.prod (relativeEffectiveCartierSubfunctor f).toFunctor
    (relativeEffectiveCartierSubfunctor f).toFunctor) := ⊤
  simpa [relativeEffectiveCartierEqualitySubfunctor, A] using
    (Subfunctor.mem_equalizer_iff
      (A.ι ≫ FunctorToTypes.prod.fst)
      (A.ι ≫ FunctorToTypes.prod.snd)
      (⟨p, trivial⟩ : A.toFunctor.obj T))

end

end AlgebraicGeometry

end TauCeti
