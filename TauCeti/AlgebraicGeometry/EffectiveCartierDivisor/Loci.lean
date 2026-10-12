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
The inclusion satisfies equality of the projections, and every family satisfying that equality
factors uniquely through the locus.
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
def relativeEffectiveCartierEqualitySubfunctor :
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

namespace relativeEffectiveCartierEqualitySubfunctor

/-- The two divisor projections agree on the equality locus. -/
@[reassoc]
lemma condition :
    (relativeEffectiveCartierEqualitySubfunctor f).ι ≫ FunctorToTypes.prod.fst =
      (relativeEffectiveCartierEqualitySubfunctor f).ι ≫ FunctorToTypes.prod.snd := by
  ext T p
  exact (mem_relativeEffectiveCartierEqualitySubfunctor_obj_iff f).mp p.property

variable {G : (Over S)ᵒᵖ ⥤ Type u}
  (φ : G ⟶ FunctorToTypes.prod (relativeEffectiveCartierSubfunctor f).toFunctor
    (relativeEffectiveCartierSubfunctor f).toFunctor)
  (h : φ ≫ FunctorToTypes.prod.fst = φ ≫ FunctorToTypes.prod.snd)

/-- A family of pairs with equal divisors factors through the equality locus. -/
def lift : G ⟶ (relativeEffectiveCartierEqualitySubfunctor f).toFunctor :=
  Subfunctor.lift φ (by
    intro T p hp
    obtain ⟨x, rfl⟩ := hp
    apply (mem_relativeEffectiveCartierEqualitySubfunctor_obj_iff f).mpr
    simpa using ConcreteCategory.congr_hom (congr_app h T) x)

/-- Composing the lift with the inclusion recovers the original family of pairs. -/
@[reassoc (attr := simp)]
lemma lift_ι : lift f φ h ≫ (relativeEffectiveCartierEqualitySubfunctor f).ι = φ := by
  exact Subfunctor.lift_ι _ _

/-- The lift is the unique factorization of the family through the equality locus. -/
lemma lift_unique (ψ : G ⟶ (relativeEffectiveCartierEqualitySubfunctor f).toFunctor)
    (hψ : ψ ≫ (relativeEffectiveCartierEqualitySubfunctor f).ι = φ) :
    ψ = lift f φ h := by
  exact (cancel_mono (relativeEffectiveCartierEqualitySubfunctor f).ι).mp
    (hψ.trans (lift_ι f φ h).symm)

end relativeEffectiveCartierEqualitySubfunctor

end

end AlgebraicGeometry

end TauCeti
