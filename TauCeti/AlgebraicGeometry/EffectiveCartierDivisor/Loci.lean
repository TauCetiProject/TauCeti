/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Functor
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

/-- The functor whose points are pairs of relative effective Cartier divisors on the same base
change of `X` over `S`. -/
@[expose]
def relativeEffectiveCartierPairFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := (relativeEffectiveCartierSubfunctor f).toFunctor.obj T ×
    (relativeEffectiveCartierSubfunctor f).toFunctor.obj T
  map {T T'} φ := TypeCat.ofHom fun p =>
    ((relativeEffectiveCartierSubfunctor f).toFunctor.map φ p.1,
      (relativeEffectiveCartierSubfunctor f).toFunctor.map φ p.2)
  map_id T := by
    ext p <;> simp
  map_comp φ ψ := by
    ext p
    · apply Subtype.ext
      exact congrArg Subtype.val <| congrArg (fun g => g p.1)
        ((relativeEffectiveCartierSubfunctor f).toFunctor.map_comp φ ψ)
    · apply Subtype.ext
      exact congrArg Subtype.val <| congrArg (fun g => g p.2)
        ((relativeEffectiveCartierSubfunctor f).toFunctor.map_comp φ ψ)

/-- Pullback of a pair of divisors acts componentwise. -/
@[simp]
lemma relativeEffectiveCartierPairFunctor_map_apply {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (p : (relativeEffectiveCartierPairFunctor f).obj T) :
    (relativeEffectiveCartierPairFunctor f).map φ p =
      ((relativeEffectiveCartierSubfunctor f).toFunctor.map φ p.1,
        (relativeEffectiveCartierSubfunctor f).toFunctor.map φ p.2) := rfl

/-- The first projection from the functor of pairs of relative effective Cartier divisors. -/
@[expose]
def relativeEffectiveCartierPairFst : relativeEffectiveCartierPairFunctor f ⟶
    (relativeEffectiveCartierSubfunctor f).toFunctor where
  app T := TypeCat.ofHom Prod.fst
  naturality _ _ _ := by ext p; apply Subtype.ext; rfl

/-- The first projection sends a pair to its first divisor. -/
@[simp]
lemma relativeEffectiveCartierPairFst_app_apply {T : (Over S)ᵒᵖ}
    (p : (relativeEffectiveCartierPairFunctor f).obj T) :
    (relativeEffectiveCartierPairFst f).app T p = p.1 := rfl

/-- The second projection from the functor of pairs of relative effective Cartier divisors. -/
@[expose]
def relativeEffectiveCartierPairSnd : relativeEffectiveCartierPairFunctor f ⟶
    (relativeEffectiveCartierSubfunctor f).toFunctor where
  app T := TypeCat.ofHom Prod.snd
  naturality _ _ _ := by ext p; apply Subtype.ext; rfl

/-- The second projection sends a pair to its second divisor. -/
@[simp]
lemma relativeEffectiveCartierPairSnd_app_apply {T : (Over S)ᵒᵖ}
    (p : (relativeEffectiveCartierPairFunctor f).obj T) :
    (relativeEffectiveCartierPairSnd f).app T p = p.2 := rfl

/-- The equality locus of pairs of relative effective Cartier divisors, constructed as the
equalizer of the two projections from the pair functor. -/
abbrev relativeEffectiveCartierEqualitySubfunctor :
    Subfunctor (relativeEffectiveCartierPairFunctor f) :=
  Subfunctor.equalizer ((⊤ : Subfunctor (relativeEffectiveCartierPairFunctor f)).ι ≫
      relativeEffectiveCartierPairFst f)
    ((⊤ : Subfunctor (relativeEffectiveCartierPairFunctor f)).ι ≫
      relativeEffectiveCartierPairSnd f)

/-- A pair lies in the equality locus exactly when its two divisors agree. -/
@[simp]
lemma mem_relativeEffectiveCartierEqualitySubfunctor_obj_iff
    {T : (Over S)ᵒᵖ} {p : (relativeEffectiveCartierPairFunctor f).obj T} :
    p ∈ (relativeEffectiveCartierEqualitySubfunctor f).obj T ↔
      (relativeEffectiveCartierPairFst f).app T p =
        (relativeEffectiveCartierPairSnd f).app T p := by
  let A : Subfunctor (relativeEffectiveCartierPairFunctor f) := ⊤
  simpa [relativeEffectiveCartierEqualitySubfunctor, A] using
    (Subfunctor.mem_equalizer_iff
      (A.ι ≫ relativeEffectiveCartierPairFst f)
      (A.ι ≫ relativeEffectiveCartierPairSnd f)
      (⟨p, trivial⟩ : A.toFunctor.obj T))

end

end AlgebraicGeometry

end TauCeti
