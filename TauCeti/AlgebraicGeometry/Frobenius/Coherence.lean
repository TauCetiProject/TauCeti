/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.Twist

/-!
# Coherence of iterated Frobenius twists

The comparison from a successive pair of Frobenius twists to the twist for the sum of
exponents respects units, associativity, morphisms over the base, and arbitrary base change.
Consequently successive twists can be identified without depending on parenthesization.
The base-change projection also respects identity and composite changes of base.

These are equations for the existing `Scheme.Hom.iterateFrobeniusTwistAddIso` and
`Scheme.Hom.iterateFrobeniusTwistMap`, not new choices of comparison maps. Every equation
retains the canonical pullback identifications, including transport of the exponent along
associativity of addition. The cartesian property of `iterateFrobeniusTwistMap` then makes
its projection equations coherence equations for the corresponding base-change isomorphisms.
No perfectness, reducedness, affineness, or finiteness hypothesis on the base is needed.

## References

* The Stacks Project, section Frobenii, Tags 0CC6 and 0CCG.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S T U : Scheme.{u}} (π : X ⟶ S) (p : ℕ) [Fact p.Prime]
  (hS : (p : Γ(S, ⊤)) = 0)

/-- Adding a zero twist on the right is the canonical zeroth-twist identification. -/
@[reassoc]
theorem iterateFrobeniusTwistAddIso_zero_right (m : ℕ) :
    (π.iterateFrobeniusTwistAddIso p hS m 0).hom ≫
        (pullback.congrHom rfl
          (congrArg (S.iterateFrobenius p hS) (Nat.add_zero m))).hom =
      ((pullback.snd π (S.iterateFrobenius p hS m)).iterateFrobeniusTwistZeroIso p hS).hom := by
  apply pullback.hom_ext
  · simpa using π.iterateFrobeniusTwistAddIso_hom_fst p hS m 0
  · simpa [pullback.condition] using π.iterateFrobeniusTwistAddIso_hom_snd p hS m 0

/-- Adding a zero twist on the left agrees with pulling back the zeroth-twist identification. -/
@[reassoc]
theorem iterateFrobeniusTwistAddIso_zero_left (n : ℕ) :
    (π.iterateFrobeniusTwistAddIso p hS 0 n).hom ≫
        (pullback.congrHom rfl
          (congrArg (S.iterateFrobenius p hS) (Nat.zero_add n))).hom =
      pullback.map _ _ π (S.iterateFrobenius p hS n)
        (π.iterateFrobeniusTwistZeroIso p hS).hom (𝟙 S) (𝟙 S)
        (by simp [pullback.condition]) (by simp) := by
  apply pullback.hom_ext <;> simp

/-- Combining three successive twists is independent of parenthesization, with the target
identified along associativity of the sum of exponents. -/
@[reassoc]
theorem iterateFrobeniusTwistAddIso_assoc (m n r : ℕ) :
    pullback.map _ _ _ (S.iterateFrobenius p hS r)
        (π.iterateFrobeniusTwistAddIso p hS m n).hom (𝟙 S) (𝟙 S)
        (by simp) (by simp) ≫
      (π.iterateFrobeniusTwistAddIso p hS (m + n) r).hom ≫
        (pullback.congrHom rfl
          (congrArg (S.iterateFrobenius p hS) (Nat.add_assoc m n r))).hom =
      ((pullback.snd π (S.iterateFrobenius p hS m)).iterateFrobeniusTwistAddIso
        p hS n r).hom ≫
          (π.iterateFrobeniusTwistAddIso p hS m (n + r)).hom := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- The comparison for a successor exponent is the addition comparison for exponent one. -/
@[reassoc]
theorem iterateFrobeniusTwistAddIso_one_right (n : ℕ) :
    (pullback.congrHom rfl (S.iterateFrobenius_one hS)).hom ≫
        (π.iterateFrobeniusTwistSuccIso p hS n).hom =
      (π.iterateFrobeniusTwistAddIso p hS n 1).hom := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- The addition comparison is natural in morphisms of schemes over the base. -/
@[reassoc]
theorem iterateFrobeniusTwistAddIso_naturality (πY : Y ⟶ S) (g : X ⟶ Y)
    (hg : g ≫ πY = π) (m n : ℕ) :
    pullback.map _ _ _ (S.iterateFrobenius p hS n)
        (pullback.map π (S.iterateFrobenius p hS m) πY _ g (𝟙 S) (𝟙 S)
          (by simp [hg]) (by simp)) (𝟙 S) (𝟙 S)
        (by simp) (by simp) ≫
      (πY.iterateFrobeniusTwistAddIso p hS m n).hom =
      (π.iterateFrobeniusTwistAddIso p hS m n).hom ≫
        pullback.map π (S.iterateFrobenius p hS (m + n)) πY _ g (𝟙 S) (𝟙 S)
          (by simp [hg]) (by simp) := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Combining two twists commutes with arbitrary base change. Both routes project from
the double twist of the base-changed scheme to the sum twist of the original scheme. -/
@[reassoc]
theorem iterateFrobeniusTwistAddIso_baseChange (m n : ℕ) (f : T ⟶ S) :
    ((pullback.snd π f).iterateFrobeniusTwistAddIso p (natCast_eq_zero_of_hom f hS)
        m n).hom ≫ π.iterateFrobeniusTwistMap p hS (m + n) f =
      pullback.map _ _ _ (S.iterateFrobenius p hS n)
        (π.iterateFrobeniusTwistMap p hS m f) f f
        (by simp) (iterateFrobenius_naturality _ hS f n) ≫
          (π.iterateFrobeniusTwistAddIso p hS m n).hom := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Base change along the identity agrees with the canonical pullback comparison removing
that identity base change. -/
theorem iterateFrobeniusTwistMap_id (n : ℕ) :
    π.iterateFrobeniusTwistMap p hS n (𝟙 S) =
      (pullbackLeftPullbackSndIso π (𝟙 S) (S.iterateFrobenius p hS n)).hom ≫
        (pullback.congrHom rfl (Category.comp_id _)).hom := by
  apply pullback.hom_ext <;> simp

/-- Two successive base changes give the same twist projection as their composite. The
source comparison is the pullback of the canonical comparison of successive base changes. -/
@[reassoc]
theorem iterateFrobeniusTwistMap_comp (n : ℕ) (f : T ⟶ S) (g : U ⟶ T) :
    (pullback.snd π f).iterateFrobeniusTwistMap p (natCast_eq_zero_of_hom f hS) n g ≫
        π.iterateFrobeniusTwistMap p hS n f =
      pullback.map _ _ _
        (U.iterateFrobenius p (natCast_eq_zero_of_hom (g ≫ f) hS) n)
        (pullbackLeftPullbackSndIso π f g).hom (𝟙 U) (𝟙 U)
        (by simp) (by simp) ≫
          π.iterateFrobeniusTwistMap p hS n (g ≫ f) := by
  apply pullback.hom_ext <;> simp [Category.assoc]

end AlgebraicGeometry.Scheme.Hom
