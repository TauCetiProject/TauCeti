/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.Twist
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Map

/-!
# Frobenius and fibre products

The Frobenius twist of `X ×_S Y` is canonically `X^{(pⁿ)} ×_S Y^{(pⁿ)}`.
Under this isomorphism, iterated relative Frobenius is the product of the iterated
relative Frobenius maps of the factors. The base need not be perfect, and none of
the schemes need be reduced, affine or of finite type.

`Scheme.Hom.iterateFrobeniusTwistProdIso` uses the existing base-change comparison
`CategoryTheory.IsPullback.pullback_map`. Its projection formulas specify the
comparison without unfolding it. `Scheme.Hom.iterateRelativeFrobenius_prod` identifies
the relative maps. Absolute Frobenius on a fibre product is described by
`Scheme.iterateFrobenius_pullback`.

## References

* The Stacks Project, section Frobenii, Tags 0CC6 and 0CCG.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y S : Scheme.{u}}

/-- Absolute Frobenius on a fibre product acts by Frobenius on both factors and on the base. -/
theorem iterateFrobenius_pullback (f : X ⟶ S) (g : Y ⟶ S) (p : ℕ) [Fact p.Prime]
    (hS : (p : Γ(S, ⊤)) = 0) (n : ℕ) :
    (pullback f g).iterateFrobenius p
        (natCast_eq_zero_of_hom (pullback.fst f g ≫ f) hS) n =
      pullback.map f g f g
        (X.iterateFrobenius p (natCast_eq_zero_of_hom f hS) n)
        (Y.iterateFrobenius p (natCast_eq_zero_of_hom g hS) n)
        (S.iterateFrobenius p hS n)
        (iterateFrobenius_naturality _ hS f n).symm
        (iterateFrobenius_naturality _ hS g n).symm := by
  apply pullback.hom_ext
  · simpa using iterateFrobenius_naturality _ (natCast_eq_zero_of_hom f hS)
      (pullback.fst f g) n
  · simpa using iterateFrobenius_naturality _ (natCast_eq_zero_of_hom g hS)
      (pullback.snd f g) n

namespace Hom

variable (f : X ⟶ S) (g : Y ⟶ S) (p : ℕ) [Fact p.Prime]
  (hS : (p : Γ(S, ⊤)) = 0) (n : ℕ)

/-- Twisting a fibre product by the `n`-fold Frobenius is the fibre product of the twists,
with both twisted factors regarded as schemes over `S` through their second projections. -/
noncomputable def iterateFrobeniusTwistProdIso :
    pullback (pullback.fst f g ≫ f) (S.iterateFrobenius p hS n) ≅
      pullback (pullback.snd f (S.iterateFrobenius p hS n))
        (pullback.snd g (S.iterateFrobenius p hS n)) :=
  (((IsPullback.of_hasPullback f (S.iterateFrobenius p hS n)).flip.pullback_map
    (IsPullback.of_hasPullback g (S.iterateFrobenius p hS n)).flip).flip.isoPullback).symm

/-- The first projection of the product-twist comparison is the twist of the first projection. -/
@[reassoc (attr := simp)]
theorem iterateFrobeniusTwistProdIso_hom_fst :
    (iterateFrobeniusTwistProdIso f g p hS n).hom ≫ pullback.fst _ _ =
      pullback.map (pullback.fst f g ≫ f) _ f _ (pullback.fst f g) (𝟙 S) (𝟙 S)
        (by simp) (by simp) := by
  apply (cancel_epi (iterateFrobeniusTwistProdIso f g p hS n).inv).mp
  apply pullback.hom_ext <;> simp [iterateFrobeniusTwistProdIso]

/-- The second projection of the product-twist comparison is the twist of the second projection. -/
@[reassoc (attr := simp)]
theorem iterateFrobeniusTwistProdIso_hom_snd :
    (iterateFrobeniusTwistProdIso f g p hS n).hom ≫ pullback.snd _ _ =
      pullback.map (pullback.fst f g ≫ f) _ g _ (pullback.snd f g) (𝟙 S) (𝟙 S)
        (by simp [pullback.condition]) (by simp) := by
  apply (cancel_epi (iterateFrobeniusTwistProdIso f g p hS n).inv).mp
  apply pullback.hom_ext <;> simp [iterateFrobeniusTwistProdIso, pullback.condition]

/-- The inverse product-twist comparison projects to the original fibre product by the
projections from both twists. -/
@[reassoc (attr := simp)]
theorem iterateFrobeniusTwistProdIso_inv_fst :
    (iterateFrobeniusTwistProdIso f g p hS n).inv ≫ pullback.fst _ _ =
      pullback.map _ _ f g (pullback.fst f _) (pullback.fst g _)
        (S.iterateFrobenius p hS n) pullback.condition.symm pullback.condition.symm := by
  simp [iterateFrobeniusTwistProdIso]

/-- The product-twist comparison is an isomorphism over `S`. -/
@[reassoc (attr := simp)]
theorem iterateFrobeniusTwistProdIso_inv_snd :
    (iterateFrobeniusTwistProdIso f g p hS n).inv ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.snd f (S.iterateFrobenius p hS n) := by
  simp [iterateFrobeniusTwistProdIso]

/-- Iterated relative Frobenius on a fibre product is the product of the two iterated
relative Frobenius maps under the canonical product-twist comparison. -/
theorem iterateRelativeFrobenius_prod :
    (pullback.fst f g ≫ f).iterateRelativeFrobenius p hS n ≫
        (iterateFrobeniusTwistProdIso f g p hS n).hom =
      pullback.map f g (pullback.snd f (S.iterateFrobenius p hS n))
        (pullback.snd g (S.iterateFrobenius p hS n))
        (f.iterateRelativeFrobenius p hS n) (g.iterateRelativeFrobenius p hS n) (𝟙 S)
        (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, iterateFrobeniusTwistProdIso_hom_fst]
    simpa using iterateRelativeFrobenius_naturality hS f (pullback.fst f g) rfl n
  · simp only [Category.assoc, iterateFrobeniusTwistProdIso_hom_snd]
    simpa using iterateRelativeFrobenius_naturality hS g (pullback.snd f g)
      pullback.condition.symm n

/-- The product-twist comparison is natural in both schemes over the base. -/
@[reassoc]
theorem iterateFrobeniusTwistProdIso_naturality {X' Y' : Scheme.{u}}
    (f' : X' ⟶ S) (g' : Y' ⟶ S) (a : X ⟶ X') (b : Y ⟶ Y')
    (ha : a ≫ f' = f) (hb : b ≫ g' = g) :
    pullback.map (pullback.fst f g ≫ f) _ (pullback.fst f' g' ≫ f') _
        (pullback.map f g f' g' a b (𝟙 S) (by simp [ha]) (by simp [hb]))
        (𝟙 S) (𝟙 S) (by simp [ha]) (by simp) ≫
        (iterateFrobeniusTwistProdIso f' g' p hS n).hom =
      (iterateFrobeniusTwistProdIso f g p hS n).hom ≫
        pullback.map (pullback.snd f (S.iterateFrobenius p hS n))
          (pullback.snd g (S.iterateFrobenius p hS n))
          (pullback.snd f' (S.iterateFrobenius p hS n))
          (pullback.snd g' (S.iterateFrobenius p hS n))
          (pullback.map f _ f' _ a (𝟙 S) (𝟙 S) (by simp [ha]) (by simp))
          (pullback.map g _ g' _ b (𝟙 S) (𝟙 S) (by simp [hb]) (by simp))
          (𝟙 S) (by simp) (by simp) := by
  ext <;> simp

end Hom

end AlgebraicGeometry.Scheme
