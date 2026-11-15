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

The comparison is the general base-change isomorphism
`CategoryTheory.Limits.pullbackBaseChangeIso`, specialized to iterated Frobenius on the base.
Its projection formulas specify the comparison without unfolding it.
`Scheme.Hom.iterateRelativeFrobenius_pullback` identifies the relative maps.
Absolute Frobenius on a fibre product is described by `Scheme.iterateFrobenius_pullback`.

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

/-- Iterated relative Frobenius on a fibre product is the product of the two iterated
relative Frobenius maps under the canonical base-change comparison. -/
@[reassoc]
theorem iterateRelativeFrobenius_pullback :
    (pullback.fst f g ≫ f).iterateRelativeFrobenius p hS n ≫
        (pullbackBaseChangeIso f g (S.iterateFrobenius p hS n)).hom =
      pullback.map f g (pullback.snd f (S.iterateFrobenius p hS n))
        (pullback.snd g (S.iterateFrobenius p hS n))
        (f.iterateRelativeFrobenius p hS n) (g.iterateRelativeFrobenius p hS n) (𝟙 S)
        (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackBaseChangeIso_hom_fst]
    simpa using iterateRelativeFrobenius_naturality hS f (pullback.fst f g) rfl n
  · simp only [Category.assoc, pullbackBaseChangeIso_hom_snd]
    simpa using iterateRelativeFrobenius_naturality hS g (pullback.snd f g)
      pullback.condition.symm n

end Hom

end AlgebraicGeometry.Scheme
