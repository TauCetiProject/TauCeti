/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.Twist
public import TauCeti.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-!
# Frobenius morphisms are integral universal homeomorphisms

Let `p` be a prime. The absolute Frobenius `F_X : X ⟶ X` of a scheme `X` in which `p` vanishes is
the identity on points, but it is in general not an isomorphism of schemes. This file proves that
it is nevertheless a *universal homeomorphism*: every base change of `F_X` is a homeomorphism of
underlying spaces. The same holds for the relative Frobenius `F_{X/S} : X ⟶ X^{(p)}` of a scheme
`X` over `S`, for their iterates, and so for every morphism `f` admitting a morphism `g` in the
other direction such that both `f ≫ g` and `g ≫ f` are iterated absolute Frobenii.

Universal homeomorphisms are expressed both in Mathlib's form
`(topologically @IsHomeomorph).universally f` and as instances of
`TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism`. The generic instances for this class imply
that the absolute and relative Frobenius and their iterates are surjective, universally injective
(radicial), universally closed and integral.

The key input is `AlgebraicGeometry.Scheme.universally_isHomeomorph_of_comp_eq_iterateFrobenius`:
if `f ≫ g` and `g ≫ f` are the `n`-fold absolute Frobenius of `X` and of `Y`, then on every base
change `X' ⟶ Y'` of `f`, the morphism `Y' ⟶ X'` induced by `F^n_{Y'}` and `g` is inverse to it
up to Frobenius on both sides; since Frobenius is the identity on points, the two maps are mutually
inverse continuous maps of underlying spaces.

## Main results

* `AlgebraicGeometry.Scheme.universally_isHomeomorph_of_comp_eq_iterateFrobenius`: a morphism
  that is invertible up to an iterated absolute Frobenius is a universal homeomorphism.
* `AlgebraicGeometry.Scheme.universally_isHomeomorph_frobenius` and
  `AlgebraicGeometry.Scheme.universally_isHomeomorph_iterateFrobenius`: the absolute Frobenius and
  its iterates are universal homeomorphisms.
* `AlgebraicGeometry.Scheme.Hom.universally_isHomeomorph_relativeFrobenius` and
  `AlgebraicGeometry.Scheme.Hom.universally_isHomeomorph_iterateRelativeFrobenius`: the relative
  Frobenius and its iterates are universal homeomorphisms.
* `AlgebraicGeometry.Scheme.isUniversalHomeomorphism_of_comp_eq_iterateFrobenius`: the
  class-valued criterion for morphisms invertible up to Frobenius.
* `AlgebraicGeometry.Scheme.isUniversalHomeomorphism_frobenius` and
  `AlgebraicGeometry.Scheme.isUniversalHomeomorphism_iterateFrobenius`: class instances for
  absolute Frobenius and its iterates.
* `AlgebraicGeometry.Scheme.Hom.isUniversalHomeomorphism_relativeFrobenius` and
  `AlgebraicGeometry.Scheme.Hom.isUniversalHomeomorphism_iterateRelativeFrobenius`: class
  instances for relative Frobenius and its iterates.

## References

* The Stacks Project, [Tag 0CC6](https://stacks.math.columbia.edu/tag/0CC6), Frobenii: the
  absolute and relative Frobenius are integral universal homeomorphisms.
-/

public section

open CategoryTheory Limits MorphismProperty TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace Scheme

section Absolute

variable {X Y : Scheme.{u}} {p : ℕ} [Fact p.Prime]

/-- **A morphism invertible up to Frobenius is a universal homeomorphism.** If `f : X ⟶ Y` and
`g : Y ⟶ X` compose, in either order, to the `n`-fold absolute Frobenius of `X` and of `Y`, then
every base change of `f` is a homeomorphism of underlying spaces. -/
theorem universally_isHomeomorph_of_comp_eq_iterateFrobenius {f : X ⟶ Y} (g : Y ⟶ X)
    (hY : (p : Γ(Y, ⊤)) = 0) (n : ℕ)
    (hfg : f ≫ g = X.iterateFrobenius p (natCast_eq_zero_of_hom f hY) n)
    (hgf : g ≫ f = Y.iterateFrobenius p hY n) :
    (topologically @IsHomeomorph).universally f := by
  intro X' Y' i₁ i₂ f' h
  have hY' : (p : Γ(Y', ⊤)) = 0 := natCast_eq_zero_of_hom i₂ hY
  have hX' : (p : Γ(X', ⊤)) = 0 := natCast_eq_zero_of_hom f' hY'
  -- the morphism `Y' ⟶ X'` with components `F^n_{Y'}` and `i₂ ≫ g` inverts `f'` up to Frobenius
  let s : Y' ⟶ X' := h.lift (Y'.iterateFrobenius p hY' n) (i₂ ≫ g) <| by
    rw [Category.assoc, hgf, iterateFrobenius_naturality hY' hY]
  have hsf : s ≫ f' = Y'.iterateFrobenius p hY' n := h.lift_fst _ _ _
  have hfs : f' ≫ s = X'.iterateFrobenius p hX' n := by
    refine h.hom_ext ?_ ?_
    · rw [Category.assoc, hsf, iterateFrobenius_naturality hX' hY']
    · rw [Category.assoc, h.lift_snd, ← Category.assoc, h.w, Category.assoc, hfg,
        iterateFrobenius_naturality hX' (natCast_eq_zero_of_hom f hY)]
  refine isHomeomorph_iff_exists_inverse.2 ⟨f'.continuous, s, fun x ↦ ?_, fun y ↦ ?_,
    s.continuous⟩
  · rw [← Scheme.Hom.comp_apply, hfs, iterateFrobenius_apply]
  · rw [← Scheme.Hom.comp_apply, hsf, iterateFrobenius_apply]

/-- **The iterated absolute Frobenius is a universal homeomorphism.** -/
theorem universally_isHomeomorph_iterateFrobenius (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) :
    (topologically @IsHomeomorph).universally (X.iterateFrobenius p hX n) :=
  universally_isHomeomorph_of_comp_eq_iterateFrobenius (𝟙 X) hX n
    (Category.comp_id _) (Category.id_comp _)

/-- **The absolute Frobenius is a universal homeomorphism**: every base change of `F_X` is a
homeomorphism of underlying spaces. -/
theorem universally_isHomeomorph_frobenius (hX : (p : Γ(X, ⊤)) = 0) :
    (topologically @IsHomeomorph).universally (X.frobenius p hX) := by
  simpa using universally_isHomeomorph_iterateFrobenius hX 1

/-- A morphism invertible up to iterated absolute Frobenius is a universal homeomorphism. -/
theorem isUniversalHomeomorphism_of_comp_eq_iterateFrobenius {f : X ⟶ Y} (g : Y ⟶ X)
    (hY : (p : Γ(Y, ⊤)) = 0) (n : ℕ)
    (hfg : f ≫ g = X.iterateFrobenius p (natCast_eq_zero_of_hom f hY) n)
    (hgf : g ≫ f = Y.iterateFrobenius p hY n) : IsUniversalHomeomorphism f :=
  ⟨universally_isHomeomorph_of_comp_eq_iterateFrobenius g hY n hfg hgf⟩

/-- Iterated absolute Frobenius remains a homeomorphism after every base change. -/
instance isUniversalHomeomorphism_iterateFrobenius (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) :
    IsUniversalHomeomorphism (X.iterateFrobenius p hX n) :=
  ⟨universally_isHomeomorph_iterateFrobenius hX n⟩

/-- Absolute Frobenius remains a homeomorphism after every base change. -/
instance isUniversalHomeomorphism_frobenius (hX : (p : Γ(X, ⊤)) = 0) :
    IsUniversalHomeomorphism (X.frobenius p hX) :=
  ⟨universally_isHomeomorph_frobenius hX⟩

end Absolute

namespace Hom

variable {X S : Scheme.{u}} (π : X ⟶ S) (p : ℕ) [Fact p.Prime] (hS : (p : Γ(S, ⊤)) = 0)

/-- **The iterated relative Frobenius is a universal homeomorphism.** -/
theorem universally_isHomeomorph_iterateRelativeFrobenius (n : ℕ) :
    (topologically @IsHomeomorph).universally (π.iterateRelativeFrobenius p hS n) :=
  universally_isHomeomorph_of_comp_eq_iterateFrobenius (pullback.fst _ _)
    (natCast_eq_zero_of_hom (pullback.snd _ _) hS) n
    (iterateRelativeFrobenius_fst π p hS n) (fst_iterateRelativeFrobenius π p hS n)

/-- **The relative Frobenius is a universal homeomorphism**: every base change of
`F_{X/S} : X ⟶ X^{(p)}` is a homeomorphism of underlying spaces. -/
theorem universally_isHomeomorph_relativeFrobenius :
    (topologically @IsHomeomorph).universally (π.relativeFrobenius p hS) :=
  universally_isHomeomorph_of_comp_eq_iterateFrobenius (pullback.fst _ _)
    (natCast_eq_zero_of_hom (pullback.snd _ _) hS) 1
    (by simp) (by simp)

/-- Iterated relative Frobenius remains a homeomorphism after every base change. -/
instance isUniversalHomeomorphism_iterateRelativeFrobenius (n : ℕ) :
    IsUniversalHomeomorphism (π.iterateRelativeFrobenius p hS n) :=
  ⟨universally_isHomeomorph_iterateRelativeFrobenius π p hS n⟩

/-- Relative Frobenius remains a homeomorphism after every base change, with no flatness or
perfectness hypothesis on the base. -/
instance isUniversalHomeomorphism_relativeFrobenius :
    IsUniversalHomeomorphism (π.relativeFrobenius p hS) :=
  ⟨universally_isHomeomorph_relativeFrobenius π p hS⟩

end Hom

end Scheme

end AlgebraicGeometry
