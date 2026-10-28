/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
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

A universal homeomorphism is written here in Mathlib's form
`(topologically @IsHomeomorph).universally f`. It follows that the absolute and relative Frobenius
and their iterates are surjective, universally injective (radicial) and universally closed; being
moreover affine, they are integral.

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
* Instances: these morphisms are `Surjective`, `UniversallyInjective`, `UniversallyClosed` and
  `IsIntegralHom`.

## References

* The Stacks Project, [Tag 0CC6](https://stacks.math.columbia.edu/tag/0CC6), Frobenii: the
  absolute and relative Frobenius are integral universal homeomorphisms.
-/

public section

open CategoryTheory Limits MorphismProperty

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

instance surjective_iterateFrobenius (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) :
    Surjective (X.iterateFrobenius p hX n) :=
  .of_universally_isHomeomorph <| universally_isHomeomorph_iterateFrobenius hX n

instance universallyInjective_iterateFrobenius (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) :
    UniversallyInjective (X.iterateFrobenius p hX n) :=
  .of_universally_isHomeomorph <| universally_isHomeomorph_iterateFrobenius hX n

instance universallyClosed_iterateFrobenius (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) :
    UniversallyClosed (X.iterateFrobenius p hX n) :=
  .of_universally_isHomeomorph <| universally_isHomeomorph_iterateFrobenius hX n

instance surjective_frobenius (hX : (p : Γ(X, ⊤)) = 0) : Surjective (X.frobenius p hX) :=
  .of_universally_isHomeomorph <| universally_isHomeomorph_frobenius hX

instance universallyInjective_frobenius (hX : (p : Γ(X, ⊤)) = 0) :
    UniversallyInjective (X.frobenius p hX) :=
  .of_universally_isHomeomorph <| universally_isHomeomorph_frobenius hX

instance universallyClosed_frobenius (hX : (p : Γ(X, ⊤)) = 0) :
    UniversallyClosed (X.frobenius p hX) :=
  .of_universally_isHomeomorph <| universally_isHomeomorph_frobenius hX

/-- **The absolute Frobenius is integral.** -/
instance isIntegralHom_frobenius (hX : (p : Γ(X, ⊤)) = 0) : IsIntegralHom (X.frobenius p hX) :=
  -- `F_X` is affine, since it pulls back every open to itself, and universally closed
  have : IsAffineHom (X.frobenius p hX) := ⟨fun U hU ↦ by rwa [frobenius_preimage]⟩
  IsIntegralHom.iff_universallyClosed_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩

/-- **The iterated absolute Frobenius is integral.** -/
instance isIntegralHom_iterateFrobenius (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) :
    IsIntegralHom (X.iterateFrobenius p hX n) := by
  induction n with
  | zero => rw [iterateFrobenius_zero]; infer_instance
  | succ n ih => rw [iterateFrobenius_succ]; infer_instance

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

instance surjective_iterateRelativeFrobenius (n : ℕ) :
    Surjective (π.iterateRelativeFrobenius p hS n) :=
  .of_universally_isHomeomorph <| universally_isHomeomorph_iterateRelativeFrobenius π p hS n

instance universallyInjective_iterateRelativeFrobenius (n : ℕ) :
    UniversallyInjective (π.iterateRelativeFrobenius p hS n) :=
  .of_universally_isHomeomorph <| universally_isHomeomorph_iterateRelativeFrobenius π p hS n

instance universallyClosed_iterateRelativeFrobenius (n : ℕ) :
    UniversallyClosed (π.iterateRelativeFrobenius p hS n) :=
  .of_universally_isHomeomorph <| universally_isHomeomorph_iterateRelativeFrobenius π p hS n

instance surjective_relativeFrobenius : Surjective (π.relativeFrobenius p hS) :=
  .of_universally_isHomeomorph <| universally_isHomeomorph_relativeFrobenius π p hS

instance universallyInjective_relativeFrobenius :
    UniversallyInjective (π.relativeFrobenius p hS) :=
  .of_universally_isHomeomorph <| universally_isHomeomorph_relativeFrobenius π p hS

instance universallyClosed_relativeFrobenius : UniversallyClosed (π.relativeFrobenius p hS) :=
  .of_universally_isHomeomorph <| universally_isHomeomorph_relativeFrobenius π p hS

/-- **The iterated relative Frobenius is integral.** -/
instance isIntegralHom_iterateRelativeFrobenius (n : ℕ) :
    IsIntegralHom (π.iterateRelativeFrobenius p hS n) :=
  -- its composite with the projection `X^{(p^n)} ⟶ X`, which is integral and hence separated as
  -- a base change of `F_S^n`, is the integral morphism `F_X^n`
  have : IsSeparated (pullback.fst π (S.iterateFrobenius p hS n)) := .of_isAffineHom _
  have : IsIntegralHom (π.iterateRelativeFrobenius p hS n ≫ pullback.fst _ _) := by
    rw [iterateRelativeFrobenius_fst]; infer_instance
  .of_comp _ (pullback.fst _ _)

/-- **The relative Frobenius is integral.** -/
instance isIntegralHom_relativeFrobenius : IsIntegralHom (π.relativeFrobenius p hS) :=
  -- its composite with the projection `X^{(p)} ⟶ X`, which is integral and hence separated as a
  -- base change of `F_S`, is the integral morphism `F_X`
  have : IsSeparated (pullback.fst π (S.frobenius p hS)) := .of_isAffineHom _
  have : IsIntegralHom (π.relativeFrobenius p hS ≫ pullback.fst _ _) := by
    rw [relativeFrobenius_fst]; infer_instance
  .of_comp _ (pullback.fst _ _)

end Hom

end Scheme

end AlgebraicGeometry
