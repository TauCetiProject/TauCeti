/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.Simple
public import TauCeti.CategoryTheory.Monoidal.Rigid.SquaredNorm
public import TauCeti.CategoryTheory.Preadditive.Schur

/-!
# Invertibility of bidual traces and squared norms in finite semisimple categories

In a finite semisimple right rigid abelian category `C`, the coevaluation `η_ X Xᘁ : 𝟙_ C ⟶ X ⊗ Xᘁ`
of any nonzero object `X` is nonzero, so when every endomorphism of `X` is a scalar multiple of
`𝟙 X` over a commutative semiring `R`, Schur's lemma for exact pairings
(`TauCeti.comp_evaluation_ne_zero_of_surjective_right`) makes `doubleDualTrace b` nonzero for any
isomorphism `b : X ⟶ Xᘁᘁ`—without assuming that `𝟙_ C` is simple. Passing from `X` to `Xᘁ` via
`TauCeti.surjective_algebraMap_end_rightDual` yields the parallel nonvanishing of
`doubleDualTrace (bᘁ)` for any isomorphism `b : Xᘁᘁ ⟶ X`.

When `𝟙_ C` is moreover simple, every nonzero endomorphism of `𝟙_ C` is an isomorphism, so both
bidual trace factors and their composite `squaredNorm a` (for `a : X ≅ Xᘁᘁ`) are isomorphisms in `C`
(equivalently units in `End (𝟙_ C)`), and hence `squaredNorm a` is nonzero.

Over an algebraically closed field `k`, Schur's lemma supplies surjectivity of
`algebraMap k (End X)` for every simple object `X` with finite-dimensional endomorphisms, yielding
invertibility and nonvanishing of both bidual trace factors and of `squaredNorm a` without assuming
a pivotal structure or characteristic zero.

## Main declarations

* `TauCeti.doubleDualTrace_ne_zero_of_surjective` and
  `TauCeti.doubleDualTrace_rightAdjointMate_ne_zero_of_surjective`: nonvanishing of both bidual
  trace factors in any finite semisimple right rigid category;
* `TauCeti.isIso_doubleDualTrace_of_surjective`,
  `TauCeti.isUnit_endOf_doubleDualTrace_of_surjective`,
  `TauCeti.isIso_doubleDualTrace_rightAdjointMate_of_surjective`, and
  `TauCeti.isUnit_endOf_doubleDualTrace_rightAdjointMate_of_surjective`: invertibility when `𝟙_ C`
  is simple;
* `TauCeti.isIso_squaredNorm_of_surjective` and `TauCeti.squaredNorm_ne_zero_of_surjective`:
  invertibility and nonvanishing of `squaredNorm a` over a commutative semiring when `𝟙_ C` is
  simple;
* `TauCeti.doubleDualTrace_ne_zero`, `TauCeti.doubleDualTrace_rightAdjointMate_ne_zero`,
  `TauCeti.isIso_doubleDualTrace`, `TauCeti.isUnit_endOf_doubleDualTrace`,
  `TauCeti.isIso_doubleDualTrace_rightAdjointMate`,
  `TauCeti.isUnit_endOf_doubleDualTrace_rightAdjointMate`, `TauCeti.isIso_squaredNorm`, and
  `TauCeti.squaredNorm_ne_zero`: the specializations to split simple objects over an algebraically
  closed field.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  [arXiv:math/0203060](https://arxiv.org/abs/math/0203060), §2.1, Proposition 2.1
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.21
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Abelian C] [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]

section CommSemiring

variable {R : Type w} [CommSemiring R] [Linear R C] [MonoidalLinear R C]

/-- In a finite semisimple right rigid abelian category, if `X` is nonzero and
`algebraMap R (End X)` is surjective, then `doubleDualTrace b` is nonzero for any isomorphism
`b : X ⟶ Xᘁᘁ`. The tensor unit need not be simple. -/
theorem doubleDualTrace_ne_zero_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (b : X ⟶ (Xᘁ : C)ᘁ) [IsIso b] :
    doubleDualTrace b ≠ 0 := by
  let := exactPairingCongrRight (X := (Xᘁ : C)) (asIso b)
  have h := comp_evaluation_ne_zero_of_surjective_right (X := (Xᘁ : C)) hX
    (coevaluation_ne_zero (Y := (Xᘁ : C)) hX₀)
  rwa [exactPairingCongrRight_evaluation, asIso_hom, ← doubleDualTrace_def] at h

/-- In a finite semisimple right rigid abelian category, if `X` is nonzero and
`algebraMap R (End X)` is surjective, then `doubleDualTrace (bᘁ)` is nonzero for any isomorphism
`b : Xᘁᘁ ⟶ X`. The tensor unit need not be simple. -/
theorem doubleDualTrace_rightAdjointMate_ne_zero_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (b : (Xᘁ : C)ᘁ ⟶ X) [IsIso b] :
    doubleDualTrace (bᘁ) ≠ 0 := by
  have hX' : ¬IsZero (Xᘁ : C) := fun h ↦ hX₀ <| (IsZero.iff_id_eq_zero X).mpr <|
    rightAdjointMate_injective <| by
      rw [rightAdjointMate_id, rightAdjointMate_zero]
      exact h.eq_of_src _ _
  have hb : bᘁ = (asIso b).rightAdjointMate.hom := by
    rw [Iso.rightAdjointMate_hom, asIso_hom]
  have : IsIso (bᘁ) := hb ▸ inferInstance
  exact doubleDualTrace_ne_zero_of_surjective hX' (surjective_algebraMap_end_rightDual hX) (bᘁ)

section SimpleUnit

variable [Simple (𝟙_ C)]

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then `doubleDualTrace b` is an isomorphism for any
isomorphism `b : X ⟶ Xᘁᘁ`. -/
theorem isIso_doubleDualTrace_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (b : X ⟶ (Xᘁ : C)ᘁ) [IsIso b] :
    IsIso (doubleDualTrace b) :=
  isIso_of_hom_simple (doubleDualTrace_ne_zero_of_surjective hX₀ hX b)

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then `End.of (doubleDualTrace b)` is a unit in
`End (𝟙_ C)` for any isomorphism `b : X ⟶ Xᘁᘁ`. -/
theorem isUnit_endOf_doubleDualTrace_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (b : X ⟶ (Xᘁ : C)ᘁ) [IsIso b] :
    IsUnit (End.of (doubleDualTrace b)) :=
  (CategoryTheory.isUnit_iff_isIso _).mpr (isIso_doubleDualTrace_of_surjective hX₀ hX b)

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then `doubleDualTrace (bᘁ)` is an isomorphism for any
isomorphism `b : Xᘁᘁ ⟶ X`. -/
theorem isIso_doubleDualTrace_rightAdjointMate_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (b : (Xᘁ : C)ᘁ ⟶ X) [IsIso b] :
    IsIso (doubleDualTrace (bᘁ)) :=
  isIso_of_hom_simple (doubleDualTrace_rightAdjointMate_ne_zero_of_surjective hX₀ hX b)

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then `End.of (doubleDualTrace (bᘁ))` is a unit in
`End (𝟙_ C)` for any isomorphism `b : Xᘁᘁ ⟶ X`. -/
theorem isUnit_endOf_doubleDualTrace_rightAdjointMate_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (b : (Xᘁ : C)ᘁ ⟶ X) [IsIso b] :
    IsUnit (End.of (doubleDualTrace (bᘁ))) :=
  (CategoryTheory.isUnit_iff_isIso _).mpr
    (isIso_doubleDualTrace_rightAdjointMate_of_surjective hX₀ hX b)

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then `squaredNorm a` is an isomorphism. -/
theorem isIso_squaredNorm_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    IsIso (squaredNorm a) := by
  rw [squaredNorm_def]
  have := isIso_doubleDualTrace_of_surjective hX₀ hX a.hom
  have := isIso_doubleDualTrace_rightAdjointMate_of_surjective hX₀ hX a.inv
  exact IsIso.comp_isIso

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then `squaredNorm a` is nonzero. -/
theorem squaredNorm_ne_zero_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a ≠ 0 :=
  (isIso_iff_ne_zero _).mp (isIso_squaredNorm_of_surjective hX₀ hX a)

end SimpleUnit

end CommSemiring

section Field

variable (k : Type w) [Field k] [IsAlgClosed k] [Linear k C] [MonoidalLinear k C]
variable {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]

include k in
/-- In a finite semisimple right rigid category over an algebraically closed field, the bidual
trace of an isomorphism `b : X ⟶ Xᘁᘁ` out of a simple object with finite-dimensional endomorphisms
is nonzero. -/
theorem doubleDualTrace_ne_zero (b : X ⟶ (Xᘁ : C)ᘁ) [IsIso b] :
    doubleDualTrace b ≠ 0 :=
  doubleDualTrace_ne_zero_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective b

include k in
/-- In a finite semisimple right rigid category over an algebraically closed field, the bidual
trace of the right adjoint mate of an isomorphism `b : Xᘁᘁ ⟶ X` into a simple object with
finite-dimensional endomorphisms is nonzero. -/
theorem doubleDualTrace_rightAdjointMate_ne_zero (b : (Xᘁ : C)ᘁ ⟶ X) [IsIso b] :
    doubleDualTrace (bᘁ) ≠ 0 :=
  doubleDualTrace_rightAdjointMate_ne_zero_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective b

section SimpleUnit

variable [Simple (𝟙_ C)]

include k in
/-- In a finite semisimple right rigid category with simple unit over an algebraically closed
field, the bidual trace of an isomorphism `b : X ⟶ Xᘁᘁ` out of a simple object with
finite-dimensional endomorphisms is invertible. -/
theorem isIso_doubleDualTrace (b : X ⟶ (Xᘁ : C)ᘁ) [IsIso b] :
    IsIso (doubleDualTrace b) :=
  isIso_doubleDualTrace_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective b

include k in
/-- In a finite semisimple right rigid category with simple unit over an algebraically closed
field, `End.of (doubleDualTrace b)` is a unit in `End (𝟙_ C)` for any isomorphism `b : X ⟶ Xᘁᘁ` out
of a simple object with finite-dimensional endomorphisms. -/
theorem isUnit_endOf_doubleDualTrace (b : X ⟶ (Xᘁ : C)ᘁ) [IsIso b] :
    IsUnit (End.of (doubleDualTrace b)) :=
  isUnit_endOf_doubleDualTrace_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective b

include k in
/-- In a finite semisimple right rigid category with simple unit over an algebraically closed
field, the bidual trace of the right adjoint mate of an isomorphism `b : Xᘁᘁ ⟶ X` into a simple
object with finite-dimensional endomorphisms is invertible. -/
theorem isIso_doubleDualTrace_rightAdjointMate (b : (Xᘁ : C)ᘁ ⟶ X) [IsIso b] :
    IsIso (doubleDualTrace (bᘁ)) :=
  isIso_doubleDualTrace_rightAdjointMate_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective b

include k in
/-- In a finite semisimple right rigid category with simple unit over an algebraically closed
field, `End.of (doubleDualTrace (bᘁ))` is a unit in `End (𝟙_ C)` for any isomorphism `b : Xᘁᘁ ⟶ X`
into a simple object with finite-dimensional endomorphisms. -/
theorem isUnit_endOf_doubleDualTrace_rightAdjointMate (b : (Xᘁ : C)ᘁ ⟶ X) [IsIso b] :
    IsUnit (End.of (doubleDualTrace (bᘁ))) :=
  isUnit_endOf_doubleDualTrace_rightAdjointMate_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective b

include k in
/-- In a finite semisimple right rigid category with simple unit over an algebraically closed
field, the squared norm of a simple object with finite-dimensional endomorphisms is invertible. -/
theorem isIso_squaredNorm (a : X ≅ (Xᘁ : C)ᘁ) : IsIso (squaredNorm a) :=
  isIso_squaredNorm_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective a

include k in
/-- In a finite semisimple right rigid category with simple unit over an algebraically closed
field, the squared norm of a simple object with finite-dimensional endomorphisms is nonzero. -/
theorem squaredNorm_ne_zero (a : X ≅ (Xᘁ : C)ᘁ) : squaredNorm a ≠ 0 :=
  squaredNorm_ne_zero_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective a

end SimpleUnit

end Field

end TauCeti
