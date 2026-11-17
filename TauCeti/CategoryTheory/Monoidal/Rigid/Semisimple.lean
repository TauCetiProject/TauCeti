/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.SquaredNorm
public import TauCeti.CategoryTheory.Preadditive.Schur
public import TauCeti.CategoryTheory.Semisimple.Basic

/-!
# Invertibility of bidual traces and squared norms in finite semisimple categories

In a finite semisimple right rigid abelian category `C` whose tensor unit `𝟙_ C` is simple, the
coevaluation `η_ X Xᘁ : 𝟙_ C ⟶ X ⊗ Xᘁ` of any nonzero object `X` is nonzero, hence a split
monomorphism. When every endomorphism of `X` is a scalar multiple of `𝟙 X` over a commutative
semiring `R`, `TauCeti.isIso_doubleDualTrace_of_isSplitMono` applies to both `a : X ≅ Xᘁᘁ` and its
dual isomorphism `a.rightAdjointMate.symm : Xᘁ ≅ Xᘁᘁᘁ`: both trace factors `doubleDualTrace a.hom`
and `doubleDualTrace (a.inv)ᘁ`, as well as their composite `squaredNorm a`, are isomorphisms in `C`
(equivalently units in `End (𝟙_ C)`), and hence nonzero because `𝟙_ C` is simple.

Over an algebraically closed field `k`, Schur's lemma supplies surjectivity of
`algebraMap k (End X)` for every simple object `X` with finite-dimensional endomorphisms, yielding
invertibility and nonvanishing of both bidual trace factors and of `squaredNorm a` without assuming
a pivotal structure or characteristic zero.

## Main declarations

* `TauCeti.isIso_doubleDualTrace_of_surjective`,
  `TauCeti.isUnit_endOf_doubleDualTrace_of_surjective`, and
  `TauCeti.doubleDualTrace_ne_zero_of_surjective`: invertibility and nonvanishing of
  `doubleDualTrace a.hom` for a nonzero object with scalar endomorphisms;
* `TauCeti.isIso_doubleDualTrace_rightAdjointMate_inv_of_surjective`,
  `TauCeti.isUnit_endOf_doubleDualTrace_rightAdjointMate_inv_of_surjective`, and
  `TauCeti.doubleDualTrace_rightAdjointMate_inv_ne_zero_of_surjective`: the parallel results for
  the second trace factor `doubleDualTrace (a.inv)ᘁ`;
* `TauCeti.isIso_squaredNorm_of_surjective` and `TauCeti.squaredNorm_ne_zero_of_surjective`:
  invertibility and nonvanishing of `squaredNorm a` over a commutative semiring;
* `TauCeti.isIso_doubleDualTrace_of_simple`, `TauCeti.isUnit_endOf_doubleDualTrace_of_simple`,
  `TauCeti.doubleDualTrace_ne_zero_of_simple`,
  `TauCeti.isIso_doubleDualTrace_rightAdjointMate_inv_of_simple`,
  `TauCeti.isUnit_endOf_doubleDualTrace_rightAdjointMate_inv_of_simple`,
  `TauCeti.doubleDualTrace_rightAdjointMate_inv_ne_zero_of_simple`,
  `TauCeti.isIso_squaredNorm_of_simple`, and `TauCeti.squaredNorm_ne_zero_of_simple`: the
  specializations to split simple objects over an algebraically closed field.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005),
  §2.1, Proposition 2.1
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.21
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Abelian C] [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

section CommSemiring

variable {R : Type w} [CommSemiring R] [Linear R C] [MonoidalLinear R C]

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then `doubleDualTrace a.hom` is an isomorphism. -/
theorem isIso_doubleDualTrace_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    IsIso (doubleDualTrace a.hom) := by
  have : IsSplitMono (η_ X Xᘁ) :=
    isSplitMono_of_nonzero_from_simple (coevaluation_ne_zero hX₀)
  exact isIso_doubleDualTrace_of_isSplitMono hX a

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then `End.of (doubleDualTrace a.hom)` is a unit in
`End (𝟙_ C)`. -/
theorem isUnit_endOf_doubleDualTrace_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    IsUnit (End.of (doubleDualTrace a.hom)) := by
  have : IsSplitMono (η_ X Xᘁ) :=
    isSplitMono_of_nonzero_from_simple (coevaluation_ne_zero hX₀)
  exact isUnit_endOf_doubleDualTrace_of_isSplitMono hX a

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then `doubleDualTrace a.hom` is nonzero. -/
theorem doubleDualTrace_ne_zero_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    doubleDualTrace a.hom ≠ 0 :=
  (isIso_iff_ne_zero _).1 (isIso_doubleDualTrace_of_surjective hX₀ hX a)

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then `doubleDualTrace (rightAdjointMate a.inv)` is an
isomorphism. -/
theorem isIso_doubleDualTrace_rightAdjointMate_inv_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    IsIso (doubleDualTrace (rightAdjointMate a.inv)) := by
  have hX' : ¬IsZero (Xᘁ : C) := fun h ↦ hX₀ <| (IsZero.iff_id_eq_zero X).2 <|
    rightAdjointMate_injective <| by
      rw [rightAdjointMate_id, rightAdjointMate_zero]
      exact h.eq_of_src _ _
  rw [← Iso.rightAdjointMate_inv, ← Iso.symm_hom]
  exact isIso_doubleDualTrace_of_surjective hX' (surjective_algebraMap_end_rightDual hX)
    a.rightAdjointMate.symm

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then
`End.of (doubleDualTrace (rightAdjointMate a.inv))` is a unit in `End (𝟙_ C)`. -/
theorem isUnit_endOf_doubleDualTrace_rightAdjointMate_inv_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    IsUnit (End.of (doubleDualTrace (rightAdjointMate a.inv))) :=
  (CategoryTheory.isUnit_iff_isIso _).2
    (isIso_doubleDualTrace_rightAdjointMate_inv_of_surjective hX₀ hX a)

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then `doubleDualTrace (rightAdjointMate a.inv)` is
nonzero. -/
theorem doubleDualTrace_rightAdjointMate_inv_ne_zero_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    doubleDualTrace (rightAdjointMate a.inv) ≠ 0 :=
  (isIso_iff_ne_zero _).1 (isIso_doubleDualTrace_rightAdjointMate_inv_of_surjective hX₀ hX a)

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then `squaredNorm a` is an isomorphism. -/
theorem isIso_squaredNorm_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    IsIso (squaredNorm a) := by
  rw [squaredNorm_def]
  have := isIso_doubleDualTrace_of_surjective hX₀ hX a
  have := isIso_doubleDualTrace_rightAdjointMate_inv_of_surjective hX₀ hX a
  exact IsIso.comp_isIso

/-- In a finite semisimple right rigid abelian category with simple tensor unit, if `X` is nonzero
and `algebraMap R (End X)` is surjective, then `squaredNorm a` is nonzero. -/
theorem squaredNorm_ne_zero_of_surjective {X : C} (hX₀ : ¬IsZero X)
    (hX : Function.Surjective (algebraMap R (End X))) (a : X ≅ (Xᘁ : C)ᘁ) :
    squaredNorm a ≠ 0 :=
  (isIso_iff_ne_zero _).1 (isIso_squaredNorm_of_surjective hX₀ hX a)

end CommSemiring

section Field

variable (k : Type w) [Field k] [IsAlgClosed k] [Linear k C] [MonoidalLinear k C]

include k in
/-- For a split simple object `X` in a finite semisimple right rigid category with simple tensor
unit, `doubleDualTrace a.hom` is an isomorphism. -/
theorem isIso_doubleDualTrace_of_simple {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]
    (a : X ≅ (Xᘁ : C)ᘁ) : IsIso (doubleDualTrace a.hom) :=
  isIso_doubleDualTrace_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective a

include k in
/-- For a split simple object `X` in a finite semisimple right rigid category with simple tensor
unit, `End.of (doubleDualTrace a.hom)` is a unit in `End (𝟙_ C)`. -/
theorem isUnit_endOf_doubleDualTrace_of_simple {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]
    (a : X ≅ (Xᘁ : C)ᘁ) : IsUnit (End.of (doubleDualTrace a.hom)) :=
  isUnit_endOf_doubleDualTrace_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective a

include k in
/-- For a split simple object `X` in a finite semisimple right rigid category with simple tensor
unit, `doubleDualTrace a.hom` is nonzero. -/
theorem doubleDualTrace_ne_zero_of_simple {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]
    (a : X ≅ (Xᘁ : C)ᘁ) : doubleDualTrace a.hom ≠ 0 :=
  doubleDualTrace_ne_zero_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective a

include k in
/-- For a split simple object `X` in a finite semisimple right rigid category with simple tensor
unit, `doubleDualTrace (rightAdjointMate a.inv)` is an isomorphism. -/
theorem isIso_doubleDualTrace_rightAdjointMate_inv_of_simple {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (a : X ≅ (Xᘁ : C)ᘁ) :
    IsIso (doubleDualTrace (rightAdjointMate a.inv)) :=
  isIso_doubleDualTrace_rightAdjointMate_inv_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective a

include k in
/-- For a split simple object `X` in a finite semisimple right rigid category with simple tensor
unit, `End.of (doubleDualTrace (rightAdjointMate a.inv))` is a unit in `End (𝟙_ C)`. -/
theorem isUnit_endOf_doubleDualTrace_rightAdjointMate_inv_of_simple {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (a : X ≅ (Xᘁ : C)ᘁ) :
    IsUnit (End.of (doubleDualTrace (rightAdjointMate a.inv))) :=
  isUnit_endOf_doubleDualTrace_rightAdjointMate_inv_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective a

include k in
/-- For a split simple object `X` in a finite semisimple right rigid category with simple tensor
unit, `doubleDualTrace (rightAdjointMate a.inv)` is nonzero. -/
theorem doubleDualTrace_rightAdjointMate_inv_ne_zero_of_simple {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (a : X ≅ (Xᘁ : C)ᘁ) :
    doubleDualTrace (rightAdjointMate a.inv) ≠ 0 :=
  doubleDualTrace_rightAdjointMate_inv_ne_zero_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective a

include k in
/-- For a split simple object `X` in a finite semisimple right rigid category with simple tensor
unit, `squaredNorm a` is an isomorphism. -/
theorem isIso_squaredNorm_of_simple {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]
    (a : X ≅ (Xᘁ : C)ᘁ) : IsIso (squaredNorm a) :=
  isIso_squaredNorm_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective a

include k in
/-- For a split simple object `X` in a finite semisimple right rigid category with simple tensor
unit, `squaredNorm a` is nonzero. -/
theorem squaredNorm_ne_zero_of_simple {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]
    (a : X ≅ (Xᘁ : C)ᘁ) : squaredNorm a ≠ 0 :=
  squaredNorm_ne_zero_of_surjective (Simple.not_isZero X)
    (bijective_algebraMap_end_of_simple k X).surjective a

end Field

end TauCeti
