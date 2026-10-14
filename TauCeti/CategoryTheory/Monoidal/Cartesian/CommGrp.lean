/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Commutative group objects form a preadditive category

Let `C` be a braided cartesian monoidal category. For commutative group objects `A` and `B` of
`C`, the morphisms `A ⟶ B` of `CommGrp C` form a commutative group under the pointwise group
law of `B`: the sum of `f` and `g` is the composite `lift f g ≫ μ`, the product of `f` and `g` in
the group `A.X ⟶ B.X` of points of `B` with values in `A.X`. Composition is additive on both
sides, since precomposition preserves the group law on points and postcomposition with a
homomorphism of group objects does too. Hence `CommGrp C` is a preadditive category, and the
endomorphisms of a commutative group object form a ring (`CategoryTheory.End.ring`) whose
multiplication is composition.

For commutative group schemes over a base scheme `S`, that is `C = Over S`, this is the abelian
group of homomorphisms `Hom_S(G, H)` and the endomorphism ring `End_S(G)`, in which an integer
`n` acts as multiplication by `n` (`CommGrp.intCast_hom_hom_hom`).

The group law is written additively on morphisms of `CommGrp C`, while the group law on points of
a group object is written multiplicatively (Mathlib's scoped instance `CategoryTheory.Hom.group`),
so `f + g` corresponds to the product of the underlying morphisms (`CommGrp.add_hom_hom_hom`).

## Main definitions

* `CategoryTheory.CommGrp.homMk`: the morphism of commutative group objects given by a homomorphism
  of the underlying group objects.
* `CategoryTheory.CommGrp.instPreadditive`: `CommGrp C` is preadditive.

## Main results

* `CategoryTheory.CommGrp.add_hom_hom_hom`, `CategoryTheory.CommGrp.zero_hom_hom_hom`,
  `CategoryTheory.CommGrp.neg_hom_hom_hom`, `CategoryTheory.CommGrp.sub_hom_hom_hom` and
  `CategoryTheory.CommGrp.zsmul_hom_hom_hom`: the group operations on morphisms of `CommGrp C`
  are the pointwise ones.
* `CategoryTheory.CommGrp.intCast_hom_hom_hom`: the integer `n` in the endomorphism ring of a
  commutative group object `A` is the `n`-th power of the identity of `A.X` for the group law on
  points, that is, multiplication by `n`.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.CommGrp

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

/-- The commutative group of morphisms `A ⟶ B` of commutative group objects, under the pointwise
group law of `B`, written additively. It is transported along `InducedCategory.homEquiv` from the
commutative group of morphisms of group objects into the commutative group object `B` (Mathlib's
`Hom.commGroup` in `Grp C`). -/
noncomputable instance instAddCommGroupHom (A B : CommGrp C) : AddCommGroup (A ⟶ B) :=
  (InducedCategory.homEquiv.trans Additive.ofMul).addCommGroup

variable {A B : CommGrp C}

/-- Construct a morphism `A ⟶ B` of commutative group objects from a homomorphism of group objects
`f : A.X ⟶ B.X`. -/
def homMk (f : A.X ⟶ B.X) [IsMonHom f] : A ⟶ B :=
  InducedCategory.homMk (Grp.homMk f)

/-- The underlying morphism of `homMk f` is `f`. -/
@[simp]
theorem homMk_hom_hom_hom (f : A.X ⟶ B.X) [IsMonHom f] : (homMk f).hom.hom.hom = f :=
  (rfl)

/-- The sum of morphisms of commutative group objects is the product of the underlying morphisms
for the group law on points. -/
@[simp]
theorem add_hom_hom_hom (f g : A ⟶ B) : (f + g).hom.hom.hom = f.hom.hom.hom * g.hom.hom.hom :=
  (rfl)

/-- The zero morphism of commutative group objects is the unit point `toUnit _ ≫ η`. -/
@[simp]
theorem zero_hom_hom_hom : (0 : A ⟶ B).hom.hom.hom = 1 :=
  (rfl)

/-- The negative of a morphism of commutative group objects is its inverse for the group law on
points. -/
@[simp]
theorem neg_hom_hom_hom (f : A ⟶ B) : (-f).hom.hom.hom = f.hom.hom.hom⁻¹ :=
  (rfl)

/-- The difference of morphisms of commutative group objects is the quotient of the underlying
morphisms for the group law on points. -/
@[simp]
theorem sub_hom_hom_hom (f g : A ⟶ B) : (f - g).hom.hom.hom = f.hom.hom.hom / g.hom.hom.hom := by
  rw [sub_eq_add_neg, add_hom_hom_hom, neg_hom_hom_hom, div_eq_mul_inv]

/-- A natural multiple of a morphism of commutative group objects is a power of the underlying
morphism for the group law on points. -/
@[simp]
theorem nsmul_hom_hom_hom (f : A ⟶ B) (n : ℕ) : (n • f).hom.hom.hom = f.hom.hom.hom ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, add_hom_hom_hom, ih, pow_succ]

/-- An integer multiple of a morphism of commutative group objects is a power of the underlying
morphism for the group law on points. -/
@[simp]
theorem zsmul_hom_hom_hom (f : A ⟶ B) (n : ℤ) : (n • f).hom.hom.hom = f.hom.hom.hom ^ n := by
  cases n with
  | ofNat n => simp
  | negSucc n => rw [negSucc_zsmul, neg_hom_hom_hom, nsmul_hom_hom_hom, zpow_negSucc]

/-- **Commutative group objects form a preadditive category.** Composition of morphisms of
commutative group objects is additive in each variable. -/
noncomputable instance instPreadditive : Preadditive (CommGrp C) where
  add_comp _ _ _ f g h := hom_ext _ _ <| by simp [MonObj.mul_comp]
  comp_add _ _ _ f g h := hom_ext _ _ <| by simp [MonObj.comp_mul]

/-- The integer `n` in the endomorphism ring of a commutative group object `A` is multiplication
by `n`: the `n`-th power of the identity of `A.X` for the group law on points. -/
@[simp]
theorem intCast_hom_hom_hom (A : CommGrp C) (n : ℤ) :
    (n : End A).hom.hom.hom = 𝟙 A.X ^ n := by
  rw [← zsmul_one, zsmul_hom_hom_hom, End.one_def, id_hom, Grp.id_hom_hom]

/-- The natural number `n` in the endomorphism ring of a commutative group object `A` is
multiplication by `n`: the `n`-th power of the identity of `A.X` for the group law on points. -/
@[simp]
theorem natCast_hom_hom_hom (A : CommGrp C) (n : ℕ) :
    (n : End A).hom.hom.hom = 𝟙 A.X ^ n := by
  rw [← Int.cast_natCast, intCast_hom_hom_hom, zpow_natCast]

end CategoryTheory.CommGrp
