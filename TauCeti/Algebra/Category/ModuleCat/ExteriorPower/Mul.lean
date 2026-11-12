/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Multiplication of exterior powers in the category of modules

The wedge product gives `⋀ⁱ M ⊗ ⋀ʲ M ⟶ ⋀ⁱ⁺ʲ M`, naturally in `M`. Together with the
zeroth exterior-power isomorphism it is associative and unital, and swapping the factors
introduces the Koszul sign `(-1)^(i*j)`. These sectionwise maps induce multiplication of
exterior powers of sheaves of modules.

The construction packages Mathlib's `exteriorPower.wedge`; the characteristic formula on
wedges uses `exteriorPower.wedge_ιMulti`. The categorical API follows the pattern of
`ModuleCat.symmetricPower.mul` in `TauCeti/Algebra/Category/ModuleCat/SymmetricPower/Mul.lean`.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace ModuleCat.exteriorPower

variable {R : Type u} [CommRing R]

/-- Two maps out of a tensor product of exterior powers agree if they agree on pairs of
pure wedges. -/
lemma tensor_hom_ext {M N P : ModuleCat.{u} R} {i j : ℕ}
    {f g : M.exteriorPower i ⊗ N.exteriorPower j ⟶ P}
    (h : ∀ (x : Fin i → M) (y : Fin j → N), f (mk x ⊗ₜ mk y) = g (mk x ⊗ₜ mk y)) :
    f = g := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply _root_.exteriorPower.linearMap_ext
  apply _root_.AlternatingMap.ext
  intro x
  apply _root_.exteriorPower.linearMap_ext
  exact _root_.AlternatingMap.ext (h x)

/-- Exterior multiplication, as a morphism of modules. -/
noncomputable def mul (M : ModuleCat.{u} R) (i j : ℕ) :
    M.exteriorPower i ⊗ M.exteriorPower j ⟶ M.exteriorPower (i + j) :=
  ofHom (TensorProduct.lift (_root_.exteriorPower.wedge R M i j))

/-- Exterior multiplication is the product in the exterior algebra. -/
@[simp]
lemma coe_mul_tmul (M : ModuleCat.{u} R) {i j : ℕ} (x : M.exteriorPower i)
    (y : M.exteriorPower j) :
    Subtype.val (mul M i j (x ⊗ₜ y)) = x.1 * y.1 :=
  (rfl)

/-- A pure wedge has the same value in the exterior algebra. -/
@[simp]
lemma coe_mk {M : ModuleCat.{u} R} {n : ℕ} (x : Fin n → M) :
    Subtype.val (mk x) = ExteriorAlgebra.ιMulti R n x :=
  _root_.exteriorPower.ιMulti_apply_coe R n x

/-- Multiplication concatenates the factors of two pure wedges, in that order. -/
@[simp]
lemma mul_mk (M : ModuleCat.{u} R) {i j : ℕ} (x : Fin i → M) (y : Fin j → M) :
    mul M i j (mk x ⊗ₜ mk y) = mk (Fin.append x y) :=
  _root_.exteriorPower.wedge_ιMulti x y

/-- Transport of degree does not change an element of the exterior algebra. -/
@[simp]
lemma coe_eqToHom_apply (M : ModuleCat.{u} R) {i j : ℕ} (h : i = j) (x : M.exteriorPower i) :
    Subtype.val (eqToHom (congrArg M.exteriorPower h) x) = x.1 := by
  subst h
  rfl

/-- The exterior power of a module morphism is induced by the exterior-algebra map. -/
@[simp]
lemma coe_map_apply {M N : ModuleCat.{u} R} (f : M ⟶ N) {n : ℕ}
    (x : M.exteriorPower n) :
    Subtype.val (map f n x) = ExteriorAlgebra.map f.hom x.1 :=
  _root_.exteriorPower.coe_map f.hom x

/-- The inverse zeroth-power isomorphism is the scalar inclusion in the exterior algebra. -/
@[simp]
lemma coe_iso₀_inv_apply (M : ModuleCat.{u} R) (r : R) :
    Subtype.val ((iso₀ M).inv r) = algebraMap R (ExteriorAlgebra R M) r := by
  -- The inverse of Mathlib's explicit linear equivalence is scalar multiplication of the
  -- empty wedge; unfold that equivalence to identify its categorical wrapper.
  change (r • _root_.exteriorPower.ιMulti R 0 (fun i : Fin 0 ↦ (Fin.elim0 i : M)) :
    ExteriorAlgebra R M) = _
  simp [Algebra.smul_def]

/-- Exterior multiplication is natural in the module. -/
@[reassoc]
lemma mul_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) (i j : ℕ) :
    (map f i ⊗ₘ map f j) ≫ mul N i j = mul M i j ≫ map f (i + j) := by
  exact MonoidalCategory.tensor_ext fun x y ↦
    _root_.exteriorPower.wedge_map_apply f.hom x y

/-- Exterior multiplication is associative, with the canonical identification of degrees. -/
@[reassoc]
lemma mul_assoc (M : ModuleCat.{u} R) (i j k : ℕ) :
    (mul M i j ▷ M.exteriorPower k) ≫ mul M (i + j) k =
      (α_ _ _ _).hom ≫ (M.exteriorPower i ◁ mul M j k) ≫ mul M i (j + k) ≫
        eqToHom (congrArg M.exteriorPower (add_assoc i j k).symm) := by
  refine MonoidalCategory.tensor_ext₃' fun x y z ↦ Subtype.ext ?_
  simp only [ConcreteCategory.comp_apply]
  -- Explicit rewrites keep the exterior-power carrier and its submodule instances aligned;
  -- `simp` cannot match the whiskering formulas through these dependent coercions.
  rw [MonoidalCategory.whiskerRight_apply, coe_mul_tmul, coe_mul_tmul,
    MonoidalCategory.associator_hom_apply, MonoidalCategory.whiskerLeft_apply,
    coe_eqToHom_apply M (add_assoc i j k).symm, coe_mul_tmul, coe_mul_tmul, _root_.mul_assoc]

/-- Swapping the factors of exterior multiplication introduces the Koszul sign. -/
@[reassoc]
lemma mul_comm (M : ModuleCat.{u} R) (i j : ℕ) :
    (β_ (M.exteriorPower i) (M.exteriorPower j)).hom ≫ mul M j i =
      (-1 : ℤ) ^ (i * j) •
        (mul M i j ≫ eqToHom (congrArg M.exteriorPower (add_comm i j))) := by
  refine tensor_hom_ext fun x y ↦ Subtype.ext ?_
  -- Morphism scalar multiplication is pointwise, and the exterior-power carrier is a
  -- submodule of the exterior algebra; these wrappers obscure scalar rewriting by `simp`.
  change _ = ((-1 : ℤ) ^ (i * j)) •
    Subtype.val ((mul M i j ≫ eqToHom (congrArg M.exteriorPower (add_comm i j)))
      (mk x ⊗ₜ mk y))
  rw [ConcreteCategory.comp_apply, MonoidalCategory.braiding_hom_apply,
    coe_mul_tmul, ConcreteCategory.comp_apply, coe_eqToHom_apply M (add_comm i j),
    coe_mul_tmul, coe_mk, coe_mk]
  simpa only [Units.smul_def,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using
    ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm (R := R) y x

/-- The zeroth exterior power is a left unit for exterior multiplication. -/
@[reassoc]
lemma one_mul (M : ModuleCat.{u} R) (n : ℕ) :
    ((iso₀ M).inv ▷ M.exteriorPower n) ≫ mul M 0 n =
      (λ_ (M.exteriorPower n)).hom ≫ eqToHom (congrArg M.exteriorPower (zero_add n).symm) := by
  refine MonoidalCategory.tensor_ext fun r x ↦ Subtype.ext ?_
  simp only [ConcreteCategory.comp_apply]
  -- As in `mul_assoc`, rewrite explicitly through the dependent exterior-power coercions.
  rw [MonoidalCategory.whiskerRight_apply, coe_mul_tmul,
    MonoidalCategory.leftUnitor_hom_apply, coe_eqToHom_apply M (zero_add n).symm]
  rw [coe_iso₀_inv_apply]
  exact (Algebra.smul_def r x.1).symm

/-- The zeroth exterior power is a right unit for exterior multiplication. -/
@[reassoc]
lemma mul_one (M : ModuleCat.{u} R) (n : ℕ) :
    (M.exteriorPower n ◁ (iso₀ M).inv) ≫ mul M n 0 =
      (ρ_ (M.exteriorPower n)).hom ≫ eqToHom (congrArg M.exteriorPower (add_zero n).symm) := by
  refine MonoidalCategory.tensor_ext fun x r ↦ Subtype.ext ?_
  simp only [ConcreteCategory.comp_apply]
  -- As in `mul_assoc`, rewrite explicitly through the dependent exterior-power coercions.
  rw [MonoidalCategory.whiskerLeft_apply, coe_mul_tmul,
    MonoidalCategory.rightUnitor_hom_apply, coe_eqToHom_apply M (add_zero n).symm]
  rw [coe_iso₀_inv_apply]
  exact (Algebra.commutes r x.1).symm.trans (Algebra.smul_def r x.1).symm

end ModuleCat.exteriorPower
