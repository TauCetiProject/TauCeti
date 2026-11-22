/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.SkewMonoidAlgebra.Basic

/-!
# Equivariant modules and modules over the skew monoid algebra

Let a monoid `Γ` act on a ring `A` by ring endomorphisms (`MulSemiringAction Γ A`). A
*`Γ`-equivariant `A`-module* is an `A`-module `M` with a distributive action of `Γ` satisfying
`g • (a • m) = (g • a) • (g • m)`, Mathlib's `SMulDistribClass Γ A M`; its morphisms are the
`A`-linear maps commuting with the action of `Γ`. They form the category
`TauCeti.EquivariantModuleCat A Γ`.

The *skew monoid algebra* `A ⋊ Γ` is Mathlib's `SkewMonoidAlgebra A Γ`, with multiplication
`single g a * single h b = single (g * h) (a * g • b)`. This file proves that equivariant modules
are exactly the left modules over `A ⋊ Γ`:

* an equivariant module `M` is an `A ⋊ Γ`-module by `single g a • m = a • g • m`;
* conversely a left `A ⋊ Γ`-module `M` is an `A`-module through `a ↦ single 1 a` and carries an
  action of `Γ` through `g ↦ single g 1`; the identity
  `single g 1 * single 1 a = single 1 (g • a) * single g 1` is the compatibility
  `g • (a • m) = (g • a) • (g • m)`.

These two constructions are inverse equivalences of categories
`TauCeti.EquivariantModuleCat.equivalenceModuleSkewMonoidAlgebra`. For the trivial action of `Γ`
on a commutative ring `k`, `k ⋊ Γ` is the monoid algebra `k[Γ]` and an equivariant module is a
representation of `Γ`; the construction follows Mathlib's equivalence between representations
and `k[Γ]`-modules, `Rep.equivalenceModuleMonoidAlgebra`.

## Main definitions

* `TauCeti.EquivariantModuleCat A Γ`: the category of `Γ`-equivariant `A`-modules.
* `TauCeti.EquivariantModuleCat.toEnd`: the action of `A ⋊ Γ` on an equivariant module, and the
  resulting `Module (SkewMonoidAlgebra A Γ)` instance.
* `TauCeti.EquivariantModuleCat.ofModule`: a module over `A ⋊ Γ` as an equivariant module, with
  `TauCeti.EquivariantModuleCat.ofModuleAddEquiv` its identification with the module.
* `TauCeti.EquivariantModuleCat.toModuleSkewMonoidAlgebra`: the functor to modules over `A ⋊ Γ`.
* `TauCeti.EquivariantModuleCat.ofModuleSkewMonoidAlgebra`: the functor from modules over `A ⋊ Γ`.
* `TauCeti.EquivariantModuleCat.equivalenceModuleSkewMonoidAlgebra`: the equivalence of categories
  between equivariant `A`-modules and left modules over `A ⋊ Γ`.

## Main results

* `TauCeti.EquivariantModuleCat.single_smul`: `single g a • m = a • g • m`.
* `TauCeti.EquivariantModuleCat.ofModuleAddEquiv_smul_eq_single_one_smul` and
  `TauCeti.EquivariantModuleCat.ofModuleAddEquiv_smul_eq_of_smul`: on a module over `A ⋊ Γ`, `a`
  acts by `single 1 a` and `g` by `single g 1`.

## References

* I. Reiten and C. Riedtmann, *Skew group algebras in the representation theory of Artin
  algebras*, J. Algebra 92 (1985), 224–282.
-/

public noncomputable section

open CategoryTheory

universe v u w

namespace TauCeti

variable (A : Type u) (Γ : Type w) [Ring A] [Monoid Γ] [MulSemiringAction Γ A]

/-- A *`Γ`-equivariant `A`-module*: an `A`-module with a distributive action of `Γ` satisfying
`g • (a • m) = (g • a) • (g • m)`. With the `A`-linear maps commuting with `Γ` as morphisms these
form a category, equivalent to the category of left modules over the skew monoid algebra
`SkewMonoidAlgebra A Γ` (`TauCeti.EquivariantModuleCat.equivalenceModuleSkewMonoidAlgebra`). -/
structure EquivariantModuleCat where
  /-- The underlying type. -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module A carrier]
  [isDistribMulAction : DistribMulAction Γ carrier]
  [isSMulDistribClass : SMulDistribClass Γ A carrier]

attribute [instance] EquivariantModuleCat.isAddCommGroup EquivariantModuleCat.isModule
  EquivariantModuleCat.isDistribMulAction EquivariantModuleCat.isSMulDistribClass

namespace EquivariantModuleCat

variable {A Γ}

instance : CoeSort (EquivariantModuleCat.{v} A Γ) (Type v) :=
  ⟨carrier⟩

attribute [coe] carrier

/-- A morphism of equivariant modules: an `A`-linear map commuting with the action of `Γ`. -/
structure Hom (X Y : EquivariantModuleCat.{v} A Γ) where
  /-- The underlying `A`-linear map. -/
  hom : X →ₗ[A] Y
  /-- The underlying map commutes with the action of `Γ`. -/
  comm (g : Γ) (x : X) : hom (g • x) = g • hom x

attribute [simp] Hom.comm

instance : Category (EquivariantModuleCat.{v} A Γ) where
  Hom := Hom
  id _ := ⟨LinearMap.id, fun _ _ ↦ rfl⟩
  comp f g := ⟨g.hom ∘ₗ f.hom, fun _ _ ↦ by simp⟩

/-- Two morphisms of equivariant modules agree when their underlying linear maps agree. -/
@[ext]
theorem hom_ext {X Y : EquivariantModuleCat.{v} A Γ} {f g : X ⟶ Y} (h : f.hom = g.hom) :
    f = g := by
  cases f; cases g; congr

@[simp]
theorem id_hom (X : EquivariantModuleCat.{v} A Γ) : (𝟙 X : X ⟶ X).hom = LinearMap.id :=
  (rfl)

@[simp]
theorem comp_hom {X Y Z : EquivariantModuleCat.{v} A Γ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom ∘ₗ f.hom :=
  (rfl)

/-- The morphism of equivariant modules given by an `A`-linear map commuting with `Γ`. -/
abbrev homMk {X Y : EquivariantModuleCat.{v} A Γ} (f : X →ₗ[A] Y)
    (hf : ∀ (g : Γ) (x : X), f (g • x) = g • f x) : X ⟶ Y :=
  ⟨f, hf⟩

/-- The isomorphism of equivariant modules given by an `A`-linear equivalence commuting with
`Γ`. -/
def isoMk {X Y : EquivariantModuleCat.{v} A Γ} (e : X ≃ₗ[A] Y)
    (he : ∀ (g : Γ) (x : X), e (g • x) = g • e x) : X ≅ Y where
  hom := homMk e.toLinearMap he
  inv := homMk e.symm.toLinearMap fun g y ↦ e.injective (by simp [he])
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

@[simp]
theorem isoMk_hom_hom {X Y : EquivariantModuleCat.{v} A Γ} (e : X ≃ₗ[A] Y)
    (he : ∀ (g : Γ) (x : X), e (g • x) = g • e x) : (isoMk e he).hom.hom = e.toLinearMap :=
  (rfl)

@[simp]
theorem isoMk_inv_hom {X Y : EquivariantModuleCat.{v} A Γ} (e : X ≃ₗ[A] Y)
    (he : ∀ (g : Γ) (x : X), e (g • x) = g • e x) : (isoMk e he).inv.hom = e.symm.toLinearMap :=
  (rfl)

/-! ### Equivariant modules as modules over the skew monoid algebra -/

/-- The action of the skew monoid algebra `A ⋊ Γ` on an equivariant module `X`, as a ring
homomorphism to the additive endomorphisms of `X`: `single g a` acts by `x ↦ a • g • x`. -/
def toEnd (X : EquivariantModuleCat.{v} A Γ) : SkewMonoidAlgebra A Γ →+* AddMonoid.End X :=
  SkewMonoidAlgebra.liftNCRingHom (Module.toAddMonoidEnd A X)
    (DistribMulAction.toAddMonoidEnd Γ X) fun {a g} ↦
      AddMonoidHom.ext fun x ↦ (smul_distrib_smul g a x).symm

@[simp]
theorem toEnd_single (X : EquivariantModuleCat.{v} A Γ) (g : Γ) (a : A) (x : X) :
    X.toEnd (SkewMonoidAlgebra.single g a) x = a • g • x := by
  simp [toEnd, SkewMonoidAlgebra.liftNCRingHom]
  -- The product of additive endomorphisms is their composite.
  rfl

/-- An equivariant module is a left module over the skew monoid algebra `A ⋊ Γ`, with
`single g a • x = a • g • x` (`TauCeti.EquivariantModuleCat.single_smul`). -/
instance (X : EquivariantModuleCat.{v} A Γ) : Module (SkewMonoidAlgebra A Γ) X :=
  Module.compHom X X.toEnd

theorem smul_def (X : EquivariantModuleCat.{v} A Γ) (f : SkewMonoidAlgebra A Γ) (x : X) :
    f • x = X.toEnd f x :=
  (rfl)

/-- The action of `single g a` on an equivariant module is `x ↦ a • g • x`. -/
@[simp]
theorem single_smul (X : EquivariantModuleCat.{v} A Γ) (g : Γ) (a : A) (x : X) :
    SkewMonoidAlgebra.single g a • x = a • g • x := by
  rw [smul_def, toEnd_single]

/-- The action of `A` on an equivariant module factors through `A ⋊ Γ`. -/
instance (X : EquivariantModuleCat.{v} A Γ) : IsScalarTower A (SkewMonoidAlgebra A Γ) X where
  smul_assoc a f x := by
    induction f using SkewMonoidAlgebra.induction_on with
    | zero => simp
    | single g b => simp [SkewMonoidAlgebra.smul_single, mul_smul]
    | add f₁ f₂ h₁ h₂ => simp [smul_add, add_smul, h₁, h₂]

/-- A morphism of equivariant modules is linear over the skew monoid algebra. -/
theorem hom_smul {X Y : EquivariantModuleCat.{v} A Γ} (f : X ⟶ Y) (s : SkewMonoidAlgebra A Γ)
    (x : X) : f.hom (s • x) = s • f.hom x := by
  induction s using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single g a => simp
  | add s₁ s₂ h₁ h₂ => simp [add_smul, h₁, h₂]

variable (A Γ) in
-- Exposed so that the module over `A ⋊ Γ` has the equivariant module as its underlying type.
/-- The functor from equivariant `A`-modules to left modules over the skew monoid algebra
`A ⋊ Γ`, on which `single g a` acts by `x ↦ a • g • x`. -/
@[expose]
def toModuleSkewMonoidAlgebra :
    EquivariantModuleCat.{v} A Γ ⥤ ModuleCat.{v} (SkewMonoidAlgebra A Γ) where
  obj X := ModuleCat.of _ X
  map f := ModuleCat.ofHom
    { toFun := f.hom
      map_add' := f.hom.map_add
      map_smul' := hom_smul f }

@[simp]
theorem toModuleSkewMonoidAlgebra_obj (X : EquivariantModuleCat.{v} A Γ) :
    (toModuleSkewMonoidAlgebra A Γ).obj X = ModuleCat.of (SkewMonoidAlgebra A Γ) X :=
  (rfl)

@[simp]
theorem toModuleSkewMonoidAlgebra_map_hom_apply {X Y : EquivariantModuleCat.{v} A Γ}
    (f : X ⟶ Y) (x : X) : ((toModuleSkewMonoidAlgebra A Γ).map f).hom x = f.hom x :=
  (rfl)

/-! ### Modules over the skew monoid algebra as equivariant modules -/

variable (A Γ) in
-- Exposed so that the equivariant module has the module over `A ⋊ Γ` as its underlying type.
/-- A left module over the skew monoid algebra `A ⋊ Γ` as an equivariant `A`-module: `a : A` acts
by `single 1 a` and `g : Γ` by `single g 1`. -/
@[expose]
def ofModule (M : Type v) [AddCommGroup M] [Module (SkewMonoidAlgebra A Γ) M] :
    EquivariantModuleCat.{v} A Γ :=
  letI : Module A M := Module.compHom M (SkewMonoidAlgebra.singleOneRingHom (G := Γ))
  letI : DistribMulAction Γ M := DistribMulAction.compHom M (SkewMonoidAlgebra.of A Γ)
  { carrier := M
    isSMulDistribClass := ⟨fun g a m ↦ by
      -- By definition `g` acts by `single g 1` and `a` by `single 1 a`.
      change (SkewMonoidAlgebra.single g 1 : SkewMonoidAlgebra A Γ) •
          (SkewMonoidAlgebra.single 1 a : SkewMonoidAlgebra A Γ) • m =
        (SkewMonoidAlgebra.single 1 (g • a) : SkewMonoidAlgebra A Γ) •
          (SkewMonoidAlgebra.single g 1 : SkewMonoidAlgebra A Γ) • m
      simp [← mul_smul]⟩ }

section ofModule

variable {M : Type v} [AddCommGroup M] [Module (SkewMonoidAlgebra A Γ) M]

/-- The identity map from the equivariant module `TauCeti.EquivariantModuleCat.ofModule A Γ M` to
the module `M` over `A ⋊ Γ`, as an additive equivalence. -/
def ofModuleAddEquiv : ofModule A Γ M ≃+ M :=
  AddEquiv.refl M

/-- On a module over `A ⋊ Γ`, viewed as an equivariant module, `a : A` acts by `single 1 a`. -/
@[simp]
theorem ofModuleAddEquiv_smul_eq_single_one_smul (a : A) (m : ofModule A Γ M) :
    ofModuleAddEquiv (a • m) =
      (SkewMonoidAlgebra.single 1 a : SkewMonoidAlgebra A Γ) • ofModuleAddEquiv m :=
  (rfl)

/-- On a module over `A ⋊ Γ`, viewed as an equivariant module, `g : Γ` acts by
`SkewMonoidAlgebra.of A Γ g = single g 1`. -/
@[simp]
theorem ofModuleAddEquiv_smul_eq_of_smul (g : Γ) (m : ofModule A Γ M) :
    ofModuleAddEquiv (g • m) = SkewMonoidAlgebra.of A Γ g • ofModuleAddEquiv m :=
  (rfl)

end ofModule

variable (A Γ) in
/-- The functor from left modules over the skew monoid algebra `A ⋊ Γ` to equivariant `A`-modules,
sending a module to `TauCeti.EquivariantModuleCat.ofModule`. -/
@[expose]
def ofModuleSkewMonoidAlgebra :
    ModuleCat.{v} (SkewMonoidAlgebra A Γ) ⥤ EquivariantModuleCat.{v} A Γ where
  obj M := ofModule A Γ M
  map f :=
    homMk
      { toFun := f.hom
        map_add' := f.hom.map_add
        map_smul' := fun a m ↦ f.hom.map_smul (SkewMonoidAlgebra.single 1 a) m }
      fun g m ↦ f.hom.map_smul (SkewMonoidAlgebra.single g 1) m

@[simp]
theorem ofModuleSkewMonoidAlgebra_obj (M : ModuleCat.{v} (SkewMonoidAlgebra A Γ)) :
    (ofModuleSkewMonoidAlgebra A Γ).obj M = ofModule A Γ M :=
  (rfl)

@[simp]
theorem ofModuleSkewMonoidAlgebra_map_hom_apply {M N : ModuleCat.{v} (SkewMonoidAlgebra A Γ)}
    (f : M ⟶ N) (m : ofModule A Γ M) :
    ofModuleAddEquiv (((ofModuleSkewMonoidAlgebra A Γ).map f).hom m) =
      f.hom (ofModuleAddEquiv m) :=
  (rfl)

/-! ### The equivalence -/

/-- The unit of `TauCeti.EquivariantModuleCat.equivalenceModuleSkewMonoidAlgebra`: an equivariant
module is isomorphic, by the identity map, to the equivariant module obtained from its module
structure over `A ⋊ Γ`. -/
def unitIso (X : EquivariantModuleCat.{v} A Γ) : X ≅ ofModule A Γ X :=
  isoMk
    ((ofModuleAddEquiv (A := A) (Γ := Γ) (M := X)).symm.toLinearEquiv fun a x ↦
      ofModuleAddEquiv.injective (by simp))
    fun g x ↦ ofModuleAddEquiv.injective (by simp)

@[simp]
theorem unitIso_hom_hom_apply (X : EquivariantModuleCat.{v} A Γ) (x : X) :
    ofModuleAddEquiv ((unitIso X).hom.hom x) = x :=
  (rfl)

/-- The counit of `TauCeti.EquivariantModuleCat.equivalenceModuleSkewMonoidAlgebra`: a module over
`A ⋊ Γ` is isomorphic, by the identity map, to the module over `A ⋊ Γ` obtained from its
equivariant module structure. -/
def counitIso (M : ModuleCat.{v} (SkewMonoidAlgebra A Γ)) :
    ModuleCat.of (SkewMonoidAlgebra A Γ) (ofModule A Γ M) ≅ M :=
  LinearEquiv.toModuleIso <| ofModuleAddEquiv.toLinearEquiv fun f m ↦ by
    induction f using SkewMonoidAlgebra.induction_on with
    | zero => simp
    | single g a => simp [← mul_smul]
    | add f₁ f₂ h₁ h₂ => simp only [add_smul, map_add, h₁, h₂]

@[simp]
theorem counitIso_hom_hom_apply (M : ModuleCat.{v} (SkewMonoidAlgebra A Γ))
    (m : ofModule A Γ M) : (counitIso M).hom.hom m = ofModuleAddEquiv m :=
  (rfl)

variable (A Γ) in
/-- **Equivariant modules are modules over the skew monoid algebra.** The category of
`Γ`-equivariant `A`-modules is equivalent to the category of left modules over `A ⋊ Γ`: an
equivariant module becomes an `A ⋊ Γ`-module by `single g a • x = a • g • x`, and an
`A ⋊ Γ`-module becomes equivariant through `a ↦ single 1 a` and `g ↦ single g 1`. -/
def equivalenceModuleSkewMonoidAlgebra :
    EquivariantModuleCat.{v} A Γ ≌ ModuleCat.{v} (SkewMonoidAlgebra A Γ) where
  functor := toModuleSkewMonoidAlgebra A Γ
  inverse := ofModuleSkewMonoidAlgebra A Γ
  unitIso := NatIso.ofComponents unitIso fun _ ↦ rfl
  counitIso := NatIso.ofComponents counitIso fun _ ↦ rfl
  functor_unitIso_comp _ := rfl

@[simp]
theorem equivalenceModuleSkewMonoidAlgebra_functor :
    (equivalenceModuleSkewMonoidAlgebra.{v} A Γ).functor = toModuleSkewMonoidAlgebra A Γ :=
  (rfl)

@[simp]
theorem equivalenceModuleSkewMonoidAlgebra_inverse :
    (equivalenceModuleSkewMonoidAlgebra.{v} A Γ).inverse = ofModuleSkewMonoidAlgebra A Γ :=
  (rfl)

instance : (toModuleSkewMonoidAlgebra.{v} A Γ).IsEquivalence :=
  (equivalenceModuleSkewMonoidAlgebra A Γ).isEquivalence_functor

instance : (ofModuleSkewMonoidAlgebra.{v} A Γ).IsEquivalence :=
  (equivalenceModuleSkewMonoidAlgebra A Γ).isEquivalence_inverse

end EquivariantModuleCat

end TauCeti
