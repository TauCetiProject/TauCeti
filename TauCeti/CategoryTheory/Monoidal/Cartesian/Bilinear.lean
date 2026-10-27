/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import TauCeti.CategoryTheory.Monoidal.Functor

/-!
# Bilinear and alternating morphisms of monoid objects

Let `C` be a cartesian monoidal category and `A`, `B`, `M` monoid objects of `C`. For every object
`T`, the morphisms `T ⟶ A` (the `T`-valued points of `A`) form a monoid under the pointwise
product (Mathlib's `CategoryTheory.Hom.monoid`, scoped in `CategoryTheory.MonObj`). A morphism
`e : A ⊗ B ⟶ M` is *bilinear* (`TauCeti.CategoryTheory.IsBilinear`) if, for every `T`, the pairing
`(a, b) ↦ lift a b ≫ e` of `T`-valued points is multiplicative in each variable, and a morphism
`e : A ⊗ A ⟶ M` is *alternating* (`TauCeti.CategoryTheory.IsAlternating`) if `lift a a ≫ e = 1`
for every point `a`. For group schemes over a base `S`, that is `C = Over S`, these are the
bilinear and alternating pairings of group schemes, such as the Weil pairing
`E[N] ×_S E[N] ⟶ μ_N`.

Both conditions are stated on points, so they are preserved by every monoidal functor between
cartesian monoidal categories, which preserves points, products and the pointwise product. For a
faithful functor they are also reflected, so the bijection between morphisms `A ⊗ B ⟶ M` and
`F.obj A ⊗ F.obj B ⟶ F.obj M` given by a fully faithful monoidal functor
(`CategoryTheory.Functor.FullyFaithful.tensorHomEquiv`, in
`TauCeti.CategoryTheory.Monoidal.Functor`) matches bilinear and alternating morphisms on the two
sides. Applied to an equivalence of categories, such as Grothendieck's Galois correspondence
between finite étale schemes over a field and finite continuous Galois sets, this transports
alternating pairings of group objects.

## Main definitions

* `TauCeti.CategoryTheory.IsBilinear e`: the morphism `e : A ⊗ B ⟶ M` is bilinear.
* `TauCeti.CategoryTheory.IsAlternating e`: the morphism `e : A ⊗ A ⟶ M` vanishes on the
  diagonal.

## Main results

* `TauCeti.CategoryTheory.isAlternating_iff`: alternation is the single identity
  `lift (𝟙 A) (𝟙 A) ≫ e = 1` for the universal point.
* `TauCeti.CategoryTheory.IsBilinear.map` and `TauCeti.CategoryTheory.IsAlternating.map`:
  monoidal functors preserve bilinear and alternating morphisms.
* `CategoryTheory.Functor.isBilinear_map_iff` and `CategoryTheory.Functor.isAlternating_map_iff`:
  faithful monoidal functors reflect them.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

open scoped MonObj Obj

universe v₁ v₂ u₁ u₂

namespace TauCeti.CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]

section Defs

variable {A B M : C} [MonObj M]

/-- A morphism `e : A ⊗ B ⟶ M` of monoid objects is *bilinear* if the induced pairing
`(a, b) ↦ lift a b ≫ e` on `T`-valued points is multiplicative in each variable, for every
object `T`. -/
structure IsBilinear [MonObj A] [MonObj B] (e : A ⊗ B ⟶ M) : Prop where
  /-- Multiplicativity in the first variable. -/
  lift_mul_left {T : C} (a a' : T ⟶ A) (b : T ⟶ B) :
    lift (a * a') b ≫ e = (lift a b ≫ e) * (lift a' b ≫ e)
  /-- Multiplicativity in the second variable. -/
  lift_mul_right {T : C} (a : T ⟶ A) (b b' : T ⟶ B) :
    lift a (b * b') ≫ e = (lift a b ≫ e) * (lift a b' ≫ e)

/-- A morphism `e : A ⊗ A ⟶ M` into a monoid object is *alternating* if it is trivial on the
diagonal: `lift a a ≫ e = 1` for every `T`-valued point `a` of `A`. -/
def IsAlternating (e : A ⊗ A ⟶ M) : Prop :=
  ∀ ⦃T : C⦄ (a : T ⟶ A), lift a a ≫ e = 1

/-- Unfolding `IsAlternating`: `e` is alternating if and only if `lift a a ≫ e = 1` for every
`T`-valued point `a` of `A`. -/
theorem isAlternating_def {e : A ⊗ A ⟶ M} :
    IsAlternating e ↔ ∀ ⦃T : C⦄ (a : T ⟶ A), lift a a ≫ e = 1 :=
  Iff.rfl

/-- An alternating morphism is trivial on every diagonal point `lift a a`. -/
@[simp]
theorem IsAlternating.lift_self {e : A ⊗ A ⟶ M} (h : IsAlternating e) {T : C} (a : T ⟶ A) :
    lift a a ≫ e = 1 :=
  h a

/-- Alternation is a single identity, for the universal point `𝟙 A`: every point `a : T ⟶ A`
factors as `a ≫ 𝟙 A`. -/
theorem isAlternating_iff {e : A ⊗ A ⟶ M} :
    IsAlternating e ↔ lift (𝟙 A) (𝟙 A) ≫ e = 1 := by
  refine ⟨fun h ↦ h _, fun h T a ↦ ?_⟩
  rw [← Category.comp_id a, ← comp_lift_assoc, h, MonObj.comp_one]

/-- Postcomposing a bilinear morphism with a homomorphism of monoid objects gives a bilinear
morphism. -/
theorem IsBilinear.comp [MonObj A] [MonObj B] {N : C} [MonObj N] {e : A ⊗ B ⟶ M}
    (h : IsBilinear e) (g : M ⟶ N) [IsMonHom g] : IsBilinear (e ≫ g) where
  lift_mul_left a a' b := by
    rw [reassoc_of% h.lift_mul_left a a' b, MonObj.mul_comp, Category.assoc, Category.assoc]
  lift_mul_right a b b' := by
    rw [reassoc_of% h.lift_mul_right a b b', MonObj.mul_comp, Category.assoc, Category.assoc]

/-- Precomposing a bilinear morphism with homomorphisms of monoid objects in each variable gives a
bilinear morphism. -/
theorem IsBilinear.tensorHom_comp [MonObj A] [MonObj B] {A' B' : C} [MonObj A'] [MonObj B']
    {e : A ⊗ B ⟶ M} (h : IsBilinear e) (f : A' ⟶ A) (g : B' ⟶ B) [IsMonHom f] [IsMonHom g] :
    IsBilinear ((f ⊗ₘ g) ≫ e) where
  lift_mul_left a a' b := by
    simp only [lift_map_assoc, MonObj.mul_comp, h.lift_mul_left]
  lift_mul_right a b b' := by
    simp only [lift_map_assoc, MonObj.mul_comp, h.lift_mul_right]

/-- Postcomposing an alternating morphism with a homomorphism of monoid objects gives an
alternating morphism. -/
theorem IsAlternating.comp {N : C} [MonObj N] {e : A ⊗ A ⟶ M} (h : IsAlternating e)
    (g : M ⟶ N) [IsMonHom g] : IsAlternating (e ≫ g) := fun _ a ↦ by
  rw [← Category.assoc, h a, MonObj.one_comp]

/-- Precomposing an alternating morphism with `f ⊗ₘ f` gives an alternating morphism. -/
theorem IsAlternating.tensorHom_comp {A' : C} {e : A ⊗ A ⟶ M} (h : IsAlternating e)
    (f : A' ⟶ A) : IsAlternating ((f ⊗ₘ f) ≫ e) := fun _ a ↦ by
  rw [lift_map_assoc, h]

end Defs

section Functor

variable (F : C ⥤ D) [F.Monoidal] {A B M : C} [MonObj M]

/-- A monoidal functor between cartesian monoidal categories preserves bilinear morphisms: if
`e : A ⊗ B ⟶ M` is bilinear, so is `μ F A B ≫ F.map e : F.obj A ⊗ F.obj B ⟶ F.obj M`. -/
theorem IsBilinear.map [MonObj A] [MonObj B] {e : A ⊗ B ⟶ M} (h : IsBilinear e) :
    IsBilinear (Functor.LaxMonoidal.μ F A B ≫ F.map e) := by
  -- Every triple of points of `F.obj A`, `F.obj A`, `F.obj B` (resp. `F.obj A`, `F.obj B`,
  -- `F.obj B`) is the image under `F` of the universal triple on `A ⊗ (A ⊗ B)` (resp.
  -- `A ⊗ (B ⊗ B)`), precomposed with a point of the image of that product.
  constructor
  · intro T a a' b
    let c : T ⟶ F.obj (A ⊗ (A ⊗ B)) :=
      lift a (lift a' b ≫ Functor.LaxMonoidal.μ F A B) ≫ Functor.LaxMonoidal.μ F _ _
    have key := congrArg F.map
      (h.lift_mul_left (fst A (A ⊗ B)) (snd _ _ ≫ fst A B) (snd _ _ ≫ snd A B))
    simp only [Functor.map_comp, F.map_mul, ← Functor.Monoidal.lift_μ] at key
    simpa only [c, Category.assoc, MonObj.comp_mul, comp_lift_assoc, Functor.Monoidal.μ_fst,
      Functor.Monoidal.μ_snd_assoc, Functor.Monoidal.μ_snd, lift_fst, lift_snd_assoc, lift_snd]
      using c ≫= key
  · intro T a b b'
    let c : T ⟶ F.obj (A ⊗ (B ⊗ B)) :=
      lift a (lift b b' ≫ Functor.LaxMonoidal.μ F B B) ≫ Functor.LaxMonoidal.μ F _ _
    have key := congrArg F.map
      (h.lift_mul_right (fst A (B ⊗ B)) (snd _ _ ≫ fst B B) (snd _ _ ≫ snd B B))
    simp only [Functor.map_comp, F.map_mul, ← Functor.Monoidal.lift_μ] at key
    simpa only [c, Category.assoc, MonObj.comp_mul, comp_lift_assoc, Functor.Monoidal.μ_fst,
      Functor.Monoidal.μ_snd_assoc, Functor.Monoidal.μ_snd, lift_fst, lift_snd_assoc, lift_snd]
      using c ≫= key

/-- A monoidal functor between cartesian monoidal categories preserves alternating morphisms: if
`e : A ⊗ A ⟶ M` is alternating, so is `μ F A A ≫ F.map e`. -/
theorem IsAlternating.map {e : A ⊗ A ⟶ M} (h : IsAlternating e) :
    IsAlternating (Functor.LaxMonoidal.μ F A A ≫ F.map e) := by
  rw [isAlternating_iff] at h ⊢
  rw [← F.map_id, Functor.Monoidal.lift_μ_assoc, ← F.map_comp, h, F.map_one]

end Functor

end TauCeti.CategoryTheory

namespace CategoryTheory.Functor

open TauCeti.CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {F : C ⥤ D} [F.Monoidal] {A B M : C} [MonObj M]

/-- A faithful monoidal functor between cartesian monoidal categories reflects bilinear
morphisms. -/
theorem isBilinear_map_iff [F.Faithful] [MonObj A] [MonObj B] {e : A ⊗ B ⟶ M} :
    IsBilinear (Functor.LaxMonoidal.μ F A B ≫ F.map e) ↔ IsBilinear e := by
  refine ⟨fun h ↦ ⟨fun a a' b ↦ F.map_injective ?_, fun a b b' ↦ F.map_injective ?_⟩,
    fun h ↦ h.map F⟩
  · simpa only [F.map_mul, F.map_comp, ← Functor.Monoidal.lift_μ_assoc] using
      h.lift_mul_left (F.map a) (F.map a') (F.map b)
  · simpa only [F.map_mul, F.map_comp, ← Functor.Monoidal.lift_μ_assoc] using
      h.lift_mul_right (F.map a) (F.map b) (F.map b')

/-- A faithful monoidal functor between cartesian monoidal categories reflects alternating
morphisms. -/
theorem isAlternating_map_iff [F.Faithful] {e : A ⊗ A ⟶ M} :
    IsAlternating (Functor.LaxMonoidal.μ F A A ≫ F.map e) ↔ IsAlternating e := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map F⟩
  rw [isAlternating_iff] at h ⊢
  apply F.map_injective
  rwa [F.map_one, F.map_comp, ← Functor.Monoidal.lift_μ_assoc, F.map_id]

end CategoryTheory.Functor
