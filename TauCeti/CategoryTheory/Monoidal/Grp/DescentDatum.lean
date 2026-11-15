/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.DescentDatum
import TauCeti.CategoryTheory.Comma.Over

/-!
# Products of descent data and descent data on monoid and group objects

Let `p : S' ⟶ S` be a morphism in a category `C` with pullbacks. The slice category `Over S'` is
cartesian monoidal with terminal object `𝟙_ (Over S') = (𝟙 S' : S' ⟶ S')` and binary product
`X₁ ⊗ X₂ = X₁ ×_{S'} X₂`. This file constructs the terminal descent datum `DescentDatum.unit p` on
`𝟙_ (Over S')` and the binary product `D₁.prod D₂` of two descent data on `X₁` and `X₂`, acting
diagonally as `s · (x₁, x₂) = (s · x₁, s · x₂)`, together with their projections, pairing of
morphisms, and canonical comparisons with the base change functor `Over.pullback p`.

A descent datum `D` on a monoid object `X` in `Over S'` is compatible with the monoid structure
(`DescentDatum.IsMon D`) when the unit `η[X] : 𝟙_ (Over S') ⟶ X` and multiplication
`μ[X] : X ⊗ X ⟶ X` intertwine the actions of `unit p`, `D.prod D`, and `D`. When `X` is a group
object, compatibility with the monoid structure automatically implies that inversion `ι[X] : X ⟶ X`
is a morphism of descent data (`DescentDatum.invHom`), by uniqueness of inverses in the group of
morphisms into `X` in `Over S'`.

Canonical base-change descent data on monoid objects satisfy `IsMon` (`baseChange_isMon`), and
`IsMon` transfers across monoid isomorphisms of descent data (`Hom.isMon_iff`) and restricts along
monomorphic monoid homomorphisms (`Hom.isMon_of_mono`).

## Main definitions

* `TauCeti.DescentDatum.unit`: the terminal descent datum on `𝟙_ (Over S')`.
* `TauCeti.DescentDatum.prod`: the diagonal descent datum on `X₁ ⊗ X₂`, with projections `fstHom`
  and `sndHom` and universal pairing `Hom.lift`.
* `TauCeti.DescentDatum.baseChangeUnitHom`, `TauCeti.DescentDatum.baseChangeProdHom`: canonical
  isomorphisms comparing `baseChange p` with `unit` and `prod`.
* `TauCeti.DescentDatum.IsMon`: compatibility of a descent datum with a `MonObj` structure on its
  carrier, bundling `oneHom` and `mulHom`, and `invHom` when the carrier is a `GrpObj`.
* `TauCeti.DescentDatum.ofMono`, `TauCeti.DescentDatum.ofMonoHom`, and
  `TauCeti.DescentDatum.Hom.mkOfCompMono`: restriction of descent data and morphisms of descent data
  along morphisms in `Over S'` whose underlying map in `C` is a monomorphism.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1.
* M. Demazure and A. Grothendieck, *Schémas en groupes* (SGA 3), Exposé I, §2.
-/

public section

namespace TauCeti.DescentDatum

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {S S' : C}

section Unit

variable (p : S' ⟶ S)

/-- The terminal descent datum on `𝟙_ (Over S')`, acting by `s · s₀ = s`. -/
noncomputable def unit : DescentDatum p (𝟙_ (Over S')) where
  act := pullback.fst p ((𝟙_ (Over S')).hom ≫ p)
  act_hom := Category.comp_id _
  lift_act := pullback.lift_fst _ _ _
  act_assoc := by simp

/-- The action of the terminal descent datum is the first projection to `S'`. -/
@[simp]
theorem unit_act : (unit p).act = pullback.fst p ((𝟙_ (Over S')).hom ≫ p) :=
  (rfl)

variable {p}

/-- The unique morphism from a descent datum `D` on `X` to `unit p`, with underlying morphism
`toUnit X : X ⟶ 𝟙_ (Over S')`. -/
noncomputable def Hom.toUnit {X : Over S'} (D : DescentDatum p X) : Hom D (unit p) where
  hom := CartesianMonoidalCategory.toUnit X
  map_act := by simp [D.act_hom]

/-- The underlying morphism over `S'` of `D.toUnit` is `CartesianMonoidalCategory.toUnit X`. -/
@[simp]
theorem Hom.toUnit_hom {X : Over S'} (D : DescentDatum p X) :
    (Hom.toUnit D).hom = CartesianMonoidalCategory.toUnit X :=
  (rfl)

/-- Morphisms of descent data into `unit p` are unique. -/
instance subsingleton_hom_unit {X : Over S'} (D : DescentDatum p X) :
    Subsingleton (Hom D (unit p)) where
  allEq f g := Hom.ext (toUnit_unique f.hom g.hom)

variable (p) in
/-- The canonical isomorphism of descent data `baseChange p (𝟙_ (Over S)) ⟶ unit p`, whose
underlying morphism in `Over S'` is the oplax unit `Functor.OplaxMonoidal.η (Over.pullback p)`. -/
noncomputable def baseChangeUnitHom :
    Hom (baseChange p (𝟙_ (Over S))) (unit p) :=
  Hom.toUnit (baseChange p (𝟙_ (Over S)))

/-- The underlying morphism of `baseChangeUnitHom p` is the oplax monoidal counit of
`Over.pullback p`. -/
@[simp]
theorem baseChangeUnitHom_hom (p : S' ⟶ S) :
    (baseChangeUnitHom p).hom = Functor.OplaxMonoidal.η (Over.pullback p) :=
  toUnit_unique _ _

/-- `baseChangeUnitHom p` is an isomorphism of descent data. -/
instance isIso_baseChangeUnitHom_hom (p : S' ⟶ S) : IsIso (baseChangeUnitHom p).hom := by
  rw [baseChangeUnitHom_hom]
  infer_instance

/-- The inverse of `baseChangeUnitHom p` has underlying morphism `Functor.LaxMonoidal.ε`. -/
theorem baseChangeUnitHom_inv_hom (p : S' ⟶ S) :
    (baseChangeUnitHom p).inv.hom = Functor.LaxMonoidal.ε (Over.pullback p) := by
  simp

end Unit

section Prod

variable {p : S' ⟶ S} {X₁ X₂ Y₁ Y₂ Z : Over S'}

/-- The map of action spaces `S' ×_S (X₁ ⊗ X₂) ⟶ S' ×_S X₁` induced by the first projection. -/
private noncomputable def prodActionFst (p : S' ⟶ S) (X₁ X₂ : Over S') :
    pullback p ((X₁ ⊗ X₂).hom ≫ p) ⟶ pullback p (X₁.hom ≫ p) :=
  pullback.map p ((X₁ ⊗ X₂).hom ≫ p) p (X₁.hom ≫ p) (𝟙 S') (fst X₁ X₂).left (𝟙 S)
    (by simp) (by simp)

/-- The map of action spaces `S' ×_S (X₁ ⊗ X₂) ⟶ S' ×_S X₂` induced by the second projection. -/
private noncomputable def prodActionSnd (p : S' ⟶ S) (X₁ X₂ : Over S') :
    pullback p ((X₁ ⊗ X₂).hom ≫ p) ⟶ pullback p (X₂.hom ≫ p) :=
  pullback.map p ((X₁ ⊗ X₂).hom ≫ p) p (X₂.hom ≫ p) (𝟙 S') (snd X₁ X₂).left (𝟙 S)
    (by simp) (by simp [pullback.condition_assoc])

/-- The product of two descent data `D₁` on `X₁` and `D₂` on `X₂`, acting diagonally on
`X₁ ⊗ X₂ = X₁ ×_{S'} X₂` by `s · (x₁, x₂) = (s · x₁, s · x₂)`. -/
noncomputable def prod (D₁ : DescentDatum p X₁) (D₂ : DescentDatum p X₂) :
    DescentDatum p (X₁ ⊗ X₂) where
  act := pullback.lift (prodActionFst p X₁ X₂ ≫ D₁.act) (prodActionSnd p X₁ X₂ ≫ D₂.act) <| by
    simp [prodActionFst, prodActionSnd]
  act_hom := by simp [prodActionFst]
  lift_act := by
    refine Over.tensorObj_ext _ _ ?_ ?_
    · have h₁ : pullback.lift (X₁ ⊗ X₂).hom (𝟙 (X₁ ⊗ X₂).left) (by simp) ≫ prodActionFst p X₁ X₂ =
          (fst X₁ X₂).left ≫ pullback.lift X₁.hom (𝟙 X₁.left) (by simp) := by
        refine pullback.hom_ext ?_ ?_ <;> simp [prodActionFst]
      rw [Category.assoc, pullback.lift_fst, reassoc_of% h₁, D₁.lift_act, Category.comp_id]
      simp
    · have h₂ : pullback.lift (X₁ ⊗ X₂).hom (𝟙 (X₁ ⊗ X₂).left) (by simp) ≫ prodActionSnd p X₁ X₂ =
          (snd X₁ X₂).left ≫ pullback.lift X₂.hom (𝟙 X₂.left) (by simp) := by
        refine pullback.hom_ext ?_ ?_ <;> simp [prodActionSnd, pullback.condition]
      rw [Category.assoc, pullback.lift_snd, reassoc_of% h₂, D₂.lift_act, Category.comp_id]
      simp
  act_assoc := by
    refine Over.tensorObj_ext _ _ ?_ ?_
    · have key₁ := pullback.map p (pullback.fst p ((X₁ ⊗ X₂).hom ≫ p) ≫ p)
        p (pullback.fst p (X₁.hom ≫ p) ≫ p) (𝟙 S') (prodActionFst p X₁ X₂) (𝟙 S)
        (by simp) (by simp [prodActionFst]) ≫= D₁.act_assoc
      simp only [Category.assoc, pullback.lift_fst]
      simp only [← Category.assoc] at key₁ ⊢
      convert key₁ using 2 <;> refine pullback.hom_ext ?_ ?_ <;> simp [prodActionFst]
    · have key₂ := pullback.map p (pullback.fst p ((X₁ ⊗ X₂).hom ≫ p) ≫ p)
        p (pullback.fst p (X₂.hom ≫ p) ≫ p) (𝟙 S') (prodActionSnd p X₁ X₂) (𝟙 S)
        (by simp) (by simp [prodActionSnd]) ≫= D₂.act_assoc
      simp only [Category.assoc, pullback.lift_snd]
      simp only [← Category.assoc] at key₂ ⊢
      convert key₂ using 2 <;> refine pullback.hom_ext ?_ ?_ <;> simp [prodActionSnd]

/-- The first coordinate of the diagonal action on `X₁ ⊗ X₂` is the action of `D₁`. -/
@[reassoc]
theorem prod_act_fst (D₁ : DescentDatum p X₁) (D₂ : DescentDatum p X₂) :
    (D₁.prod D₂).act ≫ (fst X₁ X₂).left =
      pullback.map p ((X₁ ⊗ X₂).hom ≫ p) p (X₁.hom ≫ p) (𝟙 S') (fst X₁ X₂).left (𝟙 S)
        (by simp) (by simp) ≫ D₁.act :=
  pullback.lift_fst _ _ _

/-- The second coordinate of the diagonal action on `X₁ ⊗ X₂` is the action of `D₂`. -/
@[reassoc]
theorem prod_act_snd (D₁ : DescentDatum p X₁) (D₂ : DescentDatum p X₂) :
    (D₁.prod D₂).act ≫ (snd X₁ X₂).left =
      pullback.map p ((X₁ ⊗ X₂).hom ≫ p) p (X₂.hom ≫ p) (𝟙 S') (snd X₁ X₂).left (𝟙 S)
        (by simp) (by simp [pullback.condition_assoc]) ≫ D₂.act :=
  pullback.lift_snd _ _ _

/-- Also rewrite `prod_act_fst` when `(fst X₁ X₂).left` is unfolded to `pullback.fst`. -/
@[reassoc (attr := simp)]
theorem prod_act_pullback_fst (D₁ : DescentDatum p X₁) (D₂ : DescentDatum p X₂) :
    (D₁.prod D₂).act ≫ pullback.fst X₁.hom X₂.hom =
      pullback.map p ((X₁ ⊗ X₂).hom ≫ p) p (X₁.hom ≫ p) (𝟙 S') (pullback.fst X₁.hom X₂.hom)
        (𝟙 S) (by simp) (by simp) ≫ D₁.act :=
  pullback.lift_fst _ _ _

/-- Also rewrite `prod_act_snd` when `(snd X₁ X₂).left` is unfolded to `pullback.snd`. -/
@[reassoc (attr := simp)]
theorem prod_act_pullback_snd (D₁ : DescentDatum p X₁) (D₂ : DescentDatum p X₂) :
    (D₁.prod D₂).act ≫ pullback.snd X₁.hom X₂.hom =
      pullback.map p ((X₁ ⊗ X₂).hom ≫ p) p (X₂.hom ≫ p) (𝟙 S') (pullback.snd X₁.hom X₂.hom)
        (𝟙 S) (by simp) (by simp [pullback.condition_assoc]) ≫ D₂.act :=
  pullback.lift_snd _ _ _

/-- The first projection `X₁ ⊗ X₂ ⟶ X₁` as a morphism of descent data. -/
noncomputable def fstHom (D₁ : DescentDatum p X₁) (D₂ : DescentDatum p X₂) :
    Hom (D₁.prod D₂) D₁ where
  hom := fst X₁ X₂
  map_act := (prod_act_fst D₁ D₂).symm

/-- The underlying morphism of `fstHom D₁ D₂` is `fst X₁ X₂`. -/
@[simp]
theorem fstHom_hom (D₁ : DescentDatum p X₁) (D₂ : DescentDatum p X₂) :
    (fstHom D₁ D₂).hom = fst X₁ X₂ :=
  (rfl)

/-- The second projection `X₁ ⊗ X₂ ⟶ X₂` as a morphism of descent data. -/
noncomputable def sndHom (D₁ : DescentDatum p X₁) (D₂ : DescentDatum p X₂) :
    Hom (D₁.prod D₂) D₂ where
  hom := snd X₁ X₂
  map_act := (prod_act_snd D₁ D₂).symm

/-- The underlying morphism of `sndHom D₁ D₂` is `snd X₁ X₂`. -/
@[simp]
theorem sndHom_hom (D₁ : DescentDatum p X₁) (D₂ : DescentDatum p X₂) :
    (sndHom D₁ D₂).hom = snd X₁ X₂ :=
  (rfl)

/-- Universal pairing of morphisms of descent data into a product descent datum. -/
noncomputable def Hom.lift {E : DescentDatum p Z} {D₁ : DescentDatum p X₁} {D₂ : DescentDatum p X₂}
    (f : Hom E D₁) (g : Hom E D₂) : Hom E (D₁.prod D₂) where
  hom := CartesianMonoidalCategory.lift f.hom g.hom
  map_act := by
    refine Over.tensorObj_ext _ _ ?_ ?_
    · simp only [Category.assoc, Over.lift_left, pullback.lift_fst, prod_act_pullback_fst,
        ← f.map_act]
      rw [← Category.assoc]
      refine congrArg (· ≫ D₁.act) (pullback.hom_ext ?_ ?_) <;> simp
    · simp only [Category.assoc, Over.lift_left, pullback.lift_snd, prod_act_pullback_snd,
        ← g.map_act]
      rw [← Category.assoc]
      refine congrArg (· ≫ D₂.act) (pullback.hom_ext ?_ ?_) <;> simp

/-- The underlying morphism of `Hom.lift f g` is `CartesianMonoidalCategory.lift f.hom g.hom`. -/
@[simp]
theorem Hom.lift_hom {E : DescentDatum p Z} {D₁ : DescentDatum p X₁} {D₂ : DescentDatum p X₂}
    (f : Hom E D₁) (g : Hom E D₂) :
    (Hom.lift f g).hom = CartesianMonoidalCategory.lift f.hom g.hom :=
  (rfl)

/-- Composing `Hom.lift f g` with `fstHom` recovers `f`. -/
@[simp]
theorem fstHom_comp_lift {E : DescentDatum p Z} {D₁ : DescentDatum p X₁} {D₂ : DescentDatum p X₂}
    (f : Hom E D₁) (g : Hom E D₂) :
    (fstHom D₁ D₂).comp (Hom.lift f g) = f :=
  Hom.ext (by simp)

/-- Composing `Hom.lift f g` with `sndHom` recovers `g`. -/
@[simp]
theorem sndHom_comp_lift {E : DescentDatum p Z} {D₁ : DescentDatum p X₁} {D₂ : DescentDatum p X₂}
    (f : Hom E D₁) (g : Hom E D₂) :
    (sndHom D₁ D₂).comp (Hom.lift f g) = g :=
  Hom.ext (by simp)

/-- Two morphisms of descent data into `D₁.prod D₂` are equal if their composites with `fstHom`
and `sndHom` agree. -/
theorem Hom.prod_ext {E : DescentDatum p Z} {D₁ : DescentDatum p X₁} {D₂ : DescentDatum p X₂}
    {f g : Hom E (D₁.prod D₂)}
    (h₁ : (fstHom D₁ D₂).comp f = (fstHom D₁ D₂).comp g)
    (h₂ : (sndHom D₁ D₂).comp f = (sndHom D₁ D₂).comp g) : f = g :=
  Hom.ext (CartesianMonoidalCategory.hom_ext f.hom g.hom
    (by simpa using congrArg Hom.hom h₁) (by simpa using congrArg Hom.hom h₂))

/-- Tensor product `f₁ ⊗ₘ f₂` of two morphisms of descent data. -/
noncomputable def Hom.prodMap {D₁ : DescentDatum p X₁} {D₂ : DescentDatum p X₂}
    {E₁ : DescentDatum p Y₁} {E₂ : DescentDatum p Y₂}
    (f₁ : Hom D₁ E₁) (f₂ : Hom D₂ E₂) : Hom (D₁.prod D₂) (E₁.prod E₂) :=
  Hom.lift (f₁.comp (fstHom D₁ D₂)) (f₂.comp (sndHom D₁ D₂))

/-- The underlying morphism of `Hom.prodMap f₁ f₂` is `f₁.hom ⊗ₘ f₂.hom`. -/
@[simp]
theorem Hom.prodMap_hom {D₁ : DescentDatum p X₁} {D₂ : DescentDatum p X₂}
    {E₁ : DescentDatum p Y₁} {E₂ : DescentDatum p Y₂}
    (f₁ : Hom D₁ E₁) (f₂ : Hom D₂ E₂) :
    (Hom.prodMap f₁ f₂).hom = f₁.hom ⊗ₘ f₂.hom := by
  simp [Hom.prodMap, tensorHom_def]

variable (p) in
/-- The canonical isomorphism of descent data
`baseChange p (X₀ ⊗ Y₀) ⟶ (baseChange p X₀).prod (baseChange p Y₀)`, whose underlying morphism in
`Over S'` is the oplax monoidal comultiplication `Functor.OplaxMonoidal.δ (Over.pullback p)`. -/
noncomputable def baseChangeProdHom (X₀ Y₀ : Over S) :
    Hom (baseChange p (X₀ ⊗ Y₀)) ((baseChange p X₀).prod (baseChange p Y₀)) :=
  Hom.lift (baseChangeHom p (fst X₀ Y₀)) (baseChangeHom p (snd X₀ Y₀))

/-- The underlying morphism of `baseChangeProdHom p X₀ Y₀` is `Functor.OplaxMonoidal.δ`. -/
@[simp]
theorem baseChangeProdHom_hom (p : S' ⟶ S) (X₀ Y₀ : Over S) :
    (baseChangeProdHom p X₀ Y₀).hom = Functor.OplaxMonoidal.δ (Over.pullback p) X₀ Y₀ := by
  rw [baseChangeProdHom, Hom.lift_hom, baseChangeHom_hom, baseChangeHom_hom,
    Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory]
  rfl

/-- `baseChangeProdHom p X₀ Y₀` is an isomorphism of descent data. -/
instance isIso_baseChangeProdHom_hom (p : S' ⟶ S) (X₀ Y₀ : Over S) :
    IsIso (baseChangeProdHom p X₀ Y₀).hom := by
  rw [baseChangeProdHom_hom]
  infer_instance

/-- The inverse of `baseChangeProdHom p X₀ Y₀` has underlying morphism `Functor.LaxMonoidal.μ`. -/
theorem baseChangeProdHom_inv_hom (p : S' ⟶ S) (X₀ Y₀ : Over S) :
    (baseChangeProdHom p X₀ Y₀).inv.hom = Functor.LaxMonoidal.μ (Over.pullback p) X₀ Y₀ := by
  simp

end Prod

section IsMon

variable {p : S' ⟶ S}

/-- Compatibility of a descent datum `D` on a monoid object `X` in `Over S'` with the monoid
structure: the unit `η[X]` and multiplication `μ[X]` intertwine the actions of `unit p`,
`D.prod D`, and `D`. When `X` is a group object, inversion is automatically compatible as well
(`invHom`). -/
class IsMon {X : Over S'} [MonObj X] (D : DescentDatum p X) : Prop where
  /-- The unit `η[X] : 𝟙_ (Over S') ⟶ X` intertwines `unit p` and `D`. -/
  one_act :
    pullback.map p ((𝟙_ (Over S')).hom ≫ p) p (X.hom ≫ p) (𝟙 S') η[X].left (𝟙 S)
        (by simp) (by simp) ≫ D.act =
      (unit p).act ≫ η[X].left
  /-- The multiplication `μ[X] : X ⊗ X ⟶ X` intertwines `D.prod D` and `D`. -/
  mul_act :
    pullback.map p ((X ⊗ X).hom ≫ p) p (X.hom ≫ p) (𝟙 S') μ[X].left (𝟙 S)
        (by simp) (by simp) ≫ D.act =
      (D.prod D).act ≫ μ[X].left

attribute [reassoc] IsMon.one_act IsMon.mul_act

/-- The unit `η[X]` of a monoid object with a compatible descent datum `D`, bundled as a morphism
of descent data `unit p ⟶ D`. -/
noncomputable def oneHom {X : Over S'} [MonObj X] (D : DescentDatum p X) [D.IsMon] :
    Hom (unit p) D where
  hom := η[X]
  map_act := IsMon.one_act

/-- The underlying morphism of `oneHom D` is `η[X]`. -/
@[simp]
theorem oneHom_hom {X : Over S'} [MonObj X] (D : DescentDatum p X) [D.IsMon] :
    (oneHom D).hom = η[X] :=
  (rfl)

/-- The multiplication `μ[X]` of a monoid object with a compatible descent datum `D`, bundled as a
morphism of descent data `D.prod D ⟶ D`. -/
noncomputable def mulHom {X : Over S'} [MonObj X] (D : DescentDatum p X) [D.IsMon] :
    Hom (D.prod D) D where
  hom := μ[X]
  map_act := IsMon.mul_act

/-- The underlying morphism of `mulHom D` is `μ[X]`. -/
@[simp]
theorem mulHom_hom {X : Over S'} [MonObj X] (D : DescentDatum p X) [D.IsMon] :
    (mulHom D).hom = μ[X] :=
  (rfl)

/-- **Automatic equivariance of inversion.** If `D` is a monoid-compatible descent datum on a
group object `G` in `Over S'`, then the inversion `ι[G] : G ⟶ G` automatically intertwines `D.act`:
in the group of morphisms `Over.mk (pullback.fst p (G.hom ≫ p)) ⟶ G` in `Over S'`, the
shifted-inversion map `(s, g) ↦ s · g⁻¹` is a right inverse to `D.act` because `D` preserves
multiplication and the identity. -/
@[reassoc]
theorem IsMon.inv_act {G : Over S'} [GrpObj G] (D : DescentDatum p G) [D.IsMon] :
    pullback.map p (G.hom ≫ p) p (G.hom ≫ p) (𝟙 S') ι[G].left (𝟙 S)
        (by simp) (by simp) ≫ D.act =
      D.act ≫ ι[G].left := by
  let A : Over S' := Over.mk (pullback.fst p (G.hom ≫ p))
  let α : A ⟶ G := Over.homMk D.act (by simp [A])
  let β : A ⟶ G := Over.homMk
    (pullback.map p (G.hom ≫ p) p (G.hom ≫ p) (𝟙 S') ι[G].left (𝟙 S)
      (by simp) (by simp) ≫ D.act) (by simp [A])
  suffices h : β = α⁻¹ by
    simpa [α, β, Hom.inv_def] using congrArg CommaMorphism.left h
  refine (mul_eq_one_iff_inv_eq.mp ?_).symm
  rw [Hom.mul_def, Hom.one_def]
  ext1
  -- Express `(α * β).left` via `(D.prod D).act ≫ μ[G].left` applied to `(g, g⁻¹)`.
  let δ : A.left ⟶ pullback p ((G ⊗ G).hom ≫ p) :=
    pullback.map p (G.hom ≫ p) p ((G ⊗ G).hom ≫ p) (𝟙 S')
      (CartesianMonoidalCategory.lift (𝟙 G) ι[G]).left (𝟙 S) (by simp) (by simp)
  have hlift : (CartesianMonoidalCategory.lift α β).left = δ ≫ (D.prod D).act := by
    refine Over.tensorObj_ext _ _ ?_ ?_
    · simp only [Over.lift_left, pullback.lift_fst, Category.assoc, prod_act_pullback_fst,
        α, Over.homMk_left]
      refine Eq.trans (Category.id_comp D.act).symm
        (Eq.trans (congrArg (· ≫ D.act) ?_) (Category.assoc _ _ _))
      refine pullback.hom_ext ?_ ?_ <;> simp [δ]
    · simp only [Over.lift_left, pullback.lift_snd, Category.assoc, prod_act_pullback_snd,
        β, Over.homMk_left]
      refine Eq.trans (congrArg (· ≫ D.act) ?_) (Category.assoc _ _ _)
      refine pullback.hom_ext ?_ ?_ <;> simp [δ]
  have hmap_mul : δ ≫ pullback.map p ((G ⊗ G).hom ≫ p) p (G.hom ≫ p) (𝟙 S') μ[G].left (𝟙 S)
      (by simp) (by simp) =
      pullback.map p (G.hom ≫ p) p ((𝟙_ (Over S')).hom ≫ p) (𝟙 S') (toUnit G).left (𝟙 S)
        (by simp) (by simp) ≫
        pullback.map p ((𝟙_ (Over S')).hom ≫ p) p (G.hom ≫ p) (𝟙 S') η[G].left (𝟙 S)
          (by simp) (by simp) := by
    have hinv : pullback.lift (𝟙 G.left) ι[G].left (by simp) ≫ μ[G].left =
        G.hom ≫ η[G].left := by
      have h := congrArg Over.Hom.left (GrpObj.right_inv G)
      simpa only [Over.comp_left, Over.lift_left, Over.id_left, Over.toUnit_left] using h
    refine pullback.hom_ext ?_ ?_
    · simp [δ]
    · simp [δ, hinv]
  simp only [Over.comp_left, hlift, Category.assoc, ← IsMon.mul_act, reassoc_of% hmap_mul,
    IsMon.one_act]
  simp [A]

/-- The inversion `ι[G]` of a group object with a monoid-compatible descent datum `D`, bundled as a
morphism of descent data `D ⟶ D`. -/
noncomputable def invHom {G : Over S'} [GrpObj G] (D : DescentDatum p G) [D.IsMon] :
    Hom D D where
  hom := ι[G]
  map_act := IsMon.inv_act D

/-- The underlying morphism of `invHom D` is `ι[G]`. -/
@[simp]
theorem invHom_hom {G : Over S'} [GrpObj G] (D : DescentDatum p G) [D.IsMon] :
    (invHom D).hom = ι[G] :=
  (rfl)

/-- The canonical descent datum on the base change of a monoid object over `S` is compatible with
its base-changed monoid structure. -/
instance baseChange_isMon (p : S' ⟶ S) (X₀ : Over S) [MonObj X₀] :
    (baseChange p X₀).IsMon where
  one_act := by
    let φ := (baseChangeHom p η[X₀]).comp (baseChangeUnitHom p).inv
    have hφ : φ.hom = η[(Over.pullback p).obj X₀] := by simp [φ, Functor.obj.η_def]
    simpa only [hφ] using φ.map_act
  mul_act := by
    let ψ := (baseChangeHom p μ[X₀]).comp (baseChangeProdHom p X₀ X₀).inv
    have hψ : ψ.hom = μ[(Over.pullback p).obj X₀] := by simp [ψ, Functor.obj.μ_def]
    simpa only [hψ] using ψ.map_act

/-- **Restriction of `IsMon` along a monomorphic homomorphism.** If `f : D ⟶ E` is a morphism of
descent data whose underlying morphism `f.hom : X ⟶ Y` is a monoid homomorphism with monic
underlying map in `C`, and `E` is compatible with the monoid structure on `Y`, then `D` is
compatible with the monoid structure on `X`. -/
theorem Hom.isMon_of_mono {X Y : Over S'} [MonObj X] [MonObj Y]
    {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E)
    [Mono f.hom.left] [IsMonHom f.hom] [E.IsMon] : D.IsMon where
  one_act := by
    let g₁ : Hom (unit p) E := oneHom E
    have hg₁ : g₁.hom = η[X] ≫ f.hom := by simp [g₁]
    have h₁ := g₁.map_act
    simp only [hg₁, Over.comp_left] at h₁
    have hmap : pullback.map p ((𝟙_ (Over S')).hom ≫ p) p (Y.hom ≫ p) (𝟙 S')
          (η[X].left ≫ f.hom.left) (𝟙 S) (by simp) (by simp [Over.w_assoc]) =
        pullback.map p ((𝟙_ (Over S')).hom ≫ p) p (X.hom ≫ p) (𝟙 S') η[X].left (𝟙 S)
          (by simp) (by simp) ≫
        pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') f.hom.left (𝟙 S)
          (by simp) (by simp) := by
      refine pullback.hom_ext ?_ ?_ <;> simp
    rw [← cancel_mono f.hom.left]
    simpa only [hmap, Category.assoc, f.map_act] using h₁
  mul_act := by
    let g₂ : Hom (D.prod D) E := (mulHom E).comp (f.prodMap f)
    have hg₂ : g₂.hom = μ[X] ≫ f.hom := by simp [g₂]
    have h₂ := g₂.map_act
    simp only [hg₂, Over.comp_left] at h₂
    have hmap : pullback.map p ((X ⊗ X).hom ≫ p) p (Y.hom ≫ p) (𝟙 S')
          (μ[X].left ≫ f.hom.left) (𝟙 S) (by simp) (by simp [Over.w_assoc]) =
        pullback.map p ((X ⊗ X).hom ≫ p) p (X.hom ≫ p) (𝟙 S') μ[X].left (𝟙 S)
          (by simp) (by simp) ≫
        pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') f.hom.left (𝟙 S)
          (by simp) (by simp) := by
      refine pullback.hom_ext ?_ ?_ <;> simp
    rw [← cancel_mono f.hom.left]
    simpa only [hmap, Category.assoc, f.map_act] using h₂

/-- If `f : D ⟶ E` is an isomorphism of descent data whose underlying morphism in `Over S'` is a
monoid isomorphism, then `D` is compatible with the monoid structure if and only if `E` is. -/
theorem Hom.isMon_iff {X Y : Over S'} [MonObj X] [MonObj Y]
    {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E)
    [IsIso f.hom] [IsMonHom f.hom] : D.IsMon ↔ E.IsMon := by
  have : IsIso f.hom.left := Over.isIso_left f.hom
  have : IsIso f.inv.hom.left := Over.isIso_left f.inv.hom
  have : IsMonHom f.inv.hom := by
    have : IsMonHom (asIso f.hom).hom := ‹_›
    simpa [Hom.inv_hom] using (inferInstance : IsMonHom (asIso f.hom).inv)
  exact ⟨fun _ ↦ f.inv.isMon_of_mono, fun _ ↦ f.isMon_of_mono⟩

end IsMon

section MonoRestrict

variable {p : S' ⟶ S}

/-- **Restriction of a descent datum along a monomorphism.** If `f : X ⟶ Y` in `Over S'` has monic
underlying morphism in `C` and `act : pullback p (X.hom ≫ p) ⟶ X.left` intertwines `f.left` with
the action of `E : DescentDatum p Y`, then `act` automatically satisfies `act_hom`, `lift_act`, and
`act_assoc`, defining a descent datum on `X`. -/
noncomputable def ofMono {X Y : Over S'} (E : DescentDatum p Y) (f : X ⟶ Y) [Mono f.left]
    (act : pullback p (X.hom ≫ p) ⟶ X.left)
    (hact : act ≫ f.left = pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') f.left (𝟙 S)
      (by simp) (by simp) ≫ E.act) :
    DescentDatum p X where
  act := act
  act_hom := (congrArg (act ≫ ·) (Over.w f)).symm.trans <| by
    rw [reassoc_of% hact, E.act_hom, pullback.lift_fst, Category.comp_id]
  lift_act := by
    rw [← cancel_mono f.left, Category.id_comp, Category.assoc, hact]
    have hmap : pullback.lift X.hom (𝟙 X.left) (by simp) ≫
        pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') f.left (𝟙 S) (by simp) (by simp) =
        f.left ≫ pullback.lift Y.hom (𝟙 Y.left) (by simp) := by
      refine pullback.hom_ext ?_ ?_ <;> simp
    rw [reassoc_of% hmap, E.lift_act, Category.comp_id]
  act_assoc := by
    have hhom : act ≫ X.hom = pullback.fst p (X.hom ≫ p) :=
      (congrArg (act ≫ ·) (Over.w f)).symm.trans <| by
        rw [reassoc_of% hact, E.act_hom, pullback.lift_fst, Category.comp_id]
    rw [← cancel_mono f.left]
    simp only [Category.assoc, hact]
    let m := pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') f.left (𝟙 S) (by simp) (by simp)
    let M := pullback.map p (pullback.fst p (X.hom ≫ p) ≫ p)
      p (pullback.fst p (Y.hom ≫ p) ≫ p) (𝟙 S') m (𝟙 S) (by simp) (by simp [m])
    have h₁ : pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
          (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ act)
          (by rw [Category.assoc, reassoc_of% hhom]; exact pullback.condition) ≫ m =
        M ≫ pullback.lift (pullback.fst p (pullback.fst p (Y.hom ≫ p) ≫ p))
          (pullback.snd p (pullback.fst p (Y.hom ≫ p) ≫ p) ≫ E.act)
          (by rw [Category.assoc, reassoc_of% E.act_hom]; exact pullback.condition) := by
      refine pullback.hom_ext (by simp [M, m]) (by simp [M, m, hact])
    have h₂ : pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
          (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ pullback.snd p (X.hom ≫ p))
          (by
            rw [Category.assoc, ← pullback.condition (f := p) (g := X.hom ≫ p)]
            exact pullback.condition) ≫ m =
        M ≫ pullback.lift (pullback.fst p (pullback.fst p (Y.hom ≫ p) ≫ p))
          (pullback.snd p (pullback.fst p (Y.hom ≫ p) ≫ p) ≫ pullback.snd p (Y.hom ≫ p))
          (by
            rw [Category.assoc, ← pullback.condition (f := p) (g := Y.hom ≫ p)]
            exact pullback.condition) := by
      refine pullback.hom_ext ?_ ?_ <;> simp [M, m]
    rw [reassoc_of% h₁, E.act_assoc, ← reassoc_of% h₂]

/-- The action of `ofMono E f act hact` is `act`. -/
@[simp]
theorem ofMono_act {X Y : Over S'} (E : DescentDatum p Y) (f : X ⟶ Y) [Mono f.left]
    (act : pullback p (X.hom ≫ p) ⟶ X.left)
    (hact : act ≫ f.left = pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') f.left (𝟙 S)
      (by simp) (by simp) ≫ E.act) :
    (ofMono E f act hact).act = act :=
  (rfl)

/-- The monomorphism `f : X ⟶ Y` as a morphism of descent data `ofMono E f act hact ⟶ E`. -/
noncomputable def ofMonoHom {X Y : Over S'} (E : DescentDatum p Y) (f : X ⟶ Y) [Mono f.left]
    (act : pullback p (X.hom ≫ p) ⟶ X.left)
    (hact : act ≫ f.left = pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') f.left (𝟙 S)
      (by simp) (by simp) ≫ E.act) :
    Hom (ofMono E f act hact) E where
  hom := f
  map_act := hact.symm

/-- The underlying morphism of `ofMonoHom` is `f`. -/
@[simp]
theorem ofMonoHom_hom {X Y : Over S'} (E : DescentDatum p Y) (f : X ⟶ Y) [Mono f.left]
    (act : pullback p (X.hom ≫ p) ⟶ X.left)
    (hact : act ≫ f.left = pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') f.left (𝟙 S)
      (by simp) (by simp) ≫ E.act) :
    (ofMonoHom E f act hact).hom = f :=
  (rfl)

/-- A morphism `f : X ⟶ Y` in `Over S'` whose composite with a monomorphic morphism of descent data
`g : E ⟶ F` is a morphism of descent data `h : D ⟶ F` is itself a morphism of descent data
`D ⟶ E`. -/
noncomputable def Hom.mkOfCompMono {X Y Z : Over S'} {D : DescentDatum p X}
    {E : DescentDatum p Y} {F : DescentDatum p Z} (f : X ⟶ Y) (g : Hom E F) [Mono g.hom.left]
    (h : Hom D F) (hfg : f ≫ g.hom = h.hom) :
    Hom D E where
  hom := f
  map_act := by
    have hfg_left : f.left ≫ g.hom.left = h.hom.left := by
      rw [← Over.comp_left, hfg]
    rw [← cancel_mono g.hom.left, Category.assoc, Category.assoc, hfg_left, ← h.map_act,
      ← g.map_act, ← Category.assoc]
    congr 1
    refine pullback.hom_ext ?_ ?_ <;> simp [hfg_left]

/-- The underlying morphism of `Hom.mkOfCompMono` is `f`. -/
@[simp]
theorem Hom.mkOfCompMono_hom {X Y Z : Over S'} {D : DescentDatum p X}
    {E : DescentDatum p Y} {F : DescentDatum p Z} (f : X ⟶ Y) (g : Hom E F) [Mono g.hom.left]
    (h : Hom D F) (hfg : f ≫ g.hom = h.hom) :
    (Hom.mkOfCompMono f g h hfg).hom = f :=
  (rfl)

end MonoRestrict

end TauCeti.DescentDatum
