/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.DescentDatum

/-!
# Products and terminal object of descent data

Let `p : S' ⟶ S` be a morphism in a category `C` with pullbacks. The slice category `Over S'` is
cartesian monoidal with terminal object `𝟙_ (Over S') = (𝟙 S' : S' ⟶ S')` and binary product
`X₁ ⊗ X₂ = X₁ ×_{S'} X₂`. This file constructs the terminal descent datum `DescentDatum.unit p` on
`𝟙_ (Over S')` and the binary product `D₁.prod D₂` of two descent data on `X₁` and `X₂`, acting
diagonally as `s · (x₁, x₂) = (s · x₁, s · x₂)`, together with their projections, universal pairing
of morphisms (`Hom.lift`), tensor product of morphisms (`Hom.prodMap`), and canonical isomorphism
comparisons with the base change functor `Over.pullback p` (`baseChangeUnitHom` and
`baseChangeProdHom`).

## Main definitions

* `TauCeti.DescentDatum.unit`: the terminal descent datum on `𝟙_ (Over S')`, with unique morphism
  `Hom.toUnit`.
* `TauCeti.DescentDatum.prod`: the diagonal descent datum on `X₁ ⊗ X₂`, with projections `fstHom`
  and `sndHom`, universal pairing `Hom.lift`, and product of morphisms `Hom.prodMap`.
* `TauCeti.DescentDatum.baseChangeUnitHom`, `TauCeti.DescentDatum.baseChangeProdHom`: canonical
  isomorphisms comparing `baseChange p` with `unit` and `prod`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1.
-/

public section

namespace TauCeti.DescentDatum

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

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
    (baseChangeProdHom p X₀ Y₀).hom = Functor.OplaxMonoidal.δ (Over.pullback p) X₀ Y₀ :=
  CartesianMonoidalCategory.hom_ext _ _ (by simp [baseChangeProdHom]) (by simp [baseChangeProdHom])

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

end TauCeti.DescentDatum
