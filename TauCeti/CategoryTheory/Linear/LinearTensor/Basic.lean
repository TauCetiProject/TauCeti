/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# The tensor product of linear categories

Let `C` and `D` be `k`-linear categories over a commutative semiring `k`. Their **`k`-linear
tensor product** `LinearTensor k C D` has pairs `(X, Y)` of objects as objects, and morphisms

`(X, Y) ⟶ (X', Y')  =  (X ⟶ X') ⊗[k] (Y ⟶ Y')`,

composed componentwise on pure tensors: `(f ⊗ g) ≫ (f' ⊗ g') = (f ≫ f') ⊗ (g ≫ g')`. It is again a
`k`-linear category, and the canonical functor `LinearTensor.bifunctor k C D : C ⥤ D ⥤ _`,
`(f, g) ↦ f ⊗ g`, is `k`-linear in each variable. It is universal among such bifunctors:
a functor `F : C ⥤ D ⥤ E` into a `k`-linear category which is additive and `k`-linear in each
variable extends along `bifunctor` to the `k`-linear functor `LinearTensor.lift k F`, and an
additive functor out of `LinearTensor k C D` is determined up to isomorphism by its restriction
along `bifunctor`. The tensor product preserves essential smallness in a common universe.
For preadditive categories, `Preadditive.TensorProduct` specializes this construction to `ℤ`,
using Mathlib's `CategoryTheory.Linear.preadditiveIntLinear` instances.

The linear tensor product is the ordinary-category counterpart of the tensor product
`TauCeti.tensorEnrichedCategory` of enriched categories: here `LinearTensor k C D` is a category
with a `Linear k` structure. It is the linear tensor product of Mitchell,
*Rings with several objects*, §2.

## Main declarations

* `TauCeti.LinearTensor`: the `k`-linear tensor product of `C` and `D`, with its `Preadditive`
  and `Linear k` instances, the pure tensors `LinearTensor.tmul`, the composition rule
  `LinearTensor.tmul_comp_tmul` and the induction principle `LinearTensor.hom_induction_on`;
* `TauCeti.LinearTensor.bifunctor`, `TauCeti.LinearTensor.lift`,
  `TauCeti.LinearTensor.bifunctorCompLiftIso`, `TauCeti.LinearTensor.ext` and
  `TauCeti.LinearTensor.liftUnique`: the universal property, with
  `TauCeti.LinearTensor.naturality_of_tmul` reducing naturality to the pure tensors `f ⊗ 𝟙` and
  `𝟙 ⊗ g`.
-/

@[expose] public section

noncomputable section

open CategoryTheory TensorProduct

universe w v₁ v₂ v₃ u₁ u₂ u₃ s

namespace TauCeti

/-- The objects of the `k`-linear tensor product of the categories `C` and `D`: pairs of an
object of `C` and an object of `D`. The scalars `k` only enter through the morphisms. -/
structure LinearTensor (k : Type w) (C : Type u₁) (D : Type u₂) where
  /-- The component in `C`. -/
  fst : C
  /-- The component in `D`. -/
  snd : D

/-- The tensor product of preadditive categories, using their canonical integer linearity. -/
abbrev Preadditive.TensorProduct (C : Type u₁) (D : Type u₂) := LinearTensor ℤ C D

namespace LinearTensor

section Category

variable {k : Type w} [CommSemiring k]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D]

/-- The morphisms `(X, Y) ⟶ (X', Y')` of `LinearTensor k C D`: the tensor product over `k` of the
morphism modules `X ⟶ X'` and `Y ⟶ Y'`. -/
abbrev Hom (P Q : LinearTensor k C D) : Type (max v₁ v₂) :=
  (P.fst ⟶ Q.fst) ⊗[k] (P.snd ⟶ Q.snd)

/-- Induction on `Hom P Q`, used to build the category structure before the morphisms
`P ⟶ Q` exist; afterwards `hom_induction_on` is the public induction principle. -/
@[elab_as_elim]
private theorem Hom.induction_on {P Q : LinearTensor k C D} {motive : Hom P Q → Prop}
    (t : Hom P Q) (tmul : ∀ (f : P.fst ⟶ Q.fst) (g : P.snd ⟶ Q.snd), motive (f ⊗ₜ g))
    (add : ∀ t t', motive t → motive t' → motive (t + t')) : motive t :=
  TensorProduct.inductionOn t tmul add

/-- Composition in `LinearTensor k C D` as a bilinear map: it composes pure tensors
componentwise. -/
def compₗ (P Q R : LinearTensor k C D) : Hom P Q →ₗ[k] Hom Q R →ₗ[k] Hom P R :=
  TensorProduct.map₂ (Linear.comp P.fst Q.fst R.fst) (Linear.comp P.snd Q.snd R.snd)

/-- `compₗ` composes pure tensors componentwise; after the category structure is built this is
the public `tmul_comp_tmul`. -/
private theorem compₗ_tmul {P Q R : LinearTensor k C D} (f : P.fst ⟶ Q.fst) (g : P.snd ⟶ Q.snd)
    (f' : Q.fst ⟶ R.fst) (g' : Q.snd ⟶ R.snd) :
    compₗ P Q R (f ⊗ₜ g) (f' ⊗ₜ g') = (f ≫ f') ⊗ₜ (g ≫ g') :=
  rfl

/-- The `k`-linear tensor product of `C` and `D` is a category, with identities `𝟙 X ⊗ 𝟙 Y` and
composition `compₗ`. -/
instance : Category.{max v₁ v₂} (LinearTensor k C D) where
  Hom := Hom
  id P := (𝟙 P.fst ⊗ₜ 𝟙 P.snd : Hom P P)
  comp t t' := compₗ _ _ _ t t'
  id_comp {P Q} t := by
    induction t using Hom.induction_on with
    | tmul f g => rw [compₗ_tmul, Category.id_comp, Category.id_comp]
    | add t t' ht ht' => simp only [map_add, ht, ht']
  comp_id {P Q} t := by
    induction t using Hom.induction_on with
    | tmul f g => rw [compₗ_tmul, Category.comp_id, Category.comp_id]
    | add t t' ht ht' => simp only [map_add, LinearMap.add_apply, ht, ht']
  assoc {P Q R S} t t' t'' := by
    induction t using Hom.induction_on with
    | add t₁ t₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | tmul f g =>
      induction t' using Hom.induction_on with
      | add t₁ t₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
      | tmul f' g' =>
        induction t'' using Hom.induction_on with
        | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
        | tmul f'' g'' =>
          rw [compₗ_tmul, compₗ_tmul, compₗ_tmul, compₗ_tmul, Category.assoc, Category.assoc]

instance (P Q : LinearTensor k C D) : AddCommGroup (P ⟶ Q) :=
  inferInstanceAs <| AddCommGroup (Hom P Q)

instance (P Q : LinearTensor k C D) : Module k (P ⟶ Q) :=
  inferInstanceAs <| Module k (Hom P Q)

/-- Composition in `LinearTensor k C D` is the bilinear map `compₗ`. -/
theorem comp_def {P Q R : LinearTensor k C D} (t : P ⟶ Q) (t' : Q ⟶ R) :
    t ≫ t' = compₗ P Q R t t' := rfl

/-- The `k`-linear tensor product of `C` and `D` is preadditive, with the additive structure of
the tensor products of morphism modules. -/
instance : Preadditive (LinearTensor k C D) where
  add_comp P Q R t t' t'' := by simp only [comp_def, LinearMap.map_add₂]
  comp_add P Q R t t' t'' := by simp only [comp_def, map_add]

/-- The `k`-linear tensor product of `C` and `D` is `k`-linear. -/
instance : Linear k (LinearTensor k C D) where
  smul_comp P Q R r t t' := by simp only [comp_def, LinearMap.map_smul₂]
  comp_smul P Q R t r t' := by simp only [comp_def, map_smul]

/-- Morphisms of `LinearTensor k C D` are the elements of the tensor product of the morphism
modules of the two components. -/
def homEquiv (P Q : LinearTensor k C D) :
    (P ⟶ Q) ≃ₗ[k] (P.fst ⟶ Q.fst) ⊗[k] (P.snd ⟶ Q.snd) :=
  LinearEquiv.refl k _

/-- The pure tensor `f ⊗ g : (X, Y) ⟶ (X', Y')` of morphisms `f : X ⟶ X'` and `g : Y ⟶ Y'`. -/
def tmul {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    (⟨X, Y⟩ : LinearTensor k C D) ⟶ ⟨X', Y'⟩ :=
  f ⊗ₜ g

@[simp]
theorem homEquiv_tmul {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    homEquiv _ _ (tmul (k := k) f g) = f ⊗ₜ g :=
  rfl

@[simp]
theorem homEquiv_symm_tmul {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    (homEquiv (k := k) ⟨X, Y⟩ ⟨X', Y'⟩).symm (f ⊗ₜ g) = tmul f g :=
  rfl

/-- Pure tensors compose componentwise. -/
@[reassoc (attr := simp)]
theorem tmul_comp_tmul {X X' X'' : C} {Y Y' Y'' : D} (f : X ⟶ X') (g : Y ⟶ Y') (f' : X' ⟶ X'')
    (g' : Y' ⟶ Y'') : tmul (k := k) f g ≫ tmul f' g' = tmul (f ≫ f') (g ≫ g') :=
  rfl

/-- The identity of `(X, Y)` is the pure tensor `𝟙 X ⊗ 𝟙 Y`. -/
@[simp]
theorem tmul_id_id (X : C) (Y : D) : tmul (k := k) (𝟙 X) (𝟙 Y) = 𝟙 _ :=
  rfl

/-- A pure tensor factors as `(f ⊗ 𝟙) ≫ (𝟙 ⊗ g)`. -/
theorem tmul_eq_comp {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    tmul (k := k) f g = tmul f (𝟙 Y) ≫ tmul (𝟙 X') g := by
  simp

@[simp]
theorem add_tmul {X X' : C} {Y Y' : D} (f f' : X ⟶ X') (g : Y ⟶ Y') :
    tmul (k := k) (f + f') g = tmul f g + tmul f' g :=
  TensorProduct.add_tmul f f' g

@[simp]
theorem tmul_add {X X' : C} {Y Y' : D} (f : X ⟶ X') (g g' : Y ⟶ Y') :
    tmul (k := k) f (g + g') = tmul f g + tmul f g' :=
  TensorProduct.tmul_add f g g'

@[simp]
theorem zero_tmul {X X' : C} {Y Y' : D} (g : Y ⟶ Y') : tmul (k := k) (0 : X ⟶ X') g = 0 :=
  TensorProduct.zero_tmul _ g

@[simp]
theorem tmul_zero {X X' : C} {Y Y' : D} (f : X ⟶ X') : tmul (k := k) f (0 : Y ⟶ Y') = 0 :=
  TensorProduct.tmul_zero _ f

@[simp]
theorem smul_tmul {X X' : C} {Y Y' : D} (r : k) (f : X ⟶ X') (g : Y ⟶ Y') :
    tmul (k := k) (r • f) g = r • tmul f g :=
  (TensorProduct.smul_tmul' r f g).symm

@[simp]
theorem tmul_smul {X X' : C} {Y Y' : D} (r : k) (f : X ⟶ X') (g : Y ⟶ Y') :
    tmul (k := k) f (r • g) = r • tmul f g :=
  TensorProduct.tmul_smul r f g

theorem sum_tmul {X X' : C} {Y Y' : D} {J : Type*} (s : Finset J) (f : J → (X ⟶ X'))
    (g : Y ⟶ Y') : tmul (k := k) (∑ j ∈ s, f j) g = ∑ j ∈ s, tmul (f j) g :=
  TensorProduct.sum_tmul s f g

theorem tmul_sum {X X' : C} {Y Y' : D} {J : Type*} (s : Finset J) (f : X ⟶ X')
    (g : J → (Y ⟶ Y')) : tmul (k := k) f (∑ j ∈ s, g j) = ∑ j ∈ s, tmul f (g j) :=
  TensorProduct.tmul_sum f s g

/-- Induction on morphisms `(X, Y) ⟶ (X', Y')` of `LinearTensor k C D`: a property of morphisms
which holds for pure tensors and is stable under addition holds for all morphisms. -/
@[elab_as_elim]
theorem hom_induction_on {X X' : C} {Y Y' : D}
    {motive : ((⟨X, Y⟩ : LinearTensor k C D) ⟶ ⟨X', Y'⟩) → Prop}
    (t : (⟨X, Y⟩ : LinearTensor k C D) ⟶ ⟨X', Y'⟩)
    (tmul : ∀ (f : X ⟶ X') (g : Y ⟶ Y'), motive (tmul f g))
    (add : ∀ t t', motive t → motive t' → motive (t + t')) : motive t :=
  TensorProduct.inductionOn (motive := motive) t tmul add

/-- Linear maps on the homs of a linear tensor product preserve composition if they
preserve composition of pure tensors. -/
theorem map_comp_of_tmul {E : Type u₃} [Category.{v₃} E] [Preadditive E] [Linear k E]
    (obj : LinearTensor k C D → E) (hom : ∀ P Q, (P ⟶ Q) →ₗ[k] (obj P ⟶ obj Q))
    (comp : ∀ {X Y Z : C} {X' Y' Z' : D}
      (f : X ⟶ Y) (g : X' ⟶ Y') (f' : Y ⟶ Z) (g' : Y' ⟶ Z'),
      hom ⟨X, X'⟩ ⟨Z, Z'⟩ (tmul (f ≫ f') (g ≫ g')) =
        hom ⟨X, X'⟩ ⟨Y, Y'⟩ (tmul f g) ≫ hom ⟨Y, Y'⟩ ⟨Z, Z'⟩ (tmul f' g'))
    {P Q S : LinearTensor k C D} (a : P ⟶ Q) (b : Q ⟶ S) :
    hom P S (a ≫ b) = hom P Q a ≫ hom Q S b := by
  obtain ⟨X, X'⟩ := P
  obtain ⟨Y, Y'⟩ := Q
  obtain ⟨Z, Z'⟩ := S
  induction a using hom_induction_on with
  | add a₁ a₂ h₁ h₂ =>
    simp only [Preadditive.add_comp, map_add, h₁, h₂]
  | tmul f g =>
    induction b using hom_induction_on with
    | add b₁ b₂ h₁ h₂ =>
      simp only [Preadditive.comp_add, map_add, h₁, h₂]
    | tmul f' g' => simpa only [tmul_comp_tmul] using comp f g f' g'

/-- The isomorphism of pairs `(X, Y) ≅ (X', Y')` built from isomorphisms of the components. -/
@[simps]
def isoMk {X X' : C} {Y Y' : D} (e : X ≅ X') (e' : Y ≅ Y') :
    (⟨X, Y⟩ : LinearTensor k C D) ≅ ⟨X', Y'⟩ where
  hom := tmul e.hom e'.hom
  inv := tmul e.inv e'.inv
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- The homs of the tensor product are small in any universe in which both factors have
small homs. -/
instance [LocallySmall.{s} C] [LocallySmall.{s} D] : LocallySmall.{s} (LinearTensor k C D) where
  hom_small P Q := small_map (homEquiv P Q).toEquiv

/-- The tensor product of two essentially small linear categories is essentially small in
the same universe. -/
instance [EssentiallySmall.{s} C] [EssentiallySmall.{s} D] :
    EssentiallySmall.{s} (LinearTensor k C D) := by
  refine (essentiallySmall_iff _).2 ⟨?_, inferInstance⟩
  refine small_of_surjective (f := fun p : Skeleton C × Skeleton D ↦
    toSkeleton (⟨(fromSkeleton C).obj p.1, (fromSkeleton D).obj p.2⟩ : LinearTensor k C D)) ?_
  intro P
  obtain ⟨⟨X, Y⟩, rfl⟩ := Quotient.exists_rep P
  exact ⟨(toSkeleton X, toSkeleton Y), congr_toSkeleton_of_iso
    (isoMk (fromSkeletonToSkeletonIso X) (fromSkeletonToSkeletonIso Y))⟩

instance {P Q : LinearTensor k C D} [Subsingleton (P.fst ⟶ Q.fst)] : Subsingleton (P ⟶ Q) :=
  inferInstanceAs <| Subsingleton ((P.fst ⟶ Q.fst) ⊗[k] (P.snd ⟶ Q.snd))

instance {P Q : LinearTensor k C D} [Subsingleton (P.snd ⟶ Q.snd)] : Subsingleton (P ⟶ Q) :=
  inferInstanceAs <| Subsingleton ((P.fst ⟶ Q.fst) ⊗[k] (P.snd ⟶ Q.snd))

end Category

section Universal

variable (k : Type w) [CommSemiring k]
  (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear k C]
  (D : Type u₂) [Category.{v₂} D] [Preadditive D] [Linear k D]

/-- The canonical functor `C ⥤ D ⥤ LinearTensor k C D`, sending `X` and `Y` to the pair `(X, Y)`
and morphisms `f` and `g` to the pure tensor `f ⊗ g`. It is additive and `k`-linear in each
variable. -/
def bifunctor : C ⥤ D ⥤ LinearTensor k C D where
  obj X :=
    { obj Y := ⟨X, Y⟩
      map g := tmul (𝟙 X) g }
  map f := { app Y := tmul f (𝟙 Y) }

variable {k C D}

@[simp]
theorem bifunctor_obj_obj (X : C) (Y : D) : ((bifunctor k C D).obj X).obj Y = ⟨X, Y⟩ :=
  rfl

@[simp]
theorem bifunctor_obj_map (X : C) {Y Y' : D} (g : Y ⟶ Y') :
    ((bifunctor k C D).obj X).map g = tmul (𝟙 X) g :=
  rfl

@[simp]
theorem bifunctor_map_app {X X' : C} (f : X ⟶ X') (Y : D) :
    ((bifunctor k C D).map f).app Y = tmul f (𝟙 Y) :=
  rfl

instance (X : C) : ((bifunctor k C D).obj X).Additive where
  map_add := tmul_add _ _ _

instance (X : C) : ((bifunctor k C D).obj X).Linear k where
  map_smul g r := tmul_smul r (𝟙 X) g

instance : (bifunctor k C D).Additive where
  map_add {_ _ f f'} := by
    ext Y
    rw [NatTrans.app_add, bifunctor_map_app, bifunctor_map_app, bifunctor_map_app]
    exact add_tmul f f' (𝟙 Y)

instance : (bifunctor k C D).Linear k where
  map_smul f r := by
    ext Y
    rw [NatTrans.app_smul, bifunctor_map_app, bifunctor_map_app]
    exact smul_tmul r f (𝟙 Y)

/-- Inserting a fixed object in the second factor is additive. -/
instance (Y : D) : ((bifunctor k C D).flip.obj Y).Additive :=
  inferInstanceAs ((bifunctor k C D ⋙ (evaluation D _).obj Y).Additive)

/-- Inserting a fixed object in the second factor is linear. -/
instance (Y : D) : ((bifunctor k C D).flip.obj Y).Linear k where
  map_smul f r := congrArg (fun α ↦ α.app Y) ((bifunctor k C D).map_smul r f)

variable {E : Type u₃} [Category.{v₃} E] [Preadditive E]

section Lift

variable [Linear k E] (F : C ⥤ D ⥤ E) [F.Additive] [F.Linear k] [∀ X, (F.obj X).Additive]
  [∀ X, (F.obj X).Linear k]

variable (k) in
/-- The extension of a bifunctor `F : C ⥤ D ⥤ E`, additive and `k`-linear in each variable, to a
`k`-linear functor `LinearTensor k C D ⥤ E`: it sends `(X, Y)` to `F X Y` and a pure tensor
`f ⊗ g` to `F f ≫ F g`. -/
def lift : LinearTensor k C D ⥤ E :=
  let obj (P : LinearTensor k C D) := (F.obj P.fst).obj P.snd
  let hom (P Q : LinearTensor k C D) : (P ⟶ Q) →ₗ[k] (obj P ⟶ obj Q) :=
    TensorProduct.lift (LinearMap.mk₂ k
      (fun (f : P.fst ⟶ Q.fst) (g : P.snd ⟶ Q.snd) ↦ (F.map f).app P.snd ≫ (F.obj Q.fst).map g)
      (fun f f' g ↦ by simp) (fun r f g ↦ by simp) (fun f g g' ↦ by simp) (fun r f g ↦ by simp))
  have hom_tmul {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
      hom ⟨X, Y⟩ ⟨X', Y'⟩ (tmul f g) = (F.map f).app Y ≫ (F.obj X').map g := rfl
  { obj
    map {P Q} := hom P Q
    map_id P := by
      obtain ⟨X, Y⟩ := P
      rw [← tmul_id_id, hom_tmul]
      simp [obj]
    map_comp := by
      apply map_comp_of_tmul obj hom
      intro X Y Z X' Y' Z' f g f' g'
      simp only [hom_tmul]
      simp }

@[simp]
theorem lift_obj (P : LinearTensor k C D) : (lift k F).obj P = (F.obj P.fst).obj P.snd :=
  rfl

@[simp]
theorem lift_map_tmul {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    (lift k F).map (tmul (k := k) f g) = (F.map f).app Y ≫ (F.obj X').map g :=
  rfl

instance : (lift k F).Additive where
  map_add {P Q} t t' := map_add
    (TensorProduct.lift _ : _ →ₗ[k] ((F.obj P.fst).obj P.snd ⟶ (F.obj Q.fst).obj Q.snd)) t t'

instance : (lift k F).Linear k where
  map_smul {P Q} t r := map_smul
    (TensorProduct.lift _ : _ →ₗ[k] ((F.obj P.fst).obj P.snd ⟶ (F.obj Q.fst).obj Q.snd)) r t

variable (k) in
/-- The extension `lift k F` restricts along `bifunctor` to `F`. -/
def bifunctorCompLiftIso :
    bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj (lift k F) ≅ F :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ Iso.refl _) fun g ↦ by simp)
    fun f ↦ by
      ext Y
      -- `NatIso.ofComponents_hom_app` does not fire: the source objects of the components are
      -- `(lift k F).obj (X, Y)`, equal to `(F.obj X).obj Y` only after unfolding `lift`.
      simp [NatIso.ofComponents]

@[simp]
theorem bifunctorCompLiftIso_hom_app_app (X : C) (Y : D) :
    ((bifunctorCompLiftIso k F).hom.app X).app Y = 𝟙 _ :=
  rfl

@[simp]
theorem bifunctorCompLiftIso_inv_app_app (X : C) (Y : D) :
    ((bifunctorCompLiftIso k F).inv.app X).app Y = 𝟙 _ :=
  rfl

end Lift

/-- A family of morphisms `G P ⟶ G' P` between additive functors out of `LinearTensor k C D` is
natural as soon as it is natural with respect to the morphisms `f ⊗ 𝟙` and `𝟙 ⊗ g`. -/
theorem naturality_of_tmul {G G' : LinearTensor k C D ⥤ E} [G.Additive] [G'.Additive]
    (φ : ∀ P, G.obj P ⟶ G'.obj P)
    (h₁ : ∀ {X X' : C} (f : X ⟶ X') (Y : D),
      G.map (tmul f (𝟙 Y)) ≫ φ ⟨X', Y⟩ = φ ⟨X, Y⟩ ≫ G'.map (tmul f (𝟙 Y)))
    (h₂ : ∀ (X : C) {Y Y' : D} (g : Y ⟶ Y'),
      G.map (tmul (𝟙 X) g) ≫ φ ⟨X, Y'⟩ = φ ⟨X, Y⟩ ≫ G'.map (tmul (𝟙 X) g))
    {P Q : LinearTensor k C D} (t : P ⟶ Q) : G.map t ≫ φ Q = φ P ≫ G'.map t := by
  obtain ⟨X, Y⟩ := P
  obtain ⟨X', Y'⟩ := Q
  induction t using hom_induction_on with
  | add t₁ t₂ ht₁ ht₂ =>
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, ht₁, ht₂]
  | tmul f g =>
    rw [tmul_eq_comp, G.map_comp, G'.map_comp, Category.assoc, h₂, reassoc_of% (h₁ f Y)]

/-- Two additive functors out of `LinearTensor k C D` whose restrictions along `bifunctor` are
isomorphic are isomorphic, with the same components. -/
def ext {G G' : LinearTensor k C D ⥤ E} [G.Additive] [G'.Additive]
    (α : bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj G ≅
      bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj G') :
    G ≅ G' :=
  NatIso.ofComponents (fun P ↦ (α.app P.fst).app P.snd)
    (naturality_of_tmul (fun P ↦ ((α.app P.fst).app P.snd).hom)
      (fun f Y ↦ NatTrans.congr_app (α.hom.naturality f) Y)
      (fun X _ _ g ↦ (α.hom.app X).naturality g))

@[simp]
theorem ext_hom_app {G G' : LinearTensor k C D ⥤ E} [G.Additive] [G'.Additive]
    (α : bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj G ≅
      bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj G') (P : LinearTensor k C D) :
    (ext α).hom.app P = (α.hom.app P.fst).app P.snd :=
  rfl

/-- **Uniqueness of the extension**: an additive functor `L` out of `LinearTensor k C D` whose
restriction along `bifunctor` is isomorphic to `F` is isomorphic to `lift k F`. -/
def liftUnique [Linear k E] (F : C ⥤ D ⥤ E) [F.Additive] [F.Linear k] [∀ X, (F.obj X).Additive]
    [∀ X, (F.obj X).Linear k] (L : LinearTensor k C D ⥤ E) [L.Additive]
    (α : bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj L ≅ F) : L ≅ lift k F :=
  ext (α ≪≫ (bifunctorCompLiftIso k F).symm)

end Universal

end LinearTensor

end TauCeti
