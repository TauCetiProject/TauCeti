/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.CategoryTheory.Linear.Mat
public import TauCeti.CategoryTheory.Linear.SplitSimpleFamily
public import TauCeti.CategoryTheory.Preadditive.Mat

/-!
# The Deligne tensor product of linear categories

Let `C` and `D` be `k`-linear categories over a commutative semiring `k`. Their **`k`-linear
tensor product** `LinearTensor k C D` has pairs `(X, Y)` of objects as objects, and morphisms

`(X, Y) ⟶ (X', Y')  =  (X ⟶ X') ⊗[k] (Y ⟶ Y')`,

composed componentwise on pure tensors: `(f ⊗ g) ≫ (f' ⊗ g') = (f ≫ f') ⊗ (g ≫ g')`. It is again a
`k`-linear category, and the canonical functor `LinearTensor.bifunctor k C D : C ⥤ D ⥤ _`,
`(f, g) ↦ f ⊗ g`, is `k`-linear in each variable. It is universal among such bifunctors:
a functor `F : C ⥤ D ⥤ E` into a `k`-linear category which is additive and `k`-linear in each
variable extends along `bifunctor` to the `k`-linear functor `LinearTensor.lift k F`, and an
additive functor out of `LinearTensor k C D` is determined up to isomorphism by its restriction
along `bifunctor`. This is the ordinary-category counterpart of the tensor product
`TauCeti.tensorEnrichedCategory` of enriched categories: here `LinearTensor k C D` is a category
with a `Linear k` structure, which is what `Mat_` and split simple families are built on.

The **Deligne tensor product** `DeligneProduct k C D` is the additive envelope
`Mat_ (LinearTensor k C D)` of the linear tensor product, whose objects are formal finite
biproducts of pairs `X ⊠ Y`. It has finite biproducts, and the same universal property holds for
functors into additive `k`-linear categories (in the universes of `Mat_.lift`), now with
`DeligneProduct.lift k F` extending `F` additively over finite biproducts. For finite semisimple
categories whose simple objects have endomorphisms `k`, for instance over an algebraically closed
field, this is the Deligne tensor product `C ⊠ D` of Etingof–Gelaki–Nikshych–Ostrik.

Finally, if `S : ι → C` and `T : ι' → D` are split simple families over `k` (every member has
scalar endomorphisms, there are no morphisms between distinct members, and every object is a
finite biproduct of members), then so is the family of pairs `S i ⊠ T j` in `DeligneProduct k C D`,
indexed by `ι × ι'` (`TauCeti.IsSplitSimpleFamily.deligneProduct`). So every object of `C ⊠ D` is a
finite biproduct of the objects `S i ⊠ T j`, which have scalar endomorphisms and admit no nonzero
morphisms between distinct members; this is the semisimplicity of the Deligne product.

## Main declarations

* `TauCeti.LinearTensor`: the `k`-linear tensor product of `C` and `D`, with its `Preadditive`
  and `Linear k` instances, the pure tensors `LinearTensor.tmul`, the composition rule
  `LinearTensor.tmul_comp_tmul` and the induction principle `LinearTensor.hom_induction_on`;
* `TauCeti.LinearTensor.bijective_algebraMap_mk`: a pair of objects with scalar endomorphisms has
  scalar endomorphisms;
* `TauCeti.LinearTensor.bifunctor`, `TauCeti.LinearTensor.lift`,
  `TauCeti.LinearTensor.bifunctorCompLiftIso`, `TauCeti.LinearTensor.ext` and
  `TauCeti.LinearTensor.liftUnique`: the universal property, with
  `TauCeti.LinearTensor.naturality_of_tmul` reducing naturality to the pure tensors `f ⊗ 𝟙` and
  `𝟙 ⊗ g`;
* `TauCeti.LinearTensor.biconeTmul` and `TauCeti.LinearTensor.isBilimitBiconeTmul`: the pair of
  two biproducts is the biproduct of the pairs;
* `TauCeti.DeligneProduct`, with `TauCeti.DeligneProduct.bifunctor`, `TauCeti.DeligneProduct.lift`,
  `TauCeti.DeligneProduct.bifunctorCompLiftIso`, `TauCeti.DeligneProduct.ext` (with its components
  `TauCeti.DeligneProduct.ext_hom_app`) and `TauCeti.DeligneProduct.liftUnique`;
* `TauCeti.DeligneProduct.biproductIso`: `(⨁ f) ⊠ (⨁ g)` is the biproduct of the `f j ⊠ g j'`, with
  components `TauCeti.DeligneProduct.biproductIso_hom_π` and
  `TauCeti.DeligneProduct.ι_biproductIso_inv`;
* `TauCeti.IsSplitSimpleFamily.deligneProduct`: products of split simple families.

## References

* [P. Deligne, *Catégories tannakiennes*][deligne1990], §5
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], Definition 1.11.1,
  Proposition 1.11.2 and §4.6
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TensorProduct

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace TauCeti

/-- The objects of the `k`-linear tensor product of the categories `C` and `D`: pairs of an
object of `C` and an object of `D`. The scalars `k` only enter through the morphisms. -/
structure LinearTensor (k : Type w) (C : Type u₁) (D : Type u₂) where
  /-- The component in `C`. -/
  fst : C
  /-- The component in `D`. -/
  snd : D

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

/-- The isomorphism of pairs `(X, Y) ≅ (X', Y')` built from isomorphisms of the components. -/
@[simps]
def isoMk {X X' : C} {Y Y' : D} (e : X ≅ X') (e' : Y ≅ Y') :
    (⟨X, Y⟩ : LinearTensor k C D) ≅ ⟨X', Y'⟩ where
  hom := tmul e.hom e'.hom
  inv := tmul e.inv e'.inv
  hom_inv_id := by simp
  inv_hom_id := by simp

instance {P Q : LinearTensor k C D} [Subsingleton (P.fst ⟶ Q.fst)] : Subsingleton (P ⟶ Q) :=
  inferInstanceAs <| Subsingleton ((P.fst ⟶ Q.fst) ⊗[k] (P.snd ⟶ Q.snd))

instance {P Q : LinearTensor k C D} [Subsingleton (P.snd ⟶ Q.snd)] : Subsingleton (P ⟶ Q) :=
  inferInstanceAs <| Subsingleton ((P.fst ⟶ Q.fst) ⊗[k] (P.snd ⟶ Q.snd))

/-- If `X` and `Y` have scalar endomorphisms, so does the pair `(X, Y)`: its endomorphisms are
`End X ⊗[k] End Y = k ⊗[k] k = k`. -/
theorem bijective_algebraMap_mk {X : C} {Y : D} (hX : Function.Bijective (algebraMap k (End X)))
    (hY : Function.Bijective (algebraMap k (End Y))) :
    Function.Bijective (algebraMap k (End (⟨X, Y⟩ : LinearTensor k C D))) := by
  let eX : k ≃ₗ[k] (X ⟶ X) := LinearEquiv.ofBijective
    ((End.linearEquiv (R := k)).toLinearMap ∘ₗ Algebra.linearMap k (End X))
      ((End.linearEquiv (R := k)).bijective.comp hX)
  let eY : k ≃ₗ[k] (Y ⟶ Y) := LinearEquiv.ofBijective
    ((End.linearEquiv (R := k)).toLinearMap ∘ₗ Algebra.linearMap k (End Y))
      ((End.linearEquiv (R := k)).bijective.comp hY)
  let e : k ≃ₗ[k] End (⟨X, Y⟩ : LinearTensor k C D) := (TensorProduct.lid k k).symm ≪≫ₗ
    TensorProduct.congr eX eY ≪≫ₗ (homEquiv (⟨X, Y⟩ : LinearTensor k C D) ⟨X, Y⟩).symm ≪≫ₗ
      (End.linearEquiv (R := k)).symm
  convert e.bijective
  ext r : 2
  -- Both sides reduce to `r • 𝟙 (X, Y)`: the right-hand side to `r` times the identity written
  -- through `homEquiv`, which `homEquiv_symm_tmul` and `tmul_id_id` turn into `𝟙 (X, Y)`.
  simp only [e, eX, eY, End.algebraMap_asHom, LinearEquiv.trans_apply, lid_symm_apply, congr_tmul,
    LinearEquiv.ofBijective_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Algebra.linearMap_apply, map_one, End.linearEquiv_apply, AddEquiv.toEquiv_eq_coe,
    Equiv.toFun_as_coe, EquivLike.coe_coe, End.addEquiv_apply, End.one_asHom,
    TensorProduct.tmul_smul, map_smul, End.linearEquiv_symm_apply, Equiv.invFun_as_coe,
    AddEquiv.coe_toEquiv_symm, End.smul_asHom, End.addEquiv_symm_apply_asHom]
  rw [homEquiv_symm_tmul, tmul_id_id]

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

variable {E : Type u₃} [Category.{v₃} E] [Preadditive E]

section Lift

variable [Linear k E] (F : C ⥤ D ⥤ E) [F.Additive] [F.Linear k] [∀ X, (F.obj X).Additive]
  [∀ X, (F.obj X).Linear k]

variable (k) in
/-- The extension of a bifunctor `F : C ⥤ D ⥤ E`, additive and `k`-linear in each variable, to a
`k`-linear functor `LinearTensor k C D ⥤ E`: it sends `(X, Y)` to `F X Y` and a pure tensor
`f ⊗ g` to `F f ≫ F g`. -/
def lift : LinearTensor k C D ⥤ E where
  obj P := (F.obj P.fst).obj P.snd
  map {P Q} := TensorProduct.lift (LinearMap.mk₂ k
    (fun (f : P.fst ⟶ Q.fst) (g : P.snd ⟶ Q.snd) ↦ (F.map f).app P.snd ≫ (F.obj Q.fst).map g)
    (fun f f' g ↦ by simp) (fun r f g ↦ by simp) (fun f g g' ↦ by simp) (fun r f g ↦ by simp))
  map_id P := by
    obtain ⟨X, Y⟩ := P
    rw [← tmul_id_id, tmul, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
    simp
  map_comp {P Q R} t t' := by
    obtain ⟨X₁, Y₁⟩ := P
    obtain ⟨X₂, Y₂⟩ := Q
    obtain ⟨X₃, Y₃⟩ := R
    induction t using hom_induction_on with
    | add t₁ t₂ h₁ h₂ => simp only [Preadditive.add_comp, map_add, h₁, h₂]
    | tmul f g =>
      induction t' using hom_induction_on with
      | add t₁ t₂ h₁ h₂ => simp only [Preadditive.comp_add, map_add, h₁, h₂]
      | tmul f' g' =>
        rw [tmul_comp_tmul]
        simp only [tmul, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
        simp

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

section Biproduct

variable {k : Type w} [CommSemiring k]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D]
  {J : Type*} {J' : Type*} {f : J → C} {g : J' → D}

/-- The bicone on the family of pairs `(f j, g j')` with cone point `(b.pt, c.pt)`, built from
bicones `b` on `f` and `c` on `g`: its projections and inclusions are the pure tensors of those of
`b` and `c`. -/
@[simps π ι]
def biconeTmul (b : Bicone f) (c : Bicone g) :
    Bicone (fun p : J × J' ↦ (⟨f p.1, g p.2⟩ : LinearTensor k C D)) where
  pt := ⟨b.pt, c.pt⟩
  π p := tmul (b.π p.1) (c.π p.2)
  ι p := tmul (b.ι p.1) (c.ι p.2)
  ι_π p q := by
    obtain ⟨p₁, p₂⟩ := p
    obtain ⟨q₁, q₂⟩ := q
    by_cases h₁ : p₁ = q₁
    · subst h₁
      by_cases h₂ : p₂ = q₂
      · subst h₂
        simp
      · simp [bicone_ι_π_ne _ h₂, h₂]
    · simp [bicone_ι_π_ne _ h₁, h₁]

@[simp]
theorem biconeTmul_pt (b : Bicone f) (c : Bicone g) :
    (biconeTmul (k := k) b c).pt = ⟨b.pt, c.pt⟩ :=
  rfl

/-- **The pair of two biproducts is the biproduct of the pairs**: if `b` and `c` are bilimit
bicones over finite index types, so is `biconeTmul b c`. -/
def isBilimitBiconeTmul [Fintype J] [Fintype J'] {b : Bicone f} {c : Bicone g} (hb : b.IsBilimit)
    (hc : c.IsBilimit) : (biconeTmul (k := k) b c).IsBilimit :=
  isBilimitOfTotal _ <| by
    simp only [biconeTmul_π, biconeTmul_ι]
    -- Restate the goal with the cone point `(biconeTmul b c).pt` written as `⟨b.pt, c.pt⟩`
    -- (`biconeTmul_pt`).
    change ∑ p : J × J', tmul (k := k) (b.π p.1) (c.π p.2) ≫ tmul (b.ι p.1) (c.ι p.2) =
      𝟙 (⟨b.pt, c.pt⟩ : LinearTensor k C D)
    rw [← tmul_id_id, ← IsBilimit.total hb, ← IsBilimit.total hc, sum_tmul, Fintype.sum_prod_type]
    simp only [tmul_sum, tmul_comp_tmul]

end Biproduct

end LinearTensor

/-- The **Deligne tensor product** of `k`-linear categories `C` and `D`: the additive envelope
`Mat_` of their `k`-linear tensor product `LinearTensor k C D`. Its objects are formal finite
biproducts of pairs `X ⊠ Y`; its category, preadditive and `k`-linear structures are those of
`Mat_` over the `k`-linear category `LinearTensor k C D`. -/
abbrev DeligneProduct (k : Type w) (C : Type u₁) (D : Type u₂) :=
  Mat_ (LinearTensor k C D)

namespace DeligneProduct

variable (k : Type w) [CommSemiring k]
  (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear k C]
  (D : Type u₂) [Category.{v₂} D] [Preadditive D] [Linear k D]

/-- The canonical functor `C ⥤ D ⥤ DeligneProduct k C D`, sending `X` and `Y` to `X ⊠ Y`. It is
additive and `k`-linear in each variable. -/
def bifunctor : C ⥤ D ⥤ DeligneProduct k C D :=
  LinearTensor.bifunctor k C D ⋙
    (Functor.whiskeringRight D _ _).obj (Mat_.embedding (LinearTensor k C D))

variable {k C D}

@[simp]
theorem bifunctor_obj_obj (X : C) (Y : D) :
    ((bifunctor k C D).obj X).obj Y = (Mat_.embedding _).obj ⟨X, Y⟩ :=
  rfl

@[simp]
theorem bifunctor_obj_map (X : C) {Y Y' : D} (g : Y ⟶ Y') :
    ((bifunctor k C D).obj X).map g = (Mat_.embedding _).map (LinearTensor.tmul (𝟙 X) g) :=
  rfl

@[simp]
theorem bifunctor_map_app {X X' : C} (f : X ⟶ X') (Y : D) :
    ((bifunctor k C D).map f).app Y = (Mat_.embedding _).map (LinearTensor.tmul f (𝟙 Y)) :=
  rfl

instance (X : C) : ((bifunctor k C D).obj X).Additive :=
  inferInstanceAs <| Functor.Additive
    ((LinearTensor.bifunctor k C D).obj X ⋙ Mat_.embedding (LinearTensor k C D))

instance (X : C) : ((bifunctor k C D).obj X).Linear k :=
  inferInstanceAs <| Functor.Linear k
    ((LinearTensor.bifunctor k C D).obj X ⋙ Mat_.embedding (LinearTensor k C D))

instance : (bifunctor k C D).Additive where
  map_add {_ _ f f'} := by
    ext Y : 2
    rw [NatTrans.app_add, bifunctor_map_app, bifunctor_map_app, bifunctor_map_app,
      LinearTensor.add_tmul]
    exact Functor.map_add _

instance : (bifunctor k C D).Linear k where
  map_smul f r := by
    ext Y : 2
    rw [NatTrans.app_smul, bifunctor_map_app, bifunctor_map_app, LinearTensor.smul_tmul]
    exact Functor.map_smul _ _ _

/-- **`⊠` preserves finite biproducts in both variables**: for finite families `f` in `C` and `g`
in `D`, the object `(⨁ f) ⊠ (⨁ g)` is the biproduct of the objects `f j ⊠ g j'`. -/
def biproductIso {J J' : Type} [Fintype J] [Fintype J'] (f : J → C) (g : J' → D)
    [HasBiproduct f] [HasBiproduct g] :
    (Mat_.embedding (LinearTensor k C D)).obj ⟨⨁ f, ⨁ g⟩ ≅
      ⨁ fun p : J × J' ↦ (Mat_.embedding (LinearTensor k C D)).obj ⟨f p.1, g p.2⟩ :=
  biproduct.uniqueUpToIso _ (isBilimitOfPreserves (Mat_.embedding (LinearTensor k C D))
    (LinearTensor.isBilimitBiconeTmul (biproduct.isBilimit f) (biproduct.isBilimit g)))

/-- The components of `biproductIso` towards the summands: the projection onto `f p.1 ⊠ g p.2`
is the pure tensor of the two projections. -/
@[reassoc (attr := simp)]
theorem biproductIso_hom_π {J J' : Type} [Fintype J] [Fintype J'] (f : J → C) (g : J' → D)
    [HasBiproduct f] [HasBiproduct g] (p : J × J') :
    (biproductIso (k := k) f g).hom ≫ biproduct.π _ p =
      (Mat_.embedding _).map (LinearTensor.tmul (biproduct.π f p.1) (biproduct.π g p.2)) :=
  biproduct.lift_π _ _

/-- The components of `biproductIso` from the summands: the inclusion of `f p.1 ⊠ g p.2` is the
pure tensor of the two inclusions. -/
@[reassoc (attr := simp)]
theorem ι_biproductIso_inv {J J' : Type} [Fintype J] [Fintype J'] (f : J → C) (g : J' → D)
    [HasBiproduct f] [HasBiproduct g] (p : J × J') :
    biproduct.ι _ p ≫ (biproductIso (k := k) f g).inv =
      (Mat_.embedding _).map (LinearTensor.tmul (biproduct.ι f p.1) (biproduct.ι g p.2)) :=
  biproduct.ι_desc _ _

variable {E : Type (max u₁ u₂)} [Category.{max v₁ v₂} E] [Preadditive E] [HasFiniteBiproducts E]

section Lift

variable [Linear k E] (F : C ⥤ D ⥤ E) [F.Additive] [F.Linear k] [∀ X, (F.obj X).Additive]
  [∀ X, (F.obj X).Linear k]

variable (k) in
/-- The extension of a bifunctor `F : C ⥤ D ⥤ E`, additive and `k`-linear in each variable, to a
`k`-linear functor `DeligneProduct k C D ⥤ E` into an additive `k`-linear category: it sends
`X ⊠ Y` to `F X Y` and formal biproducts to biproducts. -/
def lift : DeligneProduct k C D ⥤ E :=
  Mat_.lift (LinearTensor.lift k F)

instance : (lift k F).Additive :=
  inferInstanceAs <| Functor.Additive (Mat_.lift (LinearTensor.lift k F))

instance : (lift k F).Linear k :=
  inferInstanceAs <| Functor.Linear k (Mat_.lift (LinearTensor.lift k F))

/-- `lift k F` sends a formal biproduct of pairs `X ⊠ Y` to the biproduct of the objects
`F X Y`. -/
@[simp]
theorem lift_obj (M : DeligneProduct k C D) :
    (lift k F).obj M = ⨁ fun i ↦ (F.obj (M.X i).fst).obj (M.X i).snd :=
  rfl

/-- `lift k F` sends a matrix of morphisms to the matrix of their images under
`LinearTensor.lift k F`. -/
@[simp]
theorem lift_map {M N : DeligneProduct k C D} (t : M ⟶ N) :
    (lift k F).map t = biproduct.matrix fun i j ↦ (LinearTensor.lift k F).map (t i j) :=
  rfl

variable (k) in
/-- The extension `lift k F` restricts along `bifunctor` to `F`. -/
def bifunctorCompLiftIso : bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj (lift k F) ≅ F :=
  Functor.isoWhiskerLeft (LinearTensor.bifunctor k C D)
      ((Functor.whiskeringRight D _ E).mapIso (Mat_.embeddingLiftIso (LinearTensor.lift k F))) ≪≫
    LinearTensor.bifunctorCompLiftIso k F

/-- The component of `bifunctorCompLiftIso k F` at `X ⊠ Y` is the identity of `F X Y`, seen as a
map out of the one-term biproduct `(lift k F).obj (X ⊠ Y)`. -/
@[simp]
theorem bifunctorCompLiftIso_hom_app_app (X : C) (Y : D) :
    ((bifunctorCompLiftIso k F).hom.app X).app Y = biproduct.desc fun _ ↦ 𝟙 ((F.obj X).obj Y) :=
  -- By definition, the component is that of `Mat_.embeddingLiftIso`, which is this
  -- `biproduct.desc`, followed by the identity component of `LinearTensor.bifunctorCompLiftIso`.
  Category.comp_id _

/-- The inverse component of `bifunctorCompLiftIso k F` at `X ⊠ Y` is the identity of `F X Y`, seen
as a map into the one-term biproduct `(lift k F).obj (X ⊠ Y)`. -/
@[simp]
theorem bifunctorCompLiftIso_inv_app_app (X : C) (Y : D) :
    ((bifunctorCompLiftIso k F).inv.app X).app Y = biproduct.lift fun _ ↦ 𝟙 ((F.obj X).obj Y) :=
  -- By definition, the identity component of `LinearTensor.bifunctorCompLiftIso` followed by the
  -- inverse component of `Mat_.embeddingLiftIso`, which is this `biproduct.lift`.
  Category.id_comp _

end Lift

/-- Two additive functors out of `DeligneProduct k C D` whose restrictions along `bifunctor` are
isomorphic are isomorphic. -/
def ext {G G' : DeligneProduct k C D ⥤ E} [G.Additive] [G'.Additive]
    (α : bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj G ≅
      bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj G') :
    G ≅ G' :=
  Mat_.ext (LinearTensor.ext α)

/-- The components of `ext α`: on a formal biproduct `M` of pairs, decompose `G M` as the
biproduct of the `G (X ⊠ Y)` over the entries `(X, Y)` of `M`, apply the components of `α`, and
reassemble. -/
theorem ext_hom_app {G G' : DeligneProduct k C D ⥤ E} [G.Additive] [G'.Additive]
    (α : bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj G ≅
      bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj G') (M : DeligneProduct k C D) :
    (ext α).hom.app M = (Mat_.additiveObjIsoBiproduct G M).hom ≫
      biproduct.map (fun i ↦ (α.hom.app (M.X i).fst).app (M.X i).snd) ≫
        (Mat_.additiveObjIsoBiproduct G' M).inv :=
  -- `ext α` is `Mat_.ext (LinearTensor.ext α)`, and the components of `LinearTensor.ext α` are
  -- those of `α` (`LinearTensor.ext_hom_app`, which holds by `rfl`).
  Mat_.ext_hom_app (LinearTensor.ext α) M

/-- **Uniqueness of the extension**: an additive functor `L` out of `DeligneProduct k C D` whose
restriction along `bifunctor` is isomorphic to `F` is isomorphic to `lift k F`. -/
def liftUnique [Linear k E] (F : C ⥤ D ⥤ E) [F.Additive] [F.Linear k] [∀ X, (F.obj X).Additive]
    [∀ X, (F.obj X).Linear k] (L : DeligneProduct k C D ⥤ E) [L.Additive]
    (α : bifunctor k C D ⋙ (Functor.whiskeringRight D _ E).obj L ≅ F) : L ≅ lift k F :=
  ext (α ≪≫ (bifunctorCompLiftIso k F).symm)

end DeligneProduct

namespace IsSplitSimpleFamily

variable {k : Type w} [CommSemiring k]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C] [HasFiniteBiproducts C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D] [HasFiniteBiproducts D]
  {ι : Type*} {ι' : Type*} {S : ι → C} {T : ι' → D}

/-- **Products of split simple families**: if `S` and `T` are split simple families in `C` and
`D`, then the objects `S i ⊠ T j` form a split simple family in the Deligne product
`DeligneProduct k C D`, indexed by `ι × ι'`. -/
theorem deligneProduct (hS : IsSplitSimpleFamily k S) (hT : IsSplitSimpleFamily k T) :
    IsSplitSimpleFamily k
      (fun p : ι × ι' ↦ ((DeligneProduct.bifunctor k C D).obj (S p.1)).obj (T p.2)) where
  bijective_algebraMap p := by
    have h : algebraMap k (End ((Mat_.embedding (LinearTensor k C D)).obj ⟨S p.1, T p.2⟩)) =
        (Mat_.embedding _).mapEndAlgHom k _ ∘
          algebraMap k (End (⟨S p.1, T p.2⟩ : LinearTensor k C D)) :=
      funext fun r ↦ (((Mat_.embedding _).mapEndAlgHom k _).commutes r).symm
    have key := ((Mat_.embedding _).mapEndAlgHom_bijective k _
      ⟨(Mat_.embedding _).map_injective, (Mat_.embedding _).map_surjective⟩).comp
        (LinearTensor.bijective_algebraMap_mk (hS.bijective_algebraMap p.1)
          (hT.bijective_algebraMap p.2))
    rw [← h] at key
    exact key
  homOrthogonal p q hpq := by
    have : Subsingleton ((⟨S p.1, T p.2⟩ : LinearTensor k C D) ⟶ ⟨S q.1, T q.2⟩) := by
      by_cases h : p.1 = q.1
      · have : Subsingleton (T p.2 ⟶ T q.2) := hT.homOrthogonal fun h' ↦ hpq (Prod.ext h h')
        infer_instance
      · have : Subsingleton (S p.1 ⟶ S q.1) := hS.homOrthogonal h
        infer_instance
    exact ((Mat_.embedding (LinearTensor k C D)).map_surjective (X := ⟨S p.1, T p.2⟩)
      (Y := ⟨S q.1, T q.2⟩)).subsingleton
  exists_iso_biproduct M := by
    choose κ hκ a ha using fun i ↦ hS.exists_iso_biproduct (M.X i).fst
    choose κ' hκ' b hb using fun i ↦ hT.exists_iso_biproduct (M.X i).snd
    refine ⟨Σ i, κ i × κ' i, inferInstance, fun x ↦ (a x.1 x.2.1, b x.1 x.2.2), ⟨?_⟩⟩
    exact M.isoBiproductEmbedding ≪≫
      biproduct.mapIso (fun i ↦ (Mat_.embedding _).mapIso
        (LinearTensor.isoMk (ha i).some (hb i).some) ≪≫
          DeligneProduct.biproductIso (fun x ↦ S (a i x)) (fun y ↦ T (b i y))) ≪≫
      biproductBiproductIso _ _

end IsSplitSimpleFamily

end TauCeti
