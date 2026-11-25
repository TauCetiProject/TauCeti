/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.RestrictScalars

/-!
# Change of coefficients as functors on representations

Let `A → B` be a homomorphism of commutative rings and `G` a monoid. Base change `V ↦ B ⊗_A V`
(Tau Ceti's `Representation.baseChange`, acting on intertwining maps by
`Representation.IntertwiningMap.baseChange`) is a functor `Rep.extendScalars B : Rep A G ⥤ Rep B G`.
It is additive, naturally isomorphic to the identity along `A → A` (`Rep.extendScalarsId`), and
compatible with composition along `A → B → C` (`Rep.extendScalarsComp`, from Mathlib's
`TensorProduct.AlgebraTensorModule.cancelBaseChange`).

Restriction of scalars `Rep.restrictScalars A : Rep B G ⥤ Rep A G` reads a `B`-module as an
`A`-module through `A → B`, with the same operators (`Representation.restrictScalars`); it is also
additive. Base change is left adjoint to it (`Rep.extendRestrictScalarsAdj`): an intertwining map
`B ⊗_A V → W` corresponds to the `A`-linear intertwining map `v ↦ f (1 ⊗ v)`.

The declarations follow Mathlib's change-of-rings API for modules,
`ModuleCat.extendScalars`, `ModuleCat.restrictScalars`, `ModuleCat.extendRestrictScalarsAdj`,
`ModuleCat.extendScalarsId` and `ModuleCat.extendScalarsComp` in
`Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`, whose names, unit `v ↦ 1 ⊗ v` and counit
`b ⊗ w ↦ b • w` they reuse. As there, the carriers of `B ⊗_A V` live in `Type (max v w)` for
`B : Type v` and `V : Type w`, so base change acts on `Rep.{max v w}`.

## Main definitions

* `Rep.extendScalars B`: base change `Rep A G ⥤ Rep B G`.
* `Rep.restrictScalars A`: restriction of scalars `Rep B G ⥤ Rep A G`.
* `Rep.extendRestrictScalarsAdj`: the adjunction `extendScalars B ⊣ restrictScalars A`.
* `Rep.extendScalarsId`: base change along the identity is the identity functor.
* `Rep.extendScalarsComp`: base change along `A → B → C` is base change along `A → C`.
-/

@[expose] public section

open CategoryTheory TensorProduct Representation

universe w u v

namespace Rep

variable {G : Type*} [Monoid G]

/-! ### Base change -/

section ExtendScalars

variable {A : Type u} [CommRing A] (B : Type v) [CommRing B] [Algebra A B]

/-- **Base change of representations**: the functor `V ↦ B ⊗_A V` from representations over `A`
to representations over `B`, acting on intertwining maps by `f ↦ B ⊗ f`. -/
-- An abbreviation, so that instance search and `simp` see the carrier `B ⊗[A] V` of the objects.
noncomputable abbrev extendScalars : Rep.{max v w} A G ⥤ Rep.{max v w} B G where
  obj V := of (V.ρ.baseChange B)
  map f := ofHom (f.hom.baseChange B)
  map_id _ := hom_ext <| IntertwiningMap.ext <|
    (IntertwiningMap.toLinearMap_baseChange _ B).trans LinearMap.baseChange_id
  map_comp f g := hom_ext <| IntertwiningMap.baseChange_comp g.hom f.hom B

variable {B}

-- Not `@[simp]`: `simp` proves it by unfolding the abbreviation `extendScalars` and
-- `Representation.IntertwiningMap.baseChange_tmul`.
/-- `extendScalars B` sends `f` to `B ⊗ f`, which acts on pure tensors by `b ⊗ v ↦ b ⊗ f v`. -/
lemma extendScalars_map_hom_tmul {V W : Rep.{max v w} A G} (f : V ⟶ W) (b : B) (v : V) :
    ((extendScalars B).map f).hom (b ⊗ₜ[A] v) = b ⊗ₜ[A] f.hom v :=
  IntertwiningMap.baseChange_tmul f.hom B b v

variable (B) in
/-- Two morphisms out of `B ⊗_A V` that agree on pure tensors are equal. -/
lemma extendScalars_hom_ext {V : Rep.{max v w} A G} {W : Rep.{max v w} B G}
    {f g : (extendScalars B).obj V ⟶ W}
    (h : ∀ (b : B) (v : V), f.hom (b ⊗ₜ[A] v) = g.hom (b ⊗ₜ[A] v)) : f = g :=
  hom_ext <| IntertwiningMap.ext <| LinearMap.ext fun x ↦ by
    induction x using TensorProduct.inductionOn with
    | tmul b v => exact h b v
    | add x y hx hy => rw [map_add, map_add, hx, hy]

variable (B) in
/-- Base change of representations is an additive functor. -/
instance additive_extendScalars :
    (extendScalars B : Rep.{max v w} A G ⥤ Rep.{max v w} B G).Additive where
  map_add {_ _ f g} := extendScalars_hom_ext B fun b v ↦ by simp [add_hom, tmul_add]

end ExtendScalars

/-! ### Restriction of scalars -/

section RestrictScalars

variable (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]

/-- **Restriction of scalars** along `A → B`: a representation over `B` read over `A` through
`a • v = algebraMap A B a • v` (Mathlib's `Module.restrictScalars`), with the same operators
(`Representation.restrictScalars`) and the same intertwining maps. -/
def restrictScalars : Rep.{w} B G ⥤ Rep.{w} A G where
  obj V :=
    letI := Module.restrictScalars A B V
    haveI := IsScalarTower.restrictScalars A B V
    of (V.ρ.restrictScalars A)
  map {V W} f :=
    letI := Module.restrictScalars A B V
    letI := Module.restrictScalars A B W
    haveI := IsScalarTower.restrictScalars A B V
    haveI := IsScalarTower.restrictScalars A B W
    ofHom
      { toLinearMap := f.hom.toLinearMap.restrictScalars A
        isIntertwining' g := LinearMap.ext fun v ↦ by
          simpa using LinearMap.congr_fun (f.hom.isIntertwining' g) v }

variable {A}

/-- The `B`-module structure on the carrier of `(restrictScalars A).obj V`, that of `V`. -/
instance instModuleRestrictScalarsObj (V : Rep.{w} B G) : Module B ((restrictScalars A).obj V) :=
  (inferInstance : Module B V)

/-- On `(restrictScalars A).obj V` the `A`- and `B`-actions form a scalar tower. -/
instance isScalarTower_restrictScalars_obj (V : Rep.{w} B G) :
    IsScalarTower A B ((restrictScalars A).obj V) :=
  IsScalarTower.restrictScalars A B V

/-- In `(restrictScalars A).obj V`, `a : A` acts as `algebraMap A B a`. -/
lemma restrictScalars_obj_smul (V : Rep.{w} B G) (a : A) (v : (restrictScalars A).obj V) :
    a • v = algebraMap A B a • v :=
  (rfl)

/-- `restrictScalars A` does not change the underlying map of a morphism. -/
@[simp] lemma restrictScalars_map_hom_apply {V W : Rep.{w} B G} (f : V ⟶ W)
    (v : (restrictScalars A).obj V) :
    ((restrictScalars A).map f).hom v = f.hom (v : V) :=
  (rfl)

/-- `restrictScalars A` keeps the operators. -/
@[simp] lemma restrictScalars_obj_ρ_apply (V : Rep.{w} B G) (g : G)
    (v : (restrictScalars A).obj V) :
    ((restrictScalars A).obj V).ρ g v = V.ρ g (v : V) :=
  letI := Module.restrictScalars A B V
  haveI := IsScalarTower.restrictScalars A B V
  Representation.restrictScalars_apply A V.ρ g v

variable (A) in
/-- Restriction of scalars of representations is an additive functor. -/
instance additive_restrictScalars : (restrictScalars A : Rep.{w} B G ⥤ Rep.{w} A G).Additive where
  map_add := rfl

end RestrictScalars

/-! ### The adjunction -/

section Adjunction

variable (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]

/-- **Base change is left adjoint to restriction of scalars.** The unit is `v ↦ 1 ⊗ v`
(`Rep.extendRestrictScalarsAdj_unit_app_hom_apply`) and the counit is `b ⊗ w ↦ b • w`
(`Rep.extendRestrictScalarsAdj_counit_app_hom_tmul`). -/
noncomputable def extendRestrictScalarsAdj :
    (extendScalars B : Rep.{max v w} A G ⥤ Rep.{max v w} B G) ⊣ restrictScalars A where
  unit :=
    { app V := ConcreteCategory.ofHom (C := Rep.{max v w} A G) (X := V)
        (Y := (restrictScalars A).obj ((extendScalars B).obj V))
        { toFun v := ((1 : B) ⊗ₜ[A] v : B ⊗[A] V)
          map_add' := tmul_add 1
          map_smul' a v := by
            have h : ((1 : B) ⊗ₜ[A] (a • v) : B ⊗[A] V) = algebraMap A B a • (1 : B) ⊗ₜ[A] v := by
              rw [algebraMap_smul, tmul_smul]
            exact h.trans (restrictScalars_obj_smul ((extendScalars B).obj V) a _).symm
          isIntertwining' g := LinearMap.ext fun v ↦ by
            have h : ((1 : B) ⊗ₜ[A] V.ρ g v : B ⊗[A] V) =
                V.ρ.baseChange B g ((1 : B) ⊗ₜ[A] v) := by
              rw [baseChange_apply, LinearMap.baseChange_tmul]
            exact h.trans (restrictScalars_obj_ρ_apply ((extendScalars B).obj V) g _).symm }
      naturality _ _ f := hom_ext <| IntertwiningMap.ext <| LinearMap.ext fun v ↦ by
        exact (IntertwiningMap.baseChange_tmul f.hom B 1 v).symm }
  counit :=
    { app W :=
        letI := Module.restrictScalars A B W
        haveI := IsScalarTower.restrictScalars A B W
        ConcreteCategory.ofHom (C := Rep.{max v w} B G)
          (X := (extendScalars B).obj ((restrictScalars A).obj W)) (Y := W) <|
          (LinearMap.liftBaseChange B
            ((LinearMap.id : W →ₗ[B] W).restrictScalars A : (restrictScalars A).obj W →ₗ[A] W))
            |>.intertwiningMap_of_isIntertwiningMap _ _ <|
              ((LinearMap.isIntertwiningMap_liftBaseChange_iff _ W.ρ _).2
                (restrictScalars_obj_ρ_apply (A := A) W)).isIntertwining
      naturality X _ f := by
        refine extendScalars_hom_ext B (V := (restrictScalars A).obj X) fun b v ↦ ?_
        simp only [Functor.comp_map, Functor.id_map, hom_comp, IntertwiningMap.comp_apply,
          hom_ofHom]
        rw [IntertwiningMap.baseChange_tmul]
        exact (map_smul f.hom b _).symm }
  left_triangle_components V := by
    refine extendScalars_hom_ext B (V := V) fun b v ↦ ?_
    simp only [hom_comp, IntertwiningMap.comp_apply, hom_ofHom, IntertwiningMap.baseChange_tmul,
      hom_id, IntertwiningMap.id_apply]
    exact (smul_tmul' b (1 : B) v).trans (by simp)
  right_triangle_components W := hom_ext <| IntertwiningMap.ext <| LinearMap.ext fun w ↦
    one_smul B (w : W)

variable {A B}

-- Not `@[simp]`, like `extendRestrictScalarsAdj_counit_app_hom_tmul`: `simp` rewrites the objects
-- `(𝟭 _).obj V` and `(extendScalars B ⋙ restrictScalars A).obj V` in the implicit arguments of its
-- left-hand side, so that it would never apply. Rewrite with it instead.
/-- The unit of `extendScalars B ⊣ restrictScalars A` sends `v` to `1 ⊗ v`. -/
lemma extendRestrictScalarsAdj_unit_app_hom_apply (V : Rep.{max v w} A G) (v : V) :
    ((extendRestrictScalarsAdj A B).unit.app V).hom v = (1 : B) ⊗ₜ[A] v :=
  (rfl)

/-- The counit of `extendScalars B ⊣ restrictScalars A` sends `b ⊗ w` to `b • w`. -/
lemma extendRestrictScalarsAdj_counit_app_hom_tmul (W : Rep.{max v w} B G) (b : B)
    (w : (restrictScalars A).obj W) :
    ((extendRestrictScalarsAdj A B).counit.app W).hom (b ⊗ₜ[A] w) = b • w :=
  (rfl)

/-- The adjunction sends `f : B ⊗_A V ⟶ W` to `v ↦ f (1 ⊗ v)`. -/
@[simp] lemma extendRestrictScalarsAdj_homEquiv_apply_hom_apply {V : Rep.{max v w} A G}
    {W : Rep.{max v w} B G} (f : (extendScalars B).obj V ⟶ W) (v : V) :
    ((extendRestrictScalarsAdj A B).homEquiv V W f).hom v = f.hom ((1 : B) ⊗ₜ[A] v) :=
  (rfl)

/-- The adjunction sends `g : V ⟶ W` over `A` to `b ⊗ v ↦ b • g v`. -/
@[simp] lemma extendRestrictScalarsAdj_homEquiv_symm_apply_hom_tmul {V : Rep.{max v w} A G}
    {W : Rep.{max v w} B G} (g : V ⟶ (restrictScalars A).obj W) (b : B) (v : V) :
    (((extendRestrictScalarsAdj A B).homEquiv V W).symm g).hom (b ⊗ₜ[A] v) =
      b • (g.hom v : W) := by
  rw [Adjunction.homEquiv_counit, hom_comp, IntertwiningMap.comp_apply,
    extendScalars_map_hom_tmul, extendRestrictScalarsAdj_counit_app_hom_tmul]

end Adjunction

/-! ### Identity and composition -/

section IdComp

variable (A : Type u) [CommRing A]

/-- **Base change along the identity is the identity**: `A ⊗_A V ≅ V`, `a ⊗ v ↦ a • v`. -/
noncomputable def extendScalarsId :
    (extendScalars A : Rep.{max u w} A G ⥤ Rep.{max u w} A G) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun V ↦ mkIso <| .mk (TensorProduct.lid A V) fun g ↦ by ext v; simp)
    fun f ↦ extendScalars_hom_ext A fun a v ↦ by simp [mkIso]

-- Not `@[simp]`, like the other component lemmas of `extendScalarsId` and `extendScalarsComp`:
-- `simp` rewrites the objects `(𝟭 _).obj V` and `(extendScalars B ⋙ extendScalars C).obj V` in the
-- implicit arguments of their left-hand sides, so that they would never apply. Rewrite with them.
/-- `extendScalarsId` sends `a ⊗ v` to `a • v`. -/
lemma extendScalarsId_hom_app_hom_tmul (V : Rep.{max u w} A G) (a : A) (v : V) :
    ((extendScalarsId A).hom.app V).hom (a ⊗ₜ[A] v) = a • v :=
  TensorProduct.lid_tmul v a

/-- The inverse of `extendScalarsId` sends `v` to `1 ⊗ v`. -/
lemma extendScalarsId_inv_app_hom_apply (V : Rep.{max u w} A G) (v : V) :
    ((extendScalarsId A).inv.app V).hom v = (1 : A) ⊗ₜ[A] v :=
  TensorProduct.lid_symm_apply v

variable {A} (B : Type v) [CommRing B] [Algebra A B] (C : Type v) [CommRing C] [Algebra A C]
  [Algebra B C] [IsScalarTower A B C]

/-- **Base change is compatible with composition**: for `A → B → C`, base change to `B` and then
to `C` is base change to `C`, through `C ⊗_B (B ⊗_A V) ≅ C ⊗_A V`, `c ⊗ (b ⊗ v) ↦ (b • c) ⊗ v`
(Mathlib's `TensorProduct.AlgebraTensorModule.cancelBaseChange`). The rings `B` and `C` are taken
in one universe, so that both functors act on `Rep.{max v w}`. -/
noncomputable def extendScalarsComp :
    (extendScalars B ⋙ extendScalars C : Rep.{max v w} A G ⥤ Rep.{max v w} C G) ≅
      extendScalars C :=
  NatIso.ofComponents
    (fun V ↦ mkIso <| .mk (AlgebraTensorModule.cancelBaseChange A B C C V) fun g ↦ by
      ext v
      simp)
    fun f ↦ by
      refine hom_ext (IntertwiningMap.ext ?_)
      simp only [Functor.comp_obj]
      ext v
      simp

/-- `extendScalarsComp` sends `c ⊗ (b ⊗ v)` to `(b • c) ⊗ v`. -/
lemma extendScalarsComp_hom_app_hom_tmul_tmul (V : Rep.{max v w} A G) (c : C) (b : B)
    (v : V) :
    ((extendScalarsComp B C).hom.app V).hom (c ⊗ₜ[B] (b ⊗ₜ[A] v)) = (b • c) ⊗ₜ[A] v :=
  (rfl)

/-- The inverse of `extendScalarsComp` sends `c ⊗ v` to `c ⊗ (1 ⊗ v)`. -/
lemma extendScalarsComp_inv_app_hom_tmul (V : Rep.{max v w} A G) (c : C) (v : V) :
    ((extendScalarsComp B C).inv.app V).hom (c ⊗ₜ[A] v) = c ⊗ₜ[B] ((1 : B) ⊗ₜ[A] v) :=
  (rfl)

end IdComp

end Rep
