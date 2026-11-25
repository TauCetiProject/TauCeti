/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import TauCeti.RepresentationTheory.RestrictScalars
public import TauCeti.RepresentationTheory.Smooth.BaseChange
public import TauCeti.RepresentationTheory.Smooth.Category

/-!
# Change of coefficients as functors on smooth representations

Let `A → B` be a homomorphism of commutative rings and `G` a topological group. Base change
`V ↦ B ⊗_A V` (Tau Ceti's `Representation.baseChange`) preserves smoothness, and this file makes
it a functor `TauCeti.SmoothRep.extendScalars B : SmoothRep A G ⥤ SmoothRep B G`. It is additive,
naturally isomorphic to the identity along `A → A` (`TauCeti.SmoothRep.extendScalarsId`), and
compatible with composition along `A → B → C` (`TauCeti.SmoothRep.extendScalarsComp`, from
Mathlib's `TensorProduct.AlgebraTensorModule.cancelBaseChange`).

Restriction of scalars `TauCeti.SmoothRep.restrictScalars A : SmoothRep B G ⥤ SmoothRep A G`
reads a `B`-module as an `A`-module through `A → B`, with the same operators. Base change is left
adjoint to it (`TauCeti.SmoothRep.extendRestrictScalarsAdj`): an intertwining map
`B ⊗_A V → W` corresponds to the `A`-linear intertwining map `v ↦ f (1 ⊗ v)`.

The carriers of `B ⊗_A V` live in `Type (max v w)` for `B : Type v` and `V : Type w`, so, as for
Mathlib's `ModuleCat.extendScalars`, the functors act on `SmoothRep.{max v w}`.

## Main definitions

* `TauCeti.SmoothRep.extendScalars B`: base change `SmoothRep A G ⥤ SmoothRep B G`.
* `TauCeti.SmoothRep.restrictScalars A`: restriction of scalars `SmoothRep B G ⥤ SmoothRep A G`.
* `TauCeti.SmoothRep.extendRestrictScalarsAdj`: the adjunction
  `extendScalars B ⊣ restrictScalars A`.
* `TauCeti.SmoothRep.extendScalarsId`: base change along the identity is the identity functor.
* `TauCeti.SmoothRep.extendScalarsComp`: base change along `A → B → C` is base change along
  `A → C`.
-/

@[expose] public section

open CategoryTheory TensorProduct Representation

universe w u v

namespace TauCeti

namespace SmoothRep

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Composition of morphisms of smooth representations evaluates as composition of maps. -/
@[simp] lemma comp_hom_hom_apply {R : Type*} [Ring R] {X Y Z : SmoothRep.{w} R G} (f : X ⟶ Y)
    (g : Y ⟶ Z) (x : X.obj) : (f ≫ g).hom.hom x = g.hom.hom (f.hom.hom x) :=
  (rfl)

/-- A sum of morphisms of smooth representations evaluates as a sum. -/
@[simp] lemma add_hom_hom_apply {R : Type*} [Ring R] {X Y : SmoothRep.{w} R G} (f g : X ⟶ Y)
    (x : X.obj) : (f + g).hom.hom x = f.hom.hom x + g.hom.hom x :=
  (rfl)

/-! ### Base change -/

section ExtendScalars

variable {A : Type u} [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
  [SeparatelyContinuousMul G]

/-- **Base change of smooth representations**: the functor `V ↦ B ⊗_A V` from smooth
representations over `A` to smooth representations over `B`, acting on morphisms by `f ↦ B ⊗ f`.
Smoothness is preserved by `Representation.isSmooth_baseChange`. -/
-- An abbreviation, so that instance search sees the carrier `B ⊗[A] V` of the objects.
noncomputable abbrev extendScalars : SmoothRep.{max v w} A G ⥤ SmoothRep.{max v w} B G where
  obj V := of (V.obj.ρ.baseChange B)
  map f := ObjectProperty.homMk <| Rep.ofHom
    { toLinearMap := f.hom.hom.toLinearMap.baseChange B
      isIntertwining' g := by simpa using (f.hom.hom.baseChange B).isIntertwining' g }
  map_id V := ObjectProperty.hom_ext _ <| Rep.hom_ext <| IntertwiningMap.ext <|
    LinearMap.baseChange_id (R := A) (A := B) (M := V.obj)
  map_comp f g := ObjectProperty.hom_ext _ <| Rep.hom_ext <| IntertwiningMap.ext <|
    LinearMap.baseChange_comp f.hom.hom.toLinearMap g.hom.hom.toLinearMap

variable {B}

/-- The underlying representation of `(extendScalars B).obj V` is `B ⊗_A V`. -/
@[simp] lemma extendScalars_obj_obj_ρ (V : SmoothRep.{max v w} A G) :
    ((extendScalars B).obj V).obj.ρ = V.obj.ρ.baseChange B :=
  (rfl)

/-- `extendScalars B` sends `f` to `B ⊗ f`, which acts on pure tensors by `b ⊗ v ↦ b ⊗ f v`. -/
lemma extendScalars_map_hom_hom_tmul {V W : SmoothRep.{max v w} A G} (f : V ⟶ W) (b : B)
    (v : V.obj) : ((extendScalars B).map f).hom.hom (b ⊗ₜ[A] v) = b ⊗ₜ[A] f.hom.hom v :=
  (rfl)

variable (B) in
/-- Two morphisms out of `B ⊗_A V` that agree on pure tensors are equal. -/
lemma extendScalars_hom_ext {V : SmoothRep.{max v w} A G} {W : SmoothRep.{max v w} B G}
    {f g : (extendScalars B).obj V ⟶ W}
    (h : ∀ (b : B) (v : V.obj), f.hom.hom (b ⊗ₜ[A] v) = g.hom.hom (b ⊗ₜ[A] v)) : f = g :=
  ObjectProperty.hom_ext _ <| Rep.hom_ext <| IntertwiningMap.ext <| LinearMap.ext fun x ↦ by
    induction x using TensorProduct.inductionOn with
    | tmul b v => exact h b v
    | add x y hx hy => rw [map_add, map_add, hx, hy]

variable (B) in
/-- Base change of smooth representations is an additive functor. -/
instance additive_extendScalars :
    (extendScalars B : SmoothRep.{max v w} A G ⥤ SmoothRep.{max v w} B G).Additive where
  map_add {_ _ f g} := extendScalars_hom_ext B fun b v ↦ by
    rw [add_hom_hom_apply]
    simp [tmul_add]

end ExtendScalars

/-! ### Restriction of scalars -/

section RestrictScalars

variable (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]

/-- The `A`-module structure `a • v = algebraMap A B a • v` on a representation over `B`. It is
not an instance: on a base change `B ⊗_A V` it would differ from the tensor product's own
`A`-module structure. -/
abbrev restrictModule (V : SmoothRep.{w} B G) : Module A V.obj :=
  Module.compHom V.obj (algebraMap A B)

/-- The `A`-module structure `restrictModule` is compatible with the `B`-module structure. -/
lemma isScalarTower_restrictModule (V : SmoothRep.{w} B G) :
    letI := restrictModule A V
    IsScalarTower A B V.obj :=
  letI := restrictModule A V
  ⟨fun a b v ↦ by rw [Algebra.smul_def]; exact mul_smul _ _ _⟩

/-- **Restriction of scalars** along `A → B`: a smooth representation over `B` read over `A`
through `a • v = algebraMap A B a • v`, with the same operators and the same intertwining maps. -/
def restrictScalars : SmoothRep.{w} B G ⥤ SmoothRep.{w} A G where
  obj V :=
    letI := restrictModule A V
    haveI := isScalarTower_restrictModule A V
    ⟨Rep.of (X := V.obj)
      { toFun g := (V.obj.ρ g).restrictScalars A
        map_one' := by ext; simp
        map_mul' g h := by ext; simp },
      ⟨fun v ↦ IsSmooth.isOpen_stabilizer (ρ := V.obj.ρ) v⟩⟩
  map {V W} f :=
    letI := restrictModule A V
    letI := restrictModule A W
    haveI := isScalarTower_restrictModule A V
    haveI := isScalarTower_restrictModule A W
    ObjectProperty.homMk <| Rep.ofHom
      { toLinearMap := f.hom.hom.toLinearMap.restrictScalars A
        isIntertwining' g := LinearMap.ext fun v ↦ by
          simpa using LinearMap.congr_fun (f.hom.hom.isIntertwining' g) v }
  map_id _ := ObjectProperty.hom_ext _ <| Rep.hom_ext <| IntertwiningMap.ext <| LinearMap.ext
    fun _ ↦ rfl
  map_comp _ _ := ObjectProperty.hom_ext _ <| Rep.hom_ext <| IntertwiningMap.ext <| LinearMap.ext
    fun _ ↦ rfl

variable {A}

/-- The `B`-module structure on the carrier of `(restrictScalars A).obj V`, that of `V`. -/
instance instModuleRestrictScalarsObj (V : SmoothRep.{w} B G) :
    Module B ((restrictScalars A).obj V).obj :=
  inferInstanceAs (Module B V.obj)

/-- On `(restrictScalars A).obj V` the `A`- and `B`-actions form a scalar tower. -/
instance isScalarTower_restrictScalars_obj (V : SmoothRep.{w} B G) :
    IsScalarTower A B ((restrictScalars A).obj V).obj :=
  isScalarTower_restrictModule A V

/-- In `(restrictScalars A).obj V`, `a : A` acts as `algebraMap A B a`. -/
lemma restrictScalars_obj_smul (V : SmoothRep.{w} B G) (a : A)
    (v : ((restrictScalars A).obj V).obj) : a • v = algebraMap A B a • v :=
  (rfl)

/-- `restrictScalars A` does not change the underlying map of a morphism. -/
@[simp] lemma restrictScalars_map_hom_hom_apply {V W : SmoothRep.{w} B G} (f : V ⟶ W)
    (v : ((restrictScalars A).obj V).obj) :
    ((restrictScalars A).map f).hom.hom v = f.hom.hom (show V.obj from v) :=
  (rfl)

/-- `restrictScalars A` keeps the operators. -/
@[simp] lemma restrictScalars_obj_obj_ρ_apply (V : SmoothRep.{w} B G) (g : G)
    (v : ((restrictScalars A).obj V).obj) :
    ((restrictScalars A).obj V).obj.ρ g v = V.obj.ρ g (show V.obj from v) :=
  (rfl)

end RestrictScalars

/-! ### The adjunction -/

section Adjunction

variable {A : Type u} [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
  [SeparatelyContinuousMul G]

/-- The unit of the base change adjunction: `v ↦ 1 ⊗ v`, an `A`-linear intertwining map
`V → B ⊗_A V`. -/
noncomputable def extendRestrictScalarsUnitApp (V : SmoothRep.{max v w} A G) :
    V ⟶ (restrictScalars A).obj ((extendScalars B).obj V) :=
  ObjectProperty.homMk <| ConcreteCategory.ofHom (C := Rep.{max v w} A G) (X := V.obj)
    (Y := ((restrictScalars A).obj ((extendScalars B).obj V)).obj)
    { toFun v := ((1 : B) ⊗ₜ[A] v : B ⊗[A] V.obj)
      map_add' := tmul_add 1
      map_smul' a v := by
        change ((1 : B) ⊗ₜ[A] (a • v) : B ⊗[A] V.obj) =
          algebraMap A B a • ((1 : B) ⊗ₜ[A] v : B ⊗[A] V.obj)
        rw [← smul_tmul, ← Algebra.algebraMap_eq_smul_one, smul_tmul', smul_eq_mul, mul_one]
      isIntertwining' g := LinearMap.ext fun (v : V.obj) ↦ by
        change ((1 : B) ⊗ₜ[A] V.obj.ρ g v : B ⊗[A] V.obj) =
          (V.obj.ρ.baseChange B g) ((1 : B) ⊗ₜ[A] v)
        simp }

/-- The counit of the base change adjunction: `b ⊗ w ↦ b • w`, a `B`-linear intertwining map
`B ⊗_A W → W`. -/
noncomputable def extendRestrictScalarsCounitApp (W : SmoothRep.{max v w} B G) :
    (extendScalars B).obj ((restrictScalars A).obj W) ⟶ W :=
  letI := restrictModule A W
  haveI := isScalarTower_restrictModule A W
  ObjectProperty.homMk <| ConcreteCategory.ofHom (C := Rep.{max v w} B G)
    (X := ((extendScalars B).obj ((restrictScalars A).obj W)).obj) (Y := W.obj) <|
    (LinearMap.liftBaseChange B
      ({ toFun x := (show W.obj from x)
         map_add' _ _ := rfl
         map_smul' _ _ := rfl } : ((restrictScalars A).obj W).obj →ₗ[A] W.obj))
      |>.intertwiningMap_of_isIntertwiningMap _ _ fun g x ↦ by
        induction x using TensorProduct.inductionOn with
        | tmul b x =>
          rw [show ((extendScalars B).obj ((restrictScalars A).obj W)).obj.ρ g (b ⊗ₜ[A] x) =
            b ⊗ₜ[A] ((restrictScalars A).obj W).obj.ρ g x by simp; rfl]
          exact (map_smul (W.obj.ρ g) b (show W.obj from x)).symm
        | add x y hx hy => simp only [map_add, hx, hy]

/-- The unit of the base change adjunction sends `v` to `1 ⊗ v`. -/
@[simp] lemma extendRestrictScalarsUnitApp_hom_hom_apply (V : SmoothRep.{max v w} A G)
    (v : V.obj) :
    (extendRestrictScalarsUnitApp B V).hom.hom v = ((1 : B) ⊗ₜ[A] v : B ⊗[A] V.obj) :=
  (rfl)

/-- The counit of the base change adjunction sends `b ⊗ w` to `b • w`. -/
@[simp] lemma extendRestrictScalarsCounitApp_hom_hom_tmul (W : SmoothRep.{max v w} B G) (b : B)
    (x : ((restrictScalars A).obj W).obj) :
    (extendRestrictScalarsCounitApp B W).hom.hom (b ⊗ₜ[A] x) = (show W.obj from b • x) :=
  (rfl)

/-- The left triangle identity of the base change adjunction: `b ⊗ v ↦ b ⊗ (1 ⊗ v) ↦ b ⊗ v`. -/
lemma extendRestrictScalars_left_triangle (V : SmoothRep.{max v w} A G) :
    (extendScalars B).map (extendRestrictScalarsUnitApp B V) ≫
      extendRestrictScalarsCounitApp B ((extendScalars B).obj V) = 𝟙 _ := by
  refine ObjectProperty.hom_ext _ (Rep.hom_ext (IntertwiningMap.ext (LinearMap.ext fun x ↦ ?_)))
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    change (extendRestrictScalarsCounitApp B ((extendScalars B).obj V)).hom.hom
      (((extendScalars B).map (extendRestrictScalarsUnitApp B V)).hom.hom (b ⊗ₜ[A] v)) = b ⊗ₜ[A] v
    change b • ((1 : B) ⊗ₜ[A] v : B ⊗[A] V.obj) = b ⊗ₜ[A] v
    rw [smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

/-- **Base change is left adjoint to restriction of scalars.** The unit is `v ↦ 1 ⊗ v` and the
counit is `b ⊗ w ↦ b • w`. -/
noncomputable def extendRestrictScalarsAdj :
    (extendScalars B : SmoothRep.{max v w} A G ⥤ SmoothRep.{max v w} B G) ⊣
      restrictScalars A where
  unit :=
    { app := extendRestrictScalarsUnitApp.{w} B
      naturality _ _ f := ObjectProperty.hom_ext _ <| Rep.hom_ext <| IntertwiningMap.ext <|
        LinearMap.ext fun _ ↦ rfl }
  counit :=
    { app := extendRestrictScalarsCounitApp.{w} B
      naturality _ _ f := extendScalars_hom_ext B fun b v ↦ by
        rw [comp_hom_hom_apply, comp_hom_hom_apply]
        exact (map_smul f.hom.hom b _).symm }
  left_triangle_components V := extendRestrictScalars_left_triangle B V
  right_triangle_components W := ObjectProperty.hom_ext _ <| Rep.hom_ext <|
    IntertwiningMap.ext <| LinearMap.ext fun w ↦ one_smul B (show W.obj from w)

end Adjunction

/-! ### Identity and composition -/

section IdComp

variable (A : Type u) [CommRing A] [SeparatelyContinuousMul G]

/-- **Base change along the identity is the identity**: `A ⊗_A V ≅ V`, `a ⊗ v ↦ a • v`. -/
noncomputable def extendScalarsId :
    (extendScalars A : SmoothRep.{max u w} A G ⥤ SmoothRep.{max u w} A G) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun V ↦ ObjectProperty.isoMk _ <| Rep.mkIso <| .mk (TensorProduct.lid A V.obj) fun g ↦ by
      ext v
      simp)
    fun f ↦ extendScalars_hom_ext A fun a v ↦ by simp

variable {A} (B : Type v) [CommRing B] [Algebra A B] (C : Type v) [CommRing C] [Algebra A C]
  [Algebra B C] [IsScalarTower A B C]

/-- **Base change is compatible with composition**: for `A → B → C`, base change to `B` and then
to `C` is base change to `C`, through `C ⊗_B (B ⊗_A V) ≅ C ⊗_A V`, `c ⊗ (b ⊗ v) ↦ (c b) ⊗ v`
(Mathlib's `TensorProduct.AlgebraTensorModule.cancelBaseChange`). The rings `B` and `C` are taken
in one universe, so that both functors act on `SmoothRep.{max v w}`. -/
noncomputable def extendScalarsComp :
    (extendScalars B ⋙ extendScalars C : SmoothRep.{max v w} A G ⥤ SmoothRep.{max v w} C G) ≅
      extendScalars C :=
  NatIso.ofComponents
    (fun V ↦ ObjectProperty.isoMk _ <| Rep.mkIso <|
      .mk (AlgebraTensorModule.cancelBaseChange A B C C V.obj) fun g ↦ LinearMap.ext fun x ↦ by
        induction x using TensorProduct.inductionOn with
        | tmul c y =>
          induction y using TensorProduct.inductionOn with
          | tmul b v => simp
          | add y z hy hz =>
            simp only [tmul_add, map_add, LinearMap.comp_apply] at hy hz ⊢
            rw [hy, hz]
        | add x y hx hy => simp only [map_add, LinearMap.comp_apply] at hx hy ⊢; rw [hx, hy])
    fun f ↦ extendScalars_hom_ext C fun c x ↦ by
      induction x using TensorProduct.inductionOn with
      | tmul b v => simp
      | add y z hy hz => simp only [tmul_add, map_add] at hy hz ⊢; rw [hy, hz]

end IdComp

end SmoothRep

end TauCeti
