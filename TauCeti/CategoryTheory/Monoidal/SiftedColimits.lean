/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import TauCeti.CategoryTheory.Monoidal.Limits

/-!
# Sifted colimits of monoid and group objects

In a monoidal category `C` where tensoring on each side preserves colimits of sifted shape `J`
(for example, any monoidal closed category), the forgetful functors from `Mon C` and `CommMon C`
create colimits of shape `J`. If moreover `C` is Cartesian monoidal, the forgetful functors from
`Grp C` and `CommGrp C` create colimits of shape `J`.

Since filtered categories (in particular `ℕ`) are sifted (`IsFiltered.isSifted`), this provides
filtered and sequential colimits of monoid and group objects in Cartesian closed categories such as
`CompactlyGenerated`, computed on the underlying colimit in `C`.

## Main results

* `CategoryTheory.Mon.isColimitOfForget`, `CategoryTheory.Mon.forgetCreatesColimitsOfShape`:
  `Mon.forget C` creates colimits of sifted shape `J` when tensoring preserves `J`-colimits.
* `CategoryTheory.CommMon.forgetCreatesColimitsOfShape`: `CommMon.forget C` creates colimits of
  sifted shape `J` when `C` is braided and tensoring preserves `J`-colimits.
* `CategoryTheory.Grp.isColimitOfForget`, `CategoryTheory.Grp.forgetCreatesColimitsOfShape`:
  `Grp.forget C` creates colimits of sifted shape `J` in a Cartesian monoidal category when
  tensoring preserves `J`-colimits.
* `CategoryTheory.CommGrp.forgetCreatesColimitsOfShape`: the corresponding creation instance for
  commutative group objects.
-/

public section

universe w w' v u

namespace CategoryTheory

open CategoryTheory Limits MonoidalCategory MonObj

section Mon

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
  {J : Type w} [Category.{w'} J] [IsSifted J]

private lemma isSifted_exists_cospan (j₁ j₂ : J) :
    ∃ k : J, Nonempty (j₁ ⟶ k) ∧ Nonempty (j₂ ⟶ k) := by
  let S : Functor.Final (Functor.diag J) := inferInstance
  obtain ⟨X⟩ := (S.out (j₁, j₂)).is_nonempty
  exact ⟨X.right, ⟨X.hom.fst⟩, ⟨X.hom.snd⟩⟩

/-- A cocone in `Mon C` over a sifted diagram whose underlying cocone in `C` is colimiting and
whose tensor square is preserved as a colimit is itself colimiting. -/
noncomputable def Mon.isColimitOfForget (F : J ⥤ Mon C) (c : Cocone F)
    (hc : IsColimit ((Mon.forget C).mapCocone c))
    [PreservesColimit₂ (F ⋙ Mon.forget C) (F ⋙ Mon.forget C) (curriedTensor C)] :
    IsColimit c where
  desc s :=
    Mon.Hom.mk' (hc.desc ((Mon.forget C).mapCocone s))
      (one_f := by
        obtain ⟨j₀⟩ := IsSifted.nonempty (C := J)
        let desc : c.pt.X ⟶ s.pt.X := hc.desc ((Mon.forget C).mapCocone s)
        have hfac : (c.ι.app j₀).hom ≫ desc = (s.ι.app j₀).hom :=
          hc.fac ((Mon.forget C).mapCocone s) j₀
        change η[c.pt.X] ≫ desc = η[s.pt.X]
        rw [← IsMonHom.one_hom (c.ι.app j₀).hom, Category.assoc, hfac, IsMonHom.one_hom])
      (mul_f := by
        apply (hc.tensor hc).hom_ext
        intro j
        let desc : c.pt.X ⟶ s.pt.X := hc.desc ((Mon.forget C).mapCocone s)
        have hfac : (c.ι.app j).hom ≫ desc = (s.ι.app j).hom :=
          hc.fac ((Mon.forget C).mapCocone s) j
        let ιj : (F.obj j).X ⟶ c.pt.X := (c.ι.app j).hom
        have h₂ :
            (ιj ⊗ₘ ιj) ≫ μ[c.pt.X] ≫ desc = μ[(F.obj j).X] ≫ (s.ι.app j).hom := by
          dsimp [ιj]
          rw [← IsMonHom.mul_hom_assoc, hfac]
        have h₃ :
            (ιj ⊗ₘ ιj) ≫ (desc ⊗ₘ desc) ≫ μ[s.pt.X] =
              μ[(F.obj j).X] ≫ (s.ι.app j).hom := by
          dsimp [ιj]
          rw [tensorHom_comp_tensorHom_assoc, hfac, ← IsMonHom.mul_hom]
        exact h₂.trans h₃.symm)
  fac s j := Mon.Hom.ext (hc.fac ((Mon.forget C).mapCocone s) j)
  uniq s m hm :=
    Mon.Hom.ext (hc.uniq ((Mon.forget C).mapCocone s) m.hom fun j ↦ congrArg Mon.Hom.hom (hm j))

/-- The underlying morphism of the descent from `Mon.isColimitOfForget` is the descent of the
underlying cocone. -/
theorem Mon.isColimitOfForget_desc_hom (F : J ⥤ Mon C) (c : Cocone F)
    (hc : IsColimit ((Mon.forget C).mapCocone c))
    [PreservesColimit₂ (F ⋙ Mon.forget C) (F ⋙ Mon.forget C) (curriedTensor C)]
    (s : Cocone F) :
    ((Mon.isColimitOfForget F c hc).desc s).hom = hc.desc ((Mon.forget C).mapCocone s) := (rfl)

namespace Mon.ColimitConstruction

variable [∀ X : C, PreservesColimitsOfShape J (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape J (tensorRight X)]
  (F : J ⥤ Mon C) (c : Cocone (F ⋙ Mon.forget C)) (hc : IsColimit c)

private noncomputable def mulCocone :
    Cocone ((F ⋙ Mon.forget C) ⊗ (F ⋙ Mon.forget C)) :=
  Cocone.mk c.pt
    { app j := μ[(F.obj j).X] ≫ c.ι.app j
      naturality i j f := by
        let φ : (F.obj i).X ⟶ (F.obj j).X := (F.map f).hom
        let ιi : (F.obj i).X ⟶ c.pt := c.ι.app i
        let ιj : (F.obj j).X ⟶ c.pt := c.ι.app j
        have hw : φ ≫ ιj = ιi := c.w f
        change (φ ⊗ₘ φ) ≫ μ[(F.obj j).X] ≫ ιj = (μ[(F.obj i).X] ≫ ιi) ≫ 𝟙 c.pt
        rw [← IsMonHom.mul_hom_assoc φ, hw, Category.comp_id] }

private noncomputable def colimitMul : c.pt ⊗ c.pt ⟶ c.pt :=
  (hc.tensor hc).desc (mulCocone F c)

private theorem tensor_ι_colimitMul (j : J) :
    ((c.ι.app j : (F.obj j).X ⟶ c.pt) ⊗ₘ (c.ι.app j : (F.obj j).X ⟶ c.pt)) ≫
      colimitMul F c hc = μ[(F.obj j).X] ≫ (c.ι.app j : (F.obj j).X ⟶ c.pt) :=
  (hc.tensor hc).fac (mulCocone F c) j

private noncomputable def colimitOne : 𝟙_ C ⟶ c.pt :=
  let j₀ : J := Nonempty.some IsSifted.nonempty
  η[(F.obj j₀).X] ≫ c.ι.app j₀

omit [∀ X : C, PreservesColimitsOfShape J (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape J (tensorRight X)] in
private theorem one_comp_ι (j : J) :
    η[(F.obj j).X] ≫ (c.ι.app j : (F.obj j).X ⟶ c.pt) = colimitOne F c := by
  let j₀ : J := Nonempty.some IsSifted.nonempty
  obtain ⟨k, ⟨f₁⟩, ⟨f₂⟩⟩ := isSifted_exists_cospan j j₀
  let ιj : (F.obj j).X ⟶ c.pt := c.ι.app j
  let ιk : (F.obj k).X ⟶ c.pt := c.ι.app k
  let ι₀ : (F.obj j₀).X ⟶ c.pt := c.ι.app j₀
  have hw₁ : (F.map f₁).hom ≫ ιk = ιj := c.w f₁
  have hw₂ : (F.map f₂).hom ≫ ιk = ι₀ := c.w f₂
  calc
    η[(F.obj j).X] ≫ ιj
      = η[(F.obj j).X] ≫ (F.map f₁).hom ≫ ιk := by rw [hw₁]
    _ = η[(F.obj k).X] ≫ ιk := by rw [IsMonHom.one_hom_assoc]
    _ = η[(F.obj j₀).X] ≫ (F.map f₂).hom ≫ ιk := by rw [IsMonHom.one_hom_assoc]
    _ = η[(F.obj j₀).X] ≫ ι₀ := by rw [hw₂]

/-- The monoid object structure induced on the underlying colimit of a sifted diagram in `Mon C`. -/
@[instance_reducible]
noncomputable def monObj : MonObj c.pt where
  one := colimitOne F c
  mul := colimitMul F c hc
  one_mul := by
    apply IsColimit.hom_ext_whiskerLeft hc
    intro j
    let ιj : (F.obj j).X ⟶ c.pt := c.ι.app j
    have hone : η[(F.obj j).X] ≫ ιj = colimitOne F c := one_comp_ι F c j
    have hmul : (ιj ⊗ₘ ιj) ≫ colimitMul F c hc = μ[(F.obj j).X] ≫ ιj :=
      tensor_ι_colimitMul F c hc j
    change (𝟙_ C ◁ ιj) ≫ colimitOne F c ▷ c.pt ≫ colimitMul F c hc =
      (𝟙_ C ◁ ιj) ≫ (λ_ c.pt).hom
    calc
      (𝟙_ C ◁ ιj) ≫ colimitOne F c ▷ c.pt ≫ colimitMul F c hc
        = (colimitOne F c ▷ (F.obj j).X) ≫ (c.pt ◁ ιj) ≫ colimitMul F c hc := by
          rw [← Category.assoc, whisker_exchange, Category.assoc]
      _ = ((η[(F.obj j).X] ≫ ιj) ▷ (F.obj j).X) ≫ (c.pt ◁ ιj) ≫ colimitMul F c hc := by
          rw [hone]
      _ = (η[(F.obj j).X] ▷ (F.obj j).X) ≫ (ιj ▷ (F.obj j).X) ≫
            (c.pt ◁ ιj) ≫ colimitMul F c hc := by
          rw [comp_whiskerRight_assoc]
      _ = (η[(F.obj j).X] ▷ (F.obj j).X) ≫ (ιj ⊗ₘ ιj) ≫ colimitMul F c hc := by
          rw [← tensorHom_def_assoc]
      _ = (η[(F.obj j).X] ▷ (F.obj j).X) ≫ μ[(F.obj j).X] ≫ ιj := by
          rw [hmul]
      _ = (λ_ (F.obj j).X).hom ≫ ιj := by
          rw [MonObj.one_mul_assoc]
      _ = (𝟙_ C ◁ ιj) ≫ (λ_ c.pt).hom := by
          rw [leftUnitor_naturality]
  mul_one := by
    apply IsColimit.hom_ext_whiskerRight hc
    intro j
    let ιj : (F.obj j).X ⟶ c.pt := c.ι.app j
    have hone : η[(F.obj j).X] ≫ ιj = colimitOne F c := one_comp_ι F c j
    have hmul : (ιj ⊗ₘ ιj) ≫ colimitMul F c hc = μ[(F.obj j).X] ≫ ιj :=
      tensor_ι_colimitMul F c hc j
    change (ιj ▷ 𝟙_ C) ≫ c.pt ◁ colimitOne F c ≫ colimitMul F c hc =
      (ιj ▷ 𝟙_ C) ≫ (ρ_ c.pt).hom
    calc
      (ιj ▷ 𝟙_ C) ≫ c.pt ◁ colimitOne F c ≫ colimitMul F c hc
        = ((F.obj j).X ◁ colimitOne F c) ≫ (ιj ▷ c.pt) ≫ colimitMul F c hc := by
          rw [← Category.assoc, ← whisker_exchange, Category.assoc]
      _ = ((F.obj j).X ◁ (η[(F.obj j).X] ≫ ιj)) ≫ (ιj ▷ c.pt) ≫ colimitMul F c hc := by
          rw [hone]
      _ = ((F.obj j).X ◁ η[(F.obj j).X]) ≫ ((F.obj j).X ◁ ιj) ≫
            (ιj ▷ c.pt) ≫ colimitMul F c hc := by
          rw [MonoidalCategory.whiskerLeft_comp_assoc]
      _ = ((F.obj j).X ◁ η[(F.obj j).X]) ≫ (ιj ⊗ₘ ιj) ≫ colimitMul F c hc := by
          rw [← tensorHom_def'_assoc]
      _ = ((F.obj j).X ◁ η[(F.obj j).X]) ≫ μ[(F.obj j).X] ≫ ιj := by
          rw [hmul]
      _ = (ρ_ (F.obj j).X).hom ≫ ιj := by
          rw [MonObj.mul_one_assoc]
      _ = (ιj ▷ 𝟙_ C) ≫ (ρ_ c.pt).hom := by
          rw [rightUnitor_naturality]
  mul_assoc := by
    apply ((hc.tensor hc).tensor hc).hom_ext
    intro j
    let ιj : (F.obj j).X ⟶ c.pt := c.ι.app j
    have hmul : (ιj ⊗ₘ ιj) ≫ colimitMul F c hc = μ[(F.obj j).X] ≫ ιj :=
      tensor_ι_colimitMul F c hc j
    change ((ιj ⊗ₘ ιj) ⊗ₘ ιj) ≫ (colimitMul F c hc ▷ c.pt) ≫ colimitMul F c hc =
      ((ιj ⊗ₘ ιj) ⊗ₘ ιj) ≫ (α_ c.pt c.pt c.pt).hom ≫
        (c.pt ◁ colimitMul F c hc) ≫ colimitMul F c hc
    have h₁ :
        ((ιj ⊗ₘ ιj) ⊗ₘ ιj) ≫ (colimitMul F c hc ▷ c.pt) ≫ colimitMul F c hc =
        ((μ[(F.obj j).X] ▷ (F.obj j).X) ≫ μ[(F.obj j).X]) ≫ ιj := by
      calc
        ((ιj ⊗ₘ ιj) ⊗ₘ ιj) ≫ (colimitMul F c hc ▷ c.pt) ≫ colimitMul F c hc
          = (((ιj ⊗ₘ ιj) ≫ colimitMul F c hc) ⊗ₘ (ιj ≫ 𝟙 c.pt)) ≫
              colimitMul F c hc := by
            rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc]
        _ = ((μ[(F.obj j).X] ≫ ιj) ⊗ₘ (𝟙 (F.obj j).X ≫ ιj)) ≫
              colimitMul F c hc := by
            rw [hmul, Category.comp_id, Category.id_comp]
        _ = ((μ[(F.obj j).X] ▷ (F.obj j).X) ≫ (ιj ⊗ₘ ιj)) ≫ colimitMul F c hc := by
            rw [← tensorHom_comp_tensorHom, tensorHom_id]
        _ = ((μ[(F.obj j).X] ▷ (F.obj j).X) ≫ μ[(F.obj j).X]) ≫ ιj := by
            rw [Category.assoc, hmul, ← Category.assoc]
    have h₂ : ((ιj ⊗ₘ ιj) ⊗ₘ ιj) ≫ (α_ c.pt c.pt c.pt).hom ≫
        (c.pt ◁ colimitMul F c hc) ≫ colimitMul F c hc =
        ((α_ (F.obj j).X (F.obj j).X (F.obj j).X).hom ≫
          ((F.obj j).X ◁ μ[(F.obj j).X]) ≫ μ[(F.obj j).X]) ≫ ιj := by
      have ha : ((ιj ⊗ₘ ιj) ⊗ₘ ιj) ≫ (α_ c.pt c.pt c.pt).hom =
          (α_ (F.obj j).X (F.obj j).X (F.obj j).X).hom ≫ (ιj ⊗ₘ (ιj ⊗ₘ ιj)) :=
        associator_naturality _ _ _
      calc
        ((ιj ⊗ₘ ιj) ⊗ₘ ιj) ≫ (α_ c.pt c.pt c.pt).hom ≫
            (c.pt ◁ colimitMul F c hc) ≫ colimitMul F c hc
          = (α_ (F.obj j).X (F.obj j).X (F.obj j).X).hom ≫
              ((ιj ⊗ₘ (ιj ⊗ₘ ιj)) ≫ (𝟙 c.pt ⊗ₘ colimitMul F c hc)) ≫
              colimitMul F c hc := by
            rw [← Category.assoc, ha, Category.assoc, id_tensorHom, Category.assoc]
        _ = (α_ (F.obj j).X (F.obj j).X (F.obj j).X).hom ≫
              ((ιj ≫ 𝟙 c.pt) ⊗ₘ ((ιj ⊗ₘ ιj) ≫ colimitMul F c hc)) ≫
              colimitMul F c hc := by
            rw [tensorHom_comp_tensorHom]
        _ = (α_ (F.obj j).X (F.obj j).X (F.obj j).X).hom ≫
              ((𝟙 (F.obj j).X ≫ ιj) ⊗ₘ (μ[(F.obj j).X] ≫ ιj)) ≫
              colimitMul F c hc := by
            rw [Category.comp_id, Category.id_comp, hmul]
        _ = (α_ (F.obj j).X (F.obj j).X (F.obj j).X).hom ≫
              (((F.obj j).X ◁ μ[(F.obj j).X]) ≫ (ιj ⊗ₘ ιj)) ≫ colimitMul F c hc := by
            rw [← tensorHom_comp_tensorHom, id_tensorHom]
        _ = ((α_ (F.obj j).X (F.obj j).X (F.obj j).X).hom ≫
              ((F.obj j).X ◁ μ[(F.obj j).X]) ≫ μ[(F.obj j).X]) ≫ ιj := by
            simp only [Category.assoc, hmul]
    exact h₁.trans (by rw [h₂, MonObj.mul_assoc])

theorem one_eq (j : J) :
    let _ := monObj F c hc
    η[(F.obj j).X] ≫ c.ι.app j = η[c.pt] :=
  one_comp_ι F c j

theorem tensor_ι_mul (j : J) :
    let _ := monObj F c hc
    ((c.ι.app j : (F.obj j).X ⟶ c.pt) ⊗ₘ (c.ι.app j : (F.obj j).X ⟶ c.pt)) ≫ μ[c.pt] =
      μ[(F.obj j).X] ≫ c.ι.app j :=
  tensor_ι_colimitMul F c hc j

/-- The lifted cocone in `Mon C` over an underlying colimiting cocone. -/
noncomputable def cocone : Cocone F :=
  let _ := monObj F c hc
  Cocone.mk { X := c.pt, mon := monObj F c hc }
    { app j := Mon.Hom.mk' (c.ι.app j) (one_eq F c hc j) (tensor_ι_mul F c hc j).symm
      naturality _ _ f := Mon.Hom.ext ((c.w f).trans (Category.comp_id _).symm) }

/-- Forgetting the monoid structure of the lifted cocone recovers the underlying cocone. -/
noncomputable def forgetCoconeIso : (Mon.forget C).mapCocone (cocone F c hc) ≅ c :=
  Cocone.ext (Iso.refl _) fun j ↦ by
    change ((cocone F c hc).ι.app j).hom ≫ 𝟙 c.pt = c.ι.app j
    exact Category.comp_id _

/-- The lifted cocone in `Mon C` is colimiting. -/
noncomputable def isColimit : IsColimit (cocone F c hc) :=
  isColimitOfForget F _ (IsColimit.ofIsoColimit hc (forgetCoconeIso F c hc).symm)

end Mon.ColimitConstruction

variable [∀ X : C, PreservesColimitsOfShape J (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape J (tensorRight X)]

/-- The forgetful functor `Mon.forget C` creates colimits of sifted shape `J` when tensoring on
either side preserves `J`-colimits. -/
noncomputable instance Mon.forgetCreatesColimitsOfShape :
    CreatesColimitsOfShape J (Mon.forget C) where
  CreatesColimit {F} :=
    { lifts c hc :=
        { liftedCocone := Mon.ColimitConstruction.cocone F c hc
          validLift := Mon.ColimitConstruction.forgetCoconeIso F c hc }
      reflects {c} hc := ⟨Mon.isColimitOfForget F c hc⟩ }

/-- `Mon C` has colimits of sifted shape `J` whenever `C` does and tensoring preserves them. -/
noncomputable instance Mon.hasColimitsOfShape [HasColimitsOfShape J C] :
    HasColimitsOfShape J (Mon C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (Mon.forget C)

end Mon

section CommMon

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C]
  {J : Type w} [Category.{w'} J]
  [∀ X : C, PreservesColimitsOfShape J (tensorLeft X)]

private lemma preservesColimitsOfShape_tensorRight (X : C) :
    PreservesColimitsOfShape J (tensorRight X) where
  preservesColimit {F} :=
    MonoidalCategory.Limits.preservesColimit_of_braided_and_preservesColimit_tensor_left F X

variable [IsSifted J]

/-- A cocone in `CommMon C` over a sifted diagram whose underlying cocone in `C` is colimiting is
itself colimiting. -/
noncomputable def CommMon.isColimitOfForget (F : J ⥤ CommMon C) (c : Cocone F)
    (hc : IsColimit ((CommMon.forget C).mapCocone c)) : IsColimit c :=
  have := preservesColimitsOfShape_tensorRight (C := C) (J := J)
  isColimitOfReflects (CommMon.forget₂Mon C)
    (Mon.isColimitOfForget (F ⋙ CommMon.forget₂Mon C) ((CommMon.forget₂Mon C).mapCocone c) hc)

namespace CommMon.ColimitConstruction

variable (F : J ⥤ CommMon C) (c : Cocone (F ⋙ CommMon.forget C)) (hc : IsColimit c)

private lemma isCommMonObj_colimit :
    let _ := preservesColimitsOfShape_tensorRight (C := C) (J := J)
    let _ := Mon.ColimitConstruction.monObj (F ⋙ CommMon.forget₂Mon C) c hc
    IsCommMonObj c.pt := by
  let _ := preservesColimitsOfShape_tensorRight (C := C) (J := J)
  let _ := Mon.ColimitConstruction.monObj (F ⋙ CommMon.forget₂Mon C) c hc
  refine ⟨(hc.tensor hc).hom_ext fun j ↦ ?_⟩
  let ιj : (F.obj j).X ⟶ c.pt := c.ι.app j
  change (ιj ⊗ₘ ιj) ≫ (β_ c.pt c.pt).hom ≫ μ[c.pt] = (ιj ⊗ₘ ιj) ≫ μ[c.pt]
  have hnat : (ιj ⊗ₘ ιj) ≫ (β_ c.pt c.pt).hom =
      (β_ (F.obj j).X (F.obj j).X).hom ≫ (ιj ⊗ₘ ιj) :=
    BraidedCategory.braiding_naturality _ _
  have hmul : (ιj ⊗ₘ ιj) ≫ μ[c.pt] = μ[(F.obj j).X] ≫ ιj :=
    Mon.ColimitConstruction.tensor_ι_mul (F ⋙ CommMon.forget₂Mon C) c hc j
  rw [← Category.assoc, hnat, Category.assoc, hmul, IsCommMonObj.mul_comm_assoc]

/-- The lifted cocone in `CommMon C` over an underlying colimiting cocone. -/
noncomputable def cocone : Cocone F :=
  let _ := preservesColimitsOfShape_tensorRight (C := C) (J := J)
  let mc := Mon.ColimitConstruction.cocone (F ⋙ CommMon.forget₂Mon C) c hc
  Cocone.mk
    { X := c.pt
      mon := Mon.ColimitConstruction.monObj (F ⋙ CommMon.forget₂Mon C) c hc
      comm := isCommMonObj_colimit F c hc }
    { app j := CommMon.homMk (mc.ι.app j)
      naturality _ _ f := CommMon.hom_ext _ _ ((c.w f).trans (Category.comp_id _).symm) }

/-- Forgetting the commutative monoid structure recovers the underlying cocone. -/
noncomputable def forgetCoconeIso : (CommMon.forget C).mapCocone (cocone F c hc) ≅ c :=
  Cocone.ext (Iso.refl _) fun j ↦ by
    change ((cocone F c hc).ι.app j).hom.hom ≫ 𝟙 c.pt = c.ι.app j
    exact Category.comp_id _

/-- The lifted cocone in `CommMon C` is colimiting. -/
noncomputable def isColimit : IsColimit (cocone F c hc) :=
  isColimitOfForget F _ (IsColimit.ofIsoColimit hc (forgetCoconeIso F c hc).symm)

end CommMon.ColimitConstruction

/-- The forgetful functor `CommMon.forget C` creates colimits of sifted shape `J` when `C` is
braided and left-tensoring preserves `J`-colimits. -/
noncomputable instance CommMon.forgetCreatesColimitsOfShape :
    CreatesColimitsOfShape J (CommMon.forget C) where
  CreatesColimit {F} :=
    { lifts c hc :=
        { liftedCocone := CommMon.ColimitConstruction.cocone F c hc
          validLift := CommMon.ColimitConstruction.forgetCoconeIso F c hc }
      reflects {c} hc := ⟨CommMon.isColimitOfForget F c hc⟩ }

/-- `CommMon C` has colimits of sifted shape `J` whenever `C` does and `tensorLeft` preserves
them. -/
noncomputable instance CommMon.hasColimitsOfShape [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CommMon C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (CommMon.forget C)

end CommMon

section Grp

open CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]
  {J : Type w} [Category.{w'} J] [IsSifted J]
  [∀ X : C, PreservesColimitsOfShape J (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape J (tensorRight X)]

/-- A cocone in `Grp C` over a sifted diagram whose underlying cocone in `C` is colimiting is
itself colimiting. -/
noncomputable def Grp.isColimitOfForget (F : J ⥤ Grp C) (c : Cocone F)
    (hc : IsColimit ((Grp.forget C).mapCocone c)) : IsColimit c :=
  isColimitOfReflects (Grp.forget₂Mon C)
    (Mon.isColimitOfForget (F ⋙ Grp.forget₂Mon C) ((Grp.forget₂Mon C).mapCocone c) hc)

/-- The underlying morphism of the descent from `Grp.isColimitOfForget` is the descent of the
underlying cocone. -/
theorem Grp.isColimitOfForget_desc_hom (F : J ⥤ Grp C) (c : Cocone F)
    (hc : IsColimit ((Grp.forget C).mapCocone c)) (s : Cocone F) :
    ((Grp.isColimitOfForget F c hc).desc s).hom.hom = hc.desc ((Grp.forget C).mapCocone s) :=
  hc.uniq ((Grp.forget C).mapCocone s) _ fun j ↦
    congrArg (fun k ↦ k.hom.hom) ((Grp.isColimitOfForget F c hc).fac s j)

namespace Grp.ColimitConstruction

variable (F : J ⥤ Grp C) (c : Cocone (F ⋙ Grp.forget C)) (hc : IsColimit c)

private noncomputable def invCocone : Cocone (F ⋙ Grp.forget C) :=
  Cocone.mk c.pt
    { app j := ι[(F.obj j).X] ≫ c.ι.app j
      naturality i j f := by
        let φ : (F.obj i).X ⟶ (F.obj j).X := (F.map f).hom.hom
        let ιi : (F.obj i).X ⟶ c.pt := c.ι.app i
        let ιj : (F.obj j).X ⟶ c.pt := c.ι.app j
        have hinv : φ ≫ ι[(F.obj j).X] = ι[(F.obj i).X] ≫ φ :=
          (GrpObj.inv_hom φ).symm
        have hw : φ ≫ ιj = ιi := c.w f
        change φ ≫ ι[(F.obj j).X] ≫ ιj = (ι[(F.obj i).X] ≫ ιi) ≫ 𝟙 c.pt
        rw [← Category.assoc, hinv, Category.assoc, hw, Category.comp_id] }

private noncomputable def colimitInv : c.pt ⟶ c.pt :=
  hc.desc (invCocone F c)

omit [IsSifted J] [∀ X : C, PreservesColimitsOfShape J (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape J (tensorRight X)] in
private theorem ι_colimitInv (j : J) :
    (c.ι.app j : (F.obj j).X ⟶ c.pt) ≫ colimitInv F c hc = ι[(F.obj j).X] ≫ c.ι.app j :=
  hc.fac (invCocone F c) j

/-- The group object structure induced on the underlying colimit of a sifted diagram in `Grp C`. -/
@[instance_reducible]
noncomputable def grpObj : GrpObj c.pt where
  toMonObj := Mon.ColimitConstruction.monObj (F ⋙ Grp.forget₂Mon C) c hc
  inv := colimitInv F c hc
  left_inv := by
    let _ := Mon.ColimitConstruction.monObj (F ⋙ Grp.forget₂Mon C) c hc
    refine hc.hom_ext fun j ↦ ?_
    let ιj : (F.obj j).X ⟶ c.pt := c.ι.app j
    have hmul : (ιj ⊗ₘ ιj) ≫ μ[c.pt] = μ[(F.obj j).X] ≫ ιj :=
      Mon.ColimitConstruction.tensor_ι_mul (F ⋙ Grp.forget₂Mon C) c hc j
    have hone : η[(F.obj j).X] ≫ ιj = η[c.pt] :=
      Mon.ColimitConstruction.one_eq (F ⋙ Grp.forget₂Mon C) c hc j
    have hinv : ιj ≫ colimitInv F c hc = ι[(F.obj j).X] ≫ ιj :=
      ι_colimitInv F c hc j
    change ιj ≫ lift (colimitInv F c hc) (𝟙 c.pt) ≫ μ[c.pt] =
      ιj ≫ toUnit c.pt ≫ η[c.pt]
    calc
      ιj ≫ lift (colimitInv F c hc) (𝟙 c.pt) ≫ μ[c.pt]
        = lift (ιj ≫ colimitInv F c hc) ιj ≫ μ[c.pt] := by
          rw [← Category.assoc, comp_lift, Category.comp_id]
      _ = lift (ι[(F.obj j).X] ≫ ιj) (𝟙 (F.obj j).X ≫ ιj) ≫ μ[c.pt] := by
          rw [hinv, Category.id_comp]
      _ = lift ι[(F.obj j).X] (𝟙 (F.obj j).X) ≫ (ιj ⊗ₘ ιj) ≫ μ[c.pt] := by
          rw [lift_map_assoc]
      _ = lift ι[(F.obj j).X] (𝟙 (F.obj j).X) ≫ μ[(F.obj j).X] ≫ ιj := by
          rw [hmul]
      _ = toUnit (F.obj j).X ≫ η[(F.obj j).X] ≫ ιj := by
          rw [GrpObj.left_inv_assoc]
      _ = toUnit (F.obj j).X ≫ η[c.pt] := by rw [hone]
      _ = ιj ≫ toUnit c.pt ≫ η[c.pt] := by
          rw [← Category.assoc, toUnit_unique (ιj ≫ toUnit c.pt) (toUnit (F.obj j).X)]
  right_inv := by
    let _ := Mon.ColimitConstruction.monObj (F ⋙ Grp.forget₂Mon C) c hc
    refine hc.hom_ext fun j ↦ ?_
    let ιj : (F.obj j).X ⟶ c.pt := c.ι.app j
    have hmul : (ιj ⊗ₘ ιj) ≫ μ[c.pt] = μ[(F.obj j).X] ≫ ιj :=
      Mon.ColimitConstruction.tensor_ι_mul (F ⋙ Grp.forget₂Mon C) c hc j
    have hone : η[(F.obj j).X] ≫ ιj = η[c.pt] :=
      Mon.ColimitConstruction.one_eq (F ⋙ Grp.forget₂Mon C) c hc j
    have hinv : ιj ≫ colimitInv F c hc = ι[(F.obj j).X] ≫ ιj :=
      ι_colimitInv F c hc j
    change ιj ≫ lift (𝟙 c.pt) (colimitInv F c hc) ≫ μ[c.pt] =
      ιj ≫ toUnit c.pt ≫ η[c.pt]
    calc
      ιj ≫ lift (𝟙 c.pt) (colimitInv F c hc) ≫ μ[c.pt]
        = lift ιj (ιj ≫ colimitInv F c hc) ≫ μ[c.pt] := by
          rw [← Category.assoc, comp_lift, Category.comp_id]
      _ = lift (𝟙 (F.obj j).X ≫ ιj) (ι[(F.obj j).X] ≫ ιj) ≫ μ[c.pt] := by
          rw [hinv, Category.id_comp]
      _ = lift (𝟙 (F.obj j).X) ι[(F.obj j).X] ≫ (ιj ⊗ₘ ιj) ≫ μ[c.pt] := by
          rw [lift_map_assoc]
      _ = lift (𝟙 (F.obj j).X) ι[(F.obj j).X] ≫ μ[(F.obj j).X] ≫ ιj := by
          rw [hmul]
      _ = toUnit (F.obj j).X ≫ η[(F.obj j).X] ≫ ιj := by
          rw [GrpObj.right_inv_assoc]
      _ = toUnit (F.obj j).X ≫ η[c.pt] := by rw [hone]
      _ = ιj ≫ toUnit c.pt ≫ η[c.pt] := by
          rw [← Category.assoc, toUnit_unique (ιj ≫ toUnit c.pt) (toUnit (F.obj j).X)]

/-- The lifted cocone in `Grp C` over an underlying colimiting cocone. -/
noncomputable def cocone : Cocone F :=
  let mc := Mon.ColimitConstruction.cocone (F ⋙ Grp.forget₂Mon C) c hc
  Cocone.mk { X := c.pt, grp := grpObj F c hc }
    { app j := Grp.homMk' (mc.ι.app j)
      naturality _ _ f := Grp.hom_ext _ _ ((c.w f).trans (Category.comp_id _).symm) }

/-- Forgetting the group structure of the lifted cocone recovers the underlying cocone. -/
noncomputable def forgetCoconeIso : (Grp.forget C).mapCocone (cocone F c hc) ≅ c :=
  Cocone.ext (Iso.refl _) fun j ↦ by
    change ((cocone F c hc).ι.app j).hom.hom ≫ 𝟙 c.pt = c.ι.app j
    exact Category.comp_id _

/-- The lifted cocone in `Grp C` is colimiting. -/
noncomputable def isColimit : IsColimit (cocone F c hc) :=
  isColimitOfForget F _ (IsColimit.ofIsoColimit hc (forgetCoconeIso F c hc).symm)

end Grp.ColimitConstruction

/-- The forgetful functor `Grp.forget C` creates colimits of sifted shape `J` in a Cartesian
monoidal category when tensoring on either side preserves `J`-colimits. -/
noncomputable instance Grp.forgetCreatesColimitsOfShape :
    CreatesColimitsOfShape J (Grp.forget C) where
  CreatesColimit {F} :=
    { lifts c hc :=
        { liftedCocone := Grp.ColimitConstruction.cocone F c hc
          validLift := Grp.ColimitConstruction.forgetCoconeIso F c hc }
      reflects {c} hc := ⟨Grp.isColimitOfForget F c hc⟩ }

/-- `Grp C` has colimits of sifted shape `J` whenever `C` does and tensoring preserves them. -/
noncomputable instance Grp.hasColimitsOfShape [HasColimitsOfShape J C] :
    HasColimitsOfShape J (Grp C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (Grp.forget C)

end Grp

section CommGrp

open CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C] [BraidedCategory.{v} C]
  {J : Type w} [Category.{w'} J] [IsSifted J]
  [∀ X : C, PreservesColimitsOfShape J (tensorLeft X)]

/-- A cocone in `CommGrp C` over a sifted diagram whose underlying cocone in `C` is colimiting is
itself colimiting. -/
noncomputable def CommGrp.isColimitOfForget (F : J ⥤ CommGrp C) (c : Cocone F)
    (hc : IsColimit ((CommGrp.forget C).mapCocone c)) : IsColimit c :=
  have := preservesColimitsOfShape_tensorRight (C := C) (J := J)
  isColimitOfReflects (CommGrp.forget₂Grp C)
    (Grp.isColimitOfForget (F ⋙ CommGrp.forget₂Grp C) ((CommGrp.forget₂Grp C).mapCocone c) hc)

namespace CommGrp.ColimitConstruction

variable (F : J ⥤ CommGrp C) (c : Cocone (F ⋙ CommGrp.forget C)) (hc : IsColimit c)

/-- The lifted cocone in `CommGrp C` over an underlying colimiting cocone. -/
noncomputable def cocone : Cocone F :=
  let _ := preservesColimitsOfShape_tensorRight (C := C) (J := J)
  let gc := Grp.ColimitConstruction.cocone (F ⋙ CommGrp.forget₂Grp C) c hc
  Cocone.mk
    { X := c.pt
      grp := Grp.ColimitConstruction.grpObj (F ⋙ CommGrp.forget₂Grp C) c hc
      comm :=
        CommMon.ColimitConstruction.isCommMonObj_colimit (F ⋙ CommGrp.forget₂CommMon C) c hc }
    { app j := InducedCategory.homMk (gc.ι.app j)
      naturality _ _ f := CommGrp.hom_ext _ _ ((c.w f).trans (Category.comp_id _).symm) }

/-- Forgetting the commutative group structure recovers the underlying cocone. -/
noncomputable def forgetCoconeIso : (CommGrp.forget C).mapCocone (cocone F c hc) ≅ c :=
  Cocone.ext (Iso.refl _) fun j ↦ by
    change ((cocone F c hc).ι.app j).hom.hom.hom ≫ 𝟙 c.pt = c.ι.app j
    exact Category.comp_id _

/-- The lifted cocone in `CommGrp C` is colimiting. -/
noncomputable def isColimit : IsColimit (cocone F c hc) :=
  isColimitOfForget F _ (IsColimit.ofIsoColimit hc (forgetCoconeIso F c hc).symm)

end CommGrp.ColimitConstruction

/-- The forgetful functor `CommGrp.forget C` creates colimits of sifted shape `J` when `C` is
Cartesian and braided and left-tensoring preserves `J`-colimits. -/
noncomputable instance CommGrp.forgetCreatesColimitsOfShape :
    CreatesColimitsOfShape J (CommGrp.forget C) where
  CreatesColimit {F} :=
    { lifts c hc :=
        { liftedCocone := CommGrp.ColimitConstruction.cocone F c hc
          validLift := CommGrp.ColimitConstruction.forgetCoconeIso F c hc }
      reflects {c} hc := ⟨CommGrp.isColimitOfForget F c hc⟩ }

/-- `CommGrp C` has colimits of sifted shape `J` whenever `C` does and `tensorLeft` preserves
them. -/
noncomputable instance CommGrp.hasColimitsOfShape [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CommGrp C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (CommGrp.forget C)

end CommGrp

end CategoryTheory
