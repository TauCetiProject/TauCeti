/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Scalar
public import TauCeti.CategoryTheory.Semisimple.Multiplicity

/-!
# Simple summands of the tensor unit and Peircian support

In a finite semisimple monoidal category `C` whose tensor product is additive
(`MonoidalPreadditive`), the tensor unit `𝟙_ C` need not be simple: `C` may be a *multitensor* or
*multifusion* category. By Eckmann–Hilton (`TauCeti.scalar_comm`), `End (𝟙_ C)` is commutative, so
`𝟙_ C` decomposes as a multiplicity-free finite biproduct of pairwise tensor-orthogonal simple
objects (`TauCeti.UnitSimpleClasses.tensorUnitBicone`,
`TauCeti.UnitSimpleClasses.tensorUnitBiconeIsBilimit`,
`TauCeti.UnitSimpleClasses.tensorUnitIsoBiproduct`).

`TauCeti.UnitSimpleClasses C` is the type of isomorphism classes of simple objects mapping
nontrivially into `𝟙_ C`. Every simple object `X` has a unique left support
`TauCeti.leftUnitClass X` and a unique right support `TauCeti.rightUnitClass X` in
`UnitSimpleClasses C` characterized by `(leftUnitClass X).repr ⊗ X ≅ X` and
`X ⊗ (rightUnitClass X).repr ≅ X`, explicitly realized by `TauCeti.leftUnitClassReprIso` and
`TauCeti.rightUnitClassReprIso` via the summand inclusions and projections with the unitors. Every
nonzero morphism `U ⟶ X ⊗ Y` between simple objects satisfies the composability and boundary
conditions `rightUnitClass X = leftUnitClass Y`, `leftUnitClass U = leftUnitClass X`, and
`rightUnitClass U = rightUnitClass Y`. Exact-pairing and rigid-duality results for these supports
are in `TauCeti/CategoryTheory/Semisimple/UnitSummands/Rigid.lean`.

## Main declarations

* `TauCeti.UnitSimpleClasses`: isomorphism classes of simple summands of `𝟙_ C`.
* `TauCeti.UnitSimpleClasses.isZero_tensorObj_of_ne`: distinct unit summands have zero tensor.
* `TauCeti.simpleMultiplicities_tensorUnit_le_one`: `𝟙_ C` is multiplicity-free.
* `TauCeti.UnitSimpleClasses.ι`, `π`, `tensorUnitBicone`, `tensorUnitBiconeIsBilimit`,
  `sum_π_comp_ι`, `tensorUnitIsoBiproduct`: biproduct decomposition of `𝟙_ C`.
* `TauCeti.leftUnitClass`, `rightUnitClass`, `leftUnitClassReprIso`, `rightUnitClassReprIso`:
  unique left and right unit summands supporting a simple object.
* `TauCeti.rightUnitClass_eq_leftUnitClass_of_hom_ne_zero`, `leftUnitClass_eq_of_hom_ne_zero`,
  `rightUnitClass_eq_of_hom_ne_zero`: endpoint compatibility along nonzero `U ⟶ X ⊗ Y`.
* `TauCeti.UnitSimpleClasses.equiv`: transport of unit summand classes along a monoidal equivalence.

## References

* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  Higher Structures **4** (2020), no. 2, 22–56 (arXiv:1808.00323), §§2.1, 3.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.3
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace TauCeti

section Retract

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- Any retract `(f, p)` of the tensor unit `𝟙_ C` is canonically tensor-idempotent. -/
def tensorSelfIsoOfRetract {U : C} (f : U ⟶ 𝟙_ C) (p : 𝟙_ C ⟶ U) (h : f ≫ p = 𝟙 U) :
    U ⊗ U ≅ U where
  hom := f ▷ U ≫ (λ_ U).hom
  inv := (λ_ U).inv ≫ p ▷ U
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight, h, id_whiskerRight]
  inv_hom_id := by
    have hu : (p ≫ f) ▷ 𝟙_ C = ((λ_ (𝟙_ C)).hom ≫ (p ≫ f)) ≫ (λ_ (𝟙_ C)).inv := by
      rw [Iso.eq_comp_inv]; simp [unitors_equal]
    have hid : (p ≫ f) ▷ U = 𝟙 (𝟙_ C ⊗ U) := calc
      (p ≫ f) ▷ U
          = (p ≫ f) ▷ U ≫ 𝟙_ C ◁ (f ≫ p) := by rw [h, whiskerLeft_id, Category.comp_id]
        _ = (𝟙_ C ◁ f ≫ (p ≫ f) ▷ 𝟙_ C) ≫ 𝟙_ C ◁ p := by
              rw [whiskerLeft_comp, ← Category.assoc, ← tensorHom_def, tensorHom_def']
        _ = ((λ_ U).hom ≫ (f ≫ p ≫ f) ≫ (λ_ (𝟙_ C)).inv) ≫ 𝟙_ C ◁ p := by
              simp only [hu, Category.assoc, leftUnitor_naturality_assoc]
        _ = 𝟙 (𝟙_ C ⊗ U) := by
              rw [← Category.assoc f p f, h, Category.id_comp]
              simp [reassoc_of% h]
    rw [Category.assoc, ← Category.assoc (p ▷ U), ← comp_whiskerRight, hid,
      Category.id_comp, Iso.inv_hom_id]

@[reassoc]
theorem tensorSelfIsoOfRetract_hom {U : C} (f : U ⟶ 𝟙_ C) (p : 𝟙_ C ⟶ U) (h : f ≫ p = 𝟙 U) :
    (tensorSelfIsoOfRetract f p h).hom = f ▷ U ≫ (λ_ U).hom := (rfl)

@[reassoc]
theorem tensorSelfIsoOfRetract_inv {U : C} (f : U ⟶ 𝟙_ C) (p : 𝟙_ C ⟶ U) (h : f ≫ p = 𝟙 U) :
    (tensorSelfIsoOfRetract f p h).inv = (λ_ U).inv ≫ p ▷ U := (rfl)

/-- Two retracts of the tensor unit `𝟙_ C` with zero cross-composite have zero tensor product. -/
theorem isZero_tensorObj_of_retract [HasZeroMorphisms C] {U V : C}
    (f₁ : U ⟶ 𝟙_ C) (p₁ : 𝟙_ C ⟶ U) (h₁ : f₁ ≫ p₁ = 𝟙 U)
    (f₂ : V ⟶ 𝟙_ C) (p₂ : 𝟙_ C ⟶ V) (h₂ : f₂ ≫ p₂ = 𝟙 V) (hzero : f₁ ≫ p₂ = 0) :
    IsZero (U ⊗ V) := by
  have he : p₁ ≫ f₁ ≫ p₂ ≫ f₂ = 0 := by simp [reassoc_of% hzero]
  have htensor : (p₁ ≫ f₁) ⊗ₘ (p₂ ≫ f₂) = 0 := by
    rw [← cancel_mono (λ_ (𝟙_ C)).hom, zero_comp, tensorHom_def, Category.assoc,
      leftUnitor_naturality, unitors_equal, rightUnitor_naturality_assoc, ← unitors_equal,
      Category.assoc, he, comp_zero]
  have hid₁ : 𝟙 U = f₁ ≫ (p₁ ≫ f₁) ≫ p₁ := by simp [← Category.assoc, h₁]
  have hid₂ : 𝟙 V = f₂ ≫ (p₂ ≫ f₂) ≫ p₂ := by simp [← Category.assoc, h₂]
  rw [IsZero.iff_id_eq_zero, ← id_tensorHom_id, hid₁, hid₂, ← tensorHom_comp_tensorHom,
    ← tensorHom_comp_tensorHom, htensor]
  simp

end Retract

section Basic

variable (C : Type u₁) [Category.{v₁} C] [HasZeroMorphisms C] [MonoidalCategory C]

/-- The isomorphism classes of simple summands of the tensor unit `𝟙_ C`, realized as the simple
classes whose representative admits a nonzero morphism to `𝟙_ C`. -/
abbrev UnitSimpleClasses :=
  {I : SimpleClasses C // ∃ f : I.repr ⟶ 𝟙_ C, f ≠ 0}

namespace UnitSimpleClasses

variable {C}

/-- The chosen representative in `C` of a simple unit summand class. -/
abbrev repr (I : UnitSimpleClasses C) : C := I.val.repr

instance (I : UnitSimpleClasses C) : Simple I.repr := I.val.property

/-- Every unit summand representative admits a nonzero morphism to `𝟙_ C`. -/
theorem exists_hom_to_unit_ne_zero (I : UnitSimpleClasses C) :
    ∃ f : I.repr ⟶ 𝟙_ C, f ≠ 0 := I.property

@[simp]
theorem eq_iff_nonempty_iso (I J : UnitSimpleClasses C) :
    I = J ↔ Nonempty (I.repr ≅ J.repr) := by
  rw [Subtype.ext_iff, SimpleClasses.eq_iff_nonempty_iso]

/-- Construct a `UnitSimpleClasses C` element from a nonzero morphism out of a simple object into
`𝟙_ C`. -/
def mkOfHomNeZero {X : C} [Simple X] {f : X ⟶ 𝟙_ C} (hf : f ≠ 0) : UnitSimpleClasses C :=
  ⟨SimpleClasses.classOf X, ⟨(SimpleClasses.classOfReprIso X).hom ≫ f, fun h ↦
    hf (by simpa using (SimpleClasses.classOfReprIso X).inv ≫= h)⟩⟩

@[simp]
theorem val_mkOfHomNeZero {X : C} [Simple X] {f : X ⟶ 𝟙_ C} (hf : f ≠ 0) :
    (mkOfHomNeZero hf).val = SimpleClasses.classOf X := (rfl)

/-- When `𝟙_ C` is simple, its isomorphism class as a unit summand. -/
def unit [Simple (𝟙_ C)] : UnitSimpleClasses C :=
  mkOfHomNeZero (CategoryTheory.id_ne_zero (𝟙_ C))

@[simp]
theorem val_unit [Simple (𝟙_ C)] : (unit (C := C)).val = SimpleClasses.classOf (𝟙_ C) := (rfl)

section Equivalence

variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [MonoidalCategory D]

private theorem map_unit_hom_ne_zero (e : C ≌ D) [e.functor.Monoidal]
    (I : UnitSimpleClasses C) : ∃ g : (SimpleClasses.equiv e I.val).repr ⟶ 𝟙_ D, g ≠ 0 := by
  obtain ⟨f, hf⟩ := I.property
  have : e.functor.PreservesZeroMorphisms := e.functor.preservesZeroMorphisms_of_isLeftAdjoint
  let d := SimpleClasses.equivApplyReprIso e I.val
  let u := Functor.Monoidal.εIso e.functor
  refine ⟨d.hom ≫ e.functor.map f ≫ u.inv, fun h ↦ hf <| e.functor.map_injective ?_⟩
  rw [e.functor.map_zero]; simpa using d.inv ≫= h =≫ u.hom

/-- A monoidal equivalence induces a bijection between the simple summand classes of the tensor
units. -/
def equiv (e : C ≌ D) [e.functor.Monoidal] : UnitSimpleClasses C ≃ UnitSimpleClasses D where
  toFun I := ⟨SimpleClasses.equiv e I.val, map_unit_hom_ne_zero e I⟩
  invFun J :=
    letI := e.inverseMonoidal
    ⟨SimpleClasses.equiv e.symm J.val, map_unit_hom_ne_zero e.symm J⟩
  left_inv I := Subtype.ext <| (SimpleClasses.eq_iff_nonempty_iso _ _).2
    ⟨SimpleClasses.equivApplyReprIso e.symm _ ≪≫
      e.inverse.mapIso (SimpleClasses.equivApplyReprIso e I.val) ≪≫ (e.unitIso.app I.repr).symm⟩
  right_inv J := Subtype.ext <| (SimpleClasses.eq_iff_nonempty_iso _ _).2
    ⟨SimpleClasses.equivApplyReprIso e _ ≪≫
      e.functor.mapIso (SimpleClasses.equivApplyReprIso e.symm J.val) ≪≫ e.counitIso.app J.repr⟩

@[simp]
theorem val_equiv_apply (e : C ≌ D) [e.functor.Monoidal] (I : UnitSimpleClasses C) :
    (equiv e I).val = SimpleClasses.equiv e I.val := (rfl)

@[simp]
theorem equiv_symm (e : C ≌ D) [e.functor.Monoidal] :
    (equiv e).symm = @equiv D _ _ _ C _ _ _ e.symm e.inverseMonoidal := (rfl)

@[simp]
theorem equiv_refl (I : UnitSimpleClasses C) :
    equiv (CategoryTheory.Equivalence.refl (C := C)) I = I :=
  Subtype.ext <| (SimpleClasses.eq_iff_nonempty_iso _ _).2
    ⟨SimpleClasses.equivApplyReprIso CategoryTheory.Equivalence.refl I.val⟩

@[simp]
theorem equiv_trans {E : Type u₃} [Category.{v₃} E] [HasZeroMorphisms E] [MonoidalCategory E]
    (e₁ : C ≌ D) (e₂ : D ≌ E) [e₁.functor.Monoidal] [e₂.functor.Monoidal]
    (I : UnitSimpleClasses C) :
    equiv (e₁.trans e₂) I = equiv e₂ (equiv e₁ I) :=
  Subtype.ext <| (SimpleClasses.eq_iff_nonempty_iso _ _).2
    ⟨SimpleClasses.equivApplyReprIso (e₁.trans e₂) I.val ≪≫
      e₂.functor.mapIso (SimpleClasses.equivApplyReprIso e₁ I.val).symm ≪≫
      (SimpleClasses.equivApplyReprIso e₂ (equiv e₁ I).val).symm⟩

end Equivalence

end UnitSimpleClasses

end Basic

section SimpleUnit

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasKernels C]
  [MonoidalCategory C] [Simple (𝟙_ C)]

instance UnitSimpleClasses.instUnique : Unique (UnitSimpleClasses C) where
  default := UnitSimpleClasses.unit
  uniq I := Subtype.ext <| by
    rw [val_unit, ← SimpleClasses.classOf_repr I.val, SimpleClasses.classOf_eq_iff_exists_ne_zero]
    exact I.property

end SimpleUnit

section Semisimple

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [MonoidalCategory C]
  [IsFiniteSemisimpleCategory C]

attribute [local instance] Abelian.hasFiniteBiproducts

instance : Finite (UnitSimpleClasses C) := by
  refine Finite.of_injective
    (fun I : UnitSimpleClasses C ↦
      (⟨I.val, Finsupp.mem_support_iff.2 <| by
        simpa using (simpleMultiplicities_apply_classOf_ne_zero_iff (𝟙_ C) I.repr).2 I.property⟩ :
        (simpleMultiplicities (𝟙_ C)).support))
    fun I J h ↦ Subtype.ext (congrArg (fun x : (simpleMultiplicities (𝟙_ C)).support ↦ x.val) h)

/-- The tensor unit has a simple summand if and only if it is not a zero object. -/
theorem UnitSimpleClasses.nonempty_iff :
    Nonempty (UnitSimpleClasses C) ↔ ¬ IsZero (𝟙_ C) := by
  refine ⟨fun ⟨I⟩ h0 ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨f, hf⟩ := I.property
    exact hf (h0.eq_of_tgt _ _)
  · obtain ⟨S, _, f, hf⟩ := exists_simple_hom_ne_zero h
    exact ⟨UnitSimpleClasses.mkOfHomNeZero hf⟩

/-- In a finite semisimple monoidal category, the tensor unit is multiplicity-free: every simple
isomorphism class occurs at most once in `𝟙_ C`, since `End (𝟙_ C)` is commutative by
Eckmann–Hilton. -/
theorem simpleMultiplicities_tensorUnit_le_one (S : SimpleClasses C) :
    simpleMultiplicities (𝟙_ C) S ≤ 1 :=
  simpleMultiplicities_le_one_of_comm (𝟙_ C) scalar_comm S

@[simp]
theorem UnitSimpleClasses.simpleMultiplicities_tensorUnit (I : UnitSimpleClasses C) :
    simpleMultiplicities (𝟙_ C) I.val = 1 := by
  have hne : simpleMultiplicities (𝟙_ C) I.val ≠ 0 := by
    simpa using (simpleMultiplicities_apply_classOf_ne_zero_iff (𝟙_ C) I.repr).2 I.property
  have hle := simpleMultiplicities_tensorUnit_le_one I.val
  omega

section Biproduct

private structure TensorUnitDecomp (C : Type u₁) [Category.{v₁} C] [Abelian C] [MonoidalCategory C]
    [IsFiniteSemisimpleCategory C] where
  ι : Type
  [fintype : Fintype ι]
  summands : ι → C
  [simple : ∀ i, Simple (summands i)]
  [hasBiproduct : HasBiproduct summands]
  iso : 𝟙_ C ≅ ⨁ summands
  equiv : ι ≃ UnitSimpleClasses C
  summandIso : ∀ i, summands i ≅ (equiv i).repr

private def chosenTensorUnitDecomp (C : Type u₁) [Category.{v₁} C] [Abelian C]
    [MonoidalCategory C] [IsFiniteSemisimpleCategory C] : TensorUnitDecomp C := by
  classical
  let h := IsFiniteSemisimpleCategory.exists_biproduct_simples (𝟙_ C)
  let κ := h.choose; let hκ := h.choose_spec.choose; let a := h.choose_spec.choose_spec.choose
  let ha := h.choose_spec.choose_spec.choose_spec.choose
  let hba := h.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let e := h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some
  let f : κ → UnitSimpleClasses C :=
    fun i ↦ UnitSimpleClasses.mkOfHomNeZero (biproduct_ι_comp_inv_ne_zero e i)
  have hf_inj : Function.Injective f := fun i j hij ↦ by
    have hcard : Nat.card {k // SimpleClasses.classOf (a k) = SimpleClasses.classOf (a i)} ≤ 1 := by
      rw [← simpleMultiplicities_apply_eq_card a e]; exact simpleMultiplicities_tensorUnit_le_one _
    have hsub : Subsingleton {k // SimpleClasses.classOf (a k) = SimpleClasses.classOf (a i)} :=
      (Fintype.card_le_one_iff_subsingleton).1 (by rwa [← Nat.card_eq_fintype_card])
    exact congrArg Subtype.val
      (@Subsingleton.elim _ hsub ⟨i, rfl⟩ ⟨j, (congrArg Subtype.val hij).symm⟩)
  have hf_surj : Function.Surjective f := fun I ↦ by
    have hcard : Nat.card {k // SimpleClasses.classOf (a k) = I.val} = 1 := by
      rw [← simpleMultiplicities_apply_eq_card a e]
      exact UnitSimpleClasses.simpleMultiplicities_tensorUnit I
    have hne : Nonempty {k // SimpleClasses.classOf (a k) = I.val} := by
      rw [← Fintype.card_pos_iff, ← Nat.card_eq_fintype_card, hcard]; omega
    exact ⟨hne.some.val, Subtype.ext hne.some.property⟩
  exact
    { ι := κ, fintype := hκ, summands := a, simple := ha, hasBiproduct := hba, iso := e
      equiv := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
      summandIso := fun i ↦ (SimpleClasses.classOfReprIso (a i)).symm }

namespace UnitSimpleClasses

attribute [local instance] TensorUnitDecomp.fintype TensorUnitDecomp.simple
  TensorUnitDecomp.hasBiproduct

/-- Canonical inclusion of a simple summand `I.repr` into the tensor unit `𝟙_ C`. -/
def ι (I : UnitSimpleClasses C) : I.repr ⟶ 𝟙_ C :=
  let d := chosenTensorUnitDecomp C
  let i := d.equiv.symm I
  eqToHom (congrArg (fun J : UnitSimpleClasses C ↦ J.repr) (d.equiv.apply_symm_apply I).symm) ≫
    (d.summandIso i).inv ≫ biproduct.ι d.summands i ≫ d.iso.inv

/-- Canonical projection from the tensor unit `𝟙_ C` onto a simple summand `I.repr`. -/
def π (I : UnitSimpleClasses C) : 𝟙_ C ⟶ I.repr :=
  let d := chosenTensorUnitDecomp C
  let i := d.equiv.symm I
  d.iso.hom ≫ biproduct.π d.summands i ≫ (d.summandIso i).hom ≫
    eqToHom (congrArg (fun J : UnitSimpleClasses C ↦ J.repr) (d.equiv.apply_symm_apply I))

@[reassoc (attr := simp)]
theorem ι_comp_π_self (I : UnitSimpleClasses C) : ι I ≫ π I = 𝟙 I.repr := by
  classical
  dsimp only [ι, π]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_assoc, ↓reduceDIte,
    eqToHom_refl, Category.id_comp, eqToHom_trans]

@[reassoc (attr := simp)]
theorem ι_comp_π_ne {I J : UnitSimpleClasses C} (h : I ≠ J) : ι I ≫ π J = 0 := by
  dsimp only [ι, π]
  have hne := (chosenTensorUnitDecomp C).equiv.symm.injective.ne h
  simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_ne_assoc _ hne, zero_comp,
    comp_zero]

theorem ι_ne_zero (I : UnitSimpleClasses C) : ι I ≠ 0 := fun h ↦
  CategoryTheory.id_ne_zero I.repr (by rw [← ι_comp_π_self I, h, zero_comp])

theorem π_ne_zero (I : UnitSimpleClasses C) : π I ≠ 0 := fun h ↦
  CategoryTheory.id_ne_zero I.repr (by rw [← ι_comp_π_self I, h, comp_zero])

/-- Biproduct decomposition of the tensor unit `𝟙_ C` indexed by `UnitSimpleClasses C`. -/
def tensorUnitBicone : Bicone (fun I : UnitSimpleClasses C ↦ I.repr) where
  pt := 𝟙_ C
  π := π
  ι := ι
  ι_π I J := by
    by_cases h : I = J
    · subst h; simp
    · simp [h, ι_comp_π_ne h]

/-- The point of `tensorUnitBicone` is the tensor unit `𝟙_ C`. -/
@[simp]
theorem tensorUnitBicone_pt : (tensorUnitBicone (C := C)).pt = 𝟙_ C := (rfl)

/-- The projection leg of `tensorUnitBicone` at `I` is `π I` up to the point identification. -/
@[simp]
theorem tensorUnitBicone_π (I : UnitSimpleClasses C) :
    (tensorUnitBicone (C := C)).π I = eqToHom (tensorUnitBicone_pt (C := C)) ≫ π I :=
  (Category.id_comp _).symm

/-- The inclusion leg of `tensorUnitBicone` at `I` is `ι I` up to the point identification. -/
@[simp]
theorem tensorUnitBicone_ι (I : UnitSimpleClasses C) :
    (tensorUnitBicone (C := C)).ι I = ι I ≫ eqToHom (tensorUnitBicone_pt (C := C)).symm :=
  (Category.comp_id _).symm

private theorem π_equiv (i : (chosenTensorUnitDecomp C).ι) :
    π ((chosenTensorUnitDecomp C).equiv i) =
      (chosenTensorUnitDecomp C).iso.hom ≫ biproduct.π _ i ≫
        ((chosenTensorUnitDecomp C).summandIso i).hom := by
  dsimp only [π]
  have h : ∀ {j} (_ : j = i) (hk : (chosenTensorUnitDecomp C).equiv j = _),
      (chosenTensorUnitDecomp C).iso.hom ≫ biproduct.π _ j ≫
      ((chosenTensorUnitDecomp C).summandIso j).hom ≫
      eqToHom (congrArg (fun K : UnitSimpleClasses C ↦ K.repr) hk) =
      (chosenTensorUnitDecomp C).iso.hom ≫ biproduct.π _ i ≫
      ((chosenTensorUnitDecomp C).summandIso i).hom := by rintro _ rfl _; simp
  exact h ((chosenTensorUnitDecomp C).equiv.symm_apply_apply i)
    ((chosenTensorUnitDecomp C).equiv.apply_symm_apply _)

private theorem ι_equiv (i : (chosenTensorUnitDecomp C).ι) :
    ι ((chosenTensorUnitDecomp C).equiv i) =
      ((chosenTensorUnitDecomp C).summandIso i).inv ≫ biproduct.ι _ i ≫
        (chosenTensorUnitDecomp C).iso.inv := by
  dsimp only [ι]
  have h : ∀ {j} (_ : j = i) (hk : _ = (chosenTensorUnitDecomp C).equiv j),
      eqToHom (congrArg (fun K : UnitSimpleClasses C ↦ K.repr) hk) ≫
      ((chosenTensorUnitDecomp C).summandIso j).inv ≫ biproduct.ι _ j ≫
      (chosenTensorUnitDecomp C).iso.inv = ((chosenTensorUnitDecomp C).summandIso i).inv ≫
      biproduct.ι _ i ≫ (chosenTensorUnitDecomp C).iso.inv := by rintro _ rfl _; simp
  exact h ((chosenTensorUnitDecomp C).equiv.symm_apply_apply i)
    ((chosenTensorUnitDecomp C).equiv.apply_symm_apply _).symm

/-- `tensorUnitBicone` is a bilimit, realizing `𝟙_ C` as the biproduct of its simple summand
classes `UnitSimpleClasses C`. -/
def tensorUnitBiconeIsBilimit : (tensorUnitBicone (C := C)).IsBilimit :=
  let d := chosenTensorUnitDecomp C
  { isLimit := Fan.IsLimit.mk _
      (fun s ↦ (biproduct.lift fun i ↦ s.proj (d.equiv i) ≫ (d.summandIso i).inv) ≫ d.iso.inv)
      (fun s I ↦ by
        dsimp only [d, Fan.proj, Bicone.toCone_pt, Bicone.toCone_π_app, tensorUnitBicone, π]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.lift_π_assoc]
        have hproj : ∀ {J K : UnitSimpleClasses C} (h : J = K),
            s.π.app ⟨J⟩ ≫ eqToHom (congrArg (fun L : UnitSimpleClasses C ↦ L.repr) h) =
              s.π.app ⟨K⟩ := by rintro _ _ rfl; simp
        exact hproj (d.equiv.apply_symm_apply I))
      (fun s m hm ↦ by
        dsimp only [tensorUnitBicone] at m hm ⊢
        rw [← cancel_mono d.iso.hom]; apply biproduct.hom_ext; intro i
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, biproduct.lift_π]
        have hm' := hm (d.equiv i)
        dsimp only [d, Fan.proj, Bicone.toCone_π_app, tensorUnitBicone] at hm' ⊢
        rw [π_equiv] at hm'
        rw [← Category.assoc, ← cancel_mono ((chosenTensorUnitDecomp C).summandIso i).hom]
        simpa [Category.assoc] using hm')
    isColimit := Cofan.IsColimit.mk _
      (fun s ↦ d.iso.hom ≫ biproduct.desc fun i ↦ (d.summandIso i).hom ≫ s.inj (d.equiv i))
      (fun s I ↦ by
        dsimp only [d, Cofan.inj, Bicone.toCocone_pt, Bicone.toCocone_ι_app, tensorUnitBicone, ι]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_desc]
        have hinj : ∀ {J K : UnitSimpleClasses C} (h : J = K),
            eqToHom (congrArg (fun L : UnitSimpleClasses C ↦ L.repr) h) ≫ s.ι.app ⟨K⟩ =
              s.ι.app ⟨J⟩ := by rintro _ _ rfl; simp
        exact hinj (d.equiv.apply_symm_apply I).symm)
      (fun s m hm ↦ by
        dsimp only [tensorUnitBicone] at m hm ⊢
        rw [← cancel_epi d.iso.inv]; apply biproduct.hom_ext'; intro i
        simp only [Iso.inv_hom_id_assoc, biproduct.ι_desc]
        have hm' := hm (d.equiv i)
        dsimp only [d, Cofan.inj, Bicone.toCocone_ι_app, tensorUnitBicone] at hm' ⊢
        rw [ι_equiv] at hm'
        rw [← cancel_epi ((chosenTensorUnitDecomp C).summandIso i).inv]
        simpa [Category.assoc] using hm') }

/-- Morphisms into `𝟙_ C` are determined by postcomposition with the canonical projections
`π I`. -/
theorem hom_ext {X : C} {f g : X ⟶ 𝟙_ C}
    (h : ∀ I : UnitSimpleClasses C, f ≫ π I = g ≫ π I) : f = g :=
  (tensorUnitBiconeIsBilimit (C := C)).isLimit.hom_ext fun ⟨I⟩ ↦ h I

/-- Morphisms out of `𝟙_ C` are determined by precomposition with the canonical inclusions
`ι I`. -/
theorem hom_ext' {X : C} {f g : 𝟙_ C ⟶ X}
    (h : ∀ I : UnitSimpleClasses C, ι I ≫ f = ι I ≫ g) : f = g :=
  (tensorUnitBiconeIsBilimit (C := C)).isColimit.hom_ext fun ⟨I⟩ ↦ h I

/-- The family of chosen representatives of `UnitSimpleClasses C` admits a biproduct. -/
theorem hasBiproduct : HasBiproduct (fun I : UnitSimpleClasses C ↦ I.repr) :=
  HasBiproduct.mk ⟨tensorUnitBicone (C := C), tensorUnitBiconeIsBilimit (C := C)⟩

/-- Resolution of the identity of `𝟙_ C` as the sum of the unit-summand projections followed by
the inclusions. -/
theorem sum_π_comp_ι [Fintype (UnitSimpleClasses C)] :
    ∑ I : UnitSimpleClasses C, π I ≫ ι I = 𝟙 (𝟙_ C) := by
  let d := chosenTensorUnitDecomp C
  rw [← Fintype.sum_equiv d.equiv (fun i ↦ π (d.equiv i) ≫ ι (d.equiv i))
    (fun I ↦ π I ≫ ι I) (fun _ ↦ rfl)]
  have hterm : ∀ i : d.ι, π (d.equiv i) ≫ ι (d.equiv i) =
      d.iso.hom ≫ biproduct.π d.summands i ≫ biproduct.ι d.summands i ≫ d.iso.inv := by
    intro i; dsimp only [d]; rw [π_equiv, ι_equiv]; simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp_rw [hterm, ← Category.assoc, ← Preadditive.sum_comp, Category.assoc, ← Preadditive.comp_sum,
    biproduct.total]
  simp

/-- Canonical isomorphism between `𝟙_ C` and the biproduct of its simple summand classes
`UnitSimpleClasses C`. -/
def tensorUnitIsoBiproduct [HasBiproduct (fun I : UnitSimpleClasses C ↦ I.repr)] :
    𝟙_ C ≅ ⨁ fun I : UnitSimpleClasses C ↦ I.repr :=
  (tensorUnitBiconeIsBilimit (C := C)).isLimit.conePointUniqueUpToIso (biproduct.isLimit _)

@[reassoc (attr := simp)]
theorem tensorUnitIsoBiproduct_hom_π [HasBiproduct (fun I : UnitSimpleClasses C ↦ I.repr)]
    (I : UnitSimpleClasses C) : (tensorUnitIsoBiproduct (C := C)).hom ≫ biproduct.π _ I = π I :=
  (biproduct.isLimit _).conePointUniqueUpToIso_inv_comp
    (tensorUnitBiconeIsBilimit (C := C)).isLimit ⟨I⟩

@[reassoc (attr := simp)]
theorem ι_tensorUnitIsoBiproduct_inv [HasBiproduct (fun I : UnitSimpleClasses C ↦ I.repr)]
    (I : UnitSimpleClasses C) : biproduct.ι _ I ≫ (tensorUnitIsoBiproduct (C := C)).inv = ι I := by
  classical
  rw [Iso.comp_inv_eq]; apply (biproduct.isLimit _).hom_ext; rintro ⟨J⟩
  simp only [Category.assoc, tensorUnitIsoBiproduct_hom_π, biproduct.ι_π, Bicone.toCone_π_app]
  by_cases h : I = J
  · subst h; simp
  · simp [h, ι_comp_π_ne h]

@[reassoc (attr := simp)]
theorem tensorUnitIsoBiproduct_inv_π [HasBiproduct (fun I : UnitSimpleClasses C ↦ I.repr)]
    (I : UnitSimpleClasses C) : (tensorUnitIsoBiproduct (C := C)).inv ≫ π I = biproduct.π _ I := by
  rw [Iso.inv_comp_eq, tensorUnitIsoBiproduct_hom_π]

@[reassoc (attr := simp)]
theorem ι_tensorUnitIsoBiproduct_hom [HasBiproduct (fun I : UnitSimpleClasses C ↦ I.repr)]
    (I : UnitSimpleClasses C) : ι I ≫ (tensorUnitIsoBiproduct (C := C)).hom = biproduct.ι _ I := by
  rw [← ι_tensorUnitIsoBiproduct_inv (C := C) I, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every simple unit summand is tensor-idempotent: `I.repr ⊗ I.repr ≅ I.repr`. -/
def tensorSelfIso (I : UnitSimpleClasses C) : I.repr ⊗ I.repr ≅ I.repr :=
  tensorSelfIsoOfRetract (ι I) (π I) (ι_comp_π_self I)

@[reassoc]
theorem tensorSelfIso_hom (I : UnitSimpleClasses C) :
    (tensorSelfIso I).hom = ι I ▷ I.repr ≫ (λ_ I.repr).hom := (rfl)

@[reassoc]
theorem tensorSelfIso_inv (I : UnitSimpleClasses C) :
    (tensorSelfIso I).inv = (λ_ I.repr).inv ≫ π I ▷ I.repr := (rfl)

end UnitSimpleClasses

end Biproduct

/-- Distinct simple summands of `𝟙_ C` have zero tensor product. -/
theorem UnitSimpleClasses.isZero_tensorObj_of_ne {I J : UnitSimpleClasses C} (h : I ≠ J) :
    IsZero (I.repr ⊗ J.repr) :=
  isZero_tensorObj_of_retract (ι I) (π I) (ι_comp_π_self I) (ι J) (π J) (ι_comp_π_self J)
    (ι_comp_π_ne h)

/-- Every nonzero morphism out of `𝟙_ C` remains nonzero after precomposing with some simple
summand of `𝟙_ C`. -/
theorem exists_unitSimpleClasses_comp_ne_zero {Z : C} {h : 𝟙_ C ⟶ Z} (hh : h ≠ 0) :
    ∃ (I : UnitSimpleClasses C) (f : I.repr ⟶ 𝟙_ C), f ≠ 0 ∧ f ≫ h ≠ 0 := by
  have ⟨S, hS, s, hs⟩ : ∃ (S : C) (_ : Simple S) (s : S ⟶ 𝟙_ C), s ≫ h ≠ 0 := by
    by_contra! h0
    exact hh ((𝟭 C).hom_ext_of_simple fun S _ s ↦ by simpa using h0 S inferInstance s)
  let _ := hS; let d := SimpleClasses.classOfReprIso S
  have h2 : (d.hom ≫ s) ≫ h ≠ 0 := fun hc ↦ hs <| by
    rw [← d.inv_hom_id_assoc (s ≫ h), ← Category.assoc d.hom s h, hc, comp_zero]
  have h1 : d.hom ≫ s ≠ 0 := fun hc ↦ h2 (by rw [hc, zero_comp])
  exact ⟨⟨SimpleClasses.classOf S, ⟨d.hom ≫ s, h1⟩⟩, d.hom ≫ s, h1, h2⟩

private theorem exists_unitSimpleClasses_iso_of_functor (F : C ⥤ C)
    (dist : ∀ {ι : Type} [Fintype ι] (a : ι → C), F.obj (⨁ a) ≅ ⨁ fun i ↦ F.obj (a i))
    {X : C} [Simple X] (u : X ≅ F.obj (𝟙_ C)) :
    ∃ I : UnitSimpleClasses C, Nonempty (F.obj I.repr ≅ X) := by
  obtain ⟨ι, hι, a, ha, hba, ⟨e⟩⟩ :=
    IsFiniteSemisimpleCategory.exists_biproduct_simples (𝟙_ C)
  let _ := hι; let _ := ha; let _ := hba
  let B : ι → C := fun i ↦ F.obj (a i)
  let d : X ≅ ⨁ B := u ≪≫ F.mapIso e ≪≫ dist a
  obtain ⟨i, hi⟩ : ∃ i, ¬ IsZero (B i) := by
    by_contra! h
    refine Simple.not_isZero X (IsZero.of_iso ?_ d)
    exact (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun i ↦ (h i).eq_of_tgt _ _)
  let m : B i ⟶ X := biproduct.ι B i ≫ d.inv
  have hm : m ≠ 0 := fun hm0 ↦ hi <| (IsZero.iff_id_eq_zero _).2 <| by
    simpa [m, Category.assoc] using hm0 =≫ (d.hom ≫ biproduct.π B i)
  have : IsIso m := isIso_of_mono_of_ne_zero hm
  exact ⟨UnitSimpleClasses.mkOfHomNeZero (biproduct_ι_comp_inv_ne_zero e i),
    ⟨F.mapIso (SimpleClasses.classOfReprIso (a i)) ≪≫ asIso m⟩⟩

variable [MonoidalPreadditive C]

private theorem exists_unitSimpleClasses_iso_left (X : C) [Simple X] :
    ∃ I : UnitSimpleClasses C, Nonempty (I.repr ⊗ X ≅ X) :=
  exists_unitSimpleClasses_iso_of_functor (tensorRight X) (fun a ↦ rightDistributor a X) (λ_ X).symm

private theorem exists_unitSimpleClasses_iso_right (X : C) [Simple X] :
    ∃ I : UnitSimpleClasses C, Nonempty (X ⊗ I.repr ≅ X) :=
  exists_unitSimpleClasses_iso_of_functor (tensorLeft X) (fun a ↦ leftDistributor X a) (ρ_ X).symm

/-- The unique simple summand class `I` of `𝟙_ C` such that `I.repr ⊗ X ≅ X`. -/
def leftUnitClass (X : C) [Simple X] : UnitSimpleClasses C :=
  (exists_unitSimpleClasses_iso_left X).choose

/-- The unique simple summand class `I` of `𝟙_ C` such that `X ⊗ I.repr ≅ X`. -/
def rightUnitClass (X : C) [Simple X] : UnitSimpleClasses C :=
  (exists_unitSimpleClasses_iso_right X).choose

/-- Tensoring a simple object `X` on the left by any unit summand other than `leftUnitClass X`
yields a zero object. -/
theorem isZero_unitRepr_tensorObj_of_ne {X : C} [Simple X] {I : UnitSimpleClasses C}
    (h : I ≠ leftUnitClass X) : IsZero (I.repr ⊗ X) :=
  let e : (leftUnitClass X).repr ⊗ X ≅ X := (exists_unitSimpleClasses_iso_left X).choose_spec.some
  ((tensorRight X).map_isZero (UnitSimpleClasses.isZero_tensorObj_of_ne h)).of_iso
    ((α_ I.repr (leftUnitClass X).repr X) ≪≫ whiskerLeftIso I.repr e).symm

/-- Tensoring a simple object `X` on the right by any unit summand other than `rightUnitClass X`
yields a zero object. -/
theorem isZero_tensorObj_unitRepr_of_ne {X : C} [Simple X] {I : UnitSimpleClasses C}
    (h : I ≠ rightUnitClass X) : IsZero (X ⊗ I.repr) :=
  let e : X ⊗ (rightUnitClass X).repr ≅ X := (exists_unitSimpleClasses_iso_right X).choose_spec.some
  ((tensorLeft X).map_isZero (UnitSimpleClasses.isZero_tensorObj_of_ne h.symm)).of_iso
    ((α_ X (rightUnitClass X).repr I.repr).symm ≪≫ whiskerRightIso e I.repr).symm

/-- For any simple object `X`, tensoring on the left with `(leftUnitClass X).repr` leaves `X`
isomorphic to itself, via the summand inclusion and the left unitor. -/
def leftUnitClassReprIso (X : C) [Simple X] : (leftUnitClass X).repr ⊗ X ≅ X where
  hom := UnitSimpleClasses.ι (leftUnitClass X) ▷ X ≫ (λ_ X).hom
  inv := (λ_ X).inv ≫ UnitSimpleClasses.π (leftUnitClass X) ▷ X
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight,
      UnitSimpleClasses.ι_comp_π_self, id_whiskerRight]
  inv_hom_id := by
    classical
    let := Fintype.ofFinite (UnitSimpleClasses C)
    have hsum : (UnitSimpleClasses.π (leftUnitClass X) ≫ UnitSimpleClasses.ι (leftUnitClass X)) ▷
        X = 𝟙 (𝟙_ C ⊗ X) := by
      rw [← id_whiskerRight, ← UnitSimpleClasses.sum_π_comp_ι, sum_whiskerRight]
      symm; rw [Finset.sum_eq_single (leftUnitClass X)]
      · intro I _ hne
        rw [comp_whiskerRight, (isZero_unitRepr_tensorObj_of_ne hne).eq_of_tgt (_ ▷ X) 0, zero_comp]
      · exact fun h ↦ absurd (Finset.mem_univ _) h
    rw [Category.assoc, ← Category.assoc (UnitSimpleClasses.π _ ▷ X), ← comp_whiskerRight, hsum,
      Category.id_comp, Iso.inv_hom_id]

@[reassoc]
theorem leftUnitClassReprIso_hom (X : C) [Simple X] :
    (leftUnitClassReprIso X).hom = UnitSimpleClasses.ι (leftUnitClass X) ▷ X ≫ (λ_ X).hom := (rfl)

@[reassoc]
theorem leftUnitClassReprIso_inv (X : C) [Simple X] :
    (leftUnitClassReprIso X).inv = (λ_ X).inv ≫ UnitSimpleClasses.π (leftUnitClass X) ▷ X := (rfl)

/-- For any simple object `X`, tensoring on the right with `(rightUnitClass X).repr` leaves `X`
isomorphic to itself, via the summand inclusion and the right unitor. -/
def rightUnitClassReprIso (X : C) [Simple X] : X ⊗ (rightUnitClass X).repr ≅ X where
  hom := X ◁ UnitSimpleClasses.ι (rightUnitClass X) ≫ (ρ_ X).hom
  inv := (ρ_ X).inv ≫ X ◁ UnitSimpleClasses.π (rightUnitClass X)
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← whiskerLeft_comp,
      UnitSimpleClasses.ι_comp_π_self, whiskerLeft_id]
  inv_hom_id := by
    classical
    let := Fintype.ofFinite (UnitSimpleClasses C)
    have hsum : X ◁ (UnitSimpleClasses.π (rightUnitClass X) ≫
        UnitSimpleClasses.ι (rightUnitClass X)) = 𝟙 (X ⊗ 𝟙_ C) := by
      rw [← whiskerLeft_id, ← UnitSimpleClasses.sum_π_comp_ι, whiskerLeft_sum]
      symm; rw [Finset.sum_eq_single (rightUnitClass X)]
      · intro I _ hne
        rw [whiskerLeft_comp, (isZero_tensorObj_unitRepr_of_ne hne).eq_of_tgt (X ◁ _) 0, zero_comp]
      · exact fun h ↦ absurd (Finset.mem_univ _) h
    rw [Category.assoc, ← Category.assoc (X ◁ UnitSimpleClasses.π _), ← whiskerLeft_comp, hsum,
      Category.id_comp, Iso.inv_hom_id]

@[reassoc]
theorem rightUnitClassReprIso_hom (X : C) [Simple X] :
    (rightUnitClassReprIso X).hom = X ◁ UnitSimpleClasses.ι (rightUnitClass X) ≫ (ρ_ X).hom := (rfl)

@[reassoc]
theorem rightUnitClassReprIso_inv (X : C) [Simple X] :
    (rightUnitClassReprIso X).inv = (ρ_ X).inv ≫ X ◁ UnitSimpleClasses.π (rightUnitClass X) := (rfl)

theorem not_isZero_leftUnitClass_tensorObj (X : C) [Simple X] :
    ¬ IsZero ((leftUnitClass X).repr ⊗ X) :=
  fun h ↦ Simple.not_isZero X (h.of_iso (leftUnitClassReprIso X).symm)

theorem not_isZero_tensorObj_rightUnitClass (X : C) [Simple X] :
    ¬ IsZero (X ⊗ (rightUnitClass X).repr) :=
  fun h ↦ Simple.not_isZero X (h.of_iso (rightUnitClassReprIso X).symm)

/-- `leftUnitClass X` is the unique unit summand `I` for which `I.repr ⊗ X` is nonzero. -/
theorem leftUnitClass_eq_iff {X : C} [Simple X] {I : UnitSimpleClasses C} :
    leftUnitClass X = I ↔ ¬ IsZero (I.repr ⊗ X) :=
  ⟨fun h ↦ h ▸ not_isZero_leftUnitClass_tensorObj X, fun h ↦
    by_contra fun hne ↦ h (isZero_unitRepr_tensorObj_of_ne (Ne.symm hne))⟩

/-- `rightUnitClass X` is the unique unit summand `I` for which `X ⊗ I.repr` is nonzero. -/
theorem rightUnitClass_eq_iff {X : C} [Simple X] {I : UnitSimpleClasses C} :
    rightUnitClass X = I ↔ ¬ IsZero (X ⊗ I.repr) :=
  ⟨fun h ↦ h ▸ not_isZero_tensorObj_rightUnitClass X, fun h ↦
    by_contra fun hne ↦ h (isZero_tensorObj_unitRepr_of_ne (Ne.symm hne))⟩

/-- Every simple object has a unique left-supporting unit summand. -/
theorem existsUnique_unitSimpleClasses_left (X : C) [Simple X] :
    ∃! I : UnitSimpleClasses C, ¬ IsZero (I.repr ⊗ X) :=
  ⟨leftUnitClass X, not_isZero_leftUnitClass_tensorObj X, fun _ h ↦ (leftUnitClass_eq_iff.2 h).symm⟩

/-- Every simple object has a unique right-supporting unit summand. -/
theorem existsUnique_unitSimpleClasses_right (X : C) [Simple X] :
    ∃! I : UnitSimpleClasses C, ¬ IsZero (X ⊗ I.repr) :=
  ⟨rightUnitClass X, not_isZero_tensorObj_rightUnitClass X,
    fun _ h ↦ (rightUnitClass_eq_iff.2 h).symm⟩

/-- Isomorphic simple objects have the same left unit class. -/
theorem leftUnitClass_congr {X Y : C} [Simple X] [Simple Y] (e : X ≅ Y) :
    leftUnitClass X = leftUnitClass Y :=
  leftUnitClass_eq_iff.2 fun h ↦
    not_isZero_leftUnitClass_tensorObj Y (h.of_iso (whiskerLeftIso (leftUnitClass Y).repr e.symm))

/-- Isomorphic simple objects have the same right unit class. -/
theorem rightUnitClass_congr {X Y : C} [Simple X] [Simple Y] (e : X ≅ Y) :
    rightUnitClass X = rightUnitClass Y :=
  rightUnitClass_eq_iff.2 fun h ↦
    not_isZero_tensorObj_rightUnitClass Y
      (h.of_iso (whiskerRightIso e.symm (rightUnitClass Y).repr))

@[simp]
theorem leftUnitClass_classOf_repr (X : C) [Simple X] :
    leftUnitClass (SimpleClasses.classOf X).repr = leftUnitClass X :=
  leftUnitClass_congr (SimpleClasses.classOfReprIso X)

@[simp]
theorem rightUnitClass_classOf_repr (X : C) [Simple X] :
    rightUnitClass (SimpleClasses.classOf X).repr = rightUnitClass X :=
  rightUnitClass_congr (SimpleClasses.classOfReprIso X)

@[simp]
theorem leftUnitClass_unitRepr (I : UnitSimpleClasses C) : leftUnitClass I.repr = I :=
  by_contra fun hne ↦
    not_isZero_leftUnitClass_tensorObj I.repr (UnitSimpleClasses.isZero_tensorObj_of_ne hne)

@[simp]
theorem rightUnitClass_unitRepr (I : UnitSimpleClasses C) : rightUnitClass I.repr = I :=
  by_contra fun hne ↦
    not_isZero_tensorObj_rightUnitClass I.repr
      (UnitSimpleClasses.isZero_tensorObj_of_ne (Ne.symm hne))

/-- If the tensor product `X ⊗ Y` of two simple objects is nonzero, then
`rightUnitClass X = leftUnitClass Y`. -/
theorem rightUnitClass_eq_leftUnitClass_of_not_isZero {X Y : C} [Simple X] [Simple Y]
    (h : ¬ IsZero (X ⊗ Y)) : rightUnitClass X = leftUnitClass Y := by
  by_contra hne
  have hz' := (tensorRight Y).map_isZero
    ((tensorLeft X).map_isZero (UnitSimpleClasses.isZero_tensorObj_of_ne hne))
  have e : (X ⊗ ((rightUnitClass X).repr ⊗ (leftUnitClass Y).repr)) ⊗ Y ≅ X ⊗ Y :=
    whiskerRightIso (α_ X (rightUnitClass X).repr (leftUnitClass Y).repr).symm Y ≪≫
      α_ (X ⊗ (rightUnitClass X).repr) (leftUnitClass Y).repr Y ≪≫
      tensorIso (rightUnitClassReprIso X) (leftUnitClassReprIso Y)
  exact h (hz'.of_iso e.symm)

/-- Along a nonzero morphism `U ⟶ X ⊗ Y` between simple objects, the right support of `X` equals
the left support of `Y`. -/
theorem rightUnitClass_eq_leftUnitClass_of_hom_ne_zero {X Y U : C} [Simple X] [Simple Y]
    {f : U ⟶ X ⊗ Y} (hf : f ≠ 0) : rightUnitClass X = leftUnitClass Y :=
  rightUnitClass_eq_leftUnitClass_of_not_isZero fun h ↦ hf (h.eq_of_tgt _ _)

/-- Along a nonzero morphism `U ⟶ X ⊗ Y` with `U` and `X` simple, `U` and `X` have the same left
unit class. -/
theorem leftUnitClass_eq_of_hom_ne_zero {X Y U : C} [Simple X] [Simple U]
    {f : U ⟶ X ⊗ Y} (hf : f ≠ 0) : leftUnitClass U = leftUnitClass X := by
  symm; rw [leftUnitClass_eq_iff]; intro hz
  have := isSplitMono_of_nonzero_from_simple hf
  have h0 : (leftUnitClass U).repr ◁ f = 0 :=
    (((tensorRight Y).map_isZero hz).of_iso (α_ _ X Y).symm).eq_of_tgt _ _
  exact not_isZero_leftUnitClass_tensorObj U <| (IsZero.iff_id_eq_zero _).2 <| by
    rw [← whiskerLeft_id, ← IsSplitMono.id f, whiskerLeft_comp, h0, zero_comp]

/-- Along a nonzero morphism `U ⟶ X ⊗ Y` with `U` and `Y` simple, `U` and `Y` have the same right
unit class. -/
theorem rightUnitClass_eq_of_hom_ne_zero {X Y U : C} [Simple Y] [Simple U]
    {f : U ⟶ X ⊗ Y} (hf : f ≠ 0) : rightUnitClass U = rightUnitClass Y := by
  symm; rw [rightUnitClass_eq_iff]; intro hz
  have := isSplitMono_of_nonzero_from_simple hf
  have h0 : f ▷ (rightUnitClass U).repr = 0 :=
    (((tensorLeft X).map_isZero hz).of_iso (α_ X Y _)).eq_of_tgt _ _
  exact not_isZero_tensorObj_rightUnitClass U <| (IsZero.iff_id_eq_zero _).2 <| by
    rw [← id_whiskerRight, ← IsSplitMono.id f, comp_whiskerRight, h0, zero_comp]

section Equivalence

variable {D : Type u₂} [Category.{v₂} D] [Abelian D] [MonoidalCategory D]
  [MonoidalPreadditive D] [IsFiniteSemisimpleCategory D]

/-- A monoidal equivalence commutes with `leftUnitClass`. -/
@[simp]
theorem leftUnitClass_equiv_obj (e : C ≌ D) [e.functor.Monoidal] (X : C) [Simple X] :
    @leftUnitClass D _ _ _ _ _ (e.functor.obj X) (CategoryTheory.simple_obj e.functor X) =
      UnitSimpleClasses.equiv e (leftUnitClass X) := by
  let _ := CategoryTheory.simple_obj e.functor X
  rw [leftUnitClass_eq_iff]
  let I := leftUnitClass X
  let iso : (UnitSimpleClasses.equiv e I).repr ⊗ e.functor.obj X ≅ e.functor.obj X :=
    whiskerRightIso (SimpleClasses.equivApplyReprIso e I.val) (e.functor.obj X) ≪≫
      Functor.Monoidal.μIso e.functor I.repr X ≪≫ e.functor.mapIso (leftUnitClassReprIso X)
  exact fun h ↦ Simple.not_isZero (e.functor.obj X) (h.of_iso iso.symm)

/-- A monoidal equivalence commutes with `rightUnitClass`. -/
@[simp]
theorem rightUnitClass_equiv_obj (e : C ≌ D) [e.functor.Monoidal] (X : C) [Simple X] :
    @rightUnitClass D _ _ _ _ _ (e.functor.obj X) (CategoryTheory.simple_obj e.functor X) =
      UnitSimpleClasses.equiv e (rightUnitClass X) := by
  let _ := CategoryTheory.simple_obj e.functor X
  rw [rightUnitClass_eq_iff]
  let I := rightUnitClass X
  let iso : e.functor.obj X ⊗ (UnitSimpleClasses.equiv e I).repr ≅ e.functor.obj X :=
    whiskerLeftIso (e.functor.obj X) (SimpleClasses.equivApplyReprIso e I.val) ≪≫
      Functor.Monoidal.μIso e.functor X I.repr ≪≫ e.functor.mapIso (rightUnitClassReprIso X)
  exact fun h ↦ Simple.not_isZero (e.functor.obj X) (h.of_iso iso.symm)

@[simp]
theorem leftUnitClass_equiv_repr (e : C ≌ D) [e.functor.Monoidal] (S : SimpleClasses C) :
    leftUnitClass (SimpleClasses.equiv e S).repr =
      UnitSimpleClasses.equiv e (leftUnitClass S.repr) :=
  let _ := CategoryTheory.simple_obj e.functor S.repr
  (leftUnitClass_congr (SimpleClasses.equivApplyReprIso e S)).trans
    (leftUnitClass_equiv_obj e S.repr)

@[simp]
theorem rightUnitClass_equiv_repr (e : C ≌ D) [e.functor.Monoidal] (S : SimpleClasses C) :
    rightUnitClass (SimpleClasses.equiv e S).repr =
      UnitSimpleClasses.equiv e (rightUnitClass S.repr) :=
  let _ := CategoryTheory.simple_obj e.functor S.repr
  (rightUnitClass_congr (SimpleClasses.equivApplyReprIso e S)).trans
    (rightUnitClass_equiv_obj e S.repr)

end Equivalence

end Semisimple

end TauCeti
