/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grading.Universal
public import TauCeti.CategoryTheory.Monoidal.Scalar
public import TauCeti.CategoryTheory.Semisimple.Equivalence
public import TauCeti.CategoryTheory.Semisimple.Monoidal

/-!
# Simple summands of the tensor unit and Peircian support

In a finite semisimple monoidal category `C` whose tensor product is additive
(`MonoidalPreadditive`), the tensor unit `𝟙_ C` need not be simple: `C` may be a *multitensor* or
*multifusion* category. By Eckmann–Hilton (`TauCeti.scalar_comm`), `End (𝟙_ C)` is commutative, so
`𝟙_ C` decomposes as a multiplicity-free finite biproduct of pairwise tensor-orthogonal simple
objects.

`TauCeti.UnitSimpleClasses C` is the type of isomorphism classes of simple objects mapping
nontrivially into `𝟙_ C`. Every simple object `X` has a unique left support
`TauCeti.leftUnitClass X` and a unique right support `TauCeti.rightUnitClass X` in
`UnitSimpleClasses C` characterized by `(leftUnitClass X).repr ⊗ X ≅ X` and
`X ⊗ (rightUnitClass X).repr ≅ X`. Every nonzero morphism `U ⟶ X ⊗ Y` between simple objects
satisfies the composability and boundary conditions
`rightUnitClass X = leftUnitClass Y`, `leftUnitClass U = leftUnitClass X`, and
`rightUnitClass U = rightUnitClass Y`. Under rigidity, duality swaps the left and right unit
classes and two simple objects have nonzero tensor product precisely when
`rightUnitClass X = leftUnitClass Y`.

## Main declarations

* `TauCeti.UnitSimpleClasses`: isomorphism classes of simple summands of `𝟙_ C`.
* `TauCeti.UnitSimpleClasses.isZero_tensorObj_of_ne`: distinct unit summands have zero tensor
  product.
* `TauCeti.simpleMultiplicities_tensorUnit_le_one`: `𝟙_ C` is multiplicity-free.
* `TauCeti.leftUnitClass`, `TauCeti.rightUnitClass`, `TauCeti.leftUnitClassReprIso`,
  `TauCeti.rightUnitClassReprIso`: the unique left and right unit summands supporting a simple
  object.
* `TauCeti.rightUnitClass_eq_leftUnitClass_of_hom_ne_zero`,
  `TauCeti.leftUnitClass_eq_of_hom_ne_zero`, `TauCeti.rightUnitClass_eq_of_hom_ne_zero`:
  endpoint compatibility along nonzero morphisms `U ⟶ X ⊗ Y`.
* `TauCeti.not_isZero_tensorObj_iff_rightUnitClass_eq_leftUnitClass`: in a rigid finite semisimple
  monoidal category, `X ⊗ Y` is nonzero for simple `X, Y` iff `rightUnitClass X = leftUnitClass Y`.
* `TauCeti.UnitSimpleClasses.equiv`: transport of unit summand classes along a monoidal equivalence.

## References

* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  Higher Structures **4** (2020), no. 2, 22–56 (arXiv:1808.00323), §§2.1, 3.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.3
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ v₂ u₁ u₂

namespace TauCeti

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
    (mkOfHomNeZero hf).val = SimpleClasses.classOf X :=
  (rfl)

/-- When `𝟙_ C` is simple, its isomorphism class as a unit summand. -/
def unit [Simple (𝟙_ C)] : UnitSimpleClasses C :=
  mkOfHomNeZero (CategoryTheory.id_ne_zero (𝟙_ C))

@[simp]
theorem val_unit [Simple (𝟙_ C)] :
    (unit (C := C)).val = SimpleClasses.classOf (𝟙_ C) :=
  (rfl)

section Equivalence

variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [MonoidalCategory D]

private theorem map_unit_hom_ne_zero (e : C ≌ D) [e.functor.Monoidal]
    (I : UnitSimpleClasses C) :
    ∃ g : (SimpleClasses.equiv e I.val).repr ⟶ 𝟙_ D, g ≠ 0 := by
  obtain ⟨f, hf⟩ := I.property
  have : e.functor.PreservesZeroMorphisms :=
    e.functor.preservesZeroMorphisms_of_isLeftAdjoint
  let d := SimpleClasses.equivApplyReprIso e I.val
  let u := Functor.Monoidal.εIso e.functor
  refine ⟨d.hom ≫ e.functor.map f ≫ u.inv, fun h ↦ hf ?_⟩
  apply e.functor.map_injective
  rw [e.functor.map_zero]
  simpa using d.inv ≫= h =≫ u.hom

/-- A monoidal equivalence induces a bijection between the simple summand classes of the tensor
units. -/
def equiv (e : C ≌ D) [e.functor.Monoidal] :
    UnitSimpleClasses C ≃ UnitSimpleClasses D where
  toFun I := ⟨SimpleClasses.equiv e I.val, map_unit_hom_ne_zero e I⟩
  invFun J :=
    letI := e.inverseMonoidal
    ⟨SimpleClasses.equiv e.symm J.val, map_unit_hom_ne_zero e.symm J⟩
  left_inv I := Subtype.ext <| (SimpleClasses.eq_iff_nonempty_iso _ _).2
    ⟨SimpleClasses.equivApplyReprIso e.symm _ ≪≫
      e.inverse.mapIso (SimpleClasses.equivApplyReprIso e I.val) ≪≫
      (e.unitIso.app I.repr).symm⟩
  right_inv J := Subtype.ext <| (SimpleClasses.eq_iff_nonempty_iso _ _).2
    ⟨SimpleClasses.equivApplyReprIso e _ ≪≫
      e.functor.mapIso (SimpleClasses.equivApplyReprIso e.symm J.val) ≪≫
      e.counitIso.app J.repr⟩

@[simp]
theorem val_equiv_apply (e : C ≌ D) [e.functor.Monoidal] (I : UnitSimpleClasses C) :
    (equiv e I).val = SimpleClasses.equiv e I.val :=
  (rfl)

@[simp]
theorem equiv_symm (e : C ≌ D) [e.functor.Monoidal] :
    (equiv e).symm = @equiv D _ _ _ C _ _ _ e.symm e.inverseMonoidal :=
  (rfl)

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
    simpleMultiplicities (𝟙_ C) S ≤ 1 := by
  classical
  obtain ⟨ι, hι, a, ha, hba, ⟨e⟩⟩ :=
    IsFiniteSemisimpleCategory.exists_biproduct_simples (𝟙_ C)
  let _ := hι
  let _ := ha
  let _ := hba
  rw [simpleMultiplicities_apply_eq_card a e S, Nat.card_eq_fintype_card,
    Fintype.card_le_one_iff_subsingleton]
  refine ⟨fun ⟨i, hi⟩ ⟨j, hj⟩ ↦ ?_⟩
  apply Subtype.ext
  by_contra hne
  obtain ⟨φ⟩ := (SimpleClasses.classOf_eq_iff_nonempty_iso _ _).1 (hi.trans hj.symm)
  let f₁ : a i ⟶ 𝟙_ C := biproduct.ι a i ≫ e.inv
  let p₁ : 𝟙_ C ⟶ a i := e.hom ≫ biproduct.π a i
  let f₂ : a i ⟶ 𝟙_ C := φ.hom ≫ biproduct.ι a j ≫ e.inv
  let p₂ : 𝟙_ C ⟶ a i := e.hom ≫ biproduct.π a j ≫ φ.inv
  have h₁₁ : f₁ ≫ p₁ = 𝟙 (a i) := by simp [f₁, p₁]
  have h₂₂ : f₂ ≫ p₂ = 𝟙 (a i) := by simp [f₂, p₂]
  have h₁₂ : f₁ ≫ p₂ = 0 := by
    simp only [f₁, p₂, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, biproduct.ι_π_ne a hne, zero_comp]
  have hcomm := f₁ ≫= scalar_comm (p₁ ≫ f₂) (p₂ ≫ f₁) =≫ p₁
  have hlhs : f₁ ≫ ((p₁ ≫ f₂) ≫ p₂ ≫ f₁) ≫ p₁ = 𝟙 (a i) := by
    simp only [Category.assoc]
    rw [reassoc_of% h₁₁, reassoc_of% h₂₂, h₁₁]
  have hrhs : f₁ ≫ ((p₂ ≫ f₁) ≫ p₁ ≫ f₂) ≫ p₁ = 0 := by
    simp only [Category.assoc]
    rw [reassoc_of% h₁₂, zero_comp]
  exact CategoryTheory.id_ne_zero (a i) (hlhs.symm.trans (hcomm.trans hrhs))

@[simp]
theorem UnitSimpleClasses.simpleMultiplicities_tensorUnit (I : UnitSimpleClasses C) :
    simpleMultiplicities (𝟙_ C) I.val = 1 := by
  have hne : simpleMultiplicities (𝟙_ C) I.val ≠ 0 := by
    simpa using (simpleMultiplicities_apply_classOf_ne_zero_iff (𝟙_ C) I.repr).2 I.property
  have hle := simpleMultiplicities_tensorUnit_le_one I.val
  omega

/-- Distinct simple summands of `𝟙_ C` have zero tensor product. -/
theorem UnitSimpleClasses.isZero_tensorObj_of_ne {I J : UnitSimpleClasses C} (h : I ≠ J) :
    IsZero (I.repr ⊗ J.repr) := by
  obtain ⟨f, hf⟩ := I.property
  obtain ⟨g, hg⟩ := J.property
  have := isSplitMono_of_nonzero_from_simple hf
  have := isSplitMono_of_nonzero_from_simple hg
  let p := retraction f
  let q := retraction g
  have hIJ : I.val ≠ J.val := mt Subtype.ext h
  have hfq : f ≫ q = 0 :=
    @Subsingleton.elim _ (SimpleClasses.homOrthogonal_repr hIJ) _ _
  have he₁₂ : p ≫ f ≫ q ≫ g = 0 := by simp [reassoc_of% hfq]
  have htensor : (p ≫ f) ⊗ₘ (q ≫ g) = 0 := by
    rw [← cancel_mono (λ_ (𝟙_ C)).hom, zero_comp, tensorHom_def, Category.assoc,
      leftUnitor_naturality, unitors_equal, rightUnitor_naturality_assoc, ← unitors_equal,
      Category.assoc, he₁₂, comp_zero]
  have hid₁ : 𝟙 I.repr = f ≫ (p ≫ f) ≫ p := by
    simp [p, ← Category.assoc, IsSplitMono.id]
  have hid₂ : 𝟙 J.repr = g ≫ (q ≫ g) ≫ q := by
    simp [q, ← Category.assoc, IsSplitMono.id]
  rw [IsZero.iff_id_eq_zero, ← id_tensorHom_id, hid₁, hid₂, ← tensorHom_comp_tensorHom,
    ← tensorHom_comp_tensorHom, htensor]
  simp

/-- Every nonzero morphism out of `𝟙_ C` remains nonzero after precomposing with some simple
summand of `𝟙_ C`. -/
theorem exists_unitSimpleClasses_comp_ne_zero {Z : C} {h : 𝟙_ C ⟶ Z} (hh : h ≠ 0) :
    ∃ (I : UnitSimpleClasses C) (f : I.repr ⟶ 𝟙_ C), f ≠ 0 ∧ f ≫ h ≠ 0 := by
  have ⟨S, hS, s, hs⟩ : ∃ (S : C) (_ : Simple S) (s : S ⟶ 𝟙_ C), s ≫ h ≠ 0 := by
    by_contra! h0
    refine hh ((𝟭 C).hom_ext_of_simple fun S _ s ↦ ?_)
    simpa using h0 S inferInstance s
  let _ := hS
  let d := SimpleClasses.classOfReprIso S
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
  let _ := hι
  let _ := ha
  let _ := hba
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
  exists_unitSimpleClasses_iso_of_functor (tensorRight X) (fun a ↦ rightDistributor a X)
    (λ_ X).symm

private theorem exists_unitSimpleClasses_iso_right (X : C) [Simple X] :
    ∃ I : UnitSimpleClasses C, Nonempty (X ⊗ I.repr ≅ X) :=
  exists_unitSimpleClasses_iso_of_functor (tensorLeft X) (fun a ↦ leftDistributor X a)
    (ρ_ X).symm

/-- The unique simple summand class `I` of `𝟙_ C` such that `I.repr ⊗ X ≅ X`. -/
def leftUnitClass (X : C) [Simple X] : UnitSimpleClasses C :=
  (exists_unitSimpleClasses_iso_left X).choose

/-- For any simple object `X`, tensoring on the left with `(leftUnitClass X).repr` leaves `X`
isomorphic to itself. -/
def leftUnitClassReprIso (X : C) [Simple X] : (leftUnitClass X).repr ⊗ X ≅ X :=
  (exists_unitSimpleClasses_iso_left X).choose_spec.some

/-- The unique simple summand class `I` of `𝟙_ C` such that `X ⊗ I.repr ≅ X`. -/
def rightUnitClass (X : C) [Simple X] : UnitSimpleClasses C :=
  (exists_unitSimpleClasses_iso_right X).choose

/-- For any simple object `X`, tensoring on the right with `(rightUnitClass X).repr` leaves `X`
isomorphic to itself. -/
def rightUnitClassReprIso (X : C) [Simple X] : X ⊗ (rightUnitClass X).repr ≅ X :=
  (exists_unitSimpleClasses_iso_right X).choose_spec.some

theorem not_isZero_leftUnitClass_tensorObj (X : C) [Simple X] :
    ¬ IsZero ((leftUnitClass X).repr ⊗ X) :=
  fun h ↦ Simple.not_isZero X (h.of_iso (leftUnitClassReprIso X).symm)

theorem not_isZero_tensorObj_rightUnitClass (X : C) [Simple X] :
    ¬ IsZero (X ⊗ (rightUnitClass X).repr) :=
  fun h ↦ Simple.not_isZero X (h.of_iso (rightUnitClassReprIso X).symm)

/-- Tensoring a simple object `X` on the left by any unit summand other than `leftUnitClass X`
yields a zero object. -/
theorem isZero_unitRepr_tensorObj_of_ne {X : C} [Simple X] {I : UnitSimpleClasses C}
    (h : I ≠ leftUnitClass X) : IsZero (I.repr ⊗ X) := by
  have hz := (tensorRight X).map_isZero (UnitSimpleClasses.isZero_tensorObj_of_ne h)
  exact hz.of_iso ((α_ I.repr (leftUnitClass X).repr X) ≪≫
    whiskerLeftIso I.repr (leftUnitClassReprIso X)).symm

/-- Tensoring a simple object `X` on the right by any unit summand other than `rightUnitClass X`
yields a zero object. -/
theorem isZero_tensorObj_unitRepr_of_ne {X : C} [Simple X] {I : UnitSimpleClasses C}
    (h : I ≠ rightUnitClass X) : IsZero (X ⊗ I.repr) := by
  have hz := (tensorLeft X).map_isZero (UnitSimpleClasses.isZero_tensorObj_of_ne h.symm)
  exact hz.of_iso ((α_ X (rightUnitClass X).repr I.repr).symm ≪≫
    whiskerRightIso (rightUnitClassReprIso X) I.repr).symm

/-- `leftUnitClass X` is the unique unit summand `I` for which `I.repr ⊗ X` is nonzero. -/
theorem leftUnitClass_eq_iff {X : C} [Simple X] {I : UnitSimpleClasses C} :
    leftUnitClass X = I ↔ ¬ IsZero (I.repr ⊗ X) := by
  refine ⟨fun h ↦ h ▸ not_isZero_leftUnitClass_tensorObj X, fun h ↦ ?_⟩
  by_contra hne
  exact h (isZero_unitRepr_tensorObj_of_ne (Ne.symm hne))

/-- `rightUnitClass X` is the unique unit summand `I` for which `X ⊗ I.repr` is nonzero. -/
theorem rightUnitClass_eq_iff {X : C} [Simple X] {I : UnitSimpleClasses C} :
    rightUnitClass X = I ↔ ¬ IsZero (X ⊗ I.repr) := by
  refine ⟨fun h ↦ h ▸ not_isZero_tensorObj_rightUnitClass X, fun h ↦ ?_⟩
  by_contra hne
  exact h (isZero_tensorObj_unitRepr_of_ne (Ne.symm hne))

/-- Every simple object has a unique left-supporting unit summand. -/
theorem existsUnique_unitSimpleClasses_left (X : C) [Simple X] :
    ∃! I : UnitSimpleClasses C, ¬ IsZero (I.repr ⊗ X) :=
  ⟨leftUnitClass X, not_isZero_leftUnitClass_tensorObj X,
    fun _ h ↦ (leftUnitClass_eq_iff.2 h).symm⟩

/-- Every simple object has a unique right-supporting unit summand. -/
theorem existsUnique_unitSimpleClasses_right (X : C) [Simple X] :
    ∃! I : UnitSimpleClasses C, ¬ IsZero (X ⊗ I.repr) :=
  ⟨rightUnitClass X, not_isZero_tensorObj_rightUnitClass X,
    fun _ h ↦ (rightUnitClass_eq_iff.2 h).symm⟩

/-- Isomorphic simple objects have the same left unit class. -/
theorem leftUnitClass_congr {X Y : C} [Simple X] [Simple Y] (e : X ≅ Y) :
    leftUnitClass X = leftUnitClass Y := by
  rw [leftUnitClass_eq_iff]
  intro h
  exact not_isZero_leftUnitClass_tensorObj Y
    (h.of_iso (whiskerLeftIso (leftUnitClass Y).repr e.symm))

/-- Isomorphic simple objects have the same right unit class. -/
theorem rightUnitClass_congr {X Y : C} [Simple X] [Simple Y] (e : X ≅ Y) :
    rightUnitClass X = rightUnitClass Y := by
  rw [rightUnitClass_eq_iff]
  intro h
  exact not_isZero_tensorObj_rightUnitClass Y
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
theorem leftUnitClass_unitRepr (I : UnitSimpleClasses C) :
    leftUnitClass I.repr = I := by
  by_contra hne
  exact not_isZero_leftUnitClass_tensorObj I.repr
    (UnitSimpleClasses.isZero_tensorObj_of_ne hne)

@[simp]
theorem rightUnitClass_unitRepr (I : UnitSimpleClasses C) :
    rightUnitClass I.repr = I := by
  by_contra hne
  exact not_isZero_tensorObj_rightUnitClass I.repr
    (UnitSimpleClasses.isZero_tensorObj_of_ne (Ne.symm hne))

/-- Every simple unit summand is tensor-idempotent: `I.repr ⊗ I.repr ≅ I.repr`. -/
def UnitSimpleClasses.tensorSelfIso (I : UnitSimpleClasses C) :
    I.repr ⊗ I.repr ≅ I.repr :=
  whiskerRightIso (eqToIso (congrArg UnitSimpleClasses.repr (leftUnitClass_unitRepr I)).symm)
    I.repr ≪≫ leftUnitClassReprIso I.repr

/-- Every simple summand of the tensor unit has trivial degree in `universalGradingGroup C`. -/
@[simp]
theorem universalGradingGroup.degree_unitSummand (I : UnitSimpleClasses C) :
    universalGradingGroup.degree I.val = 1 := by
  let a := (UnitSimpleClasses.tensorSelfIso I).symm
  have ha : a.hom ≠ 0 := fun h ↦
    CategoryTheory.id_ne_zero I.repr (by rw [← a.hom_inv_id, h, zero_comp])
  exact mul_eq_left.mp (universalGradingGroup.degree_mul I.val I.val I.val a.hom ha).symm

/-- Any simple object mapping nontrivially into `𝟙_ C` has trivial degree in
`universalGradingGroup C`. -/
theorem universalGradingGroup.degree_classOf_eq_one_of_hom_to_unit_ne_zero
    {X : C} [Simple X] {f : X ⟶ 𝟙_ C} (hf : f ≠ 0) :
    universalGradingGroup.degree (SimpleClasses.classOf X) = 1 :=
  universalGradingGroup.degree_unitSummand (UnitSimpleClasses.mkOfHomNeZero hf)

/-- If the tensor product `X ⊗ Y` of two simple objects is nonzero, then
`rightUnitClass X = leftUnitClass Y`. -/
theorem rightUnitClass_eq_leftUnitClass_of_not_isZero {X Y : C} [Simple X] [Simple Y]
    (h : ¬ IsZero (X ⊗ Y)) : rightUnitClass X = leftUnitClass Y := by
  by_contra hne
  have hz : IsZero ((rightUnitClass X).repr ⊗ (leftUnitClass Y).repr) :=
    UnitSimpleClasses.isZero_tensorObj_of_ne hne
  have hz' : IsZero ((X ⊗ ((rightUnitClass X).repr ⊗ (leftUnitClass Y).repr)) ⊗ Y) :=
    (tensorRight Y).map_isZero ((tensorLeft X).map_isZero hz)
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
  symm
  rw [leftUnitClass_eq_iff]
  intro hz
  have := isSplitMono_of_nonzero_from_simple hf
  let I := leftUnitClass U
  have h0 : I.repr ◁ f = 0 :=
    (((tensorRight Y).map_isZero hz).of_iso (α_ I.repr X Y).symm).eq_of_tgt _ _
  have hid : 𝟙 (I.repr ⊗ U) = 0 := by
    rw [← whiskerLeft_id, ← IsSplitMono.id f, whiskerLeft_comp, h0, zero_comp]
  exact not_isZero_leftUnitClass_tensorObj U ((IsZero.iff_id_eq_zero _).2 hid)

/-- Along a nonzero morphism `U ⟶ X ⊗ Y` with `U` and `Y` simple, `U` and `Y` have the same right
unit class. -/
theorem rightUnitClass_eq_of_hom_ne_zero {X Y U : C} [Simple Y] [Simple U]
    {f : U ⟶ X ⊗ Y} (hf : f ≠ 0) : rightUnitClass U = rightUnitClass Y := by
  symm
  rw [rightUnitClass_eq_iff]
  intro hz
  have := isSplitMono_of_nonzero_from_simple hf
  let J := rightUnitClass U
  have h0 : f ▷ J.repr = 0 :=
    (((tensorLeft X).map_isZero hz).of_iso (α_ X Y J.repr)).eq_of_tgt _ _
  have hid : 𝟙 (U ⊗ J.repr) = 0 := by
    rw [← id_whiskerRight, ← IsSplitMono.id f, comp_whiskerRight, h0, zero_comp]
  exact not_isZero_tensorObj_rightUnitClass U ((IsZero.iff_id_eq_zero _).2 hid)

section Rigid

variable [RigidCategory C]

/-- Right duality interchanges left and right unit classes: the left unit class of `Xᘁ` is the
right unit class of `X`. -/
@[simp]
theorem leftUnitClass_rightDual (X : C) [Simple X] :
    leftUnitClass Xᘁ = rightUnitClass X := by
  obtain ⟨I, f, _, hf⟩ :=
    exists_unitSimpleClasses_comp_ne_zero (coevaluation_ne_zero (Y := Xᘁ) (Simple.not_isZero X))
  exact (rightUnitClass_eq_leftUnitClass_of_hom_ne_zero hf).symm

/-- Right duality interchanges left and right unit classes: the right unit class of `Xᘁ` is the
left unit class of `X`. -/
@[simp]
theorem rightUnitClass_rightDual (X : C) [Simple X] :
    rightUnitClass Xᘁ = leftUnitClass X := by
  obtain ⟨I, f, _, hf⟩ :=
    exists_unitSimpleClasses_comp_ne_zero (coevaluation_ne_zero (Y := Xᘁ) (Simple.not_isZero X))
  have hI₁ : I = leftUnitClass X := by
    simpa using leftUnitClass_eq_of_hom_ne_zero hf
  have hI₂ : I = rightUnitClass Xᘁ := by
    simpa using rightUnitClass_eq_of_hom_ne_zero hf
  exact hI₂.symm.trans hI₁

@[simp]
theorem leftUnitClass_dual_repr (S : SimpleClasses C) :
    leftUnitClass S.dual.repr = rightUnitClass S.repr := by
  rw [leftUnitClass_congr (SimpleClasses.dualReprIso S), leftUnitClass_rightDual]

@[simp]
theorem rightUnitClass_dual_repr (S : SimpleClasses C) :
    rightUnitClass S.dual.repr = leftUnitClass S.repr := by
  rw [rightUnitClass_congr (SimpleClasses.dualReprIso S), rightUnitClass_rightDual]

/-- In a rigid finite semisimple monoidal category, the tensor product of two simple objects `X`
and `Y` is nonzero if and only if `rightUnitClass X = leftUnitClass Y`. -/
theorem not_isZero_tensorObj_iff_rightUnitClass_eq_leftUnitClass (X Y : C) [Simple X]
    [Simple Y] : ¬ IsZero (X ⊗ Y) ↔ rightUnitClass X = leftUnitClass Y := by
  refine ⟨rightUnitClass_eq_leftUnitClass_of_not_isZero, fun h hz ↦ ?_⟩
  obtain ⟨I, f, _, hf⟩ :=
    exists_unitSimpleClasses_comp_ne_zero (coevaluation_ne_zero (Y := Yᘁ) (Simple.not_isZero Y))
  have hI : I = rightUnitClass X := by
    have hIY : I = leftUnitClass Y := by simpa using leftUnitClass_eq_of_hom_ne_zero hf
    exact hIY.trans h.symm
  have := isSplitMono_of_nonzero_from_simple hf
  have hz' : IsZero (X ⊗ (Y ⊗ Yᘁ)) :=
    ((tensorRight Yᘁ).map_isZero hz).of_iso (α_ X Y Yᘁ).symm
  have h0 : X ◁ (f ≫ η_ Y Yᘁ) = 0 := hz'.eq_of_tgt _ _
  have hid : 𝟙 (X ⊗ I.repr) = 0 := by
    rw [← whiskerLeft_id, ← IsSplitMono.id (f ≫ η_ Y Yᘁ), whiskerLeft_comp, h0, zero_comp]
  exact not_isZero_tensorObj_rightUnitClass X (hI ▸ (IsZero.iff_id_eq_zero _).2 hid)

end Rigid

section Equivalence

variable {D : Type u₂} [Category.{v₂} D] [Abelian D] [MonoidalCategory D]
  [MonoidalPreadditive D] [IsFiniteSemisimpleCategory D]

/-- A monoidal equivalence commutes with `leftUnitClass`. -/
@[simp]
theorem leftUnitClass_equiv_obj (e : C ≌ D) [e.functor.Monoidal] (X : C) [Simple X] :
    @leftUnitClass D _ _ _ _ _ (e.functor.obj X) (CategoryTheory.simple_obj e.functor X) =
      UnitSimpleClasses.equiv e (leftUnitClass X) := by
  let _ : Simple (e.functor.obj X) := CategoryTheory.simple_obj e.functor X
  rw [leftUnitClass_eq_iff]
  let I := leftUnitClass X
  let iso : (UnitSimpleClasses.equiv e I).repr ⊗ e.functor.obj X ≅ e.functor.obj X :=
    whiskerRightIso (SimpleClasses.equivApplyReprIso e I.val) (e.functor.obj X) ≪≫
      Functor.Monoidal.μIso e.functor I.repr X ≪≫
      e.functor.mapIso (leftUnitClassReprIso X)
  exact fun h ↦ Simple.not_isZero (e.functor.obj X) (h.of_iso iso.symm)

/-- A monoidal equivalence commutes with `rightUnitClass`. -/
@[simp]
theorem rightUnitClass_equiv_obj (e : C ≌ D) [e.functor.Monoidal] (X : C) [Simple X] :
    @rightUnitClass D _ _ _ _ _ (e.functor.obj X) (CategoryTheory.simple_obj e.functor X) =
      UnitSimpleClasses.equiv e (rightUnitClass X) := by
  let _ : Simple (e.functor.obj X) := CategoryTheory.simple_obj e.functor X
  rw [rightUnitClass_eq_iff]
  let I := rightUnitClass X
  let iso : e.functor.obj X ⊗ (UnitSimpleClasses.equiv e I).repr ≅ e.functor.obj X :=
    whiskerLeftIso (e.functor.obj X) (SimpleClasses.equivApplyReprIso e I.val) ≪≫
      Functor.Monoidal.μIso e.functor X I.repr ≪≫
      e.functor.mapIso (rightUnitClassReprIso X)
  exact fun h ↦ Simple.not_isZero (e.functor.obj X) (h.of_iso iso.symm)

@[simp]
theorem leftUnitClass_equiv_repr (e : C ≌ D) [e.functor.Monoidal] (S : SimpleClasses C) :
    leftUnitClass (SimpleClasses.equiv e S).repr =
      UnitSimpleClasses.equiv e (leftUnitClass S.repr) := by
  let _ : Simple (e.functor.obj S.repr) := CategoryTheory.simple_obj e.functor S.repr
  exact (leftUnitClass_congr (SimpleClasses.equivApplyReprIso e S)).trans
    (leftUnitClass_equiv_obj e S.repr)

@[simp]
theorem rightUnitClass_equiv_repr (e : C ≌ D) [e.functor.Monoidal] (S : SimpleClasses C) :
    rightUnitClass (SimpleClasses.equiv e S).repr =
      UnitSimpleClasses.equiv e (rightUnitClass S.repr) := by
  let _ : Simple (e.functor.obj S.repr) := CategoryTheory.simple_obj e.functor S.repr
  exact (rightUnitClass_congr (SimpleClasses.equivApplyReprIso e S)).trans
    (rightUnitClass_equiv_obj e S.repr)

end Equivalence

end Semisimple

end TauCeti
