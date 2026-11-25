/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import TauCeti.CategoryTheory.Preadditive.TowerDifference
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import TauCeti.Algebra.DirectSum.Telescope
import TauCeti.CategoryTheory.Preadditive.Compact
import TauCeti.CategoryTheory.Triangulated.LiftingObstruction

/-!
# Homotopy colimits of sequences and the Milnor short exact sequence

Let `X : ℕ ⥤ C` be a sequence `X₀ ⟶ X₁ ⟶ ⋯` in a preadditive category whose terms have a countable
coproduct `∐ₙ Xₙ`. The **coproduct–difference map** `X.sequenceDifference` is the endomorphism
`1 - s` of `∐ₙ Xₙ` with `n`-th component `ιₙ - X(n → n + 1) ≫ ιₙ₊₁`, dual to
`CategoryTheory.Functor.towerDifference`. When `C` is pretriangulated, a **homotopy colimit** (or
Milnor telescope, `TauCeti.HomotopyColimit X`) is a distinguished triangle
`∐ₙ Xₙ ⟶ ∐ₙ Xₙ ⟶ pt ⟶ (∐ₙ Xₙ)⟦1⟧` completing `X.sequenceDifference`; it always exists, carries a
cocone `h.cocone` with legs `h.ι n`, and is weakly functorial (`HomotopyColimit.exists_hom`).

For `G : C` whose additive represented functor preserves countable coproducts, every morphism
`G ⟶ h.pt` factors through some `h.ι N` (`exists_eq_comp_ι`) and `g : G ⟶ X.obj n` vanishes in
`h.pt` iff it vanishes at some stage `m ≥ n` (`comp_ι_eq_zero_iff`). For any contravariant
homological functor `E : Cᵒᵖ ⥤ A` into an abelian category `A` sending countable coproducts to
countable products, applying `E` yields the **Milnor short exact sequence**
`0 ⟶ cokernel d₁ ⟶ E(h.pt) ⟶ kernel d₀ ⟶ 0` (`milnorShortComplex_shortExact`), natural in sequence
morphisms; for `A = AddCommGrpCat`, compatible families lift to `E(h.pt)` (`exists_map_ι_eq`).

## Main declarations

* `CategoryTheory.Functor.sequenceDifference`, `TauCeti.HomotopyColimit`.
* `TauCeti.HomotopyColimit.exists_eq_comp_ι`, `TauCeti.HomotopyColimit.comp_ι_eq_zero_iff`.
* `TauCeti.HomotopyColimit.milnorLimOneTo`, `TauCeti.HomotopyColimit.milnorToLim`,
  `TauCeti.HomotopyColimit.milnorShortComplex`,
  `TauCeti.HomotopyColimit.milnorShortComplex_shortExact`.
* `TauCeti.HomotopyColimit.exists_map_ι_eq`.

## References

* A. Neeman, *Triangulated categories*, Annals of Mathematics Studies 148, Princeton University
  Press (2001), Definition 1.6.4 and Lemma 1.6.6.
* S. Schwede, *Symmetric spectra*, Chapter II, Definition 5.4 and Lemma 5.6.
* [Stacks: Derived Categories, Section 13.33, Tag 0910](https://stacks.math.columbia.edu/tag/0910)
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Pretriangulated Pretriangulated.Opposite
open scoped DirectSum

universe v v' u u'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Preadditive C]

section SequenceDifference

variable (X : ℕ ⥤ C) [HasCoproduct fun n : ℕ ↦ X.obj n]

/-- The **coproduct–difference map** `1 - s` of a sequence `X₀ ⟶ X₁ ⟶ ⋯`: the endomorphism of
`∐ₙ Xₙ` whose `n`-th component is `ιₙ - X(n → n + 1) ≫ ιₙ₊₁` (`ι_sequenceDifference`). -/
def sequenceDifference : (∐ fun n : ℕ ↦ X.obj n) ⟶ (∐ fun n : ℕ ↦ X.obj n) :=
  Sigma.desc fun n ↦
    Sigma.ι (fun n : ℕ ↦ X.obj n) n -
      X.map (homOfLE (Nat.le_add_right n 1)) ≫ Sigma.ι (fun n : ℕ ↦ X.obj n) (n + 1)

@[reassoc (attr := simp)]
lemma ι_sequenceDifference (n : ℕ) :
    Sigma.ι (fun n : ℕ ↦ X.obj n) n ≫ X.sequenceDifference =
      Sigma.ι (fun n : ℕ ↦ X.obj n) n -
        X.map (homOfLE (Nat.le_add_right n 1)) ≫ Sigma.ι (fun n : ℕ ↦ X.obj n) (n + 1) := by
  simp [sequenceDifference]

/-- A morphism `π` out of `∐ₙ Xₙ` kills `X.sequenceDifference` exactly when its components are
compatible with the transitions `Xₙ ⟶ Xₙ₊₁`. -/
lemma sequenceDifference_comp_eq_zero_iff {Y : C} (π : (∐ fun n : ℕ ↦ X.obj n) ⟶ Y) :
    X.sequenceDifference ≫ π = 0 ↔
      ∀ n, X.map (homOfLE (Nat.le_add_right n 1)) ≫ Sigma.ι _ (n + 1) ≫ π =
        Sigma.ι _ n ≫ π := by
  refine ⟨fun h n ↦ ?_, fun h ↦ Sigma.hom_ext _ _ fun n ↦ ?_⟩
  · have h' := Sigma.ι (fun n : ℕ ↦ X.obj n) n ≫= h
    simp only [ι_sequenceDifference_assoc, Preadditive.sub_comp, Category.assoc,
      comp_zero] at h'
    exact (sub_eq_zero.1 h').symm
  · simp [Preadditive.sub_comp, h n]

variable {X} in
/-- A morphism out of `∐ₙ Xₙ` killing `X.sequenceDifference` defines a cocone on `X` whose `n`-th
leg is `Sigma.ι _ n ≫ π`. -/
@[simps pt]
abbrev coconeOfSequenceDifference {Y : C} (π : (∐ fun n : ℕ ↦ X.obj n) ⟶ Y)
    (w : X.sequenceDifference ≫ π = 0) : Cocone X where
  pt := Y
  ι := NatTrans.ofSequence (fun n ↦ Sigma.ι _ n ≫ π) fun n ↦ by
    simp [(X.sequenceDifference_comp_eq_zero_iff π).1 w n]

@[simp]
lemma coconeOfSequenceDifference_ι_app {Y : C} (π : (∐ fun n : ℕ ↦ X.obj n) ⟶ Y)
    (w : X.sequenceDifference ≫ π = 0) (n : ℕ) :
    (coconeOfSequenceDifference π w).ι.app n = Sigma.ι (fun n : ℕ ↦ X.obj n) n ≫ π :=
  rfl

end SequenceDifference

/-- The coproduct–difference map is natural in morphisms of sequences `α : X ⟶ Y`. -/
@[reassoc]
lemma sequenceDifference_naturality {X Y : ℕ ⥤ C}
    [HasCoproduct fun n : ℕ ↦ X.obj n] [HasCoproduct fun n : ℕ ↦ Y.obj n] (α : X ⟶ Y) :
    X.sequenceDifference ≫ Limits.Sigma.map (fun n ↦ α.app n) =
      Limits.Sigma.map (fun n ↦ α.app n) ≫ Y.sequenceDifference :=
  Sigma.hom_ext _ _ fun n ↦ by
    simp [Preadditive.sub_comp, Preadditive.comp_sub, α.naturality_assoc]

end CategoryTheory.Functor

namespace TauCeti

section PreadditiveCofan

variable {C : Type u} [Category.{v} C] [Preadditive C] (G : C) (X : ℕ ⥤ C)

/-- Under `directSumEquivOfPreserves`, `telescopeDiff` corresponds to postcomposition with any
endomorphism `d` of a colimit cofan satisfying the coproduct–difference formula. -/
private lemma directSumEquivOfPreserves_telescopeDiff {c : Cofan fun n : ℕ ↦ X.obj n}
    (hc : IsColimit c)
    [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op G))]
    (d : c.pt ⟶ c.pt)
    (hd : ∀ n, c.inj n ≫ d = c.inj n - X.map (homOfLE (Nat.le_add_right n 1)) ≫ c.inj (n + 1))
    (x : ⨁ n : ℕ, (G ⟶ X.obj n)) :
    directSumEquivOfPreserves G hc
        (telescopeDiff
          (fun n ↦ Preadditive.rightComp G (X.map (homOfLE (Nat.le_add_right n 1)))) x) =
      directSumEquivOfPreserves G hc x ≫ d := by
  refine DirectSum.induction_on x (by simp) (fun n g ↦ ?_)
    fun _ _ hu hv ↦ by simp [map_add, hu, hv, Preadditive.add_comp]
  rw [telescopeDiff_of, map_sub, directSumEquivOfPreserves_of, directSumEquivOfPreserves_of,
    Category.assoc, hd n, Preadditive.comp_sub]
  simp [Preadditive.rightComp, Category.assoc]

private lemma postcomp_injective_of_cofan {c : Cofan fun n : ℕ ↦ X.obj n} (hc : IsColimit c)
    [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op G))]
    (d : c.pt ⟶ c.pt)
    (hd : ∀ n, c.inj n ≫ d = c.inj n - X.map (homOfLE (Nat.le_add_right n 1)) ≫ c.inj (n + 1)) :
    Function.Injective (fun f : G ⟶ c.pt ↦ f ≫ d) := fun f₁ f₂ hf ↦ by
  let e := directSumEquivOfPreserves G hc
  refine e.symm.injective <|
    telescopeDiff_injective
      (fun n ↦ Preadditive.rightComp G (X.map (homOfLE (Nat.le_add_right n 1)))) <|
      e.injective ?_
  simpa [directSumEquivOfPreserves_telescopeDiff G X hc d hd, e] using hf

private lemma telescopeDiff_rightComp_eq_of_le
    {x : ⨁ m : ℕ, (G ⟶ X.obj m)} {n : ℕ} {g : G ⟶ X.obj n}
    (hseq : telescopeDiff
      (fun m ↦ Preadditive.rightComp G (X.map (homOfLE (Nat.le_add_right m 1)))) x =
        DirectSum.of (fun m ↦ G ⟶ X.obj m) n g)
    {m : ℕ} (hnm : n ≤ m) : x m = g ≫ X.map (homOfLE hnm) := by
  induction hnm with
  | refl => simpa [Category.comp_id] using apply_eq_of_telescopeDiff_eq_of hseq
  | @step k hnk ih =>
    rw [apply_succ_eq_of_telescopeDiff_eq_of_ne hseq (by lia), ih]
    simp [Preadditive.rightComp, ← X.map_comp]

end PreadditiveCofan

section OpProductHelpers

section Category

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  (E : Cᵒᵖ ⥤ A) [PreservesLimitsOfShape (Discrete ℕ) E]

/-- Given a colimit cofan `c` in `C` and a functor `E : Cᵒᵖ ⥤ A` preserving `Discrete ℕ`-limits,
identify `E(c.pt)` with the categorical product `∏ᶜₙ E(Y n)`. -/
private def mapOpCofanIsoPi {Y : ℕ → C} {c : Cofan Y} (hc : IsColimit c)
    [HasProduct fun n : ℕ ↦ E.obj (op (Y n))] :
    E.obj (op c.pt) ≅ ∏ᶜ (fun n : ℕ ↦ E.obj (op (Y n))) :=
  have : HasCoproduct Y := HasColimit.mk ⟨c, hc⟩
  IsLimit.conePointUniqueUpToIso
    (isLimitFanMkObjOfIsLimit E (fun n ↦ op (Y n)) (fun n ↦ (c.inj n).op) (Cofan.IsColimit.op hc))
    (productIsProduct fun n : ℕ ↦ E.obj (op (Y n)))

@[reassoc (attr := simp)]
private lemma mapOpCofanIsoPi_hom_comp_π {Y : ℕ → C} {c : Cofan Y} (hc : IsColimit c)
    [HasProduct fun n : ℕ ↦ E.obj (op (Y n))] (n : ℕ) :
    (mapOpCofanIsoPi E hc).hom ≫ Pi.π (fun n : ℕ ↦ E.obj (op (Y n))) n = E.map (c.inj n).op :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk n)

/-- The canonical isomorphism `E(∐ₙ Xₙ) ≅ ∏ᶜₙ (X.op ⋙ E)(op n)` for a functor `E : Cᵒᵖ ⥤ A`
preserving countable products. -/
private def coprodIsoPi (X : ℕ ⥤ C) [HasCoproduct fun n : ℕ ↦ X.obj n]
    [HasProduct fun n : ℕ ↦ (X.op ⋙ E).obj (op n)] :
    E.obj (op (∐ fun n : ℕ ↦ X.obj n)) ≅ ∏ᶜ (fun n : ℕ ↦ (X.op ⋙ E).obj (op n)) :=
  have : HasProduct fun n : ℕ ↦ E.obj (op (X.obj n)) := ‹_›
  mapOpCofanIsoPi E (coproductIsCoproduct fun n : ℕ ↦ X.obj n)

@[reassoc]
private lemma coprodIsoPi_hom_comp_π (X : ℕ ⥤ C) [HasCoproduct fun n : ℕ ↦ X.obj n]
    [HasProduct fun n : ℕ ↦ (X.op ⋙ E).obj (op n)] (n : ℕ) :
    (coprodIsoPi E X).hom ≫ Pi.π (fun n : ℕ ↦ (X.op ⋙ E).obj (op n)) n =
      E.map (Sigma.ι (fun n : ℕ ↦ X.obj n) n).op :=
  have : HasProduct fun n : ℕ ↦ E.obj (op (X.obj n)) := ‹_›
  mapOpCofanIsoPi_hom_comp_π E (coproductIsCoproduct fun n : ℕ ↦ X.obj n) n

section Shift

variable [HasShift C ℤ]

/-- The canonical isomorphism `E((∐ₙ Xₙ)⟦1⟧) ≅ ∏ᶜₙ ((X ⋙ shiftFunctor C 1).op ⋙ E)(op n)` for
a functor `E : Cᵒᵖ ⥤ A` preserving countable products. -/
private def shiftCoprodIsoPi (X : ℕ ⥤ C) [HasCoproduct fun n : ℕ ↦ X.obj n]
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)] :
    E.obj (op ((∐ fun n : ℕ ↦ X.obj n)⟦(1 : ℤ)⟧)) ≅
      ∏ᶜ (fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)) :=
  have : HasProduct fun n : ℕ ↦ E.obj (op ((X.obj n)⟦(1 : ℤ)⟧)) := ‹_›
  mapOpCofanIsoPi E
    (isColimitOfHasCoproductOfPreservesColimit (shiftFunctor C (1 : ℤ)) (fun n : ℕ ↦ X.obj n))

@[reassoc]
private lemma shiftCoprodIsoPi_hom_comp_π (X : ℕ ⥤ C) [HasCoproduct fun n : ℕ ↦ X.obj n]
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)] (n : ℕ) :
    (shiftCoprodIsoPi E X).hom ≫
        Pi.π (fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)) n =
      E.map ((Sigma.ι (fun n : ℕ ↦ X.obj n) n)⟦(1 : ℤ)⟧').op :=
  have : HasProduct fun n : ℕ ↦ E.obj (op ((X.obj n)⟦(1 : ℤ)⟧)) := ‹_›
  mapOpCofanIsoPi_hom_comp_π E
    (isColimitOfHasCoproductOfPreservesColimit (shiftFunctor C (1 : ℤ)) (fun n : ℕ ↦ X.obj n)) n

private lemma shiftCoprodIsoPi_inv_naturality
    {X Y : ℕ ⥤ C} [HasCoproduct fun n : ℕ ↦ X.obj n] [HasCoproduct fun n : ℕ ↦ Y.obj n]
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)]
    [HasProduct fun n : ℕ ↦ ((Y ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)]
    (α : X ⟶ Y) :
    (shiftCoprodIsoPi E Y).inv ≫ E.map ((Limits.Sigma.map fun n ↦ α.app n)⟦(1 : ℤ)⟧').op =
      Limits.Pi.map
        (f := fun n ↦ ((Y ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n))
        (g := fun n ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n))
        (fun n ↦ E.map ((α.app n)⟦(1 : ℤ)⟧').op) ≫ (shiftCoprodIsoPi E X).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine Pi.hom_ext _ _ fun n ↦ ?_
  have hY := shiftCoprodIsoPi_hom_comp_π E Y n =≫ E.map ((α.app n)⟦(1 : ℤ)⟧').op
  simp only [Category.assoc] at hY
  simp only [Category.assoc, Pi.map_π, shiftCoprodIsoPi_hom_comp_π, hY]
  rw [← E.map_comp, ← E.map_comp, ← op_comp, ← op_comp]
  congr 2; rw [← Functor.map_comp, ← Functor.map_comp, Limits.Sigma.ι_map]

end Shift

end Category

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {A : Type u'} [Category.{v'} A] [Preadditive A]
  (E : Cᵒᵖ ⥤ A) [E.Additive] [PreservesLimitsOfShape (Discrete ℕ) E]
  (X : ℕ ⥤ C) [HasCoproduct fun n : ℕ ↦ X.obj n]

@[reassoc]
private lemma map_sequenceDifference_comp_coprodIsoPi
    [HasProduct fun n : ℕ ↦ (X.op ⋙ E).obj (op n)] :
    E.map X.sequenceDifference.op ≫ (coprodIsoPi E X).hom =
      (coprodIsoPi E X).hom ≫ (X.op ⋙ E).towerDifference := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  rw [Category.assoc, Category.assoc, Functor.towerDifference_π, Preadditive.comp_sub,
    coprodIsoPi_hom_comp_π, ← Category.assoc (coprodIsoPi E X).hom,
    coprodIsoPi_hom_comp_π, ← E.map_comp, ← op_comp, Functor.ι_sequenceDifference, op_sub,
    E.map_sub, op_comp, E.map_comp]
  rfl

@[reassoc]
private lemma map_shift_sequenceDifference_comp_shiftCoprodIsoPi [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)] :
    E.map (X.sequenceDifference⟦(1 : ℤ)⟧').op ≫ (shiftCoprodIsoPi E X).hom =
      (shiftCoprodIsoPi E X).hom ≫ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  rw [Category.assoc, Category.assoc, Functor.towerDifference_π, Preadditive.comp_sub,
    shiftCoprodIsoPi_hom_comp_π, ← Category.assoc (shiftCoprodIsoPi E X).hom,
    shiftCoprodIsoPi_hom_comp_π, ← E.map_comp, ← op_comp, ← Functor.map_comp,
    Functor.ι_sequenceDifference, Functor.map_sub, Functor.map_comp, op_sub, E.map_sub,
    op_comp, E.map_comp]
  rfl

@[reassoc]
private lemma towerDifference_comp_shiftCoprodIsoPi_inv [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)] :
    ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference ≫ (shiftCoprodIsoPi E X).inv =
      (shiftCoprodIsoPi E X).inv ≫ E.map (X.sequenceDifference⟦(1 : ℤ)⟧').op := by
  rw [Iso.comp_inv_eq, Category.assoc, map_shift_sequenceDifference_comp_shiftCoprodIsoPi,
    Iso.inv_hom_id_assoc]

end Preadditive

end OpProductHelpers

section HomotopyColimit

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A **homotopy colimit** (or Milnor telescope) of a sequence `X : ℕ ⥤ C` in a pretriangulated
category: a choice of distinguished triangle
`∐ₙ Xₙ ⟶ ∐ₙ Xₙ ⟶ pt ⟶ (∐ₙ Xₙ)⟦1⟧` completing `X.sequenceDifference`. -/
structure HomotopyColimit (X : ℕ ⥤ C) [HasCoproduct fun n : ℕ ↦ X.obj n] where
  /-- The homotopy colimit object. -/
  pt : C
  /-- The projection `∐ₙ Xₙ ⟶ pt` from the countable coproduct of the terms. -/
  π : (∐ fun n : ℕ ↦ X.obj n) ⟶ pt
  /-- The connecting morphism `pt ⟶ (∐ₙ Xₙ)⟦1⟧`. -/
  δ : pt ⟶ (∐ fun n : ℕ ↦ X.obj n)⟦(1 : ℤ)⟧
  /-- The defining triangle `∐ₙ Xₙ ⟶ ∐ₙ Xₙ ⟶ pt ⟶ (∐ₙ Xₙ)⟦1⟧` is distinguished. -/
  distinguished : Triangle.mk X.sequenceDifference π δ ∈ distTriang C

namespace HomotopyColimit

/-- Every sequence with a countable coproduct admits a homotopy colimit. -/
theorem nonempty (X : ℕ ⥤ C) [HasCoproduct fun n : ℕ ↦ X.obj n] :
    Nonempty (HomotopyColimit X) :=
  let ⟨Z, π, δ, h⟩ := distinguished_cocone_triangle X.sequenceDifference
  ⟨⟨Z, π, δ, h⟩⟩

section Basic

variable {X : ℕ ⥤ C} [HasCoproduct fun n : ℕ ↦ X.obj n] (h : HomotopyColimit X)

/-- The defining distinguished triangle of a homotopy colimit. -/
abbrev triangle : Triangle C := Triangle.mk X.sequenceDifference h.π h.δ

lemma triangle_distinguished : h.triangle ∈ distTriang C := h.distinguished

@[reassoc (attr := simp)]
lemma sequenceDifference_comp_π : X.sequenceDifference ≫ h.π = 0 :=
  comp_distTriang_mor_zero₁₂ h.triangle h.distinguished

@[reassoc (attr := simp)]
lemma π_comp_δ : h.π ≫ h.δ = 0 :=
  comp_distTriang_mor_zero₂₃ h.triangle h.distinguished

@[reassoc (attr := simp)]
lemma δ_comp_shift_sequenceDifference : h.δ ≫ X.sequenceDifference⟦(1 : ℤ)⟧' = 0 :=
  comp_distTriang_mor_zero₃₁ h.triangle h.distinguished

/-- The canonical morphism `X.obj n ⟶ h.pt` from the `n`-th term into the homotopy colimit. -/
def ι (n : ℕ) : X.obj n ⟶ h.pt := Sigma.ι (fun n : ℕ ↦ X.obj n) n ≫ h.π

lemma ι_def (n : ℕ) : h.ι n = Sigma.ι (fun n : ℕ ↦ X.obj n) n ≫ h.π :=
  (rfl)

/-- The canonical cocone on `X` with apex `h.pt` and legs `h.ι n`. -/
abbrev cocone : Cocone X :=
  Functor.coconeOfSequenceDifference h.π h.sequenceDifference_comp_π

lemma cocone_ι_app (n : ℕ) : h.cocone.ι.app n = h.ι n := by rfl

@[reassoc (attr := simp)]
lemma map_comp_ι {m n : ℕ} (f : m ⟶ n) : X.map f ≫ h.ι n = h.ι m := h.cocone.w f

@[reassoc]
lemma map_homOfLE_comp_ι {m n : ℕ} (hmn : m ≤ n) : X.map (homOfLE hmn) ≫ h.ι n = h.ι m :=
  h.map_comp_ι (homOfLE hmn)

/-- A homotopy colimit of a sequence whose terms satisfy `P` again satisfies `P`, whenever `P` is
isomorphism-closed, closed under countable coproducts, and closed under cones. -/
theorem prop_pt {P : ObjectProperty C} [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] [P.IsTriangulatedClosed₃]
    (hX : ∀ n, P (X.obj n)) : P h.pt :=
  have hSigma : P (∐ fun n : ℕ ↦ X.obj n) := P.prop_colimit _ fun ⟨n⟩ ↦ hX n
  P.ext_of_isTriangulatedClosed₃ h.triangle h.distinguished hSigma hSigma

end Basic

/-- Weak functoriality of homotopy colimits: any morphism of sequences `α : X ⟶ Y` induces a
morphism of their defining triangles. -/
theorem exists_hom {X Y : ℕ ⥤ C} [HasCoproduct fun n : ℕ ↦ X.obj n]
    [HasCoproduct fun n : ℕ ↦ Y.obj n] (hX : HomotopyColimit X) (hY : HomotopyColimit Y)
    (α : X ⟶ Y) :
    ∃ f : hX.pt ⟶ hY.pt,
      hX.π ≫ f = Limits.Sigma.map (fun n ↦ α.app n) ≫ hY.π ∧
        hX.δ ≫ (Limits.Sigma.map (fun n ↦ α.app n))⟦(1 : ℤ)⟧' = f ≫ hY.δ :=
  complete_distinguished_triangle_morphism hX.triangle hY.triangle
    hX.distinguished hY.distinguished
    (Limits.Sigma.map fun n ↦ α.app n) (Limits.Sigma.map fun n ↦ α.app n)
    (Functor.sequenceDifference_naturality α)

section Compact

variable {X : ℕ ⥤ C} [HasCoproduct fun n : ℕ ↦ X.obj n] (h : HomotopyColimit X)
  {G : C} [PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op G))]

/-- Every morphism from an object whose additive represented functor preserves countable coproducts
into a homotopy colimit kills the connecting morphism `h.δ`. -/
theorem comp_δ_eq_zero (f : G ⟶ h.pt) : f ≫ h.δ = 0 := by
  let hc := isColimitOfHasCoproductOfPreservesColimit (shiftFunctor C (1 : ℤ))
    (fun n : ℕ ↦ X.obj n)
  refine postcomp_injective_of_cofan G (X ⋙ shiftFunctor C (1 : ℤ)) hc
    (X.sequenceDifference⟦(1 : ℤ)⟧') (fun n ↦ ?_) (by simp [Category.assoc])
  simp only [cofan_mk_inj, Functor.comp_map, ← Functor.map_comp, Functor.ι_sequenceDifference,
    Functor.map_sub]

/-- Every morphism from an object whose additive represented functor preserves countable coproducts
into a homotopy colimit lifts along `h.π : ∐ₙ Xₙ ⟶ h.pt`. -/
theorem exists_comp_π_eq (f : G ⟶ h.pt) : ∃ k : G ⟶ (∐ fun n : ℕ ↦ X.obj n), k ≫ h.π = f :=
  (Triangle.exists_comp_mor₂_eq_iff h.distinguished f).2 (h.comp_δ_eq_zero f)

/-- Every morphism from an object whose additive represented functor preserves countable coproducts
into a homotopy colimit factors through some stage `h.ι N`. -/
theorem exists_eq_comp_ι (f : G ⟶ h.pt) : ∃ (N : ℕ) (g : G ⟶ X.obj N), f = g ≫ h.ι N := by
  classical
  obtain ⟨k, rfl⟩ := h.exists_comp_π_eq f
  let e := directSumEquivOfPreserves G (coproductIsCoproduct fun n : ℕ ↦ X.obj n)
  let x := e.symm k
  let N := x.support.sup id
  refine ⟨N, ∑ n ∈ x.support, if hle : n ≤ N then x n ≫ X.map (homOfLE hle) else 0, ?_⟩
  have hk : k = ∑ n ∈ x.support, x n ≫ Sigma.ι (fun n : ℕ ↦ X.obj n) n := by
    rw [← e.apply_symm_apply k, ← DirectSum.sum_support_of (e.symm k), map_sum]
    exact Finset.sum_congr rfl fun n _ ↦ directSumEquivOfPreserves_of G _ n (x n)
  rw [hk, Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hle : n ≤ N := Finset.le_sup (f := id) hn
  rw [dite_eq_left hle, Category.assoc, Category.assoc, h.map_homOfLE_comp_ι hle, h.ι_def]

/-- For an object `G` whose additive represented functor preserves countable coproducts, a morphism
`g : G ⟶ X.obj n` vanishes in `h.pt` if and only if it already vanishes at some later stage
`m ≥ n`. -/
theorem comp_ι_eq_zero_iff {n : ℕ} (g : G ⟶ X.obj n) :
    g ≫ h.ι n = 0 ↔ ∃ (m : ℕ) (hnm : n ≤ m), g ≫ X.map (homOfLE hnm) = 0 := by
  classical
  refine ⟨fun hg ↦ ?_, fun ⟨_, hnm, hm⟩ ↦ by
    rw [← h.map_homOfLE_comp_ι hnm, ← Category.assoc, hm, zero_comp]⟩
  obtain ⟨k, hk⟩ := h.triangle.coyoneda_exact₂ h.distinguished
    (g ≫ Sigma.ι (fun n : ℕ ↦ X.obj n) n) (by simpa [h.ι_def] using hg)
  let e := directSumEquivOfPreserves G (coproductIsCoproduct fun n : ℕ ↦ X.obj n)
  let x := e.symm k
  have hseq :
      telescopeDiff
          (fun m ↦ Preadditive.rightComp G (X.map (homOfLE (Nat.le_add_right m 1)))) x =
        DirectSum.of (fun n ↦ G ⟶ X.obj n) n g := e.injective <| by
    rw [directSumEquivOfPreserves_telescopeDiff G X (coproductIsCoproduct _)
      X.sequenceDifference X.ι_sequenceDifference, e.apply_symm_apply,
      directSumEquivOfPreserves_of]
    exact hk.symm
  let m := max n (x.support.sup id + 1)
  have hm_not : m ∉ x.support := fun hm ↦ by
    have : m ≤ x.support.sup id := Finset.le_sup (f := id) hm
    have : x.support.sup id + 1 ≤ m := le_max_right _ _
    lia
  exact ⟨m, le_max_left _ _,
    (telescopeDiff_rightComp_eq_of_le G X hseq (le_max_left _ _)).symm.trans
      (DFinsupp.notMem_support_iff.1 hm_not)⟩

end Compact

section Milnor

section Maps

variable {A : Type u'} [Category.{v'} A] [Preadditive A]
  {X : ℕ ⥤ C} [HasCoproduct fun n : ℕ ↦ X.obj n] (h : HomotopyColimit X)
  (E : Cᵒᵖ ⥤ A) [E.Additive] [PreservesLimitsOfShape (Discrete ℕ) E]

/-- The edge map `E(h.pt) ⟶ kernel (X.op ⋙ E).towerDifference` in the Milnor short exact
sequence of a homotopy colimit. -/
def milnorToLim [HasProduct fun n : ℕ ↦ (X.op ⋙ E).obj (op n)]
    [HasKernel (X.op ⋙ E).towerDifference] :
    E.obj (op h.pt) ⟶ kernel (X.op ⋙ E).towerDifference :=
  kernel.lift (X.op ⋙ E).towerDifference (E.map h.π.op ≫ (coprodIsoPi E X).hom) <| by
    rw [Category.assoc, ← map_sequenceDifference_comp_coprodIsoPi, ← E.map_comp_assoc,
      ← op_comp, h.sequenceDifference_comp_π, op_zero, E.map_zero, zero_comp]

@[reassoc]
private lemma milnorToLim_comp_kernel_ι [HasProduct fun n : ℕ ↦ (X.op ⋙ E).obj (op n)]
    [HasKernel (X.op ⋙ E).towerDifference] :
    h.milnorToLim E ≫ kernel.ι (X.op ⋙ E).towerDifference =
      E.map h.π.op ≫ (coprodIsoPi E X).hom :=
  kernel.lift_ι _ _ _

@[reassoc]
lemma milnorToLim_comp_kernel_ι_comp_π [HasProduct fun n : ℕ ↦ (X.op ⋙ E).obj (op n)]
    [HasKernel (X.op ⋙ E).towerDifference] (n : ℕ) :
    h.milnorToLim E ≫ kernel.ι (X.op ⋙ E).towerDifference ≫
        Pi.π (fun n : ℕ ↦ (X.op ⋙ E).obj (op n)) n =
      E.map (h.ι n).op := by
  rw [milnorToLim_comp_kernel_ι_assoc, coprodIsoPi_hom_comp_π, ← E.map_comp, ← op_comp]; rfl

/-- The `lim¹` map `cokernel ((X ⋙ shiftFunctor C 1).op ⋙ E).towerDifference ⟶ E(h.pt)` in the
Milnor short exact sequence of a homotopy colimit. -/
def milnorLimOneTo
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)]
    [HasCokernel ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference] :
    cokernel ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference ⟶ E.obj (op h.pt) :=
  cokernel.desc ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference
    ((shiftCoprodIsoPi E X).inv ≫ E.map h.δ.op) <| by
      rw [towerDifference_comp_shiftCoprodIsoPi_inv_assoc, ← E.map_comp, ← op_comp,
        h.δ_comp_shift_sequenceDifference, op_zero, E.map_zero, comp_zero]

@[reassoc]
private lemma cokernel_π_comp_milnorLimOneTo
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)]
    [HasCokernel ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference] :
    cokernel.π ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference ≫ h.milnorLimOneTo E =
      (shiftCoprodIsoPi E X).inv ≫ E.map h.δ.op :=
  cokernel.π_desc _ _ _

/-- Precomposing `h.milnorLimOneTo E` with `cokernel.π` and the canonical product comparison out of
`E((∐ₙ Xₙ)⟦1⟧)` recovers `E.map h.δ.op`. -/
@[reassoc]
lemma lift_cokernel_π_comp_milnorLimOneTo
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)]
    [HasCokernel ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference] :
    Pi.lift (f := fun n ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n))
        (fun n ↦ E.map ((Sigma.ι (fun n : ℕ ↦ X.obj n) n)⟦(1 : ℤ)⟧').op) ≫
      cokernel.π ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference ≫ h.milnorLimOneTo E =
      E.map h.δ.op := by
  have hhom : Pi.lift (f := fun n ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n))
      (fun n ↦ E.map ((Sigma.ι (fun n : ℕ ↦ X.obj n) n)⟦(1 : ℤ)⟧').op) =
      (shiftCoprodIsoPi E X).hom :=
    Pi.hom_ext _ _ fun n ↦ by rw [limit.lift_π, Fan.mk_π_app, shiftCoprodIsoPi_hom_comp_π]
  rw [hhom, cokernel_π_comp_milnorLimOneTo, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma milnorLimOneTo_comp_milnorToLim
    [HasProduct fun n : ℕ ↦ (X.op ⋙ E).obj (op n)] [HasKernel (X.op ⋙ E).towerDifference]
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)]
    [HasCokernel ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference] :
    h.milnorLimOneTo E ≫ h.milnorToLim E = 0 := by
  rw [← cancel_epi (cokernel.π ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference),
    ← cancel_mono (kernel.ι (X.op ⋙ E).towerDifference),
    comp_zero, zero_comp, Category.assoc, Category.assoc, milnorToLim_comp_kernel_ι,
    cokernel_π_comp_milnorLimOneTo_assoc, ← E.map_comp_assoc, ← op_comp,
    h.π_comp_δ, op_zero, E.map_zero, zero_comp, comp_zero]

/-- The Milnor short complex `cokernel d₁ ⟶ E(h.pt) ⟶ kernel d₀` attached to a homotopy colimit
`h` and an additive functor `E : Cᵒᵖ ⥤ A` preserving countable products. -/
abbrev milnorShortComplex
    [HasProduct fun n : ℕ ↦ (X.op ⋙ E).obj (op n)] [HasKernel (X.op ⋙ E).towerDifference]
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)]
    [HasCokernel ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference] :
    ShortComplex A :=
  ShortComplex.mk (h.milnorLimOneTo E) (h.milnorToLim E) (h.milnorLimOneTo_comp_milnorToLim E)

/-- Naturality of `milnorToLim` with respect to a morphism `f : hX.pt ⟶ hY.pt` compatible with a
morphism of sequences `α : X ⟶ Y`. -/
@[reassoc]
lemma milnorToLim_naturality {X Y : ℕ ⥤ C}
    [HasCoproduct fun n : ℕ ↦ X.obj n] [HasCoproduct fun n : ℕ ↦ Y.obj n]
    (hX : HomotopyColimit X) (hY : HomotopyColimit Y)
    (E : Cᵒᵖ ⥤ A) [E.Additive] [PreservesLimitsOfShape (Discrete ℕ) E]
    [HasProduct fun n : ℕ ↦ (X.op ⋙ E).obj (op n)]
    [HasProduct fun n : ℕ ↦ (Y.op ⋙ E).obj (op n)]
    [HasKernel (X.op ⋙ E).towerDifference] [HasKernel (Y.op ⋙ E).towerDifference]
    (α : X ⟶ Y) (f : hX.pt ⟶ hY.pt)
    (hf : hX.π ≫ f = Limits.Sigma.map (fun n ↦ α.app n) ≫ hY.π) :
    E.map f.op ≫ hX.milnorToLim E =
      hY.milnorToLim E ≫
        kernel.map (Y.op ⋙ E).towerDifference (X.op ⋙ E).towerDifference
          (Limits.Pi.map (f := fun n ↦ (Y.op ⋙ E).obj (op n))
            (g := fun n ↦ (X.op ⋙ E).obj (op n)) fun n ↦ E.map (α.app n).op)
          (Limits.Pi.map (f := fun n ↦ (Y.op ⋙ E).obj (op n))
            (g := fun n ↦ (X.op ⋙ E).obj (op n)) fun n ↦ E.map (α.app n).op)
          (Functor.towerDifference_naturality (Functor.whiskerRight (NatTrans.op α) E)) := by
  rw [← cancel_mono (kernel.ι (X.op ⋙ E).towerDifference)]
  refine Pi.hom_ext _ _ fun n ↦ ?_
  have hYcomp := hY.milnorToLim_comp_kernel_ι_comp_π E n =≫ E.map (α.app n).op
  simp only [Category.assoc] at hYcomp
  simp only [Category.assoc, milnorToLim_comp_kernel_ι_comp_π, kernel.lift_ι_assoc,
    Pi.map_π, hYcomp]
  rw [← E.map_comp, ← E.map_comp, ← op_comp, ← op_comp]
  congr 2; simpa [hX.ι_def, hY.ι_def, Category.assoc] using Sigma.ι (fun n : ℕ ↦ X.obj n) n ≫= hf

/-- Naturality of `milnorLimOneTo` with respect to a morphism `f : hX.pt ⟶ hY.pt` compatible with
the connecting morphisms over `α : X ⟶ Y`. -/
@[reassoc]
lemma milnorLimOneTo_naturality {X Y : ℕ ⥤ C}
    [HasCoproduct fun n : ℕ ↦ X.obj n] [HasCoproduct fun n : ℕ ↦ Y.obj n]
    (hX : HomotopyColimit X) (hY : HomotopyColimit Y)
    (E : Cᵒᵖ ⥤ A) [E.Additive] [PreservesLimitsOfShape (Discrete ℕ) E]
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)]
    [HasProduct fun n : ℕ ↦ ((Y ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)]
    [HasCokernel ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference]
    [HasCokernel ((Y ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference]
    (α : X ⟶ Y) (f : hX.pt ⟶ hY.pt)
    (hδ : hX.δ ≫ (Limits.Sigma.map (fun n ↦ α.app n))⟦(1 : ℤ)⟧' = f ≫ hY.δ) :
    hY.milnorLimOneTo E ≫ E.map f.op =
      cokernel.map ((Y ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference
          ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference
          (Limits.Pi.map (f := fun n ↦ ((Y ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n))
            (g := fun n ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n))
            fun n ↦ E.map ((α.app n)⟦(1 : ℤ)⟧').op)
          (Limits.Pi.map (f := fun n ↦ ((Y ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n))
            (g := fun n ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n))
            fun n ↦ E.map ((α.app n)⟦(1 : ℤ)⟧').op)
          (Functor.towerDifference_naturality
            (Functor.whiskerRight
              (NatTrans.op (Functor.whiskerRight α (shiftFunctor C (1 : ℤ)))) E)) ≫
        hX.milnorLimOneTo E := by
  rw [← cancel_epi (cokernel.π ((Y ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference)]
  simp only [cokernel_π_comp_milnorLimOneTo_assoc, cokernel.π_desc_assoc]
  rw [Category.assoc (Limits.Pi.map _), cokernel_π_comp_milnorLimOneTo,
    ← Category.assoc (Limits.Pi.map _), ← shiftCoprodIsoPi_inv_naturality E α, Category.assoc,
    ← E.map_comp, ← E.map_comp, ← op_comp, ← op_comp, hδ]

end Maps

section Exactness

variable {A : Type u'} [Category.{v'} A] [Abelian A]
  {X : ℕ ⥤ C} [HasCoproduct fun n : ℕ ↦ X.obj n] (h : HomotopyColimit X)
  (E : Cᵒᵖ ⥤ A) [E.IsHomological] [PreservesLimitsOfShape (Discrete ℕ) E]

private lemma milnor_exact₀ [HasProduct fun n : ℕ ↦ (X.op ⋙ E).obj (op n)] :
    (ShortComplex.mk (E.map h.π.op ≫ (coprodIsoPi E X).hom) (X.op ⋙ E).towerDifference <| by
      rw [Category.assoc, ← map_sequenceDifference_comp_coprodIsoPi, ← E.map_comp_assoc,
        ← op_comp, h.sequenceDifference_comp_π, op_zero, E.map_zero, zero_comp]).Exact := by
  refine ShortComplex.exact_of_iso ?_ (E.map_distinguished_op_exact h.triangle h.distinguished)
  exact ShortComplex.isoMk (Iso.refl _) (coprodIsoPi E X) (coprodIsoPi E X)
    (by dsimp [ShortComplex.op, shortComplexOfDistTriangle]; rw [Category.id_comp])
    (map_sequenceDifference_comp_coprodIsoPi E X).symm

private lemma milnor_exact₁
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)] :
    (ShortComplex.mk ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference
      ((shiftCoprodIsoPi E X).inv ≫ E.map h.δ.op) <| by
        rw [towerDifference_comp_shiftCoprodIsoPi_inv_assoc, ← E.map_comp, ← op_comp,
          h.δ_comp_shift_sequenceDifference, op_zero, E.map_zero, comp_zero]).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (E.map_distinguished_op_exact _ (rot_of_distTriang _ (rot_of_distTriang _ h.distinguished)))
  let e₁ := shiftCoprodIsoPi E X
  let negE₁ : E.obj (op ((∐ fun n : ℕ ↦ X.obj n)⟦(1 : ℤ)⟧)) ≅ _ :=
    ⟨-e₁.hom, -e₁.inv, by simp, by simp⟩
  refine ShortComplex.isoMk negE₁ e₁ (Iso.refl _) ?_
    (by
      dsimp [ShortComplex.op, shortComplexOfDistTriangle, Triangle.rotate, e₁]
      rw [Iso.hom_inv_id_assoc, Category.comp_id])
  dsimp [ShortComplex.op, shortComplexOfDistTriangle, Triangle.rotate, negE₁, e₁]
  rw [E.map_neg, Preadditive.neg_comp, Preadditive.neg_comp,
    map_shift_sequenceDifference_comp_shiftCoprodIsoPi]

private lemma milnor_exact₂
    [HasProduct fun n : ℕ ↦ (X.op ⋙ E).obj (op n)]
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)] :
    (ShortComplex.mk ((shiftCoprodIsoPi E X).inv ≫ E.map h.δ.op)
      (E.map h.π.op ≫ (coprodIsoPi E X).hom) <| by
        rw [Category.assoc, ← E.map_comp_assoc, ← op_comp, h.π_comp_δ, op_zero, E.map_zero,
          zero_comp, comp_zero]).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (E.map_distinguished_op_exact _ (rot_of_distTriang _ h.distinguished))
  exact ShortComplex.isoMk (shiftCoprodIsoPi E X) (Iso.refl _) (coprodIsoPi E X)
    (by
      dsimp [ShortComplex.op, shortComplexOfDistTriangle, Triangle.rotate]
      rw [Iso.hom_inv_id_assoc, Category.comp_id])
    (by
      dsimp [ShortComplex.op, shortComplexOfDistTriangle, Triangle.rotate]
      rw [Category.id_comp])

/-- **The Milnor short exact sequence** of a homotopy colimit `h` for any contravariant homological
functor `E : Cᵒᵖ ⥤ A` into an abelian category `A` that sends countable coproducts to countable
products:
`0 ⟶ cokernel d₁ ⟶ E(h.pt) ⟶ kernel d₀ ⟶ 0`. -/
theorem milnorShortComplex_shortExact
    [HasProduct fun n : ℕ ↦ (X.op ⋙ E).obj (op n)]
    [HasProduct fun n : ℕ ↦ ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).obj (op n)] :
    (h.milnorShortComplex E).ShortExact := by
  let d₀ := (X.op ⋙ E).towerDifference
  let d₁ := ((X ⋙ shiftFunctor C (1 : ℤ)).op ⋙ E).towerDifference
  let S₂ := ShortComplex.mk ((shiftCoprodIsoPi E X).inv ≫ E.map h.δ.op)
    (E.map h.π.op ≫ (coprodIsoPi E X).hom) (by
      rw [Category.assoc, ← E.map_comp_assoc, ← op_comp, h.π_comp_δ, op_zero, E.map_zero,
        zero_comp, comp_zero])
  let Smid := ShortComplex.mk (h.milnorLimOneTo E) (E.map h.π.op ≫ (coprodIsoPi E X).hom) (by
    rw [← cancel_epi (cokernel.π d₁), comp_zero, cokernel_π_comp_milnorLimOneTo_assoc,
      ← E.map_comp_assoc, ← op_comp, h.π_comp_δ, op_zero, E.map_zero, zero_comp, comp_zero])
  let φ₁ : S₂ ⟶ Smid := ShortComplex.homMk (cokernel.π d₁) (𝟙 _) (𝟙 _)
    (by dsimp [S₂, Smid, d₁]; simp [cokernel_π_comp_milnorLimOneTo]) (by dsimp [S₂, Smid]; simp)
  have : Epi φ₁.τ₁ := inferInstanceAs (Epi (cokernel.π d₁))
  have : IsIso φ₁.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono φ₁.τ₃ := inferInstanceAs (Mono (𝟙 _))
  let φ₂ : h.milnorShortComplex E ⟶ Smid := ShortComplex.homMk (𝟙 _) (𝟙 _) (kernel.ι d₀)
    (by dsimp [Smid]; simp) (by dsimp [Smid, d₀]; simp [milnorToLim_comp_kernel_ι])
  have : Epi φ₂.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso φ₂.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono φ₂.τ₃ := inferInstanceAs (Mono (kernel.ι d₀))
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₂).2 <|
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₁).1 (h.milnor_exact₂ E))
    (h.milnor_exact₁ E).mono_cokernelDesc (h.milnor_exact₀ E).epi_kernelLift

end Exactness

/-- For a contravariant homological functor `E : Cᵒᵖ ⥤ AddCommGrpCat.{u'}` preserving countable
products, every compatible family of elements in `E(Xₙ)` lifts to an element of `E(h.pt)`. -/
theorem exists_map_ι_eq {X : ℕ ⥤ C} [HasCoproduct fun n : ℕ ↦ X.obj n] (h : HomotopyColimit X)
    (E : Cᵒᵖ ⥤ AddCommGrpCat.{u'}) [E.IsHomological] [PreservesLimitsOfShape (Discrete ℕ) E]
    (x : ∀ n : ℕ, E.obj (op (X.obj n)))
    (hx : ∀ n : ℕ, E.map (X.map (homOfLE (Nat.le_add_right n 1))).op (x (n + 1)) = x n) :
    ∃ u : E.obj (op h.pt), ∀ n : ℕ, E.map (h.ι n).op u = x n := by
  let F : ℕ → AddCommGrpCat.{u'} := fun n ↦ (X.op ⋙ E).obj (op n)
  let pIso : (∏ᶜ F) ≅ AddCommGrpCat.of (∀ n, F n) :=
    IsLimit.conePointUniqueUpToIso (productIsProduct F)
      (AddCommGrpCat.HasLimit.productLimitCone F).isLimit
  have hpIso (n : ℕ) (z : (∏ᶜ F : AddCommGrpCat.{u'})) : pIso.hom z n = Pi.π F n z :=
    ConcreteCategory.congr_hom (IsLimit.conePointUniqueUpToIso_hom_comp (productIsProduct F)
      (AddCommGrpCat.HasLimit.productLimitCone F).isLimit ⟨n⟩) z
  have hpIso_inv (n : ℕ) (y : ∀ k, F k) : Pi.π F n (pIso.inv y) = y n := by
    rw [← hpIso n (pIso.inv y), ← ConcreteCategory.comp_apply, pIso.inv_hom_id]; rfl
  have hy : (X.op ⋙ E).towerDifference (pIso.inv x) = 0 := by
    apply (AddCommGrpCat.mono_iff_injective pIso.hom).1 inferInstance
    rw [map_zero]; ext n
    rw [hpIso n, ← ConcreteCategory.comp_apply, Functor.towerDifference_π]
    dsimp [F] at hpIso_inv hx ⊢
    rw [hpIso_inv, hpIso_inv, hx n, sub_self]; rfl
  let Sk := ShortComplex.mk (kernel.ι (X.op ⋙ E).towerDifference) (X.op ⋙ E).towerDifference
    (kernel.condition _)
  obtain ⟨k, hk⟩ := (ShortComplex.ab_exact_iff Sk).1
    (Sk.exact_of_f_is_kernel (kernelIsKernel _)) (pIso.inv x) hy
  have : Epi (h.milnorToLim E) := (h.milnorShortComplex_shortExact E).epi_g
  obtain ⟨u, hu⟩ := (AddCommGrpCat.epi_iff_surjective (h.milnorToLim E)).1 inferInstance k
  exact ⟨u, fun n ↦ by rw [← h.milnorToLim_comp_kernel_ι_comp_π E n, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, hu, hk, hpIso_inv]⟩

end Milnor

end HomotopyColimit

end HomotopyColimit

end TauCeti

end
