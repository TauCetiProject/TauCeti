/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homology.Basic
public import TauCeti.CategoryTheory.ComposableArrows.Postcomp

import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic

/-!
# Low-degree category homology, acyclicity of terminal objects, and concrete computations

This file establishes the fundamental low-degree and acyclicity properties of the category chain
complex `TauCeti.categoryChainComplex C M` and category homology `TauCeti.categoryHomology C M n`:

1. **Degree-zero homology as colimit.** For any cocone `c` on `M : C ⥤ A`, the map
   `TauCeti.categoryChainComplex.desc₀ c : (categoryChainComplex C M).X 0 ⟶ c.pt` vanishes on
   `d 1 0`, and when `c` is a colimit cocone it exhibits `c.pt` as the cokernel of `d 1 0`.
   Consequently `TauCeti.categoryHomology₀IsoOfIsColimit` identifies `H₀(C, M)` with `c.pt`,
   yielding the isomorphism `TauCeti.categoryHomology₀Iso C M : categoryHomology C M 0 ≅ colimit M`
   and the natural isomorphism `TauCeti.categoryHomology₀NatIso C A : categoryHomologyFunctor C A 0
   ≅ colim`.

2. **Connected categories with constant coefficients.** When `C` is connected, the constant
   coefficient functor `(Functor.const C).obj X` has `H₀(C, const X) ≅ X`
   (`TauCeti.categoryHomology₀ConstIsoOfIsConnected`).

3. **Categories with a terminal object.** Given `ht : IsTerminal t`, appending `ht.from σ.right` via
   `CategoryTheory.ComposableArrows.postcomp` defines an explicit contracting chain homotopy on
   `categoryChainComplex C M`, producing the chain homotopy equivalence
   `TauCeti.categoryChainComplexTerminalHomotopyEquiv ht M` with `(ChainComplex.single₀ A).obj
   (M.obj t)`. Hence `H₀(C, M) ≅ M.obj t` (`TauCeti.categoryHomology₀IsoOfIsTerminal`) and
   `IsZero (categoryHomology C M (n + 1))` for all `n`
   (`TauCeti.isZero_categoryHomology_succ_of_isTerminal`).

4. **Comparison of degree-two homology and cohomology for `ℤ/2ℤ`.** For the one-object category
   `SingleObj (Multiplicative (ZMod 2))` with constant integral coefficients `ModuleCat.of ℤ ℤ`,
   `H₂` vanishes (`TauCeti.isZero_categoryHomology_singleObj_zmod_two_int_two`), whereas the
   degree-two group cohomology `groupCohomology (Rep.trivial ℤ (Multiplicative (ZMod 2)) ℤ) 2` is
   isomorphic to `ModuleCat.of ℤ (ZMod 2)` (`TauCeti.groupCohomologyTrivialZModTwoIntTwoIso`) and
   is therefore nonzero (`TauCeti.not_isZero_groupCohomology_trivial_zmod_two_int_two`).

## Main declarations

* `TauCeti.categoryHomology₀IsoOfIsColimit`, `TauCeti.categoryHomology₀Iso`,
  `TauCeti.categoryHomology₀NatIso`: `H₀(C, M) ≅ colim M`, naturally in `M` and compatible with
  precomposition.
* `TauCeti.categoryHomology₀ConstIsoOfIsConnected`: `H₀(C, const X) ≅ X` for connected `C`.
* `TauCeti.categoryChainComplexTerminalHomotopyEquiv`,
  `TauCeti.categoryHomology₀IsoOfIsTerminal`,
  `TauCeti.isZero_categoryHomology_succ_of_isTerminal`: chain contraction and vanishing higher
  homology when `C` has a terminal object.
* `TauCeti.isZero_categoryHomology_singleObj_zmod_two_int_two`,
  `TauCeti.groupCohomologyTrivialZModTwoIntTwoIso`,
  `TauCeti.not_isZero_groupCohomology_trivial_zmod_two_int_two`: `H₂(B(ℤ/2ℤ), ℤ) = 0` versus
  `H²(ℤ/2ℤ, ℤ) ≅ ℤ/2ℤ`.

## References

* [Daniel Quillen, *Higher algebraic K-theory: I*][quillen1973], §1.
* [Charles A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*][weibel2013],
  Chapter IV, §3.5.
-/

public noncomputable section

open CategoryTheory Limits Opposite

open scoped Simplicial

universe v₁ u₁ v₂ u₂ v u

namespace TauCeti

/-! ### Degree-zero category homology as a colimit -/

section DegreeZero

variable {C : Type u₁} [Category.{v₁} C] {A : Type u} [Category.{v} A]
  [HasCoproducts.{max u₁ v₁} A] [Preadditive A]

namespace categoryChainComplex

/-- The morphism `(categoryChainComplex C M).X 0 ⟶ c.pt` induced on `0`-chains by a cocone `c` on
`M : C ⥤ A`. -/
def desc₀ {M : C ⥤ A} (c : Cocone M) : (categoryChainComplex C M).X 0 ⟶ c.pt :=
  (isColimitXCofan M 0).desc (Cofan.mk c.pt fun σ ↦ c.ι.app (σ.obj 0))

@[reassoc (attr := simp)]
lemma ι_desc₀ {M : C ⥤ A} (c : Cocone M) (σ : ComposableArrows C 0) :
    ι M σ ≫ desc₀ c = c.ι.app (σ.obj 0) :=
  (isColimitXCofan M 0).fac (Cofan.mk c.pt fun σ ↦ c.ι.app (σ.obj 0)) ⟨σ⟩

@[reassoc (attr := simp)]
lemma ι₀_desc₀ {M : C ⥤ A} (c : Cocone M) (x : C) :
    ι₀ M x ≫ desc₀ c = c.ι.app x :=
  ι_desc₀ c (ComposableArrows.mk₀ x)

@[reassoc (attr := simp)]
lemma d_desc₀ {M : C ⥤ A} (c : Cocone M) (n : ℕ) :
    (categoryChainComplex C M).d n 0 ≫ desc₀ c = 0 := by
  by_cases hn : n = 1
  · subst hn
    ext σ
    obtain ⟨x, y, f, rfl⟩ := ComposableArrows.mk₁_surjective σ
    rw [ι_mk₁, ι₁_d_one_zero_assoc, Preadditive.sub_comp, Category.assoc, ι₀_desc₀, ι₀_desc₀,
      c.w f, sub_self, comp_zero]
  · rw [HomologicalComplex.shape _ _ _ (by simp; lia), zero_comp]

/-- Any morphism out of `(categoryChainComplex C M).X 0` vanishing on `d 1 0` assembles into a
cocone on `M`. -/
@[expose, simps]
def coconeOfCompDZero {M : C ⥤ A} {T : A} (g : (categoryChainComplex C M).X 0 ⟶ T)
    (hg : (categoryChainComplex C M).d 1 0 ≫ g = 0) : Cocone M where
  pt := T
  ι :=
    { app x := ι₀ M x ≫ g
      naturality {x y} f := by
        dsimp
        rw [Category.comp_id, ← sub_eq_zero, ← Category.assoc, ← Preadditive.sub_comp,
          ← ι₁_d_one_zero_assoc, hg, comp_zero] }

/-- When `c` is a colimit cocone on `M : C ⥤ A`, `desc₀ c` exhibits `c.pt` as the cokernel of
`(categoryChainComplex C M).d 1 0`. -/
def isColimitCokernelCoforkDOneZero {M : C ⥤ A} {c : Cocone M} (hc : IsColimit c) :
    IsColimit (CokernelCofork.ofπ (desc₀ c) (d_desc₀ c 1)) :=
  CokernelCofork.IsColimit.ofπ (desc₀ c) (d_desc₀ c 1)
    (fun g hg ↦ hc.desc (coconeOfCompDZero g hg))
    (fun g hg ↦ by
      ext σ
      obtain ⟨x, rfl⟩ := ComposableArrows.mk₀_surjective σ
      exact (Category.assoc (ι₀ M x) (desc₀ c) _).symm.trans
        ((congrArg (· ≫ _) (ι₀_desc₀ c x)).trans (hc.fac (coconeOfCompDZero g hg) x)))
    (fun g hg m hm ↦ hc.uniq (coconeOfCompDZero g hg) m fun x ↦
      ((congrArg (· ≫ m) (ι₀_desc₀ c x).symm).trans (Category.assoc _ _ _)).trans
        (congrArg (ι₀ M x ≫ ·) hm))

end categoryChainComplex

section HomologyZero

variable [CategoryWithHomology A]

/-- The canonical quotient projection `(categoryChainComplex C M).X 0 ⟶ categoryHomology C M 0`
from `0`-chains to degree-zero category homology. -/
def categoryHomology.π₀ (M : C ⥤ A) :
    (categoryChainComplex C M).X 0 ⟶ categoryHomology C M 0 :=
  (categoryChainComplex C M).pOpcycles 0 ≫
    (ChainComplex.isoHomologyι₀ (categoryChainComplex C M)).inv

instance (M : C ⥤ A) : Epi (categoryHomology.π₀ M) := by
  dsimp [categoryHomology.π₀]
  infer_instance

@[reassoc (attr := simp)]
lemma categoryHomology.d_comp_π₀ (M : C ⥤ A) (n : ℕ) :
    (categoryChainComplex C M).d n 0 ≫ categoryHomology.π₀ M = 0 := by
  dsimp [categoryHomology.π₀]
  rw [HomologicalComplex.d_pOpcycles_assoc, zero_comp]

@[reassoc (attr := simp)]
lemma categoryHomology.π₀_naturality {M N : C ⥤ A} (α : M ⟶ N) :
    categoryHomology.π₀ M ≫ categoryHomologyMap α 0 =
      (categoryChainComplexMap α).f 0 ≫ categoryHomology.π₀ N := by
  dsimp [categoryHomology.π₀, categoryHomologyMap]
  rw [Category.assoc, ChainComplex.isoHomologyι₀_inv_naturality,
    HomologicalComplex.p_opcyclesMap_assoc]

@[reassoc (attr := simp)]
lemma categoryHomology.π₀_precomp {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) :
    categoryHomology.π₀ (F ⋙ M) ≫ categoryHomologyPrecomp F M 0 =
      (categoryChainComplexPrecomp F M).f 0 ≫ categoryHomology.π₀ M := by
  dsimp [categoryHomology.π₀, categoryHomologyPrecomp]
  rw [Category.assoc, ChainComplex.isoHomologyι₀_inv_naturality,
    HomologicalComplex.p_opcyclesMap_assoc]

/-- Given a colimit cocone `c` on `M : C ⥤ A`, degree-zero category homology `categoryHomology C M
0` is canonically isomorphic to `c.pt`. -/
def categoryHomology₀IsoOfIsColimit {M : C ⥤ A} {c : Cocone M} (hc : IsColimit c) :
    categoryHomology C M 0 ≅ c.pt :=
  ChainComplex.isoHomologyι₀ (categoryChainComplex C M) ≪≫
    ((categoryChainComplex C M).opcyclesIsCokernel 1 0 (by simp)).coconePointUniqueUpToIso
      (categoryChainComplex.isColimitCokernelCoforkDOneZero hc)

@[reassoc (attr := simp)]
lemma π₀_categoryHomology₀IsoOfIsColimit_hom {M : C ⥤ A} {c : Cocone M} (hc : IsColimit c) :
    categoryHomology.π₀ M ≫ (categoryHomology₀IsoOfIsColimit hc).hom =
      categoryChainComplex.desc₀ c := by
  dsimp [categoryHomology.π₀, categoryHomology₀IsoOfIsColimit]
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    ((categoryChainComplex C M).opcyclesIsCokernel 1 0 (by simp))
    (categoryChainComplex.isColimitCokernelCoforkDOneZero hc) WalkingParallelPair.one

@[reassoc]
lemma ι₀_π₀_categoryHomology₀IsoOfIsColimit_hom {M : C ⥤ A} {c : Cocone M} (hc : IsColimit c)
    (x : C) :
    categoryChainComplex.ι₀ M x ≫ categoryHomology.π₀ M ≫
        (categoryHomology₀IsoOfIsColimit hc).hom =
      c.ι.app x := by
  rw [π₀_categoryHomology₀IsoOfIsColimit_hom, categoryChainComplex.ι₀_desc₀]

@[reassoc (attr := simp)]
lemma ι_categoryHomology₀IsoOfIsColimit_inv {M : C ⥤ A} {c : Cocone M} (hc : IsColimit c)
    (x : C) :
    c.ι.app x ≫ (categoryHomology₀IsoOfIsColimit hc).inv =
      categoryChainComplex.ι₀ M x ≫ categoryHomology.π₀ M := by
  rw [← cancel_mono (categoryHomology₀IsoOfIsColimit hc).hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ι₀_π₀_categoryHomology₀IsoOfIsColimit_hom]

variable (C) in
/-- Degree-zero category homology `H₀(C, M)` is naturally isomorphic to `colimit M`. -/
@[expose]
def categoryHomology₀Iso (M : C ⥤ A) [HasColimit M] :
    categoryHomology C M 0 ≅ colimit M :=
  categoryHomology₀IsoOfIsColimit (colimit.isColimit M)

@[reassoc (attr := simp)]
lemma π₀_categoryHomology₀Iso_hom (M : C ⥤ A) [HasColimit M] :
    categoryHomology.π₀ M ≫ (categoryHomology₀Iso C M).hom =
      categoryChainComplex.desc₀ (colimit.cocone M) :=
  π₀_categoryHomology₀IsoOfIsColimit_hom (colimit.isColimit M)

@[reassoc]
lemma ι₀_π₀_categoryHomology₀Iso_hom (M : C ⥤ A) [HasColimit M] (x : C) :
    categoryChainComplex.ι₀ M x ≫ categoryHomology.π₀ M ≫ (categoryHomology₀Iso C M).hom =
      colimit.ι M x :=
  ι₀_π₀_categoryHomology₀IsoOfIsColimit_hom (colimit.isColimit M) x

@[reassoc (attr := simp)]
lemma colimit_ι_categoryHomology₀Iso_inv (M : C ⥤ A) [HasColimit M] (x : C) :
    colimit.ι M x ≫ (categoryHomology₀Iso C M).inv =
      categoryChainComplex.ι₀ M x ≫ categoryHomology.π₀ M :=
  ι_categoryHomology₀IsoOfIsColimit_inv (colimit.isColimit M) x

@[reassoc]
lemma categoryHomology₀Iso_naturality {M N : C ⥤ A} [HasColimit M] [HasColimit N] (α : M ⟶ N) :
    categoryHomologyMap α 0 ≫ (categoryHomology₀Iso C N).hom =
      (categoryHomology₀Iso C M).hom ≫ colimMap α := by
  rw [← cancel_epi (categoryHomology.π₀ M), categoryHomology.π₀_naturality_assoc,
    π₀_categoryHomology₀Iso_hom, π₀_categoryHomology₀Iso_hom_assoc]
  ext σ
  rw [categoryChainComplex.ι_map_f_assoc, categoryChainComplex.ι_desc₀,
    categoryChainComplex.ι_desc₀_assoc]
  exact (ι_colimMap α (σ.obj 0)).symm

/-- Compatibility of `categoryHomology₀Iso` with functoriality in the indexing category via
`colimit.pre`. -/
@[reassoc]
lemma categoryHomology₀Iso_precomp {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) [HasColimit (F ⋙ M)] [HasColimit M] :
    categoryHomologyPrecomp F M 0 ≫ (categoryHomology₀Iso D M).hom =
      (categoryHomology₀Iso C (F ⋙ M)).hom ≫ colimit.pre M F := by
  rw [← cancel_epi (categoryHomology.π₀ (F ⋙ M)), categoryHomology.π₀_precomp_assoc,
    π₀_categoryHomology₀Iso_hom, π₀_categoryHomology₀Iso_hom_assoc]
  ext σ
  refine ((categoryChainComplex.ι_precomp_f_assoc F M σ _).trans
    (categoryChainComplex.ι_desc₀ (colimit.cocone M) _)).trans ?_
  exact (colimit.ι_pre M F (σ.obj 0)).symm.trans
    (categoryChainComplex.ι_desc₀_assoc (colimit.cocone (F ⋙ M)) σ (colimit.pre M F)).symm

variable (C A) in
/-- When `A` has colimits of shape `C`, degree-zero category homology `categoryHomologyFunctor C A
0` is naturally isomorphic to `colim : (C ⥤ A) ⥤ A`. -/
@[expose, simps!]
def categoryHomology₀NatIso [HasColimitsOfShape C A] :
    categoryHomologyFunctor C A 0 ≅ colim :=
  NatIso.ofComponents (fun M ↦ categoryHomology₀Iso C M) fun α ↦
    categoryHomology₀Iso_naturality α

end HomologyZero

end DegreeZero

/-! ### Connected categories with constant coefficients -/

section Connected

variable (C : Type u₁) [Category.{v₁} C] [IsConnected C] {A : Type u} [Category.{v} A]
  [HasCoproducts.{max u₁ v₁} A] [Preadditive A] [CategoryWithHomology A]

/-- For a connected category `C` and an object `X : A`, degree-zero category homology with constant
coefficients `X` is canonically isomorphic to `X`. -/
@[expose]
def categoryHomology₀ConstIsoOfIsConnected (X : A) :
    categoryHomology C ((Functor.const C).obj X) 0 ≅ X :=
  categoryHomology₀IsoOfIsColimit (isColimitConstCocone C X)

@[reassoc (attr := simp)]
lemma ι₀_π₀_categoryHomology₀ConstIsoOfIsConnected_hom (X : A) (x : C) :
    categoryChainComplex.ι₀ ((Functor.const C).obj X) x ≫
        categoryHomology.π₀ ((Functor.const C).obj X) ≫
          (categoryHomology₀ConstIsoOfIsConnected C X).hom =
      𝟙 X :=
  ι₀_π₀_categoryHomology₀IsoOfIsColimit_hom (isColimitConstCocone C X) x

lemma categoryHomology₀ConstIsoOfIsConnected_inv_eq (X : A) (x : C) :
    (categoryHomology₀ConstIsoOfIsConnected C X).inv =
      categoryChainComplex.ι₀ ((Functor.const C).obj X) x ≫
        categoryHomology.π₀ ((Functor.const C).obj X) := by
  simpa [categoryHomology₀ConstIsoOfIsConnected] using
    ι_categoryHomology₀IsoOfIsColimit_inv (isColimitConstCocone C X) x

end Connected

/-! ### Acyclicity of categories with a terminal object -/

section Terminal

variable {C : Type u₁} [Category.{v₁} C] {A : Type u} [Category.{v} A]
  [HasCoproducts.{max u₁ v₁} A] [Preadditive A]

namespace categoryChainComplex

section SingleZero

variable [HasZeroObject A]

/-- The augmentation chain map `categoryChainComplex C M ⟶ (ChainComplex.single₀ A).obj (M.obj t)`
associated to a terminal object `t : C`. -/
def toSingle₀OfIsTerminal {t : C} (ht : IsTerminal t) (M : C ⥤ A) :
    categoryChainComplex C M ⟶ (ChainComplex.single₀ A).obj (M.obj t) :=
  HomologicalComplex.mkHomToSingle (desc₀ (coconeOfDiagramTerminal ht M)) fun i hi ↦ by
    obtain rfl : i = 1 := by simpa using hi.symm
    exact d_desc₀ (coconeOfDiagramTerminal ht M) 1

@[simp]
lemma toSingle₀OfIsTerminal_f_zero {t : C} (ht : IsTerminal t) (M : C ⥤ A) :
    (toSingle₀OfIsTerminal ht M).f 0 =
      desc₀ (coconeOfDiagramTerminal ht M) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (M.obj t)).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

@[simp]
lemma toSingle₀OfIsTerminal_f_succ {t : C} (ht : IsTerminal t) (M : C ⥤ A) (n : ℕ) :
    (toSingle₀OfIsTerminal ht M).f (n + 1) = 0 :=
  (HomologicalComplex.isZero_single_obj_X _ _ _ _ (Nat.succ_ne_zero n)).eq_of_tgt _ _

/-- The inclusion chain map `(ChainComplex.single₀ A).obj (M.obj x) ⟶ categoryChainComplex C M`
at an object `x : C`. -/
def fromSingle₀ (M : C ⥤ A) (x : C) :
    (ChainComplex.single₀ A).obj (M.obj x) ⟶ categoryChainComplex C M :=
  HomologicalComplex.mkHomFromSingle (ι₀ M x) fun _ hk ↦ by simp at hk

@[simp]
lemma fromSingle₀_f_zero (M : C ⥤ A) (x : C) :
    (fromSingle₀ M x).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (M.obj x)).hom ≫ ι₀ M x :=
  HomologicalComplex.mkHomFromSingle_f _ _

@[simp]
lemma fromSingle₀_f_succ (M : C ⥤ A) (x : C) (n : ℕ) :
    (fromSingle₀ M x).f (n + 1) = 0 :=
  (HomologicalComplex.isZero_single_obj_X _ _ _ _ (Nat.succ_ne_zero n)).eq_of_src _ _

@[reassoc (attr := simp)]
lemma fromSingle₀_comp_toSingle₀OfIsTerminal {t : C} (ht : IsTerminal t) (M : C ⥤ A) :
    fromSingle₀ M t ≫ toSingle₀OfIsTerminal ht M =
      𝟙 ((ChainComplex.single₀ A).obj (M.obj t)) := by
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  rcases i with _ | n
  · rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, fromSingle₀_f_zero,
      toSingle₀OfIsTerminal_f_zero, Category.assoc, ι₀_desc₀_assoc, coconeOfDiagramTerminal_ι_app,
      ht.hom_ext (ht.from t) (𝟙 t), M.map_id, Category.id_comp, Iso.hom_inv_id]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ (Nat.succ_ne_zero n)).eq_of_src _ _

end SingleZero

/-- The degree-`n` contracting chain homotopy operator on `categoryChainComplex C M` induced by a
terminal object `t : C`, sending the summand of `σ : ComposableArrows C n` to
`(-1)^(n + 1) • ι M (σ.postcomp (ht.from σ.right))`. -/
def contractingHomotopyOfIsTerminal {t : C} (ht : IsTerminal t) (M : C ⥤ A) (n : ℕ) :
    (categoryChainComplex C M).X n ⟶ (categoryChainComplex C M).X (n + 1) :=
  (isColimitXCofan M n).desc (Cofan.mk ((categoryChainComplex C M).X (n + 1)) fun σ ↦
    (-1 : ℤ) ^ (n + 1) • ι M (σ.postcomp (ht.from σ.right)))

@[reassoc (attr := simp)]
lemma ι_contractingHomotopyOfIsTerminal {t : C} (ht : IsTerminal t) (M : C ⥤ A) {n : ℕ}
    (σ : ComposableArrows C n) :
    ι M σ ≫ contractingHomotopyOfIsTerminal ht M n =
      (-1 : ℤ) ^ (n + 1) • ι M (σ.postcomp (ht.from σ.right)) :=
  (isColimitXCofan M n).fac _ ⟨σ⟩

@[reassoc (attr := simp)]
lemma ι₀_contractingHomotopyOfIsTerminal {t : C} (ht : IsTerminal t) (M : C ⥤ A) (x : C) :
    ι₀ M x ≫ contractingHomotopyOfIsTerminal ht M 0 = -ι₁ M (ht.from x) := by
  refine (ι_contractingHomotopyOfIsTerminal ht M (ComposableArrows.mk₀ x)).trans ?_
  rw [pow_one, neg_one_zsmul]
  refine congrArg Neg.neg ?_
  exact (ι_congr M (ComposableArrows.mk₀_postcomp (ht.from x)) rfl).trans
    ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))

private lemma contractingHomotopy_comm_zero {t : C} (ht : IsTerminal t) (M : C ⥤ A) :
    contractingHomotopyOfIsTerminal ht M 0 ≫ (categoryChainComplex C M).d 1 0 +
      desc₀ (coconeOfDiagramTerminal ht M) ≫ ι₀ M t = 𝟙 ((categoryChainComplex C M).X 0) := by
  ext σ
  obtain ⟨x, rfl⟩ := ComposableArrows.mk₀_surjective σ
  refine ((Preadditive.comp_add _ _ _ _ _ _).trans ?_).trans (Category.comp_id _).symm
  have h1 : ι₀ M x ≫ contractingHomotopyOfIsTerminal ht M 0 ≫
      (categoryChainComplex C M).d 1 0 = ι₀ M x - M.map (ht.from x) ≫ ι₀ M t := by
    rw [ι₀_contractingHomotopyOfIsTerminal_assoc, Preadditive.neg_comp, ι₁_d_one_zero, neg_sub]
  have h2 : ι₀ M x ≫ desc₀ (coconeOfDiagramTerminal ht M) ≫ ι₀ M t =
      M.map (ht.from x) ≫ ι₀ M t := by
    rw [ι₀_desc₀_assoc, coconeOfDiagramTerminal_ι_app]
  exact (congrArg₂ (· + ·) h1 h2).trans (sub_add_cancel _ _)

private lemma ι_postcomp_δ_zero {t : C} (ht : IsTerminal t) (M : C ⥤ A) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) :
    M.map ((σ.postcomp (ht.from σ.right)).map (homOfLE (Fin.zero_le 1))) ≫
        ι M ((nerve C).δ (0 : Fin (n + 3)) (σ.postcomp (ht.from σ.right))) =
      M.map (σ.map (homOfLE (Fin.zero_le 1))) ≫
        ι M (((nerve C).δ (0 : Fin (n + 2)) σ).postcomp
          (ht.from (((nerve C).δ (0 : Fin (n + 2)) σ).right))) := by
  let f_t : σ.right ⟶ t := ht.from σ.right
  let σ₀ : ComposableArrows C n := (nerve C).δ (0 : Fin (n + 2)) σ
  have hδ₀ : (nerve C).δ (0 : Fin (n + 3)) (σ.postcomp f_t) = σ₀.postcomp (ht.from σ₀.right) :=
    (σ.whiskerLeft_castSucc_succAbove_postcomp (0 : Fin (n + 2)) f_t).trans
      (congrArg σ₀.postcomp (ht.hom_ext _ _))
  have h0 : (0 : Fin (n + 3)) = (0 : Fin (n + 2)).castSucc := by ext; simp
  have h1 : (1 : Fin (n + 3)) = (1 : Fin (n + 2)).castSucc := by
    ext
    simp [Nat.mod_eq_of_lt]
  have hobj₀ : (σ.postcomp f_t).obj (0 : Fin (n + 3)) = σ.obj (0 : Fin (n + 2)) :=
    (congrArg (σ.postcomp f_t).obj h0).trans (σ.postcomp_obj_castSucc f_t (0 : Fin (n + 2)))
  have hobj₁ : (σ.postcomp f_t).obj (1 : Fin (n + 3)) = σ.obj (1 : Fin (n + 2)) :=
    (congrArg (σ.postcomp f_t).obj h1).trans (σ.postcomp_obj_castSucc f_t (1 : Fin (n + 2)))
  have hmap : (σ.postcomp f_t).map (homOfLE (Fin.zero_le (1 : Fin (n + 3)))) =
      eqToHom hobj₀ ≫
        σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2)))) ≫ eqToHom hobj₁.symm := by
    have hmap' := σ.postcomp_map_castSucc f_t (0 : Fin (n + 2)) (1 : Fin (n + 2)) (Fin.zero_le 1)
    have hhom : homOfLE (Fin.zero_le (1 : Fin (n + 3))) =
        eqToHom h0 ≫
          homOfLE (Fin.castSucc_le_castSucc_iff.mpr (Fin.zero_le (1 : Fin (n + 2)))) ≫
            eqToHom h1.symm := Subsingleton.elim _ _
    rw [hhom, Functor.map_comp, Functor.map_comp, hmap', eqToHom_map, eqToHom_map]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  have hι : ι M ((nerve C).δ (0 : Fin (n + 3)) (σ.postcomp f_t)) =
      eqToHom (congrArg M.obj hobj₁) ≫ ι M (σ₀.postcomp (ht.from σ₀.right)) :=
    ι_congr M hδ₀ hobj₁
  have hcomp (v : M.obj (σ.obj (1 : Fin (n + 2))) ⟶ (categoryChainComplex C M).X (n + 1)) :
      M.map (eqToHom hobj₀ ≫
        σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2)))) ≫ eqToHom hobj₁.symm) ≫
          (eqToHom (congrArg M.obj hobj₁) ≫ v) =
        eqToHom (congrArg M.obj hobj₀) ≫
          (M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫ v) := by
    rw [M.map_comp, M.map_comp, eqToHom_map, eqToHom_map, Category.assoc, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact (congrArg₂ (· ≫ ·) (congrArg M.map hmap) hι).trans
    ((hcomp _).trans ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _)))

private lemma contractingHomotopy_comm_succ {t : C} (ht : IsTerminal t) (M : C ⥤ A) (n : ℕ) :
    (categoryChainComplex C M).d (n + 1) n ≫ contractingHomotopyOfIsTerminal ht M n +
      contractingHomotopyOfIsTerminal ht M (n + 1) ≫
        (categoryChainComplex C M).d (n + 2) (n + 1) =
      𝟙 ((categoryChainComplex C M).X (n + 1)) := by
  ext σ
  let f_t : σ.right ⟶ t := ht.from σ.right
  let τ : ComposableArrows C (n + 2) := σ.postcomp f_t
  -- Compute `ι M σ ≫ d (n + 1) n ≫ s n`.
  have hds : ι M σ ≫ (categoryChainComplex C M).d (n + 1) n ≫
      contractingHomotopyOfIsTerminal ht M n =
      (-1 : ℤ) ^ (n + 1) • (M.map (σ.map (homOfLE (Fin.zero_le 1))) ≫
        ι M (((nerve C).δ 0 σ).postcomp (ht.from (((nerve C).δ 0 σ).right)))) +
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j.val + 1) * (-1 : ℤ) ^ (n + 1)) •
        ι M (((nerve C).δ j.succ σ).postcomp (ht.from (((nerve C).δ j.succ σ).right))) := by
    refine ((ι_d_assoc M σ _).trans (Preadditive.add_comp _ _ _ _ _ _)).trans ?_
    refine congrArg₂ (· + ·) ?_ ?_
    · let m₀ := M.map (σ.map (homOfLE (Fin.zero_le 1)))
      exact ((Category.assoc m₀ _ _).trans
        (congrArg (m₀ ≫ ·) (ι_contractingHomotopyOfIsTerminal ht M _))).trans
        (Preadditive.comp_zsmul _ _ _)
    · refine (Preadditive.sum_comp Finset.univ _ _).trans (Finset.sum_congr rfl fun j _ ↦ ?_)
      let c_j : ℤ := (-1 : ℤ) ^ (j.val + 1)
      exact ((Preadditive.zsmul_comp _ _ c_j).trans
        (congrArg (c_j • ·) (ι_contractingHomotopyOfIsTerminal ht M _))).trans
        (smul_smul _ _ _)
  -- Compute the interior faces `k = j.castSucc` of `τ = σ.postcomp f_t`.
  have hsucc (j : Fin (n + 1)) :
      ι M ((nerve C).δ j.castSucc.succ τ) =
        ι M (((nerve C).δ j.succ σ).postcomp (ht.from (((nerve C).δ j.succ σ).right))) := by
    have hδ : (nerve C).δ j.castSucc.succ τ =
        ((nerve C).δ j.succ σ).postcomp (ht.from (((nerve C).δ j.succ σ).right)) := by
      have hcs : j.castSucc.succ = j.succ.castSucc := by ext; rfl
      refine (congrArg (fun k ↦ (nerve C).δ k τ) hcs).trans ?_
      exact (σ.whiskerLeft_castSucc_succAbove_postcomp j.succ f_t).trans
        (congrArg (((nerve C).δ j.succ σ).postcomp) (ht.hom_ext _ _))
    exact (ι_congr M hδ rfl).trans
      ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))
  -- Compute the final face `k = Fin.last (n + 1)` of `τ = σ.postcomp f_t`.
  have hlast : ι M ((nerve C).δ (Fin.last (n + 1)).succ τ) = ι M σ := by
    have hδlast : (nerve C).δ (Fin.last (n + 1)).succ τ = σ :=
      (congrArg (fun k ↦ (nerve C).δ k τ) (Fin.succ_last (n + 1))).trans
        ((CategoryTheory.nerve.δ_last_eq τ).trans (σ.postcomp_δlast f_t))
    exact (ι_congr M hδlast rfl).trans
      ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))
  -- Compute `ι M σ ≫ s (n + 1) ≫ d (n + 2) (n + 1)` and cancel with `hds`.
  have hsd : ι M σ ≫ contractingHomotopyOfIsTerminal ht M (n + 1) ≫
      (categoryChainComplex C M).d (n + 2) (n + 1) =
      -((-1 : ℤ) ^ (n + 1) • (M.map (σ.map (homOfLE (Fin.zero_le 1))) ≫
        ι M (((nerve C).δ 0 σ).postcomp (ht.from (((nerve C).δ 0 σ).right))))) +
      (-(∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j.val + 1) * (-1 : ℤ) ^ (n + 1)) •
        ι M (((nerve C).δ j.succ σ).postcomp (ht.from (((nerve C).δ j.succ σ).right)))) +
      ι M σ) := by
    have hdτ : (ι M τ ≫ (categoryChainComplex C M).d (n + 2) (n + 1) :
        M.obj (σ.obj 0) ⟶ (categoryChainComplex C M).X (n + 1)) =
        M.map (σ.map (homOfLE (Fin.zero_le 1))) ≫
          ι M (((nerve C).δ 0 σ).postcomp (ht.from (((nerve C).δ 0 σ).right))) +
        ((∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) •
          ι M (((nerve C).δ j.succ σ).postcomp (ht.from (((nerve C).δ j.succ σ).right)))) +
        (-1 : ℤ) ^ (n + 2) • ι M σ) := by
      refine (ι_d M τ).trans (congrArg₂ (· + ·) (ι_postcomp_δ_zero ht M σ) ?_)
      refine (Fin.sum_univ_castSucc _).trans ?_
      refine congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun j _ ↦ congrArg ((-1 : ℤ) ^ (j.val + 1) • ·) (hsucc j))
        (congrArg ((-1 : ℤ) ^ (n + 2) • ·) hlast)
    refine ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (ι_contractingHomotopyOfIsTerminal ht M σ)).trans
        ((Preadditive.zsmul_comp _ _ _).trans
          (congrArg ((-1 : ℤ) ^ (n + 2) • ·) hdτ)))).trans ?_
    rw [zsmul_add, zsmul_add]
    have hneg0 : (-1 : ℤ) ^ (n + 2) = -((-1 : ℤ) ^ (n + 1)) := by
      rw [pow_succ, mul_neg_one]
    refine congrArg₂ (· + ·) (by rw [hneg0, neg_zsmul]) ?_
    refine congrArg₂ (· + ·) ?_ ?_
    · refine (Finset.smul_sum.trans ?_).trans (Finset.sum_neg_distrib _)
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      exact (smul_smul _ _ _).trans
        ((congrArg (· • _) ((congrArg (· * _) hneg0).trans
          ((neg_mul _ _).trans (congrArg Neg.neg (mul_comm _ _))))).trans
          (neg_zsmul _ _))
    · rw [smul_smul, ← pow_add]
      have heven : Even ((n + 2) + (n + 2)) := ⟨n + 2, rfl⟩
      rw [heven.neg_one_pow, one_zsmul]
  have hab (a b c : M.obj (σ.obj 0) ⟶ (categoryChainComplex C M).X (n + 1)) :
      (a + b) + (-a + (-b + c)) = c := by abel
  exact (Preadditive.comp_add _ _ _ _ _ _).trans
    ((congrArg₂ (· + ·) hds hsd).trans ((hab _ _ _).trans (Category.comp_id _).symm))

/-- The contracting chain homotopy between `𝟙 (categoryChainComplex C M)` and the projection onto
degree `0` at a terminal object `t : C`. -/
def homotopyIdOfIsTerminal [HasZeroObject A] {t : C} (ht : IsTerminal t) (M : C ⥤ A) :
    Homotopy (𝟙 (categoryChainComplex C M))
      (toSingle₀OfIsTerminal ht M ≫ fromSingle₀ M t) where
  hom i j :=
    if h : i + 1 = j then
      contractingHomotopyOfIsTerminal ht M i ≫
        eqToHom (congrArg (categoryChainComplex C M).X h)
    else 0
  zero _ _ w := dite_eq_right_iff.mpr fun h ↦ (w h).elim
  comm i := by
    cases i with
    | zero =>
      rw [dNext_eq_zero _ 0 (by simp), prevD_eq _ (ComplexShape.down_mk 1 0 rfl)]
      simp only [↓reduceDIte, eqToHom_refl, Category.comp_id, zero_add,
        HomologicalComplex.id_f, HomologicalComplex.comp_f, toSingle₀OfIsTerminal_f_zero,
        fromSingle₀_f_zero, Category.assoc, Iso.inv_hom_id_assoc]
      exact (contractingHomotopy_comm_zero ht M).symm
    | succ n =>
      rw [dNext_eq _ (ComplexShape.down_mk (n + 1) n rfl),
        prevD_eq _ (ComplexShape.down_mk (n + 2) (n + 1) rfl)]
      simp only [↓reduceDIte, eqToHom_refl, Category.comp_id, HomologicalComplex.id_f,
        HomologicalComplex.comp_f, fromSingle₀_f_succ, comp_zero, add_zero]
      exact (contractingHomotopy_comm_succ ht M n).symm

end categoryChainComplex

/-- When `t : C` is terminal, `categoryChainComplex C M` is chain homotopy equivalent to
`M.obj t` concentrated in degree `0`. -/
def categoryChainComplexTerminalHomotopyEquiv [HasZeroObject A] {t : C} (ht : IsTerminal t)
    (M : C ⥤ A) :
    HomotopyEquiv (categoryChainComplex C M) ((ChainComplex.single₀ A).obj (M.obj t)) where
  hom := categoryChainComplex.toSingle₀OfIsTerminal ht M
  inv := categoryChainComplex.fromSingle₀ M t
  homotopyHomInvId := (categoryChainComplex.homotopyIdOfIsTerminal ht M).symm
  homotopyInvHomId := Homotopy.ofEq
    (categoryChainComplex.fromSingle₀_comp_toSingle₀OfIsTerminal ht M)

/-- When `t : C` is terminal, `H₀(C, M) ≅ M.obj t`. -/
@[expose]
def categoryHomology₀IsoOfIsTerminal [CategoryWithHomology A] {t : C} (ht : IsTerminal t)
    (M : C ⥤ A) :
    categoryHomology C M 0 ≅ M.obj t :=
  categoryHomology₀IsoOfIsColimit (colimitOfDiagramTerminal ht M)

@[reassoc (attr := simp)]
lemma ι₀_π₀_categoryHomology₀IsoOfIsTerminal_hom [CategoryWithHomology A] {t : C}
    (ht : IsTerminal t) (M : C ⥤ A) (x : C) :
    categoryChainComplex.ι₀ M x ≫ categoryHomology.π₀ M ≫
        (categoryHomology₀IsoOfIsTerminal ht M).hom =
      M.map (ht.from x) :=
  ι₀_π₀_categoryHomology₀IsoOfIsColimit_hom (colimitOfDiagramTerminal ht M) x

@[simp]
lemma categoryHomology₀IsoOfIsTerminal_inv [CategoryWithHomology A] {t : C}
    (ht : IsTerminal t) (M : C ⥤ A) :
    (categoryHomology₀IsoOfIsTerminal ht M).inv =
      categoryChainComplex.ι₀ M t ≫ categoryHomology.π₀ M := by
  have h := ι_categoryHomology₀IsoOfIsColimit_inv (colimitOfDiagramTerminal ht M) t
  rwa [coconeOfDiagramTerminal_ι_app, ht.hom_ext (ht.from t) (𝟙 t), M.map_id, Category.id_comp] at h

/-- When `C` has a terminal object `t`, all positive-degree category homology groups
`categoryHomology C M (n + 1)` vanish. -/
lemma isZero_categoryHomology_succ_of_isTerminal [HasZeroObject A] [CategoryWithHomology A]
    {t : C} (ht : IsTerminal t) (M : C ⥤ A) (n : ℕ) :
    IsZero (categoryHomology C M (n + 1)) := by
  have hsingle : IsZero (((ChainComplex.single₀ A).obj (M.obj t)).homology (n + 1)) :=
    (ChainComplex.exactAt_succ_single_obj (M.obj t) n).isZero_homology
  exact ((categoryChainComplexTerminalHomotopyEquiv ht M).toHomologyIso (n + 1)).isZero_iff.mpr
    hsingle

end Terminal

/-! ### Degree-two homology versus cohomology of `ℤ/2ℤ` with integral coefficients -/

section ZModTwo

private abbrev G₂ : Type := Multiplicative (ZMod 2)

private def g₂ : G₂ := Multiplicative.ofAdd (1 : ZMod 2)

private abbrev e₂ : SingleObj.star G₂ ⟶ SingleObj.star G₂ := g₂

private abbrev id₂ : SingleObj.star G₂ ⟶ SingleObj.star G₂ := 𝟙 (SingleObj.star G₂)

private lemma g₂_ne_one : g₂ ≠ 1 := by
  decide

private lemma g₂_mul_self : g₂ * g₂ = 1 := by
  decide

private lemma e₂_comp_self : e₂ ≫ e₂ = id₂ :=
  g₂_mul_self

private lemma eq_one_or_eq_g₂ (x : G₂) : x = 1 ∨ x = g₂ := by
  revert x
  decide

private lemma mem_zpowers_g₂ (x : G₂) : x ∈ Subgroup.zpowers g₂ := by
  rcases eq_one_or_eq_g₂ x with rfl | rfl
  · exact ⟨0, zpow_zero g₂⟩
  · exact ⟨1, zpow_one g₂⟩

private def s₁_e₂ : (nerve (SingleObj G₂)) _⦋1⦌ := ComposableArrows.mk₁ e₂

private def s₁_id : (nerve (SingleObj G₂)) _⦋1⦌ := ComposableArrows.mk₁ id₂

private def s₂_e₂ : (nerve (SingleObj G₂)) _⦋2⦌ := ComposableArrows.mk₂ e₂ e₂

private lemma s₁_e₂_mem_nonDegenerate :
    s₁_e₂ ∈ (nerve (SingleObj G₂)).nonDegenerate 1 := by
  rw [SSet.mem_nonDegenerate_iff_notMem_degenerate, SSet.degenerate_eq_iUnion_range_σ,
    Set.mem_iUnion]
  rintro ⟨i, hi⟩
  obtain rfl : i = 0 := Fin.eq_zero i
  obtain ⟨x, hx⟩ := (CategoryTheory.nerve.mem_range_σ_iff (ComposableArrows.mk₁ e₂) 0).mp hi
  obtain rfl : x = SingleObj.star G₂ := Subsingleton.elim _ _
  have htot : (ComposableArrows.mk₁ e₂).totalArrow (0 : Fin 1).castSucc (0 : Fin 1).succ
      (Fin.castSucc_le_succ 0) = ⟨SingleObj.star G₂, SingleObj.star G₂, e₂⟩ := by
    rw [ComposableArrows.totalArrow_def]
    simp
  rw [htot] at hx
  exact g₂_ne_one (eq_of_heq (Quiver.Total.ext_iff.mp hx.symm).2.2)

private lemma eq_s₂_e₂_of_mem_nonDegenerate
    {s : (nerve (SingleObj G₂)) _⦋2⦌} (hs : s ∈ (nerve (SingleObj G₂)).nonDegenerate 2) :
    s = s₂_e₂ := by
  rw [SSet.mem_nonDegenerate_iff_notMem_degenerate, SSet.degenerate_eq_iUnion_range_σ,
    Set.mem_iUnion, not_exists] at hs
  obtain ⟨x, y, z, f₁, f₂, rfl⟩ := ComposableArrows.mk₂_surjective s
  obtain rfl : x = SingleObj.star G₂ := Subsingleton.elim _ _
  obtain rfl : y = SingleObj.star G₂ := Subsingleton.elim _ _
  obtain rfl : z = SingleObj.star G₂ := Subsingleton.elim _ _
  have hf₁ : f₁ = e₂ := by
    rcases eq_one_or_eq_g₂ f₁ with h₁ | h₁
    · refine False.elim (hs (0 : Fin 2) ((CategoryTheory.nerve.mem_range_σ_iff _ 0).mpr ?_))
      refine ⟨SingleObj.star G₂, ?_⟩
      rw [ComposableArrows.totalArrow_def]
      simp [h₁, SingleObj.id_as_one]
    · exact h₁
  have hf₂ : f₂ = e₂ := by
    rcases eq_one_or_eq_g₂ f₂ with h₂ | h₂
    · refine False.elim (hs (1 : Fin 2) ((CategoryTheory.nerve.mem_range_σ_iff _ 1).mpr ?_))
      refine ⟨SingleObj.star G₂, ?_⟩
      rw [ComposableArrows.totalArrow_def]
      simp [h₂, SingleObj.id_as_one]
    · exact h₂
  subst hf₁ hf₂
  rfl

/-- For the single-object category `SingleObj (Multiplicative (ZMod 2))` with constant integral
coefficients `ModuleCat.of ℤ ℤ`, degree-two category homology vanishes: `H₂(B(ℤ/2ℤ), ℤ) = 0`. -/
theorem isZero_categoryHomology_singleObj_zmod_two_int_two :
    IsZero (categoryHomology (SingleObj (Multiplicative (ZMod 2)))
      ((Functor.const _).obj (ModuleCat.of ℤ ℤ)) 2) := by
  let X : SSet.{0} := nerve (SingleObj G₂)
  let R : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ
  let K : ChainComplex (ModuleCat.{0} ℤ) ℕ := X.normalizedChainComplex R
  -- Project `K.X 2` and `K.X 1` onto their unique nondegenerate summands `s₂_e₂` and `s₁_e₂`.
  let j₂ : R ⟶ K.X 2 := X.ιNormalizedChainComplex s₂_e₂
  let p₂ : K.X 2 ⟶ R :=
    (X.isColimitCofanNormalizedChainComplex R 2).desc (Cofan.mk R fun _ ↦ 𝟙 R)
  let p₁ : K.X 1 ⟶ R :=
    (X.isColimitCofanNormalizedChainComplex R 1).desc (Cofan.mk R fun _ ↦ 𝟙 R)
  have hp₂j₂ : p₂ ≫ j₂ = 𝟙 (K.X 2) := by
    refine X.normalizedChainComplex_hom_ext fun s hs ↦ ?_
    have hp₂ : X.ιNormalizedChainComplex s ≫ p₂ = 𝟙 R :=
      (X.isColimitCofanNormalizedChainComplex R 2).fac _ ⟨s, hs⟩
    rw [reassoc_of% hp₂, Category.comp_id]
    exact congrArg X.ιNormalizedChainComplex (eq_s₂_e₂_of_mem_nonDegenerate hs).symm
  have hp₁ : X.ιNormalizedChainComplex s₁_e₂ ≫ p₁ = 𝟙 R :=
    (X.isColimitCofanNormalizedChainComplex R 1).fac _ ⟨s₁_e₂, s₁_e₂_mem_nonDegenerate⟩
  have hdeg₁ : X.ιNormalizedChainComplex (R := R) s₁_id = 0 := by
    refine X.ιNormalizedChainComplex_eq_zero s₁_id ?_
    rw [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
    exact ⟨0, ComposableArrows.mk₀ (SingleObj.star G₂),
      CategoryTheory.nerve.σ₀_mk₀_eq (SingleObj.star G₂)⟩
  -- On the unique nondegenerate `2`-chain `s₂_e₂`, `d 2 1` acts as multiplication by `2`.
  have hd₂ : j₂ ≫ K.d 2 1 ≫ p₁ = (2 : ℤ) • 𝟙 R := by
    dsimp [j₂, K]
    rw [← Category.assoc, SSet.ιNormalizedChainComplex_d, Fin.sum_univ_three,
      Preadditive.add_comp, Preadditive.add_comp]
    have hδ₀ : X.δ 0 s₂_e₂ = s₁_e₂ :=
      CategoryTheory.nerve.δ₀_mk₂_eq e₂ e₂
    have hδ₁ : X.δ 1 s₂_e₂ = s₁_id :=
      (CategoryTheory.nerve.δ₁_mk₂_eq e₂ e₂).trans (congrArg ComposableArrows.mk₁ e₂_comp_self)
    have hδ₂ : X.δ 2 s₂_e₂ = s₁_e₂ :=
      CategoryTheory.nerve.δ₂_mk₂_eq e₂ e₂
    simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_one_zsmul,
      Fin.val_two, even_two.neg_one_pow, hδ₀, hδ₁, hδ₂, hdeg₁, neg_zero, zero_comp, add_zero,
      hp₁, two_zsmul]
  -- Since `ℤ` is torsion-free, `K.d 2 1` is monomorphic, so `K` has zero homology in degree `2`.
  have hmono : Mono (K.d 2 1) := by
    refine Preadditive.mono_of_cancel_zero _ fun {T} u hu ↦ ?_
    have h2 : (2 : ℤ) • (u ≫ p₂) = 0 := by
      calc
        (2 : ℤ) • (u ≫ p₂) = (u ≫ p₂) ≫ ((2 : ℤ) • 𝟙 R) := by
          rw [Preadditive.comp_zsmul, Category.comp_id]
        _ = u ≫ (p₂ ≫ j₂) ≫ K.d 2 1 ≫ p₁ := by
          simp only [← hd₂, Category.assoc]
        _ = (u ≫ K.d 2 1) ≫ p₁ := by
          rw [hp₂j₂, Category.id_comp, Category.assoc]
        _ = 0 := by rw [hu, zero_comp]
    have hup₂ : u ≫ p₂ = 0 := by
      ext m
      have hm : (2 : ℤ) * (u ≫ p₂).hom m = 0 := by
        simpa [zsmul_eq_mul] using congrArg (fun φ : T ⟶ R ↦ φ.hom m) h2
      simpa using mul_eq_zero.mp hm
    calc
      u = u ≫ p₂ ≫ j₂ := by rw [hp₂j₂, Category.comp_id]
      _ = (u ≫ p₂) ≫ j₂ := (Category.assoc _ _ _).symm
      _ = 0 := by rw [hup₂, zero_comp]
  have hmono_g : Mono (K.sc' 3 2 1).g := hmono
  have hi : (K.sc' 3 2 1).iCycles = 0 := by
    rw [← cancel_mono (K.sc' 3 2 1).g, ShortComplex.iCycles_g, zero_comp]
  have hcyc : IsZero (K.sc' 3 2 1).cycles := by
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (K.sc' 3 2 1).iCycles, Category.id_comp, hi, zero_comp]
  have hsc : IsZero (K.sc' 3 2 1).homology := by
    rw [IsZero.iff_id_eq_zero, ← cancel_epi (K.sc' 3 2 1).homologyπ, Category.comp_id,
      hcyc.eq_of_src (K.sc' 3 2 1).homologyπ 0, comp_zero]
  have hK : IsZero (K.homology 2) :=
    (ShortComplex.homologyMapIso (K.isoSc' 3 2 1 (by simp) (by simp))).isZero_iff.mpr hsc
  have hX : IsZero (X.homology R 2) :=
    ((X.homotopyEquivNormalizedChainComplex R).toHomologyIso 2).isZero_iff.mpr hK
  exact (categoryHomologyConstIso (SingleObj G₂) R 2).isZero_iff.mpr hX

/-- Degree-two group cohomology of `Multiplicative (ZMod 2)` with trivial integral coefficients
`Rep.trivial ℤ (Multiplicative (ZMod 2)) ℤ` is isomorphic to `ModuleCat.of ℤ (ZMod 2)`. -/
def groupCohomologyTrivialZModTwoIntTwoIso :
    groupCohomology (Rep.trivial ℤ (Multiplicative (ZMod 2)) ℤ) 2 ≅
      ModuleCat.of ℤ (ZMod 2) := by
  let A₀ : Rep ℤ G₂ := Rep.trivial ℤ G₂ ℤ
  let π₂ := Rep.FiniteCyclicGroup.groupCohomologyπEven A₀ g₂ mem_zpowers_g₂ 2 even_two
  have hker_top : ∀ n : ℤ,
      n ∈ LinearMap.ker (Rep.applyAsHom A₀ g₂ - 𝟙 A₀).hom.toLinearMap := fun n ↦ by
    simp [A₀, Rep.applyAsHom, Rep.sub_hom]
  let ι_ker : ℤ →ₗ[ℤ] LinearMap.ker (Rep.applyAsHom A₀ g₂ - 𝟙 A₀).hom.toLinearMap :=
    { toFun n := ⟨n, hker_top n⟩
      map_add' _ _ := rfl
      map_smul' _ _ := Subtype.ext (by simp) }
  let q : ℤ →ₗ[ℤ] groupCohomology A₀ 2 := π₂.hom.comp ι_ker
  have hq_surj : Function.Surjective q := by
    have hπ_surj : Function.Surjective π₂.hom :=
      (ModuleCat.epi_iff_surjective π₂).mp inferInstance
    intro y
    obtain ⟨⟨n, _⟩, rfl⟩ := hπ_surj y
    exact ⟨n, rfl⟩
  have hq_ker : LinearMap.ker q = Ideal.span {(2 : ℤ)} := by
    ext n
    have hπ : q n = π₂ ⟨n, hker_top n⟩ := rfl
    rw [LinearMap.mem_ker, hπ, Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff,
      Ideal.mem_span_singleton, LinearMap.mem_range]
    dsimp only
    have hnorm (m : A₀) : A₀.norm.asHom.hom.toLinearMap m = (2 : ℤ) * m := by
      have huniv : (Finset.univ : Finset G₂) = {1, g₂} := by
        ext x
        simp [eq_one_or_eq_g₂ x]
      have happly : A₀.norm.asHom.hom.toLinearMap m = (A₀.ρ.norm m : ℤ) := rfl
      rw [happly]
      simp [A₀, Representation.norm, huniv, g₂_ne_one.symm, two_mul]
    simp only [hnorm]
    exact ⟨fun ⟨m, hm⟩ ↦ ⟨m, hm.symm⟩, fun ⟨m, hm⟩ ↦ ⟨m, hm.symm⟩⟩
  let e : groupCohomology A₀ 2 ≃ₗ[ℤ] ZMod 2 :=
    (q.quotKerEquivOfSurjective hq_surj).symm.trans
      ((Submodule.quotEquivOfEq _ _ hq_ker).trans
        (Int.quotientSpanNatEquivZMod 2).toAddEquiv.toIntLinearEquiv)
  exact e.toModuleIso

/-- Contrasting with `isZero_categoryHomology_singleObj_zmod_two_int_two`, the degree-two group
cohomology `H²(ℤ/2ℤ, ℤ)` with trivial integral coefficients is nonzero. -/
theorem not_isZero_groupCohomology_trivial_zmod_two_int_two :
    ¬ IsZero (groupCohomology (Rep.trivial ℤ (Multiplicative (ZMod 2)) ℤ) 2) := by
  rw [groupCohomologyTrivialZModTwoIntTwoIso.isZero_iff]
  intro hzero
  have h1 : (𝟙 (ModuleCat.of ℤ (ZMod 2))) (1 : ZMod 2) = 0 := by
    rw [hzero.eq_of_src (𝟙 _) 0]
    rfl
  exact one_ne_zero h1

end ZModTwo

end TauCeti
