/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Equivalence
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Over
public import TauCeti.Topology.Sheaves.Cohomology.Instances
public import TauCeti.Topology.Sheaves.Godement
public import TauCeti.Topology.Sheaves.Flasque.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Topology.Sheaves.Over
import Mathlib.Topology.Sheaves.Stalks
import TauCeti.CategoryTheory.Sites.ExtensionByZero
import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence

/-!
# Fine sheaves of abelian groups and their acyclicity

Let `X` be a topological space. A sheaf `F` of abelian groups on `X` is *fine*
(`TopCat.Sheaf.IsFine`) if every indexed open cover `U : ι → Opens X` of `X` admits a locally
finite family of closed subsets `K : ι → Set X` with `K i ⊆ U i` and a family of sheaf
endomorphisms `η : ι → (F ⟶ F)` such that each `η i` vanishes on open sets disjoint from `K i`,
and on every open set meeting only finitely many `K i` the corresponding finite sum of the `η i`
acts as the identity. Unlike flasque sheaves, sections of a fine sheaf need not extend from
arbitrary open subsets to `X`; the prototypical example is the sheaf of smooth vector-valued
functions on a Hausdorff σ-compact manifold.

This file proves that every fine sheaf of abelian groups has vanishing sheaf cohomology in positive
degrees (`TopCat.Sheaf.subsingleton_H_of_isFine`), and vanishing cohomology on any open subset `U`
whose restricted sheaf `U.sheafRestrict.obj F` is fine
(`TopCat.Sheaf.subsingleton_H'_of_isFine_sheafRestrict`).

The proof uses the functorial Godement embedding `0 ⟶ F ⟶ G⁰(F) ⟶ Z¹(F) ⟶ 0` from
`TauCeti.Topology.Sheaves.Godement`:

* Vanishing on opens disjoint from `K` and finite sums acting as the identity on an open `W` are
  both detected on stalks at points outside `K` or inside `W`. Since `godement` acts on stalks
  coordinatewise through `skyscraperSheafFunctor` and `stalkFunctor` preserves epimorphisms, any
  fine partition of endomorphisms on `F` pushes forward to `G⁰(F)` and descends to the cokernel
  `Z¹(F)`. Thus `G⁰(F)` and `Z¹(F)` are again fine (`TopCat.Sheaf.isFine_godement_obj`,
  `TopCat.Sheaf.isFine_cokernel_toGodement_app`).
* Every global section `q` of `Z¹(F)` lifts to a global section of `G⁰(F)`
  (`TopCat.Sheaf.cokernel_π_toGodement_app_top_surjective`): local lifts of `q` extend to global
  sections `b x` of the flasque sheaf `G⁰(F)`, and the locally finite sum `∑ x, G⁰(η x)(b x)` glues
  on opens meeting finitely many `K x`. For each `x`, the difference `π(b x) - q` vanishes on `U x`
  while `Z¹(η x)` vanishes on `(K x)ᶜ`, and `U x ∪ (K x)ᶜ = X` because `K x ⊆ U x`, so
  `Z¹(η x)(π(b x)) = Z¹(η x)(q)` globally and the glued section maps to `q`.
* Since `G⁰(F)` is flasque, `H¹(X, F)` vanishes by `CategoryTheory.Sheaf.H'.subsingleton_X₁_one`,
  and induction on the degree along `0 ⟶ F ⟶ G⁰(F) ⟶ Z¹(F) ⟶ 0` gives `Hⁿ(X, F) = 0` for all
  `n > 0`.

## Main definitions

* `TopCat.Sheaf.IsFine`: fine sheaves of abelian groups on a topological space.

## Main results

* `TopCat.Sheaf.IsFine.of_iso`, `TopCat.Sheaf.isFine_iff_of_iso`: invariance of fineness under
  isomorphism of sheaves.
* `TopCat.Sheaf.isFine_godement_obj`, `TopCat.Sheaf.isFine_cokernel_toGodement_app`: fineness passes
  to the Godement sheaf and to the cokernel of `toGodement`.
* `TopCat.Sheaf.cokernel_π_toGodement_app_top_surjective`: global sections lift along
  `G⁰(F) ⟶ coker(F ⟶ G⁰(F))` when `F` is fine.
* `TopCat.Sheaf.subsingleton_H_succ_of_isFine`, `TopCat.Sheaf.subsingleton_H_of_isFine`: a fine
  sheaf of abelian groups has vanishing cohomology `Sheaf.H` in every positive degree.
* `TopCat.Sheaf.subsingleton_H'_of_isFine_sheafRestrict`: `Hⁿ(U, F)` vanishes in every positive
  degree whenever `U.sheafRestrict.obj F` is fine.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, Hermann, 1958, Chapitre II, §3.7
  and §4.4, Théorème 4.4.3.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific, 2021,
  §7.5.4, Example 7.5.31 and Proposition 7.5.32, p. 327.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TauCeti.Topology

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- A sheaf `F` of abelian groups on `X` is *fine* if every indexed open cover `U : ι → Opens X` of
`X` admits a locally finite family of closed subsets `K : ι → Set X` with `K i ⊆ U i` and a family
of endomorphisms `η : ι → (F ⟶ F)` such that each `η i` vanishes on opens disjoint from `K i`, and
whenever an open `W` is disjoint from `K i` outside a finite set `s`, the finite sum
`∑ i ∈ s, (η i).hom.app (op W)` is the identity on `F(W)`. -/
@[mk_iff]
class IsFine (F : X.Sheaf AddCommGrpCat.{u}) : Prop where
  exists_partition :
    ∀ {ι : Type u} (U : ι → Opens X), ⨆ i, U i = ⊤ →
      ∃ (K : ι → Set X) (η : ι → (F ⟶ F)),
        LocallyFinite K ∧
        (∀ i, IsClosed (K i)) ∧
        (∀ i, K i ⊆ U i) ∧
        (∀ i (W : Opens X), Disjoint (W : Set X) (K i) → (η i).hom.app (op W) = 0) ∧
        (∀ (W : Opens X) (s : Finset ι),
          (∀ i, i ∉ s → Disjoint (W : Set X) (K i)) →
            ∑ i ∈ s, (η i).hom.app (op W) = 𝟙 (F.obj.obj (op W)))

/-- Accessor for the fine partition of endomorphisms subordinate to an open cover `U` of `X`. -/
theorem IsFine.exists_partition_of_iSup_eq_top {F : X.Sheaf AddCommGrpCat.{u}} [F.IsFine]
    {ι : Type u} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤) :
    ∃ (K : ι → Set X) (η : ι → (F ⟶ F)),
      LocallyFinite K ∧
      (∀ i, IsClosed (K i)) ∧
      (∀ i, K i ⊆ U i) ∧
      (∀ i (W : Opens X), Disjoint (W : Set X) (K i) → (η i).hom.app (op W) = 0) ∧
      (∀ (W : Opens X) (s : Finset ι),
        (∀ i, i ∉ s → Disjoint (W : Set X) (K i)) →
          ∑ i ∈ s, (η i).hom.app (op W) = 𝟙 (F.obj.obj (op W))) :=
  IsFine.exists_partition U hU

/-- Fineness of sheaves is preserved under isomorphism. -/
theorem IsFine.of_iso {F G : X.Sheaf AddCommGrpCat.{u}} (e : F ≅ G) [F.IsFine] : G.IsFine where
  exists_partition U hU := by
    obtain ⟨K, η, hlf, hclosed, hsub, hzero, hsum⟩ := IsFine.exists_partition (F := F) U hU
    refine ⟨K, fun i ↦ e.inv ≫ η i ≫ e.hom, hlf, hclosed, hsub, fun i W hW ↦ ?_,
      fun W s hs ↦ ?_⟩
    · simp [ObjectProperty.FullSubcategory.comp_hom, hzero i W hW]
    · have hterm (i : _) :
          (e.inv ≫ η i ≫ e.hom).hom.app (op W) =
            e.inv.hom.app (op W) ≫ (η i).hom.app (op W) ≫ e.hom.hom.app (op W) := rfl
      simp only [hterm, ← Preadditive.comp_sum, ← Preadditive.sum_comp, hsum W s hs,
        Category.id_comp]
      rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]
      rfl

/-- Isomorphic sheaves of abelian groups are simultaneously fine. -/
theorem isFine_iff_of_iso {F G : X.Sheaf AddCommGrpCat.{u}} (e : F ≅ G) :
    F.IsFine ↔ G.IsFine :=
  ⟨fun _ ↦ IsFine.of_iso e, fun _ ↦ IsFine.of_iso e.symm⟩

/-- A zero sheaf of abelian groups is fine. -/
theorem isFine_of_isZero {F : X.Sheaf AddCommGrpCat.{u}} (hF : IsZero F) : F.IsFine where
  exists_partition U _ :=
    ⟨fun _ ↦ ∅, fun _ ↦ 0, fun _ ↦ ⟨Set.univ, Filter.univ_mem, by simp⟩,
      fun _ ↦ isClosed_empty, fun _ ↦ Set.empty_subset _, fun _ _ _ ↦ rfl,
      fun W _ _ ↦ by
        have hW : IsZero (F.obj.obj (op W)) :=
          (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
            (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W)).map_isZero hF
        exact hW.eq_of_src _ _⟩

/-- Every sheaf of abelian groups on an empty topological space is fine. -/
instance isFine_of_isEmpty [IsEmpty X] (F : X.Sheaf AddCommGrpCat.{u}) : F.IsFine where
  exists_partition _ _ :=
    ⟨fun _ ↦ ∅, fun _ ↦ 0, fun x ↦ IsEmpty.elim ‹IsEmpty X› x,
      fun _ ↦ isClosed_empty, fun _ ↦ Set.empty_subset _, fun _ _ _ ↦ rfl,
      fun W _ _ ↦ by
        obtain rfl : W = ⊥ := Subsingleton.elim _ _
        exact (Limits.IsTerminal.isZero F.isTerminalOfEmpty).eq_of_src _ _⟩

section StalkTransfer

/-- The germ map `F(U) ⟶ (stalkFunctor _ x).obj F`, typed with `stalkFunctor.obj` rather than
`Presheaf.stalk` so evaluation under `(stalkFunctor _ x).map` is syntactically well-typed at
implicit transparency. -/
private def germ' (F : X.Presheaf AddCommGrpCat.{u}) (U : Opens X) (x : X) (hx : x ∈ U) :
    F.obj (op U) ⟶ (Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F :=
  F.germ U x hx

private lemma germ'_res_apply (F : X.Presheaf AddCommGrpCat.{u}) {U V : Opens X} (i : U ⟶ V)
    (x : X) (hx : x ∈ U) (s : F.obj (op V)) :
    germ' F U x hx (F.map i.op s) = germ' F V x (i.le hx) s :=
  F.germ_res_apply i x hx s

private lemma stalkFunctor_map_germ'_apply {F G : X.Presheaf AddCommGrpCat.{u}} (U : Opens X)
    (x : X) (hx : x ∈ U) (f : F ⟶ G) (s : F.obj (op U)) :
    (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f (germ' F U x hx s) =
      germ' G U x hx (f.app (op U) s) :=
  Presheaf.stalkFunctor_map_germ_apply U x hx f s

private lemma exists_germ'_eq (F : X.Presheaf AddCommGrpCat.{u}) (x : X)
    (g : (Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F) :
    ∃ (U : Opens X) (hx : x ∈ U) (s : F.obj (op U)), germ' F U x hx s = g :=
  F.exists_germ_eq g

private lemma section_ext_germ' (F : X.Sheaf AddCommGrpCat.{u}) (W : Opens X)
    (s t : F.obj.obj (op W))
    (h : ∀ x (hx : x ∈ W), germ' F.obj W x hx s = germ' F.obj W x hx t) : s = t :=
  Presheaf.section_ext F W s t h

/-- If an endomorphism `η` of `F` vanishes on every open disjoint from a closed set `K`, its stalk
map vanishes at every point outside `K`. -/
private lemma stalkFunctor_map_eq_zero_of_notMem {F : X.Sheaf AddCommGrpCat.{u}} {K : Set X}
    (hK : IsClosed K) {η : F ⟶ F}
    (hzero : ∀ W : Opens X, Disjoint (W : Set X) K → η.hom.app (op W) = 0)
    {x : X} (hx : x ∉ K) :
    (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map η.hom = 0 := by
  refine ConcreteCategory.ext_apply fun g ↦ ?_
  obtain ⟨U, hxU, s, rfl⟩ := exists_germ'_eq F.obj x g
  let W : Opens X := U ⊓ ⟨Kᶜ, hK.isOpen_compl⟩
  have hxW : x ∈ W := ⟨hxU, hx⟩
  have hdisj : Disjoint (W : Set X) K := Set.disjoint_left.2 fun _ hy hK' ↦ hy.2 hK'
  rw [stalkFunctor_map_germ'_apply, ← germ'_res_apply F.obj (homOfLE inf_le_left : W ⟶ U) x hxW,
    ← η.hom.naturality_apply, hzero W hdisj]
  exact map_zero (ConcreteCategory.hom (germ' F.obj W x hxW))

/-- Conversely, if the stalk map of `η` vanishes at every point of an open `W`, then `η` vanishes
on `F(W)`. -/
private lemma app_eq_zero_of_stalkFunctor_map_eq_zero {F : X.Sheaf AddCommGrpCat.{u}}
    {η : F ⟶ F} {W : Opens X}
    (hstalk : ∀ x ∈ W, (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map η.hom = 0) :
    η.hom.app (op W) = 0 := by
  refine ConcreteCategory.ext_apply fun s ↦ section_ext_germ' F W _ _ fun x hx ↦ ?_
  rw [← stalkFunctor_map_germ'_apply, hstalk x hx]
  exact (map_zero (ConcreteCategory.hom (germ' F.obj W x hx))).symm

/-- Applying a finite sum of morphisms in `AddCommGrpCat` to an element sums the pointwise
values. -/
private lemma finset_sum_hom_apply {A B : AddCommGrpCat.{u}} {ι : Type*} (s : Finset ι)
    (f : ι → (A ⟶ B)) (a : A) :
    (∑ i ∈ s, f i) a = ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, AddCommGrpCat.hom_add_apply, ih]

/-- If `∑ i ∈ s, (η i).hom.app (op W) = 𝟙` on opens inside `W`, then at every point `x ∈ W` the
finite sum of stalk maps `∑ i ∈ s, (stalkFunctor _ x).map (η i).hom` is the identity. -/
private lemma sum_stalkFunctor_map_eq_id {F : X.Sheaf AddCommGrpCat.{u}} {ι : Type u}
    {η : ι → (F ⟶ F)} {W : Opens X} {s : Finset ι}
    (hsum : ∀ V : Opens X, V ≤ W → ∑ i ∈ s, (η i).hom.app (op V) = 𝟙 (F.obj.obj (op V)))
    {x : X} (hx : x ∈ W) :
    ∑ i ∈ s, (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (η i).hom =
      𝟙 ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F.obj) := by
  refine ConcreteCategory.ext_apply fun g ↦ ?_
  obtain ⟨U, hxU, t, rfl⟩ := exists_germ'_eq F.obj x g
  let V : Opens X := U ⊓ W
  have hxV : x ∈ V := ⟨hxU, hx⟩
  rw [finset_sum_hom_apply, ConcreteCategory.id_apply]
  have hterm (i : ι) :
      (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (η i).hom (germ' F.obj U x hxU t) =
        germ' F.obj V x hxV
          ((η i).hom.app (op V) (F.obj.map (homOfLE inf_le_left : V ⟶ U).op t)) := by
    rw [← germ'_res_apply F.obj (homOfLE inf_le_left : V ⟶ U) x hxV t,
      stalkFunctor_map_germ'_apply]
  simp only [hterm, ← map_sum, ← finset_sum_hom_apply, hsum V inf_le_right,
    ConcreteCategory.id_apply]
  exact germ'_res_apply F.obj (homOfLE inf_le_left : V ⟶ U) x hxV t

/-- Conversely, if `∑ i ∈ s, (stalkFunctor _ x).map (η i).hom = 𝟙` at every point `x ∈ W`, then
`∑ i ∈ s, (η i).hom.app (op W) = 𝟙`. -/
private lemma sum_app_eq_id_of_sum_stalkFunctor_map_eq_id {F : X.Sheaf AddCommGrpCat.{u}}
    {ι : Type u} {η : ι → (F ⟶ F)} {W : Opens X} {s : Finset ι}
    (hstalk : ∀ x ∈ W,
      ∑ i ∈ s, (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (η i).hom =
        𝟙 ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F.obj)) :
    ∑ i ∈ s, (η i).hom.app (op W) = 𝟙 (F.obj.obj (op W)) := by
  refine ConcreteCategory.ext_apply fun t ↦ section_ext_germ' F W _ _ fun x hx ↦ ?_
  have hterm (i : ι) :
      germ' F.obj W x hx ((η i).hom.app (op W) t) =
        (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (η i).hom (germ' F.obj W x hx t) :=
    (stalkFunctor_map_germ'_apply W x hx (η i).hom t).symm
  rw [finset_sum_hom_apply, map_sum, ConcreteCategory.id_apply]
  simp only [hterm, ← finset_sum_hom_apply, hstalk x hx, ConcreteCategory.id_apply]

open scoped Classical in
/-- Pushing an endomorphism `η` of `F` through `godement` preserves vanishing on opens disjoint from
a closed set `K`. -/
private lemma godement_map_app_eq_zero {F : X.Sheaf AddCommGrpCat.{u}} {K : Set X}
    (hK : IsClosed K) {η : F ⟶ F}
    (hzero : ∀ W : Opens X, Disjoint (W : Set X) K → η.hom.app (op W) = 0)
    {W : Opens X} (hW : Disjoint (W : Set X) K) :
    ((godement AddCommGrpCat.{u} X).map η).hom.app (op W) = 0 := by
  let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W)
  let fam : X → X.Sheaf AddCommGrpCat.{u} :=
    fun y ↦ (skyscraperSheafFunctor y).obj ((Presheaf.stalkFunctor AddCommGrpCat.{u} y).obj F.obj)
  let m : ∏ᶜ fam ⟶ ∏ᶜ fam :=
    Limits.Pi.map fun y ↦
      (skyscraperSheafFunctor y).map ((Presheaf.stalkFunctor AddCommGrpCat.{u} y).map η.hom)
  let eProd := PreservesProduct.iso E fam
  -- Express section evaluation of `(godement _ X).map η` at `op W` as `E.map m` on `∏ᶜ fam`.
  change E.map m = 0
  rw [← cancel_mono eProd.hom, Limits.zero_comp]
  refine Limits.Pi.hom_ext _ _ fun x ↦ ?_
  rw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π, Limits.zero_comp,
    ← E.map_comp, Limits.Pi.map_π, E.map_comp]
  by_cases hxW : x ∈ W
  · have hxK : x ∉ K := Set.disjoint_left.1 hW hxW
    rw [stalkFunctor_map_eq_zero_of_notMem hK hzero hxK, Functor.map_zero, Functor.map_zero,
      Limits.comp_zero]
  · exact (Limits.IsTerminal.isZero (isTerminalSkyscraperSheafObjObjOfNotMem hxW)).eq_of_tgt _ _

open scoped Classical in
/-- Pushing a family of endomorphisms `η i` of `F` through `godement` preserves finite sums equal to
the identity on opens. -/
private lemma sum_godement_map_app_eq_id {F : X.Sheaf AddCommGrpCat.{u}} {ι : Type u}
    {η : ι → (F ⟶ F)} {W : Opens X} {s : Finset ι}
    (hsum : ∀ V : Opens X, V ≤ W → ∑ i ∈ s, (η i).hom.app (op V) = 𝟙 (F.obj.obj (op V))) :
    ∑ i ∈ s, ((godement AddCommGrpCat.{u} X).map (η i)).hom.app (op W) =
      𝟙 (((godement AddCommGrpCat.{u} X).obj F).obj.obj (op W)) := by
  let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W)
  let fam : X → X.Sheaf AddCommGrpCat.{u} :=
    fun y ↦ (skyscraperSheafFunctor y).obj ((Presheaf.stalkFunctor AddCommGrpCat.{u} y).obj F.obj)
  let m (i : ι) : ∏ᶜ fam ⟶ ∏ᶜ fam :=
    Limits.Pi.map fun y ↦
      (skyscraperSheafFunctor y).map ((Presheaf.stalkFunctor AddCommGrpCat.{u} y).map (η i).hom)
  let eProd := PreservesProduct.iso E fam
  -- Express section evaluation of `(godement _ X).map (η i)` at `op W` as `E.map (m i)`.
  change ∑ i ∈ s, E.map (m i) = 𝟙 (E.obj (∏ᶜ fam))
  rw [← cancel_mono eProd.hom, Category.id_comp]
  refine Limits.Pi.hom_ext _ _ fun x ↦ ?_
  rw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π, Preadditive.sum_comp]
  let S := skyscraperSheafFunctor (X := X) (C := AddCommGrpCat.{u}) x ⋙ E
  have : S.Additive := Functor.additive_of_preserves_binary_products S
  have hcoord (i : ι) :
      E.map (m i) ≫ E.map (Pi.π fam x) =
        E.map (Pi.π fam x) ≫ S.map ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (η i).hom) := by
    rw [← E.map_comp, Limits.Pi.map_π, E.map_comp]
    rfl
  simp only [hcoord, ← Preadditive.comp_sum]
  by_cases hxW : x ∈ W
  · rw [← S.map_sum, sum_stalkFunctor_map_eq_id hsum hxW, S.map_id]
    dsimp only [S, Functor.comp_obj, fam]
    exact Category.comp_id _
  · exact (Limits.IsTerminal.isZero (isTerminalSkyscraperSheafObjObjOfNotMem hxW)).eq_of_tgt _ _

/-- The Godement sheaf of a fine sheaf of abelian groups is fine. -/
instance isFine_godement_obj (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFine] :
    ((godement AddCommGrpCat.{u} X).obj F).IsFine where
  exists_partition U hU := by
    obtain ⟨K, η, hlf, hclosed, hsub, hzero, hsum⟩ := IsFine.exists_partition (F := F) U hU
    refine ⟨K, fun i ↦ (godement AddCommGrpCat.{u} X).map (η i), hlf, hclosed, hsub,
      fun i W hW ↦ godement_map_app_eq_zero (hclosed i) (hzero i) hW,
      fun W s hs ↦ sum_godement_map_app_eq_id fun V hVW ↦
        hsum V s fun i hi ↦ (hs i hi).mono_left (hVW : (V : Set X) ⊆ W)⟩

/-- Endomorphism of `cokernel ((toGodement AddCommGrpCat X).app F)` induced by an endomorphism of
`F`. -/
private def cokernelToGodementEnd {F : X.Sheaf AddCommGrpCat.{u}} (η : F ⟶ F) :
    cokernel ((toGodement AddCommGrpCat.{u} X).app F) ⟶
      cokernel ((toGodement AddCommGrpCat.{u} X).app F) :=
  cokernel.map _ _ η ((godement AddCommGrpCat.{u} X).map η)
    ((toGodement AddCommGrpCat.{u} X).naturality η).symm

@[reassoc (attr := simp)]
private lemma π_cokernelToGodementEnd {F : X.Sheaf AddCommGrpCat.{u}} (η : F ⟶ F) :
    cokernel.π ((toGodement AddCommGrpCat.{u} X).app F) ≫ cokernelToGodementEnd η =
      (godement AddCommGrpCat.{u} X).map η ≫
        cokernel.π ((toGodement AddCommGrpCat.{u} X).app F) :=
  cokernel.π_desc _ _ _

/-- Taking stalks at `x` sends an epimorphism of sheaves of abelian groups to an epimorphism. -/
private lemma epi_stalkFunctor_map {F G : X.Sheaf AddCommGrpCat.{u}} (π : F ⟶ G) [Epi π] (x : X) :
    Epi ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π.hom) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro y
  obtain ⟨U, hxU, s, rfl⟩ := G.presheaf.exists_germ_eq y
  have : CategoryTheory.Sheaf.IsLocallySurjective π :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' _ π).2 inferInstance
  obtain ⟨V, iVU, ⟨t, ht⟩, hxV⟩ :=
    CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology X) π.hom s x hxU
  refine ⟨F.presheaf.germ V x hxV t, ?_⟩
  rw [Presheaf.stalkFunctor_map_germ_apply, ht, G.presheaf.germ_res_apply]

/-- Descending an endomorphism `η` to `cokernel (toGodement)` preserves vanishing on opens disjoint
from a closed set `K`. -/
private lemma cokernelToGodementEnd_app_eq_zero {F : X.Sheaf AddCommGrpCat.{u}} {K : Set X}
    (hK : IsClosed K) {η : F ⟶ F}
    (hzero : ∀ W : Opens X, Disjoint (W : Set X) K → η.hom.app (op W) = 0)
    {W : Opens X} (hW : Disjoint (W : Set X) K) :
    (cokernelToGodementEnd η).hom.app (op W) = 0 := by
  let π := cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)
  refine app_eq_zero_of_stalkFunctor_map_eq_zero fun x hxW ↦ ?_
  have hxK : x ∉ K := Set.disjoint_left.1 hW hxW
  have hepi : Epi ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π.hom) :=
    epi_stalkFunctor_map π x
  rw [← cancel_epi ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π.hom),
    ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom, π_cokernelToGodementEnd,
    ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp,
    stalkFunctor_map_eq_zero_of_notMem hK
      (fun V hV ↦ godement_map_app_eq_zero hK hzero hV) hxK,
    Limits.zero_comp, Limits.comp_zero]

/-- Descending a family of endomorphisms `η i` to `cokernel (toGodement)` preserves finite sums
acting as the identity on opens. -/
private lemma sum_cokernelToGodementEnd_app_eq_id {F : X.Sheaf AddCommGrpCat.{u}} {ι : Type u}
    {η : ι → (F ⟶ F)} {W : Opens X} {s : Finset ι}
    (hsum : ∀ V : Opens X, V ≤ W → ∑ i ∈ s, (η i).hom.app (op V) = 𝟙 (F.obj.obj (op V))) :
    ∑ i ∈ s, (cokernelToGodementEnd (η i)).hom.app (op W) =
      𝟙 ((cokernel ((toGodement AddCommGrpCat.{u} X).app F)).obj.obj (op W)) := by
  let π := cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)
  refine sum_app_eq_id_of_sum_stalkFunctor_map_eq_id fun x hxW ↦ ?_
  have hepi : Epi ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π.hom) :=
    epi_stalkFunctor_map π x
  have hG := sum_stalkFunctor_map_eq_id
    (F := (godement AddCommGrpCat.{u} X).obj F)
    (η := fun i ↦ (godement AddCommGrpCat.{u} X).map (η i)) (W := W) (s := s)
    (fun V hVW ↦ sum_godement_map_app_eq_id fun W' hW'V ↦ hsum W' (hW'V.trans hVW)) hxW
  rw [← cancel_epi ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π.hom),
    Category.comp_id, Preadditive.comp_sum]
  have hcomm (i : ι) :
      (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π.hom ≫
          (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (cokernelToGodementEnd (η i)).hom =
        (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((godement AddCommGrpCat.{u} X).map (η i)).hom ≫
          (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π.hom := by
    rw [← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom, π_cokernelToGodementEnd,
      ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
  simp only [hcomm, ← Preadditive.sum_comp, hG, Category.id_comp]

/-- The cokernel of `toGodement` on a fine sheaf of abelian groups is again fine. -/
instance isFine_cokernel_toGodement_app (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFine] :
    (cokernel ((toGodement AddCommGrpCat.{u} X).app F)).IsFine where
  exists_partition U hU := by
    obtain ⟨K, η, hlf, hclosed, hsub, hzero, hsum⟩ := IsFine.exists_partition (F := F) U hU
    refine ⟨K, fun i ↦ cokernelToGodementEnd (η i), hlf, hclosed, hsub,
      fun i W hW ↦ cokernelToGodementEnd_app_eq_zero (hclosed i) (hzero i) hW,
      fun W s hs ↦ sum_cokernelToGodementEnd_app_eq_id fun V hVW ↦
        hsum V s fun i hi ↦ (hs i hi).mono_left (hVW : (V : Set X) ⊆ W)⟩

end StalkTransfer

section LiftingAndAcyclicity

/-- If `b` is a global section of `G⁰(F)` whose image in `Z¹(F)` agrees with `q` on `U`, and `η` is
an endomorphism of `F` vanishing on opens disjoint from a closed subset `K ⊆ U`, then `Z¹(η)`
identifies `π(b)` and `q` globally on `X`. -/
private lemma cokernelToGodementEnd_app_top_eq {F : X.Sheaf AddCommGrpCat.{u}}
    {U : Opens X} {K : Set X} (hK : IsClosed K) (hKU : K ⊆ U) {η : F ⟶ F}
    (hzero : ∀ W : Opens X, Disjoint (W : Set X) K → η.hom.app (op W) = 0)
    (q : (cokernel ((toGodement AddCommGrpCat.{u} X).app F)).obj.obj (op ⊤))
    (b : ((godement AddCommGrpCat.{u} X).obj F).obj.obj (op ⊤))
    (hb : (cokernel ((toGodement AddCommGrpCat.{u} X).app F)).obj.map (homOfLE le_top : U ⟶ ⊤).op
        ((cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)).hom.app (op ⊤) b) =
      (cokernel ((toGodement AddCommGrpCat.{u} X).app F)).obj.map (homOfLE le_top : U ⟶ ⊤).op q) :
    (cokernelToGodementEnd η).hom.app (op ⊤)
        ((cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)).hom.app (op ⊤) b) =
      (cokernelToGodementEnd η).hom.app (op ⊤) q := by
  let Z := cokernel ((toGodement AddCommGrpCat.{u} X).app F)
  let V : Opens X := ⟨Kᶜ, hK.isOpen_compl⟩
  have hcov : (⊤ : Opens X) ≤ U ⊔ V := fun x _ ↦ by
    by_cases hx : x ∈ K
    · exact Or.inl (hKU hx)
    · exact Or.inr hx
  refine Z.eq_of_locally_eq₂ (homOfLE le_top : U ⟶ ⊤) (homOfLE le_top : V ⟶ ⊤) hcov _ _ ?_ ?_
  · rw [← ConcreteCategory.comp_apply, ← (cokernelToGodementEnd η).hom.naturality,
      ConcreteCategory.comp_apply, hb, ← ConcreteCategory.comp_apply,
      (cokernelToGodementEnd η).hom.naturality, ConcreteCategory.comp_apply]
  · have hdisj : Disjoint (V : Set X) K := disjoint_compl_left
    have hV0 := cokernelToGodementEnd_app_eq_zero hK hzero hdisj
    calc Z.obj.map (homOfLE le_top : V ⟶ ⊤).op
          ((cokernelToGodementEnd η).hom.app (op ⊤)
            ((cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)).hom.app (op ⊤) b))
      _ = (cokernelToGodementEnd η).hom.app (op V)
            (Z.obj.map (homOfLE le_top : V ⟶ ⊤).op
              ((cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)).hom.app (op ⊤) b)) := by
          rw [← ConcreteCategory.comp_apply, ← (cokernelToGodementEnd η).hom.naturality,
            ConcreteCategory.comp_apply]
      _ = 0 := by rw [hV0]; rfl
      _ = (cokernelToGodementEnd η).hom.app (op V)
            (Z.obj.map (homOfLE le_top : V ⟶ ⊤).op q) := by rw [hV0]; rfl
      _ = Z.obj.map (homOfLE le_top : V ⟶ ⊤).op ((cokernelToGodementEnd η).hom.app (op ⊤) q) := by
          rw [← ConcreteCategory.comp_apply, (cokernelToGodementEnd η).hom.naturality,
            ConcreteCategory.comp_apply]

/-- Two finite sums of endomorphisms of `G` agree on an open `W` whenever the terms outside their
intersection vanish on `W`. -/
private lemma sum_end_eq_of_disjoint {G : X.Sheaf AddCommGrpCat.{u}} {ι : Type u}
    {K : ι → Set X} {ξ : ι → (G ⟶ G)}
    (hzero : ∀ i (W : Opens X), Disjoint (W : Set X) (K i) → (ξ i).hom.app (op W) = 0)
    {W : Opens X} {s₁ s₂ : Finset ι}
    (hs₁ : ∀ i, i ∉ s₁ → Disjoint (W : Set X) (K i))
    (hs₂ : ∀ i, i ∉ s₂ → Disjoint (W : Set X) (K i))
    (b : ι → G.obj.obj (op W)) :
    ∑ i ∈ s₁, (ξ i).hom.app (op W) (b i) = ∑ i ∈ s₂, (ξ i).hom.app (op W) (b i) := by
  classical
  have hsub₁ : ∑ i ∈ s₁, (ξ i).hom.app (op W) (b i) =
      ∑ i ∈ s₁ ∪ s₂, (ξ i).hom.app (op W) (b i) :=
    Finset.sum_subset Finset.subset_union_left fun i _ hi ↦ by
      rw [hzero i W (hs₁ i hi)]; rfl
  have hsub₂ : ∑ i ∈ s₂, (ξ i).hom.app (op W) (b i) =
      ∑ i ∈ s₁ ∪ s₂, (ξ i).hom.app (op W) (b i) :=
    Finset.sum_subset Finset.subset_union_right fun i _ hi ↦ by
      rw [hzero i W (hs₂ i hi)]; rfl
  exact hsub₁.trans hsub₂.symm

/-- Every global section of `Z¹(F)` locally agrees with the image of a global section of `G⁰(F)`. -/
private lemma exists_global_lift_on_nhds {F : X.Sheaf AddCommGrpCat.{u}}
    (q : (cokernel ((toGodement AddCommGrpCat.{u} X).app F)).obj.obj (op ⊤)) (x : X) :
    ∃ (U : Opens X), x ∈ U ∧ ∃ b : ((godement AddCommGrpCat.{u} X).obj F).obj.obj (op ⊤),
      (cokernel ((toGodement AddCommGrpCat.{u} X).app F)).obj.map (homOfLE le_top : U ⟶ ⊤).op
          ((cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)).hom.app (op ⊤) b) =
        (cokernel ((toGodement AddCommGrpCat.{u} X).app F)).obj.map (homOfLE le_top : U ⟶ ⊤).op
          q := by
  let G := (godement AddCommGrpCat.{u} X).obj F
  let Z := cokernel ((toGodement AddCommGrpCat.{u} X).app F)
  let π : G ⟶ Z := cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)
  have : G.IsFlasque := isFlasque_godement_obj AddCommGrpCat.{u} X F
  have : CategoryTheory.Sheaf.IsLocallySurjective π :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' _ π).2 inferInstance
  obtain ⟨U, iU, ⟨b₀, hb₀⟩, hxU⟩ :=
    CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology X) π.hom q x _root_.trivial
  have hepi : Epi (G.obj.map iU.op) := Presheaf.IsFlasque.epi iU.op
  obtain ⟨b, hb⟩ := (AddCommGrpCat.epi_iff_surjective _).1 hepi b₀
  refine ⟨U, hxU, b, ?_⟩
  have hiU : iU = homOfLE le_top := Subsingleton.elim _ _
  subst hiU
  rw [← ConcreteCategory.comp_apply, ← π.hom.naturality, ConcreteCategory.comp_apply, hb, hb₀]

/-- Pointwise evaluation of `π ∘ G⁰(η)` on a global lift `b` whose cokernel image agrees with `q` on
`U ⊇ K`. -/
private lemma cokernel_π_godement_map_eq {F : X.Sheaf AddCommGrpCat.{u}}
    {U W : Opens X} {K : Set X} (hK : IsClosed K) (hKU : K ⊆ U) {η : F ⟶ F}
    (hzero : ∀ V : Opens X, Disjoint (V : Set X) K → η.hom.app (op V) = 0)
    (q : (cokernel ((toGodement AddCommGrpCat.{u} X).app F)).obj.obj (op ⊤))
    (b : ((godement AddCommGrpCat.{u} X).obj F).obj.obj (op ⊤))
    (hb : (cokernel ((toGodement AddCommGrpCat.{u} X).app F)).obj.map (homOfLE le_top : U ⟶ ⊤).op
        ((cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)).hom.app (op ⊤) b) =
      (cokernel ((toGodement AddCommGrpCat.{u} X).app F)).obj.map (homOfLE le_top : U ⟶ ⊤).op q) :
    (cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)).hom.app (op W)
        (((godement AddCommGrpCat.{u} X).map η).hom.app (op W)
          (((godement AddCommGrpCat.{u} X).obj F).obj.map (homOfLE le_top : W ⟶ ⊤).op b)) =
      (cokernelToGodementEnd η).hom.app (op W)
        ((cokernel ((toGodement AddCommGrpCat.{u} X).app F)).obj.map
          (homOfLE le_top : W ⟶ ⊤).op q) := by
  let G := (godement AddCommGrpCat.{u} X).obj F
  let Z := cokernel ((toGodement AddCommGrpCat.{u} X).app F)
  let π : G ⟶ Z := cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)
  let ξ : G ⟶ G := (godement AddCommGrpCat.{u} X).map η
  have h₁ : (ξ ≫ π).hom.app (op W) = (π ≫ cokernelToGodementEnd η).hom.app (op W) :=
    congrArg (fun m ↦ m.hom.app (op W)) (π_cokernelToGodementEnd η).symm
  have hcomm :
      π.hom.app (op W) (ξ.hom.app (op W) (G.obj.map (homOfLE le_top : W ⟶ ⊤).op b)) =
        Z.obj.map (homOfLE le_top : W ⟶ ⊤).op
          ((cokernelToGodementEnd η).hom.app (op ⊤) (π.hom.app (op ⊤) b)) := by
    calc π.hom.app (op W) (ξ.hom.app (op W) (G.obj.map (homOfLE le_top : W ⟶ ⊤).op b))
      _ = (ξ ≫ π).hom.app (op W) (G.obj.map (homOfLE le_top : W ⟶ ⊤).op b) := rfl
      _ = (π ≫ cokernelToGodementEnd η).hom.app (op W)
            (G.obj.map (homOfLE le_top : W ⟶ ⊤).op b) := by rw [h₁]
      _ = (cokernelToGodementEnd η).hom.app (op W)
            (Z.obj.map (homOfLE le_top : W ⟶ ⊤).op (π.hom.app (op ⊤) b)) := by
          simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
            ← ConcreteCategory.comp_apply, ← π.hom.naturality]
          rfl
      _ = Z.obj.map (homOfLE le_top : W ⟶ ⊤).op
            ((cokernelToGodementEnd η).hom.app (op ⊤) (π.hom.app (op ⊤) b)) := by
          rw [← ConcreteCategory.comp_apply, (cokernelToGodementEnd η).hom.naturality,
            ConcreteCategory.comp_apply]
  rw [hcomm, cokernelToGodementEnd_app_top_eq hK hKU hzero q b hb,
    ← ConcreteCategory.comp_apply, ← (cokernelToGodementEnd η).hom.naturality,
    ConcreteCategory.comp_apply]

/-- Around each point `y : X`, a locally finite family `K : ι → Set X` meets only finitely many
members on an open neighborhood `W` of `y`. -/
private lemma exists_open_finset_disjoint_of_locallyFinite {ι : Type u} {K : ι → Set X}
    (hlf : LocallyFinite K) (y : X) :
    ∃ (W : Opens X) (s : Finset ι), y ∈ W ∧ ∀ i, i ∉ s → Disjoint (W : Set X) (K i) := by
  obtain ⟨V, hyV, hVfin⟩ := hlf y
  obtain ⟨W₀, hW₀V, hW₀open, hyW₀⟩ := mem_nhds_iff.1 hyV
  have hW₀fin : {i : ι | (K i ∩ W₀).Nonempty}.Finite :=
    hVfin.subset fun i (hi : (K i ∩ W₀).Nonempty) ↦ hi.mono (Set.inter_subset_inter_right _ hW₀V)
  exact ⟨⟨W₀, hW₀open⟩, hW₀fin.toFinset, hyW₀, fun i hi ↦
    Set.disjoint_left.2 fun z hzW hzK ↦ hi (hW₀fin.mem_toFinset.2 ⟨z, hzK, hzW⟩)⟩

/-- Glue local Godement lifts `b x` weighted by `(godement _ X).map (η x)` along a refinement `W`
meeting only finitely many supports `K x`. -/
private lemma exists_glued_godement_section {F : X.Sheaf AddCommGrpCat.{u}}
    {K : X → Set X} (hclosed : ∀ x, IsClosed (K x)) {η : X → (F ⟶ F)}
    (hzero : ∀ x (V : Opens X), Disjoint (V : Set X) (K x) → (η x).hom.app (op V) = 0)
    (b : X → ((godement AddCommGrpCat.{u} X).obj F).obj.obj (op ⊤))
    {W : X → Opens X} (hWtop : ⨆ y, W y = ⊤) {s : X → Finset X}
    (hs : ∀ y x, x ∉ s y → Disjoint (W y : Set X) (K x)) :
    ∃ g : ((godement AddCommGrpCat.{u} X).obj F).obj.obj (op ⊤), ∀ y : X,
      ((godement AddCommGrpCat.{u} X).obj F).obj.map (homOfLE le_top : W y ⟶ ⊤).op g =
        ∑ x ∈ s y, (((godement AddCommGrpCat.{u} X).map (η x)).hom.app (op (W y)))
          (((godement AddCommGrpCat.{u} X).obj F).obj.map (homOfLE le_top : W y ⟶ ⊤).op (b x)) := by
  let G := (godement AddCommGrpCat.{u} X).obj F
  let ξ : X → (G ⟶ G) := fun x ↦ (godement AddCommGrpCat.{u} X).map (η x)
  have hξzero (x : X) (V : Opens X) (hV : Disjoint (V : Set X) (K x)) :
      (ξ x).hom.app (op V) = 0 :=
    godement_map_app_eq_zero (hclosed x) (hzero x) hV
  let sf : ∀ y : X, G.obj.obj (op (W y)) := fun y ↦
    ∑ x ∈ s y, (ξ x).hom.app (op (W y)) (G.obj.map (homOfLE le_top : W y ⟶ ⊤).op (b x))
  have hcompat : Presheaf.IsCompatible G.obj W sf := fun y₁ y₂ ↦ by
    let V := W y₁ ⊓ W y₂
    have hnat (y : X) (iV : V ⟶ W y) (x : X) :
        G.obj.map iV.op ((ξ x).hom.app (op (W y))
            (G.obj.map (homOfLE le_top : W y ⟶ ⊤).op (b x))) =
          (ξ x).hom.app (op V) (G.obj.map (homOfLE le_top : V ⟶ ⊤).op (b x)) := by
      rw [← ConcreteCategory.comp_apply, ← (ξ x).hom.naturality, ConcreteCategory.comp_apply]
      congr 1
      rw [← ConcreteCategory.comp_apply, ← G.obj.map_comp]
      rfl
    simp only [sf, map_sum, hnat y₁ (Opens.infLELeft _ _), hnat y₂ (Opens.infLERight _ _)]
    exact sum_end_eq_of_disjoint hξzero
      (fun x hx ↦ (hs y₁ x hx).mono_left (inf_le_left : V ≤ W y₁))
      (fun x hx ↦ (hs y₂ x hx).mono_left (inf_le_right : V ≤ W y₂)) _
  obtain ⟨g₀, hg₀, -⟩ := (Presheaf.isSheaf_iff_isSheafUniqueGluing G.obj).1 G.property W sf hcompat
  refine ⟨G.obj.map (eqToHom hWtop.symm).op g₀, fun y ↦ ?_⟩
  rw [← ConcreteCategory.comp_apply, ← G.obj.map_comp, ← op_comp,
    Subsingleton.elim ((homOfLE le_top : W y ⟶ ⊤) ≫ eqToHom hWtop.symm) (Opens.leSupr W y)]
  exact hg₀ y

/-- When `F` is fine, every global section of `cokernel ((toGodement AddCommGrpCat X).app F)` lifts
to a global section of `(godement AddCommGrpCat X).obj F`. -/
theorem cokernel_π_toGodement_app_top_surjective (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFine] :
    Function.Surjective
      ((cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)).hom.app (op ⊤)) := by
  classical
  intro q
  let Z := cokernel ((toGodement AddCommGrpCat.{u} X).app F)
  let π := cokernel.π ((toGodement AddCommGrpCat.{u} X).app F)
  choose U hxU b hb using exists_global_lift_on_nhds q
  have hU : ⨆ x, U x = ⊤ := top_unique fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxU x⟩
  obtain ⟨K, η, hlf, hclosed, hsub, hzero, hsum⟩ := IsFine.exists_partition (F := F) U hU
  choose W s hyW hs using exists_open_finset_disjoint_of_locallyFinite hlf
  have hWtop : ⨆ y, W y = ⊤ := top_unique fun y _ ↦ Opens.mem_iSup.2 ⟨y, hyW y⟩
  obtain ⟨g, hgW⟩ := exists_glued_godement_section hclosed hzero b hWtop hs
  refine ⟨g, Z.eq_of_locally_eq' (U := W) (⊤ : Opens X) (fun _ ↦ homOfLE le_top) hWtop.ge _ _
    fun y ↦ ?_⟩
  rw [← ConcreteCategory.comp_apply, ← π.hom.naturality, ConcreteCategory.comp_apply, hgW y]
  have hterm (x : X) :
      π.hom.app (op (W y))
          ((((godement AddCommGrpCat.{u} X).map (η x)).hom.app (op (W y)))
            (((godement AddCommGrpCat.{u} X).obj F).obj.map (homOfLE le_top : W y ⟶ ⊤).op (b x))) =
        (cokernelToGodementEnd (η x)).hom.app (op (W y))
          (Z.obj.map (homOfLE le_top : W y ⟶ ⊤).op q) :=
    cokernel_π_godement_map_eq (hclosed x) (hsub x) (hzero x) q (b x) (hb x)
  simp only [map_sum, hterm, ← finset_sum_hom_apply]
  rw [sum_cokernelToGodementEnd_app_eq_id fun V hVW ↦
    hsum V (s y) fun x hx ↦ (hs y x hx).mono_left (hVW : (V : Set X) ⊆ W y)]
  rfl

/-- The short exact sequence `0 ⟶ F ⟶ G⁰(F) ⟶ coker(F ⟶ G⁰(F)) ⟶ 0`. -/
private lemma toGodement_shortExact (F : X.Sheaf AddCommGrpCat.{u}) :
    (ShortComplex.mk ((toGodement AddCommGrpCat.{u} X).app F)
      (cokernel.π ((toGodement AddCommGrpCat.{u} X).app F))
      (cokernel.condition _)).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

/-- Dimension-shifting induction: every fine sheaf has vanishing `H' (n + 1) ⊤`. -/
private lemma subsingleton_H'_succ_top_of_isFine_aux (n : ℕ) :
    ∀ (F : X.Sheaf AddCommGrpCat.{u}), F.IsFine →
      Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) (⊤ : Opens X)) := by
  induction n with
  | zero =>
    intro F hF
    have hS := toGodement_shortExact F
    have : Presheaf.IsFlasque ((godement AddCommGrpCat.{u} X).obj F).obj :=
      isFlasque_godement_obj AddCommGrpCat.{u} X F
    exact CategoryTheory.Sheaf.H'.subsingleton_X₁_one hS (⊤ : Opens X)
      (cokernel_π_toGodement_app_top_surjective F)
      (TauCeti.Topology.subsingleton_H'_succ_of_isFlasque
        ((godement AddCommGrpCat.{u} X).obj F) 0 (⊤ : Opens X))
  | succ n ih =>
    intro F hF
    have hS := toGodement_shortExact F
    have : Presheaf.IsFlasque ((godement AddCommGrpCat.{u} X).obj F).obj :=
      isFlasque_godement_obj AddCommGrpCat.{u} X F
    exact CategoryTheory.Sheaf.H'.subsingleton_X₁ hS (⊤ : Opens X) (n + 1)
      (ih _ (isFine_cokernel_toGodement_app F))
      (TauCeti.Topology.subsingleton_H'_succ_of_isFlasque
        ((godement AddCommGrpCat.{u} X).obj F) (n + 1) (⊤ : Opens X))

/-- A fine sheaf of abelian groups has vanishing cohomology `H' (n + 1) ⊤` in every positive
degree. -/
instance subsingleton_H'_succ_top_of_isFine (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFine] (n : ℕ) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) (⊤ : Opens X)) :=
  subsingleton_H'_succ_top_of_isFine_aux n F inferInstance

/-- A fine sheaf of abelian groups has vanishing cohomology `H' n ⊤` for every `n > 0`. -/
theorem subsingleton_H'_top_of_isFine (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFine]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F n (⊤ : Opens X)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  infer_instance

/-- A fine sheaf of abelian groups has vanishing cohomology `Sheaf.H` in every positive degree. -/
instance subsingleton_H_succ_of_isFine (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFine] (n : ℕ) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} F (n + 1)) := by
  have := subsingleton_H'_succ_top_of_isFine F n
  exact Function.Injective.subsingleton
    (f := ConcreteCategory.hom (F.cohomologyPresheafObjIsoH (n + 1) isTerminalTop).inv)
    (ConcreteCategory.bijective_of_isIso _).injective

/-- **Acyclicity of fine sheaves.** A fine sheaf of abelian groups on a topological space has
vanishing sheaf cohomology `Sheaf.H` in every positive degree. -/
theorem subsingleton_H_of_isFine (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFine]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} F n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  infer_instance

/-- If the restriction `U.sheafRestrict.obj F` of an abelian sheaf `F` to an open subset `U` is
fine, then `F` has vanishing cohomology `H' (n + 1) U` over `U`. -/
instance subsingleton_H'_succ_of_isFine_sheafRestrict (F : X.Sheaf AddCommGrpCat.{u})
    (U : Opens X) [IsFine (X := TopCat.of U) (U.sheafRestrict.obj F)] (n : ℕ) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) U) := by
  have : PreservesFiniteColimits (U.sheafRestrict (C := AddCommGrpCat.{u})) := by
    have hp : PreservesFiniteColimits
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion') := by
      have := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        U.inclusion').leftAdjoint_preservesColimits.{0, 0}
      infer_instance
    exact @preservesFiniteColimits_of_natIso _ _ _ _ _ _
      (U.isOpenEmbedding.sheafPullbackIso (A := AddCommGrpCat.{u})) hp
  have : PreservesFiniteColimits
      ((Opens.grothendieckTopology X).overPullback AddCommGrpCat.{u} U) :=
    preservesFiniteColimits_of_natIso
      (U.sheafRestrictSheafEquivOver (A := AddCommGrpCat.{u}))
  let eOver : F.H' (n + 1) U ≅ AddCommGrpCat.of ((F.over U).H (n + 1)) :=
    ((Opens.grothendieckTopology X).cohomologyPresheafEvaluationIsoFunctorOverH U (n + 1)).app F
  let eSh : U.sheafEquivOver.inverse.obj (U.sheafRestrict.obj F) ≅ F.over U :=
    U.sheafRestrictSheafEquivOver.app F
  let eTop : (U.sheafEquivOver.inverse.obj (U.sheafRestrict.obj F)).H' (n + 1) (Over.mk (𝟙 U)) ≅
      AddCommGrpCat.of ((U.sheafEquivOver.inverse.obj (U.sheafRestrict.obj F)).H (n + 1)) :=
    (U.sheafEquivOver.inverse.obj (U.sheafRestrict.obj F)).cohomologyPresheafObjIsoH (n + 1)
      (Over.mkIdTerminal (X := U))
  let eCongr :
      (U.sheafEquivOver.inverse.obj (U.sheafRestrict.obj F)).H' (n + 1) (Over.mk (𝟙 U)) ≅
        (U.sheafRestrict.obj F).H' (n + 1) (U.overEquivalence.symm.inverse.obj (Over.mk (𝟙 U))) :=
    TauCeti.CategoryTheory.cohomologyPresheafObjIsoSheafCongr
      (Opens.grothendieckTopology U) ((Opens.grothendieckTopology X).over U)
      U.overEquivalence.symm (U.sheafRestrict.obj F) (n + 1) (Over.mk (𝟙 U))
  have htop : U.overEquivalence.symm.inverse.obj (Over.mk (𝟙 U)) = (⊤ : Opens U) :=
    top_unique fun x _ ↦ x.2
  have hsub : Subsingleton ((U.sheafRestrict.obj F).H' (n + 1)
      (U.overEquivalence.symm.inverse.obj (Over.mk (𝟙 U)))) := by
    rw [htop]
    exact subsingleton_H'_succ_top_of_isFine (X := TopCat.of U) (U.sheafRestrict.obj F) n
  let eAll : F.H' (n + 1) U ≅
      (U.sheafRestrict.obj F).H' (n + 1) (U.overEquivalence.symm.inverse.obj (Over.mk (𝟙 U))) :=
    eOver ≪≫ (CategoryTheory.Sheaf.functorH _ (n + 1)).mapIso eSh.symm ≪≫ eTop.symm ≪≫ eCongr
  exact Function.Injective.subsingleton (f := ConcreteCategory.hom eAll.hom)
    (ConcreteCategory.bijective_of_isIso _).injective

/-- If `U.sheafRestrict.obj F` is fine, then `F` has vanishing cohomology `H' n U` for every
`n > 0`. -/
theorem subsingleton_H'_of_isFine_sheafRestrict (F : X.Sheaf AddCommGrpCat.{u})
    (U : Opens X) [IsFine (X := TopCat.of U) (U.sheafRestrict.obj F)] (n : ℕ) (hn : 0 < n) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F n U) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  infer_instance

end LiftingAndAcyclicity

end TopCat.Sheaf
