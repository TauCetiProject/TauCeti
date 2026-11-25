/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Shift.Basic
public import TauCeti.Algebra.Category.Grp.Coproducts
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Compact objects for coproducts in a preadditive category

An object `G` of a preadditive category `C` (with morphisms in `Type v`) is **compact for
coproducts** (`TauCeti.IsCompactForCoproducts G`) if `preadditiveCoyoneda.obj (op G)` preserves all
`Type v`-indexed coproducts. For every colimit cofan `c` on `f : J → C`, the comparison homomorphism
`directSumHom G c : (⨁ j, (G ⟶ f j)) →+ (G ⟶ c.pt)` sending `g : G ⟶ f j` to `g ≫ c.inj j` is
always injective (`TauCeti.directSumHom_injective`), and `G` is compact iff `directSumHom G c` is
bijective (equivalently, surjective) for all `Type v`-indexed colimit cofans. Compactness holds for
zero objects, is closed under isomorphisms, retracts, finite coproducts, arbitrary shifts,
equivalences, and left adjoints whose right adjoint preserves coproducts, and in `AddCommGrpCat.{v}`
holds for `ULift ℤ` while failing for `∐ₙ ULift ℤ`.

## Main declarations

* `TauCeti.IsCompactForCoproducts`, `TauCeti.directSumHom`,
  `TauCeti.IsCompactForCoproducts.directSumEquiv`,
  `TauCeti.IsCompactForCoproducts.coprodDirectSumEquiv`.
* `TauCeti.directSumHom_injective`, `TauCeti.isCompactForCoproducts_iff_bijective_directSumHom`,
  `TauCeti.isCompactForCoproducts_iff_surjective_directSumHom`.
* `TauCeti.IsCompactForCoproducts.of_isColimit_cofan_finite`,
  `TauCeti.IsCompactForCoproducts.shift`, `CategoryTheory.Retract.isCompactForCoproducts`,
  `CategoryTheory.Adjunction.isCompactForCoproducts_left`.
* `AddCommGrpCat.isCompactForCoproducts_ulift_int`,
  `AddCommGrpCat.not_isCompactForCoproducts_coproduct_nat`.

## References

* S. Schwede, *Symmetric spectra*, Chapter II, Definition 5.4 and Lemma 5.6.
* A. Neeman, *Triangulated categories*, Annals of Mathematics Studies 148, Princeton University
  Press (2001), Definition 4.2.7.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject
open scoped DirectSum

universe u u₁ u₂ v w

namespace TauCeti

section Basic

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- An object `G` of a preadditive category is compact for coproducts if its additive represented
functor `preadditiveCoyoneda.obj (op G)` preserves all `Type v`-indexed coproducts. -/
def IsCompactForCoproducts (G : C) : Prop :=
  ∀ J : Type v, PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G))

lemma isCompactForCoproducts_def (G : C) :
    IsCompactForCoproducts G ↔
      ∀ J : Type v, PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G)) :=
  Iff.rfl

/-- A compact object preserves coproducts indexed by any `J : Type v`. -/
lemma IsCompactForCoproducts.preservesColimitsOfShape {G : C} (hG : IsCompactForCoproducts G)
    (J : Type v) : PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G)) := hG J

/-- A compact object preserves coproducts indexed by any `v`-small type `J`. -/
lemma IsCompactForCoproducts.preservesColimitsOfShape_of_small {G : C}
    (hG : IsCompactForCoproducts G) (J : Type w) [Small.{v} J] :
    PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G)) :=
  have := hG (Shrink.{v} J)
  preservesColimitsOfShape_of_equiv (Discrete.equivalence (equivShrink.{v} J).symm) _

/-- Compactness for coproducts is invariant under isomorphism. -/
lemma IsCompactForCoproducts.of_iso {G H : C} (hG : IsCompactForCoproducts G) (e : G ≅ H) :
    IsCompactForCoproducts H := fun J ↦
  have := hG J
  preservesColimitsOfShape_of_natIso (preadditiveCoyoneda.mapIso e.symm.op)

lemma isCompactForCoproducts_iff_of_iso {G H : C} (e : G ≅ H) :
    IsCompactForCoproducts G ↔ IsCompactForCoproducts H :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- The canonical comparison homomorphism `(⨁ j, (G ⟶ f j)) →+ (G ⟶ c.pt)` associated to a cofan
`c` on `f : J → C`, sending the `j`-th summand `g : G ⟶ f j` to `g ≫ c.inj j`. -/
def directSumHom (G : C) {J : Type w} [DecidableEq J] {f : J → C} (c : Cofan f) :
    (⨁ j : J, (G ⟶ f j)) →+ (G ⟶ c.pt) :=
  DirectSum.toAddMonoid fun j ↦ Preadditive.rightComp G (c.inj j)

lemma directSumHom_def (G : C) {J : Type w} [DecidableEq J] {f : J → C} (c : Cofan f) :
    directSumHom G c = DirectSum.toAddMonoid fun j ↦ Preadditive.rightComp G (c.inj j) := (rfl)

@[simp]
lemma directSumHom_of (G : C) {J : Type w} [DecidableEq J] {f : J → C} (c : Cofan f) (j : J)
    (g : G ⟶ f j) : directSumHom G c (DirectSum.of (fun j ↦ G ⟶ f j) j g) = g ≫ c.inj j := by
  simp [directSumHom, Preadditive.rightComp]

/-- The canonical projection `c.pt ⟶ f k` onto the `k`-th summand of a colimit cofan `c` in a
preadditive category. -/
private def cofanProj {J : Type w} [DecidableEq J] {f : J → C} {c : Cofan f} (hc : IsColimit c)
    (k : J) : c.pt ⟶ f k :=
  Cofan.IsColimit.desc hc fun j ↦ if h : j = k then eqToHom (by rw [h]) else 0

private lemma inj_comp_cofanProj {J : Type w} [DecidableEq J] {f : J → C} {c : Cofan f}
    (hc : IsColimit c) (j k : J) :
    c.inj j ≫ cofanProj hc k = if h : j = k then eqToHom (by rw [h]) else 0 :=
  Cofan.IsColimit.fac hc _ j

/-- The endomorphism of a colimit cofan killing all summands in a finite set `s` and fixing the
complement. -/
private def cofanTail {J : Type w} [DecidableEq J] {f : J → C} {c : Cofan f} (hc : IsColimit c)
    (s : Finset J) : c.pt ⟶ c.pt :=
  Cofan.IsColimit.desc hc fun j ↦ if j ∈ s then 0 else c.inj j

private lemma inj_comp_cofanTail_of_mem {J : Type w} [DecidableEq J] {f : J → C} {c : Cofan f}
    (hc : IsColimit c) {s : Finset J} {j : J} (hj : j ∈ s) :
    c.inj j ≫ cofanTail hc s = 0 := by simp [cofanTail, hj]

private lemma cofanTail_add_sum_proj {J : Type w} [DecidableEq J] {f : J → C} {c : Cofan f}
    (hc : IsColimit c) (s : Finset J) :
    cofanTail hc s + ∑ j ∈ s, cofanProj hc j ≫ c.inj j = 𝟙 c.pt := by
  refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
  rw [Preadditive.comp_add, cofanTail, Cofan.IsColimit.fac, Preadditive.comp_sum, Category.comp_id]
  have hterm : ∀ j ∈ s, c.inj i ≫ cofanProj hc j ≫ c.inj j =
      if i = j then c.inj i else 0 := fun j _ ↦ by
    rw [← Category.assoc, inj_comp_cofanProj]
    split_ifs with h
    · subst h; simp
    · simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq s i (fun _ ↦ c.inj i)]
  split_ifs <;> simp

private lemma directSumHom_comp_cofanProj (G : C) {J : Type w} [DecidableEq J] {f : J → C}
    {c : Cofan f} (hc : IsColimit c) (x : ⨁ j : J, (G ⟶ f j)) (k : J) :
    directSumHom G c x ≫ cofanProj hc k = x k := by
  refine DirectSum.induction_on x (by simp) (fun j g ↦ ?_) (fun u v hu hv ↦ ?_)
  · rw [directSumHom_of, Category.assoc, inj_comp_cofanProj]
    split_ifs with h
    · subst h; simp [DirectSum.of_eq_same]
    · simp [DirectSum.of_eq_of_ne (β := fun j ↦ G ⟶ f j) j k g (Ne.symm h)]
  · rw [map_add, Preadditive.add_comp, hu, hv, DirectSum.add_apply]

/-- For every object `G` and every colimit cofan `c` in a preadditive category, the canonical
direct-sum comparison homomorphism `directSumHom G c` is always injective. -/
theorem directSumHom_injective (G : C) {J : Type w} [DecidableEq J] {f : J → C} {c : Cofan f}
    (hc : IsColimit c) : Function.Injective (directSumHom G c) :=
  (injective_iff_map_eq_zero _).2 fun x hx ↦ DFinsupp.ext fun k ↦ by
    rw [← directSumHom_comp_cofanProj G hc x k, hx, Limits.zero_comp]; rfl

/-- `preadditiveCoyoneda.obj (op G)` preserves a colimit cofan `c` indexed by `J : Type v` if and
only if the direct-sum comparison map `directSumHom G c` is bijective. -/
theorem preservesColimit_discrete_iff_bijective_directSumHom (G : C) {J : Type v} [DecidableEq J]
    {f : J → C} {c : Cofan f} (hc : IsColimit c) :
    PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (op G)) ↔
      Function.Bijective (directSumHom G c) := by
  have hc' : IsColimit (Cofan.mk c.pt c.inj) :=
    hc.ofIsoColimit (Cocone.ext (Iso.refl _) fun ⟨j⟩ ↦ by simp [Cofan.inj])
  have h1 : PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (op G)) ↔
      Nonempty (IsColimit ((preadditiveCoyoneda.obj (op G)).mapCocone (Cofan.mk c.pt c.inj))) :=
    ⟨fun _ ↦ ⟨isColimitOfPreserves _ hc'⟩,
      fun ⟨h⟩ ↦ preservesColimit_of_preserves_colimit_cocone hc' h⟩
  rw [h1, (isColimitMapCoconeCofanMkEquiv _ f c.inj).nonempty_congr,
    AddCommGrpCat.isColimit_cofan_iff_bijective]
  rfl

/-- `preadditiveCoyoneda.obj (op G)` preserves a colimit cofan `c` indexed by `J : Type v` if and
only if the direct-sum comparison map `directSumHom G c` is surjective. -/
theorem preservesColimit_discrete_iff_surjective_directSumHom (G : C) {J : Type v} [DecidableEq J]
    {f : J → C} {c : Cofan f} (hc : IsColimit c) :
    PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (op G)) ↔
      Function.Surjective (directSumHom G c) := by
  rw [preservesColimit_discrete_iff_bijective_directSumHom G hc]
  exact ⟨Function.Bijective.surjective, fun hs ↦ ⟨directSumHom_injective G hc, hs⟩⟩

/-- An object `G` is compact for coproducts if and only if for every `J : Type v` and every colimit
cofan `c` indexed by `J`, the direct-sum comparison map `directSumHom G c` is bijective. -/
theorem isCompactForCoproducts_iff_bijective_directSumHom (G : C) :
    IsCompactForCoproducts G ↔
      ∀ (J : Type v) [DecidableEq J] (f : J → C) (c : Cofan f), IsColimit c →
        Function.Bijective (directSumHom G c) := by
  refine ⟨fun hG J _ f c hc ↦
    have := hG J; (preservesColimit_discrete_iff_bijective_directSumHom G hc).1 inferInstance,
    fun h J ↦ ⟨fun {K} ↦ ?_⟩⟩
  classical
  have eK : Discrete.functor (fun j ↦ K.obj ⟨j⟩) ≅ K := Discrete.natIso fun ⟨_⟩ ↦ Iso.refl _
  have : PreservesColimit (Discrete.functor fun j ↦ K.obj ⟨j⟩) (preadditiveCoyoneda.obj (op G)) :=
    ⟨fun {c} hc ↦
      have := (preservesColimit_discrete_iff_bijective_directSumHom G hc).2 (h J _ c hc)
      ⟨isColimitOfPreserves _ hc⟩⟩
  exact preservesColimit_of_iso_diagram _ eK

/-- An object `G` is compact for coproducts if and only if for every `J : Type v` and every colimit
cofan `c` indexed by `J`, every morphism `G ⟶ c.pt` factors through a finite sub-coproduct
(equivalently, `directSumHom G c` is surjective). -/
theorem isCompactForCoproducts_iff_surjective_directSumHom (G : C) :
    IsCompactForCoproducts G ↔
      ∀ (J : Type v) [DecidableEq J] (f : J → C) (c : Cofan f), IsColimit c →
        Function.Surjective (directSumHom G c) := by
  rw [isCompactForCoproducts_iff_bijective_directSumHom]
  exact forall₅_congr fun _ _ _ _ hc ↦
    ⟨Function.Bijective.surjective, fun hs ↦ ⟨directSumHom_injective G hc, hs⟩⟩

/-- If `preadditiveCoyoneda.obj (op G)` preserves `Discrete J`-colimits for a `v`-small type `J`,
then `directSumHom G c` is bijective for every colimit cofan `c` indexed by `J`. -/
theorem bijective_directSumHom_of_preserves (G : C) {J : Type w} [Small.{v} J] [DecidableEq J]
    {f : J → C} {c : Cofan f} (hc : IsColimit c)
    [PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G))] :
    Function.Bijective (directSumHom G c) := by
  classical
  let e := equivShrink.{v} J
  let c' : Cofan (f ∘ e.symm) := Cofan.mk c.pt fun k ↦ c.inj (e.symm k)
  have : PreservesColimitsOfShape (Discrete (Shrink.{v} J)) (preadditiveCoyoneda.obj (op G)) :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence e) _
  have hbij := (preservesColimit_discrete_iff_bijective_directSumHom G
    ((c.isColimitEquivOfEquiv e.symm) hc)).1 inferInstance
  have hcomp :
      (directSumHom G c).comp (DirectSum.equivCongrLeft e).symm.toAddMonoidHom =
        directSumHom G c' := DirectSum.addHom_ext fun k g ↦ by
    have hsymm : (DirectSum.equivCongrLeft (β := fun j ↦ G ⟶ f j) e).symm
        (DirectSum.of (fun k ↦ G ⟶ f (e.symm k)) k g) =
        DirectSum.of (fun j ↦ G ⟶ f j) (e.symm k) g :=
      (DirectSum.equivCongrLeft e).symm_apply_eq.2
        (DirectSum.equivCongrLeft_of (β := fun j ↦ G ⟶ f j) e k g).symm
    rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hsymm, directSumHom_of]
    exact (directSumHom_of G c' k g).symm
  refine (Function.Bijective.of_comp_iff _ (DirectSum.equivCongrLeft e).symm.bijective).1 ?_
  have hcoe : (directSumHom G c ∘ (DirectSum.equivCongrLeft e).symm) = directSumHom G c' :=
    congrArg DFunLike.coe hcomp
  exact hcoe ▸ hbij

section DirectSumEquivOfPreserves

variable (G : C) {J : Type w} [Small.{v} J] [DecidableEq J] {f : J → C} {c : Cofan f}
  (hc : IsColimit c) [PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G))]

/-- The direct-sum equivalence `(⨁ j, (G ⟶ f j)) ≃+ (G ⟶ c.pt)` for a colimit cofan `c` indexed
by a `v`-small type `J`, whenever `preadditiveCoyoneda.obj (op G)` preserves
`Discrete J`-colimits. -/
def directSumEquivOfPreserves : (⨁ j : J, (G ⟶ f j)) ≃+ (G ⟶ c.pt) :=
  AddEquiv.ofBijective (directSumHom G c) (bijective_directSumHom_of_preserves G hc)

lemma coe_directSumEquivOfPreserves :
    ⇑(directSumEquivOfPreserves G hc) = directSumHom G c :=
  (rfl)

@[simp]
lemma directSumEquivOfPreserves_of (j : J) (g : G ⟶ f j) :
    directSumEquivOfPreserves G hc (DirectSum.of (fun j ↦ G ⟶ f j) j g) = g ≫ c.inj j := by
  simp [directSumEquivOfPreserves]

@[simp]
lemma directSumEquivOfPreserves_symm_comp_inj (j : J) (g : G ⟶ f j) :
    (directSumEquivOfPreserves G hc).symm (g ≫ c.inj j) = DirectSum.of (fun j ↦ G ⟶ f j) j g :=
  (directSumEquivOfPreserves G hc).injective (by simp)

end DirectSumEquivOfPreserves

section CompactDirectSumEquiv

variable {G : C} (hG : IsCompactForCoproducts G) {J : Type w} [Small.{v} J] [DecidableEq J]

/-- For a compact object `G`, maps out of `G` into a colimit cofan `c` indexed by a `v`-small type
identify with the direct sum of the component homomorphism groups. -/
def IsCompactForCoproducts.directSumEquiv {f : J → C} {c : Cofan f} (hc : IsColimit c) :
    (⨁ j : J, (G ⟶ f j)) ≃+ (G ⟶ c.pt) :=
  have := hG.preservesColimitsOfShape_of_small J
  directSumEquivOfPreserves G hc

lemma IsCompactForCoproducts.coe_directSumEquiv {f : J → C} {c : Cofan f} (hc : IsColimit c) :
    ⇑(hG.directSumEquiv hc) = directSumHom G c :=
  (rfl)

@[simp]
lemma IsCompactForCoproducts.directSumEquiv_of {f : J → C} {c : Cofan f} (hc : IsColimit c)
    (j : J) (g : G ⟶ f j) :
    hG.directSumEquiv hc (DirectSum.of (fun j ↦ G ⟶ f j) j g) = g ≫ c.inj j := by
  simp [IsCompactForCoproducts.directSumEquiv]

@[simp]
lemma IsCompactForCoproducts.directSumEquiv_symm_comp_inj {f : J → C} {c : Cofan f}
    (hc : IsColimit c) (j : J) (g : G ⟶ f j) :
    (hG.directSumEquiv hc).symm (g ≫ c.inj j) = DirectSum.of (fun j ↦ G ⟶ f j) j g := by
  simp [IsCompactForCoproducts.directSumEquiv]

/-- For a compact object `G` and a `v`-small family `f : J → C` with a coproduct, maps `G ⟶ ∐ f`
identify with `⨁ j, (G ⟶ f j)`, retaining the canonical inclusions `Sigma.ι f j`. -/
def IsCompactForCoproducts.coprodDirectSumEquiv (f : J → C) [HasCoproduct f] :
    (⨁ j : J, (G ⟶ f j)) ≃+ (G ⟶ ∐ f) :=
  hG.directSumEquiv (coproductIsCoproduct f)

lemma IsCompactForCoproducts.coprodDirectSumEquiv_def (f : J → C) [HasCoproduct f] :
    hG.coprodDirectSumEquiv f = hG.directSumEquiv (coproductIsCoproduct f) :=
  (rfl)

@[simp]
lemma IsCompactForCoproducts.coprodDirectSumEquiv_of (f : J → C) [HasCoproduct f]
    (j : J) (g : G ⟶ f j) :
    hG.coprodDirectSumEquiv f (DirectSum.of (fun j ↦ G ⟶ f j) j g) = g ≫ Sigma.ι f j :=
  hG.directSumEquiv_of (coproductIsCoproduct f) j g

@[simp]
lemma IsCompactForCoproducts.coprodDirectSumEquiv_symm_comp_ι (f : J → C) [HasCoproduct f]
    (j : J) (g : G ⟶ f j) :
    (hG.coprodDirectSumEquiv f).symm (g ≫ Sigma.ι f j) = DirectSum.of (fun j ↦ G ⟶ f j) j g :=
  hG.directSumEquiv_symm_comp_inj (coproductIsCoproduct f) j g

end CompactDirectSumEquiv

end Basic

section Closure

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A finite coproduct of compact objects is compact. -/
theorem IsCompactForCoproducts.of_isColimit_cofan_finite {ι : Type w} [Finite ι] {X : ι → C}
    {c : Cofan X} (hc : IsColimit c) (hX : ∀ i, IsCompactForCoproducts (X i)) :
    IsCompactForCoproducts c.pt := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [isCompactForCoproducts_iff_surjective_directSumHom]
  intro J _ f d hd g
  choose u hu using fun i ↦
    (isCompactForCoproducts_iff_surjective_directSumHom (X i)).1 (hX i) J f d hd (c.inj i ≫ g)
  let s : Finset J := Finset.univ.biUnion fun i ↦ (u i).support
  refine ⟨∑ j ∈ s, DirectSum.of (fun j ↦ c.pt ⟶ f j) j (Cofan.IsColimit.desc hc fun i ↦ u i j),
    Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_⟩
  rw [map_sum, Preadditive.comp_sum, ← hu i, ← DirectSum.sum_support_of (u i), map_sum]
  simp only [directSumHom_of, ← Category.assoc, Cofan.IsColimit.fac]
  exact (Finset.sum_subset (Finset.subset_biUnion_of_mem _ (Finset.mem_univ i))
    fun j _ hj ↦ by rw [DFinsupp.notMem_support_iff.1 hj, Limits.zero_comp]).symm

/-- Every zero object is compact for coproducts. -/
theorem IsCompactForCoproducts.of_isZero {Z : C} (hZ : IsZero Z) : IsCompactForCoproducts Z :=
  IsCompactForCoproducts.of_isColimit_cofan_finite
    (Cofan.IsColimit.mk (Cofan.mk (f := Empty.elim) Z fun i ↦ i.elim) (fun s ↦ hZ.to_ s.pt)
      (fun _ i ↦ i.elim) fun _ _ _ ↦ hZ.eq_of_src _ _)
    fun i : Empty ↦ i.elim

/-- The chosen zero object is compact for coproducts. -/
theorem isCompactForCoproducts_zero [HasZeroObject C] : IsCompactForCoproducts (0 : C) :=
  IsCompactForCoproducts.of_isZero (Limits.isZero_zero C)

/-- A finite coproduct `∐ X` of compact objects is compact. -/
theorem IsCompactForCoproducts.coproduct {ι : Type w} [Finite ι] {X : ι → C} [HasCoproduct X]
    (hX : ∀ i, IsCompactForCoproducts (X i)) : IsCompactForCoproducts (∐ X) :=
  IsCompactForCoproducts.of_isColimit_cofan_finite (coproductIsCoproduct X) hX

/-- A finite biproduct `⨁ X` of compact objects is compact. -/
theorem IsCompactForCoproducts.biproduct {ι : Type w} [Finite ι] {X : ι → C} [HasBiproduct X]
    (hX : ∀ i, IsCompactForCoproducts (X i)) : IsCompactForCoproducts (⨁ X) :=
  IsCompactForCoproducts.of_isColimit_cofan_finite (biproduct.isColimit X) hX

/-- The binary biproduct of two compact objects is compact. -/
theorem IsCompactForCoproducts.biprod {X Y : C} [HasBinaryBiproduct X Y]
    (hX : IsCompactForCoproducts X) (hY : IsCompactForCoproducts Y) :
    IsCompactForCoproducts (X ⊞ Y) :=
  let c : Cofan (Bool.rec Y X) := Cofan.mk (X ⊞ Y) fun b ↦ match b with
    | true => biprod.inl | false => biprod.inr
  IsCompactForCoproducts.of_isColimit_cofan_finite
    (Cofan.IsColimit.mk c (fun s ↦ biprod.desc (s.inj true) (s.inj false))
      (fun _ b ↦ by cases b <;> simp [c])
      (fun _ _ hm ↦ biprod.hom_ext' _ _ (by simpa [c] using hm true) (by simpa [c] using hm false)))
    fun b ↦ by cases b <;> assumption

end Closure

end TauCeti

namespace CategoryTheory

section RetractAndAdjunction

/-- A retract of a compact object is compact. -/
theorem Retract.isCompactForCoproducts {C : Type u} [Category.{v} C] [Preadditive C]
    {G H : C} (r : Retract G H) (hH : TauCeti.IsCompactForCoproducts H) :
    TauCeti.IsCompactForCoproducts G := by
  rw [TauCeti.isCompactForCoproducts_iff_surjective_directSumHom]
  intro J _ f c hc g
  obtain ⟨y, hy⟩ :=
    (TauCeti.isCompactForCoproducts_iff_surjective_directSumHom H).1 hH J f c hc (r.r ≫ g)
  let preI : (⨁ j : J, (H ⟶ f j)) →+ (⨁ j : J, (G ⟶ f j)) :=
    DirectSum.toAddMonoid fun j ↦
      (DirectSum.of (fun j ↦ G ⟶ f j) j).comp (Preadditive.leftComp (f j) r.i)
  have hcommI : ∀ z, TauCeti.directSumHom G c (preI z) = r.i ≫ TauCeti.directSumHom H c z :=
    fun z ↦ DirectSum.induction_on z (by simp)
      (fun _ _ ↦ by simp [preI, Preadditive.leftComp, Category.assoc])
      fun _ _ ha hb ↦ by simp [map_add, ha, hb, Preadditive.comp_add]
  exact ⟨preI y, by rw [hcommI, hy, ← Category.assoc, r.retract, Category.id_comp]⟩

section TwoCategories

variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]

/-- If `L ⊣ R` is an adjunction between preadditive categories with the same morphism universe and
`R` preserves small coproducts, then `L` preserves compact objects. -/
theorem Adjunction.isCompactForCoproducts_left {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) R]
    {G : C} (hG : TauCeti.IsCompactForCoproducts G) :
    TauCeti.IsCompactForCoproducts (L.obj G) := by
  classical
  have : R.IsRightAdjoint := adj.isRightAdjoint
  rw [TauCeti.isCompactForCoproducts_iff_surjective_directSumHom]
  intro J _ f c hc u
  let hc' : IsColimit (Cofan.mk c.pt c.inj) :=
    hc.ofIsoColimit (Cocone.ext (Iso.refl _) fun ⟨_⟩ ↦ by simp [Cofan.inj])
  let hcR := isColimitCofanMkObjOfIsColimit R f c.inj hc'
  obtain ⟨y, hy⟩ := (TauCeti.isCompactForCoproducts_iff_surjective_directSumHom G).1 hG J _ _ hcR
    (adj.homEquiv G c.pt u)
  let s := y.support
  have h0 : adj.homEquiv G c.pt 0 = 0 := by simp [Adjunction.homEquiv_unit]
  have hu_tail : u ≫ TauCeti.cofanTail hc s = 0 := by
    apply (adj.homEquiv G c.pt).injective
    rw [adj.homEquiv_naturality_right, ← hy, h0, ← DirectSum.sum_support_of y, map_sum,
      Preadditive.sum_comp]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [TauCeti.directSumHom_of, Category.assoc, cofan_mk_inj, ← R.map_comp,
      TauCeti.inj_comp_cofanTail_of_mem hc hj, Functor.map_zero, Limits.comp_zero]
  refine ⟨∑ j ∈ s, DirectSum.of (fun j ↦ L.obj G ⟶ f j) j (u ≫ TauCeti.cofanProj hc j), ?_⟩
  rw [map_sum]
  simp only [TauCeti.directSumHom_of, Category.assoc]
  rw [← Preadditive.comp_sum, ← zero_add (u ≫ _), ← hu_tail, ← Preadditive.comp_add,
    TauCeti.cofanTail_add_sum_proj hc s, Category.comp_id]

/-- An equivalence of preadditive categories preserves compact objects. -/
theorem Equivalence.isCompactForCoproducts_functor (e : C ≌ D) {G : C}
    (hG : TauCeti.IsCompactForCoproducts G) : TauCeti.IsCompactForCoproducts (e.functor.obj G) :=
  have : ∀ J : Type v, PreservesColimitsOfShape (Discrete J) e.inverse := fun _ ↦ inferInstance
  e.toAdjunction.isCompactForCoproducts_left hG

/-- An equivalence of preadditive categories preserves and reflects compact objects. -/
theorem Equivalence.isCompactForCoproducts_functor_iff (e : C ≌ D) {G : C} :
    TauCeti.IsCompactForCoproducts (e.functor.obj G) ↔ TauCeti.IsCompactForCoproducts G :=
  ⟨fun h ↦ (e.symm.isCompactForCoproducts_functor h).of_iso (e.unitIso.symm.app G),
    e.isCompactForCoproducts_functor⟩

end TwoCategories

end RetractAndAdjunction

end CategoryTheory

namespace TauCeti

section Shift

variable {C : Type u} [Category.{v} C] [Preadditive C] {A : Type*} [AddGroup A] [HasShift C A]

/-- Shifts of a compact object by any element of an additive group are compact. -/
theorem IsCompactForCoproducts.shift (a : A) {G : C} (hG : IsCompactForCoproducts G) :
    IsCompactForCoproducts (G⟦a⟧) :=
  (shiftEquiv C a).isCompactForCoproducts_functor hG

theorem isCompactForCoproducts_shift_iff (a : A) (G : C) :
    IsCompactForCoproducts (G⟦a⟧) ↔ IsCompactForCoproducts G :=
  (shiftEquiv C a).isCompactForCoproducts_functor_iff

end Shift

end TauCeti

namespace AddCommGrpCat

/-- The free abelian group `ULift ℤ` of rank one is compact for coproducts in `AddCommGrpCat`. -/
theorem isCompactForCoproducts_ulift_int :
    TauCeti.IsCompactForCoproducts (of (ULift.{v} ℤ)) := fun _ ↦
  let e : preadditiveCoyoneda.obj (op (of (ULift.{v} ℤ))) ≅ 𝟭 AddCommGrpCat.{v} :=
    NatIso.ofComponents (fun A ↦ (uliftZMultiplesAddEquiv A).toAddCommGrpIso) fun _ ↦
      AddCommGrpCat.ext fun _ ↦ rfl
  preservesColimitsOfShape_of_natIso e.symm

/-- The countable coproduct `∐ₙ ULift ℤ` is not compact in `AddCommGrpCat`: its identity morphism
has infinitely many nonzero coordinate projections. -/
theorem not_isCompactForCoproducts_coproduct_nat :
    ¬ TauCeti.IsCompactForCoproducts (∐ fun _ : ℕ ↦ of (ULift.{v} ℤ)) := by
  classical
  let Z : ℕ → AddCommGrpCat.{v} := fun _ ↦ of (ULift.{v} ℤ)
  intro hK
  obtain ⟨x, hx⟩ := (hK.coprodDirectSumEquiv Z).surjective (𝟙 (∐ Z))
  obtain ⟨N, hN⟩ := Infinite.exists_notMem_finset x.support
  have hproj : TauCeti.cofanProj (coproductIsCoproduct Z) N = 0 := by
    have h := TauCeti.directSumHom_comp_cofanProj (∐ Z) (coproductIsCoproduct Z) x N
    rw [← hK.coe_directSumEquiv (coproductIsCoproduct Z), ← hK.coprodDirectSumEquiv_def Z] at h
    rw [hx, Category.id_comp, DFinsupp.notMem_support_iff.1 hN] at h
    exact h
  have h1 : (𝟙 (Z N) : Z N ⟶ Z N) = 0 := by
    simpa [hproj] using (TauCeti.inj_comp_cofanProj (coproductIsCoproduct Z) N N).symm
  exact one_ne_zero (congrArg ULift.down (ConcreteCategory.congr_hom h1 (ULift.up (1 : ℤ))))

end AddCommGrpCat

end
