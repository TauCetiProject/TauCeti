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
coproducts** (`TauCeti.IsCompactForCoproducts G`) if the additive represented functor
`preadditiveCoyoneda.obj (op G) : C ⥤ AddCommGrpCat.{v}` preserves all `Type v`-indexed
coproducts. For every colimit cofan `c` on `f : J → C`, the canonical comparison homomorphism
`directSumHom G c : (⨁ j, (G ⟶ f j)) →+ (G ⟶ c.pt)` sending `g : G ⟶ f j` to `g ≫ c.inj j` is
always injective (`TauCeti.directSumHom_injective`), and `G` is compact if and only if
`directSumHom G c` is bijective (equivalently, surjective) for all `Type v`-indexed colimit cofans
(`TauCeti.isCompactForCoproducts_iff_bijective_directSumHom`,
`TauCeti.isCompactForCoproducts_iff_surjective_directSumHom`).

Compactness for coproducts is invariant under isomorphism, holds for zero objects, and is closed
under retracts, finite coproducts, arbitrary shifts, equivalences, and left adjoints whose right
adjoint preserves small coproducts (without assuming additivity of the adjoint or shift functor).
In `AddCommGrpCat.{v}`, the generator `ULift ℤ` is compact whereas the countable coproduct
`∐ₙ ULift ℤ` is not.

## Main definitions

* `TauCeti.IsCompactForCoproducts`: the compactness predicate on objects of a preadditive category.
* `TauCeti.directSumHom`: the canonical comparison map `(⨁ j, (G ⟶ f j)) →+ (G ⟶ c.pt)` for a
  cofan `c`.
* `TauCeti.IsCompactForCoproducts.directSumEquiv`,
  `TauCeti.IsCompactForCoproducts.coprodDirectSumEquiv`: the resulting additive equivalences
  retaining the canonical coproduct inclusions.

## Main results

* `TauCeti.directSumHom_injective`: `directSumHom G c` is always injective for a colimit cofan `c`.
* `TauCeti.isCompactForCoproducts_iff_bijective_directSumHom`,
  `TauCeti.isCompactForCoproducts_iff_surjective_directSumHom`: direct-sum characterizations of
  compactness.
* `TauCeti.IsCompactForCoproducts.of_iso`, `TauCeti.IsCompactForCoproducts.of_isZero`,
  `TauCeti.IsCompactForCoproducts.of_isColimit_cofan_finite`,
  `TauCeti.IsCompactForCoproducts.biprod`, `TauCeti.IsCompactForCoproducts.shift`: stability under
  isomorphisms, zero objects, finite coproducts, and shifts.
* `CategoryTheory.Retract.isCompactForCoproducts`,
  `CategoryTheory.Adjunction.isCompactForCoproducts_left`: stability under retracts and left
  adjoints whose right adjoint preserves coproducts.
* `AddCommGrpCat.isCompactForCoproducts_ulift_int`,
  `AddCommGrpCat.not_isCompactForCoproducts_coproduct_nat`: `ULift ℤ` is compact in
  `AddCommGrpCat`, while its countable coproduct is not.

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
    (J : Type v) : PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G)) :=
  hG J

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
  DirectSum.toAddMonoid fun j ↦
    { toFun := fun g ↦ g ≫ c.inj j
      map_zero' := Limits.zero_comp
      map_add' := fun _ _ ↦ Preadditive.add_comp _ _ _ _ _ _ }

@[simp]
lemma directSumHom_of (G : C) {J : Type w} [DecidableEq J] {f : J → C} (c : Cofan f) (j : J)
    (g : G ⟶ f j) :
    directSumHom G c (DirectSum.of (fun j ↦ G ⟶ f j) j g) = g ≫ c.inj j := by
  simp [directSumHom]

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
    c.inj j ≫ cofanTail hc s = 0 := by
  simp [cofanTail, hj]

private lemma cofanTail_add_sum_proj {J : Type w} [DecidableEq J] {f : J → C} {c : Cofan f}
    (hc : IsColimit c) (s : Finset J) :
    cofanTail hc s + ∑ j ∈ s, cofanProj hc j ≫ c.inj j = 𝟙 c.pt := by
  refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
  rw [Preadditive.comp_add, cofanTail, Cofan.IsColimit.fac, Preadditive.comp_sum, Category.comp_id]
  have hsum : ∑ j ∈ s, c.inj i ≫ cofanProj hc j ≫ c.inj j =
      if i ∈ s then c.inj i else 0 := by
    have hterm : ∀ j ∈ s, c.inj i ≫ cofanProj hc j ≫ c.inj j =
        if i = j then c.inj i else 0 := fun j _ ↦ by
      rw [← Category.assoc, inj_comp_cofanProj]
      split_ifs with h
      · subst h; simp
      · simp
    rw [Finset.sum_congr rfl hterm]
    by_cases hi : i ∈ s
    · rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j _ hji; simp [Ne.symm hji]
      · intro h; exact absurd hi h
    · simp only [hi, ↓reduceIte]
      exact Finset.sum_eq_zero fun j hj ↦ by simp [show i ≠ j from fun hij ↦ hi (hij ▸ hj)]
  rw [hsum]
  split_ifs <;> simp

private lemma directSumHom_comp_cofanProj (G : C) {J : Type w} [DecidableEq J] {f : J → C}
    {c : Cofan f} (hc : IsColimit c) (x : ⨁ j : J, (G ⟶ f j)) (k : J) :
    directSumHom G c x ≫ cofanProj hc k = x k := by
  refine DirectSum.induction_on x (by simp) (fun j g ↦ ?_) (fun u v hu hv ↦ ?_)
  · rw [directSumHom_of, Category.assoc, inj_comp_cofanProj]
    split_ifs with h
    · subst h
      simp [DirectSum.of_eq_same]
    · simp [DirectSum.of_eq_of_ne (β := fun j ↦ G ⟶ f j) j k g (Ne.symm h)]
  · rw [map_add, Preadditive.add_comp, hu, hv, DirectSum.add_apply]

/-- For every object `G` and every colimit cofan `c` in a preadditive category, the canonical
direct-sum comparison homomorphism `directSumHom G c` is always injective. -/
theorem directSumHom_injective (G : C) {J : Type w} [DecidableEq J] {f : J → C} {c : Cofan f}
    (hc : IsColimit c) : Function.Injective (directSumHom G c) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  ext k
  rw [← directSumHom_comp_cofanProj G hc x k, hx, Limits.zero_comp]
  rfl

/-- `preadditiveCoyoneda.obj (op G)` preserves a colimit cofan `c` indexed by `J : Type v` if and
only if the direct-sum comparison map `directSumHom G c` is bijective. -/
theorem preservesColimit_discrete_iff_bijective_directSumHom (G : C) {J : Type v} [DecidableEq J]
    {f : J → C} {c : Cofan f} (hc : IsColimit c) :
    PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (op G)) ↔
      Function.Bijective (directSumHom G c) := by
  let F := preadditiveCoyoneda.obj (op G)
  have hc' : IsColimit (Cofan.mk c.pt c.inj) :=
    hc.ofIsoColimit (Cocone.ext (Iso.refl _) fun ⟨j⟩ ↦ by simp [Cofan.inj])
  have h1 : PreservesColimit (Discrete.functor f) F ↔
      Nonempty (IsColimit (F.mapCocone (Cofan.mk c.pt c.inj))) :=
    ⟨fun _ ↦ ⟨isColimitOfPreserves F hc'⟩,
      fun ⟨h⟩ ↦ preservesColimit_of_preserves_colimit_cocone hc' h⟩
  rw [h1, (isColimitMapCoconeCofanMkEquiv F f c.inj).nonempty_congr,
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
  constructor
  · intro hG J _ f c hc
    have := hG J
    exact (preservesColimit_discrete_iff_bijective_directSumHom G hc).1 inferInstance
  · intro h J
    classical
    refine ⟨fun {K} ↦ ?_⟩
    let f : J → C := fun j ↦ K.obj ⟨j⟩
    have eK : Discrete.functor f ≅ K := Discrete.natIso fun ⟨j⟩ ↦ Iso.refl _
    suffices PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (op G)) from
      preservesColimit_of_iso_diagram _ eK
    refine ⟨fun {c} hc ↦ ?_⟩
    have : PreservesColimit (Discrete.functor f) (preadditiveCoyoneda.obj (op G)) :=
      (preservesColimit_discrete_iff_bijective_directSumHom G hc).2 (h J f c hc)
    exact ⟨isColimitOfPreserves _ hc⟩

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

/-- Reindex a colimit cofan along an equivalence of indexing types. -/
private def isColimitCofanReindex {J : Type w} {J' : Type*} (e : J ≃ J') {f : J → C}
    {c : Cofan f} (hc : IsColimit c) :
    IsColimit (Cofan.mk c.pt fun k ↦ c.inj (e.symm k) : Cofan (f ∘ e.symm)) :=
  let eDiag : (Discrete.equivalence e.symm).functor ⋙ Discrete.functor f ≅
      Discrete.functor (f ∘ e.symm) :=
    Discrete.natIso fun _ ↦ Iso.refl _
  let c₀ : Cocone (Discrete.functor (f ∘ e.symm)) :=
    (Cocone.precompose eDiag.inv).obj (c.whisker (Discrete.equivalence e.symm).functor)
  have hc₀ : IsColimit c₀ :=
    (IsColimit.precomposeInvEquiv eDiag _).symm
      (hc.whiskerEquivalence (Discrete.equivalence e.symm))
  hc₀.ofIsoColimit <| Cocone.ext (Iso.refl _) fun ⟨k⟩ ↦ by
    simp only [c₀, eDiag, Cocone.precompose_obj_ι, NatTrans.comp_app, Cocone.whisker_ι,
      Functor.whiskerLeft_app, Discrete.natIso_inv_app, Iso.refl_inv, Iso.refl_hom,
      Category.comp_id]
    exact Category.id_comp _

/-- If `preadditiveCoyoneda.obj (op G)` preserves `Discrete J`-colimits for a `v`-small type `J`,
then `directSumHom G c` is bijective for every colimit cofan `c` indexed by `J`. -/
theorem bijective_directSumHom_of_preserves (G : C) {J : Type w} [Small.{v} J] [DecidableEq J]
    {f : J → C} {c : Cofan f} (hc : IsColimit c)
    [PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G))] :
    Function.Bijective (directSumHom G c) := by
  classical
  let e : J ≃ Shrink.{v} J := equivShrink.{v} J
  let c' : Cofan (f ∘ e.symm) := Cofan.mk c.pt fun k ↦ c.inj (e.symm k)
  let hc' : IsColimit c' := isColimitCofanReindex e hc
  have : PreservesColimitsOfShape (Discrete (Shrink.{v} J)) (preadditiveCoyoneda.obj (op G)) :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence e) _
  have hbij : Function.Bijective (directSumHom G c') :=
    (preservesColimit_discrete_iff_bijective_directSumHom G hc').1 inferInstance
  have hcomp :
      (directSumHom G c).comp (DirectSum.equivCongrLeft e).symm.toAddMonoidHom =
        directSumHom G c' := by
    refine DirectSum.addHom_ext fun k g ↦ ?_
    have hsymm :
        (DirectSum.equivCongrLeft (β := fun j ↦ G ⟶ f j) e).symm
            (DirectSum.of (fun k ↦ G ⟶ f (e.symm k)) k g) =
          DirectSum.of (fun j ↦ G ⟶ f j) (e.symm k) g :=
      (DirectSum.equivCongrLeft e).symm_apply_eq.2
        (DirectSum.equivCongrLeft_of (β := fun j ↦ G ⟶ f j) e k g).symm
    rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hsymm, directSumHom_of]
    exact (directSumHom_of G c' k g).symm
  have hbij' : Function.Bijective (directSumHom G c ∘ (DirectSum.equivCongrLeft e).symm) := by
    have hcoe : (directSumHom G c ∘ (DirectSum.equivCongrLeft e).symm) = directSumHom G c' :=
      congrArg DFunLike.coe hcomp
    rw [hcoe]
    exact hbij
  exact (Function.Bijective.of_comp_iff _ (DirectSum.equivCongrLeft e).symm.bijective).1 hbij'

/-- The direct-sum equivalence `(⨁ j, (G ⟶ f j)) ≃+ (G ⟶ c.pt)` for a colimit cofan `c` indexed
by a `v`-small type `J`, whenever `preadditiveCoyoneda.obj (op G)` preserves
`Discrete J`-colimits. -/
def directSumEquivOfPreserves (G : C) {J : Type w} [Small.{v} J] [DecidableEq J]
    {f : J → C} {c : Cofan f} (hc : IsColimit c)
    [PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G))] :
    (⨁ j : J, (G ⟶ f j)) ≃+ (G ⟶ c.pt) :=
  AddEquiv.ofBijective (directSumHom G c) (bijective_directSumHom_of_preserves G hc)

@[simp]
lemma directSumEquivOfPreserves_of (G : C) {J : Type w} [Small.{v} J] [DecidableEq J]
    {f : J → C} {c : Cofan f} (hc : IsColimit c)
    [PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G))]
    (j : J) (g : G ⟶ f j) :
    directSumEquivOfPreserves G hc (DirectSum.of (fun j ↦ G ⟶ f j) j g) = g ≫ c.inj j := by
  simp [directSumEquivOfPreserves]

@[simp]
lemma directSumEquivOfPreserves_symm_comp_inj (G : C) {J : Type w} [Small.{v} J] [DecidableEq J]
    {f : J → C} {c : Cofan f} (hc : IsColimit c)
    [PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op G))]
    (j : J) (g : G ⟶ f j) :
    (directSumEquivOfPreserves G hc).symm (g ≫ c.inj j) = DirectSum.of (fun j ↦ G ⟶ f j) j g :=
  (directSumEquivOfPreserves G hc).injective (by simp)

/-- For a compact object `G`, maps out of `G` into a colimit cofan `c` indexed by a `v`-small type
identify with the direct sum of the component homomorphism groups. -/
def IsCompactForCoproducts.directSumEquiv {G : C} (hG : IsCompactForCoproducts G)
    {J : Type w} [Small.{v} J] [DecidableEq J] {f : J → C} {c : Cofan f} (hc : IsColimit c) :
    (⨁ j : J, (G ⟶ f j)) ≃+ (G ⟶ c.pt) :=
  have := hG.preservesColimitsOfShape_of_small J
  directSumEquivOfPreserves G hc

@[simp]
lemma IsCompactForCoproducts.directSumEquiv_of {G : C} (hG : IsCompactForCoproducts G)
    {J : Type w} [Small.{v} J] [DecidableEq J] {f : J → C} {c : Cofan f} (hc : IsColimit c)
    (j : J) (g : G ⟶ f j) :
    hG.directSumEquiv hc (DirectSum.of (fun j ↦ G ⟶ f j) j g) = g ≫ c.inj j := by
  simp [IsCompactForCoproducts.directSumEquiv]

@[simp]
lemma IsCompactForCoproducts.directSumEquiv_symm_comp_inj {G : C} (hG : IsCompactForCoproducts G)
    {J : Type w} [Small.{v} J] [DecidableEq J] {f : J → C} {c : Cofan f} (hc : IsColimit c)
    (j : J) (g : G ⟶ f j) :
    (hG.directSumEquiv hc).symm (g ≫ c.inj j) = DirectSum.of (fun j ↦ G ⟶ f j) j g := by
  simp [IsCompactForCoproducts.directSumEquiv]

/-- For a compact object `G` and a `v`-small family `f : J → C` with a coproduct, maps `G ⟶ ∐ f`
identify with `⨁ j, (G ⟶ f j)`, retaining the canonical inclusions `Sigma.ι f j`. -/
def IsCompactForCoproducts.coprodDirectSumEquiv {G : C} (hG : IsCompactForCoproducts G)
    {J : Type w} [Small.{v} J] [DecidableEq J] (f : J → C) [HasCoproduct f] :
    (⨁ j : J, (G ⟶ f j)) ≃+ (G ⟶ ∐ f) :=
  hG.directSumEquiv (coproductIsCoproduct f)

@[simp]
lemma IsCompactForCoproducts.coprodDirectSumEquiv_of {G : C} (hG : IsCompactForCoproducts G)
    {J : Type w} [Small.{v} J] [DecidableEq J] (f : J → C) [HasCoproduct f]
    (j : J) (g : G ⟶ f j) :
    hG.coprodDirectSumEquiv f (DirectSum.of (fun j ↦ G ⟶ f j) j g) = g ≫ Sigma.ι f j :=
  hG.directSumEquiv_of (coproductIsCoproduct f) j g

@[simp]
lemma IsCompactForCoproducts.coprodDirectSumEquiv_symm_comp_ι {G : C}
    (hG : IsCompactForCoproducts G) {J : Type w} [Small.{v} J] [DecidableEq J] (f : J → C)
    [HasCoproduct f] (j : J) (g : G ⟶ f j) :
    (hG.coprodDirectSumEquiv f).symm (g ≫ Sigma.ι f j) = DirectSum.of (fun j ↦ G ⟶ f j) j g :=
  hG.directSumEquiv_symm_comp_inj (coproductIsCoproduct f) j g

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
  refine ⟨∑ j ∈ s, DirectSum.of (fun j ↦ c.pt ⟶ f j) j (Cofan.IsColimit.desc hc fun i ↦ u i j), ?_⟩
  refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
  rw [map_sum, Preadditive.comp_sum, ← hu i, ← DirectSum.sum_support_of (u i), map_sum]
  have hlhs : ∀ j ∈ s,
      c.inj i ≫ directSumHom c.pt d
        (DirectSum.of (fun j ↦ c.pt ⟶ f j) j (Cofan.IsColimit.desc hc fun i ↦ u i j)) =
      u i j ≫ d.inj j := fun j _ ↦ by
    rw [directSumHom_of, ← Category.assoc, Cofan.IsColimit.fac]
  have hrhs : ∀ j ∈ (u i).support,
      directSumHom (X i) d (DirectSum.of (fun j ↦ X i ⟶ f j) j (u i j)) = u i j ≫ d.inj j :=
    fun j _ ↦ directSumHom_of (X i) d j (u i j)
  rw [Finset.sum_congr rfl hlhs, Finset.sum_congr rfl hrhs]
  have hsub : (u i).support ⊆ s :=
    Finset.subset_biUnion_of_mem (fun i ↦ (u i).support) (Finset.mem_univ i)
  exact (Finset.sum_subset hsub
    fun j _ hj ↦ by rw [DFinsupp.notMem_support_iff.1 hj, Limits.zero_comp]).symm

/-- Every zero object is compact for coproducts. -/
theorem IsCompactForCoproducts.of_isZero {Z : C} (hZ : IsZero Z) : IsCompactForCoproducts Z := by
  let c : Cofan (Empty.elim : Empty → C) := Cofan.mk Z fun i : Empty ↦ i.elim
  have hc : IsColimit c :=
    Cofan.IsColimit.mk c (fun s ↦ hZ.to_ s.pt) (fun _ i ↦ i.elim) fun _ _ _ ↦ hZ.eq_of_src _ _
  exact IsCompactForCoproducts.of_isColimit_cofan_finite hc fun i : Empty ↦ i.elim

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
    IsCompactForCoproducts (X ⊞ Y) := by
  let f : Bool → C := fun b ↦ match b with
    | true => X
    | false => Y
  let c : Cofan f := Cofan.mk (X ⊞ Y) fun b ↦ match b with
    | true => biprod.inl
    | false => biprod.inr
  have hc : IsColimit c :=
    Cofan.IsColimit.mk c (fun s ↦ biprod.desc (s.inj true) (s.inj false))
      (fun s b ↦ by cases b <;> simp [c])
      (fun s m hm ↦ biprod.hom_ext' _ _ (by simpa [c] using hm true) (by simpa [c] using hm false))
  exact IsCompactForCoproducts.of_isColimit_cofan_finite hc fun b ↦ by cases b <;> assumption

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
      (DirectSum.of (fun j ↦ G ⟶ f j) j).comp
        { toFun := fun k ↦ r.i ≫ k
          map_zero' := Limits.comp_zero
          map_add' := fun _ _ ↦ Preadditive.comp_add _ _ _ _ _ _ }
  have hcommI : ∀ z, TauCeti.directSumHom G c (preI z) = r.i ≫ TauCeti.directSumHom H c z := by
    intro z
    refine DirectSum.induction_on z (by simp) (fun j k ↦ ?_) (fun a b ha hb ↦ ?_)
    · simp [preI, Category.assoc]
    · simp [map_add, ha, hb, Preadditive.comp_add]
  refine ⟨preI y, ?_⟩
  rw [hcommI, hy, ← Category.assoc, r.retract, Category.id_comp]

/-- If `L ⊣ R` is an adjunction between preadditive categories with the same morphism universe and
`R` preserves small coproducts, then `L` preserves compact objects. -/
theorem Adjunction.isCompactForCoproducts_left {C : Type u₁} {D : Type u₂}
    [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) R]
    {G : C} (hG : TauCeti.IsCompactForCoproducts G) :
    TauCeti.IsCompactForCoproducts (L.obj G) := by
  classical
  have : R.IsRightAdjoint := adj.isRightAdjoint
  rw [TauCeti.isCompactForCoproducts_iff_surjective_directSumHom]
  intro J _ f c hc u
  let hc' : IsColimit (Cofan.mk c.pt c.inj) :=
    hc.ofIsoColimit (Cocone.ext (Iso.refl _) fun ⟨j⟩ ↦ by simp [Cofan.inj])
  let cR : Cofan (fun j ↦ R.obj (f j)) := Cofan.mk (R.obj c.pt) fun j ↦ R.map (c.inj j)
  let hcR : IsColimit cR := isColimitCofanMkObjOfIsColimit R f c.inj hc'
  obtain ⟨y, hy⟩ := (TauCeti.isCompactForCoproducts_iff_surjective_directSumHom G).1 hG J _ cR hcR
    (adj.homEquiv G c.pt u)
  let s := y.support
  have hu_tail : u ≫ TauCeti.cofanTail hc s = 0 := by
    apply (adj.homEquiv G c.pt).injective
    rw [adj.homEquiv_naturality_right, ← hy]
    have h0 : adj.homEquiv G c.pt (0 : L.obj G ⟶ c.pt) = 0 := by
      simp [Adjunction.homEquiv_unit]
    rw [h0, ← DirectSum.sum_support_of y, map_sum, Preadditive.sum_comp]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [TauCeti.directSumHom_of, Category.assoc]
    change y j ≫ R.map (c.inj j) ≫ R.map (TauCeti.cofanTail hc s) = 0
    rw [← R.map_comp, TauCeti.inj_comp_cofanTail_of_mem hc hj, Functor.map_zero, Limits.comp_zero]
  refine ⟨∑ j ∈ s, DirectSum.of (fun j ↦ L.obj G ⟶ f j) j (u ≫ TauCeti.cofanProj hc j), ?_⟩
  rw [map_sum]
  have hterm : ∀ j ∈ s,
      TauCeti.directSumHom (L.obj G) c
        (DirectSum.of (fun j ↦ L.obj G ⟶ f j) j (u ≫ TauCeti.cofanProj hc j)) =
      u ≫ TauCeti.cofanProj hc j ≫ c.inj j := fun j _ ↦ by
    rw [TauCeti.directSumHom_of, Category.assoc]
  rw [Finset.sum_congr rfl hterm, ← Preadditive.comp_sum,
    ← zero_add (u ≫ ∑ j ∈ s, TauCeti.cofanProj hc j ≫ c.inj j), ← hu_tail,
    ← Preadditive.comp_add, TauCeti.cofanTail_add_sum_proj hc s, Category.comp_id]

/-- An equivalence of preadditive categories preserves compact objects. -/
theorem Equivalence.isCompactForCoproducts_functor {C : Type u₁} {D : Type u₂}
    [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
    (e : C ≌ D) {G : C} (hG : TauCeti.IsCompactForCoproducts G) :
    TauCeti.IsCompactForCoproducts (e.functor.obj G) := by
  have : ∀ J : Type v, PreservesColimitsOfShape (Discrete J) e.inverse :=
    fun _ ↦ inferInstance
  exact e.toAdjunction.isCompactForCoproducts_left hG

/-- An equivalence of preadditive categories preserves and reflects compact objects. -/
theorem Equivalence.isCompactForCoproducts_functor_iff {C : Type u₁} {D : Type u₂}
    [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
    (e : C ≌ D) {G : C} :
    TauCeti.IsCompactForCoproducts (e.functor.obj G) ↔ TauCeti.IsCompactForCoproducts G :=
  ⟨fun h ↦ (e.symm.isCompactForCoproducts_functor h).of_iso (e.unitIso.symm.app G),
    e.isCompactForCoproducts_functor⟩

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
    TauCeti.IsCompactForCoproducts (of (ULift.{v} ℤ)) := by
  let e : preadditiveCoyoneda.obj (op (of (ULift.{v} ℤ))) ≅ 𝟭 AddCommGrpCat.{v} :=
    NatIso.ofComponents (fun A ↦ (uliftZMultiplesAddEquiv A).toAddCommGrpIso) fun f ↦
      AddCommGrpCat.ext fun g ↦ by
        -- Both sides evaluate `g ≫ f` at the generator `ULift.up 1`.
        change f.hom (g.hom (ULift.up (1 : ℤ))) = f.hom (g.hom (ULift.up (1 : ℤ)))
        rfl
  intro J
  exact preservesColimitsOfShape_of_natIso e.symm

/-- The countable coproduct `∐ₙ ULift ℤ` is not compact in `AddCommGrpCat`: its identity morphism
has infinitely many nonzero coordinate projections. -/
theorem not_isCompactForCoproducts_coproduct_nat :
    ¬ TauCeti.IsCompactForCoproducts (∐ fun _ : ℕ ↦ of (ULift.{v} ℤ)) := by
  classical
  let Z : ℕ → AddCommGrpCat.{v} := fun _ ↦ of (ULift.{v} ℤ)
  let K : AddCommGrpCat.{v} := ∐ Z
  intro hK
  obtain ⟨x, hx⟩ := (hK.coprodDirectSumEquiv Z).surjective (𝟙 K)
  obtain ⟨N, hN⟩ := Infinite.exists_notMem_finset x.support
  have h1 : (coprodIsoDirectSum Z).hom (Sigma.ι Z N (ULift.up (1 : ℤ))) N = ULift.up (1 : ℤ) := by
    rw [← ConcreteCategory.comp_apply, ι_coprodIsoDirectSum_hom]
    simp [DirectSum.of_eq_same]
  have h2 : (coprodIsoDirectSum Z).hom
      ((hK.coprodDirectSumEquiv Z x) (Sigma.ι Z N (ULift.up (1 : ℤ)))) N = 0 := by
    have hxsum : x = ∑ n ∈ x.support, DirectSum.of (fun n ↦ K ⟶ Z n) n (x n) :=
      (DirectSum.sum_support_of x).symm
    rw [hxsum, map_sum]
    have hsum : ∀ (s : Finset ℕ) (F : ℕ → (K ⟶ K)) (a : K),
        (∑ n ∈ s, F n) a = ∑ n ∈ s, F n a := fun s F a ↦ by
      induction s using Finset.induction_on with
      | empty => simp
      | insert k s hk ih => simp [Finset.sum_insert hk, ih]
    rw [hsum, map_sum, DirectSum.sum_apply]
    refine Finset.sum_eq_zero fun n hn ↦ ?_
    have hne : N ≠ n := fun h ↦ hN (h ▸ hn)
    rw [hK.coprodDirectSumEquiv_of]
    rw [ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply (Sigma.ι Z n),
      ι_coprodIsoDirectSum_hom]
    simpa using DirectSum.of_eq_of_ne (β := fun i ↦ Z i) n N
      ((x n) (Sigma.ι Z N (ULift.up (1 : ℤ)))) hne
  rw [hx] at h2
  have h10 : ULift.up (1 : ℤ) = ULift.up (0 : ℤ) := h1.symm.trans h2
  exact one_ne_zero (congrArg ULift.down h10)

end AddCommGrpCat

end
