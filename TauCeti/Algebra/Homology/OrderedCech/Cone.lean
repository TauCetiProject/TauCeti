/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Single
public import TauCeti.Algebra.Homology.OrderedCech

import TauCeti.Data.Finset.Basic

/-!
# The ordered Čech complex of a cone

Let `F : (Finset ι)ᵒᵖ ⥤ C` be a functor on the finite sets of a linearly ordered type, and let `v`
be an index such that adjoining `v` to a nonempty set `s` does not change the value of `F`: the
restriction `F(s ∪ {v}) ⟶ F(s)` is an isomorphism. Then the ordered Čech complex of `F` is chain
homotopy equivalent to `F({v})`, placed in degree `0`
(`CategoryTheory.Functor.orderedCechHomotopyEquivOfVertex`).

The contracting homotopy sends the summand `F(s)` to `± F(s ∪ {v})` through the inverse of the
restriction, the cone with vertex `v`. The augmentation sends the summand `F({i})` to `F({v})`
through `F({i}) ≅ F({i, v}) ⟶ F({v})`, so it is the identity on the summand `F({v})`
(`CategoryTheory.Functor.orderedCechComplexι_orderedCechHomotopyEquivOfVertex_hom_f_zero`). Its
section is the summand inclusion of `F({v})`
(`CategoryTheory.Functor.orderedCechHomotopyEquivOfVertex_inv_f_zero`).

The argument adapts the cone of `TauCeti.freeCechHomotopyEquiv`
(`TauCeti/Algebra/Homology/OrderedCech/Cover.lean`), where the vertex of the cone depends on the
point of the cover.

## Main definitions

* `CategoryTheory.Functor.orderedCechHomotopyEquivOfVertex F v hF`: the chain homotopy
  equivalence between the ordered Čech complex of `F` and `F({v})` in degree `0`.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Finset

universe w v u

namespace CategoryTheory

namespace Functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {ι : Type w} [LinearOrder ι] (F : (Finset ι)ᵒᵖ ⥤ C)

namespace OrderedCechCone

/-! ### The contracting homotopy

The proof works with the summand inclusions `single F p t`, which are defined for every finite set
`t` and vanish unless `t` has `p + 1` elements, so that sums over the elements of a set need no
cardinality proofs. -/

/-- The inclusion of the summand `F(t)` in degree `p`; it vanishes when `t` does not have `p + 1`
elements. -/
private def single (p : ℕ) (t : Finset ι) : F.obj (op t) ⟶ F.orderedCechComplex.X p :=
  if ht : #t = p + 1 then F.orderedCechComplexι ⟨t, ht⟩ else 0

private lemma single_of_card_eq {p : ℕ} {t : Finset ι} (ht : #t = p + 1) :
    single F p t = F.orderedCechComplexι ⟨t, ht⟩ := by
  simp [single, ht]

private lemma single_of_card_ne {p : ℕ} {t : Finset ι} (ht : #t ≠ p + 1) : single F p t = 0 := by
  simp [single, ht]

private lemma map_single_congr {p : ℕ} {s t t' : Finset ι} (h : t ⊆ s) (h' : t' ⊆ s)
    (e : t = t') :
    F.map (homOfLE h).op ≫ single F p t = F.map (homOfLE h').op ≫ single F p t' := by
  subst e
  rfl

private lemma map_single_of_eq {p : ℕ} {s t : Finset ι} (h : t ⊆ s) (e : t = s) :
    F.map (homOfLE h).op ≫ single F p t = single F p s := by
  subst e
  rw [show homOfLE h = 𝟙 t from Subsingleton.elim _ _, op_id, F.map_id, Category.id_comp]

private lemma hom_ext {p : ℕ} {Y : C} {f g : F.orderedCechComplex.X p ⟶ Y}
    (h : ∀ s : Finset ι, #s = p + 1 → single F p s ≫ f = single F p s ≫ g) : f = g :=
  F.orderedCechComplex_hom_ext fun s ↦ by
      simpa only [single_of_card_eq F s.property] using h s.val s.property

private lemma single_d {p : ℕ} {s : Finset ι} (hs : #s = p + 1 + 1) :
    single F (p + 1) s ≫ F.orderedCechComplex.d (p + 1) p =
      ∑ i ∈ s, ((-1 : ℤ) ^ #{j ∈ s | j < i}) •
        (F.map (homOfLE (erase_subset i s)).op ≫ single F p (s.erase i)) := by
  rw [single_of_card_eq F hs, F.ι_orderedCechComplex_d (s := ⟨s, hs⟩), ← sum_coe_sort s]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [single_of_card_eq F (by rw [card_erase_of_mem i.property, hs, Nat.add_sub_cancel])]

variable (v : ι) (hF : ∀ s : Finset ι, s.Nonempty → IsIso (F.map (homOfLE (subset_insert v s)).op))

/-- The inverse `F(s) ⟶ F(s ∪ {v})` of the restriction for a nonempty set `s`, and zero for the
empty set. -/
private def cone (s : Finset ι) : F.obj (op s) ⟶ F.obj (op (insert v s)) :=
  if h : s.Nonempty then
    haveI := hF s h
    CategoryTheory.inv (F.map (homOfLE (subset_insert v s)).op)
  else 0

omit [HasCoproducts.{w} C] in
private lemma cone_map {s : Finset ι} (hs : s.Nonempty) :
    cone F v hF s ≫ F.map (homOfLE (subset_insert v s)).op = 𝟙 _ := by
  have := hF s hs
  simp [cone, hs]

omit [HasCoproducts.{w} C] in
/-- The inverses of the restrictions commute with the restrictions. -/
@[reassoc]
private lemma cone_map_insert {s t : Finset ι} (h : t ⊆ s) (ht : t.Nonempty) :
    cone F v hF s ≫ F.map (homOfLE (insert_subset_insert v h)).op =
      F.map (homOfLE h).op ≫ cone F v hF t := by
  have := hF t ht
  rw [← cancel_mono (F.map (homOfLE (subset_insert v t)).op), Category.assoc, Category.assoc,
    cone_map F v hF ht, Category.comp_id, ← F.map_comp, ← op_comp, homOfLE_comp]
  conv_rhs => rw [← Category.id_comp (F.map _), ← cone_map F v hF (ht.mono h), Category.assoc,
    ← F.map_comp, ← op_comp, homOfLE_comp]

/-- When `v ∈ s` the cone is the identity of `F(s) = F(s ∪ {v})`. -/
private lemma cone_single_of_mem {p : ℕ} {s : Finset ι} (hs : s.Nonempty) (hc : v ∈ s) :
    cone F v hF s ≫ single F p (insert v s) = single F p s := by
  rw [← map_single_of_eq F (subset_insert v s) (insert_eq_of_mem hc).symm, ← Category.assoc,
    cone_map F v hF hs, Category.id_comp]

/-- The components of the contracting homotopy: the summand `F(s)` goes to `± F(s ∪ {v})`. The
sign makes `v` the vertex of a cone. -/
private def homotopy (p j : ℕ) : F.orderedCechComplex.X p ⟶ F.orderedCechComplex.X j :=
  F.orderedCechComplexDesc fun s ↦ ((-1 : ℤ) ^ #{k ∈ s.val | k < v}) •
    (cone F v hF s.val ≫ single F j (insert v s.val))

private lemma single_homotopy {p : ℕ} (j : ℕ) {s : Finset ι} (hs : #s = p + 1) :
    single F p s ≫ homotopy F v hF p j =
      ((-1 : ℤ) ^ #{k ∈ s | k < v}) • (cone F v hF s ≫ single F j (insert v s)) := by
  rw [single_of_card_eq F hs, homotopy, ι_orderedCechComplexDesc]

/-- The sum `∑ₖ ± F((s ∖ {k}) ∪ {v})` over `k ∈ s`, which is both the homotopy after the
differential on `F(s)` and the remainder of the differential after the homotopy. -/
private def coneFace (p : ℕ) (s : Finset ι) : F.obj (op s) ⟶ F.orderedCechComplex.X p :=
  ∑ k ∈ s, ((-1 : ℤ) ^ #{j ∈ s | j < k} * (-1) ^ #{j ∈ s.erase k | j < v}) •
    (cone F v hF s ≫ F.map (homOfLE (insert_subset_insert v (erase_subset k s))).op ≫
      single F p (insert v (s.erase k)))

private lemma single_homotopy_d_of_notMem {p : ℕ} {s : Finset ι} (hs : #s = p + 1)
    (hc : v ∉ s) :
    single F p s ≫ homotopy F v hF p (p + 1) ≫ F.orderedCechComplex.d (p + 1) p =
      single F p s - coneFace F v hF p s := by
  have hne : s.Nonempty := card_pos.1 (by omega)
  -- The term of `v` in the differential of `F(s ∪ {v})` carries the sign of the homotopy twice.
  have hsign : ((-1 : ℤ) ^ #{k ∈ s | k < v} * (-1) ^ #{j ∈ insert v s | j < v}) = 1 := by
    simp only [filter_insert, lt_irrefl, ↓reduceIte]
    rw [← pow_add, ← two_mul, (even_two_mul _).neg_one_pow]
  rw [← Category.assoc, single_homotopy F v hF _ hs, Preadditive.zsmul_comp, Category.assoc,
    single_d F (by rw [card_insert_of_notMem hc, hs]), sum_insert hc, coneFace, sub_eq_add_neg,
    ← sum_neg_distrib]
  simp only [Preadditive.comp_add, Preadditive.comp_sum, Preadditive.comp_zsmul, smul_add,
    Finset.smul_sum, smul_smul, hsign, one_smul]
  rw [map_single_congr F _ (subset_insert v s) (erase_insert hc), ← Category.assoc,
    cone_map F v hF hne, Category.id_comp]
  congr 1
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hck : v ≠ k := fun h ↦ hc (h ▸ hk)
  rw [neg_one_pow_card_filter_lt_mul_insert hc hk, neg_smul,
    map_single_congr F _ (insert_subset_insert v (erase_subset k s)) (erase_insert_of_ne hck)]

private lemma single_homotopy_of_mem {p : ℕ} {s : Finset ι} (hs : #s = p + 1) (hc : v ∈ s) :
    single F p s ≫ homotopy F v hF p (p + 1) = 0 := by
  rw [single_homotopy F v hF _ hs,
    single_of_card_ne F (by rw [insert_eq_of_mem hc, hs]; omega), comp_zero, smul_zero]

private lemma single_d_homotopy {p : ℕ} {s : Finset ι} (hs : #s = p + 1 + 1) :
    single F (p + 1) s ≫ F.orderedCechComplex.d (p + 1) p ≫ homotopy F v hF p (p + 1) =
      coneFace F v hF (p + 1) s := by
  rw [← Category.assoc, single_d F hs, Preadditive.sum_comp, coneFace]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hne : (s.erase k).Nonempty := card_pos.1 (by rw [card_erase_of_mem hk]; omega)
  rw [Preadditive.zsmul_comp, Category.assoc,
    single_homotopy F v hF _ (by rw [card_erase_of_mem hk, hs]; rfl), Preadditive.comp_zsmul,
    smul_smul, cone_map_insert_assoc F v hF (erase_subset k s) hne]

private lemma coneFace_of_mem {p : ℕ} {s : Finset ι} (hs : #s = p + 1) (hc : v ∈ s) :
    coneFace F v hF p s = single F p s := by
  rw [coneFace, sum_eq_single v]
  · rw [map_single_congr F _ (subset_insert v s) (insert_erase hc), ← Category.assoc,
      cone_map F v hF ⟨v, hc⟩, Category.id_comp, filter_erase, erase_eq_of_notMem (by simp),
      ← pow_add, ← two_mul, (even_two_mul _).neg_one_pow, one_smul]
  · intro k hk hkc
    rw [single_of_card_ne F (by
      rw [insert_eq_of_mem (mem_erase.2 ⟨Ne.symm hkc, hc⟩), card_erase_of_mem hk, hs]; omega),
      comp_zero, comp_zero, smul_zero]
  · exact fun h ↦ (h hc).elim

/-- The map `F({i}) ≅ F({i, v}) ⟶ F({v})` for a singleton `s = {i}`, and more generally the
restriction to `F({v})` after the cone. -/
private def toVertex (s : Finset ι) : F.obj (op s) ⟶ F.obj (op {v}) :=
  cone F v hF s ≫ F.map (homOfLE (singleton_subset_iff.2 (mem_insert_self v s))).op

omit [HasCoproducts.{w} C] in
private lemma map_toVertex {s t : Finset ι} (h : t ⊆ s) (ht : t.Nonempty) :
    F.map (homOfLE h).op ≫ toVertex F v hF t = toVertex F v hF s := by
  rw [toVertex, toVertex, ← cone_map_insert_assoc F v hF h ht, ← F.map_comp, ← op_comp,
    homOfLE_comp]

omit [HasCoproducts.{w} C] in
private lemma toVertex_singleton : toVertex F v hF {v} = 𝟙 _ :=
  cone_map F v hF (singleton_nonempty v)

/-- In degree `0` the cone face of `F({i})` is the restriction to the summand `F({v})`. -/
private lemma coneFace_zero {s : Finset ι} (hs : #s = 0 + 1) :
    coneFace F v hF 0 s = toVertex F v hF s ≫ single F 0 {v} := by
  obtain ⟨i, rfl⟩ := card_eq_one.1 hs
  rw [coneFace, sum_singleton, map_single_congr F _ (singleton_subset_iff.2 (mem_insert_self v {i}))
    (by rw [erase_singleton, insert_empty]), toVertex, Category.assoc]
  simp [filter_singleton]

/-- The augmentation in degree `0`, sending the summand `F({i})` to `F({v})`. -/
private def augmentationX : F.orderedCechComplex.X 0 ⟶ F.obj (op {v}) :=
  F.orderedCechComplexDesc fun s ↦ toVertex F v hF s.val

private lemma single_augmentationX {s : Finset ι} (hs : #s = 0 + 1) :
    single F 0 s ≫ augmentationX F v hF = toVertex F v hF s := by
  rw [single_of_card_eq F hs, augmentationX, ι_orderedCechComplexDesc]

private lemma d_augmentationX : F.orderedCechComplex.d 1 0 ≫ augmentationX F v hF = 0 := by
  ext ⟨s, hs⟩
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hs
  -- Order the pair, then both restrictions to `F({v})` agree.
  wlog h : a < b generalizing a b
  · -- The summand is indexed by the subtype of sets of size two, so swapping `a` and `b` must
    -- also transport the cardinality proof `hs`.
    have e : (⟨{a, b}, hs⟩ : {s : Finset ι // #s = 0 + 1 + 1}) = ⟨{b, a}, pair_comm a b ▸ hs⟩ :=
      Subtype.ext (pair_comm a b)
    rw [e]
    exact this b a hab.symm _ (hab.lt_or_gt.resolve_left h)
  rw [ι_orderedCechComplex_d_pair_assoc F h, Preadditive.sub_comp, Category.assoc,
    Category.assoc, ← single_of_card_eq F (card_singleton a),
    ← single_of_card_eq F (card_singleton b), single_augmentationX F v hF (card_singleton a),
    single_augmentationX F v hF (card_singleton b), map_toVertex F v hF _ (singleton_nonempty a),
    map_toVertex F v hF _ (singleton_nonempty b), sub_self, comp_zero]

variable [HasZeroObject C]

/-- The augmentation of the ordered Čech complex onto `F({v})`, placed in degree `0`. -/
private def augmentation : F.orderedCechComplex ⟶ (ChainComplex.single₀ C).obj (F.obj (op {v})) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨augmentationX F v hF, d_augmentationX F v hF⟩

/-- The section of the augmentation: `F({v})` is the summand of `{v}`. -/
private def coneSection : (ChainComplex.single₀ C).obj (F.obj (op {v})) ⟶ F.orderedCechComplex :=
  (ChainComplex.fromSingle₀Equiv _ _).symm (single F 0 {v})

private lemma single_augmentation_f_zero {s : Finset ι} (hs : #s = 0 + 1) :
    single F 0 s ≫ (augmentation F v hF).f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 _).hom =
      toVertex F v hF s := by
  rw [← single_augmentationX F v hF hs]
  simp [augmentation]

private lemma ι_coneSectionf_zero :
    (HomologicalComplex.singleObjXSelf _ 0 _).inv ≫ (coneSection F v).f 0 = single F 0 {v} := by
  simp [coneSection]

private lemma coneSectioncomp_augmentation : coneSection F v ≫ augmentation F v hF = 𝟙 _ := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [← cancel_epi (HomologicalComplex.singleObjXSelf _ 0 _).inv,
    ← cancel_mono (HomologicalComplex.singleObjXSelf _ 0 _).hom, HomologicalComplex.comp_f,
    Category.assoc, Category.assoc, reassoc_of% ι_coneSectionf_zero,
    single_augmentation_f_zero F v hF (card_singleton _), toVertex_singleton,
    HomologicalComplex.id_f, Category.comp_id, Iso.inv_hom_id]

private lemma id_sub_augmentation_comp_section :
    𝟙 _ - augmentation F v hF ≫ coneSection F v =
      Homotopy.nullHomotopicMap' fun i j (_ : (ComplexShape.down ℕ).Rel j i) ↦
        homotopy F v hF i j := by
  ext (_ | p) : 1
  · rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left (ComplexShape.down_mk 1 0 rfl)
      (fun l h ↦ by simp at h)]
    refine hom_ext F fun s hs ↦ ?_
    rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, HomologicalComplex.comp_f,
      Preadditive.comp_sub, Category.comp_id,
      ← Iso.hom_inv_id_assoc (HomologicalComplex.singleObjXSelf _ 0 _) ((coneSection F v).f 0),
      reassoc_of% single_augmentation_f_zero F v hF hs, ι_coneSectionf_zero,
      ← coneFace_zero F v hF hs]
    by_cases hc : v ∈ s
    · rw [coneFace_of_mem F v hF hs hc, sub_self, ← Category.assoc,
        single_homotopy_of_mem F v hF hs hc, zero_comp]
    · rw [single_homotopy_d_of_notMem F v hF hs hc]
  · rw [Homotopy.nullHomotopicMap'_f (ComplexShape.down_mk (p + 2) (p + 1) rfl)
      (ComplexShape.down_mk (p + 1) p rfl)]
    refine hom_ext F fun s hs ↦ ?_
    simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, HomologicalComplex.comp_f,
      coneSection, ChainComplex.fromSingle₀Equiv_symm_apply_f_succ, comp_zero, sub_zero,
      Category.comp_id, Preadditive.comp_add, single_d_homotopy F v hF hs]
    by_cases hc : v ∈ s
    · rw [coneFace_of_mem F v hF hs hc, ← Category.assoc, single_homotopy_of_mem F v hF hs hc,
        zero_comp, add_zero]
    · rw [single_homotopy_d_of_notMem F v hF hs hc, add_sub_cancel]

end OrderedCechCone

open OrderedCechCone

variable [HasZeroObject C]

/-- **The ordered Čech complex of a cone is contractible onto its vertex.** If adjoining the index
`v` to a nonempty set `s` does not change the value of `F`, in that the restriction
`F(s ∪ {v}) ⟶ F(s)` is an isomorphism, then the ordered Čech complex of `F` is chain homotopy
equivalent to `F({v})`, placed in degree `0`. -/
def orderedCechHomotopyEquivOfVertex (v : ι)
    (hF : ∀ s : Finset ι, s.Nonempty → IsIso (F.map (homOfLE (subset_insert v s)).op)) :
    HomotopyEquiv F.orderedCechComplex ((ChainComplex.single₀ C).obj (F.obj (op {v}))) where
  hom := augmentation F v hF
  inv := coneSection F v
  homotopyHomInvId := (Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (id_sub_augmentation_comp_section F v hF)).trans
      (Homotopy.nullHomotopy' _))).symm
  homotopyInvHomId := Homotopy.ofEq (coneSectioncomp_augmentation F v hF)

/-- The homotopy equivalence `Functor.orderedCechHomotopyEquivOfVertex` is the identity on the
summand `F({v})` of the degree `0` term, followed by the identification of `F({v})` with the degree
`0` term of the single complex. -/
@[reassoc (attr := simp)]
lemma orderedCechComplexι_orderedCechHomotopyEquivOfVertex_hom_f_zero (v : ι)
    (hF : ∀ s : Finset ι, s.Nonempty → IsIso (F.map (homOfLE (subset_insert v s)).op)) :
    F.orderedCechComplexι (p := 0) ⟨{v}, card_singleton v⟩ ≫
        (F.orderedCechHomotopyEquivOfVertex v hF).hom.f 0 =
      (HomologicalComplex.singleObjXSelf _ 0 _).inv := by
  rw [← cancel_mono (HomologicalComplex.singleObjXSelf _ 0 _).hom, Iso.inv_hom_id, Category.assoc,
    ← single_of_card_eq F (card_singleton v)]
  exact (single_augmentation_f_zero F v hF (card_singleton v)).trans (toVertex_singleton F v hF)

/-- The inverse of the homotopy equivalence `Functor.orderedCechHomotopyEquivOfVertex` is, in
degree `0`, the inclusion of the summand `F({v})`. -/
@[simp, reassoc]
lemma orderedCechHomotopyEquivOfVertex_inv_f_zero (v : ι)
    (hF : ∀ s : Finset ι, s.Nonempty → IsIso (F.map (homOfLE (subset_insert v s)).op)) :
    (F.orderedCechHomotopyEquivOfVertex v hF).inv.f 0 =
      F.orderedCechComplexι (p := 0) ⟨{v}, card_singleton v⟩ := by
  rw [← single_of_card_eq F (card_singleton v)]
  -- The inverse is `coneSection F v`, which is defined through `fromSingle₀Equiv`.
  exact ChainComplex.fromSingle₀Equiv_symm_apply_f_zero _

end Functor

end CategoryTheory
