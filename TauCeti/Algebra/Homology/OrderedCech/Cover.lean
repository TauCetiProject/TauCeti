/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Single
public import TauCeti.Algebra.Homology.OrderedCech

import Mathlib.Tactic.Ring

/-!
# The ordered Čech complex of a cover of a set

Let `P : ι → Set A` be a family of subsets of a type `A`, indexed by a linearly ordered type, and
let `R` be an object of a preadditive category with coproducts. The functor
`TauCeti.freeCechFunctor R P` sends a finite set `s` of indices to the coproduct of copies of `R`
indexed by the points of `⋂_{i ∈ s} P i`, and an inclusion of finite sets to the map induced by the
inclusion of these intersections. Its ordered Čech complex has in degree `p` one copy of `R` for
each pair of a set `s = {i₀ < ⋯ < iₚ}` and a point of `P i₀ ∩ ⋯ ∩ P iₚ`, and it is augmented to
the coproduct of copies of `R` indexed by `A` (`TauCeti.freeCechAugmentation`).

When the `P i` cover `A`, this augmentation is a chain homotopy equivalence
(`TauCeti.freeCechHomotopyEquiv`): the ordered Čech complex is a resolution of the coproduct of
copies of `R` indexed by `A`. Choosing for each point `a` an index `c a` with `a ∈ P (c a)`, the
contracting homotopy sends the summand of `(s, a)` to `± (s ∪ {c a}, a)`, the cone with vertex
`c a`, and the section of the augmentation sends `a` to `({c a}, a)`.

The main example is the `q`-th row of the Čech double complex of singular chains of an open cover,
for which `A` is the set of singular `q`-simplices lying in some member of the cover and `P i` is
the set of those lying in the `i`-th member.

## Main definitions and results

* `TauCeti.freeCechFunctor R P`: the functor `s ↦ ∐_{⋂_{i ∈ s} P i} R` on finite sets of indices.
* `TauCeti.freeCechAugmentation R P`: the augmentation of its ordered Čech complex onto the
  coproduct of copies of `R` indexed by `A`, sending the summand of `({i}, a)` to the summand of
  `a` (`TauCeti.freeCechι_freeCechAugmentation_f_zero`).
* `TauCeti.freeCechHomotopyEquiv R hP`: for a cover, the augmentation is a chain homotopy
  equivalence.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in
  Mathematics 82, Springer, 1982, §8, for the ordered Čech complex of a cover and the exactness of
  its augmentation (the generalized Mayer–Vietoris principle). There exactness is proved with a
  partition of unity; for a cover of a set the cone on a chosen member suffices.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Finset

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  {ι : Type w} {A : Type w} (R : C) (P : ι → Set A)

/-- The coproduct of copies of `R` indexed by the points of `⋂_{i ∈ s} P i`, as a functor of the
finite set `s` of indices; an inclusion `t ⊆ s` goes to the map induced by the inclusion of
`⋂_{i ∈ s} P i` in `⋂_{i ∈ t} P i`. The empty set goes to the coproduct of copies of `R` indexed
by all of `A`. It is `sigmaConst.obj R` applied to the functor `s ↦ ⋂_{i ∈ s} P i` to types. It
is characterised by the summand inclusions `TauCeti.freeCechι`, which form a coproduct cocone
(`TauCeti.isColimitFreeCechCofan`), and by `TauCeti.ι_freeCechFunctor_map`. -/
def freeCechFunctor : (Finset ι)ᵒᵖ ⥤ C :=
  { obj s := {a : A // ∀ i ∈ s.unop, a ∈ P i}
    map f := TypeCat.ofHom fun a ↦ ⟨a.1, fun i hi ↦ a.2 i (leOfHom f.unop hi)⟩ } ⋙
    sigmaConst.obj R

variable {P}

/-- The inclusion of the summand of a point `a ∈ ⋂_{i ∈ s} P i` in the value of
`TauCeti.freeCechFunctor R P` at `s`. -/
def freeCechι {s : Finset ι} (a : A) (ha : ∀ i ∈ s, a ∈ P i) :
    R ⟶ (freeCechFunctor R P).obj (op s) :=
  Sigma.ι (fun _ : {a : A // ∀ i ∈ s, a ∈ P i} ↦ R) ⟨a, ha⟩

variable (P) in
/-- The summand inclusions `TauCeti.freeCechι` exhibit the value of `TauCeti.freeCechFunctor R P`
at `s` as the coproduct of copies of `R` indexed by the points of `⋂_{i ∈ s} P i`. -/
def isColimitFreeCechCofan (s : Finset ι) :
    IsColimit (Cofan.mk ((freeCechFunctor R P).obj (op s))
      fun a : {a : A // ∀ i ∈ s, a ∈ P i} ↦ freeCechι R a.1 a.2) :=
  coproductIsCoproduct _

/-- The morphism out of the value of `TauCeti.freeCechFunctor R P` at `s` given on each summand. -/
def freeCechDesc {s : Finset ι} {Y : C} (f : ∀ a : A, (∀ i ∈ s, a ∈ P i) → (R ⟶ Y)) :
    (freeCechFunctor R P).obj (op s) ⟶ Y :=
  Sigma.desc fun a ↦ f a.1 a.2

/-- The morphism `TauCeti.freeCechDesc R f` restricts to `f a ha` on the summand of `a`. -/
@[reassoc (attr := simp)]
lemma ι_freeCechDesc {s : Finset ι} {Y : C} (f : ∀ a : A, (∀ i ∈ s, a ∈ P i) → (R ⟶ Y)) (a : A)
    (ha : ∀ i ∈ s, a ∈ P i) :
    freeCechι R a ha ≫ freeCechDesc R f = f a ha :=
  Sigma.ι_comp_desc _ _

/-- Morphisms out of a value of `TauCeti.freeCechFunctor R P` agree when they agree on every
summand. -/
@[ext]
lemma freeCechFunctor_hom_ext {s : Finset ι} {Y : C} {f g : (freeCechFunctor R P).obj (op s) ⟶ Y}
    (h : ∀ a ha, freeCechι R a ha ≫ f = freeCechι R a ha ≫ g) : f = g :=
  Sigma.hom_ext _ _ fun a ↦ h a.1 a.2

/-- The map of `TauCeti.freeCechFunctor R P` induced by an inclusion of finite sets sends the
summand of a point to the summand of the same point. -/
@[reassoc (attr := simp)]
lemma ι_freeCechFunctor_map {s t : Finset ι} (f : op s ⟶ op t) (a : A) (ha : ∀ i ∈ s, a ∈ P i) :
    freeCechι R a ha ≫ (freeCechFunctor R P).map f =
      freeCechι R a fun i hi ↦ ha i (leOfHom f.unop hi) :=
  (Sigma.ι_comp_map' _ _ _).trans (Category.id_comp _)

variable [Preadditive C] [LinearOrder ι] [HasZeroObject C]

variable (P) in
/-- The augmentation of the ordered Čech complex of `TauCeti.freeCechFunctor R P` onto the
coproduct of copies of `R` indexed by `A`: the summand of `({i}, a)` goes to the summand of `a`
(`TauCeti.freeCechι_freeCechAugmentation_f_zero`). -/
def freeCechAugmentation :
    (freeCechFunctor R P).orderedCechComplex ⟶ (ChainComplex.single₀ C).obj (∐ fun _ : A ↦ R) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(freeCechFunctor R P).orderedCechAugmentation ≫
        freeCechDesc R fun a _ ↦ Sigma.ι (fun _ : A ↦ R) a, by
      rw [(freeCechFunctor R P).orderedCechComplex_d_comp_orderedCechAugmentation_assoc,
        zero_comp]⟩

/-- The augmentation sends the summand of a point `a` of `P i`, in the summand of `{i}`, to the
summand of `a`. -/
@[reassoc (attr := simp)]
lemma freeCechι_freeCechAugmentation_f_zero (s : {s : Finset ι // #s = 0 + 1}) (a : A)
    (ha : ∀ i ∈ s.1, a ∈ P i) :
    freeCechι R a ha ≫ (freeCechFunctor R P).orderedCechComplexι s ≫
        (freeCechAugmentation R P).f 0 =
      Sigma.ι (fun _ : A ↦ R) a := by
  have h : freeCechι R a ha ≫ (freeCechFunctor R P).orderedCechComplexι s ≫
      (freeCechAugmentation R P).f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 _).hom =
        Sigma.ι (fun _ : A ↦ R) a := by
    simp [freeCechAugmentation]
  simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom] at h
  rw [← Category.comp_id ((freeCechAugmentation R P).f 0)]
  exact h

namespace FreeCech

/-! ### The contracting homotopy

The proof works with the summand inclusions `single R p t a`, which are defined for every finite
set `t` and vanish unless `t` has `p + 1` elements, so that sums over the elements of a set need no
cardinality proofs. -/

/-- The inclusion of the summand of the point `a` and the set `t` in degree `p`; it vanishes when
`t` does not have `p + 1` elements. -/
private def single (p : ℕ) (t : Finset ι) (a : A) (ha : ∀ i ∈ t, a ∈ P i) :
    R ⟶ (freeCechFunctor R P).orderedCechComplex.X p :=
  if ht : #t = p + 1 then freeCechι R a ha ≫ (freeCechFunctor R P).orderedCechComplexι ⟨t, ht⟩
  else 0

omit [HasZeroObject C] in
private lemma single_of_card_eq {p : ℕ} {t : Finset ι} {a : A} (ha : ∀ i ∈ t, a ∈ P i)
    (ht : #t = p + 1) :
    single R p t a ha = freeCechι R a ha ≫ (freeCechFunctor R P).orderedCechComplexι ⟨t, ht⟩ :=
  by simp [single, ht]

omit [HasZeroObject C] in
private lemma single_of_card_ne {p : ℕ} {t : Finset ι} {a : A} (ha : ∀ i ∈ t, a ∈ P i)
    (ht : #t ≠ p + 1) : single R p t a ha = 0 :=
  by simp [single, ht]

omit [HasZeroObject C] in
private lemma single_congr {p : ℕ} {t t' : Finset ι} {a : A} (ha : ∀ i ∈ t, a ∈ P i)
    (e : t = t') : single R p t a ha = single R p t' a (e ▸ ha) := by
  subst e
  rfl

omit [HasZeroObject C] in
private lemma hom_ext {p : ℕ} {Y : C} {f g : (freeCechFunctor R P).orderedCechComplex.X p ⟶ Y}
    (h : ∀ (s : Finset ι) (_ : #s = p + 1) (a : A) (ha : ∀ i ∈ s, a ∈ P i),
      single R p s a ha ≫ f = single R p s a ha ≫ g) : f = g := by
  refine Functor.orderedCechComplex_hom_ext _ fun s ↦ freeCechFunctor_hom_ext R fun a ha ↦ ?_
  simpa only [single_of_card_eq R ha s.2, Category.assoc] using h s.1 s.2 a ha

omit [HasZeroObject C] in
private lemma single_d {p : ℕ} {s : Finset ι} (hs : #s = p + 1 + 1) {a : A}
    (ha : ∀ i ∈ s, a ∈ P i) :
    single R (p + 1) s a ha ≫ (freeCechFunctor R P).orderedCechComplex.d (p + 1) p =
      ∑ i ∈ s, ((-1 : ℤ) ^ #{j ∈ s | j < i}) •
        single R p (s.erase i) a fun j hj ↦ ha j (mem_of_mem_erase hj) := by
  rw [single_of_card_eq R ha hs, Category.assoc, Functor.ι_orderedCechComplex_d (s := ⟨s, hs⟩),
    Preadditive.comp_sum, ← sum_coe_sort s]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul, ι_freeCechFunctor_map_assoc,
    single_of_card_eq R _ (by rw [card_erase_of_mem i.2, hs, Nat.add_sub_cancel])]

/-- The augmentation on a summand inclusion of degree `0`. -/
private lemma single_freeCechAugmentation {s : Finset ι} (hs : #s = 0 + 1) {a : A}
    (ha : ∀ i ∈ s, a ∈ P i) :
    single R 0 s a ha ≫ (freeCechAugmentation R P).f 0 ≫
        (HomologicalComplex.singleObjXSelf _ 0 _).hom =
      Sigma.ι (fun _ : A ↦ R) a := by
  rw [single_of_card_eq R ha hs, Category.assoc, ChainComplex.single₀ObjXSelf, Iso.refl_hom]
  -- The identity is on degree `0` of the single complex, which is `∐ fun _ : A ↦ R` only up to
  -- definitional unfolding of `HomologicalComplex.single`.
  exact (freeCechι_freeCechAugmentation_f_zero_assoc R ⟨s, hs⟩ a ha _).trans (Category.comp_id _)

variable (hP : ⋃ i, P i = Set.univ)

/-- A chosen member of the cover containing `a`. -/
private def vertex (a : A) : ι :=
  (Set.mem_iUnion.1 (hP ▸ Set.mem_univ a)).choose

omit [LinearOrder ι] in
private lemma mem_vertex (a : A) : a ∈ P (vertex hP a) :=
  (Set.mem_iUnion.1 (hP ▸ Set.mem_univ a)).choose_spec

/-- The components of the contracting homotopy: the summand of `(s, a)` goes to `± (s ∪ {c}, a)`,
for the chosen member `c` of the cover containing `a`. The sign makes `c` the vertex of a cone. -/
private def homotopy (p j : ℕ) :
    (freeCechFunctor R P).orderedCechComplex.X p ⟶ (freeCechFunctor R P).orderedCechComplex.X j :=
  Functor.orderedCechComplexDesc _ fun s ↦ freeCechDesc R fun a ha ↦
    ((-1 : ℤ) ^ #{k ∈ s.1 | k < vertex hP a}) •
      single R j (insert (vertex hP a) s.1) a
        ((forall_mem_insert _ _ _).2 ⟨mem_vertex hP a, ha⟩)

omit [HasZeroObject C] in
private lemma single_homotopy {p : ℕ} (j : ℕ) {s : Finset ι} (hs : #s = p + 1) {a : A}
    (ha : ∀ i ∈ s, a ∈ P i) :
    single R p s a ha ≫ homotopy R hP p j =
      ((-1 : ℤ) ^ #{k ∈ s | k < vertex hP a}) •
        single R j (insert (vertex hP a) s) a
          ((forall_mem_insert _ _ _).2 ⟨mem_vertex hP a, ha⟩) := by
  rw [single_of_card_eq R ha hs, Category.assoc, homotopy, Functor.ι_orderedCechComplexDesc,
    ι_freeCechDesc]

/-- The sum `∑ₖ ± ((s ∖ {k}) ∪ {c}, a)` over `k ∈ s`, which is both the homotopy after the
differential on `(s, a)` and the remainder of the differential after the homotopy. -/
private def coneFace (p : ℕ) (s : Finset ι) (a : A) (ha : ∀ i ∈ s, a ∈ P i) :
    R ⟶ (freeCechFunctor R P).orderedCechComplex.X p :=
  ∑ k ∈ s, ((-1 : ℤ) ^ #{j ∈ s | j < k} * (-1) ^ #{j ∈ s.erase k | j < vertex hP a}) •
    single R p (insert (vertex hP a) (s.erase k)) a
      ((forall_mem_insert _ _ _).2 ⟨mem_vertex hP a, fun j hj ↦ ha j (mem_of_mem_erase hj)⟩)

omit hP in
/-- Deleting an element `k` of `s` and adding `c ∉ s` in either order gives opposite signs. -/
private lemma sign_cone {s : Finset ι} {c k : ι} (hc : c ∉ s) (hk : k ∈ s) :
    ((-1 : ℤ) ^ #{j ∈ s | j < c}) * (-1) ^ #{j ∈ insert c s | j < k} =
      -((-1) ^ #{j ∈ s | j < k} * (-1) ^ #{j ∈ s.erase k | j < c}) := by
  have hck : c ≠ k := fun h ↦ hc (h ▸ hk)
  rcases hck.lt_or_gt with h | h
  · simp only [filter_insert, h, ↓reduceIte, filter_erase]
    rw [card_insert_of_notMem (by simp [hc]),
      erase_eq_of_notMem (show k ∉ {j ∈ s | j < c} by simp [h.not_gt]), pow_succ]
    ring
  · simp only [filter_insert, h.not_gt, ↓reduceIte, filter_erase]
    rw [← card_erase_add_one (mem_filter.2 ⟨hk, h⟩), pow_succ]
    ring

omit [HasZeroObject C] in
private lemma single_homotopy_d_of_notMem {p : ℕ} {s : Finset ι} (hs : #s = p + 1) {a : A}
    (ha : ∀ i ∈ s, a ∈ P i) (hc : vertex hP a ∉ s) :
    single R p s a ha ≫ homotopy R hP p (p + 1) ≫
        (freeCechFunctor R P).orderedCechComplex.d (p + 1) p =
      single R p s a ha - coneFace R hP p s a ha := by
  rw [← Category.assoc, single_homotopy R hP _ hs, Preadditive.zsmul_comp,
    single_d R (by rw [card_insert_of_notMem hc, hs]), sum_insert hc, smul_add, coneFace,
    sub_eq_add_neg, ← sum_neg_distrib, Finset.smul_sum, single_congr R _ (erase_insert hc),
    smul_smul, filter_insert]
  simp only [lt_irrefl, ↓reduceIte]
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  congr 1
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hck : vertex hP a ≠ k := fun h ↦ hc (h ▸ hk)
  rw [smul_smul, sign_cone hc hk, neg_smul, single_congr R _ (erase_insert_of_ne hck)]

omit [HasZeroObject C] in
private lemma single_homotopy_of_mem {p : ℕ} {s : Finset ι} (hs : #s = p + 1) {a : A}
    (ha : ∀ i ∈ s, a ∈ P i) (hc : vertex hP a ∈ s) :
    single R p s a ha ≫ homotopy R hP p (p + 1) = 0 := by
  rw [single_homotopy R hP _ hs,
    single_of_card_ne R _ (by rw [insert_eq_of_mem hc, hs]; omega), smul_zero]

omit [HasZeroObject C] in
private lemma single_d_homotopy {p : ℕ} {s : Finset ι} (hs : #s = p + 1 + 1) {a : A}
    (ha : ∀ i ∈ s, a ∈ P i) :
    single R (p + 1) s a ha ≫ (freeCechFunctor R P).orderedCechComplex.d (p + 1) p ≫
        homotopy R hP p (p + 1) =
      coneFace R hP (p + 1) s a ha := by
  rw [← Category.assoc, single_d R hs, Preadditive.sum_comp, coneFace]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Preadditive.zsmul_comp, single_homotopy R hP _ (by rw [card_erase_of_mem hk, hs]; rfl),
    smul_smul]

omit [HasZeroObject C] in
private lemma coneFace_of_mem {p : ℕ} {s : Finset ι} (hs : #s = p + 1) {a : A}
    (ha : ∀ i ∈ s, a ∈ P i) (hc : vertex hP a ∈ s) :
    coneFace R hP p s a ha = single R p s a ha := by
  rw [coneFace, sum_eq_single (vertex hP a)]
  · rw [single_congr R _ (insert_erase hc), filter_erase, erase_eq_of_notMem (by simp),
      ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  · intro k hk hkc
    rw [single_of_card_ne R _ (by
      rw [insert_eq_of_mem (mem_erase.2 ⟨Ne.symm hkc, hc⟩), card_erase_of_mem hk, hs]; omega),
      smul_zero]
  · exact fun h ↦ (h hc).elim

omit [HasZeroObject C] in
/-- In degree `0` the cone face of `({i}, a)` is the summand of `({c}, a)`. -/
private lemma coneFace_zero {s : Finset ι} (hs : #s = 0 + 1) {a : A} (ha : ∀ i ∈ s, a ∈ P i) :
    coneFace R hP 0 s a ha =
      single R 0 {vertex hP a} a (by simpa using mem_vertex hP a) := by
  obtain ⟨i, rfl⟩ := card_eq_one.1 hs
  simp [coneFace, filter_singleton]

/-- The section of the augmentation: the summand of `a` goes to the summand of `({c}, a)`. -/
private def section_ :
    (ChainComplex.single₀ C).obj (∐ fun _ : A ↦ R) ⟶ (freeCechFunctor R P).orderedCechComplex :=
  (ChainComplex.fromSingle₀Equiv _ _).symm
    (Sigma.desc fun a ↦ single R 0 {vertex hP a} a (by simpa using mem_vertex hP a))

private lemma ι_section_f_zero (a : A) :
    Sigma.ι (fun _ : A ↦ R) a ≫ (HomologicalComplex.singleObjXSelf _ 0 _).inv ≫
        (section_ R hP).f 0 =
      single R 0 {vertex hP a} a (by simpa using mem_vertex hP a) := by
  simp [section_]

private lemma section_comp_freeCechAugmentation :
    section_ R hP ≫ freeCechAugmentation R P = 𝟙 _ := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [← cancel_epi (HomologicalComplex.singleObjXSelf _ 0 _).inv,
    ← cancel_mono (HomologicalComplex.singleObjXSelf _ 0 _).hom]
  refine Sigma.hom_ext _ _ fun a ↦ ?_
  rw [HomologicalComplex.comp_f, Category.assoc, Category.assoc, reassoc_of% ι_section_f_zero,
    single_freeCechAugmentation R (card_singleton _), HomologicalComplex.id_f, Category.comp_id,
    Iso.inv_hom_id, Category.comp_id]

private lemma id_sub_freeCechAugmentation_comp_section :
    𝟙 _ - freeCechAugmentation R P ≫ section_ R hP =
      Homotopy.nullHomotopicMap' fun i j (_ : (ComplexShape.down ℕ).Rel j i) ↦
        homotopy R hP i j := by
  ext (_ | p) : 1
  · rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left (ComplexShape.down_mk 1 0 rfl)
      (fun l h ↦ by simp at h)]
    refine hom_ext R fun s hs a ha ↦ ?_
    rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, HomologicalComplex.comp_f,
      Preadditive.comp_sub, Category.comp_id,
      ← Iso.hom_inv_id_assoc (HomologicalComplex.singleObjXSelf _ 0 _) ((section_ R hP).f 0),
      reassoc_of% single_freeCechAugmentation R hs ha, ι_section_f_zero, ← coneFace_zero R hP hs ha]
    by_cases hc : vertex hP a ∈ s
    · rw [coneFace_of_mem R hP hs ha hc, sub_self, ← Category.assoc,
        single_homotopy_of_mem R hP hs ha hc, zero_comp]
    · rw [single_homotopy_d_of_notMem R hP hs ha hc]
  · rw [Homotopy.nullHomotopicMap'_f (ComplexShape.down_mk (p + 2) (p + 1) rfl)
      (ComplexShape.down_mk (p + 1) p rfl)]
    refine hom_ext R fun s hs a ha ↦ ?_
    simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, HomologicalComplex.comp_f,
      section_, ChainComplex.fromSingle₀Equiv_symm_apply_f_succ, comp_zero, sub_zero,
      Category.comp_id, Preadditive.comp_add, single_d_homotopy R hP hs ha]
    by_cases hc : vertex hP a ∈ s
    · rw [coneFace_of_mem R hP hs ha hc, ← Category.assoc, single_homotopy_of_mem R hP hs ha hc,
        zero_comp, add_zero]
    · rw [single_homotopy_d_of_notMem R hP hs ha hc, add_sub_cancel]

end FreeCech

open FreeCech in
/-- **The ordered Čech complex of a cover resolves the free object on the covered set.** When the
subsets `P i` cover `A`, the augmentation of the ordered Čech complex of
`TauCeti.freeCechFunctor R P` onto the coproduct of copies of `R` indexed by `A` is a chain
homotopy equivalence. -/
def freeCechHomotopyEquiv (hP : ⋃ i, P i = Set.univ) :
    HomotopyEquiv (freeCechFunctor R P).orderedCechComplex
      ((ChainComplex.single₀ C).obj (∐ fun _ : A ↦ R)) where
  hom := freeCechAugmentation R P
  inv := section_ R hP
  homotopyHomInvId := (Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (id_sub_freeCechAugmentation_comp_section R hP)).trans
      (Homotopy.nullHomotopy' _))).symm
  homotopyInvHomId := Homotopy.ofEq (section_comp_freeCechAugmentation R hP)

/-- The forward map of `TauCeti.freeCechHomotopyEquiv` is the augmentation. -/
@[simp]
lemma freeCechHomotopyEquiv_hom (hP : ⋃ i, P i = Set.univ) :
    (freeCechHomotopyEquiv R hP).hom = freeCechAugmentation R P := (rfl)

end TauCeti
