/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.Data.Fintype.Powerset

import TauCeti.Data.Finset.Basic

/-!
# The signed totalization of a finite commutative cube

Let `ι` be a finite linearly ordered type. A commutative cube indexed by `ι` in a category `C` is
a functor `F : Finset ι ⥤ C` on the subsets of `ι`, ordered by inclusion: it assigns an object
`F(S)` to every vertex `S ⊆ ι` and an edge map `F(S) ⟶ F(S ∪ {a})` to every `a ∉ S`, and every
square face of edge maps commutes. When `C` is preadditive with finite biproducts, the signed
height totalization of `F` is the cochain complex whose term in degree `r` is the biproduct of the
`F(S)` over the vertices of height `#S = r`, and whose differential is the sum of the edge maps
leaving a vertex, the edge `S ⟶ S ∪ {a}` carrying the sign `(-1)` to the number of elements of
`S` below `a`. These signs turn the commutativity of each square face into anticommutativity, so
the differential squares to zero.

This is the construction of the Khovanov complex from the cube of resolutions of a link diagram,
where `ι` is the set of crossings with a chosen order and `S` is the set of crossings given the
second resolution; the cochain complex is indexed by `ℤ` so that it can be shifted to the
normalized grading. Its terms vanish outside the degrees `0, …, #ι`, and in degree `0` it is the
initial vertex `F(∅)`.

The sign rule is that of the ordered Čech complex `CategoryTheory.Functor.orderedCechComplex`:
after reversing all arrows, the vertices of positive height form the ordered Čech complex of the
opposite functor, shifted down by one degree. Here the vertex `F(∅)` is part of the complex, the
degree is the height `#S` itself, and the terms are finite biproducts.

## Main definitions

* `CategoryTheory.Functor.cubeComplex F`: the signed totalization of the cube `F`; its terms are
  biproducts with summand inclusions `Functor.cubeComplexι` and projections
  `Functor.cubeComplexπ`, and its differential is characterised on summands by
  `Functor.ι_cubeComplex_d` and, into a vertex, by `Functor.cubeComplex_d_π`.
* `CategoryTheory.NatTrans.cubeComplexMap α`: the cochain map induced by a map of cubes.
* `CategoryTheory.cubeComplexFunctor C ι`: the totalization as an additive functor of the cube.

## Main results

* `Functor.isZero_cubeComplex_X_of_neg`, `Functor.isZero_cubeComplex_X_of_card_lt`: the terms
  vanish outside the degrees `0, …, #ι`.
* `Functor.cubeComplex_total`: each term is the direct sum of its vertices.
* `Functor.cubeComplexXZeroIso`: the degree `0` term is the initial vertex `F(∅)`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §2.
-/

public section

noncomputable section

open CategoryTheory Limits Finset

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {ι : Type w} [Fintype ι] [LinearOrder ι]

namespace Functor

variable (F : Finset ι ⥤ C)

/-- The edge map from the vertex `F(S)` to the summand `F(T)` of the biproduct of the vertices of
height `j`, for `S ⊆ T`; it vanishes when `T` has another height. -/
private def cubeInclusion (j : ℤ) {S T : Finset ι} (h : S ⊆ T) :
    F.obj S ⟶ ⨁ fun U : {U : Finset ι // (#U : ℤ) = j} ↦ F.obj U.1 :=
  if hT : (#T : ℤ) = j then
    F.map (homOfLE h) ≫ biproduct.ι (fun U : {U : Finset ι // (#U : ℤ) = j} ↦ F.obj U.1) ⟨T, hT⟩
  else 0

omit [LinearOrder ι] in
private lemma cubeInclusion_congr (j : ℤ) {S T T' : Finset ι} (h : S ⊆ T) (e : T = T') :
    F.cubeInclusion j h = F.cubeInclusion j (e ▸ h) := by
  subst e
  rfl

omit [LinearOrder ι] in
private lemma map_comp_cubeInclusion (j : ℤ) {S T U : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ U) :
    F.map (homOfLE h₁) ≫ F.cubeInclusion j h₂ = F.cubeInclusion j (h₁.trans h₂) := by
  unfold cubeInclusion
  split_ifs
  · rw [← Category.assoc, ← F.map_comp, homOfLE_comp]
  · rw [comp_zero]

private lemma cubeInclusion_insert_eq_zero (j : ℤ) {S : Finset ι} {a : ι} (ha : a ∉ S)
    (hj : (#S : ℤ) + 1 ≠ j) : F.cubeInclusion j (S.subset_insert a) = 0 := by
  rw [cubeInclusion, dite_eq_right (by rwa [card_insert_of_notMem ha, Nat.cast_succ])]

/-- The signed cube differential, sending the vertex `F(S)` to the signed sum of its edge maps
to the vertices `F(S ∪ {a})`. -/
private def cubeD (i j : ℤ) :
    (⨁ fun S : {S : Finset ι // (#S : ℤ) = i} ↦ F.obj S.1) ⟶
      ⨁ fun T : {T : Finset ι // (#T : ℤ) = j} ↦ F.obj T.1 :=
  biproduct.desc fun S ↦ ∑ a ∈ S.1ᶜ, ((-1 : ℤ) ^ #{b ∈ S.1 | b < a}) •
    F.cubeInclusion j (S.1.subset_insert a)

private lemma cubeInclusion_comp_cubeD {j k : ℤ} (hjk : j + 1 = k) {S T : Finset ι}
    (h : S ⊆ T) : F.cubeInclusion j h ≫ F.cubeD j k = ∑ a ∈ Tᶜ,
      ((-1 : ℤ) ^ #{b ∈ T | b < a}) • F.cubeInclusion k (h.trans (T.subset_insert a)) := by
  by_cases hT : (#T : ℤ) = j
  · rw [cubeInclusion, dite_eq_left hT, Category.assoc, cubeD, biproduct.ι_desc,
      Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Preadditive.comp_zsmul, map_comp_cubeInclusion]
  · rw [cubeInclusion, dite_eq_right hT, zero_comp]
    refine (Finset.sum_eq_zero fun a ha ↦ ?_).symm
    rw [← map_comp_cubeInclusion F k h (T.subset_insert a),
      cubeInclusion_insert_eq_zero F k (mem_compl.1 ha)
      (by omega), comp_zero, smul_zero]

private lemma cubeD_comp_cubeD (i : ℤ) : F.cubeD i (i + 1) ≫ F.cubeD (i + 1) (i + 1 + 1) = 0 := by
  refine biproduct.hom_ext' _ _ fun S ↦ ?_
  rw [← Category.assoc, cubeD, biproduct.ι_desc, comp_zero, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, F.cubeInclusion_comp_cubeD rfl, Finset.smul_sum, smul_smul]
  rw [Finset.sum_sigma']
  -- The two routes `S ⟶ S ∪ {a} ⟶ S ∪ {a, b}` and `S ⟶ S ∪ {b} ⟶ S ∪ {a, b}` around each square
  -- face cancel.
  refine Finset.sum_involution (fun p _ ↦ ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [mem_sigma, mem_compl, mem_insert, not_or] at hp
    rw [cubeInclusion_congr F _ _ (insert_comm b a S.1), ← add_smul,
      neg_one_pow_card_filter_lt_mul_insert_insert hp.1 hp.2.2 (Ne.symm hp.2.1),
      neg_add_cancel, zero_smul]
  · rintro ⟨a, b⟩ hp _ h
    simp only [mem_sigma, mem_compl, mem_insert, not_or] at hp
    exact hp.2.1 (congrArg Sigma.fst h)
  · rintro ⟨a, b⟩ hp
    simp only [mem_sigma, mem_compl, mem_insert, not_or] at hp ⊢
    exact ⟨hp.2.2, Ne.symm hp.2.1, hp.1⟩
  · rintro ⟨a, b⟩ _
    rfl

/-- The signed totalization of the commutative cube `F`: in degree `r` it is the biproduct of
the vertices `F(S)` of height `#S = r`, with differential the sum of the edge maps
`F(S) ⟶ F(S ∪ {a})`, signed by `(-1)` to the number of elements of `S` below `a`. It is
characterised by the summand inclusions `Functor.cubeComplexι` and projections
`Functor.cubeComplexπ`, and by `Functor.ι_cubeComplex_d`. -/
def cubeComplex : CochainComplex C ℤ where
  X r := ⨁ fun S : {S : Finset ι // (#S : ℤ) = r} ↦ F.obj S.1
  d := F.cubeD
  shape i j hij := by
    refine biproduct.hom_ext' _ _ fun S ↦ ?_
    rw [cubeD, biproduct.ι_desc, comp_zero]
    refine Finset.sum_eq_zero fun a ha ↦ ?_
    rw [cubeInclusion_insert_eq_zero F j (mem_compl.1 ha) (by rw [S.2]; exact hij), smul_zero]
  d_comp_d' := by
    rintro i _ _ rfl rfl
    exact F.cubeD_comp_cubeD i

/-- The degree `r` term is the biproduct of the vertices of height `r`. -/
lemma cubeComplex_X (r : ℤ) :
    F.cubeComplex.X r = ⨁ fun S : {S : Finset ι // (#S : ℤ) = r} ↦ F.obj S.1 := (rfl)

/-- The inclusion of the vertex `F(S)` into the degree `r` term of the cube complex, for a vertex
of height `#S = r`. -/
def cubeComplexι {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) : F.obj S.1 ⟶ F.cubeComplex.X r :=
  biproduct.ι (fun S : {S : Finset ι // (#S : ℤ) = r} ↦ F.obj S.1) S

/-- The vertex inclusion agrees with the biproduct inclusion under the term identification. -/
@[reassoc (attr := simp)]
lemma cubeComplexι_comp_eqToHom {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι S ≫ eqToHom (F.cubeComplex_X r) =
      biproduct.ι (fun T : {T : Finset ι // (#T : ℤ) = r} ↦ F.obj T.1) S :=
  Category.comp_id _

/-- The projection of the degree `r` term of the cube complex onto the vertex `F(S)`, for a vertex
of height `#S = r`. -/
def cubeComplexπ {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) : F.cubeComplex.X r ⟶ F.obj S.1 :=
  biproduct.π (fun S : {S : Finset ι // (#S : ℤ) = r} ↦ F.obj S.1) S

/-- The biproduct projection agrees with the vertex projection under the term identification. -/
@[reassoc (attr := simp)]
lemma eqToHom_comp_cubeComplexπ {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    eqToHom (F.cubeComplex_X r) ≫
      biproduct.π (fun T : {T : Finset ι // (#T : ℤ) = r} ↦ F.obj T.1) S =
        F.cubeComplexπ S :=
  Category.id_comp _

/-- Transporting a cube term to an equal height preserves each vertex inclusion. -/
@[reassoc (attr := simp)]
lemma cubeComplexι_comp_XIsoOfEq_hom {r r' : ℤ} (h : r = r')
    (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι S ≫ (F.cubeComplex.XIsoOfEq h).hom =
      F.cubeComplexι ⟨S.1, S.2.trans h⟩ := by
  subst h
  simp

/-- The inclusion of a vertex followed by the projection onto a vertex of the same height is the
identity when the vertices agree, and zero otherwise. -/
@[reassoc]
lemma cubeComplexι_π {r : ℤ} (S T : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι S ≫ F.cubeComplexπ T =
      if h : S = T then eqToHom (congrArg (fun U : {S : Finset ι // (#S : ℤ) = r} ↦ F.obj U.1) h)
      else 0 :=
  biproduct.ι_π _ S T

/-- The inclusion of a vertex followed by the projection onto it is the identity. -/
@[reassoc (attr := simp)]
lemma cubeComplexι_π_self {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι S ≫ F.cubeComplexπ S = 𝟙 _ :=
  biproduct.ι_π_self _ S

/-- The inclusion of a vertex followed by the projection onto another vertex vanishes. -/
@[reassoc (attr := simp)]
lemma cubeComplexι_π_of_ne {r : ℤ} {S T : {S : Finset ι // (#S : ℤ) = r}} (h : S ≠ T) :
    F.cubeComplexι S ≫ F.cubeComplexπ T = 0 :=
  biproduct.ι_π_ne _ h

/-- The inclusion of a vertex is compatible with the identification of equal vertices. -/
@[reassoc]
lemma eqToHom_comp_cubeComplexι {r : ℤ} {S T : Finset ι} (h : S = T) (hT : (#T : ℤ) = r) :
    eqToHom (congrArg F.obj h) ≫ F.cubeComplexι ⟨T, hT⟩ = F.cubeComplexι ⟨S, h ▸ hT⟩ := by
  subst h
  simp

/-- The morphism out of the degree `r` term of the cube complex given on each vertex. -/
def cubeComplexDesc {r : ℤ} {A : C} (f : ∀ S : {S : Finset ι // (#S : ℤ) = r}, F.obj S.1 ⟶ A) :
    F.cubeComplex.X r ⟶ A :=
  biproduct.desc f

/-- The morphism `Functor.cubeComplexDesc f` restricts to `f S` on the vertex `F(S)`. -/
@[reassoc (attr := simp)]
lemma ι_cubeComplexDesc {r : ℤ} {A : C}
    (f : ∀ S : {S : Finset ι // (#S : ℤ) = r}, F.obj S.1 ⟶ A) (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι S ≫ F.cubeComplexDesc f = f S :=
  biproduct.ι_desc f S

/-- The morphism into the degree `r` term of the cube complex given on each vertex. -/
def cubeComplexLift {r : ℤ} {A : C} (f : ∀ S : {S : Finset ι // (#S : ℤ) = r}, A ⟶ F.obj S.1) :
    A ⟶ F.cubeComplex.X r :=
  biproduct.lift f

/-- The morphism `Functor.cubeComplexLift f` projects to `f S` on the vertex `F(S)`. -/
@[reassoc (attr := simp)]
lemma cubeComplexLift_π {r : ℤ} {A : C}
    (f : ∀ S : {S : Finset ι // (#S : ℤ) = r}, A ⟶ F.obj S.1) (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexLift f ≫ F.cubeComplexπ S = f S :=
  biproduct.lift_π f S

/-- The projections onto the vertices of height `r`, followed by their inclusions, sum to the
identity of the degree `r` term of the cube complex. -/
@[simp]
lemma cubeComplex_total (r : ℤ) :
    ∑ S : {S : Finset ι // (#S : ℤ) = r}, F.cubeComplexπ S ≫ F.cubeComplexι S = 𝟙 _ :=
  biproduct.total

/-- Morphisms out of a term of the cube complex agree when they agree on every vertex. -/
@[ext]
lemma cubeComplex_hom_ext {r : ℤ} {A : C} {f g : F.cubeComplex.X r ⟶ A}
    (h : ∀ S, F.cubeComplexι S ≫ f = F.cubeComplexι S ≫ g) : f = g :=
  biproduct.hom_ext' _ _ h

/-- Morphisms into a term of the cube complex agree when their projections to every vertex
agree. -/
@[ext 1001]
lemma cubeComplex_hom_ext' {r : ℤ} {A : C} {f g : A ⟶ F.cubeComplex.X r}
    (h : ∀ S, f ≫ F.cubeComplexπ S = g ≫ F.cubeComplexπ S) : f = g :=
  biproduct.hom_ext _ _ h

/-- A term of the signed totalization vanishes exactly when all vertices of that height vanish. -/
lemma isZero_cubeComplex_X_iff (r : ℤ) :
    IsZero (F.cubeComplex.X r) ↔
      ∀ S : {S : Finset ι // (#S : ℤ) = r}, IsZero (F.obj S.1) := by
  constructor
  · intro h S
    rw [IsZero.iff_id_eq_zero, ← F.cubeComplexι_π_self S,
      h.eq_zero_of_tgt (F.cubeComplexι S), zero_comp]
  · intro h
    rw [IsZero.iff_id_eq_zero]
    exact F.cubeComplex_hom_ext fun S ↦ (h S).eq_of_src _ _

/-- The cube differential on the vertex `F(S)` of height `r` is the sum, over the indices `a ∉ S`,
of the edge map `F(S) ⟶ F(S ∪ {a})` with sign `(-1)` to the number of elements of `S` below
`a`. -/
@[reassoc]
lemma ι_cubeComplex_d {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι S ≫ F.cubeComplex.d r (r + 1) =
      ∑ a : (S.1ᶜ : Finset ι), ((-1 : ℤ) ^ #{b ∈ S.1 | b < a.1}) •
        F.map (homOfLE (S.1.subset_insert a.1)) ≫
          F.cubeComplexι ⟨insert a.1 S.1, by
            rw [card_insert_of_notMem (mem_compl.1 a.2), Nat.cast_succ, S.2]⟩ := by
  refine (biproduct.ι_desc _ S).trans ?_
  rw [← sum_coe_sort]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [cubeInclusion,
    dite_eq_left (by rw [card_insert_of_notMem (mem_compl.1 a.2), Nat.cast_succ, S.2])]
  -- `cubeComplexι` is the biproduct inclusion.
  rfl

/-- The cube differential into the vertex `F(T)` of height `r + 1` is the sum, over the indices
`a ∈ T`, of the projection onto the vertex `F(T \ {a})` followed by the edge map
`F(T \ {a}) ⟶ F(T)`, with sign `(-1)` to the number of elements of `T \ {a}` below `a`. -/
@[reassoc]
lemma cubeComplex_d_π {r : ℤ} (T : {T : Finset ι // (#T : ℤ) = r + 1}) :
    F.cubeComplex.d r (r + 1) ≫ F.cubeComplexπ T =
      ∑ a : T.1, ((-1 : ℤ) ^ #{b ∈ T.1.erase a.1 | b < a.1}) •
        F.cubeComplexπ ⟨T.1.erase a.1, by have := card_erase_add_one a.2; have := T.2; omega⟩ ≫
          F.map (homOfLE (T.1.erase_subset a.1)) := by
  refine F.cubeComplex_hom_ext fun U ↦ ?_
  rw [F.ι_cubeComplex_d_assoc, Preadditive.sum_comp, Preadditive.comp_sum]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  by_cases hU : ∃ c ∉ U.1, insert c U.1 = T.1
  · obtain ⟨c, hc, hT⟩ := hU
    have hcT : c ∈ T.1 := hT ▸ mem_insert_self c U.1
    have hU' : T.1.erase c = U.1 := hT ▸ erase_insert hc
    rw [Finset.sum_eq_single_of_mem (⟨c, mem_compl.2 hc⟩ : (U.1ᶜ : Finset ι)) (mem_univ _) ?hL,
      Finset.sum_eq_single_of_mem (⟨c, hcT⟩ : T.1) (mem_univ _) ?hR]
    case hL =>
      rintro ⟨a, ha⟩ - hac
      rw [F.cubeComplexι_π_of_ne, comp_zero, smul_zero]
      intro h
      have ha' : a ∈ T.1 := congrArg Subtype.val h ▸ mem_insert_self a U.1
      rw [← hT] at ha'
      exact hac (Subtype.ext ((mem_insert.1 ha').resolve_right (mem_compl.1 ha)))
    case hR =>
      rintro ⟨a, ha⟩ - hac
      rw [F.cubeComplexι_π_of_ne_assoc, zero_comp, smul_zero]
      intro h
      have hU : U.1 = T.1.erase a := congrArg Subtype.val h
      have haU : a ∈ U.1 := by
        rw [← hT] at ha
        exact (mem_insert.1 ha).resolve_left fun h ↦ hac (Subtype.ext h)
      exact notMem_erase a T.1 (hU ▸ haU)
    -- Both sides are the edge map `F(U) ⟶ F(T)` with the same sign.
    have key {s : ℤ} (V W : {S : Finset ι // (#S : ℤ) = s}) (h : V.1 = W.1) :
        F.cubeComplexι V ≫ F.cubeComplexπ W = F.map (eqToHom h) := by
      obtain ⟨V, hV⟩ := V
      obtain ⟨W, hW⟩ := W
      dsimp only at h
      subst h
      simp
    have hs : #{b ∈ T.1.erase c | b < c} = #{b ∈ U.1 | b < c} := by rw [hU']
    dsimp only
    rw [hs, key _ T hT, reassoc_of% (key U _ hU'.symm), ← F.map_comp, ← F.map_comp]
    exact congrArg (fun f ↦ ((-1 : ℤ) ^ #{b ∈ U.1 | b < c}) • F.map f) (Subsingleton.elim _ _)
  · push Not at hU
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · rintro ⟨a, ha⟩ -
      rw [F.cubeComplexι_π_of_ne_assoc, zero_comp, smul_zero]
      intro h
      have hU' : U.1 = T.1.erase a := congrArg Subtype.val h
      exact hU a (hU' ▸ notMem_erase a T.1) (by rw [hU', insert_erase ha])
    · rintro ⟨a, ha⟩ -
      rw [F.cubeComplexι_π_of_ne, comp_zero, smul_zero]
      exact fun h ↦ hU a (mem_compl.1 ha) (congrArg Subtype.val h)

/-- The cube complex vanishes in negative degrees. -/
lemma isZero_cubeComplex_X_of_neg {r : ℤ} (hr : r < 0) : IsZero (F.cubeComplex.X r) := by
  rw [IsZero.iff_id_eq_zero]
  ext S
  have := S.2
  omega

/-- The cube complex vanishes in the degrees above the cardinality of the index type. -/
lemma isZero_cubeComplex_X_of_card_lt {r : ℤ} (hr : (Fintype.card ι : ℤ) < r) :
    IsZero (F.cubeComplex.X r) := by
  rw [IsZero.iff_id_eq_zero]
  ext S
  have : (#S.1 : ℤ) ≤ Fintype.card ι := by exact_mod_cast card_le_univ S.1
  have := S.2
  omega

/-- The degree `0` term of the cube complex is the initial vertex `F(∅)`, the only vertex of
height `0`. -/
def cubeComplexXZeroIso : F.cubeComplex.X 0 ≅ F.obj ∅ where
  hom := F.cubeComplexπ ⟨∅, by simp⟩
  inv := F.cubeComplexι ⟨∅, by simp⟩
  hom_inv_id := by
    ext ⟨S, hS⟩
    obtain rfl : S = ∅ := by simpa using hS
    simp
  inv_hom_id := F.cubeComplexι_π_self _

/-- The identification of the degree `0` term with `F(∅)` is the projection onto that vertex. -/
@[simp]
lemma cubeComplexXZeroIso_hom : F.cubeComplexXZeroIso.hom = F.cubeComplexπ ⟨∅, by simp⟩ :=
  (rfl)

/-- The identification of `F(∅)` with the degree `0` term is the inclusion of that vertex. -/
@[simp]
lemma cubeComplexXZeroIso_inv : F.cubeComplexXZeroIso.inv = F.cubeComplexι ⟨∅, by simp⟩ :=
  (rfl)

end Functor

namespace NatTrans

variable {F G H : Finset ι ⥤ C}

/-- The cochain map of cube complexes induced by a map of cubes, acting vertex by vertex
(`NatTrans.ι_cubeComplexMap_f`). -/
def cubeComplexMap (α : F ⟶ G) : F.cubeComplex ⟶ G.cubeComplex where
  f r := F.cubeComplexDesc fun S ↦ α.app S.1 ≫ G.cubeComplexι S
  comm' := by
    rintro r _ rfl
    refine F.cubeComplex_hom_ext fun S ↦ ?_
    rw [Functor.ι_cubeComplexDesc_assoc, Category.assoc, Functor.ι_cubeComplex_d,
      Functor.ι_cubeComplex_d_assoc, Preadditive.comp_sum, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc,
      Functor.ι_cubeComplexDesc, NatTrans.naturality_assoc]

/-- The cochain map induced by `α` restricts to `α` on the vertex `F(S)`. -/
@[reassoc (attr := simp)]
lemma ι_cubeComplexMap_f (α : F ⟶ G) {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι S ≫ (cubeComplexMap α).f r = α.app S.1 ≫ G.cubeComplexι S :=
  F.ι_cubeComplexDesc _ S

/-- The cochain map induced by `α` followed by the projection onto the vertex `G(S)` is the
projection onto `F(S)` followed by `α`. -/
@[reassoc (attr := simp)]
lemma cubeComplexMap_f_π (α : F ⟶ G) {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    (cubeComplexMap α).f r ≫ G.cubeComplexπ S = F.cubeComplexπ S ≫ α.app S.1 := by
  ext T
  by_cases h : T = S
  · subst h
    simp
  · simp [h]

/-- The identification of the degree `0` term with the initial vertex is natural in the cube. -/
@[reassoc]
lemma cubeComplexMap_f_zero_comp_cubeComplexXZeroIso_hom (α : F ⟶ G) :
    (cubeComplexMap α).f 0 ≫ G.cubeComplexXZeroIso.hom =
      F.cubeComplexXZeroIso.hom ≫ α.app ∅ := by
  simp

/-- The identification of the initial vertex with the degree `0` term is natural in the cube. -/
@[reassoc]
lemma cubeComplexXZeroIso_inv_comp_cubeComplexMap_f_zero (α : F ⟶ G) :
    F.cubeComplexXZeroIso.inv ≫ (cubeComplexMap α).f 0 =
      α.app ∅ ≫ G.cubeComplexXZeroIso.inv := by
  simp

@[simp]
lemma cubeComplexMap_id (F : Finset ι ⥤ C) : cubeComplexMap (𝟙 F) = 𝟙 F.cubeComplex := by
  ext r S
  simp

@[simp]
lemma cubeComplexMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    cubeComplexMap (α ≫ β) = cubeComplexMap α ≫ cubeComplexMap β := by
  ext r S
  simp

@[simp]
lemma cubeComplexMap_add (α β : F ⟶ G) :
    cubeComplexMap (α + β) = cubeComplexMap α + cubeComplexMap β := by
  ext r S
  simp [Preadditive.add_comp]

end NatTrans

variable (C ι) in
/-- The cube complex `Functor.cubeComplex` as a functor of the cube. -/
@[expose, simps]
def cubeComplexFunctor : (Finset ι ⥤ C) ⥤ CochainComplex C ℤ where
  obj F := F.cubeComplex
  map α := NatTrans.cubeComplexMap α
  map_id := NatTrans.cubeComplexMap_id
  map_comp := NatTrans.cubeComplexMap_comp

/-- The cube complex is additive in the cube. -/
instance cubeComplexFunctor_additive : (cubeComplexFunctor C ι).Additive where
  map_add := NatTrans.cubeComplexMap_add _ _

end CategoryTheory
