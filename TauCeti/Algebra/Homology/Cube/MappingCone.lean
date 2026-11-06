/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Data.Fintype.WithTopBot
public import Mathlib.Order.Hom.WithTopBot
public import TauCeti.Algebra.Homology.Cube.Basic
public import TauCeti.Algebra.Homology.Cube.Reindex
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone
public import TauCeti.Data.Finset.WithBot

/-!
# The cube complex as a mapping cone

Let `F : Finset (WithBot ι) ⥤ C` be a commutative cube whose index set has a first element `⊥`.
Its vertices split into the `0`-face, the vertices `S` not containing `⊥`, and the `1`-face, the
vertices `insert ⊥ S`; both faces are cubes indexed by `ι`, and the edges in the direction `⊥` form
a map of cubes from the `0`-face to the `1`-face. Since `⊥` lies below every other index, the edges
of the `0`-face keep their signs in the signed totalization of `F`, the edges of the `1`-face change
sign, and the edges in the direction `⊥` carry no sign. Hence the totalization of `F` is, up to a
shift by one, the mapping cone of the cochain map between the totalizations of the two faces.

For the Khovanov complex of a link diagram, with `⊥` a selected crossing put first in the crossing
order, the two faces are the cubes of resolutions of the two smoothings of that crossing and the
map between them is the saddle map. This decomposition underlies the skein long exact sequence and
the cancellation arguments for Reidemeister invariance.

The same holds at any index of a cube `F : Finset (Fin (n + 1)) ⥤ C`, not only at the first one.
The `0`-face at `c` consists of the vertices `S.map c.succAboveEmb` avoiding `c`, the `1`-face of
the vertices `insert c (S.map c.succAboveEmb)`, both indexed by `S : Finset (Fin n)`. Putting `c`
first in the order of the indices reduces this to the case of `⊥`, by the reordering isomorphism
`CategoryTheory.Functor.cubeComplexReindexIso`. The reordering contributes the sign
`(-1) ^ #{i ∈ S | i.castSucc < c}` on the vertex `insert c (S.map c.succAboveEmb)`, the number of
indices of the vertex that the reordering moves `c` past.

## Main definitions

* `CategoryTheory.Functor.cubeFaceZero F`, `CategoryTheory.Functor.cubeFaceOne F`: the `0`-face
  and the `1`-face of a cube indexed by `WithBot ι`, in the direction of `⊥`.
* `CategoryTheory.Functor.cubeFaceMap F`: the map of cubes from the `0`-face to the `1`-face given
  by the edges in the direction of `⊥`.
* `CategoryTheory.Functor.cubeComplexMappingConeIso F`: the isomorphism between the mapping cone
  of the cochain map induced by `Functor.cubeFaceMap F` and the cube complex of `F` shifted by one.
  It is characterised on the vertices of the faces by
  `Functor.inl_v_cubeComplexMappingConeIso_hom_f` and
  `Functor.inr_f_cubeComplexMappingConeIso_hom_f`: a vertex of the `0`-face is sent to the same
  vertex of `F`, and a vertex of the `1`-face to the negative of the same vertex of `F`.
* `CategoryTheory.Functor.cubeFaceZeroAt F c`, `CategoryTheory.Functor.cubeFaceOneAt F c`,
  `CategoryTheory.Functor.cubeFaceMapAt F c`: the two faces of a cube indexed by `Fin (n + 1)` in
  the direction of `c`, and the map of cubes between them given by the edges in that direction.
* `CategoryTheory.Functor.cubeComplexMappingConeIsoAt F c`: the isomorphism between the mapping
  cone of the cochain map induced by `Functor.cubeFaceMapAt F c` and the cube complex of `F`
  shifted by one. A vertex of the `0`-face is sent to the same vertex of `F`
  (`Functor.inl_v_cubeComplexMappingConeIsoAt_hom_f`), and a vertex `S` of the `1`-face to
  `-(-1) ^ #{i ∈ S | i.castSucc < c}` times the same vertex of `F`
  (`Functor.inr_f_cubeComplexMappingConeIsoAt_hom_f`).

## Implementation notes

The two faces split the cube complex degreewise into a short exact sequence whose connecting map
is the face map, so the isomorphism specializes Mathlib's `mappingConeHomOfDegreewiseSplitIso`.
At an arbitrary index `c`, the cube is first read through the reordering
`finSuccEquiv' c : Fin (n + 1) ≃ WithBot (Fin n)`, which sends `c` to `⊥` and `c.succAbove i` to
`i`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), 337-370.
-/

public section

noncomputable section

attribute [local instance] CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts

open CategoryTheory Limits Finset CochainComplex

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Functor

section Faces

variable {ι : Type w} (F : Finset (WithBot ι) ⥤ C)

/-- The `0`-face of a cube indexed by `WithBot ι`: the restriction to the vertices `S` not
containing the first index `⊥`, as a cube indexed by `ι`. -/
abbrev cubeFaceZero : Finset ι ⥤ C :=
  (show Monotone (Finset.map Function.Embedding.coeWithBot) from
    fun _ _ ↦ map_subset_map.2).functor ⋙ F

/-- The `1`-face of a cube indexed by `WithBot ι`: the restriction to the vertices
`WithBot.insertBot S` containing the first index `⊥`, as a cube indexed by `ι`. -/
abbrev cubeFaceOne : Finset ι ⥤ C :=
  WithBot.insertBot.monotone.functor ⋙ F

/-- The edge maps of a cube indexed by `WithBot ι` in the direction of the first index `⊥`, as a
map of cubes from the `0`-face to the `1`-face. -/
def cubeFaceMap : F.cubeFaceZero ⟶ F.cubeFaceOne where
  app S := F.map (homOfLE (WithBot.map_coeWithBot_subset_insertBot S))
  naturality _ _ _ := by
    simp only [comp_map, ← F.map_comp]
    -- Morphisms in the preorder category of subsets are proofs of inclusion.
    rfl

/-- The component of `Functor.cubeFaceMap F` at a vertex `S` is the edge map of `F` from `S` to
`WithBot.insertBot S`. -/
@[simp]
lemma cubeFaceMap_app (S : Finset ι) :
    F.cubeFaceMap.app S = F.map (homOfLE (WithBot.map_coeWithBot_subset_insertBot S)) :=
  (rfl)

end Faces

section FacesAt

variable {n : ℕ} (F : Finset (Fin (n + 1)) ⥤ C) (c : Fin (n + 1))

/-- The `0`-face of a cube indexed by `Fin (n + 1)` in the direction of the index `c`: the
restriction to the vertices `S.map c.succAboveEmb` not containing `c`, as a cube indexed by
`Fin n`. -/
abbrev cubeFaceZeroAt : Finset (Fin n) ⥤ C :=
  (show Monotone (Finset.map c.succAboveEmb) from fun _ _ ↦ map_subset_map.2).functor ⋙ F

/-- The `1`-face of a cube indexed by `Fin (n + 1)` in the direction of the index `c`: the
restriction to the vertices `insert c (S.map c.succAboveEmb)` containing `c`, as a cube indexed by
`Fin n`. -/
abbrev cubeFaceOneAt : Finset (Fin n) ⥤ C :=
  (show Monotone fun S : Finset (Fin n) ↦ insert c (S.map c.succAboveEmb) from
    fun _ _ h ↦ insert_subset_insert c (map_subset_map.2 h)).functor ⋙ F

/-- The edge maps of a cube indexed by `Fin (n + 1)` in the direction of the index `c`, as a map
of cubes from the `0`-face at `c` to the `1`-face at `c`. -/
def cubeFaceMapAt : F.cubeFaceZeroAt c ⟶ F.cubeFaceOneAt c where
  app S := F.map (homOfLE (subset_insert c _))
  naturality _ _ _ := by
    simp only [comp_map, ← F.map_comp]
    rfl

/-- The component of `Functor.cubeFaceMapAt F c` at a vertex `S` is the edge map of `F` from
`S.map c.succAboveEmb` to `insert c (S.map c.succAboveEmb)`. -/
@[simp]
lemma cubeFaceMapAt_app (S : Finset (Fin n)) :
    (F.cubeFaceMapAt c).app S = F.map (homOfLE (subset_insert c _)) :=
  (rfl)

end FacesAt

variable [Preadditive C] [HasFiniteBiproducts C]

section Congr

variable {κ : Type w} [Fintype κ] [LinearOrder κ] (G : Finset κ ⥤ C)

/-- An edge map followed by the inclusion of its target vertex only depends on the target vertex
up to equality. -/
private lemma map_homOfLE_comp_cubeComplexι_congr {r : ℤ} {T U U' : Finset κ} (e : U = U')
    (h : T ⊆ U) (hU : (#U : ℤ) = r) :
    G.map (homOfLE h) ≫ G.cubeComplexι ⟨U, hU⟩ =
      G.map (homOfLE (e ▸ h)) ≫ G.cubeComplexι ⟨U', e ▸ hU⟩ := by
  subst e
  rfl

end Congr

section Bot

variable {ι : Type w} [Fintype ι] [LinearOrder ι] (F : Finset (WithBot ι) ⥤ C)

/-! ### The vertices of the two faces -/

/-- The inclusion of the totalization of the `0`-face into the cube complex. -/
private def faceZeroι (r : ℤ) : F.cubeFaceZero.cubeComplex.X r ⟶ F.cubeComplex.X r :=
  F.cubeFaceZero.cubeComplexDesc fun S ↦
    F.cubeComplexι ⟨S.1.map Function.Embedding.coeWithBot, by rw [card_map, S.2]⟩

/-- The projection of the cube complex onto the totalization of the `0`-face. -/
private def faceZeroπ (r : ℤ) : F.cubeComplex.X r ⟶ F.cubeFaceZero.cubeComplex.X r :=
  F.cubeFaceZero.cubeComplexLift fun S ↦
    F.cubeComplexπ ⟨S.1.map Function.Embedding.coeWithBot, by rw [card_map, S.2]⟩

/-- The inclusion of the totalization of the `1`-face into the cube complex, raising the degree by
one. -/
private def faceOneι (s r : ℤ) (h : s + 1 = r) :
    F.cubeFaceOne.cubeComplex.X s ⟶ F.cubeComplex.X r :=
  F.cubeFaceOne.cubeComplexDesc fun S ↦
    F.cubeComplexι ⟨WithBot.insertBot S.1, by simp [S.2, h]⟩

/-- The projection of the cube complex onto the totalization of the `1`-face, lowering the degree
by one. -/
private def faceOneπ (s r : ℤ) (h : s + 1 = r) :
    F.cubeComplex.X r ⟶ F.cubeFaceOne.cubeComplex.X s :=
  F.cubeFaceOne.cubeComplexLift fun S ↦
    F.cubeComplexπ ⟨WithBot.insertBot S.1, by simp [S.2, h]⟩

@[reassoc (attr := simp)]
private lemma cubeComplexι_faceZeroι {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeFaceZero.cubeComplexι S ≫ F.faceZeroι r =
      F.cubeComplexι ⟨S.1.map Function.Embedding.coeWithBot, by rw [card_map, S.2]⟩ :=
  F.cubeFaceZero.ι_cubeComplexDesc _ S

@[reassoc (attr := simp)]
private lemma cubeComplexι_faceOneι {s r : ℤ} (h : s + 1 = r)
    (S : {S : Finset ι // (#S : ℤ) = s}) :
    F.cubeFaceOne.cubeComplexι S ≫ F.faceOneι s r h =
      F.cubeComplexι ⟨WithBot.insertBot S.1, by simp [S.2, h]⟩ :=
  F.cubeFaceOne.ι_cubeComplexDesc _ S

@[reassoc (attr := simp)]
private lemma cubeComplexι_faceZeroπ {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι ⟨S.1.map Function.Embedding.coeWithBot, by rw [card_map, S.2]⟩ ≫
      F.faceZeroπ r = F.cubeFaceZero.cubeComplexι S := by
  ext T
  simp only [faceZeroπ, Category.assoc, cubeComplexLift_π]
  by_cases h : S = T
  · subst h
    simp
  · rw [cubeComplexι_π_of_ne _ fun e ↦ h (Subtype.ext
      (map_inj.1 (Subtype.ext_iff.1 e))),
      cubeComplexι_π_of_ne _ h]

@[reassoc (attr := simp)]
private lemma cubeComplexι_faceOneπ {s r : ℤ} (h : s + 1 = r)
    (S : {S : Finset ι // (#S : ℤ) = s}) :
    F.cubeComplexι ⟨WithBot.insertBot S.1, by simp [S.2, h]⟩ ≫ F.faceOneπ s r h =
      F.cubeFaceOne.cubeComplexι S := by
  ext T
  simp only [faceOneπ, Category.assoc, cubeComplexLift_π]
  by_cases hST : S = T
  · subst hST
    simp
  · rw [cubeComplexι_π_of_ne _ fun e ↦ hST (Subtype.ext
      (WithBot.insertBot.injective (Subtype.ext_iff.1 e))),
      cubeComplexι_π_of_ne _ hST]

@[reassoc]
private lemma cubeComplexι_insertBot_faceZeroπ {s r : ℤ} (h : s + 1 = r)
    (S : {S : Finset ι // (#S : ℤ) = s}) :
    F.cubeComplexι ⟨WithBot.insertBot S.1, by simp [S.2, h]⟩ ≫ F.faceZeroπ r = 0 := by
  ext T
  simp only [faceZeroπ, Category.assoc, cubeComplexLift_π, zero_comp]
  exact cubeComplexι_π_of_ne _ fun e ↦
    map_coeWithBot_ne_insertBot _ _ (Subtype.ext_iff.1 e).symm

@[reassoc (attr := simp)]
private lemma cubeComplexι_map_faceOneπ {s r : ℤ} (h : s + 1 = r)
    (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι ⟨S.1.map Function.Embedding.coeWithBot, by rw [card_map, S.2]⟩ ≫
      F.faceOneπ s r h = 0 := by
  ext T
  simp only [faceOneπ, Category.assoc, cubeComplexLift_π, zero_comp]
  exact cubeComplexι_π_of_ne _ fun e ↦ map_coeWithBot_ne_insertBot _ _ (Subtype.ext_iff.1 e)

@[reassoc (attr := simp)]
private lemma faceZeroι_faceZeroπ (r : ℤ) : F.faceZeroι r ≫ F.faceZeroπ r = 𝟙 _ := by
  refine cubeComplex_hom_ext _ fun S ↦ ?_
  simp

@[reassoc (attr := simp)]
private lemma faceOneι_faceOneπ {s r : ℤ} (h : s + 1 = r) :
    F.faceOneι s r h ≫ F.faceOneπ s r h = 𝟙 _ := by
  refine cubeComplex_hom_ext _ fun S ↦ ?_
  simp

@[reassoc (attr := simp)]
private lemma faceZeroι_faceOneπ {s r : ℤ} (h : s + 1 = r) :
    F.faceZeroι r ≫ F.faceOneπ s r h = 0 := by
  refine cubeComplex_hom_ext _ fun S ↦ ?_
  simp

@[reassoc (attr := simp)]
private lemma faceOneι_faceZeroπ {s r : ℤ} (h : s + 1 = r) :
    F.faceOneι s r h ≫ F.faceZeroπ r = 0 := by
  refine cubeComplex_hom_ext _ fun S ↦ ?_
  rw [cubeComplexι_faceOneι_assoc, F.cubeComplexι_insertBot_faceZeroπ h, comp_zero]

/-- The two faces decompose every term of the cube complex as a biproduct. -/
private lemma faceZeroπ_faceZeroι_add_faceOneπ_faceOneι {s r : ℤ} (h : s + 1 = r) :
    F.faceZeroπ r ≫ F.faceZeroι r + F.faceOneπ s r h ≫ F.faceOneι s r h = 𝟙 _ := by
  refine cubeComplex_hom_ext _ fun ⟨T, hT⟩ ↦ ?_
  rw [Preadditive.comp_add, Category.comp_id]
  obtain ⟨S, rfl⟩ | ⟨S, rfl⟩ := exists_eq_map_coeWithBot_or_exists_eq_insertBot T
  · have hS : (#S : ℤ) = r := by rwa [card_map] at hT
    rw [F.cubeComplexι_faceZeroπ_assoc ⟨S, hS⟩, F.cubeComplexι_map_faceOneπ_assoc h ⟨S, hS⟩,
      zero_comp, add_zero, cubeComplexι_faceZeroι]
  · have hS : (#S : ℤ) = s := by
      rw [WithBot.card_insertBot, Nat.cast_succ] at hT
      omega
    rw [F.cubeComplexι_insertBot_faceZeroπ_assoc h ⟨S, hS⟩, F.cubeComplexι_faceOneπ_assoc h ⟨S, hS⟩,
      zero_comp, zero_add, cubeComplexι_faceOneι]

/-! ### The differential on the two faces -/

/-- On the `0`-face, the cube differential is the differential of the `0`-face followed by the
edges in the direction of `⊥`. -/
@[reassoc]
private lemma faceZeroι_d (r : ℤ) :
    F.faceZeroι r ≫ F.cubeComplex.d r (r + 1) =
      F.cubeFaceZero.cubeComplex.d r (r + 1) ≫ F.faceZeroι (r + 1) +
        (NatTrans.cubeComplexMap F.cubeFaceMap).f r ≫ F.faceOneι r (r + 1) rfl := by
  refine cubeComplex_hom_ext _ fun S ↦ ?_
  rw [cubeComplexι_faceZeroι_assoc, ι_cubeComplex_d, Preadditive.comp_add,
    NatTrans.ι_cubeComplexMap_f_assoc, ι_cubeComplex_d_assoc, Preadditive.sum_comp,
    cubeComplexι_faceOneι]
  -- The indices outside the vertex `S` of the `0`-face are `⊥` and the indices outside `S`.
  rw [← (optionComplEquivComplMapCoeWithBot S.1).sum_comp, Fintype.sum_option]
  refine (congrArg₂ (· + ·) ?_ ?_).trans (add_comm _ _)
  · simpa using F.map_homOfLE_comp_cubeComplexι_congr
      (by rw [coe_optionComplEquivComplMapCoeWithBot_none, WithBot.insertBot_eq_insert]) _ _
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [coe_optionComplEquivComplMapCoeWithBot_some, Preadditive.zsmul_comp,
      Category.assoc, cubeComplexι_faceZeroι]
    refine congrArg₂ (· • ·) (congrArg _ (card_filter_lt_coe_map_coeWithBot _ _)) ?_
    exact F.map_homOfLE_comp_cubeComplexι_congr
      (by rw [coe_optionComplEquivComplMapCoeWithBot_some]; exact (map_insert _ _ _).symm) _ _

/-- On the `1`-face, the cube differential is the negative of the differential of the `1`-face. -/
@[reassoc]
private lemma faceOneι_d {s r s' r' : ℤ} (h : s + 1 = r) (hs : s + 1 = s') (hr : r + 1 = r') :
    F.faceOneι s r h ≫ F.cubeComplex.d r r' =
      -(F.cubeFaceOne.cubeComplex.d s s' ≫ F.faceOneι s' r' (by omega)) := by
  subst hs hr
  refine cubeComplex_hom_ext _ fun S ↦ ?_
  rw [cubeComplexι_faceOneι_assoc, ι_cubeComplex_d, Preadditive.comp_neg, ι_cubeComplex_d_assoc,
    Preadditive.sum_comp, ← Finset.sum_neg_distrib]
  -- The indices outside the vertex `WithBot.insertBot S` of the `1`-face are the indices outside
  -- `S`.
  rw [← (complEquivComplInsertBot S.1).sum_comp]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [coe_complEquivComplInsertBot, card_filter_lt_coe_insertBot, pow_succ, mul_neg_one,
    neg_smul, Preadditive.zsmul_comp, Category.assoc, cubeComplexι_faceOneι]
  refine congrArg (fun x ↦ -(_ • x)) ?_
  refine F.map_homOfLE_comp_cubeComplexι_congr ?_ _ _
  rw [coe_complEquivComplInsertBot, WithBot.insertBot_eq_insert, WithBot.insertBot_eq_insert,
    map_insert, insert_comm]
  -- `Function.Embedding.coeWithBot a` is the coercion `↑a`.
  rfl

/-! ### The mapping cone -/

/-- The degreewise split short exact sequence formed by the `1`-face shifted down by one, the cube
complex, and the `0`-face. -/
private abbrev faceShortComplex : ShortComplex (CochainComplex C ℤ) where
  X₁ := F.cubeFaceOne.cubeComplex⟦(-1 : ℤ)⟧
  X₂ := F.cubeComplex
  X₃ := F.cubeFaceZero.cubeComplex
  f :=
    { f p := F.faceOneι (p + -1) p (by omega)
      comm' := by
        rintro p _ rfl
        rw [F.faceOneι_d (s' := p + 1 + -1) _ (by omega) rfl, shiftFunctor_obj_d',
          Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.neg_comp] }
  g :=
    { f := F.faceZeroπ
      comm' := by
        rintro p _ rfl
        rw [← Category.id_comp (F.cubeComplex.d p (p + 1)),
          ← F.faceZeroπ_faceZeroι_add_faceOneπ_faceOneι (s := p + -1) (by omega)]
        simp [F.faceZeroι_d, F.faceOneι_d_assoc _ rfl rfl] }
  zero := by
    ext p : 1
    exact F.faceOneι_faceZeroπ (by omega)

/-- The splitting of `faceShortComplex` in each degree given by the two faces. -/
private def faceSplitting (n : ℤ) :
    (F.faceShortComplex.map (HomologicalComplex.eval C _ n)).Splitting where
  r := F.faceOneπ (n + -1) n (by omega)
  s := F.faceZeroι n
  f_r := F.faceOneι_faceOneπ _
  s_g := F.faceZeroι_faceZeroπ n
  id := (add_comm _ _).trans (F.faceZeroπ_faceZeroι_add_faceOneπ_faceOneι _)

@[reassoc (attr := simp)]
private lemma XIsoOfEq_hom_faceOneι {s s' r : ℤ} (e : s = s') (h' : s' + 1 = r) :
    (F.cubeFaceOne.cubeComplex.XIsoOfEq e).hom ≫ F.faceOneι s' r h' =
      F.faceOneι s r (by omega) := by
  subst e
  simp

@[reassoc (attr := simp)]
private lemma faceOneπ_XIsoOfEq_hom {s s' r : ℤ} (h : s + 1 = r) (e : s = s') :
    F.faceOneπ s r h ≫ (F.cubeFaceOne.cubeComplex.XIsoOfEq e).hom =
      F.faceOneπ s' r (by omega) := by
  subst e
  simp

private lemma faceOneι_faceOneπ_of_eq {s s' r : ℤ} (h : s + 1 = r) (h' : s' + 1 = r) :
    F.faceOneι s r h ≫ F.faceOneπ s' r h' =
      (F.cubeFaceOne.cubeComplex.XIsoOfEq (by omega)).hom := by
  obtain rfl : s = s' := by omega
  simp

/-- The connecting map of `faceShortComplex` is the face map, up to cancelling the shifts. -/
private lemma homOfDegreewiseSplit_faceSplitting :
    homOfDegreewiseSplit _ F.faceSplitting = NatTrans.cubeComplexMap F.cubeFaceMap ≫
      (shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by omega)).inv.app _ := by
  ext n : 1
  rw [homOfDegreewiseSplit_f]
  simp [cocycleOfDegreewiseSplit, faceShortComplex, faceSplitting, F.faceZeroι_d_assoc,
    faceOneι_faceOneπ_of_eq, shiftFunctorCompIsoId, shiftFunctorZero_inv_app_f,
    shiftFunctorAdd'_hom_app_f']

/-- The mapping cone of the face map is the mapping cone of the connecting map of
`faceShortComplex`. -/
private def mappingConeIsoHomOfDegreewiseSplit :
    mappingCone (NatTrans.cubeComplexMap F.cubeFaceMap) ≅
      mappingCone (homOfDegreewiseSplit _ F.faceSplitting) :=
  mappingCone.mapIso (Iso.refl _)
    ((shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by omega)).symm.app _)
    (by rw [F.homOfDegreewiseSplit_faceSplitting]; exact (Category.id_comp _).symm)

/-- **The cube complex is a mapping cone.** For a cube `F` indexed by `WithBot ι`, the mapping
cone of the cochain map from the totalization of the `0`-face to that of the `1`-face induced by
the edges in the direction of `⊥` is isomorphic to the cube complex of `F` shifted by one. A
vertex of the `0`-face is sent to the same vertex of `F`
(`Functor.inl_v_cubeComplexMappingConeIso_hom_f`), and a vertex of the `1`-face to the negative
of the same vertex of `F` (`Functor.inr_f_cubeComplexMappingConeIso_hom_f`). -/
def cubeComplexMappingConeIso :
    mappingCone (NatTrans.cubeComplexMap F.cubeFaceMap) ≅ F.cubeComplex⟦(1 : ℤ)⟧ :=
  F.mappingConeIsoHomOfDegreewiseSplit ≪≫ mappingConeHomOfDegreewiseSplitIso _ F.faceSplitting

/-- The isomorphism `Functor.cubeComplexMappingConeIso` sends a vertex of the `0`-face, placed in
the mapping cone by `mappingCone.inl`, to the same vertex of the cube complex. -/
@[reassoc (attr := simp)]
lemma inl_v_cubeComplexMappingConeIso_hom_f (p : ℤ) (S : {S : Finset ι // (#S : ℤ) = p + 1}) :
    F.cubeFaceZero.cubeComplexι S ≫
        (mappingCone.inl (NatTrans.cubeComplexMap F.cubeFaceMap)).v (p + 1) p (by omega) ≫
          F.cubeComplexMappingConeIso.hom.f p =
      F.cubeComplexι ⟨S.1.map Function.Embedding.coeWithBot, by rw [card_map, S.2]⟩ := by
  simp [cubeComplexMappingConeIso, mappingConeIsoHomOfDegreewiseSplit, mappingCone.map,
    mappingConeHomOfDegreewiseSplitXIso, faceSplitting, shiftFunctorCompIsoId]

/-- The isomorphism `Functor.cubeComplexMappingConeIso` sends a vertex of the `1`-face, placed in
the mapping cone by `mappingCone.inr`, to the negative of the same vertex of the cube complex. -/
@[reassoc (attr := simp)]
lemma inr_f_cubeComplexMappingConeIso_hom_f (p : ℤ) (S : {S : Finset ι // (#S : ℤ) = p}) :
    F.cubeFaceOne.cubeComplexι S ≫
        (mappingCone.inr (NatTrans.cubeComplexMap F.cubeFaceMap)).f p ≫
          F.cubeComplexMappingConeIso.hom.f p =
      -F.cubeComplexι ⟨WithBot.insertBot S.1, by simp [S.2]⟩ := by
  simp [cubeComplexMappingConeIso, mappingConeIsoHomOfDegreewiseSplit, mappingCone.map,
    mappingConeHomOfDegreewiseSplitXIso, faceSplitting, shiftFunctorCompIsoId,
    shiftFunctorZero_inv_app_f, shiftFunctorAdd'_hom_app_f']

/-- The inverse of `Functor.cubeComplexMappingConeIso` sends a vertex of the cube complex not
containing `⊥` to the same vertex of the `0`-face, placed in the mapping cone by
`mappingCone.inl`. -/
@[reassoc (attr := simp)]
lemma cubeComplexι_cubeComplexMappingConeIso_inv_f (p : ℤ)
    (S : {S : Finset ι // (#S : ℤ) = p + 1}) :
    F.cubeComplexι ⟨S.1.map Function.Embedding.coeWithBot, by rw [card_map, S.2]⟩ ≫
        F.cubeComplexMappingConeIso.inv.f p =
      F.cubeFaceZero.cubeComplexι S ≫
        (mappingCone.inl (NatTrans.cubeComplexMap F.cubeFaceMap)).v (p + 1) p (by omega) := by
  simp [cubeComplexMappingConeIso, mappingConeIsoHomOfDegreewiseSplit, mappingCone.map,
    mappingConeHomOfDegreewiseSplitXIso, faceSplitting, shiftFunctorCompIsoId,
    shiftFunctorZero_hom_app_f, shiftFunctorAdd'_inv_app_f']

/-- The inverse of `Functor.cubeComplexMappingConeIso` sends a vertex `WithBot.insertBot S` of the
cube complex to the negative of the vertex `S` of the `1`-face, placed in the mapping cone by
`mappingCone.inr`. -/
@[reassoc (attr := simp)]
lemma cubeComplexι_insertBot_cubeComplexMappingConeIso_inv_f (p : ℤ)
    (S : {S : Finset ι // (#S : ℤ) = p}) :
    F.cubeComplexι ⟨WithBot.insertBot S.1, by simp [S.2]⟩ ≫
        F.cubeComplexMappingConeIso.inv.f p =
      -(F.cubeFaceOne.cubeComplexι S ≫
        (mappingCone.inr (NatTrans.cubeComplexMap F.cubeFaceMap)).f p) := by
  simp [cubeComplexMappingConeIso, mappingConeIsoHomOfDegreewiseSplit, mappingCone.map,
    mappingConeHomOfDegreewiseSplitXIso, faceSplitting, shiftFunctorCompIsoId,
    shiftFunctorZero_hom_app_f, shiftFunctorAdd'_inv_app_f',
    F.cubeComplexι_insertBot_faceZeroπ_assoc (s := p) rfl]

end Bot

/-! ### The mapping cone at an arbitrary index -/

section At

variable {n : ℕ} (F : Finset (Fin (n + 1)) ⥤ C) (c : Fin (n + 1))

/-- The reordering of `Fin (n + 1)` putting `c` first, as `⊥`, and the other indices in order. -/
private def atBotEquiv : Fin (n + 1) ≃ WithBot (Fin n) :=
  finSuccEquiv' c

@[simp]
private lemma atBotEquiv_symm_bot : (atBotEquiv c).symm ⊥ = c :=
  finSuccEquiv'_symm_none c

@[simp]
private lemma atBotEquiv_symm_coe (i : Fin n) : (atBotEquiv c).symm i = c.succAbove i :=
  finSuccEquiv'_symm_some c i

@[simp]
private lemma atBotEquiv_self : atBotEquiv c c = ⊥ :=
  finSuccEquiv'_at c

@[simp]
private lemma atBotEquiv_succAbove (i : Fin n) : atBotEquiv c (c.succAbove i) = i :=
  finSuccEquiv'_succAbove c i

/-- The cube `F` with its indices reordered by `atBotEquiv c`, so that `c` comes first. -/
private abbrev cubeAtBot : Finset (WithBot (Fin n)) ⥤ C :=
  (show Monotone (Finset.map (atBotEquiv c).symm.toEmbedding)
    from fun _ _ ↦ map_subset_map.2).functor ⋙ F

omit [Preadditive C] [HasFiniteBiproducts C] in
/-- Reading `F` through the reordering `atBotEquiv c` is compatible with the edge maps. -/
private lemma isCubeReindexCompatible_cubeAtBot :
    IsCubeReindexCompatible F (F.cubeAtBot c) (atBotEquiv c)
      (fun S ↦ eqToIso (congrArg F.obj (by ext; simp))) := by
  refine isCubeReindexCompatible_iff.2 fun S a _ ↦ ?_
  simp only [eqToIso.hom, comp_map]
  rw [← eqToHom_map F (by ext; simp), ← eqToHom_map F (by ext; simp), ← F.map_comp,
    ← F.map_comp]
  exact congrArg F.map (Subsingleton.elim _ _)

/-- The vertices of the `0`-face of `cubeAtBot` are those of the `0`-face of `F` at `c`. -/
private lemma map_coeWithBot_map_symm (S : Finset (Fin n)) :
    (S.map Function.Embedding.coeWithBot).map (atBotEquiv c).symm.toEmbedding =
      S.map c.succAboveEmb := by
  ext x
  simp only [mem_map, Function.Embedding.coeWithBot_apply, Equiv.coe_toEmbedding,
    exists_exists_and_eq_and, atBotEquiv_symm_coe, Fin.coe_succAboveEmb]

/-- The vertices of the `1`-face of `cubeAtBot` are those of the `1`-face of `F` at `c`. -/
private lemma insertBot_map_symm (S : Finset (Fin n)) :
    (WithBot.insertBot S).map (atBotEquiv c).symm.toEmbedding = insert c (S.map c.succAboveEmb) :=
  by simp [WithBot.insertBot_eq_insert, map_insert, map_coeWithBot_map_symm]

/-- `map_coeWithBot_map_symm`, read in the other direction. -/
private lemma map_succAboveEmb_map (S : Finset (Fin n)) :
    (S.map c.succAboveEmb).map (atBotEquiv c).toEmbedding =
      S.map Function.Embedding.coeWithBot := by
  rw [← map_coeWithBot_map_symm c S, map_map]
  ext
  simp

/-- `insertBot_map_symm`, read in the other direction. -/
private lemma insert_map_succAboveEmb_map (S : Finset (Fin n)) :
    (insert c (S.map c.succAboveEmb)).map (atBotEquiv c).toEmbedding = WithBot.insertBot S := by
  rw [← insertBot_map_symm c S, map_map]
  ext
  simp

/-- `atBotEquiv` has no inversions on a set of indices avoiding `c`. -/
private lemma inversions_map_succAboveEmb (S : Finset (Fin n)) :
    (S.map c.succAboveEmb).inversions (atBotEquiv c) = ∅ := by
  ext ⟨a, b⟩
  simp only [mem_inversions, mem_map, Fin.coe_succAboveEmb, notMem_empty, iff_false, not_and]
  rintro ⟨i, -, rfl⟩ ⟨j, -, rfl⟩ hij
  simpa [Fin.succAbove_lt_succAbove_iff] using hij.le

/-- The inversions of `atBotEquiv` on a set of indices containing `c` are the pairs `(a, c)` with
`a < c`. -/
private lemma card_inversions_insert_map_succAboveEmb (S : Finset (Fin n)) :
    #((insert c (S.map c.succAboveEmb)).inversions (atBotEquiv c)) =
      #{i ∈ S | i.castSucc < c} := by
  rw [card_inversions_insert _ (by simp [Fin.succAbove_ne]), inversions_map_succAboveEmb]
  simp [filter_map, Function.comp_def]

/-- The `0`-face of `cubeAtBot` is the `0`-face of `F` at `c`. -/
private def cubeAtBotFaceZeroIso : (F.cubeAtBot c).cubeFaceZero ≅ F.cubeFaceZeroAt c :=
  NatIso.ofComponents (fun S ↦ eqToIso (congrArg F.obj (map_coeWithBot_map_symm c S))) fun _ ↦ by
    simp only [comp_map, eqToIso.hom]
    rw [← eqToHom_map F (map_coeWithBot_map_symm c _), ← eqToHom_map F
      (map_coeWithBot_map_symm c _), ← F.map_comp, ← F.map_comp]
    exact congrArg F.map (Subsingleton.elim _ _)

/-- The `1`-face of `cubeAtBot` is the `1`-face of `F` at `c`. -/
private def cubeAtBotFaceOneIso : (F.cubeAtBot c).cubeFaceOne ≅ F.cubeFaceOneAt c :=
  NatIso.ofComponents (fun S ↦ eqToIso (congrArg F.obj (insertBot_map_symm c S))) fun _ ↦ by
    simp only [comp_map, eqToIso.hom]
    rw [← eqToHom_map F (insertBot_map_symm c _), ← eqToHom_map F (insertBot_map_symm c _),
      ← F.map_comp, ← F.map_comp]
    exact congrArg F.map (Subsingleton.elim _ _)

/-- The totalization of `cubeAtBotFaceZeroIso`. -/
private def cubeAtBotFaceZeroComplexIso :
    (F.cubeFaceZeroAt c).cubeComplex ≅ (F.cubeAtBot c).cubeFaceZero.cubeComplex :=
  (cubeComplexFunctor C (Fin n)).mapIso (F.cubeAtBotFaceZeroIso c).symm

/-- The totalization of `cubeAtBotFaceOneIso`. -/
private def cubeAtBotFaceOneComplexIso :
    (F.cubeFaceOneAt c).cubeComplex ≅ (F.cubeAtBot c).cubeFaceOne.cubeComplex :=
  (cubeComplexFunctor C (Fin n)).mapIso (F.cubeAtBotFaceOneIso c).symm

/-- The face isomorphisms carry the edges of `F` in the direction of `c` to the edges of
`cubeAtBot` in the direction of `⊥`. -/
private lemma cubeAtBotFace_comm :
    NatTrans.cubeComplexMap (F.cubeFaceMapAt c) ≫ (F.cubeAtBotFaceOneComplexIso c).hom =
      (F.cubeAtBotFaceZeroComplexIso c).hom ≫
        NatTrans.cubeComplexMap (F.cubeAtBot c).cubeFaceMap := by
  simp only [cubeAtBotFaceOneComplexIso, cubeAtBotFaceZeroComplexIso, Functor.mapIso_hom,
    Iso.symm_hom, cubeComplexFunctor_map]
  rw [← NatTrans.cubeComplexMap_comp, ← NatTrans.cubeComplexMap_comp]
  congr 1
  ext S
  simp only [NatTrans.comp_app, cubeFaceMapAt_app, cubeAtBotFaceOneIso, cubeAtBotFaceZeroIso,
    NatIso.ofComponents_inv_app, eqToIso.inv, cubeFaceMap_app, comp_map]
  rw [← eqToHom_map F (insertBot_map_symm c S).symm, ← eqToHom_map F
    (map_coeWithBot_map_symm c S).symm, ← F.map_comp, ← F.map_comp]
  exact congrArg F.map (Subsingleton.elim _ _)

/-- The inverse of the reindexing isomorphism on a vertex `T.map (atBotEquiv c)`, written as any
equal finite set `U`. -/
@[reassoc]
private lemma cubeComplexι_cubeAtBotReindexIso_inv_f {r : ℤ} (T : Finset (Fin (n + 1)))
    {U : Finset (WithBot (Fin n))} (hTU : T.map (atBotEquiv c).toEmbedding = U)
    (hU : (#U : ℤ) = r) :
    (F.cubeAtBot c).cubeComplexι ⟨U, hU⟩ ≫
        (F.cubeComplexReindexIso _ _ (F.isCubeReindexCompatible_cubeAtBot c)).inv.f r =
      (-1 : ℤ) ^ #(T.inversions (atBotEquiv c)) •
        eqToHom (congrArg F.obj (by subst hTU; ext; simp)) ≫
          F.cubeComplexι ⟨T, by rw [← hU, ← hTU, card_map]⟩ := by
  subst hTU
  simpa using F.ι_cubeComplexReindexIso_inv_f _ _ (F.isCubeReindexCompatible_cubeAtBot c)
    ⟨T, by rw [← hU, card_map]⟩

/-- **The cube complex is a mapping cone at any index.** For a cube `F` indexed by `Fin (n + 1)`
and an index `c`, the mapping cone of the cochain map from the totalization of the face
`c ∉ S` to that of the face `c ∈ S` induced by the edges in the direction of `c` is isomorphic
to the cube complex of `F` shifted by one. A vertex of the `0`-face is sent to the same vertex of
`F` (`Functor.inl_v_cubeComplexMappingConeIsoAt_hom_f`), and a vertex `S` of the `1`-face to the
same vertex of `F` with the sign `-(-1) ^ #{i ∈ S | i.castSucc < c}`
(`Functor.inr_f_cubeComplexMappingConeIsoAt_hom_f`). For `c = 0` this sign is `-1`, as in
`Functor.cubeComplexMappingConeIso`. -/
def cubeComplexMappingConeIsoAt :
    mappingCone (NatTrans.cubeComplexMap (F.cubeFaceMapAt c)) ≅ F.cubeComplex⟦(1 : ℤ)⟧ :=
  mappingCone.mapIso _ _ (F.cubeAtBotFace_comm c) ≪≫ (F.cubeAtBot c).cubeComplexMappingConeIso ≪≫
    (shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).mapIso
      (F.cubeComplexReindexIso _ _ (F.isCubeReindexCompatible_cubeAtBot c)).symm

/-- The isomorphism `Functor.cubeComplexMappingConeIsoAt` sends a vertex of the `0`-face, placed
in the mapping cone by `mappingCone.inl`, to the same vertex of the cube complex. -/
@[reassoc (attr := simp)]
lemma inl_v_cubeComplexMappingConeIsoAt_hom_f (p : ℤ)
    (S : {S : Finset (Fin n) // (#S : ℤ) = p + 1}) :
    (F.cubeFaceZeroAt c).cubeComplexι S ≫
        (mappingCone.inl (NatTrans.cubeComplexMap (F.cubeFaceMapAt c))).v (p + 1) p (by omega) ≫
          (F.cubeComplexMappingConeIsoAt c).hom.f p =
      F.cubeComplexι ⟨S.1.map c.succAboveEmb, by rw [card_map, S.2]⟩ := by
  simp only [cubeComplexMappingConeIsoAt, Iso.trans_hom, HomologicalComplex.comp_f,
    mappingCone.mapIso_hom, mappingCone.inl_v_map_f_assoc]
  simp only [cubeAtBotFaceZeroComplexIso, cubeAtBotFaceZeroIso, Functor.mapIso_hom,
    Iso.symm_hom, cubeComplexFunctor_map,
    NatTrans.ι_cubeComplexMap_f_assoc, NatIso.ofComponents_inv_app, eqToIso.inv,
    inl_v_cubeComplexMappingConeIso_hom_f_assoc, shiftFunctor_map_f']
  rw [F.cubeComplexι_cubeAtBotReindexIso_inv_f c (S.1.map c.succAboveEmb)
    (map_succAboveEmb_map c S.1), inversions_map_succAboveEmb]
  simp

/-- The isomorphism `Functor.cubeComplexMappingConeIsoAt` sends a vertex `S` of the `1`-face,
placed in the mapping cone by `mappingCone.inr`, to the vertex `insert c (S.map c.succAboveEmb)`
of the cube complex, with the sign `-(-1) ^ #{i ∈ S | i.castSucc < c}`. -/
@[reassoc (attr := simp)]
lemma inr_f_cubeComplexMappingConeIsoAt_hom_f (p : ℤ) (S : {S : Finset (Fin n) // (#S : ℤ) = p}) :
    (F.cubeFaceOneAt c).cubeComplexι S ≫
        (mappingCone.inr (NatTrans.cubeComplexMap (F.cubeFaceMapAt c))).f p ≫
          (F.cubeComplexMappingConeIsoAt c).hom.f p =
      -((-1 : ℤ) ^ #{i ∈ S.1 | i.castSucc < c} •
        F.cubeComplexι ⟨insert c (S.1.map c.succAboveEmb), by
          simp [card_insert_of_notMem, Fin.succAbove_ne, S.2]⟩) := by
  simp only [cubeComplexMappingConeIsoAt, Iso.trans_hom, HomologicalComplex.comp_f,
    mappingCone.mapIso_hom, mappingCone.inr_f_map_f_assoc]
  simp only [cubeAtBotFaceOneComplexIso, cubeAtBotFaceOneIso, Functor.mapIso_hom,
    Iso.symm_hom, cubeComplexFunctor_map,
    NatTrans.ι_cubeComplexMap_f_assoc, NatIso.ofComponents_inv_app, eqToIso.inv,
    inr_f_cubeComplexMappingConeIso_hom_f_assoc, shiftFunctor_map_f', Preadditive.neg_comp,
    Preadditive.comp_neg]
  rw [F.cubeComplexι_cubeAtBotReindexIso_inv_f c (insert c (S.1.map c.succAboveEmb))
    (insert_map_succAboveEmb_map c S.1), card_inversions_insert_map_succAboveEmb]
  simp

/-- The inverse of `Functor.cubeComplexMappingConeIsoAt` sends a vertex of the cube complex not
containing `c` to the same vertex of the `0`-face, placed in the mapping cone by
`mappingCone.inl`. -/
@[reassoc (attr := simp)]
lemma cubeComplexι_cubeComplexMappingConeIsoAt_inv_f (p : ℤ)
    (S : {S : Finset (Fin n) // (#S : ℤ) = p + 1}) :
    F.cubeComplexι ⟨S.1.map c.succAboveEmb, by rw [card_map, S.2]⟩ ≫
        (F.cubeComplexMappingConeIsoAt c).inv.f p =
      (F.cubeFaceZeroAt c).cubeComplexι S ≫
        (mappingCone.inl (NatTrans.cubeComplexMap (F.cubeFaceMapAt c))).v (p + 1) p (by omega) := by
  rw [← F.inl_v_cubeComplexMappingConeIsoAt_hom_f_assoc, ← HomologicalComplex.comp_f,
    Iso.hom_inv_id, HomologicalComplex.id_f, Category.comp_id]

/-- The inverse of `Functor.cubeComplexMappingConeIsoAt` sends the vertex
`insert c (S.map c.succAboveEmb)` of the cube complex to the vertex `S` of the `1`-face, placed in
the mapping cone by `mappingCone.inr`, with the sign `-(-1) ^ #{i ∈ S | i.castSucc < c}`. -/
@[reassoc (attr := simp)]
lemma cubeComplexι_insert_cubeComplexMappingConeIsoAt_inv_f (p : ℤ)
    (S : {S : Finset (Fin n) // (#S : ℤ) = p}) :
    F.cubeComplexι ⟨insert c (S.1.map c.succAboveEmb), by
          simp [card_insert_of_notMem, Fin.succAbove_ne, S.2]⟩ ≫
        (F.cubeComplexMappingConeIsoAt c).inv.f p =
      -((-1 : ℤ) ^ #{i ∈ S.1 | i.castSucc < c} •
        (F.cubeFaceOneAt c).cubeComplexι S ≫
          (mappingCone.inr (NatTrans.cubeComplexMap (F.cubeFaceMapAt c))).f p) := by
  have h := congrArg (· ≫ (F.cubeComplexMappingConeIsoAt c).inv.f p)
    (F.inr_f_cubeComplexMappingConeIsoAt_hom_f c p S)
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id, Category.comp_id,
    Preadditive.neg_comp, Preadditive.zsmul_comp] at h
  rw [h, smul_neg, neg_neg, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

end At

end Functor

end CategoryTheory
