/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Data.Fintype.WithTopBot
public import Mathlib.Order.Hom.WithTopBot
public import TauCeti.Algebra.Homology.Cube.Basic
import TauCeti.Data.Finset.WithBot

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

variable {ι : Type w} [DecidableEq ι] (F : Finset (WithBot ι) ⥤ C)

/-- The `0`-face of a cube indexed by `WithBot ι`: the restriction to the vertices `S` not
containing the first index `⊥`, as a cube indexed by `ι`. -/
abbrev cubeFaceZero : Finset ι ⥤ C where
  obj S := F.obj (S.map Function.Embedding.coeWithBot)
  map f := F.map (homOfLE (map_subset_map.2 (leOfHom f)))
  -- Morphisms in the preorder category of subsets are proofs of inclusion.
  map_id _ := by
    rw [← F.map_id]
    rfl
  map_comp _ _ := by
    rw [← F.map_comp]
    rfl

/-- The `1`-face of a cube indexed by `WithBot ι`: the restriction to the vertices `insert ⊥ S`
containing the first index `⊥`, as a cube indexed by `ι`. -/
abbrev cubeFaceOne : Finset ι ⥤ C where
  obj S := F.obj (insert ⊥ (S.map Function.Embedding.coeWithBot))
  map f := F.map (homOfLE (insert_subset_insert _ (map_subset_map.2 (leOfHom f))))
  map_id _ := by
    rw [← F.map_id]
    rfl
  map_comp _ _ := by
    rw [← F.map_comp]
    rfl

/-- The edge maps of a cube indexed by `WithBot ι` in the direction of the first index `⊥`, as a
map of cubes from the `0`-face to the `1`-face. -/
def cubeFaceMap : F.cubeFaceZero ⟶ F.cubeFaceOne where
  app S := F.map (homOfLE (subset_insert ⊥ (S.map Function.Embedding.coeWithBot)))
  naturality _ _ _ := by
    simp only [← F.map_comp]
    -- Morphisms in the preorder category of subsets are proofs of inclusion.
    rfl

/-- The component of `Functor.cubeFaceMap F` at a vertex `S` is the edge map of `F` from `S` to
`insert ⊥ S`. -/
@[simp]
lemma cubeFaceMap_app (S : Finset ι) :
    F.cubeFaceMap.app S =
      F.map (homOfLE (subset_insert ⊥ (S.map Function.Embedding.coeWithBot))) :=
  (rfl)

end Faces

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
    F.cubeComplexι ⟨insert ⊥ (S.1.map Function.Embedding.coeWithBot), by
      rw [card_insert_bot_map_coeWithBot, Nat.cast_succ, S.2, h]⟩

/-- The projection of the cube complex onto the totalization of the `1`-face, lowering the degree
by one. -/
private def faceOneπ (s r : ℤ) (h : s + 1 = r) :
    F.cubeComplex.X r ⟶ F.cubeFaceOne.cubeComplex.X s :=
  F.cubeFaceOne.cubeComplexLift fun S ↦
    F.cubeComplexπ ⟨insert ⊥ (S.1.map Function.Embedding.coeWithBot), by
      rw [card_insert_bot_map_coeWithBot, Nat.cast_succ, S.2, h]⟩

@[reassoc (attr := simp)]
private lemma cubeComplexι_faceZeroι {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeFaceZero.cubeComplexι S ≫ F.faceZeroι r =
      F.cubeComplexι ⟨S.1.map Function.Embedding.coeWithBot, by rw [card_map, S.2]⟩ :=
  F.cubeFaceZero.ι_cubeComplexDesc _ S

@[reassoc (attr := simp)]
private lemma cubeComplexι_faceOneι {s r : ℤ} (h : s + 1 = r)
    (S : {S : Finset ι // (#S : ℤ) = s}) :
    F.cubeFaceOne.cubeComplexι S ≫ F.faceOneι s r h =
      F.cubeComplexι ⟨insert ⊥ (S.1.map Function.Embedding.coeWithBot), by
        rw [card_insert_bot_map_coeWithBot, Nat.cast_succ, S.2, h]⟩ :=
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
    F.cubeComplexι ⟨insert ⊥ (S.1.map Function.Embedding.coeWithBot), by
        rw [card_insert_bot_map_coeWithBot, Nat.cast_succ, S.2, h]⟩ ≫ F.faceOneπ s r h =
      F.cubeFaceOne.cubeComplexι S := by
  ext T
  simp only [faceOneπ, Category.assoc, cubeComplexLift_π]
  by_cases hST : S = T
  · subst hST
    simp
  · rw [cubeComplexι_π_of_ne _ fun e ↦ hST (Subtype.ext
      (insert_bot_map_coeWithBot_inj.1 (Subtype.ext_iff.1 e))),
      cubeComplexι_π_of_ne _ hST]

@[reassoc]
private lemma cubeComplexι_insert_faceZeroπ {s r : ℤ} (h : s + 1 = r)
    (S : {S : Finset ι // (#S : ℤ) = s}) :
    F.cubeComplexι ⟨insert ⊥ (S.1.map Function.Embedding.coeWithBot), by
        rw [card_insert_bot_map_coeWithBot, Nat.cast_succ, S.2, h]⟩ ≫ F.faceZeroπ r = 0 := by
  ext T
  simp only [faceZeroπ, Category.assoc, cubeComplexLift_π, zero_comp]
  exact cubeComplexι_π_of_ne _ fun e ↦
    map_coeWithBot_ne_insert_bot _ _ (Subtype.ext_iff.1 e).symm

@[reassoc (attr := simp)]
private lemma cubeComplexι_map_faceOneπ {s r : ℤ} (h : s + 1 = r)
    (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι ⟨S.1.map Function.Embedding.coeWithBot, by rw [card_map, S.2]⟩ ≫
      F.faceOneπ s r h = 0 := by
  ext T
  simp only [faceOneπ, Category.assoc, cubeComplexLift_π, zero_comp]
  exact cubeComplexι_π_of_ne _ fun e ↦ map_coeWithBot_ne_insert_bot _ _ (Subtype.ext_iff.1 e)

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
  rw [cubeComplexι_faceOneι_assoc, F.cubeComplexι_insert_faceZeroπ h, comp_zero]

/-- The two faces decompose every term of the cube complex as a biproduct. -/
private lemma faceZeroπ_faceZeroι_add_faceOneπ_faceOneι {s r : ℤ} (h : s + 1 = r) :
    F.faceZeroπ r ≫ F.faceZeroι r + F.faceOneπ s r h ≫ F.faceOneι s r h = 𝟙 _ := by
  refine cubeComplex_hom_ext _ fun ⟨T, hT⟩ ↦ ?_
  rw [Preadditive.comp_add, Category.comp_id]
  obtain ⟨S, rfl⟩ | ⟨S, rfl⟩ := exists_eq_map_coeWithBot_or_exists_eq_insert_bot T
  · have hS : (#S : ℤ) = r := by rwa [card_map] at hT
    rw [F.cubeComplexι_faceZeroπ_assoc ⟨S, hS⟩, F.cubeComplexι_map_faceOneπ_assoc h ⟨S, hS⟩,
      zero_comp, add_zero, cubeComplexι_faceZeroι]
  · have hS : (#S : ℤ) = s := by
      rw [card_insert_bot_map_coeWithBot, Nat.cast_succ] at hT
      omega
    rw [F.cubeComplexι_insert_faceZeroπ_assoc h ⟨S, hS⟩, F.cubeComplexι_faceOneπ_assoc h ⟨S, hS⟩,
      zero_comp, zero_add, cubeComplexι_faceOneι]

/-! ### The differential on the two faces -/

/-- On the `0`-face, the cube differential is the differential of the `0`-face followed by the
edges in the direction of `⊥`. -/
private lemma faceZeroι_d (r : ℤ) :
    F.faceZeroι r ≫ F.cubeComplex.d r (r + 1) =
      F.cubeFaceZero.cubeComplex.d r (r + 1) ≫ F.faceZeroι (r + 1) +
        (NatTrans.cubeComplexMap F.cubeFaceMap).f r ≫ F.faceOneι r (r + 1) rfl := by
  refine cubeComplex_hom_ext _ fun S ↦ ?_
  rw [cubeComplexι_faceZeroι_assoc, ι_cubeComplex_d, Preadditive.comp_add,
    NatTrans.ι_cubeComplexMap_f_assoc, ι_cubeComplex_d_assoc, Preadditive.sum_comp,
    cubeComplexι_faceOneι]
  -- The indices outside the vertex `S` of the `0`-face are `⊥` and the indices outside `S`.
  let j : Option ↥(S.1ᶜ) → ↥((S.1.map Function.Embedding.coeWithBot)ᶜ) :=
    fun o ↦ o.elim ⟨⊥, by simp⟩ fun a ↦ ⟨a.1, by simpa using mem_compl.1 a.2⟩
  have hj : Function.Bijective j := by
    refine ⟨fun o o' e ↦ ?_, fun a ↦ ?_⟩
    · replace e := congrArg Subtype.val e
      rcases o with _ | ⟨a, ha⟩ <;> rcases o' with _ | ⟨a', ha'⟩
      · rfl
      · exact absurd e WithBot.bot_ne_coe
      · exact absurd e WithBot.coe_ne_bot
      · exact congrArg some (Subtype.ext (WithBot.coe_injective e))
    · obtain ⟨a, ha⟩ := a
      induction a using WithBot.recBotCoe with
      | bot => exact ⟨none, rfl⟩
      | coe a => exact ⟨some ⟨a, by simpa using ha⟩, rfl⟩
  refine (Fintype.sum_bijective j hj _ _ fun _ ↦ rfl).symm.trans ?_
  rw [Fintype.sum_option]
  refine (congrArg₂ (· + ·) ?_ ?_).trans (add_comm _ _)
  · simp [j]
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [j, Option.elim_some, Preadditive.zsmul_comp, Category.assoc,
      cubeComplexι_faceZeroι]
    refine congrArg₂ (· • ·) (congrArg _ (card_filter_lt_coe_map_coeWithBot _ _)) ?_
    exact F.map_homOfLE_comp_cubeComplexι_congr (map_insert _ _ _).symm _ _

/-- On the `1`-face, the cube differential is the negative of the differential of the `1`-face. -/
private lemma faceOneι_d {s r : ℤ} (h : s + 1 = r) :
    F.faceOneι s r h ≫ F.cubeComplex.d r (r + 1) =
      -(F.cubeFaceOne.cubeComplex.d s (s + 1) ≫ F.faceOneι (s + 1) (r + 1) (by omega)) := by
  refine cubeComplex_hom_ext _ fun S ↦ ?_
  rw [cubeComplexι_faceOneι_assoc, ι_cubeComplex_d, Preadditive.comp_neg, ι_cubeComplex_d_assoc,
    Preadditive.sum_comp, ← Finset.sum_neg_distrib]
  -- The indices outside the vertex `insert ⊥ S` of the `1`-face are the indices outside `S`.
  let j : ↥(S.1ᶜ) → ↥((insert ⊥ (S.1.map Function.Embedding.coeWithBot))ᶜ) :=
    fun a ↦ ⟨a.1, by simpa using mem_compl.1 a.2⟩
  have hj : Function.Bijective j := by
    refine ⟨fun a a' e ↦ Subtype.ext (by simpa [j] using e), fun a ↦ ?_⟩
    obtain ⟨a, ha⟩ := a
    induction a using WithBot.recBotCoe with
    | bot => simp at ha
    | coe a => exact ⟨⟨a, by simpa using ha⟩, rfl⟩
  refine (Fintype.sum_bijective j hj _ _ fun _ ↦ rfl).symm.trans ?_
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [j, card_filter_lt_coe_insert_bot_map_coeWithBot, pow_succ, mul_neg_one, neg_smul,
    Preadditive.zsmul_comp, Category.assoc, cubeComplexι_faceOneι]
  refine congrArg (fun x ↦ -(_ • x)) ?_
  refine F.map_homOfLE_comp_cubeComplexι_congr ?_ _ _
  rw [map_insert, insert_comm]
  -- `Function.Embedding.coeWithBot a` is the coercion `↑a`.
  rfl

/-! ### The mapping cone -/

/-- The term in degree `p` of the mapping cone of the face map is the term in degree `p + 1` of
the cube complex. -/
private def mappingConeXIso (p : ℤ) :
    (mappingCone (NatTrans.cubeComplexMap F.cubeFaceMap)).X p ≅ F.cubeComplex.X (p + 1) where
  hom := (mappingCone.fst (NatTrans.cubeComplexMap F.cubeFaceMap)).1.v p (p + 1) rfl ≫
      F.faceZeroι (p + 1) -
    (mappingCone.snd (NatTrans.cubeComplexMap F.cubeFaceMap)).v p p (add_zero p) ≫
      F.faceOneι p (p + 1) rfl
  inv := F.faceZeroπ (p + 1) ≫
      (mappingCone.inl (NatTrans.cubeComplexMap F.cubeFaceMap)).v (p + 1) p (by omega) -
    F.faceOneπ p (p + 1) rfl ≫ (mappingCone.inr (NatTrans.cubeComplexMap F.cubeFaceMap)).f p
  hom_inv_id := by
    refine mappingCone.ext_from _ (p + 1) p rfl ?_ ?_ <;> simp
  inv_hom_id := by
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
      mappingCone.inl_v_fst_v_assoc, mappingCone.inl_v_snd_v_assoc, mappingCone.inr_f_fst_v_assoc,
      mappingCone.inr_f_snd_v_assoc, zero_comp, comp_zero, sub_zero, zero_sub, sub_neg_eq_add]
    exact F.faceZeroπ_faceZeroι_add_faceOneπ_faceOneι rfl

/-- **The cube complex is a mapping cone.** For a cube `F` indexed by `WithBot ι`, the mapping
cone of the cochain map from the totalization of the `0`-face to that of the `1`-face induced by
the edges in the direction of `⊥` is isomorphic to the cube complex of `F` shifted by one. A
vertex of the `0`-face is sent to the same vertex of `F`
(`Functor.inl_v_cubeComplexMappingConeIso_hom_f`), and a vertex of the `1`-face to the negative
of the same vertex of `F` (`Functor.inr_f_cubeComplexMappingConeIso_hom_f`). -/
def cubeComplexMappingConeIso :
    mappingCone (NatTrans.cubeComplexMap F.cubeFaceMap) ≅ F.cubeComplex⟦(1 : ℤ)⟧ :=
  HomologicalComplex.Hom.isoOfComponents F.mappingConeXIso <| by
    rintro p _ rfl
    refine mappingCone.ext_from _ (p + 1) p rfl ?_ ?_
    · simp only [mappingConeXIso, shiftFunctor_obj_d', Int.negOnePow_one, Units.neg_smul,
        one_smul, Preadditive.comp_neg, mappingCone.inl_v_fst_v_assoc,
        mappingCone.inl_v_snd_v_assoc, zero_comp, sub_zero, F.faceZeroι_d,
        mappingCone.inl_v_d_assoc _ (p + 1) p (p + 1 + 1) (by omega) (by omega),
        Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
        mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc, comp_zero, zero_sub]
      abel
    · simp only [mappingConeXIso, shiftFunctor_obj_d', Int.negOnePow_one, Units.neg_smul,
        one_smul, Preadditive.comp_neg, Preadditive.comp_sub_assoc, mappingCone.inr_f_fst_v_assoc,
        mappingCone.inr_f_snd_v_assoc, zero_comp, zero_sub, Preadditive.neg_comp,
        neg_neg, F.faceOneι_d rfl, mappingCone.inr_f_d_assoc, Preadditive.comp_sub, comp_zero]

/-- The isomorphism `Functor.cubeComplexMappingConeIso` sends a vertex of the `0`-face, placed in
the mapping cone by `mappingCone.inl`, to the same vertex of the cube complex. -/
@[reassoc (attr := simp)]
lemma inl_v_cubeComplexMappingConeIso_hom_f (p : ℤ) (S : {S : Finset ι // (#S : ℤ) = p + 1}) :
    F.cubeFaceZero.cubeComplexι S ≫
        (mappingCone.inl (NatTrans.cubeComplexMap F.cubeFaceMap)).v (p + 1) p (by omega) ≫
          F.cubeComplexMappingConeIso.hom.f p =
      F.cubeComplexι ⟨S.1.map Function.Embedding.coeWithBot, by rw [card_map, S.2]⟩ := by
  simp [cubeComplexMappingConeIso, mappingConeXIso]

/-- The isomorphism `Functor.cubeComplexMappingConeIso` sends a vertex of the `1`-face, placed in
the mapping cone by `mappingCone.inr`, to the negative of the same vertex of the cube complex. -/
@[reassoc (attr := simp)]
lemma inr_f_cubeComplexMappingConeIso_hom_f (p : ℤ) (S : {S : Finset ι // (#S : ℤ) = p}) :
    F.cubeFaceOne.cubeComplexι S ≫
        (mappingCone.inr (NatTrans.cubeComplexMap F.cubeFaceMap)).f p ≫
          F.cubeComplexMappingConeIso.hom.f p =
      -F.cubeComplexι ⟨insert ⊥ (S.1.map Function.Embedding.coeWithBot), by
        rw [card_insert_bot_map_coeWithBot, Nat.cast_succ, S.2]⟩ := by
  simp [cubeComplexMappingConeIso, mappingConeXIso]

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
  simp [cubeComplexMappingConeIso, mappingConeXIso]

/-- The inverse of `Functor.cubeComplexMappingConeIso` sends a vertex `insert ⊥ S` of the cube
complex to the negative of the vertex `S` of the `1`-face, placed in the mapping cone by
`mappingCone.inr`. -/
@[reassoc (attr := simp)]
lemma cubeComplexι_insert_cubeComplexMappingConeIso_inv_f (p : ℤ)
    (S : {S : Finset ι // (#S : ℤ) = p}) :
    F.cubeComplexι ⟨insert ⊥ (S.1.map Function.Embedding.coeWithBot), by
        rw [card_insert_bot_map_coeWithBot, Nat.cast_succ, S.2]⟩ ≫
        F.cubeComplexMappingConeIso.inv.f p =
      -(F.cubeFaceOne.cubeComplexι S ≫
        (mappingCone.inr (NatTrans.cubeComplexMap F.cubeFaceMap)).f p) := by
  simp [cubeComplexMappingConeIso, mappingConeXIso,
    F.cubeComplexι_insert_faceZeroπ_assoc (s := p) rfl]

end Functor

end CategoryTheory
