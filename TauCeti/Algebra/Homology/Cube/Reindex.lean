/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Cube.Basic
public import TauCeti.Data.Finset.Inversions

/-!
# Reordering the indices of a cube complex

The signed totalization `CategoryTheory.Functor.cubeComplex` of a commutative cube
`F : Finset ι ⥤ C` depends on the chosen linear order of `ι` through its edge signs
`(-1) ^ #{b ∈ S | b < a}`. This file shows that the totalizations for two orders are isomorphic
cochain complexes, the isomorphism acting on each vertex `S` by the sign of the permutation of `S`
comparing the two orders.

More generally, let `e : ι ≃ κ` be an equivalence of finite linearly ordered types, not
necessarily monotone, and let `G : Finset κ ⥤ C` be a cube with vertex isomorphisms
`α S : F(S) ≅ G(e(S))` commuting with the edge maps. Then
`CategoryTheory.Functor.cubeComplexReindexIso F e α hα : F.cubeComplex ≅ G.cubeComplex` acts on
the vertex `F(S)` by `(-1) ^ #(S.inversions e) • α S`, where `S.inversions e` is the finite set of
pairs `a < b` in `S` with `e b < e a`. Taking for `κ` a type synonym of `ι` with a second linear
order and for `e` the identity map, or for `G` the cube `F` read through a permutation of its
indices, gives the reordering isomorphism. In a cube of resolutions of a link diagram, `ι` is the
ordered set of crossings and this is the change of crossing order.

The isomorphism is the identity for the identity reindexing
(`Functor.cubeComplexReindexIso_refl`) and is compatible with composition
(`Functor.cubeComplexReindexIso_trans`), because inversion signs are multiplicative.

## Main definitions

* `CategoryTheory.Functor.cubeComplexReindexIso F e α hα`: the cochain isomorphism between the
  cube complexes of two cubes related by a reindexing `e : ι ≃ κ`, characterised on vertices by
  `Functor.ι_cubeComplexReindexIso_hom_f` and `Functor.ι_cubeComplexReindexIso_inv_f`.

## Main results

* `Functor.cubeComplexReindexIso_refl`: the reindexing isomorphism along the identity is the
  identity.
* `Functor.cubeComplexReindexIso_trans`: the reindexing isomorphism along a composite is the
  composite of the reindexing isomorphisms.

## References

* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §2.
-/

public section

noncomputable section

open CategoryTheory Limits Finset

universe w w' w'' v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {ι : Type w} [Fintype ι] [LinearOrder ι] {κ : Type w'} [Fintype κ] [LinearOrder κ]
  {μ : Type w''} [Fintype μ] [LinearOrder μ]

/-- An edge map into a vertex followed by the inclusion of that vertex depends only on the
vertex, not on the way it is written. -/
private lemma map_comp_cubeComplexι_congr (G : Finset κ ⥤ C) {r : ℤ} {S T T' : Finset κ}
    (h : S ⊆ T) (h' : S ⊆ T') (hTT' : T = T') (hT : (#T : ℤ) = r) (hT' : (#T' : ℤ) = r) :
    G.map (homOfLE h) ≫ G.cubeComplexι ⟨T, hT⟩ =
      G.map (homOfLE h') ≫ G.cubeComplexι ⟨T', hT'⟩ := by
  subst hTT'
  rfl

variable (F : Finset ι ⥤ C) {G : Finset κ ⥤ C} (e : ι ≃ κ)
  (α : ∀ S : Finset ι, F.obj S ≅ G.obj (S.map e.toEmbedding))

/-- The vertex `e(S)` of the same height as the vertex `S`. -/
private abbrev mapVertex {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    {T : Finset κ // (#T : ℤ) = r} :=
  ⟨S.1.map e.toEmbedding, by rw [card_map]; exact S.2⟩

/-- The degree `r` part of `Functor.cubeComplexReindexIso`: the vertex `F(S)` is sent to the
vertex `G(e(S))` by `α S`, with the inversion sign of `e` on `S`. -/
private def cubeComplexReindexXHom (r : ℤ) : F.cubeComplex.X r ⟶ G.cubeComplex.X r :=
  F.cubeComplexDesc fun S ↦
    (-1 : ℤ) ^ #(S.1.inversions e) • (α S.1).hom ≫ G.cubeComplexι (mapVertex e S)

/-- The inverse of `cubeComplexReindexXHom`. -/
private def cubeComplexReindexXInv (r : ℤ) : G.cubeComplex.X r ⟶ F.cubeComplex.X r :=
  F.cubeComplexLift fun S ↦
    (-1 : ℤ) ^ #(S.1.inversions e) • (G.cubeComplexπ (mapVertex e S) ≫ (α S.1).inv)

@[reassoc]
private lemma ι_cubeComplexReindexXHom {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι S ≫ F.cubeComplexReindexXHom e α r =
      (-1 : ℤ) ^ #(S.1.inversions e) • (α S.1).hom ≫ G.cubeComplexι (mapVertex e S) :=
  F.ι_cubeComplexDesc _ S

@[reassoc]
private lemma ι_cubeComplexReindexXInv {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    G.cubeComplexι (mapVertex e S) ≫ F.cubeComplexReindexXInv e α r =
      (-1 : ℤ) ^ #(S.1.inversions e) • (α S.1).inv ≫ F.cubeComplexι S := by
  refine F.cubeComplex_hom_ext' fun T ↦ ?_
  rw [Category.assoc, cubeComplexReindexXInv, cubeComplexLift_π, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, Category.assoc]
  by_cases h : S = T
  · subst h
    simp
  · have h' : mapVertex e S ≠ mapVertex e T := fun h' ↦
      h (Subtype.ext (by simpa using congrArg Subtype.val h'))
    simp [h, h']

/-- The degreewise isomorphism underlying `Functor.cubeComplexReindexIso`. -/
private def cubeComplexReindexXIso (r : ℤ) : F.cubeComplex.X r ≅ G.cubeComplex.X r where
  hom := F.cubeComplexReindexXHom e α r
  inv := F.cubeComplexReindexXInv e α r
  hom_inv_id := by
    refine F.cubeComplex_hom_ext fun S ↦ ?_
    rw [F.ι_cubeComplexReindexXHom_assoc, Preadditive.zsmul_comp, Category.assoc,
      ι_cubeComplexReindexXInv, Preadditive.comp_zsmul, Iso.hom_inv_id_assoc, smul_smul,
      ← mul_pow]
    simp
  inv_hom_id := by
    refine G.cubeComplex_hom_ext fun ⟨T, hT⟩ ↦ ?_
    obtain ⟨S, rfl⟩ : ∃ S : Finset ι, S.map e.toEmbedding = T :=
      ⟨T.map e.symm.toEmbedding, by simp [map_map]⟩
    rw [← Category.assoc, F.ι_cubeComplexReindexXInv e α ⟨S, by simpa using hT⟩,
      Preadditive.zsmul_comp, Category.assoc, ι_cubeComplexReindexXHom, Preadditive.comp_zsmul,
      Iso.inv_hom_id_assoc, smul_smul, ← mul_pow]
    simp

variable {F e α} in
/-- The degreewise isomorphisms `cubeComplexReindexXIso` commute with the differentials. -/
private lemma cubeComplexReindexXIso_hom_comp_d
    (hα : ∀ (S : Finset ι) (a : ι), a ∉ S →
      F.map (homOfLE (S.subset_insert a)) ≫ (α (insert a S)).hom =
        (α S).hom ≫ G.map (homOfLE (map_subset_map.2 (S.subset_insert a))))
    (r : ℤ) :
    F.cubeComplexReindexXHom e α r ≫ G.cubeComplex.d r (r + 1) =
      F.cubeComplex.d r (r + 1) ≫ F.cubeComplexReindexXHom e α (r + 1) := by
  refine F.cubeComplex_hom_ext fun S ↦ ?_
  rw [F.ι_cubeComplexReindexXHom_assoc, Preadditive.zsmul_comp, Category.assoc,
    ι_cubeComplex_d, F.ι_cubeComplex_d_assoc, Preadditive.comp_sum, Finset.smul_sum,
    Preadditive.sum_comp]
  -- Match the edge `S ⟶ S ∪ {a}` of `F` with the edge `e(S) ⟶ e(S) ∪ {e a}` of `G`.
  refine (Fintype.sum_equiv (e.subtypeEquiv fun a ↦ by simp) _ _ fun a ↦ ?_).symm
  have ha : a.1 ∉ S.1 := mem_compl.1 a.2
  simp only [Equiv.subtypeEquiv_apply, Preadditive.zsmul_comp, Category.assoc,
    F.ι_cubeComplexReindexXHom, Preadditive.comp_zsmul, smul_smul]
  rw [← Category.assoc (F.map _), hα S.1 a.1 ha, Category.assoc]
  congr 1
  · rw [filter_map, card_map]
    simpa [mul_comm] using neg_one_pow_card_inversions_insert (R := ℤ) e.injective ha
  · exact congrArg _ (map_comp_cubeComplexι_congr G _ _ (by simp) _ _)

/-- **Reordering the indices of a cube complex.** For an equivalence `e : ι ≃ κ` of finite
linearly ordered types and vertex isomorphisms `α S : F(S) ≅ G(e(S))` commuting with the edge
maps, the cube complexes of `F` and `G` are isomorphic. On the vertex `F(S)` the isomorphism is
`α S` multiplied by the inversion sign `(-1) ^ #(S.inversions e)` of `e` on `S`
(`Functor.ι_cubeComplexReindexIso_hom_f`); these signs absorb the change in the edge signs. -/
def cubeComplexReindexIso
    (hα : ∀ (S : Finset ι) (a : ι), a ∉ S →
      F.map (homOfLE (S.subset_insert a)) ≫ (α (insert a S)).hom =
        (α S).hom ≫ G.map (homOfLE (map_subset_map.2 (S.subset_insert a)))) :
    F.cubeComplex ≅ G.cubeComplex :=
  HomologicalComplex.Hom.isoOfComponents (F.cubeComplexReindexXIso e α) <| by
    rintro r _ rfl
    exact cubeComplexReindexXIso_hom_comp_d hα r

variable (hα : ∀ (S : Finset ι) (a : ι), a ∉ S →
  F.map (homOfLE (S.subset_insert a)) ≫ (α (insert a S)).hom =
    (α S).hom ≫ G.map (homOfLE (map_subset_map.2 (S.subset_insert a))))

/-- The reindexing isomorphism sends the vertex `F(S)` to the vertex `G(e(S))` by `α S`, with the
inversion sign of `e` on `S`. -/
@[reassoc (attr := simp)]
lemma ι_cubeComplexReindexIso_hom_f {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι S ≫ (F.cubeComplexReindexIso e α hα).hom.f r =
      (-1 : ℤ) ^ #(S.1.inversions e) • (α S.1).hom ≫
        G.cubeComplexι ⟨S.1.map e.toEmbedding, by rw [card_map]; exact S.2⟩ :=
  F.ι_cubeComplexReindexXHom e α S

/-- The inverse of the reindexing isomorphism sends the vertex `G(e(S))` to the vertex `F(S)` by
the inverse of `α S`, with the inversion sign of `e` on `S`. -/
@[reassoc (attr := simp)]
lemma ι_cubeComplexReindexIso_inv_f {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    G.cubeComplexι ⟨S.1.map e.toEmbedding, by rw [card_map]; exact S.2⟩ ≫
        (F.cubeComplexReindexIso e α hα).inv.f r =
      (-1 : ℤ) ^ #(S.1.inversions e) • (α S.1).inv ≫ F.cubeComplexι S :=
  F.ι_cubeComplexReindexXInv e α S

/-- Reindexing along the identity, with the identifications `F(S) = F(S.map id)`, is the
identity of the cube complex. -/
@[simp]
lemma cubeComplexReindexIso_refl :
    F.cubeComplexReindexIso (Equiv.refl ι) (fun S ↦ eqToIso (congrArg F.obj (by simp)))
        (fun S a _ ↦ by
          rw [eqToIso.hom, eqToIso.hom, ← eqToHom_map F (by simp : S = S.map _),
            ← eqToHom_map F (by simp : insert a S = (insert a S).map _), ← F.map_comp,
            ← F.map_comp]
          exact congrArg F.map (Subsingleton.elim _ _)) =
      Iso.refl F.cubeComplex := by
  ext r : 2
  refine F.cubeComplex_hom_ext fun S ↦ ?_
  rw [ι_cubeComplexReindexIso_hom_f, eqToIso.hom, eqToHom_comp_cubeComplexι] <;> simp

/-- Reindexing along a composite `e₂ ∘ e₁` is the composite of the reindexings along `e₁` and
`e₂`. The vertex isomorphisms along `e₂ ∘ e₁` are the composites `α₂ (e₁(S)) ∘ α₁ S`, followed by
the identification `e₂(e₁(S)) = (e₂ ∘ e₁)(S)`, and `h` is their compatibility with the edge maps. -/
lemma cubeComplexReindexIso_trans {H : Finset μ ⥤ C} (e₁ : ι ≃ κ) (e₂ : κ ≃ μ)
    (α₁ : ∀ S : Finset ι, F.obj S ≅ G.obj (S.map e₁.toEmbedding))
    (α₂ : ∀ S : Finset κ, G.obj S ≅ H.obj (S.map e₂.toEmbedding))
    (h₁ : ∀ (S : Finset ι) (a : ι), a ∉ S →
      F.map (homOfLE (S.subset_insert a)) ≫ (α₁ (insert a S)).hom =
        (α₁ S).hom ≫ G.map (homOfLE (map_subset_map.2 (S.subset_insert a))))
    (h₂ : ∀ (S : Finset κ) (a : κ), a ∉ S →
      G.map (homOfLE (S.subset_insert a)) ≫ (α₂ (insert a S)).hom =
        (α₂ S).hom ≫ H.map (homOfLE (map_subset_map.2 (S.subset_insert a))))
    (h : ∀ (S : Finset ι) (a : ι), a ∉ S →
      F.map (homOfLE (S.subset_insert a)) ≫
          (α₁ (insert a S) ≪≫ α₂ ((insert a S).map e₁.toEmbedding) ≪≫
            eqToIso (congrArg H.obj (by simp [map_map]))).hom =
        (α₁ S ≪≫ α₂ (S.map e₁.toEmbedding) ≪≫ eqToIso (congrArg H.obj (by simp [map_map]))).hom ≫
          H.map (homOfLE (map_subset_map.2 (S.subset_insert a)))) :
    F.cubeComplexReindexIso (e₁.trans e₂)
        (fun S ↦ α₁ S ≪≫ α₂ (S.map e₁.toEmbedding) ≪≫
          eqToIso (congrArg H.obj (by simp [map_map]))) h =
      F.cubeComplexReindexIso e₁ α₁ h₁ ≪≫ G.cubeComplexReindexIso e₂ α₂ h₂ := by
  ext r : 2
  refine F.cubeComplex_hom_ext fun S ↦ ?_
  have hsign := neg_one_pow_card_inversions_comp (R := ℤ) e₁.toEmbedding e₂.injective S.1
  simp only [Equiv.coe_toEmbedding] at hsign
  simp only [Iso.trans_hom, HomologicalComplex.comp_f, ι_cubeComplexReindexIso_hom_f_assoc,
    ι_cubeComplexReindexIso_hom_f, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc,
    smul_smul, eqToIso.hom, Equiv.coe_trans]
  rw [eqToHom_comp_cubeComplexι H (by simp [map_map]), hsign]

end CategoryTheory.Functor
