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

* `CategoryTheory.Functor.IsCubeReindexCompatible F G e α`: the vertex isomorphisms `α` commute
  with the edge maps. It holds for the identity reindexing (`IsCubeReindexCompatible.refl`) and
  is preserved by composition (`IsCubeReindexCompatible.trans`).
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

variable {C : Type u} [Category.{v} C] {ι : Type w} [LinearOrder ι] {κ : Type w'} [LinearOrder κ]
  {μ : Type w''} [LinearOrder μ]

/-- The vertex isomorphisms `α S : F(S) ≅ G(e(S))` of a reindexing `e : ι ≃ κ` commute with the
edge maps `F(S) ⟶ F(S ∪ {a})` and `G(e(S)) ⟶ G(e(S) ∪ {e a})`. -/
def IsCubeReindexCompatible (F : Finset ι ⥤ C) (G : Finset κ ⥤ C) (e : ι ≃ κ)
    (α : ∀ S : Finset ι, F.obj S ≅ G.obj (S.map e.toEmbedding)) : Prop :=
  ∀ (S : Finset ι) (a : ι), a ∉ S →
    F.map (homOfLE (S.subset_insert a)) ≫ (α (insert a S)).hom =
      (α S).hom ≫ G.map (homOfLE (map_subset_map.2 (S.subset_insert a)))

omit [LinearOrder κ] in
/-- Unfolding `Functor.IsCubeReindexCompatible`: the vertex isomorphisms commute with every edge
map `F(S) ⟶ F(S ∪ {a})` with `a ∉ S`. -/
theorem isCubeReindexCompatible_iff {F : Finset ι ⥤ C} {G : Finset κ ⥤ C} {e : ι ≃ κ}
    {α : ∀ S : Finset ι, F.obj S ≅ G.obj (S.map e.toEmbedding)} :
    IsCubeReindexCompatible F G e α ↔ ∀ (S : Finset ι) (a : ι), a ∉ S →
      F.map (homOfLE (S.subset_insert a)) ≫ (α (insert a S)).hom =
        (α S).hom ≫ G.map (homOfLE (map_subset_map.2 (S.subset_insert a))) :=
  Iff.rfl

namespace IsCubeReindexCompatible

omit [LinearOrder κ] in
/-- The edge compatibility, for an edge `S ⟶ T` whose target is only propositionally
`insert a S`. -/
private lemma map_comp_hom {F : Finset ι ⥤ C} {G : Finset κ ⥤ C} {e : ι ≃ κ}
    {α : ∀ S : Finset ι, F.obj S ≅ G.obj (S.map e.toEmbedding)}
    (hα : IsCubeReindexCompatible F G e α) {S T : Finset ι} {a : ι} (ha : a ∉ S)
    (hT : insert a S = T) (h : S ⊆ T) (h' : S.map e.toEmbedding ⊆ T.map e.toEmbedding) :
    F.map (homOfLE h) ≫ (α T).hom = (α S).hom ≫ G.map (homOfLE h') := by
  subst hT
  exact hα S a ha

/-- The identifications `F(S) = F(S.map id)` are compatible with the edge maps. -/
theorem refl (F : Finset ι ⥤ C) :
    IsCubeReindexCompatible F F (Equiv.refl ι) fun S ↦ eqToIso (congrArg F.obj (by simp)) := by
  intro S a _
  rw [eqToIso.hom, eqToIso.hom, ← eqToHom_map F (by simp : S = S.map _),
    ← eqToHom_map F (by simp : insert a S = (insert a S).map _), ← F.map_comp, ← F.map_comp]
  exact congrArg F.map (Subsingleton.elim _ _)

/-- The composites `α₂ (e₁(S)) ∘ α₁ S`, followed by the identification `e₂(e₁(S)) = (e₂ ∘ e₁)(S)`,
are compatible with the edge maps when `α₁` and `α₂` are. -/
theorem trans {F : Finset ι ⥤ C} {G : Finset κ ⥤ C} {H : Finset μ ⥤ C} {e₁ : ι ≃ κ}
    {e₂ : κ ≃ μ} {α₁ : ∀ S : Finset ι, F.obj S ≅ G.obj (S.map e₁.toEmbedding)}
    {α₂ : ∀ S : Finset κ, G.obj S ≅ H.obj (S.map e₂.toEmbedding)}
    (h₁ : IsCubeReindexCompatible F G e₁ α₁) (h₂ : IsCubeReindexCompatible G H e₂ α₂) :
    IsCubeReindexCompatible F H (e₁.trans e₂) fun S ↦
      α₁ S ≪≫ α₂ (S.map e₁.toEmbedding) ≪≫ eqToIso (congrArg H.obj (by simp [map_map])) := by
  intro S a ha
  simp only [Iso.trans_hom, eqToIso.hom]
  rw [← Category.assoc, h₁ S a ha, Category.assoc, ← Category.assoc (G.map _),
    h₂.map_comp_hom (a := e₁ a) (by simpa using ha) (by simp [map_insert]) _
      (map_subset_map.2 (map_subset_map.2 (S.subset_insert a))),
    Category.assoc]
  simp only [Category.assoc, Iso.cancel_iso_hom_left]
  rw [← eqToHom_map H (by simp [map_map]), ← eqToHom_map H (by simp [map_map]), ← H.map_comp,
    ← H.map_comp]
  exact congrArg H.map (Subsingleton.elim _ _)

end IsCubeReindexCompatible

variable [Preadditive C] [HasFiniteBiproducts C] [Fintype ι] [Fintype κ] [Fintype μ]

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
  simp only [cubeComplexReindexXInv, Category.assoc, cubeComplexLift_π, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp]
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
    simp [ι_cubeComplexReindexXHom_assoc, ι_cubeComplexReindexXInv, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, smul_smul, ← mul_pow]
  inv_hom_id := by
    refine G.cubeComplex_hom_ext fun ⟨T, hT⟩ ↦ ?_
    obtain ⟨S, rfl⟩ : ∃ S : Finset ι, S.map e.toEmbedding = T :=
      ⟨T.map e.symm.toEmbedding, by simp [map_map]⟩
    simp [F.ι_cubeComplexReindexXInv_assoc e α ⟨S, by simpa using hT⟩, ι_cubeComplexReindexXHom,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← mul_pow]

variable {F e α} in
/-- The degreewise isomorphisms `cubeComplexReindexXIso` commute with the differentials. -/
private lemma cubeComplexReindexXIso_hom_comp_d (hα : IsCubeReindexCompatible F G e α) (r : ℤ) :
    F.cubeComplexReindexXHom e α r ≫ G.cubeComplex.d r (r + 1) =
      F.cubeComplex.d r (r + 1) ≫ F.cubeComplexReindexXHom e α (r + 1) := by
  refine F.cubeComplex_hom_ext fun S ↦ ?_
  simp only [ι_cubeComplexReindexXHom_assoc, ι_cubeComplex_d, ι_cubeComplex_d_assoc,
    Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc,
    Finset.smul_sum]
  -- Match the edge `S ⟶ S ∪ {a}` of `F` with the edge `e(S) ⟶ e(S) ∪ {e a}` of `G`.
  refine (Fintype.sum_equiv (e.subtypeEquiv fun a ↦ by simp) _ _ fun a ↦ ?_).symm
  have ha : a.1 ∉ S.1 := mem_compl.1 a.2
  simp only [Equiv.subtypeEquiv_apply, F.ι_cubeComplexReindexXHom, Preadditive.comp_zsmul,
    smul_smul]
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
def cubeComplexReindexIso (hα : IsCubeReindexCompatible F G e α) :
    F.cubeComplex ≅ G.cubeComplex :=
  HomologicalComplex.Hom.isoOfComponents (F.cubeComplexReindexXIso e α) <| by
    rintro r _ rfl
    exact cubeComplexReindexXIso_hom_comp_d hα r

variable (hα : IsCubeReindexCompatible F G e α)

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
        (IsCubeReindexCompatible.refl F) = Iso.refl F.cubeComplex := by
  ext r : 2
  refine F.cubeComplex_hom_ext fun S ↦ ?_
  rw [ι_cubeComplexReindexIso_hom_f, eqToIso.hom, eqToHom_comp_cubeComplexι] <;> simp

/-- Reindexing along a composite `e₂ ∘ e₁` is the composite of the reindexings along `e₁` and
`e₂`. The vertex isomorphisms along `e₂ ∘ e₁` are the composites `α₂ (e₁(S)) ∘ α₁ S`, followed by
the identification `e₂(e₁(S)) = (e₂ ∘ e₁)(S)`; their compatibility with the edge maps is
`Functor.IsCubeReindexCompatible.trans`. -/
lemma cubeComplexReindexIso_trans {H : Finset μ ⥤ C} (e₁ : ι ≃ κ) (e₂ : κ ≃ μ)
    (α₁ : ∀ S : Finset ι, F.obj S ≅ G.obj (S.map e₁.toEmbedding))
    (α₂ : ∀ S : Finset κ, G.obj S ≅ H.obj (S.map e₂.toEmbedding))
    (h₁ : IsCubeReindexCompatible F G e₁ α₁) (h₂ : IsCubeReindexCompatible G H e₂ α₂) :
    F.cubeComplexReindexIso (e₁.trans e₂)
        (fun S ↦ α₁ S ≪≫ α₂ (S.map e₁.toEmbedding) ≪≫
          eqToIso (congrArg H.obj (by simp [map_map]))) (h₁.trans h₂) =
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
