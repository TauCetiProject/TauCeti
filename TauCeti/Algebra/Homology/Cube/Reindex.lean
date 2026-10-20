/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Cube.Basic
public import TauCeti.Data.Finset.Inversion

/-!
# Reordering the index set of a cube complex

The signed totalization `CategoryTheory.Functor.cubeComplex` of a cube `F : Finset ι' ⥤ C`
depends on the linear order of `ι'` through its edge signs `(-1) ^ #{b ∈ S | b < a}`. Reordering
the index set changes the complex only up to an isomorphism with vertex signs. Precisely, let
`e : ι ≃ ι'` be any bijection between finite linear orders, not necessarily monotone. The
reindexed cube `F.cubeReindex e : Finset ι ⥤ C` has the vertex `F(S.map e)` at `S`, so it has the
same vertices and edges as `F`, indexed and ordered through `ι`. Its cube complex is isomorphic to
that of `F` by the map which is `(-1) ^ #(S.inversions e)` times the identity on the vertex
`F(S.map e)`. Here `S.inversions e` is the set of pairs `a < b` in `S` with `e b < e a`, so this
sign is the sign of the permutation comparing the two orders of `S`.

For the cube of resolutions of a link diagram, `ι` and `ι'` are the crossings with two chosen
orders, and this is the comparison of the Khovanov complexes built from two crossing orders.

## Main definitions

* `CategoryTheory.Functor.cubeReindex F e`: the cube `S ↦ F(S.map e)`, with its maps of cubes
  `CategoryTheory.NatTrans.cubeReindex α e`.
* `CategoryTheory.Functor.cubeComplexReindexIso F e`: the isomorphism of cube complexes
  `(F.cubeReindex e).cubeComplex ≅ F.cubeComplex`, characterised by
  `Functor.ι_cubeComplexReindexIso_hom_f` and `Functor.cubeComplexReindexIso_inv_f_π`.
* `CategoryTheory.Functor.cubeReindexReflIso F` and `CategoryTheory.Functor.cubeReindexTransIso`:
  the identifications of `F.cubeReindex (Equiv.refl ι)` with `F` and of
  `(F.cubeReindex e₂).cubeReindex e₁` with `F.cubeReindex (e₁.trans e₂)`.

## Main results

* `Functor.cubeComplexReindexIso_hom_naturality`: the isomorphism is natural in the cube.
* `Functor.cubeComplexReindexIso_refl_hom` and `Functor.cubeComplexReindexIso_trans_hom`: the
  identity and composition laws.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §2.
-/

public section

noncomputable section

open CategoryTheory Limits Finset

universe w w' w'' v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {ι : Type w} {ι' : Type w'} {ι'' : Type w''}

namespace Functor

/-- The reindexing of a cube `F : Finset ι' ⥤ C` along a bijection `e : ι ≃ ι'`: its vertex at
`S` is the vertex `F(S.map e)`, and its edges are those of `F`. It is reducible, so that its
vertices are reducibly vertices of `F`. -/
abbrev cubeReindex (F : Finset ι' ⥤ C) (e : ι ≃ ι') : Finset ι ⥤ C where
  obj S := F.obj (S.map e.toEmbedding)
  map f := F.map (homOfLE (map_subset_map.2 (leOfHom f)))
  map_id _ := (congrArg F.map (Subsingleton.elim _ _)).trans (F.map_id _)
  map_comp _ _ := (congrArg F.map (Subsingleton.elim _ _)).trans (F.map_comp _ _)

/-- Reindexing a cube along the identity gives the same cube, up to the identification of
`S.map (Equiv.refl ι)` with `S`. -/
def cubeReindexReflIso (F : Finset ι ⥤ C) : F.cubeReindex (Equiv.refl ι) ≅ F :=
  NatIso.ofComponents (fun S ↦ F.mapIso (eqToIso (by simp))) fun _ ↦ by
    simp only [mapIso_hom, ← F.map_comp]
    exact congrArg F.map (Subsingleton.elim _ _)

@[simp]
lemma cubeReindexReflIso_hom_app (F : Finset ι ⥤ C) (S : Finset ι) :
    F.cubeReindexReflIso.hom.app S = F.map (eqToHom (by simp)) :=
  (rfl)

@[simp]
lemma cubeReindexReflIso_inv_app (F : Finset ι ⥤ C) (S : Finset ι) :
    F.cubeReindexReflIso.inv.app S = F.map (eqToHom (by simp)) :=
  (rfl)

/-- Reindexing a cube along `e₂` and then along `e₁` is reindexing it along `e₁.trans e₂`, up to
the identification of `(S.map e₁).map e₂` with `S.map (e₁.trans e₂)`. -/
def cubeReindexTransIso (F : Finset ι'' ⥤ C) (e₁ : ι ≃ ι') (e₂ : ι' ≃ ι'') :
    (F.cubeReindex e₂).cubeReindex e₁ ≅ F.cubeReindex (e₁.trans e₂) :=
  NatIso.ofComponents (fun S ↦ F.mapIso (eqToIso (show (S.map e₁.toEmbedding).map e₂.toEmbedding =
      S.map (e₁.trans e₂).toEmbedding by simp [map_map]))) fun _ ↦ by
    simp only [mapIso_hom, ← F.map_comp]
    exact congrArg F.map (Subsingleton.elim _ _)

@[simp]
lemma cubeReindexTransIso_hom_app (F : Finset ι'' ⥤ C) (e₁ : ι ≃ ι') (e₂ : ι' ≃ ι'')
    (S : Finset ι) :
    (F.cubeReindexTransIso e₁ e₂).hom.app S = F.map (eqToHom (by simp [map_map])) :=
  (rfl)

@[simp]
lemma cubeReindexTransIso_inv_app (F : Finset ι'' ⥤ C) (e₁ : ι ≃ ι') (e₂ : ι' ≃ ι'')
    (S : Finset ι) :
    (F.cubeReindexTransIso e₁ e₂).inv.app S = F.map (eqToHom (by simp [map_map])) :=
  (rfl)

end Functor

namespace NatTrans

/-- The reindexing of a map of cubes along a bijection `e : ι ≃ ι'`: on the vertex `S` it is the
component of `α` at `S.map e`. -/
def cubeReindex {F F' : Finset ι' ⥤ C} (α : F ⟶ F') (e : ι ≃ ι') :
    F.cubeReindex e ⟶ F'.cubeReindex e where
  app S := α.app (S.map e.toEmbedding)

@[simp]
lemma cubeReindex_app {F F' : Finset ι' ⥤ C} (α : F ⟶ F') (e : ι ≃ ι') (S : Finset ι) :
    (cubeReindex α e).app S = α.app (S.map e.toEmbedding) :=
  (rfl)

end NatTrans

variable [Preadditive C] [HasFiniteBiproducts C] [Fintype ι] [LinearOrder ι] [Fintype ι']
  [LinearOrder ι'] [Fintype ι''] [LinearOrder ι'']

namespace Functor

/-- Edge maps into vertices of the cube complex only depend on the target vertex. -/
private lemma map_comp_cubeComplexι_congr (F : Finset ι ⥤ C) {r : ℤ} {V U U' : Finset ι}
    (f : V ⟶ U) (f' : V ⟶ U') (h : U = U') (hU : (#U : ℤ) = r) (hU' : (#U' : ℤ) = r) :
    F.map f ≫ F.cubeComplexι ⟨U, hU⟩ = F.map f' ≫ F.cubeComplexι ⟨U', hU'⟩ := by
  subst h
  obtain rfl := Subsingleton.elim f f'
  rfl

private lemma neg_one_pow_mul_self (n : ℕ) : (-1 : ℤ) ^ n * (-1) ^ n = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

variable (F : Finset ι' ⥤ C) (e : ι ≃ ι')

/-- A vertex of the reindexed cube is a vertex of `F`, so the inclusions and projections of the
two cube complexes at matching vertices compose in the same way. -/
private lemma cubeComplexι_π_map {r : ℤ} (S S' : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι ⟨S.1.map e.toEmbedding, by simpa using S.2⟩ ≫
        F.cubeComplexπ ⟨S'.1.map e.toEmbedding, by simpa using S'.2⟩ =
      (F.cubeReindex e).cubeComplexι S ≫ (F.cubeReindex e).cubeComplexπ S' := by
  by_cases h : S = S'
  · subst h
    simp
  · rw [cubeComplexι_π_of_ne _ h, cubeComplexι_π_of_ne]
    simpa [Subtype.ext_iff] using h

/-- The degreewise isomorphism underlying `Functor.cubeComplexReindexIso`. -/
private def reindexXIso (r : ℤ) : (F.cubeReindex e).cubeComplex.X r ≅ F.cubeComplex.X r where
  hom := cubeComplexDesc _ fun S ↦
    ((-1 : ℤ) ^ #(S.1.inversions e)) • F.cubeComplexι ⟨S.1.map e.toEmbedding, by simpa using S.2⟩
  inv := cubeComplexLift _ fun S ↦
    ((-1 : ℤ) ^ #(S.1.inversions e)) • F.cubeComplexπ ⟨S.1.map e.toEmbedding, by simpa using S.2⟩
  hom_inv_id := by
    refine cubeComplex_hom_ext _ fun S ↦ cubeComplex_hom_ext' _ fun S' ↦ ?_
    simp only [ι_cubeComplexDesc_assoc, Category.assoc, cubeComplexLift_π, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, smul_smul, Category.id_comp, cubeComplexι_π_map]
    by_cases h : S = S'
    · subst h
      rw [neg_one_pow_mul_self, one_smul]
    · rw [cubeComplexι_π_of_ne _ h, smul_zero]
  inv_hom_id := by
    refine cubeComplex_hom_ext _ fun T ↦ ?_
    obtain ⟨S, rfl⟩ : ∃ S : {S : Finset ι // (#S : ℤ) = r},
        (⟨S.1.map e.toEmbedding, by simpa using S.2⟩ : {T : Finset ι' // (#T : ℤ) = r}) = T :=
      ⟨⟨T.1.map e.symm.toEmbedding, by simpa using T.2⟩, Subtype.ext (by simp [map_map])⟩
    have hinv : F.cubeComplexι ⟨S.1.map e.toEmbedding, by simpa using S.2⟩ ≫
        cubeComplexLift _ (fun S ↦ ((-1 : ℤ) ^ #(S.1.inversions e)) •
          F.cubeComplexπ ⟨S.1.map e.toEmbedding, by simpa using S.2⟩) =
        ((-1 : ℤ) ^ #(S.1.inversions e)) • (F.cubeReindex e).cubeComplexι S := by
      refine cubeComplex_hom_ext' _ fun S' ↦ ?_
      simp only [Category.assoc, cubeComplexLift_π, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
        cubeComplexι_π_map]
      by_cases h : S = S'
      · subst h
        rfl
      · simp [cubeComplexι_π_of_ne _ h]
    rw [reassoc_of% hinv, Preadditive.zsmul_comp, ι_cubeComplexDesc, smul_smul,
      neg_one_pow_mul_self, one_smul, Category.comp_id]

private lemma ι_reindexXIso_hom {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    (F.cubeReindex e).cubeComplexι S ≫ (F.reindexXIso e r).hom =
      ((-1 : ℤ) ^ #(S.1.inversions e)) •
        F.cubeComplexι ⟨S.1.map e.toEmbedding, by simpa using S.2⟩ :=
  ι_cubeComplexDesc _ _ S

/-- **Reordering the index set of a cube complex.** For a bijection `e : ι ≃ ι'` of finite linear
orders, not necessarily monotone, the cube complex of the reindexed cube `F.cubeReindex e` is
isomorphic to the cube complex of `F`. On the vertex `S` the isomorphism is the identity of
`F(S.map e)` times the sign `(-1) ^ #(S.inversions e)` of the permutation comparing the two orders
of `S` (`Functor.ι_cubeComplexReindexIso_hom_f`). -/
def cubeComplexReindexIso : (F.cubeReindex e).cubeComplex ≅ F.cubeComplex :=
  HomologicalComplex.Hom.isoOfComponents (F.reindexXIso e) <| by
    rintro r _ rfl
    refine cubeComplex_hom_ext _ fun S ↦ ?_
    rw [reassoc_of% (F.ι_reindexXIso_hom e S), ι_cubeComplex_d_assoc, Preadditive.zsmul_comp,
      ι_cubeComplex_d, Preadditive.sum_comp, Finset.smul_sum]
    -- Match the edge `S ⟶ insert a S` with the edge `S.map e ⟶ insert (e a) (S.map e)`.
    refine (Fintype.sum_equiv (e.subtypeEquiv fun a ↦ by simp) _ _ fun a ↦ ?_).symm
    rw [Preadditive.zsmul_comp, Category.assoc, F.ι_reindexXIso_hom e, Preadditive.comp_zsmul,
      smul_smul, smul_smul]
    congr 1
    · rw [neg_one_pow_card_inversions_insert e.injective.injOn (mem_compl.1 a.2)]
      simp only [Equiv.subtypeEquiv_apply, filter_map, card_map, Function.comp_def,
        Equiv.coe_toEmbedding]
      rw [← mul_assoc, ← mul_assoc, neg_one_pow_mul_self, one_mul, mul_comm]
    · exact map_comp_cubeComplexι_congr F _ _ (by simp [map_insert]) _ _

/-- The isomorphism `Functor.cubeComplexReindexIso` is `(-1) ^ #(S.inversions e)` times the
identity on the vertex `S` of the reindexed cube. -/
@[reassoc (attr := simp)]
lemma ι_cubeComplexReindexIso_hom_f {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    (F.cubeReindex e).cubeComplexι S ≫ (F.cubeComplexReindexIso e).hom.f r =
      ((-1 : ℤ) ^ #(S.1.inversions e)) •
        F.cubeComplexι ⟨S.1.map e.toEmbedding, by simpa using S.2⟩ :=
  F.ι_reindexXIso_hom e S

/-- The inverse of `Functor.cubeComplexReindexIso` is `(-1) ^ #(S.inversions e)` times the
identity on the vertex `S` of the reindexed cube. -/
@[reassoc (attr := simp)]
lemma cubeComplexReindexIso_inv_f_π {r : ℤ} (S : {S : Finset ι // (#S : ℤ) = r}) :
    (F.cubeComplexReindexIso e).inv.f r ≫ (F.cubeReindex e).cubeComplexπ S =
      ((-1 : ℤ) ^ #(S.1.inversions e)) •
        F.cubeComplexπ ⟨S.1.map e.toEmbedding, by simpa using S.2⟩ :=
  cubeComplexLift_π _ _ S

/-- The reordering isomorphism is natural in the cube. -/
@[reassoc]
lemma cubeComplexReindexIso_hom_naturality {F F' : Finset ι' ⥤ C} (α : F ⟶ F') :
    NatTrans.cubeComplexMap (NatTrans.cubeReindex α e) ≫ (F'.cubeComplexReindexIso e).hom =
      (F.cubeComplexReindexIso e).hom ≫ NatTrans.cubeComplexMap α :=
  HomologicalComplex.hom_ext _ _ fun _ ↦ cubeComplex_hom_ext _ fun S ↦ by
    simp [Preadditive.comp_zsmul, Preadditive.zsmul_comp]

/-- **The identity law.** Reordering along the identity of `ι` is the cube complex map of the
identification `Functor.cubeReindexReflIso`: all its vertex signs are `1`. -/
lemma cubeComplexReindexIso_refl_hom (F : Finset ι ⥤ C) :
    (F.cubeComplexReindexIso (Equiv.refl ι)).hom =
      NatTrans.cubeComplexMap F.cubeReindexReflIso.hom := by
  refine HomologicalComplex.hom_ext _ _ fun r ↦ cubeComplex_hom_ext _ fun S ↦ ?_
  simp only [ι_cubeComplexReindexIso_hom_f, Equiv.coe_refl, inversions_id, card_empty, pow_zero,
    one_smul, NatTrans.ι_cubeComplexMap_f, cubeReindexReflIso_hom_app]
  rw [← Category.id_comp (F.cubeComplexι _), ← F.map_id]
  exact map_comp_cubeComplexι_congr F _ _ (by simp) _ _

/-- **The composition law.** Reordering along `e₁` and then along `e₂` is reordering along
`e₁.trans e₂`, after the identification `Functor.cubeReindexTransIso`: the vertex signs multiply,
by `Finset.neg_one_pow_card_inversions_comp`. -/
lemma cubeComplexReindexIso_trans_hom (F : Finset ι'' ⥤ C) (e₁ : ι ≃ ι') (e₂ : ι' ≃ ι'') :
    ((F.cubeReindex e₂).cubeComplexReindexIso e₁).hom ≫ (F.cubeComplexReindexIso e₂).hom =
      NatTrans.cubeComplexMap (F.cubeReindexTransIso e₁ e₂).hom ≫
        (F.cubeComplexReindexIso (e₁.trans e₂)).hom := by
  refine HomologicalComplex.hom_ext _ _ fun r ↦ cubeComplex_hom_ext _ fun S ↦ ?_
  simp only [HomologicalComplex.comp_f, ι_cubeComplexReindexIso_hom_f_assoc,
    Preadditive.zsmul_comp, ι_cubeComplexReindexIso_hom_f, smul_smul,
    NatTrans.ι_cubeComplexMap_f_assoc, cubeReindexTransIso_hom_app, Preadditive.comp_zsmul]
  have hsign := neg_one_pow_card_inversions_comp (R := ℤ) e₁.toEmbedding (s := S.1)
    e₂.injective.injOn
  rw [Equiv.coe_toEmbedding, ← Equiv.coe_trans] at hsign
  rw [← hsign]
  congr 1
  rw [← Category.id_comp (F.cubeComplexι _), ← F.map_id]
  exact map_comp_cubeComplexι_congr F _ _ (by simp [map_map]) _ _

end Functor

end CategoryTheory
