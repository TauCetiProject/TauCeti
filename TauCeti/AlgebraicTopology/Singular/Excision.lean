/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Excision
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Relative
public import TauCeti.Topology.Category.TopPair

/-!
# Excision for relative singular homology

Let `(X, B)` be a topological pair and `A ⊆ X` a subset such that the interiors of `A` and `B`
cover `X`.  The inclusion of pairs `(A, A ∩ B) ⟶ (X, B)` induces an isomorphism on relative
singular homology in every degree, with coefficients in any object of an abelian category with
coproducts (`TopPair.isIso_singularHomologyMap_excisionMap`).  Equivalently, excising a set `Z`
whose closure lies in the interior of `B` does not change relative homology
(`TopPair.isIso_singularHomologyMap_excisionMap_compl`).

Both follow from a statement about an arbitrary map of topological pairs `f : P ⟶ P'` whose map
on ambient spaces is an embedding and whose subspace is the full preimage of the subspace of `P'`:
if the ambient space of `P'` has an open cover each of whose members lies in the subspace of `P'`
or in the image of `f`, then `f` induces isomorphisms on relative singular homology
(`TopPair.isIso_singularHomologyMap_of_open_cover`).

Two intermediate results are available on their own.  The relative small-chain theorem
(`TopPair.isIso_homologyMap_restrictι_smallSingularSubcomplex`) identifies the relative homology
of a topological pair with that of its singular pair restricted to the simplices subordinate to
any open cover of the ambient space.  Under the hypotheses of
`TopPair.isIso_singularHomologyMap_of_open_cover`, the map `f` puts the simplices subordinate to
the pulled-back cover which do not lie in the subspace of `P` in bijection with the simplices
subordinate to the cover which do not lie in the subspace of `P'`
(`TopPair.relativeSimplex_restrictMap_bijective`); this is the form in which the hypotheses on `f`
and the cover enter, and it feeds the complementary-simplex criterion of simplicial excision.

A continuous map `g : X ⟶ Y` carrying `A` into `A'` and `B` into `B'` is a map of excision data:
it induces a map of pairs `TopPair.interPairMap g hA hB : (A, A ∩ B) ⟶ (A', A' ∩ B')`, functorial
in `g`, which together with `TopPair.ofSubsetMap g hB : (X, B) ⟶ (Y, B')` forms a commutative
square with the excision maps (`TopPair.interPairMap_comp_excisionMap`), so the excision
isomorphisms are natural in the data.
Compatibility with the connecting morphism of the pair is `TopPair.singularHomologyδ_naturality`
applied to the excision map.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Theorem 2.20 and Proposition 2.21.
* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter VII.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe w v u

namespace TopPair

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

section Excision

variable {P P' : TopPair.{w}} (f : P ⟶ P') (hf : IsEmbedding (Hom.fst f))
  (hsnd : ∀ x, Hom.fst f x ∈ Set.range P'.map → x ∈ Set.range P.map)
  {ι : Type*} (U : ι → Set P'.fst) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)
  (hUf : ∀ i, U i ⊆ Set.range P'.map ∨ U i ⊆ Set.range (Hom.fst f))

include hsnd in
/-- If the subspace of `P` is the full preimage of the subspace of `P'`, then a map of pairs sends
small simplices not lying in the subspace of `P` to small simplices not lying in the subspace of
`P'`. -/
lemma mem_relativeSimplex_restrictMap_right_app (n : ℕ)
    (x : ((toSSetPair.obj P).restrict
        (P.smallSingularSubcomplex (fun i ↦ Hom.fst f ⁻¹' U i))).RelativeSimplex n) :
    (SSetPair.restrictMap (toSSetPair.map f)
        (smallSingularSubcomplex_le_preimage f U)).right.app _ x.1 ∈
      ((toSSetPair.obj P').restrict (P'.smallSingularSubcomplex U)).RelativeSimplex n := by
  intro hx
  obtain ⟨a, ha⟩ := (SSetPair.mem_range_restrict_hom_app_iff _ _ _).mp hx
  have hx' := (P'.isEmbedding_map.isInducing.mem_range_toSSet_map_app_iff _ _).mp
    ⟨a, ha.trans (SSetPair.restrictMap_right_app_coe _ _ x.1)⟩
  refine x.2 ((mem_range_restrict_hom_app_iff P _ _).mpr ?_)
  rintro _ ⟨t, rfl⟩
  apply hsnd
  apply hx'
  exact ⟨t, rfl⟩

include hf hsnd hUf in
/-- **Complementary small simplices correspond.** For a map of pairs which is an embedding on
ambient spaces, whose subspace is the full preimage of the subspace of the target, and an open
cover of the target each of whose members lies in the subspace or in the image, the simplices small
for the pulled-back cover not lying in the subspace correspond bijectively to the simplices small
for the cover not lying in the subspace of the target. -/
lemma relativeSimplex_restrictMap_bijective (n : ℕ) :
    Function.Bijective (fun x : ((toSSetPair.obj P).restrict
        (P.smallSingularSubcomplex (fun i ↦ Hom.fst f ⁻¹' U i))).RelativeSimplex n ↦
      (⟨_, mem_relativeSimplex_restrictMap_right_app f hsnd U n x⟩ :
        ((toSSetPair.obj P').restrict (P'.smallSingularSubcomplex U)).RelativeSimplex n)) := by
  have : Mono (Hom.fst f) := (TopCat.mono_iff_injective _).mpr hf.injective
  constructor
  · intro x y hxy
    have h1 := congrArg (fun z : ((toSSetPair.obj P').restrict
        (P'.smallSingularSubcomplex U)).RelativeSimplex n ↦ z.1.1) hxy
    have h2 := (SSetPair.restrictMap_right_app_coe _ _ x.1).symm.trans
      (h1.trans (SSetPair.restrictMap_right_app_coe _ _ y.1))
    exact Subtype.ext (Subtype.ext (injective_of_mono ((TopCat.toSSet.map (Hom.fst f)).app _) h2))
  · intro y
    obtain ⟨i, hi⟩ := (P'.mem_smallSingularSubcomplex_iff U _).mp y.1.2
    have hy : ¬ Set.range (P'.fst.toSSetObjEquiv _ y.1.1) ⊆ Set.range P'.map := fun h ↦
      y.2 ((mem_range_restrict_hom_app_iff P' _ _).mpr h)
    -- The simplex lies in a member of the cover, which lies in the image of `f` since the simplex
    -- does not lie in the subspace; as `f` is an embedding, the simplex is induced from `P`.
    have hsub : Set.range (P'.fst.toSSetObjEquiv _ y.1.1) ⊆ Set.range (Hom.fst f) := by
      rcases hUf i with h | h
      · exact (hy (hi.trans h)).elim
      · exact hi.trans h
    obtain ⟨σ, hσ⟩ := (hf.isInducing.mem_range_toSSet_map_app_iff _ _).mpr hsub
    have hσ' : (ConcreteCategory.hom (Hom.fst f)).comp (P.fst.toSSetObjEquiv _ σ) =
        P'.fst.toSSetObjEquiv _ y.1.1 := by
      rw [← TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, hσ]
    rw [← hσ', ContinuousMap.coe_comp, Set.range_comp, Set.image_subset_iff] at hi
    have hσS : σ ∈ (P.smallSingularSubcomplex (fun i ↦ Hom.fst f ⁻¹' U i)).obj _ :=
      (P.mem_smallSingularSubcomplex_iff _ _).mpr ⟨i, hi⟩
    refine ⟨⟨⟨σ, hσS⟩, ?_⟩, ?_⟩
    · intro hσA
      have hσA' := (mem_range_restrict_hom_app_iff P _ _).mp hσA
      apply hy
      rw [← hσ', ContinuousMap.coe_comp, Set.range_comp]
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, rfl⟩ := hσA' ha
      exact ⟨Hom.snd f b, Hom.w_apply f b⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact (SSetPair.restrictMap_right_app_coe _ _ _).trans hσ

include hf hsnd hU hcov hUf in
/-- **Excision for relative singular homology.** Let `f : P ⟶ P'` be a map of topological pairs
which is an embedding on ambient spaces and whose subspace is the full preimage of the subspace of
`P'`.  If the ambient space of `P'` has an open cover each of whose members lies in the subspace of
`P'` or in the image of `f`, then `f` induces isomorphisms on relative singular homology. -/
theorem isIso_singularHomologyMap_of_open_cover (n : ℕ) :
    IsIso (TopPair.singularHomologyMap f R n) := by
  have h₁ := isIso_homologyMap_restrictι_smallSingularSubcomplex R P' U hU hcov n
  have h₂ := isIso_homologyMap_restrictι_smallSingularSubcomplex R P
    (fun i ↦ Hom.fst f ⁻¹' U i) (fun i ↦ (hU i).preimage (Hom.fst f).hom.continuous)
    (by rw [← Set.preimage_iUnion, hcov, Set.preimage_univ]) n
  have h₃ : IsIso (SSetPair.homologyMap (SSetPair.restrictMap (toSSetPair.map f)
      (smallSingularSubcomplex_le_preimage f U)) R n) :=
    SSetPair.isIso_homologyMap_of_relativeSimplex_equiv _ R
      (fun m ↦ Equiv.ofBijective _ (relativeSimplex_restrictMap_bijective f hf hsnd U hUf m))
      (fun _ _ ↦ rfl) n
  have hsq := SSetPair.restrictMap_comp_restrictι (toSSetPair.map f)
    (smallSingularSubcomplex_le_preimage f U)
  have : IsIso (SSetPair.homologyMap ((toSSetPair.obj P).restrictι
      (P.smallSingularSubcomplex (fun i ↦ Hom.fst f ⁻¹' U i))) R n ≫
      TopPair.singularHomologyMap f R n) := by
    rw [← SSetPair.homologyMap_comp, ← hsq, SSetPair.homologyMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left (SSetPair.homologyMap ((toSSetPair.obj P).restrictι
    (P.smallSingularSubcomplex (fun i ↦ Hom.fst f ⁻¹' U i))) R n) _

end Excision

section Subsets

variable {X : TopCat.{w}} (A B : Set X)

/-- The topological pair `(A, A ∩ B)`, with `A ∩ B` realised as the preimage of `B` in the
subspace `A`. -/
abbrev interPair : TopPair.{w} := TopPair.ofSubset (X := TopCat.of A) (Subtype.val ⁻¹' B)

/-- The inclusion of pairs `(A, A ∩ B) ⟶ (X, B)`. -/
def excisionMap : interPair A B ⟶ ofSubset B :=
  TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom ⟨B.restrictPreimage Subtype.val, continuous_subtype_val.restrictPreimage⟩)

@[simp]
lemma excisionMap_fst_apply (x : (interPair A B).fst) : Hom.fst (excisionMap A B) x = x.1 := (rfl)

@[simp]
lemma excisionMap_snd_apply (x : (interPair A B).snd) :
    (Hom.snd (excisionMap A B) x).1 = x.1.1 := (rfl)

/-- **Excision.** If the interiors of `A` and `B` cover `X`, the inclusion of pairs
`(A, A ∩ B) ⟶ (X, B)` induces isomorphisms on relative singular homology. -/
theorem isIso_singularHomologyMap_excisionMap (h : interior A ∪ interior B = Set.univ)
    (n : ℕ) : IsIso (TopPair.singularHomologyMap (excisionMap A B) R n) := by
  refine isIso_singularHomologyMap_of_open_cover R (excisionMap A B) IsEmbedding.subtypeVal ?_
    (fun b : Bool ↦ bif b then interior A else interior B)
    (fun b ↦ by cases b <;> exact isOpen_interior) ?_ ?_ n
  · rintro x ⟨y, hy⟩
    have hy' : y.1 = x.1 := hy
    exact ⟨⟨x, (hy' ▸ y.2 : x.1 ∈ B)⟩, rfl⟩
  · rw [← Set.union_eq_iUnion]
    exact h
  · intro b
    cases b
    · exact Or.inl (interior_subset.trans fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩)
    · exact Or.inr (interior_subset.trans fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩)

/-- **Excision of a set with closure in the interior of the subspace.** If `closure Z ⊆ interior B`,
the inclusion of pairs `(X ∖ Z, B ∖ Z) ⟶ (X, B)` induces isomorphisms on relative singular
homology. -/
theorem isIso_singularHomologyMap_excisionMap_compl (Z : Set X) (h : closure Z ⊆ interior B)
    (n : ℕ) : IsIso (TopPair.singularHomologyMap (excisionMap Zᶜ B) R n) := by
  refine isIso_singularHomologyMap_excisionMap R Zᶜ B ?_ n
  rw [interior_compl, Set.eq_univ_iff_forall]
  intro x
  by_cases hx : x ∈ closure Z
  · exact Or.inr (h hx)
  · exact Or.inl hx

variable {A B} {Y : TopCat.{w}} (g : X ⟶ Y) {A' B' : Set Y}
  (hA : Set.MapsTo g A A') (hB : Set.MapsTo g B B')

/-- A map of excision data: a continuous map `g : X ⟶ Y` carrying `A` into `A'` and `B` into `B'`
induces a map of pairs `(A, A ∩ B) ⟶ (A', A' ∩ B')`. -/
def interPairMap : interPair A B ⟶ interPair A' B' :=
  ofSubsetMap (TopCat.ofHom ⟨hA.restrict, g.hom.continuous.restrict hA⟩)
    (fun _ hx ↦ hB hx)

@[simp]
lemma interPairMap_fst_apply (x : (interPair A B).fst) :
    (Hom.fst (interPairMap g hA hB) x).1 = g x.1 :=
  congrArg Subtype.val (ofSubsetMap_fst_apply
    (TopCat.ofHom ⟨hA.restrict, g.hom.continuous.restrict hA⟩) (fun _ hx ↦ hB hx) x)

@[simp]
lemma interPairMap_snd_apply (x : (interPair A B).snd) :
    (Hom.snd (interPairMap g hA hB) x).1.1 = g x.1.1 :=
  congrArg Subtype.val (ofSubsetMap_snd_apply
    (TopCat.ofHom ⟨hA.restrict, g.hom.continuous.restrict hA⟩) (fun _ hx ↦ hB hx) x)

@[simp]
lemma interPairMap_id (hA : Set.MapsTo (𝟙 X) A A) (hB : Set.MapsTo (𝟙 X) B B) :
    interPairMap (𝟙 X) hA hB = 𝟙 (interPair A B) := by
  ext : 2
  · exact Subtype.ext (Subtype.ext (interPairMap_snd_apply _ _ _ _))
  · exact Subtype.ext (interPairMap_fst_apply _ _ _ _)

@[reassoc]
lemma interPairMap_comp {Z : TopCat.{w}} (g' : Y ⟶ Z) {A'' B'' : Set Z}
    (hA' : Set.MapsTo g' A' A'') (hB' : Set.MapsTo g' B' B'')
    (hA'' : Set.MapsTo (g ≫ g') A A'') (hB'' : Set.MapsTo (g ≫ g') B B'') :
    interPairMap (g ≫ g') hA'' hB'' = interPairMap g hA hB ≫ interPairMap g' hA' hB' := by
  ext : 2
  · exact Subtype.ext (Subtype.ext (by simp))
  · exact Subtype.ext (by simp)

/-- The excision maps are natural in the excision data. -/
@[reassoc]
lemma interPairMap_comp_excisionMap :
    interPairMap g hA hB ≫ excisionMap A' B' = excisionMap A B ≫ ofSubsetMap g hB := by
  ext : 2
  · exact Subtype.ext (by simp)
  · exact (interPairMap_fst_apply g hA hB _).trans (ofSubsetMap_fst_apply g hB _).symm

end Subsets

end TopPair
