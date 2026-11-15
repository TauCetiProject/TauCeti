/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Excision
import TauCeti.Analysis.Normed.Module.Ball.Radial.Push
import TauCeti.Topology.ContinuousMap.GlueClosedEmbeddings
import TauCeti.Topology.VectorBundle.Smul

/-!
# Attaching a disc bundle

Let `E → B` be a real vector bundle whose fibre norm is continuous on the total space, with unit
disc bundle `D(E)` and unit sphere bundle `S(E)` (`TauCeti.discBundle`, `TauCeti.sphereBundle`).
Say that a space `Z` is obtained from a closed subset `X` by attaching `D(E)` along `S(E)` through
a map of pairs `f : (D(E), S(E)) ⟶ (Z, X)` when `f` is a closed embedding of `D(E)` into `Z`
whose image meets `X` exactly in the image of `S(E)`, and `X` together with the image of `f` is
all of `Z`. Then `f` induces isomorphisms on relative singular homology and cohomology, with
arbitrary coefficients, in every degree (`TauCeti.isIso_singularHomologyMap_of_attach_discBundle`
and `TauCeti.isIso_singularCohomologyMap_of_attach_discBundle`). Together with the comparison of
the disc-sphere pair with the Thom pair (`TauCeti.isIso_singularHomologyMap_discSpherePairMap` and
`TauCeti.isIso_singularCohomologyMap_discSpherePairMap`), the relative homology and cohomology of
`(Z, X)` are those of the Thom pair `(E, E₀)`.

This is how the attachment of a disc bundle is seen by homology. For instance, crossing a critical
level of a Morse–Bott function attaches, up to homotopy, the negative disc bundle of each critical
submanifold on the level to the sublevel below it; with `X` that lower sublevel and `Z` its union
with the attached disc bundles, the relative homology of the attachment is that of the Thom pair
of the negative normal bundle. The rank zero case is included: there `S(E)` is empty, `D(E)` is
`E` and `Z` is the disjoint union of `X` and a copy of the base.

The proof thickens `X` by an outer collar of the attached disc bundle, as in the proof that good
pairs satisfy excision for quotients. Write `D½` for the vectors of `D(E)` of norm greater than
`1/2` and `N = X ∪ f(D½)`. The radial push `TauCeti.radialPush 2⁻¹`, applied in every fibre of
`D(E)`, deforms it so as to push every vector of norm at least `1/2` out to the unit sphere and to
double the smaller ones; it fixes `S(E)` and keeps `D½` in place. Extended by the identity of `X`,
it is a deformation of `Z` keeping `X` and `N` in place and pushing `N` into `X`. So the inclusions
`(D(E), S(E)) ⟶ (D(E), D½)` and `(Z, X) ⟶ (Z, N)` induce isomorphisms
(`TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy`). Finally the complement of `X` lies
in the image of `f`, and `N` is open, its complement being the image of the closed disc bundle of
radius `1/2`. So excision for the open cover of `Z` by `N` and the complement of `X`
(`TopPair.isIso_singularHomologyMap_of_open_cover`) makes `(D(E), D½) ⟶ (Z, N)` an isomorphism.

## Main results

* `TauCeti.isIso_singularHomologyMap_of_attach_discBundle`: attaching a disc bundle along its
  sphere bundle induces isomorphisms `Hₙ(D(E), S(E)) ≅ Hₙ(Z, X)`.
* `TauCeti.isIso_singularCohomologyMap_of_attach_discBundle`: the same in cohomology,
  `Hⁿ(Z, X) ≅ Hⁿ(D(E), S(E))`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, Proposition 2.22 and its proof (good pairs and excision).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Topology
open scoped unitInterval

universe w v u

namespace TauCeti

variable {B : Type w} {F : Type*} {E : B → Type w} [∀ b, NormedAddCommGroup (E b)]

/-! ### The thickened subspace -/

variable (F E) in
/-- The vectors of the disc bundle of norm greater than `1/2`. -/
private def outerCollar : Set (discBundle F E) :=
  {v | 2⁻¹ < ‖(v : TotalSpace F E).2‖}

private lemma mem_outerCollar {v : discBundle F E} :
    v ∈ outerCollar F E ↔ 2⁻¹ < ‖(v : TotalSpace F E).2‖ :=
  Iff.rfl

private lemma sphereBundle_subset_outerCollar :
    Subtype.val ⁻¹' sphereBundle F E ⊆ outerCollar F E := fun v hv ↦ by
  rw [mem_outerCollar, mem_sphereBundle.1 hv]
  norm_num

section Thickening

variable [TopologicalSpace (TotalSpace F E)] {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  (φ : C(discBundle F E, Z))

/-- The thickening `X ∪ φ(D½)` of `X` by the outer collar of the attached disc bundle. -/
private def thickening : Set Z :=
  X ∪ φ '' outerCollar F E

variable {φ} (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) (hφ : IsClosedEmbedding φ)
  (hX : IsClosed X)
  (hφX : ∀ v : discBundle F E, φ v ∈ X → (v : TotalSpace F E) ∈ sphereBundle F E)
  (hφS : ∀ v : discBundle F E, (v : TotalSpace F E) ∈ sphereBundle F E → φ v ∈ X)
  (hcover : X ∪ range φ = univ)

include hφ hφX in
/-- The attached disc bundle meets the thickening exactly in its outer collar. -/
private lemma mem_thickening_iff (v : discBundle F E) :
    φ v ∈ thickening (X := X) φ ↔ v ∈ outerCollar F E := by
  refine ⟨fun h ↦ h.elim (fun hX ↦ sphereBundle_subset_outerCollar (hφX v hX)) ?_,
    fun h ↦ Or.inr ⟨v, h, rfl⟩⟩
  rintro ⟨w, hw, hwv⟩
  exact hφ.injective hwv ▸ hw

include hnorm hφ hφX hcover in
/-- The complement of the thickening is the image of the closed disc bundle of radius `1/2`, so the
thickening is open. -/
private lemma isOpen_thickening : IsOpen (thickening (X := X) φ) := by
  have hc : (thickening (X := X) φ)ᶜ = φ '' (outerCollar F E)ᶜ := by
    ext z
    refine ⟨fun hz ↦ ?_, ?_⟩
    · obtain ⟨v, rfl⟩ : z ∈ range φ :=
        (hcover.symm ▸ mem_univ z : z ∈ X ∪ _).resolve_left fun hzX ↦ hz (Or.inl hzX)
      exact ⟨v, fun hv ↦ hz ((mem_thickening_iff hφ hφX v).2 hv), rfl⟩
    · rintro ⟨v, hv, rfl⟩ hz
      exact hv ((mem_thickening_iff hφ hφX v).1 hz)
  rw [← isClosed_compl_iff, hc]
  exact hφ.isClosedMap _
    (isOpen_lt continuous_const (hnorm.comp continuous_subtype_val)).isClosed_compl

/-! ### The collar deformations -/

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, NormedSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- The radial push `TauCeti.radialPush 2⁻¹` in every fibre of the disc bundle: at time one it
pushes every vector of norm at least `1/2` out to the unit sphere and doubles the smaller ones. -/
private def discCollar : C(I × discBundle F E, discBundle F E) where
  toFun p := ⟨TotalSpace.mk' F p.2.1.proj (radialPush 2⁻¹ p.1 p.2.1.2),
    mem_discBundle.2 (norm_radialPush_le_one p.1 (mem_discBundle.1 p.2.2))⟩
  continuous_toFun := by
    have hv : Continuous fun p : I × discBundle F E ↦ (p.2 : TotalSpace F E) :=
      continuous_subtype_val.comp continuous_snd
    have ht : Continuous fun p : I × discBundle F E ↦ (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    -- The radial push rescales each vector by a factor in `[0, 3]`, continuous off the zero
    -- section.
    refine Continuous.subtype_mk ((hv.smul_totalSpace_of_norm_le (C := 3) (fun p ↦ ?_)
      fun p hp ↦ ?_).congr fun p ↦ by rw [radialPush_eq_smul]) _
    · have hm : 0 ≤ min 1 (2⁻¹ / ‖(p.2 : TotalSpace F E).2‖) :=
        le_min zero_le_one (by positivity)
      have hm' := min_le_left 1 (2⁻¹ / ‖(p.2 : TotalSpace F E).2‖)
      rw [Real.norm_of_nonneg (by nlinarith [p.1.2.1, p.1.2.2])]
      norm_num
      nlinarith [p.1.2.1, p.1.2.2]
    · exact (continuousAt_const.sub ht.continuousAt).add (ht.continuousAt.mul
        (continuousAt_const.mul (continuousAt_const.min (continuousAt_const.div
          (hnorm.comp hv).continuousAt (norm_ne_zero_iff.2 hp)))))

private lemma coe_discCollar (t : I) (v : discBundle F E) :
    (discCollar hnorm (t, v) : TotalSpace F E) =
      TotalSpace.mk' F v.1.proj (radialPush 2⁻¹ t v.1.2) :=
  rfl

/-- The collar deformation keeps the outer collar in place at every time. -/
private lemma discCollar_mem_outerCollar (t : I) {v : discBundle F E} (hv : v ∈ outerCollar F E) :
    discCollar hnorm (t, v) ∈ outerCollar F E :=
  hv.trans_le (norm_le_norm_radialPush (by norm_num) (by norm_num) t (mem_discBundle.1 v.2))

/-- At time one the collar deformation pushes the outer collar onto the sphere bundle. -/
private lemma discCollar_one_mem_sphereBundle {v : discBundle F E} (hv : v ∈ outerCollar F E) :
    (discCollar hnorm (1, v) : TotalSpace F E) ∈ sphereBundle F E := by
  rw [coe_discCollar, mem_sphereBundle]
  exact norm_radialPush_one (by norm_num) hv.le

/-- The collar deformation fixes the sphere bundle at every time. -/
private lemma discCollar_of_mem_sphereBundle (t : I) {v : discBundle F E}
    (hv : (v : TotalSpace F E) ∈ sphereBundle F E) : discCollar hnorm (t, v) = v := by
  apply Subtype.ext
  rw [coe_discCollar, radialPush_of_norm_eq_one (by norm_num) (by norm_num) t
    (mem_sphereBundle.1 hv)]

/-- At time zero the collar deformation is the identity. -/
private lemma discCollar_zero (v : discBundle F E) : discCollar hnorm (0, v) = v := by
  apply Subtype.ext
  rw [coe_discCollar, radialPush_zero]

/-- The collar deformation of the disc bundle as a homotopy from the identity. -/
private def discCollarHomotopy :
    (ContinuousMap.id (discBundle F E)).Homotopy ((discCollar hnorm).curry 1) where
  toContinuousMap := discCollar hnorm
  map_zero_left := discCollar_zero hnorm
  map_one_left _ := rfl

private lemma discCollarHomotopy_apply (p : I × discBundle F E) :
    discCollarHomotopy hnorm p = discCollar hnorm p :=
  rfl

include hX hφX hcover in
/-- The collar deformation of the disc bundle, transported to its image in `Z` and extended by the
identity of `X`: the gluing of the projection `I × X → Z` and `φ ∘ discCollar` along the closed
embeddings of `I × X` and `I × D(E)` into `I × Z`. -/
private def attachCollar : C(I × Z, Z) :=
  ContinuousMap.glueClosedEmbeddings (i := Prod.map id ((↑) : X → Z)) (j := Prod.map id φ)
    ⟨fun p ↦ p.2, by fun_prop⟩ (φ.comp (discCollar hnorm))
    (IsClosedEmbedding.id.prodMap hX.isClosedEmbedding_subtypeVal)
    (IsClosedEmbedding.id.prodMap hφ)
    (eq_univ_of_forall fun p ↦ by
      obtain hz | ⟨v, hv⟩ := (hcover.symm ▸ mem_univ p.2 : p.2 ∈ X ∪ range φ)
      · exact Or.inl ⟨(p.1, ⟨p.2, hz⟩), rfl⟩
      · exact Or.inr ⟨(p.1, v), Prod.ext rfl hv⟩)
    (by
      rintro ⟨t, x⟩ ⟨s, v⟩ h
      obtain ⟨rfl, hx⟩ : t = s ∧ (x : Z) = φ v := Prod.ext_iff.1 h
      rw [ContinuousMap.coe_mk, ContinuousMap.comp_apply,
        discCollar_of_mem_sphereBundle hnorm t (hφX v (hx ▸ x.2))]
      exact hx)

private lemma attachCollar_apply (t : I) (v : discBundle F E) :
    attachCollar hnorm hφ hX hφX hcover (t, φ v) = φ (discCollar hnorm (t, v)) :=
  ContinuousMap.glueClosedEmbeddings_apply_right _ _ _ _ _ _ (t, v)

private lemma attachCollar_of_mem (t : I) {z : Z} (hz : z ∈ X) :
    attachCollar hnorm hφ hX hφX hcover (t, z) = z :=
  ContinuousMap.glueClosedEmbeddings_apply_left _ _ _ _ _ _ (t, (⟨z, hz⟩ : X))

/-- The collar deformation of the attached space as a homotopy from the identity. -/
private def attachCollarHomotopy :
    (ContinuousMap.id Z).Homotopy ((attachCollar hnorm hφ hX hφX hcover).curry 1) where
  toContinuousMap := attachCollar hnorm hφ hX hφX hcover
  map_zero_left z := by
    obtain hz | ⟨v, rfl⟩ := (hcover.symm ▸ mem_univ z : z ∈ X ∪ range φ)
    · exact attachCollar_of_mem hnorm hφ hX hφX hcover 0 hz
    · exact (attachCollar_apply hnorm hφ hX hφX hcover 0 v).trans
        (congrArg φ (discCollar_zero hnorm v))
  map_one_left _ := rfl

private lemma attachCollarHomotopy_apply (p : I × Z) :
    attachCollarHomotopy hnorm hφ hX hφX hcover p = attachCollar hnorm hφ hX hφX hcover p :=
  rfl

/-! ### The deformations as maps of pairs -/

private lemma discCollarHomotopy_mem_sphereBundle (t : I) {v : discBundle F E}
    (hv : (v : TotalSpace F E) ∈ sphereBundle F E) :
    (discCollarHomotopy hnorm (t, v) : TotalSpace F E) ∈ sphereBundle F E := by
  rwa [discCollarHomotopy_apply, discCollar_of_mem_sphereBundle hnorm t hv]

private lemma discCollarHomotopy_mem_outerCollar (t : I) {v : discBundle F E}
    (hv : v ∈ outerCollar F E) : discCollarHomotopy hnorm (t, v) ∈ outerCollar F E := by
  rw [discCollarHomotopy_apply]
  exact discCollar_mem_outerCollar hnorm t hv

private lemma attachCollarHomotopy_mem (t : I) {z : Z} (hz : z ∈ X) :
    attachCollarHomotopy hnorm hφ hX hφX hcover (t, z) ∈ X := by
  rwa [attachCollarHomotopy_apply, attachCollar_of_mem hnorm hφ hX hφX hcover t hz]

private lemma attachCollarHomotopy_mem_thickening (t : I) {z : Z}
    (hz : z ∈ thickening (X := X) φ) :
    attachCollarHomotopy hnorm hφ hX hφX hcover (t, z) ∈ thickening (X := X) φ := by
  rw [attachCollarHomotopy_apply]
  obtain hz | ⟨v, hv, rfl⟩ := hz
  · rw [attachCollar_of_mem hnorm hφ hX hφX hcover t hz]
    exact Or.inl hz
  · rw [attachCollar_apply]
    exact Or.inr ⟨_, discCollar_mem_outerCollar hnorm t hv, rfl⟩

include hφS in
private lemma mapsTo_attachCollar_thickening :
    MapsTo ((attachCollar hnorm hφ hX hφX hcover).curry 1) (thickening (X := X) φ) X := by
  rintro z (hz | ⟨v, hv, rfl⟩)
  · rw [ContinuousMap.curry_apply, attachCollar_of_mem hnorm hφ hX hφX hcover 1 hz]
    exact hz
  · rw [ContinuousMap.curry_apply, attachCollar_apply]
    exact hφS _ (discCollar_one_mem_sphereBundle hnorm hv)

end Thickening

/-! ### The comparison square -/

section Square

variable [TopologicalSpace (TotalSpace F E)] {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  (φ : C(discBundle F E, Z))

variable (F E) in
/-- The inclusion `(D(E), S(E)) ⟶ (D(E), D½)`. -/
private def sphereToOuterCollar :
    TopPair.ofSubset (X := TopCat.of (discBundle F E)) (Subtype.val ⁻¹' sphereBundle F E) ⟶
      TopPair.ofSubset (X := TopCat.of (discBundle F E)) (outerCollar F E) :=
  TopPair.ofSubsetMap (𝟙 _) fun _ hv ↦ sphereBundle_subset_outerCollar hv

/-- The inclusion `(Z, X) ⟶ (Z, N)`. -/
private def subsetToThickening :
    TopPair.ofSubset (X := TopCat.of Z) X ⟶
      TopPair.ofSubset (X := TopCat.of Z) (thickening (X := X) φ) :=
  TopPair.ofSubsetMap (𝟙 _) fun _ hz ↦ Or.inl hz

/-- The map `(D(E), D½) ⟶ (Z, N)` induced by the attachment. -/
private def outerCollarToThickening :
    TopPair.ofSubset (X := TopCat.of (discBundle F E)) (outerCollar F E) ⟶
      TopPair.ofSubset (X := TopCat.of Z) (thickening (X := X) φ) :=
  TopPair.ofSubsetMap (TopCat.ofHom φ) fun v hv ↦ Or.inr ⟨v, hv, rfl⟩

private lemma fst_sphereToOuterCollar : TopPair.Hom.fst (sphereToOuterCollar F E) = 𝟙 _ :=
  TopPair.ofSubsetMap_fst _ _

private lemma fst_subsetToThickening :
    TopPair.Hom.fst (subsetToThickening (X := X) φ) = 𝟙 _ :=
  TopPair.ofSubsetMap_fst _ _

private lemma fst_outerCollarToThickening :
    TopPair.Hom.fst (outerCollarToThickening (X := X) φ) = TopCat.ofHom φ :=
  TopPair.ofSubsetMap_fst _ _

variable (F E) in
/-- The isomorphism of the disc-sphere pair with the pair `(D(E), S(E))` presented as a subset of
`D(E)`. -/
private abbrev discSpherePairIso :
    TopPair.ofSubset (X := TopCat.of (discBundle F E)) (Subtype.val ⁻¹' sphereBundle F E) ≅
      discSpherePair F E :=
  TopPair.ofSubsetPreimageValIso (X := TopCat.of (TotalSpace F E))
    (sphereBundle_subset_discBundle F E)

/-- The comparison square: `(D(E), S(E)) ⟶ (Z, X) ⟶ (Z, N)` agrees with
`(D(E), S(E)) ⟶ (D(E), D½) ⟶ (Z, N)`. -/
private lemma comp_subsetToThickening_eq
    {f : discSpherePair F E ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
    (hfφ : TopPair.Hom.fst f = TopCat.ofHom φ) :
    f ≫ subsetToThickening φ =
      (discSpherePairIso F E).inv ≫ sphereToOuterCollar F E ≫ outerCollarToThickening φ := by
  refine TopPair.hom_ext_of_fst _ ?_
  have hinv : TopPair.Hom.fst (discSpherePairIso F E).inv = 𝟙 _ :=
    TopCat.ext fun x ↦ TopPair.ofSubsetPreimageValIso_inv_fst_apply x
  rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, hfφ, hinv,
    fst_outerCollarToThickening, fst_subsetToThickening, fst_sphereToOuterCollar]
  -- The identities are those of `TopCat.of Z` and `TopCat.of D(E)`, which `Category.comp_id` does
  -- not recognise through the ambient spaces of the pairs; both sides unfold to `TopCat.ofHom φ`.
  rfl

/-- The open cover of `Z` by the thickening `N` and the complement of `X`. -/
private def thickeningCover : Bool → Set Z :=
  fun b ↦ bif b then thickening (X := X) φ else Xᶜ

private lemma iUnion_thickeningCover : ⋃ b, thickeningCover (X := X) φ b = univ :=
  eq_univ_of_forall fun z ↦ mem_iUnion.2 <| by
    by_cases hz : z ∈ X
    · exact ⟨true, Or.inl hz⟩
    · exact ⟨false, hz⟩

variable {φ} (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) (hφ : IsClosedEmbedding φ)
  (hX : IsClosed X)
  (hφX : ∀ v : discBundle F E, φ v ∈ X → (v : TotalSpace F E) ∈ sphereBundle F E)
  (hcover : X ∪ range φ = univ)

include hφ hX hnorm hφX hcover in
private lemma isOpen_thickeningCover (b : Bool) : IsOpen (thickeningCover (X := X) φ b) := by
  cases b
  · exact hX.isOpen_compl
  · exact isOpen_thickening hnorm hφ hφX hcover

include hcover in
private lemma thickeningCover_subset (b : Bool) :
    thickeningCover (X := X) φ b ⊆
        Set.range (TopPair.ofSubset (X := TopCat.of Z) (thickening (X := X) φ)).map ∨
      thickeningCover (X := X) φ b ⊆
        Set.range (TopPair.Hom.fst (outerCollarToThickening (X := X) φ)) := by
  rw [fst_outerCollarToThickening]
  cases b
  · exact Or.inr fun z hz ↦ (hcover.symm ▸ mem_univ z : z ∈ X ∪ _).resolve_left hz
  · exact Or.inl (TopPair.range_ofSubset_map (X := TopCat.of Z) (B := thickening (X := X) φ)).ge

include hφ in
private lemma isEmbedding_fst_outerCollarToThickening :
    IsEmbedding (TopPair.Hom.fst (outerCollarToThickening (X := X) φ)) := by
  rw [fst_outerCollarToThickening]
  exact hφ.isEmbedding

include hφ hφX in
private lemma mem_range_of_fst_outerCollarToThickening_mem (v : discBundle F E)
    (hv : TopPair.Hom.fst (outerCollarToThickening (X := X) φ) v ∈
      Set.range (TopPair.ofSubset (X := TopCat.of Z) (thickening (X := X) φ)).map) :
    v ∈ Set.range (TopPair.ofSubset (X := TopCat.of (discBundle F E)) (outerCollar F E)).map := by
  rw [fst_outerCollarToThickening] at hv
  refine (TopPair.range_ofSubset_map (X := TopCat.of (discBundle F E)) (B := outerCollar F E)).ge ?_
  exact (mem_thickening_iff hφ hφX v).1
    ((TopPair.range_ofSubset_map (X := TopCat.of Z) (B := thickening (X := X) φ)).le hv)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
  (k : Type*) [Ring k] [Linear k C] (M : C)

include hnorm hφ hX hφX hcover in
private lemma isIso_singularHomologyMap_outerCollarToThickening :
    IsIso (TopPair.singularHomologyMap (outerCollarToThickening (X := X) φ) R n) :=
  TopPair.isIso_singularHomologyMap_of_open_cover R _ (isEmbedding_fst_outerCollarToThickening hφ)
    (mem_range_of_fst_outerCollarToThickening_mem hφ hφX) _
    (isOpen_thickeningCover hnorm hφ hX hφX hcover) (iUnion_thickeningCover φ)
    (thickeningCover_subset hcover) n

include hnorm hφ hX hφX hcover in
private lemma isIso_singularCohomologyMap_outerCollarToThickening :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (outerCollarToThickening (X := X) φ) n) :=
  TopPair.isIso_singularCohomologyMap_of_open_cover _
    (isEmbedding_fst_outerCollarToThickening hφ)
    (mem_range_of_fst_outerCollarToThickening_mem hφ hφX) _
    (isOpen_thickeningCover hnorm hφ hX hφX hcover) (iUnion_thickeningCover φ)
    (thickeningCover_subset hcover) n

end Square

/-! ### Attaching a disc bundle -/

section Attach

variable [TopologicalSpace (TotalSpace F E)] {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : discSpherePair F E ⟶ TopPair.ofSubset (X := TopCat.of Z) X}

/-- A map of pairs out of the disc-sphere pair carries the sphere bundle into the subspace. -/
private lemma fst_mem_of_mem_sphereBundle {v : discBundle F E}
    (hv : (v : TotalSpace F E) ∈ sphereBundle F E) : TopPair.Hom.fst f v ∈ X := by
  have h : TopPair.Hom.fst f v =
      (TopPair.ofSubset (X := TopCat.of Z) X).map (TopPair.Hom.snd f ⟨v.1, hv⟩) :=
    (TopPair.Hom.w_apply f ⟨v.1, hv⟩).symm
  rw [h]
  exact (TopPair.Hom.snd f ⟨v.1, hv⟩).2

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, NormedSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
  {φ : C(discBundle F E, Z)} (hφ : IsClosedEmbedding φ) (hX : IsClosed X)
  (hφX : ∀ v : discBundle F E, φ v ∈ X → (v : TotalSpace F E) ∈ sphereBundle F E)
  (hφS : ∀ v : discBundle F E, (v : TotalSpace F E) ∈ sphereBundle F E → φ v ∈ X)
  (hcover : X ∪ range φ = univ)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
  (k : Type*) [Ring k] [Linear k C] (M : C)

include hnorm in
private lemma isIso_singularHomologyMap_sphereToOuterCollar :
    IsIso (TopPair.singularHomologyMap (sphereToOuterCollar F E) R n) :=
  TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy _ (discCollarHomotopy hnorm)
    (fun τ _ hv ↦ discCollarHomotopy_mem_sphereBundle hnorm τ hv)
    (fun τ _ hv ↦ discCollarHomotopy_mem_outerCollar hnorm τ hv)
    (fun _ hv ↦ discCollar_one_mem_sphereBundle hnorm hv) R n

include hnorm in
private lemma isIso_singularCohomologyMap_sphereToOuterCollar :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (sphereToOuterCollar F E) n) :=
  TopPair.isIso_singularCohomologyMap_ofSubsetMap_id_of_homotopy _ (discCollarHomotopy hnorm)
    (fun τ _ hv ↦ discCollarHomotopy_mem_sphereBundle hnorm τ hv)
    (fun τ _ hv ↦ discCollarHomotopy_mem_outerCollar hnorm τ hv)
    (fun _ hv ↦ discCollar_one_mem_sphereBundle hnorm hv) R k M n

include hnorm hφ hX hφX hφS hcover in
private lemma isIso_singularHomologyMap_subsetToThickening :
    IsIso (TopPair.singularHomologyMap (subsetToThickening (X := X) φ) R n) :=
  TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy _
    (attachCollarHomotopy hnorm hφ hX hφX hcover)
    (fun τ _ hz ↦ attachCollarHomotopy_mem hnorm hφ hX hφX hcover τ hz)
    (fun τ _ hz ↦ attachCollarHomotopy_mem_thickening hnorm hφ hX hφX hcover τ hz)
    (mapsTo_attachCollar_thickening hnorm hφ hX hφX hφS hcover) R n

include hnorm hφ hX hφX hφS hcover in
private lemma isIso_singularCohomologyMap_subsetToThickening :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (subsetToThickening (X := X) φ) n) :=
  TopPair.isIso_singularCohomologyMap_ofSubsetMap_id_of_homotopy _
    (attachCollarHomotopy hnorm hφ hX hφX hcover)
    (fun τ _ hz ↦ attachCollarHomotopy_mem hnorm hφ hX hφX hcover τ hz)
    (fun τ _ hz ↦ attachCollarHomotopy_mem_thickening hnorm hφ hX hφX hcover τ hz)
    (mapsTo_attachCollar_thickening hnorm hφ hX hφX hφS hcover) R k M n

variable (hf : IsClosedEmbedding (TopPair.Hom.fst f))
  (hfX : ∀ v : discBundle F E, TopPair.Hom.fst f v ∈ X → (v : TotalSpace F E) ∈ sphereBundle F E)
  (hfcover : X ∪ range (TopPair.Hom.fst f) = univ)

include hnorm hf hX hfX hfcover in
/-- **Attaching a disc bundle induces isomorphisms on relative homology.** Let `E → B` be a real
vector bundle whose fibre norm is continuous on the total space, and let
`f : (D(E), S(E)) ⟶ (Z, X)` be a map of pairs with `X` closed in `Z`. Suppose that `f` is a closed
embedding of `D(E)` into `Z` sending a point into `X` only if it lies in `S(E)`, and that `X`
together with the image of `f` is all of `Z`: the space `Z` is obtained from `X` by attaching
`D(E)` along `S(E)`. Then `f` induces isomorphisms `Hₙ(D(E), S(E)) ≅ Hₙ(Z, X)` on relative singular
homology, with coefficients in any abelian category with coproducts, in every degree. -/
theorem isIso_singularHomologyMap_of_attach_discBundle :
    IsIso (TopPair.singularHomologyMap f R n) := by
  let φ : C(discBundle F E, Z) := (TopPair.Hom.fst f).hom
  have := isIso_singularHomologyMap_sphereToOuterCollar hnorm R n
  have := isIso_singularHomologyMap_outerCollarToThickening hnorm (φ := φ) hf hX hfX hfcover R n
  have := isIso_singularHomologyMap_subsetToThickening hnorm (φ := φ) hf hX hfX
    (fun _ hv ↦ fst_mem_of_mem_sphereBundle hv) hfcover R n
  have := TopPair.isIso_singularHomologyMap (discSpherePairIso F E).inv (discSpherePairIso F E).hom
    (by rw [Iso.inv_hom_id]; exact TopPair.Homotopy.refl _)
    (by rw [Iso.hom_inv_id]; exact TopPair.Homotopy.refl _) R n
  have hsq := congrArg (TopPair.singularHomologyMap · R n)
    (comp_subsetToThickening_eq φ (TopCat.ofHom_hom _).symm)
  simp only [TopPair.singularHomologyMap_comp] at hsq
  have : IsIso (TopPair.singularHomologyMap f R n ≫
      TopPair.singularHomologyMap (subsetToThickening (X := X) φ) R n) := by
    rw [hsq]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (TopPair.singularHomologyMap (subsetToThickening φ) R n)

include hnorm hf hX hfX hfcover in
/-- **Attaching a disc bundle induces isomorphisms on relative cohomology.** Under the hypotheses
of `TauCeti.isIso_singularHomologyMap_of_attach_discBundle`, the map of pairs
`f : (D(E), S(E)) ⟶ (Z, X)` induces isomorphisms `Hⁿ(Z, X) ≅ Hⁿ(D(E), S(E))` on relative singular
cohomology, with arbitrary coefficients, in every degree. -/
theorem isIso_singularCohomologyMap_of_attach_discBundle :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n) := by
  let φ : C(discBundle F E, Z) := (TopPair.Hom.fst f).hom
  have := isIso_singularCohomologyMap_sphereToOuterCollar hnorm R n k M
  have := isIso_singularCohomologyMap_outerCollarToThickening hnorm (φ := φ) hf hX hfX hfcover
    R n k M
  have := isIso_singularCohomologyMap_subsetToThickening hnorm (φ := φ) hf hX hfX
    (fun _ hv ↦ fst_mem_of_mem_sphereBundle hv) hfcover R n k M
  have := TopPair.isIso_singularCohomologyMap (discSpherePairIso F E).inv
    (discSpherePairIso F E).hom (by rw [Iso.inv_hom_id]; exact TopPair.Homotopy.refl _)
    (by rw [Iso.hom_inv_id]; exact TopPair.Homotopy.refl _) R k M n
  have hsq := congrArg (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) · n)
    (comp_subsetToThickening_eq φ (TopCat.ofHom_hom _).symm)
  simp only [TopPair.singularCohomologyMap_comp] at hsq
  have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (subsetToThickening (X := X) φ) n ≫ TopPair.singularCohomologyMap f n) := by
    rw [hsq]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (subsetToThickening φ) n) _

end Attach

end TauCeti
