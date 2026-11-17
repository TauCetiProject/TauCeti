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

Let `E → B` be a real vector bundle with a fibre gauge `ρ` (`TauCeti.IsFiberGauge`): a continuous
function on the total space, positively homogeneous on each fibre and positive off the zero
section, such as a fibre norm which is continuous on the total space. Let `D_ρ(E) = {ρ ≤ 1}` and
`S_ρ(E) = {ρ = 1}` be its disc and sphere bundles (`TauCeti.gaugeDiscBundle`,
`TauCeti.gaugeSphereBundle`). Say that a space `Z` is obtained from a closed subset `X` by
attaching `D_ρ(E)` along `S_ρ(E)` through a map of pairs `f : (D_ρ(E), S_ρ(E)) ⟶ (Z, X)` when `f`
is a closed embedding of `D_ρ(E)` into `Z` whose image meets `X` exactly in the image of
`S_ρ(E)`, and `X` together with the image of `f` is all of `Z`. Then `f` induces isomorphisms on
relative singular homology and cohomology, with arbitrary coefficients, in every degree
(`TauCeti.isIso_singularHomologyMap_of_attach_gaugeDiscBundle` and
`TauCeti.isIso_singularCohomologyMap_of_attach_gaugeDiscBundle`). Together with the comparison of
the disc-sphere pair with the Thom pair (`TauCeti.isIso_singularHomologyMap_gaugeDiscSpherePairMap`
and `TauCeti.isIso_singularCohomologyMap_gaugeDiscSpherePairMap`), the relative homology and
cohomology of `(Z, X)` are those of the Thom pair `(E, E₀)`.

This is how the attachment of a disc bundle is seen by homology. For instance, crossing a critical
level of a Morse–Bott function attaches, up to homotopy, the negative disc bundle of each critical
submanifold on the level to the sublevel below it; with `X` that lower sublevel and `Z` its union
with the attached disc bundles, the relative homology of the attachment is that of the Thom pair
of the negative normal bundle. There the attached disc bundle is cut out by the normal Hessian,
`{-½ Hess(v, v) ≤ ε}`, which is the disc bundle of the gauge `v ↦ √(-Hess(v, v) / (2ε))` rather
than the unit disc bundle of a norm carried by the fibres. The unit disc bundle `D(E)` of a fibre
norm is the case `ρ v = ‖v‖` (`TauCeti.isFiberGauge_norm`). The rank zero case is included: there
`S_ρ(E)` is empty, `D_ρ(E)` is `E` and `Z` is the disjoint union of `X` and a copy of the base.

The proof thickens `X` by an outer collar of the attached disc bundle, as in the proof that good
pairs satisfy excision for quotients. Write `D½` for the vectors of `D_ρ(E)` of gauge greater than
`1/2` and `N = X ∪ f(D½)`. The radial push `TauCeti.radialPush 2⁻¹`, applied to the gauge in every
fibre of `D_ρ(E)`, deforms it so as to push every vector of gauge at least `1/2` out to `S_ρ(E)`
and to double the smaller ones; it fixes `S_ρ(E)` and keeps `D½` in place. Extended by the
identity of `X`, it is a deformation of `Z` keeping `X` and `N` in place and pushing `N` into `X`.
So the inclusions `(D_ρ(E), S_ρ(E)) ⟶ (D_ρ(E), D½)` and `(Z, X) ⟶ (Z, N)` induce isomorphisms
(`TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy`). Finally the complement of `X`
lies in the image of `f`, and `N` is open, its complement being the image of the closed set of
vectors of gauge at most `1/2`. So excision for the open cover of `Z` by `N` and the complement of
`X` (`TopPair.isIso_singularHomologyMap_of_open_cover`) makes `(D_ρ(E), D½) ⟶ (Z, N)` an
isomorphism.

## Main results

* `TauCeti.isIso_singularHomologyMap_of_attach_gaugeDiscBundle`: attaching the disc bundle of a
  fibre gauge along its sphere bundle induces isomorphisms `Hₙ(D_ρ(E), S_ρ(E)) ≅ Hₙ(Z, X)`.
* `TauCeti.isIso_singularCohomologyMap_of_attach_gaugeDiscBundle`: the same in cohomology,
  `Hⁿ(Z, X) ≅ Hⁿ(D_ρ(E), S_ρ(E))`.

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

variable {B : Type w} {F : Type*} {E : B → Type w} {ρ : TotalSpace F E → ℝ}

/-! ### The thickened subspace -/

variable (ρ) in
/-- The vectors of the disc bundle of gauge greater than `1/2`. -/
private def outerCollar : Set (gaugeDiscBundle ρ) :=
  {v | 2⁻¹ < ρ v}

private lemma mem_outerCollar {v : gaugeDiscBundle ρ} :
    v ∈ outerCollar ρ ↔ 2⁻¹ < ρ v :=
  Iff.rfl

private lemma sphereBundle_subset_outerCollar :
    Subtype.val ⁻¹' gaugeSphereBundle ρ ⊆ outerCollar ρ := fun v hv ↦ by
  rw [mem_outerCollar, mem_gaugeSphereBundle.1 hv]
  norm_num

section Thickening

variable [TopologicalSpace (TotalSpace F E)] {Z : Type w} [TopologicalSpace Z] {X : Set Z}

variable (φ : C(gaugeDiscBundle ρ, Z)) in
/-- The thickening `X ∪ φ(D½)` of `X` by the outer collar of the attached disc bundle. -/
private def thickening : Set Z :=
  X ∪ φ '' outerCollar ρ

variable {φ : C(gaugeDiscBundle ρ, Z)}

/-- The attached disc bundle meets the thickening exactly in its outer collar. -/
private lemma mem_thickening_iff (hφ : IsClosedEmbedding φ)
    (hφX : ∀ v : gaugeDiscBundle ρ, φ v ∈ X → (v : TotalSpace F E) ∈ gaugeSphereBundle ρ)
    (v : gaugeDiscBundle ρ) :
    φ v ∈ thickening (X := X) φ ↔ v ∈ outerCollar ρ := by
  refine ⟨fun h ↦ h.elim (fun hX ↦ sphereBundle_subset_outerCollar (hφX v hX)) ?_,
    fun h ↦ Or.inr ⟨v, h, rfl⟩⟩
  rintro ⟨w, hw, hwv⟩
  exact hφ.injective hwv ▸ hw

/-- The complement of the thickening is the image of the closed set of vectors of gauge at most
`1/2`, so the thickening is open. -/
private lemma isOpen_thickening (hρ : Continuous ρ) (hφ : IsClosedEmbedding φ)
    (hφX : ∀ v : gaugeDiscBundle ρ, φ v ∈ X → (v : TotalSpace F E) ∈ gaugeSphereBundle ρ)
    (hcover : X ∪ range φ = univ) : IsOpen (thickening (X := X) φ) := by
  have hc : (thickening (X := X) φ)ᶜ = φ '' (outerCollar ρ)ᶜ := by
    ext z
    refine ⟨fun hz ↦ ?_, ?_⟩
    · obtain ⟨v, rfl⟩ : z ∈ range φ :=
        (hcover.symm ▸ mem_univ z : z ∈ X ∪ _).resolve_left fun hzX ↦ hz (Or.inl hzX)
      exact ⟨v, fun hv ↦ hz ((mem_thickening_iff hφ hφX v).2 hv), rfl⟩
    · rintro ⟨v, hv, rfl⟩ hz
      exact hv ((mem_thickening_iff hφ hφX v).1 hz)
  rw [← isClosed_compl_iff, hc]
  exact hφ.isClosedMap _
    (isOpen_lt continuous_const (hρ.comp continuous_subtype_val)).isClosed_compl

/-! ### The collar deformations -/

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  (hρ : IsFiberGauge ρ)

/-- The radial push `TauCeti.radialPush 2⁻¹` applied to the gauge in every fibre of the disc
bundle: at time one it pushes every vector of gauge at least `1/2` out to the sphere bundle and
doubles the smaller ones. -/
private def discCollar : C(I × gaugeDiscBundle ρ, gaugeDiscBundle ρ) where
  toFun p := ⟨TotalSpace.mk' F p.2.1.proj (radialPushScale 2⁻¹ p.1 (ρ p.2) • p.2.1.2), by
    rw [mem_gaugeDiscBundle, hρ.smul_of_nonneg (radialPushScale_nonneg _ _ (hρ.nonneg _)),
      ← radialPush_eq_radialPushScale_mul _ (hρ.nonneg _)]
    exact radialPush_le_one _ (mem_gaugeDiscBundle.1 p.2.2)⟩
  continuous_toFun := by
    have hv : Continuous fun p : I × gaugeDiscBundle ρ ↦ (p.2 : TotalSpace F E) :=
      continuous_subtype_val.comp continuous_snd
    -- The collar rescales each vector by a factor in `[0, 3]`, continuous off the zero section.
    refine Continuous.subtype_mk
      (hv.smul_totalSpace_of_norm_le (C := 3) (fun p ↦ ?_) fun p hp ↦ ?_) _
    · rw [Real.norm_of_nonneg (radialPushScale_nonneg _ _ (hρ.nonneg _))]
      exact (radialPushScale_le (by norm_num) _ _).trans_eq (by norm_num)
    · exact (continuousAt_radialPushScale _ (hρ.pos hp).ne').comp
        (continuousAt_fst.prodMk (hρ.continuous.comp hv).continuousAt)

private lemma coe_discCollar (t : I) (v : gaugeDiscBundle ρ) :
    (discCollar hρ (t, v) : TotalSpace F E) =
      TotalSpace.mk' F v.1.proj (radialPushScale 2⁻¹ t (ρ v) • v.1.2) :=
  rfl

/-- The gauge of the collar deformation is the radial push of the gauge. -/
private lemma apply_discCollar (t : I) (v : gaugeDiscBundle ρ) :
    ρ (discCollar hρ (t, v)) = radialPush (2⁻¹ : ℝ) t (ρ v) := by
  rw [coe_discCollar, hρ.smul_of_nonneg (radialPushScale_nonneg _ t (hρ.nonneg _)),
    radialPush_eq_radialPushScale_mul t (hρ.nonneg _)]

/-- The collar deformation keeps the outer collar in place at every time. -/
private lemma discCollar_mem_outerCollar (t : I) {v : gaugeDiscBundle ρ} (hv : v ∈ outerCollar ρ) :
    discCollar hρ (t, v) ∈ outerCollar ρ := by
  rw [mem_outerCollar, apply_discCollar hρ]
  exact hv.trans_le
    (le_radialPush (by norm_num) (by norm_num) t (hρ.nonneg _) (mem_gaugeDiscBundle.1 v.2))

/-- At time one the collar deformation pushes the outer collar onto the sphere bundle. -/
private lemma discCollar_one_mem_gaugeSphereBundle {v : gaugeDiscBundle ρ}
    (hv : v ∈ outerCollar ρ) : (discCollar hρ (1, v) : TotalSpace F E) ∈ gaugeSphereBundle ρ := by
  rw [mem_gaugeSphereBundle, apply_discCollar hρ]
  exact radialPush_one_eq_one (by norm_num) hv.le

/-- The collar deformation fixes the sphere bundle at every time. -/
private lemma discCollar_of_mem_gaugeSphereBundle (t : I) {v : gaugeDiscBundle ρ}
    (hv : (v : TotalSpace F E) ∈ gaugeSphereBundle ρ) : discCollar hρ (t, v) = v := by
  apply Subtype.ext
  rw [coe_discCollar, mem_gaugeSphereBundle.1 hv,
    radialPushScale_one_right (by norm_num) (by norm_num), one_smul]

/-- At time zero the collar deformation is the identity. -/
private lemma discCollar_zero (v : gaugeDiscBundle ρ) : discCollar hρ (0, v) = v := by
  apply Subtype.ext
  simp [coe_discCollar]

/-- The collar deformation of the disc bundle as a homotopy from the identity. -/
private def discCollarHomotopy :
    (ContinuousMap.id (gaugeDiscBundle ρ)).Homotopy ((discCollar hρ).curry 1) where
  toContinuousMap := discCollar hρ
  map_zero_left := discCollar_zero hρ
  map_one_left _ := rfl

private lemma discCollarHomotopy_apply (p : I × gaugeDiscBundle ρ) :
    discCollarHomotopy hρ p = discCollar hρ p :=
  rfl

/-- The collar deformation of the disc bundle, transported to its image in `Z` and extended by the
identity of `X`: the gluing of the projection `I × X → Z` and `φ ∘ discCollar` along the closed
embeddings of `I × X` and `I × D_ρ(E)` into `I × Z`. -/
private def attachCollar (hφ : IsClosedEmbedding φ) (hX : IsClosed X)
    (hφX : ∀ v : gaugeDiscBundle ρ, φ v ∈ X → (v : TotalSpace F E) ∈ gaugeSphereBundle ρ)
    (hcover : X ∪ range φ = univ) : C(I × Z, Z) :=
  ContinuousMap.glueClosedEmbeddings (i := Prod.map id ((↑) : X → Z)) (j := Prod.map id φ)
    ⟨fun p ↦ p.2, by fun_prop⟩ (φ.comp (discCollar hρ))
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
        discCollar_of_mem_gaugeSphereBundle hρ t (hφX v (hx ▸ x.2))]
      exact hx)

variable (hφ : IsClosedEmbedding φ) (hX : IsClosed X)
  (hφX : ∀ v : gaugeDiscBundle ρ, φ v ∈ X → (v : TotalSpace F E) ∈ gaugeSphereBundle ρ)
  (hcover : X ∪ range φ = univ)

private lemma attachCollar_apply (t : I) (v : gaugeDiscBundle ρ) :
    attachCollar hρ hφ hX hφX hcover (t, φ v) = φ (discCollar hρ (t, v)) :=
  ContinuousMap.glueClosedEmbeddings_apply_right _ _ _ _ _ _ (t, v)

private lemma attachCollar_of_mem (t : I) {z : Z} (hz : z ∈ X) :
    attachCollar hρ hφ hX hφX hcover (t, z) = z :=
  ContinuousMap.glueClosedEmbeddings_apply_left _ _ _ _ _ _ (t, (⟨z, hz⟩ : X))

/-- The collar deformation of the attached space as a homotopy from the identity. -/
private def attachCollarHomotopy :
    (ContinuousMap.id Z).Homotopy ((attachCollar hρ hφ hX hφX hcover).curry 1) where
  toContinuousMap := attachCollar hρ hφ hX hφX hcover
  map_zero_left z := by
    obtain hz | ⟨v, rfl⟩ := (hcover.symm ▸ mem_univ z : z ∈ X ∪ range φ)
    · exact attachCollar_of_mem hρ hφ hX hφX hcover 0 hz
    · exact (attachCollar_apply hρ hφ hX hφX hcover 0 v).trans
        (congrArg φ (discCollar_zero hρ v))
  map_one_left _ := rfl

private lemma attachCollarHomotopy_apply (p : I × Z) :
    attachCollarHomotopy hρ hφ hX hφX hcover p = attachCollar hρ hφ hX hφX hcover p :=
  rfl

/-! ### The deformations as maps of pairs -/

private lemma discCollarHomotopy_mem_gaugeSphereBundle (t : I) {v : gaugeDiscBundle ρ}
    (hv : (v : TotalSpace F E) ∈ gaugeSphereBundle ρ) :
    (discCollarHomotopy hρ (t, v) : TotalSpace F E) ∈ gaugeSphereBundle ρ := by
  rwa [discCollarHomotopy_apply, discCollar_of_mem_gaugeSphereBundle hρ t hv]

private lemma discCollarHomotopy_mem_outerCollar (t : I) {v : gaugeDiscBundle ρ}
    (hv : v ∈ outerCollar ρ) : discCollarHomotopy hρ (t, v) ∈ outerCollar ρ := by
  rw [discCollarHomotopy_apply]
  exact discCollar_mem_outerCollar hρ t hv

private lemma attachCollarHomotopy_mem (t : I) {z : Z} (hz : z ∈ X) :
    attachCollarHomotopy hρ hφ hX hφX hcover (t, z) ∈ X := by
  rwa [attachCollarHomotopy_apply, attachCollar_of_mem hρ hφ hX hφX hcover t hz]

private lemma attachCollarHomotopy_mem_thickening (t : I) {z : Z}
    (hz : z ∈ thickening (X := X) φ) :
    attachCollarHomotopy hρ hφ hX hφX hcover (t, z) ∈ thickening (X := X) φ := by
  rw [attachCollarHomotopy_apply]
  obtain hz | ⟨v, hv, rfl⟩ := hz
  · rw [attachCollar_of_mem hρ hφ hX hφX hcover t hz]
    exact Or.inl hz
  · rw [attachCollar_apply]
    exact Or.inr ⟨_, discCollar_mem_outerCollar hρ t hv, rfl⟩

private lemma mapsTo_attachCollar_thickening
    (hφS : ∀ v : gaugeDiscBundle ρ, (v : TotalSpace F E) ∈ gaugeSphereBundle ρ → φ v ∈ X) :
    MapsTo ((attachCollar hρ hφ hX hφX hcover).curry 1) (thickening (X := X) φ) X := by
  rintro z (hz | ⟨v, hv, rfl⟩)
  · rw [ContinuousMap.curry_apply, attachCollar_of_mem hρ hφ hX hφX hcover 1 hz]
    exact hz
  · rw [ContinuousMap.curry_apply, attachCollar_apply]
    exact hφS _ (discCollar_one_mem_gaugeSphereBundle hρ hv)

end Thickening

/-! ### The comparison square -/

section Square

variable [TopologicalSpace (TotalSpace F E)] {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  (φ : C(gaugeDiscBundle ρ, Z))

variable (ρ) in
/-- The inclusion `(D_ρ(E), S_ρ(E)) ⟶ (D_ρ(E), D½)`. -/
private def sphereToOuterCollar :
    TopPair.ofSubset (X := TopCat.of (gaugeDiscBundle ρ)) (Subtype.val ⁻¹' gaugeSphereBundle ρ) ⟶
      TopPair.ofSubset (X := TopCat.of (gaugeDiscBundle ρ)) (outerCollar ρ) :=
  TopPair.ofSubsetMap (𝟙 _) fun _ hv ↦ sphereBundle_subset_outerCollar hv

/-- The inclusion `(Z, X) ⟶ (Z, N)`. -/
private def subsetToThickening :
    TopPair.ofSubset (X := TopCat.of Z) X ⟶
      TopPair.ofSubset (X := TopCat.of Z) (thickening (X := X) φ) :=
  TopPair.ofSubsetMap (𝟙 _) fun _ hz ↦ Or.inl hz

/-- The map `(D_ρ(E), D½) ⟶ (Z, N)` induced by the attachment. -/
private def outerCollarToThickening :
    TopPair.ofSubset (X := TopCat.of (gaugeDiscBundle ρ)) (outerCollar ρ) ⟶
      TopPair.ofSubset (X := TopCat.of Z) (thickening (X := X) φ) :=
  TopPair.ofSubsetMap (TopCat.ofHom φ) fun v hv ↦ Or.inr ⟨v, hv, rfl⟩

private lemma fst_sphereToOuterCollar : TopPair.Hom.fst (sphereToOuterCollar ρ) = 𝟙 _ :=
  TopPair.ofSubsetMap_fst _ _

private lemma fst_subsetToThickening :
    TopPair.Hom.fst (subsetToThickening (X := X) φ) = 𝟙 _ :=
  TopPair.ofSubsetMap_fst _ _

private lemma fst_outerCollarToThickening :
    TopPair.Hom.fst (outerCollarToThickening (X := X) φ) = TopCat.ofHom φ :=
  TopPair.ofSubsetMap_fst _ _

variable (ρ) in
/-- The isomorphism of the disc-sphere pair with the pair `(D_ρ(E), S_ρ(E))` presented as a subset
of `D_ρ(E)`. -/
private abbrev discSpherePairIso :
    TopPair.ofSubset (X := TopCat.of (gaugeDiscBundle ρ)) (Subtype.val ⁻¹' gaugeSphereBundle ρ) ≅
      gaugeDiscSpherePair ρ :=
  TopPair.ofSubsetPreimageValIso (X := TopCat.of (TotalSpace F E))
    (gaugeSphereBundle_subset_gaugeDiscBundle ρ)

/-- The comparison square: `(D_ρ(E), S_ρ(E)) ⟶ (Z, X) ⟶ (Z, N)` agrees with
`(D_ρ(E), S_ρ(E)) ⟶ (D_ρ(E), D½) ⟶ (Z, N)`. -/
private lemma comp_subsetToThickening_eq
    {f : gaugeDiscSpherePair ρ ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
    (hfφ : TopPair.Hom.fst f = TopCat.ofHom φ) :
    f ≫ subsetToThickening φ =
      (discSpherePairIso ρ).inv ≫ sphereToOuterCollar ρ ≫ outerCollarToThickening φ := by
  refine TopPair.hom_ext_of_fst _ ?_
  have hinv : TopPair.Hom.fst (discSpherePairIso ρ).inv = 𝟙 _ :=
    TopCat.ext fun x ↦ TopPair.ofSubsetPreimageValIso_inv_fst_apply x
  rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, hfφ, hinv,
    fst_outerCollarToThickening, fst_subsetToThickening, fst_sphereToOuterCollar]
  -- The identities are those of `TopCat.of Z` and `TopCat.of D_ρ(E)`, which `Category.comp_id` does
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

variable {φ}

private lemma isOpen_thickeningCover (hρ : Continuous ρ)
    (hφ : IsClosedEmbedding φ) (hX : IsClosed X)
    (hφX : ∀ v : gaugeDiscBundle ρ, φ v ∈ X → (v : TotalSpace F E) ∈ gaugeSphereBundle ρ)
    (hcover : X ∪ range φ = univ) (b : Bool) : IsOpen (thickeningCover (X := X) φ b) := by
  cases b
  · exact hX.isOpen_compl
  · exact isOpen_thickening hρ hφ hφX hcover

private lemma thickeningCover_subset (hcover : X ∪ range φ = univ) (b : Bool) :
    thickeningCover (X := X) φ b ⊆
        Set.range (TopPair.ofSubset (X := TopCat.of Z) (thickening (X := X) φ)).map ∨
      thickeningCover (X := X) φ b ⊆
        Set.range (TopPair.Hom.fst (outerCollarToThickening (X := X) φ)) := by
  rw [fst_outerCollarToThickening]
  cases b
  · exact Or.inr fun z hz ↦ (hcover.symm ▸ mem_univ z : z ∈ X ∪ _).resolve_left hz
  · exact Or.inl (TopPair.range_ofSubset_map (X := TopCat.of Z) (B := thickening (X := X) φ)).ge

private lemma isEmbedding_fst_outerCollarToThickening (hφ : IsClosedEmbedding φ) :
    IsEmbedding (TopPair.Hom.fst (outerCollarToThickening (X := X) φ)) := by
  rw [fst_outerCollarToThickening]
  exact hφ.isEmbedding

private lemma mem_range_of_fst_outerCollarToThickening_mem (hφ : IsClosedEmbedding φ)
    (hφX : ∀ v : gaugeDiscBundle ρ, φ v ∈ X → (v : TotalSpace F E) ∈ gaugeSphereBundle ρ)
    (v : gaugeDiscBundle ρ)
    (hv : TopPair.Hom.fst (outerCollarToThickening (X := X) φ) v ∈
      Set.range (TopPair.ofSubset (X := TopCat.of Z) (thickening (X := X) φ)).map) :
    v ∈ Set.range (TopPair.ofSubset (X := TopCat.of (gaugeDiscBundle ρ)) (outerCollar ρ)).map := by
  rw [fst_outerCollarToThickening] at hv
  refine (TopPair.range_ofSubset_map (X := TopCat.of (gaugeDiscBundle ρ))
    (B := outerCollar ρ)).ge ?_
  exact (mem_thickening_iff hφ hφX v).1
    ((TopPair.range_ofSubset_map (X := TopCat.of Z) (B := thickening (X := X) φ)).le hv)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
  (k : Type*) [Ring k] [Linear k C] (M : C)

private lemma isIso_singularHomologyMap_outerCollarToThickening
    (hρ : Continuous ρ)
    (hφ : IsClosedEmbedding φ) (hX : IsClosed X)
    (hφX : ∀ v : gaugeDiscBundle ρ, φ v ∈ X → (v : TotalSpace F E) ∈ gaugeSphereBundle ρ)
    (hcover : X ∪ range φ = univ) :
    IsIso (TopPair.singularHomologyMap (outerCollarToThickening (X := X) φ) R n) :=
  TopPair.isIso_singularHomologyMap_of_open_cover R _ (isEmbedding_fst_outerCollarToThickening hφ)
    (mem_range_of_fst_outerCollarToThickening_mem hφ hφX) _
    (isOpen_thickeningCover hρ hφ hX hφX hcover) (iUnion_thickeningCover φ)
    (thickeningCover_subset hcover) n

private lemma isIso_singularCohomologyMap_outerCollarToThickening
    (hρ : Continuous ρ)
    (hφ : IsClosedEmbedding φ) (hX : IsClosed X)
    (hφX : ∀ v : gaugeDiscBundle ρ, φ v ∈ X → (v : TotalSpace F E) ∈ gaugeSphereBundle ρ)
    (hcover : X ∪ range φ = univ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (outerCollarToThickening (X := X) φ) n) :=
  TopPair.isIso_singularCohomologyMap_of_open_cover _
    (isEmbedding_fst_outerCollarToThickening hφ)
    (mem_range_of_fst_outerCollarToThickening_mem hφ hφX) _
    (isOpen_thickeningCover hρ hφ hX hφX hcover) (iUnion_thickeningCover φ)
    (thickeningCover_subset hcover) n

end Square

/-! ### Attaching a disc bundle -/

section Attach

variable [TopologicalSpace (TotalSpace F E)] {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : gaugeDiscSpherePair ρ ⟶ TopPair.ofSubset (X := TopCat.of Z) X}

/-- A map of pairs out of the disc-sphere pair carries the sphere bundle into the subspace. -/
private lemma fst_mem_of_mem_gaugeSphereBundle {v : gaugeDiscBundle ρ}
    (hv : (v : TotalSpace F E) ∈ gaugeSphereBundle ρ) : TopPair.Hom.fst f v ∈ X := by
  have h : TopPair.Hom.fst f v =
      (TopPair.ofSubset (X := TopCat.of Z) X).map (TopPair.Hom.snd f ⟨v.1, hv⟩) :=
    (TopPair.Hom.w_apply f ⟨v.1, hv⟩).symm
  rw [h]
  exact (TopPair.Hom.snd f ⟨v.1, hv⟩).2

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

section HomotopyIso

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
  (k : Type*) [Ring k] [Linear k C] (M : C)

private lemma isIso_singularHomologyMap_sphereToOuterCollar
    (hρ : IsFiberGauge ρ) :
    IsIso (TopPair.singularHomologyMap (sphereToOuterCollar ρ) R n) :=
  TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy _ (discCollarHomotopy hρ)
    (fun τ _ hv ↦ discCollarHomotopy_mem_gaugeSphereBundle hρ τ hv)
    (fun τ _ hv ↦ discCollarHomotopy_mem_outerCollar hρ τ hv)
    (fun _ hv ↦ discCollar_one_mem_gaugeSphereBundle hρ hv) R n

private lemma isIso_singularCohomologyMap_sphereToOuterCollar
    (hρ : IsFiberGauge ρ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (sphereToOuterCollar ρ) n) :=
  TopPair.isIso_singularCohomologyMap_ofSubsetMap_id_of_homotopy _ (discCollarHomotopy hρ)
    (fun τ _ hv ↦ discCollarHomotopy_mem_gaugeSphereBundle hρ τ hv)
    (fun τ _ hv ↦ discCollarHomotopy_mem_outerCollar hρ τ hv)
    (fun _ hv ↦ discCollar_one_mem_gaugeSphereBundle hρ hv) R k M n

private lemma isIso_singularHomologyMap_subsetToThickening {φ : C(gaugeDiscBundle ρ, Z)}
    (hρ : IsFiberGauge ρ)
    (hφ : IsClosedEmbedding φ) (hX : IsClosed X)
    (hφX : ∀ v : gaugeDiscBundle ρ, φ v ∈ X → (v : TotalSpace F E) ∈ gaugeSphereBundle ρ)
    (hφS : ∀ v : gaugeDiscBundle ρ, (v : TotalSpace F E) ∈ gaugeSphereBundle ρ → φ v ∈ X)
    (hcover : X ∪ range φ = univ) :
    IsIso (TopPair.singularHomologyMap (subsetToThickening (X := X) φ) R n) :=
  TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy _
    (attachCollarHomotopy hρ hφ hX hφX hcover)
    (fun τ _ hz ↦ attachCollarHomotopy_mem hρ hφ hX hφX hcover τ hz)
    (fun τ _ hz ↦ attachCollarHomotopy_mem_thickening hρ hφ hX hφX hcover τ hz)
    (mapsTo_attachCollar_thickening hρ hφ hX hφX hcover hφS) R n

private lemma isIso_singularCohomologyMap_subsetToThickening {φ : C(gaugeDiscBundle ρ, Z)}
    (hρ : IsFiberGauge ρ)
    (hφ : IsClosedEmbedding φ) (hX : IsClosed X)
    (hφX : ∀ v : gaugeDiscBundle ρ, φ v ∈ X → (v : TotalSpace F E) ∈ gaugeSphereBundle ρ)
    (hφS : ∀ v : gaugeDiscBundle ρ, (v : TotalSpace F E) ∈ gaugeSphereBundle ρ → φ v ∈ X)
    (hcover : X ∪ range φ = univ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (subsetToThickening (X := X) φ) n) :=
  TopPair.isIso_singularCohomologyMap_ofSubsetMap_id_of_homotopy _
    (attachCollarHomotopy hρ hφ hX hφX hcover)
    (fun τ _ hz ↦ attachCollarHomotopy_mem hρ hφ hX hφX hcover τ hz)
    (fun τ _ hz ↦ attachCollarHomotopy_mem_thickening hρ hφ hX hφX hcover τ hz)
    (mapsTo_attachCollar_thickening hρ hφ hX hφX hcover hφS) R k M n

end HomotopyIso

/-- **Attaching a disc bundle induces isomorphisms on relative homology.** Let `ρ` be a fibre gauge
on a real vector bundle `E → B`, for instance a fibre norm which is continuous on the total space,
and let `f : (D_ρ(E), S_ρ(E)) ⟶ (Z, X)` be a map of pairs with `X` closed in `Z`. Suppose that `f`
is a closed embedding of `D_ρ(E)` into `Z` sending a point into `X` only if it lies in `S_ρ(E)`,
and that `X` together with the image of `f` is all of `Z`: the space `Z` is obtained from `X` by
attaching `D_ρ(E)` along `S_ρ(E)`. Then `f` induces isomorphisms `Hₙ(D_ρ(E), S_ρ(E)) ≅ Hₙ(Z, X)` on
relative singular homology, with coefficients in any abelian category with coproducts, in every
degree. -/
theorem isIso_singularHomologyMap_of_attach_gaugeDiscBundle
    (hρ : IsFiberGauge ρ) (hX : IsClosed X)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
    (hf : IsClosedEmbedding (TopPair.Hom.fst f))
    (hfX : ∀ v : gaugeDiscBundle ρ,
      TopPair.Hom.fst f v ∈ X → (v : TotalSpace F E) ∈ gaugeSphereBundle ρ)
    (hfcover : X ∪ range (TopPair.Hom.fst f) = univ) :
    IsIso (TopPair.singularHomologyMap f R n) := by
  let φ : C(gaugeDiscBundle ρ, Z) := (TopPair.Hom.fst f).hom
  have := isIso_singularHomologyMap_sphereToOuterCollar R n hρ
  have := isIso_singularHomologyMap_outerCollarToThickening (φ := φ) R n hρ.continuous hf hX hfX
    hfcover
  have := isIso_singularHomologyMap_subsetToThickening (φ := φ) R n hρ hf hX hfX
    (fun _ hv ↦ fst_mem_of_mem_gaugeSphereBundle hv) hfcover
  have := TopPair.isIso_singularHomologyMap (discSpherePairIso ρ).inv (discSpherePairIso ρ).hom
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

/-- **Attaching a disc bundle induces isomorphisms on relative cohomology.** Under the hypotheses
of `TauCeti.isIso_singularHomologyMap_of_attach_gaugeDiscBundle`, the map of pairs
`f : (D_ρ(E), S_ρ(E)) ⟶ (Z, X)` induces isomorphisms `Hⁿ(Z, X) ≅ Hⁿ(D_ρ(E), S_ρ(E))` on relative
singular cohomology, with arbitrary coefficients, in every degree. -/
theorem isIso_singularCohomologyMap_of_attach_gaugeDiscBundle
    (hρ : IsFiberGauge ρ) (hX : IsClosed X)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
    (k : Type*) [Ring k] [Linear k C] (M : C)
    (hf : IsClosedEmbedding (TopPair.Hom.fst f))
    (hfX : ∀ v : gaugeDiscBundle ρ,
      TopPair.Hom.fst f v ∈ X → (v : TotalSpace F E) ∈ gaugeSphereBundle ρ)
    (hfcover : X ∪ range (TopPair.Hom.fst f) = univ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n) := by
  let φ : C(gaugeDiscBundle ρ, Z) := (TopPair.Hom.fst f).hom
  have := isIso_singularCohomologyMap_sphereToOuterCollar R n k M hρ
  have := isIso_singularCohomologyMap_outerCollarToThickening (φ := φ) R n k M hρ.continuous hf hX
    hfX hfcover
  have := isIso_singularCohomologyMap_subsetToThickening (φ := φ) R n k M hρ hf hX hfX
    (fun _ hv ↦ fst_mem_of_mem_gaugeSphereBundle hv) hfcover
  have := TopPair.isIso_singularCohomologyMap (discSpherePairIso ρ).inv
    (discSpherePairIso ρ).hom (by rw [Iso.inv_hom_id]; exact TopPair.Homotopy.refl _)
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
