/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Additivity.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Attach
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import TauCeti.Analysis.Normed.Module.Ball.Radial.Push
import TauCeti.Topology.ContinuousMap.Glue.ClosedEmbeddings
import TauCeti.Topology.ContinuousMap.Sigma
import TauCeti.Topology.Homotopy.Sigma
import TauCeti.Topology.VectorBundle.Smul

/-!
# Attaching disc bundles

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

The same holds for finitely many disc bundles attached at once, along closed embeddings with
pairwise disjoint images, the bundles having possibly different bases, ranks and gauges: the
relative homology of `(Z, X)` is the coproduct of the relative homologies of the disc-sphere pairs
(`TauCeti.isColimitCofanSingularHomologyOfAttachGaugeDiscBundle`), and its relative cohomology is
their product (`TauCeti.isLimitFanSingularCohomologyOfAttachGaugeDiscBundle`), the structure maps
being induced by the attaching maps.

This is how attachments of disc bundles are seen by homology. For instance, crossing a critical
level of a Morse–Bott function attaches, up to homotopy, the negative disc bundle of each critical
submanifold on the level to the sublevel below it. The critical submanifolds on one level may have
different dimensions and indices, so their negative normal bundles have different bases and
ranks; with `X` the lower sublevel and `Z` its union with the attached disc bundles, the relative
homology of the attachment is the sum over the critical submanifolds of the relative homologies of
their disc-sphere pairs, which are those of the Thom pairs of the negative normal bundles. There
each attached disc bundle is cut out by the normal Hessian, `{-½ Hess(v, v) ≤ ε}`, which is the
disc bundle of the gauge `v ↦ √(-Hess(v, v) / (2ε))` rather than the unit disc bundle of a norm
carried by the fibres. The unit disc bundle `D(E)` of a fibre norm is the case `ρ v = ‖v‖`
(`TauCeti.isFiberGauge_norm`). The rank zero case is included: there `S_ρ(E)` is empty, `D_ρ(E)`
is `E` and `Z` is the disjoint union of `X` and a copy of the base.

The proofs apply the comparison for attachments along a subspace with a deformation neighbourhood
(`TopPair.isIso_singularHomologyMap_of_attach`, `TopPair.isIso_singularCohomologyMap_of_attach`).
Its neighbourhood of `S_ρ(E)` in `D_ρ(E)` is the set `D½` of vectors of gauge greater than `1/2`,
and its deformation is the radial push `TauCeti.radialPush 2⁻¹`, applied to the gauge in every
fibre of `D_ρ(E)`: it pushes every vector of gauge at least `1/2` out to `S_ρ(E)` and doubles the
smaller ones, it fixes `S_ρ(E)` and keeps `D½` in place. For several disc bundles the attaching
maps glue to a closed embedding of the disjoint union of the disc bundles
(`ContinuousMap.isClosedEmbedding_sigma`), the radial push runs on every summand, and additivity of
relative homology (`TopPair.isColimitCofanSingularHomology`) and cohomology
(`TopPair.isLimitFanSingularCohomology`) splits the disjoint union of the disc-sphere pairs.

More generally, if a space `T` strong deformation retracts onto a closed subset `A` with a disc
bundle attached along `S_ρ(E)` by a closed embedding of `D_ρ(E)` into `T`, then the relative
homology and cohomology of `(T, A)` are those of `(D_ρ(E), S_ρ(E))`
(`TauCeti.exists_isIso_singularHomologyMap_of_homotopyRel_attach_discBundle` and
`TauCeti.exists_isIso_singularCohomologyMap_of_homotopyRel_attach_discBundle`): the retraction
identifies `(T, A)` with the attachment, to which the results above apply.

## Main results

* `TauCeti.isIso_singularHomologyMap_of_attach_gaugeDiscBundle`: attaching the disc bundle of a
  fibre gauge along its sphere bundle induces isomorphisms `Hₙ(D_ρ(E), S_ρ(E)) ≅ Hₙ(Z, X)`.
* `TauCeti.isIso_singularCohomologyMap_of_attach_gaugeDiscBundle`: the same in cohomology,
  `Hⁿ(Z, X) ≅ Hⁿ(D_ρ(E), S_ρ(E))`.
* `TauCeti.exists_isIso_singularHomologyMap_of_homotopyRel_attach_discBundle`: a space which
  strong deformation retracts onto a subset with a disc bundle attached has the relative homology
  of the disc-sphere pair.
* `TauCeti.exists_isIso_singularCohomologyMap_of_homotopyRel_attach_discBundle`: the same in
  cohomology.
* `TauCeti.exists_isIso_of_homotopyRel_attach_discBundle`: both, through a single map of pairs.
* `TauCeti.isColimitCofanSingularHomologyOfAttachGaugeDiscBundle`: attaching finitely many disc
  bundles `D_ρₐ(Eₐ)` along their sphere bundles with disjoint images gives
  `Hₙ(Z, X) ≅ ∐ₐ Hₙ(D_ρₐ(Eₐ), S_ρₐ(Eₐ))`.
* `TauCeti.isLimitFanSingularCohomologyOfAttachGaugeDiscBundle`: the same in cohomology,
  `Hⁿ(Z, X) ≅ ∏ₐ Hⁿ(D_ρₐ(Eₐ), S_ρₐ(Eₐ))`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, Proposition 2.22 and its proof (good pairs and excision).
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261, for the
  attachment of the negative disc bundles of several critical submanifolds on one level.
-/

public section

noncomputable section

open Bundle CategoryTheory Function Limits Set Topology
open scoped unitInterval

universe w v u

namespace TauCeti

/-! ### The radial push in the fibres of a disc bundle -/

section Collar

variable {B : Type w} {F : Type*} {E : B → Type w} {ρ : TotalSpace F E → ℝ}

variable (ρ) in
/-- The vectors of the disc bundle of gauge greater than `1/2`. -/
private def outerCollar : Set (gaugeDiscBundle ρ) :=
  {v | 2⁻¹ < ρ v}

private lemma mem_outerCollar {v : gaugeDiscBundle ρ} :
    v ∈ outerCollar ρ ↔ 2⁻¹ < ρ v :=
  Iff.rfl

variable [TopologicalSpace (TotalSpace F E)]

/-- The subspace of the disc-sphere pair, as the range of its embedding, consists of the vectors of
the sphere bundle. -/
private lemma mem_range_gaugeDiscSpherePair_map {v : gaugeDiscBundle ρ} :
    v ∈ range (gaugeDiscSpherePair ρ).map ↔ (v : TotalSpace F E) ∈ gaugeSphereBundle ρ := by
  rw [TopPair.range_ofInclusion_map]
  exact mem_preimage

private lemma range_gaugeDiscSpherePair_map_subset_outerCollar :
    range (gaugeDiscSpherePair ρ).map ⊆ outerCollar ρ := fun v hv ↦ mem_outerCollar.2 (by
  rw [mem_gaugeSphereBundle.1 (mem_range_gaugeDiscSpherePair_map.1 hv)]
  norm_num)

private lemma isOpen_outerCollar (hρ : Continuous ρ) : IsOpen (outerCollar ρ) :=
  isOpen_lt continuous_const (hρ.comp continuous_subtypeVal)

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  (hρ : IsFiberGauge ρ)

/-- The radial push `TauCeti.radialPush 2⁻¹` applied to the gauge in every fibre of the disc
bundle: at time one it pushes every vector of gauge at least `1/2` out to the sphere bundle and
doubles the smaller ones. -/
private def discCollar : C(I × gaugeDiscBundle ρ, gaugeDiscBundle ρ) where
  toFun p := ⟨TotalSpace.mk' F p.2.val.proj (radialPushScale 2⁻¹ p.1 (ρ p.2) • p.2.val.snd), by
    rw [mem_gaugeDiscBundle, hρ.smul_of_nonneg (radialPushScale_nonneg _ _ (hρ.nonneg _)),
      ← radialPush_eq_radialPushScale_mul _ (hρ.nonneg _)]
    exact radialPush_le_one _ (mem_gaugeDiscBundle.1 p.2.property)⟩
  continuous_toFun := by
    have hv : Continuous fun p : I × gaugeDiscBundle ρ ↦ (p.2 : TotalSpace F E) :=
      continuous_subtypeVal.comp continuous_snd
    -- The collar rescales each vector by a factor in `[0, 3]`, continuous off the zero section.
    refine Continuous.subtype_mk
      (hv.smul_totalSpace_of_norm_le (C := 3) (fun p ↦ ?_) fun p hp ↦ ?_) _
    · rw [Real.norm_of_nonneg (radialPushScale_nonneg _ _ (hρ.nonneg _))]
      exact (radialPushScale_le (by norm_num) _ _).trans_eq (by norm_num)
    · exact (continuousAt_radialPushScale _ (hρ.pos hp).ne').comp
        (continuousAt_fst.prodMk (hρ.continuous.comp hv).continuousAt)

private lemma coe_discCollar (t : I) (v : gaugeDiscBundle ρ) :
    (discCollar hρ (t, v) : TotalSpace F E) =
      TotalSpace.mk' F v.val.proj (radialPushScale 2⁻¹ t (ρ v) • v.val.snd) :=
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
    (le_radialPush (by norm_num) (by norm_num) t (hρ.nonneg _) (mem_gaugeDiscBundle.1 v.property))

/-- At time one the collar deformation pushes the outer collar onto the sphere bundle. -/
private lemma discCollar_one_mem_range {v : gaugeDiscBundle ρ} (hv : v ∈ outerCollar ρ) :
    discCollar hρ (1, v) ∈ range (gaugeDiscSpherePair ρ).map := by
  rw [mem_range_gaugeDiscSpherePair_map, mem_gaugeSphereBundle, apply_discCollar hρ]
  exact radialPush_one_eq_one (by norm_num) hv.le

/-- The collar deformation fixes the sphere bundle at every time. -/
private lemma discCollar_of_mem_range (t : I) {v : gaugeDiscBundle ρ}
    (hv : v ∈ range (gaugeDiscSpherePair ρ).map) : discCollar hρ (t, v) = v := by
  apply Subtype.ext
  rw [coe_discCollar, mem_gaugeSphereBundle.1 (mem_range_gaugeDiscSpherePair_map.1 hv),
    radialPushScale_one_right (by norm_num) (by norm_num), one_smul]

/-- At time zero the collar deformation is the identity. -/
private lemma discCollar_zero (v : gaugeDiscBundle ρ) : discCollar hρ (0, v) = v := by
  apply Subtype.ext
  simp [coe_discCollar]

end Collar

/-! ### Attaching a disc bundle -/

section Attach

variable {B : Type w} {F : Type*} {E : B → Type w} {ρ : TotalSpace F E → ℝ}
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace B] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : gaugeDiscSpherePair ρ ⟶ TopPair.ofSubset (X := TopCat.of Z) X}

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
    IsIso (TopPair.singularHomologyMap f R n) :=
  TopPair.isIso_singularHomologyMap_of_attach R n f hX hf
    (fun v hv ↦ mem_range_gaugeDiscSpherePair_map.2 (hfX v hv)) hfcover
    (isOpen_outerCollar hρ.continuous) range_gaugeDiscSpherePair_map_subset_outerCollar
    (discCollar hρ) (discCollar_zero hρ) (fun t _ ↦ discCollar_of_mem_range hρ t)
    (fun t _ ↦ discCollar_mem_outerCollar hρ t) (fun _ ↦ discCollar_one_mem_range hρ)

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
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n) :=
  TopPair.isIso_singularCohomologyMap_of_attach R k M n f hX hf
    (fun v hv ↦ mem_range_gaugeDiscSpherePair_map.2 (hfX v hv)) hfcover
    (isOpen_outerCollar hρ.continuous) range_gaugeDiscSpherePair_map_subset_outerCollar
    (discCollar hρ) (discCollar_zero hρ) (fun t _ ↦ discCollar_of_mem_range hρ t)
    (fun t _ ↦ discCollar_mem_outerCollar hρ t) (fun _ ↦ discCollar_one_mem_range hρ)

end Attach

/-! ### Deformation retracts with an attached disc bundle -/

section Deformation

variable {B : Type w} {F : Type*} {E : B → Type w} {ρ : TotalSpace F E → ℝ}
variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℝ F E] {Y : Type w} [TopologicalSpace Y] {A T D : Set Y}
  {g : TotalSpace F E → Y}

/-- Attaching a disc bundle, for subsets of an ambient space: if `g` restricts to a closed
embedding of `D_ρ(E)` with image `D`, sending a point of `D_ρ(E)` into the closed set `A` exactly
when it lies in `S_ρ(E)`, then for `A ⊆ Z ⊆ A ∪ D` with `D ⊆ Z` the map of pairs
`(D_ρ(E), S_ρ(E)) ⟶ (Z, A)` induced by `g` is an isomorphism on relative homology and
cohomology. -/
private lemma exists_isIso_attach_discBundle_subset
    (hρ : IsFiberGauge ρ) (hA : IsClosed A) {Z : Set Y}
    (hAZ : A ⊆ Z) (hDZ : D ⊆ Z) (hZ : Z ⊆ A ∪ D)
    (hg : IsClosedEmbedding ((gaugeDiscBundle ρ).domRestrict g)) (hgD : g '' gaugeDiscBundle ρ = D)
    (hgA : ∀ v ∈ gaugeDiscBundle ρ, g v ∈ A ↔ v ∈ gaugeSphereBundle ρ) :
    ∃ ψ : gaugeDiscSpherePair ρ ⟶ TopPair.ofInclusion (X := TopCat.of Y) hAZ,
      (∀ v : gaugeDiscBundle ρ, Subtype.val (TopPair.Hom.fst ψ v) = g v) ∧
      (∀ {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ),
        IsIso (TopPair.singularHomologyMap ψ R n)) ∧
      ∀ {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
        (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ),
        IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) ψ n) := by
  have hgZ (v : gaugeDiscBundle ρ) : g v ∈ Z := hDZ (hgD ▸ mem_image_of_mem g v.property)
  -- The corestriction `φ` of `g` attaches the disc bundle to `A` inside `Z`.
  let φ : C(gaugeDiscBundle ρ, Z) := ⟨fun v ↦ ⟨g v, hgZ v⟩, hg.continuous.subtype_mk _⟩
  have hmem {x : Z} (hx : (x : Y) ∈ D) : ∃ v : gaugeDiscBundle ρ, φ v = x := by
    obtain ⟨v, hv, hvx⟩ := (hgD ▸ hx : (x : Y) ∈ g '' gaugeDiscBundle ρ)
    exact ⟨⟨v, hv⟩, Subtype.ext hvx⟩
  have hφ : IsClosedEmbedding φ := by
    refine (isClosedEmbedding_iff _).2 ⟨(IsEmbedding.subtypeVal.of_comp_iff).1 hg.isEmbedding, ?_⟩
    have hrange : range φ = Subtype.val ⁻¹' D :=
      Subset.antisymm (range_subset_iff.2 fun v ↦ hgD ▸ mem_image_of_mem g v.property) fun _ hx ↦
          hmem hx
    rw [hrange]
    have hD : IsClosed D := hgD ▸ range_domRestrict g _ ▸ hg.isClosed_range
    exact hD.preimage continuous_subtypeVal
  have hφA (v : gaugeDiscBundle ρ) (hv : (v : TotalSpace F E) ∈ gaugeSphereBundle ρ) :
      (φ v : Y) ∈ A :=
    (hgA v v.property).2 hv
  let ψ := TopPair.ofInclusionMap (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of Y)
    (gaugeSphereBundle_subset_gaugeDiscBundle ρ) hAZ φ hφA
  have hψ (v : gaugeDiscBundle ρ) : TopPair.Hom.fst ψ v = φ v :=
    TopPair.ofInclusionMap_fst_apply (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of Y)
      (hst := gaugeSphereBundle_subset_gaugeDiscBundle ρ) (hst' := hAZ) φ hφA v
  -- Presented as a map into the pair `(Z, A)` of a subset of `Z`, `ψ` attaches a disc bundle.
  let e := TopPair.ofSubsetPreimageValIso (X := TopCat.of Y) hAZ
  have hfst : TopPair.Hom.fst (ψ ≫ e.inv) = TopCat.ofHom φ := by
    ext v
    rw [TopPair.Hom.fst_comp, TopCat.comp_app]
    exact (TopPair.ofSubsetPreimageValIso_inv_fst_apply (X := TopCat.of Y) (hst := hAZ) _).trans
      (hψ v)
  have hf : IsClosedEmbedding (TopPair.Hom.fst (ψ ≫ e.inv)) := by rw [hfst]; exact hφ
  have hfX (v : gaugeDiscBundle ρ) (hv : TopPair.Hom.fst (ψ ≫ e.inv) v ∈ Subtype.val ⁻¹' A) :
      (v : TotalSpace F E) ∈ gaugeSphereBundle ρ :=
    (hgA v v.property).1 (by rw [hfst] at hv; exact hv)
  have hfcover : Subtype.val ⁻¹' A ∪ range (TopPair.Hom.fst (ψ ≫ e.inv)) = univ := by
    rw [hfst]
    exact eq_univ_of_forall fun x ↦ (hZ x.property).imp id fun hx ↦ hmem hx
  have hψe : ψ = (ψ ≫ e.inv) ≫ e.hom := by simp
  have he₁ : TopPair.Homotopy (e.hom ≫ e.inv) (𝟙 _) := by rw [Iso.hom_inv_id]; exact .refl _
  have he₂ : TopPair.Homotopy (e.inv ≫ e.hom) (𝟙 _) := by rw [Iso.inv_hom_id]; exact .refl _
  refine ⟨ψ, fun v ↦ congrArg Subtype.val (hψ v), fun R n ↦ ?_, fun R k _ _ M n ↦ ?_⟩
  · have := isIso_singularHomologyMap_of_attach_gaugeDiscBundle (f := ψ ≫ e.inv) hρ
      (hA.preimage continuous_subtypeVal) R n hf hfX hfcover
    have := TopPair.isIso_singularHomologyMap e.hom e.inv he₁ he₂ R n
    rw [hψe, TopPair.singularHomologyMap_comp]
    infer_instance
  · have := isIso_singularCohomologyMap_of_attach_gaugeDiscBundle (f := ψ ≫ e.inv) hρ
      (hA.preimage continuous_subtypeVal) R n k M hf hfX hfcover
    have := TopPair.isIso_singularCohomologyMap e.hom e.inv he₁ he₂ R k M n
    rw [hψe, TopPair.singularCohomologyMap_comp]
    infer_instance

variable (hρ : IsFiberGauge ρ) (hAT : A ⊆ T) (hA : IsClosed A)
  (hg : IsClosedEmbedding ((gaugeDiscBundle ρ).domRestrict g)) (hgD : g '' gaugeDiscBundle ρ = D)
  (hDT : D ⊆ T) (hgA : ∀ v ∈ gaugeDiscBundle ρ, g v ∈ A ↔ v ∈ gaugeSphereBundle ρ)
  (r : C(T, ↥(T ∩ (A ∪ D))))
  (G : ((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel (ContinuousMap.id T)
    {x | (x : Y) ∈ A ∪ D})

include hρ hA hg hgD hDT hgA G in
/-- **A deformation retract onto a disc bundle attachment, in homology and cohomology.** Under the
hypotheses of `TauCeti.exists_isIso_singularHomologyMap_of_homotopyRel_attach_discBundle`, `g`
induces a single map of pairs `(D_ρ(E), S_ρ(E)) ⟶ (T, A)` which is an isomorphism on relative
singular homology and on relative singular cohomology, with arbitrary coefficients, in every
degree. -/
theorem exists_isIso_of_homotopyRel_attach_discBundle :
    ∃ ψ : gaugeDiscSpherePair ρ ⟶ TopPair.ofInclusion (X := TopCat.of Y) hAT,
      (∀ v : gaugeDiscBundle ρ, Subtype.val (TopPair.Hom.fst ψ v) = g v) ∧
      (∀ {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ),
        IsIso (TopPair.singularHomologyMap ψ R n)) ∧
      ∀ {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
        (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ),
        IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) ψ n) := by
  have hAZ : A ⊆ T ∩ (A ∪ D) := fun x hx ↦ ⟨hAT hx, Or.inl hx⟩
  have hZT : T ∩ (A ∪ D) ⊆ T := inter_subset_left
  -- The disc bundle is attached to `A` inside `T ∩ (A ∪ D) = A ∪ D`, which includes into `T`.
  obtain ⟨ψ₀, hψ₀, hhom, hcohom⟩ := exists_isIso_attach_discBundle_subset hρ hA hAZ
    (fun x hx ↦ ⟨hDT hx, Or.inr hx⟩) inter_subset_right hg hgD hgA
  let ψ₁ :
      TopPair.ofInclusion (X := TopCat.of Y) hAZ ⟶ TopPair.ofInclusion (X := TopCat.of Y) hAT :=
    TopPair.ofInclusionMap hAZ hAT (ContinuousMap.inclusion hZT) fun _ hx ↦ hx
  -- `ψ₁` induces isomorphisms since `T` deformation retracts onto `A ∪ D`.
  have hset : {x : ↥T | (x : Y) ∈ T ∩ (A ∪ D)} = {x : ↥T | (x : Y) ∈ A ∪ D} := by
    ext x
    exact ⟨And.right, fun h ↦ ⟨x.property, h⟩⟩
  refine ⟨ψ₀ ≫ ψ₁, fun v ↦ ?_, fun R n ↦ ?_, fun R k _ _ M n ↦ ?_⟩
  · have h₁ := TopPair.ofInclusionMap_fst_apply (X := TopCat.of Y) (Y := TopCat.of Y)
      (hst := hAZ) (hst' := hAT) (ContinuousMap.inclusion hZT) (fun _ hx ↦ hx)
      (TopPair.Hom.fst ψ₀ v)
    exact (congrArg Subtype.val h₁).trans (hψ₀ v)
  · have : IsIso (TopPair.singularHomologyMap ψ₁ R n) :=
      TopPair.isIso_singularHomologyMap_ofInclusionMap_inclusion_of_homotopyRel
        (X := TopCat.of Y) hAZ hZT r (hset ▸ G) R n
    have := hhom R n
    rw [TopPair.singularHomologyMap_comp]
    infer_instance
  · have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) ψ₁ n) :=
      TopPair.isIso_singularCohomologyMap_ofInclusionMap_inclusion_of_homotopyRel
        (X := TopCat.of Y) hAZ hZT r (hset ▸ G) R k M n
    have := hcohom R k M n
    rw [TopPair.singularCohomologyMap_comp]
    infer_instance

include hρ hA hg hgD hDT hgA G in
/-- **A deformation retract onto a disc bundle attachment.** Let `ρ` be a fibre gauge on a real
vector bundle `E → B`, for instance a fibre norm which is continuous on the total space, let
`A ⊆ T` be subsets of a space `Y` with `A` closed, and let `g` restrict to a closed embedding of the
disc bundle `D_ρ(E)` into `Y` with image a subset `D` of `T`, sending a point of `D_ρ(E)` into `A`
exactly when it lies in the sphere bundle `S_ρ(E)`. If `T` strong deformation retracts onto
`A ∪ D`, through a retraction `r` and a homotopy `G` from it to the identity fixing `A ∪ D`, then
`g` induces a map of pairs `(D_ρ(E), S_ρ(E)) ⟶ (T, A)` which is an isomorphism
`Hₙ(D_ρ(E), S_ρ(E)) ≅ Hₙ(T, A)` on relative singular homology, with coefficients in any abelian
category with coproducts, in every degree. -/
theorem exists_isIso_singularHomologyMap_of_homotopyRel_attach_discBundle :
    ∃ ψ : gaugeDiscSpherePair ρ ⟶ TopPair.ofInclusion (X := TopCat.of Y) hAT,
      (∀ v : gaugeDiscBundle ρ, Subtype.val (TopPair.Hom.fst ψ v) = g v) ∧
      ∀ {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ),
        IsIso (TopPair.singularHomologyMap ψ R n) := by
  -- The universe of the unused cohomology coefficient ring is irrelevant; take it to be `0`.
  obtain ⟨ψ, hψ, hhom, -⟩ := exists_isIso_of_homotopyRel_attach_discBundle.{_, _, _, _, 0} hρ
    hAT hA hg hgD hDT hgA r G
  exact ⟨ψ, hψ, hhom⟩

include hρ hA hg hgD hDT hgA G in
/-- **A deformation retract onto a disc bundle attachment, in cohomology.** Under the hypotheses of
`TauCeti.exists_isIso_singularHomologyMap_of_homotopyRel_attach_discBundle`, `g` induces a map of
pairs `(D_ρ(E), S_ρ(E)) ⟶ (T, A)` which is an isomorphism `Hⁿ(T, A) ≅ Hⁿ(D_ρ(E), S_ρ(E))` on
relative singular cohomology, with arbitrary coefficients, in every degree. -/
theorem exists_isIso_singularCohomologyMap_of_homotopyRel_attach_discBundle :
    ∃ ψ : gaugeDiscSpherePair ρ ⟶ TopPair.ofInclusion (X := TopCat.of Y) hAT,
      (∀ v : gaugeDiscBundle ρ, Subtype.val (TopPair.Hom.fst ψ v) = g v) ∧
      ∀ {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
        (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ),
        IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) ψ n) := by
  obtain ⟨ψ, hψ, -, hcohom⟩ := exists_isIso_of_homotopyRel_attach_discBundle hρ hAT hA hg hgD
    hDT hgA r G
  exact ⟨ψ, hψ, hcohom⟩

end Deformation

/-! ### Attaching several disc bundles -/

section Several

variable {ι : Type w} {B : ι → Type w} {F : ι → Type*} {E : ∀ a, B a → Type w}
  {ρ : ∀ a, TotalSpace (F a) (E a) → ℝ} [∀ a, TopologicalSpace (TotalSpace (F a) (E a))]
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  (f : ∀ a, gaugeDiscSpherePair (ρ a) ⟶ TopPair.ofSubset (X := TopCat.of Z) X)

/-- If `X` and the images of the `f a` cover `Z`, so do `X` and the image of the map out of the
disjoint union of the disc-sphere pairs which is `f a` on the summand of `a`. -/
private lemma union_range_sigmaCofanIsColimit_desc
    (hfcover : X ∪ ⋃ a, range (TopPair.Hom.fst (f a)) = univ) :
    X ∪ range (TopPair.Hom.fst
      (Cofan.IsColimit.desc (TopPair.sigmaCofanIsColimit fun a ↦ gaugeDiscSpherePair (ρ a)) f)) =
      univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  obtain hz | hz := (hfcover.symm ▸ mem_univ z : z ∈ X ∪ ⋃ a, range (TopPair.Hom.fst (f a)))
  · exact Or.inl hz
  · obtain ⟨a, v, rfl⟩ := mem_iUnion.1 hz
    exact Or.inr ⟨⟨a, v⟩, TopPair.sigmaCofanIsColimit_desc_fst_apply _ f _⟩

/-- The map out of the disjoint union of the disc-sphere pairs which is `f a` on the summand of `a`
is a closed embedding when the `f a` are, with pairwise disjoint images. -/
private lemma isClosedEmbedding_fst_sigmaCofanIsColimit_desc [Finite ι]
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hdisj : Pairwise (Disjoint on fun a ↦ range (TopPair.Hom.fst (f a)))) :
    IsClosedEmbedding (TopPair.Hom.fst (Cofan.IsColimit.desc
      (TopPair.sigmaCofanIsColimit fun a ↦ gaugeDiscSpherePair (ρ a)) f)) := by
  rw [TopPair.sigmaCofanIsColimit_desc_fst]
  exact ContinuousMap.isClosedEmbedding_sigma hf hdisj (locallyFinite_of_finite _)

/-- The map out of the disjoint union of the disc-sphere pairs which is `f a` on the summand of `a`
sends a point into `X` only if it lies in the disjoint union of the sphere bundles, when each `f a`
sends a point into `X` only if it lies in the sphere bundle of `Eₐ`. -/
private lemma mem_range_sigma_map_of_fst_sigmaCofanIsColimit_desc_mem
    (hfX : ∀ a, ∀ v : gaugeDiscBundle (ρ a),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ gaugeSphereBundle (ρ a))
    (x : Σ a, gaugeDiscBundle (ρ a))
    (hx : TopPair.Hom.fst (Cofan.IsColimit.desc
      (TopPair.sigmaCofanIsColimit fun a ↦ gaugeDiscSpherePair (ρ a)) f) x ∈ X) :
    x ∈ range (TopPair.sigma fun a ↦ gaugeDiscSpherePair (ρ a)).map :=
  (TopPair.mem_range_sigma_map _).2 (mem_range_gaugeDiscSpherePair_map.2
    (hfX _ _ (TopPair.sigmaCofanIsColimit_desc_fst_apply _ f x ▸ hx)))

/-- The vectors of the disjoint union of the disc bundles of gauge greater than `1/2`. -/
private def sigmaOuterCollar : Set (Σ a, gaugeDiscBundle (ρ a)) :=
  {x | x.2 ∈ outerCollar (ρ x.1)}

private lemma range_sigma_map_subset_sigmaOuterCollar :
    range (TopPair.sigma fun a ↦ gaugeDiscSpherePair (ρ a)).map ⊆ sigmaOuterCollar :=
  fun _ hx ↦
    range_gaugeDiscSpherePair_map_subset_outerCollar ((TopPair.mem_range_sigma_map _).1 hx)

private lemma isOpen_sigmaOuterCollar (hρ : ∀ a, Continuous (ρ a)) :
    IsOpen (sigmaOuterCollar (ρ := ρ)) :=
  isOpen_sigma_iff.2 fun a ↦ isOpen_outerCollar (hρ a)

variable [∀ a, TopologicalSpace (B a)] [∀ a, NormedAddCommGroup (F a)] [∀ a, NormedSpace ℝ (F a)]
  [∀ a b, AddCommGroup (E a b)] [∀ a b, Module ℝ (E a b)] [∀ a b, TopologicalSpace (E a b)]
  [∀ a, FiberBundle (F a) (E a)] [∀ a, VectorBundle ℝ (F a) (E a)]

/-- The radial push `TauCeti.radialPush 2⁻¹` applied to the gauge in every fibre of every summand
of the disjoint union of the disc bundles: the homotopies `discCollar` of the summands, followed by
their inclusions, glued along the disjoint union. -/
private def sigmaDiscCollar (hρ : ∀ a, IsFiberGauge (ρ a)) :
    C(I × Σ a, gaugeDiscBundle (ρ a), Σ a, gaugeDiscBundle (ρ a)) :=
  (ContinuousMap.Homotopy.sigma fun a ↦
    (ContinuousMap.Homotopy.refl ⟨Sigma.mk a, continuous_sigmaMk⟩).comp
      (ContinuousMap.Homotopy.ofApplyZero (f := .id _) (discCollar (hρ a))
        (discCollar_zero (hρ a)))).toContinuousMap

section

variable (hρ : ∀ a, IsFiberGauge (ρ a))

/-- On the summand of `a`, the collar deformation of the disjoint union is that of `D_ρₐ(Eₐ)`. -/
private lemma sigmaDiscCollar_apply (t : I) (x : Σ a, gaugeDiscBundle (ρ a)) :
    sigmaDiscCollar hρ (t, x) = ⟨x.1, discCollar (hρ x.1) (t, x.2)⟩ := by
  obtain ⟨a, v⟩ := x
  simp only [sigmaDiscCollar, ContinuousMap.Homotopy.coe_toContinuousMap,
    ContinuousMap.Homotopy.sigma_apply, ContinuousMap.Homotopy.comp_apply,
    ContinuousMap.Homotopy.refl_apply, ContinuousMap.coe_mk]
  exact congrArg (Sigma.mk a) (ContinuousMap.Homotopy.ofApplyZero_apply (f := .id _) _ _ _)

private lemma sigmaDiscCollar_zero (x : Σ a, gaugeDiscBundle (ρ a)) :
    sigmaDiscCollar hρ (0, x) = x := by
  rw [sigmaDiscCollar_apply, discCollar_zero]

private lemma sigmaDiscCollar_of_mem_range (t : I) {x : Σ a, gaugeDiscBundle (ρ a)}
    (hx : x ∈ range (TopPair.sigma fun a ↦ gaugeDiscSpherePair (ρ a)).map) :
    sigmaDiscCollar hρ (t, x) = x := by
  rw [sigmaDiscCollar_apply,
    discCollar_of_mem_range (hρ x.1) t ((TopPair.mem_range_sigma_map _).1 hx)]

private lemma sigmaDiscCollar_mem_sigmaOuterCollar (t : I) {x : Σ a, gaugeDiscBundle (ρ a)}
    (hx : x ∈ sigmaOuterCollar) : sigmaDiscCollar hρ (t, x) ∈ sigmaOuterCollar := by
  rw [sigmaDiscCollar_apply]
  exact discCollar_mem_outerCollar (hρ x.1) t hx

private lemma sigmaDiscCollar_one_mem_range {x : Σ a, gaugeDiscBundle (ρ a)}
    (hx : x ∈ sigmaOuterCollar) :
    sigmaDiscCollar hρ (1, x) ∈ range (TopPair.sigma fun a ↦ gaugeDiscSpherePair (ρ a)).map := by
  rw [sigmaDiscCollar_apply]
  exact (TopPair.mem_range_sigma_map _).2 (discCollar_one_mem_range (hρ x.1) hx)

end

variable [Finite ι]

/-- The hypotheses of an attachment of several disc bundles make the attachment of their disjoint
union an attachment along a subspace with a deformation neighbourhood, so that its relative homology
is that of the disjoint union of the disc-sphere pairs. -/
private lemma isIso_singularHomologyMap_sigmaCofanIsColimit_desc
    (hρ : ∀ a, IsFiberGauge (ρ a)) (hX : IsClosed X)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hfX : ∀ a, ∀ v : gaugeDiscBundle (ρ a),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ gaugeSphereBundle (ρ a))
    (hdisj : Pairwise (Disjoint on fun a ↦ range (TopPair.Hom.fst (f a))))
    (hfcover : X ∪ ⋃ a, range (TopPair.Hom.fst (f a)) = univ) :
    IsIso (TopPair.singularHomologyMap
      (Cofan.IsColimit.desc (TopPair.sigmaCofanIsColimit fun a ↦ gaugeDiscSpherePair (ρ a)) f)
      R n) :=
  TopPair.isIso_singularHomologyMap_of_attach R n _ hX
    (isClosedEmbedding_fst_sigmaCofanIsColimit_desc f hf hdisj)
    (mem_range_sigma_map_of_fst_sigmaCofanIsColimit_desc_mem f hfX)
    (union_range_sigmaCofanIsColimit_desc f hfcover)
    (isOpen_sigmaOuterCollar fun a ↦ (hρ a).continuous) range_sigma_map_subset_sigmaOuterCollar
    (sigmaDiscCollar hρ) (sigmaDiscCollar_zero hρ) (fun t _ ↦ sigmaDiscCollar_of_mem_range hρ t)
    (fun t _ ↦ sigmaDiscCollar_mem_sigmaOuterCollar hρ t)
    (fun _ ↦ sigmaDiscCollar_one_mem_range hρ)

/-- The cohomology form of `isIso_singularHomologyMap_sigmaCofanIsColimit_desc`. -/
private lemma isIso_singularCohomologyMap_sigmaCofanIsColimit_desc
    (hρ : ∀ a, IsFiberGauge (ρ a)) (hX : IsClosed X)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ)
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hfX : ∀ a, ∀ v : gaugeDiscBundle (ρ a),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ gaugeSphereBundle (ρ a))
    (hdisj : Pairwise (Disjoint on fun a ↦ range (TopPair.Hom.fst (f a))))
    (hfcover : X ∪ ⋃ a, range (TopPair.Hom.fst (f a)) = univ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (Cofan.IsColimit.desc (TopPair.sigmaCofanIsColimit fun a ↦ gaugeDiscSpherePair (ρ a)) f)
      n) :=
  TopPair.isIso_singularCohomologyMap_of_attach R k M n _ hX
    (isClosedEmbedding_fst_sigmaCofanIsColimit_desc f hf hdisj)
    (mem_range_sigma_map_of_fst_sigmaCofanIsColimit_desc_mem f hfX)
    (union_range_sigmaCofanIsColimit_desc f hfcover)
    (isOpen_sigmaOuterCollar fun a ↦ (hρ a).continuous) range_sigma_map_subset_sigmaOuterCollar
    (sigmaDiscCollar hρ) (sigmaDiscCollar_zero hρ) (fun t _ ↦ sigmaDiscCollar_of_mem_range hρ t)
    (fun t _ ↦ sigmaDiscCollar_mem_sigmaOuterCollar hρ t)
    (fun _ ↦ sigmaDiscCollar_one_mem_range hρ)

/-- **Attaching several disc bundles: relative homology is the coproduct.** Let `Eₐ → Bₐ`, for `a`
in a finite type, be real vector bundles with fibre gauges `ρₐ`, for instance fibre norms which are
continuous on the total spaces, the bundles having possibly different bases and ranks, and let
`f a : (D_ρₐ(Eₐ), S_ρₐ(Eₐ)) ⟶ (Z, X)` be maps of pairs with `X` closed in `Z`. Suppose that each
`f a` is a closed embedding of `D_ρₐ(Eₐ)` into `Z` sending a point into `X` only if it lies in
`S_ρₐ(Eₐ)`, that the images of the `f a` are pairwise disjoint, and that `X` together with these
images is all of `Z`: the space `Z` is obtained from `X` by attaching the disc bundles `D_ρₐ(Eₐ)`
along their sphere bundles. Then, in every degree and with coefficients in any abelian category
with coproducts, `Hₙ(Z, X)` is the coproduct of the `Hₙ(D_ρₐ(Eₐ), S_ρₐ(Eₐ))`, with the maps
induced by the `f a` as the coproduct inclusions. -/
def isColimitCofanSingularHomologyOfAttachGaugeDiscBundle
    (hρ : ∀ a, IsFiberGauge (ρ a)) (hX : IsClosed X)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hfX : ∀ a, ∀ v : gaugeDiscBundle (ρ a),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ gaugeSphereBundle (ρ a))
    (hdisj : Pairwise (Disjoint on fun a ↦ range (TopPair.Hom.fst (f a))))
    (hfcover : X ∪ ⋃ a, range (TopPair.Hom.fst (f a)) = univ) :
    IsColimit (Cofan.mk ((TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n)
      fun a ↦ TopPair.singularHomologyMap (f a) R n) :=
  have := isIso_singularHomologyMap_sigmaCofanIsColimit_desc f hρ hX R n hf hfX hdisj hfcover
  -- Finite coproducts are exact in an abelian category, which has finite biproducts.
  have : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  IsColimit.ofIsoColimit
    (TopPair.isColimitCofanSingularHomology (fun a ↦ gaugeDiscSpherePair (ρ a)) C R n)
    (Cofan.ext (asIso (TopPair.singularHomologyMap (Cofan.IsColimit.desc
      (TopPair.sigmaCofanIsColimit fun a ↦ gaugeDiscSpherePair (ρ a)) f) R n)) fun a ↦ by
      rw [cofan_mk_inj, cofan_mk_inj, asIso_hom, ← TopPair.singularHomologyMap_comp]
      exact congrArg (TopPair.singularHomologyMap · R n) (Cofan.IsColimit.fac _ f a))

/-- **Attaching several disc bundles: relative cohomology is the product.** Under the hypotheses of
`TauCeti.isColimitCofanSingularHomologyOfAttachGaugeDiscBundle`, in every degree and with arbitrary
coefficients, `Hⁿ(Z, X)` is the product of the `Hⁿ(D_ρₐ(Eₐ), S_ρₐ(Eₐ))`, with the maps induced by
the `f a` as the product projections. -/
def isLimitFanSingularCohomologyOfAttachGaugeDiscBundle
    (hρ : ∀ a, IsFiberGauge (ρ a)) (hX : IsClosed X)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ)
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hfX : ∀ a, ∀ v : gaugeDiscBundle (ρ a),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ gaugeSphereBundle (ρ a))
    (hdisj : Pairwise (Disjoint on fun a ↦ range (TopPair.Hom.fst (f a))))
    (hfcover : X ∪ ⋃ a, range (TopPair.Hom.fst (f a)) = univ) :
    IsLimit (Fan.mk ((TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n)
      fun a ↦ TopPair.singularCohomologyMap (f a) n) := by
  have := isIso_singularCohomologyMap_sigmaCofanIsColimit_desc f hρ hX R k M n hf hfX hdisj
    hfcover
  refine IsLimit.ofIsoLimit
    (TopPair.isLimitFanSingularCohomology (fun a ↦ gaugeDiscSpherePair (ρ a)) C R k M n)
    (Fan.ext (asIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (Cofan.IsColimit.desc
      (TopPair.sigmaCofanIsColimit fun a ↦ gaugeDiscSpherePair (ρ a)) f) n)).symm fun a ↦ ?_)
  rw [fan_mk_proj, fan_mk_proj, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp,
    ← TopPair.singularCohomologyMap_comp]
  exact congrArg (TopPair.singularCohomologyMap · n) (Cofan.IsColimit.fac _ f a)

end Several

end TauCeti
