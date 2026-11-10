/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Derivative
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Chart
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Homological

/-!
# Smooth orientations are homological orientations

An orientation `o` of a boundaryless `C¹` manifold `M` modelled on a real inner product space `E`
of dimension `n + 1` (`TauCeti.Manifold.Orientation`) selects at every point `x` the local
orientation of its oriented preferred chart (`TauCeti.localOrientationOfManifoldOrientation`), a
generator of `Hₙ₊₁(M, M ∖ {x}; ℤ)`. These local orientations are carried to each other by
transport along paths, so they form a homological orientation
(`TauCeti.Manifold.Orientation.toHomologicalOrientation`). Through it, the fundamental class, the
degree and the local index of `TauCeti.HomologicalOrientation` apply to smooth oriented manifolds,
and can be compared with tangent-space computations such as signed counts of preimages.

Two facts about the local orientations selected by oriented charts go into the proof.

* **Within a chart.** Along a path inside the image of a compact convex subset of the target of a
  chart, transport preserves the local orientations selected in that chart by a fixed orientation
  of the model
  (`OpenPartialHomeomorph.localOrientationTransport_localOrientationOfOrientedChart`). In the model
  `E`, the generators at the points of a convex set `K` are restrictions of one class of
  `Hₙ₊₁(E, E ∖ K)`: through the connecting morphism, the generator at `p` is read by radial
  projection about `p`, and on `E ∖ K` the radial projections about two points of `K` are homotopic
  through radial projections about the points of the segment between them. The generators of a
  chart are pulled back from those of the model through the source of the chart.
* **Change of chart.** Two charts select local orientations differing by the sign of the Jacobian
  determinant of the transition map
  (`OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul`). This is the action
  of a map on local homology at a point where its derivative is invertible
  (`TauCeti.localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt`), together with the
  invariance of the model generators under translations.

The chart signs of an orientation lift compensate the signs of these Jacobians, so near each point
the local orientations selected in the preferred charts are those selected in a single chart by a
single orientation of the model, and transport preserves them.

## Main declarations

* `OpenPartialHomeomorph.localOrientationTransport_localOrientationOfOrientedChart`: transport
  preserves oriented-chart local orientations along a path in a compact convex set of a chart.
* `OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul`: changing the chart
  multiplies the selected local orientation by the sign of the Jacobian of the transition map.
* `TauCeti.Manifold.Orientation.toHomologicalOrientation`: the homological orientation of a smooth
  orientation, with `toHomologicalOrientation_apply`, `toHomologicalOrientation_neg` and
  `toHomologicalOrientation_injective`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2 (local degree) and Section 3.3 (local orientations, and orientations as locally
  consistent choices of them).
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module Set Topology
open scoped Manifold

universe w v u

namespace TauCeti

section Model

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem mem_refl_source (p : E) : p ∈ (OpenPartialHomeomorph.refl E).source := by
  rw [OpenPartialHomeomorph.refl_source]
  exact mem_univ p

/-- Radial projection about a point `p` of `K`, on the complement of `K`. -/
private def complRadial {K : Set E} {p : E} (hp : p ∈ K) : C((Kᶜ : Set E), sphere (0 : E) 1) :=
  (complSingletonHomotopyEquivSphere p).toFun.comp
    (ContinuousMap.inclusion (compl_subset_compl.2 (singleton_subset_iff.2 hp)))

private theorem coe_complRadial_apply {K : Set E} {p : E} (hp : p ∈ K) (y : (Kᶜ : Set E)) :
    (complRadial hp y : E) = ‖(y : E) - p‖⁻¹ • ((y : E) - p) := by
  simp [complRadial]

/-- Radial projection about the points of a segment in a convex set `K` is a homotopy, on the
complement of `K`, between the radial projections about its end points. -/
private def complRadialHomotopy {K : Set E} (hK : Convex ℝ K) {p q : E} (hp : p ∈ K)
    (hq : q ∈ K) : (complRadial hp).Homotopy (complRadial hq) where
  toContinuousMap := normalizeToSphere
    (fun z : unitInterval × (Kᶜ : Set E) ↦ (z.2 : E) - AffineMap.lineMap p q (z.1 : ℝ))
    (by fun_prop) fun z ↦ sub_ne_zero.2 fun h ↦
      z.2.2 (h ▸ hK.lineMap_mem hp hq ⟨z.1.2.1, z.1.2.2⟩)
  map_zero_left z := Subtype.ext (by simp [coe_complRadial_apply, NormedSpace.normalize])
  map_one_left z := Subtype.ext (by simp [coe_complRadial_apply, NormedSpace.normalize])

/-- On the subspace of the pair `(E, E ∖ K)`, the inclusion into `E ∖ {p}` followed by radial
projection about `p` is `TauCeti.complRadial`. -/
private theorem snd_ofSubsetMap_comp_complSingletonHomotopyEquivSphere {K : Set E} {p : E}
    (hp : p ∈ K) :
    TopPair.Hom.snd (TopPair.ofSubsetMap (𝟙 (TopCat.of E)) (B := (Kᶜ : Set (TopCat.of E)))
        (B' := {p}ᶜ) (compl_subset_compl.2 (singleton_subset_iff.2 hp))) ≫
      TopCat.ofHom (complSingletonHomotopyEquivSphere p).toFun =
    TopCat.ofHom (complRadial hp) := by
  ext z
  -- The subspace of `TopPair.ofSubset` is the subtype only after unfolding the pair.
  exact congrArg (fun y ↦ ((complSingletonHomotopyEquivSphere p).toFun y : E))
    (Subtype.ext (TopPair.ofSubsetMap_snd_apply _ _ z))

/-- Read through the connecting morphism and radial projection about the point, the restrictions
`Hₖ₊₁(E, E ∖ K) ⟶ Hₖ₊₁(E, E ∖ {p})` agree for all points `p` of a convex set `K`. -/
@[reassoc]
private theorem localHomologyRestriction_comp_reducedSingularHomologyδ_comp_eq {K : Set E}
    (hK : Convex ℝ K) {p q : E} (hp : p ∈ K) (hq : q ∈ K) (k : ℕ) :
    localHomologyRestriction R (singleton_subset_iff.2 hp) (k + 1) ≫
        (TopPair.ofSubset ({p}ᶜ : Set (TopCat.of E))).reducedSingularHomologyδ R k ≫
          (reducedSingularHomologyFunctor R k).map
            (TopCat.ofHom (complSingletonHomotopyEquivSphere p).toFun) =
      localHomologyRestriction R (singleton_subset_iff.2 hq) (k + 1) ≫
        (TopPair.ofSubset ({q}ᶜ : Set (TopCat.of E))).reducedSingularHomologyδ R k ≫
          (reducedSingularHomologyFunctor R k).map
            (TopCat.ofHom (complSingletonHomotopyEquivSphere q).toFun) := by
  rw [localHomologyRestriction_def, localHomologyRestriction_def,
    ← TopPair.reducedSingularHomologyδ_naturality_assoc,
    ← TopPair.reducedSingularHomologyδ_naturality_assoc]
  congr 1
  -- The composites are only type-correct after unfolding the subspace of the pair.
  erw [← Functor.map_comp, ← Functor.map_comp,
    snd_ofSubsetMap_comp_complSingletonHomotopyEquivSphere hp,
    snd_ofSubsetMap_comp_complSingletonHomotopyEquivSphere hq]
  exact reducedSingularHomologyFunctor_map_eq_of_homotopy R (complRadialHomotopy hK hp hq) k

omit [NormedSpace ℝ E] in
private theorem translate_preimage_subset (p c : E) :
    (⟨fun y ↦ c + (y - p), by fun_prop⟩ : C(E, E)) ⁻¹' {c} ⊆ {p} :=
  fun _ hy ↦ sub_eq_zero.1 (add_eq_left.1 hy)

end Model

section ChartPullback

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
variable {M : Type w} [TopologicalSpace M] [T1Space M]
  {E : Type w} [TopologicalSpace E] [T1Space E] (φ : OpenPartialHomeomorph M E)

/-- The restriction of a chart to its source, as a continuous map. -/
private def sourceRestrict : C(φ.source, E) :=
  ⟨φ.source.domRestrict φ, φ.continuousOn.domRestrict⟩

omit [T1Space M] [T1Space E] in
private theorem sourceRestrict_apply (z : φ.source) : sourceRestrict φ z = φ z :=
  (rfl)

omit [T1Space M] [T1Space E] in
/-- The source of `φ` meets the preimage of a subset `K` of its target in the preimage of
`φ.symm '' K`. -/
private theorem sourceRestrict_preimage_eq {K : Set E} (hKφ : K ⊆ φ.target) :
    sourceRestrict φ ⁻¹' K = ContinuousMap.subtypeVal φ.source ⁻¹' (φ.symm '' K) := by
  ext z
  simp [φ.symm_image_eq_source_inter_preimage hKφ, sourceRestrict_apply, z.2]

omit [T1Space M] [T1Space E] in
private theorem sourceRestrict_preimage {a : M} (ha : a ∈ φ.source) :
    sourceRestrict φ ⁻¹' {φ a} ⊆ ContinuousMap.subtypeVal φ.source ⁻¹' {a} :=
  fun x hx ↦ φ.injOn x.2 ha hx

/-- **The chart isomorphism through the source.** The local homology isomorphism of a chart `φ`
at `a` is the inverse of the excision isomorphism of the source of `φ`, followed by the map
induced by `φ` on the source. -/
private theorem localHomologyMap_subtypeVal_comp_singularHomologyComplSingletonIsoOfChart_hom
    {a : M} (ha : a ∈ φ.source) (k : ℕ) :
    localHomologyMap R (ContinuousMap.subtypeVal φ.source)
        (S := ContinuousMap.subtypeVal φ.source ⁻¹' {a}) (T := {a}) subset_rfl k ≫
          (singularHomologyComplSingletonIsoOfChart R φ ha k).hom =
      localHomologyMap R (sourceRestrict φ) (sourceRestrict_preimage φ ha) k := by
  have h₁ : localHomologyMap R (ContinuousMap.subtypeVal φ.source)
      (S := ContinuousMap.subtypeVal φ.source ⁻¹' {a}) (T := {a}) subset_rfl k =
        TopPair.singularHomologyMap
        (TopPair.excisionMap (X := TopCat.of M) φ.source {a}ᶜ) R k := by
    -- The pairs agree only after unfolding the preimages of complements.
    erw [localHomologyMap_def]
    congr 1
    apply TopPair.hom_ext_of_fst
    ext z
    erw [TopPair.excisionMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
    rfl
  have h₂ : localHomologyMap R (sourceRestrict φ) (sourceRestrict_preimage φ ha) k =
      TopPair.singularHomologyMap ((TopPair.ofSubsetIso (X := TopCat.of φ.source)
          (Y := TopCat.of φ.target) φ.toHomeomorphSourceTarget
          (B := Subtype.val ⁻¹' {a}ᶜ) (B' := Subtype.val ⁻¹' {φ a}ᶜ)
          fun z ↦ (φ.injOn.eq_iff z.2 ha).not.symm).hom ≫
        TopPair.excisionMap (X := TopCat.of E) φ.target {φ a}ᶜ) R k := by
    -- The pairs agree only after unfolding the preimages of complements.
    erw [localHomologyMap_def]
    congr 1
    apply TopPair.hom_ext_of_fst
    ext z
    rw [TopPair.Hom.fst_comp]
    erw [ConcreteCategory.comp_apply, TopPair.excisionMap_fst_apply, TopPair.ofSubsetIso_hom,
      TopPair.ofSubsetMap_fst_apply,
      TopPair.ofSubsetMap_fst_apply]
    rfl
  rw [h₁, h₂, TopPair.singularHomologyMap_comp]
  exact singularHomologyMap_excisionMap_comp_singularHomologyComplSingletonIsoOfChart_hom R φ ha k

end ChartPullback

section Generator

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (ω : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1)

/-- **Oriented generators along a convex set.** If a class of `Hₙ₊₁(E, E ∖ K; ℤ)`, for a convex
set `K`, restricts at one point `p` of `K` to the local orientation selected by `ω`, then it
restricts to the local orientation selected by `ω` at every point `q` of `K`. -/
private theorem localHomologyRestriction_eq_localOrientationOfOrientedChart_refl {K : Set E}
    (hK : Convex ℝ K) {p q : E} (hp : p ∈ K) (hq : q ∈ K)
    (c : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) K (n + 1))
    (hc : localHomologyRestriction (ModuleCat.of ℤ (ULift.{w} ℤ)) (singleton_subset_iff.2 hp)
      (n + 1) c =
      ((OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart (mem_refl_source p) ω
        hE).val) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{w} ℤ)) (singleton_subset_iff.2 hq) (n + 1)
      c =
      ((OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart (mem_refl_source q) ω
        hE).val := by
  set R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let e (x : E) := singularHomologyComplSingletonIsoOfOrientation R
    (OpenPartialHomeomorph.refl E) (mem_refl_source x) ω hE
  have h : localHomologyRestriction R (singleton_subset_iff.2 hp) (n + 1) ≫ (e p).hom =
      localHomologyRestriction R (singleton_subset_iff.2 hq) (n + 1) ≫ (e q).hom := by
    simp only [e, singularHomologyComplSingletonIsoOfOrientation_refl_hom]
    exact localHomologyRestriction_comp_reducedSingularHomologyδ_comp_eq_assoc R hK hp hq n _
  rw [OpenPartialHomeomorph.coe_localOrientationOfOrientedChart] at hc ⊢
  apply (ConcreteCategory.bijective_of_isIso (e q).hom).1
  rw [← ConcreteCategory.comp_apply, ← h, ConcreteCategory.comp_apply, hc]
  exact ((e p).inv_hom_id_apply 1).trans ((e q).inv_hom_id_apply 1).symm

end Generator

section Pullback

variable {M : Type w} [TopologicalSpace M] [T1Space M]
  {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (ω : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1) (φ : OpenPartialHomeomorph M E)

/-- **Oriented-chart local orientations are pulled back from the model.** A class on the source
of a chart `φ` which `φ` carries to the local orientation of the model `E` at `φ a` selected by
`ω` is carried by the inclusion of the source to the local orientation of `M` at `a` selected by
the oriented chart. -/
private theorem localHomologyMap_subtypeVal_eq_localOrientationOfOrientedChart {a : M}
    (ha : a ∈ φ.source)
    (w : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      (ContinuousMap.subtypeVal φ.source ⁻¹' {a}) (n + 1))
    (hw : localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (sourceRestrict φ)
        (sourceRestrict_preimage φ ha) (n + 1) w =
      ((OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart (mem_refl_source (φ a)) ω
        hE).val) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (ContinuousMap.subtypeVal φ.source)
        (S := ContinuousMap.subtypeVal φ.source ⁻¹' {a}) (T := {a}) subset_rfl (n + 1) w =
      (φ.localOrientationOfOrientedChart ha ω hE).val := by
  let e := singularHomologyComplSingletonIsoOfOrientation (ModuleCat.of ℤ (ULift.{w} ℤ)) φ ha ω hE
  let e₀ := singularHomologyComplSingletonIsoOfOrientation (ModuleCat.of ℤ (ULift.{w} ℤ))
    (OpenPartialHomeomorph.refl E) (mem_refl_source (φ a)) ω hE
  have key : (singularHomologyComplSingletonIsoOfChart (ModuleCat.of ℤ (ULift.{w} ℤ)) φ ha
      (n + 1)).hom (localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ))
        (ContinuousMap.subtypeVal φ.source) (S := ContinuousMap.subtypeVal φ.source ⁻¹' {a})
        (T := {a}) subset_rfl (n + 1) w) =
      localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (sourceRestrict φ)
        (sourceRestrict_preimage φ ha) (n + 1) w := by
    rw [← ConcreteCategory.comp_apply,
      localHomologyMap_subtypeVal_comp_singularHomologyComplSingletonIsoOfChart_hom]
  rw [OpenPartialHomeomorph.coe_localOrientationOfOrientedChart] at hw ⊢
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  rw [Iso.inv_hom_id_apply,
    singularHomologyComplSingletonIsoOfOrientation_hom_eq _ φ ha (mem_refl_source (φ a)),
    ConcreteCategory.comp_apply, key, hw]
  exact e₀.inv_hom_id_apply 1

/-- `TauCeti.localHomologyMap_subtypeVal_eq_localOrientationOfOrientedChart` with the image point
of the chart given as any `b = φ a`. -/
private theorem localHomologyMap_subtypeVal_eq_localOrientationOfOrientedChart_of_eq {a : M}
    (ha : a ∈ φ.source) {b : E} (hb : φ a = b)
    (w : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      (ContinuousMap.subtypeVal φ.source ⁻¹' {a}) (n + 1))
    (hS : sourceRestrict φ ⁻¹' {b} ⊆ ContinuousMap.subtypeVal φ.source ⁻¹' {a})
    (hw : localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (sourceRestrict φ) hS (n + 1) w =
      ((OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart (mem_refl_source b) ω
        hE).val) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (ContinuousMap.subtypeVal φ.source)
        (S := ContinuousMap.subtypeVal φ.source ⁻¹' {a}) (T := {a}) subset_rfl (n + 1) w =
      (φ.localOrientationOfOrientedChart ha ω hE).val := by
  subst hb
  exact localHomologyMap_subtypeVal_eq_localOrientationOfOrientedChart ω hE φ ha w hw

end Pullback

section Transport

variable {M : Type w} [TopologicalSpace M] [T2Space M]
  {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  (ω : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1) (φ : OpenPartialHomeomorph M E)

omit [T2Space M] [InnerProductSpace ℝ E] in
private theorem mem_symm_image {K : Set E} {p : M} (hp : p ∈ φ.source) (hpK : φ p ∈ K) :
    p ∈ φ.symm '' K :=
  ⟨φ p, hpK, φ.left_inv hp⟩

/-- A class of the source of `φ` relative to the complement of `φ.symm '' K`, which `φ` carries
to a class of `Hₙ₊₁(E, E ∖ K)` restricting at `φ p` to the local orientation of the model, is
carried by the inclusion of the source to a class restricting at `p` to the oriented-chart local
orientation. -/
private theorem localHomologyRestriction_localHomologyMap_subtypeVal_eq {K : Set E}
    (hKφ : K ⊆ φ.target)
    (w : localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      (ContinuousMap.subtypeVal φ.source ⁻¹' (φ.symm '' K)) (n + 1))
    {p : M} (hp : p ∈ φ.source) (hpK : φ p ∈ K)
    (hw : localHomologyRestriction (ModuleCat.of ℤ (ULift.{w} ℤ)) (singleton_subset_iff.2 hpK)
        (n + 1) (localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (sourceRestrict φ)
          (sourceRestrict_preimage_eq φ hKφ).subset (n + 1) w) =
      ((OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart (mem_refl_source (φ p)) ω
        hE).val) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{w} ℤ))
        (singleton_subset_iff.2 (mem_symm_image φ hp hpK)) (n + 1)
        (localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (ContinuousMap.subtypeVal φ.source)
          (S := ContinuousMap.subtypeVal φ.source ⁻¹' (φ.symm '' K)) (T := φ.symm '' K)
          subset_rfl (n + 1) w) =
      (φ.localOrientationOfOrientedChart hp ω hE).val := by
  have hpS : ContinuousMap.subtypeVal φ.source ⁻¹' {p} ⊆
      ContinuousMap.subtypeVal φ.source ⁻¹' (φ.symm '' K) := by
    rintro z hz
    rw [mem_preimage, mem_singleton_iff] at hz
    rw [mem_preimage, hz]
    exact mem_symm_image φ hp hpK
  -- Restricting the pulled-back class to `p` is the pullback of its restriction to `p` in the
  -- source of `φ`, and similarly for its image in `E`.
  have h₁ := ConcreteCategory.congr_hom
    ((localHomologyMap_comp_localHomologyRestriction _ (ContinuousMap.subtypeVal φ.source)
      (singleton_subset_iff.2 (mem_symm_image φ hp hpK)) subset_rfl (n + 1)).trans
      (localHomologyRestriction_comp_localHomologyMap _ (ContinuousMap.subtypeVal φ.source) hpS
        subset_rfl (n + 1)).symm) w
  have h₂ := ConcreteCategory.congr_hom
    ((localHomologyMap_comp_localHomologyRestriction _ (sourceRestrict φ)
        (singleton_subset_iff.2 hpK) (sourceRestrict_preimage_eq φ hKφ).subset (n + 1)).trans
      (localHomologyRestriction_comp_localHomologyMap _ (sourceRestrict φ) hpS
        (sourceRestrict_preimage φ hp) (n + 1)).symm) w
  simp only [ConcreteCategory.comp_apply] at h₁ h₂
  rw [h₁]
  exact localHomologyMap_subtypeVal_eq_localOrientationOfOrientedChart ω hE φ hp _ (h₂ ▸ hw)

omit [T2Space M] [InnerProductSpace ℝ E] in
private theorem apply_mem_of_mem_symm_image {K : Set E} (hKφ : K ⊆ φ.target) {p : M}
    (hp : p ∈ φ.symm '' K) : φ p ∈ K := by
  obtain ⟨z, hz, rfl⟩ := hp
  rwa [φ.right_inv (hKφ hz)]

/-- **Transport of oriented-chart local orientations.** Along a path inside the image under a
chart `φ` of a compact convex subset `K` of its target, the transport of local orientations
carries the local orientation selected by an orientation `ω` of the model in the chart `φ` at the
start of the path to the one selected by `ω` in `φ` at its end. -/
theorem _root_.OpenPartialHomeomorph.localOrientationTransport_localOrientationOfOrientedChart
    [FiniteDimensional ℝ E] [ChartedSpace E M] {K : Set E} (hK : Convex ℝ K)
    (hKc : IsCompact K) (hKφ : K ⊆ φ.target) {x y : M} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ φ.symm '' K) (hx : x ∈ φ.source) (hy : y ∈ φ.source) :
    localOrientationTransport M E (n + 1)
        (Path.Homotopic.Quotient.mk γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y)
        (φ.localOrientationOfOrientedChart hx ω hE) =
      φ.localOrientationOfOrientedChart hy ω hE := by
  set Z := ModuleCat.of ℤ (ULift.{w} ℤ)
  have hxK : φ x ∈ K := apply_mem_of_mem_symm_image φ hKφ (γ.source ▸ hγ 0)
  have hyK : φ y ∈ K := apply_mem_of_mem_symm_image φ hKφ (γ.target ▸ hγ 1)
  -- A class of `Hₙ₊₁(E, E ∖ K)` restricting to the model local orientations at the points of `K`.
  have : IsIso (localHomologyRestriction Z (singleton_subset_iff.2 hxK) (n + 1)) := by
    rw [localHomologyRestriction_def]
    exact isIso_singularHomologyMap_compl_of_starConvex Z (hK.starConvex hxK) hxK hKc.isBounded
      (n + 1)
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso
    (localHomologyRestriction Z (singleton_subset_iff.2 hxK) (n + 1))).2
    ((OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart (mem_refl_source (φ x)) ω
      hE).val
  have hc' := localHomologyRestriction_eq_localOrientationOfOrientedChart_refl ω hE hK hxK hyK c hc
  -- Its pullback to `Hₙ₊₁(M, M ∖ φ.symm '' K)` through the source of `φ`.
  have : IsIso (localHomologyMap Z (sourceRestrict φ) (sourceRestrict_preimage_eq φ hKφ).subset
      (n + 1)) :=
    isIso_localHomologyMap Z (sourceRestrict φ) φ.isOpenEmbedding_restrict
      (sourceRestrict_preimage_eq φ hKφ) hKc.isClosed
      (fun z hz ↦ ⟨⟨φ.symm z, φ.map_target (hKφ hz)⟩, φ.right_inv (hKφ hz)⟩) (n + 1)
  obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso (localHomologyMap Z (sourceRestrict φ)
    (sourceRestrict_preimage_eq φ hKφ).subset (n + 1))).2 c
  have hgx := localHomologyRestriction_localHomologyMap_subtypeVal_eq ω hE φ hKφ w hx hxK
    (hw ▸ hc)
  have hgy := localHomologyRestriction_localHomologyMap_subtypeVal_eq ω hE φ hKφ w hy hyK
    (hw ▸ hc')
  apply Subtype.ext
  rw [coe_localOrientationTransport, ← hgx, ← hgy, ← ConcreteCategory.comp_apply,
    localHomologyRestriction_comp_localHomologyTransport Z φ hK hKc hKφ γ hγ (n + 1)]

end Transport

section ChartChange

variable {M : Type w} [TopologicalSpace M] [T1Space M]
  {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
  (ω : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1)

/-- **Change of oriented chart.** For two charts `φ` and `χ` at `a` whose transition map
`χ ∘ φ.symm` has an invertible derivative `f'` at `φ a`, the local orientations of `M` at `a`
selected by an orientation `ω` of the model in the two charts differ by the sign of `det f'`. -/
theorem _root_.OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul
    (φ χ : OpenPartialHomeomorph M E) {a : M} (haφ : a ∈ φ.source) (haχ : a ∈ χ.source)
    {f' : E →L[ℝ] E} (hf : HasFDerivAt (χ ∘ φ.symm) f' (φ a)) (hdet : f'.det ≠ 0) :
    (χ.localOrientationOfOrientedChart haχ ω hE).val =
      (SignType.sign f'.det : ℤ) • (φ.localOrientationOfOrientedChart haφ ω hE).val := by
  set Z := ModuleCat.of ℤ (ULift.{w} ℤ)
  set s : ℤ := (SignType.sign f'.det : ℤ)
  -- The transition map on the open set `V` of the model where it is defined.
  set V : Set E := φ.target ∩ φ.symm ⁻¹' χ.source
  have haV : φ a ∈ V := ⟨φ.map_source haφ, by simpa [φ.left_inv haφ] using haχ⟩
  have hU : V ∈ 𝓝 (φ a) := (φ.isOpen_inter_preimage_symm χ.open_source).mem_nhds haV
  have hτc : ContinuousOn (χ ∘ φ.symm) V :=
    χ.continuousOn.comp (φ.continuousOn_symm.mono inter_subset_left) fun _ hy ↦ hy.2
  have hτinj : ∀ y ∈ V, (χ ∘ φ.symm) y = (χ ∘ φ.symm) (φ a) → y = φ a := by
    intro y hy hyτ
    have h := χ.injOn hy.2 (by simpa [φ.left_inv haφ] using haχ) hyτ
    rw [← φ.right_inv hy.1, h, φ.left_inv haφ]
  have key := localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt Z hU hτc hf hdet hτinj
    (n + 1)
  -- The common part `W` of the two sources, and the maps out of it.
  set W : Set M := φ.source ∩ χ.source
  have hWo : IsOpen W := φ.open_source.inter χ.open_source
  have haW : a ∈ W := ⟨haφ, haχ⟩
  let iφ : C(W, φ.source) := ContinuousMap.inclusion inter_subset_left
  let iχ : C(W, χ.source) := ContinuousMap.inclusion inter_subset_right
  let m : C(W, V) := ⟨fun x ↦ ⟨φ x, φ.map_source x.2.1, by
      simpa [V, φ.left_inv x.2.1] using x.2.2⟩,
    (φ.continuousOn.comp_continuous continuous_subtype_val fun x ↦ x.2.1).subtype_mk _⟩
  set SW : Set W := ContinuousMap.subtypeVal W ⁻¹' {a}
  have hgφ : IsOpenEmbedding ((sourceRestrict φ).comp iφ) :=
    φ.isOpenEmbedding_restrict.comp
      (IsOpenEmbedding.inclusion inter_subset_left (hWo.preimage continuous_subtype_val))
  have hgφS : (sourceRestrict φ).comp iφ ⁻¹' {φ a} = SW := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, ContinuousMap.comp_apply, SW]
    exact ⟨fun h ↦ φ.injOn x.2.1 haφ h, fun h ↦ by rw [← h]; rfl⟩
  have : IsIso (localHomologyMap Z ((sourceRestrict φ).comp iφ) hgφS.subset (n + 1)) :=
    isIso_localHomologyMap Z _ hgφ hgφS isClosed_singleton
      (singleton_subset_iff.2 ⟨⟨a, haW⟩, rfl⟩) (n + 1)
  obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso
    (localHomologyMap Z ((sourceRestrict φ).comp iφ) hgφS.subset (n + 1))).2
    ((OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart (mem_refl_source (φ a)) ω
      hE).val
  have hiφ : iφ ⁻¹' (ContinuousMap.subtypeVal φ.source ⁻¹' {a}) ⊆ SW := fun _ hx ↦ hx
  have hiχ : iχ ⁻¹' (ContinuousMap.subtypeVal χ.source ⁻¹' {a}) ⊆ SW := fun _ hx ↦ hx
  -- On the side of `φ`, the class `w` gives the oriented-chart local orientation of `φ`.
  have hφ := localHomologyMap_subtypeVal_eq_localOrientationOfOrientedChart ω hE φ haφ
    (localHomologyMap Z iφ hiφ (n + 1) w) (by
      rw [← ConcreteCategory.comp_apply, localHomologyMap_comp]
      exact hw)
  -- On the side of `χ`, it gives `s` times the model local orientation at `χ a`.
  set b := (χ ∘ φ.symm) (φ a)
  have hb : χ a = b := by simp [b, φ.left_inv haφ]
  have hSχ : sourceRestrict χ ⁻¹' {b} ⊆ ContinuousMap.subtypeVal χ.source ⁻¹' {a} := by
    rw [← hb]
    exact sourceRestrict_preimage χ haχ
  let τV : C(V, E) := ⟨V.domRestrict (χ ∘ φ.symm), hτc.domRestrict⟩
  let tV : C(V, E) := ⟨fun y : V ↦ b + (y - φ a), by fun_prop⟩
  let T : C(E, E) := ⟨fun y ↦ b + (y - φ a), by fun_prop⟩
  have hm : m ⁻¹' {⟨φ a, mem_of_mem_nhds hU⟩} ⊆ SW := fun x hx ↦
    φ.injOn x.2.1 haφ (congrArg Subtype.val (mem_singleton_iff.1 hx))
  have h₁ : (sourceRestrict χ).comp iχ = τV.comp m := by
    ext x
    simp [τV, m, iχ, sourceRestrict_apply, φ.left_inv x.2.1]
  have h₂ : tV.comp m = T.comp ((sourceRestrict φ).comp iφ) := by
    ext x
    simp [tV, T, m, iφ, sourceRestrict_apply]
  have e₁ : localHomologyMap Z iχ hiχ (n + 1) ≫ localHomologyMap Z (sourceRestrict χ) hSχ (n + 1) =
      s • (localHomologyMap Z ((sourceRestrict φ).comp iφ) hgφS.subset (n + 1) ≫
        localHomologyMap Z T (translate_preimage_subset (φ a) b) (n + 1)) := by
    rw [localHomologyMap_comp, localHomologyMap_congr Z h₁,
      ← localHomologyMap_comp Z m τV (W := {b}) hm (fun y hy ↦ Subtype.ext (hτinj y y.2 hy)), key,
      Preadditive.comp_zsmul, localHomologyMap_comp, localHomologyMap_congr Z h₂,
      ← localHomologyMap_comp]
  have hs : s * s = 1 := by
    rcases hdet.lt_or_gt with h | h <;> simp [s, sign_neg, sign_pos, h]
  have hχw : localHomologyMap Z (sourceRestrict χ) hSχ (n + 1)
      (s • localHomologyMap Z iχ hiχ (n + 1) w) =
      ((OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart (mem_refl_source b) ω
        hE).val := by
    have hz (F : localHomology Z SW (n + 1) ⟶ localHomology Z {b} (n + 1)) (x) :
        (s • F) x = s • F x :=
      congrArg (fun L ↦ L x) (ModuleCat.hom_zsmul s F)
    rw [map_zsmul, ← ConcreteCategory.comp_apply, e₁, hz, ConcreteCategory.comp_apply, hw,
      localHomologyMap_translate_localOrientationOfOrientedChart_refl (mem_refl_source (φ a))
        (mem_refl_source b) (translate_preimage_subset (φ a) b) ω hE, smul_smul, hs,
      one_smul]
  have hχ := localHomologyMap_subtypeVal_eq_localOrientationOfOrientedChart_of_eq ω hE χ haχ hb
    _ hSχ hχw
  -- Both sides come from the class `w` on the common part of the two sources.
  have hW : (ContinuousMap.subtypeVal χ.source).comp iχ =
      (ContinuousMap.subtypeVal φ.source).comp iφ := rfl
  have e₂ := ConcreteCategory.congr_hom ((localHomologyMap_comp Z iχ
      (ContinuousMap.subtypeVal χ.source) hiχ subset_rfl (n + 1)).trans
    ((localHomologyMap_congr Z hW _ (n + 1)).trans
      (localHomologyMap_comp Z iφ (ContinuousMap.subtypeVal φ.source) hiφ subset_rfl
        (n + 1)).symm)) w
  simp only [ConcreteCategory.comp_apply] at e₂
  rw [← hχ, map_zsmul, e₂, hφ]

end ChartChange

section Manifold

variable {M E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] {n : ℕ} (hE : finrank ℝ E = n + 1)

/-- A chart orientation of an orientation lift selects the oriented-chart local orientation of
the model orientation, times the chart sign. -/
private theorem coe_localOrientationOfOrientedChart_chartOrientation
    (l : Manifold.OrientationLift 𝓘(ℝ, E) M (Fin (n + 1))) (α : M) (y : (chartAt E α).source)
    (φ : OpenPartialHomeomorph M E) {a : M} (ha : a ∈ φ.source) :
    (φ.localOrientationOfOrientedChart ha (l.chartOrientation α y) hE).val =
      (l.sign α y : ℤ) • (φ.localOrientationOfOrientedChart ha l.modelOrientation hE).val := by
  rw [Manifold.OrientationLift.chartOrientation_eq_ite]
  rcases Int.units_eq_one_or (l.sign α y) with h | h
  · simp [h]
  · have hn : (-1 : ℤˣ) ≠ 1 := by decide
    simp [h, hn, LocalOrientation.coe_neg]

omit [T2Space M] in
/-- The product of the chart signs of an orientation lift at a point is the sign of the Jacobian
of the transition map. -/
private theorem coe_sign_mul_sign_eq_sign_det
    (l : Manifold.OrientationLift 𝓘(ℝ, E) M (Fin (n + 1))) {x a : M}
    (ha : a ∈ (chartAt E x).source) :
    ((l.sign x ⟨a, ha⟩ * l.sign a ⟨a, mem_chart_source E a⟩ : ℤˣ) : ℤ) =
      (SignType.sign (fderiv ℝ (chartAt E a ∘ (chartAt E x).symm) (chartAt E x a)).det : ℤ) := by
  have h := l.sign_mul_sign x a a ha (mem_chart_source E a)
  have hext : (extChartAt 𝓘(ℝ, E) a ∘ (extChartAt 𝓘(ℝ, E) x).symm) =
      (chartAt E a ∘ (chartAt E x).symm) := by
    rw [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm]
    rfl
  rwa [hext, ModelWithCorners.range_eq_univ, fderivWithin_univ, extChartAt_coe,
    modelWithCornersSelf_coe, Function.id_comp] at h

/-- At a point `a` in the source of the preferred chart at `x`, the local orientation selected by
an orientation lift in the preferred chart at `a` is the one it selects in the preferred chart at
`x`. -/
private theorem localOrientationOfOrientedChart_chartAt_eq
    (l : Manifold.OrientationLift 𝓘(ℝ, E) M (Fin (n + 1))) {x a : M}
    (ha : a ∈ (chartAt E x).source) :
    (chartAt E a).localOrientationOfOrientedChart (mem_chart_source E a)
        (l.chartOrientation a ⟨a, mem_chart_source E a⟩) hE =
      (chartAt E x).localOrientationOfOrientedChart ha (l.chartOrientation x ⟨a, ha⟩) hE := by
  set f := chartAt E a ∘ (chartAt E x).symm
  have hs := coe_sign_mul_sign_eq_sign_det l ha
  have hdet : (fderiv ℝ f (chartAt E x a)).det ≠ 0 := by
    intro h
    rw [h, sign_zero, SignType.coe_zero] at hs
    exact (Units.ne_zero _) hs
  have hdiff : DifferentiableAt ℝ f (chartAt E x a) := by
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hdet
    exact hdet (by simp [ContinuousLinearMap.det, hE])
  apply Subtype.ext
  rw [coe_localOrientationOfOrientedChart_chartOrientation,
    coe_localOrientationOfOrientedChart_chartOrientation,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul _ hE
      (chartAt E x) (chartAt E a) ha (mem_chart_source E a) hdiff.hasFDerivAt hdet,
    ← hs, smul_smul]
  congr 1
  rcases Int.units_eq_one_or (l.sign a ⟨a, mem_chart_source E a⟩) with h | h <;> simp [h]

omit [T2Space M] in
/-- Near every point `x`, a closed ball about `x` in the preferred chart at `x` on which the chart
sign of an orientation lift is constant. -/
private theorem exists_closedBall_sign_eq
    (l : Manifold.OrientationLift 𝓘(ℝ, E) M (Fin (n + 1))) (x : M) :
    ∃ r > 0, closedBall (chartAt E x x) r ⊆ (chartAt E x).target ∧
      ∀ a (ha : a ∈ (chartAt E x).source), chartAt E x a ∈ closedBall (chartAt E x x) r →
        l.sign x ⟨a, ha⟩ = l.sign x ⟨x, mem_chart_source E x⟩ := by
  set φ := chartAt E x
  set O : Set M := Subtype.val '' {a : φ.source | l.sign x a = l.sign x ⟨x, mem_chart_source E x⟩}
  have hO : IsOpen O := φ.open_source.isOpenMap_subtype_val _
    ((l.locallyConstant_sign x).isOpen_fiber _)
  have hxV : φ x ∈ φ.target ∩ φ.symm ⁻¹' O :=
    ⟨φ.map_source (mem_chart_source E x), by
      rw [mem_preimage, φ.left_inv (mem_chart_source E x)]
      exact ⟨⟨x, mem_chart_source E x⟩, rfl, rfl⟩⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 (φ.isOpen_inter_preimage_symm hO) _ hxV
  have hK : closedBall (φ x) (ε / 2) ⊆ φ.target ∩ φ.symm ⁻¹' O :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεV
  refine ⟨ε / 2, half_pos hε, fun z hz ↦ (hK hz).1, fun a ha haK ↦ ?_⟩
  obtain ⟨b, hb, hba⟩ := (hK haK).2
  rw [φ.left_inv ha] at hba
  subst hba
  exact hb

/-- The local orientations selected by an orientation lift in the preferred charts are carried to
each other by transport along paths. -/
private theorem localOrientationTransport_chartAt
    (l : Manifold.OrientationLift 𝓘(ℝ, E) M (Fin (n + 1))) {x y : FundamentalGroupoid M}
    (f : x ⟶ y) :
    localOrientationTransport M E (n + 1) f
        ((chartAt E x.as).localOrientationOfOrientedChart (mem_chart_source E x.as)
          (l.chartOrientation x.as ⟨x.as, mem_chart_source E x.as⟩) hE) =
      (chartAt E y.as).localOrientationOfOrientedChart (mem_chart_source E y.as)
        (l.chartOrientation y.as ⟨y.as, mem_chart_source E y.as⟩) hE := by
  set z : ∀ a : M, LocalOrientation M a (n + 1) := fun a ↦
    (chartAt E a).localOrientationOfOrientedChart (mem_chart_source E a)
      (l.chartOrientation a ⟨a, mem_chart_source E a⟩) hE
  -- Around each point, a ball in its preferred chart on which the chart sign is constant.
  choose r hr hrφ hrs using exists_closedBall_sign_eq l
  let U (b : M) : Set M := (chartAt E b).symm '' ball (chartAt E b b) (r b)
  have hU (b : M) : U b ∈ 𝓝 b := by
    have h := (chartAt E b).symm.image_mem_nhds (mem_chart_target E b)
      (ball_mem_nhds (chartAt E b b) (hr b))
    rwa [(chartAt E b).left_inv (mem_chart_source E b)] at h
  -- Along a path in `U b`, transport carries `z` at its start to `z` at its end.
  have hpath (b : M) {c d : M} (γ : Path c d) (hγ : ∀ t, γ t ∈ U b) :
      localOrientationTransport M E (n + 1)
        (Path.Homotopic.Quotient.mk γ : FundamentalGroupoid.mk c ⟶ FundamentalGroupoid.mk d)
        (z c) = z d := by
    set φ := chartAt E b
    have hγK (t) : γ t ∈ φ.symm '' closedBall (φ b) (r b) :=
      image_mono ball_subset_closedBall (hγ t)
    have hmem {e : M} (he : e ∈ φ.symm '' closedBall (φ b) (r b)) :
        ∃ h : e ∈ φ.source, z e = φ.localOrientationOfOrientedChart h
          (l.chartOrientation b ⟨b, mem_chart_source E b⟩) hE := by
      obtain ⟨q, hq, rfl⟩ := he
      have hq' : φ.symm q ∈ φ.source := φ.map_target (hrφ b hq)
      refine ⟨hq', ?_⟩
      simp only [z]
      have hsign := hrs b (φ.symm q) hq' (by rwa [φ.right_inv (hrφ b hq)])
      rw [localOrientationOfOrientedChart_chartAt_eq hE l hq',
        Manifold.OrientationLift.chartOrientation_eq_ite,
        Manifold.OrientationLift.chartOrientation_eq_ite, hsign]
    obtain ⟨hc, hzc⟩ := hmem (γ.source ▸ hγK 0)
    obtain ⟨hd, hzd⟩ := hmem (γ.target ▸ hγK 1)
    rw [hzc, hzd]
    exact φ.localOrientationTransport_localOrientationOfOrientedChart _ hE
      (convex_closedBall _ _) (isCompact_closedBall _ _) (hrφ b) γ hγK hc hd
  -- The path classes along which transport carries `z` to `z` form a subgroupoid.
  let S : Subgroupoid (FundamentalGroupoid M) :=
    { arrows c d := {g | localOrientationTransport M E (n + 1) g (z c.as) = z d.as}
      inv {c d g} hg := by
        rw [Set.mem_ofPred_eq, ← hg, ← Equiv.trans_apply, ← localOrientationTransport_comp]
        simp
      mul {c d e g} hg {g'} hg' := by
        rw [Set.mem_ofPred_eq, localOrientationTransport_comp, Equiv.trans_apply, hg, hg'] }
  -- It contains the classes of paths in the sets `U b`, so it is everything.
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← FundamentalGroupoid.iSup_im_map_subtypeVal_eq_top (U := U)
      fun b ↦ ⟨b, hU b⟩]
    refine iSup_le fun b ↦ ?_
    rw [Subgroupoid.im, Subgroupoid.map_le_iff_le_comap]
    rintro ⟨⟨c⟩, ⟨d⟩, g⟩ -
    induction g using Path.Homotopic.Quotient.ind with | mk γ =>
    exact hpath b (γ.map continuous_subtype_val) fun t ↦ (γ t).2
  have hf : f ∈ S.arrows x y := hS ▸ trivial
  exact hf

end Manifold

namespace Manifold.Orientation

variable {M E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] {n : ℕ}
  (hE : finrank ℝ E = n + 1)

/-- **A smooth orientation is a homological orientation.** An orientation `o` of a boundaryless
`C¹` manifold modelled on an `(n + 1)`-dimensional real inner product space selects, at every
point, the local orientation of its oriented preferred chart
(`TauCeti.localOrientationOfManifoldOrientation`), and these local orientations are carried to
each other by transport along paths. -/
def toHomologicalOrientation (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1))) :
    HomologicalOrientation M E (n + 1) where
  toFun x := localOrientationOfManifoldOrientation o hE x
  localOrientationTransport_toFun' f := by
    induction o using Manifold.Orientation.inductionOn with
    | _ l =>
      simp only [localOrientationOfManifoldOrientation_mk]
      exact localOrientationTransport_chartAt hE l f

/-- The homological orientation of a smooth orientation `o` is, at every point, the local
orientation selected by `o`. -/
@[simp]
theorem toHomologicalOrientation_apply (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (x : M) : o.toHomologicalOrientation hE x = localOrientationOfManifoldOrientation o hE x :=
  (rfl)

/-- Reversing a smooth orientation reverses its homological orientation. -/
@[simp]
theorem toHomologicalOrientation_neg (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1))) :
    (-o).toHomologicalOrientation hE = -o.toHomologicalOrientation hE :=
  HomologicalOrientation.ext fun x ↦ by
    simp [localOrientationOfManifoldOrientation_neg]

/-- **Distinct smooth orientations have distinct homological orientations.** -/
theorem toHomologicalOrientation_injective :
    Function.Injective (toHomologicalOrientation (M := M) hE) := by
  intro o o' h
  refine Manifold.Orientation.ext fun x ↦ ?_
  have hx := DFunLike.congr_fun h x
  induction o using Manifold.Orientation.inductionOn with
  | _ l =>
    induction o' using Manifold.Orientation.inductionOn with
    | _ l' =>
      simp only [toHomologicalOrientation_apply, localOrientationOfManifoldOrientation_mk] at hx
      rw [orientationAt_mk, orientationAt_mk, l.orientationAt_eq, l'.orientationAt_eq]
      rcases _root_.Orientation.eq_or_eq_neg (l.chartOrientation x ⟨x, mem_chart_source E x⟩)
          (l'.chartOrientation x ⟨x, mem_chart_source E x⟩) (by simp [hE]) with h' | h'
      · exact h'
      · -- Opposite orientations select opposite local orientations, which differ.
        rw [h', OpenPartialHomeomorph.localOrientationOfOrientedChart_neg] at hx
        exact absurd (congrArg Subtype.val hx) (IsLocalOrientation.neg_ne
          (singularHomologyComplSingletonIsoOfOrientation _ (chartAt E x) (mem_chart_source E x)
            (l'.chartOrientation x ⟨x, mem_chart_source E x⟩) hE)
          (OpenPartialHomeomorph.localOrientationOfOrientedChart _ _ _ hE).property)

end Manifold.Orientation

end TauCeti
