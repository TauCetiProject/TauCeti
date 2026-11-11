/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Generic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Degree

import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The Euler number as a signed count of transverse zeros

Let `M` be a boundaryless manifold of dimension `n + 1`, modelled on a real inner product space
`X` and oriented by a smooth orientation `oM`, and let `E → M` be a real vector bundle of rank
`n + 1` with orientation `o`. At a zero `z` of a section `s` which is differentiable at `z` and
whose linearization `Dₛ(z) : T_z M → E_z` (`TauCeti.sectionLinearization`) is invertible, the local
index of `s` (`TauCeti.VectorBundleOrientation.sectionIndex`, with respect to the homological
orientation of `oM`) is the orientation sign of `Dₛ(z)`: it is `1` if `Dₛ(z)` carries the
orientation of `T_z M` to that of `E_z`, and `-1` otherwise.

Combined with the sum-of-local-indices formula
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`, this
evaluates the Euler class of `E` on the fundamental class of a compact `M` as the signed count of
the zeros of any section all of whose zeros are transverse, and such sections exist when the
bundle is smooth (`TauCeti.exists_contMDiffSection_regular_finite_zero_of_finrank_eq`).

The proof reads the section in the preferred chart `φ` at `z`, composed with the linear
equivalence `Λ = e_z ∘ Dₛ(z) : X ≃ F` given by the linearization followed by the preferred
trivialization `e` at `z`. In these coordinates the section has derivative the identity at the
image of `z`, so `TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`
computes the local index as `1`, once the coordinate chart `Λ ∘ φ` is known to carry the local
orientation of `oM` at `z` to the local orientation of `F` selected by the orientation that `e`
reads on the fibres near `z`. That follows from the description of the homological orientation of
`oM` by oriented charts (`TauCeti.localOrientationOfManifoldOrientation_eq`) and from the
comparison, for a real inner product space `X`, of the local orientation of `X` at the origin
selected by an orientation (`Orientation.localOrientation`) with the one selected in the identity
chart (`Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl`).

## Main results

* `Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl`: in a real inner product
  space, the local orientation at the origin selected by an orientation is the one selected by it
  in the identity chart.
* `TauCeti.VectorBundleOrientation.sectionIndex_toHomologicalOrientation_eq_one` and
  `TauCeti.VectorBundleOrientation.sectionIndex_toHomologicalOrientation_eq_neg_one`: at a zero
  with invertible linearization, the local index is `1` or `-1` according as the linearization
  preserves or reverses the orientations;
  `TauCeti.VectorBundleOrientation.sectionIndex_toHomologicalOrientation_eq_ite` combines them at
  a zero with surjective linearization.
* `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sign`: on a compact
  manifold, the Euler class evaluated on the fundamental class is the signed count of the zeros of
  a section with only transverse zeros.
* `TauCeti.VectorBundleOrientation.exists_contMDiffSection_eulerClass_eq_sum_sign`:
  a smooth oriented bundle of rank the dimension of a compact oriented manifold has a smooth section
  with finitely many zeros, all transverse, whose signed count is the Euler number.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 and Problem 11-C.
* G. E. Bredon, *Topology and Geometry*, Graduate Texts in Mathematics 139, Springer (1993),
  Chapter VI, §12.
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

section Model

variable {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] {n : ℕ}

private theorem zero_mem_refl_source (X : Type) [TopologicalSpace X] [Zero X] :
    (0 : X) ∈ (OpenPartialHomeomorph.refl X).source := by
  rw [OpenPartialHomeomorph.refl_source]
  exact mem_univ _

/-- A linear isometry carries the local orientation at the origin selected by `ν` in the identity
chart to the one selected by the transported orientation in the identity chart: both are read
through the connecting morphism, radial projection, and the sphere generators, which the isometry
preserves. -/
private theorem localHomologyMap_linearIsometryEquiv_localOrientationOfOrientedChart_refl
    (f : X ≃ₗᵢ[ℝ] Y) (ν : Orientation ℝ X (Fin (n + 1))) (hX : finrank ℝ X = n + 1)
    (hY : finrank ℝ Y = n + 1)
    (h : (⟨f, f.continuous⟩ : C(X, Y)) ⁻¹' {0} ⊆ {0}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (⟨f, f.continuous⟩ : C(X, Y)) h (n + 1)
        ((OpenPartialHomeomorph.refl X).localOrientationOfOrientedChart
          (zero_mem_refl_source X) ν hX).val =
      ((OpenPartialHomeomorph.refl Y).localOrientationOfOrientedChart (zero_mem_refl_source Y)
        (ν.map _ f.toLinearEquiv) hY).val := by
  set R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let eX := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl X)
    (zero_mem_refl_source X) ν hX
  let eY := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl Y)
    (zero_mem_refl_source Y) (ν.map _ f.toLinearEquiv) hY
  -- Radial projection onto the unit spheres commutes with the isometry.
  have hsq : TopPair.Hom.snd (TopPair.ofSubsetMap (X := TopCat.of X) (Y := TopCat.of Y)
        (TopCat.ofHom (⟨f, f.continuous⟩ : C(X, Y))) (B := {0}ᶜ) (B' := {0}ᶜ)
        ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 h))) ≫
      TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : Y)).toFun =
      TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : X)).toFun ≫
        TopCat.ofHom ⟨f.toLinearIsometry.unitSphereMap,
          f.toLinearIsometry.continuous_unitSphereMap⟩ := by
    ext x
    -- The subspace of `TopPair.ofSubset` is the subtype only after unfolding the pair.
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    refine (coe_complSingletonHomotopyEquivSphere_apply (0 : Y) _).trans ?_
    erw [TopPair.ofSubsetMap_snd_apply, LinearIsometry.coe_unitSphereMap_apply,
      coe_complSingletonHomotopyEquivSphere_apply]
    simp
  have key : localHomologyMap R (⟨f, f.continuous⟩ : C(X, Y)) h (n + 1) ≫ eY.hom = eX.hom := by
    simp only [eX, eY, singularHomologyComplSingletonIsoOfOrientation_refl_hom]
    rw [localHomologyMap_def, ← TopPair.reducedSingularHomologyδ_naturality_assoc]
    congr 1
    -- The composite is only type-correct after unfolding the subspace of the pair.
    erw [← Functor.map_comp_assoc, hsq, Functor.map_comp_assoc]
    exact congrArg _ (reducedSingularHomologySphereIsoOfOrientation_hom_naturality R ν
      (ν.map _ f.toLinearEquiv) f rfl hX)
  rw [OpenPartialHomeomorph.coe_localOrientationOfOrientedChart,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  apply (ConcreteCategory.bijective_of_isIso eY.hom).1
  rw [← ConcreteCategory.comp_apply, key]
  exact (eX.inv_hom_id_apply 1).trans (eY.inv_hom_id_apply 1).symm

end Model

end TauCeti

namespace Orientation

open TauCeti

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] {n : ℕ}

/-- **The local orientation of an orientation in the identity chart.** In a real inner product
space `X` of dimension `n + 1`, the local orientation at the origin selected by an orientation `ν`
(`Orientation.localOrientation`) is the one selected by `ν` in the identity chart of `X`. -/
theorem localOrientation_eq_localOrientationOfOrientedChart_refl
    (ν : Orientation ℝ X (Fin (n + 1))) (hX : finrank ℝ X = n + 1) :
    ν.localOrientation hX = (OpenPartialHomeomorph.refl X).localOrientationOfOrientedChart
      (by rw [OpenPartialHomeomorph.refl_source]; exact mem_univ _) ν hX := by
  have := FiniteDimensional.of_finrank_eq_succ hX
  -- Compare both with the Euclidean model through a linear isometry.
  let f : X ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ULift.{0} (Fin (n + 1))) :=
    ((stdOrthonormalBasis ℝ X).reindex ((finCongr hX).trans Equiv.ulift.symm)).repr
  have hM : finrank ℝ (EuclideanSpace ℝ (ULift.{0} (Fin (n + 1)))) = n + 1 :=
    finrank_euclideanSpace_ulift_fin (n + 1)
  have hmap := localOrientation_map f.toContinuousLinearEquiv ν hX hM
  rw [localOrientation_euclideanSpace] at hmap
  have hiso : IsIso (TopPair.singularHomologyMap f.toContinuousLinearEquiv.complZeroPairIso.hom
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1)) := inferInstance
  apply Subtype.ext
  apply (ConcreteCategory.bijective_of_isIso (TopPair.singularHomologyMap
    f.toContinuousLinearEquiv.complZeroPairIso.hom (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1))).1
  rw [← LocalOrientation.coe_map, ← hmap, ContinuousLinearEquiv.complZeroPairIso_hom]
  have h := localHomologyMap_linearIsometryEquiv_localOrientationOfOrientedChart_refl f ν hX hM
    (fun x hx ↦ by simpa using hx)
  rw [← localHomologyMap_def]
  exact h.symm

end Orientation

universe u v

namespace TauCeti

section Chart

variable {C : Type u} [Category.{v} C] [Limits.HasCoproducts.{0} C] [Abelian C] (R : C)
  {M X : Type} [TopologicalSpace M] [T1Space M] [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The restriction of a chart to its source, as a continuous map. -/
private def chartSourceRestrict (φ : OpenPartialHomeomorph M X) : C(φ.source, X) :=
  ⟨φ.source.domRestrict φ, φ.continuousOn.domRestrict⟩

omit [T1Space M] [InnerProductSpace ℝ X] in
private theorem chartSourceRestrict_preimage (φ : OpenPartialHomeomorph M X) {a : M}
    (ha : a ∈ φ.source) :
    chartSourceRestrict φ ⁻¹' {φ a} ⊆ ContinuousMap.subtypeVal φ.source ⁻¹' {a} :=
  fun x hx ↦ φ.injOn x.2 ha hx

omit [InnerProductSpace ℝ X] in
/-- The local homology isomorphism of a chart `φ` at `a` is the inverse of the excision
isomorphism of the source of `φ`, followed by the map induced by `φ` on the source. -/
private theorem localHomologyMap_subtypeVal_comp_chartIso_hom (φ : OpenPartialHomeomorph M X)
    {a : M} (ha : a ∈ φ.source) (k : ℕ) :
    localHomologyMap R (ContinuousMap.subtypeVal φ.source)
        (S := ContinuousMap.subtypeVal φ.source ⁻¹' {a}) (T := {a}) subset_rfl k ≫
          (singularHomologyComplSingletonIsoOfChart R φ ha k).hom =
      localHomologyMap R (chartSourceRestrict φ) (chartSourceRestrict_preimage φ ha) k := by
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
  have h₂ : localHomologyMap R (chartSourceRestrict φ) (chartSourceRestrict_preimage φ ha) k =
      TopPair.singularHomologyMap ((TopPair.ofSubsetIso (X := TopCat.of φ.source)
          (Y := TopCat.of φ.target) φ.toHomeomorphSourceTarget
          (B := Subtype.val ⁻¹' {a}ᶜ) (B' := Subtype.val ⁻¹' {φ a}ᶜ)
          fun z ↦ (φ.injOn.eq_iff z.2 ha).not.symm).hom ≫
        TopPair.excisionMap (X := TopCat.of X) φ.target {φ a}ᶜ) R k := by
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

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- **An oriented chart, followed by a linear equivalence, reads the local orientation it selects
as the local orientation of the transported orientation.** Let `φ` be a chart of `M` with values in
a real inner product space `X`, `ν` an orientation of `X`, and `L : X ≃L[ℝ] F` a linear
equivalence. The map `x ↦ L (φ x - φ z)` on the source of `φ` carries the local orientation of `M`
at `z` selected by `ν` in `φ`, read in the source through excision, to the local orientation of `F`
at the origin selected by the transported orientation `ν.map L`. -/
private theorem localHomologyMap_chart_localOrientationOfOrientedChart
    (φ : OpenPartialHomeomorph M X) {z : M} (hz : z ∈ φ.source) (L : X ≃L[ℝ] F)
    (ν : Orientation ℝ X (Fin (n + 1))) (hX : finrank ℝ X = n + 1) (hF : finrank ℝ F = n + 1)
    (σ : C(φ.source, F)) (hσ : ∀ x : φ.source, σ x = L (φ x - φ z))
    (h : σ ⁻¹' {0} ⊆ {⟨z, hz⟩}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) σ (S := {⟨z, hz⟩}) (T := {0}) h (n + 1)
        ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (n + 1)).symm
          (φ.localOrientationOfOrientedChart hz ν hX)).val =
      ((ν.map _ L.toLinearEquiv).localOrientation hF).val := by
  set Z := ModuleCat.of ℤ (ULift.{0} ℤ)
  set c := ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (n + 1)).symm
    (φ.localOrientationOfOrientedChart hz ν hX)).val
  -- `σ` is the restricted chart, followed by the translation taking `φ z` to the origin and by `L`.
  set sR := chartSourceRestrict φ
  let T : C(X, X) := ⟨fun y ↦ 0 + (y - φ z), by fun_prop⟩
  let Lc : C(X, F) := ⟨L, L.continuous⟩
  have hsR : sR ⁻¹' {φ z} ⊆ {⟨z, hz⟩} := fun x hx ↦ Subtype.ext (φ.injOn x.2 hz hx)
  have hT : T ⁻¹' {0} ⊆ {φ z} := fun y hy ↦ sub_eq_zero.1 (add_eq_left.1 hy)
  have hL : Lc ⁻¹' {0} ⊆ {0} := fun y hy ↦ by simpa [Lc] using hy
  have hσ' : σ = Lc.comp (T.comp sR) :=
    ContinuousMap.ext fun x ↦ by simp [hσ, Lc, T, sR, chartSourceRestrict]
  have hcomp : localHomologyMap Z σ h (n + 1) = localHomologyMap Z sR hsR (n + 1) ≫
      localHomologyMap Z T hT (n + 1) ≫ localHomologyMap Z Lc hL (n + 1) := by
    rw [localHomologyMap_comp, localHomologyMap_comp]
    exact localHomologyMap_congr Z hσ' h (n + 1)
  -- The restricted chart carries `c` to the local orientation of `X` at `φ z` selected by `ν` in
  -- the identity chart: read through the excision of the source, this is the definition of the
  -- oriented-chart local orientation.
  have hid : ContinuousMap.id φ.source ⁻¹' (ContinuousMap.subtypeVal φ.source ⁻¹' {z}) ⊆
      {⟨z, hz⟩} := fun x (hx : x.1 = z) ↦ Subtype.ext hx
  have hc : localHomologyMap Z (ContinuousMap.subtypeVal φ.source) (S := {⟨z, hz⟩}) (T := {z})
      (fun x (hx : x.1 = z) ↦ Subtype.ext hx) (n + 1) c =
        (φ.localOrientationOfOrientedChart hz ν hX).val :=
    φ.open_source.isOpenEmbedding_subtypeVal.localHomologyMap_localOrientationEquiv_symm ⟨z, hz⟩
      (φ.localOrientationOfOrientedChart hz ν hX) (fun x (hx : x.1 = z) ↦ Subtype.ext hx)
  have hA : localHomologyMap Z sR hsR (n + 1) c =
      ((OpenPartialHomeomorph.refl X).localOrientationOfOrientedChart
        (by rw [OpenPartialHomeomorph.refl_source]; exact mem_univ (φ z)) ν hX).val := by
    have h₁ : localHomologyMap Z sR hsR (n + 1) c =
        (localHomologyMap Z (ContinuousMap.id φ.source) hid (n + 1) ≫
          localHomologyMap Z sR (chartSourceRestrict_preimage φ hz) (n + 1)) c := by
      rw [localHomologyMap_comp]
      rfl
    have h₂ : (localHomologyMap Z (ContinuousMap.id φ.source) hid (n + 1) ≫
        localHomologyMap Z sR (chartSourceRestrict_preimage φ hz) (n + 1)) c =
        (singularHomologyComplSingletonIsoOfChart Z φ hz (n + 1)).hom
          (localHomologyMap Z (ContinuousMap.subtypeVal φ.source) (S := {⟨z, hz⟩}) (T := {z})
            (fun x (hx : x.1 = z) ↦ Subtype.ext hx) (n + 1) c) := by
      rw [← localHomologyMap_subtypeVal_comp_chartIso_hom Z φ hz (n + 1), ← Category.assoc,
        localHomologyMap_comp]
      rfl
    rw [h₁, h₂, hc, OpenPartialHomeomorph.coe_localOrientationOfOrientedChart,
      OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
    let e₀ := singularHomologyComplSingletonIsoOfOrientation Z (OpenPartialHomeomorph.refl X)
      (by rw [OpenPartialHomeomorph.refl_source]; exact mem_univ (φ z)) ν hX
    apply (ConcreteCategory.bijective_of_isIso e₀.hom).1
    rw [← ConcreteCategory.comp_apply, ← singularHomologyComplSingletonIsoOfOrientation_hom_eq,
      Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  -- The translation carries it to the local orientation at the origin, which `L` carries to the
  -- local orientation selected by `ν.map L`.
  have hB := localHomologyMap_translate_localOrientationOfOrientedChart_refl
    (by rw [OpenPartialHomeomorph.refl_source]; exact mem_univ (φ z))
    (by rw [OpenPartialHomeomorph.refl_source]; exact mem_univ 0) hT ν hX
  have hC : localHomologyMap Z Lc hL (n + 1)
      ((OpenPartialHomeomorph.refl X).localOrientationOfOrientedChart
        (by rw [OpenPartialHomeomorph.refl_source]; exact mem_univ 0) ν hX).val =
      ((ν.map _ L.toLinearEquiv).localOrientation hF).val := by
    rw [Orientation.localOrientation_map L ν hX hF, LocalOrientation.coe_map,
      ← Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl,
      ContinuousLinearEquiv.complZeroPairIso_hom, ← localHomologyMap_def]
    rfl
  rw [hcomp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hA, hB, hC]

end Chart

namespace VectorBundleOrientation

variable {X M : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [TopologicalSpace M] [ChartedSpace X M] [T2Space M] [IsManifold 𝓘(ℝ, X) 1 M] {n : ℕ}
  (hX : finrank ℝ X = n + 1)
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {E : M → Type}
  [TopologicalSpace (TotalSpace F E)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  (o : VectorBundleOrientation F E (Fin (n + 1))) (hF : finrank ℝ F = n + 1)
  (oM : Manifold.Orientation 𝓘(ℝ, X) M (Fin (n + 1))) {s : ∀ x, E x}
  (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))

/-- **The local index at an orientation-preserving transverse zero is `1`.** Let `z` be a zero of
a section `s` of an oriented bundle `E` of rank `n + 1` over a manifold oriented by `oM`, at which
`s` is differentiable with invertible linearization `D : T_z M ≃ E_z`. If `D` carries the
orientation of `T_z M` to that of the fibre `E_z`, then the local index of `s` at `z`, with
respect to the homological orientation of `oM`, is `1`. -/
theorem sectionIndex_toHomologicalOrientation_eq_one {z : M} (hz : s z = 0)
    (hsd : MDifferentiableAt 𝓘(ℝ, X) (𝓘(ℝ, X).prod 𝓘(ℝ, F))
      (fun x ↦ TotalSpace.mk' F x (s x)) z)
    (D : TangentSpace 𝓘(ℝ, X) z ≃L[ℝ] E z)
    (hD : (D : TangentSpace 𝓘(ℝ, X) z →L[ℝ] E z) = sectionLinearization (F := F) 𝓘(ℝ, X) id s z)
    (ho : (oM.orientationAt z).map _ D.toLinearEquiv = o z) :
    o.sectionIndex hF (oM.toHomologicalOrientation hX) hs z = 1 := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  set e := trivializationAt F E z
  have hze : z ∈ e.baseSet := mem_baseSet_trivializationAt F E z
  -- The fibre coordinate of `s` in the preferred trivialization, and its derivative in the chart.
  have hg : MDifferentiableAt 𝓘(ℝ, X) 𝓘(ℝ, F) (fun y ↦ (e ⟨y, s y⟩).2) z :=
    ((mdifferentiableAt_totalSpace 𝓘(ℝ, X) (fun x ↦ TotalSpace.mk' F x (s x))).1 hsd).2
  have hgc : HasFDerivAt ((fun y ↦ (e ⟨y, s y⟩).2) ∘ (chartAt X z).symm)
      ((e.continuousLinearMapAt ℝ z).comp (sectionLinearization (F := F) 𝓘(ℝ, X) id s z))
      (chartAt X z z) := by
    have h₁ := (TauCeti.mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm.1
      hg).hasFDerivAt
    rw [← TauCeti.mvfderiv_eq_fderiv_comp_extChartAt_symm] at h₁
    erw [continuousLinearMapAt_comp_sectionLinearization continuousAt_id hze hg hz]
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def, id] at h₁
    exact h₁
  -- The chart `φ = Λ ∘ chartAt X z`, where `Λ = e_z ∘ D`, in which the section has derivative the
  -- identity at `φ z`.
  let Λ : X ≃L[ℝ] F := D.trans (e.continuousLinearEquivAt ℝ z hze)
  let φ : OpenPartialHomeomorph M F := (chartAt X z).transHomeomorph Λ.toHomeomorph
  have hzφ : z ∈ φ.source := mem_chart_source X z
  have hA : HasFDerivAt (fun y ↦ (e (TotalSpace.mk' F (φ.symm y) (s (φ.symm y)))).2)
      (ContinuousLinearMap.id ℝ F) (φ z) := by
    have hpt : chartAt X z z = Λ.symm (φ z) := (Λ.symm_apply_apply _).symm
    rw [hpt] at hgc
    have h₂ := hgc.comp (φ z) Λ.symm.hasFDerivAt
    convert h₂ using 1
    · ext v
      rfl
    ext v
    change v = e.continuousLinearMapAt ℝ z
      (sectionLinearization (F := F) 𝓘(ℝ, X) id s z (Λ.symm v))
    rw [← hD, ← e.coe_continuousLinearEquivAt_eq hze]
    exact (Λ.apply_symm_apply v).symm
  have hf0 : (e (TotalSpace.mk' F (φ.symm (φ z)) (s (φ.symm (φ z))))).2 = 0 := by
    rw [φ.left_inv hzφ, hz]
    exact congrArg Prod.snd (e.zeroSection ℝ hze)
  -- An isolating neighbourhood of `z` on which `e` reads the fibre orientations as at `z`.
  have hne : ∀ᶠ y in 𝓝[≠] (φ z), (e (TotalSpace.mk' F (φ.symm y) (s (φ.symm y)))).2 ≠
      (e (TotalSpace.mk' F (φ.symm (φ z)) (s (φ.symm (φ z))))).2 :=
    hA.eventually_ne ⟨1, by simpa using AntilipschitzWith.id⟩
  obtain ⟨V, hV, hVo, hzV⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hne)
  obtain ⟨W, hW, hWo, hzW⟩ := eventually_nhds_iff.1
    (o.eventually_mapOrientation_eq (by simp [hF]) e hze)
  set U := (φ.source ∩ φ ⁻¹' V) ∩ (e.baseSet ∩ W)
  have hUo : IsOpen U := (φ.isOpen_inter_preimage hVo).inter (e.open_baseSet.inter hWo)
  have hzU : z ∈ U := ⟨⟨hzφ, hzV⟩, hze, hzW⟩
  have hUe : U ⊆ e.baseSet := fun x hx ↦ hx.2.1
  have hUφ : U ⊆ φ.source := fun x hx ↦ hx.1.1
  have hUz : ∀ x ∈ U, s x = 0 → x = z := by
    intro x hx hx0
    by_contra hxz
    have hne : φ x ≠ φ z := fun h ↦ hxz (φ.injOn hx.1.1 hzφ h)
    apply hV (φ x) hx.1.2 hne
    rw [hf0, φ.left_inv hx.1.1, hx0]
    exact congrArg Prod.snd (e.zeroSection ℝ (hUe hx))
  have ho' : ∀ x (hx : x ∈ U), e.mapOrientation (Fin (n + 1)) (hUe hx) (o x) =
      e.mapOrientation (Fin (n + 1)) hze (o z) := fun x hx ↦ hW x hx.2.2 (hUe hx)
  -- The chart `φ` reads the homological orientation of `oM` at `z` as the local orientation
  -- selected by the orientation that `e` reads on the fibres.
  have hmap : (oM.orientationAt z).map _ Λ.toLinearEquiv =
      e.mapOrientation (Fin (n + 1)) hze (o z) := by
    have hΛ : Λ.toLinearEquiv = D.toLinearEquiv.trans (e.linearEquivAt ℝ z hze) :=
      LinearEquiv.ext fun _ ↦ rfl
    rw [hΛ]
    refine (Orientation.map_trans D.toLinearEquiv (e.linearEquivAt ℝ z hze)
      (oM.orientationAt z)).trans ?_
    rw [ho, Trivialization.mapOrientation_apply]
  have hφ := localHomologyMap_chart_localOrientationOfOrientedChart (chartAt X z)
    (mem_chart_source X z) Λ (oM.orientationAt z) hX hF
    ⟨fun x : φ.source ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩
    (fun x ↦ (map_sub Λ _ _).symm)
    (fun x hx ↦ Subtype.ext (φ.injOn x.2 hzφ (sub_eq_zero.1 hx)))
  rw [hmap, ← localOrientationOfManifoldOrientation_eq,
    ← Manifold.Orientation.toHomologicalOrientation_apply] at hφ
  have hdet : (ContinuousLinearMap.id ℝ F).det = 1 := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
  rw [sectionIndex_eq_sign_det_of_hasFDerivAt o hF _ hs e φ hUo hzU hUz hz hUe hUφ ho' hφ hA
    (by rw [hdet]; exact one_ne_zero), hdet, sign_one, SignType.coe_one]

/-- **The local index at an orientation-reversing transverse zero is `-1`.** At a zero `z` of `s`
where `s` is differentiable with invertible linearization `D : T_z M ≃ E_z` carrying the
orientation of `T_z M` to the opposite of that of `E_z`, the local index of `s` at `z`, with respect
to the homological orientation of `oM`, is `-1`. -/
theorem sectionIndex_toHomologicalOrientation_eq_neg_one {z : M} (hz : s z = 0)
    (hsd : MDifferentiableAt 𝓘(ℝ, X) (𝓘(ℝ, X).prod 𝓘(ℝ, F))
      (fun x ↦ TotalSpace.mk' F x (s x)) z)
    (D : TangentSpace 𝓘(ℝ, X) z ≃L[ℝ] E z)
    (hD : (D : TangentSpace 𝓘(ℝ, X) z →L[ℝ] E z) = sectionLinearization (F := F) 𝓘(ℝ, X) id s z)
    (ho : (oM.orientationAt z).map _ D.toLinearEquiv = -o z) :
    o.sectionIndex hF (oM.toHomologicalOrientation hX) hs z = -1 := by
  -- For the opposite orientation of the bundle, `D` preserves the orientations.
  have h := sectionIndex_toHomologicalOrientation_eq_one hX (-o) hF oM hs hz hsd D hD
    (by rw [ho, neg_apply])
  rw [sectionIndex_neg] at h
  omega

open Classical in
/-- **The local index at a transverse zero is the orientation sign of the linearization.** At a
zero `z` of `s` where `s` is differentiable with surjective linearization `T_z M → E_z` (hence an
isomorphism, the dimensions being equal), the local index of `s` at `z` is `1` if the linearization
carries the orientation of `T_z M` to that of `E_z`, and `-1` otherwise. -/
theorem sectionIndex_toHomologicalOrientation_eq_ite {z : M} (hz : s z = 0)
    (hsd : MDifferentiableAt 𝓘(ℝ, X) (𝓘(ℝ, X).prod 𝓘(ℝ, F))
      (fun x ↦ TotalSpace.mk' F x (s x)) z)
    (hreg : Function.Surjective (sectionLinearization (F := F) 𝓘(ℝ, X) id s z)) :
    o.sectionIndex hF (oM.toHomologicalOrientation hX) hs z =
      if ∃ D : TangentSpace 𝓘(ℝ, X) z ≃L[ℝ] E z,
          (D : TangentSpace 𝓘(ℝ, X) z →L[ℝ] E z) = sectionLinearization (F := F) 𝓘(ℝ, X) id s z ∧
            (oM.orientationAt z).map _ D.toLinearEquiv = o z
        then 1 else -1 := by
  split_ifs with h
  · obtain ⟨D, hD, ho⟩ := h
    exact sectionIndex_toHomologicalOrientation_eq_one hX o hF oM hs hz hsd D hD ho
  -- The linearization is a surjection between spaces of the same dimension, hence an
  -- isomorphism, and it reverses the orientations since it does not preserve them.
  have := FiniteDimensional.of_finrank_eq_succ hF
  have := VectorBundle.finiteDimensional ℝ F E z
  have hfin : finrank ℝ (TangentSpace 𝓘(ℝ, X) z) = finrank ℝ (E z) :=
    hX.trans ((VectorBundle.finrank_eq ℝ F E z).trans hF).symm
  set A := sectionLinearization (F := F) 𝓘(ℝ, X) id s z
  have hinj : Function.Injective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f := A.toLinearMap)).2 hreg
  -- Read in the preferred trivialization `e` at `z`, `A` is an isomorphism `X ≃ F` of
  -- finite-dimensional normed spaces, hence a continuous linear equivalence.
  set e := trivializationAt F E z
  have hze : z ∈ e.baseSet := mem_baseSet_trivializationAt F E z
  let B : X →L[ℝ] F := (e.continuousLinearEquivAt ℝ z hze : E z →L[ℝ] F).comp A
  have hB : Function.Bijective B :=
    ⟨(e.continuousLinearEquivAt ℝ z hze).injective.comp hinj,
      (e.continuousLinearEquivAt ℝ z hze).surjective.comp hreg⟩
  let D : TangentSpace 𝓘(ℝ, X) z ≃L[ℝ] E z :=
    (LinearEquiv.ofBijective B.toLinearMap hB).toContinuousLinearEquiv.trans
      (e.continuousLinearEquivAt ℝ z hze).symm
  have hD : (D : TangentSpace 𝓘(ℝ, X) z →L[ℝ] E z) = A := ContinuousLinearMap.ext fun v ↦
    (e.continuousLinearEquivAt ℝ z hze).symm_apply_apply (A v)
  rcases Orientation.eq_or_eq_neg ((oM.orientationAt z).map _ D.toLinearEquiv) (o z)
    (by rw [Fintype.card_fin, VectorBundle.finrank_eq ℝ F E z, hF]) with ho | ho
  · exact absurd ⟨D, hD, ho⟩ h
  · exact sectionIndex_toHomologicalOrientation_eq_neg_one hX o hF oM hs hz hsd D hD ho

include hs in
open Classical in
/-- **The Euler number is the signed count of transverse zeros.** Let `M` be a compact boundaryless
manifold of dimension `n + 1` oriented by `oM`, and `E → M` a real vector bundle of rank `n + 1`
oriented by `o`. For a section `s` with finitely many zeros, differentiable at each of them with
surjective linearization, the Euler class of `E` evaluated on the fundamental class of `M` is the
number of zeros at which the linearization `T_z M → E_z` preserves the orientations minus the
number at which it reverses them. -/
theorem evalFundamentalClass_eulerClass_eq_sum_sign [CompactSpace M]
    (hsd : ∀ z, s z = 0 → MDifferentiableAt 𝓘(ℝ, X) (𝓘(ℝ, X).prod 𝓘(ℝ, F))
      (fun x ↦ TotalSpace.mk' F x (s x)) z)
    (hreg : ∀ z, s z = 0 → Function.Surjective (sectionLinearization (F := F) 𝓘(ℝ, X) id s z))
    (hZ : {x | s x = 0}.Finite) :
    ((oM.toHomologicalOrientation hX).evalFundamentalClass hX (ModuleCat.of ℤ (ULift.{0} ℤ))
        (ContinuousMap.id M) (o.eulerClass hF)).down =
      ∑ z ∈ hZ.toFinset, if ∃ D : TangentSpace 𝓘(ℝ, X) z ≃L[ℝ] E z,
          (D : TangentSpace 𝓘(ℝ, X) z →L[ℝ] E z) = sectionLinearization (F := F) 𝓘(ℝ, X) id s z ∧
            (oM.orientationAt z).map _ D.toLinearEquiv = o z
        then 1 else -1 := by
  rw [evalFundamentalClass_eulerClass_eq_sum_sectionIndex o hF _ hs hX hZ]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz0 : s z = 0 := hZ.mem_toFinset.1 hz
  exact sectionIndex_toHomologicalOrientation_eq_ite hX o hF oM hs hz0 (hsd z hz0) (hreg z hz0)

open Classical in
/-- **The Euler number is a signed count of zeros of a smooth section.** Let `M` be a compact
boundaryless smooth manifold of dimension `n + 1` oriented by `oM`, and `E → M` a smooth real vector
bundle of rank `n + 1` oriented by `o`. Then `E` has a smooth section with finitely many zeros, at
each of which the linearization `T_z M → E_z` is an isomorphism, and the Euler class of `E`
evaluated on the fundamental class of `M` is the number of zeros at which the linearization
preserves the orientations minus the number at which it reverses them. -/
theorem exists_contMDiffSection_eulerClass_eq_sum_sign [CompactSpace M] [IsManifold 𝓘(ℝ, X) ∞ M]
    [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F E 𝓘(ℝ, X)] :
    ∃ (s : ContMDiffSection 𝓘(ℝ, X) F ∞ E) (hZ : {x | s x = 0}.Finite),
      (∀ z, s z = 0 → Function.Surjective (sectionLinearization (F := F) 𝓘(ℝ, X) id s z)) ∧
      ((oM.toHomologicalOrientation hX).evalFundamentalClass hX (ModuleCat.of ℤ (ULift.{0} ℤ))
          (ContinuousMap.id M) (o.eulerClass hF)).down =
        ∑ z ∈ hZ.toFinset, if ∃ D : TangentSpace 𝓘(ℝ, X) z ≃L[ℝ] E z,
            (D : TangentSpace 𝓘(ℝ, X) z →L[ℝ] E z) = sectionLinearization (F := F) 𝓘(ℝ, X) id s z ∧
              (oM.orientationAt z).map _ D.toLinearEquiv = o z
          then 1 else -1 := by
  obtain ⟨s, hreg, hZ⟩ := exists_contMDiffSection_regular_finite_zero_of_finrank_eq
    (X := X) (F := F) (V := E) (hX.trans hF.symm)
  refine ⟨s, hZ, hreg, ?_⟩
  exact evalFundamentalClass_eulerClass_eq_sum_sign hX o hF oM s.contMDiff.continuous
    (fun z _ ↦ (s.contMDiff z).mdifferentiableAt (by simp)) hreg hZ

end VectorBundleOrientation

end TauCeti
