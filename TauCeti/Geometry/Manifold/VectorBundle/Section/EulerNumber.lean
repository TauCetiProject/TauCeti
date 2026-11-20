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
the zeros of a continuous section with finitely many zeros, all transverse. Such sections
exist when the bundle is smooth
(`TauCeti.exists_contMDiffSection_regular_finite_zero_of_finrank_eq`).

The proof reads the section in the preferred chart `φ` at `z`, composed with the linear
equivalence `Λ = e_z ∘ Dₛ(z) : X ≃ F` given by the linearization followed by the preferred
trivialization `e` at `z`. In these coordinates the section has derivative the identity at the
image of `z`, so `TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`
computes the local index as `1`, once the coordinate chart `Λ ∘ φ` is known to carry the local
orientation of `oM` at `z` to the local orientation of `F` selected by the orientation that `e`
reads on the fibres near `z`. That follows from the description of the homological orientation of
`oM` by oriented charts (`TauCeti.localOrientationOfManifoldOrientation_eq`) and from the
transport of the local orientation selected by an oriented chart along a linear equivalence
(`OpenPartialHomeomorph.localHomologyMap_chart_localOrientationOfOrientedChart`).

## Main results

* `TauCeti.VectorBundleOrientation.sectionIndex_toHomologicalOrientation_eq_one` and
  `TauCeti.VectorBundleOrientation.sectionIndex_toHomologicalOrientation_eq_neg_one`: at a zero
  with invertible linearization, the local index is `1` or `-1` according as the linearization
  preserves or reverses the orientations;
  `TauCeti.VectorBundleOrientation.sectionIndex_toHomologicalOrientation_eq_ite` combines them at
  a zero with surjective linearization.
* `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sign`: on a compact
  manifold, the Euler class evaluated on the fundamental class is the signed count of the zeros of
  a continuous section with finitely many zeros, all transverse.
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
  -- The fibre coordinate of `s` in the preferred trivialization is differentiable at `z`.
  have hg : MDifferentiableAt 𝓘(ℝ, X) 𝓘(ℝ, F) (fun y ↦ (e ⟨y, s y⟩).2) z :=
    ((mdifferentiableAt_totalSpace 𝓘(ℝ, X) (fun x ↦ TotalSpace.mk' F x (s x))).1 hsd).2
  -- The chart `φ = Λ ∘ chartAt X z`, where `Λ = e_z ∘ D`, in which the section has derivative the
  -- identity at `φ z`.
  let Λ : X ≃L[ℝ] F := D.trans (e.continuousLinearEquivAt ℝ z hze)
  let φ : OpenPartialHomeomorph M F := (chartAt X z).transHomeomorph Λ.toHomeomorph
  have hzφ : z ∈ φ.source := mem_chart_source X z
  have hA := e.hasFDerivAt_comp_chartAt_transHomeomorph_symm_sectionLinearization_id
    hze hz hg Λ fun v ↦ by
    -- `Λ v` is `e_z (D v)` by definition of the composite.
    rw [← hD, ← e.coe_continuousLinearEquivAt_eq hze, ContinuousLinearEquiv.coe_coe]
    exact D.trans_apply _ v
  obtain ⟨U, hUo, hzU, hUz, hUe, hUφ, ho'⟩ := exists_isolating_nhds_of_hasFDerivAt o hF e φ hze hzφ
    hz hA ⟨1, by simpa using AntilipschitzWith.id⟩
  -- The chart carries the manifold orientation to the fibre orientation read in `e`.
  have hmap : (oM.orientationAt z).map _ Λ.toLinearEquiv =
      e.mapOrientation (Fin (n + 1)) hze (o z) := by
    have hΛ : Λ.toLinearEquiv = D.toLinearEquiv.trans (e.linearEquivAt ℝ z hze) := by
      rw [ContinuousLinearEquiv.trans_toLinearEquiv]
      -- `continuousLinearEquivAt.toLinearEquiv` is the same trivialization's `linearEquivAt`;
      -- the former adds continuity fields to the latter, with no change to the linear map.
      rfl
    rw [hΛ]
    refine (Orientation.map_trans D.toLinearEquiv (e.linearEquivAt ℝ z hze)
      (oM.orientationAt z)).trans ?_
    rw [ho, Trivialization.mapOrientation_apply]
  -- The index formula centers after `Λ`; linearity identifies it with the canonical chart map.
  have hσ : (⟨fun x : φ.source ↦ φ x - φ z,
      φ.continuousOn.domRestrict.sub continuous_const⟩ : C(φ.source, F)) =
      ((Λ : X →L[ℝ] F) : C(X, F)).comp
        ((⟨fun y ↦ y - (chartAt X z) z, by fun_prop⟩ : C(X, X)).comp
          (chartAt X z).sourceRestrict) :=
    ContinuousMap.ext fun x ↦ by
      -- The source subtype is written as `φ.source` on the left and `(chartAt X z).source`
      -- on the right. Their induced topologies become identical after unfolding the composite
      -- chart, so `erw` is needed for the composition and source-restriction application
      -- lemmas to match. The final equality uses the same source identification as `hσ`.
      erw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
      simp only [ContinuousMap.coe_mk, ContinuousMap.coe_apply, ContinuousLinearEquiv.coe_coe,
        φ, OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
        ContinuousLinearEquiv.coe_toHomeomorph]
      erw [(chartAt X z).sourceRestrict_apply]
      exact (map_sub Λ ((chartAt X z) x) ((chartAt X z) z)).symm
  have hφ := (chartAt X z).localHomologyMap_chart_localOrientationOfOrientedChart
    (mem_chart_source X z) Λ (oM.orientationAt z) hX hF (by
      rw [← hσ]
      exact fun x hx ↦ Subtype.ext (φ.injOn x.property hzφ (sub_eq_zero.1 hx)))
  simp only [← hσ] at hφ
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
  obtain ⟨D, hD⟩ : ∃ D : TangentSpace 𝓘(ℝ, X) z ≃L[ℝ] E z,
      (D : TangentSpace 𝓘(ℝ, X) z →L[ℝ] E z) = sectionLinearization (F := F) 𝓘(ℝ, X) id s z :=
    exists_continuousLinearEquiv_eq_sectionLinearization_of_surjective (hX.trans hF.symm) hreg
  rcases Orientation.eq_or_eq_neg ((oM.orientationAt z).map _ D.toLinearEquiv) (o z)
    (by rw [Nat.card_fin, VectorBundle.finrank_eq ℝ F E z, hF]) with ho | ho
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
