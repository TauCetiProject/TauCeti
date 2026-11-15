/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.StrongSite.Basic
public import TauCeti.Topology.GTopology.Restrict

/-!
# Restriction of the strong affinoid G-topology to an affinoid subdomain

Let `φ : A →ₐ[K] B` represent an affinoid subdomain `U ⊆ Sp A` (`IsAffinoidSubdomainMap φ U`).
Following [BGR, §9.1.4, Proposition 5], the bijection `Sp B ≃ U` identifies the strong affinoid
G-topology of `Sp B` with the G-topology induced by `strongGTopology` on `U`:

* Pushing forward along `Sp B → Sp A` preserves affinoid-test refined families
  (`IsAffinoidSubdomainMap.image_isAffinoidTestRefined`) and carries strong-admissible opens of
  `Sp B` order-isomorphically onto strong-admissible opens of `Sp A` contained in `U`
  (`IsAffinoidSubdomainMap.strongAdmissibleOpenOrderIso`).
* Together with `AlgHom.strongAffinoidMap`, this yields mutually inverse continuous maps of
  G-topologies `IsAffinoidSubdomainMap.strongToRestrict` and
  `IsAffinoidSubdomainMap.strongRestrictTo` between `strongGTopology` on `Sp B` and
  `strongGTopology.restrict U`.

Applying these constructions to `V.isAffinoidSubdomainMap` for `V : AffinoidSubdomain K A`
compares the induced strong G-topology on `V` with the intrinsic strong G-topology of `V.sections`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §9.1.4,
  Proposition 5.
-/

public section

namespace TauCeti

universe u

section Pushforward

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

instance AffinoidSubdomain.instFactIsAffinoidAlgebraSections (U : AffinoidSubdomain K A) :
    Fact (IsAffinoidAlgebra K U.sections) :=
  ⟨U.isAffinoidAlgebra⟩

namespace IsAffinoidSubdomainMap

/-- Pushing forward along the classical point map of an affinoid subdomain representation preserves
affinoid-test refined families. -/
theorem image_isAffinoidTestRefined (hA : IsAffinoidAlgebra K A)
    {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)} (hφ : IsAffinoidSubdomainMap φ U)
    {W : Set (MaximalSpectrum B)} {ℱ : Set (Set (MaximalSpectrum B))}
    (hW : IsAffinoidTestRefined K W ℱ) :
    IsAffinoidTestRefined K (hφ.isAffinoidAlgebra.maximalSpectrumComap φ '' W)
      ((fun s ↦ hφ.isAffinoidAlgebra.maximalSpectrumComap φ '' s) '' ℱ) := by
  -- Factor each test map through the universal property of the subdomain.
  rw [isAffinoidTestRefined_iff] at hW ⊢
  intro D _ _ hD ψ hψ
  have hψU : Set.range (hD.maximalSpectrumComap ψ) ⊆ U :=
    hψ.trans ((Set.image_subset_range _ _).trans hφ.range_maximalSpectrumComap_subset)
  let χ : B →ₐ[K] D := hφ.lift hD ψ hψU
  have hχW : Set.range (hD.maximalSpectrumComap χ) ⊆ W := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hψ ⟨z, rfl⟩
    have hz := congrFun
      (IsAffinoidAlgebra.maximalSpectrumComap_comp hφ.isAffinoidAlgebra hD φ χ) z
    rw [hφ.lift_comp] at hz
    rwa [← hφ.maximalSpectrumComap_injective hA (hwz.trans hz)]
  obtain ⟨R, hfin, hRuniv, hRℱ⟩ := hW hD χ hχW
  refine ⟨R, hfin, hRuniv, fun P hP ↦ ?_⟩
  obtain ⟨s, hs, hPs⟩ := hRℱ P hP
  refine ⟨_, ⟨s, hs, rfl⟩, fun z hz ↦ ?_⟩
  have hcomp := congrFun
    (IsAffinoidAlgebra.maximalSpectrumComap_comp hφ.isAffinoidAlgebra hD φ χ) z
  rw [hφ.lift_comp] at hcomp
  rw [Set.mem_preimage, hcomp]
  exact ⟨hD.maximalSpectrumComap χ z, hPs hz, rfl⟩

/-- Push a strong-admissible open of `Sp B` forward along an affinoid subdomain map `φ : A →ₐ[K] B`
to a strong-admissible open of `Sp A`. -/
noncomputable def mapStrongAdmissibleOpen (hA : IsAffinoidAlgebra K A)
    {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)} (hφ : IsAffinoidSubdomainMap φ U)
    (W : StrongAdmissibleOpen K B) : StrongAdmissibleOpen K A where
  carrier := hφ.isAffinoidAlgebra.maximalSpectrumComap φ '' W
  exists_affinoid_cover := by
    obtain ⟨S, hSu, hS⟩ := W.exists_affinoid_cover
    have hSu' : ⋃₀ ((fun V : AffinoidSubdomain K B ↦ (V : Set (MaximalSpectrum B))) '' S) =
        (W : Set (MaximalSpectrum B)) := hSu
    have hS' : IsAffinoidTestRefined K (W : Set (MaximalSpectrum B))
        ((fun V : AffinoidSubdomain K B ↦ (V : Set (MaximalSpectrum B))) '' S) := hS
    let S' : Set (AffinoidSubdomain K A) :=
      (fun V : AffinoidSubdomain K B ↦
        AffinoidSubdomain.ofMap (hφ.comp hA V.isAffinoidSubdomainMap)) '' S
    have himg : ((fun Z : AffinoidSubdomain K A ↦ (Z : Set (MaximalSpectrum A))) '' S') =
        (fun s ↦ hφ.isAffinoidAlgebra.maximalSpectrumComap φ '' s) ''
          ((fun V : AffinoidSubdomain K B ↦ (V : Set (MaximalSpectrum B))) '' S) := by
      simp only [S', Set.image_image, AffinoidSubdomain.coe_ofMap]
    refine ⟨S', ?_, himg ▸ hφ.image_isAffinoidTestRefined hA hS'⟩
    rw [himg, ← hSu']
    ext x
    simp only [Set.mem_sUnion, Set.mem_image, exists_exists_and_eq_and]
    exact ⟨fun ⟨V, hV, y, hy, hyx⟩ ↦ ⟨y, ⟨V, hV, hy⟩, hyx⟩,
      fun ⟨y, ⟨V, hV, hy⟩, hyx⟩ ↦ ⟨V, hV, y, hy, hyx⟩⟩

@[simp]
theorem coe_mapStrongAdmissibleOpen (hA : IsAffinoidAlgebra K A)
    {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)} (hφ : IsAffinoidSubdomainMap φ U)
    (W : StrongAdmissibleOpen K B) :
    (hφ.mapStrongAdmissibleOpen hA W : Set (MaximalSpectrum A)) =
      hφ.isAffinoidAlgebra.maximalSpectrumComap φ '' (W : Set (MaximalSpectrum B)) :=
  (rfl)

theorem mapStrongAdmissibleOpen_subset (hA : IsAffinoidAlgebra K A)
    {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)} (hφ : IsAffinoidSubdomainMap φ U)
    (W : StrongAdmissibleOpen K B) :
    (hφ.mapStrongAdmissibleOpen hA W : Set (MaximalSpectrum A)) ⊆ U :=
  (Set.image_subset_range _ _).trans hφ.range_maximalSpectrumComap_subset

end IsAffinoidSubdomainMap

end Pushforward

section RestrictSite

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [hA : Fact (IsAffinoidAlgebra K A)]

namespace IsAffinoidSubdomainMap

variable {φ : A →ₐ[K] B} {U : StrongAdmissibleOpen K A}
  (hφ : IsAffinoidSubdomainMap φ (StrongAdmissibleOpen.setEmbedding U))

/-- Strong-admissible opens of `Sp B` correspond order-isomorphically to strong-admissible opens of
`Sp A` contained in `U` [BGR, §9.1.4, Proposition 5]. -/
noncomputable def strongAdmissibleOpenOrderIso :
    StrongAdmissibleOpen K B ≃o Set.Iic U :=
  let _ : Fact (IsAffinoidAlgebra K B) := ⟨hφ.isAffinoidAlgebra⟩
  { toFun W := ⟨hφ.mapStrongAdmissibleOpen hA.out W, Set.mem_Iic.mpr <|
      SetLike.coe_subset_coe.mp <|
        (hφ.mapStrongAdmissibleOpen_subset hA.out W).trans_eq
          (StrongAdmissibleOpen.setEmbedding_apply U)⟩
    invFun V := V.1.comap φ
    left_inv W := by
      apply SetLike.coe_injective
      ext y
      simp [(hφ.maximalSpectrumComap_injective hA.out).mem_set_image]
    right_inv V := by
      apply Subtype.ext
      apply SetLike.coe_injective
      rw [coe_mapStrongAdmissibleOpen, StrongAdmissibleOpen.coe_comap, Set.image_preimage_eq_iff,
        hφ.range_maximalSpectrumComap hA.out, StrongAdmissibleOpen.setEmbedding_apply,
        SetLike.coe_subset_coe]
      exact Set.mem_Iic.mp V.2
    map_rel_iff' {W₁ W₂} := by
      simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, ← SetLike.coe_subset_coe,
        coe_mapStrongAdmissibleOpen,
        Set.image_subset_image_iff (hφ.maximalSpectrumComap_injective hA.out)] }

@[simp]
theorem coe_strongAdmissibleOpenOrderIso_apply (W : StrongAdmissibleOpen K B) :
    (hφ.strongAdmissibleOpenOrderIso W : StrongAdmissibleOpen K A) =
      hφ.mapStrongAdmissibleOpen hA.out W :=
  (rfl)

variable [hB : Fact (IsAffinoidAlgebra K B)]

/-- The continuous map from the strong G-topology of `Sp B` to the induced strong G-topology on
`U ⊆ Sp A`, obtained by corestricting `φ.strongAffinoidMap`. -/
noncomputable def strongToRestrict :
    (StrongAdmissibleOpen.strongGTopology (K := K) (A := B)).ContinuousMap
      ((StrongAdmissibleOpen.strongGTopology (K := K) (A := A)).restrict U) :=
  φ.strongAffinoidMap.codRestrict fun y ↦ by
    rw [φ.strongAffinoidMap_apply]
    exact hφ.range_maximalSpectrumComap_subset ⟨y, rfl⟩

theorem coe_strongToRestrict_apply (y : MaximalSpectrum B) :
    (hφ.strongToRestrict y : MaximalSpectrum A) = hB.out.maximalSpectrumComap φ y := by
  simp [strongToRestrict]

@[simp]
theorem strongToRestrict_apply_eq_maximalSpectrumEquiv (y : MaximalSpectrum B) :
    hφ.strongToRestrict y = hφ.maximalSpectrumEquiv hA.out y := by
  apply Subtype.ext
  rw [coe_strongToRestrict_apply, hφ.coe_maximalSpectrumEquiv hA.out]

/-- The inverse continuous map from the induced strong G-topology on `U ⊆ Sp A` to the strong
G-topology of `Sp B` [BGR, §9.1.4, Proposition 5]. -/
noncomputable def strongRestrictTo :
    ((StrongAdmissibleOpen.strongGTopology (K := K) (A := A)).restrict U).ContinuousMap
      (StrongAdmissibleOpen.strongGTopology (K := K) (A := B)) where
  toFun := (hφ.maximalSpectrumEquiv hA.out).symm
  comap W := hφ.strongAdmissibleOpenOrderIso W
  coe_comap' W := by
    ext x
    simp only [GTopology.restrictEmbedding_apply, StrongAdmissibleOpen.setEmbedding_apply,
      coe_strongAdmissibleOpenOrderIso_apply, coe_mapStrongAdmissibleOpen, Set.mem_preimage]
    refine ⟨fun ⟨y, hyW, hyx⟩ ↦ ?_, fun hxW ↦ ⟨_, hxW, ?_⟩⟩
    · have hy : y = (hφ.maximalSpectrumEquiv hA.out).symm x := by
        apply (hφ.maximalSpectrumEquiv hA.out).injective
        rw [Equiv.apply_symm_apply]
        exact Subtype.ext ((hφ.coe_maximalSpectrumEquiv hA.out y).trans hyx)
      exact hy ▸ hyW
    · rw [← hφ.coe_maximalSpectrumEquiv hA.out, Equiv.apply_symm_apply]
  covers_comap {W S} hS := by
    rw [StrongAdmissibleOpen.strongGTopology_covers_iff] at hS
    rw [GTopology.restrict_covers_iff, StrongAdmissibleOpen.strongGTopology_covers_iff]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨V, hV, rfl⟩, rfl⟩
      exact Subtype.mk_le_mk.mp (hφ.strongAdmissibleOpenOrderIso.monotone (hS.1 V hV))
    · have himg : ((fun Z : StrongAdmissibleOpen K A ↦ (Z : Set (MaximalSpectrum A))) ''
          ((Subtype.val : Set.Iic U → StrongAdmissibleOpen K A) ''
            (hφ.strongAdmissibleOpenOrderIso '' S))) =
          (fun s ↦ hφ.isAffinoidAlgebra.maximalSpectrumComap φ '' s) ''
            ((fun V : StrongAdmissibleOpen K B ↦ (V : Set (MaximalSpectrum B))) '' S) := by
        simp only [Set.image_image, coe_strongAdmissibleOpenOrderIso_apply,
          coe_mapStrongAdmissibleOpen]
      rw [himg]
      exact hφ.image_isAffinoidTestRefined hA.out hS.2

@[simp]
theorem strongRestrictTo_apply (x : StrongAdmissibleOpen.setEmbedding U) :
    hφ.strongRestrictTo x = (hφ.maximalSpectrumEquiv hA.out).symm x :=
  (rfl)

@[simp]
theorem strongRestrictTo_comp_strongToRestrict :
    hφ.strongRestrictTo.comp hφ.strongToRestrict =
      GTopology.ContinuousMap.id (StrongAdmissibleOpen.strongGTopology (K := K) (A := B)) := by
  apply GTopology.ContinuousMap.ext
  intro y
  simp

@[simp]
theorem strongToRestrict_comp_strongRestrictTo :
    hφ.strongToRestrict.comp hφ.strongRestrictTo =
      GTopology.ContinuousMap.id
        ((StrongAdmissibleOpen.strongGTopology (K := K) (A := A)).restrict U) := by
  apply GTopology.ContinuousMap.ext
  intro x
  simp

end IsAffinoidSubdomainMap

end RestrictSite

end TauCeti
