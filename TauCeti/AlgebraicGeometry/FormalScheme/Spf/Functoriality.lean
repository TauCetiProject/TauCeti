/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Map
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

import TauCeti.Topology.Sheaves.Functors

/-!
# Functoriality of the formal-spectrum sheaf maps

The maps between quotient structure sheaves, and hence their inverse-limit maps, preserve
identities and composition. These results supply the sheaf component of functoriality for
morphisms of formal spectra. The rings need only have adic topologies: completeness and
noetherianity are not needed for these sheaf identities.

## Main results

* `TauCeti.FormalScheme.Spf.pushforward_comap_id`,
  `TauCeti.FormalScheme.Spf.pushforward_comap_comp`: sheaf pushforward along `comap` respects
  identities and composition.
* `TauCeti.FormalScheme.Spf.quotientMap_id`, `TauCeti.FormalScheme.Spf.quotientMap_comp`:
  the maps on quotient thickenings respect identities and composition.
* `TauCeti.FormalScheme.Spf.structureSheafMap_id`,
  `TauCeti.FormalScheme.Spf.structureSheafMap_comp`: the inverse-limit structure-sheaf maps
  respect identities and composition.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, §10.2.
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme.Spf

variable {A B C : Type u} [CommRing A] [TopologicalSpace A] [CommRing B]
  [TopologicalSpace B] [CommRing C] [TopologicalSpace C]
  (φ : B →+* A) (hφ : Continuous φ) (ψ : C →+* B) (hψ : Continuous ψ)
  {I L : Ideal A} {K : Ideal B} {H : Ideal C}

private theorem ofHom_comap_id :
    TopCat.ofHom (comap (RingHom.id A) continuous_id) = 𝟙 (TopCat.of (carrier A)) := by
  simp

private theorem ofHom_comap_comp :
    TopCat.ofHom (comap (φ.comp ψ) (hφ.comp hψ)) =
      TopCat.ofHom (comap φ hφ) ≫ TopCat.ofHom (comap ψ hψ) := by
  rw [comap_comp, TopCat.ofHom_comp]

/-- Pushforward of a sheaf along `comap (RingHom.id A)` agrees with the sheaf itself. -/
theorem pushforward_comap_id {D : Type*} [Category* D]
    (F : (TopCat.of (carrier A)).Sheaf D) :
    (TopCat.Sheaf.pushforward D (TopCat.ofHom (comap (RingHom.id A) continuous_id))).obj F = F :=
  TopCat.Sheaf.pushforward_obj_of_eq_id ofHom_comap_id F

/-- Pushforward of a sheaf along `comap (φ.comp ψ)` agrees with iterated pushforward along
`comap φ` and `comap ψ`. -/
theorem pushforward_comap_comp {D : Type*} [Category* D]
    (F : (TopCat.of (carrier A)).Sheaf D) :
    (TopCat.Sheaf.pushforward D (TopCat.ofHom (comap (φ.comp ψ) (hφ.comp hψ)))).obj F =
      (TopCat.Sheaf.pushforward D (TopCat.ofHom (comap ψ hψ))).obj
        ((TopCat.Sheaf.pushforward D (TopCat.ofHom (comap φ hφ))).obj F) :=
  TopCat.Sheaf.pushforward_obj_of_eq_comp (ofHom_comap_comp φ hφ ψ hψ) F

/-- The identity ring homomorphism induces the identity map on each quotient sheaf. -/
@[simp]
theorem quotientMap_id (hL : IsAdic L) :
    quotientMap (RingHom.id A) continuous_id hL hL le_rfl =
      eqToHom (pushforward_comap_id (quotientSheaf hL)).symm := by
  apply Sheaf.hom_ext
  ext U : 2
  have h : Ideal.quotientMap L (RingHom.id A) le_rfl = RingHom.id (A ⧸ L) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
  have hU : (Opens.map (quotientInclusion hL)).obj U.unop =
      (Opens.map (quotientInclusion hL)).obj
        ((Opens.map (TopCat.ofHom (comap (RingHom.id A) continuous_id))).obj U.unop) := by
    rw [ofHom_comap_id]
    rfl
  refine CommRingCat.hom_ext ?_
  have hlhs := congrArg CommRingCat.Hom.hom
    (quotientMap_hom_app (RingHom.id A) continuous_id hL hL le_rfl U)
  have hrhs := congrArg CommRingCat.Hom.hom
    (TopCat.Sheaf.eqToHom_hom_app (pushforward_comap_id (quotientSheaf hL)).symm U)
  exact hlhs.trans <| (StructureSheaf.comap_congr h _ _ _ _).trans <|
    (StructureSheaf.comap_id hU).trans hrhs.symm

/-- The maps on quotient sheaves commute with composition of continuous ring homomorphisms. -/
@[reassoc]
theorem quotientMap_comp (hH : IsAdic H) (hK : IsAdic K) (hL : IsAdic L)
    (hHK : H ≤ K.comap ψ) (hKL : K ≤ L.comap φ) :
    quotientMap ψ hψ hH hK hHK ≫
      (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap ψ hψ))).map
        (quotientMap φ hφ hK hL hKL) =
      quotientMap (φ.comp ψ) (hφ.comp hψ) hH hL (fun _ hx ↦ hKL (hHK hx)) ≫
        eqToHom (pushforward_comap_comp φ hφ ψ hψ (quotientSheaf hL)) := by
  apply Sheaf.hom_ext
  ext U : 2
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, NatTrans.comp_app]
  refine CommRingCat.hom_ext ?_
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp]
  have hU : (Opens.map (quotientInclusion hL)).obj
      (unop ((Opens.map (TopCat.ofHom (comap (φ.comp ψ) (hφ.comp hψ)))).op.obj U)) =
      (Opens.map (quotientInclusion hL)).obj
        (unop ((Opens.map (TopCat.ofHom (comap φ hφ))).op.obj
          ((Opens.map (TopCat.ofHom (comap ψ hψ))).op.obj U))) := by
    rw [ofHom_comap_comp]
    rfl
  have hring : (Ideal.quotientMap L φ hKL).comp (Ideal.quotientMap K ψ hHK) =
      Ideal.quotientMap L (φ.comp ψ) (fun _ hx ↦ hKL (hHK hx)) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
  have hψU : ((quotientMap ψ hψ hH hK hHK).hom.app U).hom =
      StructureSheaf.comap (Ideal.quotientMap K ψ hHK) _ _
        (map_quotientInclusion_comap_subset ψ hψ hH hK hHK U.unop) :=
    congrArg CommRingCat.Hom.hom (quotientMap_hom_app ψ hψ hH hK hHK U)
  have hφU : (((TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap ψ hψ))).map
      (quotientMap φ hφ hK hL hKL)).hom.app U).hom =
      StructureSheaf.comap (Ideal.quotientMap L φ hKL) _ _
        (map_quotientInclusion_comap_subset φ hφ hK hL hKL
          ((Opens.map (TopCat.ofHom (comap ψ hψ))).obj U.unop)) :=
    congrArg CommRingCat.Hom.hom (quotientMap_hom_app φ hφ hK hL hKL
      (op ((Opens.map (TopCat.ofHom (comap ψ hψ))).obj U.unop)))
  have hφψU : ((quotientMap (φ.comp ψ) (hφ.comp hψ) hH hL
      (fun _ hx ↦ hKL (hHK hx))).hom.app U).hom =
      StructureSheaf.comap (Ideal.quotientMap L (φ.comp ψ) (fun _ hx ↦ hKL (hHK hx))) _ _
        (map_quotientInclusion_comap_subset (φ.comp ψ) (hφ.comp hψ) hH hL _ U.unop) :=
    congrArg CommRingCat.Hom.hom
      (quotientMap_hom_app (φ.comp ψ) (hφ.comp hψ) hH hL (fun _ hx ↦ hKL (hHK hx)) U)
  have heqU : ((eqToHom (pushforward_comap_comp φ hφ ψ hψ (quotientSheaf hL))).hom.app U).hom =
      StructureSheaf.comap (RingHom.id (A ⧸ L)) _ _
        (by rw [hU, PrimeSpectrum.comap_id]; exact Set.Subset.rfl) :=
    (congrArg CommRingCat.Hom.hom (TopCat.Sheaf.eqToHom_hom_app _ U)).trans
      (StructureSheaf.comap_id hU).symm
  exact (congrArg₂ RingHom.comp hφU hψU).trans <|
    (StructureSheaf.comap_comp _ _ _ _ _ _ _).symm.trans <|
      (StructureSheaf.comap_congr (hring.trans (RingHom.id_comp _).symm) _ _ _ _).trans <|
        (StructureSheaf.comap_comp _ _ _ _ _ _ _).trans (congrArg₂ RingHom.comp heqU hφψU).symm

section TopologicalRings

variable [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]

/-- The identity ring homomorphism induces the identity structure-sheaf map. -/
@[simp]
theorem structureSheafMap_id (hI : IsAdic I) :
    structureSheafMap (RingHom.id A) continuous_id hI hI =
      eqToHom (pushforward_comap_id (structureSheaf hI)).symm := by
  refine structureSheaf.pushforward_hom_ext (RingHom.id A) continuous_id hI fun n ↦ ?_
  rw [structureSheafMap_comp_quotientProjection (RingHom.id A) continuous_id hI hI
    (is_ideal_adic_pow hI n.succ_pos) n le_rfl, quotientMap_id, toQuotientSheaf_pow_succ,
    TopCat.Sheaf.eqToHom_symm_comp_pushforward_map_of_eq_id ofHom_comap_id]

/-- The inverse-limit structure-sheaf maps commute with composition. -/
@[reassoc]
theorem structureSheafMap_comp (hH : IsAdic H) (hK : IsAdic K) (hL : IsAdic L) :
    structureSheafMap ψ hψ hH hK ≫
      (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap ψ hψ))).map
        (structureSheafMap φ hφ hK hL) =
      structureSheafMap (φ.comp ψ) (hφ.comp hψ) hH hL ≫
        eqToHom (pushforward_comap_comp φ hφ ψ hψ (structureSheaf hL)) := by
  refine (comp_eqToHom_iff (pushforward_comap_comp φ hφ ψ hψ (structureSheaf hL)).symm _ _).mp ?_
  refine structureSheaf.pushforward_hom_ext (φ.comp ψ) (hφ.comp hψ) hL fun n ↦ ?_
  let Fφ := TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap φ hφ))
  let Fψ := TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap ψ hψ))
  let Fφψ := TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap (φ.comp ψ) (hφ.comp hψ)))
  have hL' := is_ideal_adic_pow hL n.succ_pos
  obtain ⟨m, hm⟩ := hK.exists_pow_succ_le_comap (hL.isOpen_pow (n + 1)) hφ
  have hK' := is_ideal_adic_pow hK m.succ_pos
  obtain ⟨k, hk⟩ := hH.exists_pow_succ_le_comap (hK.isOpen_pow (m + 1)) hψ
  have hH' := is_ideal_adic_pow hH k.succ_pos
  calc
    ((structureSheafMap ψ hψ hH hK ≫ Fψ.map (structureSheafMap φ hφ hK hL)) ≫
        eqToHom (pushforward_comap_comp φ hφ ψ hψ (structureSheaf hL)).symm) ≫
        Fφψ.map (quotientProjection hL n)
      = structureSheafMap ψ hψ hH hK ≫
          Fψ.map (structureSheafMap φ hφ hK hL ≫ Fφ.map (quotientProjection hL n)) ≫
            eqToHom (pushforward_comap_comp φ hφ ψ hψ (quotientSheaf hL')).symm := by
        simp only [Fφ, Fψ, Fφψ, Category.assoc]
        rw [TopCat.Sheaf.eqToHom_symm_comp_pushforward_map_of_eq_comp
          (ofHom_comap_comp φ hφ ψ hψ), ← Functor.map_comp_assoc]
    _ = (structureSheafMap ψ hψ hH hK ≫ Fψ.map (toQuotientSheaf hK hK')) ≫
          Fψ.map (quotientMap φ hφ hK' hL' hm) ≫
            eqToHom (pushforward_comap_comp φ hφ ψ hψ (quotientSheaf hL')).symm := by
        rw [structureSheafMap_comp_quotientProjection φ hφ hK hL hK' n hm]
        simp only [Functor.map_comp, Category.assoc]
    _ = toQuotientSheaf hH hH' ≫
          (quotientMap ψ hψ hH' hK' hk ≫ Fψ.map (quotientMap φ hφ hK' hL' hm)) ≫
            eqToHom (pushforward_comap_comp φ hφ ψ hψ (quotientSheaf hL')).symm := by
        rw [structureSheafMap_comp_toQuotientSheaf ψ hψ hH hK hH' hK' hk]
        simp only [Category.assoc]
    _ = toQuotientSheaf hH hH' ≫
          quotientMap (φ.comp ψ) (hφ.comp hψ) hH' hL' (fun _ hx ↦ hm (hk hx)) := by
        rw [quotientMap_comp φ hφ ψ hψ hH' hK' hL' hk hm]
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    _ = structureSheafMap (φ.comp ψ) (hφ.comp hψ) hH hL ≫
          Fφψ.map (quotientProjection hL n) :=
        (structureSheafMap_comp_quotientProjection (φ.comp ψ) (hφ.comp hψ) hH hL hH' n
          (fun _ hx ↦ hm (hk hx))).symm

end TopologicalRings

end TauCeti.FormalScheme.Spf
