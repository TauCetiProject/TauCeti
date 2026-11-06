/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Map
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

import all TauCeti.AlgebraicGeometry.FormalScheme.Spf.Carrier
import all TauCeti.AlgebraicGeometry.FormalScheme.Spf.StructureSheaf

/-!
# Functoriality of the formal-spectrum sheaf maps

The maps between quotient structure sheaves, and hence their inverse-limit maps, preserve
identities and composition. These results supply the sheaf component of functoriality for
morphisms of formal spectra. The rings need only have adic topologies: completeness and
noetherianity are not needed for these sheaf identities.

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

/-- The identity ring homomorphism induces the identity map on each quotient sheaf. -/
@[simp]
theorem quotientMap_id (hL : IsAdic L) :
    quotientMap (RingHom.id A) continuous_id hL hL le_rfl =
      eqToHom (by rw [comap_id]; rfl) := by
  erw [eqToHom_refl]
  apply Sheaf.hom_ext
  ext U : 2
  erw [quotientMap_hom_app]
  have h : Ideal.quotientMap L (RingHom.id A) le_rfl = RingHom.id (A ⧸ L) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
  exact CommRingCat.hom_ext <| (StructureSheaf.comap_congr h _ _ _ _).trans
    (StructureSheaf.comap_id' _)

/-- The maps on quotient sheaves commute with composition of continuous ring homomorphisms. -/
@[reassoc]
theorem quotientMap_comp (hH : IsAdic H) (hK : IsAdic K) (hL : IsAdic L)
    (hHK : H ≤ K.comap ψ) (hKL : K ≤ L.comap φ) :
    quotientMap ψ hψ hH hK hHK ≫
      (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap ψ hψ))).map
        (quotientMap φ hφ hK hL hKL) =
      quotientMap (φ.comp ψ) (hφ.comp hψ) hH hL (fun _ hx ↦ hKL (hHK hx)) ≫
        eqToHom (by rw [comap_comp φ hφ ψ hψ]; rfl) := by
  erw [eqToHom_refl, Category.comp_id]
  apply Sheaf.hom_ext
  ext U : 2
  erw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    TopCat.Sheaf.pushforward_map, TopCat.Presheaf.pushforward_map_app',
    quotientMap_hom_app, quotientMap_hom_app, quotientMap_hom_app]
  refine CommRingCat.hom_ext <| (StructureSheaf.comap_comp _ _ _ _ _ _ _).symm.trans
    (StructureSheaf.comap_congr ?_ _ _ _ _)
  exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)

section TopologicalRings

variable [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]

/-- The identity ring homomorphism induces the identity structure-sheaf map. -/
@[simp]
theorem structureSheafMap_id (hI : IsAdic I) :
    structureSheafMap (RingHom.id A) continuous_id hI hI =
      eqToHom (by rw [comap_id]; rfl) := by
  erw [eqToHom_refl]
  refine structureSheaf.pushforward_hom_ext (RingHom.id A) continuous_id hI fun n ↦ ?_
  rw [structureSheafMap_comp_quotientProjection (RingHom.id A) continuous_id hI hI
    (is_ideal_adic_pow hI n.succ_pos) n le_rfl, quotientMap_id]
  erw [eqToHom_refl]
  -- Pushforward along the identity has the same sections but a differently wrapped target.
  erw [Category.comp_id, toQuotientSheaf_pow_succ]
  rfl

/-- The inverse-limit structure-sheaf maps commute with composition. -/
@[reassoc]
theorem structureSheafMap_comp (hH : IsAdic H) (hK : IsAdic K) (hL : IsAdic L) :
    structureSheafMap ψ hψ hH hK ≫
      (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap ψ hψ))).map
        (structureSheafMap φ hφ hK hL) =
      structureSheafMap (φ.comp ψ) (hφ.comp hψ) hH hL ≫
        eqToHom (by rw [comap_comp φ hφ ψ hψ]; rfl) := by
  erw [eqToHom_refl, Category.comp_id]
  refine structureSheaf.pushforward_hom_ext (φ.comp ψ) (hφ.comp hψ) hL fun n ↦ ?_
  obtain ⟨m, hm⟩ := hK.exists_pow_succ_le_comap (hL.isOpen_pow (n + 1)) hφ
  have hK' := is_ideal_adic_pow hK m.succ_pos
  obtain ⟨k, hk⟩ := hH.exists_pow_succ_le_comap (hK.isOpen_pow (m + 1)) hψ
  have hH' := is_ideal_adic_pow hH k.succ_pos
  -- Pushforward along the composite uses the same preimages of opens as iterated pushforward.
  have hpush :
      (TopCat.Sheaf.pushforward CommRingCat
        (TopCat.ofHom (comap (φ.comp ψ) (hφ.comp hψ)))).map (quotientProjection hL n) =
      (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap ψ hψ))).map
        ((TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap φ hφ))).map
          (quotientProjection hL n)) := rfl
  erw [hpush, Category.assoc, ← CategoryTheory.Functor.map_comp,
    structureSheafMap_comp_quotientProjection φ hφ hK hL hK' n hm,
    CategoryTheory.Functor.map_comp, ← Category.assoc,
    structureSheafMap_comp_toQuotientSheaf ψ hψ hH hK hH' hK' hk, Category.assoc,
    quotientMap_comp φ hφ ψ hψ hH' hK' _ hk hm, eqToHom_refl, Category.comp_id,
    structureSheafMap_comp_quotientProjection (φ.comp ψ) (hφ.comp hψ) hH hL hH' n
      (fun _ hx ↦ hm (hk hx))]

end TopologicalRings

end TauCeti.FormalScheme.Spf
