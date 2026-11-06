/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Functoriality
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Quotient

import all TauCeti.AlgebraicGeometry.FormalScheme.Spf.Carrier
import all TauCeti.AlgebraicGeometry.FormalScheme.Spf.StructureSheaf
import all TauCeti.AlgebraicGeometry.FormalScheme.Spf.Quotient

/-!
# Morphisms of formal spectra

A continuous homomorphism of adic rings induces a morphism of locally ringed spaces
in the opposite direction. The underlying continuous map pulls back open primes and the
structure-sheaf map is obtained from the maps of quotient thickenings.

This file proves that the resulting stalk maps are local: after composing with an
ideal-of-definition quotient, they agree with the stalk maps of morphisms of ordinary
schemes. It also records the compatibility with every quotient thickening and the induced
map on global sections. The identities `map_id` and `map_comp` make this construction
contravariantly functorial. No noetherian hypothesis is needed.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*,
  Ch. I, 10.2.1–10.2.2.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme.Spf

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsAdicRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]
  (φ : B →+* A) (hφ : Continuous φ) {K : Ideal B} {L : Ideal A}

/-- The continuous map and the inverse-limit sheaf map, before checking locality. -/
private noncomputable def mapPresheafedSpace :
    (Spf A).toPresheafedSpace ⟶ (Spf B).toPresheafedSpace where
  base := TopCat.ofHom (comap φ hφ)
  c := (structureSheafMap φ hφ (IsAdicRing.ideal_spec B).2.1
    (IsAdicRing.ideal_spec A).2.1).hom

-- The extra restriction `i` accounts for the equality, rather than definitional equality,
-- of the base maps in the square of quotient thickenings.
omit [IsTopologicalRing A] [IsAdicRing A] [IsTopologicalRing B] [IsAdicRing B] in
private theorem specQuotientMap_c_app (hK : IsAdic K) (hL : IsAdic L)
    (hKL : K ≤ L.comap φ) (U : Opens (carrier B))
    (i : (Opens.map (quotientInclusion hL)).obj
        ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U) ⟶
      (Opens.map (Spec.topMap (CommRingCat.ofHom (Ideal.quotientMap L φ hKL)))).obj
        ((Opens.map (quotientInclusion hK)).obj U)) :
    (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.quotientMap L φ hKL))).c.app
        (op ((Opens.map (quotientInclusion hK)).obj U)) ≫
      (Spec.locallyRingedSpaceObj (CommRingCat.of (A ⧸ L))).presheaf.map i.op =
        (quotientMap φ hφ hK hL hKL).hom.app (op U) := by
  dsimp only [Spec.locallyRingedSpaceMap, Spec.sheafedSpaceMap]
  erw [Spec.locallyRingedSpaceObj_presheaf_map, quotientMap_hom_app]
  exact CommRingCat.hom_ext (StructureSheaf.map_comp_comap (Ideal.quotientMap L φ hKL)
    ((Opens.map (quotientInclusion hK)).obj U) _ i)

/-- On every compatible pair of thickenings the constructed map is the ordinary spectrum map. -/
private theorem fromSpecQuotient_comp_mapPresheafedSpace (hK : IsAdic K) (hL : IsAdic L)
    (hKL : K ≤ L.comap φ) :
    (fromSpecQuotient hL).toHom ≫ mapPresheafedSpace φ hφ =
      (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.quotientMap L φ hKL)) ≫
        fromSpecQuotient hK).toHom := by
  rw [LocallyRingedSpace.comp_toHom]
  symm
  refine PresheafedSpace.Hom.ext _ _ ?_ ?_
  · apply ConcreteCategory.hom_ext
    intro q
    exact (comap_quotientInclusion φ hφ hK hL hKL q).symm
  · apply NatTrans.ext
    funext U
    erw [NatTrans.comp_app, Functor.whiskerRight_app, PresheafedSpace.comp_c_app,
      PresheafedSpace.comp_c_app, Category.assoc, specQuotientMap_c_app φ hφ hK hL hKL]
    exact congrArg (fun η ↦ η.hom.app U)
      (structureSheafMap_comp_toQuotientSheaf φ hφ (IsAdicRing.ideal_spec B).2.1
        (IsAdicRing.ideal_spec A).2.1 hK hL hKL).symm

/-- Locality can be checked after passing to a quotient thickening through every point. -/
private theorem mapPresheafedSpace_isLocalHom (p : carrier A) :
    IsLocalHom ((mapPresheafedSpace φ hφ).stalkMap p).hom := by
  let L := IsAdicRing.ideal A
  have hL : IsAdic L := (IsAdicRing.ideal_spec A).2.1
  obtain ⟨n, hn⟩ := IsAdic.exists_pow_succ_le_comap (IsAdicRing.ideal_spec B).2.1
    (by simpa using hL.isOpen_pow 1) hφ
  let K := IsAdicRing.ideal B ^ (n + 1)
  have hK : IsAdic K := is_ideal_adic_pow (IsAdicRing.ideal_spec B).2.1 n.succ_pos
  let q := homeomorphSpecQuotient hL p
  have hp : (fromSpecQuotient hL).base q = p := by
    rw [fromSpecQuotient_points]
    exact (homeomorphSpecQuotient hL).symm_apply_apply p
  have hlocal : IsLocalHom
      (((fromSpecQuotient hL).toHom ≫ mapPresheafedSpace φ hφ).stalkMap q).hom := by
    rw [fromSpecQuotient_comp_mapPresheafedSpace φ hφ hK hL hn]
    exact LocallyRingedSpace.isLocalHomStalkMap'
      (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.quotientMap L φ hn)) ≫
        fromSpecQuotient hK) q
  erw [PresheafedSpace.stalkMap.comp] at hlocal
  have := @isLocalHom_of_comp _ _ _ _ _ _
    ((mapPresheafedSpace φ hφ).stalkMap ((fromSpecQuotient hL).base q)).hom
    ((fromSpecQuotient hL).stalkMap q).hom hlocal
  rwa [hp] at this

/-- The morphism of locally ringed spaces induced contravariantly by a continuous ring
homomorphism. On points it pulls back open primes, and on quotient thickenings it is induced
by the corresponding quotient ring homomorphisms (EGA I, Ch. I, 10.2.1). -/
noncomputable def map : Spf A ⟶ Spf B where
  toHom := mapPresheafedSpace φ hφ
  prop := mapPresheafedSpace_isLocalHom φ hφ

/-- The underlying map of `Spf.map` pulls back open prime ideals. -/
@[simp]
theorem map_base : (map φ hφ).base = TopCat.ofHom (comap φ hφ) :=
  (rfl)

/-- The underlying presheafed-space morphism of `Spf.map`, including its sheaf component. -/
theorem map_toHom : (map φ hφ).toHom =
    { base := TopCat.ofHom (comap φ hφ)
      c := (structureSheafMap φ hφ (IsAdicRing.ideal_spec B).2.1
        (IsAdicRing.ideal_spec A).2.1).hom } :=
  (rfl)

/-- `Spf.map` commutes with every compatible pair of ideal-of-definition quotient inclusions. -/
@[reassoc]
theorem fromSpecQuotient_comp_map (hK : IsAdic K) (hL : IsAdic L)
    (hKL : K ≤ L.comap φ) :
    fromSpecQuotient hL ≫ map φ hφ =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.quotientMap L φ hKL)) ≫
        fromSpecQuotient hK := by
  apply LocallyRingedSpace.Hom.ext'
  exact fromSpecQuotient_comp_mapPresheafedSpace φ hφ hK hL hKL

/-- Under the global-section comparisons, the map induced by `Spf.map φ` is `φ`
(EGA I, Ch. I, 10.2.2). -/
@[reassoc]
theorem map_globalSections :
    have := (IsAdicRing.ideal_spec A).2.2
    have := (IsAdicRing.ideal_spec B).2.2
    (map φ hφ).c.app (op ⊤) ≫ (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).hom =
      (globalSectionsIso (IsAdicRing.ideal_spec B).2.1).hom ≫ CommRingCat.ofHom φ := by
  intro _ _
  exact structureSheafMap_hom_app_top_comp_globalSectionsIso_hom φ hφ
    (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec A).2.1

/-- A morphism of formal spectra determines the continuous ring homomorphism that induces it. -/
theorem map_injective {φ ψ : B →+* A} {hφ : Continuous φ} {hψ : Continuous ψ}
    (h : map φ hφ = map ψ hψ) : φ = ψ := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec B).2.2
  have hglobal :
      (globalSectionsIso (IsAdicRing.ideal_spec B).2.1).hom ≫ CommRingCat.ofHom φ =
        (globalSectionsIso (IsAdicRing.ideal_spec B).2.1).hom ≫ CommRingCat.ofHom ψ := by
    rw [← map_globalSections φ hφ, h, map_globalSections ψ hψ]
  have hmaps := (cancel_epi (globalSectionsIso (IsAdicRing.ideal_spec B).2.1).hom).mp hglobal
  exact congrArg CommRingCat.Hom.hom hmaps

/-- The identity homomorphism induces the identity morphism of formal spectra. -/
@[simp]
theorem map_id : map (RingHom.id A) continuous_id = 𝟙 (Spf A) := by
  apply LocallyRingedSpace.Hom.ext'
  rw [map_toHom, LocallyRingedSpace.id_toHom]
  refine PresheafedSpace.Hom.ext _ _ rfl ?_
  apply NatTrans.ext
  funext U
  erw [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.comp_id, PresheafedSpace.id_c_app,
    CategoryTheory.Functor.map_id]
  exact congrArg (fun η ↦ η.hom.app U)
    (structureSheafMap_id (IsAdicRing.ideal_spec A).2.1)

variable {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsAdicRing C] (ψ : C →+* B) (hψ : Continuous ψ)

/-- Composition of continuous homomorphisms induces composition in the opposite order. -/
@[reassoc]
theorem map_comp : map (φ.comp ψ) (hφ.comp hψ) = map φ hφ ≫ map ψ hψ := by
  apply LocallyRingedSpace.Hom.ext'
  rw [LocallyRingedSpace.comp_toHom, map_toHom, map_toHom, map_toHom]
  refine PresheafedSpace.Hom.ext _ _ rfl ?_
  apply NatTrans.ext
  funext U
  erw [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.comp_id, PresheafedSpace.comp_c_app]
  exact congrArg (fun η ↦ η.hom.app U)
    (structureSheafMap_comp φ hφ ψ hψ (IsAdicRing.ideal_spec C).2.1
      (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec A).2.1).symm

end TauCeti.FormalScheme.Spf
