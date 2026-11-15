/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Functoriality
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Quotient

import TauCeti.Topology.Sheaves.Functors

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

Conversely, every morphism of locally ringed spaces `f : Spf A ⟶ Spf B` arises in this way from
the ring homomorphism `φ : B → A` it induces on global sections (EGA I, Ch. I, 10.2.2), so
`Spf.homEquiv` identifies such morphisms with the continuous ring homomorphisms `B → A`. The
global section of `Spf B` corresponding to `b ∈ B` is invertible exactly on `D(b)`, and locality
of the stalk maps makes `f` pull back `D(b)` to `D(φ b)`. Hence `f` is `Spec φ` on points, and `φ`
is continuous: it carries the finitely generated ideal of definition of `B` into the radical of
that of `A`, which is the intersection of the open primes of `A`. On each `D(b)`, the sheaf map of
`f` followed by restriction to `D(φ b)` is a continuous homomorphism of completed localisations
`B_{b} → A_{φ b}` extending `φ`, so it agrees with that of `Spf.map φ`.

## Main definitions

* `TauCeti.FormalScheme.Spf.map`: the morphism `Spf A ⟶ Spf B` induced by a continuous ring
  homomorphism `B → A`.
* `TauCeti.FormalScheme.Spf.globalSectionsHom`: the ring homomorphism `B → A` induced on global
  sections by a morphism `Spf A ⟶ Spf B`.
* `TauCeti.FormalScheme.Spf.homEquiv`: morphisms `Spf A ⟶ Spf B` are the continuous ring
  homomorphisms `B → A`.

## Main results

* `TauCeti.FormalScheme.Spf.map_globalSections`: `Spf.map φ` induces `φ` on global sections.
* `TauCeti.FormalScheme.Spf.basicOpen_globalSectionsIso_inv`: the global section `a` is
  invertible exactly on `D(a)`.
* `TauCeti.FormalScheme.Spf.preimage_basicOpen`: a morphism `Spf A ⟶ Spf B` pulls back `D(b)` to
  `D(φ b)`.
* `TauCeti.FormalScheme.Spf.continuous_globalSectionsHom`: the map on global sections of a
  morphism of formal spectra is continuous (automatic continuity).
* `TauCeti.FormalScheme.Spf.map_globalSectionsHom`: every morphism `Spf A ⟶ Spf B` is `Spf.map`
  of its map on global sections.

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
  refine CommRingCat.hom_ext ?_
  rw [CommRingCat.hom_comp]
  have hc : ((Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.quotientMap L φ hKL))).c.app
      (op ((Opens.map (quotientInclusion hK)).obj U))).hom =
      StructureSheaf.comap (Ideal.quotientMap L φ hKL)
        ((Opens.map (quotientInclusion hK)).obj U) _ fun _ ↦ id :=
    rfl
  have hmap := congrArg CommRingCat.Hom.hom
    (Spec.locallyRingedSpaceObj_presheaf_map (CommRingCat.of (A ⧸ L)) i.op)
  have hquot := congrArg CommRingCat.Hom.hom (quotientMap_hom_app φ hφ hK hL hKL (op U))
  exact (congrArg₂ RingHom.comp hmap hc).trans
    ((StructureSheaf.map_comp_comap (Ideal.quotientMap L φ hKL)
      ((Opens.map (quotientInclusion hK)).obj U) _ i).trans hquot.symm)

/-- On every compatible pair of thickenings the constructed map is the ordinary spectrum map. -/
private theorem fromSpecQuotient_comp_mapPresheafedSpace (hK : IsAdic K) (hL : IsAdic L)
    (hKL : K ≤ L.comap φ) :
    (fromSpecQuotient hL).toHom ≫ mapPresheafedSpace φ hφ =
      (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.quotientMap L φ hKL)) ≫
        fromSpecQuotient hK).toHom := by
  let f₁ := (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.quotientMap L φ hKL))).toHom
  let g₁ : (Spec.locallyRingedSpaceObj (CommRingCat.of (B ⧸ K))).toPresheafedSpace ⟶
      (Spf B).toPresheafedSpace :=
    { base := quotientInclusion hK
      c := (toQuotientSheaf (IsAdicRing.ideal_spec B).2.1 hK).hom }
  let f₂ : (Spec.locallyRingedSpaceObj (CommRingCat.of (A ⧸ L))).toPresheafedSpace ⟶
      (Spf A).toPresheafedSpace :=
    { base := quotientInclusion hL
      c := (toQuotientSheaf (IsAdicRing.ideal_spec A).2.1 hL).hom }
  have hbase : (f₁ ≫ g₁).base = (f₂ ≫ mapPresheafedSpace φ hφ).base := by
    apply ConcreteCategory.hom_ext
    intro q
    exact (comap_quotientInclusion φ hφ hK hL hKL q).symm
  rw [LocallyRingedSpace.comp_toHom, fromSpecQuotient_toHom hK, fromSpecQuotient_toHom hL]
  symm
  refine PresheafedSpace.Hom.ext _ _ hbase ?_
  ext U : 1
  refine CommRingCat.hom_ext ?_
  rw [NatTrans.comp_app, Functor.whiskerRight_app, CommRingCat.hom_comp]
  have hcomp₁ := (congrArg CommRingCat.Hom.hom
    (PresheafedSpace.comp_c_app f₁ g₁ (op U))).trans (CommRingCat.hom_comp _ _)
  have hcomp₂ := (congrArg CommRingCat.Hom.hom
    (PresheafedSpace.comp_c_app f₂ (mapPresheafedSpace φ hφ) (op U))).trans
      (CommRingCat.hom_comp _ _)
  have hspec := congrArg CommRingCat.Hom.hom (specQuotientMap_c_app φ hφ hK hL hKL U
    (eqToHom (congrArg (fun f ↦ (Opens.map f).obj U) hbase.symm)))
  have hsheaf := congrArg (fun η ↦ (η.hom.app (op U)).hom)
    (structureSheafMap_comp_toQuotientSheaf φ hφ (IsAdicRing.ideal_spec B).2.1
      (IsAdicRing.ideal_spec A).2.1 hK hL hKL).symm
  exact (congrArg (RingHom.comp _) hcomp₁).trans <| (RingHom.comp_assoc _ _ _).symm.trans <|
    (congrArg₂ RingHom.comp ((CommRingCat.hom_comp _ _).symm.trans hspec) rfl).trans <|
      hsheaf.trans hcomp₂.symm

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
  have hcomp : (((fromSpecQuotient hL).toHom ≫ mapPresheafedSpace φ hφ).stalkMap q).hom =
      ((fromSpecQuotient hL).stalkMap q).hom.comp
        ((mapPresheafedSpace φ hφ).stalkMap ((fromSpecQuotient hL).base q)).hom :=
    (congrArg CommRingCat.Hom.hom
      (PresheafedSpace.stalkMap.comp (fromSpecQuotient hL).toHom (mapPresheafedSpace φ hφ) q)).trans
      (CommRingCat.hom_comp _ _)
  have : IsLocalHom (((fromSpecQuotient hL).stalkMap q).hom.comp
      ((mapPresheafedSpace φ hφ).stalkMap ((fromSpecQuotient hL).base q)).hom) :=
    hcomp ▸ hlocal
  have := isLocalHom_of_comp
    ((mapPresheafedSpace φ hφ).stalkMap ((fromSpecQuotient hL).base q)).hom
    ((fromSpecQuotient hL).stalkMap q).hom
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
  have hid : TopCat.ofHom (comap (RingHom.id A) continuous_id) = 𝟙 (TopCat.of (carrier A)) := by
    simp
  apply LocallyRingedSpace.Hom.ext'
  rw [map_toHom, LocallyRingedSpace.id_toHom]
  refine PresheafedSpace.Hom.ext _ _ hid ?_
  rw [structureSheafMap_id]
  exact TopCat.Sheaf.eqToHom_hom_comp_whiskerRight_of_eq_id hid _ _

variable {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsAdicRing C] (ψ : C →+* B) (hψ : Continuous ψ)

/-- Composition of continuous homomorphisms induces composition in the opposite order. -/
@[reassoc]
theorem map_comp : map (φ.comp ψ) (hφ.comp hψ) = map φ hφ ≫ map ψ hψ := by
  have hfg : TopCat.ofHom (comap (φ.comp ψ) (hφ.comp hψ)) =
      TopCat.ofHom (comap φ hφ) ≫ TopCat.ofHom (comap ψ hψ) := by
    rw [comap_comp, TopCat.ofHom_comp]
  apply LocallyRingedSpace.Hom.ext'
  rw [LocallyRingedSpace.comp_toHom, map_toHom, map_toHom, map_toHom]
  refine PresheafedSpace.Hom.ext _ _ hfg ?_
  have h := congrArg InducedCategory.Hom.hom (structureSheafMap_comp φ hφ ψ hψ
    (IsAdicRing.ideal_spec C).2.1 (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec A).2.1).symm
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    TopCat.Sheaf.pushforward_map, TopCat.Sheaf.eqToHom_hom_eq_whiskerRight_of_eq_comp hfg _ _] at h
  exact h

/-! ### Morphisms of formal spectra are induced by continuous homomorphisms -/

section GlobalSections

/-- The global section `a` restricts on `D(g)` to the image of `a` in the completed localisation
`A_{g}`. -/
private theorem map_globalSectionsIso_inv_apply (g a : A) :
    have := (IsAdicRing.ideal_spec A).2.2
    (Spf A).presheaf.map (homOfLE (le_top : basicOpen g ≤ ⊤)).op
        ((globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv a) =
      (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 g).inv
        (algebraMap A (AdicRing.CompletedAway A g) a) := by
  intro _
  have h : (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv ≫
      (structureSheaf (IsAdicRing.ideal_spec A).2.1).obj.map
        (homOfLE (le_top : basicOpen g ≤ ⊤)).op ≫
        (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1
          g).hom = CommRingCat.ofHom (algebraMap A _) :=
    globalSectionsIso_inv_comp_basicOpenSectionsIso_hom _ _ g
  rw [← Category.assoc, ← Iso.eq_comp_inv] at h
  exact ConcreteCategory.congr_hom h a

/-- The global section of `Spf A` corresponding to `a ∈ A` is invertible exactly on the basic
open set `D(a)`. -/
theorem basicOpen_globalSectionsIso_inv (a : A) :
    have := (IsAdicRing.ideal_spec A).2.2
    (Spf A).toRingedSpace.basicOpen ((globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv a) =
      basicOpen a := by
  intro _
  refine Opens.ext (Set.ext fun (p : carrier A) ↦ ?_)
  let c : BasicNeighbourhood p := ⟨1, (p : PrimeSpectrum A).isPrime.one_notMem⟩
  -- the germ of the global section at `p` is that of its restriction to `D(1)`, the image of
  -- `a` in `A_{1}`, whose residue class at `p` is the image of `a` in `Frac(A ⧸ p)`
  have hgerm : (Spf A).presheaf.germ ⊤ p trivial
      ((globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv a) =
      (Spf A).presheaf.germ (basicOpen c.elem) p (mem_basicOpen.mpr c.notMem)
        ((basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1
          c.elem).inv (algebraMap A (AdicRing.CompletedAway A c.elem) a)) :=
    (TopCat.Presheaf.germ_res_apply (Spf A).presheaf (homOfLE le_top) p _ _).symm.trans
      (congrArg _ (map_globalSectionsIso_inv_apply c.elem a))
  have := (Spf A).isLocalRing p
  refine (RingedSpace.mem_basicOpen (Spf A).toRingedSpace _ p trivial).trans
    (((iff_of_eq (congrArg IsUnit hgerm)).trans ?_).trans (mem_basicOpen (p := p)).symm)
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  refine (map_ne_zero_iff _ (stalkResidueFieldEquiv p).injective).symm.trans ?_
  have key : stalkResidueFieldEquiv p (IsLocalRing.residue _ _) = _ :=
    stalkResidueFieldEquiv_residue_germ c a
  rw [key, ne_eq, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- The ring homomorphism `B → A` induced on global sections by a morphism `Spf A ⟶ Spf B` of
locally ringed spaces, read through the identifications of the global sections with `B` and
`A`. -/
noncomputable def globalSectionsHom (f : Spf A ⟶ Spf B) : B →+* A :=
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec B).2.2
  ((globalSectionsIso (IsAdicRing.ideal_spec B).2.1).inv ≫ f.c.app (op ⊤) ≫
    (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).hom).hom

/-- Under the identifications of the global sections with `B` and `A`, a morphism
`Spf A ⟶ Spf B` acts on global sections by `globalSectionsHom`. -/
@[reassoc]
theorem globalSectionsIso_inv_comp_c_app_top (f : Spf A ⟶ Spf B) :
    have := (IsAdicRing.ideal_spec A).2.2
    have := (IsAdicRing.ideal_spec B).2.2
    (globalSectionsIso (IsAdicRing.ideal_spec B).2.1).inv ≫ f.c.app (op ⊤) =
      CommRingCat.ofHom (globalSectionsHom f) ≫
        (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv := by
  intro _ _
  exact (Iso.eq_comp_inv _).mpr ((Category.assoc _ _ _).trans (CommRingCat.ofHom_hom _).symm)

/-- The morphism of formal spectra induced by `φ` induces `φ` on global sections. -/
@[simp]
theorem globalSectionsHom_map : globalSectionsHom (map φ hφ) = φ := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec B).2.2
  exact congrArg CommRingCat.Hom.hom
    ((congrArg (_ ≫ ·) (map_globalSections φ hφ)).trans (Iso.inv_hom_id_assoc _ _))

/-- A morphism `Spf A ⟶ Spf B` pulls back the basic open set `D(b)` to `D(φ b)`, where `φ` is
its map on global sections. -/
theorem preimage_basicOpen (f : Spf A ⟶ Spf B) (b : B) :
    (Opens.map f.base).obj (basicOpen b) = basicOpen (globalSectionsHom f b) := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec B).2.2
  have h : f.c.app (op ⊤) ((globalSectionsIso (IsAdicRing.ideal_spec B).2.1).inv b) =
      (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv (globalSectionsHom f b) :=
    ConcreteCategory.congr_hom (globalSectionsIso_inv_comp_c_app_top f) b
  -- `D(b)` is the locus where the global section `b` is invertible, and such loci pull back
  -- along morphisms of locally ringed spaces to the loci of the pulled-back sections
  exact ((congrArg (Opens.map f.base).obj (basicOpen_globalSectionsIso_inv b).symm).trans
    (LocallyRingedSpace.preimage_basicOpen f _)).trans
      ((congrArg _ h).trans (basicOpen_globalSectionsIso_inv _))

/-- A morphism `Spf A ⟶ Spf B` sends an open prime `p` of `A` to a prime containing `b ∈ B`
exactly when `p` contains the image of `b` on global sections. -/
theorem mem_base_asIdeal_iff (f : Spf A ⟶ Spf B) (p : carrier A) (b : B) :
    b ∈ (f.base p).1.asIdeal ↔ globalSectionsHom f b ∈ (p : PrimeSpectrum A).asIdeal := by
  have h := iff_of_eq (congrArg (p ∈ ·) (preimage_basicOpen f b))
  exact not_iff_not.mp ((mem_basicOpen (p := f.base p)).symm.trans (h.trans mem_basicOpen))

/-- On points, a morphism `Spf A ⟶ Spf B` pulls back open primes along its map on global
sections. -/
theorem coe_base_apply (f : Spf A ⟶ Spf B) (p : carrier A) :
    (f.base p).1 = PrimeSpectrum.comap (globalSectionsHom f) (p : PrimeSpectrum A) :=
  PrimeSpectrum.ext (Ideal.ext (mem_base_asIdeal_iff f p))

/-- **Automatic continuity**: the ring homomorphism induced on global sections by a morphism of
formal spectra is continuous (EGA I, Ch. I, 10.2.2). The ideal of definition of `B` lies in
every open prime of `B`, so its image lies in every open prime of `A`, that is, in the radical
of the ideal of definition of `A`. -/
theorem continuous_globalSectionsHom (f : Spf A ⟶ Spf B) : Continuous (globalSectionsHom f) := by
  refine (IsAdicRing.ideal_spec B).2.1.continuous_of_map_le_radical (IsAdicRing.ideal_spec A).2.1
    (IsAdicRing.ideal_spec B).1 ?_
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hIP, hP⟩
  let p : carrier A := ⟨⟨P, hP⟩, (mem_carrier_iff_le (IsAdicRing.ideal_spec A).2.1).mpr hIP⟩
  exact (mem_base_asIdeal_iff f p b).mp
    ((mem_carrier_iff_le (IsAdicRing.ideal_spec B).2.1).mp (f.base p).2 hb)

/-- The sheaf map of `f : Spf A ⟶ Spf B` on `D(b)`, followed by restriction to a basic open set
`D(a)` inside the preimage of `D(b)`, as a homomorphism of completed localisations
`B_{b} → A_{a}`. -/
private noncomputable def basicOpenHom (f : Spf A ⟶ Spf B) (b : B) {a : A}
    (h : basicOpen a ≤ (Opens.map f.base).obj (basicOpen b)) :
    AdicRing.CompletedAway B b →+* AdicRing.CompletedAway A a :=
  ((basicOpenSectionsIso (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec B).1 b).inv ≫
    f.c.app (op (basicOpen b)) ≫ (Spf A).presheaf.map (homOfLE h).op ≫
      (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 a).hom).hom

/-- On the image of `B`, the homomorphism `B_{b} → A_{a}` given by `f` is the map of `f` on
global sections. -/
private theorem basicOpenHom_comp_algebraMap (f : Spf A ⟶ Spf B) (b : B) {a : A}
    (h : basicOpen a ≤ (Opens.map f.base).obj (basicOpen b)) :
    (basicOpenHom f b h).comp (algebraMap B (AdicRing.CompletedAway B b)) =
      (algebraMap A (AdicRing.CompletedAway A a)).comp (globalSectionsHom f) := by
  have := (IsAdicRing.ideal_spec A).2.2
  have := (IsAdicRing.ideal_spec B).2.2
  ext x
  have hc : f.c.app (op ⊤) ((globalSectionsIso (IsAdicRing.ideal_spec B).2.1).inv x) =
      (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv (globalSectionsHom f x) :=
    ConcreteCategory.congr_hom (globalSectionsIso_inv_comp_c_app_top f) x
  have hnat : f.c.app (op (basicOpen b)) ((Spf B).presheaf.map
        (homOfLE (le_top : basicOpen b ≤ ⊤)).op
          ((globalSectionsIso (IsAdicRing.ideal_spec B).2.1).inv x)) =
      (Spf A).presheaf.map (homOfLE (le_top : (Opens.map f.base).obj (basicOpen b) ≤
        (Opens.map f.base).obj ⊤)).op
          (f.c.app (op ⊤) ((globalSectionsIso (IsAdicRing.ideal_spec B).2.1).inv x)) :=
    ConcreteCategory.congr_hom (f.c.naturality (homOfLE le_top).op) _
  have hA : (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 a).hom
      ((Spf A).presheaf.map (homOfLE (le_top : basicOpen a ≤ ⊤)).op
        ((globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv (globalSectionsHom f x))) =
      algebraMap A _ (globalSectionsHom f x) := by
    rw [map_globalSectionsIso_inv_apply, Iso.inv_hom_id_apply]
  rw [RingHom.comp_apply, RingHom.comp_apply]
  -- the image of `x` in `B_{b}` is the restriction of the global section `x`, which `f` maps
  -- to the restriction of the global section `φ x`
  calc basicOpenHom f b h (algebraMap B _ x)
      = (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 a).hom
          ((Spf A).presheaf.map (homOfLE h).op (f.c.app (op (basicOpen b))
            ((Spf B).presheaf.map (homOfLE (le_top : basicOpen b ≤ ⊤)).op
              ((globalSectionsIso (IsAdicRing.ideal_spec B).2.1).inv x)))) := by
        rw [map_globalSectionsIso_inv_apply]
        rfl
    _ = (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 a).hom
          ((Spf A).presheaf.map (homOfLE h).op ((Spf A).presheaf.map
            (homOfLE (le_top : (Opens.map f.base).obj (basicOpen b) ≤
              (Opens.map f.base).obj ⊤)).op
            ((globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv (globalSectionsHom f x)))) := by
        rw [hnat, hc]
    _ = _ := by
        refine Eq.trans (congrArg _ ?_) hA
        exact (ConcreteCategory.comp_apply _ _ _).symm.trans
          (ConcreteCategory.congr_hom ((Spf A).presheaf.map_comp _ _).symm _)

/-- The homomorphism `B_{b} → A_{a}` given by `f` is continuous, since its restriction to `B` is
continuous by automatic continuity. -/
private theorem continuous_basicOpenHom (f : Spf A ⟶ Spf B) (b : B) {a : A}
    (h : basicOpen a ≤ (Opens.map f.base).obj (basicOpen b)) :
    Continuous (basicOpenHom f b h) := by
  refine IsAdic.continuous_of_map_le_radical (AdicRing.CompletedAway.isAdic B b)
    (AdicRing.CompletedAway.isAdic A a) ((IsAdicRing.ideal_spec B).1.map _) ?_
  rw [Ideal.map_map, basicOpenHom_comp_algebraMap, ← Ideal.map_map]
  exact (Ideal.map_mono ((IsAdicRing.ideal_spec B).2.1.map_le_radical_of_continuous
    (IsAdicRing.ideal_spec A).2.1 (continuous_globalSectionsHom f))).trans
      (Ideal.map_radical_le _)

/-- Two morphisms `Spf A ⟶ Spf B` with the same map on global sections have the same sheaf map on
`D(b)` followed by restriction to `D(a)`: as homomorphisms `B_{b} → A_{a}` both are continuous and
agree on the image of `B`. -/
private theorem c_app_basicOpen_comp_map_eq {f g : Spf A ⟶ Spf B}
    (hfg : globalSectionsHom f = globalSectionsHom g) (b : B) {a : A}
    (hf : basicOpen a ≤ (Opens.map f.base).obj (basicOpen b))
    (hg : basicOpen a ≤ (Opens.map g.base).obj (basicOpen b)) :
    f.c.app (op (basicOpen b)) ≫ (Spf A).presheaf.map (homOfLE hf).op =
      g.c.app (op (basicOpen b)) ≫ (Spf A).presheaf.map (homOfLE hg).op := by
  have key :
      (basicOpenSectionsIso (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec B).1 b).inv ≫
          f.c.app (op (basicOpen b)) ≫ (Spf A).presheaf.map (homOfLE hf).op ≫
            (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1
              (IsAdicRing.ideal_spec A).1 a).hom =
        (basicOpenSectionsIso (IsAdicRing.ideal_spec B).2.1 (IsAdicRing.ideal_spec B).1 b).inv ≫
          g.c.app (op (basicOpen b)) ≫ (Spf A).presheaf.map (homOfLE hg).op ≫
            (basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1
              (IsAdicRing.ideal_spec A).1 a).hom :=
    congrArg CommRingCat.ofHom <| AdicRing.CompletedAway.ringHom_ext B b
      (g₁ := basicOpenHom f b hf) (g₂ := basicOpenHom g b hg)
      (continuous_basicOpenHom f b hf) (continuous_basicOpenHom g b hg)
      (by rw [basicOpenHom_comp_algebraMap, basicOpenHom_comp_algebraMap, hfg])
  rw [cancel_epi] at key
  exact (Iso.cancel_iso_hom_right _ _ _).mp
    ((Category.assoc _ _ _).trans (key.trans (Category.assoc _ _ _).symm))

/-- Every morphism of locally ringed spaces `Spf A ⟶ Spf B` is induced by its map on global
sections (EGA I, Ch. I, 10.2.2). -/
@[simp]
theorem map_globalSectionsHom (f : Spf A ⟶ Spf B) :
    map (globalSectionsHom f) (continuous_globalSectionsHom f) = f := by
  have hφ := continuous_globalSectionsHom f
  have hbase : (map (globalSectionsHom f) hφ).base = f.base := by
    ext p
    rw [map_base]
    exact Subtype.ext ((coe_comap_apply _ _ p).trans (coe_base_apply f p).symm)
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.Hom.ext _ _ hbase ?_
  -- a map of sheaves is determined by its components on the basic open sets `D(b)`
  refine TopCat.Sheaf.hom_ext _ ((TopCat.Sheaf.pushforward _ f.base).obj (Spf A).sheaf)
    isBasis_basicOpen fun b ↦ ?_
  rw [NatTrans.comp_app, Functor.whiskerRight_app]
  have hf : basicOpen (globalSectionsHom f b) ≤ (Opens.map f.base).obj (basicOpen b) :=
    (preimage_basicOpen f b).ge
  have hm : basicOpen (globalSectionsHom f b) ≤
      (Opens.map (map (globalSectionsHom f) hφ).base).obj (basicOpen b) :=
    ((preimage_basicOpen _ b).trans (by rw [globalSectionsHom_map])).ge
  have key := c_app_basicOpen_comp_map_eq (globalSectionsHom_map _ hφ) b hm hf
  have hle : (Opens.map f.base).obj (basicOpen b) ≤ basicOpen (globalSectionsHom f b) :=
    (preimage_basicOpen f b).le
  -- both sides factor through the restriction to `D(φ b)`, where they agree by `key`
  exact (congrArg (fun i ↦ _ ≫ (Spf A).presheaf.map i)
      (Subsingleton.elim _ ((homOfLE hm).op ≫ (homOfLE hle).op))).trans <|
    (congrArg (_ ≫ ·) ((Spf A).presheaf.map_comp _ _)).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) key).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((Spf A).presheaf.map_comp _ _).symm).trans <|
    (congrArg (fun i ↦ _ ≫ (Spf A).presheaf.map i) (Subsingleton.elim _ (𝟙 _))).trans <|
    (congrArg (_ ≫ ·) ((Spf A).presheaf.map_id _)).trans (Category.comp_id _)

/-- Morphisms of locally ringed spaces `Spf A ⟶ Spf B` correspond to continuous ring
homomorphisms `B → A`, by taking global sections; its inverse is `Spf.map` (EGA I, Ch. I,
10.2.2). -/
noncomputable def homEquiv : (Spf A ⟶ Spf B) ≃ {φ : B →+* A // Continuous φ} where
  toFun f := ⟨globalSectionsHom f, continuous_globalSectionsHom f⟩
  invFun φ := map φ.1 φ.2
  left_inv := map_globalSectionsHom
  right_inv φ := Subtype.ext (globalSectionsHom_map φ.1 φ.2)

/-- `Spf.homEquiv` takes a morphism to its map on global sections. -/
@[simp]
theorem homEquiv_apply_coe (f : Spf A ⟶ Spf B) :
    (homEquiv f : B →+* A) = globalSectionsHom f :=
  (rfl)

/-- The inverse of `Spf.homEquiv` is `Spf.map`. -/
@[simp]
theorem homEquiv_symm_apply (φ : {φ : B →+* A // Continuous φ}) :
    homEquiv.symm φ = map φ.1 φ.2 :=
  (rfl)

/-- The identity of `Spf A` induces the identity on global sections. -/
@[simp]
theorem globalSectionsHom_id : globalSectionsHom (𝟙 (Spf A)) = RingHom.id A := by
  rw [← map_id, globalSectionsHom_map]

/-- Global sections turn composition of morphisms of formal spectra around. -/
@[simp]
theorem globalSectionsHom_comp (f : Spf A ⟶ Spf B) (g : Spf B ⟶ Spf C) :
    globalSectionsHom (f ≫ g) = (globalSectionsHom f).comp (globalSectionsHom g) := by
  rw [← map_globalSectionsHom f, ← map_globalSectionsHom g, ← map_comp, globalSectionsHom_map,
    globalSectionsHom_map, globalSectionsHom_map]

end GlobalSections

end TauCeti.FormalScheme.Spf
