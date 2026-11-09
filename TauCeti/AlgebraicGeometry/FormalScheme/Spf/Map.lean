/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.IdealIndependence

/-!
# The structure-sheaf map of a continuous homomorphism of adic rings

Let `φ : B → A` be a continuous homomorphism of topological rings whose topologies are defined by
ideals `J ⊆ B` and `I ⊆ A`. Pulling open primes back along `φ` is a continuous map
`Spf φ : Spf A → Spf B` of underlying spaces (`TauCeti.FormalScheme.Spf.comap`). This file
constructs the other half of the morphism of ringed spaces `Spf A → Spf B` (EGA I, Ch. I,
10.2.1): the map of sheaves of rings `O_{Spf B} → (Spf φ)_* O_{Spf A}`.

It is built from the thickenings. For ideals of definition `K` of `B` and `L` of `A` with
`φ(K) ⊆ L`, the ring map `B ⧸ K → A ⧸ L` induced by `φ` gives a map from the structure sheaf `O_K`
of `Spec (B ⧸ K)` to the pushforward of the structure sheaf `O_L` of `Spec (A ⧸ L)`, both
transported to the formal spectra. By continuity of `φ`, every ideal of definition `L` of `A`
receives some power of `J`, so composing the projection `O_{Spf B} → O_{J ^ (m + 1)}` with these
maps gives maps `O_{Spf B} → (Spf φ)_* O_L` compatible with the reduction maps of `A`. Since
`O_{Spf A}` is the limit of its thickenings and pushforward along `Spf φ` is a right adjoint, they
assemble to the structure-sheaf map. It does not depend on the choice of the ideals of definition
`J` and `I`, and when `B` is `J`-adically complete and `A` is `I`-adically complete it is `φ`
itself on global sections, under the identifications of the global sections with `B` and `A`
(EGA I, Ch. I, 10.2.2).

## Main definitions

* `TauCeti.FormalScheme.Spf.quotientMap`: for ideals of definition `K` of `B` and `L` of `A` with
  `φ(K) ⊆ L`, the map `O_K → (Spf φ)_* O_L` of the thickenings induced by `B ⧸ K → A ⧸ L`.
* `TauCeti.FormalScheme.Spf.structureSheafMap`: the structure-sheaf map
  `O_{Spf B} → (Spf φ)_* O_{Spf A}`.

## Main results

* `TauCeti.FormalScheme.Spf.quotientTransition_comp_quotientMap`,
  `TauCeti.FormalScheme.Spf.quotientMap_comp_quotientTransition`: the maps of thickenings are
  compatible with the reduction maps of `B` and of `A`.
* `TauCeti.FormalScheme.Spf.quotientSheafGlobalSectionsIso_inv_comp_quotientMap`: on global
  sections, the map of thickenings is `B ⧸ K → A ⧸ L`.
* `TauCeti.FormalScheme.Spf.structureSheafMap_comp_toQuotientSheaf`,
  `TauCeti.FormalScheme.Spf.structureSheafMap_comp_quotientProjection`: the structure-sheaf map
  projects to every thickening of `A` through the maps of thickenings.
* `TauCeti.FormalScheme.Spf.structureSheaf.pushforward_hom_ext`: morphisms into the pushforward
  of `O_{Spf A}` are determined by their projections to the thickenings.
* `TauCeti.FormalScheme.Spf.structureSheafMap_comp_structureSheafIso_hom`: the structure-sheaf map
  commutes with the comparison isomorphisms for different ideals of definition.
* `TauCeti.FormalScheme.Spf.structureSheafMap_hom_app_top_comp_globalSectionsIso_hom`: for
  adically complete `A` and `B`, on global sections the structure-sheaf map is `φ`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, §10.2
  (10.2.1, 10.2.2).
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

namespace TauCeti.FormalScheme.Spf

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
  (φ : B →+* A) (hφ : Continuous φ) {I L L' : Ideal A} {J K K' : Ideal B}

section QuotientMap

/-- The identifications of `Spf A` and `Spf B` with `Spec (A ⧸ L)` and `Spec (B ⧸ K)` are
compatible with the maps induced by `φ` and by `B ⧸ K → A ⧸ L`. -/
theorem comap_quotientInclusion (hK : IsAdic K) (hL : IsAdic L) (hKL : K ≤ L.comap φ)
    (q : PrimeSpectrum (A ⧸ L)) :
    comap φ hφ (quotientInclusion hL q) =
      quotientInclusion hK (PrimeSpectrum.comap (Ideal.quotientMap L φ hKL) q) := by
  ext1
  rw [coe_comap_apply, quotientInclusion_apply, quotientInclusion_apply,
    coe_homeomorphSpecQuotient_symm_apply, coe_homeomorphSpecQuotient_symm_apply,
    ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
    Ideal.quotientMap_comp_mk]

/-- The preimage in `Spec (A ⧸ L)` of the preimage of an open `U` of `Spf B` in `Spf A` lies over
the preimage of `U` in `Spec (B ⧸ K)`, under the map induced by `B ⧸ K → A ⧸ L`. -/
theorem map_quotientInclusion_comap_subset (hK : IsAdic K) (hL : IsAdic L)
    (hKL : K ≤ L.comap φ) (U : Opens (carrier B)) :
    ((Opens.map (quotientInclusion hL)).obj
        ((Opens.map (TopCat.ofHom (comap φ hφ))).obj U)).1 ⊆
      PrimeSpectrum.comap (Ideal.quotientMap L φ hKL) ⁻¹'
        ((Opens.map (quotientInclusion hK)).obj U).1 := by
  intro q hq
  have hq' : comap φ hφ (quotientInclusion hL q) ∈ U := hq
  rw [comap_quotientInclusion φ hφ hK hL hKL] at hq'
  exact hq'

/-- For ideals of definition `K` of `B` and `L` of `A` with `φ(K) ⊆ L`, the map from the
structure sheaf of the thickening `Spec (B ⧸ K)` to the pushforward along `Spf A → Spf B` of the
structure sheaf of `Spec (A ⧸ L)`, induced on sections by `B ⧸ K → A ⧸ L`. -/
noncomputable def quotientMap (hK : IsAdic K) (hL : IsAdic L) (hKL : K ≤ L.comap φ) :
    quotientSheaf hK ⟶
      (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap φ hφ))).obj (quotientSheaf hL) :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (StructureSheaf.comap (Ideal.quotientMap L φ hKL) _ _
        (map_quotientInclusion_comap_subset φ hφ hK hL hKL U.unop))
      naturality _ _ _ := CommRingCat.hom_ext <|
        (StructureSheaf.comap_comp_map _ _ _ _).trans (StructureSheaf.map_comp_comap _ _ _ _).symm }

/-- On sections over an open `U`, the map `O_K → (Spf φ)_* O_L` is the map of structure sheaves
induced by `B ⧸ K → A ⧸ L`. -/
@[simp]
theorem quotientMap_hom_app (hK : IsAdic K) (hL : IsAdic L) (hKL : K ≤ L.comap φ)
    (U : (Opens (carrier B))ᵒᵖ) :
    (quotientMap φ hφ hK hL hKL).hom.app U =
      CommRingCat.ofHom (StructureSheaf.comap (Ideal.quotientMap L φ hKL) _ _
        (map_quotientInclusion_comap_subset φ hφ hK hL hKL U.unop)) := by
  unfold quotientMap
  rfl

/-- The maps induced by `φ` are compatible with the reduction maps of `B`: reducing `O_K → O_K'`
and then mapping to `(Spf φ)_* O_L` is mapping `O_K` to `(Spf φ)_* O_L`. -/
@[reassoc (attr := simp)]
theorem quotientTransition_comp_quotientMap (hK : IsAdic K) (hK' : IsAdic K') (hL : IsAdic L)
    (hKK' : K ≤ K') (hK'L : K' ≤ L.comap φ) :
    quotientTransition hK hK' hKK' ≫ quotientMap φ hφ hK' hL hK'L =
      quotientMap φ hφ hK hL (hKK'.trans hK'L) := by
  apply Sheaf.hom_ext
  ext U : 2
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, quotientTransition_hom_app,
    quotientMap_hom_app, quotientMap_hom_app]
  refine CommRingCat.hom_ext <| (StructureSheaf.comap_comp _ _ _ _ _ _ _).symm.trans
    (StructureSheaf.comap_congr ?_ _ _ _ _)
  exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)

/-- The maps induced by `φ` are compatible with the reduction maps of `A`: mapping `O_K` to
`(Spf φ)_* O_L` and then reducing to `(Spf φ)_* O_L'` is mapping `O_K` to `(Spf φ)_* O_L'`. -/
@[reassoc (attr := simp)]
theorem quotientMap_comp_quotientTransition (hK : IsAdic K) (hL : IsAdic L) (hL' : IsAdic L')
    (hKL : K ≤ L.comap φ) (hLL' : L ≤ L') :
    quotientMap φ hφ hK hL hKL ≫
        (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap φ hφ))).map
          (quotientTransition hL hL' hLL') =
      quotientMap φ hφ hK hL' (hKL.trans (Ideal.comap_mono hLL')) := by
  apply Sheaf.hom_ext
  ext U : 2
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, TopCat.Sheaf.pushforward_map,
    TopCat.Presheaf.pushforward_map_app', quotientTransition_hom_app, quotientMap_hom_app,
    quotientMap_hom_app]
  refine CommRingCat.hom_ext <| (StructureSheaf.comap_comp _ _ _ _ _ _ _).symm.trans
    (StructureSheaf.comap_congr ?_ _ _ _ _)
  exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)

/-- On global sections, the map `O_K → (Spf φ)_* O_L` is the map `B ⧸ K → A ⧸ L` induced by
`φ`. -/
@[reassoc]
theorem quotientSheafGlobalSectionsIso_inv_comp_quotientMap (hK : IsAdic K) (hL : IsAdic L)
    (hKL : K ≤ L.comap φ) :
    (quotientSheafGlobalSectionsIso hK).inv ≫ (quotientMap φ hφ hK hL hKL).hom.app (op ⊤) =
      CommRingCat.ofHom (Ideal.quotientMap L φ hKL) ≫ (quotientSheafGlobalSectionsIso hL).inv := by
  rw [quotientSheafGlobalSectionsIso_inv, quotientSheafGlobalSectionsIso_inv, quotientMap_hom_app]
  exact StructureSheaf.toOpen_comp_comap _ _

end QuotientMap

section StructureSheaf

variable [IsTopologicalRing A] [IsTopologicalRing B]

/-- The map `O_{Spf B} → (Spf φ)_* O_L`, for an ideal of definition `L` of `A`: the projection
to a thickening `O_{J ^ (n + 1)}` with `φ(J ^ (n + 1)) ⊆ L`, followed by `quotientMap`. -/
private noncomputable def toPushforwardQuotientSheaf (hJ : IsAdic J) (hL : IsAdic L) :
    structureSheaf hJ ⟶
      (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap φ hφ))).obj (quotientSheaf hL) :=
  quotientProjection hJ
      (hJ.exists_pow_succ_le_comap (by simpa using hL.isOpen_pow 1) hφ).choose ≫
    quotientMap φ hφ _ hL
      (hJ.exists_pow_succ_le_comap (by simpa using hL.isOpen_pow 1) hφ).choose_spec

omit [IsTopologicalRing A] in
/-- Reducing to a smaller thickening `O_N` before mapping to `(Spf φ)_* O_L` does not change
the composite `O_{Spf B} → O_K → (Spf φ)_* O_L`. -/
private theorem toQuotientSheaf_comp_quotientMap_of_le {N : Ideal B} (hJ : IsAdic J)
    (hN : IsAdic N) (hK : IsAdic K) (hL : IsAdic L) (hNK : N ≤ K) (hKL : K ≤ L.comap φ) :
    toQuotientSheaf hJ hK ≫ quotientMap φ hφ hK hL hKL =
      toQuotientSheaf hJ hN ≫ quotientMap φ hφ hN hL (hNK.trans hKL) := by
  rw [← toQuotientSheaf_comp_quotientTransition hJ hN hK hNK, Category.assoc,
    quotientTransition_comp_quotientMap]

omit [IsTopologicalRing A] in
/-- The composite `O_{Spf B} → O_K → (Spf φ)_* O_L` does not depend on the ideal of definition
`K` with `φ(K) ⊆ L`. -/
private theorem toPushforwardQuotientSheaf_eq (hJ : IsAdic J) (hK : IsAdic K) (hL : IsAdic L)
    (hKL : K ≤ L.comap φ) :
    toPushforwardQuotientSheaf φ hφ hJ hL =
      toQuotientSheaf hJ hK ≫ quotientMap φ hφ hK hL hKL := by
  obtain ⟨n, hn⟩ := hJ.exists_pow_succ_le (by simpa using hK.isOpen_pow 1)
  set c := (hJ.exists_pow_succ_le_comap (by simpa using hL.isOpen_pow 1) hφ).choose
  have hN := is_ideal_adic_pow hJ (c + n).succ_pos
  rw [toPushforwardQuotientSheaf, ← toQuotientSheaf_pow_succ,
    toQuotientSheaf_comp_quotientMap_of_le φ hφ hJ hN _ hL
      (Ideal.pow_le_pow_right (by omega)),
    toQuotientSheaf_comp_quotientMap_of_le φ hφ hJ hN hK hL
      ((Ideal.pow_le_pow_right (by omega)).trans hn)]

omit [IsTopologicalRing A] in
/-- The maps `O_{Spf B} → (Spf φ)_* O_L` are compatible with the reduction maps of `A`. -/
private theorem toPushforwardQuotientSheaf_comp_quotientTransition (hJ : IsAdic J) (hL : IsAdic L)
    (hL' : IsAdic L') (hLL' : L ≤ L') :
    toPushforwardQuotientSheaf φ hφ hJ hL ≫
        (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap φ hφ))).map
          (quotientTransition hL hL' hLL') =
      toPushforwardQuotientSheaf φ hφ hJ hL' := by
  rw [toPushforwardQuotientSheaf, Category.assoc, quotientMap_comp_quotientTransition,
    toPushforwardQuotientSheaf_eq φ hφ hJ (is_ideal_adic_pow hJ (Nat.succ_pos _)) hL',
    toQuotientSheaf_pow_succ]

/-- The adjunction between pullback and pushforward of sheaves along `Spf A → Spf B`. Maps into
the pushforward of `O_{Spf A}` correspond to maps into `O_{Spf A}` itself, which are given by
compatible families of maps to the thickenings. -/
private noncomputable abbrev adjunction :=
  TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat (TopCat.ofHom (comap φ hφ))

/-- The maps corresponding under `adjunction` to the maps `O_{Spf B} → (Spf φ)_* O_L` are
compatible with the reduction maps of `A`. -/
private theorem homEquiv_symm_comp_quotientTransition (hJ : IsAdic J) (hI : IsAdic I) {m n : ℕ}
    (h : m ≤ n) :
    ((adjunction φ hφ).homEquiv _ _).symm
        (toPushforwardQuotientSheaf φ hφ hJ (is_ideal_adic_pow hI n.succ_pos)) ≫
      quotientTransition _ _ (Ideal.pow_le_pow_right (Nat.succ_le_succ h)) =
    ((adjunction φ hφ).homEquiv _ _).symm
      (toPushforwardQuotientSheaf φ hφ hJ (is_ideal_adic_pow hI m.succ_pos)) := by
  rw [← Adjunction.homEquiv_naturality_right_symm,
    toPushforwardQuotientSheaf_comp_quotientTransition]

/-- The **structure-sheaf map** `O_{Spf B} → (Spf φ)_* O_{Spf A}` of the morphism
`Spf A → Spf B` induced by a continuous ring homomorphism `φ : B → A`
(EGA I, Ch. I, 10.2.1). On every thickening it is induced by the maps `B ⧸ K → A ⧸ L` for
ideals of definition with `φ(K) ⊆ L` (`structureSheafMap_comp_toQuotientSheaf`), and these
projections determine it (`structureSheaf.pushforward_hom_ext`). When `A` and `B` are adically
complete, it is `φ` on global sections
(`structureSheafMap_hom_app_top_comp_globalSectionsIso_hom`). -/
noncomputable def structureSheafMap (hJ : IsAdic J) (hI : IsAdic I) :
    structureSheaf hJ ⟶
      (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap φ hφ))).obj (structureSheaf hI) :=
  (adjunction φ hφ).homEquiv _ _ <| structureSheaf.lift hI
    (fun n ↦ ((adjunction φ hφ).homEquiv _ _).symm
      (toPushforwardQuotientSheaf φ hφ hJ (is_ideal_adic_pow hI n.succ_pos)))
    (homEquiv_symm_comp_quotientTransition φ hφ hJ hI)

/-- The structure-sheaf map projects to every thickening `(Spf φ)_* O_{I ^ (n + 1)}` through the
map `B ⧸ K → A ⧸ I ^ (n + 1)`, for any ideal of definition `K` with `φ(K) ⊆ I ^ (n + 1)`. -/
@[reassoc]
theorem structureSheafMap_comp_quotientProjection (hJ : IsAdic J) (hI : IsAdic I) (hK : IsAdic K)
    (n : ℕ) (hKI : K ≤ (I ^ (n + 1)).comap φ) :
    structureSheafMap φ hφ hJ hI ≫
        (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap φ hφ))).map
          (quotientProjection hI n) =
      toQuotientSheaf hJ hK ≫ quotientMap φ hφ hK _ hKI := by
  rw [structureSheafMap, ← Adjunction.homEquiv_naturality_right,
    structureSheaf.lift_quotientProjection _ _ (homEquiv_symm_comp_quotientTransition φ hφ hJ hI),
    Equiv.apply_symm_apply, toPushforwardQuotientSheaf_eq φ hφ hJ hK _ hKI]

omit [IsTopologicalRing B] in
/-- Morphisms into the pushforward of `O_{Spf A}` along `Spf A → Spf B` are determined by their
composites with the pushforwards of the projections to the thickenings. -/
theorem structureSheaf.pushforward_hom_ext (hI : IsAdic I)
    {F : Sheaf (Opens.grothendieckTopology (TopCat.of (carrier B))) CommRingCat}
    {f g : F ⟶
      (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap φ hφ))).obj (structureSheaf hI)}
    (h : ∀ n, f ≫ (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap φ hφ))).map
        (quotientProjection hI n) =
      g ≫ (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap φ hφ))).map
        (quotientProjection hI n)) : f = g :=
  ((adjunction φ hφ).homEquiv _ _).symm.injective <| structureSheaf.hom_ext hI fun n ↦ by
    rw [← Adjunction.homEquiv_naturality_right_symm, ← Adjunction.homEquiv_naturality_right_symm,
      h n]

/-- The structure-sheaf map projects to every thickening `(Spf φ)_* O_L` through the map
`B ⧸ K → A ⧸ L`, for ideals of definition `K` of `B` and `L` of `A` with `φ(K) ⊆ L`. -/
@[reassoc]
theorem structureSheafMap_comp_toQuotientSheaf (hJ : IsAdic J) (hI : IsAdic I) (hK : IsAdic K)
    (hL : IsAdic L) (hKL : K ≤ L.comap φ) :
    structureSheafMap φ hφ hJ hI ≫
        (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap φ hφ))).map
          (toQuotientSheaf hI hL) =
      toQuotientSheaf hJ hK ≫ quotientMap φ hφ hK hL hKL := by
  obtain ⟨n, hn⟩ := hI.exists_pow_succ_le (by simpa using hL.isOpen_pow 1)
  obtain ⟨m, hm⟩ := hJ.exists_pow_succ_le_comap (hI.isOpen_pow (n + 1)) hφ
  have hN := is_ideal_adic_pow hJ m.succ_pos
  rw [toQuotientSheaf_eq hI hL hn, Functor.map_comp, ← Category.assoc,
    structureSheafMap_comp_quotientProjection φ hφ hJ hI hN n hm, Category.assoc,
    quotientMap_comp_quotientTransition, ← toPushforwardQuotientSheaf_eq,
    toPushforwardQuotientSheaf_eq φ hφ hJ hK hL hKL]

/-- The structure-sheaf map does not depend on the ideals of definition: it commutes with the
comparison isomorphisms `structureSheafIso` of `B` and of `A`. -/
@[reassoc]
theorem structureSheafMap_comp_structureSheafIso_hom {I' : Ideal A} {J' : Ideal B}
    (hJ : IsAdic J) (hJ' : IsAdic J') (hI : IsAdic I) (hI' : IsAdic I') :
    structureSheafMap φ hφ hJ hI ≫
        (TopCat.Sheaf.pushforward CommRingCat (TopCat.ofHom (comap φ hφ))).map
          (structureSheafIso hI hI').hom =
      (structureSheafIso hJ hJ').hom ≫ structureSheafMap φ hφ hJ' hI' := by
  refine structureSheaf.pushforward_hom_ext φ hφ hI' fun n ↦ ?_
  obtain ⟨m, hm⟩ := hJ'.exists_pow_succ_le_comap (hI'.isOpen_pow (n + 1)) hφ
  have hN := is_ideal_adic_pow hJ' m.succ_pos
  rw [Category.assoc, ← Functor.map_comp, structureSheafIso_hom_comp_quotientProjection,
    structureSheafMap_comp_toQuotientSheaf φ hφ hJ hI hN _ hm, Category.assoc,
    structureSheafMap_comp_quotientProjection φ hφ hJ' hI' hN n hm,
    structureSheafIso_hom_comp_toQuotientSheaf_assoc]

variable [IsAdicComplete I A] [IsAdicComplete J B]

/-- For adically complete `A` and `B`, the structure-sheaf map of `φ` is `φ` on global sections:
under the identifications of the global sections of `O_{Spf B}` and `O_{Spf A}` with `B` and `A`,
it sends `b` to `φ b` (EGA I, Ch. I, 10.2.2). -/
@[reassoc]
theorem structureSheafMap_hom_app_top_comp_globalSectionsIso_hom (hJ : IsAdic J)
    (hI : IsAdic I) :
    (structureSheafMap φ hφ hJ hI).hom.app (op ⊤) ≫ (globalSectionsIso hI).hom =
      (globalSectionsIso hJ).hom ≫ CommRingCat.ofHom φ := by
  -- Over `⊤`, the sections of a pushforward are the sections over the preimage of `⊤`, which is
  -- `⊤` only by unfolding `Opens.map`. Name the components over `⊤` of the structure-sheaf map
  -- and of `quotientMap` with source and target the sections over `⊤`, so that the rewrites
  -- below see well-typed composites.
  obtain ⟨M, hM⟩ : ∃ M : (structureSheaf hJ).obj.obj (op ⊤) ⟶ (structureSheaf hI).obj.obj (op ⊤),
      M = (structureSheafMap φ hφ hJ hI).hom.app (op ⊤) := ⟨_, rfl⟩
  suffices h : M ≫ (globalSectionsIso hI).hom = (globalSectionsIso hJ).hom ≫ CommRingCat.ofHom φ by
    subst hM
    exact h
  rw [← cancel_epi (globalSectionsIso hJ).inv, Iso.inv_hom_id_assoc]
  refine (IsAdicComplete.isLimitQuotientPowSuccCone I).hom_ext fun n ↦ ?_
  obtain ⟨m, hm⟩ := hJ.exists_pow_succ_le_comap (hI.isOpen_pow (n.unop + 1)) hφ
  have hN := is_ideal_adic_pow hJ m.succ_pos
  obtain ⟨Q, hQ⟩ : ∃ Q : (quotientSheaf hN).obj.obj (op ⊤) ⟶
      (quotientSheaf (is_ideal_adic_pow hI n.unop.succ_pos)).obj.obj (op ⊤),
      Q = (quotientMap φ hφ hN _ hm).hom.app (op ⊤) := ⟨_, rfl⟩
  have hMQ : M ≫ (quotientProjection hI n.unop).hom.app (op ⊤) =
      (toQuotientSheaf hJ hN).hom.app (op ⊤) ≫ Q := by
    subst hM hQ
    exact congrArg (fun f ↦ f.hom.app (op ⊤))
      (structureSheafMap_comp_quotientProjection φ hφ hJ hI hN n.unop hm)
  have hQ' : (quotientSheafGlobalSectionsIso hN).inv ≫ Q =
      CommRingCat.ofHom (Ideal.quotientMap _ φ hm) ≫
        (quotientSheafGlobalSectionsIso (is_ideal_adic_pow hI n.unop.succ_pos)).inv := by
    subst hQ
    exact quotientSheafGlobalSectionsIso_inv_comp_quotientMap φ hφ hN _ hm
  -- Reduce modulo `I ^ (n + 1)`: on global sections, `quotientProjection hI n` followed by the
  -- identification with `A ⧸ I ^ (n + 1)` is the quotient map.
  have hI' : (globalSectionsIso hI).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n.unop + 1))) =
      (quotientProjection hI n.unop).hom.app (op ⊤) ≫
        (quotientSheafGlobalSectionsIso (is_ideal_adic_pow hI n.unop.succ_pos)).hom := by
    rw [← cancel_epi (globalSectionsIso hI).inv, Iso.inv_hom_id_assoc,
      globalSectionsIso_inv_comp_quotientProjection_assoc, Iso.inv_hom_id, Category.comp_id]
  -- The apex of `Ideal.quotientPowSuccCone I` is `CommRingCat.of A` only by unfolding, and its
  -- legs are the quotient maps; state the reduction of the goal modulo `I ^ (n + 1)` directly.
  have key : ((globalSectionsIso hJ).inv ≫ M ≫ (globalSectionsIso hI).hom) ≫
      CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n.unop + 1))) =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n.unop + 1))) := by
    rw [Category.assoc, Category.assoc, hI', reassoc_of% hMQ,
      globalSectionsIso_inv_comp_toQuotientSheaf_assoc, reassoc_of% hQ', Iso.inv_hom_id,
      Category.comp_id, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]
  exact key

end StructureSheaf

end TauCeti.FormalScheme.Spf
