/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.SpectralSequence
public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.Naturality
public import TauCeti.Algebra.Homology.SpectralSequence.Comparison

/-!
# Naturality of the Künneth spectral sequence

A chain map `f : K ⟶ K'` of complexes of modules over a commutative ring induces a morphism of
Künneth spectral sequences (`HomologicalComplex.kunnethSpectralSequenceMapLeft`): the morphism of
the spectral sequences of the column filtrations
(`HomologicalComplex₂.columnFiltrationSpectralSequenceMap`) induced by the morphism of Künneth
bicomplexes `HomologicalComplex.kunnethBicomplexMapLeft f L`, `f ▷ Q.X p` on column `p` for the
Cartan–Eilenberg resolution `Q` of `L`. On the first page, identified with
`⨁_{i + j = k} Hᵢ(K) ⊗ Hⱼ(Q.X p)`, it is the map induced by the maps `Hᵢ(f)`
(`HomologicalComplex.kunnethSpectralSequenceFirstPageXIso_hom_naturality`), and on the second page,
identified with `⨁_{i + j = q} Torₚ(Hᵢ(K), Hⱼ(L))`, it is the map induced by the maps
`Torₚ(Hᵢ(f), Hⱼ(L))` (`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso_hom_naturality`).

The Künneth bicomplex is built from the Cartan–Eilenberg resolution of the second variable, so a
chain map `g : L₁ ⟶ L₂` induces a morphism of Künneth spectral sequences
(`HomologicalComplex.kunnethSpectralSequenceMapRight`) through a lift of `g` to the
Cartan–Eilenberg resolutions (`ChainComplex.cartanEilenbergResolutionMap`). That lift depends on
choices, so no functoriality is stated for it. More generally, any morphism `ψ` of the
Cartan–Eilenberg resolutions induces a morphism of Künneth spectral sequences
(`HomologicalComplex.kunnethSpectralSequenceMapRightOfLift`), functorially in `ψ`. On the first
page it is the map induced by the maps `Hⱼ(ψ.f p)`
(`HomologicalComplex.kunnethSpectralSequenceFirstPageXIso_hom_naturality_rightOfLift`). When `ψ`
lies over `g`, on the second page it is the map induced by the maps `Torₚ(Hᵢ(K), Hⱼ(g))`
(`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso_hom_naturality_rightOfLift`), so from
the second page on it does not depend on `ψ`
(`HomologicalComplex.kunnethSpectralSequenceMapRightOfLift_hom_eq`).

## Main definitions and results

* `HomologicalComplex.kunnethSpectralSequenceMapLeft`: the morphism of Künneth spectral sequences
  in the first variable, with `HomologicalComplex.kunnethSpectralSequenceMapLeft_id` and
  `HomologicalComplex.kunnethSpectralSequenceMapLeft_comp`.
* `HomologicalComplex.kunnethSpectralSequenceFirstPageXIso_hom_naturality`,
  `HomologicalComplex.kunnethFirstPageXIsoTorSum_hom_naturality`: the morphism in the first
  variable on the first page.
* `HomologicalComplex.kunnethSpectralSequenceSecondPageXIso_hom_naturality`: the morphism in the
  first variable on the second page.
* `HomologicalComplex.kunnethSpectralSequenceMapRight`: a morphism of Künneth spectral sequences
  in the second variable, through a lift to the Cartan–Eilenberg resolutions, and
  `HomologicalComplex.kunnethSpectralSequenceMapRightOfLift`, through any morphism of
  Cartan–Eilenberg resolutions, with `HomologicalComplex.kunnethSpectralSequenceMapRightOfLift_id`
  and `HomologicalComplex.kunnethSpectralSequenceMapRightOfLift_comp`.
* `HomologicalComplex.kunnethSpectralSequenceFirstPageXIso_hom_naturality_rightOfLift`, with its
  instance `HomologicalComplex.kunnethSpectralSequenceFirstPageXIso_hom_naturality_right`, and
  `HomologicalComplex.kunnethFirstPageXIsoTorSum_hom_naturality_rightOfLift`: the morphism in the
  second variable on the first page.
* `HomologicalComplex.kunnethSpectralSequenceSecondPageXIso_hom_naturality_rightOfLift`, with its
  instance `HomologicalComplex.kunnethSpectralSequenceSecondPageXIso_hom_naturality_right`: the
  morphism in the second variable on the second page, the map induced on `Tor` in the second
  variable.
* Both second-page results, in either variable, are deduced from
  `HomologicalComplex.kunnethSpectralSequenceSecondPageXIso_hom_naturality_of_firstPage`, in
  `TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.SpectralSequence`.
* `HomologicalComplex.kunnethSpectralSequenceMapRightOfLift_hom_eq`: two lifts of the same chain
  map induce the same morphism from the second page on.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Limits ChainComplex

universe u

namespace HomologicalComplex

variable {R : Type u} [CommRing R] {K K' K'' : ChainComplex (ModuleCat.{u} R) ℕ}
  (f : K ⟶ K') (f' : K' ⟶ K'') (L : ChainComplex (ModuleCat.{u} R) ℕ)

/-- **Naturality of the Künneth spectral sequence in the first variable**: the morphism of
Künneth spectral sequences induced by a chain map `f : K ⟶ K'`, that of the spectral sequences of
the column filtrations induced by `HomologicalComplex.kunnethBicomplexMapLeft f L`. -/
abbrev kunnethSpectralSequenceMapLeft :
    kunnethSpectralSequence K L ⟶ kunnethSpectralSequence K' L :=
  HomologicalComplex₂.columnFiltrationSpectralSequenceMap (kunnethBicomplexMapLeft f L)

@[simp]
lemma kunnethSpectralSequenceMapLeft_id : kunnethSpectralSequenceMapLeft (𝟙 K) L = 𝟙 _ := by
  simp [kunnethSpectralSequenceMapLeft]

@[simp]
lemma kunnethSpectralSequenceMapLeft_comp :
    kunnethSpectralSequenceMapLeft (f ≫ f') L =
      kunnethSpectralSequenceMapLeft f L ≫ kunnethSpectralSequenceMapLeft f' L := by
  simp [kunnethSpectralSequenceMapLeft]

/-- **The morphism of Künneth spectral sequences in the first variable on the first page.** Under
the identifications `HomologicalComplex.kunnethSpectralSequenceFirstPageXIso` of the first pages at
column `p`, degree `k` with `⨁_{i + j = k} Hᵢ(K) ⊗ Hⱼ(Q.X p)`, the morphism induced by `f` is the
map induced by the maps `Hᵢ(f)`. -/
@[reassoc]
theorem kunnethSpectralSequenceFirstPageXIso_hom_naturality (p k : ℕ) :
    ((kunnethSpectralSequenceMapLeft f L).hom 2).f (-(k : ℤ) - 2 * p, p) ≫
        (kunnethSpectralSequenceFirstPageXIso K' L p k).hom =
      (kunnethSpectralSequenceFirstPageXIso K L p k).hom ≫
        GradedObject.Monoidal.whiskerRight (fun i ↦ homologyMap f i)
          (fun j ↦ ((ChainComplex.cartanEilenbergResolution L).X p).homology j) k := by
  simp only [kunnethSpectralSequenceFirstPageXIso_eq, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso_hom_naturality_assoc,
    Category.assoc]
  congr 1
  rw [IsIso.eq_inv_comp, ← kunnethColumnHomologyKunneth_naturality_left_assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- The morphism of Künneth spectral sequences in the first variable on the first page, under the
identifications `HomologicalComplex.kunnethFirstPageXIsoTorSum` with the terms of the complexes
`HomologicalComplex.kunnethTorSumComplex`: it is the morphism of complexes
`HomologicalComplex.kunnethTorSumComplexMap` induced by the maps `Hᵢ(f)`. -/
@[reassoc]
theorem kunnethFirstPageXIsoTorSum_hom_naturality (p q : ℕ) :
    ((kunnethSpectralSequenceMapLeft f L).hom 2).f (-(q : ℤ) - 2 * p, p) ≫
        (kunnethFirstPageXIsoTorSum K' L p q).hom =
      (kunnethFirstPageXIsoTorSum K L p q).hom ≫
        (kunnethTorSumComplexMap L (fun i ↦ homologyMap f i) q).f p := by
  rw [kunnethFirstPageXIsoTorSum_eq, kunnethFirstPageXIsoTorSum_eq, Iso.trans_hom, Iso.trans_hom,
    kunnethSpectralSequenceFirstPageXIso_hom_naturality_assoc,
    tensorObjIsoKunnethTorSumComplexX_hom_naturality, Category.assoc]

/-- **The morphism of Künneth spectral sequences in the first variable on the second page.** Under
the identifications `HomologicalComplex.kunnethSpectralSequenceSecondPageXIso` of the second pages
at column `p`, degree `q` with `⨁_{i + j = q} Torₚ(Hᵢ(K), Hⱼ(L))`, the morphism induced by `f` is
the map induced by the maps `Torₚ(Hᵢ(f), Hⱼ(L))`. -/
@[reassoc]
theorem kunnethSpectralSequenceSecondPageXIso_hom_naturality (p q : ℕ) :
    ((kunnethSpectralSequenceMapLeft f L).hom 3).f (-(q : ℤ) - 2 * p, p) ≫
        (kunnethSpectralSequenceSecondPageXIso K' L p q).hom =
      (kunnethSpectralSequenceSecondPageXIso K L p q).hom ≫
        GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{u} R) p) (fun x ↦ x.1 + x.2)
          (fun i ↦ homologyMap f i) (𝟙 fun j ↦ L.homology j) q := by
  rw [kunnethSpectralSequenceSecondPageXIso_hom_naturality_of_firstPage K L _ p q _
      (kunnethFirstPageXIsoTorSum_hom_naturality f L p q),
    kunnethTorSumComplexHomologyIso_hom_naturality, Iso.inv_hom_id_assoc]

section Right

variable (K) {L₁ L₂ L₃ : ChainComplex (ModuleCat.{u} R) ℕ} (g : L₁ ⟶ L₂)

/-- **A morphism of Künneth spectral sequences in the second variable**: the morphism of the
spectral sequences of the column filtrations induced by
`HomologicalComplex.kunnethBicomplexMapRight K g`, over a chain map `g : L₁ ⟶ L₂`. It depends on
the choice of the lift of `g` to the Cartan–Eilenberg resolutions, but only up to the first page:
from the second page on it is the map induced by the maps `Torₚ(Hᵢ(K), Hⱼ(g))`
(`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso_hom_naturality_right`,
`HomologicalComplex.kunnethSpectralSequenceMapRightOfLift_hom_eq`). -/
abbrev kunnethSpectralSequenceMapRight :
    kunnethSpectralSequence K L₁ ⟶ kunnethSpectralSequence K L₂ :=
  HomologicalComplex₂.columnFiltrationSpectralSequenceMap (kunnethBicomplexMapRight K g)

/-- The morphism of Künneth spectral sequences induced by a morphism `ψ` of the Cartan–Eilenberg
resolutions of `L₁` and `L₂`: the morphism of the spectral sequences of the column filtrations
induced by `HomologicalComplex.kunnethBicomplexMapRightOfLift K ψ`. -/
abbrev kunnethSpectralSequenceMapRightOfLift
    (ψ : cartanEilenbergResolution L₁ ⟶ cartanEilenbergResolution L₂) :
    kunnethSpectralSequence K L₁ ⟶ kunnethSpectralSequence K L₂ :=
  HomologicalComplex₂.columnFiltrationSpectralSequenceMap (kunnethBicomplexMapRightOfLift K ψ)

/-- The morphism of Künneth spectral sequences over `g` is the one induced by the lift
`ChainComplex.cartanEilenbergResolutionMap g` of `g` to the Cartan–Eilenberg resolutions. -/
lemma kunnethSpectralSequenceMapRight_eq :
    kunnethSpectralSequenceMapRight K g =
      kunnethSpectralSequenceMapRightOfLift K (ChainComplex.cartanEilenbergResolutionMap g) :=
  congrArg HomologicalComplex₂.columnFiltrationSpectralSequenceMap (kunnethBicomplexMapRight_eq K g)

/-- The identity of the Cartan–Eilenberg resolution induces the identity of the Künneth spectral
sequence. -/
@[simp]
lemma kunnethSpectralSequenceMapRightOfLift_id :
    kunnethSpectralSequenceMapRightOfLift K (𝟙 (cartanEilenbergResolution L₁)) = 𝟙 _ := by
  simp [kunnethSpectralSequenceMapRightOfLift]

/-- `HomologicalComplex.kunnethSpectralSequenceMapRightOfLift` is compatible with composition. -/
@[simp]
lemma kunnethSpectralSequenceMapRightOfLift_comp
    (ψ : cartanEilenbergResolution L₁ ⟶ cartanEilenbergResolution L₂)
    (ψ' : cartanEilenbergResolution L₂ ⟶ cartanEilenbergResolution L₃) :
    kunnethSpectralSequenceMapRightOfLift K (ψ ≫ ψ') =
      kunnethSpectralSequenceMapRightOfLift K ψ ≫ kunnethSpectralSequenceMapRightOfLift K ψ' := by
  simp [kunnethSpectralSequenceMapRightOfLift]

variable (ψ : cartanEilenbergResolution L₁ ⟶ cartanEilenbergResolution L₂)

/-- **The morphism of Künneth spectral sequences induced by a morphism `ψ` of Cartan–Eilenberg
resolutions, on the first page.** Under the identifications
`HomologicalComplex.kunnethSpectralSequenceFirstPageXIso` of the first pages at column `p`,
degree `k` with `⨁_{i + j = k} Hᵢ(K) ⊗ Hⱼ(Q.X p)`, it is the map induced by the maps
`Hⱼ(ψ.f p)`. -/
@[reassoc]
theorem kunnethSpectralSequenceFirstPageXIso_hom_naturality_rightOfLift (p k : ℕ) :
    ((kunnethSpectralSequenceMapRightOfLift K ψ).hom 2).f (-(k : ℤ) - 2 * p, p) ≫
        (kunnethSpectralSequenceFirstPageXIso K L₂ p k).hom =
      (kunnethSpectralSequenceFirstPageXIso K L₁ p k).hom ≫
        GradedObject.Monoidal.whiskerLeft (fun i ↦ K.homology i)
          (fun j ↦ homologyMap (ψ.f p) j) k := by
  have h : kunnethColumnHomologyKunneth K L₁ p k ≫
      homologyMap ((kunnethBicomplexMapRightOfLift K ψ).f p) k =
      GradedObject.Monoidal.whiskerLeft (fun i ↦ K.homology i)
        (fun j ↦ homologyMap (ψ.f p) j) k ≫ kunnethColumnHomologyKunneth K L₂ p k := by
    rw [kunnethBicomplexMapRightOfLift_f]
    -- the columns of the Künneth bicomplexes are `K ⊗ Q.X p` by definition
    exact (kunnethColumnHomologyKunneth_naturality_right K p k (ψ.f p)).symm
  simp only [kunnethSpectralSequenceFirstPageXIso_eq, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso_hom_naturality_assoc,
    Category.assoc]
  congr 1
  rw [IsIso.eq_inv_comp, reassoc_of% h, IsIso.hom_inv_id, Category.comp_id]

/-- The morphism of Künneth spectral sequences induced by `ψ` on the first page, under the
identifications `HomologicalComplex.kunnethFirstPageXIsoTorSum` with the terms of the complexes
`HomologicalComplex.kunnethTorSumComplex`: it is the morphism of complexes
`HomologicalComplex.kunnethTorSumComplexMapRight` induced by the morphisms
`ChainComplex.cartanEilenbergResolution.homologyResolutionMap ψ j` of the resolutions of the
homology. -/
@[reassoc]
theorem kunnethFirstPageXIsoTorSum_hom_naturality_rightOfLift (p q : ℕ) :
    ((kunnethSpectralSequenceMapRightOfLift K ψ).hom 2).f (-(q : ℤ) - 2 * p, p) ≫
        (kunnethFirstPageXIsoTorSum K L₂ p q).hom =
      (kunnethFirstPageXIsoTorSum K L₁ p q).hom ≫
        (kunnethTorSumComplexMapRight K
          (fun j ↦ ChainComplex.cartanEilenbergResolution.homologyResolutionMap ψ j) q).f p := by
  rw [kunnethFirstPageXIsoTorSum_eq, kunnethFirstPageXIsoTorSum_eq, Iso.trans_hom, Iso.trans_hom,
    kunnethSpectralSequenceFirstPageXIso_hom_naturality_rightOfLift_assoc,
    tensorObjIsoKunnethTorSumComplexX_hom_naturality_right K _ q p _
      (fun j ↦ ChainComplex.cartanEilenbergResolution.homologyResolutionMap_f ψ j p),
    Category.assoc]

/-- **The morphism of Künneth spectral sequences induced by a morphism `ψ` of Cartan–Eilenberg
resolutions over `g : L₁ ⟶ L₂`, on the second page.** Under the identifications
`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso` of the second pages at column `p`,
degree `q` with `⨁_{i + j = q} Torₚ(Hᵢ(K), Hⱼ(L))`, it is the map induced by the maps
`Torₚ(Hᵢ(K), Hⱼ(g))`. In particular it does not depend on `ψ`. -/
@[reassoc]
theorem kunnethSpectralSequenceSecondPageXIso_hom_naturality_rightOfLift
    (hψ : ψ.f 0 ≫ cartanEilenbergResolutionπ L₂ = cartanEilenbergResolutionπ L₁ ≫ g)
    (p q : ℕ) :
    ((kunnethSpectralSequenceMapRightOfLift K ψ).hom 3).f (-(q : ℤ) - 2 * p, p) ≫
        (kunnethSpectralSequenceSecondPageXIso K L₂ p q).hom =
      (kunnethSpectralSequenceSecondPageXIso K L₁ p q).hom ≫
        GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{u} R) p) (fun x ↦ x.1 + x.2)
          (𝟙 fun i ↦ K.homology i) (fun j ↦ homologyMap g j) q := by
  rw [kunnethSpectralSequenceSecondPageXIso_hom_naturality_of_firstPage K L₁ _ p q _
      (kunnethFirstPageXIsoTorSum_hom_naturality_rightOfLift K ψ p q),
    kunnethTorSumComplexHomologyIso_hom_naturality_right K _ _
      (fun j ↦ ChainComplex.cartanEilenbergResolution.homologyResolutionMap_f_zero_comp_π_f_zero
        ψ g hψ j),
    Iso.inv_hom_id_assoc]

/-- **Independence of the lift from the second page on.** Two morphisms `ψ` and `ψ'` of
Cartan–Eilenberg resolutions over the same chain map `g` induce the same morphism of Künneth
spectral sequences on every page `r ≥ 3`, that is, from the second page on. -/
theorem kunnethSpectralSequenceMapRightOfLift_hom_eq
    (ψ' : cartanEilenbergResolution L₁ ⟶ cartanEilenbergResolution L₂)
    (hψ : ψ.f 0 ≫ cartanEilenbergResolutionπ L₂ = cartanEilenbergResolutionπ L₁ ≫ g)
    (hψ' : ψ'.f 0 ≫ cartanEilenbergResolutionπ L₂ = cartanEilenbergResolutionπ L₁ ≫ g)
    (r : ℤ) (hr : 3 ≤ r) :
    (kunnethSpectralSequenceMapRightOfLift K ψ).hom r (by omega) =
      (kunnethSpectralSequenceMapRightOfLift K ψ').hom r (by omega) := by
  refine SpectralSequence.Hom.hom_eq_of_le _ _ 3 (by omega) ?_ r hr
  ext ⟨a, b⟩ : 1
  by_cases hab : 0 ≤ b ∧ a + 2 * b ≤ 0
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, b = p := ⟨b.toNat, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q : ℕ, a = -(q : ℤ) - 2 * p := ⟨(-(a + 2 * p)).toNat, by omega⟩
    rw [← cancel_mono (kunnethSpectralSequenceSecondPageXIso K L₂ p q).hom,
      kunnethSpectralSequenceSecondPageXIso_hom_naturality_rightOfLift K g ψ hψ,
      kunnethSpectralSequenceSecondPageXIso_hom_naturality_rightOfLift K g ψ' hψ']
  · exact ((kunnethBicomplex K L₁).flip.isZero_rowFiltrationSpectralSequence_page_X 3
      (by omega) a b (by omega)).eq_of_src _ _

/-- **The morphism of Künneth spectral sequences in the second variable on the first page.** Under
the identifications `HomologicalComplex.kunnethSpectralSequenceFirstPageXIso`, the morphism over
`g` is the map induced by the maps `Hⱼ(Q(g).f p)` for the lift
`Q(g) = ChainComplex.cartanEilenbergResolutionMap g`. -/
@[reassoc]
theorem kunnethSpectralSequenceFirstPageXIso_hom_naturality_right (p k : ℕ) :
    ((kunnethSpectralSequenceMapRight K g).hom 2).f (-(k : ℤ) - 2 * p, p) ≫
        (kunnethSpectralSequenceFirstPageXIso K L₂ p k).hom =
      (kunnethSpectralSequenceFirstPageXIso K L₁ p k).hom ≫
        GradedObject.Monoidal.whiskerLeft (fun i ↦ K.homology i)
          (fun j ↦ homologyMap ((ChainComplex.cartanEilenbergResolutionMap g).f p) j) k := by
  rw [kunnethSpectralSequenceMapRight_eq]
  exact kunnethSpectralSequenceFirstPageXIso_hom_naturality_rightOfLift K _ p k

/-- **The morphism of Künneth spectral sequences in the second variable on the second page.**
Under the identifications `HomologicalComplex.kunnethSpectralSequenceSecondPageXIso` of the second
pages at column `p`, degree `q` with `⨁_{i + j = q} Torₚ(Hᵢ(K), Hⱼ(L))`, the morphism over `g` is
the map induced by the maps `Torₚ(Hᵢ(K), Hⱼ(g))`. It does not depend on the choice of the lift of
`g` to the Cartan–Eilenberg resolutions. -/
@[reassoc]
theorem kunnethSpectralSequenceSecondPageXIso_hom_naturality_right (p q : ℕ) :
    ((kunnethSpectralSequenceMapRight K g).hom 3).f (-(q : ℤ) - 2 * p, p) ≫
        (kunnethSpectralSequenceSecondPageXIso K L₂ p q).hom =
      (kunnethSpectralSequenceSecondPageXIso K L₁ p q).hom ≫
        GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{u} R) p) (fun x ↦ x.1 + x.2)
          (𝟙 fun i ↦ K.homology i) (fun j ↦ homologyMap g j) q := by
  rw [kunnethSpectralSequenceMapRight_eq]
  exact kunnethSpectralSequenceSecondPageXIso_hom_naturality_rightOfLift K g _
    (ChainComplex.cartanEilenbergResolutionMap_π g) p q

end Right

end HomologicalComplex
