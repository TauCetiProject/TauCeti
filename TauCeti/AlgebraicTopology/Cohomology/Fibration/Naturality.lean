/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Fibration.CellFiber

/-!
# Naturality of the cohomological Serre spectral sequence in maps of fibrations

Let `p : E ⟶ B` and `p' : E' ⟶ B'` be maps to spaces carrying relative CW complexes `C ⊆ B` and
`C' ⊆ B'`, and let `f : E ⟶ E'` lie over a map `g : B ⟶ B'`, that is `f ≫ p' = p ≫ g`. If `g` is
cellular, carrying each skeleton of `C` into the skeleton of `C'` of the same dimension, then `f`
carries the preimages of the skeleta of `C` into those of `C'`, so pulling back cochains along `f`
induces a morphism from the cohomological Serre spectral sequence of `p'` to that of `p`
(`TauCeti.TopCat.serreCohomologySpectralSequenceMap`). It is by definition the morphism of
cohomology spectral sequences of filtered spaces
`TauCeti.filteredSpaceCohomologySpectralSequenceMap`, so it is functorial
(`TauCeti.filteredSpaceCohomologySpectralSequenceMap_id`,
`TauCeti.filteredSpaceCohomologySpectralSequenceMap_comp`).

A map `f` over the identity of `B`, that is `f ≫ p' = p`, induces the morphism
`TauCeti.TopCat.serreCohomologySpectralSequenceMapOver`. Between Serre fibrations, its first page
is described cell by cell. Through the identifications `E₁^{n,q} ≅ ∏ⱼ Hq(p⁻¹(χⱼ(0)); M)` of
`TauCeti.TopCat.serreCohomologySpectralSequenceFirstPageXIsoPi`, the morphism acts on the factor of
the `n`-cell `j` by the map induced on `Hq` by the restriction `p⁻¹(χⱼ(0)) ⟶ p'⁻¹(χⱼ(0))` of `f` to
the fibres over the centre of the cell
(`TauCeti.TopCat.serreCohomologySpectralSequenceFirstPageXIsoPi_hom_naturality`).

**Comparison theorem.** If `f` induces isomorphisms on the cohomology of the fibres over the
points of `C`, then the morphism of cohomological Serre spectral sequences is an isomorphism on
every object of every page from the first on
(`TauCeti.TopCat.isIso_serreCohomologySpectralSequenceMapOver_hom_f`).

## Main definitions

* `TauCeti.TopCat.serreCohomologySpectralSequenceMap`: the morphism of cohomological Serre
  spectral sequences induced by a map of fibrations over a cellular map of the bases.
* `TauCeti.TopCat.serreCohomologySpectralSequenceMapOver`: its special case for a map of fibrations
  over the identity of `B`.

## Main results

* `TauCeti.TopCat.serreCohomologySpectralSequenceFirstPageXIsoPi_hom_naturality`: on the first
  page, the morphism induced by a map over `B` is the product of the maps of the fibres over the
  centres of the cells.
* `TauCeti.TopCat.isIso_singularCohomologyMap_preimagePairMap`: a map of Serre fibrations over `B`
  which is a cohomology isomorphism on the fibres over the centres of the `n`-cells is one on the
  pairs `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))`.
* `TauCeti.TopCat.isIso_serreCohomologySpectralSequenceMapOver_hom_f`: a map of Serre fibrations
  over `B` that is a cohomology isomorphism on the fibres induces an isomorphism of cohomological
  Serre spectral sequences from the first page on.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1 and Theorem 3.4 (the comparison theorem for cohomological spectral sequences).
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

section Map

variable {E B E' B' : _root_.TopCat.{u}} [T2Space B] [T2Space B'] {C D : Set B}
  [RelCWComplex C D] {C' D' : Set B'} [RelCWComplex C' D'] {p : E ⟶ B} {p' : E' ⟶ B'}
  {f : E ⟶ E'} {g : B ⟶ B'}

variable (C C') in
/-- **The morphism of cohomological Serre spectral sequences induced by a map of fibrations.** A
map `f : E ⟶ E'` over a map `g : B ⟶ B'` that carries each skeleton of `C` into the skeleton of
`C'` of the same dimension induces, by pulling back cochains, a morphism from the cohomological
Serre spectral sequence of `p'` over `C'` to that of `p` over `C`: the morphism of cohomology
spectral sequences of the filtrations of `E` and `E'` by the preimages of the skeleta
(`TauCeti.filteredSpaceCohomologySpectralSequenceMap`). No fibration hypothesis is needed to
define it. -/
abbrev serreCohomologySpectralSequenceMap (R : Type u) [Ring R] (k : Type*) [Ring k]
    [Linear k (ModuleCat.{u} R)] (M : ModuleCat.{u} R) (hfg : f ≫ p' = p ≫ g)
    (hg : ∀ n : ℕ, MapsTo g (skeletonLT C n) (skeletonLT C' n)) :
    serreCohomologySpectralSequence C' p' R k M ⟶ serreCohomologySpectralSequence C p R k M :=
  filteredSpaceCohomologySpectralSequenceMap (ModuleCat.of R R) k M f
    (mapsTo_preimageSkeleton_of_mapsTo_skeletonLT
      (by rw [← TopCat.coe_comp, hfg, TopCat.coe_comp]) hg)
    (monotone_preimageSkeleton p) (monotone_preimageSkeleton p')

end Map

section MapOver

variable {E B E' : _root_.TopCat.{u}} [T2Space B] {C D : Set B} [RelCWComplex C D] {p : E ⟶ B}
  {p' : E' ⟶ B} {f : E ⟶ E'}

variable (C) in
/-- **The morphism of cohomological Serre spectral sequences induced by a map over `B`.** A map
`f : E ⟶ E'` with `f ≫ p' = p` induces a morphism from the cohomological Serre spectral sequence
of `p'` over `C` to that of `p`: the morphism
`TauCeti.TopCat.serreCohomologySpectralSequenceMap` over the identity of `B`. -/
abbrev serreCohomologySpectralSequenceMapOver (R : Type u) [Ring R] (k : Type*) [Ring k]
    [Linear k (ModuleCat.{u} R)] (M : ModuleCat.{u} R) (hf : f ≫ p' = p) :
    serreCohomologySpectralSequence C p' R k M ⟶ serreCohomologySpectralSequence C p R k M :=
  serreCohomologySpectralSequenceMap C C R k M (g := 𝟙 B) (hf.trans (Category.comp_id p).symm)
    fun _ ↦ by rw [TopCat.coe_id]; exact mapsTo_id _

variable (R : Type u) [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{u} R)]
  (M : ModuleCat.{u} R)

/-- On the stage `a ≤ b` of the skeletal filtrations, for `a = n - 1` and `b = n`, the map of
pairs induced by a map `f` over `B` is the map `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p'⁻¹(Xⁿ), p'⁻¹(Xⁿ⁻¹))` of
preimages of consecutive skeleta, through the identifications of the two pairs. -/
private lemma singularCohomologyMap_filteredSpaceStepMap_comp_eqToHom (hf : f ≫ p' = p) (n : ℕ)
    (a b : ℤ) (ha : a = n - 1) (hb : b = n) (m : ℕ) :
    TopPair.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
        (filteredSpaceStepMap (monotone_preimageSkeleton (C := C) p)
          (monotone_preimageSkeleton (C := C) p') f
          (mapsTo_preimageSkeleton f fun x ↦ ConcreteCategory.congr_hom hf x)
          (by lia : a ≤ b)) m ≫
        eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularCohomology (ModuleCat.of R R) k M m)
          (TopPair.ofInclusion_congr _ (preimage_mono (skeletonLT_subset_skeletonLT_succ C n))
            (preimageSkeleton_eq_preimage_skeletonLT p n a ha)
            (by rw [show b = a + 1 by lia]
                exact preimageSkeleton_add_one_eq_preimage_skeletonLT p n a ha))) =
      eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularCohomology (ModuleCat.of R R) k M m)
          (TopPair.ofInclusion_congr _ (preimage_mono (skeletonLT_subset_skeletonLT_succ C n))
            (preimageSkeleton_eq_preimage_skeletonLT p' n a ha)
            (by rw [show b = a + 1 by lia]
                exact preimageSkeleton_add_one_eq_preimage_skeletonLT p' n a ha))) ≫
        TopPair.singularCohomologyMap
          (TopCat.Hom.preimagePairMap f hf (skeletonLT_subset_skeletonLT_succ C n)) m :=
  TopPair.singularCohomologyMap_comp_eqToHom_of_eq
    (preimageSkeleton_eq_preimage_skeletonLT p n a ha)
    (by rw [show b = a + 1 by lia]; exact preimageSkeleton_add_one_eq_preimage_skeletonLT p n a ha)
    (preimageSkeleton_eq_preimage_skeletonLT p' n a ha)
    (by rw [show b = a + 1 by lia]; exact preimageSkeleton_add_one_eq_preimage_skeletonLT p' n a ha)
    _ _
    (fun x ↦ (filteredSpaceStepMap_fst_apply _ _ f _ _ x).trans <| Eq.symm <|
      (congrArg Subtype.val (ConcreteCategory.congr_hom
        (TopCat.Hom.preimagePairMap_fst f hf (skeletonLT_subset_skeletonLT_succ C n))
          ⟨x.val, _⟩)).trans (TopCat.Hom.coe_preimageMap_apply f hf _ ⟨x.val, _⟩)) m

end MapOver

section OverBase

variable {E B E' : _root_.TopCat.{u}} [T2Space B] {C D : Set B} [RelCWComplex C D] {p : E ⟶ B}
  {p' : E' ⟶ B} {f : E ⟶ E'} (hp : serreFibrations p) (hp' : serreFibrations p')
  (R : Type u) [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{u} R)] (M : ModuleCat.{u} R)

include hp hp' in
/-- **The first page of the morphism of cohomological Serre spectral sequences induced by a map
over `B`.** For a map `f` over `B` between Serre fibrations `p` and `p'`, the identifications
`E₁^{n,q} ≅ ∏ⱼ Hq(p⁻¹(χⱼ(0)); M)` of `TauCeti.TopCat.serreCohomologySpectralSequenceFirstPageXIsoPi`
intertwine the morphism of cohomological Serre spectral sequences with the product, over the
`n`-cells `j`, of the maps induced on `Hq` by the restrictions `p⁻¹(χⱼ(0)) ⟶ p'⁻¹(χⱼ(0))` of `f`
to the fibres over the centres of the cells. -/
@[reassoc]
theorem serreCohomologySpectralSequenceFirstPageXIsoPi_hom_naturality (hf : f ≫ p' = p)
    (n q : ℕ) (s t : ℤ) (hs : s = n) (hst : s + t = (q + n : ℕ)) :
    ((serreCohomologySpectralSequenceMapOver C R k M hf).hom 1 le_rfl).f (s, t) ≫
        (serreCohomologySpectralSequenceFirstPageXIsoPi C hp R k M n q s t hs hst).hom =
      (serreCohomologySpectralSequenceFirstPageXIsoPi C hp' R k M n q s t hs hst).hom ≫
        Limits.Pi.map fun j ↦ TopCat.singularCohomologyMap (f.preimageMap hf {map n j 0}) q := by
  -- The naturality of the first page of the filtered spaces (`e₁`), of the identification of the
  -- step `s - 1 ≤ s` with the pair of preimages of consecutive skeleta (`e₂`), and of the product
  -- over the cells (`e₃`).
  have e₁ := filteredSpaceCohomologySpectralSequenceFirstPageXIso_hom_naturality
    (ModuleCat.of R R) k M f (mapsTo_preimageSkeleton f fun x ↦ ConcreteCategory.congr_hom hf x)
    (monotone_preimageSkeleton (C := C) p) (monotone_preimageSkeleton (C := C) p') s t (s - 1)
    (s - 1 + 1) rfl (sub_add_cancel s 1) (q + n) hst
  have e₂ := singularCohomologyMap_filteredSpaceStepMap_comp_eqToHom (C := C) R k M hf n (s - 1)
    (s - 1 + 1) (by lia) (by lia) (q + n)
  have e₃ := preimageSkeletonPairSingularCohomologyIsoPi_hom_naturality (C := C) hp R k M hp' hf n q
    (fun j ↦ f.preimageMap hf {map n j 0}) (fun j x ↦ f.coe_preimageMap_apply hf _ x)
  -- The identification of the first page is the composite of these three, through objects that
  -- agree only up to unfolding, so the equations are composed as terms.
  rw [serreCohomologySpectralSequenceFirstPageXIsoPi_hom,
    serreCohomologySpectralSequenceFirstPageXIsoPi_hom]
  exact (Category.assoc (obj := ModuleCat k) _ _ _).symm.trans <| (eq_whisker e₁ _).trans <|
    (Category.assoc (obj := ModuleCat k) _ _ _).trans <| (whisker_eq _ <|
      (Category.assoc (obj := ModuleCat k) _ _ _).symm.trans <| (eq_whisker e₂ _).trans <|
        (Category.assoc (obj := ModuleCat k) _ _ _).trans <| (whisker_eq _ e₃).trans
          (Category.assoc (obj := ModuleCat k) _ _ _).symm).trans
    (Category.assoc (obj := ModuleCat k) _ _ _).symm

include hp hp' in
variable (C) in
/-- **A map of Serre fibrations inducing isomorphisms on the cohomology of the fibres over the
centres of the cells induces isomorphisms on consecutive stages of the skeletal filtrations.** Let
`f` be a map over `B` between Serre fibrations `p` and `p'`, and let `C ⊆ B` be a relative CW
complex with skeleta `Xⁿ`. If the restrictions of `f` to the fibres over the centres of the
`n`-cells induce isomorphisms on `Hq(-; M)`, then `f` induces an isomorphism
`Hq+n(p'⁻¹(Xⁿ), p'⁻¹(Xⁿ⁻¹); M) ≅ Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); M)`. -/
theorem isIso_singularCohomologyMap_preimagePairMap (hf : f ≫ p' = p) (n q : ℕ)
    (hfib : ∀ j : cell C n, IsIso (TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k)
      (M := M) (f.preimageMap hf {map n j 0}) q)) :
    IsIso (TopPair.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
      (TopCat.Hom.preimagePairMap f hf (skeletonLT_subset_skeletonLT_succ C n)) (q + n)) := by
  have e := preimageSkeletonPairSingularCohomologyIsoPi_hom_naturality (C := C) hp R k M hp' hf n q
    (fun j ↦ f.preimageMap hf {map n j 0}) (fun j x ↦ f.coe_preimageMap_apply hf _ x)
  rw [← Iso.eq_comp_inv] at e
  rw [e]
  infer_instance

include hp hp' in
/-- **The comparison theorem for maps of Serre fibrations, in cohomology.** Let `f` be a map over
`B` between Serre fibrations `p` and `p'`, and let `C ⊆ B` be a relative CW complex. If for every
point `b` of `C` the restriction `p⁻¹(b) ⟶ p'⁻¹(b)` of `f` induces isomorphisms on the singular
cohomology `Hq(-; M)` of the fibres in every degree `q`, then the morphism of cohomological Serre
spectral sequences induced by `f` is an isomorphism on every object of every page `r ≥ 1`. -/
theorem isIso_serreCohomologySpectralSequenceMapOver_hom_f (hf : f ≫ p' = p)
    (hfib : ∀ b ∈ C, ∀ q : ℕ, IsIso (TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k)
      (M := M) (f.preimageMap hf {b}) q))
    (r : ℤ) (hr : 1 ≤ r) (st : ℤ × ℤ) :
    IsIso (((serreCohomologySpectralSequenceMapOver C R k M hf).hom r hr).f st) := by
  refine isIso_filteredSpaceCohomologySpectralSequenceMap_hom_f _ _ _ _ _ _ _ (fun s m ↦ ?_) r hr
    st
  rcases lt_or_ge s 0 with hs | hs
  · -- Below the base both stages are the preimage of `D`, so both pairs have no cohomology.
    have hz {E₀ : _root_.TopCat.{u}} (p₀ : E₀ ⟶ B) :
        IsZero ((TopPair.ofInclusion (monotone_preimageSkeleton (C := C) p₀
          (by lia : s - 1 ≤ s))).singularCohomology (ModuleCat.of R R) k M m) :=
      TopPair.isZero_singularCohomology_of_surjective_map _ _ _ _ (fun y ↦ by
        refine ⟨⟨y.val, ?_⟩, rfl⟩
        rw [preimageSkeleton_of_neg (C := C) p₀ (by lia : s - 1 < 0),
          ← preimageSkeleton_of_neg (C := C) p₀ hs]
        exact y.property) m
    exact (hz p').isIso (hz p) _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n := ⟨s.toNat, by lia⟩
  rcases lt_or_ge m n with hm | hm
  · -- Below the cell dimension both pairs have no cohomology.
    exact (isZero_singularCohomology_preimageSkeleton hp' R k M C n m (by lia)).isIso
      (isZero_singularCohomology_preimageSkeleton hp R k M C n m (by lia)) _
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, m = q + n := ⟨m - n, by lia⟩
  -- On the preimages of consecutive skeleta the map is an isomorphism, since the fibre over the
  -- centre of each cell is a fibre over a point of `C`.
  have hpair := isIso_singularCohomologyMap_preimagePairMap C hp hp' R k M hf n q fun j ↦
    hfib _ (closedCell_subset_complex n j ⟨0, Metric.mem_closedBall_self zero_le_one, rfl⟩) q
  have e := singularCohomologyMap_filteredSpaceStepMap_comp_eqToHom (C := C) R k M hf n (n - 1) n
    rfl rfl (q + n)
  have he : IsIso (_ ≫ _) := (congrArg IsIso e).mpr inferInstance
  exact (isIso_comp_right_iff _ _).1 he

end OverBase

end TopCat

end TauCeti
