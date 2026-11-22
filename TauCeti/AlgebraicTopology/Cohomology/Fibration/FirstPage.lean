/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Additivity.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Fibration.Disk
public import TauCeti.AlgebraicTopology.Cohomology.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.Singular.Fibration.CellFiber
public import TauCeti.AlgebraicTopology.Singular.Fibration.Cohomology

/-!
# The first page of the cohomological Serre spectral sequence

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex with skeleta
`Xⁿ = skeletonLT C (n + 1)`, and let `M` be a module over a ring `R`. The relative cohomology of
consecutive stages of the filtration `Eₙ = p⁻¹(Xⁿ)` is the product, over the `n`-cells `j`, of the
cohomology of the fibre `Fⱼ = p⁻¹(χⱼ(0))` over the centre of the cell, shifted by `n`:

`Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); M) ≅ ∏ⱼ Hq(Fⱼ; M)`

(`TauCeti.TopCat.preimageSkeletonPairSingularCohomologyIsoPi`). These are the terms of the first
page of the cohomological Serre spectral sequence `TauCeti.TopCat.serreCohomologySpectralSequence`:
in the classical indexing,

`E₁^{s,t} ≅ ∏ⱼ Hᵗ(p⁻¹(χⱼ(0)); M)`,

the product running over the `s`-cells `j` of `C`
(`TauCeti.TopCat.serreCohomologySpectralSequenceFirstPageXIsoPi`). For the identity fibration these
are the cellular cochain groups. This is the dual of the computation of the first page of the
homological Serre spectral sequence as a direct sum
(`TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma`,
`TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma`).

Cohomology is taken with chain coefficients `R` and values in `M`, that is, it is the cohomology of
`Hom(C(-; R), M)`, as for `TauCeti.TopCat.serreCohomologySpectralSequence`.

The computation follows the three steps of the homological one.

* The projection `(P, ∂P) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` from the pullback of `p` to the disjoint union of
  the disks of the `n`-cells, relative to its part over their boundary spheres, induces
  isomorphisms on relative homology
  (`TauCeti.TopCat.isIso_singularHomologyMap_cellPullbackPairMap`).
  The relative singular chains with coefficients in `R` are free, so it also induces isomorphisms
  on relative cohomology (`TopPair.isIso_singularCohomologyMap_of_isIso_singularHomologyMap`).
* The pair `(P, ∂P)` is the coproduct in `TopPair` of the pullbacks `(Pⱼ, ∂Pⱼ)` of `p` along the
  characteristic maps of the single cells (`TauCeti.TopCat.isColimitCofanCellDiskPullbackPairι`),
  and relative singular cohomology takes it to a product
  (`TauCeti.TopPair.isLimitFanSingularCohomologyOfIsColimit`).
* Each `Pⱼ ⟶ Dⁿ` is a Serre fibration over a disk, so `Hq+n(Pⱼ, ∂Pⱼ; M) ≅ Hq(Fⱼ'; M)` for its fibre
  `Fⱼ'` over the centre of the disk (`TauCeti.TopCat.singularCohomologyPreimageSphereIso`), and
  `Fⱼ'` is the fibre `Fⱼ` of `p` (`TauCeti.TopCat.cellDiskPullbackFiberHomeomorph`).

A map `f : E ⟶ E'` over `B` between Serre fibrations induces maps between all these objects, and
the identification is natural for them: on the first page it acts on the factor of `j` by the map
induced on cohomology by the map of fibres over `χⱼ(0)`
(`TauCeti.TopCat.preimageSkeletonPairSingularCohomologyIsoPi_hom_naturality`).

## Main definitions and results

* `TauCeti.TopCat.cellDiskPullbackPairSingularCohomologyIso`: `Hq+n(Pⱼ, ∂Pⱼ; M) ≅ Hq(Fⱼ; M)`,
  natural in maps over `B`
  (`TauCeti.TopCat.cellDiskPullbackPairSingularCohomologyIso_hom_naturality`).
* `TauCeti.TopCat.isLimitFanSingularCohomologyPreimageSkeletonPair`: the maps induced by the
  projections `(Pⱼ, ∂Pⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` exhibit `Hᵐ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); M)` as the
  product of the `Hᵐ(Pⱼ, ∂Pⱼ; M)`.
* `TauCeti.TopCat.preimageSkeletonPairSingularCohomologyIsoPi`:
  `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); M) ≅ ∏ⱼ Hq(Fⱼ; M)`, characterized on the factors by
  `TauCeti.TopCat.preimageSkeletonPairSingularCohomologyIsoPi_hom_π`, and natural in maps over `B`
  (`TauCeti.TopCat.preimageSkeletonPairSingularCohomologyIsoPi_hom_naturality`).
* `TauCeti.TopCat.serreCohomologySpectralSequenceFirstPageXIsoPi`: the first page of the
  cohomological Serre spectral sequence is `E₁^{s,t} ≅ ∏ⱼ Hᵗ(p⁻¹(χⱼ(0)); M)`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1, Section 1.2 (the cohomology spectral sequence).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} {C D : Set B} [RelCWComplex C D]
  (hp : serreFibrations p) (R : Type u) [Ring R] (k : Type*) [Ring k]
  [Linear k (ModuleCat.{u} R)] (M : ModuleCat.{u} R)

section CellDisk

include hp

/-- **The cohomology of the pullback of a Serre fibration along the characteristic map of a cell,
relative to its part over the boundary sphere, is the cohomology of the fibre over the centre of the
cell, shifted by the dimension:** `Hq+n(Pⱼ, ∂Pⱼ; M) ≅ Hq(p⁻¹(χⱼ(0)); M)`. -/
def cellDiskPullbackPairSingularCohomologyIso (n q : ℕ) (j : cell C n) :
    (cellDiskPullbackPair p C n j).singularCohomology (ModuleCat.of R R) k M (q + n) ≅
      (_root_.TopCat.of (p ⁻¹' {map n j 0} : Set E)).singularCohomology (ModuleCat.of R R) k M q :=
  (singularCohomologyPreimageSphereIso (ModuleCat.of R R) k M
      (mem_serreFibrations_pullbackFst hp (cellULiftMap C n j)) q (q + n) (by simp)).symm ≪≫
    ((singularCohomologyFunctor (ModuleCat.of R R) k M q).mapIso
      (_root_.TopCat.isoOfHomeo (cellDiskPullbackFiberHomeomorph p C n j)).op).symm

/-- The identification `Hq+n(Pⱼ, ∂Pⱼ; M) ≅ Hq(Fⱼ; M)` is the inverse of the identification over the
disk followed by the map induced by the identification of the fibres. -/
lemma cellDiskPullbackPairSingularCohomologyIso_hom (n q : ℕ) (j : cell C n) :
    (cellDiskPullbackPairSingularCohomologyIso hp R k M n q j).hom =
      (singularCohomologyPreimageSphereIso (ModuleCat.of R R) k M
          (mem_serreFibrations_pullbackFst hp (cellULiftMap C n j)) q (q + n) (by simp)).inv ≫
        TopCat.singularCohomologyMap
          (_root_.TopCat.isoOfHomeo (cellDiskPullbackFiberHomeomorph p C n j)).inv q :=
  (rfl)

variable {E' : _root_.TopCat.{u}} {p' : E' ⟶ B} {f : E ⟶ E'} in
/-- The identifications `Hq+n(Pⱼ, ∂Pⱼ; M) ≅ Hq(Fⱼ; M)` are natural in maps `f` over `B`: through
them, the map induced by `f` on `Hq+n(Pⱼ, ∂Pⱼ)` is the map induced on `Hq` by any map `g` of the
fibres over the centre of the cell that agrees with `f`. -/
@[reassoc]
lemma cellDiskPullbackPairSingularCohomologyIso_hom_naturality (hp' : serreFibrations p')
    (hf : f ≫ p' = p) (n q : ℕ) (j : cell C n)
    (g : _root_.TopCat.of (p ⁻¹' {map n j 0} : Set E) ⟶
      _root_.TopCat.of (p' ⁻¹' {map n j 0} : Set E'))
    (hg : ∀ x, (g x : E') = f x) :
    TopPair.singularCohomologyMap (cellDiskPullbackPairHom hf n j) (q + n) ≫
        (cellDiskPullbackPairSingularCohomologyIso hp R k M n q j).hom =
      (cellDiskPullbackPairSingularCohomologyIso hp' R k M n q j).hom ≫
        TopCat.singularCohomologyMap g q := by
  have hfP := _root_.TopCat.pullbackMapOfCompEq_comp_pullbackFst (cellULiftMap C n j) hf
  -- The map of the fibres of the pullbacks over the centre of the disk.
  let g₀ := TopCat.Hom.preimageMap _ hfP {x | (x : ULift.{u} (Fin n → ℝ)) = 0}
  have nat := singularCohomologyPreimageSphereIso_hom_naturality (ModuleCat.of R R) k M
    (mem_serreFibrations_pullbackFst hp (cellULiftMap C n j))
    (mem_serreFibrations_pullbackFst hp' (cellULiftMap C n j)) hfP g₀
    (TopCat.Hom.coe_preimageMap_apply _ hfP _) q (q + n) (by simp)
  -- Through the identifications of the fibres over the centres, `g₀` is `g`.
  have hg₀ : g₀ ≫ (_root_.TopCat.isoOfHomeo (cellDiskPullbackFiberHomeomorph p' C n j)).hom =
      (_root_.TopCat.isoOfHomeo (cellDiskPullbackFiberHomeomorph p C n j)).hom ≫ g := by
    ext x
    -- Both sides send `x` to `f x.1.1.2`.
    calc (cellDiskPullbackFiberHomeomorph p' C n j (g₀ x) : E') = (g₀ x).val.val.2 :=
          coe_cellDiskPullbackFiberHomeomorph_apply n j (g₀ x)
      _ = f x.val.val.2 := by
          rw [TopCat.Hom.coe_preimageMap_apply, _root_.TopCat.coe_pullbackMapOfCompEq_apply]
      _ = f (cellDiskPullbackFiberHomeomorph p C n j x) :=
          congrArg f (coe_cellDiskPullbackFiberHomeomorph_apply n j x).symm
      _ = g (cellDiskPullbackFiberHomeomorph p C n j x) := (hg _).symm
  have hg₀' : (_root_.TopCat.isoOfHomeo (cellDiskPullbackFiberHomeomorph p C n j)).inv ≫ g₀ =
      g ≫ (_root_.TopCat.isoOfHomeo (cellDiskPullbackFiberHomeomorph p' C n j)).inv := by
    rw [Iso.eq_comp_inv, Category.assoc, hg₀, Iso.inv_hom_id_assoc]
  -- The map of pairs of the pullbacks over the disk is `cellDiskPullbackPairHom`.
  have hΦ : TopPair.ofSubsetMap (_root_.TopCat.pullbackMapOfCompEq (cellULiftMap C n j) hf)
      ((_root_.TopCat.pullbackMapOfCompEq (cellULiftMap C n j) hf).mapsTo_preimage_of_comp_eq hfP
        {x | (x : ULift.{u} (Fin n → ℝ)) ∈ Metric.sphere 0 1}) = cellDiskPullbackPairHom hf n j :=
    TopPair.hom_ext_of_fst _ (by rw [cellDiskPullbackPairHom_fst, TopPair.ofSubsetMap_fst])
  rw [hΦ] at nat
  -- The naturality of the identification over the disk, read through its inverse.
  have nat' := (Iso.comp_inv_eq _).2 (((Iso.eq_inv_comp _).2 nat).trans (Category.assoc _ _ _).symm)
  rw [cellDiskPullbackPairSingularCohomologyIso_hom, cellDiskPullbackPairSingularCohomologyIso_hom,
    reassoc_of% nat', Category.assoc, ← TopCat.singularCohomologyMap_comp, hg₀',
    TopCat.singularCohomologyMap_comp]

end CellDisk

section Skeleton

variable [T2Space B]

include hp

variable (C) in
/-- The projection `(P, ∂P) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` from the pullback of a Serre fibration `p` to
the disks of the `n`-cells, relative to its part over their boundary spheres, induces isomorphisms
on relative singular cohomology in every degree. -/
theorem isIso_singularCohomologyMap_cellPullbackPairMap (n m : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
      (cellPullbackPairMap p C n) m) :=
  TopPair.isIso_singularCohomologyMap_of_isIso_singularHomologyMap _ _ k M
    (isIso_singularHomologyMap_cellPullbackPairMap C hp R n) m

variable (C) in
/-- **The relative cohomology of consecutive stages of the skeletal filtration of a Serre fibration
is the product of the contributions of the cells.** The projections
`(Pⱼ, ∂Pⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` from the pullbacks of `p` along the characteristic maps of the
`n`-cells exhibit `Hᵐ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); M)` as the product of the `Hᵐ(Pⱼ, ∂Pⱼ; M)`. -/
def isLimitFanSingularCohomologyPreimageSkeletonPair (n m : ℕ) :
    IsLimit (Fan.mk ((preimageSkeletonPair p C n).singularCohomology (ModuleCat.of R R) k M m)
      fun j ↦ TopPair.singularCohomologyMap (cellDiskPullbackPairMap p C n j) m) :=
  have := isIso_singularCohomologyMap_cellPullbackPairMap C hp R k M n m
  IsLimit.ofIsoLimit (TopPair.isLimitFanSingularCohomologyOfIsColimit _ (ModuleCat.{u} R)
      (ModuleCat.of R R) k M (isColimitCofanCellDiskPullbackPairι p C n) m)
    (Fan.ext (asIso (TopPair.singularCohomologyMap (cellPullbackPairMap p C n) m)).symm fun j ↦ by
      rw [Iso.symm_hom, asIso_inv, fan_mk_proj, fan_mk_proj, cofan_mk_inj,
        cellDiskPullbackPairMap_def, TopPair.singularCohomologyMap_comp, IsIso.inv_hom_id_assoc])

variable (C) in
/-- **The first page of the cohomological skeletal filtration of a Serre fibration.** For a Serre
fibration `p : E ⟶ B` and a relative CW complex `C ⊆ B` with skeleta `Xⁿ`,
`Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); M) ≅ ∏ⱼ Hq(p⁻¹(χⱼ(0)); M)`, the product running over the `n`-cells `j` of
`C` and `χⱼ(0)` being the centre of the cell `j`. On the factor of `j` it is
`Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ Hq+n(Pⱼ, ∂Pⱼ) ≅ Hq(p⁻¹(χⱼ(0)))`
(`TauCeti.TopCat.preimageSkeletonPairSingularCohomologyIsoPi_hom_π`). -/
def preimageSkeletonPairSingularCohomologyIsoPi (n q : ℕ) :
    (preimageSkeletonPair p C n).singularCohomology (ModuleCat.of R R) k M (q + n) ≅
      ∏ᶜ fun j : cell C n ↦ (_root_.TopCat.of (p ⁻¹' {map n j 0} : Set E)).singularCohomology
        (ModuleCat.of R R) k M q :=
  (isLimitFanSingularCohomologyPreimageSkeletonPair C hp R k M n (q + n)).conePointUniqueUpToIso
      (productIsProduct _) ≪≫
    Pi.mapIso fun j ↦ cellDiskPullbackPairSingularCohomologyIso hp R k M n q j

/-- On the factor of the `n`-cell `j`, `TauCeti.TopCat.preimageSkeletonPairSingularCohomologyIsoPi`
is restriction along the projection `(Pⱼ, ∂Pⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` followed by
`Hq+n(Pⱼ, ∂Pⱼ) ≅ Hq(p⁻¹(χⱼ(0)))`. -/
@[reassoc (attr := simp)]
lemma preimageSkeletonPairSingularCohomologyIsoPi_hom_π (n q : ℕ) (j : cell C n) :
    (preimageSkeletonPairSingularCohomologyIsoPi C hp R k M n q).hom ≫ Pi.π _ j =
      TopPair.singularCohomologyMap (cellDiskPullbackPairMap p C n j) (q + n) ≫
        (cellDiskPullbackPairSingularCohomologyIso hp R k M n q j).hom := by
  rw [preimageSkeletonPairSingularCohomologyIsoPi, Iso.trans_hom, Category.assoc,
    Pi.mapIso_hom_π]
  exact (isLimitFanSingularCohomologyPreimageSkeletonPair C hp R k M n
    (q + n)).conePointUniqueUpToIso_hom_comp_assoc (productIsProduct _) ⟨j⟩ _

variable {E' : _root_.TopCat.{u}} {p' : E' ⟶ B} {f : E ⟶ E'} in
/-- **Naturality of the first page of the cohomological skeletal filtration of a Serre
fibration.** For a map `f` over `B` between Serre fibrations `p` and `p'`, the identifications
`Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); M) ≅ ∏ⱼ Hq(p⁻¹(χⱼ(0)); M)` intertwine the map induced by `f` on the
consecutive stages of the skeletal filtrations with the product of the maps induced on `Hq` by any
maps `g j` of the fibres over the centres of the cells that agree with `f`. -/
@[reassoc]
theorem preimageSkeletonPairSingularCohomologyIsoPi_hom_naturality (hp' : serreFibrations p')
    (hf : f ≫ p' = p) (n q : ℕ)
    (g : ∀ j : cell C n, _root_.TopCat.of (p ⁻¹' {map n j 0} : Set E) ⟶
      _root_.TopCat.of (p' ⁻¹' {map n j 0} : Set E'))
    (hg : ∀ j x, (g j x : E') = f x) :
    TopPair.singularCohomologyMap
        (TopCat.Hom.preimagePairMap f hf (skeletonLT_subset_skeletonLT_succ C n)) (q + n) ≫
        (preimageSkeletonPairSingularCohomologyIsoPi C hp R k M n q).hom =
      (preimageSkeletonPairSingularCohomologyIsoPi C hp' R k M n q).hom ≫
        Limits.Pi.map fun j ↦ TopCat.singularCohomologyMap (g j) q := by
  refine Pi.hom_ext _ _ fun j ↦ ?_
  -- On the factor of `j`, this is the naturality of `Hq+n(Pⱼ, ∂Pⱼ) ≅ Hq(Fⱼ)`.
  rw [Category.assoc, preimageSkeletonPairSingularCohomologyIsoPi_hom_π, Category.assoc,
    Limits.Pi.map_π,
    preimageSkeletonPairSingularCohomologyIsoPi_hom_π_assoc,
    ← TopPair.singularCohomologyMap_comp_assoc,
    cellDiskPullbackPairMap_comp_preimagePairMap, TopPair.singularCohomologyMap_comp_assoc,
    cellDiskPullbackPairSingularCohomologyIso_hom_naturality hp R k M hp' hf n q j (g j) (hg j)]

variable (C) in
/-- **The first page of the cohomological Serre spectral sequence.** For a Serre fibration
`p : E ⟶ B` and a relative CW complex `C ⊆ B`, the object at `(s, t)` of the first page of the
cohomological Serre spectral sequence of `p` with coefficients in `M` is the product
`∏ⱼ Hᵗ(p⁻¹(χⱼ(0)); M)` over the `s`-cells `j` of `C`. In the classical indexing this is
`E₁^{s,t}`. -/
def serreCohomologySpectralSequenceFirstPageXIsoPi (s t : ℕ) :
    ((serreCohomologySpectralSequence C p R k M).page 1).X ((s : ℤ), (t : ℤ)) ≅
      ∏ᶜ fun j : cell C s ↦ (_root_.TopCat.of (p ⁻¹' {map s j 0} : Set E)).singularCohomology
        (ModuleCat.of R R) k M t :=
  filteredSpaceCohomologySpectralSequenceFirstPageXIso (ModuleCat.of R R) k M
      (monotone_preimageSkeleton p) s t (s - 1) (s - 1 + 1) rfl (by lia) (t + s) (by lia) ≪≫
    eqToIso (congrArg (fun P : TopPair.{u} ↦ P.singularCohomology (ModuleCat.of R R) k M (t + s))
      (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair s (s - 1) rfl)) ≪≫
    preimageSkeletonPairSingularCohomologyIsoPi C hp R k M s t

/-- On the factor of the `s`-cell `j`,
`TauCeti.TopCat.serreCohomologySpectralSequenceFirstPageXIsoPi` is induced by the pullback of `p`
along the characteristic map of `j`, `Ht+s(p⁻¹(Xˢ), p⁻¹(Xˢ⁻¹)) ⟶ Ht+s(Pⱼ, ∂Pⱼ) ≅ Ht(p⁻¹(χⱼ(0)))`. -/
@[reassoc (attr := simp)]
lemma serreCohomologySpectralSequenceFirstPageXIsoPi_hom_π (s t : ℕ) (j : cell C s) :
    (serreCohomologySpectralSequenceFirstPageXIsoPi C hp R k M s t).hom ≫ Pi.π _ j =
      (filteredSpaceCohomologySpectralSequenceFirstPageXIso (ModuleCat.of R R) k M
          (monotone_preimageSkeleton p) s t (s - 1) (s - 1 + 1) rfl (by lia) (t + s) (by lia)).hom ≫
        eqToHom (congrArg
          (fun P : TopPair.{u} ↦ P.singularCohomology (ModuleCat.of R R) k M (t + s))
          (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair s (s - 1) rfl)) ≫
        TopPair.singularCohomologyMap (cellDiskPullbackPairMap p C s j) (t + s) ≫
        (cellDiskPullbackPairSingularCohomologyIso hp R k M s t j).hom := by
  simp [serreCohomologySpectralSequenceFirstPageXIsoPi]

end Skeleton

end TopCat

end TauCeti
