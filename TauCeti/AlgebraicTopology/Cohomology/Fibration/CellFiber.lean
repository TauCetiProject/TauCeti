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

(`TauCeti.TopCat.preimageSkeletonPairSingularCohomologyIsoPi`). These are the objects of the first
page of the cohomological Serre spectral sequence: in its cohomological indexing,
`E₁^{n,q} ≅ ∏ⱼ Hq(Fⱼ; M)` (`TauCeti.TopCat.serreCohomologySpectralSequenceFirstPageXIsoPi`). For
the identity fibration they are the cellular cochain groups. This is the cohomological counterpart
of `TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma`, and the computation follows the
same three steps.

* The projection `(P, ∂P) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` from the pullback of `p` to the disks of the
  `n`-cells, relative to its part over the boundary spheres, induces isomorphisms on relative
  homology with coefficients in `R`
  (`TauCeti.TopCat.isIso_singularHomologyMap_cellPullbackPairMap`).
  The relative singular chains with coefficients in `R` are projective, so it also induces
  isomorphisms on relative cohomology
  (`TauCeti.TopCat.isIso_singularCohomologyMap_cellPullbackPairMap`, through
  `TopPair.isIso_singularCohomologyMap_of_isIso_singularHomologyMap`).
* The pair `(P, ∂P)` is the coproduct of the pullbacks `(Pⱼ, ∂Pⱼ)` along the characteristic maps
  of the single cells (`TauCeti.TopCat.isColimitCofanCellDiskPullbackPairι`), and relative singular
  cohomology turns coproducts of pairs into products
  (`TopPair.isLimitFanSingularCohomologyOfIsColimit`).
* Each `Pⱼ ⟶ Dⁿ` is a Serre fibration over a disk, so `Hq(Fⱼ; M) ≅ Hq+n(Pⱼ, ∂Pⱼ; M)`
  (`TauCeti.TopCat.singularCohomologyPreimageSphereIso`), the fibre of `Pⱼ` over the centre of the
  disk being the fibre `Fⱼ` of `p` (`TauCeti.TopCat.cellDiskPullbackFiberHomeomorph`).

All identifications are natural in maps `f : E ⟶ E'` over `B` between Serre fibrations: on the
factor of `j`, the map induced by `f` acts by the map induced on cohomology by the restriction of
`f` to the fibres over `χⱼ(0)`.

The identification of the first differential `d₁` with the cellular coboundary with
path-transport coefficients, and hence of the second page with `H^n(B; Hq(F; M))`, is not
treated here.

## Main definitions and results

* `TauCeti.TopCat.isIso_singularCohomologyMap_cellPullbackPairMap`: the projection
  `(P, ∂P) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` induces isomorphisms on relative cohomology.
* `TauCeti.TopCat.isLimitFanSingularCohomologyPreimageSkeletonPair`: the maps induced by the
  projections `(Pⱼ, ∂Pⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` exhibit `Hᵐ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` as the product
  of the `Hᵐ(Pⱼ, ∂Pⱼ)`.
* `TauCeti.TopCat.cellDiskPullbackPairSingularCohomologyIso`: `Hq(Fⱼ) ≅ Hq+n(Pⱼ, ∂Pⱼ)`, natural
  in maps over `B` (`TauCeti.TopCat.cellDiskPullbackPairSingularCohomologyIso_hom_naturality`).
* `TauCeti.TopCat.preimageSkeletonPairSingularCohomologyIsoPi`:
  `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ≅ ∏ⱼ Hq(Fⱼ)`, characterized on the factors by
  `TauCeti.TopCat.preimageSkeletonPairSingularCohomologyIsoPi_hom_π`, and natural in maps over `B`
  (`TauCeti.TopCat.preimageSkeletonPairSingularCohomologyIsoPi_hom_naturality`).
* `TauCeti.TopCat.serreCohomologySpectralSequenceFirstPageXIsoPi`: the object `E₁^{n,q}` of the
  first page of the cohomological Serre spectral sequence is `∏ⱼ Hq(Fⱼ)`.

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

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} {C D : Set B} [RelCWComplex C D]
  (hp : serreFibrations p) (R : Type u) [Ring R] (k : Type*) [Ring k]
  [Linear k (ModuleCat.{u} R)] (M : ModuleCat.{u} R)

include hp

/-! ### A single cell -/

/-- **The cohomology of the pullback of a Serre fibration along the characteristic map of a cell,
relative to its part over the boundary sphere, is the cohomology of the fibre over the centre of the
cell, shifted by the dimension:** `Hq(p⁻¹(χⱼ(0)); M) ≅ Hq+n(Pⱼ, ∂Pⱼ; M)`. -/
def cellDiskPullbackPairSingularCohomologyIso (n q : ℕ) (j : cell C n) :
    (_root_.TopCat.of (p ⁻¹' {map n j 0} : Set E)).singularCohomology (ModuleCat.of R R) k M q ≅
      (cellDiskPullbackPair p C n j).singularCohomology (ModuleCat.of R R) k M (q + n) :=
  (singularCohomologyFunctor (ModuleCat.of R R) k M q).mapIso
      (_root_.TopCat.isoOfHomeo (cellDiskPullbackFiberHomeomorph p C n j)).op ≪≫
    singularCohomologyPreimageSphereIso (ModuleCat.of R R) k M
      (mem_serreFibrations_pullbackFst hp (cellULiftMap C n j)) q (q + n) (by simp)

/-- The identification `Hq(Fⱼ) ≅ Hq+n(Pⱼ, ∂Pⱼ)` is restriction along the identification of the
fibre of `Pⱼ` over the centre of the disk with `Fⱼ`, followed by
`TauCeti.TopCat.singularCohomologyPreimageSphereIso`. -/
lemma cellDiskPullbackPairSingularCohomologyIso_hom (n q : ℕ) (j : cell C n) :
    (cellDiskPullbackPairSingularCohomologyIso hp R k M n q j).hom =
      TopCat.singularCohomologyMap
          (_root_.TopCat.isoOfHomeo (cellDiskPullbackFiberHomeomorph p C n j)).hom q ≫
        (singularCohomologyPreimageSphereIso (ModuleCat.of R R) k M
          (mem_serreFibrations_pullbackFst hp (cellULiftMap C n j)) q (q + n) (by simp)).hom := by
  rw [cellDiskPullbackPairSingularCohomologyIso]
  rfl

variable {E' : _root_.TopCat.{u}} {p' : E' ⟶ B} {f : E ⟶ E'} in
/-- The identifications `Hq(Fⱼ) ≅ Hq+n(Pⱼ, ∂Pⱼ)` are natural in maps `f` over `B`: through them,
the map induced by `f` on `Hq+n(Pⱼ, ∂Pⱼ)` is the map induced on `Hq` by any map `g` of the fibres
over the centre of the cell that agrees with `f`. -/
@[reassoc]
lemma cellDiskPullbackPairSingularCohomologyIso_hom_naturality (hp' : serreFibrations p')
    (hf : f ≫ p' = p) (n q : ℕ) (j : cell C n)
    (g : _root_.TopCat.of (p ⁻¹' {map n j 0} : Set E) ⟶
      _root_.TopCat.of (p' ⁻¹' {map n j 0} : Set E'))
    (hg : ∀ x, (g x : E') = f x) :
    (cellDiskPullbackPairSingularCohomologyIso hp' R k M n q j).hom ≫
        TopPair.singularCohomologyMap (cellDiskPullbackPairHom hf n j) (q + n) =
      TopCat.singularCohomologyMap g q ≫
        (cellDiskPullbackPairSingularCohomologyIso hp R k M n q j).hom := by
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
  -- The map of pairs induced by `f` is the one of the naturality statement over the disk.
  have hpair : cellDiskPullbackPairHom hf n j = TopPair.ofSubsetMap
      (_root_.TopCat.pullbackMapOfCompEq (cellULiftMap C n j) hf)
      (TopCat.Hom.mapsTo_preimage_of_comp_eq _ hfP _) :=
    TopPair.hom_ext_of_fst _ (by rw [cellDiskPullbackPairHom_fst, TopPair.ofSubsetMap_fst])
  rw [hpair, cellDiskPullbackPairSingularCohomologyIso_hom,
    cellDiskPullbackPairSingularCohomologyIso_hom]
  -- Move `f` past the disk identification with `nat`, then past the fibre identification with
  -- `hg₀`. The objects of these composites agree only after unfolding `TopCat.of`, so the chase is
  -- assembled as a term rather than with `rw`.
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) nat).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      ((TopCat.singularCohomologyMap_comp g₀ _ q).symm.trans
        ((congrArg (TopCat.singularCohomologyMap · q) hg₀).trans
          (TopCat.singularCohomologyMap_comp _ g q)))).trans (Category.assoc _ _ _))))

variable [T2Space B]

/-! ### The pullback to the disks of the cells -/

variable (C) in
/-- **The skeletal filtration of a Serre fibration over the cells, in cohomology.** For a Serre
fibration `p : E ⟶ B` and a relative CW complex `C ⊆ B` with skeleta `Xⁿ`, the projection
`(P, ∂P) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` from the pullback of `p` to the disks of the `n`-cells, relative to
its part over their boundary spheres, induces isomorphisms on relative singular cohomology with
values in any module `M`, in every degree `m`. -/
theorem isIso_singularCohomologyMap_cellPullbackPairMap (n m : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
      (cellPullbackPairMap p C n) m) :=
  TopPair.isIso_singularCohomologyMap_of_isIso_singularHomologyMap _ (ModuleCat.of R R) k M
    (isIso_singularHomologyMap_cellPullbackPairMap C hp R n) m

variable (C) in
/-- **The relative cohomology of consecutive stages of the skeletal filtration of a Serre
fibration is the product of the contributions of the cells.** The maps induced by the projections
`(Pⱼ, ∂Pⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` from the pullbacks of `p` along the characteristic maps of the
`n`-cells exhibit `Hᵐ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); M)` as the product of the `Hᵐ(Pⱼ, ∂Pⱼ; M)`. -/
def isLimitFanSingularCohomologyPreimageSkeletonPair (n m : ℕ) :
    IsLimit (Fan.mk ((preimageSkeletonPair p C n).singularCohomology (ModuleCat.of R R) k M m)
      fun j ↦ TopPair.singularCohomologyMap (cellDiskPullbackPairMap p C n j) m) :=
  have := isIso_singularCohomologyMap_cellPullbackPairMap C hp R k M n m
  IsLimit.ofIsoLimit (TopPair.isLimitFanSingularCohomologyOfIsColimit _ (ModuleCat.of R R) k M
      (isColimitCofanCellDiskPullbackPairι p C n) m)
    (Fan.ext (asIso (TopPair.singularCohomologyMap (cellPullbackPairMap p C n) m)).symm
      fun j ↦ by
        simp [cellDiskPullbackPairMap_def, TopPair.singularCohomologyMap_comp])

/-! ### The product over the cells -/

variable (C) in
/-- **The first page of the skeletal filtration of a Serre fibration, in cohomology.** For a Serre
fibration `p : E ⟶ B` and a relative CW complex `C ⊆ B` with skeleta `Xⁿ`,
`Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); M) ≅ ∏ⱼ Hq(p⁻¹(χⱼ(0)); M)`, the product running over the `n`-cells `j` of
`C` and `χⱼ(0)` being the centre of the cell `j`. On the factor of `j` it is restriction to the
pullback `(Pⱼ, ∂Pⱼ)` of `p` along the characteristic map of `j`, followed by
`Hq+n(Pⱼ, ∂Pⱼ) ≅ Hq(p⁻¹(χⱼ(0)))`
(`TauCeti.TopCat.preimageSkeletonPairSingularCohomologyIsoPi_hom_π`). -/
def preimageSkeletonPairSingularCohomologyIsoPi (n q : ℕ) :
    (preimageSkeletonPair p C n).singularCohomology (ModuleCat.of R R) k M (q + n) ≅
      ∏ᶜ fun j : cell C n ↦
        (_root_.TopCat.of (p ⁻¹' {map n j 0} : Set E)).singularCohomology (ModuleCat.of R R) k M
          q :=
  (isLimitFanSingularCohomologyPreimageSkeletonPair C hp R k M n (q + n)).conePointUniqueUpToIso
      (productIsProduct _) ≪≫
    Pi.mapIso fun j ↦ (cellDiskPullbackPairSingularCohomologyIso hp R k M n q j).symm

@[reassoc (attr := simp)]
lemma preimageSkeletonPairSingularCohomologyIsoPi_hom_π (n q : ℕ) (j : cell C n) :
    (preimageSkeletonPairSingularCohomologyIsoPi C hp R k M n q).hom ≫ Pi.π _ j =
      TopPair.singularCohomologyMap (cellDiskPullbackPairMap p C n j) (q + n) ≫
        (cellDiskPullbackPairSingularCohomologyIso hp R k M n q j).inv := by
  rw [preimageSkeletonPairSingularCohomologyIsoPi, Iso.trans_hom, Category.assoc,
    Pi.mapIso_hom_π, Iso.symm_hom, ← Category.assoc]
  exact congrArg (· ≫ _) ((isLimitFanSingularCohomologyPreimageSkeletonPair C hp R k M n
    (q + n)).conePointUniqueUpToIso_hom_comp (productIsProduct _) ⟨j⟩)

variable {E' : _root_.TopCat.{u}} {p' : E' ⟶ B} {f : E ⟶ E'} in
/-- **Naturality of the first page of the skeletal filtration of a Serre fibration, in
cohomology.** For a map `f` over `B` between Serre fibrations `p` and `p'`, the identifications
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
  -- On the factor of `j`, this is the naturality of `Hq(Fⱼ) ≅ Hq+n(Pⱼ, ∂Pⱼ)`.
  have hcell := cellDiskPullbackPairSingularCohomologyIso_hom_naturality hp R k M hp' hf n q j
    (g j) (hg j)
  rw [← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq] at hcell
  rw [Category.assoc, preimageSkeletonPairSingularCohomologyIsoPi_hom_π, Category.assoc,
    Limits.Pi.map_π,
    preimageSkeletonPairSingularCohomologyIsoPi_hom_π_assoc, ← hcell,
    ← TopPair.singularCohomologyMap_comp_assoc, cellDiskPullbackPairMap_comp_preimagePairMap,
    TopPair.singularCohomologyMap_comp_assoc]

/-! ### The first page of the cohomological Serre spectral sequence -/

variable (C) in
/-- **The first page of the cohomological Serre spectral sequence.** For a Serre fibration
`p : E ⟶ B` and a relative CW complex `C ⊆ B`, the object at `(s, t)` of the first page of the
cohomological Serre spectral sequence, with `s = n` and `s + t = q + n`, is the product
`∏ⱼ Hq(p⁻¹(χⱼ(0)); M)` over the `n`-cells `j` of `C`. In the classical indexing this is
`E₁^{n,q}`. -/
def serreCohomologySpectralSequenceFirstPageXIsoPi (n q : ℕ) (s t : ℤ) (hs : s = n)
    (hst : s + t = (q + n : ℕ)) :
    ((serreCohomologySpectralSequence C p R k M).page 1).X (s, t) ≅
      ∏ᶜ fun j : cell C n ↦
        (_root_.TopCat.of (p ⁻¹' {map n j 0} : Set E)).singularCohomology (ModuleCat.of R R) k M
          q :=
  filteredSpaceCohomologySpectralSequenceFirstPageXIso (ModuleCat.of R R) k M
      (monotone_preimageSkeleton p) s t (s - 1) s rfl rfl (q + n) hst ≪≫
    eqToIso (congrArg
      (fun P : TopPair.{u} ↦ P.singularCohomology (ModuleCat.of R R) k M (q + n))
      (ofInclusion_preimageSkeleton_sub_one_eq_preimageSkeletonPair n s hs)) ≪≫
    preimageSkeletonPairSingularCohomologyIsoPi C hp R k M n q

/-- On the factor of the `n`-cell `j`,
`TauCeti.TopCat.serreCohomologySpectralSequenceFirstPageXIsoPi` is restriction to the pullback of
`p` along the characteristic map of `j`, followed by `Hq+n(Pⱼ, ∂Pⱼ) ≅ Hq(p⁻¹(χⱼ(0)))`. -/
@[reassoc (attr := simp)]
lemma serreCohomologySpectralSequenceFirstPageXIsoPi_hom_π (n q : ℕ) (s t : ℤ) (hs : s = n)
    (hst : s + t = (q + n : ℕ)) (j : cell C n) :
    (serreCohomologySpectralSequenceFirstPageXIsoPi C hp R k M n q s t hs hst).hom ≫
        Pi.π _ j =
      (filteredSpaceCohomologySpectralSequenceFirstPageXIso (ModuleCat.of R R) k M
          (monotone_preimageSkeleton p) s t (s - 1) s rfl rfl (q + n) hst).hom ≫
        eqToHom (congrArg
          (fun P : TopPair.{u} ↦ P.singularCohomology (ModuleCat.of R R) k M (q + n))
          (ofInclusion_preimageSkeleton_sub_one_eq_preimageSkeletonPair n s hs)) ≫
        TopPair.singularCohomologyMap (cellDiskPullbackPairMap p C n j) (q + n) ≫
        (cellDiskPullbackPairSingularCohomologyIso hp R k M n q j).inv := by
  simp [serreCohomologySpectralSequenceFirstPageXIsoPi]

end TopCat

end TauCeti
