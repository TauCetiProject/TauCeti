/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.Fibration.CellFiber
public import TauCeti.AlgebraicTopology.Singular.ReducedRelative
public import TauCeti.Topology.CWComplex.Classical.Sphere.Basic
public import TauCeti.Topology.CWComplex.Comparison

/-!
# Serre fibrations over a sphere

Let `p : E ⟶ Sⁿ` be a Serre fibration over the unit sphere of `EuclideanSpace ℝ ι`, `n ≥ 1`, and
let `F = p⁻¹(x₀)` be its fibre over the pole `x₀ = TauCeti.spherePolePoint h`. The sphere is a CW
complex with one `0`-cell, the pole, and one `n`-cell (`TauCeti.sphereCWComplex`), so the
skeletal filtration of `E` has just two stages `F ⊆ E`, and the relative homology of the pair
`(E, F)` is the homology of the fibre over the centre `x₁ = TauCeti.sphereTopCellCenter h` of the
top cell, shifted by `n`:

`Hq+n(E, F; R) ≅ Hq(p⁻¹(x₁); R)` (`TauCeti.TopCat.sphereFibrationSingularHomologyIso`),

and `Hₘ(E, F; R) = 0` for `m < n`
(`TauCeti.TopCat.isZero_singularHomology_sphereFibration_of_lt`). Together with the long exact
sequence of the pair `(E, F)` these are the terms of the Wang sequence
`⋯ ⟶ Hₖ(F) ⟶ Hₖ(E) ⟶ Hₖ₋ₙ(p⁻¹(x₁)) ⟶ Hₖ₋₁(F) ⟶ ⋯` of a fibration over a sphere. One consequence
needs no knowledge of the connecting maps: `Hq+n(E; R) ≅ Hq(p⁻¹(x₁); R)` whenever `F` has no
homology in degrees `q + n` and `q + n - 1`
(`TauCeti.TopCat.singularHomologySphereFibrationIsoOfIsZero`). When the total
space is contractible, the connecting isomorphisms of the pair turn them into
`H~q+n-1(F; R) ≅ Hq(p⁻¹(x₁); R)`; for the path fibration of the sphere this computes the homology of
the loop space of the sphere.

These are the first-page computations of the skeletal filtration of a Serre fibration
(`TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma` and
`TauCeti.TopCat.isZero_singularHomology_preimage_skeletonLT`), applied to the CW structure of the
sphere, read on the sphere itself rather than on the ambient Euclidean space
(`TauCeti.toRelativeCWComplex` and its classical round trip).

## Main definitions

* `TauCeti.TopCat.sphereRelCWComplex`: the CW structure of the sphere on the sphere itself, with
  its skeleta `TauCeti.TopCat.skeletonLT_sphereRelCWComplex`,
  `TauCeti.TopCat.skeletonLT_succ_sphereRelCWComplex` and its single top cell
  `TauCeti.TopCat.uniqueCellSphereRelCWComplex`.
* `TauCeti.TopCat.spherePreimageSkeletonPairIso`: the pair of the two stages of the skeletal
  filtration of `E` is the pair `(E, F)`.

## Main results

* `TauCeti.TopCat.sphereFibrationSingularHomologyIso`: `Hq+n(E, F; R) ≅ Hq(p⁻¹(x₁); R)`.
* `TauCeti.TopCat.isZero_singularHomology_sphereFibration_of_lt`: `Hₘ(E, F; R) = 0` for `m < n`.
* `TauCeti.TopCat.singularHomologySphereFibrationIsoOfIsZero`: `Hq+n(E; R) ≅ Hq(p⁻¹(x₁); R)` when
  `Hq+n(F; R)` and `Hq+n-1(F; R)` vanish.
* `TauCeti.TopCat.reducedSingularHomologySphereFibrationIso`,
  `TauCeti.TopCat.isZero_reducedSingularHomology_sphereFibration_of_lt`: for a contractible total
  space over `Sⁿ⁺¹`, `H~q+n(F; R) ≅ Hq(p⁻¹(x₁); R)`, and `H~ₖ(F; R) = 0` for `k < n`.

## References

* H.-C. Wang, *The homology groups of the fibre bundles over a sphere*, Duke Math. J. 16 (1949),
  33–38.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1 (the Wang sequence of a fibration over a sphere).
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

variable {ι : Type u} [Fintype ι] {n : ℕ}

section Fibration

variable (h : Fintype.card ι = n + 1)

/-- The CW structure of the unit sphere `Sⁿ`, transported from the ambient Euclidean space to the
sphere itself by the classical round trip `TauCeti.toRelativeCWComplex`. -/
@[instance_reducible]
def sphereRelCWComplex :
    letI := sphereCWComplex h
    RelCWComplex (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1))
      (range (ContinuousMap.inclusion (base_subset_complex
        (C := (sphere (0 : EuclideanSpace ℝ ι) 1))))) :=
  letI := sphereCWComplex h
  (toRelativeCWComplex (sphere (0 : EuclideanSpace ℝ ι) 1)).toRelCWComplex

section Skeleton

/-- For `1 ≤ k ≤ n`, `skeletonLT k` of the CW structure on the sphere is the pole. -/
lemma skeletonLT_sphereRelCWComplex {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    letI := sphereRelCWComplex h
    (skeletonLT (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) k :
      Set (sphere (0 : EuclideanSpace ℝ ι) 1)) = {spherePolePoint h} := by
  let _ := sphereCWComplex h
  let _ := sphereRelCWComplex h
  refine Subtype.val_injective.image_injective ?_
  rw [image_categoricalRoundTrip_skeletonLT, image_singleton,
    skeletonLT_sphereCWComplex h (mod_cast hk) (mod_cast hkn), coe_spherePolePoint]

/-- The cells of the CW structure on the sphere itself are the cells of the CW structure on the
sphere in the ambient Euclidean space. -/
private def sphereRelCWComplexCellEquiv (m : ℕ) :
    letI := sphereCWComplex h
    letI := sphereRelCWComplex h
    cell (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) m ≃
      cell (sphere (0 : EuclideanSpace ℝ ι) 1) m :=
  letI := sphereCWComplex h
  (toRelativeCWComplex (sphere (0 : EuclideanSpace ℝ ι) 1)).toRelCWComplexCellEquiv m

/-- The CW structure on the sphere has no cells above dimension `n`, so `skeletonLT (n + 1)` is the
whole sphere. -/
lemma skeletonLT_succ_sphereRelCWComplex :
    letI := sphereRelCWComplex h
    (skeletonLT (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) ((n + 1 : ℕ) : ℕ∞) :
      Set (sphere (0 : EuclideanSpace ℝ ι) 1)) = univ :=
  letI := sphereCWComplex h
  letI := sphereRelCWComplex h
  skeletonLT_eq_complex_of_isEmpty_cell _ (n + 1) fun _ hm ↦
    have := isEmpty_cell_sphereCWComplex h hm
    (sphereRelCWComplexCellEquiv h _).isEmpty

/-- The CW structure on `Sⁿ`, `n ≥ 1`, has exactly one `n`-cell. -/
@[instance_reducible]
def uniqueCellSphereRelCWComplex (hn : 1 ≤ n) :
    letI := sphereRelCWComplex h
    Unique (cell (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) n) :=
  letI := sphereCWComplex h
  letI := sphereRelCWComplex h
  letI := uniqueCellSphereCWComplex h (by omega)
  (sphereRelCWComplexCellEquiv h n).unique

/-- The centre of the `n`-cell of the CW structure on the sphere is
`TauCeti.sphereTopCellCenter h`. -/
private lemma map_sphereRelCWComplex_zero (hn : n ≠ 0)
    (i : letI := sphereRelCWComplex h; cell (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) n) :
    letI := sphereRelCWComplex h
    map (C := (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1))) n i 0 = sphereTopCellCenter h := by
  let _ := sphereCWComplex h
  let _ := sphereRelCWComplex h
  refine Subtype.ext ?_
  have := categoricalRoundTrip_map_apply (sphere (0 : EuclideanSpace ℝ ι) 1) n i
    ⟨0, mem_closedBall_self zero_le_one⟩
  exact (this.trans (congrArg (fun f : PartialEquiv _ _ ↦ f 0)
    (map_sphereCWComplex_of_ne_zero h hn (sphereRelCWComplexCellEquiv h n i)))).trans
    (coe_sphereTopCellCenter h).symm

end Skeleton

section Fibre

variable {E : _root_.TopCat.{u}} {p : E ⟶ _root_.TopCat.of (sphere (0 : EuclideanSpace ℝ ι) 1)}

/-- The pair `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` of the two stages of the skeletal filtration of `E` is the pair
`(E, F)` of `E` and the fibre over the pole. -/
def spherePreimageSkeletonPairIso (hn : 1 ≤ n) :
    letI := sphereRelCWComplex h
    preimageSkeletonPair p (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) n ≅
      TopPair.ofSubset (p ⁻¹' {spherePolePoint h}) :=
  letI := sphereRelCWComplex h
  TopPair.ofInclusionIsoOfSubset _
    (fun x ↦ by rw [mem_preimage, skeletonLT_succ_sphereRelCWComplex h]; exact mem_univ _)
    (fun x ↦ by rw [mem_preimage, mem_preimage, skeletonLT_sphereRelCWComplex h hn le_rfl])

@[simp]
lemma spherePreimageSkeletonPairIso_hom_fst_apply (hn : 1 ≤ n)
    (x : letI := sphereRelCWComplex h
      (preimageSkeletonPair p (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) n).fst) :
    TopPair.Hom.fst (spherePreimageSkeletonPairIso h hn).hom x = x.val :=
  TopPair.ofInclusionIsoOfSubset_hom_fst_apply ..

/-- The projection of the pullback over the top cell, read in the pair `(E, F)`, sends a point of
the pullback to its point of `E`. -/
@[simp]
lemma spherePreimageSkeletonPairIso_hom_fst_cellPullbackPairMap_fst_apply (hn : 1 ≤ n)
    (x : letI := sphereRelCWComplex h
      (cellPullbackPair p (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) n).fst) :
    letI := sphereRelCWComplex h
    TopPair.Hom.fst (spherePreimageSkeletonPairIso h hn).hom
      (TopPair.Hom.fst (cellPullbackPairMap p univ n) x) = x.val.2 :=
  letI := sphereRelCWComplex h
  (spherePreimageSkeletonPairIso_hom_fst_apply ..).trans (coe_cellPullbackPairMap_fst_apply ..)

variable (hp : serreFibrations p) (R : Type u) [Ring R]

include hp

/-- **The relative homology of a fibration over a sphere modulo the fibre over the pole.** For a
Serre fibration `p : E ⟶ Sⁿ`, `n ≥ 1`, with fibre `F` over the pole,
`Hq+n(E, F; R) ≅ Hq(p⁻¹(x₁); R)`, where `x₁` is the centre of the top cell of `Sⁿ`. -/
def sphereFibrationSingularHomologyIso (hn : 1 ≤ n) (q : ℕ) :
    (TopPair.ofSubset (p ⁻¹' {spherePolePoint h})).singularHomology (ModuleCat.of R R) (q + n) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {sphereTopCellCenter h} : Set E)) :=
  letI := sphereRelCWComplex h
  letI := uniqueCellSphereRelCWComplex h hn
  (TopPair.singularHomologyMapIso (ModuleCat.of R R) (spherePreimageSkeletonPairIso h hn)
      (q + n)).symm ≪≫
    preimageSkeletonPairSingularHomologyIsoSigma _ hp R n q ≪≫ coproductUniqueIso _ ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo (Homeomorph.setCongr (by
        rw [map_sphereRelCWComplex_zero h (by omega)])))

/-- **The relative homology of a fibration over a sphere modulo the fibre over the pole vanishes
below the dimension of the sphere.** For a Serre fibration `p : E ⟶ Sⁿ` with fibre `F` over the
pole, `Hₘ(E, F; R) = 0` for `m < n`. -/
theorem isZero_singularHomology_sphereFibration_of_lt {m : ℕ} (hm : m < n) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {spherePolePoint h})).singularHomology
      (ModuleCat.of R R) m) := by
  let _ := sphereRelCWComplex h
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  refine (isZero_singularHomology_preimage_skeletonLT (C := univ) hp R
    (k := ((i + 1 + 1 : ℕ) : ℕ∞)) (by norm_cast; omega) (by omega : m ≤ i)).of_iso ?_
  -- `(i : ℕ∞) + 1` and `((i + 1 : ℕ) : ℕ∞)` are defeq, so the pair is `preimageSkeletonPair p _ n`.
  exact (TopPair.singularHomologyMapIso (ModuleCat.of R R)
    (spherePreimageSkeletonPairIso h (by omega)) m).symm

/-- **`Hq+n(E) ≅ Hq(p⁻¹(x₁))` when the fibre has no homology in degrees `q + n` and
`q + n - 1`.** For a Serre fibration `p : E ⟶ Sⁿ`, `n ≥ 1`, whose fibre `F` over the pole has
vanishing homology in the degrees `q + n` and `m = q + n - 1`, the map `Hq+n(E) ⟶ Hq+n(E, F)` of
the long exact sequence of the pair is an isomorphism, so `Hq+n(E; R) ≅ Hq(p⁻¹(x₁); R)`, where
`x₁` is the centre of the top cell of `Sⁿ`. -/
def singularHomologySphereFibrationIsoOfIsZero (hn : 1 ≤ n) {q m : ℕ} (hm : m + 1 = q + n)
    (hq : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (q + n)).obj
      (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {spherePolePoint h} : Set E))))
    (hm' : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
      (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {spherePolePoint h} : Set E)))) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (q + n)).obj
        (ModuleCat.of R R)).obj E ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {sphereTopCellCenter h} : Set E)) :=
  eqToIso (singularHomologyFunctor_obj_obj_eq_toSSet_homology _ _ E) ≪≫
    @asIso _ _ _ _ ((TopPair.ofSubset (p ⁻¹' {spherePolePoint h})).singularHomologyπ
      (ModuleCat.of R R) (q + n)) (by
        rw [← hm] at hq ⊢
        -- The subspace of `TopPair.ofSubset s` is `TopCat.of s` by definition, and reduced
        -- homology embeds into singular homology, so it vanishes with it.
        exact TopPair.isIso_singularHomologyπ _ _
          (hq.of_iso ((reducedSingularHomologySuccIso _ m).app _))
          (hm'.of_mono ((reducedSingularHomologyι _ m).app _))) ≪≫
    sphereFibrationSingularHomologyIso h hp R hn q

section Contractible

variable [ContractibleSpace E]

/-- **The reduced homology of the fibre of a fibration over a sphere with contractible total
space.** For a Serre fibration `p : E ⟶ Sⁿ` with contractible total space, the fibre `F` over the
pole has no reduced homology below degree `n - 1`: `H~ₖ(F; R) = 0` for `k + 1 < n`. -/
theorem isZero_reducedSingularHomology_sphereFibration_of_lt {k : ℕ} (hk : k + 1 < n) :
    IsZero ((reducedSingularHomologyFunctor (ModuleCat.of R R) k).obj
      (_root_.TopCat.of (p ⁻¹' {spherePolePoint h} : Set E))) :=
  -- The ambient space of the pair `(E, F)` is `E`.
  have : ContractibleSpace (TopPair.ofSubset (p ⁻¹' {spherePolePoint h})).fst := ‹_›
  (isZero_singularHomology_sphereFibration_of_lt h hp R hk).of_iso
    (asIso ((TopPair.ofSubset (p ⁻¹' {spherePolePoint h})).reducedSingularHomologyδ
      (ModuleCat.of R R) k)).symm

end Contractible

end Fibre

end Fibration

section Wang

variable {E : _root_.TopCat.{u}} {p : E ⟶ _root_.TopCat.of (sphere (0 : EuclideanSpace ℝ ι) 1)}
  [ContractibleSpace E]

/-- **The Wang isomorphism of a fibration over a sphere with contractible total space.** For a
Serre fibration `p : E ⟶ Sⁿ⁺¹` with contractible total space, the reduced homology of the fibre
`F` over the pole is the homology of the fibre over the centre of the top cell, shifted by `n`:
`H~q+n(F; R) ≅ Hq(p⁻¹(x₁); R)`. It is the connecting isomorphism `Hq+n+1(E, F) ≅ H~q+n(F)` of the
pair `(E, F)` followed by `TauCeti.TopCat.sphereFibrationSingularHomologyIso`. -/
def reducedSingularHomologySphereFibrationIso (h : Fintype.card ι = n + 1 + 1)
    (hp : serreFibrations p) (R : Type u) [Ring R] (q : ℕ) :
    (reducedSingularHomologyFunctor (ModuleCat.of R R) (q + n)).obj
        (_root_.TopCat.of (p ⁻¹' {spherePolePoint h} : Set E)) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {sphereTopCellCenter h} : Set E)) :=
  -- The ambient space of the pair `(E, F)` is `E`.
  have : ContractibleSpace (TopPair.ofSubset (p ⁻¹' {spherePolePoint h})).fst := ‹_›
  (asIso ((TopPair.ofSubset (p ⁻¹' {spherePolePoint h})).reducedSingularHomologyδ
      (ModuleCat.of R R) (q + n))).symm ≪≫
    sphereFibrationSingularHomologyIso h hp R (by omega) q

end Wang

end TopCat

end TauCeti
