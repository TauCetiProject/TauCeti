/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Wang
public import TauCeti.AlgebraicTopology.Singular.Fibration.Sphere
public import TauCeti.Topology.PathSpace.Moore.Replacement.Equiv

/-!
# Multiplication by the boundary loops of the top cell on the homology of `Ω Sⁿ⁺¹`

Let `Sⁿ⁺¹` be the unit sphere of `EuclideanSpace ℝ ι`, `Fintype.card ι = n + 2`, with its CW
structure of one `0`-cell, the pole `b`, and one `(n + 1)`-cell. Read on the cube `Iⁿ⁺¹`, the
characteristic map `f` of the top cell (`TauCeti.sphereTopCellCube`) sends the boundary of the cube
to the pole (`TauCeti.sphereTopCellCube_of_mem_boundary`). A path from the pole to the centre of
the cell followed by the images of radial segments is a family of Moore paths from `b` to the
points `f d` (`TauCeti.sphereTopCellPaths`), and the boundary of this cube of paths is a cycle `y`
of degree `n` of the Moore loops at `b` (`TauCeti.sphereBoundaryLoopCycle`): the loops swept out by
the boundary of the top cell.

The projection of the pullback of the based path fibration over the cube to the based path space
induces isomorphisms `H_*(f^*P_b Sⁿ⁺¹, f^*P_b Sⁿ⁺¹|_{∂Iⁿ⁺¹}) ≅ H_*(P_b Sⁿ⁺¹, Ω_b Sⁿ⁺¹)`
(`TauCeti.isIso_singularHomologyMap_toPathFromLoopPair_sphere`). It is the cellular computation of
the skeletal filtration of a Serre fibration
(`TauCeti.TopCat.isIso_singularHomologyMap_cellPullbackPairMap`), for the CW structure of the
sphere, whose `n`-skeleton is the pole. So the Wang map of the top cell is bijective
(`TauCeti.bijective_wangMap_sphere`), and by its computation
`TauCeti.wangMap_homologyπ_sphere`, right Pontryagin multiplication by `y` is an
isomorphism `H_q(Ω Sⁿ⁺¹) ≅ H_{q+n}(Ω Sⁿ⁺¹)` of cubical homology with coefficients in any
commutative ring, whenever `q + n ≥ 1`: it is onto
(`TauCeti.exists_homologyπ_eq_mulCycles_sphereBoundaryLoopCycle`) and injective
(`TauCeti.homologyπ_eq_zero_of_mulCycles_sphereBoundaryLoopCycle`).

This is the multiplicative form of the Wang sequence of the path fibration of a sphere, the input
for the computation of the Pontryagin ring of `Ω Sⁿ⁺¹` as a polynomial ring on a class of degree
`n`.

## Main definitions

* `TauCeti.sphereTopCellCube`: the characteristic map of the top cell of `Sⁿ⁺¹`, on the cube.
* `TauCeti.sphereTopCellPaths`: the family of paths from the pole to the points of the top cell.
* `TauCeti.sphereBoundaryLoopCycle`: the cycle of loops swept out by the boundary of the top cell.

## Main results

* `TauCeti.isIso_singularHomologyMap_toPathFromLoopPair_sphere`: the pullback over the top cell
  computes the homology of `(P_b Sⁿ⁺¹, Ω_b Sⁿ⁺¹)`.
* `TauCeti.bijective_wangMap_sphere`: the Wang map of the top cell is bijective.
* `TauCeti.wangMap_homologyπ_sphere`: the Wang map of the top cell is right multiplication by the
  boundary loops, up to sign.
* `TauCeti.exists_homologyπ_eq_mulCycles_sphereBoundaryLoopCycle`,
  `TauCeti.homologyπ_eq_zero_of_mulCycles_sphereBoundaryLoopCycle`: right multiplication by the
  boundary loops is onto and injective on homology.

## References

* R. Bott, H. Samelson, *On the Pontryagin product in spaces of paths*, Comment. Math. Helv. 27
  (1953), 320–337.
* H.-C. Wang, *The homology groups of the fibre bundles over a sphere*, Duke Math. J. 16 (1949),
  33–38.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.C.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Propositions 6.17 and 6.18.
-/

public noncomputable section

open CategoryTheory HomologicalComplex Limits Metric Set Topology Topology.RelCWComplex
open scoped unitInterval

namespace TauCeti

variable {ι : Type} [Fintype ι] {n : ℕ} (h : Fintype.card ι = n + 1 + 1)

/-- The characteristic map of the top cell of the CW structure on the unit sphere `Sⁿ⁺¹`, on the
closed unit ball of `Fin (n + 1) → ℝ`. -/
def sphereTopCellBall :
    C(closedBall (0 : Fin (n + 1) → ℝ) 1, sphere (0 : EuclideanSpace ℝ ι) 1) :=
  letI := TopCat.sphereRelCWComplex h
  letI := TopCat.uniqueCellSphereRelCWComplex h (n := n + 1) (by omega)
  (sigmaCellMap (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) (n + 1)).comp
    ⟨fun v ↦ ⟨default, v⟩, continuous_sigmaMk.comp continuous_id⟩

@[simp]
theorem sphereTopCellBall_apply (v : closedBall (0 : Fin (n + 1) → ℝ) 1) :
    letI := TopCat.sphereRelCWComplex h
    letI := TopCat.uniqueCellSphereRelCWComplex h (n := n + 1) (by omega)
    sphereTopCellBall h v =
      sigmaCellMap (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) (n + 1) ⟨default, v⟩ :=
  (rfl)

/-- The characteristic map of the top cell of the CW structure on the unit sphere `Sⁿ⁺¹`, read on
the cube `Iⁿ⁺¹`. -/
def sphereTopCellCube : C(Fin (n + 1) → I, sphere (0 : EuclideanSpace ℝ ι) 1) :=
  (sphereTopCellBall h).comp (cubeHomeomorphClosedBall (Fin (n + 1)))

@[simp]
theorem sphereTopCellCube_apply (d : Fin (n + 1) → I) :
    sphereTopCellCube h d = sphereTopCellBall h (cubeHomeomorphClosedBall _ d) :=
  (rfl)

/-- The top cell of the sphere is attached to the pole: the characteristic map sends the boundary
of the cube to the pole. -/
theorem sphereTopCellCube_of_mem_boundary {d : Fin (n + 1) → I} (hd : d ∈ Cube.boundary _) :
    sphereTopCellCube h d = spherePolePoint h := by
  let _ := TopCat.sphereRelCWComplex h
  let _ := TopCat.uniqueCellSphereRelCWComplex h (n := n + 1) (by omega)
  have hmem : sphereTopCellCube h d ∈ cellFrontier (C := (univ : Set
      (sphere (0 : EuclideanSpace ℝ ι) 1))) (n + 1) default :=
    ⟨_, mem_sphere_zero_iff_norm.2 ((norm_cubeHomeomorphClosedBall_eq_one_iff _).2 hd),
      (sigmaCellMap_apply (C := (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1))) (n + 1)
        ⟨default, cubeHomeomorphClosedBall (Fin (n + 1)) d⟩).symm⟩
  have := cellFrontier_subset_skeletonLT (C := (univ : Set
      (sphere (0 : EuclideanSpace ℝ ι) 1))) (n + 1) default hmem
  rwa [TopCat.skeletonLT_sphereRelCWComplex h (by omega) le_rfl] at this

/-- A Moore path from the pole to the centre of the top cell of `Sⁿ⁺¹`. -/
def sphereTopCellCenterPath :
    MoorePathBetween (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)
      (sphereTopCellBall h ⟨0, mem_closedBall_self zero_le_one⟩) :=
  have : PathConnectedSpace (sphere (0 : EuclideanSpace ℝ ι) 1) :=
    isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_sphere (by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace, h]; norm_cast; omega) 0 zero_le_one)
  let p := PathConnectedSpace.somePath (spherePolePoint h)
    (sphereTopCellBall h ⟨0, mem_closedBall_self zero_le_one⟩)
  ⟨p.toMoorePath, Path.source_toMoorePath p, Path.target_toMoorePath p⟩

/-- The family of Moore paths from the pole of `Sⁿ⁺¹` to the points of its top cell: a fixed path
to the centre of the cell followed by the image of a radial segment, read on the cube. -/
def sphereTopCellPaths : C(Fin (n + 1) → I, MoorePath (sphere (0 : EuclideanSpace ℝ ι) 1)) :=
  (MoorePathPullback.radialPaths ((convex_closedBall 0 1).starConvex
    (mem_closedBall_self zero_le_one)) (mem_closedBall_self zero_le_one) (sphereTopCellBall h)
      (sphereTopCellCenterPath h)).comp (cubeHomeomorphClosedBall (Fin (n + 1)))

theorem sphereTopCellPaths_apply (d : Fin (n + 1) → I) :
    sphereTopCellPaths h d = MoorePathPullback.radialPaths ((convex_closedBall 0 1).starConvex
      (mem_closedBall_self zero_le_one)) (mem_closedBall_self zero_le_one) (sphereTopCellBall h)
        (sphereTopCellCenterPath h) (cubeHomeomorphClosedBall _ d) :=
  (rfl)

@[simp]
theorem source_sphereTopCellPaths (d : Fin (n + 1) → I) :
    (sphereTopCellPaths h d).source = spherePolePoint h :=
  MoorePathPullback.source_radialPaths _ _ _ _ _

@[simp]
theorem target_sphereTopCellPaths (d : Fin (n + 1) → I) :
    (sphereTopCellPaths h d).target = sphereTopCellCube h d :=
  MoorePathPullback.target_radialPaths _ _ _ _ _

/-- The pullback of the based path fibration over the cube is the pullback over the disk of the
top cell, through the homeomorphism of the cube with the disk. -/
private def topCellPullbackHomeomorph :
    letI := TopCat.sphereRelCWComplex h
    letI := TopCat.uniqueCellSphereRelCWComplex h (n := n + 1) (by omega)
    MoorePathPullback (sphereTopCellCube h) (spherePolePoint h) ≃ₜ
      {x : (Σ _ : cell (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) (n + 1),
          closedBall (0 : Fin (n + 1) → ℝ) 1) ×
        MoorePathFrom (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h) //
        sigmaCellMap (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) (n + 1) x.1 =
          MoorePathFrom.endpoint _ _ x.2} :=
  letI := TopCat.sphereRelCWComplex h
  letI := TopCat.uniqueCellSphereRelCWComplex h (n := n + 1) (by omega)
  -- the only cell of dimension `n + 1` is `default`
  have hcell (v : Σ _ : cell (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) (n + 1),
      closedBall (0 : Fin (n + 1) → ℝ) 1) : v = ⟨default, v.2⟩ :=
    Sigma.ext (Subsingleton.elim _ _) HEq.rfl
  { toFun x := ⟨(⟨default, cubeHomeomorphClosedBall _ x.val.1⟩, x.val.2),
      x.property.symm.trans (MoorePathFrom.endpoint_apply x.val.2).symm⟩
    invFun y := ⟨((cubeHomeomorphClosedBall _).symm y.val.1.2, y.val.2), by
      have := y.property
      rw [hcell y.val.1] at this
      refine ((MoorePathFrom.endpoint_apply y.val.2).symm.trans this.symm).trans ?_
      exact congrArg (sphereTopCellBall h)
        ((cubeHomeomorphClosedBall _).apply_symm_apply y.val.1.2).symm⟩
    left_inv x := Subtype.ext (Prod.ext ((cubeHomeomorphClosedBall _).symm_apply_apply _) rfl)
    right_inv y := Subtype.ext (Prod.ext ((congrArg (Sigma.mk default)
      ((cubeHomeomorphClosedBall (Fin (n + 1))).apply_symm_apply y.val.1.2)).trans
        (hcell y.val.1).symm) rfl)
    continuous_toFun := by
      refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
      · exact continuous_sigmaMk.comp ((cubeHomeomorphClosedBall _).continuous.comp
          (continuous_fst.comp continuous_subtypeVal))
      · exact continuous_snd.comp continuous_subtypeVal
    continuous_invFun := by
      refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
      · exact (cubeHomeomorphClosedBall _).symm.continuous.comp
          ((continuous_sigma fun _ ↦ continuous_id).comp
            (continuous_fst.comp continuous_subtypeVal))
      · exact continuous_snd.comp continuous_subtypeVal }

/-- The pair of the pullback over the cube relative to the boundary of the cube is the pair of the
pullback over the disk of the top cell relative to the boundary sphere. -/
private def topCellPairHom :
    letI := TopCat.sphereRelCWComplex h
    letI := TopCat.uniqueCellSphereRelCWComplex h (n := n + 1) (by omega)
    TopPair.ofSubset (X := TopCat.of (MoorePathPullback (sphereTopCellCube h) (spherePolePoint h)))
        (MoorePathPullback.proj (sphereTopCellCube h) (spherePolePoint h) ⁻¹'
          Cube.boundary (Fin (n + 1))) ⟶
      TopCat.cellPullbackPair (TopCat.ofHom (MoorePathFrom.endpoint _ (spherePolePoint h)))
        (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) (n + 1) :=
  TopPair.ofHom (TopCat.ofHom (topCellPullbackHomeomorph h)) (TopCat.ofHom
    ⟨fun x ↦ ⟨topCellPullbackHomeomorph h x.val, (norm_cubeHomeomorphClosedBall_eq_one_iff _).2
      ((MoorePathPullback.point_def x.val) ▸ MoorePathPullback.point_mem_boundary x)⟩,
    ((topCellPullbackHomeomorph h).continuous.comp continuous_subtypeVal).subtype_mk _⟩) rfl

private theorem isIso_topCellPairHom : IsIso (topCellPairHom h) := by
  let _ := TopCat.sphereRelCWComplex h
  let _ := TopCat.uniqueCellSphereRelCWComplex h (n := n + 1) (by omega)
  have : IsIso (TopPair.Hom.fst (topCellPairHom h)) :=
    (TopCat.isoOfHomeo (X := TopCat.of (MoorePathPullback (sphereTopCellCube h)
      (spherePolePoint h))) (Y := TopCat.cellPullback (TopCat.ofHom (MoorePathFrom.endpoint _
        (spherePolePoint h))) (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) (n + 1))
      (topCellPullbackHomeomorph h)).isIso_hom
  refine TopPair.isIso_of_isIso_fst_of_surjective_snd _ fun y ↦
    ⟨⟨(topCellPullbackHomeomorph h).symm y.val, ?_⟩,
      Subtype.ext ((topCellPullbackHomeomorph h).apply_symm_apply y.val)⟩
  rw [Set.mem_preimage, MoorePathPullback.proj_apply, MoorePathPullback.point_def,
    ← norm_cubeHomeomorphClosedBall_eq_one_iff]
  exact (congrArg (fun v : closedBall (0 : Fin (n + 1) → ℝ) 1 ↦ ‖(v : Fin (n + 1) → ℝ)‖)
    ((cubeHomeomorphClosedBall (Fin (n + 1))).apply_symm_apply y.val.val.1.2)).trans y.property

private theorem skeletonLT_eq_pole :
    letI := TopCat.sphereRelCWComplex h
    (skeletonLT (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) ((n + 1 : ℕ) : ℕ∞) :
      Set (sphere (0 : EuclideanSpace ℝ ι) 1)) = {spherePolePoint h} :=
  TopCat.skeletonLT_sphereRelCWComplex h (by omega) le_rfl

/-- The pair of consecutive stages of the skeletal filtration of the based path fibration of the
sphere is the pair `(P_b Sⁿ⁺¹, Ω_b Sⁿ⁺¹)`. -/
private def skeletonPairHom :
    letI := TopCat.sphereRelCWComplex h
    TopCat.preimageSkeletonPair (TopCat.ofHom (MoorePathFrom.endpoint _ (spherePolePoint h)))
        (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) (n + 1) ⟶
      pathFromLoopPair (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h) :=
  letI := TopCat.sphereRelCWComplex h
  TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩)
    (TopCat.ofHom ⟨fun x ↦ ⟨x.val.toMoorePath, x.val.source,
      (MoorePathFrom.endpoint_apply x.val).symm.trans ((Set.ext_iff.1 (skeletonLT_eq_pole h) _).1
        x.property)⟩,
      continuous_induced_rng.2 (MoorePathFrom.continuous_toMoorePath.comp
        continuous_subtypeVal)⟩)
    (by
      ext x : 1
      exact MoorePathFrom.ext (MooreLoopSpace.toMoorePath_toMoorePathFrom _))

private theorem isIso_skeletonPairHom : IsIso (skeletonPairHom h) := by
  let _ := TopCat.sphereRelCWComplex h
  have : IsIso (TopPair.Hom.fst (skeletonPairHom h)) := by
    refine TopCat.isIso_of_bijective_of_isOpenMap _ ⟨Subtype.val_injective, fun γ ↦ ?_⟩
      (IsOpen.isOpenEmbedding_subtypeVal ?_).isOpenMap
    · refine ⟨⟨γ, ?_⟩, rfl⟩
      rw [Set.mem_preimage, TopCat.skeletonLT_succ_sphereRelCWComplex h]
      exact mem_univ _
    · rw [TopCat.skeletonLT_succ_sphereRelCWComplex h, Set.preimage_univ]
      exact isOpen_univ
  refine TopPair.isIso_of_isIso_fst_of_surjective_snd _ fun ω ↦
    ⟨⟨MooreLoopSpace.toMoorePathFrom ω, ?_⟩,
      MooreLoopSpace.ext (MooreLoopSpace.toMoorePath_toMoorePathFrom ω)⟩
  rw [Set.mem_preimage, skeletonLT_eq_pole h]
  exact MooreLoopSpace.endpoint_toMoorePathFrom ω

/-- The projection of the pullback over the top cell factors through the pullback over the disk of
the top cell and the skeletal pair of the based path fibration. -/
private theorem toPathFromLoopPair_eq :
    letI := TopCat.sphereRelCWComplex h
    letI := TopCat.uniqueCellSphereRelCWComplex h (n := n + 1) (by omega)
    MoorePathPullback.toPathFromLoopPair (fun _ hd ↦ sphereTopCellCube_of_mem_boundary h hd) =
      topCellPairHom h ≫ TopCat.cellPullbackPairMap (TopCat.ofHom (MoorePathFrom.endpoint _
        (spherePolePoint h))) (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) (n + 1) ≫
          skeletonPairHom h := by
  let _ := TopCat.sphereRelCWComplex h
  let _ := TopCat.uniqueCellSphereRelCWComplex h (n := n + 1) (by omega)
  refine TopPair.hom_ext_of_fst _ ?_
  ext ⟨⟨d, γ⟩, hx⟩ : 1
  rw [MoorePathPullback.fst_toPathFromLoopPair_apply]
  refine MoorePathFrom.ext ((MoorePathPullback.toMoorePathFrom_toMoorePath _).trans ?_)
  rw [MoorePathPullback.path_mk, TopPair.Hom.fst_comp, TopPair.Hom.fst_comp]
  -- on the ambient spaces, `topCellPairHom` is a homeomorphism keeping the path, the projection of
  -- the pullback takes the path and `skeletonPairHom` is the inclusion of a subset
  exact congrArg MoorePathFrom.toMoorePath
    (TopCat.coe_cellPullbackPairMap_fst_apply (p := TopCat.ofHom (MoorePathFrom.endpoint _
      (spherePolePoint h))) (C := (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1))) (n + 1)
        (topCellPullbackHomeomorph h ⟨(d, γ), hx⟩)).symm

/-- **The projection of the pullback over the top cell is a relative homology isomorphism**: the
map of pairs `(f^*P_b Sⁿ⁺¹, f^*P_b Sⁿ⁺¹|_{∂Iⁿ⁺¹}) ⟶ (P_b Sⁿ⁺¹, Ω_b Sⁿ⁺¹)`, for the characteristic
map `f` of the top cell and the pole `b`, induces isomorphisms on relative singular homology. -/
theorem isIso_singularHomologyMap_toPathFromLoopPair_sphere (k : Type) [Ring k] (i : ℕ) :
    IsIso (TopPair.singularHomologyMap (MoorePathPullback.toPathFromLoopPair
      (fun _ hd ↦ sphereTopCellCube_of_mem_boundary h hd)) (ModuleCat.of k k) i) := by
  let _ := TopCat.sphereRelCWComplex h
  let _ := TopCat.uniqueCellSphereRelCWComplex h (n := n + 1) (by omega)
  have := TopCat.isIso_singularHomologyMap_cellPullbackPairMap
    (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1))
    ((MoorePathFrom.isHurewiczFibration_endpoint.{0} (spherePolePoint h)).mem_serreFibrations
      (p := TopCat.ofHom (MoorePathFrom.endpoint _ (spherePolePoint h)))) k (n + 1) i
  have := isIso_topCellPairHom h
  have := isIso_skeletonPairHom h
  have : IsIso (TopPair.singularHomologyMap (topCellPairHom h) (ModuleCat.of k k) i) :=
    (TopPair.singularHomologyMapIso (ModuleCat.of k k) (asIso (topCellPairHom h)) i).isIso_hom
  have : IsIso (TopPair.singularHomologyMap (skeletonPairHom h) (ModuleCat.of k k) i) :=
    (TopPair.singularHomologyMapIso (ModuleCat.of k k) (asIso (skeletonPairHom h)) i).isIso_hom
  rw [toPathFromLoopPair_eq, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_comp]
  infer_instance

/-- **The Wang map of the top cell of `Sⁿ⁺¹` is bijective** in every degree `q` with
`q + n ≥ 1`: right Pontryagin multiplication by the cycle of loops swept out by the boundary of the
top cell is an isomorphism `H_q(Ω Sⁿ⁺¹) ≅ H_{q+n}(Ω Sⁿ⁺¹)` of cubical homology. -/
theorem bijective_wangMap_sphere (k : Type) [CommRing k] (q : ℕ) (hq : q + n ≠ 0) :
    Function.Bijective (MoorePathPullback.wangMap
      (fun _ hd ↦ sphereTopCellCube_of_mem_boundary h hd) (sphereTopCellPaths h)
      (source_sphereTopCellPaths h) (target_sphereTopCellPaths h) k q) := by
  have := isIso_singularHomologyMap_toPathFromLoopPair_sphere h k (q + (n + 1))
  exact MoorePathPullback.bijective_wangMap _ _ _ _ k q
    (TopPair.isIso_homologyMap_cubicalChainComplexMap_of_isIso _ _) hq

variable (k : Type) [CommRing k]

/-- The cycle of Moore loops at the pole of `Sⁿ⁺¹` swept out by the boundary of its top cell: the
boundary of the cube of paths `TauCeti.sphereTopCellPaths`. -/
def sphereBoundaryLoopCycle :
    ((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)))).cycles
        n :=
  MoorePathPullback.boundaryLoopCycle (fun _ hd ↦ sphereTopCellCube_of_mem_boundary h hd)
    (sphereTopCellPaths h) (source_sphereTopCellPaths h) (target_sphereTopCellPaths h) k

/-- The cycle of boundary loops of the top cell is the cycle of boundary loops of the cube of
paths `TauCeti.sphereTopCellPaths`. -/
theorem sphereBoundaryLoopCycle_def :
    sphereBoundaryLoopCycle h k =
      MoorePathPullback.boundaryLoopCycle (fun _ hd ↦ sphereTopCellCube_of_mem_boundary h hd)
        (sphereTopCellPaths h) (source_sphereTopCellPaths h) (target_sphereTopCellPaths h) k :=
  (rfl)

/-- **The Wang map of the top cell of `Sⁿ⁺¹` is right multiplication by its boundary loops**, up to
the sign `(-1) ^ q`: it sends the class of a cycle `z` of degree `q` to `(-1) ^ q [z · y]`, where
`y` is `TauCeti.sphereBoundaryLoopCycle`. -/
theorem wangMap_homologyπ_sphere (q : ℕ)
    (z : ((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)))).cycles
        q) :
    MoorePathPullback.wangMap (fun _ hd ↦ sphereTopCellCube_of_mem_boundary h hd)
        (sphereTopCellPaths h) (source_sphereTopCellPaths h) (target_sphereTopCellPaths h) k q
        ((((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace
          (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)))).homologyπ q).hom z) =
      (-1 : k) ^ q • (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace
        (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)))).homologyπ (q + n)).hom
        (NormalizedCubicalChain.mulCycles k z (sphereBoundaryLoopCycle h k)) := by
  rw [MoorePathPullback.wangMap_homologyπ, sphereBoundaryLoopCycle_def]

/-- **Right multiplication by the boundary loops of the top cell is onto** the homology of
`Ω Sⁿ⁺¹` in positive degrees: every cycle `w` of degree `q + n ≥ 1` is homologous to `z · y` for a
cycle `z` of degree `q`, where `y` is `TauCeti.sphereBoundaryLoopCycle`. -/
theorem exists_homologyπ_eq_mulCycles_sphereBoundaryLoopCycle (q : ℕ) (hq : q + n ≠ 0)
    (w : ((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)))).cycles
        (q + n)) :
    ∃ z, (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace
        (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)))).homologyπ (q + n)).hom w =
      (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace
        (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)))).homologyπ (q + n)).hom
        (NormalizedCubicalChain.mulCycles k z (sphereBoundaryLoopCycle h k)) := by
  obtain ⟨a, ha⟩ := (bijective_wangMap_sphere h k q hq).2
    ((-1 : k) ^ q • (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace
      (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)))).homologyπ (q + n)).hom w)
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 (inferInstance : Epi
    (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace
      (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)))).homologyπ q)) a
  refine ⟨z, ?_⟩
  rw [wangMap_homologyπ_sphere] at ha
  have hsq {M : Type} [AddCommGroup M] [Module k M] (x : M) :
      (-1 : k) ^ q • ((-1 : k) ^ q • x) = x := by
    rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  rw [← hsq ((((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace
    (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)))).homologyπ (q + n)).hom w), ← ha,
    hsq]

/-- **Right multiplication by the boundary loops of the top cell is injective** on the homology of
`Ω Sⁿ⁺¹` in degrees `q` with `q + n ≥ 1`: if `z · y` is a boundary, so is `z`, where `y` is
`TauCeti.sphereBoundaryLoopCycle`. -/
theorem homologyπ_eq_zero_of_mulCycles_sphereBoundaryLoopCycle (q : ℕ) (hq : q + n ≠ 0)
    (z : ((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)))).cycles
        q)
    (hz : (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace
        (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)))).homologyπ (q + n)).hom
        (NormalizedCubicalChain.mulCycles k z (sphereBoundaryLoopCycle h k)) = 0) :
    (((normalizedCubicalChainComplex k).obj (TopCat.of (MooreLoopSpace
      (sphere (0 : EuclideanSpace ℝ ι) 1) (spherePolePoint h)))).homologyπ q).hom z = 0 := by
  refine (injective_iff_map_eq_zero _).1 (bijective_wangMap_sphere h k q hq).1 _ ?_
  rw [wangMap_homologyπ_sphere]
  exact (congrArg ((-1 : k) ^ q • ·) hz).trans (smul_zero _)

end TauCeti
