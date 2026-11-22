/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Cell
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Sphere.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Excision
public import TauCeti.AlgebraicTopology.Singular.Fibration.Sphere
public import TauCeti.Topology.PathSpace.Moore.Replacement.Equiv

/-!
# Multiplication by the attaching class on the homology of the loops of a sphere

Let `Sⁿ`, `n ≥ 2`, be the unit sphere of a Euclidean space, with its CW structure of one `0`-cell,
the pole `b`, and one `n`-cell (`TauCeti.TopCat.sphereRelCWComplex`). Its characteristic map, read
on the cube `Iⁿ` (`TauCeti.sphereCubeMap`), collapses the boundary of the cube to `b`. Following
the image of the straight segment from the corner `0` of the cube to `d` gives a continuous family
of Moore paths `τ d` from `b` to the image of `d` (`TauCeti.sphereCubePaths`), that is a singular
`n`-cube `σ` of the based path space `P_b Sⁿ` (`TauCeti.spherePathCube`). Its faces are paths
ending at `b`, that is Moore loops, and the signed sum of its faces is an `(n - 1)`-cycle `x` of
the Moore loops at `b`, the **attaching cycle** of the top cell (`TauCeti.sphereAttachingCycle`):
its image in `P_b Sⁿ` is the boundary of `σ` (`TauCeti.boundary_ofCube_spherePathCube`).

The main result is that the right Pontryagin product with `x` is an isomorphism

`H_q(Ω_b Sⁿ; k) ≃ₗ[k] H_{q+n-1}(Ω_b Sⁿ; k)`, `[z] ↦ [z · x]`,

in every degree `q`, on the normalized cubical homology of the Moore loops with coefficients in a
commutative ring `k` (`TauCeti.sphereLoopHomologyMulRightEquiv` and
`TauCeti.sphereLoopHomologyMulRightEquiv_homologyπ`). The product is the strict concatenation of
Moore loops, `TauCeti.NormalizedCubicalChain.mul`. This is the inductive step of the theorem of
Bott and Samelson that the Pontryagin ring `H_*(Ω_b Sⁿ; k)` is the polynomial ring on the class of
`x`: starting from the class of the constant loop in `H_0`, the product with `x` reaches every
degree divisible by `n - 1` and kills no class, so for instance the class of `x · x` has the order
of the class of the constant loop.

## The argument

This is Brown's computation of a semi-free model of the chains on `P_b Sⁿ` over the chains on
`Ω_b Sⁿ`, for a CW complex with a single cell of positive dimension. The isomorphism is the
composite of three isomorphisms.

* **The cell.** Pull the based path fibration `P_b Sⁿ → Sⁿ` back along the cube map. Acting on the
  section cube `d ↦ (d, τ d)` identifies `H_q(Ω_b Sⁿ)` with the homology of the pullback relative to
  its part over the boundary of the cube, in degree `q + n`
  (`TauCeti.MoorePathPullback.cubicalHomologyCubeBoundaryEquiv`).
* **Excision.** The projection of the pullback to `P_b Sⁿ` is a map of pairs onto
  `(P_b Sⁿ, Ω_b Sⁿ)`, the pair of the two stages of the skeletal filtration of the based path space,
  and it induces isomorphisms on relative homology
  (`TauCeti.TopCat.isIso_singularHomologyMap_cellPullbackPairMap`).
* **The contraction.** The based path space is contractible, so the connecting morphism of the pair
  `(P_b Sⁿ, Ω_b Sⁿ)` is an isomorphism in positive degrees
  (`TopPair.isIso_cubicalHomologyδ_of_contractibleSpace`).

On a `q`-cycle `z` of the loops the composite is computed on representatives: the relative cycle
`z · σ` has boundary `(-1) ^ q • z · ∂σ` by the Leibniz rule
(`TauCeti.NormalizedCubicalChain.boundary_leftAct_of_boundary_eq_zero`), and `∂σ` is the image of
`x`, so the connecting morphism sends the class of `z · σ` to `(-1) ^ q` times the class of the
product `z · x`. The sign is absorbed in `TauCeti.sphereLoopHomologyMulRightEquiv`.

## Main definitions

* `TauCeti.sphereBallMap h`: the characteristic map of the top cell of `Sⁿ`, on the closed unit
  ball of the sup norm.
* `TauCeti.sphereCubeMap h`: the characteristic map of the top cell of `Sⁿ`, read on the cube.
* `TauCeti.sphereCubePaths h`: the Moore paths from the pole along the images of straight segments.
* `TauCeti.spherePathCube h`: the singular `n`-cube `d ↦ τ d` of `P_b Sⁿ`.
* `TauCeti.sphereAttachingCycle h k`: the attaching cycle `x`, the signed sum of the faces of the
  path cube, read in the Moore loops.
* `TauCeti.sphereLoopHomologyMulRightEquiv h k q`: the isomorphism
  `H_q(Ω_b Sⁿ; k) ≃ₗ[k] H_{q+n-1}(Ω_b Sⁿ; k)`.

## Main results

* `TauCeti.boundary_ofCube_spherePathCube`: the boundary of the path cube is the image of the
  attaching cycle.
* `TauCeti.sphereLoopHomologyMulRightEquiv_homologyπ`: the isomorphism sends the class of a cycle
  `z` to the class of the product `z · x`.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* R. Bott and H. Samelson, *On the Pontryagin product in spaces of paths*, Comment. Math. Helv. 27
  (1953), 320–337.
* H.-C. Wang, *The homology groups of the fibre bundles over a sphere*, Duke Math. J. 16 (1949),
  33–38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3–4 and §7.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Proposition 6.18).
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex HomologicalComplex
open scoped unitInterval

namespace TauCeti

/-! ### The top cell of the sphere, read on the cube -/

variable {ι : Type} [Fintype ι] {m : ℕ} (h : Fintype.card ι = m + 3)

local notation "Sph" => sphere (0 : EuclideanSpace ℝ ι) 1

/-- The characteristic map of the top cell of the sphere, on the closed unit ball of the sup
norm. -/
def sphereBallMap : C(closedBall (0 : Fin (m + 2) → ℝ) 1, Sph) :=
  letI := TopCat.sphereRelCWComplex h
  letI := TopCat.uniqueCellSphereRelCWComplex h (n := m + 2) (by omega)
  (sigmaCellMap (univ : Set Sph) (m + 2)).comp
    ⟨Sigma.mk (β := fun _ ↦ closedBall (0 : Fin (m + 2) → ℝ) 1) default, continuous_sigmaMk⟩

/-- The map on the ball is the characteristic map of the single top cell. -/
theorem sphereBallMap_apply (v : closedBall (0 : Fin (m + 2) → ℝ) 1) :
    letI := TopCat.sphereRelCWComplex h
    letI := TopCat.uniqueCellSphereRelCWComplex h (n := m + 2) (by omega)
    sphereBallMap h v = sigmaCellMap (univ : Set Sph) (m + 2) ⟨default, v⟩ :=
  (rfl)

/-- The characteristic map of the top cell sends the boundary sphere of the ball to the pole. -/
theorem sphereBallMap_of_norm_eq_one {v : closedBall (0 : Fin (m + 2) → ℝ) 1}
    (hv : ‖(v : Fin (m + 2) → ℝ)‖ = 1) : sphereBallMap h v = spherePolePoint h := by
  let _ := TopCat.sphereRelCWComplex h
  let _ := TopCat.uniqueCellSphereRelCWComplex h (n := m + 2) (by omega)
  have := cellFrontier_subset_skeletonLT (C := (univ : Set Sph)) (m + 2) default
    ⟨_, mem_sphere_zero_iff_norm.2 hv, rfl⟩
  rw [TopCat.skeletonLT_sphereRelCWComplex h (by omega) le_rfl] at this
  simpa [sphereBallMap] using this

/-- The corner `0` of the cube, as a point of the closed unit ball of the sup norm. -/
private def ballCorner : closedBall (0 : Fin (m + 2) → ℝ) 1 :=
  cubeHomeomorphClosedBall (Fin (m + 2)) 0

private theorem norm_ballCorner :
    ‖((ballCorner : closedBall (0 : Fin (m + 2) → ℝ) 1) : Fin (m + 2) → ℝ)‖ = 1 :=
  (norm_cubeHomeomorphClosedBall_eq_one_iff _).2 ⟨0, Or.inl rfl⟩

/-- The **characteristic map of the top cell** of the sphere `Sⁿ`, `n = m + 2`, read on the cube
`Iⁿ` through the affine homeomorphism `TauCeti.cubeHomeomorphClosedBall` of the cube onto the
closed unit ball of the sup norm. It collapses the boundary of the cube to the pole
(`TauCeti.sphereCubeMap_of_mem_boundary`). -/
def sphereCubeMap : C(Fin (m + 2) → I, Sph) :=
  (sphereBallMap h).comp (cubeHomeomorphClosedBall (Fin (m + 2)))

/-- The cube map is the characteristic map of the single top cell, read through
`TauCeti.cubeHomeomorphClosedBall`. -/
theorem sphereCubeMap_apply (d : Fin (m + 2) → I) :
    letI := TopCat.sphereRelCWComplex h
    letI := TopCat.uniqueCellSphereRelCWComplex h (n := m + 2) (by omega)
    sphereCubeMap h d = sigmaCellMap (univ : Set Sph) (m + 2)
      ⟨default, cubeHomeomorphClosedBall (Fin (m + 2)) d⟩ :=
  (rfl)

/-- The cube map is the map on the ball, read through `TauCeti.cubeHomeomorphClosedBall`. -/
theorem sphereCubeMap_eq_sphereBallMap (d : Fin (m + 2) → I) :
    sphereCubeMap h d = sphereBallMap h (cubeHomeomorphClosedBall (Fin (m + 2)) d) :=
  (rfl)

/-- The cube map collapses the boundary of the cube to the pole. -/
theorem sphereCubeMap_of_mem_boundary {d : Fin (m + 2) → I}
    (hd : d ∈ Cube.boundary (Fin (m + 2))) : sphereCubeMap h d = spherePolePoint h :=
  sphereBallMap_of_norm_eq_one h ((norm_cubeHomeomorphClosedBall_eq_one_iff d).2 hd)

/-- The **Moore paths from the pole over the top cell**: for `d` in the cube, the image under
`TauCeti.sphereCubeMap` of the straight segment from the corner `0` of the cube to `d`, a path from
the pole to `sphereCubeMap h d`, continuous in `d`. -/
def sphereCubePaths : C(Fin (m + 2) → I, MoorePath Sph) :=
  (MoorePathPullback.radialPaths
    ((convex_closedBall (0 : Fin (m + 2) → ℝ) 1).starConvex ballCorner.property)
    ballCorner.property (sphereBallMap h)
    ⟨MoorePath.refl _, MoorePath.source_refl _,
      (MoorePath.target_refl _).trans (sphereBallMap_of_norm_eq_one h norm_ballCorner).symm⟩).comp
    (cubeHomeomorphClosedBall (Fin (m + 2)))

/-- The Moore paths from the pole are the radial paths of `TauCeti.sphereBallMap` from the image
of the corner `0` of the cube, starting with the constant path at the pole, read on the cube. -/
theorem sphereCubePaths_apply (d : Fin (m + 2) → I) :
    sphereCubePaths h d = MoorePathPullback.radialPaths
      ((convex_closedBall (0 : Fin (m + 2) → ℝ) 1).starConvex
        (cubeHomeomorphClosedBall (Fin (m + 2)) 0).property)
      (cubeHomeomorphClosedBall (Fin (m + 2)) 0).property (sphereBallMap h)
      ⟨MoorePath.refl _, MoorePath.source_refl _, (MoorePath.target_refl _).trans
        (sphereBallMap_of_norm_eq_one h
          ((norm_cubeHomeomorphClosedBall_eq_one_iff 0).2 ⟨0, Or.inl rfl⟩)).symm⟩
      (cubeHomeomorphClosedBall (Fin (m + 2)) d) :=
  (rfl)

@[simp]
theorem source_sphereCubePaths (d : Fin (m + 2) → I) :
    (sphereCubePaths h d).source = spherePolePoint h := by
  simp [sphereCubePaths]

@[simp]
theorem target_sphereCubePaths (d : Fin (m + 2) → I) :
    (sphereCubePaths h d).target = sphereCubeMap h d := by
  simp [sphereCubePaths, sphereCubeMap]

/-! ### The pullback over the top cell and excision -/

/-- The pullback of the based path fibration along the cube map, relative to its part over the
boundary of the cube. -/
private abbrev sphereCubePair : TopPair :=
  TopPair.ofSubset (X := TopCat.of (MoorePathPullback (sphereCubeMap h) (spherePolePoint h)))
    (MoorePathPullback.proj (sphereCubeMap h) (spherePolePoint h) ⁻¹' Cube.boundary (Fin (m + 2)))

/-- The projection `(d, γ) ↦ γ` of the pullback to the based path space, as a map of pairs to the
pair of the based paths and the loops. -/
private def sphereCubePairToLoopPair :
    sphereCubePair h ⟶ MoorePathFrom.loopPair Sph (spherePolePoint h) :=
  TopPair.ofHom (TopCat.ofHom MoorePathPullback.toMoorePathFrom)
    (TopCat.ofHom ⟨fun x ↦ ⟨x.val.path, x.val.source_path,
      x.val.target_path.trans (sphereCubeMap_of_mem_boundary h
        (MoorePathPullback.proj_apply x.val ▸ x.property))⟩,
      MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 (by fun_prop)⟩)
    (by
      ext x
      -- Both composites send `x` to its path, read in the based path space.
      exact MoorePathFrom.ext ((MooreLoopSpace.toMoorePath_toMoorePathFrom _).trans
        (MoorePathPullback.toMoorePathFrom_toMoorePath x.val).symm))

/-- The pullback along the cube map is homeomorphic to the pullback along the characteristic map of
the top cell, the disjoint union over its single cell of the closed unit ball. -/
private def sphereCubePullbackHomeomorph :
    letI := TopCat.sphereRelCWComplex h
    MoorePathPullback (sphereCubeMap h) (spherePolePoint h) ≃ₜ
      TopCat.cellPullback (TopCat.ofHom (MoorePathFrom.endpoint Sph (spherePolePoint h)))
        (univ : Set Sph) (m + 2) :=
  letI := TopCat.sphereRelCWComplex h
  letI := TopCat.uniqueCellSphereRelCWComplex h (n := m + 2) (by omega)
  let ιc : C(closedBall (0 : Fin (m + 2) → ℝ) 1,
      Σ _ : cell (univ : Set Sph) (m + 2), closedBall (0 : Fin (m + 2) → ℝ) 1) :=
    ⟨Sigma.mk (β := fun _ ↦ closedBall (0 : Fin (m + 2) → ℝ) 1) default, continuous_sigmaMk⟩
  have hinv (y : TopCat.cellPullback (TopCat.ofHom (MoorePathFrom.endpoint Sph (spherePolePoint h)))
      (univ : Set Sph) (m + 2)) :
      y.val.2.toMoorePath.target =
        sphereCubeMap h ((cubeHomeomorphClosedBall _).symm y.val.1.2) := by
    obtain ⟨⟨⟨i, v⟩, γ⟩, hy⟩ := y
    obtain rfl := Subsingleton.elim i default
    simpa [sphereCubeMap_apply, MoorePathFrom.endpoint_apply] using hy.symm
  have hto (x : MoorePathPullback (sphereCubeMap h) (spherePolePoint h)) :
      sigmaCellMap (univ : Set Sph) (m + 2) (ιc (cubeHomeomorphClosedBall _ x.val.1)) =
        TopCat.ofHom (MoorePathFrom.endpoint Sph (spherePolePoint h)) x.val.2 := by
    simpa [sphereCubeMap_apply, MoorePathFrom.endpoint_apply, ιc] using x.property.symm
  { toFun x := ⟨(ιc (cubeHomeomorphClosedBall _ x.val.1), x.val.2), hto x⟩
    invFun y := ⟨((cubeHomeomorphClosedBall _).symm y.val.1.2, y.val.2), hinv y⟩
    left_inv x := by
      obtain ⟨⟨d, γ⟩, hx⟩ := x
      simp [ιc]
    right_inv y := by
      obtain ⟨⟨⟨i, v⟩, γ⟩, hy⟩ := y
      obtain rfl := Subsingleton.elim i default
      simp [ιc]
    continuous_toFun := ((ιc.continuous.comp ((cubeHomeomorphClosedBall _).continuous.comp
        (continuous_fst.comp continuous_subtypeVal))).prodMk
          (continuous_snd.comp continuous_subtypeVal)).subtype_mk hto
    continuous_invFun := (((cubeHomeomorphClosedBall _).symm.continuous.comp
        ((continuous_sigma fun _ ↦ continuous_id).comp
          (continuous_fst.comp continuous_subtypeVal))).prodMk
            (continuous_snd.comp continuous_subtypeVal)).subtype_mk hinv }

/-- **Excision over the top cell**: the projection of the pullback over the cube, relative to its
part over the boundary, to the pair of the based paths and the loops induces isomorphisms on
relative cubical homology. -/
private theorem isIso_homologyMap_sphereCubePairToLoopPair (k : Type) [CommRing k] (n : ℕ) :
    IsIso (homologyMap (TopPair.cubicalChainComplexMap k (sphereCubePairToLoopPair h)) n) := by
  let _ := TopCat.sphereRelCWComplex h
  let b := spherePolePoint h
  let p : TopCat.of (MoorePathFrom Sph b) ⟶ TopCat.of Sph :=
    TopCat.ofHom (MoorePathFrom.endpoint Sph b)
  -- The pullback along the cube map is the pullback along the characteristic map.
  let φ : sphereCubePair h ≅ TopCat.cellPullbackPair p univ (m + 2) :=
    TopPair.ofSubsetIso (sphereCubePullbackHomeomorph h) fun ⟨⟨d, γ⟩, hx⟩ ↦ by
      simp [sphereCubePullbackHomeomorph, norm_cubeHomeomorphClosedBall_eq_one_iff]
  -- The ambient map of `φ` is the homeomorphism, read on the points of `sphereCubePair h`.
  have hφ (x : (sphereCubePair h).fst) :
      TopPair.Hom.fst φ.hom x = sphereCubePullbackHomeomorph h x :=
    (congrArg (fun f ↦ TopPair.Hom.fst f x) (TopPair.ofSubsetIso_hom _ _)).trans
      (TopPair.ofSubsetMap_fst_apply _ _ x)
  -- The fibre of the end point over the pole is the space of loops.
  let l : TopPair.ofSubset (p ⁻¹' {b}) ⟶ MoorePathFrom.loopPair Sph b :=
    TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨fun x ↦ ⟨x.val.toMoorePath, MoorePathFrom.source x.val,
        (MoorePathFrom.endpoint_apply x.val).symm.trans x.property⟩,
      MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 (by fun_prop)⟩)
      (by
        ext x
        exact MoorePathFrom.ext (MooreLoopSpace.toMoorePath_toMoorePathFrom _))
  have : IsIso (TopPair.Hom.fst l) := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso l := TopPair.isIso_of_isIso_fst_of_surjective_snd l fun ω ↦
    ⟨⟨MooreLoopSpace.toMoorePathFrom ω, MooreLoopSpace.endpoint_toMoorePathFrom ω⟩,
      MooreLoopSpace.ext (MooreLoopSpace.toMoorePath_toMoorePathFrom _)⟩
  have hfac : sphereCubePairToLoopPair h = φ.hom ≫ TopCat.cellPullbackPairMap p univ (m + 2) ≫
      (TopCat.spherePreimageSkeletonPairIso h (by omega)).hom ≫ l :=
    TopPair.hom_ext_of_fst _ (by
      ext x
      rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, TopCat.comp_app,
        TopCat.comp_app, TopCat.comp_app,
        TopCat.spherePreimageSkeletonPairIso_hom_fst_cellPullbackPairMap_fst_apply, hφ]
      exact MoorePathFrom.ext ((MoorePathPullback.toMoorePathFrom_toMoorePath _).trans
        (MoorePathPullback.path_mk _ _ _)))
  have := TopCat.isIso_singularHomologyMap_cellPullbackPairMap univ
    (IsHurewiczFibration.mem_serreFibrations (p := p)
      (MoorePathFrom.isHurewiczFibration_endpoint.{0} b)) k (m + 2) n
  have := TopPair.isIso_homologyMap_cubicalChainComplexMap_of_isIso (k := k)
    (TopCat.cellPullbackPairMap p univ (m + 2)) n
  rw [hfac, TopPair.cubicalChainComplexMap_comp, TopPair.cubicalChainComplexMap_comp,
    TopPair.cubicalChainComplexMap_comp]
  simp only [homologyMap_comp]
  infer_instance

/-! ### The path cube and the attaching cycle -/

/-- The **path cube** of the top cell: the singular cube `d ↦ τ d` of the based path space of the
sphere, for the Moore paths `τ = TauCeti.sphereCubePaths h` from the pole. -/
def spherePathCube :
    SingularCube (MoorePathFrom.loopPair Sph (spherePolePoint h)).fst (m + 1 + 1) :=
  ⟨fun d ↦ ⟨sphereCubePaths h d, source_sphereCubePaths h d⟩,
    (sphereCubePaths h).continuous.subtype_mk _⟩

@[simp]
theorem toMoorePath_spherePathCube (d : Fin (m + 1 + 1) → I) :
    MoorePathFrom.toMoorePath (spherePathCube h d) = sphereCubePaths h d :=
  MoorePathFrom.toMoorePath_mk _ _

/-- The faces of the path cube are loops: the boundary of the cube is sent to the paths ending at
the pole. -/
theorem mapsTo_spherePathCube :
    MapsTo (spherePathCube h) (Cube.boundary (Fin (m + 1 + 1)))
      (range (MoorePathFrom.loopPair Sph (spherePolePoint h)).map) :=
  fun d hd ↦ ⟨⟨sphereCubePaths h d, source_sphereCubePaths h d,
    (target_sphereCubePaths h d).trans (sphereCubeMap_of_mem_boundary h hd)⟩,
      MoorePathFrom.ext ((MooreLoopSpace.toMoorePath_toMoorePathFrom _).trans
        (toMoorePath_spherePathCube h d).symm)⟩

variable (k : Type) [CommRing k]

/-- The **attaching cycle** of the top cell of the sphere `Sⁿ`, `n = m + 2`: the signed sum of the
faces of the path cube, an `(n - 1)`-cycle of the Moore loops at the pole. -/
def sphereAttachingCycle :
    ((normalizedCubicalChainComplex k).obj
      (MoorePathFrom.loopPair Sph (spherePolePoint h)).snd).cycles (m + 1) :=
  TopPair.cubicalBoundaryCycleOfCube k (spherePathCube h) (mapsTo_spherePathCube h)

/-- The underlying chain of the attaching cycle is the signed sum of the faces of the path cube,
`TopPair.cubicalBoundaryChainOfCube`. -/
@[simp]
theorem iCycles_sphereAttachingCycle :
    (((normalizedCubicalChainComplex k).obj
      (MoorePathFrom.loopPair Sph (spherePolePoint h)).snd).iCycles (m + 1)).hom
        (sphereAttachingCycle h k) =
      TopPair.cubicalBoundaryChainOfCube k (spherePathCube h) (mapsTo_spherePathCube h) :=
  TopPair.iCycles_cubicalBoundaryCycleOfCube ..

/-- The boundary of the path cube is the image of the attaching cycle in the based path space. -/
theorem boundary_ofCube_spherePathCube :
    NormalizedCubicalChain.boundary (MoorePathFrom Sph (spherePolePoint h)) k (m + 1)
        (NormalizedCubicalChain.ofCube (MoorePathFrom Sph (spherePolePoint h)) k
          (spherePathCube h)) =
      NormalizedCubicalChain.map k (MooreLoopSpace.toMoorePathFrom (b := spherePolePoint h)) (m + 1)
        ((((normalizedCubicalChainComplex k).obj
          (MoorePathFrom.loopPair Sph (spherePolePoint h)).snd).iCycles (m + 1)).hom
            (sphereAttachingCycle h k)) :=
  (TopPair.map_cubicalBoundaryChainOfCube k (spherePathCube h) (mapsTo_spherePathCube h)).symm.trans
    (congrArg _ (iCycles_sphereAttachingCycle h k).symm)

/-- **The Leibniz rule for the product with the path cube**: for a `q`-cycle `z` of the Moore
loops, the boundary of `z · σ`, for the path cube `σ`, is `(-1) ^ q` times the image of the product
`z · x` with the attaching cycle `x`. -/
private theorem boundary_leftAct_sphereAttachingCycle {q : ℕ}
    (z : ((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).cycles q) :
    NormalizedCubicalChain.boundary (MoorePathFrom Sph (spherePolePoint h)) k (q + (m + 1))
      (NormalizedCubicalChain.leftAct (MooreLoopSpace Sph (spherePolePoint h))
        (MoorePathFrom Sph (spherePolePoint h)) k q (m + 1 + 1)
        ((((normalizedCubicalChainComplex k).obj
            (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).iCycles q).hom z)
        (NormalizedCubicalChain.ofCube (MoorePathFrom Sph (spherePolePoint h)) k
          (spherePathCube h))) =
      NormalizedCubicalChain.map k (MooreLoopSpace.toMoorePathFrom (b := spherePolePoint h))
        (q + (m + 1))
        ((-1 : k) ^ q • NormalizedCubicalChain.mul (MooreLoopSpace Sph (spherePolePoint h)) k q
          (m + 1) ((((normalizedCubicalChainComplex k).obj
            (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).iCycles q).hom z)
          ((((normalizedCubicalChainComplex k).obj
            (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).iCycles (m + 1)).hom
              (sphereAttachingCycle h k))) := by
  rw [NormalizedCubicalChain.boundary_leftAct_of_boundary_eq_zero _
      (NormalizedCubicalChain.boundary_cast_iCycles_eq_zero z),
    boundary_ofCube_spherePathCube h k, map_smul]
  exact congrArg _ ((NormalizedCubicalChain.map_leftAct
    (MooreLoopSpace.toMoorePathFrom (b := spherePolePoint h)) MooreLoopSpace.toMoorePathFrom_mul
      _ _).symm.trans
      (congrArg _ (NormalizedCubicalChain.leftAct_eq_mul _ _)))

/-! ### The isomorphism -/

/-- **Multiplication by the attaching class on the homology of the loops of a sphere.** For the
sphere `Sⁿ`, `n = m + 2`, the isomorphism `H_q(Ω_b Sⁿ; k) ≃ₗ[k] H_{q+n-1}(Ω_b Sⁿ; k)` of the
normalized cubical homology of the Moore loops at the pole which sends the class of a cycle `z` to
the class of its Pontryagin product `z · x` with the attaching cycle `x`
(`TauCeti.sphereLoopHomologyMulRightEquiv_homologyπ`). -/
def sphereLoopHomologyMulRightEquiv (q : ℕ) :
    ((normalizedCubicalChainComplex k).obj
        (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).homology q ≃ₗ[k]
      ((normalizedCubicalChainComplex k).obj
        (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).homology (q + (m + 1)) :=
  have := isIso_homologyMap_sphereCubePairToLoopPair h k (q + (m + 1 + 1))
  have : ContractibleSpace (MoorePathFrom.loopPair Sph (spherePolePoint h)).fst :=
    inferInstanceAs (ContractibleSpace (MoorePathFrom Sph (spherePolePoint h)))
  have : IsIso ((MoorePathFrom.loopPair Sph (spherePolePoint h)).cubicalHomologyδ k
      (q + (m + 1) + 1) (q + (m + 1)) rfl) :=
    TopPair.isIso_cubicalHomologyδ_of_contractibleSpace k _ (q + m)
  MoorePathPullback.cubicalHomologyCubeBoundaryEquiv (sphereCubePaths h)
      (source_sphereCubePaths h) (target_sphereCubePaths h) k q ≪≫ₗ
    (asIso (homologyMap (TopPair.cubicalChainComplexMap k (sphereCubePairToLoopPair h))
      (q + (m + 1 + 1)))).toLinearEquiv ≪≫ₗ
    (asIso ((MoorePathFrom.loopPair Sph (spherePolePoint h)).cubicalHomologyδ k
      (q + (m + 1) + 1) (q + (m + 1)) rfl)).toLinearEquiv ≪≫ₗ
    LinearEquiv.smulOfUnit ((-1 : kˣ) ^ q)

/-- The value of `TauCeti.sphereLoopHomologyMulRightEquiv` on a class: the image under the cell
isomorphism, excision and the connecting morphism, times the sign `(-1) ^ q`. -/
private theorem sphereLoopHomologyMulRightEquiv_apply (q : ℕ)
    (μ : ((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).homology q) :
    sphereLoopHomologyMulRightEquiv h k q μ =
      ((-1 : kˣ) ^ q) • ((MoorePathFrom.loopPair Sph (spherePolePoint h)).cubicalHomologyδ k
        (q + (m + 1) + 1) (q + (m + 1)) rfl).hom (homologyMap (TopPair.cubicalChainComplexMap k
          (sphereCubePairToLoopPair h)) (q + (m + 1 + 1))
            (MoorePathPullback.cubicalHomologyCubeBoundaryEquiv (sphereCubePaths h)
              (source_sphereCubePaths h) (target_sphereCubePaths h) k q μ)) :=
  (rfl)

/-- The projection of the section cube of the pullback is the path cube. -/
private theorem map_sectionCube :
    MoorePathPullback.toMoorePathFrom.comp
        (MoorePathPullback.sectionCube (sphereCubePaths h) (source_sphereCubePaths h)
          (target_sphereCubePaths h)) =
      spherePathCube h :=
  ContinuousMap.ext fun d ↦ MoorePathFrom.ext <|
    ((MoorePathPullback.toMoorePathFrom_toMoorePath _).trans
      (MoorePathPullback.path_sectionCube _ _ _ d)).trans (toMoorePath_spherePathCube h d).symm

/-- **The class of `z · σ`**: for a `q`-cycle `z` of the Moore loops, the chain `z · σ` of the based
path space, for the path cube `σ`, represents the image under the cell isomorphism and excision of
the class of `z`. -/
private theorem isCubicalRepresentative_leftAct_spherePathCube (q : ℕ)
    (z : ((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).cycles q) :
    (MoorePathFrom.loopPair Sph (spherePolePoint h)).IsCubicalRepresentative k
      (NormalizedCubicalChain.leftAct (MooreLoopSpace Sph (spherePolePoint h))
        (MoorePathFrom Sph (spherePolePoint h)) k q (m + 1 + 1)
        ((((normalizedCubicalChainComplex k).obj
            (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).iCycles q).hom z)
        (NormalizedCubicalChain.ofCube (MoorePathFrom Sph (spherePolePoint h)) k
          (spherePathCube h)))
      (homologyMap (TopPair.cubicalChainComplexMap k (sphereCubePairToLoopPair h))
        (q + (m + 1 + 1)) (MoorePathPullback.cubicalHomologyCubeBoundaryEquiv (sphereCubePaths h)
          (source_sphereCubePaths h) (target_sphereCubePaths h) k q
            ((((normalizedCubicalChainComplex k).obj
              (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).homologyπ q).hom z))) := by
  -- The cell isomorphism is represented by `z · c₀` for the section cube `c₀`.
  obtain ⟨r, hr, hμ⟩ := (TopPair.isCubicalRepresentative_iff _ _).1
    ((MoorePathPullback.isCubicalRepresentative_cubicalHomologyCubeBoundaryEquiv
      (sphereCubePaths h) (source_sphereCubePaths h) (target_sphereCubePaths h) k q z).map
        (sphereCubePairToLoopPair h))
  -- The projection to the based path space carries `z · c₀` to `z · σ`.
  have key : NormalizedCubicalChain.map k
        (MoorePathPullback.toMoorePathFrom (f := sphereCubeMap h) (b := spherePolePoint h)) _
        (NormalizedCubicalChain.leftAct (MooreLoopSpace Sph (spherePolePoint h))
          (MoorePathPullback (sphereCubeMap h) (spherePolePoint h)) k q (m + 1 + 1)
          ((((normalizedCubicalChainComplex k).obj
            (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).iCycles q).hom z)
          (NormalizedCubicalChain.ofCube _ k (MoorePathPullback.sectionCube (sphereCubePaths h)
            (source_sphereCubePaths h) (target_sphereCubePaths h)))) =
      NormalizedCubicalChain.leftAct (MooreLoopSpace Sph (spherePolePoint h))
        (MoorePathFrom Sph (spherePolePoint h)) k q (m + 1 + 1)
        ((((normalizedCubicalChainComplex k).obj
            (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).iCycles q).hom z)
        (NormalizedCubicalChain.ofCube (MoorePathFrom Sph (spherePolePoint h)) k
          (spherePathCube h)) := by
    refine (NormalizedCubicalChain.map_leftAct MoorePathPullback.toMoorePathFrom
      MoorePathPullback.toMoorePathFrom_leftAct _ _).trans ?_
    rw [NormalizedCubicalChain.map_ofCube]
    exact congrArg _ (congrArg _ (map_sectionCube h))
  exact (TopPair.isCubicalRepresentative_iff _ _).2 ⟨r, (congrArg (fun x ↦
    ((cokernel.π ((normalizedCubicalChainComplex k).map
      (MoorePathFrom.loopPair Sph (spherePolePoint h)).map)).f (q + (m + 1 + 1))).hom x)
        key).symm.trans hr, hμ⟩

/-- **The isomorphism `TauCeti.sphereLoopHomologyMulRightEquiv` is the product with the attaching
cycle**: it sends the class of a `q`-cycle `z` of the Moore loops at the pole to the class of the
Pontryagin product `z · x` of `z` with the attaching cycle `x` (`TauCeti.sphereAttachingCycle`),
given as any cycle `w` with the chain `z · x`. -/
theorem sphereLoopHomologyMulRightEquiv_homologyπ (q : ℕ)
    (z : ((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).cycles q)
    (w : ((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).cycles (q + (m + 1)))
    (hw : (((normalizedCubicalChainComplex k).obj _).iCycles (q + (m + 1))).hom w =
      NormalizedCubicalChain.mul _ k q (m + 1)
        ((((normalizedCubicalChainComplex k).obj _).iCycles q).hom z)
        ((((normalizedCubicalChainComplex k).obj _).iCycles (m + 1)).hom
          (sphereAttachingCycle h k))) :
    sphereLoopHomologyMulRightEquiv h k q
        ((((normalizedCubicalChainComplex k).obj _).homologyπ q).hom z) =
      (((normalizedCubicalChainComplex k).obj _).homologyπ (q + (m + 1))).hom w := by
  -- The boundary of `z · σ` is `(-1) ^ q` times the image of `z · x`, so the connecting morphism
  -- takes the value `(-1) ^ q • [w]`.
  have e1 : (((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).iCycles (q + (m + 1))).hom
        ((-1 : k) ^ q • w) = (-1 : k) ^ q • (((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).iCycles (q + (m + 1))).hom w :=
    map_smul _ _ _
  have h3 := (isCubicalRepresentative_leftAct_spherePathCube h k q z).cubicalHomologyδ_eq
    (n := q + (m + 1)) ((-1 : k) ^ q • w)
      ((congrArg (NormalizedCubicalChain.map k
        (MooreLoopSpace.toMoorePathFrom (b := spherePolePoint h))
        (q + (m + 1))) (e1.trans (congrArg _ hw))).trans
          (boundary_leftAct_sphereAttachingCycle h k z).symm)
  have e2 : (((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).homologyπ (q + (m + 1))).hom
        ((-1 : k) ^ q • w) = (-1 : k) ^ q • (((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).homologyπ (q + (m + 1))).hom w :=
    map_smul _ _ _
  -- The sign `(-1) ^ q` cancels the one in the definition.
  rw [sphereLoopHomologyMulRightEquiv_apply, h3, Units.smul_def]
  refine (congrArg _ e2).trans ?_
  -- The two smul instances agree: both are the `k`-module structure of the homology.
  change ((-1 : k) ^ q) • ((-1 : k) ^ q • (((normalizedCubicalChainComplex k).obj
    (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).homologyπ (q + (m + 1))).hom w) = _
  rw [smul_smul, ← mul_pow]
  simp

/-- **The loops of `Sⁿ` have no homology in the degrees `1, …, n - 2`.** For the sphere `Sⁿ`,
`n = m + 2`, the normalized cubical homology of the Moore loops at the pole vanishes in degree
`j + 1` for `j < m`, with coefficients in any commutative ring `k`: it is the singular homology,
which vanishes in the degrees not divisible by `n - 1`
(`TauCeti.isZero_singularHomology_mooreLoopSpace_sphere`). -/
theorem isZero_homology_sphereLoop {j : ℕ} (hj : j < m) :
    IsZero (((normalizedCubicalChainComplex k).obj
      (TopCat.of (MooreLoopSpace Sph (spherePolePoint h)))).homology (j + 1)) :=
  (isZero_singularHomology_mooreLoopSpace_sphere (n := m + 2)
    (by simp [finrank_euclideanSpace, h]) (by omega) (spherePolePoint h) k
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).of_iso
    (singularCubicalHomologyIso k _ (j + 1)).symm

end TauCeti
