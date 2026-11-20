/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Skeleton
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Relative.QuasiIso
public import TauCeti.AlgebraicTopology.Singular.Fibration.Cubical.Cells
public import TauCeti.Topology.PathSpace.Moore.Replacement.Equiv

/-!
# The quotients of the skeletal filtration of the chains on the based path space

Let `C ⊆ B` be a relative CW complex with skeleta `Xⁿ = skeletonLT C (n + 1)`, and `b ∈ B`. The
normalized cubical chains `C_*(P_b B; R)` on the Moore paths starting at `b` are filtered by the
chains supported over the preimages of the skeleta under the end point map
(`TauCeti.pathFromChainSkeleton`). This file computes the quotients of consecutive stages cell by
cell. Let `P` be the pullback of the end point map along the characteristic maps of the `n`-cells,
`MoorePathPullback (sigmaCellMap C n) b`, and `∂P` its part over their boundary spheres. Pushing
chains forward along `P → P_b B` is a quasi-isomorphism from the relative chains `C_*(P, ∂P)` onto
the quotient of the `n`-th stage by the `(n - 1)`-th
(`TauCeti.exists_add_differential_sub_mem_pathFromChainSkeleton`).

The statement is written on chains, as for `TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`:
every relative cycle is a relative boundary. A relative cycle is a pair `(x, y)` of a chain `x` of
`P` whose boundary lies over the spheres and a chain `y` of the `n`-th stage with
`x - ∂y` in the `(n - 1)`-th stage; it is a relative boundary when it is `(∂u, u + ∂v)`, with `v` in
the `n`-th stage, modulo the chains over the spheres and the `(n - 1)`-th stage. This is the form in
which a quotient of the filtration is compared with free generators attached over the cells in
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`, in Brown's construction of a
semi-free model of `C_*(P_b B; R)` over the chains on the loop space, one skeleton at a time.

The end point map of the based path space is a Hurewicz fibration
(`TauCeti.MoorePathFrom.isHurewiczFibration_endpoint`), so the
projection of relative cubical chain complexes `N(P, ∂P) ⟶ N(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` is a
quasi-isomorphism (`TauCeti.TopCat.quasiIso_cubicalChainComplexMap_cellPullbackPairMap`). The
chains of `p⁻¹(Xⁿ)` and `p⁻¹(Xⁿ⁻¹)` are the chains of `P_b B` supported in them, and
`TauCeti.exists_add_differential_sub_mem_cubicalChainModuleSupportedIn_of_quasiIso` reads this
quasi-isomorphism on the chains of `P` and `P_b B`.

## Main results

* `TauCeti.exists_add_differential_sub_mem_pathFromChainSkeleton`: the push-forward from the
  pullback to the `n`-cells, relative to the boundary spheres, is a quasi-isomorphism onto the
  quotient of the `n`-th stage of the skeletal filtration of `C_*(P_b B; R)` by the `(n - 1)`-th.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4 and §7.1.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

namespace TauCeti

universe u

variable {R : Type u} [CommRing R] (H : Type*)

/-! ### The based path fibration over the cells -/

variable {B : Type u} [TopologicalSpace B] [T2Space B] {b : B} {C D : Set B} [RelCWComplex C D]

/-- The based path fibration `P_b B → B`, as a morphism of topological spaces. -/
private abbrev pathFromEndpoint (B : Type u) [TopologicalSpace B] (b : B) :
    _root_.TopCat.of (MoorePathFrom B b) ⟶ _root_.TopCat.of B :=
  _root_.TopCat.ofHom (MoorePathFrom.endpoint B b)

variable (b C) in
/-- The pullback of the based path fibration to the disks of the `n`-cells, as the pullback
`TauCeti.TopCat.cellPullback` of a map in `TopCat`. Both spaces are subtypes of the product of the
disks of the `n`-cells with `P_b B`, since the carrier of `TopCat.of X` is `X` by definition, so the
homeomorphism is the identity on the underlying pairs and only the two defining equations, which
are symmetric to each other, differ. -/
private def cellPullbackHomeomorph (n : ℕ) :
    MoorePathPullback (sigmaCellMap C n) b ≃ₜ TopCat.cellPullback (pathFromEndpoint B b) C n :=
  Homeomorph.subtype (Homeomorph.refl _) fun _ ↦ by
    simp [MoorePathFrom.endpoint_apply, eq_comm]

variable (b C) in
/-- The preimage of `Xⁿ` is the `n`-th stage of the skeletal filtration. -/
private theorem preimage_skeletonLT_succ_eq (n : ℕ) :
    (pathFromEndpoint B b) ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞)) =
      preimageSkeleton C (MoorePathFrom.endpoint B b) n := by
  ext x
  simp [MoorePathFrom.endpoint_apply]

variable (b C) in
/-- The preimage of `Xⁿ⁻¹` is the `(n - 1)`-th stage of the skeletal filtration. -/
private theorem preimage_skeletonLT_eq (n : ℕ) :
    (pathFromEndpoint B b) ⁻¹' (skeletonLT C n) =
      preimageSkeleton C (MoorePathFrom.endpoint B b) (n - 1) := by
  ext x
  simp [MoorePathFrom.endpoint_apply]

variable (b C) in
/-- The projection of the pullback to the `n`-cells to `P_b B` is the projection to the preimage
of `Xⁿ`, followed by the inclusion. -/
private theorem toMoorePathFrom_eq (n : ℕ) (z : MoorePathPullback (sigmaCellMap C n) b) :
    MoorePathPullback.toMoorePathFrom z = ContinuousMap.subtypeVal _
      (TopPair.Hom.fst (TopCat.cellPullbackPairMap (pathFromEndpoint B b) C n)
        (cellPullbackHomeomorph b C n z)) := by
  obtain ⟨⟨d, γ⟩, h⟩ := z
  refine MoorePathFrom.ext ?_
  rw [MoorePathPullback.toMoorePathFrom_toMoorePath, MoorePathPullback.path_mk]
  -- `cellPullbackPairMap` projects a pair to its path, and `cellPullbackHomeomorph` is the
  -- identity on the underlying pairs by definition, so the right-hand side is the path `γ`.
  exact congrArg MoorePathFrom.toMoorePath
    (TopCat.coe_cellPullbackPairMap_fst_apply n (cellPullbackHomeomorph b C n ⟨(d, γ), h⟩)).symm

omit [T2Space B] in
variable (b C) in
/-- The part of the pullback over the boundary spheres. -/
private theorem image_symm_range_cellPullbackPair_map (n : ℕ) :
    ((cellPullbackHomeomorph b C n).symm : C(TopCat.cellPullback (pathFromEndpoint B b) C n,
        MoorePathPullback (sigmaCellMap C n) b)) ''
        Set.range (TopCat.cellPullbackPair (pathFromEndpoint B b) C n).map =
      MoorePathPullback.proj (sigmaCellMap C n) b ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1} := by
  ext ⟨⟨d, γ⟩, h⟩
  rw [Set.mem_preimage, MoorePathPullback.proj_apply, MoorePathPullback.point_mk,
    Set.mem_ofPred_eq]
  refine ⟨?_, fun hd ↦ ⟨_, ⟨⟨cellPullbackHomeomorph b C n ⟨(d, γ), h⟩, hd⟩, rfl⟩, rfl⟩⟩
  rintro ⟨_, ⟨v, rfl⟩, hv⟩
  -- The inverse of `cellPullbackHomeomorph` is the identity on the underlying pairs, so the cell
  -- coordinate of `hv` is this equation by definition.
  have hd : v.val.val.1 = d := congrArg (fun z ↦ z.val.1) hv
  rw [← hd]
  exact v.property

variable (b C) in
/-- The preimage of `Xⁿ⁻¹`, as a subset of `P_b B`. -/
private theorem image_range_preimageSkeletonPair_map (n : ℕ) :
    ContinuousMap.subtypeVal ((pathFromEndpoint B b) ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞))) ''
        Set.range (TopCat.preimageSkeletonPair (pathFromEndpoint B b) C n).map =
      preimageSkeleton C (MoorePathFrom.endpoint B b) (n - 1) := by
  refine Set.ext fun γ ↦ ⟨?_, fun hγ ↦ ?_⟩
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    rw [← preimage_skeletonLT_eq]
    exact w.property
  · rw [← preimage_skeletonLT_eq] at hγ
    exact ⟨_, ⟨⟨γ, hγ⟩, rfl⟩, rfl⟩

variable {H} in
/-- **The quotients of the skeletal filtration of the chains on the based path space are computed
over the cells.** Let `P` be the pullback of the based path fibration `P_b B → B` along the
characteristic maps of the `n`-cells and `∂P` its part over the boundary spheres. Pushing chains
forward along `P → P_b B` is a quasi-isomorphism from the relative chains `C_*(P, ∂P)` onto the
quotient of the `n`-th stage of the skeletal filtration of `C_*(P_b B)` by the `(n - 1)`-th, in the
following form: if `x` is a chain of `P` whose boundary lies over the spheres and `y` a chain of the
`n`-th stage such that the push-forward of `x` minus the boundary of `y` lies in the `(n - 1)`-th
stage, then `x` is the boundary of a chain `u` modulo the chains over the spheres, and `y` is the
push-forward of `u` plus the boundary of a chain `v` of the `n`-th stage modulo the `(n - 1)`-th
stage. -/
theorem exists_add_differential_sub_mem_pathFromChainSkeleton {n : ℕ}
    {x : cubicalChainModule (MoorePathPullback (sigmaCellMap C n) b) H R}
    {y : cubicalChainModule (MoorePathFrom B b) H R}
    (hx : cubicalChainModuleDifferential _ H R x ∈ cubicalChainModuleSupportedIn H R
      (MoorePathPullback.proj (sigmaCellMap C n) b ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1}))
    (hy : y ∈ pathFromChainSkeleton b C H R n)
    (hxy : cubicalChainModuleLinearMap R MoorePathPullback.toMoorePathFrom x -
        cubicalChainModuleDifferential _ H R y ∈ pathFromChainSkeleton b C H R (n - 1)) :
    ∃ (u : cubicalChainModule (MoorePathPullback (sigmaCellMap C n) b) H R)
      (v : cubicalChainModule (MoorePathFrom B b) H R),
      v ∈ pathFromChainSkeleton b C H R n ∧
        cubicalChainModuleDifferential _ H R u - x ∈ cubicalChainModuleSupportedIn H R
          (MoorePathPullback.proj (sigmaCellMap C n) b ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1}) ∧
        cubicalChainModuleLinearMap R MoorePathPullback.toMoorePathFrom u +
            cubicalChainModuleDifferential _ H R v - y ∈ pathFromChainSkeleton b C H R (n - 1) := by
  have := TopCat.quasiIso_cubicalChainComplexMap_cellPullbackPairMap (C := C)
    (IsHurewiczFibration.mem_serreFibrations (p := pathFromEndpoint B b)
      (MoorePathFrom.isHurewiczFibration_endpoint.{0} b)) R n
  simp only [mem_pathFromChainSkeleton] at hy hxy ⊢
  exact exists_add_differential_sub_mem_cubicalChainModuleSupportedIn_of_quasiIso H
    (TopCat.cellPullbackPairMap (pathFromEndpoint B b) C n)
    (Y := MoorePathFrom B b) (cellPullbackHomeomorph b C n)
    (ι := ContinuousMap.subtypeVal ((pathFromEndpoint B b) ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞))))
    IsEmbedding.subtypeVal _ (toMoorePathFrom_eq b C n)
    (image_symm_range_cellPullbackPair_map b C n)
    (Subtype.range_coe.trans (preimage_skeletonLT_succ_eq b C n))
    (image_range_preimageSkeletonPair_map b C n) hx hy hxy

end TauCeti
