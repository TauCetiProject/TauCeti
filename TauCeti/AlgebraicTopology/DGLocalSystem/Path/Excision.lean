/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Skeleton
public import TauCeti.AlgebraicTopology.Singular.Fibration.Convergence
public import TauCeti.AlgebraicTopology.Singular.Fibration.Cubical.Skeleton
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
(`TauCeti.exists_add_differential_sub_mem_pathFromChainSkeleton`). The relative homology
`H_p(P, ∂P; R)` vanishes below the cell dimension, for `p < n`
(`TauCeti.isZero_homology_cubicalChainComplex_ofSubset_sigmaCellMap`).

The statement is written on chains, as for `TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`:
every relative cycle is a relative boundary. A relative cycle is a pair `(x, y)` of a chain `x` of
`P` whose boundary lies over the spheres and a chain `y` of the `n`-th stage with
`x - ∂y` in the `(n - 1)`-th stage; it is a relative boundary when it is `(∂u, u + ∂v)`, with `v` in
the `n`-th stage, modulo the chains over the spheres and the `(n - 1)`-th stage. This is the form in
which a quotient of the filtration is compared with free generators attached over the cells in
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`, in Brown's construction of a
semi-free model of `C_*(P_b B; R)` over the chains on the loop space, one skeleton at a time.

The end point map of the based path space is a Hurewicz fibration
(`TauCeti.MoorePathFrom.isHurewiczFibration_endpoint`), so the projection of relative cubical
chain complexes `N(P, ∂P) ⟶ N(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` is a quasi-isomorphism
(`TauCeti.TopCat.quasiIso_cubicalChainComplexMap_cellPullbackPairMap`). This quasi-isomorphism
is read on chains for every Serre fibration by
`TauCeti.TopCat.exists_add_differential_sub_mem_preimageSkeleton`, and the first statement is its
case for the based path fibration.

## Main results

* `TauCeti.exists_add_differential_sub_mem_pathFromChainSkeleton`: the push-forward from the
  pullback to the `n`-cells, relative to the boundary spheres, is a quasi-isomorphism onto the
  quotient of the `n`-th stage of the skeletal filtration of `C_*(P_b B; R)` by the `(n - 1)`-th.
* `TauCeti.isZero_homology_cubicalChainComplex_ofSubset_sigmaCellMap`: the relative homology of the
  pullback to the `n`-cells, relative to the boundary spheres, vanishes in degrees below `n`.

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

omit [T2Space B] in
/-- The based path fibration is a Serre fibration, since it is a Hurewicz fibration. -/
private theorem pathFromEndpoint_mem_serreFibrations :
    TopCat.serreFibrations (pathFromEndpoint B b) :=
  (MoorePathFrom.isHurewiczFibration_endpoint.{0} b).mem_serreFibrations

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

omit [T2Space B] in
variable (b C) in
/-- `cellPullbackHomeomorph` is the identity on the underlying pairs. -/
private theorem val_cellPullbackHomeomorph (n : ℕ) (z : MoorePathPullback (sigmaCellMap C n) b) :
    (cellPullbackHomeomorph b C n z).val = z.val :=
  (rfl)

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
  simp only [mem_pathFromChainSkeleton] at hy hxy ⊢
  exact TopCat.exists_add_differential_sub_mem_preimageSkeleton H
    (pathFromEndpoint_mem_serreFibrations (B := B) (b := b)) (cellPullbackHomeomorph b C n)
    MoorePathPullback.toMoorePathFrom
    (fun ⟨⟨d, γ⟩, h⟩ ↦ MoorePathFrom.ext (by
      rw [MoorePathPullback.toMoorePathFrom_toMoorePath, MoorePathPullback.path_mk,
        val_cellPullbackHomeomorph]))
    (fun ⟨⟨d, γ⟩, h⟩ ↦ by
      rw [mem_preimage, MoorePathPullback.proj_apply, MoorePathPullback.point_mk,
        val_cellPullbackHomeomorph, mem_ofPred_eq])
    hx hy hxy

variable (b C R) in
/-- **The relative homology of the pullback over the cells vanishes below their dimension.** Let
`P` be the pullback of the based path fibration `P_b B → B` along the characteristic maps of the
`n`-cells and `∂P` its part over the boundary spheres. Then `H_p(P, ∂P; R) = 0` for `p < n`: the
projection to `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` is an isomorphism on relative homology, and the skeletal
filtration of a Serre fibration has no relative homology below the cell dimension
(`TauCeti.TopCat.isZero_singularHomology_preimageSkeleton_succ`). -/
theorem isZero_homology_cubicalChainComplex_ofSubset_sigmaCellMap {n p : ℕ} (hp : p < n) :
    IsZero (((TopPair.ofSubset (X := _root_.TopCat.of (MoorePathPullback (sigmaCellMap C n) b))
      (MoorePathPullback.proj (sigmaCellMap C n) b ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1})
        ).cubicalChainComplex R).homology p) := by
  have hser := pathFromEndpoint_mem_serreFibrations (B := B) (b := b)
  have h₁ := TopCat.isZero_singularHomology_preimageSkeleton_succ hser R (C := C)
    ((n : ℤ) - 1) p (by omega)
  rw [TopCat.ofInclusion_preimageSkeleton_eq_preimageSkeletonPair (C := C)
    (p := pathFromEndpoint B b) n ((n : ℤ) - 1) rfl] at h₁
  have h₂ : IsZero (((TopCat.preimageSkeletonPair (pathFromEndpoint B b) C n).cubicalChainComplex
      R).homology p) :=
    h₁.of_iso (TopPair.singularCubicalHomologyIso R _ p).symm
  have := TopCat.quasiIso_cubicalChainComplexMap_cellPullbackPairMap C hser R n
  have h₃ : IsZero (((TopCat.cellPullbackPair (pathFromEndpoint B b) C n).cubicalChainComplex
      R).homology p) :=
    h₂.of_iso (asIso (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap R
      (TopCat.cellPullbackPairMap (pathFromEndpoint B b) C n)) p))
  -- The two pullbacks are the same subspace of the product of the disks with `P_b B`.
  let e : TopPair.ofSubset (X := _root_.TopCat.of (MoorePathPullback (sigmaCellMap C n) b))
      (MoorePathPullback.proj (sigmaCellMap C n) b ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1}) ≅
        TopCat.cellPullbackPair (pathFromEndpoint B b) C n :=
    TopPair.ofSubsetIso (cellPullbackHomeomorph b C n) fun ⟨⟨d, γ⟩, h⟩ ↦ by
      simp [cellPullbackHomeomorph, MoorePathPullback.proj_apply, MoorePathPullback.point_mk]
  exact h₃.of_iso (asIso (HomologicalComplex.homologyMap
    (TopPair.cubicalChainComplexMap R e.hom) p))

end TauCeti
