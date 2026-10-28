/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.FirstHomology
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Skeleton
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Topology.CWComplex.Classical.Sphere.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph

/-!
# Homotopy groups of spheres up to their dimension

The unit sphere `Sⁿ` of an `(n + 1)`-dimensional real normed space is `(n - 1)`-connected:
`πₖ(Sⁿ, x)` is trivial for every `k < n`, in every degree including `π₀`
(`TauCeti.subsingleton_homotopyGroup_sphere_of_lt`). Consequently, by the Hurewicz theorem and
the homology of spheres, `πₙ(Sⁿ, x) ≅ ℤ` for `n ≥ 2` (`TauCeti.homotopyGroupSphereAddEquiv`),
and the double Moore loop space of `S³` has first integral homology `ℤ`
(`TauCeti.MooreLoopSpace.doubleFirstHomologySphereAddEquiv`).

The vanishing follows from cellular compression, as in Hatcher's Corollary 4.12. The sphere
`Sⁿ` has a CW structure with one `0`-cell and one `n`-cell (`TauCeti.sphereCWComplex`), so its
`(n - 1)`-skeleton is a single point. The inclusion of that skeleton is surjective on `πₖ` for
`k ≤ n - 1` (`TauCeti.surjective_homotopyGroupMap_skeletonLT`), so `πₖ(Sⁿ)` is trivial at the
`0`-cell, and hence at every base point since `Sⁿ` is path connected. Spheres of normed spaces are
reduced to Euclidean ones through `TauCeti.sphereHomeomorphOfFinrankEq`.

The isomorphism `πₙ(Sⁿ, x) ≅ ℤ` is the cubical Hurewicz isomorphism
`HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv` followed by the identification
`TauCeti.reducedSingularHomologySphereIso` of `Hₙ(Sⁿ; ℤ)` with `ℤ` determined by an orthonormal
basis, so its sign depends on the orientation of that basis.

## Main declarations

* `TauCeti.subsingleton_homotopyGroup_sphere_of_lt`: `πₖ(Sⁿ, x)` is trivial for `k < n`.
* `TauCeti.homotopyGroupSphereAddEquiv`: `πₙ(Sⁿ, x) ≅ ℤ` for `n ≥ 2`, given an orthonormal basis.
* `TauCeti.MooreLoopSpace.doubleFirstHomologySphereAddEquiv`: `H₁(ΩᴹΩᴹS³; ℤ) ≅ ℤ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Corollaries 4.9 and 4.12, and Section 4.2, Corollary 4.25.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 5.11.
-/

public section

noncomputable section

open Metric Set Module CategoryTheory Topology.RelCWComplex
open scoped unitInterval Topology Topology.Homotopy

namespace TauCeti

/-- **Spheres are `(n - 1)`-connected** (Hatcher, Corollary 4.9). For the unit sphere `Sⁿ` of an
`(n + 1)`-dimensional real normed space, the homotopy set `πₖ(Sⁿ, x)` is trivial for every
`k = Nat.card N < n`. In degree zero this says that `Sⁿ` is path connected for `n ≥ 1`. -/
theorem subsingleton_homotopyGroup_sphere_of_lt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (hE : finrank ℝ E = n + 1)
    {N : Type*} [Finite N] (hN : Nat.card N < n) (x : sphere (0 : E) 1) :
    Subsingleton (HomotopyGroup N (sphere (0 : E) 1) x) := by
  have := Fintype.ofFinite N
  have := Module.finite_of_finrank_eq_succ hE
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (n := n) (by omega)
  let F := EuclideanSpace ℝ (Fin (m + 2))
  have hF : Fintype.card (Fin (m + 2)) = m + 1 + 1 := Fintype.card_fin _
  let _ := sphereCWComplex hF
  have := finite_sphereCWComplex hF
  -- The `m`-skeleton of the CW structure on `Sᵐ⁺¹` is its pole, the unique `0`-cell.
  have hA := skeletonLT_sphereCWComplex hF (k := m + 1) (by simp) le_rfl
  have hp : spherePole hF ∈ (skeletonLT (sphere (0 : F) 1) (m + 1) : Set F) :=
    hA ▸ mem_singleton _
  have : Subsingleton (skeletonLT (sphere (0 : F) 1) (m + 1)) :=
    (hA ▸ subsingleton_singleton : Set.Subsingleton _).coe_sort
  -- Every class at the `0`-cell comes from the `m`-skeleton (Hatcher, Corollary 4.12); move the
  -- base point along a path in the sphere, and pass from `F` to `E`.
  have hpole := (surjective_homotopyGroupMap_skeletonLT (N := N) (by omega) rfl
    (skeletonLT (sphere (0 : F) 1) _).subset_complex ⟨_, hp⟩).subsingleton
  have : PathConnectedSpace (sphere (0 : F) 1) := isPathConnected_iff_pathConnectedSpace.1 <|
    isPathConnected_sphere (by rw [← finrank_eq_rank, finrank_euclideanSpace_fin]; norm_cast; omega)
      0 zero_le_one
  let h := sphereHomeomorphOfFinrankEq (hE.trans (finrank_euclideanSpace_fin (n := m + 2)).symm :
    finrank ℝ E = finrank ℝ F)
  exact (HomotopyGroup.homeomorphEquiv (N := N) h x).subsingleton_congr.mpr
    ((homotopyGroupEquivOfPath (PathConnectedSpace.somePath _ _)).subsingleton_congr.mp hpole)

section Hurewicz

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- `TauCeti.subsingleton_homotopyGroup_sphere_of_lt`, with the dimension read off an orthonormal
basis. -/
private theorem subsingleton_homotopyGroup_sphere_of_basis {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E) {N : Type} [Finite N] (hN : Nat.card N < m)
    (x : sphere (0 : E) 1) : Subsingleton (HomotopyGroup N (sphere (0 : E) 1) x) :=
  subsingleton_homotopyGroup_sphere_of_lt (by simp [finrank_eq_card_basis b.toBasis]) hN x

/-- **The `n`-th homotopy group of `Sⁿ` is `ℤ`** for `n ≥ 2` (Hatcher, Corollary 4.25). For the
unit sphere of a real inner product space with an orthonormal basis `b` indexed by `Fin (n + 3)`,
this is the cubical Hurewicz isomorphism `π_{n+2}(S^{n+2}, x) ≅ H_{n+2}(S^{n+2}; ℤ)` followed by
the identification of `H_{n+2}(S^{n+2}; ℤ)` with `ℤ` determined by `b`. -/
def homotopyGroupSphereAddEquiv (b : OrthonormalBasis (Fin (n + 3)) ℝ E)
    (x : sphere (0 : E) 1) :
    Additive (π_ (n + 2) (sphere (0 : E) 1) x) ≃+ ℤ :=
  (HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv fun _ hk ↦
      subsingleton_homotopyGroup_sphere_of_basis b (by simpa using hk) x).trans
    (((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) (n + 1)).app _).symm ≪≫
      reducedSingularHomologySphereIso (ModuleCat.of ℤ ℤ) b).toLinearEquiv.toAddEquiv

/-- `TauCeti.homotopyGroupSphereAddEquiv` is the cubical Hurewicz isomorphism followed by the
identification of the top homology of the sphere with `ℤ`. -/
theorem homotopyGroupSphereAddEquiv_apply (b : OrthonormalBasis (Fin (n + 3)) ℝ E)
    (x : sphere (0 : E) 1)
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) (sphere (0 : E) 1) x))
    (a : Additive (π_ (n + 2) (sphere (0 : E) 1) x)) :
    homotopyGroupSphereAddEquiv b x a =
      (reducedSingularHomologySphereIso (ModuleCat.of ℤ ℤ) b).hom.hom
        (((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) (n + 1)).inv.app _).hom
          (HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv hX a)) :=
  (rfl)

/-- **The first homology of the double loop space of `S³` is `ℤ`.** For the unit sphere `S³` of
a real inner product space with an orthonormal basis `b` indexed by `Fin 4`, the first integral
homology of the double Moore loop space `ΩᴹΩᴹS³` is `π₃(S³) ≅ ℤ`, through degree-one Hurewicz
(`TauCeti.MooreLoopSpace.doubleFirstHomologyAddEquiv`) and
`TauCeti.homotopyGroupSphereAddEquiv`. -/
def MooreLoopSpace.doubleFirstHomologySphereAddEquiv (b : OrthonormalBasis (Fin 4) ℝ E)
    (x : sphere (0 : E) 1) :
    ((singularChains ℤ).obj
      (TopCat.of (MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1))).homology 1 ≃+ ℤ :=
  have : Subsingleton (π_ 2 (sphere (0 : E) 1) x) :=
    subsingleton_homotopyGroup_sphere_of_basis b (by simp) x
  (doubleFirstHomologyAddEquiv x).symm.trans (homotopyGroupSphereAddEquiv (n := 1) b x)

/-- `TauCeti.MooreLoopSpace.doubleFirstHomologySphereAddEquiv` is the inverse of degree-one
Hurewicz for the double Moore loop space followed by `TauCeti.homotopyGroupSphereAddEquiv`. -/
theorem MooreLoopSpace.doubleFirstHomologySphereAddEquiv_apply
    (b : OrthonormalBasis (Fin 4) ℝ E) (x : sphere (0 : E) 1)
    [Subsingleton (π_ 2 (sphere (0 : E) 1) x)]
    (a : ((singularChains ℤ).obj
      (TopCat.of (MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1))).homology 1) :
    doubleFirstHomologySphereAddEquiv b x a =
      homotopyGroupSphereAddEquiv (n := 1) b x ((doubleFirstHomologyAddEquiv x).symm a) :=
  (rfl)

end Hurewicz

end TauCeti
