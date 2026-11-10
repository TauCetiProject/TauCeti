/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.FirstHomology
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Hurewicz
public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.ReducedHomology
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
the double Moore loop space of `S³` has first integral homology `ℤ`
(`TauCeti.MooreLoopSpace.doubleFirstHomologySphereAddEquiv`), and for `m ≥ 4` the double Moore loop
space of `Sᵐ` has integral homology `ℤ` in degree `m - 2`
(`TauCeti.MooreLoopSpace.doubleHomologySphereAddEquiv`). In particular `πₙ(Sⁿ, x)` is nontrivial
for `n ≥ 2` (`TauCeti.nontrivial_homotopyGroup_sphere`). In degree zero, as `π₂(S²) ≅ ℤ`,
the double Moore loop space of `S²`
has one path component for each integer, and its reduced zeroth homology is the coproduct of copies
of the coefficients indexed by the nonzero integers
(`TauCeti.MooreLoopSpace.doubleReducedHomology₀SphereIso`); with coefficients in a ring `R` it
contains a copy of `R`, so an infinite cyclic subgroup for `R = ℤ`
(`TauCeti.MooreLoopSpace.exists_injective_doubleReducedHomology₀_sphere`).

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
* `TauCeti.MooreLoopSpace.doubleHomologySphereAddEquiv`: `Hₘ₋₂(ΩᴹΩᴹSᵐ; ℤ) ≅ ℤ` for `m ≥ 4`.
* `TauCeti.MooreLoopSpace.doubleReducedHomology₀SphereIso`: `H~₀(ΩᴹΩᴹS²; R) ≅ ∐_{k ≠ 0} R`,
  with generator `[γ] - [1]` at the integer class of `γ`
  (`TauCeti.MooreLoopSpace.ι_doubleReducedHomology₀SphereIso_inv_ι`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Corollaries 4.9 and 4.12, and Section 4.2, Corollary 4.25.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Propositions 5.11 and 6.21.
-/

public section

noncomputable section

open Metric Set Module CategoryTheory Limits Topology.RelCWComplex
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

/-- **The double loop space of `Sⁿ⁺⁴` has homology `ℤ` in degree `n + 2`.** For the unit sphere
`Sⁿ⁺⁴` of a real inner product space with an orthonormal basis `b` indexed by `Fin (n + 5)`, the
integral homology of the double Moore loop space `ΩᴹΩᴹSⁿ⁺⁴` in degree `n + 2` is
`πₙ₊₄(Sⁿ⁺⁴) ≅ ℤ`, through the Hurewicz identification
`TauCeti.MooreLoopSpace.doubleHomologyAddEquiv` and `TauCeti.homotopyGroupSphereAddEquiv`. -/
def MooreLoopSpace.doubleHomologySphereAddEquiv (b : OrthonormalBasis (Fin (n + 5)) ℝ E)
    (x : sphere (0 : E) 1) :
    ((singularChains ℤ).obj
      (TopCat.of (MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1))).homology (n + 2) ≃+
        ℤ :=
  (doubleHomologyAddEquiv x n fun _ hk ↦
      subsingleton_homotopyGroup_sphere_of_basis b (by simpa using hk) x).symm.trans
    (homotopyGroupSphereAddEquiv (n := n + 2) b x)

/-- `TauCeti.MooreLoopSpace.doubleHomologySphereAddEquiv` is the inverse of the Hurewicz
identification for the double Moore loop space followed by
`TauCeti.homotopyGroupSphereAddEquiv`. -/
theorem MooreLoopSpace.doubleHomologySphereAddEquiv_apply
    (b : OrthonormalBasis (Fin (n + 5)) ℝ E) (x : sphere (0 : E) 1)
    (hX : ∀ k < n + 2, Subsingleton (π_ (k + 2) (sphere (0 : E) 1) x))
    (a : ((singularChains ℤ).obj
      (TopCat.of (MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1))).homology (n + 2)) :
    doubleHomologySphereAddEquiv b x a =
      homotopyGroupSphereAddEquiv (n := n + 2) b x ((doubleHomologyAddEquiv x n hX).symm a) :=
  (rfl)

/-- **`πₙ(Sⁿ)` is nontrivial** for `n ≥ 2`: for the unit sphere `Sⁿ⁺²` of an
`(n + 3)`-dimensional real normed space, `πₙ₊₂(Sⁿ⁺², x)` is nontrivial. -/
theorem nontrivial_homotopyGroup_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : finrank ℝ E = n + 3) (x : sphere (0 : E) 1) :
    Nontrivial (π_ (n + 2) (sphere (0 : E) 1) x) := by
  have := Module.finite_of_finrank_eq_succ hE
  let h := sphereHomeomorphOfFinrankEq (hE.trans (finrank_euclideanSpace_fin (n := n + 3)).symm :
    finrank ℝ E = finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))))
  have := (Additive.ofMul.trans (homotopyGroupSphereAddEquiv
    (EuclideanSpace.basisFun (Fin (n + 3)) ℝ) (h x)).toEquiv).nontrivial
  exact (HomotopyGroup.homeomorphEquiv h x).nontrivial

/-- The path components of the double Moore loop space of `S²` are the integers, through
`π₂(S²) ≅ ℤ`. -/
private def MooreLoopSpace.zerothHomotopyDoubleSphereEquiv (b : OrthonormalBasis (Fin 3) ℝ E)
    (x : sphere (0 : E) 1) :
    ZerothHomotopy (MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1) ≃ ℤ :=
  (zerothHomotopyDoubleEquiv x).trans
    (Additive.ofMul.trans (homotopyGroupSphereAddEquiv (n := 0) b x).toEquiv)

private theorem MooreLoopSpace.zerothHomotopyDoubleSphereEquiv_mk_one
    (b : OrthonormalBasis (Fin 3) ℝ E) (x : sphere (0 : E) 1) :
    zerothHomotopyDoubleSphereEquiv b x (.mk 1) = 0 := by
  simp [zerothHomotopyDoubleSphereEquiv]

/-- **Reduced zeroth homology of the double loop space of `S²`.** For the unit sphere `S²` of a
real inner product space with an orthonormal basis `b` indexed by `Fin 3`, the reduced zeroth
homology `H~₀(ΩᴹΩᴹS²; R)` is the coproduct of copies of `R` indexed by the nonzero integers: the
path components of `ΩᴹΩᴹS²` are the elements of `π₂(S²) ≅ ℤ`
(`TauCeti.homotopyGroupSphereAddEquiv`). -/
def MooreLoopSpace.doubleReducedHomology₀SphereIso {C : Type*} [Category C]
    [HasCoproducts.{0} C] [Preadditive C] [CategoryWithHomology C] [HasKernels C] (R : C)
    (b : OrthonormalBasis (Fin 3) ℝ E) (x : sphere (0 : E) 1) :
    (reducedSingularHomologyFunctor R 0).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1)) ≅
      ∐ fun _ : {k : ℤ // k ≠ 0} ↦ R :=
  reducedSingularHomology₀IsoOfEquiv R
    (Y := TopCat.of (MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1)) 1
    (zerothHomotopyDoubleSphereEquiv b x) (zerothHomotopyDoubleSphereEquiv_mk_one b x)

/-- The generator of `TauCeti.MooreLoopSpace.doubleReducedHomology₀SphereIso` at the integer
`π₂(S²) ≅ ℤ` assigns to the class of a double Moore loop `γ` is `[γ] - [1]`. -/
@[reassoc]
theorem MooreLoopSpace.ι_doubleReducedHomology₀SphereIso_inv_ι {C : Type*} [Category C]
    [HasCoproducts.{0} C] [Preadditive C] [CategoryWithHomology C] [HasKernels C] (R : C)
    (b : OrthonormalBasis (Fin 3) ℝ E) (x : sphere (0 : E) 1)
    (γ : MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1)
    (h : homotopyGroupSphereAddEquiv (n := 0) b x
      (Additive.ofMul (zerothHomotopyDoubleEquiv x (.mk γ))) ≠ 0) :
    Sigma.ι (fun _ : {k : ℤ // k ≠ 0} ↦ R) ⟨_, h⟩ ≫
        (doubleReducedHomology₀SphereIso R b x).inv ≫
          (reducedSingularHomologyι R 0).app
            (TopCat.of (MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1)) =
      singularHomology₀Section R
          (X := TopCat.of (MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1)) γ -
        singularHomology₀Section R
          (X := TopCat.of (MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1)) 1 :=
  ι_reducedSingularHomology₀IsoOfEquiv_inv_ι R
    (Y := TopCat.of (MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1)) 1 γ
    (zerothHomotopyDoubleSphereEquiv b x) (zerothHomotopyDoubleSphereEquiv_mk_one b x) h

/-- **The reduced zeroth homology of `ΩᴹΩᴹS²` contains the coefficients.** For the unit sphere
`S²` of a real normed space of dimension three and a ring `R`, the kernel of the augmentation
`H₀(ΩᴹΩᴹS²; R) → H₀(pt; R)` contains a copy of `R`; for `R = ℤ` this is an infinite cyclic
subgroup. -/
theorem MooreLoopSpace.exists_injective_doubleReducedHomology₀_sphere {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {R : Type} [Ring R] (hE : finrank ℝ E = 3)
    (x : sphere (0 : E) 1) :
    ∃ f : R →ₗ[R] (reducedSingularHomologyFunctor (ModuleCat.of R R) 0).obj
        (TopCat.of (MooreLoopSpace (MooreLoopSpace (sphere (0 : E) 1) x) 1)),
      Function.Injective f :=
  have := nontrivial_homotopyGroup_sphere (n := 0) hE x
  exists_injective_doubleReducedHomology₀ x

end Hurewicz

end TauCeti
