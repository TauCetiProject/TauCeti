/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact
public import TauCeti.Topology.Homotopy.HomotopyGroup.TopologicalMonoid
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
public import TauCeti.Topology.PathSpace.Moore.Comparison.HomotopyGroup
import TauCeti.AlgebraicTopology.UniversalCover.Circle.HigherHomotopy

/-!
# The loop space of `CPⁿ` splits as `S¹ × ΩS²ⁿ⁺¹`

Let `q : S²ⁿ⁺¹ → CPⁿ` be the Hopf fibration, `n ≥ 1`, and let `v` be a unit vector of `ℂⁿ⁺¹`.
Given a based map `j : S¹ → ΩCPⁿ` from the circle to the Moore loop space at `[v]`, the
**based Hopf product** (`TauCeti.ComplexProjectiveSpace.hopfProduct`) is

`j ⋆ Ωq : S¹ × ΩS²ⁿ⁺¹ → ΩCPⁿ`, `(z, γ) ↦ j z * Ωq γ`,

the Moore concatenation of the loop `j z` with the image of the loop `γ` at `v`. When `j` induces
an isomorphism `π₁(S¹) ≅ π₁(ΩCPⁿ)`, it is a weak homotopy equivalence
(`TauCeti.ComplexProjectiveSpace.isWeakHomotopyEquivalence_hopfProduct`), and such maps `j` exist
(`TauCeti.ComplexProjectiveSpace.exists_isWeakHomotopyEquivalence_hopfProduct`).

The proof compares homotopy groups through the exact homotopy sequence of the Hopf fibration
(`TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact`). Both spaces are path connected, since
`S²ⁿ⁺¹` and `CPⁿ` are simply connected. In positive degrees the Moore loop space is a topological
monoid with a strict unit, so the product acts on homotopy groups by
`(j ⋆ Ωq)_* (a × b) = j_* a * (Ωq)_* b` (`HomotopyGroup.map_mul_prod`). In degree one the second
factor vanishes, because `π₁(ΩS²ⁿ⁺¹) = π₂(S²ⁿ⁺¹) = 0`, and `j_*` is bijective by assumption. In
degrees `k ≥ 2` the first factor vanishes, because the higher homotopy groups of the circle are
trivial, and `(Ωq)_*` is bijective because the loop-space shift identifies it with
`q_* : πₖ₊₁(S²ⁿ⁺¹) → πₖ₊₁(CPⁿ)`, an isomorphism for `k + 1 ≥ 3`.

A suitable `j` comes from a generator of `π₁(ΩCPⁿ) ≅ π₂(CPⁿ)`, which the boundary map of the Hopf
fibration identifies with `π₁(S¹) ≅ ℤ`: the generating loop, read as a map from the circle, sends
the counterclockwise generator of `π₁(S¹)` to it.

Since weak homotopy equivalences induce isomorphisms on singular homology, the splitting reduces
the integral homology of `ΩCPⁿ` to that of `S¹ × ΩS²ⁿ⁺¹`.

## Main definitions

* `TauCeti.ComplexProjectiveSpace.hopfProduct`: the based Hopf product `j ⋆ Ωq`.
* `TauCeti.ComplexProjectiveSpace.mooreLoopSpaceFundamentalGroupMulEquiv`: for `n ≥ 1`, the
  isomorphism `π₁(ΩCPⁿ) ≃* ℤ` through `π₂(CPⁿ)` and the boundary map of the Hopf fibration.

## Main results

* `TauCeti.ComplexProjectiveSpace.isWeakHomotopyEquivalence_hopfProduct`: for `n ≥ 1`, `j ⋆ Ωq`
  is a weak homotopy equivalence whenever `j` is bijective on fundamental groups.
* `TauCeti.ComplexProjectiveSpace.exists_isWeakHomotopyEquivalence_hopfProduct`: for `n ≥ 1`,
  there is a based map `j` for which `j ⋆ Ωq` is a weak homotopy equivalence.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 4.41 and Example 4.45.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.
-/

public section

noncomputable section

open Metric
open scoped Topology Topology.Homotopy

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ} (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)

/-- The **based Hopf product** `j ⋆ Ωq : S¹ × ΩS²ⁿ⁺¹ → ΩCPⁿ`, `(z, γ) ↦ j z * Ωq γ`: the Moore
concatenation of the loop `j z` of `CPⁿ` with the image of the loop `γ` of `S²ⁿ⁺¹` under the Hopf
fibration `q`. -/
def hopfProduct (j : C(Circle, MooreLoopSpace (ComplexProjectiveSpace n) (mk n v))) :
    C(Circle × MooreLoopSpace (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v,
      MooreLoopSpace (ComplexProjectiveSpace n) (mk n v)) :=
  j.comp ContinuousMap.fst *
    (MooreLoopSpace.map (x := v) ⟨mk n, continuous_mk n⟩ rfl).toContinuousMap.comp
      ContinuousMap.snd

@[simp]
theorem hopfProduct_apply (j : C(Circle, MooreLoopSpace (ComplexProjectiveSpace n) (mk n v)))
    (p : Circle × MooreLoopSpace (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v) :
    hopfProduct v j p = j p.1 * MooreLoopSpace.map ⟨mk n, continuous_mk n⟩ rfl p.2 :=
  (rfl)

variable {v}

/-- **The loop space of `CPⁿ` splits as `S¹ × ΩS²ⁿ⁺¹`.** For `n ≥ 1` and a based map
`j : S¹ → ΩCPⁿ` inducing an isomorphism of fundamental groups, the based Hopf product
`j ⋆ Ωq : S¹ × ΩS²ⁿ⁺¹ → ΩCPⁿ`, `(z, γ) ↦ j z * Ωq γ`, is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_hopfProduct (hn : n ≠ 0)
    {j : C(Circle, MooreLoopSpace (ComplexProjectiveSpace n) (mk n v))} (hj : j 1 = 1)
    (hjb : Function.Bijective (FundamentalGroup.mapOfEq j hj)) :
    (hopfProduct v j).IsWeakHomotopyEquivalence := by
  -- `S²ⁿ⁺¹` and `CPⁿ` are simply connected, so both loop spaces are path connected.
  have hS (k : ℕ) (hk : k < 2 * n + 1) :
      Subsingleton (π_ k (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v) :=
    subsingleton_homotopyGroup_sphere (N := Fin k) (by simpa using hk) v
  have : PathConnectedSpace
      (MooreLoopSpace (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v) :=
    (MooreLoopSpace.pathConnectedSpace_iff_subsingleton_pi1 v).2 (hS 1 (by omega))
  have : PathConnectedSpace (MooreLoopSpace (ComplexProjectiveSpace n) (mk n v)) :=
    (MooreLoopSpace.pathConnectedSpace_iff_subsingleton_pi1 _).2
      (HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.subsingleton_congr.2 inferInstance)
  rw [ContinuousMap.isWeakHomotopyEquivalence_iff_forall_bijective (1, 1)]
  intro k
  -- The product sends the base point to the unit; the homotopy groups are compared there.
  have h1 : hopfProduct v j (1, 1) = 1 := by simp [hj]
  have key : ∀ {y} (h : hopfProduct v j (1, 1) = y),
      Function.Bijective (HomotopyGroup.map (N := Fin k) (x := (1, 1)) (hopfProduct v j) h) →
        Function.Bijective
          (HomotopyGroup.map (N := Fin k) (x := (1, 1)) (hopfProduct v j) rfl) := by
    rintro y rfl hb
    exact hb
  refine key h1 ?_
  rcases k with _ | _ | k
  · -- Degree zero: both spaces are path connected.
    have := (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero ((1, 1) :
      Circle × MooreLoopSpace (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) v)).1 inferInstance
    have := (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero
      (1 : MooreLoopSpace (ComplexProjectiveSpace n) (mk n v))).1 inferInstance
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  · -- Degree one: `π₁(ΩS²ⁿ⁺¹) = π₂(S²ⁿ⁺¹)` vanishes and `j` is bijective.
    have := (MooreLoopSpace.subsingleton_homotopyGroup_iff v 1).2 (hS 2 (by omega))
    exact HomotopyGroup.bijective_map_mul_of_bijective_of_subsingleton hj
      (map_one (MooreLoopSpace.map _ _))
      ((HomotopyGroup.bijective_map_iff_bijective_mapOfEq j hj).2 hjb)
  · -- Degrees `k + 2 ≥ 2`: the higher homotopy groups of the circle vanish.
    -- The loop-space shift identifies `(Ωq)_*` on `πₖ₊₂` with `q_*` on `πₖ₊₃`, an isomorphism.
    exact HomotopyGroup.bijective_map_mul_of_subsingleton_of_bijective hj
      (map_one (MooreLoopSpace.map _ _))
      ((MooreLoopSpace.bijective_homotopyGroup_map_iff _ rfl (k + 1)).2
        ((HomotopyGroup.bijective_map_iff_of_equiv _ rfl (finSuccEquiv (k + 2)).symm).1
          (bijective_homotopyGroupMap_mk (N := Fin (k + 2)) v)))

variable (v) in
/-- For `n ≥ 1`, `π₁(ΩCPⁿ) ≅ ℤ`: the loop-space shift gives `π₁(ΩCPⁿ) ≅ π₂(CPⁿ)`, the boundary map
of the Hopf fibration gives `π₂(CPⁿ) ≅ π₁(S¹)`, and `π₁(S¹) ≅ ℤ` by the degree. -/
def mooreLoopSpaceFundamentalGroupMulEquiv (hn : n ≠ 0) :
    FundamentalGroup (MooreLoopSpace (ComplexProjectiveSpace n) (mk n v)) 1 ≃*
      Multiplicative ℤ :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm.trans <|
    (MooreLoopSpace.homotopyGroupMulEquiv (mk n v) 0).trans <|
    (HomotopyGroup.congrMulEquiv (finSuccEquiv 1)).trans <|
    (hopfBoundaryMulEquiv v (N := Fin 1) (by simp; omega)).trans <|
    (HomotopyGroup.homeomorphMulEquivOfEq Circle.homeomorphSphere.symm (by ext; simp)).trans <|
    HomotopyGroup.pi1MulEquivFundamentalGroup.trans (Circle.fundamentalGroupMulEquiv 1)

/-- The isomorphism `π₁(ΩCPⁿ) ≃* ℤ` evaluated on a class `a`: shift `a` to `π₂(CPⁿ)` by the Moore
loop-space shift, apply the boundary map of the Hopf fibration to land in `π₁(S¹)`, and take the
degree of the resulting loop of the circle. -/
theorem mooreLoopSpaceFundamentalGroupMulEquiv_apply (hn : n ≠ 0)
    (a : FundamentalGroup (MooreLoopSpace (ComplexProjectiveSpace n) (mk n v)) 1) :
    mooreLoopSpaceFundamentalGroupMulEquiv v hn a =
      Circle.fundamentalGroupMulEquiv 1 (HomotopyGroup.pi1MulEquivFundamentalGroup
        (HomotopyGroup.map ⟨Circle.homeomorphSphere.symm, Homeomorph.continuous _⟩
          (by ext; simp)
          (hopfBoundary v (Fin 1) (HomotopyGroup.congrEquiv (finSuccEquiv 1)
            (MooreLoopSpace.homotopyGroupMulEquiv (mk n v) 0
              (HomotopyGroup.pi1MulEquivFundamentalGroup.symm a)))))) := by
  simp [mooreLoopSpaceFundamentalGroupMulEquiv]

variable (v) in
/-- **The based Hopf product realizes the splitting.** For `n ≥ 1` there is a based map
`j : S¹ → ΩCPⁿ` for which `j ⋆ Ωq : S¹ × ΩS²ⁿ⁺¹ → ΩCPⁿ` is a weak homotopy equivalence: a
generating loop of `π₁(ΩCPⁿ) ≅ ℤ`, read as a map from the circle. -/
theorem exists_isWeakHomotopyEquivalence_hopfProduct (hn : n ≠ 0) :
    ∃ j : C(Circle, MooreLoopSpace (ComplexProjectiveSpace n) (mk n v)),
      j 1 = 1 ∧ (hopfProduct v j).IsWeakHomotopyEquivalence :=
  ⟨_, Path.toCircle_one _, isWeakHomotopyEquivalence_hopfProduct hn _
    (Circle.bijective_mapOfEq_toCircle_out_symm_ofAdd_one
      (mooreLoopSpaceFundamentalGroupMulEquiv v hn))⟩

end TauCeti.ComplexProjectiveSpace
