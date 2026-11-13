/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Abundant

import Mathlib.Analysis.Quaternion
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.AlgebraicTopology.Sphere.Puncture
import TauCeti.Topology.MappingSpace.Sphere.Group

/-!
# The three-sphere is abundant with 2-spheres

The unit sphere `S³` of a real normed space of dimension `4` is abundant with 2-spheres
(`TauCeti.IsAbundantWithTwoSpheres`) at every point, with coefficients isomorphic to `ℤ`
(`TauCeti.isAbundantWithTwoSpheres_sphere`). This is the first example of Barraud, Damian,
Humilière and Oancea after their Definition 6.11.

By invariance of abundance under homeomorphisms and coefficient isomorphisms, it suffices to treat
the unit sphere `S³ ⊆ ℍ` at `1` with coefficients `ℤ`. As `S³` is a topological group,
`Map(S², S³) ≃ₜ S³ × Ω²S³` over `S³` (`TauCeti.sphereGroupHomeomorphIteratedLoopSpace`), and a
homeomorphism carries the right sphere to `1`. The local homology of the projection
`S³ × Ω²S³ → S³` along the fibre over `1` is
`H₄(S³ × Ω²S³, (S³ ∖ {1}) × Ω²S³) ≅ H₁(Ω²S³; ℤ) ≅ π₃(S³) ≅ ℤ`
(`TauCeti.TopCat.singularHomologyComplFiberIso`,
`TauCeti.doubleLoopSpaceFirstHomologySphereAddEquiv`), and the localization onto it is onto
because `S³ ∖ {1}` is contractible (`TauCeti.epi_fiberLocalization_fst`). So some class of degree
`4 > 3` lives over the fundamental class.

## Main results

* `TauCeti.isAbundantWithTwoSpheres_sphere`: the unit sphere of a real normed space of
  dimension `4` is abundant with 2-spheres at every point, with coefficients isomorphic to `ℤ`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 6.11 and the examples after it.
-/

public section

noncomputable section

open CategoryTheory Set Metric Topology AlgebraicTopology Quaternion
open scoped Topology.Homotopy

namespace TauCeti

private local instance : Fact (Module.finrank ℝ ℍ = 3 + 1) := ⟨Quaternion.finrank_eq_four⟩

/-- The unit sphere of the quaternions is abundant with 2-spheres at `1`, with integer
coefficients, through a class of degree `4`. -/
private theorem isAbundantWithTwoSpheres_sphere_quaternion_one :
    IsAbundantWithTwoSpheres (ModuleCat.of ℤ ℤ) (1 : sphere (0 : ℍ) 1) := by
  let F : Type := Ω (Ω (sphere (0 : ℍ) 1) 1) (Path.refl 1)
  -- The local homology `H₄(S³ × F, (S³ ∖ {1}) × F)` along the fibre over `1` is `H₁` of that
  -- fibre, which is `H₁(Ω²S³) ≅ ℤ`.
  have hloc : Nontrivial (localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ)
      (Prod.fst ⁻¹' {(1 : sphere (0 : ℍ) 1)} : Set (sphere (0 : ℍ) 1 × F)) 4) := by
    let fib : (Prod.fst ⁻¹' {(1 : sphere (0 : ℍ) 1)} : Set (sphere (0 : ℍ) 1 × F)) ≃ₜ F :=
      { toFun := fun x ↦ x.1.2
        invFun := fun ω ↦ ⟨(1, ω), rfl⟩
        left_inv := fun x ↦ Subtype.ext (Prod.ext x.2.symm rfl)
        right_inv := fun _ ↦ rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    let ob : OrthonormalBasis (Fin 4) ℝ ℍ :=
      (stdOrthonormalBasis ℝ ℍ).reindex (finCongr (Quaternion.finrank_eq_four (R := ℝ)))
    have : Nontrivial (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of F)) :=
      (doubleLoopSpaceFirstHomologySphereAddEquiv ob 1).toEquiv.nontrivial
    let p : TopCat.of (sphere (0 : ℍ) 1 × F) ⟶ TopCat.of (sphere (0 : ℍ) 1) :=
      TopCat.ofHom ContinuousMap.fst
    have hp : TopCat.serreFibrations p :=
      TopCat.mem_serreFibrations_fst (B := TopCat.of (sphere (0 : ℍ) 1)) (F := TopCat.of F)
    let φ := TopCat.singularHomologyComplFiberIso ℤ
      (chartAt (EuclideanSpace ℝ (Fin 3)) (1 : sphere (0 : ℍ) 1))
      (mem_chart_source (EuclideanSpace ℝ (Fin 3)) (1 : sphere (0 : ℍ) 1)) hp 1 4 (by simp)
    let ψ := ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo (X := TopCat.of (p ⁻¹' {(1 : sphere (0 : ℍ) 1)})) (Y := TopCat.of F) fib)
    exact (φ ≪≫ ψ).toLinearEquiv.toEquiv.nontrivial
  have : ContractibleSpace ({1}ᶜ : Set (sphere (0 : ℍ) 1)) :=
    contractibleSpace_sphere_compl_singleton 1
  obtain ⟨y, hy⟩ := exists_ne (0 : (localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ)
    (Prod.fst ⁻¹' {(1 : sphere (0 : ℍ) 1)} : Set (sphere (0 : ℍ) 1 × F)) 4 : ModuleCat.{0} ℤ))
  obtain ⟨α, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (epi_fiberLocalization_fst (ModuleCat.of ℤ ℤ) (F := F) (1 : sphere (0 : ℍ) 1) 4) y
  -- Transport `α` along `S³ × Ω²S³ ≃ₜ Map(S², S³)`, whose inverse is evaluation at the north
  -- pole on the first factor.
  let h : sphere (0 : ℍ) 1 × F ≃ₜ C(Sphere2, sphere (0 : ℍ) 1) :=
    sphereGroupHomeomorphIteratedLoopSpace 2 _ Sphere2.north
  have hfib : h.symm ⁻¹' (Prod.fst ⁻¹' {1}) ⊆ mappingSpaceEval Sphere2.north ⁻¹' {1} :=
    fun f hf ↦ by
      rw [mem_preimage, mappingSpaceEval_apply,
        ← sphereGroupHomeomorphIteratedLoopSpace_symm_fst (k := 2) (s₀ := Sphere2.north) f]
      exact hf
  refine isAbundantWithTwoSpheres_of_livesOverFundamentalClass_of_lt
    (E := EuclideanSpace ℝ (Fin 3)) (by simp)
    (α := (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom
      (h : C(sphere (0 : ℍ) 1 × F, C(Sphere2, sphere (0 : ℍ) 1))))) (ModuleCat.of ℤ ℤ) 4).hom α) ?_
  refine LivesOverFundamentalClass.of_homologyMap _
    (h.symm : C(C(Sphere2, sphere (0 : ℍ) 1), sphere (0 : ℍ) 1 × F)) hfib ?_
  rw [homologyMap_comp_homologyMap_of_comp_eq_id_apply _ _ _
    (ContinuousMap.ext h.symm_apply_apply) 4]
  exact (livesOverFundamentalClass_iff _ _ _ _).2 hy

/-- **The three-sphere is abundant with 2-spheres.** The unit sphere of a real normed space of
dimension `4` is abundant with 2-spheres at every point `b`, with coefficients `R` isomorphic to
`ℤ`: some class of `H₄(Map(S², S³); R)` lives over the fundamental class at `b`, and `4 > 3`. -/
theorem isAbundantWithTwoSpheres_sphere {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : Module.finrank ℝ E = 4) (b : sphere (0 : E) 1) {R : ModuleCat.{0} ℤ}
    (e : R ≅ ModuleCat.of ℤ ℤ) : IsAbundantWithTwoSpheres R b := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  let φ : sphere (0 : E) 1 ≃ₜ sphere (0 : ℍ) 1 :=
    sphereHomeomorphOfFinrankEq (hE.trans Quaternion.finrank_eq_four.symm)
  -- A homeomorphism `S³ ≃ₜ sphere (0 : E) 1` sending `1` to `b`.
  let ψ : sphere (0 : ℍ) 1 ≃ₜ sphere (0 : E) 1 := (Homeomorph.mulLeft (φ b)).trans φ.symm
  have hψ : ψ 1 = b := by simp [ψ]
  rw [e.isAbundantWithTwoSpheres_iff, ← hψ]
  exact isAbundantWithTwoSpheres_sphere_quaternion_one.homeomorph ψ

end TauCeti
