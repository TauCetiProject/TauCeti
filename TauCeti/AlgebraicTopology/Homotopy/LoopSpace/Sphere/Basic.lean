/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Sphere
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.Topology.Homotopy.MappingPath.Fiber
public import TauCeti.Topology.Homotopy.MappingPath.PathFibration
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic

/-!
# The homology of the loop space of a sphere

For `n ≥ 2` and the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real normed space, the singular
homology of the loop space `ΩSⁿ` with coefficients in a ring `R` is `R` in every degree divisible
by `n - 1` and zero in every other degree:

* `H_{k+n-1}(ΩSⁿ; R) ≅ H_k(ΩSⁿ; R)` for every `k`
  (`TauCeti.singularHomologyLoopSpaceSphereShiftIso`);
* `H_{j(n-1)}(ΩSⁿ; R) ≅ R` for every `j` (`TauCeti.singularHomologyLoopSpaceSphereIso`);
* `H_k(ΩSⁿ; R) = 0` when `n - 1` does not divide `k`
  (`TauCeti.isZero_singularHomology_loopSpace_sphere`).

The same holds for the Moore loop space, which is homotopy equivalent to the loop space on the unit
interval (`TauCeti.singularHomologyMooreLoopSpaceSphereShiftIso`,
`TauCeti.singularHomologyMooreLoopSpaceSphereIso` and
`TauCeti.isZero_singularHomology_mooreLoopSpace_sphere`).

The computation is the Wang sequence of the path fibration. The paths in `Sⁿ` ending at the base
point `x` form a contractible space `P`, and sending a path to its starting point is a Hurewicz
fibration `P → Sⁿ` (`TauCeti.MappingPathFiber.isHurewiczFibration_proj`) whose fibre over a point
`b` is the space of paths from `b` to `x`, homotopy equivalent to `ΩSⁿ`
(`TauCeti.MappingPathFiber.projFiberHomotopyEquivLoopSpace`). Read on the CW structure of the
sphere with one `0`-cell and one `n`-cell, the contractible total space gives
`H~_{k+n-1}(ΩSⁿ) ≅ H_k(ΩSⁿ)` (`TauCeti.TopCat.reducedSingularHomologySphereFibrationIso`) and
`H~_k(ΩSⁿ) = 0` for `k < n - 1`
(`TauCeti.TopCat.isZero_reducedSingularHomology_sphereFibration_of_lt`). Since `n - 1 ≥ 1`, reduced
and ordinary homology agree in the degrees `k + n - 1`, and the loop space is path-connected
because the sphere is simply connected (`TauCeti.pathConnectedSpace_loopSpace_sphere`), so
`H_0(ΩSⁿ; R) ≅ R`.

The hypothesis `n ≥ 2` is needed for the identification `H_0(ΩSⁿ; R) ≅ R`: the loop space of the
circle has one contractible path component for every integer, so `H_0(ΩS¹; R)` is a sum of copies
of `R` indexed by `ℤ`.

## References

* H.-C. Wang, *The homology groups of the fibre bundles over a sphere*, Duke Math. J. 16 (1949),
  33–38.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951).
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1 (the Wang sequence of a fibration over a sphere).
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Metric Module AlgebraicTopology
open scoped Topology Topology.Homotopy

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

section PathFibration

variable {m : ℕ} (hE : finrank ℝ E = m + 1 + 1) (x : sphere (0 : E) 1) (R : Type u) [Ring R]

/-- The model sphere `Sᵐ⁺¹` of `EuclideanSpace ℝ (ULift (Fin (m + 2)))`, which carries the CW
structure with one `0`-cell and one `(m + 1)`-cell. -/
private abbrev ModelSphere (m : ℕ) : Type u :=
  sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin (m + 1 + 1)))) 1

private lemma card_ulift_fin : Fintype.card (ULift.{u} (Fin (m + 1 + 1))) = m + 1 + 1 :=
  (Fintype.card_ulift _).trans (Fintype.card_fin _)

include hE in
/-- The unit sphere of `E` is homeomorphic to the model sphere. -/
private def modelHomeomorph : sphere (0 : E) 1 ≃ₜ ModelSphere.{u} m :=
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  sphereHomeomorphOfFinrankEq (by simp [hE])

/-- The path fibration of the sphere, read on the model sphere: a path in `sphere 0 1` ending at
`x` is sent to its starting point, transported to the model sphere. -/
private abbrev pathProj :
    _root_.TopCat.of (MappingPathFiber (ContinuousMap.id (sphere (0 : E) 1)) x) ⟶
      _root_.TopCat.of (ModelSphere.{u} m) :=
  _root_.TopCat.ofHom (MappingPathFiber.proj (ContinuousMap.id (sphere (0 : E) 1)) x) ≫
    (_root_.TopCat.isoOfHomeo (modelHomeomorph hE)).hom

private lemma serreFibrations_pathProj : TopCat.serreFibrations (pathProj hE x) :=
  MorphismProperty.RespectsIso.postcomp TopCat.serreFibrations _ _
    (MappingPathFiber.isHurewiczFibration_proj.{0} (ContinuousMap.id (sphere (0 : E) 1))
      x).mem_serreFibrations

/-- The fibre of the path fibration over a point `b` of the model sphere is homotopy equivalent to
the loop space of the sphere at `x`. -/
private def pathProjFiberHomotopyEquiv (b : ModelSphere.{u} m) :
    ContinuousMap.HomotopyEquiv (pathProj hE x ⁻¹' {b}) (Ω (sphere (0 : E) 1) x) :=
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  have : PathConnectedSpace (sphere (0 : E) 1) := isPathConnected_iff_pathConnectedSpace.1 <|
    isPathConnected_sphere (by rw [← finrank_eq_rank, hE]; norm_cast; omega) 0 zero_le_one
  (Homeomorph.setCongr (t := {y | MappingPathFiber.proj (ContinuousMap.id (sphere (0 : E) 1)) x y =
      (modelHomeomorph hE).symm b}) (by
      ext y
      exact (modelHomeomorph hE).eq_symm_apply.symm)).toHomotopyEquiv.trans
    (MappingPathFiber.projFiberHomotopyEquivLoopSpace (ContinuousMap.id _) x
      ((modelHomeomorph hE).symm b) (PathConnectedSpace.somePath _ _))

/-- **The Wang isomorphism of the path fibration of a sphere**:
`H~_{k+m}(ΩSᵐ⁺¹; R) ≅ H_k(ΩSᵐ⁺¹; R)`. -/
private def reducedSingularHomologyLoopSpaceIso (k : ℕ) :
    (reducedSingularHomologyFunctor (ModuleCat.of R R) (k + m)).obj
        (_root_.TopCat.of (Ω (sphere (0 : E) 1) x)) ≅
      ((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (Ω (sphere (0 : E) 1) x)) :=
  ((pathProjFiberHomotopyEquiv hE x
      (spherePolePoint card_ulift_fin)).reducedSingularHomologyIso
      (ModuleCat.of R R) (k + m)).symm ≪≫
    TopCat.reducedSingularHomologySphereFibrationIso card_ulift_fin
      (serreFibrations_pathProj hE x) R k ≪≫
    (pathProjFiberHomotopyEquiv hE x
      (sphereTopCellCenter card_ulift_fin)).singularHomologyIso (ModuleCat.of R R) k

include hE in
/-- The reduced homology of `ΩSᵐ⁺¹` vanishes below degree `m`. -/
private lemma isZero_reducedSingularHomology_loopSpace {k : ℕ} (hk : k < m) :
    IsZero ((reducedSingularHomologyFunctor (ModuleCat.of R R) k).obj
      (_root_.TopCat.of (Ω (sphere (0 : E) 1) x))) :=
  (TopCat.isZero_reducedSingularHomology_sphereFibration_of_lt card_ulift_fin
      (serreFibrations_pathProj hE x) R (by omega)).of_iso
    ((pathProjFiberHomotopyEquiv hE x
      (spherePolePoint card_ulift_fin)).reducedSingularHomologyIso _ k).symm

end PathFibration

variable {n : ℕ} (hE : finrank ℝ E = n + 1) (hn : 2 ≤ n) (x : sphere (0 : E) 1)
  (R : Type u) [Ring R]

section LoopSpace

/-- **The homology of `ΩSⁿ` is periodic of period `n - 1`**:
`H_{k+n-1}(ΩSⁿ; R) ≅ H_k(ΩSⁿ; R)` for the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real normed
space, `n ≥ 2`, and every `k`. -/
def singularHomologyLoopSpaceSphereShiftIso (k : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) (k + (n - 1))).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (Ω (sphere (0 : E) 1) x)) ≅
      ((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (Ω (sphere (0 : E) 1) x)) :=
  -- Since `n - 1 ≥ 1`, reduced and ordinary homology agree in degree `k + n - 1`; the degree is
  -- rewritten as `k + (n - 2) + 1` to match `TauCeti.reducedSingularHomologySuccIso`.
  eqToIso (by rw [show k + (n - 1) = k + (n - 2) + 1 by omega]) ≪≫
    ((reducedSingularHomologySuccIso (ModuleCat.of R R) (k + (n - 2))).app _).symm ≪≫
    reducedSingularHomologyLoopSpaceIso (m := n - 2 + 1) (hE.trans (by omega)) x R k

/-- **The homology of `ΩSⁿ` in the degrees divisible by `n - 1`**:
`H_{j(n-1)}(ΩSⁿ; R) ≅ R` for the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real normed space,
`n ≥ 2`, and every `j`. In degree `0` this is the augmentation. -/
def singularHomologyLoopSpaceSphereIso : (j : ℕ) →
    ((singularHomologyFunctor (ModuleCat.{u} R) (j * (n - 1))).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (Ω (sphere (0 : E) 1) x)) ≅ ModuleCat.of R R
  | 0 =>
    have := pathConnectedSpace_loopSpace_sphere hE hn x
    eqToIso (by rw [zero_mul]) ≪≫
      asIso ((_root_.TopCat.of (Ω (sphere (0 : E) 1) x)).singularHomology₀ε (ModuleCat.of R R))
  | j + 1 =>
    eqToIso (by rw [Nat.succ_mul]) ≪≫ singularHomologyLoopSpaceSphereShiftIso hE hn x R _ ≪≫
      singularHomologyLoopSpaceSphereIso j

include hE hn in
/-- **The homology of `ΩSⁿ` vanishes in the degrees not divisible by `n - 1`**, with coefficients
in any ring, for the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real normed space, `n ≥ 2`. -/
theorem isZero_singularHomology_loopSpace_sphere {k : ℕ} (hk : ¬ (n - 1) ∣ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).obj
      (_root_.TopCat.of (Ω (sphere (0 : E) 1) x))) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hkn : k < n - 1
    · -- Below degree `n - 1` the reduced homology vanishes, and `k ≠ 0` since `n - 1 ∣ 0`.
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 :=
        ⟨k - 1, by have : k ≠ 0 := by rintro rfl; exact hk (dvd_zero _)
                   omega⟩
      exact (isZero_reducedSingularHomology_loopSpace (m := n - 2 + 1) (hE.trans (by omega)) x R
        (by omega)).of_iso ((reducedSingularHomologySuccIso (ModuleCat.of R R) k).app _).symm
    · -- Above it, `H_k ≅ H_{k-n+1}`.
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + (n - 1) := ⟨k - (n - 1), by omega⟩
      exact (ih k (by omega) fun h ↦ hk ((Nat.dvd_add_self_right).2 h)).of_iso
        (singularHomologyLoopSpaceSphereShiftIso hE hn x R k)

end LoopSpace

section MooreLoopSpace

/-- **The homology of the Moore loop space of `Sⁿ` is periodic of period `n - 1`**:
`H_{k+n-1}(ΩSⁿ; R) ≅ H_k(ΩSⁿ; R)` for the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real normed
space, `n ≥ 2`, and every `k`. -/
def singularHomologyMooreLoopSpaceSphereShiftIso (k : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) (k + (n - 1))).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (MooreLoopSpace (sphere (0 : E) 1) x)) ≅
      ((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (MooreLoopSpace (sphere (0 : E) 1) x)) :=
  (MooreLoopSpace.homotopyEquivPath x).singularHomologyIso _ _ ≪≫
    singularHomologyLoopSpaceSphereShiftIso hE hn x R k ≪≫
    ((MooreLoopSpace.homotopyEquivPath x).singularHomologyIso _ _).symm

/-- **The homology of the Moore loop space of `Sⁿ` in the degrees divisible by `n - 1`**:
`H_{j(n-1)}(ΩSⁿ; R) ≅ R` for the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real normed space,
`n ≥ 2`, and every `j`. -/
def singularHomologyMooreLoopSpaceSphereIso (j : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) (j * (n - 1))).obj (ModuleCat.of R R)).obj
        (_root_.TopCat.of (MooreLoopSpace (sphere (0 : E) 1) x)) ≅ ModuleCat.of R R :=
  (MooreLoopSpace.homotopyEquivPath x).singularHomologyIso _ _ ≪≫
    singularHomologyLoopSpaceSphereIso hE hn x R j

include hE hn in
/-- **The homology of the Moore loop space of `Sⁿ` vanishes in the degrees not divisible by
`n - 1`**, with coefficients in any ring, for the unit sphere `Sⁿ` of an `(n + 1)`-dimensional
real normed space, `n ≥ 2`. -/
theorem isZero_singularHomology_mooreLoopSpace_sphere {k : ℕ} (hk : ¬ (n - 1) ∣ k) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).obj
      (_root_.TopCat.of (MooreLoopSpace (sphere (0 : E) 1) x))) :=
  (isZero_singularHomology_loopSpace_sphere hE hn x R hk).of_iso
    ((MooreLoopSpace.homotopyEquivPath x).singularHomologyIso _ _)

end MooreLoopSpace

end TauCeti
