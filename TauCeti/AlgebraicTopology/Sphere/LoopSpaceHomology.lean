/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.Fibration.Sphere
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.Topology.Homotopy.MappingPath.PathFibration
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic

/-!
# The homology of the loop space of a sphere

Let `Sⁿ` be the unit sphere of an `(n + 1)`-dimensional real inner product space, `n ≥ 2`, and
`ΩSⁿ` its loop space at a point `x`. With coefficients in any ring `R`, the singular homology of
`ΩSⁿ` is a copy of `R` in every degree divisible by `n - 1` and vanishes in every other degree:

* `H_m(ΩSⁿ; R) = 0` if `n - 1` does not divide `m`
  (`TauCeti.isZero_singularHomology_loopSpace_sphere_of_not_dvd`);
* `H_{j(n - 1)}(ΩSⁿ; R) ≅ R` for every `j`
  (`TauCeti.nonempty_singularHomology_loopSpace_sphere_iso`).

Both hold for the loop space `Ω Sⁿ x = Path x x` on the unit interval and for the Moore loop space
(`TauCeti.isZero_singularHomology_mooreLoopSpace_sphere_of_not_dvd`,
`TauCeti.nonempty_singularHomology_mooreLoopSpace_sphere_iso`), which is homotopy equivalent to it.

## The argument

The paths in `Sⁿ` ending at `x` form a contractible space `P`, and sending a path to its starting
point is a Hurewicz fibration `P → Sⁿ` (`TauCeti.MappingPathFiber.isHurewiczFibration_proj`). Its
fibre over `x` is `ΩSⁿ`, and its fibre over the antipode `-x` is the space of paths from `-x` to
`x`, homotopy equivalent to `ΩSⁿ` by prepending a fixed path from `x` to `-x`
(`TauCeti.MappingPathFiber.projFiberHomotopyEquivLoopSpace`). The Wang isomorphism of a Serre
fibration over a sphere with acyclic total space (`TauCeti.TopCat.sphereFiberWangIso`) then gives
`H_{k+1}(ΩSⁿ) ≅ H_m(ΩSⁿ)` whenever `m + n = k + 2`, that is, a shift of the degree by `n - 1`
(`TauCeti.singularHomologyLoopSpaceSphereShiftIso`). Starting from `H_0(ΩSⁿ) ≅ R`, as `ΩSⁿ` is
path connected, and from the vanishing of `H_k(ΩSⁿ)` for `1 ≤ k ≤ n - 2`, as `ΩSⁿ` is
`(n - 2)`-connected (`TauCeti.isZero_singularHomology_mooreLoopSpace_sphere`), induction on the
degree computes all the groups.

This is the additive part of the Bott–Samelson computation `H_*(ΩSⁿ; R) ≅ R[x_{n-1}]`; the
multiplicative structure is not treated here.

## Main results

* `TauCeti.singularHomologyLoopSpaceSphereShiftIso`: `H_{k+1}(ΩSⁿ; R) ≅ H_m(ΩSⁿ; R)` for
  `m + n = k + 2`.
* `TauCeti.isZero_singularHomology_loopSpace_sphere_of_not_dvd`: `H_m(ΩSⁿ; R) = 0` unless
  `n - 1 ∣ m`.
* `TauCeti.nonempty_singularHomology_loopSpace_sphere_iso`: `H_{j(n - 1)}(ΩSⁿ; R) ≅ R`.
* `TauCeti.isZero_singularHomology_mooreLoopSpace_sphere_of_not_dvd`,
  `TauCeti.nonempty_singularHomology_mooreLoopSpace_sphere_iso`: the same for Moore loops.

## References

* H.-C. Wang, *The homology groups of the fibre bundles over a sphere*, Duke Math. J. 16 (1949),
  33–38.
* R. Bott, H. Samelson, *On the Pontryagin product in spaces of paths*, Comment. Math. Helv. 27
  (1953), 320–337.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module Set Topology
open scoped Topology.Homotopy

universe u

namespace TauCeti

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (finrank ℝ V = n + 1)] (R : Type u) [Ring R]

/-- The fibration of paths in `Sⁿ` ending at `x`, by their starting point. -/
private abbrev pathProj (x : sphere (0 : V) 1) :
    _root_.TopCat.of (MappingPathFiber (ContinuousMap.id (sphere (0 : V) 1)) x) ⟶
      _root_.TopCat.of (sphere (0 : V) 1) :=
  _root_.TopCat.ofHom (MappingPathFiber.proj (ContinuousMap.id (sphere (0 : V) 1)) x)

omit [InnerProductSpace ℝ V] in
private theorem mem_serreFibrations_pathProj (x : sphere (0 : V) 1) :
    TopCat.serreFibrations (pathProj x) :=
  IsHurewiczFibration.mem_serreFibrations (MappingPathFiber.isHurewiczFibration_proj.{u} _ x)

omit [InnerProductSpace ℝ V] in
/-- The space of paths ending at `x` is contractible, so it has the homology of a point. -/
private theorem isZero_singularHomology_pathProj (x : sphere (0 : V) 1) (k : ℕ) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
      (ModuleCat.of R R)).obj
        (_root_.TopCat.of (MappingPathFiber (ContinuousMap.id (sphere (0 : V) 1)) x))) :=
  isZero_singularHomologyFunctor_of_contractibleSpace _ _ k.succ_ne_zero

/-- The sphere of a space of dimension at least `2` is path connected. -/
private theorem pathConnectedSpace_sphere (hn : n ≠ 0) : PathConnectedSpace (sphere (0 : V) 1) :=
  isPathConnected_iff_pathConnectedSpace.1 <| isPathConnected_sphere
    (by
      have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
      rw [← finrank_eq_rank, (Fact.out : finrank ℝ V = n + 1)]
      exact_mod_cast (show 1 < n + 1 by omega))
    0 zero_le_one

/-- **The homology of the loop space of a sphere is periodic.** For the unit sphere `Sⁿ` of an
`(n + 1)`-dimensional real inner product space, `n ≥ 1`, and `m + n = k + 2`,
`H_{k+1}(ΩSⁿ; R) ≅ H_m(ΩSⁿ; R)`: the degree drops by `n - 1`. This is the Wang isomorphism of the
path fibration of `Sⁿ`, whose total space is contractible. -/
def singularHomologyLoopSpaceSphereShiftIso (hn : n ≠ 0) (x : sphere (0 : V) 1) (k m : ℕ)
    (h : m + n = k + 2) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (Ω (sphere (0 : V) 1) x)) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (Ω (sphere (0 : V) 1) x)) :=
  have := pathConnectedSpace_sphere (V := V) hn
  ((MappingPathFiber.projFiberHomotopyEquivLoopSpace (ContinuousMap.id _) x (-x)
      (PathConnectedSpace.somePath _ _)).singularHomologyIso (ModuleCat.of R R) (k + 1)).symm ≪≫
    TopCat.sphereFiberWangIso R (mem_serreFibrations_pathProj x)
      (isZero_singularHomology_pathProj R x) (ne_neg_of_mem_unit_sphere ℝ x).symm k m h ≪≫
    (MappingPathFiber.projFiberHomotopyEquivLoopSpace (ContinuousMap.id _) x x
      (Path.refl x)).singularHomologyIso (ModuleCat.of R R) m

/-- **The homology of the loop space of a sphere vanishes outside the multiples of `n - 1`.** For
the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space, `n ≥ 2`,
`H_m(ΩSⁿ; R) = 0` whenever `n - 1` does not divide `m`. -/
theorem isZero_singularHomology_loopSpace_sphere_of_not_dvd (hn : 2 ≤ n) (x : sphere (0 : V) 1)
    {m : ℕ} (hm : ¬ (n - 1) ∣ m) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (Ω (sphere (0 : V) 1) x))) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m (n - 1) with hlt | hge
    · -- Below `n - 1`, `m` is positive, and the homology vanishes in low degrees.
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hm (dvd_zero _)
      exact (isZero_singularHomology_mooreLoopSpace_sphere (Fact.out : finrank ℝ V = n + 1) x R
        hm0 (by omega)).of_iso
          ((MooreLoopSpace.homotopyEquivPath x).singularHomologyIso (ModuleCat.of R R) m).symm
    · -- From `n - 1` on, shift the degree down by `n - 1`.
      obtain ⟨d, rfl⟩ : ∃ d, m = d + (n - 1) := ⟨m - (n - 1), by omega⟩
      have hd : ¬ (n - 1) ∣ d := fun h ↦ hm (h.add dvd_rfl)
      obtain ⟨k, hk⟩ : ∃ k, d + (n - 1) = k + 1 := ⟨d + (n - 1) - 1, by omega⟩
      rw [hk]
      exact (ih d (by omega) hd).of_iso
        (singularHomologyLoopSpaceSphereShiftIso (n := n) R (by omega) x k d (by omega))

/-- The loop space of a sphere of dimension at least `2` is path connected. -/
private theorem pathConnectedSpace_loopSpace_sphere (hn : 2 ≤ n) (x : sphere (0 : V) 1) :
    PathConnectedSpace (Ω (sphere (0 : V) 1) x) :=
  (pathConnectedSpace_loopSpace_iff_subsingleton_pi1 x).2 <|
    subsingleton_homotopyGroup_sphere_of_lt (Fact.out : finrank ℝ V = n + 1)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) x

/-- **The homology of the loop space of a sphere in the multiples of `n - 1`.** For the unit
sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space, `n ≥ 2`,
`H_{j(n - 1)}(ΩSⁿ; R) ≅ R` for every `j`. -/
theorem nonempty_singularHomology_loopSpace_sphere_iso (hn : 2 ≤ n) (x : sphere (0 : V) 1)
    (j : ℕ) :
    Nonempty ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (j * (n - 1))).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (Ω (sphere (0 : V) 1) x))) ≅
      ModuleCat.of R R) := by
  induction j with
  | zero =>
    have := pathConnectedSpace_loopSpace_sphere hn x
    rw [zero_mul]
    exact ⟨asIso ((_root_.TopCat.of (Ω (sphere (0 : V) 1) x)).singularHomology₀ε
      (ModuleCat.of R R))⟩
  | succ j ih =>
    obtain ⟨k, hk⟩ : ∃ k, (j + 1) * (n - 1) = k + 1 := Nat.exists_eq_add_one.2 (by
      rw [add_mul, one_mul]; omega)
    obtain ⟨e⟩ := ih
    rw [hk]
    exact ⟨singularHomologyLoopSpaceSphereShiftIso (n := n) R (by omega) x k _ (by
      rw [add_mul, one_mul] at hk
      generalize j * (n - 1) = a at hk ⊢
      omega) ≪≫ e⟩

/-- **The homology of the Moore loop space of a sphere vanishes outside the multiples of
`n - 1`.** For the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space,
`n ≥ 2`, `H_m(ΩSⁿ; R) = 0` for the Moore loop space whenever `n - 1` does not divide `m`. -/
theorem isZero_singularHomology_mooreLoopSpace_sphere_of_not_dvd (hn : 2 ≤ n)
    (x : sphere (0 : V) 1) {m : ℕ} (hm : ¬ (n - 1) ∣ m) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (MooreLoopSpace (sphere (0 : V) 1) x))) :=
  (isZero_singularHomology_loopSpace_sphere_of_not_dvd R hn x hm).of_iso
    ((MooreLoopSpace.homotopyEquivPath x).singularHomologyIso (ModuleCat.of R R) m)

/-- **The homology of the Moore loop space of a sphere in the multiples of `n - 1`.** For the
unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space, `n ≥ 2`,
`H_{j(n - 1)}(ΩSⁿ; R) ≅ R` for the Moore loop space, for every `j`. -/
theorem nonempty_singularHomology_mooreLoopSpace_sphere_iso (hn : 2 ≤ n) (x : sphere (0 : V) 1)
    (j : ℕ) :
    Nonempty ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (j * (n - 1))).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (MooreLoopSpace (sphere (0 : V) 1) x))) ≅
      ModuleCat.of R R) :=
  (nonempty_singularHomology_loopSpace_sphere_iso R hn x j).map
    ((MooreLoopSpace.homotopyEquivPath x).singularHomologyIso (ModuleCat.of R R) _ ≪≫ ·)

end TauCeti
