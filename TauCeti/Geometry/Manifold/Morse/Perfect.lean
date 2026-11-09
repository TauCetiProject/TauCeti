/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.Geometry.Manifold.Morse.Inequalities
public import TauCeti.Geometry.Manifold.Morse.Projectivization
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.FundamentalGroup.Basic
import TauCeti.Geometry.Manifold.Morse.Reeb

/-!
# Perfect Morse functions

A Morse function `f` on a manifold `M` is **perfect** with coefficients in a division ring `k`
(`TauCeti.IsPerfectMorse`) if, in every degree `n`, its number `cₙ` of critical points of index `n`
equals the dimension `bₙ` of the singular homology `Hₙ(M; k)`. By the weak Morse inequalities
`bₙ ≤ cₙ`, a perfect Morse function has the fewest critical points of each index among all Morse
functions on a compact manifold (`TauCeti.IsPerfectMorse.criticalCount_le`), and so the fewest
critical points altogether (`TauCeti.IsPerfectMorse.totalCriticalCount_le`): their number is the
total Betti number (`TauCeti.IsPerfectMorse.totalCriticalCount_eq`). Whether a perfect
Morse function exists depends on the coefficients, as projective spaces show.

* **The lacunary principle.** A Morse function on a compact manifold no two of whose critical
  points have indices differing by one is perfect for every choice of coefficients
  (`TauCeti.IsMorse.isPerfectMorse_of_forall_ne_add_one`). On `ℂℙⁿ` the moment function
  `[z] ↦ (∑ⱼ wⱼ |zⱼ|²) / ∑ⱼ |zⱼ|²` with pairwise distinct weights has only even indices, so it is
  perfect for every division ring of coefficients
  (`TauCeti.isPerfectMorse_projectiveMomentFunction_complex`).
* **Real projective space in characteristic two.** On `ℝPᴺ` the same moment function has one
  critical point of each index `0, …, N`, and `Hⱼ(ℝPᴺ; k)` is one-dimensional for `j ≤ N` when
  `2 = 0` in `k`. So the moment function is perfect over `ℤ/2`
  (`TauCeti.isPerfectMorse_projectiveMomentFunction_real`).
* **No perfect Morse function over `ℚ`.** Every Morse function on a nonempty compact manifold of
  dimension `m` has a critical point of index `m`, at a point of maximum
  (`TauCeti.IsMorse.criticalCount_finrank_ne_zero`), so a perfect Morse function forces the top
  homology to be nonzero (`TauCeti.IsPerfectMorse.finrank_singularHomology_finrank_ne_zero`).
  For `N ≥ 2`, no Morse function on `ℝPᴺ` is perfect over `ℚ`, or over any division ring in
  which `2 ≠ 0` (`TauCeti.not_isPerfectMorse_projectivization_real`). Over such a ring the Betti
  numbers of `ℝPᴺ` are `1` in degree `0`, `1` in degree `N` for odd `N`, and `0` otherwise, so a
  perfect Morse function would have at most two critical points. A function on a compact manifold
  with at least two points has at least two critical points, and by Reeb's theorem
  (`TauCeti.IsMorse.nonempty_homeomorph_sphere_of_totalCriticalCount_eq_two`) a Morse function
  with exactly two makes `ℝPᴺ` homeomorphic to the sphere `Sᴺ`. This is impossible for `N ≥ 2`,
  since `Sᴺ` is simply connected and `ℝPᴺ` is not. On `ℝP²` the moment function with three
  distinct weights has three critical points, of indices `0`, `1` and `2`; the Betti numbers are
  `1, 1, 1` over `ℤ/2` but `1, 0, 0` over `ℚ`.

## Main declarations

* `TauCeti.IsPerfectMorse`: a Morse function whose critical counts are the Betti numbers.
* `TauCeti.IsPerfectMorse.totalCriticalCount_eq`: the number of critical points of a perfect Morse
  function is the total Betti number.
* `TauCeti.IsMorse.isPerfectMorse_of_forall_ne_add_one`: the lacunary principle.
* `TauCeti.isPerfectMorse_projectiveMomentFunction_complex` and
  `TauCeti.isPerfectMorse_projectiveMomentFunction_real`: perfect moment functions on `ℂℙⁿ`, and on
  `ℝPⁿ` in characteristic two.
* `TauCeti.not_isPerfectMorse_projectivization_real`: for `N ≥ 2` no Morse function on `ℝPᴺ` is
  perfect over a division ring in which `2 ≠ 0`.

## References

* R. Bott, *Lectures on Morse theory, old and new*, Bull. Amer. Math. Soc. (N.S.) 7 (1982),
  331–358, §1 (perfect Morse functions and the lacunary principle).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §5 (the Morse inequalities) and §4 (the example of `ℂℙⁿ`).
-/

public section

open CategoryTheory Limits Module Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f g : M → ℝ}

/-! ### Perfect Morse functions -/

variable (I) in
/-- A **perfect Morse function** with coefficients in a division ring `k`: a Morse function `f`
on `M` such that, in every degree `n`, the singular homology `Hₙ(M; k)` is finite-dimensional and
its dimension is the number of critical points of `f` of index `n`. -/
structure IsPerfectMorse (k : Type u) [DivisionRing k] (f : M → ℝ) : Prop where
  /-- A perfect Morse function is a Morse function. -/
  isMorse : IsMorse I f
  /-- The singular homology of `M` with coefficients in `k` is finite-dimensional. -/
  finite_singularHomology (n : ℕ) : Module.Finite k
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj
      (TopCat.of M))
  /-- The number of critical points of index `n` is the dimension of `Hₙ(M; k)`. -/
  criticalCount_eq (n : ℕ) : criticalCount I f n =
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj
      (ModuleCat.of k k)).obj (TopCat.of M))

section Compact

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {k : Type u} [DivisionRing k]

/-- On a compact manifold, a perfect Morse function is a Morse function whose number of critical
points of each index `n` is the dimension of `Hₙ(M; k)`; the finite-dimensionality of homology is
then automatic. -/
theorem isPerfectMorse_iff : IsPerfectMorse I k f ↔ IsMorse I f ∧ ∀ n, criticalCount I f n =
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj
      (ModuleCat.of k k)).obj (TopCat.of M)) :=
  ⟨fun h ↦ ⟨h.isMorse, h.criticalCount_eq⟩,
    fun h ↦ ⟨h.1, h.1.finite_singularHomology (ModuleCat.of k k), h.2⟩⟩

/-- **A perfect Morse function has the fewest critical points of each index.** If `f` is a perfect
Morse function on a compact manifold, every Morse function `g` has at least as many critical
points of each index as `f`. -/
theorem IsPerfectMorse.criticalCount_le (hf : IsPerfectMorse I k f) (hg : IsMorse I g) (n : ℕ) :
    criticalCount I f n ≤ criticalCount I g n := by
  have h := hg.finrank_singularHomology_le (ModuleCat.of k k) n
  rw [ModuleCat.finrank_of_self, mul_one] at h
  rw [hf.criticalCount_eq]
  exact (Nat.cast_le.2 h).trans (ENat.natCast_toNat_le_self _)

/-- **A perfect Morse function has the fewest critical points.** If `f` is a perfect Morse
function on a compact manifold, every Morse function `g` has at least as many critical points
as `f`. -/
theorem IsPerfectMorse.totalCriticalCount_le (hf : IsPerfectMorse I k f) (hg : IsMorse I g) :
    totalCriticalCount I f ≤ totalCriticalCount I g := by
  rw [← sum_criticalCount_eq_totalCriticalCount, ← sum_criticalCount_eq_totalCriticalCount]
  exact Finset.sum_le_sum fun n _ ↦ hf.criticalCount_le hg n

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] in
/-- **The number of critical points of a perfect Morse function** is the total Betti number
`∑ₙ dim_k Hₙ(M; k)`, the sum running over the degrees `n ≤ dim M`. -/
theorem IsPerfectMorse.totalCriticalCount_eq (hf : IsPerfectMorse I k f) :
    totalCriticalCount I f = ∑ n ∈ Finset.range (finrank ℝ E + 1),
      (finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj
        (ModuleCat.of k k)).obj (TopCat.of M)) : ℕ∞) := by
  rw [← sum_criticalCount_eq_totalCriticalCount]
  exact Finset.sum_congr rfl fun n _ ↦ hf.criticalCount_eq n

/-- **The lacunary principle.** A Morse function on a compact manifold such that no two critical
points have indices differing by one is perfect, for every division ring of coefficients. -/
theorem IsMorse.isPerfectMorse_of_forall_ne_add_one (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) :
    IsPerfectMorse I k f := by
  refine isPerfectMorse_iff.2 ⟨hf, fun n ↦ ?_⟩
  rw [hf.finrank_singularHomology_eq_of_forall_ne_add_one (ModuleCat.of k k) hind n,
    ModuleCat.finrank_of_self, mul_one,
    ENat.natCast_toNat_eq_self.2 (hf.criticalCount_ne_top n)]

omit [IsManifold I ∞ M] [T2Space M] in
/-- **A perfect Morse function forces nonzero top homology.** If a nonempty compact manifold of
dimension `m` carries a perfect Morse function with coefficients in `k`, then `Hₘ(M; k) ≠ 0`:
the maximum is a critical point of index `m`. -/
theorem IsPerfectMorse.finrank_singularHomology_finrank_ne_zero [Nonempty M]
    (hf : IsPerfectMorse I k f) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) (finrank ℝ E)).obj
      (ModuleCat.of k k)).obj (TopCat.of M)) ≠ 0 := by
  have h := hf.isMorse.criticalCount_finrank_ne_zero
  rw [hf.criticalCount_eq] at h
  exact_mod_cast h

end Compact

/-! ### Projective spaces -/

section Projective

variable {n : ℕ} {w : Fin (n + 1) → ℝ}

/-- **The moment function on `ℂℙⁿ` is perfect.** For pairwise distinct weights, the moment
function on `ℂℙⁿ` is a perfect Morse function for every division ring of coefficients: its
critical points all have even index. -/
theorem isPerfectMorse_projectiveMomentFunction_complex (hw : Function.Injective w) (k : Type)
    [DivisionRing k] :
    IsPerfectMorse 𝓘(ℝ, Fin n → ℂ) k (projectiveMomentFunction ℂ w) := by
  refine (isMorse_projectiveMomentFunction hw).isPerfectMorse_of_forall_ne_add_one ?_
  rw [criticalPoints_projectiveMomentFunction hw]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  rw [manifoldMorseIndex_projectiveMomentFunction, manifoldMorseIndex_projectiveMomentFunction,
    Complex.finrank_real_complex]
  omega

/-- **The moment function on `ℝPⁿ` is perfect in characteristic two.** For pairwise distinct
weights, the moment function on `ℝPⁿ` has one critical point of each index `0, …, n`, and it is a
perfect Morse function with coefficients in every division ring in which `2 = 0`, such as
`ZMod 2`. -/
theorem isPerfectMorse_projectiveMomentFunction_real (hw : Function.Injective w) {k : Type}
    [DivisionRing k] (h2 : (2 : k) = 0) :
    IsPerfectMorse 𝓘(ℝ, Fin n → ℝ) k (projectiveMomentFunction ℝ w) := by
  refine isPerfectMorse_iff.2 ⟨isMorse_projectiveMomentFunction hw, fun j ↦ ?_⟩
  rw [criticalCount_projectiveMomentFunction_real hw,
    RealProjectiveSpace.finrank_singularHomology_projectivization_of_two_eq_zero h2 j]
  simp

/-- **No perfect Morse function on `ℝPᴺ` outside characteristic two.** For `N ≥ 2`, no Morse
function on `ℝPᴺ` is perfect with coefficients in a division ring in which `2 ≠ 0`, such as `ℚ`.
Its Betti numbers add up to at most two, so a perfect Morse function would have exactly two
critical points, and Reeb's theorem would make `ℝPᴺ` homeomorphic to the simply connected sphere
`Sᴺ`. In particular `ℝP²` admits no perfect Morse function over `ℚ`. -/
theorem not_isPerfectMorse_projectivization_real (hn : 2 ≤ n) {k : Type} [DivisionRing k]
    (h2 : (2 : k) ≠ 0) (f : ℙ ℝ (Fin (n + 1) → ℝ) → ℝ) :
    ¬ IsPerfectMorse 𝓘(ℝ, Fin n → ℝ) k f := by
  intro hf
  have : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  -- Over `k` the Betti numbers of `ℝPⁿ` add up to at most two, so `f` has two critical points.
  have hle : totalCriticalCount 𝓘(ℝ, Fin n → ℝ) f ≤ 2 := by
    rw [hf.totalCriticalCount_eq, finrank_fin_fun]
    simp only [RealProjectiveSpace.finrank_singularHomology_projectivization_of_two_ne_zero h2]
    refine (Finset.sum_le_sum (g := fun j ↦ ((if j = 0 then 1 else 0) + if j = n then 1 else 0 :
      ℕ∞)) fun j _ ↦ ?_).trans ?_
    · split_ifs <;> simp_all
    · simp [Finset.sum_add_distrib, one_add_one_eq_two]
  obtain ⟨e⟩ := hf.isMorse.nonempty_homeomorph_sphere_of_totalCriticalCount_eq_two
    (le_antisymm hle (two_le_totalCriticalCount hf.isMorse.contMDiff.continuous))
  rw [finrank_fin_fun] at e
  -- By Reeb's theorem `ℝPⁿ` would be homeomorphic to the simply connected sphere `Sⁿ`.
  have := simplyConnectedSpace_sphere_euclideanSpace hn
  exact RealProjectiveSpace.not_simplyConnectedSpace n hn <|
    ((RealProjectiveSpace.homeomorphProjectivization n).trans e).toHomotopyEquiv
      |>.simplyConnectedSpace

end Projective

end TauCeti
