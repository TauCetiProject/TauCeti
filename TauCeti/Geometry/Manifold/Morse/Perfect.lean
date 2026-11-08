/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Inequalities
public import TauCeti.Geometry.Manifold.Morse.Projectivization
import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Projectivization
import TauCeti.Geometry.Manifold.Morse.Reeb

/-!
# Perfect Morse functions

A Morse function `f` on a compact manifold `M` is **perfect** over a division ring `k`
(`TauCeti.IsPerfectMorse`) when, for every `j`, its number of critical points of index `j` is the
Betti number `dim_k Hⱼ(M; k)`. By the weak Morse inequalities
(`TauCeti.IsMorse.finrank_singularHomology_le`) the number of critical points of index `j` is
always at least `dim_k Hⱼ(M; k)`, so a perfect Morse function has as few critical points as the
homology of `M` over `k` allows: their number is the total Betti number
(`TauCeti.IsPerfectMorse.totalCriticalCount_eq`). Whether a Morse function is perfect depends on
the coefficients.

By the lacunary principle, a Morse function no two of whose critical points have indices differing
by one is perfect over every division ring
(`TauCeti.IsMorse.isPerfectMorse_of_forall_ne_add_one`). This applies to the moment function on
complex projective space `ℂℙⁿ`, whose indices `0, 2, …, 2n` are all even
(`TauCeti.isPerfectMorse_projectiveMomentFunction_complex`).

On real projective space `ℝℙⁿ` the moment function with distinct weights has one critical point
of each index `0, …, n`. Over a division ring of characteristic two, such as `ZMod 2`, every Betti
number `dim Hⱼ(ℝℙⁿ; k)` with `j ≤ n` is one, so this function is perfect
(`TauCeti.isPerfectMorse_projectiveMomentFunction_real`). Over a division ring in which `2 ≠ 0`,
such as `ℚ`, no Morse function on `ℝℙⁿ` with `n ≥ 2` is perfect
(`TauCeti.not_isPerfectMorse_projectivization_real`). Indeed, the Betti numbers over `k` are
`1` in degree `0`, `1` in degree `n` when `n` is odd, and `0` otherwise, so a perfect Morse
function would have at most two critical points. A function on a compact manifold with at least two
points has at least two critical points, and by Reeb's theorem
(`TauCeti.IsMorse.nonempty_homeomorph_sphere_of_totalCriticalCount_eq_two`) a Morse function with
exactly two makes `ℝℙⁿ` homeomorphic to the sphere `Sⁿ`. This is impossible for `n ≥ 2`, since
`Sⁿ` is simply connected and `ℝℙⁿ` is not. For `ℝℙ²` the moment function has three critical
points while the rational Betti numbers are `1, 0, 0`.

The homology of `ℝℙⁿ` is computed on the antipodal quotient of the sphere
(`TauCeti.RealProjectiveSpace`), and transported to the projectivization
`ℙ ℝ (Fin (n + 1) → ℝ)`, which carries the smooth structure, along
`TauCeti.RealProjectiveSpace.homeomorphProjectivization`.

## Main declarations

* `TauCeti.IsPerfectMorse`: a Morse function whose critical counts are the Betti numbers.
* `TauCeti.IsPerfectMorse.totalCriticalCount_eq`: the number of critical points of a perfect Morse
  function is the total Betti number.
* `TauCeti.IsMorse.isPerfectMorse_of_forall_ne_add_one`: the lacunary principle gives perfect Morse
  functions.
* `TauCeti.isPerfectMorse_projectiveMomentFunction_complex`: the moment function on `ℂℙⁿ` is
  perfect over every division ring.
* `TauCeti.isPerfectMorse_projectiveMomentFunction_real`: the moment function on `ℝℙⁿ` is perfect
  in characteristic two.
* `TauCeti.not_isPerfectMorse_projectivization_real`: for `n ≥ 2` no Morse function on `ℝℙⁿ` is
  perfect over a division ring in which `2 ≠ 0`.

## References

* R. Bott, *Lectures on Morse theory, old and new*, Bull. Amer. Math. Soc. 7 (1982), 331–358, §1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §§4–5.
-/

public section

noncomputable section

open Function Module Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization

universe u

namespace TauCeti

section General

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ}
  {k : Type u} [DivisionRing k]

variable (I k) in
/-- A function `f : M → ℝ` is a **perfect Morse function** over the division ring `k` when it is a
Morse function whose number of critical points of index `j` is the Betti number
`dim_k Hⱼ(M; k)` of singular homology, for every `j`. Both sides are counted in `ℕ∞`, the Betti
number being `⊤` when `Hⱼ(M; k)` is infinite-dimensional. -/
structure IsPerfectMorse (f : M → ℝ) : Prop where
  /-- A perfect Morse function is a Morse function. -/
  isMorse : IsMorse I f
  /-- The number of critical points of index `j` is the `j`-th Betti number over `k`. -/
  criticalCount_eq (j : ℕ) : criticalCount I f j =
    (Module.rank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj
      (ModuleCat.of k k)).obj (TopCat.of M))).toENat

/-- A perfect Morse function is a Morse function whose critical counts are the Betti numbers. -/
theorem isPerfectMorse_iff : IsPerfectMorse I k f ↔ IsMorse I f ∧ ∀ j, criticalCount I f j =
    (Module.rank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj
      (ModuleCat.of k k)).obj (TopCat.of M))).toENat :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- **The number of critical points of a perfect Morse function** is the total Betti number
`∑ⱼ dim_k Hⱼ(M; k)`, the sum running over the degrees `j ≤ dim M`. -/
theorem IsPerfectMorse.totalCriticalCount_eq [FiniteDimensional ℝ E] (hf : IsPerfectMorse I k f) :
    totalCriticalCount I f = ∑ j ∈ Finset.range (finrank ℝ E + 1),
      (Module.rank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj
        (ModuleCat.of k k)).obj (TopCat.of M))).toENat := by
  rw [← sum_criticalCount_eq_totalCriticalCount]
  exact Finset.sum_congr rfl fun j _ ↦ hf.criticalCount_eq j

/-- **The lacunary principle gives perfect Morse functions.** A Morse function on a compact
boundaryless manifold, no two of whose critical points have indices differing by one, is perfect
over every division ring. -/
theorem IsMorse.isPerfectMorse_of_forall_ne_add_one [FiniteDimensional ℝ E] [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [CompactSpace M] (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) :
    IsPerfectMorse I k f where
  isMorse := hf
  criticalCount_eq j := by
    rw [hf.toENat_rank_singularHomology (ModuleCat.of k k),
      hf.finrank_singularHomology_eq_of_forall_ne_add_one (ModuleCat.of k k) hind j]
    simpa using (ENat.natCast_toNat (hf.criticalCount_ne_top j)).symm

end General

/-! ### Projective spaces -/

open Projectivization

variable {n : ℕ}

/-- **The moment function on `ℂℙⁿ` is perfect.** For pairwise distinct weights, the moment function
on complex projective space is a perfect Morse function over every division ring `k`: its
critical points have the even indices `0, 2, …, 2n`, one each, and no two of them differ by one. -/
theorem isPerfectMorse_projectiveMomentFunction_complex (k : Type) [DivisionRing k]
    {w : Fin (n + 1) → ℝ} (hw : Injective w) :
    IsPerfectMorse 𝓘(ℝ, Fin n → ℂ) k (projectiveMomentFunction ℂ w) := by
  refine (isMorse_projectiveMomentFunction hw).isPerfectMorse_of_forall_ne_add_one ?_
  rw [criticalPoints_projectiveMomentFunction hw]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  simp only [manifoldMorseIndex_projectiveMomentFunction, Complex.finrank_real_complex]
  omega

/-- **The moment function on `ℝℙⁿ` is perfect in characteristic two.** For pairwise distinct
weights, the moment function on real projective space is a perfect Morse function over every
division ring `k` in which `2 = 0`, such as `ZMod 2`: it has one critical point of each index
`j ≤ n`, and `Hⱼ(ℝℙⁿ; k)` is one-dimensional for each `j ≤ n`. -/
theorem isPerfectMorse_projectiveMomentFunction_real {k : Type} [DivisionRing k] (h2 : (2 : k) = 0)
    {w : Fin (n + 1) → ℝ} (hw : Injective w) :
    IsPerfectMorse 𝓘(ℝ, Fin n → ℝ) k (projectiveMomentFunction ℝ w) where
  isMorse := isMorse_projectiveMomentFunction hw
  criticalCount_eq j := by
    rw [criticalCount_projectiveMomentFunction_real hw,
      (isMorse_projectiveMomentFunction hw).toENat_rank_singularHomology (ModuleCat.of k k),
      RealProjectiveSpace.finrank_singularHomology_projectivization,
      RealProjectiveSpace.finrank_singularHomology_of_two_eq_zero h2]
    split_ifs <;> simp

/-- **No Morse function on `ℝℙⁿ` is perfect away from characteristic two.** For `n ≥ 2` and a
division ring `k` in which `2 ≠ 0`, such as `ℚ`, no function on real projective space
`ℙ ℝ (Fin (n + 1) → ℝ)` is a perfect Morse function over `k`. -/
theorem not_isPerfectMorse_projectivization_real {k : Type} [DivisionRing k] (h2 : (2 : k) ≠ 0)
    (hn : 2 ≤ n) (f : ℙ ℝ (Fin (n + 1) → ℝ) → ℝ) : ¬ IsPerfectMorse 𝓘(ℝ, Fin n → ℝ) k f := by
  intro hf
  have : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  -- Over `k` the Betti numbers of `ℝℙⁿ` add up to at most two, so `f` has two critical points.
  have hle : totalCriticalCount 𝓘(ℝ, Fin n → ℝ) f ≤ 2 := by
    rw [hf.totalCriticalCount_eq, finrank_fin_fun]
    simp only [hf.isMorse.toENat_rank_singularHomology (ModuleCat.of k k),
      RealProjectiveSpace.finrank_singularHomology_projectivization,
      RealProjectiveSpace.finrank_singularHomology_of_two_ne_zero h2]
    refine (Finset.sum_le_sum (g := fun j ↦ ((if j = 0 then 1 else 0) + if j = n then 1 else 0 :
      ℕ∞)) fun j _ ↦ ?_).trans ?_
    · split_ifs <;> simp_all
    · simp [Finset.sum_add_distrib, one_add_one_eq_two]
  obtain ⟨e⟩ := hf.isMorse.nonempty_homeomorph_sphere_of_totalCriticalCount_eq_two
    (le_antisymm hle (two_le_totalCriticalCount hf.isMorse.contMDiff.continuous))
  rw [finrank_fin_fun] at e
  -- By Reeb's theorem `ℝℙⁿ` would be homeomorphic to the simply connected sphere `Sⁿ`.
  have := simplyConnectedSpace_sphere_euclideanSpace hn
  exact RealProjectiveSpace.not_simplyConnectedSpace n hn <|
    ((RealProjectiveSpace.homeomorphProjectivization n).trans e).toHomotopyEquiv
      |>.simplyConnectedSpace

end TauCeti
