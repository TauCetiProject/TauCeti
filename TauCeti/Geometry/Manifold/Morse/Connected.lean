/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Inequalities
import Mathlib.Algebra.Field.ULift
import TauCeti.Geometry.Manifold.Topology

/-!
# Morse functions on connected manifolds

Let `f` be a Morse function on a compact connected boundaryless manifold `M` of dimension `m`, with
`cⱼ` critical points of index `j`, and let `bⱼ = dim Hⱼ(M; V)` for a finite-dimensional module `V`
over a division ring. Since `M` is path-connected, `b₀ = dim V`, and the strong Morse inequality in
degree one, `b₁ - b₀ ≤ (c₁ - c₀) dim V`, becomes `c₀ dim V + b₁ ≤ (c₁ + 1) dim V`
(`TauCeti.IsMorse.toNat_criticalCount_zero_mul_add_finrank_singularHomology_one_le`). In
particular `c₀ ≤ c₁ + 1`: a Morse function with `c₀` local minima has at least `c₀ - 1` critical
points of index one (`TauCeti.IsMorse.criticalCount_zero_le_criticalCount_one_add_one`), and so
has one as soon as it has two local minima
(`TauCeti.IsMorse.criticalCount_one_ne_zero_of_two_le_criticalCount_zero`). Applied to `-f`, whose
critical points of index `j` are those of `f` of index `m - j`, this gives `cₘ ≤ cₘ₋₁ + 1` for the
local maxima (`TauCeti.IsMorse.criticalCount_finrank_le_criticalCount_finrank_sub_one_add_one`).

These bounds are invisible to the weak inequalities `bⱼ ≤ cⱼ dim V` and Euler's equality: odd
spheres of dimension at least three carry counts satisfying both but not `c₀ ≤ c₁ + 1`
(`TauCeti.finrank_singularHomology_sphere_le_and_sum_eq_and_not_exists_isMorse` in
`TauCeti.Geometry.Manifold.Morse.Sphere.Inequalities`).

## Main results

* `TauCeti.IsMorse.toNat_criticalCount_zero_mul_add_finrank_singularHomology_one_le`: on a compact
  connected manifold, `c₀ dim V + b₁ ≤ (c₁ + 1) dim V`.
* `TauCeti.IsMorse.criticalCount_zero_le_criticalCount_one_add_one` and
  `TauCeti.IsMorse.criticalCount_one_ne_zero_of_two_le_criticalCount_zero`: `c₀ ≤ c₁ + 1`, so two
  local minima force a critical point of index one.
* `TauCeti.IsMorse.criticalCount_finrank_le_criticalCount_finrank_sub_one_add_one`: dually,
  `cₘ ≤ cₘ₋₁ + 1`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331--358, Section 1.
-/

public section

noncomputable section

open CategoryTheory Module Set
open scoped ContDiff Manifold

universe u

namespace TauCeti

section Connected

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  {f : M → ℝ}

/-- **Index-one critical points on a connected manifold.** Let `f` be a Morse function on a compact
connected boundaryless manifold `M`, with `cⱼ` critical points of index `j`. For every
finite-dimensional module `V` over a division ring, `c₀ dim V + dim H₁(M; V) ≤ (c₁ + 1) dim V`.
This is the strong Morse inequality in degree one, since `H₀(M; V) ≅ V`. -/
theorem IsMorse.toNat_criticalCount_zero_mul_add_finrank_singularHomology_one_le
    {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V] (hf : IsMorse I f) :
    (criticalCount I f 0).toNat * finrank k V +
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) 1).obj V).obj
          (TopCat.of M)) ≤
      ((criticalCount I f 1).toNat + 1) * finrank k V := by
  have : PathConnectedSpace M := I.pathConnectedSpace M
  have h₀ : finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) 0).obj V).obj
      (TopCat.of M)) = finrank k V :=
    (asIso ((TopCat.of M).singularHomology₀ε V)).toLinearEquiv.finrank_eq
  have h := hf.sum_range_neg_one_pow_mul_finrank_singularHomology_le V 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h₀] at h
  norm_num at h
  linarith

/-- **Local minima and critical points of index one.** A Morse function on a compact connected
boundaryless manifold has at most one more critical point of index `0` than of index `1`. -/
theorem IsMorse.criticalCount_zero_le_criticalCount_one_add_one (hf : IsMorse I f) :
    criticalCount I f 0 ≤ criticalCount I f 1 + 1 := by
  have h := hf.toNat_criticalCount_zero_mul_add_finrank_singularHomology_one_le
    (ModuleCat.of (ULift.{u} ℚ) (ULift.{u} ℚ))
  simp only [Module.finrank_self, mul_one] at h
  rw [← ENat.natCast_toNat (hf.criticalCount_ne_top 0),
    ← ENat.natCast_toNat (hf.criticalCount_ne_top 1)]
  exact_mod_cast (Nat.le_add_right _ _).trans h

/-- A Morse function on a compact connected boundaryless manifold with at least two critical
points of index `0`, that is two local minima, has a critical point of index `1`. -/
theorem IsMorse.criticalCount_one_ne_zero_of_two_le_criticalCount_zero (hf : IsMorse I f)
    (h : 2 ≤ criticalCount I f 0) : criticalCount I f 1 ≠ 0 := by
  intro h₁
  have := (h.trans hf.criticalCount_zero_le_criticalCount_one_add_one).trans_eq (by rw [h₁])
  exact absurd this (by decide)

/-- **The dual bound for the local maxima.** A Morse function on a compact connected boundaryless
manifold of dimension `m` has at most one more critical point of index `m` than of index
`m - 1`. -/
theorem IsMorse.criticalCount_finrank_le_criticalCount_finrank_sub_one_add_one
    (hf : IsMorse I f) :
    criticalCount I f (finrank ℝ E) ≤ criticalCount I f (finrank ℝ E - 1) + 1 := by
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with hE | hE
  · rw [hE]
    exact le_self_add
  have h := hf.neg.criticalCount_zero_le_criticalCount_one_add_one
  rwa [hf.criticalCount_neg (Nat.zero_le _), hf.criticalCount_neg hE, Nat.sub_zero] at h

end Connected

end TauCeti
