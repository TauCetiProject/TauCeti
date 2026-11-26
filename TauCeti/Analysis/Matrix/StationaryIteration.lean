/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.Topology.Instances.Matrix

/-!
# Stationary iterations

A stationary iteration for a square matrix `G` and a vector `c` is the sequence
`x 0 = x₀`, `x (k + 1) = G *ᵥ x k + c`. The classical iterative methods for a linear system
`A x = b` (Jacobi, Gauss–Seidel, successive over-relaxation) are of this form, with `G` the
iteration matrix of a splitting of `A`.

This file gives the closed form of the iterates and of their errors, and proves the convergence
criterion: the iterates converge for every `c` and every starting vector if and only if the powers
of `G` tend to zero, and then `1 - G` is invertible and the iterates tend to `(1 - G)⁻¹ *ᵥ c`.
The criterion holds over any commutative topological ring with open units, in particular over
`ℝ` and `ℂ`, with the entrywise topology on vectors and matrices. No norm is needed, and `G`
need not have norm less than one in a given operator norm: `!![1/2, 1; 0, 1/2]` has row-sum norm
`3/2`, yet its powers tend to zero.

## Main declarations

* `Matrix.stationaryIterate G c x₀ k`: the `k`-th iterate of `x ↦ G *ᵥ x + c` from `x₀`.
* `Matrix.stationaryIterate_eq`: `x k = G ^ k *ᵥ x₀ + (∑ i ∈ range k, G ^ i) *ᵥ c`.
* `Matrix.stationaryIterate_sub_of_isFixedPt`: for a fixed point `x` of `y ↦ G *ᵥ y + c`, the
  error is `x k - x = G ^ k *ᵥ (x₀ - x)`.
* `Matrix.tendsto_stationaryIterate`: if `G` is topologically nilpotent, that is `G ^ k → 0`,
  the iterates tend to `(1 - G)⁻¹ *ᵥ c` from
  every starting vector.
* `Matrix.forall_exists_tendsto_stationaryIterate_iff`: the iterates converge for every `c` and
  every `x₀` if and only if `G ^ k → 0`.

## References

* Yousef Saad, *Iterative Methods for Sparse Linear Systems*, second edition, SIAM, 2003:
  Theorem 1.11, p. 21, and Theorem 4.1, p. 115.
-/

public section

open Filter Finset Topology

namespace Matrix

variable {ι R : Type*} [Fintype ι]

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R] (G : Matrix ι ι R) (c x₀ : ι → R)

/-- The stationary iterates of `x ↦ G *ᵥ x + c` from `x₀`: `x 0 = x₀` and
`x (k + 1) = G *ᵥ x k + c`. -/
def stationaryIterate (k : ℕ) : ι → R :=
  (fun x ↦ G *ᵥ x + c)^[k] x₀

@[simp]
theorem stationaryIterate_zero : stationaryIterate G c x₀ 0 = x₀ :=
  Function.iterate_zero_apply _ _

@[simp]
theorem stationaryIterate_succ (k : ℕ) :
    stationaryIterate G c x₀ (k + 1) = G *ᵥ stationaryIterate G c x₀ k + c :=
  Function.iterate_succ_apply' _ _ _

/-- Running `m + k` steps from `x₀` is running `k` steps from the `m`-th iterate. -/
theorem stationaryIterate_add (m k : ℕ) :
    stationaryIterate G c x₀ (m + k) = stationaryIterate G c (stationaryIterate G c x₀ m) k := by
  simp only [stationaryIterate, add_comm m k, Function.iterate_add_apply]

/-- A fixed point of `x ↦ G *ᵥ x + c` is left fixed by the iteration. -/
theorem stationaryIterate_of_isFixedPt {x : ι → R} (hx : Function.IsFixedPt (G *ᵥ · + c) x)
    (k : ℕ) : stationaryIterate G c x k = x := by
  rw [stationaryIterate]
  exact (hx.iterate k).eq

end NonUnitalNonAssocSemiring

section Semiring

variable [Semiring R] [DecidableEq ι] (G : Matrix ι ι R) (c x₀ : ι → R)

/-- The closed form of the stationary iterates:
`x k = G ^ k *ᵥ x₀ + (1 + G + ⋯ + G ^ (k - 1)) *ᵥ c`. -/
theorem stationaryIterate_eq (k : ℕ) :
    stationaryIterate G c x₀ k = (G ^ k) *ᵥ x₀ + (∑ i ∈ range k, G ^ i) *ᵥ c := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [ih, mulVec_add, mulVec_mulVec, mul_sum, sum_range_succ', add_mulVec, ← pow_succ',
      add_assoc]

end Semiring

section Ring

variable [Ring R] (G : Matrix ι ι R) (c x₀ : ι → R)

/-- The error of a stationary iteration with respect to a fixed point `x` of `y ↦ G *ᵥ y + c`
is `x k - x = G ^ k *ᵥ (x₀ - x)`. -/
theorem stationaryIterate_sub_of_isFixedPt [DecidableEq ι] {x : ι → R}
    (hx : Function.IsFixedPt (G *ᵥ · + c) x) (k : ℕ) :
    stationaryIterate G c x₀ k - x = (G ^ k) *ᵥ (x₀ - x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    conv_lhs => rw [stationaryIterate_succ, ← hx.eq]
    rw [add_sub_add_right_eq_sub, ← mulVec_sub, ih, mulVec_mulVec, pow_succ']

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- If the stationary iterates of `x ↦ G *ᵥ x + c` converge for every `c` and every starting
vector, then `G` is topologically nilpotent: its powers tend to zero. Only the starting vector
`0` is used. -/
theorem isTopologicallyNilpotent_of_forall_exists_tendsto_stationaryIterate [DecidableEq ι]
    (h : ∀ c, ∃ x, Tendsto (stationaryIterate G c 0) atTop (𝓝 x)) :
    IsTopologicallyNilpotent G := by
  refine tendsto_iff_forall_tendsto_mulVec.2 fun v ↦ ?_
  obtain ⟨x, hx⟩ := h v
  have hdiff (k : ℕ) :
      stationaryIterate G v 0 (k + 1) - stationaryIterate G v 0 k = (G ^ k) *ᵥ v := by
    rw [stationaryIterate_eq, stationaryIterate_eq, sum_range_succ, add_mulVec]
    simp
  have hlim := (hx.comp (tendsto_add_atTop_nat 1)).sub hx
  rw [sub_self] at hlim
  rw [zero_mulVec]
  exact hlim.congr hdiff

end Ring

section CommRing

variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsOpenUnits R] [DecidableEq ι]
  (G : Matrix ι ι R) (c x₀ : ι → R)

/-- If `G` is topologically nilpotent, that is its powers tend to zero, then the stationary
iterates of `x ↦ G *ᵥ x + c` tend to `(1 - G)⁻¹ *ᵥ c` from every starting vector `x₀`. Here
`1 - G` is invertible by `IsTopologicallyNilpotent.isUnit_one_sub_of_isOpenUnits`, and its
inverse is the limit of the partial sums `∑ i ∈ range k, G ^ i`. -/
theorem tendsto_stationaryIterate (hG : IsTopologicallyNilpotent G) :
    Tendsto (stationaryIterate G c x₀) atTop (𝓝 ((1 - G)⁻¹ *ᵥ c)) := by
  have hsum : Tendsto (fun k ↦ ∑ i ∈ range k, G ^ i) atTop (𝓝 (1 - G)⁻¹) := by
    rw [nonsing_inv_eq_ringInverse]
    exact hG.tendsto_geom_sum_of_isOpenUnits
  rw [show stationaryIterate G c x₀ = _ from funext (stationaryIterate_eq G c x₀)]
  simpa using (tendsto_iff_forall_tendsto_mulVec.1 hG x₀).add
    (tendsto_iff_forall_tendsto_mulVec.1 hsum c)

/-- The convergence criterion for stationary iterations: the iterates of `x ↦ G *ᵥ x + c`
converge for every `c` and every starting vector `x₀` if and only if `G` is topologically
nilpotent, that is its powers tend to zero. By `tendsto_stationaryIterate`, the limit is then
`(1 - G)⁻¹ *ᵥ c`. -/
theorem forall_exists_tendsto_stationaryIterate_iff :
    (∀ c x₀, ∃ x, Tendsto (stationaryIterate G c x₀) atTop (𝓝 x)) ↔
      IsTopologicallyNilpotent G :=
  ⟨fun h ↦ isTopologicallyNilpotent_of_forall_exists_tendsto_stationaryIterate G fun c ↦ h c 0,
    fun hG c x₀ ↦ ⟨_, tendsto_stationaryIterate G c x₀ hG⟩⟩

end CommRing

end Matrix
