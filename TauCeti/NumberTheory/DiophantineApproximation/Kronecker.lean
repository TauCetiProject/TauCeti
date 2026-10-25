/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
import TauCeti.Algebra.Module.ZLattice.DenseSubgroup

/-!
# Kronecker's approximation theorem

Let `α₁, …, αₙ` be real numbers such that `1, α₁, …, αₙ` are linearly independent over `ℚ`,
that is, `x₀ + ∑ i, xᵢ αᵢ = 0` with integers `xᵢ` only for `x = 0`. Kronecker's theorem says
that the points `(y αᵢ - xᵢ)ᵢ`, for `y ∈ ℤ` and `x ∈ ℤⁿ`, are dense in `ℝⁿ`: the integer
multiples of `α` are dense in the torus `ℝⁿ / ℤⁿ`. Hence for every target `θ ∈ ℝⁿ` and every
`ε > 0` the inhomogeneous system `|y αᵢ - xᵢ - θᵢ| ≤ ε` has infinitely many integer solutions.

This is the inhomogeneous companion of Dirichlet's theorem (`TauCeti.simultaneous_dirichlet`),
which approximates the target `θ = 0` with an explicit rate and needs no hypothesis on `α`.

## Main results

* `TauCeti.denseRange_mul_sub_intCast`: Kronecker's theorem in density form.
* `TauCeti.kronecker_approximation`: infinitely many integer solutions of
  `|y αᵢ - xᵢ - θᵢ| ≤ ε`.

## Implementation notes

The density follows from `AddSubgroup.dense_iff_forall_dual_eq_zero`: a real linear functional
`f` taking integer values on the points `y α - x` takes integer values `kᵢ = f eᵢ` on the standard
basis and `m = f α = ∑ i, kᵢ αᵢ` on `α`, an integer relation between `1, α₁, …, αₙ`, so `k = 0`
and `f = 0`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes, Chapter 2, Theorem 2.22.
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, Chapter XXIII,
  Theorem 442.
-/

public section

open Filter Topology Module

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **Kronecker's theorem, density form.** If `1` and the real numbers `αᵢ` satisfy no
nontrivial integer relation, that is, if they are linearly independent over `ℚ`, then the
points `(y αᵢ - xᵢ)ᵢ`, for `y ∈ ℤ` and `x ∈ ℤ^ι`, are dense in `ℝ^ι`. -/
theorem denseRange_mul_sub_intCast {α : ι → ℝ}
    (hα : ∀ x : ℤ × (ι → ℤ), (x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * α i = 0 → x = 0) :
    DenseRange fun p : (ι → ℤ) × ℤ ↦ fun i ↦ α i * p.2 - p.1 i := by
  classical
  let F : (ι → ℤ) × ℤ →+ (ι → ℝ) :=
    AddMonoidHom.mk' (fun p i ↦ α i * p.2 - p.1 i) fun p q ↦ by
      ext i
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Int.cast_add]
      ring
  have hF : ∀ p, F p = fun i ↦ α i * p.2 - p.1 i := fun _ ↦ rfl
  rw [DenseRange, ← funext hF, ← AddMonoidHom.coe_range, AddSubgroup.dense_iff_forall_dual_eq_zero]
  intro f hf
  -- The values of `f` on the standard basis and on `α` are integers.
  have hval (p : (ι → ℤ) × ℤ) : ∃ k : ℤ, f (F p) = k := hf _ ⟨p, rfl⟩
  choose k hk using fun j : ι ↦ hval (-Pi.single j 1, 0)
  obtain ⟨m, hm⟩ := hval (0, 1)
  have he (j : ι) : F (-Pi.single j 1, 0) = Pi.single j 1 := by
    ext i
    by_cases h : i = j <;> simp [hF, h]
  have hrel : (-m : ℝ) + ∑ j, (k j : ℝ) * α j = 0 := by
    have hα' : F (0, 1) = α := by ext i; simp [hF]
    rw [hα', pi_eq_sum_univ' α, map_sum] at hm
    simp_rw [map_smul, ← he, hk, smul_eq_mul, mul_comm (α _)] at hm
    rw [← hm]
    ring
  have hk0 : k = 0 := by simpa using congrArg Prod.snd (hα (-m, k) (by simpa using hrel))
  refine (Pi.basisFun ℝ ι).ext fun j ↦ ?_
  simpa [he, hk0] using hk j

/-- **Kronecker's approximation theorem.** If `1` and the real numbers `αᵢ` satisfy no
nontrivial integer relation, that is, if they are linearly independent over `ℚ`, then for every
`θ ∈ ℝ^ι` and `ε > 0` there are infinitely many integer pairs `(x, y)`, `x ∈ ℤ^ι`, `y ∈ ℤ`, with
`|y αᵢ - xᵢ - θᵢ| ≤ ε` for every `i`. -/
theorem kronecker_approximation {α : ι → ℝ}
    (hα : ∀ x : ℤ × (ι → ℤ), (x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * α i = 0 → x = 0) (θ : ι → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    {p : (ι → ℤ) × ℤ | ∀ i, |α i * p.2 - p.1 i - θ i| ≤ ε}.Infinite := by
  cases isEmpty_or_nonempty ι
  · simpa using Set.infinite_univ
  set F : (ι → ℤ) × ℤ → ι → ℝ := fun p i ↦ α i * p.2 - p.1 i
  -- The dense range of `F` meets the ball `B(θ, ε)` in infinitely many points, so the solution
  -- set has an infinite image under `F`.
  refine Set.Infinite.of_image F fun hfin ↦ ?_
  obtain ⟨_, hpB, ⟨p, rfl⟩, hpF⟩ := ((denseRange_mul_sub_intCast hα).sdiff_finite
    hfin).inter_open_nonempty (Metric.ball θ ε) Metric.isOpen_ball ⟨θ, Metric.mem_ball_self hε⟩
  refine hpF ⟨p, fun i ↦ ?_, rfl⟩
  rw [Metric.mem_ball, dist_eq_norm] at hpB
  exact ((norm_le_pi_norm (F p - θ) i).trans hpB.le)

end TauCeti
