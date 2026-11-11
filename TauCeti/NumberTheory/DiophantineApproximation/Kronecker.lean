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
`ε > 0` the inhomogeneous system `|y αᵢ - xᵢ - θᵢ| ≤ ε` has infinitely many integer solutions,
even with the multiplier `y` a positive integer as large as we please.

This is the inhomogeneous companion of Dirichlet's theorem (`TauCeti.simultaneous_dirichlet`),
which approximates the target `θ = 0` with an explicit rate and needs no hypothesis on `α`.

## Main results

* `TauCeti.denseRange_mul_sub_intCast`: Kronecker's theorem in density form.
* `TauCeti.kronecker_approximation`: infinitely many integer solutions of
  `|y αᵢ - xᵢ - θᵢ| ≤ ε`.
* `TauCeti.kronecker_approximation_nat`: infinitely many natural numbers `n` for which
  `|n αᵢ - xᵢ - θᵢ| ≤ ε` has an integer solution `x`.

## Implementation notes

The density follows from `AddSubgroup.dense_iff_forall_dual_eq_zero`: a real linear functional
`f` taking integer values on the points `y α - x` takes integer values `kᵢ = f eᵢ` on the standard
basis and `m = f α = ∑ i, kᵢ αᵢ` on `α`, an integer relation between `1, α₁, …, αₙ`, so `k = 0`
and `f = 0`.

The positive form `kronecker_approximation_nat` follows by symmetry: the solutions of the
homogeneous system (`θ = 0`) are closed under `(x, y) ↦ (-x, -y)`, so their multipliers `y` are
unbounded above, and adding one with a large multiplier to a single solution for `θ` gives a
solution with a large positive multiplier.

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

/-- **Kronecker's approximation theorem with positive multipliers.** If `1` and the real numbers
`αᵢ` satisfy no nontrivial integer relation, that is, if they are linearly independent over `ℚ`,
then for every `θ ∈ ℝ^ι` and `ε > 0` there are infinitely many natural numbers `n`, hence
arbitrarily large positive ones, each with some `x ∈ ℤ^ι` such that `|n αᵢ - xᵢ - θᵢ| ≤ ε` for
every `i`. -/
theorem kronecker_approximation_nat {α : ι → ℝ}
    (hα : ∀ x : ℤ × (ι → ℤ), (x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * α i = 0 → x = 0) (θ : ι → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    {n : ℕ | ∃ x : ι → ℤ, ∀ i, |α i * n - x i - θ i| ≤ ε}.Infinite := by
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨⟨x₀, y₀⟩, h₀⟩ := (kronecker_approximation hα θ hε2).nonempty
  -- The multipliers `y` of the solutions of the homogeneous system (`θ = 0`) form an infinite
  -- set, since each `y` admits only finitely many `x`.
  set Y := {y : ℤ | ∃ x : ι → ℤ, ∀ i, |α i * y - x i| ≤ ε / 2}
  have hY : Y.Infinite := fun hfin ↦ kronecker_approximation hα 0 hε2 <| (hfin.biUnion fun y _ ↦
      ((Set.Finite.pi fun i ↦ Set.finite_Icc ⌈α i * y - ε / 2⌉ ⌊α i * y + ε / 2⌋).prod
        (Set.finite_singleton y))).subset fun ⟨x, y⟩ hp ↦ by
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero] at hp
    refine Set.mem_biUnion (x := y) ⟨x, hp⟩ (Set.mk_mem_prod (fun i _ ↦ ?_) rfl)
    have := abs_le.1 (hp i)
    exact ⟨Int.ceil_le.2 (by linarith), Int.le_floor.2 (by linarith)⟩
  -- `Y` is symmetric, so it is not bounded above.
  have hYneg {y : ℤ} : y ∈ Y → -y ∈ Y := fun ⟨x, hx⟩ ↦ ⟨-x, fun i ↦ by
    rw [← abs_neg]
    convert hx i using 2
    push_cast [Pi.neg_apply]
    ring⟩
  have hYbdd : ¬BddAbove Y := fun ⟨M, hM⟩ ↦ hY <| BddBelow.finite_of_bddAbove
    ⟨-M, fun y hy ↦ neg_le.1 (hM (hYneg hy))⟩ ⟨M, hM⟩
  -- Add a homogeneous solution with large multiplier to the solution `(x₀, y₀)`.
  refine Set.infinite_of_forall_exists_gt fun N ↦ ?_
  obtain ⟨y, ⟨x, hx⟩, hy⟩ := not_bddAbove_iff.1 hYbdd (N - y₀)
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (a := y₀ + y) (by omega)
  refine ⟨n, ⟨x₀ + x, fun i ↦ ?_⟩, by omega⟩
  calc |α i * n - ↑((x₀ + x) i) - θ i|
      = |(α i * y₀ - x₀ i - θ i) + (α i * y - x i)| := by
        rw [show (n : ℝ) = y₀ + y by exact_mod_cast hn.symm, Pi.add_apply]
        push_cast
        ring_nf
    _ ≤ ε := (abs_add_le _ _).trans (by linarith [h₀ i, hx i])

end TauCeti
