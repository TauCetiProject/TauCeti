/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.RingTheory.Huber.Perfect

/-!
# Perfectoid Tate rings of characteristic `p`

In characteristic `p`, the perfectoid Tate rings are exactly the perfect complete Hausdorff Tate
rings (Scholze, *Étale cohomology of diamonds*, Proposition 3.5).

* A perfectoid Tate ring of characteristic `p` is perfect. It is reduced, so Frobenius is
  injective. For surjectivity, let `x ∈ R°`. The perfectoid condition gives `x = y₀ ^ p + ϖ ^ p z₁`
  with `y₀, z₁ ∈ R°`, then `z₁ = y₁ ^ p + ϖ ^ p z₂`, and so on. In characteristic `p` this gives
  `x = (y₀ + ϖ y₁ + ⋯ + ϖ ^ n yₙ) ^ p + ϖ ^ (p (n + 1)) z_{n+1}`. The series `∑ ϖ ^ k y_k`
  converges, because `R°` is bounded and `ϖ` is topologically nilpotent, and its sum is a `p`-th
  root of `x`. Any `x ∈ R` has `ϖ ^ (p n) x ∈ R°` for some `n`, so it is a `p`-th power too.
* Conversely, a perfect complete Hausdorff Tate ring of characteristic `p` is uniform
  (`TauCeti.Huber.IsUniform.of_perfectRing`), hence perfectoid
  (`TauCeti.Perfectoid.IsPerfectoidTateRing.of_perfectRing`).

## Main results

* `TauCeti.Perfectoid.IsPerfectoidTateRing.perfectRing`: a perfectoid Tate ring of
  characteristic `p` is perfect.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.of_perfectRing`: a perfect complete Hausdorff Tate ring
  of characteristic `p` is perfectoid.
* `TauCeti.Perfectoid.isPerfectoidTateRing_iff_perfectRing`: in characteristic `p`, a complete
  Hausdorff Tate ring is perfectoid exactly when it is perfect.

## References

* P. Scholze, *Étale cohomology of diamonds*, Proposition 3.5.
* P. Scholze, *Perfectoid spaces*, Proposition 5.9.
* K. S. Kedlaya, R. Liu, *Relative p-adic Hodge theory: foundations*, Remark 3.3.4.
-/

public section

open Filter Topology TauCeti.Huber

namespace TauCeti.Perfectoid

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R] [CharP R p]

/-- In a perfectoid Tate ring of characteristic `p`, every power-bounded element has a `p`-th
root, the sum of a series built by successive approximation modulo `ϖ ^ p`. -/
private theorem IsPerfectoidTateRing.exists_pow_eq [IsPerfectoidTateRing p R]
    (x : powerBoundedSubring R) : ∃ s : R, s ^ p = x := by
  obtain ⟨ϖ, hϖ, -, hs, -⟩ := IsPerfectoidTateRing.exists_pseudoUniformizer (p := p) (R := R)
  have hb := IsPerfectoidTateRing.isBounded_powerBoundedSubring (p := p) (R := R)
  -- every `z ∈ R°` is `Y z ^ p + ϖ ^ p * W z` with `Y z, W z ∈ R°`
  have step (z : powerBoundedSubring R) : ∃ y w : powerBoundedSubring R, z = y ^ p + ϖ ^ p * w :=
    let ⟨y, w, hw⟩ := hs z
    ⟨y, w, by rw [← hw, add_sub_cancel]⟩
  choose Y W hYW using step
  -- the successive remainders `z n` and the partial sums `∑_{k < n} ϖ ^ k * Y (z k)`
  set z : ℕ → powerBoundedSubring R := fun n ↦ W^[n] x
  set t : ℕ → R := fun k ↦ (ϖ : R) ^ k * Y (z k)
  have hrem (n : ℕ) : (x : R) = (∑ k ∈ Finset.range n, t k) ^ p + ((ϖ : R) ^ p) ^ n * z n := by
    induction n with
    | zero => simp [z, zero_pow (Fact.out : p.Prime).ne_zero]
    | succ n ih =>
      have hz : z (n + 1) = W (z n) := Function.iterate_succ_apply' W n x
      have h := congrArg (Subtype.val : powerBoundedSubring R → R) (hYW (z n))
      push_cast at h
      rw [Finset.sum_range_succ, add_pow_char, hz, ih, h]
      ring
  -- the series converges, its terms tending to zero
  have ht : Tendsto t atTop (𝓝 0) :=
    hb.tendsto_mul hϖ.isTopologicallyNilpotent (Eventually.of_forall fun k ↦ (Y (z k)).2)
  obtain ⟨σ, hσ⟩ := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (by rwa [Nat.cofinite_eq_atTop])
  refine ⟨σ, tendsto_nhds_unique (hσ.tendsto_sum_nat.pow p) ?_⟩
  -- the remainders `(ϖ ^ p) ^ n * z n` tend to zero
  have hϖp : Tendsto (fun n ↦ ((ϖ : R) ^ p) ^ n) atTop (𝓝 0) :=
    hϖ.isTopologicallyNilpotent.pow (Fact.out : p.Prime).ne_zero
  have hr := hb.tendsto_mul hϖp (Eventually.of_forall fun n ↦ (z n).2)
  simpa [sub_eq_iff_eq_add.mpr (hrem _)] using (tendsto_const_nhds (x := (x : R))).sub hr

/-- **A perfectoid Tate ring of characteristic `p` is perfect** (Scholze, *Étale cohomology of
diamonds*, Proposition 3.5). -/
theorem IsPerfectoidTateRing.perfectRing [IsPerfectoidTateRing p R] : PerfectRing R p := by
  have := IsPerfectoidTateRing.isReduced p (R := R)
  refine PerfectRing.ofSurjective R p fun x ↦ ?_
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := R)
  obtain ⟨n, hn⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent
    (isOpen_powerBoundedSubring R) x
  -- `x * ϖ ^ (p * n)` is a power-bounded `p`-th power, so `x` is a `p`-th power
  have hmem : x * ϖ ^ (p * n) ∈ powerBoundedSubring R := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (Nat.le_mul_of_pos_left n (Fact.out : p.Prime).pos)
    rw [hq, pow_add, ← mul_assoc]
    have hϖq : IsPowerBounded (ϖ ^ q) :=
      (IsPowerBounded.of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent).pow q
    exact (powerBoundedSubring R).mul_mem hn (mem_powerBoundedSubring.mpr hϖq)
  obtain ⟨s, hs⟩ := IsPerfectoidTateRing.exists_pow_eq (p := p) ⟨_, hmem⟩
  refine ⟨s * ((hϖ.isUnit.unit⁻¹ : Rˣ) : R) ^ n, ?_⟩
  calc frobenius R p (s * ((hϖ.isUnit.unit⁻¹ : Rˣ) : R) ^ n)
      = x * ((hϖ.isUnit.unit⁻¹ : Rˣ) * ϖ) ^ (p * n) := by
        rw [frobenius_def, mul_pow, hs]
        ring
    _ = x := by rw [hϖ.isUnit.val_inv_mul, one_pow, mul_one]

/-- **A perfect complete Hausdorff Tate ring of characteristic `p` is perfectoid** (Scholze,
*Étale cohomology of diamonds*, Proposition 3.5): it is uniform, every pseudouniformiser works,
`ϖ ^ p ∣ p = 0` being automatic, and Frobenius is bijective. -/
theorem IsPerfectoidTateRing.of_perfectRing [PerfectRing R p] : IsPerfectoidTateRing p R := by
  have := IsUniform.of_perfectRing (R := R) p
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := R)
  have hp : (p : powerBoundedSubring R) = 0 := Subtype.ext (CharP.cast_eq_zero R p)
  exact .of_forall_exists_pow_eq ⟨ϖ, mem_powerBoundedSubring.mpr
    (IsPowerBounded.of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent)⟩ hϖ
    (hp ▸ dvd_zero _) fun x ↦
      (surjective_frobenius R p x).imp fun _ h ↦ by rwa [frobenius_def] at h

/-- **In characteristic `p`, perfectoid means perfect** (Scholze, *Étale cohomology of diamonds*,
Proposition 3.5): a complete Hausdorff Tate ring of characteristic `p` is a perfectoid Tate ring
exactly when it is a perfect ring. -/
theorem isPerfectoidTateRing_iff_perfectRing : IsPerfectoidTateRing p R ↔ PerfectRing R p :=
  ⟨fun _ ↦ IsPerfectoidTateRing.perfectRing, fun _ ↦ .of_perfectRing⟩

end TauCeti.Perfectoid
