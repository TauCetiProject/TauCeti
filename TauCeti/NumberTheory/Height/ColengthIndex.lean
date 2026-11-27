/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.ColengthDvd
public import TauCeti.NumberTheory.Height.IndexOverPairs

/-!
# Index bounds from local colengths

At each prime-adic embedding, a colength witness supplies a change of generators with
integral entries. If its determinant divides a power of the prime, its norm is at least
the norm of that power: the complementary factor is a local integer. A bound on all
finite subtotals of the logarithmic losses therefore bounds the index of the family.

The statement is the colength-to-index comparison `New.TwistedLattice.indexLe_of_colengthDvd`
in `New/Reduction/Lattices/TwistedLattice.lean` of [grh-lean](https://github.com/lsernau/grh-lean)
at `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Finset
open scoped NNReal

namespace TauCeti.PrimePadicIso

/-- If at every prime-adic embedding the family belongs to a submodule in which the
colength of the integral condition divides `p ^ j`, then its determinant index is bounded
by any common logarithmic budget charging at least `j * log p` for that prime.
The containing submodule and the natural exponent `j` may depend on the embedding. -/
theorem indexLe_of_colengthDvd {V I : Type*} [AddCommMonoid V] [Module ℂ V]
    [Fintype I] [DecidableEq I] {L : (ι : PrimePadicIso) → Submodule ι.integers V}
    {y : I → V} {δ : ℝ} (e : ℕ → ℝ≥0)
    (hbudget : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∑ p ∈ S, (e p : ℝ) * Real.log p ≤ δ)
    (hlocal : ∀ ι : PrimePadicIso, ∃ M : Submodule ι.integers V, (∀ i, y i ∈ M) ∧
      ∃ j : ℕ, (j : ℝ) ≤ e ι.prime ∧ M.ColengthDvd (L ι) ((ι.prime : ι.integers) ^ j)) :
    IndexLe L y δ := by
  refine indexLe_iff.mpr ⟨fun p ↦ e p, fun p _ ↦ (e p).coe_nonneg, hbudget, fun ι ↦ ?_⟩
  obtain ⟨M, hy, j, hj, hcolength⟩ := hlocal ι
  obtain ⟨A, ⟨a, ha⟩, hrows⟩ := hcolength.exists_matrix y hy
  have hp : (1 : ℝ) ≤ ι.prime := by exact_mod_cast ι.fact_prime.out.one_le
  have hpNorm : ‖ι.iso (((ι.prime : ι.integers) ^ j : ι.integers) : ℂ)‖ =
      (ι.prime : ℝ) ^ (-(j : ℝ)) := by
    simpa only [Subring.coe_pow, Subring.coe_natCast, map_pow, map_natCast,
      ← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast] using
      (PadicAlgCl.norm_extends ι.prime ((ι.prime : ℚ_[ι.prime]) ^ j)).trans (Padic.norm_p_pow j)
  refine ⟨A, ?_, hrows⟩
  calc
    (ι.prime : ℝ) ^ (-(e ι.prime : ℝ)) ≤ (ι.prime : ℝ) ^ (-(j : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp (neg_le_neg hj)
    _ = ‖ι.iso ((A.det * a : ι.integers) : ℂ)‖ := by rw [← ha, hpNorm]
    _ ≤ ‖ι.iso (A.det : ℂ)‖ := by
      rw [Subring.coe_mul, map_mul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (mem_integers.mp a.property)

end TauCeti.PrimePadicIso
