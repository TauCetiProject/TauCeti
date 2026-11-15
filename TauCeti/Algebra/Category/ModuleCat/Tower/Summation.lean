/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Ring
public import TauCeti.Topology.Algebra.Nonarchimedean.LinearTopology
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Summation in inverse limits of discrete modules

A family in the limit of a tower of discrete modules is summable exactly when each coordinate
vanishes outside a finite set. A coordinate of the sum is then a finite sum. For completions
`lim A / Jₙ`, a series with its `n`-th term in `Jₙ` therefore converges, and its action on a
smooth vector is the finite sum at any annihilating cutoff.

The convergence criterion uses Mathlib's nonarchimedean summability theorem; the action is
`TauCeti.ModuleTower.limSmul`, not an action on quotient rings.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.ModuleTower

variable {R : Type*} [Ring R] (F : ModuleTower R)

/-- A family in the inverse limit is summable precisely when every coordinate is eventually
zero on the cofinite filter. -/
theorem summable_iff_forall_eventually_limπ_eq_zero {ι : Type*} (f : ι → F.lim) :
    Summable f ↔ ∀ n, ∀ᶠ i in cofinite, F.limπ n (f i) = 0 := by
  have := IsLinearTopology.nonarchimedeanAddGroup R (M := F.lim)
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, tendsto_nhds_iff]
  simp

/-- Each coordinate of a convergent series is the sum over any finite set outside which that
coordinate vanishes. -/
theorem limπ_tsum_eq_sum {ι : Type*} {f : ι → F.lim} (hf : Summable f)
    (n : ℕ) (s : Finset ι) (hs : ∀ i ∉ s, F.limπ n (f i) = 0) :
    F.limπ n (∑' i, f i) = ∑ i ∈ s, F.limπ n (f i) := by
  let : TopologicalSpace (F.obj (Opposite.op n)) := ⊥
  have := discreteTopology_bot (F.obj (Opposite.op n))
  exact (hf.hasSum.map (F.limπ n) (F.isLocallyConstant_limπ n).continuous).unique
    (hasSum_sum_of_ne_finset_zero hs)

section Quotient

variable {V : Type*} [AddCommGroup V] [Module R V]
  {J : ℕ → Submodule R V} {hJ : Antitone J}

/-- A series whose `n`-th term belongs to `Jₙ` converges in `lim V / Jₙ`. -/
theorem summable_toLimQuotients_of_mem {f : ℕ → V} (hf : ∀ n, f n ∈ J n) :
    Summable fun n ↦ toLimQuotients J hJ (f n) := by
  apply (summable_iff_forall_eventually_limπ_eq_zero _ _).2
  intro n
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop n] with i hi
  rw [← LinearMap.comp_apply, limπ_comp_toLimQuotients, quotientsπ_eq_zero_iff]
  exact hJ hi (hf i)

/-- Modulo `Jₙ`, the sum of a series with terms in `Jᵢ` is represented by its first `n` terms. -/
theorem limπ_tsum_toLimQuotients {f : ℕ → V} (hf : ∀ n, f n ∈ J n) (n : ℕ) :
    (quotients J hJ).limπ n (∑' i, toLimQuotients J hJ (f i)) =
      quotientsπ J hJ n (∑ i ∈ Finset.range n, f i) := by
  rw [limπ_tsum_eq_sum _ (summable_toLimQuotients_of_mem hf) n (Finset.range n)]
  · simp only [← LinearMap.comp_apply, limπ_comp_toLimQuotients, map_sum]
  · intro i hi
    rw [← LinearMap.comp_apply, limπ_comp_toLimQuotients, quotientsπ_eq_zero_iff]
    exact hJ (by simpa using hi) (hf i)

end Quotient

variable {A : Type*} [Ring A] {J : ℕ → Submodule A A} {hJ : Antitone J}

/-- On a smooth vector annihilated by `Jₙ`, a convergent series with its `i`-th term in `Jᵢ`
acts by its first `n` terms. -/
theorem limSmul_tsum_toLimQuotients {M : ModuleCat A} (hM : smoothModules J M)
    {f : ℕ → A} (hf : ∀ n, f n ∈ J n) {m : M} {n : ℕ}
    (hm : ∀ c ∈ J n, c • m = 0) :
    limSmul hM (∑' i, toLimQuotients J hJ (f i)) m =
      ∑ i ∈ Finset.range n, f i • m := by
  rw [limSmul_eq_smul hM _ hm (limπ_tsum_toLimQuotients hf n).symm, Finset.sum_smul]

end TauCeti.ModuleTower
