/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Uniform convergence of sequences with summably bounded increments

A sequence of functions `f n : α → E` into a Banach space whose successive increments on a set `s`
are eventually uniformly bounded by a summable sequence `u n` converges uniformly on `s` to its
pointwise limit `fun x ↦ limUnder atTop (fun n ↦ f n x)`
(`TauCeti.tendstoUniformlyOn_limUnder_of_eventually`).
-/

public section

open Filter Set Topology

namespace TauCeti

/-- A sequence of functions into a complete normed additive group whose successive differences on
`s` are eventually bounded by a summable sequence converges uniformly on `s` to its pointwise
limit. -/
theorem tendstoUniformlyOn_limUnder_of_eventually {α E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E] {f : ℕ → α → E} {u : ℕ → ℝ}
    {s : Set α} (hu : Summable u)
    (hbound : ∀ᶠ n in atTop, ∀ x ∈ s, ‖f (n + 1) x - f n x‖ ≤ u n) :
    TendstoUniformlyOn f (fun x ↦ limUnder atTop (fun n ↦ f n x)) atTop s := by
  have hs := tendstoUniformlyOn_tsum_nat_eventually
    (f := fun n x ↦ f (n + 1) x - f n x) (s := s) hu hbound
  have hconst : TendstoUniformlyOn (fun (_ : ℕ) x ↦ f 0 x) (fun x ↦ f 0 x) atTop s := by
    intro V hV
    exact Eventually.of_forall fun _ _ _ ↦ refl_mem_uniformity hV
  have ht : TendstoUniformlyOn f (fun x ↦ (∑' n, (f (n + 1) x - f n x)) + f 0 x) atTop s := by
    have htel (n : ℕ) (x : α) :
        ∑ i ∈ Finset.range n, (f (i + 1) x - f i x) = f n x - f 0 x :=
      Finset.sum_range_sub (fun i ↦ f i x) n
    simpa only [Pi.add_def, htel, sub_add_cancel] using hs.add hconst
  exact ht.congr_right fun x hx ↦ (ht.tendsto_at hx).limUnder_eq.symm

end TauCeti
