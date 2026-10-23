/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import TauCeti.MeasureTheory.Integral.LayerCake

/-!
# Følner sets from almost invariant finitely supported functions

Let a group `G` act on a type `X`, and translate functions by `(g • p) x = p (g⁻¹ • x)`. If a
nonnegative finitely supported function `p : X → ℝ` is almost invariant under a finite set
`K ⊆ G` in `ℓ¹`, in the sense that

```text
∑_{g ∈ K} ∑_x |p (g⁻¹ • x) - p x| < ε · ∑_x p x,
```

then some finite nonempty set `F ⊆ X` satisfies

```text
∑_{g ∈ K} |g • F ∆ F| < ε · |F|.
```

Such a set is found among the superlevel sets `{x | t < p x}`, `t > 0`.

This passes from Reiter's condition (almost invariant finitely supported probabilities) to Følner's
condition (almost invariant finite sets). The proof is the layer-cake argument: for counting
measure, the `ℓ¹` distance between `p` and its translate is the integral over the levels `t > 0` of
`|g • F_t ∆ F_t|`, while the `ℓ¹` norm of `p` is the integral of `|F_t|`; see
`TauCeti.exists_pos_sum_measure_symmDiff_lt_mul_measure`.

## Main results

* `TauCeti.exists_finset_sum_card_smul_symmDiff_lt_of_sum_tsum_lt`: a finite nonempty set whose
  total boundary `∑_{g ∈ K} |g • F ∆ F|` is less than `ε |F|`.
* `TauCeti.exists_finset_card_smul_symmDiff_lt_of_sum_tsum_lt`: the same set satisfies
  `|g • F ∆ F| < ε |F|` for each `g ∈ K`.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Theorem G.5.1 and the proof of
  Proposition G.5.2.
* A. Garrido, *An introduction to amenable groups*, Theorem 3.6.
-/

public section

open Finset Function MeasureTheory
open scoped Pointwise symmDiff ENNReal

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-- **Reiter implies Følner, summed form.** If a nonnegative finitely supported function `p` on
`X` satisfies `∑_{g ∈ K} ∑_x |p (g⁻¹ • x) - p x| < ε · ∑_x p x`, then some finite nonempty set
`F ⊆ X` has total boundary `∑_{g ∈ K} |g • F ∆ F| < ε |F|`. -/
theorem exists_finset_sum_card_smul_symmDiff_lt_of_sum_tsum_lt {p : X → ℝ} (hp : 0 ≤ p)
    (hfin : p.HasFiniteSupport) {K : Finset G} {ε : ℝ}
    (h : ∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x| < ε * ∑' x, p x) :
    ∃ F : Finset X, F.Nonempty ∧ ∑ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  let : MeasurableSpace X := ⊤
  have : MeasurableSingletonClass X := ⟨fun _ ↦ trivial⟩
  have hpos : 0 < ε * ∑' x, p x :=
    (sum_nonneg fun g _ ↦ tsum_nonneg fun x ↦ abs_nonneg _).trans_lt h
  have hε : 0 < ε := pos_of_mul_pos_left hpos (tsum_nonneg hp)
  -- `p` and its translates by elements of `K` are supported in the finite set `U`.
  set S := hfin.toFinset
  have hS (x : X) (hx : p x ≠ 0) : x ∈ S := hfin.mem_toFinset.2 hx
  set U : Finset X := S ∪ K.biUnion fun g ↦ g • S
  have hpU (x : X) (hx : x ∉ U) : p x = 0 := not_not.1 fun h ↦ hx (mem_union_left _ (hS x h))
  have hpgU {g : G} (hg : g ∈ K) (x : X) (hx : x ∉ U) : p (g⁻¹ • x) = 0 :=
    not_not.1 fun h ↦ hx <| mem_union_right _ <| mem_biUnion.2
      ⟨g, hg, mem_smul_finset.2 ⟨_, hS _ h, smul_inv_smul g x⟩⟩
  -- Counting measure on `X` need not be s-finite, so work with counting measure on `U`: it is a
  -- finite measure, and its integrals are sums over `U`.
  set m : Measure X := Measure.count.restrict U
  have : IsFiniteMeasure m := ⟨by simp [m]⟩
  have hm (f : X → ℝ≥0∞) : ∫⁻ x, f x ∂m = ∑ x ∈ U, f x := by simp [m, lintegral_finset]
  have hdefect : ∑ g ∈ K, ∫⁻ x, ‖p (g⁻¹ • x) - p x‖ₑ ∂m =
      ENNReal.ofReal (∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x|) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun g _ ↦ tsum_nonneg fun _ ↦ abs_nonneg _]
    refine sum_congr rfl fun g hg ↦ ?_
    rw [hm, tsum_eq_sum (s := U) fun x hx ↦ by simp [hpU x hx, hpgU hg x hx],
      ENNReal.ofReal_sum_of_nonneg fun x _ ↦ abs_nonneg _]
    simp_rw [Real.enorm_eq_ofReal_abs]
  have hmass : ∫⁻ x, ENNReal.ofReal (p x) ∂m = ENNReal.ofReal (∑' x, p x) := by
    rw [hm, tsum_eq_sum hpU, ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hp x]
  have h' : ∑ g ∈ K, ∫⁻ x, ‖p (g⁻¹ • x) - p x‖ₑ ∂m <
      ENNReal.ofReal ε * ∫⁻ x, ENNReal.ofReal (p x) ∂m := by
    rw [hdefect, hmass, ← ENNReal.ofReal_mul hε.le]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 h
  obtain ⟨t, ht, hlt⟩ := exists_pos_sum_measure_symmDiff_lt_mul_measure m K
    measurable_from_top.aemeasurable (fun _ _ ↦ measurable_from_top.aemeasurable)
    (ae_of_all _ hp) h'
  -- The superlevel set `F = {x | t < p x}` lies in `S`, and its translates are the superlevel
  -- sets of the translates of `p`.
  set F : Finset X := {x ∈ S | t < p x}
  have hF : (F : Set X) = {x | t < p x} := by
    ext x
    simpa [F] using fun hx ↦ hS x (ht.trans hx).ne'
  have hsmul (g : G) : {x | t < p (g⁻¹ • x)} = ((g • F : Finset X) : Set X) := by
    rw [coe_smul_finset, hF]
    ext x
    simp [Set.mem_smul_set_iff_inv_smul_mem]
  have hFU : F ⊆ U := (filter_subset _ _).trans subset_union_left
  have hmU (A : Finset X) (hA : A ⊆ U) : m A = #A := by
    rw [Measure.restrict_eq_self _ (coe_subset.2 hA), Measure.count_apply_finset]
  have hsd {g : G} (hg : g ∈ K) :
      m ({x | t < p (g⁻¹ • x)} ∆ {x | t < p x}) = #((g • F) ∆ F) := by
    rw [hsmul, ← hF, ← coe_symmDiff, hmU]
    refine symmDiff_le_sup.trans (union_subset ?_ hFU)
    exact (smul_finset_subset_smul_finset (filter_subset _ _)).trans
      ((subset_biUnion_of_mem (fun g ↦ g • S) hg).trans subset_union_right)
  rw [sum_congr rfl fun g hg ↦ hsd hg, ← hF, hmU F hFU, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul hε.le, ← Nat.cast_sum,
    ENNReal.lt_ofReal_iff_toReal_lt (ENNReal.natCast_ne_top _), ENNReal.toReal_natCast] at hlt
  push_cast at hlt
  refine ⟨F, card_pos.1 ?_, hlt⟩
  exact_mod_cast pos_of_mul_pos_right
    ((sum_nonneg fun g _ ↦ Nat.cast_nonneg _).trans_lt hlt) hε.le

/-- **Reiter implies Følner.** If a nonnegative finitely supported function `p` on `X` satisfies
`∑_{g ∈ K} ∑_x |p (g⁻¹ • x) - p x| < ε · ∑_x p x`, then some finite nonempty set `F ⊆ X` satisfies
`|g • F ∆ F| < ε |F|` for every `g ∈ K`. -/
theorem exists_finset_card_smul_symmDiff_lt_of_sum_tsum_lt {p : X → ℝ} (hp : 0 ≤ p)
    (hfin : p.HasFiniteSupport) {K : Finset G} {ε : ℝ}
    (h : ∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x| < ε * ∑' x, p x) :
    ∃ F : Finset X, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  obtain ⟨F, hF, hlt⟩ := exists_finset_sum_card_smul_symmDiff_lt_of_sum_tsum_lt hp hfin h
  exact ⟨F, hF, fun g hg ↦ (single_le_sum (f := fun g ↦ (#((g • F) ∆ F) : ℝ))
    (fun _ _ ↦ Nat.cast_nonneg _) hg).trans_lt hlt⟩

end TauCeti
