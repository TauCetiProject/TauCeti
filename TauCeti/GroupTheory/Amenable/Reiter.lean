/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import TauCeti.GroupTheory.Amenable.Foelner
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
`MeasureTheory.Measure.exists_pos_sum_measure_symmDiff_lt_mul_measure`.

## Main results

* `TauCeti.exists_finset_sum_card_smul_symmDiff_lt_of_sum_tsum_lt`: a finite nonempty set whose
  total boundary `∑_{g ∈ K} |g • F ∆ F|` is less than `ε |F|`.
* `TauCeti.exists_finset_card_smul_symmDiff_lt_of_sum_tsum_lt`: the same set satisfies
  `|g • F ∆ F| < ε |F|` for each `g ∈ K`.
* `TauCeti.hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt`: a group satisfying Reiter's
  condition, for its left regular action, has Følner sets.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Theorem G.5.1 and the proof of
  Proposition G.5.2.
* A. Garrido, *An introduction to amenable groups*, Theorem 3.6.
-/

public section

open Finset Function MeasureTheory
open scoped Pointwise symmDiff ENNReal

namespace TauCeti

/-- Against counting measure on a finite set `U` containing the support of a nonnegative `f`, the
integral of `f` is its sum. -/
private theorem lintegral_ofReal_count_restrict_eq_tsum {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {U : Finset X} {f : X → ℝ} (hf : 0 ≤ f)
    (hU : ∀ x ∉ U, f x = 0) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂Measure.count.restrict U = ENNReal.ofReal (∑' x, f x) := by
  rw [tsum_eq_sum hU, ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hf x]
  simp [lintegral_finset]

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-- Let `U` contain the support `S` of `p` and its translates `g • S`, `g ∈ K`. If, for counting
measure on `U`, the superlevel set `{x | t < p x}` at a level `t > 0` has total boundary less than
`ε` times its measure, then that superlevel set is a nonempty finset `F` with
`∑_{g ∈ K} |g • F ∆ F| < ε |F|`. -/
private theorem exists_finset_of_sum_count_restrict_lt [MeasurableSpace X]
    [MeasurableSingletonClass X] {p : X → ℝ} {S U : Finset X} {K : Finset G} {ε t : ℝ}
    (hS : ∀ x, p x ≠ 0 → x ∈ S) (hSU : S ⊆ U) (hKU : ∀ g ∈ K, g • S ⊆ U) (hε : 0 < ε)
    (ht : 0 < t)
    (hlt : ∑ g ∈ K, Measure.count.restrict U ({x | t < p (g⁻¹ • x)} ∆ {x | t < p x}) <
      ENNReal.ofReal ε * Measure.count.restrict U {x | t < p x}) :
    ∃ F : Finset X, F.Nonempty ∧ ∑ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
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
  have hFU : F ⊆ U := (filter_subset _ _).trans hSU
  have hmU (A : Finset X) (hA : A ⊆ U) : Measure.count.restrict U (A : Set X) = #A := by
    rw [Measure.restrict_eq_self _ (coe_subset.2 hA), Measure.count_apply_finset]
  have hsd {g : G} (hg : g ∈ K) :
      Measure.count.restrict U ({x | t < p (g⁻¹ • x)} ∆ {x | t < p x}) = #((g • F) ∆ F) := by
    rw [hsmul, ← hF, ← coe_symmDiff, hmU]
    exact symmDiff_le_sup.trans (union_subset
      ((smul_finset_subset_smul_finset (filter_subset _ _)).trans (hKU g hg)) hFU)
  rw [sum_congr rfl fun g hg ↦ hsd hg, ← hF, hmU F hFU] at hlt
  replace hlt : ∑ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hε.le] at hlt
    exact_mod_cast ENNReal.natCast_lt_ofReal.1 (by exact_mod_cast hlt)
  refine ⟨F, card_pos.1 ?_, hlt⟩
  exact_mod_cast pos_of_mul_pos_right
    ((sum_nonneg fun g _ ↦ Nat.cast_nonneg _).trans_lt hlt) hε.le

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
  -- Step 1: rewrite `h` as an inequality of integrals for counting measure on a finite set `U`
  -- containing the supports of `p` and its translates. Step 2: select a level `t > 0` by
  -- `exists_pos_sum_measure_symmDiff_lt_mul_measure`. Step 3: identify the measures of the
  -- superlevel sets at `t` with cardinalities, by `exists_finset_of_sum_count_restrict_lt`.
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
  have h' : ∑ g ∈ K, ∫⁻ x, ‖p (g⁻¹ • x) - p x‖ₑ ∂m <
      ENNReal.ofReal ε * ∫⁻ x, ENNReal.ofReal (p x) ∂m := by
    simp_rw [Real.enorm_eq_ofReal_abs]
    rw [sum_congr rfl fun g hg ↦ lintegral_ofReal_count_restrict_eq_tsum (fun _ ↦ abs_nonneg _)
        fun x hx ↦ by simp [hpU x hx, hpgU hg x hx],
      lintegral_ofReal_count_restrict_eq_tsum hp hpU,
      ← ENNReal.ofReal_sum_of_nonneg fun g _ ↦ tsum_nonneg fun _ ↦ abs_nonneg _,
      ← ENNReal.ofReal_mul hε.le]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 h
  obtain ⟨t, ht, hlt⟩ := m.exists_pos_sum_measure_symmDiff_lt_mul_measure K
    measurable_from_top.aemeasurable (fun _ _ ↦ measurable_from_top.aemeasurable)
    (ae_of_all _ hp) h'
  exact exists_finset_of_sum_count_restrict_lt hS subset_union_left
    (fun g hg ↦ (subset_biUnion_of_mem (fun g ↦ g • S) hg).trans subset_union_right) hε ht hlt

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

/-- A group satisfying **Reiter's condition** has Følner sets: if for every finite `K` and
`ε > 0` there is a finitely supported probability density `p` with
`∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε`, then `G` has Følner sets. -/
theorem hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt
    (h : ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
        ∑ g ∈ K, ∑' x, |p (g⁻¹ * x) - p x| < ε) :
    HasFoelnerSets G := by
  classical
  refine hasFoelnerSets_iff.2 fun K ε hε ↦ ?_
  obtain ⟨p, hp0, hpfin, hp1, hp⟩ := h K ε hε
  exact exists_finset_card_smul_symmDiff_lt_of_sum_tsum_lt hp0 hpfin (by simpa [hp1] using hp)

end TauCeti
