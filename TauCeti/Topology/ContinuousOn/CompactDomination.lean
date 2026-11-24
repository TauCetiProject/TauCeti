/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Uniform domination by a nonnegative continuous weight

On a compact set, a continuous real function which is strictly negative wherever a nonnegative
continuous weight vanishes is strictly bounded above by one positive constant times that weight.
The directed open-cover proof allows the weight to vanish, so no quotient continuity at its
zeros is assumed. This supplies uniform coefficient bounds for local comparison barriers.

## Main results

* `IsCompact.exists_pos_forall_lt_mul`: uniform domination by a continuous nonnegative weight.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Corollary 4.14.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section
open Set Topology

/-- A continuous function strictly negative on the zero set of a continuous nonnegative weight
is uniformly dominated by a positive multiple of that weight on a compact set. -/
theorem IsCompact.exists_pos_forall_lt_mul
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {f w : X → ℝ} (hf : ContinuousOn f K) (hw : ContinuousOn w K)
    (hwnonneg : ∀ x ∈ K, 0 ≤ w x) (hzero : ∀ x ∈ K, w x = 0 → f x < 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ K, f x < A * w x := by
  let U : ℝ → Set K := fun A ↦ {x | f x < A * w x}
  have hUo (A : ℝ) : IsOpen (U A) :=
    isOpen_lt hf.domRestrict ((continuousOn_const.mul hw).domRestrict)
  have hcover : (Set.univ : Set K) ⊆ ⋃ A : {a : ℝ // 0 < a}, U A := by
    intro x _
    by_cases hx : w x = 0
    · exact mem_iUnion.2 ⟨⟨1, zero_lt_one⟩, by simpa [U, hx] using hzero x x.property hx⟩
    · have hwpos : 0 < w x := lt_of_le_of_ne (hwnonneg x x.property) (Ne.symm hx)
      let c : ℝ := max 1 (f x / w x + 1)
      have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      have hratio : f x / w x < c :=
        lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
      exact mem_iUnion.2 ⟨⟨c, hc⟩, (div_lt_iff₀ hwpos).mp hratio⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨A, hAK⟩ := (isCompact_univ : IsCompact (Set.univ : Set K)).elim_directed_cover
    (fun a : {a : ℝ // 0 < a} ↦ U a) (fun a ↦ hUo a) hcover (by
      intro a b
      let c : {a : ℝ // 0 < a} :=
        ⟨max (a : ℝ) (b : ℝ), lt_of_lt_of_le a.property (le_max_left _ _)⟩
      have hmono {A B : ℝ} (hAB : A ≤ B) : U A ⊆ U B := by
        intro x hx
        exact hx.trans_le (mul_le_mul_of_nonneg_right hAB (hwnonneg x x.property))
      exact ⟨c, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩)
  exact ⟨A, A.property, fun x hx ↦ hAK (mem_univ (⟨x, hx⟩ : K))⟩
