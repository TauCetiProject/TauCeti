/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Compactly supported functions as finite combinations of translates

Let `η` be a nonzero function on a real normed space `E` and `χ` a compactly supported one, both of
class `Cⁿ`. Then `χ` is a finite combination of translates of `η` with compactly supported `Cⁿ`
coefficients:

`χ z = ∑_{a ∈ s} g_a(z) η(z - a)`

(`exists_finset_forall_eq_sum_mul_comp_sub`). The sets `{z | η (z - a) ≠ 0}` are open and cover
`E`, so finitely many of them cover the support of `χ`; with `Φ = ∑_{a ∈ s} η(· - a)²`, which is
positive on that support, the coefficients are `g_a = χ η(· - a) / Φ`.

This is how a norm localized by one cutoff is bounded by norms localized by another: a quantity
built from `χ(· - x) f` is the finite sum of the quantities built from `g_a(· - x) η(· - x - a) f`,
and each multiplier `g_a(· - x)` is a translate of one fixed compactly supported function, so its
size does not depend on `x`.

Such quantities read a function placed at scale `h` about a centre `x`, `y ↦ g (h⁻¹ • (y - x))`.
This keeps the class `Cⁿ` (`ContDiff.comp_inv_smul_sub`) and, for `h ≠ 0`, compact support
(`HasCompactSupport.comp_inv_smul_sub`).
-/

public section

open Set Function

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}

/-- A function of class `Cⁿ` placed at scale `h` about a centre `x`, `y ↦ g (h⁻¹ • (y - x))`, is
of class `Cⁿ`. -/
theorem _root_.ContDiff.comp_inv_smul_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} (hg : ContDiff ℝ n g) (h : ℝ) (x : E) :
    ContDiff ℝ n fun y ↦ g (h⁻¹ • (y - x)) :=
  hg.comp ((contDiff_id.sub contDiff_const).const_smul h⁻¹)

/-- A compactly supported function placed at a nonzero scale `h` about a centre `x`,
`y ↦ g (h⁻¹ • (y - x))`, is compactly supported. -/
theorem _root_.HasCompactSupport.comp_inv_smul_sub {F : Type*} [Zero F] {g : E → F}
    (hg : HasCompactSupport g) {h : ℝ} (hh : h ≠ 0) (x : E) :
    HasCompactSupport fun y ↦ g (h⁻¹ • (y - x)) :=
  (hg.comp_smul (inv_ne_zero hh)).comp_homeomorph (Homeomorph.subRight x)

/-- **A compactly supported function is a finite combination of translates of any nonzero
function.** If `η` and `χ` are of class `Cⁿ`, `η ≠ 0` and `χ` has compact support, there are a
finite set `s` of translations and compactly supported `Cⁿ` coefficients `g a`, `a ∈ s`, with
`χ z = ∑_{a ∈ s} g a z * η (z - a)` for every `z`. -/
theorem exists_finset_forall_eq_sum_mul_comp_sub {η χ : E → ℝ} (hη : ContDiff ℝ n η)
    (hη0 : η ≠ 0) (hχ : ContDiff ℝ n χ) (hc : HasCompactSupport χ) :
    ∃ (s : Finset E) (g : E → E → ℝ), (∀ a ∈ s, ContDiff ℝ n (g a) ∧ HasCompactSupport (g a)) ∧
      ∀ z, χ z = ∑ a ∈ s, g a z * η (z - a) := by
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 hη0
  have hηa (a : E) : ContDiff ℝ n fun z ↦ η (z - a) := hη.comp (contDiff_id.sub contDiff_const)
  -- Finitely many of the open sets `{z | η (z - a) ≠ 0}` cover the support of `χ`.
  obtain ⟨s, hs⟩ := hc.isCompact.elim_finite_subcover (fun a ↦ {z | η (z - a) ≠ 0})
    (fun a ↦ isOpen_compl_singleton.preimage (hηa a).continuous)
    fun z _ ↦ mem_iUnion.2 ⟨z - z₀, by simpa using hz₀⟩
  set Φ : E → ℝ := fun z ↦ ∑ a ∈ s, η (z - a) ^ 2
  have hΦ : ContDiff ℝ n Φ := ContDiff.sum fun a _ ↦ (hηa a).pow 2
  have hΦpos {z} (hz : z ∈ tsupport χ) : Φ z ≠ 0 := by
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.1 (hs hz)
    exact (Finset.sum_pos' (fun b _ ↦ sq_nonneg (η (z - b))) ⟨a, ha, sq_pos_of_ne_zero hza⟩).ne'
  refine ⟨s, fun a z ↦ χ z * (η (z - a) / Φ z), fun a _ ↦ ⟨?_, hc.mul_right⟩, fun z ↦ ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
    by_cases hz : z ∈ tsupport χ
    · exact hχ.contDiffAt.mul ((hηa a).contDiffAt.div hΦ.contDiffAt (hΦpos hz))
    -- Off the support of `χ` the coefficient vanishes near `z`.
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with w hw
    rw [image_eq_zero_of_notMem_tsupport hw, zero_mul]
  · have hsum : ∑ a ∈ s, χ z * (η (z - a) / Φ z) * η (z - a) = χ z / Φ z * Φ z := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ ↦ by ring
    rw [hsum]
    by_cases hΦz : Φ z = 0
    · rw [image_eq_zero_of_notMem_tsupport fun hz ↦ hΦpos hz hΦz, zero_div, zero_mul]
    · rw [div_mul_cancel₀ _ hΦz]

end TauCeti
