/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Closed cones without opposite directions

Let `Γ₁` and `Γ₂` be closed subsets of a proper real normed space, both closed under
multiplication by positive reals, such that no nonzero `ξ ∈ Γ₁` has `-ξ ∈ Γ₂`. Then the summands
of `a + b`, for `a ∈ Γ₁` and `b ∈ Γ₂`, are controlled by the sum: for some `κ > 0`,

`κ (‖a‖ + ‖b‖) ≤ ‖a + b‖`.

On the compact set of pairs `(a, b) ∈ Γ₁ × Γ₂` with `‖a‖ + ‖b‖ = 1` the continuous function
`‖a + b‖` does not vanish, so it is bounded below by some `κ > 0`, and both sides of the inequality
are homogeneous. Consequently the sum `Γ₁ + Γ₂` is closed: near a point it is the image of a
compact set of pairs.

Thickening `Γ₁` and `Γ₂` to the open sets `U₁` and `U₂` of vectors `η` within `ε ‖η‖` of them, for
a small `ε > 0`, preserves this geometry near a frequency `ζ₀ ∉ Γ₁ + Γ₂`: on an open cone around
`ζ₀`, no `ζ` splits as `η + (ζ - η)` with `η ∈ U₁` and `ζ - η ∈ U₂`, and a summand in one of the
thickenings leaves the other summand comparable to `ζ`.

This is the geometry behind the wave front set of a product of distributions, where `Γ₁` and `Γ₂`
contain the frequencies of the wave front sets of the factors and those of the product lie in
`Γ₁ + Γ₂`.

## Main results

* `TauCeti.exists_mul_norm_add_norm_le_norm_add`: `κ (‖a‖ + ‖b‖) ≤ ‖a + b‖` for some `κ > 0`.
* `TauCeti.isClosed_add_of_forall_neg_mem_imp_eq_zero`: the sum `Γ₁ + Γ₂` is closed.
* `TauCeti.exists_isOpen_forall_exists_norm_sub_lt`: the open thickening of a cone by vectors
  within `ε ‖η‖` of it.
* `TauCeti.exists_cones_of_notMem_add`: thickenings of `Γ₁` and `Γ₂`, and an open cone around a
  frequency off `Γ₁ + Γ₂`, on which a summand in one thickening leaves the other summand
  comparable to the sum.
* `TauCeti.forall_neg_mem_insert_zero_imp_eq_zero`: adjoining `0` to the cones creates no
  opposite nonzero vectors.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, proof of Theorem 8.2.10 (the cone geometry for the product of distributions).
-/

public section

open Metric Set
open scoped Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Γ₁ Γ₂ : Set E}

omit [NormedSpace ℝ E] in
/-- Adjoining `0` to `Γ₁` and `Γ₂` creates no opposite nonzero vectors. -/
theorem forall_neg_mem_insert_zero_imp_eq_zero (hopp : ∀ ξ ∈ Γ₁, -ξ ∈ Γ₂ → ξ = 0) :
    ∀ ξ ∈ insert (0 : E) Γ₁, -ξ ∈ insert 0 Γ₂ → ξ = 0 := by
  rintro ξ (rfl | hξ) (hξ' | hξ')
  · rfl
  · rfl
  · exact neg_eq_zero.1 hξ'
  · exact hopp ξ hξ hξ'

omit [NormedSpace ℝ E] in
/-- The pairs in `Γ₁ × Γ₂` with `‖a‖ + ‖b‖ ≤ R` form a compact set. -/
private theorem isCompact_prod_inter_norm_add_norm_le [ProperSpace E] (h₁ : IsClosed Γ₁)
    (h₂ : IsClosed Γ₂) (R : ℝ) : IsCompact (Γ₁ ×ˢ Γ₂ ∩ {p : E × E | ‖p.1‖ + ‖p.2‖ ≤ R}) := by
  refine isCompact_of_isClosed_isBounded
    ((h₁.prod h₂).inter (isClosed_le (by fun_prop) continuous_const))
    ((isBounded_closedBall (x := (0 : E × E)) (r := R)).subset fun p hp ↦ ?_)
  have h1 : ‖p.1‖ + ‖p.2‖ ≤ R := hp.2
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  exact max_le (by linarith [norm_nonneg p.2]) (by linarith [norm_nonneg p.1])

/-- **The summands are controlled by the sum.** If `Γ₁` and `Γ₂` are closed, closed under
multiplication by positive reals, and no nonzero `ξ ∈ Γ₁` has `-ξ ∈ Γ₂`, then for some `κ > 0`
every `a ∈ Γ₁` and `b ∈ Γ₂` satisfy `κ (‖a‖ + ‖b‖) ≤ ‖a + b‖`. -/
theorem exists_mul_norm_add_norm_le_norm_add [ProperSpace E] (h₁ : IsClosed Γ₁) (h₂ : IsClosed Γ₂)
    (hc₁ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₁, t • ξ ∈ Γ₁) (hc₂ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₂, t • ξ ∈ Γ₂)
    (hopp : ∀ ξ ∈ Γ₁, -ξ ∈ Γ₂ → ξ = 0) :
    ∃ κ > 0, ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, κ * (‖a‖ + ‖b‖) ≤ ‖a + b‖ := by
  -- The pairs with `‖a‖ + ‖b‖ = 1` form a compact set on which `‖a + b‖` is positive.
  set P : Set (E × E) := Γ₁ ×ˢ Γ₂ ∩ {p | ‖p.1‖ + ‖p.2‖ = 1}
  have hP : IsCompact P :=
    (isCompact_prod_inter_norm_add_norm_le h₁ h₂ 1).of_isClosed_subset
      ((h₁.prod h₂).inter (isClosed_eq (by fun_prop) continuous_const))
      fun p hp ↦ ⟨hp.1, hp.2.le⟩
  have hpos : ∀ p ∈ P, 0 < ‖p.1 + p.2‖ := by
    rintro ⟨a, b⟩ ⟨⟨ha, hb⟩, hab⟩
    refine norm_pos_iff.2 fun h ↦ ?_
    have hba : b = -a := eq_neg_of_add_eq_zero_right h
    have ha0 : a = 0 := hopp a ha (hba ▸ hb)
    simp [ha0, hba] at hab
  obtain ⟨κ, hκ, hκP⟩ := hP.exists_forall_le' (by fun_prop) hpos
  refine ⟨κ, hκ, fun a ha b hb ↦ ?_⟩
  rcases (add_nonneg (norm_nonneg a) (norm_nonneg b)).eq_or_lt with hs | hs
  · rw [← hs, mul_zero]
    exact norm_nonneg _
  -- Rescale `(a, b)` into `P`.
  have hs' : 0 < (‖a‖ + ‖b‖)⁻¹ := inv_pos.2 hs
  have hnorm : ‖(‖a‖ + ‖b‖)⁻¹ • a‖ + ‖(‖a‖ + ‖b‖)⁻¹ • b‖ = 1 := by
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hs'.le, ← mul_add, inv_mul_cancel₀ hs.ne']
  have h := hκP (_, _) ⟨⟨hc₁ _ hs' a ha, hc₂ _ hs' b hb⟩, hnorm⟩
  rw [← smul_add, norm_smul, Real.norm_of_nonneg hs'.le, le_inv_mul_iff₀ hs] at h
  rwa [mul_comm]

/-- **The sum of closed cones without opposite directions is closed.** If `Γ₁` and `Γ₂` are closed,
closed under multiplication by positive reals, and no nonzero `ξ ∈ Γ₁` has `-ξ ∈ Γ₂`, then
`Γ₁ + Γ₂` is closed. -/
theorem isClosed_add_of_forall_neg_mem_imp_eq_zero [ProperSpace E] (h₁ : IsClosed Γ₁)
    (h₂ : IsClosed Γ₂) (hc₁ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₁, t • ξ ∈ Γ₁)
    (hc₂ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₂, t • ξ ∈ Γ₂) (hopp : ∀ ξ ∈ Γ₁, -ξ ∈ Γ₂ → ξ = 0) :
    IsClosed (Γ₁ + Γ₂) := by
  obtain ⟨κ, hκ, hκab⟩ := exists_mul_norm_add_norm_le_norm_add h₁ h₂ hc₁ hc₂ hopp
  refine isClosed_of_closure_subset fun z hz ↦ ?_
  -- Near `z`, the sum is the image of the compact set of pairs with `‖a‖ + ‖b‖ ≤ R`.
  set R := (‖z‖ + 1) / κ
  set P : Set (E × E) := Γ₁ ×ˢ Γ₂ ∩ {p | ‖p.1‖ + ‖p.2‖ ≤ R}
  have hsub : (fun p : E × E ↦ p.1 + p.2) '' P ⊆ Γ₁ + Γ₂ := by
    rintro _ ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, -⟩, rfl⟩
    exact add_mem_add ha hb
  refine hsub (((isCompact_prod_inter_norm_add_norm_le h₁ h₂ R).image
    (by fun_prop)).isClosed.closure_subset ?_)
  rw [Metric.mem_closure_iff] at hz ⊢
  intro ε hε
  obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, hd⟩ := hz (min ε 1) (lt_min hε one_pos)
  refine ⟨a + b, ⟨(a, b), ⟨⟨ha, hb⟩, ?_⟩, rfl⟩, hd.trans_le (min_le_left _ _)⟩
  have hab : ‖a + b‖ ≤ ‖z‖ + 1 := by
    have h := norm_le_norm_add_norm_sub' (a + b) z
    rw [← dist_eq_norm, dist_comm] at h
    linarith [hd.trans_le (min_le_right ε 1)]
  simp only [mem_ofPred_eq]
  rw [le_div_iff₀ hκ, mul_comm]
  exact (hκab a ha b hb).trans hab

/-- The vectors `η` within `ε ‖η‖` of a set `Γ'` closed under multiplication by positive reals
form an open set containing `Γ' \ {0}`, whose complement is again closed under multiplication by
positive reals. -/
theorem exists_isOpen_forall_exists_norm_sub_lt {Γ' : Set E}
    (hc : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ', t • ξ ∈ Γ') {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set E, IsOpen U ∧ Γ' \ {0} ⊆ U ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Uᶜ, t • η ∈ Uᶜ) ∧
      ∀ η ∈ U, ∃ ξ ∈ Γ', ‖η - ξ‖ < ε * ‖η‖ := by
  refine ⟨⋃ ξ ∈ Γ', {η | ‖η - ξ‖ < ε * ‖η‖},
    isOpen_biUnion fun ξ _ ↦ isOpen_lt (by fun_prop) (by fun_prop),
    fun ξ hξ ↦ mem_biUnion hξ.1 (by simpa using mul_pos hε (norm_pos_iff.2 hξ.2)),
    forall_smul_mem_compl fun t ht η hη ↦ ?_, fun η hη ↦ by simpa using hη⟩
  -- The thickening itself is closed under multiplication by positive reals.
  obtain ⟨ξ, hξ, hηξ⟩ := mem_iUnion₂.1 hη
  refine mem_biUnion (hc t ht ξ hξ) ?_
  rw [mem_ofPred_eq] at hηξ ⊢
  rw [← smul_sub, norm_smul, norm_smul, Real.norm_of_nonneg ht.le, mul_left_comm]
  exact mul_lt_mul_of_pos_left hηξ ht

omit [NormedSpace ℝ E] in
/-- If `ζ` is at distance at least `α ‖ζ‖` from `ξ` and `ξ` is within `ε ‖u‖` of `u`, with
`ε ≤ min (1 / 2) (α / 2)`, then `ζ - u` has norm at least `α ‖ζ‖ / 4`. -/
private theorem mul_norm_le_norm_of_norm_sub_lt {α ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1 / 2)
    (hε₂ : ε ≤ α / 2) {ζ u v ξ : E} (huv : u + v = ζ) (hu : ‖u - ξ‖ < ε * ‖u‖)
    (hα : α * ‖ζ‖ ≤ ‖ζ - ξ‖) : α / 4 * ‖ζ‖ ≤ ‖v‖ := by
  have h1 : ‖ζ - ξ‖ ≤ ‖v‖ + ‖u - ξ‖ := by
    rw [← huv, show u + v - ξ = v + (u - ξ) by abel]
    exact norm_add_le _ _
  have h2 : ‖u‖ ≤ ‖ζ‖ + ‖v‖ := by
    rw [← huv]
    simpa using norm_sub_le (u + v) v
  have h3 : ε * ‖u‖ ≤ α / 2 * ‖ζ‖ + 1 / 2 * ‖v‖ := by
    calc ε * ‖u‖ ≤ ε * (‖ζ‖ + ‖v‖) := by gcongr
      _ = ε * ‖ζ‖ + ε * ‖v‖ := by ring
      _ ≤ α / 2 * ‖ζ‖ + 1 / 2 * ‖v‖ := by gcongr
  nlinarith [norm_nonneg ζ, norm_nonneg v]

omit [NormedSpace ℝ E] in
/-- If `ξ₁` is within `ε ‖η‖` of `η` and `ξ₂` within `ε ‖ζ - η‖` of `ζ - η`, the summands control
the sum, `κ (‖ξ₁‖ + ‖ξ₂‖) ≤ ‖ξ₁ + ξ₂‖`, and `ε` is small, then `ζ` is within `α ‖ζ‖` of
`ξ₁ + ξ₂`. -/
private theorem norm_sub_add_lt_mul_norm {κ α ε : ℝ} (hκ : 0 < κ) (hα : 0 ≤ α)
    (hε₃ : ε ≤ κ / (4 * (1 + κ))) (hε₄ : ε ≤ α * κ / 4) {ζ η ξ₁ ξ₂ : E}
    (he₁ : ‖η - ξ₁‖ < ε * ‖η‖) (he₂ : ‖ζ - η - ξ₂‖ < ε * ‖ζ - η‖)
    (hκ' : κ * (‖ξ₁‖ + ‖ξ₂‖) ≤ ‖ξ₁ + ξ₂‖) : ‖ζ - (ξ₁ + ξ₂)‖ < α * ‖ζ‖ := by
  have hη : ‖η‖ ≤ ‖ξ₁‖ + ‖η - ξ₁‖ := norm_le_norm_add_norm_sub' η ξ₁
  have hθ : ‖ζ - η‖ ≤ ‖ξ₂‖ + ‖ζ - η - ξ₂‖ := norm_le_norm_add_norm_sub' _ ξ₂
  have hsum : ‖ξ₁ + ξ₂‖ ≤ ‖ζ‖ + ‖η - ξ₁‖ + ‖ζ - η - ξ₂‖ := by
    calc ‖ξ₁ + ξ₂‖ = ‖ζ - (η - ξ₁) - (ζ - η - ξ₂)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le_of_le (norm_sub_le _ _) le_rfl
  have hdiff : ‖ζ - (ξ₁ + ξ₂)‖ ≤ ‖η - ξ₁‖ + ‖ζ - η - ξ₂‖ := by
    calc ‖ζ - (ξ₁ + ξ₂)‖ = ‖(η - ξ₁) + (ζ - η - ξ₂)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  -- With `s = ‖η‖ + ‖ζ - η‖`, first `κ s ≤ 4 ‖ζ‖ / 3`, then the errors are below `α ‖ζ‖ / 3`.
  set s := ‖η‖ + ‖ζ - η‖
  have hes : ‖η - ξ₁‖ + ‖ζ - η - ξ₂‖ < ε * s := by simp only [s]; linarith
  have hs : κ * s ≤ ‖ζ‖ + (1 + κ) * (ε * s) := by nlinarith
  have hκε : (1 + κ) * ε ≤ κ / 4 := by
    rw [le_div_iff₀ (by positivity)] at hε₃
    linarith
  have hs0 : 0 ≤ s := by positivity
  have hs' : κ * s ≤ 4 / 3 * ‖ζ‖ := by nlinarith
  have hεs : ε * s ≤ α / 3 * ‖ζ‖ := by
    calc ε * s ≤ α * κ / 4 * s := by gcongr
      _ = α / 4 * (κ * s) := by ring
      _ ≤ α / 4 * (4 / 3 * ‖ζ‖) := mul_le_mul_of_nonneg_left hs' (by positivity)
      _ = α / 3 * ‖ζ‖ := by ring
  nlinarith [norm_nonneg ζ, norm_nonneg (ζ - (ξ₁ + ξ₂))]

/-- **Conic neighbourhoods for the frequencies of a product.** Let `Γ₁` and `Γ₂` be closed sets
containing `0`, closed under multiplication by positive reals, without opposite nonzero vectors,
and let `ζ₀ ∉ Γ₁ + Γ₂`. Then there are open neighbourhoods `U₁ ⊇ Γ₁ \ {0}` and `U₂ ⊇ Γ₂ \ {0}`
whose complements are again closed under multiplication by positive reals, an open cone `Γ`
containing `ζ₀` and `c > 0` such that, for `ζ ∈ Γ`: if `η ∈ U₁`, then `ζ - η ∉ U₂` and
`c ‖ζ‖ ≤ ‖ζ - η‖`; and if `ζ - η ∈ U₂`, then `c ‖ζ‖ ≤ ‖η‖`. The sets `Uᵢ` are the vectors `η` within
`ε ‖η‖` of `Γᵢ` for a small `ε > 0`. -/
theorem exists_cones_of_notMem_add [ProperSpace E] (h₁ : IsClosed Γ₁) (h₂ : IsClosed Γ₂)
    (h0₁ : (0 : E) ∈ Γ₁) (h0₂ : (0 : E) ∈ Γ₂)
    (hc₁ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₁, t • ξ ∈ Γ₁) (hc₂ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₂, t • ξ ∈ Γ₂)
    (hopp : ∀ ξ ∈ Γ₁, -ξ ∈ Γ₂ → ξ = 0) {ζ₀ : E} (hζ₀ : ζ₀ ∉ Γ₁ + Γ₂) :
    ∃ U₁ U₂ : Set E, IsOpen U₁ ∧ IsOpen U₂ ∧ Γ₁ \ {0} ⊆ U₁ ∧ Γ₂ \ {0} ⊆ U₂ ∧
      (∀ t : ℝ, 0 < t → ∀ η ∈ U₁ᶜ, t • η ∈ U₁ᶜ) ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ U₂ᶜ, t • η ∈ U₂ᶜ) ∧
      ∃ Γ : Set E, IsOpen Γ ∧ ζ₀ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ ζ ∈ Γ, t • ζ ∈ Γ) ∧
        ∃ c > 0, ∀ ζ ∈ Γ, ∀ η, (η ∈ U₁ → ζ - η ∉ U₂ ∧ c * ‖ζ‖ ≤ ‖ζ - η‖) ∧
          (ζ - η ∈ U₂ → c * ‖ζ‖ ≤ ‖η‖) := by
  obtain ⟨κ, hκ, hκab⟩ := exists_mul_norm_add_norm_le_norm_add h₁ h₂ hc₁ hc₂ hopp
  -- An open cone `Γ` around `ζ₀` stays away from the closed cone `Γ₁ + Γ₂` proportionally to
  -- the norm.
  have hcl := isClosed_add_of_forall_neg_mem_imp_eq_zero h₁ h₂ hc₁ hc₂ hopp
  obtain ⟨Γ, hΓo, hζΓ, hΓc, α, hα, hball⟩ := hcl.isOpen_compl.exists_cone_closedBall_subset
    (forall_smul_mem_compl (forall_smul_mem_add hc₁ hc₂)) hζ₀
  have hαΓ : ∀ ζ ∈ Γ, ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, α * ‖ζ‖ ≤ ‖ζ - (a + b)‖ := fun ζ hζ a ha b hb ↦ by
    by_contra hlt
    refine hball ζ hζ (mem_closedBall.2 ?_) (add_mem_add ha hb)
    rw [dist_eq_norm, norm_sub_rev]
    exact (lt_of_not_ge hlt).le
  -- The thickenings of `Γ₁` and `Γ₂`.
  set ε := min (min (1 / 2) (α / 2)) (min (κ / (4 * (1 + κ))) (α * κ / 4))
  have hε : 0 < ε := by positivity
  have hε₁ : ε ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hε₂ : ε ≤ α / 2 := (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨U₁, hU₁, hsub₁, hcU₁, hmem₁⟩ := exists_isOpen_forall_exists_norm_sub_lt hc₁ hε
  obtain ⟨U₂, hU₂, hsub₂, hcU₂, hmem₂⟩ := exists_isOpen_forall_exists_norm_sub_lt hc₂ hε
  refine ⟨U₁, U₂, hU₁, hU₂, hsub₁, hsub₂, hcU₁, hcU₂, Γ, hΓo, hζΓ, hΓc, α / 4, by positivity,
    fun ζ hζ η ↦ ⟨fun hη ↦ ?_, fun hη ↦ ?_⟩⟩
  · obtain ⟨ξ₁, hξ₁, he₁⟩ := hmem₁ η hη
    refine ⟨fun hη' ↦ ?_, mul_norm_le_norm_of_norm_sub_lt hε.le hε₁ hε₂ (add_sub_cancel η ζ) he₁
      (by simpa using hαΓ ζ hζ ξ₁ hξ₁ 0 h0₂)⟩
    -- `η ∈ U₁` and `ζ - η ∈ U₂` would put `ζ` close to `Γ₁ + Γ₂`.
    obtain ⟨ξ₂, hξ₂, he₂⟩ := hmem₂ _ hη'
    exact (norm_sub_add_lt_mul_norm hκ hα.le ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _)) he₁ he₂ (hκab ξ₁ hξ₁ ξ₂ hξ₂)).not_ge
      (hαΓ ζ hζ ξ₁ hξ₁ ξ₂ hξ₂)
  · obtain ⟨ξ₂, hξ₂, he₂⟩ := hmem₂ _ hη
    exact mul_norm_le_norm_of_norm_sub_lt hε.le hε₁ hε₂ (sub_add_cancel ζ η) he₂
      (by simpa using hαΓ ζ hζ 0 h0₁ ξ₂ hξ₂)

end TauCeti
