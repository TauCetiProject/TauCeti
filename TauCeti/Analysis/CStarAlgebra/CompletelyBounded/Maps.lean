/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyBounded.Basic

/-!
# The Banach space `CB(A, B)` of completely bounded maps

For C⋆-algebras `A` and `B`, the completely bounded linear maps `A → B` form a complex vector
space `CB(A, B)`, here the submodule `LinearMap.completelyBounded A B` of `A →ₗ[ℂ] B`. The cb norm
`‖φ‖_cb = sup_n ‖φₙ‖` makes it a normed space, and it is complete: a Cauchy sequence of
completely bounded maps converges pointwise, and the uniform estimates on the amplifications pass
to the limit.

## Main declarations

* `LinearMap.completelyBounded`: the submodule `CB(A, B)` of completely bounded maps.
* `LinearMap.completelyBounded.instNormedAddCommGroup`,
  `LinearMap.completelyBounded.instNormedSpace`: the cb norm on `CB(A, B)`.
* `LinearMap.completelyBounded.instCompleteSpace`: `CB(A, B)` is a Banach space.

## References

* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Chapter 3.
* G. Pisier, *Introduction to Operator Space Theory*, §1.2.
-/

public section

open scoped ComplexOrder
open Filter Topology

namespace LinearMap

variable (A B : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The space `CB(A, B)` of completely bounded linear maps between C⋆-algebras, as a submodule
of `A →ₗ[ℂ] B`. It carries the cb norm. -/
def completelyBounded : Submodule ℂ (A →ₗ[ℂ] B) where
  carrier := {φ | φ.IsCompletelyBounded}
  add_mem' := IsCompletelyBounded.add
  zero_mem' := isCompletelyBounded_zero
  smul_mem' c _ h := h.smul c

variable {A B}

@[simp, grind =]
theorem mem_completelyBounded {φ : A →ₗ[ℂ] B} :
    φ ∈ completelyBounded A B ↔ φ.IsCompletelyBounded :=
  (Iff.rfl)

namespace completelyBounded

/-- The norm on `CB(A, B)` is the cb norm. -/
noncomputable instance instNorm : Norm (completelyBounded A B) :=
  ⟨fun φ => cbNorm (φ : A →ₗ[ℂ] B)⟩

theorem norm_def (φ : completelyBounded A B) : ‖φ‖ = cbNorm (φ : A →ₗ[ℂ] B) :=
  (rfl)

theorem isCompletelyBounded (φ : completelyBounded A B) :
    (φ : A →ₗ[ℂ] B).IsCompletelyBounded :=
  φ.property

/-- The cb norm is a norm on `CB(A, B)`. -/
theorem normedSpaceCore : NormedSpace.Core ℂ (completelyBounded A B) where
  norm_nonneg φ := cbNorm_nonneg _
  norm_smul c φ := cbNorm_smul c _
  norm_triangle φ ψ := cbNorm_add_le φ.property ψ.property
  norm_eq_zero_iff φ := by
    rw [norm_def, cbNorm_eq_zero_iff φ.property, Submodule.coe_eq_zero]

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (completelyBounded A B) :=
  .ofCore normedSpaceCore

noncomputable instance instNormedSpace : NormedSpace ℂ (completelyBounded A B) :=
  .ofCore normedSpaceCore

/-- Every amplification of `φ ∈ CB(A, B)` is bounded by `‖φ‖`. -/
theorem norm_map_le_norm_mul (φ : completelyBounded A B) {κ : Type*} [Fintype κ]
    (x : CStarMatrix κ κ A) : ‖x.map (φ : A →ₗ[ℂ] B)‖ ≤ ‖φ‖ * ‖x‖ :=
  norm_map_le_cbNorm_mul φ.property x

/-- The level-one bound `‖φ a‖ ≤ ‖φ‖ ‖a‖` on `CB(A, B)`. -/
theorem norm_apply_le_norm_mul (φ : completelyBounded A B) (a : A) :
    ‖(φ : A →ₗ[ℂ] B) a‖ ≤ ‖φ‖ * ‖a‖ :=
  norm_apply_le_cbNorm_mul φ.property a

/-- Uniform estimates on the amplifications of `φₙ - φ` along a pointwise convergent sequence:
if `‖(φₙ - φₘ)ₖ‖ ≤ b N` whenever `N ≤ n, m`, then `‖(φₙ - φ)ₖ‖ ≤ b N` for `N ≤ n`. -/
private theorem norm_map_sub_limit_le {u : ℕ → A →ₗ[ℂ] B} {φ : A →ₗ[ℂ] B}
    (hφ : ∀ a, Tendsto (fun m => u m a) atTop (𝓝 (φ a))) {b : ℕ → ℝ}
    (hb : ∀ N n m, N ≤ n → N ≤ m → ∀ (k : ℕ) (x : CStarMatrix (Fin k) (Fin k) A),
      ‖x.map ⇑(u n - u m)‖ ≤ b N * ‖x‖)
    {N n : ℕ} (hn : N ≤ n) {k : ℕ} (x : CStarMatrix (Fin k) (Fin k) A) :
    ‖x.map ⇑(u n - φ)‖ ≤ b N * ‖x‖ := by
  have hlim : Tendsto (fun m => x.map ⇑(u n - u m)) atTop (𝓝 (x.map ⇑(u n - φ))) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => by
      simpa using tendsto_const_nhds.sub (hφ (x i j))
  exact le_of_tendsto hlim.norm (eventually_atTop.mpr ⟨N, fun m hm => hb N n m hn hm k x⟩)

/-- **`CB(A, B)` is complete.** -/
instance instCompleteSpace : CompleteSpace (completelyBounded A B) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨b, hb0, hb, hb_lim⟩ := cauchySeq_iff_le_tendsto_0.mp hu
  have hb' (N n m : ℕ) (hn : N ≤ n) (hm : N ≤ m) (k : ℕ) (x : CStarMatrix (Fin k) (Fin k) A) :
      ‖x.map ⇑((u n : A →ₗ[ℂ] B) - u m)‖ ≤ b N * ‖x‖ := by
    have := norm_map_le_norm_mul (u n - u m) x
    rw [← dist_eq_norm] at this
    exact this.trans (by gcongr; exact hb n m N hn hm)
  have hpt (a : A) : CauchySeq fun n => (u n : A →ₗ[ℂ] B) a := by
    refine cauchySeq_iff_le_tendsto_0.mpr ⟨fun N => b N * ‖a‖, fun N => by
      have := hb0 N; positivity, fun n m N hn hm => ?_, by simpa using hb_lim.mul_const ‖a‖⟩
    rw [dist_eq_norm, ← LinearMap.sub_apply, ← Submodule.coe_sub]
    refine (norm_apply_le_norm_mul _ a).trans ?_
    rw [← dist_eq_norm]
    exact mul_le_mul_of_nonneg_right (hb n m N hn hm) (norm_nonneg a)
  choose f hf using fun a => cauchySeq_tendsto_of_complete (hpt a)
  let φ : A →ₗ[ℂ] B :=
    linearMapOfTendsto f (fun n => (u n : A →ₗ[ℂ] B)) (tendsto_pi_nhds.mpr hf)
  have hφ (a : A) : Tendsto (fun m => (u m : A →ₗ[ℂ] B) a) atTop (𝓝 (φ a)) := hf a
  have hsub (N n : ℕ) (hn : N ≤ n) : ((u n : A →ₗ[ℂ] B) - φ).IsCompletelyBounded :=
    isCompletelyBounded_def.mpr ⟨b N, hb0 N, fun k x => norm_map_sub_limit_le hφ hb' hn x⟩
  have hφcb : φ.IsCompletelyBounded := by
    simpa using (u 0).property.sub (hsub 0 0 le_rfl)
  refine ⟨⟨φ, hφcb⟩, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hb_lim
  exact cbNorm_le_of_bound (hb0 n) fun k x => norm_map_sub_limit_le hφ hb' le_rfl x

end completelyBounded

end LinearMap
