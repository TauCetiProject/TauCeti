/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Holder

/-!
# Absorption of lower-order parabolic Hölder seminorms

Schauder estimates for parabolic equations bound the top-order part of the norm of
`C^{2+α, 1+α/2}`: the parabolic `α`-seminorms of the Hessian `D_x² u` and of the time derivative
`∂ₜ u`. The lower-order terms, the parabolic `α`-seminorms of `u` and of `D_x u`, must then be
absorbed: they are at most a small multiple of the top-order part plus a large multiple of the
supremum of `u`. This file proves that absorption on a slab `E × [a, b]`.

The parabolic seminorm is bounded by the sum of the separate spatial and temporal seminorms. A
function with bounded oscillation which is `β`-Hölder is `γ`-Hölder for every `γ ≤ β`, with
constant `K δ^(β - γ) + D δ^(-γ)` at every scale `δ > 0`; on a slab we use the spatial scale `ε`
and the temporal scale `ε²`. For `u` the higher exponents are Lipschitz in space and in time,
from the bounds on `D_x u` and `∂ₜ u`. For `D_x u` they are Lipschitz in space, from the bound on
`D_x² u`, and `(1 + α) / 2`-Hölder in time, with constant controlled by the parabolic seminorms
of `D_x² u` and `∂ₜ u`. The supremum of `D_x u` is in turn controlled by the Landau-type
inequality `‖D_x u‖ ≤ 2 ε⁻¹ ‖u‖_∞ + ε ‖D_x² u‖_∞`.

The resulting estimate, for `α ≤ 1` and `0 < ε ≤ 1`, is

`[u]_{α,par} + [D_x u]_{α,par} ≤ 6 ε^(1 - α) N + 14 ε^(-(1 + α)) ‖u‖_∞`,

where `N = ‖D_x² u‖_∞ + ‖∂ₜ u‖_∞ + [D_x² u]_{α,par} + [∂ₜ u]_{α,par}` is the top-order part.

Its constants depend neither on the dimension nor on the slab. For `α < 1` the coefficient
`6 ε^(1 - α)` of the top-order terms is as small as desired.

## Main declarations

* `TauCeti.ParabolicSpaceTime.spaceEHolderNorm_one_le_of_hasFDerivAt` and
  `TauCeti.ParabolicSpaceTime.timeEHolderNorm_one_le_of_hasDerivWithinAt`: bounded derivatives
  give Lipschitz bounds in space and in time.
* `TauCeti.ParabolicSpaceTime.eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le`:
  the parabolic seminorm with a smaller exponent, from separate seminorms and an oscillation
  bound.
* `TauCeti.ParabolicSpaceTime.eHolderNorm_add_eHolderNorm_le`: the absorption of the
  lower-order parabolic seminorms of `u` and `D_x u`.

## References

* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996.
* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004.
-/

public section
noncomputable section

open Set
open scoped ENNReal NNReal

namespace TauCeti.ParabolicSpaceTime

variable {E F : Type*} {a b : ℝ}

/-- **The parabolic seminorm at a smaller exponent.** Let `v` be a function on the slab
`E × [a, b]` whose values lie within distance `D` of each other, with spatial `β₁`-seminorm at most
`K₁` and temporal `β₂`-seminorm at most `K₂`. If `α ≤ β₁` and `α / 2 ≤ β₂`, then for all spatial
and temporal scales `δ₁, δ₂ > 0` the parabolic `α`-seminorm of `v` is at most
`K₁ δ₁^(β₁ - α) + D δ₁^(-α) + K₂ δ₂^(β₂ - α / 2) + D δ₂^(-α / 2)`. -/
theorem eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le [MetricSpace E]
    [PseudoMetricSpace F] {v : slab (E := E) a b → F} {α β₁ β₂ K₁ K₂ D δ₁ δ₂ : ℝ≥0}
    (h₁ : spaceEHolderNorm β₁ v ≤ K₁) (h₂ : timeEHolderNorm β₂ v ≤ K₂)
    (hD : ∀ p q, dist (v p) (v q) ≤ D) (hα₁ : α ≤ β₁) (hα₂ : α / 2 ≤ β₂) (hδ₁ : 0 < δ₁)
    (hδ₂ : 0 < δ₂) :
    eHolderNorm α v ≤ ↑(K₁ * δ₁ ^ ((β₁ : ℝ) - α) + D * δ₁ ^ (-(α : ℝ)) +
      (K₂ * δ₂ ^ ((β₂ : ℝ) - (α / 2 : ℝ≥0)) + D * δ₂ ^ (-((α / 2 : ℝ≥0) : ℝ)))) := by
  refine (eHolderNorm_le_spaceEHolderNorm_add_timeEHolderNorm α v).trans ?_
  rw [ENNReal.coe_add]
  gcongr
  · refine spaceEHolderNorm_le_iff.2 fun t => ?_
    have ht : HolderOnWith K₁ β₁ (fun x => v (slabMk x t)) univ :=
      fun x _ y _ => spaceEHolderNorm_le_iff.1 h₁ t x y
    exact fun x y => ht.of_le_of_dist_le (fun _ _ _ _ => hD _ _) hα₁ hδ₁ x (mem_univ x) y
      (mem_univ y)
  · refine timeEHolderNorm_le_iff.2 fun x => ?_
    have hx : HolderOnWith K₂ β₂ (fun t => v (slabMk x t)) univ :=
      fun t _ s _ => timeEHolderNorm_le_iff.1 h₂ x t s
    exact fun t s => hx.of_le_of_dist_le (fun _ _ _ _ => hD _ _) hα₂ hδ₂ t (mem_univ t) s
      (mem_univ s)

/-- Values bounded in norm by `C` on the slab lie within distance `2 C` of each other. -/
private theorem dist_le_two_mul_of_norm_le [SeminormedAddCommGroup F] {w : E → ℝ → F} {C : ℝ≥0}
    (hC : ∀ y, ∀ t ∈ Icc a b, ‖w y t‖ ≤ C) (p q : slab (E := E) a b) :
    dist (w (p : ParabolicSpaceTime E).space (slabTime p))
      (w (q : ParabolicSpaceTime E).space (slabTime q)) ≤ ((2 * C : ℝ≥0) : ℝ) := by
  have := add_le_add (hC (p : ParabolicSpaceTime E).space _ (slabTime p).2)
    (hC (q : ParabolicSpaceTime E).space _ (slabTime q).2)
  push_cast
  linarith [dist_le_norm_add_norm (w (p : ParabolicSpaceTime E).space (slabTime p))
    (w (q : ParabolicSpaceTime E).space (slabTime q))]

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Bounded time derivatives give a temporal Lipschitz bound.** If `w (x, ·)` has derivative
`wₜ (x, ·)` within `[a, b]`, and `‖wₜ (x, t)‖ ≤ C` on the slab `E × [a, b]`, then the temporal
Lipschitz seminorm of `w` on the slab is at most `C`. -/
theorem timeEHolderNorm_one_le_of_hasDerivWithinAt {w wₜ : E → ℝ → F} {C : ℝ≥0}
    (hw : ∀ y, ∀ t ∈ Icc a b, HasDerivWithinAt (w y) (wₜ y t) (Icc a b) t)
    (hC : ∀ y, ∀ t ∈ Icc a b, ‖wₜ y t‖ ≤ C) :
    timeEHolderNorm 1
        (fun p : slab (E := E) a b => w (p : ParabolicSpaceTime E).space (slabTime p)) ≤ C := by
  refine timeEHolderNorm_le_iff.2 fun x t s => ?_
  have hlip := ((convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (hw x)
    fun t ht => by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hC x t ht).to_restrict
  simpa only [space_slabMk, slabTime_slabMk, Set.domRestrict_apply] using holderWith_one.2 hlip t s

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Bounded spatial derivatives give a spatial Lipschitz bound.** If `w (·, t)` has derivative
`w' (·, t)` for every `t ∈ [a, b]`, and `‖w' (x, t)‖ ≤ C` on the slab `E × [a, b]`, then the
spatial Lipschitz seminorm of `w` on the slab is at most `C`. -/
theorem spaceEHolderNorm_one_le_of_hasFDerivAt {w : E → ℝ → F} {w' : E → ℝ → E →L[ℝ] F}
    {C : ℝ≥0} (hw : ∀ t ∈ Icc a b, ∀ y, HasFDerivAt (w · t) (w' y t) y)
    (hC : ∀ y, ∀ t ∈ Icc a b, ‖w' y t‖ ≤ C) :
    spaceEHolderNorm 1
        (fun p : slab (E := E) a b => w (p : ParabolicSpaceTime E).space (slabTime p)) ≤ C := by
  refine spaceEHolderNorm_le_iff.2 fun t x y => ?_
  have hlip := lipschitzOnWith_univ.1 (convex_univ.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun z _ => (hw t t.2 z).hasFDerivWithinAt)
    fun z _ => by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hC z t t.2)
  simpa only [space_slabMk, slabTime_slabMk] using holderWith_one.2 hlip x y

/-- The comparison of constants in `eHolderNorm_add_eHolderNorm_le`: with `M₁ = 2 M₀ / ε + M₂ ε`
and `K = H₂ + Hₜ`, the constants produced by
`eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le` for `u` and for its spatial gradient,
at the spatial scale `ε` and the temporal scale `ε²`, add up to at most
`6 ε^(1 - α) (M₂ + Mₜ + H₂ + Hₜ) + 14 ε^(-(1 + α)) M₀`. -/
private theorem absorption_constant_le {α ε M₀ M₂ Mₜ H₂ Hₜ : ℝ≥0} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (2 * M₀ / ε + M₂ * ε) * ε ^ (((1 : ℝ≥0) : ℝ) - α) + 2 * M₀ * ε ^ (-(α : ℝ)) +
        (Mₜ * (ε ^ 2) ^ (((1 : ℝ≥0) : ℝ) - (α / 2 : ℝ≥0)) +
          2 * M₀ * (ε ^ 2) ^ (-((α / 2 : ℝ≥0) : ℝ))) +
      (M₂ * ε ^ (((1 : ℝ≥0) : ℝ) - α) + 2 * (2 * M₀ / ε + M₂ * ε) * ε ^ (-(α : ℝ)) +
        ((H₂ + Hₜ) * (ε ^ 2) ^ ((((1 + α) / 2 : ℝ≥0) : ℝ) - (α / 2 : ℝ≥0)) +
          2 * (2 * M₀ / ε + M₂ * ε) * (ε ^ 2) ^ (-((α / 2 : ℝ≥0) : ℝ)))) ≤
      6 * ε ^ (1 - (α : ℝ)) * (M₂ + Mₜ + H₂ + Hₜ) + 14 * ε ^ (-(1 + (α : ℝ))) * M₀ := by
  rw [← NNReal.coe_le_coe]
  have hε' : (0 : ℝ) < ε := hε
  have hε₁' : (ε : ℝ) ≤ 1 := hε₁
  -- Every power is a power of `ε` times `P = ε^(-α) ≥ 1`.
  have hsq : ∀ r : ℝ, ((ε : ℝ) ^ 2) ^ r = (ε : ℝ) ^ (2 * r) := fun r => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε'.le]
    norm_num
  have h₁ : (ε : ℝ) ^ (1 - (α : ℝ)) = ε * (ε : ℝ) ^ (-(α : ℝ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hε', Real.rpow_one]
  have h₂ : (ε : ℝ) ^ (2 * (1 - (α : ℝ) / 2)) = ε ^ 2 * (ε : ℝ) ^ (-(α : ℝ)) := by
    rw [show 2 * (1 - (α : ℝ) / 2) = 2 + -α by ring, Real.rpow_add hε', Real.rpow_two]
  have h₃ : (ε : ℝ) ^ (2 * -((α : ℝ) / 2)) = (ε : ℝ) ^ (-(α : ℝ)) := by
    rw [show 2 * -((α : ℝ) / 2) = -α by ring]
  have h₄ : (ε : ℝ) ^ (2 * ((1 + (α : ℝ)) / 2 - (α : ℝ) / 2)) = ε := by
    rw [show 2 * ((1 + (α : ℝ)) / 2 - (α : ℝ) / 2) = 1 by ring, Real.rpow_one]
  have h₅ : (ε : ℝ) ^ (-(1 + (α : ℝ))) = (ε : ℝ) ^ (-(α : ℝ)) / ε := by
    rw [neg_add, Real.rpow_add hε', Real.rpow_neg_one, inv_mul_eq_div]
  have hP : 1 ≤ (ε : ℝ) ^ (-(α : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε' hε₁' (neg_nonpos.2 α.coe_nonneg)
  push_cast
  simp only [hsq, h₁, h₂, h₃, h₄, h₅]
  generalize (ε : ℝ) ^ (-(α : ℝ)) = P at hP ⊢
  rw [← sub_nonneg]
  have key : 6 * (ε * P) * (M₂ + Mₜ + H₂ + Hₜ) + 14 * (P / ε) * M₀ -
      ((2 * M₀ / ε + M₂ * ε) * (ε * P) + 2 * M₀ * P + (Mₜ * (ε ^ 2 * P) + 2 * M₀ * P) +
        (M₂ * (ε * P) + 2 * (2 * M₀ / ε + M₂ * ε) * P + ((H₂ + Hₜ) * ε +
          2 * (2 * M₀ / ε + M₂ * ε) * P))) =
      M₂ * (ε * P * (1 - ε)) + Mₜ * (ε * P * (6 - ε)) + (H₂ + Hₜ) * (ε * (6 * P - 1)) +
        6 * M₀ * (P * (1 / ε - 1)) := by
    field_simp
    ring
  rw [key]
  have h1e : 1 ≤ 1 / (ε : ℝ) := by rw [le_div_iff₀ hε']; linarith
  have : 0 ≤ (1 : ℝ) - ε := by linarith
  have : 0 ≤ (6 : ℝ) - ε := by linarith
  have : 0 ≤ 6 * P - 1 := by linarith
  have : 0 ≤ 1 / (ε : ℝ) - 1 := by linarith
  positivity

variable {u : E → ℝ → F} {u' : E → ℝ → E →L[ℝ] F} {u'' : E → ℝ → E →L[ℝ] E →L[ℝ] F}
  {uₜ : E → ℝ → F}

/-- **Absorption of the lower-order parabolic seminorms.** Let `u (x, t)` be twice
differentiable in `x ∈ E` and differentiable in `t` within `[a, b]`, with spatial derivatives
`u'`, `u''` and time derivative `uₜ`, bounded on the slab `E × [a, b]` by `‖u‖ ≤ M₀`,
`‖u''‖ ≤ M₂` and `‖uₜ‖ ≤ Mₜ`, and with parabolic `α`-seminorms `[u'']_{α,par} ≤ H₂` and
`[uₜ]_{α,par} ≤ Hₜ`. If `α ≤ 1` and `0 < ε ≤ 1`, then on the slab

`[u]_{α,par} + [u']_{α,par} ≤ 6 ε^(1 - α) (M₂ + Mₜ + H₂ + Hₜ) + 14 ε^(-(1 + α)) M₀`.

For `α < 1` the coefficient of the top-order quantities tends to zero with `ε`, so the parabolic
`α`-seminorms of `u` and of its spatial gradient are absorbed into the top-order part of the
`C^{2+α, 1+α/2}` norm, at the cost of a multiple of the supremum of `u`. -/
theorem eHolderNorm_add_eHolderNorm_le {α ε M₀ M₂ Mₜ H₂ Hₜ : ℝ≥0} (hα : α ≤ 1) (hε : 0 < ε)
    (hε₁ : ε ≤ 1) (hu' : ∀ t ∈ Icc a b, ∀ y, HasFDerivAt (u · t) (u' y t) y)
    (hu'' : ∀ t ∈ Icc a b, ∀ y, HasFDerivAt (u' · t) (u'' y t) y)
    (huₜ : ∀ y, ∀ t ∈ Icc a b, HasDerivWithinAt (u y) (uₜ y t) (Icc a b) t)
    (hM₀ : ∀ y, ∀ t ∈ Icc a b, ‖u y t‖ ≤ M₀) (hM₂ : ∀ y, ∀ t ∈ Icc a b, ‖u'' y t‖ ≤ M₂)
    (hMₜ : ∀ y, ∀ t ∈ Icc a b, ‖uₜ y t‖ ≤ Mₜ)
    (hH₂ : eHolderNorm α
      (fun p : slab (E := E) a b => u'' (p : ParabolicSpaceTime E).space (slabTime p)) ≤ H₂)
    (hHₜ : eHolderNorm α
      (fun p : slab (E := E) a b => uₜ (p : ParabolicSpaceTime E).space (slabTime p)) ≤ Hₜ) :
    eHolderNorm α (fun p : slab (E := E) a b => u (p : ParabolicSpaceTime E).space (slabTime p)) +
        eHolderNorm α
          (fun p : slab (E := E) a b => u' (p : ParabolicSpaceTime E).space (slabTime p)) ≤
      ↑(6 * ε ^ (1 - (α : ℝ)) * (M₂ + Mₜ + H₂ + Hₜ) + 14 * ε ^ (-(1 + (α : ℝ))) * M₀) := by
  -- The spatial derivative `u'` is Lipschitz in space with constant `M₂`, so the Landau-type
  -- inequality bounds it by `M₁ = 2 M₀ / ε + M₂ ε`.
  have hS₂ := spaceEHolderNorm_one_le_of_hasFDerivAt hu'' hM₂
  set M₁ : ℝ≥0 := 2 * M₀ / ε + M₂ * ε with hM₁_def
  have hM₁ : ∀ y, ∀ t ∈ Icc a b, ‖u' y t‖ ≤ M₁ := fun y t ht => by
    have hlip : HolderWith M₂ 1 fun x => u' x t := fun x z => by
      simpa only [space_slabMk, slabTime_slabMk] using spaceEHolderNorm_le_iff.1 hS₂ ⟨t, ht⟩ x z
    simpa [hM₁_def] using hlip.norm_le_of_hasFDerivAt (hu' t ht) (fun z => hM₀ z t ht)
      (NNReal.coe_pos.2 hε) y
  -- The temporal `(1 + α) / 2`-seminorm of `u'` is at most `H₂ + Hₜ`.
  have hK : timeEHolderNorm ((1 + α) / 2)
      (fun p : slab (E := E) a b => u' (p : ParabolicSpaceTime E).space (slabTime p)) ≤
        ((H₂ + Hₜ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_add]
    exact (timeEHolderNorm_le_eHolderNorm_add_eHolderNorm α hu' hu'' huₜ).trans
      (add_le_add hH₂ hHₜ)
  -- Lower the exponents at the spatial scale `ε` and the temporal scale `ε²`.
  have hα₂ : α / 2 ≤ 1 := (half_le_self α.coe_nonneg).trans hα
  have hα₂' : α / 2 ≤ (1 + α) / 2 := by gcongr; exact le_add_self
  have hε₂ : 0 < ε ^ 2 := by positivity
  have hU := eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le
    (spaceEHolderNorm_one_le_of_hasFDerivAt hu' hM₁)
    (timeEHolderNorm_one_le_of_hasDerivWithinAt huₜ hMₜ) (dist_le_two_mul_of_norm_le hM₀) hα
    hα₂ hε hε₂
  have hU' := eHolderNorm_le_of_spaceEHolderNorm_le_of_timeEHolderNorm_le hS₂ hK
    (dist_le_two_mul_of_norm_le hM₁) hα hα₂' hε hε₂
  refine (add_le_add hU hU').trans ?_
  rw [← ENNReal.coe_add, ENNReal.coe_le_coe]
  exact absorption_constant_le hε hε₁

end TauCeti.ParabolicSpaceTime
