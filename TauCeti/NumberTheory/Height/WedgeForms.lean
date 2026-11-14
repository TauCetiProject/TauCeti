/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.LinearAlgebra.ExteriorPower.LinearForms

import TauCeti.Analysis.ExteriorPower.Plucker
import TauCeti.NumberTheory.Height.LinearForm

/-!
# Local Plücker bounds from nonvanishing wedge forms and projective height

Let `K` be a number field and `l : κ → Dual K (ι → K)` a finite linearly independent family of
linear forms on `ι → K`. Each `p`-wedge form `TauCeti.wedgeForms l p T` is a linear form on
`Set.powersetCard ι p → K` with a nonzero coefficient tuple
(`TauCeti.exists_ne_zero_forall_wedgeForms_eq_sum`). Whenever `wedgeForms l p T (plucker x) ≠ 0`,
combining the local Liouville inequality (`NumberField.InfinitePlace.iSup_mul_iSup_pow_mult_le`,
`NumberField.FinitePlace.iSup_mul_iSup_le`) with the minor bound on the `p × p` matrix of form
values bounds the local Plücker sup norm `⨆ s, v (plucker x s)` at a place `v` in terms of the
global projective height `Height.mulHeight (plucker x)` and columnwise bounds `b j` on `l j (x r)`
for `j ∈ T`.

* `NumberField.InfinitePlace.exists_one_le_forall_iSup_plucker_pow_mult_le`: at an infinite place
  `v`, some `A ≥ 1` (uniform across all `p`-subsets `T`, vectors `x`, and bounds `b`) satisfies
  `(⨆ s, v (plucker x s)) ^ v.mult ≤ A * mulHeight (plucker x) * (∏ j ∈ T, b j) ^ v.mult`. Notice
  that `mulHeight (plucker x)` carries exponent `1` rather than `v.mult`.
* `NumberField.FinitePlace.exists_one_le_forall_iSup_plucker_le`: at a finite place `v`, some
  `B ≥ 1` satisfies `⨆ s, v (plucker x s) ≤ B * mulHeight (plucker x) * ∏ j ∈ T, b j`.

Multiplying these estimates over the infinite places and a finite set of finite places yields lower
bounds on the projective height of `plucker x` — and hence on the relative height of the subspace
spanned by `x` — from upper bounds on `l j (x r)`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Lemma 7.5.21.
* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the absolute Subspace Theorem*,
  J. Reine Angew. Math. **548** (2002), Lemma 12.4.
-/

public section

open Height Module Set Set.powersetCard TauCeti

namespace NumberField

variable {K ι κ : Type*} [Field K] [NumberField K] [LinearOrder ι] [Fintype ι]
  [LinearOrder κ] [Finite κ]

/-- At an infinite place `v` where `l : κ → Dual K (ι → K)` is linearly independent, some uniform
constant `A ≥ 1` bounds `(⨆ s, v (plucker x s)) ^ v.mult` by
`A * mulHeight (plucker x) * (∏ j ∈ (T : Finset κ), b j) ^ v.mult` whenever `T` is a `p`-subset
whose wedge form `wedgeForms l p T` does not vanish at `plucker x` and `v (l j (x r)) ≤ b j` for
all `r` and `j ∈ T`. -/
theorem InfinitePlace.exists_one_le_forall_iSup_plucker_pow_mult_le (v : InfinitePlace K)
    {l : κ → Dual K (ι → K)} (hl : LinearIndependent K l) (p : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {x : Fin p → ι → K} (T : powersetCard κ p) {b : κ → ℝ},
      wedgeForms l p T (plucker x) ≠ 0 →
      (∀ r, ∀ j ∈ T, v (l j (x r)) ≤ b j) →
      (⨆ s, v (plucker x s)) ^ v.mult ≤
        A * mulHeight (plucker x) * (∏ j ∈ (T : Finset κ), b j) ^ v.mult := by
  choose α hα_ne hα_eq using fun T : powersetCard κ p ↦
    exists_ne_zero_forall_wedgeForms_eq_sum hl T
  have hα_pos (T : powersetCard κ p) : 0 < (⨆ s, v (α T s)) ^ v.mult := by
    obtain ⟨s₀, hs₀⟩ := Function.ne_iff.mp (hα_ne T)
    have : Nonempty (powersetCard ι p) := ⟨s₀⟩
    exact pow_pos ((InfinitePlace.pos_iff.mpr hs₀).trans_le (Finite.le_ciSup_of_le s₀ le_rfl)) _
  let d : powersetCard κ p → ℝ := fun T ↦
    (Fintype.card (powersetCard ι p) : ℝ) ^ Module.finrank ℚ K * mulHeight (α T) /
      (⨆ s, v (α T s)) ^ v.mult
  let D : ℝ := max 1 (⨆ T, d T)
  have hD1 : 1 ≤ D := le_max_left _ _
  refine ⟨D * (p.factorial : ℝ) ^ v.mult, one_le_mul_of_one_le_of_one_le hD1
    (one_le_pow₀ (by exact_mod_cast Nat.factorial_pos p)), fun {x} T {b} hne hb ↦ ?_⟩
  have : Nonempty (powersetCard κ p) := ⟨T⟩
  let w := plucker x
  have hliouv := v.iSup_mul_iSup_pow_mult_le (α T) w (hα_eq T w ▸ hne)
  rw [mul_pow, ← hα_eq T w] at hliouv
  have hdiv : (⨆ s, v (w s)) ^ v.mult ≤
      d T * mulHeight w * v (wedgeForms l p T w) ^ v.mult := by
    dsimp only [d]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀' (hα_pos T)]
    simpa only [mul_assoc] using hliouv
  have hD : (⨆ s, v (w s)) ^ v.mult ≤
      D * mulHeight w * v (wedgeForms l p T w) ^ v.mult :=
    hdiv.trans <| mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((Finite.le_ciSup_of_le T le_rfl).trans (le_max_right _ _)) (mulHeight_pos w).le)
      (by positivity)
  have hdom : v (wedgeForms l p T w) ≤ p.factorial * ∏ j ∈ (T : Finset κ), b j := by
    rw [← plucker_pi_apply]
    exact v.1.plucker_le_factorial_mul_prod _ _ hb
  refine hD.trans ?_
  calc D * mulHeight w * v (wedgeForms l p T w) ^ v.mult
      ≤ D * mulHeight w * (p.factorial * ∏ j ∈ (T : Finset κ), b j) ^ v.mult :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (apply_nonneg _ _) hdom _)
          (mul_nonneg (zero_le_one.trans hD1) (mulHeight_pos w).le)
    _ = D * (p.factorial : ℝ) ^ v.mult * mulHeight w *
          (∏ j ∈ (T : Finset κ), b j) ^ v.mult := by
        rw [mul_pow]; ring

/-- At a finite place `v` where `l : κ → Dual K (ι → K)` is linearly independent, some uniform
constant `B ≥ 1` bounds `⨆ s, v (plucker x s)` by
`B * mulHeight (plucker x) * ∏ j ∈ (T : Finset κ), b j` whenever `T` is a `p`-subset whose wedge
form `wedgeForms l p T` does not vanish at `plucker x` and `v (l j (x r)) ≤ b j` for all `r` and
`j ∈ T`. -/
theorem FinitePlace.exists_one_le_forall_iSup_plucker_le (v : FinitePlace K)
    {l : κ → Dual K (ι → K)} (hl : LinearIndependent K l) (p : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {x : Fin p → ι → K} (T : powersetCard κ p) {b : κ → ℝ},
      wedgeForms l p T (plucker x) ≠ 0 →
      (∀ r, ∀ j ∈ T, v (l j (x r)) ≤ b j) →
      ⨆ s, v (plucker x s) ≤
        B * mulHeight (plucker x) * ∏ j ∈ (T : Finset κ), b j := by
  choose α hα_ne hα_eq using fun T : powersetCard κ p ↦
    exists_ne_zero_forall_wedgeForms_eq_sum hl T
  have hα_pos (T : powersetCard κ p) : 0 < ⨆ s, v (α T s) := by
    obtain ⟨s₀, hs₀⟩ := Function.ne_iff.mp (hα_ne T)
    have : Nonempty (powersetCard ι p) := ⟨s₀⟩
    exact (FinitePlace.pos_iff.mpr hs₀).trans_le (Finite.le_ciSup_of_le s₀ le_rfl)
  let d : powersetCard κ p → ℝ := fun T ↦
    (Fintype.card (powersetCard ι p) : ℝ) ^ Module.finrank ℚ K * mulHeight (α T) / ⨆ s, v (α T s)
  refine ⟨max 1 (⨆ T, d T), le_max_left _ _, fun {x} T {b} hne hb ↦ ?_⟩
  have : Nonempty (powersetCard κ p) := ⟨T⟩
  let w := plucker x
  have hliouv := v.iSup_mul_iSup_le (α T) w (hα_eq T w ▸ hne)
  rw [← hα_eq T w] at hliouv
  have hdiv : ⨆ s, v (w s) ≤ d T * mulHeight w * v (wedgeForms l p T w) := by
    dsimp only [d]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀' (hα_pos T)]
    simpa only [mul_assoc] using hliouv
  have hD : ⨆ s, v (w s) ≤ max 1 (⨆ T, d T) * mulHeight w * v (wedgeForms l p T w) :=
    hdiv.trans <| mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((Finite.le_ciSup_of_le T le_rfl).trans (le_max_right _ _)) (mulHeight_pos w).le)
      (apply_nonneg _ _)
  have hdom : v (wedgeForms l p T w) ≤ ∏ j ∈ (T : Finset κ), b j := by
    rw [← plucker_pi_apply]
    exact v.1.plucker_le_prod v.add_le _ _ hb
  exact hD.trans <| mul_le_mul_of_nonneg_left hdom
    (mul_nonneg (zero_le_one.trans (le_max_left _ _)) (mulHeight_pos w).le)

end NumberField
