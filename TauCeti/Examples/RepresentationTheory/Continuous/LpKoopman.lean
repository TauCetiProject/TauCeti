/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.TypeTags
public import TauCeti.MeasureTheory.Measure.Count.MeasurePreserving
public import TauCeti.RepresentationTheory.Continuous.LpKoopman
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Checks: the `Lᵖ` pullback representation

Checks for `TauCeti.lpKoopman`, the representation `π(g) f = f ∘ (g⁻¹ • ·)` on `Lp E p μ`:

* the identity element fixes every class, and `π(g⁻¹) (π(g) f) = f`, including for the zero
  measure;
* on `Fin 3` with counting measure, the cycle `0 → 1 → 2 → 0` (`finRotate 3`) sends the
  observable `(0, 1, 2)` to `(2, 0, 1)`; with the transposition `τ = (0 1)`,
  `π(c τ) f = π(c) (π(τ) f) = (2, 1, 0)`, while composing the other way round gives `(0, 2, 1)`,
  so the forward-element pullback `f ↦ f ∘ (g • ·)` would compose in the reverse order;
* for the translations `x ↦ t + x` of `ℝ` with Lebesgue measure (the action of
  `Multiplicative ℝ`), `π(t) 1_[0,1] = 1_[t,t+1]`, of `Lᵖ` norm `1` for every `1 ≤ p ≤ ∞`,
  although the total measure is infinite.
-/

public section

open MeasureTheory TauCeti Set
open scoped ENNReal

namespace TauCeti.Examples.LpKoopman

section General

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (μ : Measure X) (hμ : ∀ g : G, MeasurePreserving (g • ·) μ μ)

-- The identity element fixes every `Lᵖ` class.
example (f : Lp ℂ p μ) : lpKoopman ℂ ℂ p μ hμ 1 f = f := by
  simp

-- Applying `g` and then `g⁻¹` returns the original class.
example (g : G) (f : Lp ℂ p μ) : lpKoopman ℂ ℂ p μ hμ g⁻¹ (lpKoopman ℂ ℂ p μ hμ g f) = f := by
  simpa using (lpKoopman ℂ ℂ p μ hμ).apply_inv_apply (g := g⁻¹) (v := f)

end General

section FinThree

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Every permutation of `Fin 3` preserves counting measure. -/
theorem measurePreserving_perm_count (g : Equiv.Perm (Fin 3)) :
    MeasurePreserving (g • · : Fin 3 → Fin 3) Measure.count Measure.count :=
  Measure.measurePreserving_count (measurable_of_finite _) (MulAction.bijective g)

/-- Every permutation of `Fin 3` preserves the zero measure. -/
theorem measurePreserving_perm_zero (g : Equiv.Perm (Fin 3)) :
    MeasurePreserving (g • · : Fin 3 → Fin 3) 0 0 :=
  ⟨measurable_of_finite _, by simp⟩

-- Applying `g` and then `g⁻¹` returns the original class, for the zero measure too.
example (g : Equiv.Perm (Fin 3)) (f : Lp ℂ p (0 : Measure (Fin 3))) :
    lpKoopman ℂ ℂ p 0 measurePreserving_perm_zero g⁻¹
      (lpKoopman ℂ ℂ p 0 measurePreserving_perm_zero g f) = f := by
  simpa using (lpKoopman ℂ ℂ p 0 measurePreserving_perm_zero).apply_inv_apply (g := g⁻¹) (v := f)

/-- The observable `(a, b, c)` on `Fin 3`, as an `Lᵖ` class for counting measure. -/
noncomputable abbrev obs (a b c : ℂ) : Lp ℂ p (Measure.count : Measure (Fin 3)) :=
  MemLp.of_discrete.toLp ![a, b, c]

/-- The pullback of the observable `v = (a, b, c)` on `Fin 3` by a permutation `g` is the
observable `v ∘ g⁻¹`. -/
private theorem lpKoopman_obs (g : Equiv.Perm (Fin 3)) (a b c : ℂ) :
    lpKoopman ℂ ℂ p Measure.count measurePreserving_perm_count g (obs p a b c) =
      obs p (![a, b, c] (g⁻¹ • 0)) (![a, b, c] (g⁻¹ • 1)) (![a, b, c] (g⁻¹ • 2)) := by
  rw [lpKoopman_apply, Lp.toLp_compMeasurePreserving, MemLp.toLp_eq_toLp_iff,
    Filter.EventuallyEq, Measure.ae_count_iff]
  intro x
  fin_cases x <;> simp

omit [Fact (1 ≤ p)] in
/-- Two observables on `Fin 3` with counting measure are equal exactly when their entries are. -/
private theorem obs_eq_obs_iff {a b c a' b' c' : ℂ} :
    obs p a b c = obs p a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  rw [MemLp.toLp_eq_toLp_iff, Filter.EventuallyEq, Measure.ae_count_iff]
  refine ⟨fun h ↦ ⟨h 0, h 1, h 2⟩, fun ⟨ha, hb, hc⟩ x ↦ ?_⟩
  fin_cases x <;> simp [ha, hb, hc]

/-- **Check.** The cycle `0 → 1 → 2 → 0` sends the observable `(0, 1, 2)` to `(2, 0, 1)`. -/
theorem lpKoopman_finRotate :
    lpKoopman ℂ ℂ p Measure.count measurePreserving_perm_count (finRotate 3) (obs p 0 1 2) =
      obs p 2 0 1 := by
  simp [lpKoopman_obs, Equiv.Perm.smul_def, Equiv.Perm.inv_def]

/-- **Check.** For the cycle `c` and the transposition `τ = (0 1)`, the pullback of `(0, 1, 2)`
by `c τ` is `π(c) (π(τ) f) = (2, 1, 0)`. -/
theorem lpKoopman_finRotate_mul_swap :
    lpKoopman ℂ ℂ p Measure.count measurePreserving_perm_count (finRotate 3 * Equiv.swap 0 1)
      (obs p 0 1 2) =
      lpKoopman ℂ ℂ p Measure.count measurePreserving_perm_count (finRotate 3)
        (lpKoopman ℂ ℂ p Measure.count measurePreserving_perm_count (Equiv.swap 0 1)
          (obs p 0 1 2)) ∧
    lpKoopman ℂ ℂ p Measure.count measurePreserving_perm_count (finRotate 3 * Equiv.swap 0 1)
      (obs p 0 1 2) = obs p 2 1 0 := by
  refine ⟨by rw [map_mul, mul_apply_eq_comp], ?_⟩
  simp [lpKoopman_obs, Equiv.Perm.smul_def, Equiv.Perm.inv_def, Equiv.swap_apply_of_ne_of_ne]

/-- **Check.** Composing in the forward order, `π(τ) (π(c) f) = (0, 2, 1)`, differs from
`π(c τ) f = (2, 1, 0)`. -/
theorem lpKoopman_swap_lpKoopman_finRotate :
    lpKoopman ℂ ℂ p Measure.count measurePreserving_perm_count (Equiv.swap 0 1)
        (lpKoopman ℂ ℂ p Measure.count measurePreserving_perm_count (finRotate 3)
          (obs p 0 1 2)) = obs p 0 2 1 ∧
    obs p 0 2 1 ≠ obs p 2 1 0 := by
  refine ⟨?_, fun h ↦ by simpa using ((obs_eq_obs_iff p).mp h).1⟩
  simp [lpKoopman_obs, Equiv.Perm.smul_def, Equiv.Perm.inv_def, Equiv.swap_apply_of_ne_of_ne]

end FinThree

section Translation

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The indicator of `[a, a + 1]` as an `Lᵖ` class for Lebesgue measure. -/
noncomputable abbrev unitIcc (a : ℝ) : Lp ℂ p (volume : Measure ℝ) :=
  indicatorConstLp p (measurableSet_Icc (a := a) (b := a + 1)) (by simp) 1

/-- **Check.** The pullback of `1_[0,1]` by the translation by `t` is `1_[t,t+1]`. -/
theorem lpKoopman_unitIcc_zero (t : ℝ) :
    lpKoopman ℂ ℂ p volume (measurePreserving_multiplicative_smul volume)
      (Multiplicative.ofAdd t) (unitIcc p 0) = unitIcc p t := by
  rw [lpKoopman_apply, Lp.indicatorConstLp_compMeasurePreserving]
  congr 1
  ext x
  rw [mem_preimage, ← ofAdd_neg, ofAdd_smul, vadd_eq_add, mem_Icc, mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- **Check.** The pullback of `1_[0,1]` by any translation has `Lᵖ` norm `1`, for every
`1 ≤ p ≤ ∞`, although Lebesgue measure is infinite. -/
theorem norm_lpKoopman_unitIcc_zero (t : ℝ) :
    ‖lpKoopman ℂ ℂ p volume (measurePreserving_multiplicative_smul volume)
      (Multiplicative.ofAdd t) (unitIcc p 0)‖ = 1 := by
  rw [norm_lpKoopman_apply, norm_indicatorConstLp' (zero_lt_one.trans_le Fact.out).ne' (by simp)]
  simp

end Translation

end TauCeti.Examples.LpKoopman
