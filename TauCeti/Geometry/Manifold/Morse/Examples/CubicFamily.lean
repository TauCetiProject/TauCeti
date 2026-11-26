/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.BirthDeath
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Critical points of the cubic family `x³ - t x`

The one-parameter family `f_t(x) = x³ - t x` on the real line is the simplest family in which
critical points are created: its derivative is `3 x² - t`, so

* for `t < 0` it has no critical point (`TauCeti.criticalPoints_pow_three_sub_mul_of_neg`);
* for `t = 0` it has the single critical point `0`, which is degenerate, so `f_0 = x³` is not a
  Morse function (`TauCeti.totalCriticalCount_pow_three_sub_mul_zero`,
  `TauCeti.isMorse_pow_three_sub_mul_iff`);
* for `t > 0` it has the two critical points `±√(t / 3)`
  (`TauCeti.criticalPoints_pow_three_sub_mul_of_pos`,
  `TauCeti.totalCriticalCount_pow_three_sub_mul_of_pos`), both nondegenerate: a local maximum of
  Morse index `1` at `-√(t / 3)` and a local minimum of Morse index `0` at `√(t / 3)`
  (`TauCeti.manifoldMorseIndex_pow_three_sub_mul_neg_sqrt`,
  `TauCeti.manifoldMorseIndex_pow_three_sub_mul_sqrt`,
  `TauCeti.criticalCount_pow_three_sub_mul_one_of_pos`,
  `TauCeti.criticalCount_pow_three_sub_mul_zero_of_pos`).

So `f_t` is a Morse function exactly when `t ≠ 0`. Near every parameter `t₀ ≠ 0`, each critical
point of `f_{t₀}` continues to a branch of nondegenerate critical points of the nearby `f_t`
(`TauCeti.IsNondegenerateCriticalPoint.exists_contDiffAt_criticalPoint_continuation`), but such a
continuation does not cross `t = 0`:

* no choice of critical points of `f_t` is defined for all `t` near `0`, because `f_t` has none for
  `t < 0` (`TauCeti.not_eventually_mem_criticalPoints_pow_three_sub_mul`);
* every choice `ψ t` of critical points of `f_t` for small `t > 0` tends to `0` as `t` decreases
  to `0` (`TauCeti.tendsto_zero_of_eventually_mem_criticalPoints_pow_three_sub_mul`), the degenerate
  critical point of `f_0`;
* a continuous choice over an interval of parameters is one of the two branches
  `t ↦ √(t / 3)` and `t ↦ -√(t / 3)`
  (`TauCeti.eqOn_sqrt_or_eqOn_neg_sqrt_of_mem_criticalPoints_pow_three_sub_mul`), and these two
  branches meet at `t = 0`.

Up to the factor `3`, `f_t` is the birth–death potential `x³ / 3 - s x` at the parameter
`s = t / 3` (`TauCeti.birthDeathPotential`), and the statements about branches are instances of
the corresponding statements for that potential.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS 39 (1970), 5–173.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

open Filter Set
open scoped Manifold Topology

namespace TauCeti

variable {t x : ℝ}

/-- The derivative of `x³ - t x` is `3 x² - t`. -/
private theorem hasDerivAt_pow_three_sub_mul (t x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y ^ 3 - t * y) (3 * x ^ 2 - t) x := by
  simpa using (hasDerivAt_pow 3 x).fun_sub ((hasDerivAt_id x).const_mul t)

/-- The second derivative of `x³ - t x` is `6 x`. -/
private theorem iteratedDeriv_two_pow_three_sub_mul (t x : ℝ) :
    iteratedDeriv 2 (fun y : ℝ ↦ y ^ 3 - t * y) x = 6 * x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one,
    funext fun y ↦ (hasDerivAt_pow_three_sub_mul t y).deriv]
  refine (((hasDerivAt_pow 2 x).const_mul 3).sub_const t).deriv.trans ?_
  ring

/-- **The critical points of `x³ - t x`** are the solutions of `3 x² = t`. -/
theorem mem_criticalPoints_pow_three_sub_mul_iff :
    x ∈ criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) ↔ 3 * x ^ 2 = t := by
  rw [mem_criticalPoints_iff_deriv_eq_zero, (hasDerivAt_pow_three_sub_mul t x).deriv, sub_eq_zero]

/-- The critical points of `x³ - t x` are those of the birth–death potential `x³ / 3 - s x` at the
parameter `s = t / 3`. -/
private theorem mem_criticalPoints_pow_three_sub_mul_iff_fderiv_birthDeathPotential_eq_zero :
    x ∈ criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) ↔
      fderiv ℝ (birthDeathPotential (t / 3)) x = 0 := by
  rw [mem_criticalPoints_pow_three_sub_mul_iff, fderiv_birthDeathPotential_eq_zero_iff]
  constructor <;> intro h <;> linarith

/-- For `t < 0`, the function `x³ - t x` has no critical point. -/
theorem criticalPoints_pow_three_sub_mul_of_neg (ht : t < 0) :
    criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦ fderiv_birthDeathPotential_ne_zero (by linarith) x
    (mem_criticalPoints_pow_three_sub_mul_iff_fderiv_birthDeathPotential_eq_zero.1 hx)

/-- For `t > 0`, the critical points of `x³ - t x` are `-√(t / 3)` and `√(t / 3)`. -/
theorem criticalPoints_pow_three_sub_mul_of_pos (ht : 0 < t) :
    criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) = {-√(t / 3), √(t / 3)} := by
  ext x
  rw [mem_criticalPoints_pow_three_sub_mul_iff_fderiv_birthDeathPotential_eq_zero,
    fderiv_birthDeathPotential_eq_zero_iff_of_nonneg (by positivity), mem_insert_iff,
    mem_singleton_iff]

/-- For `t < 0`, the function `x³ - t x` has no critical point. -/
theorem totalCriticalCount_pow_three_sub_mul_of_neg (ht : t < 0) :
    totalCriticalCount 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) = 0 := by
  rw [totalCriticalCount_def, criticalPoints_pow_three_sub_mul_of_neg ht, encard_empty]

/-- At `t = 0`, the function `x³ - t x` is `x³`, with the single critical point `0`. -/
theorem totalCriticalCount_pow_three_sub_mul_zero :
    totalCriticalCount 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - 0 * y) = 1 := by
  simp_rw [zero_mul, sub_zero]
  rw [totalCriticalCount_def, criticalPoints_pow (by norm_num), encard_singleton]

/-- For `t > 0`, the function `x³ - t x` has exactly two critical points. -/
theorem totalCriticalCount_pow_three_sub_mul_of_pos (ht : 0 < t) :
    totalCriticalCount 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) = 2 := by
  have h := Real.sqrt_pos.2 (div_pos ht three_pos)
  rw [totalCriticalCount_def, criticalPoints_pow_three_sub_mul_of_pos ht,
    encard_pair (by linarith)]

/-- **The cubic family is Morse exactly away from `t = 0`.** The function `x³ - t x` is a Morse
function on the line exactly when `t ≠ 0`: at `t = 0` its critical point `0` is degenerate. -/
theorem isMorse_pow_three_sub_mul_iff :
    IsMorse 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) ↔ t ≠ 0 := by
  have hcrit (x : ℝ) : fderiv ℝ (fun y : ℝ ↦ y ^ 3 - t * y) x = 0 ↔ 3 * x ^ 2 = t := by
    rw [← mem_criticalPoints_iff_fderiv_eq_zero, mem_criticalPoints_pow_three_sub_mul_iff]
  have hnd (x : ℝ) : IsNondegenerateCriticalPoint (fun y : ℝ ↦ y ^ 3 - t * y) x ↔
      3 * x ^ 2 = t ∧ x ≠ 0 := by
    rw [isNondegenerateCriticalPoint_real_iff (by fun_prop),
      (hasDerivAt_pow_three_sub_mul t x).deriv, iteratedDeriv_two_pow_three_sub_mul, sub_eq_zero]
    simp
  rw [isMorse_modelSpace_iff, hasNondegenerateCriticalPointsOn_iff]
  refine ⟨fun ⟨_, h⟩ ht ↦ ?_, fun ht ↦ ⟨by fun_prop, fun x _ hx ↦ (hnd x).2 ⟨(hcrit x).1 hx, ?_⟩⟩⟩
  · subst ht
    exact ((hnd 0).1 (h (mem_univ 0) ((hcrit 0).2 (by ring)))).2 rfl
  · rintro rfl
    exact ht (((hcrit 0).1 hx).symm.trans (by ring))

/-- For `t > 0`, the critical point `-√(t / 3)` of `x³ - t x` is a local maximum: its Morse index
is `1`. -/
theorem manifoldMorseIndex_pow_three_sub_mul_neg_sqrt (ht : 0 < t) :
    manifoldMorseIndex 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) (-√(t / 3)) = 1 := by
  have h := Real.sqrt_pos.2 (div_pos ht three_pos)
  rw [manifoldMorseIndex_modelSpace]
  exact morseIndex_real_of_neg (by rw [iteratedDeriv_two_pow_three_sub_mul]; linarith)

/-- For `t > 0`, the critical point `√(t / 3)` of `x³ - t x` is a local minimum: its Morse index
is `0`. -/
theorem manifoldMorseIndex_pow_three_sub_mul_sqrt (ht : 0 < t) :
    manifoldMorseIndex 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) √(t / 3) = 0 := by
  have h := Real.sqrt_pos.2 (div_pos ht three_pos)
  rw [manifoldMorseIndex_modelSpace]
  exact morseIndex_real_of_pos (by rw [iteratedDeriv_two_pow_three_sub_mul]; linarith)

/-- For `t > 0`, the function `x³ - t x` has exactly one critical point of Morse index `0`, the
local minimum `√(t / 3)`. -/
theorem criticalCount_pow_three_sub_mul_zero_of_pos (ht : 0 < t) :
    criticalCount 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) 0 = 1 := by
  rw [criticalCount_def, criticalPoints_pow_three_sub_mul_of_pos ht, ← encard_singleton √(t / 3)]
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl, hx⟩
    · exact absurd ((manifoldMorseIndex_pow_three_sub_mul_neg_sqrt ht).symm.trans hx) one_ne_zero
    · rfl
  · rintro rfl
    exact ⟨.inr rfl, manifoldMorseIndex_pow_three_sub_mul_sqrt ht⟩

/-- For `t > 0`, the function `x³ - t x` has exactly one critical point of Morse index `1`, the
local maximum `-√(t / 3)`. -/
theorem criticalCount_pow_three_sub_mul_one_of_pos (ht : 0 < t) :
    criticalCount 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) 1 = 1 := by
  rw [criticalCount_def, criticalPoints_pow_three_sub_mul_of_pos ht, ← encard_singleton (-√(t / 3))]
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl, hx⟩
    · rfl
    · exact absurd ((manifoldMorseIndex_pow_three_sub_mul_sqrt ht).symm.trans hx) zero_ne_one
  · rintro rfl
    exact ⟨.inl rfl, manifoldMorseIndex_pow_three_sub_mul_neg_sqrt ht⟩

/-! ### Branches of critical points do not cross `t = 0` -/

/-- **No branch of critical points crosses `t = 0`.** There is no choice of a critical point `ψ t`
of `x³ - t x` for all parameters `t` in a neighbourhood of `0`, since there is none for `t < 0`. -/
theorem not_eventually_mem_criticalPoints_pow_three_sub_mul (ψ : ℝ → ℝ) :
    ¬∀ᶠ t in 𝓝 0, ψ t ∈ criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y) := fun h ↦ by
  obtain ⟨t, hψ, ht⟩ :=
    ((h.filter_mono (nhdsWithin_le_nhds (s := Iio 0))).and self_mem_nhdsWithin).exists
  rw [criticalPoints_pow_three_sub_mul_of_neg ht] at hψ
  exact hψ

/-- **Branches of critical points end at the degenerate critical point.** Let `l` be a filter of
parameters converging to `0`, such as `𝓝[>] 0`. If `ψ t` is a critical point of `x³ - t x`
eventually along `l`, then `ψ t` tends to `0`, the degenerate critical point of `x³`. -/
theorem tendsto_zero_of_eventually_mem_criticalPoints_pow_three_sub_mul {l : Filter ℝ}
    (hl : l ≤ 𝓝 0) {ψ : ℝ → ℝ}
    (h : ∀ᶠ t in l, ψ t ∈ criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y)) :
    Tendsto ψ l (𝓝 0) :=
  tendsto_zero_of_eventually_fderiv_birthDeathPotential_eq_zero
    (((continuous_id.div_const 3).tendsto' 0 0 (zero_div 3)).mono_left hl)
    (h.mono fun _ ↦
      mem_criticalPoints_pow_three_sub_mul_iff_fderiv_birthDeathPotential_eq_zero.1)

/-- **The two branches of critical points.** A continuous choice `ψ t` of critical points of
`x³ - t x` over a preconnected set `T` of parameters, such as an interval, is one of the two
branches: `ψ t = √(t / 3)` for all `t ∈ T`, the local minima, or `ψ t = -√(t / 3)` for all
`t ∈ T`, the local maxima. The two branches meet at `t = 0`, where `ψ 0 = 0`; no parameter in `T`
is negative, since `x³ - t x` has no critical point for `t < 0`. -/
theorem eqOn_sqrt_or_eqOn_neg_sqrt_of_mem_criticalPoints_pow_three_sub_mul {T : Set ℝ}
    {ψ : ℝ → ℝ} (hT : IsPreconnected T) (hψ : ContinuousOn ψ T)
    (h : ∀ t ∈ T, ψ t ∈ criticalPoints 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 3 - t * y)) :
    EqOn ψ (fun t ↦ √(t / 3)) T ∨ EqOn ψ (fun t ↦ -√(t / 3)) T := by
  have h' (t : ℝ) (ht : t ∈ T) : fderiv ℝ (birthDeathPotential (t / 3)) (ψ t) = 0 :=
    mem_criticalPoints_pow_three_sub_mul_iff_fderiv_birthDeathPotential_eq_zero.1 (h t ht)
  have hT₀ : T ⊆ Ici 0 := fun t ht ↦ not_lt.1 fun hlt ↦ by
    simpa [criticalPoints_pow_three_sub_mul_of_neg hlt] using h t ht
  -- Away from `t = 0` the branch is one of the two square roots; at `t = 0` both vanish.
  have hext {g : ℝ → ℝ} (hg : g 0 = 0) (hE : EqOn ψ g (T ∩ Ioi 0)) : EqOn ψ g T := fun t ht ↦ by
    rcases (hT₀ ht).eq_or_lt with rfl | hpos
    · rw [hg, ← abs_eq_zero, abs_eq_sqrt_of_fderiv_birthDeathPotential_eq_zero (h' 0 ht),
        zero_div, Real.sqrt_zero]
    · exact hE ⟨ht, hpos⟩
  have hT' : IsPreconnected (T ∩ Ioi 0) := by
    rw [isPreconnected_iff_ordConnected] at hT ⊢
    exact hT.inter ordConnected_Ioi
  exact (eqOn_sqrt_or_eqOn_neg_sqrt_of_forall_fderiv_birthDeathPotential_eq_zero hT'
    (continuous_id.div_const 3).continuousOn (hψ.mono inter_subset_left)
    (fun _ ht ↦ (div_pos ht.2 three_pos).ne') fun t ht ↦ h' t ht.1).imp
    (hext (by simp)) (hext (by simp))

end TauCeti
