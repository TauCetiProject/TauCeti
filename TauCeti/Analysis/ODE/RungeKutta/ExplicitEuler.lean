/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.OneStep.Consistency
public import TauCeti.Analysis.ODE.RungeKutta.Basic
import TauCeti.Analysis.Calculus.Taylor.LipschitzDeriv

/-!
# The explicit Euler method

The explicit Euler tableau evaluates the field at the start of the step. Its increment is
`f t u`, independent of the step size. If the exact velocity is `M`-Lipschitz, the step
defect is bounded by `M h² / 2` by `TauCeti.norm_sub_sub_smul_le_of_lipschitzOnWith`.

The discrete one-step stability estimate propagates the defect on a variable mesh. The same
bound applies between nodes by shortening the final step to reach the evaluation time.

## Main results

* `TauCeti.explicitEuler_increment` identifies the increment with the initial field value.
* `TauCeti.explicitEuler_defect_le` gives the quadratic defect bound.
* `TauCeti.explicitEuler_error_le` and `TauCeti.explicitEuler_polygon_error_le` bound the
  nodal and piecewise affine errors, including an initial error.
* `TauCeti.exists_forall_explicitEuler_error_le` gives convergence for continuous exact velocity
  with the field still Lipschitz in state.

## References

* E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, University of
  Oxford, 2022, Section 2.2, equations (19) and (20) for the scalar defect and global error.
-/

public section

open Set
open scoped NNReal

namespace TauCeti

/-- The explicit Euler tableau with zero matrix, unit weight and zero node. -/
def explicitEuler : ButcherTableau 1 where
  A := 0
  b := 1
  c := 0

/-- The explicit Euler tableau has a zero stage matrix. -/
@[simp]
theorem explicitEuler_A : explicitEuler.A = 0 := (rfl)

/-- The unique weight of the explicit Euler tableau is one. -/
@[simp]
theorem explicitEuler_b : explicitEuler.b = 1 := (rfl)

/-- The unique node of the explicit Euler tableau is zero. -/
@[simp]
theorem explicitEuler_c : explicitEuler.c = 0 := (rfl)

/-- The explicit Euler tableau is strictly lower triangular. -/
@[simp]
theorem explicitEuler_isExplicit : explicitEuler.IsExplicit := by
  simp [ButcherTableau.isExplicit_iff]

section Algebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The stage vector of the explicit Euler tableau evaluates the field at the start of the
step. -/
@[simp]
theorem explicitEuler_stages_apply (f : ℝ → E → E) (t : ℝ) (u : E) (h : ℝ) (i : Fin 1) :
    explicitEuler.stages f t u h i = f t u := by
  have hs := explicitEuler_isExplicit.isStage_stages (f := f) (t := t) (y := u) (h := h)
  simpa using ButcherTableau.isStage_iff.mp hs i

/-- The explicit Euler increment is the field evaluated at the initial time and state. -/
@[simp]
theorem explicitEuler_increment (f : ℝ → E → E) (t : ℝ) (u : E) (h : ℝ) :
    explicitEuler.increment f t u h = f t u := by
  simp [ButcherTableau.increment_def]

end Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ → E → E} {y : ℝ → E} {a b : ℝ} {L M : ℝ≥0}

/-- With an `M`-Lipschitz exact velocity, the Euler defect for a step inside `[a, b]` is at most
`M h² / 2`. The two endpoints may lie in either order. -/
theorem explicitEuler_defect_le (hy : IsIntegralCurveOn y f (Icc a b))
    (hM : LipschitzOnWith M (fun r ↦ f r (y r)) (Icc a b)) {t h : ℝ}
    (ht : t ∈ Icc a b) (hth : t + h ∈ Icc a b) :
    ‖oneStepDefect (explicitEuler.increment f) y t h‖ ≤ M / 2 * h ^ 2 := by
  simpa [oneStepDefect_def, div_mul_eq_mul_div] using
    (norm_sub_sub_smul_le_of_lipschitzOnWith (fun r hr ↦ hy r hr) hM ht hth)

/-- The explicit Euler nodal error on a variable mesh is bounded by the Grönwall envelope
with rate `M hmax / 2` and the actual initial error. -/
theorem explicitEuler_error_le (hy : IsIntegralCurveOn y f (Icc a b))
    (hM : LipschitzOnWith M (fun r ↦ f r (y r)) (Icc a b))
    (hL : ∀ t ∈ Icc a b, LipschitzWith L (f t)) (y₀ : E)
    {h : ℕ → ℝ} {hmax : ℝ} {N n : ℕ} (hh : ∀ k < N, 0 ≤ h k ∧ h k ≤ hmax)
    (hb : meshNode a h N ≤ b) (hn : n ≤ N) :
    ‖y (meshNode a h n) - oneStepSeq (explicitEuler.increment f) a h y₀ n‖ ≤
      gronwallBound ‖y a - y₀‖ L (M * hmax / 2) (meshNode a h n - a) := by
  have hlip (k : ℕ) (hk : k < N) :
      LipschitzWith L (fun u ↦ explicitEuler.increment f (meshNode a h k) u (h k)) := by
    have hh₀ : ∀ j < N, 0 ≤ h j := fun j hj ↦ (hh j hj).1
    have hka := self_le_meshNode (t₀ := a) hh₀ hk.le
    have hkb := (monotoneOn_meshNode hh₀ (mem_Iic.2 hk.le) (mem_Iic.2 le_rfl) hk.le).trans hb
    simpa only [explicitEuler_increment] using hL _ ⟨hka, hkb⟩
  simpa [div_mul_eq_mul_div] using
    (norm_sub_oneStepSeq_le (p := 1) (C := (M : ℝ) / 2) y₀ hh hb hlip
      (fun t s ht hs _ hts ↦ explicitEuler_defect_le hy hM
        ⟨ht, (le_add_of_nonneg_right hs).trans hts⟩ ⟨ht.trans (le_add_of_nonneg_right hs), hts⟩)
      hn)

/-- The Euler polygon on a mesh interval has the same error bound at each interior point as a
node reached by a shortened final Euler step. -/
theorem explicitEuler_polygon_error_le (hy : IsIntegralCurveOn y f (Icc a b))
    (hM : LipschitzOnWith M (fun r ↦ f r (y r)) (Icc a b))
    (hL : ∀ t ∈ Icc a b, LipschitzWith L (f t)) (y₀ : E)
    {h : ℕ → ℝ} {hmax t : ℝ} {n : ℕ} (hh : ∀ k ≤ n, 0 ≤ h k ∧ h k ≤ hmax)
    (ht : t ∈ Icc (meshNode a h n) (meshNode a h (n + 1))) (htb : t ≤ b) :
    ‖y t - (oneStepSeq (explicitEuler.increment f) a h y₀ n +
        (t - meshNode a h n) • f (meshNode a h n)
          (oneStepSeq (explicitEuler.increment f) a h y₀ n))‖ ≤
      gronwallBound ‖y a - y₀‖ L (M * hmax / 2) (t - a) := by
  let steps := Function.update h n (t - meshNode a h n)
  have hprefix (k : ℕ) (hk : k < n) : steps k = h k := Function.update_of_ne hk.ne ..
  have hmesh := meshNode_congr (t₀ := a) hprefix
  have hseq := oneStepSeq_congr (Φ := explicitEuler.increment f) (t₀ := a) (y₀ := y₀) hprefix
  have hsteps (k : ℕ) (hk : k < n + 1) : 0 ≤ steps k ∧ steps k ≤ hmax := by
    rcases (Nat.le_of_lt_succ hk).eq_or_lt with rfl | hkn
    · have ht' := ht.2
      rw [meshNode_succ] at ht'
      simpa [steps] using And.intro (sub_nonneg.mpr ht.1)
        ((sub_le_iff_le_add.mpr (by simpa [add_comm] using ht')).trans (hh k le_rfl).2)
    · rw [hprefix k hkn]
      exact hh k hkn.le
  have hlast : meshNode a steps (n + 1) = t := by
    rw [meshNode_succ, hmesh]
    simp [steps]
  have hb : meshNode a steps (n + 1) ≤ b := hlast.le.trans htb
  have herr := explicitEuler_error_le hy hM hL y₀ hsteps hb (n := n + 1) le_rfl
  simpa [hlast, oneStepSeq_succ, hseq, hmesh, steps] using herr

/-- For exact initial data, Euler converges as the largest step tends to zero if the exact
velocity is continuous and the field is uniformly Lipschitz in the state on the time interval. -/
theorem exists_forall_explicitEuler_error_le (hy : IsIntegralCurveOn y f (Icc a b))
    (hvel : ContinuousOn (fun r ↦ f r (y r)) (Icc a b))
    (hL : ∀ t ∈ Icc a b, LipschitzWith L (f t)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (h : ℕ → ℝ) (N : ℕ), (∀ k < N, 0 ≤ h k ∧ h k ≤ δ) → meshNode a h N ≤ b →
      ∀ n ≤ N, ‖y (meshNode a h n) - oneStepSeq (explicitEuler.increment f) a h (y a) n‖ ≤ ε := by
  refine exists_forall_norm_sub_oneStepSeq_le_of_forall_norm_oneStepDefect_le (h₀ := 1) (L := L)
    zero_lt_one (fun t s ht hs _ hts ↦ ?_) (fun τ hτ ↦ ?_) hε
  · simpa only [explicitEuler_increment] using hL t ⟨ht, (le_add_of_nonneg_right hs).trans hts⟩
  · apply exists_forall_norm_oneStepDefect_le_of_consistent (h₀ := 1) zero_lt_one hy _ _ hτ
    · simpa only [explicitEuler_increment, Function.comp_def] using
        hvel.comp continuousOn_fst mapsTo_fst_prod
    · simp

end TauCeti
