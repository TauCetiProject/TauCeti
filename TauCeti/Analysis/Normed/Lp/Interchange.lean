/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Interchange between sequence `lp` and finite `PiLp`

For an arbitrary index type `α`, a finite index type `ι`, and a family `E : α → ι → Type*` of normed
groups, a sequence `f : ∀ a, PiLp q (E a)` belongs to `lp (fun a ↦ PiLp q (E a)) p` if and only if
every coordinate sequence `a ↦ f a i` belongs to `lp (fun a ↦ E a i) p` (`memℓp_piLp_iff`).

When the sequence and fibre exponents coincide (`q = p`) and `1 ≤ p ≤ ∞`, coordinatewise evaluation
is moreover an exact linear isometry equivalence `lp.piLpEquiv`:

`lp (fun a ↦ PiLp p (E a)) p ≃ₗᵢ[𝕜] PiLp p (fun i ↦ lp (fun a ↦ E a i) p)`.

At `p = 2` over `ℝ` or `ℂ`, this identifies vector-valued `ℓ²` sequences with finite Hilbert direct
sums of scalar or fibrewise `ℓ²` sequence spaces.

## Main definitions

* `lp.piLpEquiv`: `lp (fun a ↦ PiLp p (E a)) p ≃ₗᵢ[𝕜] PiLp p (fun i ↦ lp (fun a ↦ E a i) p)`.

## Main results

* `memℓp_piLp_iff`: `Memℓp f p ↔ ∀ i, Memℓp (fun a ↦ f a i) p`.
* `lp.piLpEquiv_apply`, `lp.piLpEquiv_symm_apply`: coordinatewise evaluation formulas for
  `lp.piLpEquiv` and its inverse.
-/

public section

noncomputable section

open scoped ENNReal

section Memℓp

variable {α ι : Type*} [Fintype ι] {E : α → ι → Type*} [∀ a i, NormedAddCommGroup (E a i)]
  {p q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- A sequence of finite `PiLp` vectors lies in `ℓᵖ` if and only if each coordinate sequence lies
in `ℓᵖ`. -/
theorem memℓp_piLp_iff {f : ∀ a, PiLp q (E a)} :
    Memℓp f p ↔ ∀ i, Memℓp (fun a ↦ f a i) p := by
  refine ⟨fun hf i ↦ hf.mono' fun a ↦ PiLp.norm_apply_le (f a) i, fun hf ↦ ?_⟩
  classical
  have hsingle (i : ι) : Memℓp (fun a ↦ PiLp.single q i (f a i)) p :=
    (hf i).mono' fun a ↦ (PiLp.norm_single q (E a) i (f a i)).le
  have hsum : ∀ s : Finset ι, Memℓp (fun a ↦ ∑ i ∈ s, PiLp.single q i (f a i)) p := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (zero_mem_ℓp' (E := fun a ↦ PiLp q (E a)) (p := p))
    | insert j s hj ih =>
        simpa only [Finset.sum_insert hj, Pi.add_def] using (hsingle j).add ih
  have hfeq : (fun a ↦ ∑ i, PiLp.single q i (f a i)) = f := by
    funext a
    ext j
    simp
  exact hfeq ▸ hsum Finset.univ

alias ⟨Memℓp.eval_piLp, Memℓp.of_eval_piLp⟩ := memℓp_piLp_iff

end Memℓp

namespace lp

variable {α ι : Type*} [Fintype ι]

section NormedRing

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*) [NormedRing 𝕜]
  (E : α → ι → Type*) [∀ a i, NormedAddCommGroup (E a i)] [∀ a i, Module 𝕜 (E a i)]
  [∀ a i, IsBoundedSMul 𝕜 (E a i)]

private theorem norm_toLp_eval_eq (f : lp (fun a ↦ PiLp p (E a)) p) :
    ‖WithLp.toLp p (fun i ↦ (⟨fun a ↦ f a i, (lp.memℓp f).eval_piLp i⟩ :
      lp (fun a ↦ E a i) p))‖ = ‖f‖ := by
  set g : ∀ i, lp (fun a ↦ E a i) p := fun i ↦ ⟨fun a ↦ f a i, (lp.memℓp f).eval_piLp i⟩
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hf0 : f = 0 := by
      ext a i
      exact IsEmpty.elim hι i
    simp [hf0, Subsingleton.elim (WithLp.toLp p g) 0]
  rcases eq_or_ne p ∞ with rfl | hp
  · apply le_antisymm
    · rw [PiLp.norm_eq_ciSup]
      refine ciSup_le fun i ↦ lp.norm_le_of_forall_le (norm_nonneg f) fun a ↦ ?_
      exact (PiLp.norm_apply_le (f a) i).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero f a)
    · refine lp.norm_le_of_forall_le (norm_nonneg (WithLp.toLp ∞ g)) fun a ↦ ?_
      rw [PiLp.norm_eq_ciSup, PiLp.norm_eq_ciSup]
      refine ciSup_le fun i ↦ ?_
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (g i) a).trans
        (le_ciSup (Set.finite_range fun j ↦ ‖g j‖).bddAbove i)
  · have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
    have hpow : ∑ i, ‖g i‖ ^ p.toReal = ‖f‖ ^ p.toReal := by
      calc ∑ i, ‖g i‖ ^ p.toReal
          = ∑ i, ∑' a, ‖f a i‖ ^ p.toReal := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              exact lp.norm_rpow_eq_tsum hr (g i)
        _ = ∑' a, ∑ i, ‖f a i‖ ^ p.toReal := by
              symm
              exact Summable.tsum_finsetSum fun i _ ↦ ((lp.memℓp (g i)).summable hr)
        _ = ∑' a, ‖f a‖ ^ p.toReal := by
              refine tsum_congr fun a ↦ ?_
              rw [PiLp.norm_eq_sum hr, ← Real.rpow_mul
                (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
                one_div_mul_cancel hr.ne', Real.rpow_one]
        _ = ‖f‖ ^ p.toReal := (lp.norm_rpow_eq_tsum hr f).symm
    rw [PiLp.norm_eq_sum hr]
    calc (∑ i, ‖g i‖ ^ p.toReal) ^ (1 / p.toReal)
        = (‖f‖ ^ p.toReal) ^ (1 / p.toReal) := by rw [hpow]
      _ = ‖f‖ := by
          rw [← Real.rpow_mul (norm_nonneg f), mul_one_div_cancel hr.ne', Real.rpow_one]

/-- Coordinatewise evaluation identifies `lp (fun a ↦ PiLp p (E a)) p` linear-isometrically with
`PiLp p (fun i ↦ lp (fun a ↦ E a i) p)` for every `1 ≤ p ≤ ∞` on a finite index type `ι`. -/
def piLpEquiv :
    lp (fun a ↦ PiLp p (E a)) p ≃ₗᵢ[𝕜] PiLp p (fun i ↦ lp (fun a ↦ E a i) p) where
  toFun f := WithLp.toLp p fun i ↦ ⟨fun a ↦ f a i, (lp.memℓp f).eval_piLp i⟩
  invFun g := ⟨fun a ↦ WithLp.toLp p fun i ↦ g i a, Memℓp.of_eval_piLp fun i ↦ lp.memℓp (g i)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' := norm_toLp_eval_eq p E

variable {p 𝕜 E}

/-- Coordinatewise evaluation of `lp.piLpEquiv`. -/
@[simp]
theorem piLpEquiv_apply (f : lp (fun a ↦ PiLp p (E a)) p) (i : ι) (a : α) :
    piLpEquiv p 𝕜 E f i a = f a i :=
  (rfl)

/-- Coordinatewise evaluation of `(lp.piLpEquiv).symm`. -/
@[simp]
theorem piLpEquiv_symm_apply (g : PiLp p (fun i ↦ lp (fun a ↦ E a i) p)) (a : α) (i : ι) :
    (piLpEquiv p 𝕜 E).symm g a i = g i a :=
  (rfl)

end NormedRing

end lp
