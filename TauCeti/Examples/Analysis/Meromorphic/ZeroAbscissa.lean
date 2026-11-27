/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
import TauCeti.Analysis.Meromorphic.Order

/-!
# Examples for the zero abscissa of a family

Worked values of `TauCeti.zeroAbscissa`, computed from its characterizing lemmas:

* the empty family has zero abscissa `1 / 2`;
* the family `{s - 3 / 4}` has zero abscissa `3 / 4`, while `{s - 1 / 4}` has `1 / 2`: a zero left
  of the critical line is not counted;
* the family `{s - 3 / 4, 1 / (s - 1)}` has zero abscissa `3 / 4`: the pole at `1` is not a zero;
* the family `{s - 2}`, which is not zero-free right of `1`, has zero abscissa `2`;
* the family consisting of the zero function has the junk value `0`, below `1 / 2`, which is why
  the lower bound `TauCeti.one_half_le_zeroAbscissa` assumes a common zero-free half-plane.
-/

public section

namespace TauCeti.ZeroAbscissaExamples

open TauCeti

/-- `s ↦ s - c` is zero-free right of `re c`: its only zero is `c`. -/
theorem zeroFreeRightOf_sub_const (c : ℂ) : ZeroFreeRightOf c.re (· - c) := by
  rw [zeroFreeRightOf_iff_of_analyticAt fun s _ => by fun_prop]
  intro s hs h
  rw [sub_eq_zero.1 h] at hs
  exact lt_irrefl _ hs

/-- The empty family has zero abscissa `1 / 2`. -/
example (L : Empty → ℂ → ℂ) : zeroAbscissa L = 1 / 2 := by
  simp

/-- The family `{s - 3 / 4}` has zero abscissa `3 / 4`. -/
example : zeroAbscissa (fun _ : Unit => (· - (3 / 4 : ℂ))) = 3 / 4 := by
  have h := zeroAbscissa_eq_re (L := fun _ : Unit => (· - (3 / 4 : ℂ))) (η := ()) (ρ := 3 / 4)
    (by norm_num) (by simp) fun _ => zeroFreeRightOf_sub_const _
  norm_num at h
  exact h

/-- The family `{s - 1 / 4}` has zero abscissa `1 / 2`: its zero lies left of the critical
line. -/
example : zeroAbscissa (fun _ : Unit => (· - (1 / 4 : ℂ))) = 1 / 2 := by
  have h : ZeroFreeRightOf (1 / 2) (· - (1 / 4 : ℂ)) :=
    (zeroFreeRightOf_sub_const _).mono (by norm_num)
  exact le_antisymm (zeroAbscissa_le le_rfl fun _ => h) (one_half_le_zeroAbscissa fun _ => h)

/-- The family `{s - 3 / 4, 1 / (s - 1)}` has zero abscissa `3 / 4`: the pole at `1` is not a
zero. -/
example : zeroAbscissa (fun b : Bool => if b then (· - (3 / 4 : ℂ)) else (· - (1 : ℂ))⁻¹) =
    3 / 4 := by
  have hpole : ZeroFreeRightOf ((3 / 4 : ℂ).re) (· - (1 : ℂ))⁻¹ :=
    zeroFreeRightOf_iff.2 fun s _ => by
      by_cases hs : s = 1
      · subst hs
        rw [meromorphicOrderAt_inv, meromorphicOrderAt_id_sub_const]
        decide
      · have hs' : s - 1 ≠ 0 := sub_ne_zero.2 hs
        exact (AnalyticAt.meromorphicOrderAt_nonpos_iff (by fun_prop)).2 (by simpa using hs')
  have h := zeroAbscissa_eq_re
    (L := fun b : Bool => if b then (· - (3 / 4 : ℂ)) else (· - (1 : ℂ))⁻¹) (η := true)
    (ρ := 3 / 4) (by norm_num) (by simp) fun b => by
      cases b
      · exact hpole
      · exact zeroFreeRightOf_sub_const _
  norm_num at h
  exact h

/-- The family `{s - 2}` has zero abscissa `2`, outside `[1 / 2, 1]`: it is not zero-free right
of `1`. -/
example : zeroAbscissa (fun _ : Unit => (· - (2 : ℂ))) = 2 := by
  have h := zeroAbscissa_eq_re (L := fun _ : Unit => (· - (2 : ℂ))) (η := ()) (ρ := 2)
    (by norm_num) (by simp) fun _ => zeroFreeRightOf_sub_const _
  norm_num at h
  exact h

/-- The family consisting of the zero function has unbounded zero real parts, and its zero
abscissa is the junk value `0`. -/
example : zeroAbscissa (fun _ : Unit => (0 : ℂ → ℂ)) = 0 := by
  rw [zeroAbscissa_def]
  refine Real.sSup_of_not_bddAbove fun ⟨M, hM⟩ => ?_
  have hmem := hM (Set.mem_insert_of_mem _ ⟨(), ((max M 1 + 1 : ℝ) : ℂ), ?_, by simp, rfl⟩)
  · simp only [Complex.ofReal_re] at hmem
    linarith [le_max_left M 1]
  · simp only [Complex.ofReal_re]
    linarith [le_max_right M 1]

end TauCeti.ZeroAbscissaExamples
