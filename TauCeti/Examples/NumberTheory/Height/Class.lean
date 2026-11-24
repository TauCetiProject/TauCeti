/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Class
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Filter.Cofinite

/-!
# Tests of height classes

Height classes on `ℕ` separate unbounded growth rates and forget bounded oscillation:
`[(-1)^n] = 0`, `[n + 7] = [n]` and `[n + (-1)^n] = [n]`, while `[n] ≠ 0` and `[2n] ≠ [n]`.
The classes carry no multiplication, since `[1] = [0]` but `[n · 1] ≠ [n · 0]`. Pulling back
along doubling multiplies `[n]` by `2`; pulling back along the inclusion of `{0}` kills it, so
surjectivity is needed to detect classes. Northcott passes to `n + (-1)^n` and to the pullback
along `ℕ × Fin 2 → ℕ`, but not along `ℕ × ℕ → ℕ`, whose fibres are infinite.
-/

public section

namespace TauCeti.HeightClassExamples

open TauCeti HeightClass

/-- The identity function `n ↦ n` on `ℕ`, as a real function. -/
noncomputable abbrev idReal : ℕ → ℝ := fun n ↦ n

/-- The class `[n]` on `ℕ` is nonzero, since `n` is unbounded. -/
theorem mk_idReal_ne_zero : mk idReal ≠ 0 := by
  rw [Ne, mk_eq_zero_iff]
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have := hC n
  rw [abs_of_nonneg (Nat.cast_nonneg n)] at this
  linarith

/-- The function `n ↦ n` on `ℕ` is Northcott: `{n | n ≤ b}` lies in `{n | n ≤ ⌊b⌋₊}`. -/
instance : Northcott idReal where
  finite_le b := (Set.finite_Iic ⌊b⌋₊).subset fun n (hn : (n : ℝ) ≤ b) ↦ Nat.le_floor hn

/-- A bounded oscillation has zero class although the function is not constant. -/
example : mk (fun n : ℕ ↦ (-1 : ℝ) ^ n) = 0 :=
  mk_eq_zero_iff.2 ⟨1, fun n ↦ by simp⟩

/-- The unbounded function `n` has nonzero class. -/
example : mk idReal ≠ 0 := mk_idReal_ne_zero

/-- Translation by a constant does not change the class. -/
example : mk (fun n : ℕ ↦ (n : ℝ) + 7) = mk idReal :=
  mk_eq_mk_iff.2 ⟨7, fun n ↦ by simp⟩

/-- Adding a bounded oscillation does not change the class. -/
example : mk (fun n : ℕ ↦ (n : ℝ) + (-1) ^ n) = mk idReal :=
  mk_eq_mk_iff.2 ⟨1, fun n ↦ by simp⟩

/-- Doubling changes the class: `[2n] - [n] = [n] ≠ 0`. -/
example : mk (fun n : ℕ ↦ 2 * (n : ℝ)) ≠ mk idReal := by
  intro h
  apply mk_idReal_ne_zero
  rw [← sub_eq_zero.2 h, ← Submodule.Quotient.mk_sub]
  congr 1
  ext n
  simp only [Pi.sub_apply]
  ring

/-- There is no induced multiplication: `[1] = [0]`, but `[n · 1] ≠ [n · 0]`. -/
example : mk (1 : ℕ → ℝ) = mk 0 ∧ mk (idReal * 1) ≠ mk (idReal * 0) :=
  ⟨by simp [Pi.one_def], by
    rw [mul_one, mul_zero]
    exact fun h ↦ mk_idReal_ne_zero (h.trans (Submodule.Quotient.mk_zero _))⟩

/-- Pulling `[n]` back along doubling gives `2 [n]`. -/
example : pullback (fun n : ℕ ↦ 2 * n) (mk idReal) = (2 : ℝ) • mk idReal := by
  rw [pullback_mk, ← Submodule.Quotient.mk_smul]
  congr 1
  ext n
  simp

/-- The inclusion of `{0}` into `ℕ` pulls the nonzero class `[n]` back to zero, so its pullback
is not injective: surjectivity is needed in `pullback_injective_of_surjective`. -/
example : ¬ Function.Injective (pullback (fun _ : Unit ↦ (0 : ℕ))) := fun h ↦
  mk_idReal_ne_zero (h (by simp))

/-- A bijection gives mutually inverse pullbacks. -/
example (e : ℕ ≃ ℕ) : pullback e ∘ₗ pullback e.symm = LinearMap.id := by
  rw [← pullback_comp, e.symm_comp_self, pullback_id]

/-- Northcott passes to the boundedly equal function `n + (-1)^n`. -/
example : Northcott fun n : ℕ ↦ (n : ℝ) + (-1) ^ n :=
  (northcott_congr (h := idReal) (mk_eq_mk_iff.2 ⟨1, fun n ↦ by simp⟩)).1 inferInstance

/-- The first projection `ℕ × Fin 2 → ℕ` has finite fibres. -/
instance : Filter.TendstoCofinite (Prod.fst : ℕ × Fin 2 → ℕ) :=
  (Filter.tendstoCofinite_iff_finite_preimage_singleton _).2 fun n ↦
    (Set.finite_range (Prod.mk n : Fin 2 → ℕ × Fin 2)).subset fun p (hp : p.1 = n) ↦
      ⟨p.2, by rw [← hp]⟩

/-- Pulling `n` back along the finite-fibred projection `ℕ × Fin 2 → ℕ` keeps Northcott. -/
example : Northcott fun p : ℕ × Fin 2 ↦ (p.1 : ℝ) :=
  northcott_of_pullback_eq (f := Prod.fst) (h := idReal) (by rw [pullback_mk]; rfl)

/-- Along `ℕ × ℕ → ℕ` the fibres are infinite and the pulled-back function is not Northcott:
its zero sublevel set contains every `(0, m)`. -/
example : ¬ Northcott fun p : ℕ × ℕ ↦ (p.1 : ℝ) := by
  intro h
  refine Set.infinite_range_of_injective (f := fun m : ℕ ↦ ((0 : ℕ), m))
    (fun _ _ hm ↦ (Prod.ext_iff.1 hm).2) ((h.finite_le 0).subset ?_)
  rintro _ ⟨m, rfl⟩
  simp

end TauCeti.HeightClassExamples

end
