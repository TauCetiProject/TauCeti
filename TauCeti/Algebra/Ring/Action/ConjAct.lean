/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Algebra.Ring.Subsemiring.Pointwise

/-!
# Pointwise conjugation normalization of subsemirings

If a unit `x : Bˣ` normalizes a subsemiring `C ≤ B` under `ConjAct`, so do `x⁻¹`, every integer
power `x ^ m`, and any product `E * x⁻¹` with another normalizing unit `E`. Consequently,
conjugating any element of `C` by `x ^ m` stays in `C`.
-/

public section

open scoped Pointwise

namespace Subsemiring

variable {B : Type*} [Semiring B]

/-- If `x` normalizes `C` under conjugation, then `x⁻¹` also normalizes `C`. -/
theorem conjAct_inv_smul_eq {C : Subsemiring B} {x : Bˣ} (hx : ConjAct.toConjAct x • C = C) :
    ConjAct.toConjAct x⁻¹ • C = C := by
  simpa [← mul_smul] using (congrArg (ConjAct.toConjAct x⁻¹ • ·) hx).symm

/-- If `x` normalizes `C` under conjugation, then every integer power `x ^ m` normalizes `C`. -/
theorem conjAct_zpow_smul_eq {C : Subsemiring B} {x : Bˣ} (hx : ConjAct.toConjAct x • C = C)
    (m : ℤ) : ConjAct.toConjAct (x ^ m) • C = C := by
  induction m using Int.induction_on with
  | zero => simp
  | succ _ hk => rw [zpow_add_one, map_mul, mul_smul, hx, hk]
  | pred _ hk => rw [zpow_sub_one, map_mul, mul_smul, conjAct_inv_smul_eq hx, hk]

/-- If `x` and `E` normalize `C`, then `E * x⁻¹` also normalizes `C`. -/
theorem conjAct_mul_inv_smul_eq {C : Subsemiring B} {x E : Bˣ}
    (hx : ConjAct.toConjAct x • C = C) (hE : ConjAct.toConjAct E • C = C) :
    ConjAct.toConjAct (E * x⁻¹) • C = C := by
  rw [map_mul, mul_smul, conjAct_inv_smul_eq hx, hE]

/-- Conjugating `c ∈ C` by `x ^ m` stays in `C` whenever `x` normalizes `C`. -/
theorem conj_zpow_mem {C : Subsemiring B} {x : Bˣ} (hx : ConjAct.toConjAct x • C = C) (m : ℤ)
    {c : B} (hc : c ∈ C) : ((x ^ m : Bˣ) : B) * c * ((x ^ (-m) : Bˣ) : B) ∈ C := by
  simpa [ConjAct.units_smul_def, zpow_neg] using
    (conjAct_zpow_smul_eq hx m ▸ smul_mem_pointwise_smul (ConjAct.toConjAct (x ^ m)) c C hc)

end Subsemiring
