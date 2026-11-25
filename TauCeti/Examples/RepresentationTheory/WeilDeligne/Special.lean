/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeilDeligne.Special

/-!
# Checks for the special parameter `Sp(2)`

* In `Sp(2)`, conjugation by `r(w)` scales the monodromy by `ω(w) = q ^ deg w`.
* Reversing the two weights while keeping the same nonzero arrow `e₀ ↦ e₁` makes conjugation by
  an element of degree one scale the monodromy by `q⁻¹` instead of `q`. For `q ≥ 2` in
  characteristic zero there is therefore no Weil–Deligne parameter with the reversed weights.
-/

public section

namespace TauCeti.WeilDeligneParameter.SpecialChecks

variable {E W : Type*} [Field E] [Group W] [TopologicalSpace W] {deg : W →* Multiplicative ℤ}
  {q : ℕ}

/-- In `Sp(2)`, conjugation by `r(w)` scales `N` by `q ^ deg w`. -/
example (hdeg : Continuous deg) (hq : (q : E) ≠ 0) (w : W) :
    (special q 2 hdeg hq).r w * (special q 2 hdeg hq).N * (special q 2 hdeg hq).r w⁻¹ =
      (q : E) ^ (deg w).toAdd • (special q 2 hdeg hq).N :=
  (special q 2 hdeg hq).conj_N w

/-- **Reversed weights fail.** For `q ≥ 2` in characteristic zero, no Weil–Deligne parameter on
`E²` has monodromy the shift `e₀ ↦ e₁` and an element `w` of degree one acting by `diag(q, 1)`:
conjugation by `r(w)` would scale the shift by `q⁻¹`, not by `q`. -/
example [CharZero E] (hq : 2 ≤ q) {w : W} (hw : (deg w).toAdd = 1)
    (D : WeilDeligneParameter E W (Fin 2 → E) deg q) (hN : D.N = finShift E 2)
    (hr : ∀ v, D.r w v = ![(q : E) * v 0, v 1]) : False := by
  -- The second coordinate of `r(w) (N e₀) = q • N (r(w) e₀)`.
  have h := congr_fun (D.r_apply_N_apply w (Pi.single 0 1)) 1
  rw [hN, hr, hr, hw, zpow_one] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single_eq_same, finShift_apply,
    Pi.smul_apply, smul_eq_mul] at h
  norm_num at h
  have : q * q = 1 := by exact_mod_cast h.symm
  nlinarith

end TauCeti.WeilDeligneParameter.SpecialChecks
