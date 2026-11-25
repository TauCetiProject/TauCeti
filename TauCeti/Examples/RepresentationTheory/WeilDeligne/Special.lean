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
* The open kernel of the degree map is needed: on `W = ℤ` with the indiscrete topology and the
  identity as degree, the `Sp(2)` action `r(w) = diag(1, 2 ^ deg w)` at `q = 2`, for `2 ≠ 0` in
  the field, has kernel missing `1 ∈ ℤ`, which is not open, so it underlies no Weil–Deligne
  parameter.
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

open Topology in
/-- **The open degree kernel is necessary.** Give `W = ℤ` (written multiplicatively) the
indiscrete topology and take the identity as degree. When `2 ≠ 0` in `E`, the `Sp(2)` Weil action
`r(w) = diag(1, 2 ^ deg w)` at `q = 2` has non-open kernel: the kernel misses `1 ∈ ℤ`, which
scales `e₁` by `2 ≠ 1`, and the only open subsets of an indiscrete space are `∅` and the whole
space. So this action underlies no Weil–Deligne parameter. -/
example (h2 : ((2 : ℕ) : E) ≠ 0) :
    ¬ IsOpen[⊤] (((Algebra.lmul E (Fin 2 → E)).toMonoidHom.comp
      (specialWeight (MonoidHom.id (Multiplicative ℤ)) 2 h2)).ker : Set (Multiplicative ℤ)) := by
  intro hopen
  -- The kernel contains `1`, so being open in the indiscrete topology it is everything.
  have hker := (TopologicalSpace.isOpen_top_iff _).1 hopen |>.resolve_left
    (Set.ne_empty_iff_nonempty.2 ⟨1, one_mem _⟩)
  have h1 := MonoidHom.mem_ker.1 ((Set.ext_iff.1 hker (Multiplicative.ofAdd 1)).2 trivial)
  have h := congr_fun (LinearMap.congr_fun h1 (Pi.single 1 1)) 1
  have h2' : (2 : E) = 1 := by simpa using h
  -- `2 = 1` forces `1 = 0` in the field `E`.
  exact one_ne_zero (by linear_combination h2')

end TauCeti.WeilDeligneParameter.SpecialChecks
