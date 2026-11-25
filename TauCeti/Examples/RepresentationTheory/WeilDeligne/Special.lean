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
  identity as degree, the `Sp(2)` action `r(w) = diag(1, 2 ^ deg w)` at `q = 2` has kernel `{0}`,
  which is not open, so it underlies no Weil–Deligne parameter.
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

/-- The group `ℤ`, written multiplicatively, with the indiscrete topology. -/
@[expose] def IndiscreteInt : Type := Multiplicative ℤ

/-- The group structure of `Multiplicative ℤ`. -/
instance instGroupIndiscreteInt : Group IndiscreteInt := inferInstanceAs (Group (Multiplicative ℤ))

/-- The indiscrete topology. -/
instance instTopologicalSpaceIndiscreteInt : TopologicalSpace IndiscreteInt := ⊤

/-- The identity of `ℤ`, as the degree map of `IndiscreteInt`. -/
def indiscreteIntDeg : IndiscreteInt →* Multiplicative ℤ := MonoidHom.id (Multiplicative ℤ)

/-- **The open degree kernel is necessary.** Give `W = ℤ` (written multiplicatively) the
indiscrete topology and take the identity as degree. Over any field `E`, no Weil–Deligne
parameter with `q = 2` has the `Sp(2)` Weil action `r(w) = diag(1, 2 ^ deg w)`: its kernel is
trivial, and the only open subsets of an indiscrete space are `∅` and the whole space. -/
example :
    ¬ ∃ D : WeilDeligneParameter E IndiscreteInt (Fin 2 → E) indiscreteIntDeg 2,
      ∀ w v, D.r w v =
        fun i : Fin 2 ↦ (2 : E) ^ ((indiscreteIntDeg w).toAdd * ((i : ℕ) : ℤ)) * v i := by
  rintro ⟨D, hD⟩
  -- The kernel contains `1`, so being open in the indiscrete topology it is everything.
  have hker : (D.r.ker : Set IndiscreteInt) = Set.univ :=
    (TopologicalSpace.isOpen_top_iff _).1 D.isOpen_ker |>.resolve_left
      (Set.ne_empty_iff_nonempty.2 ⟨1, one_mem _⟩)
  let w : IndiscreteInt := Multiplicative.ofAdd (1 : ℤ)
  have h1 : D.r w = 1 := MonoidHom.mem_ker.1 ((Set.ext_iff.1 hker w).2 trivial)
  have h := congr_fun (LinearMap.congr_fun h1 (Pi.single 1 1)) 1
  -- `IndiscreteInt` is a synonym for `Multiplicative ℤ` and `indiscreteIntDeg` is the identity.
  have hdeg : (indiscreteIntDeg w).toAdd = 1 := rfl
  have h2 : (2 : E) = 1 := by simpa [hD, hdeg] using h
  -- `2 = 1` forces `1 = 0` in the field `E`.
  exact one_ne_zero (by linear_combination h2)

end TauCeti.WeilDeligneParameter.SpecialChecks
