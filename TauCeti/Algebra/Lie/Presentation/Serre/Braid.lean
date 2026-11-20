/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Lie.Sl2.Weyl.Automorphism
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# A braid criterion for the Weyl units of a Serre system

In an associative rational algebra, `TauCeti.IsSerreSystem.weylUnit_braid_of_conj_E_eq` reduces
a braid relation between the pinned Weyl units at two nodes of a nilpotent Serre system to a
raising-operator calculation. If conjugation by the alternating word `(a * b) ^ n * a` fixes the
raising generator at `j` in every Serre system for `CM` with nonzero Cartan generators at `i`
and `j`, then `(a * b) ^ (n + 1) = (b * a) ^ (n + 1)` as units.

The hypothesis is applied to the signed exchange `hs.neg_swap`, whose Weyl units act by the same
conjugation (`TauCeti.IsSerreSystem.toConjAct_weylUnit_neg_swap_smul`), so the same word fixes
the lowering generator. Exponentiating then gives commutation with the Weyl unit itself. The
double- and triple-bond braid relations are derived from this criterion.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 19 and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.IsSerreSystem

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HasUniqueDiv.of_module_rat

variable {B A : Type*} [Ring A] [Algebra ℚ A]
  {CM : Matrix B B ℤ} {H E F : B → A}

/-- At a node with `CM k k = 2`, the Weyl unit of the signed exchange `hs.neg_swap` acts by the
same conjugation as the Weyl unit of `hs`. No nonvanishing of `H k` is needed: if `H k = 0` then
`E k` and `F k` vanish. The statement uses the conjugation action so that it rewrites inside
conjugation by a word in Weyl units. -/
theorem toConjAct_weylUnit_neg_swap_smul (hs : IsSerreSystem ℚ CM H E F) {k : B}
    (hkk : CM k k = 2) (hEk : IsNilpotent (E k)) (hFk : IsNilpotent (F k)) (y : A) :
    ConjAct.toConjAct (weylUnit hFk.neg hEk.neg) • y =
      ConjAct.toConjAct (weylUnit hEk hFk) • y := by
  simp only [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  by_cases hk : H k = 0
  · simp [hs.E_eq_zero_of_H_eq_zero hk (by omega : CM k k ≠ 0),
      hs.F_eq_zero_of_H_eq_zero hk (by omega : CM k k ≠ 0)]
  exact weylUnit_neg_symm_conj (hs.isSl2Triple hkk hk) hEk hFk y

/-- **The braid relation from a fixed raising generator.** Let `a` and `b` be the Weyl units at
two nodes `i` and `j` with nonzero Cartan entries between them. Suppose that, in every Serre
system for `CM` that is nonzero at both nodes, conjugation by `(a * b) ^ n * a` fixes the raising
generator at `j`. Then `(a * b) ^ (n + 1) = (b * a) ^ (n + 1)`, as units.
The hypothesis is applied to the signed exchange `hs.neg_swap` to fix the lowering generator too.
Exponentiating then makes `(a * b) ^ n * a` commute with `b`. -/
theorem weylUnit_braid_of_conj_E_eq (hs : IsSerreSystem ℚ CM H E F) {i j : B}
    (hii : CM i i = 2) (hjj : CM j j = 2) (hij : CM i j ≠ 0) (hji : CM j i ≠ 0)
    (hEi : IsNilpotent (E i)) (hFi : IsNilpotent (F i))
    (hEj : IsNilpotent (E j)) (hFj : IsNilpotent (F j)) (n : ℕ)
    (hfix : ∀ {H' E' F' : B → A}, IsSerreSystem ℚ CM H' E' F' → H' i ≠ 0 → H' j ≠ 0 →
      ∀ (hEi' : IsNilpotent (E' i)) (hFi' : IsNilpotent (F' i))
        (hEj' : IsNilpotent (E' j)) (hFj' : IsNilpotent (F' j)),
        ConjAct.toConjAct ((weylUnit hEi' hFi' * weylUnit hEj' hFj') ^ n * weylUnit hEi' hFi') •
          E' j = E' j) :
    (weylUnit hEi hFi * weylUnit hEj hFj) ^ (n + 1) =
      (weylUnit hEj hFj * weylUnit hEi hFi) ^ (n + 1) := by
  let a := weylUnit hEi hFi
  let b := weylUnit hEj hFj
  -- Degenerate Serre systems are allowed: a zero Cartan operator kills this entire bond.
  by_cases hj : H j = 0
  · obtain ⟨hEi0, hFi0, hEj0, hFj0⟩ := hs.eq_zero_of_H_eq_zero_of_cartan_ne_zero hij hji hj
    apply Units.ext
    simp [hEi0, hFi0, hEj0, hFj0]
  have hi : H i ≠ 0 := fun hi => hj (hs.H_eq_zero_of_H_eq_zero hi hij)
  have hE := hfix hs hi hj hEi hFi hEj hFj
  -- Signed exchange preserves each Weyl conjugation, so the raising calculation for
  -- `hs.neg_swap` shows that the same word fixes the lowering operator.
  let φ : Aˣ →* Function.End A := MulAction.toEndHom.comp ConjAct.toConjAct.toMonoidHom
  have hφ (u : Aˣ) (y : A) : φ u y = ConjAct.toConjAct u • y := rfl
  have hw : φ ((weylUnit hFi.neg hEi.neg * weylUnit hFj.neg hEj.neg) ^ n *
      weylUnit hFi.neg hEi.neg) = φ ((a * b) ^ n * a) := by
    have ha : φ (weylUnit hFi.neg hEi.neg) = φ a :=
      funext (hs.toConjAct_weylUnit_neg_swap_smul hii hEi hFi)
    have hb : φ (weylUnit hFj.neg hEj.neg) = φ b :=
      funext (hs.toConjAct_weylUnit_neg_swap_smul hjj hEj hFj)
    simp only [map_mul, map_pow, ha, hb]
  have hF : ConjAct.toConjAct ((a * b) ^ n * a) • F j = F j := by
    have h := hfix hs.neg_swap (neg_ne_zero.mpr hi) (neg_ne_zero.mpr hj)
      hFi.neg hEi.neg hFj.neg hEj.neg
    rw [← neg_inj, ← smul_neg, ← hφ, ← hw, hφ]
    exact h
  -- Exponentiating gives commutation with the Weyl unit itself, not merely equality
  -- of conjugation actions. This eliminates any possible central discrepancy.
  have hu : (a * b) ^ n * a * b * ((a * b) ^ n * a)⁻¹ = b :=
    conj_weylUnit_eq_of_conj_eq hEj hFj hEj hFj
      (by simpa only [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct] using hE)
      (by simpa only [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct] using hF)
  calc
    (a * b) ^ (n + 1) = (a * b) ^ n * a * b := by rw [pow_succ, ← mul_assoc]
    _ = b * ((a * b) ^ n * a) := mul_inv_eq_iff_eq_mul.mp hu
    _ = (b * a) ^ (n + 1) := by rw [mul_pow_mul, ← mul_assoc, ← pow_succ']

end TauCeti.IsSerreSystem
