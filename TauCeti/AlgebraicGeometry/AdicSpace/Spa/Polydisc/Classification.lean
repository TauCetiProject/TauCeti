/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.ClassicalPoint
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.DiscPoint

import TauCeti.Algebra.Polynomial.Splits
import TauCeti.Analysis.Normed.Field.Basic
import TauCeti.RingTheory.Huber.Restricted.OneVariable

/-!
# Recognising the points `η_{a,r}` and `η_{a,r±}` of the closed unit disc

Let `K` be an algebraically closed complete nontrivially normed nonarchimedean field and
`X = Spa (K⟨T⟩, K⟨T⟩°)` the closed unit disc. Wedhorn's Example 7.57 sorts the points of `X` into
five types. The points of types (2) and (3) are the Gauss points `η_{a,r}` of the discs
`D(a, r) = {y : ‖y - a‖ ≤ r}` (`TauCeti.ValuationSpectrum.discPoint`). Next to each `η_{a,r}` sit
the refined Gauss points `η_{a,r⁺}` and `η_{a,r⁻}` (`TauCeti.ValuationSpectrum.discPointAbove`,
`TauCeti.ValuationSpectrum.discPointBelow`). For `r ∈ |Kˣ|` these are the rank-two points of
type (5); for other radii they need not differ from `η_{a,r}`. This file characterises each of
`η_{a,r}`, `η_{a,r⁺}` and `η_{a,r⁻}`, for every radius, among all points of `X` by the position of
`x(T - a)` relative to the constants.

A point `x` is `η_{a,r}` exactly when

* `x(T - a) ≤ x(T - b)` for every `b ∈ D(a, r)`, so `a` minimises `b ↦ x(T - b)` on the disc, and
* `x(T - a)` sits at `r` relative to the constants: `x(T - a) ≤ x(c)` exactly when `r ≤ ‖c‖`,
  and `x(c) ≤ x(T - a)` exactly when `‖c‖ ≤ r`.

The second condition says that `x(T - a)` has the same position in the value group of `x` as the
real number `r` among the norms of `K`. The first condition fails for the point `η_{b,s}` with
`s < r = ‖b - a‖`, whose value on `T - a` is again `r`.

A point `x` is `η_{a,r⁺}` exactly when `x(T - a) ≤ x(c)` holds for precisely the constants with
`r < ‖c‖`, and `η_{a,r⁻}` exactly when `x(c) ≤ x(T - a)` holds for precisely the constants with
`‖c‖ < r`. So `x(T - a)` lies infinitesimally above, respectively below, the constants of norm
`r`. Since the norms of `K` are dense, these conditions make `x(T - a)` strictly larger or strictly
smaller than every `x(c)`, and no minimality condition is needed: `x(T - b)` is then `x(T - a)`
or `x(b - a)` by the ultrametric equality.

All three characterisations rest on one comparison. Suppose two points `x` and `y` compare
`T - a` with every constant in the same way, `x(T - a)` and `y(T - a)` are nonzero, and there is
a set `P` of centres with `x(T - b) = x(T - a)` for `b ∈ P` and `x(T - b) = x(b - a)` otherwise,
and likewise for `y`. Over an algebraically closed field every polynomial is a constant times a
product of linear factors `T - b`, so `x` and `y` take the values `x(c) x(T - a)^m` and
`y(c) y(T - a)^m` on it, for the same `c` and `m`. Taking `m`-th roots in `K` shows that `x` and
`y` compare these values in the same way. Polynomials are dense in `K⟨T⟩`
(`TauCeti.Huber.denseRange_eval₂RingHom_weightedX`) and both points are continuous with trivial
support, so `x = y` (`Valuation.IsContinuous.isEquiv_of_dense`). Trivial support holds because a
point with nonzero support kills some `T - b`
(`TauCeti.ValuationSpectrum.exists_weightedX_sub_weightedC_mem_supp`).

## Main results

* `TauCeti.ValuationSpectrum.eq_discPoint_iff`: a point of the closed unit disc over an
  algebraically closed field is `η_{a,r}` if and only if it satisfies the two conditions above.
* `TauCeti.ValuationSpectrum.eq_discPointAbove_iff` and
  `TauCeti.ValuationSpectrum.eq_discPointBelow_iff`: it is `η_{a,r⁺}`, respectively `η_{a,r⁻}`, if
  and only if `x(T - a)` lies just above, respectively just below, the constants of norm `r`.
* `TauCeti.ValuationSpectrum.forall_lt_and_forall_gt_of_vle_weightedC` and
  `TauCeti.ValuationSpectrum.forall_lt_and_forall_gt_of_weightedC_vle`: in that case `x(T - a)`
  is strictly larger or strictly smaller than the value of every constant.
* `TauCeti.ValuationSpectrum.eq_of_forall_valuation_weightedX_sub_weightedC_eq`: two points that
  take the value of one and the same nonzero constant on every `T - b` are equal.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

variable {K : Type*} [NontriviallyNormedField K] [NonarchimedeanRing K] {r : ℝ}

local notation "𝒯" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight
local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight

/-! ### Values on the linear polynomials -/

/-- Under the two conditions characterising `η_{a,r}`, `x(T - b)` is `x(T - a)` on the disc
`D(a, r)` and `x(b - a)` off it. -/
private theorem valuation_weightedX_sub_weightedC {x : closedPolydisc 1 K} {a : K}
    (hmin : ∀ b : K, ‖b - a‖ ≤ r → x.1.toValuativeRel.vle (T - C a) (T - C b))
    (hge : ∀ c : K, x.1.toValuativeRel.vle (C c) (T - C a) ↔ ‖c‖ ≤ r) (b : K) :
    x.1.valuation (T - C b) =
      if ‖b - a‖ ≤ r then x.1.valuation (T - C a) else x.1.valuation (C (b - a)) := by
  have hsplit : T - C b = (T - C a) - C (b - a) := by
    rw [map_sub]
    ring
  split_ifs with hb
  · refine le_antisymm ?_ ((valuation_le_iff _ _ _).mpr (hmin b hb))
    rw [hsplit]
    exact (Valuation.map_sub _ _ _).trans
      (max_le le_rfl ((valuation_le_iff _ _ _).mpr ((hge _).mpr hb)))
  · rw [hsplit, Valuation.map_sub_eq_of_lt_right]
    exact lt_of_not_ge fun h ↦ hb ((hge _).mp ((valuation_le_iff _ _ _).mp h))

/-- Under the second condition characterising `η_{a,r}`, `x(T - a) ≠ 0`. -/
private theorem valuation_weightedX_sub_weightedC_ne_zero {x : closedPolydisc 1 K} {a : K}
    (hr₀ : 0 < r) (hle : ∀ c : K, x.1.toValuativeRel.vle (T - C a) (C c) ↔ r ≤ ‖c‖) :
    x.1.valuation (T - C a) ≠ 0 := fun h ↦ by
  have := (hle 0).mp ((valuation_le_iff _ _ _).mp (h ▸ zero_le))
  rw [norm_zero] at this
  exact hr₀.not_ge this

/-! ### Two points that compare `T - a` with the constants in the same way -/

/-- If `x` and `y` take the value of `T - a` on `T - b` for `b ∈ P` and the value of `b - a` for
`b ∉ P`, then on every polynomial they take values `x(c) x(T - a)^m` and `y(c) y(T - a)^m` for the
same `c` and `m`. -/
private theorem exists_valuation_eval₂RingHom_eq [IsAlgClosed K] {x y : closedPolydisc 1 K} {a : K}
    (P : K → Prop) [DecidablePred P]
    (hx : ∀ b : K, x.1.valuation (T - C b) =
      if P b then x.1.valuation (T - C a) else x.1.valuation (C (b - a)))
    (hy : ∀ b : K, y.1.valuation (T - C b) =
      if P b then y.1.valuation (T - C a) else y.1.valuation (C (b - a))) (p : Polynomial K) :
    ∃ (c : K) (m : ℕ), x.1.valuation (Polynomial.eval₂RingHom C T p) =
        x.1.valuation (C c) * x.1.valuation (T - C a) ^ m ∧
      y.1.valuation (Polynomial.eval₂RingHom C T p) =
        y.1.valuation (C c) * y.1.valuation (T - C a) ^ m := by
  -- the claim for a product of linear factors, by induction on the multiset of roots
  have key (s : Multiset K) : ∃ (c : K) (m : ℕ),
      x.1.valuation ((s.map fun b ↦ T - C b).prod) =
        x.1.valuation (C c) * x.1.valuation (T - C a) ^ m ∧
      y.1.valuation ((s.map fun b ↦ T - C b).prod) =
        y.1.valuation (C c) * y.1.valuation (T - C a) ^ m := by
    induction s using Multiset.induction_on with
    | empty => exact ⟨1, 0, by simp, by simp⟩
    | cons b s ih =>
      obtain ⟨c, m, h₁, h₂⟩ := ih
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, h₁, h₂, hx b, hy b]
      by_cases hb : P b
      · refine ⟨c, m + 1, ?_, ?_⟩ <;>
        · simp only [hb, ↓reduceIte, pow_succ]
          ac_rfl
      · refine ⟨(b - a) * c, m, ?_, ?_⟩ <;>
        · simp only [hb, ↓reduceIte, map_mul]
          ac_rfl
  obtain ⟨c, m, h₁, h₂⟩ := key p.roots
  have hP : Polynomial.eval₂RingHom C T p =
      C p.leadingCoeff * (p.roots.map fun b ↦ T - C b).prod :=
    (IsAlgClosed.splits p).eval₂_eq_prod_roots C T
  exact ⟨p.leadingCoeff * c, m, by rw [hP, map_mul, h₁, map_mul, map_mul, mul_assoc],
    by rw [hP, map_mul, h₂, map_mul, map_mul, mul_assoc]⟩

variable [IsUltrametricDist K]

/-- If two points compare `T - a` with every constant in the same way, they compare its powers
`(T - a)^k` with every constant in the same way: take a `k`-th root of the constant in `K`. -/
private theorem pow_le_valuation_weightedC_iff_and_valuation_weightedC_le_pow_iff [IsAlgClosed K]
    {x y : closedPolydisc 1 K} {a : K}
    (hcmp : ∀ e : K, (x.1.valuation (T - C a) ≤ x.1.valuation (C e) ↔
        y.1.valuation (T - C a) ≤ y.1.valuation (C e)) ∧
      (x.1.valuation (C e) ≤ x.1.valuation (T - C a) ↔
        y.1.valuation (C e) ≤ y.1.valuation (T - C a))) (e : K) (k : ℕ) :
    (x.1.valuation (T - C a) ^ k ≤ x.1.valuation (C e) ↔
        y.1.valuation (T - C a) ^ k ≤ y.1.valuation (C e)) ∧
      (x.1.valuation (C e) ≤ x.1.valuation (T - C a) ^ k ↔
        y.1.valuation (C e) ≤ y.1.valuation (T - C a) ^ k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h₁ := (closedPolydisc_valuation_weightedC_le_iff x 1 e).trans
      (closedPolydisc_valuation_weightedC_le_iff y 1 e).symm
    have h₂ := (closedPolydisc_valuation_weightedC_le_iff x e 1).trans
      (closedPolydisc_valuation_weightedC_le_iff y e 1).symm
    simp only [map_one, pow_zero] at h₁ h₂ ⊢
    exact ⟨h₁, h₂⟩
  obtain ⟨e, rfl⟩ := IsAlgClosed.exists_pow_nat_eq e hk
  simp only [map_pow, pow_le_pow_iff_left₀ zero_le zero_le hk.ne']
  exact hcmp e

/-- If two points compare `T - a` with the constants in the same way and do not vanish on `T - a`,
then for `c ≠ 0` and `n ≤ m` they compare `x(c) x(T - a)^m` and `x(d) x(T - a)^n`, in both
directions, in the same way. -/
private theorem valuation_mul_pow_le_iff_of_le [IsAlgClosed K] {x y : closedPolydisc 1 K} {a : K}
    (hx₀ : x.1.valuation (T - C a) ≠ 0) (hy₀ : y.1.valuation (T - C a) ≠ 0)
    (hcmp : ∀ e : K, (x.1.valuation (T - C a) ≤ x.1.valuation (C e) ↔
        y.1.valuation (T - C a) ≤ y.1.valuation (C e)) ∧
      (x.1.valuation (C e) ≤ x.1.valuation (T - C a) ↔
        y.1.valuation (C e) ≤ y.1.valuation (T - C a)))
    {c : K} (hc : c ≠ 0) (d : K) {m n : ℕ} (h : n ≤ m) :
    (x.1.valuation (C c) * x.1.valuation (T - C a) ^ m ≤
        x.1.valuation (C d) * x.1.valuation (T - C a) ^ n ↔
      y.1.valuation (C c) * y.1.valuation (T - C a) ^ m ≤
        y.1.valuation (C d) * y.1.valuation (T - C a) ^ n) ∧
    (x.1.valuation (C d) * x.1.valuation (T - C a) ^ n ≤
        x.1.valuation (C c) * x.1.valuation (T - C a) ^ m ↔
      y.1.valuation (C d) * y.1.valuation (T - C a) ^ n ≤
        y.1.valuation (C c) * y.1.valuation (T - C a) ^ m) := by
  -- `m = n + k` and `d = e c`: cancel `x(c) x(T - a)^n` and `y(c) y(T - a)^n`
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨e, rfl⟩ : ∃ e, d = e * c := ⟨d / c, (div_mul_cancel₀ d hc).symm⟩
  have key (z : closedPolydisc 1 K) (hz₀ : z.1.valuation (T - C a) ≠ 0) :
      0 < z.1.valuation (C c) * z.1.valuation (T - C a) ^ n ∧
      z.1.valuation (C c) * z.1.valuation (T - C a) ^ (n + k) =
        z.1.valuation (C c) * z.1.valuation (T - C a) ^ n * z.1.valuation (T - C a) ^ k ∧
      z.1.valuation (C (e * c)) * z.1.valuation (T - C a) ^ n =
        z.1.valuation (C c) * z.1.valuation (T - C a) ^ n * z.1.valuation (C e) := by
    refine ⟨zero_lt_iff.mpr (mul_ne_zero (fun h0 ↦ hc ?_) (pow_ne_zero n hz₀)),
      by rw [pow_add, mul_assoc], by rw [map_mul, map_mul]; ac_rfl⟩
    simpa [h0] using closedPolydisc_valuation_weightedC_le_iff z c 0
  obtain ⟨hx, hx₁, hx₂⟩ := key x hx₀
  obtain ⟨hy, hy₁, hy₂⟩ := key y hy₀
  simp only [hx₁, hx₂, hy₁, hy₂, mul_le_mul_iff_of_pos_left hx, mul_le_mul_iff_of_pos_left hy]
  exact pow_le_valuation_weightedC_iff_and_valuation_weightedC_le_pow_iff hcmp e k

/-- If two points compare `T - a` with the constants in the same way and do not vanish on `T - a`,
they compare `x(c) x(T - a)^m` and `x(d) x(T - a)^n` in the same way. -/
private theorem valuation_mul_pow_le_iff [IsAlgClosed K] {x y : closedPolydisc 1 K} {a : K}
    (hx₀ : x.1.valuation (T - C a) ≠ 0) (hy₀ : y.1.valuation (T - C a) ≠ 0)
    (hcmp : ∀ e : K, (x.1.valuation (T - C a) ≤ x.1.valuation (C e) ↔
        y.1.valuation (T - C a) ≤ y.1.valuation (C e)) ∧
      (x.1.valuation (C e) ≤ x.1.valuation (T - C a) ↔
        y.1.valuation (C e) ≤ y.1.valuation (T - C a))) (c d : K) (m n : ℕ) :
    x.1.valuation (C c) * x.1.valuation (T - C a) ^ m ≤
        x.1.valuation (C d) * x.1.valuation (T - C a) ^ n ↔
      y.1.valuation (C c) * y.1.valuation (T - C a) ^ m ≤
        y.1.valuation (C d) * y.1.valuation (T - C a) ^ n := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_or_ne d 0 with rfl | hd
  · simpa using (valuation_mul_pow_le_iff_of_le hx₀ hy₀ hcmp hc 0 (Nat.zero_le m)).1
  rcases le_total n m with h | h
  · exact (valuation_mul_pow_le_iff_of_le hx₀ hy₀ hcmp hc d h).1
  · exact (valuation_mul_pow_le_iff_of_le hx₀ hy₀ hcmp hd c h).2

/-- If `x(T - a) ≤ x(c)` holds for exactly the constants with `r < ‖c‖`, then `x(T - a)` is
strictly larger than the values of the constants with `‖c‖ ≤ r` and strictly smaller than the
values of the others, because the norms of `K` are dense. -/
theorem forall_lt_and_forall_gt_of_vle_weightedC [IsAlgClosed K]
    {x : closedPolydisc 1 K} {a : K} (hr₀ : 0 < r)
    (h : ∀ c : K, x.1.toValuativeRel.vle (T - C a) (C c) ↔ r < ‖c‖) :
    (∀ c : K, ‖c‖ ≤ r → x.1.valuation (C c) < x.1.valuation (T - C a)) ∧
      ∀ c : K, ¬ ‖c‖ ≤ r → x.1.valuation (T - C a) < x.1.valuation (C c) := by
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · rw [← not_le, valuation_le_iff, h]
    exact hc.not_gt
  · obtain ⟨c', h₁, h₂⟩ := NormedField.exists_lt_norm_lt_of_isAlgClosed K hr₀.le (not_le.mp hc)
    exact ((valuation_le_iff _ _ _).mpr ((h c').mpr h₁)).trans_lt
      (lt_of_not_ge fun h' ↦ h₂.not_ge ((closedPolydisc_valuation_weightedC_le_iff x c c').mp h'))

/-- If `x(c) ≤ x(T - a)` holds for exactly the constants with `‖c‖ < r`, then `x(T - a)` is
strictly larger than the values of the constants with `‖c‖ < r` and strictly smaller than the
values of the others, because the norms of `K` are dense. -/
theorem forall_lt_and_forall_gt_of_weightedC_vle [IsAlgClosed K]
    {x : closedPolydisc 1 K} {a : K}
    (h : ∀ c : K, x.1.toValuativeRel.vle (C c) (T - C a) ↔ ‖c‖ < r) :
    (∀ c : K, ‖c‖ < r → x.1.valuation (C c) < x.1.valuation (T - C a)) ∧
      ∀ c : K, ¬ ‖c‖ < r → x.1.valuation (T - C a) < x.1.valuation (C c) := by
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · obtain ⟨c', h₁, h₂⟩ := NormedField.exists_lt_norm_lt_of_isAlgClosed K (norm_nonneg c) hc
    exact (lt_of_not_ge fun h' ↦
      h₁.not_ge ((closedPolydisc_valuation_weightedC_le_iff x c' c).mp h')).trans_le
      ((valuation_le_iff _ _ _).mpr ((h c').mpr h₂))
  · rw [← not_le, valuation_le_iff, h]
    exact hc

variable [CompleteSpace K]

/-- If `x` takes the value of `T - a` on `T - b` for `b ∈ P` and the value of `b - a` for `b ∉ P`,
and `x(T - a) ≠ 0`, then `x` has trivial support: a point with nonzero support kills some
`T - b`. -/
private theorem valuation_eq_zero_iff_of_eq_ite [IsAlgClosed K] {x : closedPolydisc 1 K} {a : K}
    (P : K → Prop) [DecidablePred P]
    (hx : ∀ b : K, x.1.valuation (T - C b) =
      if P b then x.1.valuation (T - C a) else x.1.valuation (C (b - a)))
    (hx₀ : x.1.valuation (T - C a) ≠ 0) (f : 𝒯) :
    x.1.valuation f = 0 ↔ f = 0 := by
  suffices hsupp : x.1.supp = ⊥ by
    rw [← Valuation.mem_supp_iff, ← supp_eq_valuation_supp, hsupp, Ideal.mem_bot]
  by_contra hne
  obtain ⟨b, -, hb⟩ := exists_weightedX_sub_weightedC_mem_supp x hne
  rw [supp_eq_valuation_supp, Valuation.mem_supp_iff] at hb
  have hb' := hx b
  rw [hb] at hb'
  split_ifs at hb' with hP
  · exact hx₀ hb'.symm
  · have h0 := closedPolydisc_valuation_weightedC_le_iff x (b - a) 0
    rw [map_zero, map_zero, ← hb', norm_zero] at h0
    obtain rfl : b = a := sub_eq_zero.mp (norm_le_zero_iff.mp (h0.mp le_rfl))
    exact hx₀ hb

/-- **Two points that compare `T - a` with the constants in the same way are equal**, provided
both do not vanish on `T - a` and both take the value of `T - a` on `T - b` for `b ∈ P` and the
value of `b - a` for `b ∉ P`. -/
private theorem eq_of_valuation_eq_ite [IsAlgClosed K] {x y : closedPolydisc 1 K} {a : K}
    (P : K → Prop) [DecidablePred P]
    (hx : ∀ b : K, x.1.valuation (T - C b) =
      if P b then x.1.valuation (T - C a) else x.1.valuation (C (b - a)))
    (hy : ∀ b : K, y.1.valuation (T - C b) =
      if P b then y.1.valuation (T - C a) else y.1.valuation (C (b - a)))
    (hx₀ : x.1.valuation (T - C a) ≠ 0) (hy₀ : y.1.valuation (T - C a) ≠ 0)
    (hcmp : ∀ e : K, (x.1.valuation (T - C a) ≤ x.1.valuation (C e) ↔
        y.1.valuation (T - C a) ≤ y.1.valuation (C e)) ∧
      (x.1.valuation (C e) ≤ x.1.valuation (T - C a) ↔
        y.1.valuation (C e) ≤ y.1.valuation (T - C a))) :
    x = y := by
  have hcont (z : closedPolydisc 1 K) : z.1.valuation.IsContinuous :=
    (ValuationSpectrum.isContinuous_def _).mp ((mem_closedPolydisc_iff 1 K z.1).mp z.2).1
  -- `x` and `y` compare polynomials in the same way, and polynomials are dense
  have hequiv : x.1.valuation.IsEquiv y.1.valuation := by
    refine (hcont x).isEquiv_of_dense (hcont y)
      (fun f ↦ (valuation_eq_zero_iff_of_eq_ite P hx hx₀ f).trans
        (valuation_eq_zero_iff_of_eq_ite P hy hy₀ f).symm)
      (denseRange_eval₂RingHom_weightedX isWeightFamily_one_weight) ?_
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    obtain ⟨c, m, hp, hp'⟩ := exists_valuation_eval₂RingHom_eq P hx hy p
    obtain ⟨d, n, hq, hq'⟩ := exists_valuation_eval₂RingHom_eq P hx hy q
    rw [hp, hq, hp', hq']
    exact valuation_mul_pow_le_iff hx₀ hy₀ hcmp c d m n
  exact Subtype.ext (ext' fun f g ↦ by
    rw [← valuation_le_iff, ← valuation_le_iff]
    exact hequiv f g)

/-- **Two points at which `x(T - a)` separates the same constants are equal**: if `x(T - a)` and
`y(T - a)` are strictly larger than the values of the constants with `Q c` and strictly smaller
than the values of the others, and `Q 0`, then `x = y`. -/
private theorem eq_of_forall_lt_of_forall_gt [IsAlgClosed K] {x y : closedPolydisc 1 K} {a : K}
    (Q : K → Prop) (hQ : Q 0)
    (hx : (∀ c : K, Q c → x.1.valuation (C c) < x.1.valuation (T - C a)) ∧
      ∀ c : K, ¬ Q c → x.1.valuation (T - C a) < x.1.valuation (C c))
    (hy : (∀ c : K, Q c → y.1.valuation (C c) < y.1.valuation (T - C a)) ∧
      ∀ c : K, ¬ Q c → y.1.valuation (T - C a) < y.1.valuation (C c)) :
    x = y := by
  classical
  have hcmp (z : closedPolydisc 1 K)
      (hz : (∀ c : K, Q c → z.1.valuation (C c) < z.1.valuation (T - C a)) ∧
        ∀ c : K, ¬ Q c → z.1.valuation (T - C a) < z.1.valuation (C c)) (e : K) :
      (z.1.valuation (T - C a) ≤ z.1.valuation (C e) ↔ ¬ Q e) ∧
        (z.1.valuation (C e) ≤ z.1.valuation (T - C a) ↔ Q e) :=
    ⟨⟨fun h hQe ↦ (hz.1 e hQe).not_ge h, fun hQe ↦ (hz.2 e hQe).le⟩,
      ⟨fun h ↦ by_contra fun hQe ↦ (hz.2 e hQe).not_ge h, fun hQe ↦ (hz.1 e hQe).le⟩⟩
  have hne (z : closedPolydisc 1 K)
      (hz : (∀ c : K, Q c → z.1.valuation (C c) < z.1.valuation (T - C a)) ∧
        ∀ c : K, ¬ Q c → z.1.valuation (T - C a) < z.1.valuation (C c)) :
      z.1.valuation (T - C a) ≠ 0 := by
    have h := hz.1 0 hQ
    rw [map_zero, map_zero] at h
    exact h.ne'
  refine eq_of_valuation_eq_ite (fun b ↦ Q (b - a))
    (valuation_weightedX_sub_weightedC_of_lt Q hx.1 hx.2)
    (valuation_weightedX_sub_weightedC_of_lt Q hy.1 hy.2) (hne x hx) (hne y hy) fun e ↦ ?_
  rw [(hcmp x hx e).1, (hcmp x hx e).2, (hcmp y hy e).1, (hcmp y hy e).2]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-! ### Two points that take the value of a constant on every `T - b` -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- If on every `T - b` two points take the value of one and the same constant, then on every
polynomial they take the value of one and the same constant: over an algebraically closed field,
a polynomial is a constant times a product of linear factors. -/
private theorem exists_valuation_eval₂RingHom_eq_valuation_weightedC [IsAlgClosed K]
    {x y : closedPolydisc 1 K}
    (h : ∀ b : K, ∃ e : K, x.1.valuation (T - C b) = x.1.valuation (C e) ∧
      y.1.valuation (T - C b) = y.1.valuation (C e)) (p : Polynomial K) :
    ∃ u : K, x.1.valuation (Polynomial.eval₂RingHom C T p) = x.1.valuation (C u) ∧
      y.1.valuation (Polynomial.eval₂RingHom C T p) = y.1.valuation (C u) := by
  choose e hxe hye using h
  have hP : Polynomial.eval₂RingHom C T p =
      C p.leadingCoeff * (p.roots.map fun b ↦ T - C b).prod :=
    (IsAlgClosed.splits p).eval₂_eq_prod_roots C T
  exact ⟨p.leadingCoeff * (p.roots.map e).prod,
    by simp only [hP, map_mul, map_multiset_prod, Multiset.map_map, Function.comp_def, hxe],
    by simp only [hP, map_mul, map_multiset_prod, Multiset.map_map, Function.comp_def, hye]⟩

/-- **Two points of the closed unit disc that take the value of one and the same nonzero constant on
every `T - b` are equal**, over an algebraically closed field. Both then have trivial support and
compare polynomials as the norm compares constants, and polynomials are dense. -/
theorem eq_of_forall_valuation_weightedX_sub_weightedC_eq [IsAlgClosed K]
    {x y : closedPolydisc 1 K}
    (h : ∀ b : K, ∃ e : K, e ≠ 0 ∧ x.1.valuation (T - C b) = x.1.valuation (C e) ∧
      y.1.valuation (T - C b) = y.1.valuation (C e)) : x = y := by
  have hcont (z : closedPolydisc 1 K) : z.1.valuation.IsContinuous :=
    (ValuationSpectrum.isContinuous_def _).mp ((mem_closedPolydisc_iff 1 K z.1).mp z.2).1
  -- a point with nonzero support kills some `T - b`, so both points have trivial support
  have h0 (z : closedPolydisc 1 K)
      (hz : ∀ b : K, ∃ e : K, e ≠ 0 ∧ z.1.valuation (T - C b) = z.1.valuation (C e)) (f : 𝒯) :
      z.1.valuation f = 0 ↔ f = 0 := by
    suffices hsupp : z.1.supp = ⊥ by
      rw [← Valuation.mem_supp_iff, ← supp_eq_valuation_supp, hsupp, Ideal.mem_bot]
    by_contra hne
    obtain ⟨b, -, hb⟩ := exists_weightedX_sub_weightedC_mem_supp z hne
    obtain ⟨e, he, hze⟩ := hz b
    rw [supp_eq_valuation_supp, Valuation.mem_supp_iff, hze] at hb
    exact he ((closedPolydisc_valuation_weightedC_eq_zero_iff z e).mp hb)
  have hequiv : x.1.valuation.IsEquiv y.1.valuation := by
    refine (hcont x).isEquiv_of_dense (hcont y)
      (fun f ↦ (h0 x (fun b ↦ (h b).imp fun _ he ↦ ⟨he.1, he.2.1⟩) f).trans
        (h0 y (fun b ↦ (h b).imp fun _ he ↦ ⟨he.1, he.2.2⟩) f).symm)
      (denseRange_eval₂RingHom_weightedX isWeightFamily_one_weight) ?_
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    have h' (b : K) := (h b).imp fun _ he ↦ he.2
    obtain ⟨u, hxu, hyu⟩ := exists_valuation_eval₂RingHom_eq_valuation_weightedC h' p
    obtain ⟨w, hxw, hyw⟩ := exists_valuation_eval₂RingHom_eq_valuation_weightedC h' q
    rw [hxu, hxw, hyu, hyw, closedPolydisc_valuation_weightedC_le_iff,
      closedPolydisc_valuation_weightedC_le_iff]
  exact Subtype.ext (ext' fun f g ↦ by
    rw [← valuation_le_iff, ← valuation_le_iff]
    exact hequiv f g)

/-! ### The characterisations -/

/-- **The points `η_{a,r}` among the points of the closed unit disc**, over an algebraically closed
complete nonarchimedean field: a point `x` is `η_{a,r}` if and only if `x(T - a) ≤ x(T - b)` for
every `b` with `‖b - a‖ ≤ r`, and `x(T - a)` compares with the constants as `r` compares with their
norms. These are the points of types (2) and (3) in Wedhorn's Example 7.57. -/
theorem eq_discPoint_iff [IsAlgClosed K] (x : closedPolydisc 1 K) {a : K} (ha : ‖a‖ ≤ 1)
    (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    x = discPoint a ha hr₀ hr₁ ↔
      (∀ b : K, ‖b - a‖ ≤ r → x.1.toValuativeRel.vle (T - C a) (T - C b)) ∧
      (∀ c : K, x.1.toValuativeRel.vle (T - C a) (C c) ↔ r ≤ ‖c‖) ∧
      (∀ c : K, x.1.toValuativeRel.vle (C c) (T - C a) ↔ ‖c‖ ≤ r) := by
  have hG := coe_closedDiscGaussValuation_taylorHom_weightedX_sub_weightedC ha hr₀ hr₁
  set η := discPoint a ha hr₀ hr₁
  have hη : (∀ b : K, ‖b - a‖ ≤ r → η.1.toValuativeRel.vle (T - C a) (T - C b)) ∧
      (∀ c : K, η.1.toValuativeRel.vle (T - C a) (C c) ↔ r ≤ ‖c‖) ∧
      (∀ c : K, η.1.toValuativeRel.vle (C c) (T - C a) ↔ ‖c‖ ≤ r) := by
    refine ⟨fun b _ ↦ ?_, fun c ↦ ?_, fun c ↦ ?_⟩ <;>
      simp only [η, discPoint_vle_iff, ← NNReal.coe_le_coe, hG, taylorHom_weightedC,
        closedDiscGaussValuation_weightedC, coe_nnnorm, sub_self, norm_zero, max_eq_left hr₀.le]
    · exact le_max_left _ _
  refine ⟨by rintro rfl; exact hη, fun ⟨hmin, hle, hge⟩ ↦ ?_⟩
  obtain ⟨hmin', hle', hge'⟩ := hη
  refine eq_of_valuation_eq_ite (fun b ↦ ‖b - a‖ ≤ r) (valuation_weightedX_sub_weightedC hmin hge)
    (valuation_weightedX_sub_weightedC hmin' hge')
    (valuation_weightedX_sub_weightedC_ne_zero hr₀ hle)
    (valuation_weightedX_sub_weightedC_ne_zero hr₀ hle') fun e ↦ ?_
  simp only [valuation_le_iff, hle, hle', hge, hge', and_self]

/-- **The points `η_{a,r⁺}` among the points of the closed unit disc**, over an algebraically
closed complete nonarchimedean field: a point `x` is `η_{a,r⁺}` if and only if `x(T - a) ≤ x(c)`
holds for exactly the constants `c` with `r < ‖c‖`, so that `x(T - a)` lies just above the
constants of norm `r`. For `r` the norm of an element of `K` these are the points of type (5)
written `a_{>r}` in Wedhorn's Example 7.57. -/
theorem eq_discPointAbove_iff [IsAlgClosed K] (x : closedPolydisc 1 K) {a : K} (ha : ‖a‖ ≤ 1)
    (hr₀ : 0 < r) (hr₁ : r < 1) :
    x = discPointAbove a ha hr₀ hr₁ ↔
      ∀ c : K, x.1.toValuativeRel.vle (T - C a) (C c) ↔ r < ‖c‖ := by
  have hη := discPointAbove_vle_weightedC_iff a ha hr₀ hr₁
  refine ⟨by rintro rfl; exact hη, fun h ↦ ?_⟩
  exact eq_of_forall_lt_of_forall_gt (fun c ↦ ‖c‖ ≤ r) (by simpa using hr₀.le)
    (forall_lt_and_forall_gt_of_vle_weightedC hr₀ h)
    (forall_lt_and_forall_gt_of_vle_weightedC hr₀ hη)

/-- **The points `η_{a,r⁻}` among the points of the closed unit disc**, over an algebraically
closed complete nonarchimedean field: a point `x` is `η_{a,r⁻}` if and only if `x(c) ≤ x(T - a)`
holds for exactly the constants `c` with `‖c‖ < r`, so that `x(T - a)` lies just below the
constants of norm `r`. For `r` the norm of an element of `K` these are the points of type (5)
written `a_{<r}` in Wedhorn's Example 7.57. -/
theorem eq_discPointBelow_iff [IsAlgClosed K] (x : closedPolydisc 1 K) {a : K} (ha : ‖a‖ ≤ 1)
    (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    x = discPointBelow a ha hr₀ hr₁ ↔
      ∀ c : K, x.1.toValuativeRel.vle (C c) (T - C a) ↔ ‖c‖ < r := by
  have hη := discPointBelow_weightedC_vle_iff a ha hr₀ hr₁
  refine ⟨by rintro rfl; exact hη, fun h ↦ ?_⟩
  exact eq_of_forall_lt_of_forall_gt (fun c ↦ ‖c‖ < r) (by simpa using hr₀)
    (forall_lt_and_forall_gt_of_weightedC_vle h)
    (forall_lt_and_forall_gt_of_weightedC_vle hη)

end TauCeti.ValuationSpectrum
