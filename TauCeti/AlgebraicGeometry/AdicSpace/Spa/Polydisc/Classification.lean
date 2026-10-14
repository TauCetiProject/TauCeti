/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.ClassicalPoint
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.NestedDiscPoint

import TauCeti.Algebra.Polynomial.Splits
import TauCeti.Analysis.Normed.Field.Basic
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded
import TauCeti.RingTheory.Huber.Restricted.OneVariable

/-!
# The points of the closed unit disc

Let `K` be an algebraically closed complete nontrivially normed nonarchimedean field and
`X = Spa (K⟨T⟩, K⟨T⟩°)` the closed unit disc. Wedhorn's Example 7.57 sorts the points of `X` into
five types. This file recognises the points of types (2), (3) and (5) among all points of `X`, and
proves that every point of `X` is of one of the five types.

The points of types (2) and (3) are the Gauss points `η_{a,r}` of the discs
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

To see that the five types exhaust `X`, recall that a point with nonzero support is classical, of
type (1) (`TauCeti.ValuationSpectrum.supp_ne_bot_iff_exists_eq_classicalPoint`). For a point `x`
with trivial support and a centre `b` of the disc, let `ρ(b)` be the infimum of the norms of the
constants `c` with `x(T - b) ≤ x(c)`: so `x(T - b)` lies above the constants of norm less than
`ρ(b)` and below those of norm greater than `ρ(b)`. It is positive because `x` is continuous and
does not vanish on `T - b`, and the ultrametric inequality gives `ρ(b) ≤ max(ρ(b'), ‖b - b'‖)`.
If `ρ(b') < ρ(b)` then `x(T - b) = x(b - b')`, so `ρ(b) = ‖b - b'‖`.

* If `ρ` attains its infimum `r` at a centre `a`, compare `x(T - a)` with the constants of norm `r`.
  If there are none, or `x(T - a)` equals their value, `x = η_{a,r}`, unless some `x(T - b)` with
  `‖b - a‖ ≤ r` is smaller; such an `x(T - b)` lies just below the constants of norm `r`, and
  `x = η_{b,r⁻}`. If `x(T - a)` lies strictly below or above them, `x = η_{a,r⁻}` or `η_{a,r⁺}`.
* Otherwise choose centres `aₙ` along which `ρ` decreases strictly to its infimum. The discs
  `D(aₙ, ρ(aₙ))` decrease, have radius `ρ(aₙ) = ‖aₙ - aₙ₊₁‖`, and have no common point in `K`,
  since every centre `b` has `ρ(b) > ρ(aₙ)` for some `n`. On `T - b` both `x` and the point
  attached to these discs take the value of the constant `b - aₙ`, so they are equal.

## Main results

* `TauCeti.ValuationSpectrum.eq_discPoint_iff`: a point of the closed unit disc over an
  algebraically closed field is `η_{a,r}` if and only if it satisfies the two conditions above.
* `TauCeti.ValuationSpectrum.eq_discPointAbove_iff` and
  `TauCeti.ValuationSpectrum.eq_discPointBelow_iff`: it is `η_{a,r⁺}`, respectively `η_{a,r⁻}`, if
  and only if `x(T - a)` lies just above, respectively just below, the constants of norm `r`.
* `exists_eq_discPoint_or_discPointAbove_or_discPointBelow_or_nestedDiscPoint`, in the namespace
  `TauCeti.ValuationSpectrum`: a point with trivial support is of type (2), (3), (4) or (5).
* `exists_eq_classicalPoint_or_discPoint_or_discPointAbove_or_discPointBelow_or_nestedDiscPoint`:
  every point of the closed unit disc is of one of the five types.
* `TauCeti.ValuationSpectrum.eq_of_forall_valuation_weightedX_sub_weightedC_eq`: two points that
  take the value of one and the same nonzero constant on every `T - b` are equal.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
* V. G. Berkovich, *Spectral theory and analytic geometry over non-Archimedean fields*,
  Mathematical Surveys and Monographs 33, AMS, 1990, §1.4.4, for the classification of the
  rank-one points by nested discs, which the argument above follows.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), Example 2.20.
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

/-- Moving the centre of `T - b` to `a`. -/
private theorem weightedX_sub_weightedC_eq_sub (a b : K) : T - C b = (T - C a) - C (b - a) := by
  rw [map_sub]
  ring

/-- Under the two conditions characterising `η_{a,r}`, `x(T - b)` is `x(T - a)` on the disc
`D(a, r)` and `x(b - a)` off it. -/
private theorem valuation_weightedX_sub_weightedC {x : closedPolydisc 1 K} {a : K}
    (hmin : ∀ b : K, ‖b - a‖ ≤ r → x.1.toValuativeRel.vle (T - C a) (T - C b))
    (hge : ∀ c : K, x.1.toValuativeRel.vle (C c) (T - C a) ↔ ‖c‖ ≤ r) (b : K) :
    x.1.valuation (T - C b) =
      if ‖b - a‖ ≤ r then x.1.valuation (T - C a) else x.1.valuation (C (b - a)) := by
  split_ifs with hb
  · refine le_antisymm ?_ ((valuation_le_iff _ _ _).mpr (hmin b hb))
    rw [weightedX_sub_weightedC_eq_sub a b]
    exact (Valuation.map_sub _ _ _).trans
      (max_le le_rfl ((valuation_le_iff _ _ _).mpr ((hge _).mpr hb)))
  · rw [weightedX_sub_weightedC_eq_sub a b, Valuation.map_sub_eq_of_lt_right]
    exact lt_of_not_ge fun h ↦ hb ((hge _).mp ((valuation_le_iff _ _ _).mp h))

/-- If `x(T - a)` is strictly larger than `x(c)` for the constants with `Q c` and strictly smaller
for the others, then `x(T - b)` is `x(T - a)` when `Q (b - a)` and `x(b - a)` otherwise. -/
private theorem valuation_weightedX_sub_weightedC_of_lt {x : closedPolydisc 1 K} {a : K}
    (Q : K → Prop) [DecidablePred Q]
    (hlt : ∀ c : K, Q c → x.1.valuation (C c) < x.1.valuation (T - C a))
    (hgt : ∀ c : K, ¬ Q c → x.1.valuation (T - C a) < x.1.valuation (C c)) (b : K) :
    x.1.valuation (T - C b) =
      if Q (b - a) then x.1.valuation (T - C a) else x.1.valuation (C (b - a)) := by
  rw [weightedX_sub_weightedC_eq_sub a b]
  split_ifs with hb
  · exact Valuation.map_sub_eq_of_lt_left _ (hlt _ hb)
  · exact Valuation.map_sub_eq_of_lt_right _ (hgt _ hb)

/-- If `x(T - a) < x(b - a)`, then `x(T - b) = x(b - a)`. -/
private theorem valuation_weightedX_sub_weightedC_eq_of_lt {x : closedPolydisc 1 K} {a b : K}
    (h : x.1.valuation (T - C a) < x.1.valuation (C (b - a))) :
    x.1.valuation (T - C b) = x.1.valuation (C (b - a)) := by
  rw [weightedX_sub_weightedC_eq_sub a b]
  exact Valuation.map_sub_eq_of_lt_right _ h

/-- Under the second condition characterising `η_{a,r}`, `x(T - a) ≠ 0`. -/
private theorem valuation_weightedX_sub_weightedC_ne_zero {x : closedPolydisc 1 K} {a : K}
    (hr₀ : 0 < r) (hle : ∀ c : K, x.1.toValuativeRel.vle (T - C a) (C c) ↔ r ≤ ‖c‖) :
    x.1.valuation (T - C a) ≠ 0 := fun h ↦ by
  have := (hle 0).mp ((valuation_le_iff _ _ _).mp (h ▸ zero_le))
  rw [norm_zero] at this
  exact hr₀.not_ge this

/-! ### Two points that compare `T - a` with the constants in the same way -/

/-- If `x` and `y` take the value of `T - a` on `T - b` for `b ∈ P` and the value of the constant
`d b` for `b ∉ P`, then on every polynomial they take values `x(c) x(T - a)^m` and `y(c) y(T - a)^m`
for the same `c` and `m`. -/
private theorem exists_valuation_eval₂RingHom_eq [IsAlgClosed K] {x y : closedPolydisc 1 K} {a : K}
    (P : K → Prop) [DecidablePred P] (d : K → K)
    (hx : ∀ b : K, x.1.valuation (T - C b) =
      if P b then x.1.valuation (T - C a) else x.1.valuation (C (d b)))
    (hy : ∀ b : K, y.1.valuation (T - C b) =
      if P b then y.1.valuation (T - C a) else y.1.valuation (C (d b))) (p : Polynomial K) :
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
      · refine ⟨d b * c, m, ?_, ?_⟩ <;>
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
private theorem forall_lt_and_forall_gt_of_vle_weightedC_iff [IsAlgClosed K]
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
private theorem forall_lt_and_forall_gt_of_weightedC_vle_iff [IsAlgClosed K]
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

/-! ### The radius of a point about a centre -/

/-- A point of the closed unit disc is at most one on `T - b` for `‖b‖ ≤ 1`. -/
private theorem valuation_weightedX_sub_weightedC_le_one (x : closedPolydisc 1 K) {b : K}
    (hb : ‖b‖ ≤ 1) : x.1.valuation (T - C b) ≤ x.1.valuation (C 1) := by
  have hT : x.1.valuation T ≤ x.1.valuation (C 1) := by
    rw [map_one, valuation_le_iff]
    exact ((mem_closedPolydisc_iff 1 K x.1).mp x.2).2 _
      (mem_powerBoundedSubring.mpr (isPowerBounded_weightedX_one_weight 0))
  exact (Valuation.map_sub _ _ _).trans
    (max_le hT ((closedPolydisc_valuation_weightedC_le_iff x b 1).mpr (by rwa [norm_one])))

/-- The radius of a point `x` of the disc about `b`: the infimum of the norms of the constants `c`
with `x(T - b) ≤ x(c)`. The value `x(T - b)` lies above the constants of smaller norm and below
those of larger norm. -/
private noncomputable def cutRadius (x : closedPolydisc 1 K) (b : K) : ℝ :=
  sInf (norm '' {c : K | x.1.valuation (T - C b) ≤ x.1.valuation (C c)})

omit [IsUltrametricDist K] in
private theorem cutRadius_nonneg (x : closedPolydisc 1 K) (b : K) : 0 ≤ cutRadius x b :=
  Real.sInf_nonneg (by rintro _ ⟨c, -, rfl⟩; exact norm_nonneg c)

omit [IsUltrametricDist K] in
private theorem bddBelow_cutRadius (x : closedPolydisc 1 K) (b : K) :
    BddBelow (norm '' {c : K | x.1.valuation (T - C b) ≤ x.1.valuation (C c)}) :=
  ⟨0, by rintro _ ⟨c, -, rfl⟩; exact norm_nonneg c⟩

omit [IsUltrametricDist K] in
private theorem cutRadius_le {x : closedPolydisc 1 K} {b c : K}
    (h : x.1.valuation (T - C b) ≤ x.1.valuation (C c)) : cutRadius x b ≤ ‖c‖ :=
  csInf_le (bddBelow_cutRadius x b) ⟨c, h, rfl⟩

private theorem norm_le_cutRadius {x : closedPolydisc 1 K} {b c : K} (hb : ‖b‖ ≤ 1)
    (h : x.1.valuation (C c) ≤ x.1.valuation (T - C b)) : ‖c‖ ≤ cutRadius x b :=
  le_csInf ⟨_, 1, valuation_weightedX_sub_weightedC_le_one x hb, rfl⟩ <| by
    rintro _ ⟨d, hd, rfl⟩
    exact (closedPolydisc_valuation_weightedC_le_iff x c d).mp (h.trans hd)

private theorem cutRadius_le_one (x : closedPolydisc 1 K) {b : K} (hb : ‖b‖ ≤ 1) :
    cutRadius x b ≤ 1 :=
  norm_one (α := K) ▸ cutRadius_le (valuation_weightedX_sub_weightedC_le_one x hb)

omit [IsUltrametricDist K] in
/-- The constants of norm below the radius about `b` take smaller values than `T - b`. -/
private theorem valuation_weightedC_lt_of_norm_lt_cutRadius {x : closedPolydisc 1 K} {b c : K}
    (h : ‖c‖ < cutRadius x b) : x.1.valuation (C c) < x.1.valuation (T - C b) :=
  lt_of_not_ge fun h' ↦ h.not_ge (cutRadius_le h')

/-- The constants of norm above the radius about `b` take larger values than `T - b`. -/
private theorem valuation_lt_of_cutRadius_lt_norm {x : closedPolydisc 1 K} {b c : K}
    (hb : ‖b‖ ≤ 1) (h : cutRadius x b < ‖c‖) : x.1.valuation (T - C b) < x.1.valuation (C c) := by
  obtain ⟨_, ⟨c', hc', rfl⟩, hlt⟩ := (csInf_lt_iff (bddBelow_cutRadius x b)
    ⟨_, 1, valuation_weightedX_sub_weightedC_le_one x hb, rfl⟩).mp h
  exact (Set.mem_ofPred_eq ▸ hc').trans_lt
    (lt_of_not_ge fun h' ↦ hlt.not_ge ((closedPolydisc_valuation_weightedC_le_iff x c c').mp h'))

/-- If `x(T - b) = x(d)`, the radius about `b` is `‖d‖`. -/
private theorem cutRadius_eq_norm {x : closedPolydisc 1 K} {b d : K} (hb : ‖b‖ ≤ 1)
    (h : x.1.valuation (T - C b) = x.1.valuation (C d)) : cutRadius x b = ‖d‖ :=
  le_antisymm (cutRadius_le h.le) (norm_le_cutRadius hb h.ge)

/-- A point that does not vanish on `T - b` has positive radius about `b`: by continuity, the
constants of small norm take smaller values than `T - b`. -/
private theorem cutRadius_pos {x : closedPolydisc 1 K} {b : K} (hb : ‖b‖ ≤ 1)
    (h : x.1.valuation (T - C b) ≠ 0) : 0 < cutRadius x b := by
  have hcont : x.1.valuation.IsContinuous :=
    (ValuationSpectrum.isContinuous_def _).mp ((mem_closedPolydisc_iff 1 K x.1).mp x.2).1
  have hopen := (Valuation.isContinuous_def.mp hcont (T - C b)).preimage
    (continuous_weightedC isWeightFamily_one_weight)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0
    (by simpa only [Set.mem_preimage, map_zero, Set.mem_ofPred_eq] using zero_lt_iff.mpr h)
  obtain ⟨c, hc₀, hcε⟩ := NormedField.exists_norm_lt K hε
  exact hc₀.trans_le (norm_le_cutRadius hb (hball (mem_ball_zero_iff.mpr hcε)).le)

/-- The radii about two centres differ by at most the distance of the centres. -/
private theorem cutRadius_le_max [IsAlgClosed K] {x : closedPolydisc 1 K} {b b' : K}
    (hb' : ‖b'‖ ≤ 1) : cutRadius x b ≤ max (cutRadius x b') ‖b - b'‖ := by
  by_contra! h
  obtain ⟨c, h₁, h₂⟩ := NormedField.exists_lt_norm_lt_of_isAlgClosed K
    ((cutRadius_nonneg x b').trans (le_max_left _ _)) h
  refine h₂.not_ge (cutRadius_le ?_)
  rw [weightedX_sub_weightedC_eq_sub b' b]
  exact (Valuation.map_sub _ _ _).trans (max_le
    (valuation_lt_of_cutRadius_lt_norm hb' ((le_max_left _ _).trans_lt h₁)).le
    ((closedPolydisc_valuation_weightedC_le_iff x _ _).mpr ((le_max_right _ _).trans h₁.le)))

/-- If the radius about `b'` is smaller than the radius about `b`, then `x(T - b) = x(b - b')`. -/
private theorem valuation_eq_of_cutRadius_lt [IsAlgClosed K] {x : closedPolydisc 1 K} {b b' : K}
    (hb' : ‖b'‖ ≤ 1) (h : cutRadius x b' < cutRadius x b) :
    x.1.valuation (T - C b) = x.1.valuation (C (b - b')) := by
  refine valuation_weightedX_sub_weightedC_eq_of_lt (valuation_lt_of_cutRadius_lt_norm hb' ?_)
  by_contra! h'
  exact ((cutRadius_le_max hb').trans (max_le le_rfl h')).not_gt h

/-- If the radius about `b` is at least `‖c₀‖` and `x(T - b) < x(c₀)`, then `x(c) ≤ x(T - b)`
holds for exactly the constants with `‖c‖ < ‖c₀‖`. -/
private theorem weightedC_vle_iff_of_lt {x : closedPolydisc 1 K} {b c₀ : K}
    (hr : ‖c₀‖ ≤ cutRadius x b) (hlt : x.1.valuation (T - C b) < x.1.valuation (C c₀)) (c : K) :
    x.1.toValuativeRel.vle (C c) (T - C b) ↔ ‖c‖ < ‖c₀‖ := by
  rw [← valuation_le_iff]
  refine ⟨fun h ↦ lt_of_not_ge fun h' ↦ (h.trans_lt hlt).not_ge
    ((closedPolydisc_valuation_weightedC_le_iff x c₀ c).mpr h'), fun h ↦ ?_⟩
  exact (valuation_weightedC_lt_of_norm_lt_cutRadius (h.trans_le hr)).le

/-- If the radius about `b` is at most `‖c₀‖` and `x(c₀) < x(T - b)`, then `x(T - b) ≤ x(c)`
holds for exactly the constants with `‖c₀‖ < ‖c‖`. -/
private theorem vle_weightedC_iff_of_lt {x : closedPolydisc 1 K} {b c₀ : K} (hb : ‖b‖ ≤ 1)
    (hr : cutRadius x b ≤ ‖c₀‖) (hlt : x.1.valuation (C c₀) < x.1.valuation (T - C b)) (c : K) :
    x.1.toValuativeRel.vle (T - C b) (C c) ↔ ‖c₀‖ < ‖c‖ := by
  rw [← valuation_le_iff]
  refine ⟨fun h ↦ lt_of_not_ge fun h' ↦ (hlt.trans_le h).not_ge
    ((closedPolydisc_valuation_weightedC_le_iff x c c₀).mpr h'), fun h ↦ ?_⟩
  exact (valuation_lt_of_cutRadius_lt_norm hb (hr.trans_lt h)).le

/-! ### Equality of two points that compare `T - a` with the constants in the same way -/

variable [CompleteSpace K]

/-- If `x` takes the value of `T - a` on `T - b` for `b ∈ P` and the value of the nonzero constant
`d b` for `b ∉ P`, and `x(T - a) ≠ 0`, then `x` has trivial support: a point with nonzero support
kills some `T - b`. -/
private theorem valuation_eq_zero_iff_of_eq_ite [IsAlgClosed K] {x : closedPolydisc 1 K} {a : K}
    (P : K → Prop) [DecidablePred P] (d : K → K) (hd : ∀ b : K, ¬ P b → d b ≠ 0)
    (hx : ∀ b : K, x.1.valuation (T - C b) =
      if P b then x.1.valuation (T - C a) else x.1.valuation (C (d b)))
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
  · exact (closedPolydisc_valuation_weightedC_eq_zero_iff x (d b)).not.mpr (hd b hP) hb'.symm

/-- **Two points that compare `T - a` with the constants in the same way are equal**, provided
both do not vanish on `T - a` and both take the value of `T - a` on `T - b` for `b ∈ P` and the
value of the same nonzero constant `d b` for `b ∉ P`. -/
private theorem eq_of_valuation_eq_ite [IsAlgClosed K] {x y : closedPolydisc 1 K} {a : K}
    (P : K → Prop) [DecidablePred P] (d : K → K) (hd : ∀ b : K, ¬ P b → d b ≠ 0)
    (hx : ∀ b : K, x.1.valuation (T - C b) =
      if P b then x.1.valuation (T - C a) else x.1.valuation (C (d b)))
    (hy : ∀ b : K, y.1.valuation (T - C b) =
      if P b then y.1.valuation (T - C a) else y.1.valuation (C (d b)))
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
      (fun f ↦ (valuation_eq_zero_iff_of_eq_ite P d hd hx hx₀ f).trans
        (valuation_eq_zero_iff_of_eq_ite P d hd hy hy₀ f).symm)
      (denseRange_eval₂RingHom_weightedX isWeightFamily_one_weight) ?_
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    obtain ⟨c, m, hp, hp'⟩ := exists_valuation_eval₂RingHom_eq P d hx hy p
    obtain ⟨e, n, hq, hq'⟩ := exists_valuation_eval₂RingHom_eq P d hx hy q
    rw [hp, hq, hp', hq']
    exact valuation_mul_pow_le_iff hx₀ hy₀ hcmp c e m n
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
  refine eq_of_valuation_eq_ite (fun b ↦ Q (b - a)) (· - a) (fun b hb h ↦ hb (h ▸ hQ))
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
  refine eq_of_valuation_eq_ite (fun b ↦ ‖b - a‖ ≤ r) (· - a)
    (fun b hb h ↦ hb (by rw [h, norm_zero]; exact hr₀.le))
    (valuation_weightedX_sub_weightedC hmin hge) (valuation_weightedX_sub_weightedC hmin' hge')
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
    (forall_lt_and_forall_gt_of_vle_weightedC_iff hr₀ h)
    (forall_lt_and_forall_gt_of_vle_weightedC_iff hr₀ hη)

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
    (forall_lt_and_forall_gt_of_weightedC_vle_iff h)
    (forall_lt_and_forall_gt_of_weightedC_vle_iff hη)

/-! ### Every point of the disc is of one of the five types -/

/-- **A point whose radius is smallest about some centre `a`** is a point `η_{a,r}`, `η_{a,r⁺}` or
`η_{b,r⁻}`, the last two only for `r` the norm of a constant. -/
private theorem exists_eq_of_forall_cutRadius_le [IsAlgClosed K] {x : closedPolydisc 1 K}
    {a : K} (ha : ‖a‖ ≤ 1) (hx : x.1.valuation (T - C a) ≠ 0)
    (hmin : ∀ b : K, ‖b‖ ≤ 1 → cutRadius x a ≤ cutRadius x b) :
    (∃ (a : K) (ha : ‖a‖ ≤ 1) (r : ℝ) (hr₀ : 0 < r) (hr₁ : r ≤ 1),
        x = discPoint a ha hr₀ hr₁) ∨
      (∃ (a : K) (ha : ‖a‖ ≤ 1) (c : K) (hc₀ : 0 < ‖c‖) (hc₁ : ‖c‖ < 1),
        x = discPointAbove a ha hc₀ hc₁) ∨
      ∃ (a : K) (ha : ‖a‖ ≤ 1) (c : K) (hc₀ : 0 < ‖c‖) (hc₁ : ‖c‖ ≤ 1),
        x = discPointBelow a ha hc₀ hc₁ := by
  have hr₀ : 0 < cutRadius x a := cutRadius_pos ha hx
  have hr₁ : cutRadius x a ≤ 1 := cutRadius_le_one x ha
  by_cases hK : ∃ c : K, ‖c‖ = cutRadius x a
  swap
  · -- the radius is not a norm, so `x(T - a)` sits exactly at it: `x = η_{a,r}`
    push Not at hK
    refine Or.inl ⟨a, ha, _, hr₀, hr₁, (eq_discPoint_iff x ha hr₀ hr₁).mpr ⟨fun b hb ↦ ?_,
      fun c ↦ ?_, fun c ↦ ?_⟩⟩
    · rw [← valuation_le_iff, weightedX_sub_weightedC_eq_sub a b,
        Valuation.map_sub_eq_of_lt_left _ (valuation_weightedC_lt_of_norm_lt_cutRadius
          (lt_of_le_of_ne hb (hK _)))]
    · rw [← valuation_le_iff]
      exact ⟨fun h ↦ le_of_not_gt fun h' ↦ (valuation_weightedC_lt_of_norm_lt_cutRadius h').not_ge
        h, fun h ↦ (valuation_lt_of_cutRadius_lt_norm ha (lt_of_le_of_ne h (hK c).symm)).le⟩
    · rw [← valuation_le_iff]
      exact ⟨fun h ↦ le_of_not_gt fun h' ↦ (valuation_lt_of_cutRadius_lt_norm ha h').not_ge h,
        fun h ↦ (valuation_weightedC_lt_of_norm_lt_cutRadius (lt_of_le_of_ne h (hK c))).le⟩
  obtain ⟨c₀, hc₀⟩ := hK
  rcases lt_trichotomy (x.1.valuation (T - C a)) (x.1.valuation (C c₀)) with hlt | heq | hgt
  · -- `x(T - a)` lies just below the constants of norm `r`: `x = η_{a,r⁻}`
    exact Or.inr (Or.inr ⟨a, ha, c₀, hc₀ ▸ hr₀, hc₀ ▸ hr₁, (eq_discPointBelow_iff x ha _ _).mpr
      (weightedC_vle_iff_of_lt hc₀.le hlt)⟩)
  · by_cases hb : ∃ b : K, ‖b - a‖ ≤ cutRadius x a ∧
        x.1.valuation (T - C b) < x.1.valuation (T - C a)
    · -- some `x(T - b)` lies just below the constants of norm `r`: `x = η_{b,r⁻}`
      obtain ⟨b, hba, hlt⟩ := hb
      have hb₁ : ‖b‖ ≤ 1 := by
        simpa using (IsUltrametricDist.norm_add_le_max (b - a) a).trans
          (max_le (hba.trans hr₁) ha)
      exact Or.inr (Or.inr ⟨b, hb₁, c₀, hc₀ ▸ hr₀, hc₀ ▸ hr₁, (eq_discPointBelow_iff x hb₁ _ _).mpr
        (weightedC_vle_iff_of_lt (hc₀.trans_le (hmin b hb₁)) (heq ▸ hlt))⟩)
    · -- otherwise `x(T - a)` is the smallest value and equals `x(c₀)`: `x = η_{a,r}`
      push Not at hb
      refine Or.inl ⟨a, ha, _, hr₀, hr₁, (eq_discPoint_iff x ha hr₀ hr₁).mpr ⟨fun b hb' ↦ ?_,
        fun c ↦ ?_, fun c ↦ ?_⟩⟩
      · exact (valuation_le_iff _ _ _).mp (hb b hb')
      · rw [← valuation_le_iff, heq, closedPolydisc_valuation_weightedC_le_iff, hc₀]
      · rw [← valuation_le_iff, heq, closedPolydisc_valuation_weightedC_le_iff, hc₀]
  · -- `x(T - a)` lies just above the constants of norm `r`: `x = η_{a,r⁺}`
    have hr₁' : ‖c₀‖ < 1 := lt_of_le_of_ne (hc₀ ▸ hr₁) fun h ↦ hgt.not_ge
      ((valuation_weightedX_sub_weightedC_le_one x ha).trans
        ((closedPolydisc_valuation_weightedC_le_iff x 1 c₀).mpr (by rw [h, norm_one])))
    exact Or.inr (Or.inl ⟨a, ha, c₀, hc₀ ▸ hr₀, hr₁', (eq_discPointAbove_iff x ha _ _).mpr
      (vle_weightedC_iff_of_lt ha hc₀.ge hgt)⟩)

/-- **Two points that take the same values on the discs of a sequence without common point are
equal**: if the discs `D(aₙ, |cₙ|)` have no common point in `K`, and `x(T - aₙ) < x(e)` and
`y(T - aₙ) < y(e)` for every `n` and every constant `e` with `‖cₙ‖ < ‖e‖`, then `x = y`. Both
points then take the value of the constant `b - aₙ` on `T - b`, for `n` with `b ∉ D(aₙ, |cₙ|)`. -/
private theorem eq_of_forall_valuation_lt [IsAlgClosed K] {a c : ℕ → K}
    (hempty : ∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) {x y : closedPolydisc 1 K}
    (hx : ∀ n e, ‖c n‖ < ‖e‖ → x.1.valuation (T - C (a n)) < x.1.valuation (C e))
    (hy : ∀ n e, ‖c n‖ < ‖e‖ → y.1.valuation (T - C (a n)) < y.1.valuation (C e)) :
    x = y := by
  choose N hN using hempty
  have hd (b : K) : b - a (N b) ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt (hN b))
  have hval (z : closedPolydisc 1 K)
      (hz : ∀ n e, ‖c n‖ < ‖e‖ → z.1.valuation (T - C (a n)) < z.1.valuation (C e)) (b : K) :
      z.1.valuation (T - C b) = z.1.valuation (C (b - a (N b))) :=
    valuation_weightedX_sub_weightedC_eq_of_lt (hz _ _ (hN b))
  refine eq_of_valuation_eq_ite (a := a 0) (fun _ ↦ False) (fun b ↦ b - a (N b)) (fun b _ ↦ hd b)
    (fun b ↦ by rw [ite_false, hval x hx]) (fun b ↦ by rw [ite_false, hval y hy])
    (hval x hx (a 0) ▸ (closedPolydisc_valuation_weightedC_eq_zero_iff x _).not.mpr (hd _))
    (hval y hy (a 0) ▸ (closedPolydisc_valuation_weightedC_eq_zero_iff y _).not.mpr (hd _))
    fun e ↦ ?_
  rw [hval x hx, hval y hy, closedPolydisc_valuation_weightedC_le_iff,
    closedPolydisc_valuation_weightedC_le_iff,
    closedPolydisc_valuation_weightedC_le_iff, closedPolydisc_valuation_weightedC_le_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **A point whose radius is smallest about no centre** is the point attached to a decreasing
sequence of discs with no common point in `K`: centres `aₙ` whose radii decrease to the infimum
`r` of all radii, and discs `D(aₙ, ρ(aₙ))`. -/
private theorem exists_eq_nestedDiscPoint [IsAlgClosed K] {x : closedPolydisc 1 K}
    (hB : ∀ a : K, ‖a‖ ≤ 1 → ∃ b : K, ‖b‖ ≤ 1 ∧ cutRadius x b < cutRadius x a) :
    ∃ (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) (c : ℕ → K) (hc₀ : ∀ n, c n ≠ 0)
      (hc₁ : ∀ n, ‖c n‖ ≤ 1) (hac : ∀ n, ‖a (n + 1) - a n‖ ≤ ‖c n‖)
      (hcc : ∀ n, ‖c (n + 1)‖ ≤ ‖c n‖),
      (∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) ∧ x = nestedDiscPoint a ha c hc₀ hc₁ hac hcc := by
  set t := cutRadius x '' {b : K | ‖b‖ ≤ 1}
  have hne : t.Nonempty := ⟨_, 0, by simp, rfl⟩
  have hbdd : BddBelow t := ⟨0, by rintro _ ⟨b, -, rfl⟩; exact cutRadius_nonneg x b⟩
  -- the infimum of the radii is not attained
  have hnot : sInf t ∉ t := by
    rintro ⟨a, ha, hra⟩
    obtain ⟨b, hb, hlt⟩ := hB a ha
    exact (hra ▸ hlt).not_ge (csInf_le hbdd ⟨b, hb, rfl⟩)
  obtain ⟨u, hu, -, hlim, hmem⟩ :=
    (isGLB_csInf hne hbdd).exists_seq_strictAnti_tendsto_of_notMem hnot hne
  choose a ha hau using hmem
  have hlt_succ (n : ℕ) : cutRadius x (a (n + 1)) < cutRadius x (a n) := by
    rw [hau, hau]
    exact hu n.lt_succ_self
  set c : ℕ → K := fun n ↦ a n - a (n + 1)
  -- the radius about `aₙ` is the distance to `aₙ₊₁`
  have hc (n : ℕ) : ‖c n‖ = cutRadius x (a n) :=
    (cutRadius_eq_norm (ha n) (valuation_eq_of_cutRadius_lt (ha (n + 1)) (hlt_succ n))).symm
  -- every centre lies outside some disc `D(aₙ, ρ(aₙ))`
  have hempty (b : K) : ∃ n, ‖c n‖ < ‖b - a n‖ := by
    by_cases hb : ‖b‖ ≤ 1
    · have hlt : sInf t < cutRadius x b :=
        lt_of_le_of_ne (csInf_le hbdd ⟨b, hb, rfl⟩) fun h ↦ hnot (h ▸ ⟨b, hb, rfl⟩)
      obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hlt)).exists
      rw [← hau n] at hn
      exact ⟨n, by rwa [hc, ← cutRadius_eq_norm hb (valuation_eq_of_cutRadius_lt (ha n) hn)]⟩
    · have h₁ : 1 < ‖b‖ := not_le.mp hb
      have h₂ : ‖b‖ ≤ max ‖b - a 0‖ ‖a 0‖ := by
        simpa using IsUltrametricDist.norm_add_le_max (b - a 0) (a 0)
      refine ⟨0, ((hc 0).trans_le (cutRadius_le_one x (ha 0))).trans_lt (h₁.trans_le ?_)⟩
      exact (le_max_iff.mp h₂).resolve_right fun h ↦ (h.trans (ha 0)).not_gt h₁
  have hc₀ (n : ℕ) : c n ≠ 0 :=
    norm_pos_iff.mp ((hc n).symm ▸ (cutRadius_nonneg x _).trans_lt (hlt_succ n))
  have hc₁ (n : ℕ) : ‖c n‖ ≤ 1 := (hc n).trans_le (cutRadius_le_one x (ha n))
  have hac (n : ℕ) : ‖a (n + 1) - a n‖ ≤ ‖c n‖ := (norm_sub_rev _ _).le
  have hcc (n : ℕ) : ‖c (n + 1)‖ ≤ ‖c n‖ := by
    rw [hc, hc]
    exact (hlt_succ n).le
  refine ⟨a, ha, c, hc₀, hc₁, hac, hcc, hempty, eq_of_forall_valuation_lt hempty
    (fun n e h ↦ valuation_lt_of_cutRadius_lt_norm (ha n) (hc n ▸ h)) fun n e h ↦ ?_⟩
  -- the point of the discs is at most `‖cₙ‖` on `T - aₙ`
  rw [← not_le, valuation_le_iff, nestedDiscPoint_vle_iff, not_le, ← NNReal.coe_lt_coe,
    coe_nestedDiscValuation_weightedX_sub_weightedC, nestedDiscValuation_weightedC, coe_nnnorm]
  refine (ciInf_le ⟨0, ?_⟩ n).trans_lt ?_
  · rintro _ ⟨m, rfl⟩
    exact (norm_nonneg _).trans (le_max_left _ _)
  · rwa [sub_self, norm_zero, max_eq_left (norm_nonneg _)]

/-- **The points of the closed unit disc with trivial support**, over an algebraically closed
complete nonarchimedean field: every such point is one of

* a point `η_{a,r}` (types (2) and (3) in Wedhorn's Example 7.57);
* a rank-two point `η_{a,r⁺}` or `η_{a,r⁻}` with `r` the norm of an element of `K` (type (5));
* the point attached to a decreasing sequence of discs `D(aₙ, |cₙ|)` with no common point in `K`
  (type (4)). -/
theorem exists_eq_discPoint_or_discPointAbove_or_discPointBelow_or_nestedDiscPoint [IsAlgClosed K]
    (x : closedPolydisc 1 K) (hx : x.1.supp = ⊥) :
    (∃ (a : K) (ha : ‖a‖ ≤ 1) (r : ℝ) (hr₀ : 0 < r) (hr₁ : r ≤ 1),
        x = discPoint a ha hr₀ hr₁) ∨
      (∃ (a : K) (ha : ‖a‖ ≤ 1) (c : K) (hc₀ : 0 < ‖c‖) (hc₁ : ‖c‖ < 1),
        x = discPointAbove a ha hc₀ hc₁) ∨
      (∃ (a : K) (ha : ‖a‖ ≤ 1) (c : K) (hc₀ : 0 < ‖c‖) (hc₁ : ‖c‖ ≤ 1),
        x = discPointBelow a ha hc₀ hc₁) ∨
      ∃ (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) (c : ℕ → K) (hc₀ : ∀ n, c n ≠ 0)
        (hc₁ : ∀ n, ‖c n‖ ≤ 1) (hac : ∀ n, ‖a (n + 1) - a n‖ ≤ ‖c n‖)
        (hcc : ∀ n, ‖c (n + 1)‖ ≤ ‖c n‖),
        (∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) ∧ x = nestedDiscPoint a ha c hc₀ hc₁ hac hcc := by
  -- `x` vanishes on no `T - b` with `‖b‖ ≤ 1`, else it would be the classical point at `b`
  have hx₀ (b : K) (hb : ‖b‖ ≤ 1) : x.1.valuation (T - C b) ≠ 0 := fun h ↦
    ne_classicalPoint_of_supp_eq_bot x hx ⟨_, comap_weightedC_mem_spa x⟩ (fun _ ↦ b)
      (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr hb)
      (eq_classicalPoint_of_weightedX_sub_weightedC_mem_supp x _ _
        (by rw [supp_eq_valuation_supp, Valuation.mem_supp_iff]; exact h) _)
  -- either the radius `ρ(b)` of `x(T - b)` is smallest about some centre, or it is not
  by_cases hA : ∃ a : K, ‖a‖ ≤ 1 ∧ ∀ b : K, ‖b‖ ≤ 1 → cutRadius x a ≤ cutRadius x b
  · obtain ⟨a, ha, hmin⟩ := hA
    rcases exists_eq_of_forall_cutRadius_le ha (hx₀ a ha) hmin with h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h))]
  · push Not at hA
    exact Or.inr (Or.inr (Or.inr (exists_eq_nestedDiscPoint hA)))

/-- **Every point of the closed unit disc is of one of Wedhorn's five types**, over an
algebraically closed complete nonarchimedean field (Example 7.57): a classical point `x_a`
(type (1)), a point `η_{a,r}` (types (2) and (3)), the point attached to a decreasing sequence of
discs `D(aₙ, |cₙ|)` with no common point in `K` (type (4)), or a rank-two point `η_{a,r⁺}` or
`η_{a,r⁻}` with `r` the norm of an element of `K` (type (5)). -/
theorem exists_eq_classicalPoint_or_discPoint_or_discPointAbove_or_discPointBelow_or_nestedDiscPoint
    [IsAlgClosed K] (x : closedPolydisc 1 K) :
    (∃ (y : spa (powerBoundedSubring K)) (a : Fin 1 → K) (ha : ∀ i, IsPowerBounded (a i)),
        x = classicalPoint y a ha) ∨
      (∃ (a : K) (ha : ‖a‖ ≤ 1) (r : ℝ) (hr₀ : 0 < r) (hr₁ : r ≤ 1),
        x = discPoint a ha hr₀ hr₁) ∨
      (∃ (a : K) (ha : ‖a‖ ≤ 1) (c : K) (hc₀ : 0 < ‖c‖) (hc₁ : ‖c‖ < 1),
        x = discPointAbove a ha hc₀ hc₁) ∨
      (∃ (a : K) (ha : ‖a‖ ≤ 1) (c : K) (hc₀ : 0 < ‖c‖) (hc₁ : ‖c‖ ≤ 1),
        x = discPointBelow a ha hc₀ hc₁) ∨
      ∃ (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) (c : ℕ → K) (hc₀ : ∀ n, c n ≠ 0)
        (hc₁ : ∀ n, ‖c n‖ ≤ 1) (hac : ∀ n, ‖a (n + 1) - a n‖ ≤ ‖c n‖)
        (hcc : ∀ n, ‖c (n + 1)‖ ≤ ‖c n‖),
        (∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) ∧ x = nestedDiscPoint a ha c hc₀ hc₁ hac hcc := by
  by_cases hx : x.1.supp = ⊥
  · exact Or.inr (exists_eq_discPoint_or_discPointAbove_or_discPointBelow_or_nestedDiscPoint x hx)
  · exact Or.inl ((supp_ne_bot_iff_exists_eq_classicalPoint x).mp hx)

/-! ### Recognising points of type (4) -/

section NestedDiscRecognition

variable {a c : ℕ → K} (ha : ∀ n, ‖a n‖ ≤ 1) (hc₀ : ∀ n, c n ≠ 0)
  (hc₁ : ∀ n, ‖c n‖ ≤ 1) (hac : ∀ n, ‖a (n + 1) - a n‖ ≤ ‖c n‖)
  (hcc : ∀ n, ‖c (n + 1)‖ ≤ ‖c n‖)

/-- **With no common point of the discs in `K`, the point is the only point lying in all of them**,
over an algebraically closed field: a point `x` of the closed unit disc is `η` if and only if
`x ∈ D(aₙ, |cₙ|)` for every `n`. These are the points of type (4) in Wedhorn's Example 7.57. -/
theorem eq_nestedDiscPoint_iff [IsAlgClosed K] (hempty : ∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖)
    (x : closedPolydisc 1 K) :
    x = nestedDiscPoint a ha c hc₀ hc₁ hac hcc ↔ ∀ n, x ∈ closedSubdisc (a n) (c n) := by
  refine ⟨fun h n ↦ h ▸ nestedDiscPoint_mem_closedSubdisc a ha c hc₀ hc₁ hac hcc n,
    fun hx ↦ eq_of_forall_valuation_weightedX_sub_weightedC_eq fun b ↦ ?_⟩
  -- a disc `D(aₙ, |cₙ|)` avoiding `b` makes both points take the value of `aₙ - b` on `T - b`
  obtain ⟨n, hn⟩ := hempty b
  refine ⟨a n - b, sub_ne_zero.mpr fun h ↦ ?_,
    valuation_weightedX_sub_weightedC_of_mem_closedSubdisc (hx n) hn,
    valuation_weightedX_sub_weightedC_of_mem_closedSubdisc
      (nestedDiscPoint_mem_closedSubdisc a ha c hc₀ hc₁ hac hcc n) hn⟩
  rw [h, sub_self, norm_zero] at hn
  exact (norm_nonneg _).not_gt hn

/-! ### Points without a minimum on linear polynomials -/

/-- **The points of type (4) of the closed unit disc**, over an algebraically closed complete
nonarchimedean field: a point `x` is the point attached to a decreasing sequence of discs with no
common point in `K` if and only if `b ↦ x(T - b)` attains no minimum. -/
theorem exists_eq_nestedDiscPoint_iff [IsAlgClosed K] (x : closedPolydisc 1 K) :
    (∃ (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) (c : ℕ → K) (hc₀ : ∀ n, c n ≠ 0)
      (hc₁ : ∀ n, ‖c n‖ ≤ 1) (hac : ∀ n, ‖a (n + 1) - a n‖ ≤ ‖c n‖)
      (hcc : ∀ n, ‖c (n + 1)‖ ≤ ‖c n‖),
      (∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) ∧ x = nestedDiscPoint a ha c hc₀ hc₁ hac hcc) ↔
    ¬ ∃ a₀ : K, ∀ b : K, x.1.toValuativeRel.vle (T - C a₀) (T - C b) := by
  refine ⟨fun ⟨a, ha, c, hc₀, hc₁, hac, hcc, hempty, hx⟩ ↦ ?_, fun hmin ↦ ?_⟩
  · subst hx
    exact not_exists_forall_nestedDiscPoint_vle ha hc₀ hc₁ hac hcc hempty
  obtain ⟨a, c, ha, hc₀, hc₁, hac, hcc, hempty, hx⟩ := exists_forall_mem_closedSubdisc hmin
  exact ⟨a, ha, c, hc₀, hc₁, hac, hcc, hempty,
    (eq_nestedDiscPoint_iff ha hc₀ hc₁ hac hcc hempty x).mpr hx⟩

end NestedDiscRecognition

end TauCeti.ValuationSpectrum
