/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import TauCeti.NumberTheory.NewtonPolygon.Roots
public import TauCeti.RingTheory.Valuation.Denominator
public import TauCeti.RingTheory.Valuation.Discrete.Extension

/-!
# Ramification forced by the slopes of a Newton polygon

Let `v` be a real additive valuation on a field `K` and `w` a real additive valuation on an
extension field `L` restricting to `v`. If every finite slope of a polynomial `f` over `K` equals
the rational number `q`, every nonzero root `α` of `f` in `L` has valuation `w α = -q`, by
`Polynomial.addValuation_eq_neg_of_forall_mem_newtonSlopes_eq`. The denominator of `q` therefore
constrains the arithmetic of `L`:

* if `e • w` takes integer values on the nonzero elements of `L`, as for the integral
  normalisation of `L` when `e` is the ramification index, then `q.den ∣ e`;
* if `v` takes integer values on the nonzero elements of `K` and `L/K` is finite, then
  `q.den ≤ [L : K]`, the bound complementing `e ≤ [L : K]`.

When `v : Valuation K ΓK` is a rank-one discrete valuation and `w : Valuation L ΓL` extends `v`
(`v.HasExtension w`), any pure polynomial over `K` of rational slope `q` for `v.realAddVal` with a
nonzero root in `L` satisfies `q.den ∣ w.ramificationIdx K` (via the extended real additive
valuation `w.extRealAddVal K` whenever `w` is rank-one discrete, and trivially when
`w.ramificationIdx K = 0`). When in addition `L / K` is finite (`FiniteDimensional K L`) and
`[L : K] ≤ q.den`, we obtain total ramification `w.ramificationIdx K = [L : K]`.

The minimal polynomial of a nonzero algebraic element is a nonzero polynomial with that element as
a root, so the same conclusions hold when it is pure. No completeness of `K` and no hypothesis on
the residue field is used. For instance, `X ^ p - p` has the single slope `-1 / p`, so any finite
extension of `ℚ_[p]` containing a `p`-th root of `p` has ramification index divisible by `p`.

## Main results

* `Polynomial.den_dvd_of_forall_mem_newtonSlopes_eq`: the denominator of the slope of a pure
  polynomial with a nonzero root in `L` divides the ramification index.
* `Polynomial.den_le_finrank_of_forall_mem_newtonSlopes_eq`: that denominator is at most
  `[L : K]`.
* `minpoly.den_dvd_of_forall_mem_newtonSlopes_eq` and
  `minpoly.den_le_finrank_of_forall_mem_newtonSlopes_eq`: the same divisibility and degree bound for
  a pure minimal polynomial.
* `Polynomial.den_dvd_ramificationIdx_of_forall_mem_newtonSlopes_eq`,
  `Polynomial.ramificationIdx_eq_finrank_of_forall_mem_newtonSlopes_eq`,
  `minpoly.den_dvd_ramificationIdx_of_forall_mem_newtonSlopes_eq`, and
  `minpoly.ramificationIdx_eq_finrank_of_forall_mem_newtonSlopes_eq`: intrinsic versions for
  valuations extending a rank-one discrete valuation and `Valuation.ramificationIdx`.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II, §6.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
-/

public section

section AddValuation

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : AddValuation K (WithTop ℝ)}
  {w : AddValuation L (WithTop ℝ)}

namespace Polynomial

/-- A nonzero root in `L` of a polynomial over `K` all of whose finite slopes equal `q` has
valuation `-q`. -/
private theorem addValuation_eq_neg_ratCast (hw : ∀ x, w (algebraMap K L x) = v x) {f : K[X]}
    (hf : f ≠ 0) {q : ℚ} (hq : ∀ m ∈ f.newtonSlopes v, m = q) {α : L} (hα : α ≠ 0)
    (hroot : aeval α f = 0) : w α = (((-q : ℚ) : ℝ) : WithTop ℝ) := by
  rw [Rat.cast_neg]
  exact addValuation_eq_neg_of_forall_mem_newtonSlopes_eq (fun x ↦ w.top_iff.mp)
    (algebraMap K L) hw ((Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf) hq hα
    (by rwa [IsRoot, eval_map_algebraMap])

/-- **The slope denominator of a pure polynomial divides the ramification index.** Let `w` on `L`
restrict to `v` on `K`, and let `e • w` take integer values on the nonzero elements of `L`. If
every finite slope of a nonzero `f : K[X]` equals `q` and `f` has a nonzero root in `L`, then
`q.den ∣ e`. -/
theorem den_dvd_of_forall_mem_newtonSlopes_eq (hw : ∀ x, w (algebraMap K L x) = v x) {e : ℕ}
    (hL : ∀ y : L, y ≠ 0 → ∃ n : ℤ, w y = ((n / e : ℝ) : WithTop ℝ)) {f : K[X]} (hf : f ≠ 0)
    {q : ℚ} (hq : ∀ m ∈ f.newtonSlopes v, m = q) {α : L} (hα : α ≠ 0)
    (hroot : aeval α f = 0) : q.den ∣ e := by
  simpa using AddValuation.den_dvd_of_map_eq_ratCast hL
    (addValuation_eq_neg_ratCast hw hf hq hα hroot)

/-- **The slope denominator of a pure polynomial is at most the degree.** Let `w` on a finite
extension `L` restrict to a valuation `v` on `K` taking integer values on nonzero elements. If
every finite slope of a nonzero `f : K[X]` equals `q` and `f` has a nonzero root in `L`, then
`q.den ≤ [L : K]`. -/
theorem den_le_finrank_of_forall_mem_newtonSlopes_eq [FiniteDimensional K L]
    (hint : ∀ x : K, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ))
    (hw : ∀ x, w (algebraMap K L x) = v x) {f : K[X]} (hf : f ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ f.newtonSlopes v, m = q) {α : L} (hα : α ≠ 0) (hroot : aeval α f = 0) :
    q.den ≤ Module.finrank K L := by
  simpa using AddValuation.den_le_finrank_of_map_eq_ratCast hint hw
    (addValuation_eq_neg_ratCast hw hf hq hα hroot)

end Polynomial

namespace minpoly

/-- **The slope denominator of a pure minimal polynomial divides the ramification index.** Let `w`
on `L` restrict to `v` on `K`, and let `e • w` take integer values on the nonzero elements of `L`.
If `α ∈ L` is nonzero and integral over `K` and every finite slope of its minimal polynomial
equals `q`, then `q.den ∣ e`. -/
theorem den_dvd_of_forall_mem_newtonSlopes_eq (hw : ∀ x, w (algebraMap K L x) = v x) {e : ℕ}
    (hL : ∀ y : L, y ≠ 0 → ∃ n : ℤ, w y = ((n / e : ℝ) : WithTop ℝ)) {α : L} (hα : α ≠ 0)
    (hαK : IsIntegral K α) {q : ℚ} (hq : ∀ m ∈ (minpoly K α).newtonSlopes v, m = q) :
    q.den ∣ e :=
  Polynomial.den_dvd_of_forall_mem_newtonSlopes_eq hw hL (minpoly.ne_zero hαK) hq hα
    (minpoly.aeval K α)

/-- **The slope denominator of a pure minimal polynomial is at most the degree.** Let `w` on a
finite extension `L` restrict to a valuation `v` on `K` taking integer values on nonzero elements.
If `α ∈ L` is nonzero and every finite slope of its minimal polynomial equals `q`, then
`q.den ≤ [L : K]`. -/
theorem den_le_finrank_of_forall_mem_newtonSlopes_eq [FiniteDimensional K L]
    (hint : ∀ x : K, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ))
    (hw : ∀ x, w (algebraMap K L x) = v x) {α : L} (hα : α ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ (minpoly K α).newtonSlopes v, m = q) : q.den ≤ Module.finrank K L :=
  Polynomial.den_le_finrank_of_forall_mem_newtonSlopes_eq hint hw
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral α)) hq hα (minpoly.aeval K α)

end minpoly

end AddValuation

section DiscreteValuation

variable {K L ΓK ΓL : Type*} [Field K] [Field L] [Algebra K L]
  [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]

namespace Polynomial

/-- **Pure Newton slopes force ramification of discrete valuations.** Let `w` be a valuation on `L`
extending a rank-one discrete valuation `v` on `K`. If every finite slope of a nonzero `f : K[X]`
with respect to `v.realAddVal` equals `q` and `f` has a nonzero root in `L`, then
`q.den ∣ w.ramificationIdx K`. -/
theorem den_dvd_ramificationIdx_of_forall_mem_newtonSlopes_eq
    (v : Valuation K ΓK) [v.IsRankOneDiscrete] (w : Valuation L ΓL) [v.HasExtension w] {f : K[X]}
    (hf : f ≠ 0) {q : ℚ} (hq : ∀ m ∈ f.newtonSlopes v.realAddVal, m = q) {α : L} (hα : α ≠ 0)
    (hroot : aeval α f = 0) : q.den ∣ w.ramificationIdx K := by
  rcases eq_or_ne (w.ramificationIdx K) 0 with he | he
  · exact he ▸ dvd_zero _
  · have : ((w.comap (algebraMap K L)).valueGroup).IsFiniteRelIndex w.valueGroup :=
      w.ramificationIdx_ne_zero_iff.mp he
    have := Valuation.IsRankOneDiscrete.of_isFiniteRelIndex v w
    exact den_dvd_of_forall_mem_newtonSlopes_eq (Valuation.extRealAddVal_algebraMap v w)
      (fun _ hy ↦ w.exists_div_ramificationIdx_extRealAddVal hy) hf hq hα hroot

/-- **Criterion for total ramification from a pure Newton polygon.** In a finite extension `L / K`
with a valuation `w` extending a rank-one discrete valuation `v` on `K`, if a nonzero `f : K[X]` is
pure of rational slope `q` for `v.realAddVal`, has a nonzero root in `L`, and satisfies
`[L : K] ≤ q.den`, then `w.ramificationIdx K = [L : K]`. -/
theorem ramificationIdx_eq_finrank_of_forall_mem_newtonSlopes_eq [FiniteDimensional K L]
    (v : Valuation K ΓK) [v.IsRankOneDiscrete] (w : Valuation L ΓL) [v.HasExtension w]
    {f : K[X]} (hf : f ≠ 0) {q : ℚ} (hq : ∀ m ∈ f.newtonSlopes v.realAddVal, m = q)
    {α : L} (hα : α ≠ 0) (hroot : aeval α f = 0) (hdeg : Module.finrank K L ≤ q.den) :
    w.ramificationIdx K = Module.finrank K L :=
  Nat.le_antisymm w.ramificationIdx_le_finrank
    (hdeg.trans (Nat.le_of_dvd w.ramificationIdx_pos
      (den_dvd_ramificationIdx_of_forall_mem_newtonSlopes_eq v w hf hq hα hroot)))

end Polynomial

namespace minpoly

/-- For a valuation `w` on `L` extending a rank-one discrete valuation `v` on `K`, if `α ∈ L` is
nonzero and integral over `K` and every finite slope of `minpoly K α` for `v.realAddVal` equals
`q`, then `q.den ∣ w.ramificationIdx K`. -/
theorem den_dvd_ramificationIdx_of_forall_mem_newtonSlopes_eq
    (v : Valuation K ΓK) [v.IsRankOneDiscrete] (w : Valuation L ΓL) [v.HasExtension w] {α : L}
    (hα : α ≠ 0) (hαK : IsIntegral K α) {q : ℚ}
    (hq : ∀ m ∈ (minpoly K α).newtonSlopes v.realAddVal, m = q) :
    q.den ∣ w.ramificationIdx K :=
  Polynomial.den_dvd_ramificationIdx_of_forall_mem_newtonSlopes_eq v w (minpoly.ne_zero hαK) hq hα
    (minpoly.aeval K α)

/-- In a finite extension `L / K` with `w` extending a rank-one discrete valuation `v` on `K`, if
`α ∈ L` is nonzero and `minpoly K α` is pure of rational slope `q` with `[L : K] ≤ q.den`, then
`w.ramificationIdx K = [L : K]`. -/
theorem ramificationIdx_eq_finrank_of_forall_mem_newtonSlopes_eq [FiniteDimensional K L]
    (v : Valuation K ΓK) [v.IsRankOneDiscrete] (w : Valuation L ΓL) [v.HasExtension w]
    {α : L} (hα : α ≠ 0) {q : ℚ}
    (hq : ∀ m ∈ (minpoly K α).newtonSlopes v.realAddVal, m = q)
    (hdeg : Module.finrank K L ≤ q.den) :
    w.ramificationIdx K = Module.finrank K L :=
  Polynomial.ramificationIdx_eq_finrank_of_forall_mem_newtonSlopes_eq v w
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral α)) hq hα (minpoly.aeval K α) hdeg

end minpoly

end DiscreteValuation

end
