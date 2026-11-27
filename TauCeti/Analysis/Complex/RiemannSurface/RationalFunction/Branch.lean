/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Wronskian
public import TauCeti.Analysis.Complex.RiemannSurface.Branch.Values
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Divisor
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Place
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.RatFunc.NumDenom

/-!
# Ramification of a rational map of the Riemann sphere

A rational function `f = P / Q` over `ℂ`, with `P` and `Q` coprime and `Q` monic (Mathlib's
`RatFunc.num` and `RatFunc.denom`), is a meromorphic function on the Riemann sphere
(`TauCeti.RiemannSurface.MeromorphicFunction.ratFuncEquiv`), that is, a holomorphic map
`OnePoint ℂ → OnePoint ℂ`. This file computes its local multiplicities, the ramification indices of
the map, in both charts of the source, with `p = deg P` and `q = deg Q`:

* at a finite point `z` with `Q(z) ≠ 0` the map takes the value `f(z)`, and its local multiplicity
  is the multiplicity of `z` as a root of `P - f(z) Q`; it exceeds `1` exactly when `z` is a root of
  the Wronskian `P Q' - P' Q`, that is, when `f'(z) = 0`;
* at a finite pole `z`, a root of `Q`, the local multiplicity is the multiplicity of `z` as a root
  of `Q`, the pole order;
* at `∞`, if `p > q` the map takes the value `∞` with local multiplicity `p - q`; if `p < q` it
  takes the value `0` with local multiplicity `q - p`; and if `p = q` it takes the value `c`, the
  ratio of the leading coefficients, with local multiplicity `q - deg (P - c Q)`.

The affine test alone does not see ramification at `∞`: for `f = 1 / z²` the derivative has no
finite zero, yet `f` reads `s ↦ s²` in the chart `s = 1 / z` at `∞`, so `0 = f(∞)` is a branch
value.
The branch values of the rational map are therefore described by all three cases together
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.mem_branchValues_sphereRatFunc_iff`).

The computation goes through orders of meromorphic functions. At a point `x` where a nonconstant
meromorphic function `f` takes a finite value `c` the order of `f - c` is the local multiplicity of
`f` at `x`, and at a pole the order of `f` is minus the local multiplicity
(`TauCeti.RiemannSurface.MeromorphicFunction.order_sub_algebraMap_eq_localMultiplicity` and
`TauCeti.RiemannSurface.MeromorphicFunction.order_eq_neg_localMultiplicity`). On the sphere, the
order of a rational function at a point is its order at the corresponding place of `ℂ(t)`, which is
read off from the multiplicities of the roots of its numerator and denominator, or at `∞` from
their degrees.

## Main definitions

* `TauCeti.RiemannSurface.FiniteHolomorphicMap.sphereRatFunc`: a nonconstant rational function as
  a finite holomorphic map of the Riemann sphere.

## Main results

* `TauCeti.RiemannSurface.MeromorphicFunction.order_ratFuncEquiv_coe` and
  `TauCeti.RiemannSurface.MeromorphicFunction.order_ratFuncEquiv_infty`: the orders of a rational
  function at the points of the sphere.
* `TauCeti.RiemannSurface.MeromorphicFunction.localMultiplicity_ratFuncEquiv_coe` and
  `TauCeti.RiemannSurface.MeromorphicFunction.one_lt_localMultiplicity_ratFuncEquiv_coe_iff`: at a
  finite point which is not a pole.
* `TauCeti.RiemannSurface.MeromorphicFunction.localMultiplicity_ratFuncEquiv_coe_of_isRoot`: at a
  finite pole.
* `TauCeti.RiemannSurface.MeromorphicFunction.ratFuncEquiv_apply_infty_eq_infty_iff`,
  `TauCeti.RiemannSurface.MeromorphicFunction.ratFuncEquiv_apply_infty_of_intDegree_neg` and
  `TauCeti.RiemannSurface.MeromorphicFunction.ratFuncEquiv_apply_infty_of_intDegree_eq_zero`: the
  value at `∞`.
* `MeromorphicFunction.localMultiplicity_ratFuncEquiv_infty_of_intDegree_ne_zero` and
  `MeromorphicFunction.localMultiplicity_ratFuncEquiv_infty_of_intDegree_eq_zero` (in the namespace
  `TauCeti.RiemannSurface`): the local multiplicity at `∞`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.mem_branchValues_sphereRatFunc_iff`: the branch
  values of a rational map, and
  `TauCeti.RiemannSurface.FiniteHolomorphicMap.branchValues_sphereRatFunc_inv_X_sq`: those of
  `z ↦ 1 / z²` are `0` and `∞`.

## References

* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4 (multiplicities of rational maps of the
  sphere, computed in both charts).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §2 (the local behaviour of holomorphic maps).
-/

public noncomputable section

open OnePoint Polynomial Set
open scoped Manifold

namespace TauCeti.RiemannSurface

namespace MeromorphicFunction

/-! ### Orders of rational functions on the sphere -/

section RatFunc

variable {r : RatFunc ℂ}

/-- The order of the meromorphic function of a nonzero rational function `s` at a point of the
sphere is the order of `s` at the corresponding place of `ℂ(t)`. -/
private theorem order_ratFuncEquiv_eq_ord (y : OnePoint ℂ) {s : RatFunc ℂ} (hs : s ≠ 0) :
    order y (ratFuncEquiv s) = (((place y).map ratFuncEquiv.symm).ord s : WithTop ℤ) := by
  rw [Place.ord_map, AlgEquiv.symm_symm, coe_ord_place y ((_root_.map_ne_zero _).2 hs)]

/-- A nonconstant rational function differs from every constant. -/
private theorem sub_algebraMap_ne_zero (hr : r ∉ range (algebraMap ℂ (RatFunc ℂ))) (c : ℂ) :
    r - algebraMap ℂ (RatFunc ℂ) c ≠ 0 :=
  fun h ↦ hr ⟨c, (sub_eq_zero.1 h).symm⟩

/-- **The order of a rational function at a finite point of the sphere** is the multiplicity of
the point as a root of its numerator minus its multiplicity as a root of its denominator. -/
theorem order_ratFuncEquiv_coe (a : ℂ) {s : RatFunc ℂ} (hs : s ≠ 0) :
    order (a : OnePoint ℂ) (ratFuncEquiv s) =
      (((s.num.rootMultiplicity a : ℤ) - s.denom.rootMultiplicity a : ℤ) : WithTop ℤ) := by
  classical
  rw [order_ratFuncEquiv_eq_ord _ hs, map_place_coe, Place.ord_adicOfIrreducible,
    rootMultiplicity_eq_multiplicity, rootMultiplicity_eq_multiplicity]
  simp [RatFunc.num_ne_zero hs, s.denom_ne_zero]

/-- **The order of a rational function at `∞`** is minus its degree. -/
theorem order_ratFuncEquiv_infty {s : RatFunc ℂ} (hs : s ≠ 0) :
    order (∞ : OnePoint ℂ) (ratFuncEquiv s) = ((-s.intDegree : ℤ) : WithTop ℤ) := by
  rw [order_ratFuncEquiv_eq_ord _ hs, map_place_infty, Place.ord_infty]

/-- The order of `r - c` at a finite point `a` of the sphere, for `r = P / Q` other than the
constant `c`, is the multiplicity of `a` as a root of `P - c Q` minus its multiplicity as a root
of `Q`. -/
theorem order_ratFuncEquiv_sub_algebraMap_coe (a : ℂ) {c : ℂ}
    (hrc : r - algebraMap ℂ (RatFunc ℂ) c ≠ 0) :
    order (a : OnePoint ℂ) (ratFuncEquiv r - algebraMap ℂ _ c) =
      ((((r.num - C c * r.denom).rootMultiplicity a : ℤ) - r.denom.rootMultiplicity a : ℤ) :
        WithTop ℤ) := by
  rw [← AlgEquiv.commutes ratFuncEquiv, ← map_sub, order_ratFuncEquiv_coe a hrc,
    RatFunc.algebraMap_eq_C, RatFunc.num_sub_C, RatFunc.denom_sub_C]

/-- The order of `r - c` at `∞`, for `r = P / Q` other than the constant `c`, is `deg Q` minus
`deg (P - c Q)`. -/
theorem order_ratFuncEquiv_sub_algebraMap_infty {c : ℂ}
    (hrc : r - algebraMap ℂ (RatFunc ℂ) c ≠ 0) :
    order (∞ : OnePoint ℂ) (ratFuncEquiv r - algebraMap ℂ _ c) =
      (((r.denom.natDegree : ℤ) - (r.num - C c * r.denom).natDegree : ℤ) : WithTop ℤ) := by
  rw [← AlgEquiv.commutes ratFuncEquiv, ← map_sub, order_ratFuncEquiv_infty hrc,
    RatFunc.algebraMap_eq_C, RatFunc.intDegree, RatFunc.num_sub_C, RatFunc.denom_sub_C, neg_sub]

/-- The meromorphic function of a nonconstant rational function takes two distinct values. -/
theorem exists_ratFuncEquiv_apply_ne (hr : r ∉ range (algebraMap ℂ (RatFunc ℂ))) :
    ∃ x₁ x₂, ratFuncEquiv r x₁ ≠ ratFuncEquiv r x₂ :=
  exists_apply_ne_of_notMem_range_algebraMap fun ⟨c, hc⟩ ↦
    hr ⟨c, ratFuncEquiv.injective (by rw [AlgEquiv.commutes, hc])⟩

/-- A constant rational function has local multiplicity `0` everywhere. -/
private theorem localMultiplicity_ratFuncEquiv_algebraMap (c : ℂ) (x : OnePoint ℂ) :
    localMultiplicity (ratFuncEquiv (algebraMap ℂ (RatFunc ℂ) c)) x = 0 := by
  rw [AlgEquiv.commutes, coe_algebraMap, localMultiplicity_const]

/-! #### Finite points -/

/-- **The poles of a rational function** at finite points are the roots of its denominator. -/
theorem ratFuncEquiv_apply_coe_eq_infty_iff {z : ℂ} :
    ratFuncEquiv r z = ∞ ↔ r.denom.IsRoot z := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  rw [← order_neg_iff, order_ratFuncEquiv_eq_ord _ hr, map_place_coe, WithTop.coe_lt_zero,
    Place.ord_adicOfIrreducible_neg_iff, dvd_iff_isRoot]

/-- **Local multiplicity at a finite point which is not a pole.** If `z` is not a root of the
denominator `Q` of `r = P / Q`, the local multiplicity of `r` at `z` is the multiplicity of `z` as a
root of `P - r(z) Q`. -/
theorem localMultiplicity_ratFuncEquiv_coe {z : ℂ} (hz : ¬r.denom.IsRoot z) :
    localMultiplicity (ratFuncEquiv r) z =
      (r.num - C (r.eval (RingHom.id ℂ) z) * r.denom).rootMultiplicity z := by
  set c := r.eval (RingHom.id ℂ) z
  by_cases hr : r ∈ range (algebraMap ℂ (RatFunc ℂ))
  · obtain ⟨a, rfl⟩ := hr
    rw [localMultiplicity_ratFuncEquiv_algebraMap]
    simp [c, RatFunc.algebraMap_eq_C]
  have h := order_sub_algebraMap_eq_localMultiplicity (exists_ratFuncEquiv_apply_ne hr)
    (ratFuncEquiv_apply_coe r hz)
  rw [order_ratFuncEquiv_sub_algebraMap_coe z (sub_algebraMap_ne_zero hr c),
    rootMultiplicity_eq_zero hz, Nat.cast_zero, sub_zero] at h
  exact_mod_cast h.symm

/-- **Ramification at a finite point which is not a pole.** A nonconstant rational function
`r = P / Q` has local multiplicity greater than `1` at a point `z` with `Q(z) ≠ 0` exactly when `z`
is a root of the Wronskian `P Q' - P' Q`. Since `r' = (P' Q - P Q') / Q²`, these are the zeros of
the derivative of `r` away from its poles. -/
theorem one_lt_localMultiplicity_ratFuncEquiv_coe_iff
    (hr : r ∉ range (algebraMap ℂ (RatFunc ℂ))) {z : ℂ} (hz : ¬r.denom.IsRoot z) :
    1 < localMultiplicity (ratFuncEquiv r) z ↔ (wronskian r.num r.denom).IsRoot z := by
  have hc : r.eval (RingHom.id ℂ) z * r.denom.eval z = r.num.eval z := by
    rw [RatFunc.eval_id_eq_div, div_mul_cancel₀ _ hz]
  set c := r.eval (RingHom.id ℂ) z
  rw [localMultiplicity_ratFuncEquiv_coe hz,
    one_lt_rootMultiplicity_iff_isRoot (RatFunc.num_sub_C_mul_denom_ne_zero
      fun h ↦ hr ⟨c, by rw [RatFunc.algebraMap_eq_C, h]⟩)]
  simp only [IsRoot.def, eval_sub, eval_mul, eval_C, derivative_sub, derivative_mul,
    derivative_C, zero_mul, zero_add, wronskian]
  rw [hc, sub_self, eq_self_iff_true, true_and]
  constructor <;> intro h
  · linear_combination (-r.denom.eval z) * h - (r.denom.derivative.eval z) * hc
  · refine (mul_right_inj' hz).1 ?_
    linear_combination (-1 : ℂ) * h - (r.denom.derivative.eval z) * hc

/-- **Local multiplicity at a finite pole.** At a root `z` of the denominator `Q` of `r`, the local
multiplicity of `r` is the multiplicity of `z` as a root of `Q`, the order of the pole. -/
theorem localMultiplicity_ratFuncEquiv_coe_of_isRoot {z : ℂ} (hz : r.denom.IsRoot z) :
    localMultiplicity (ratFuncEquiv r) z = r.denom.rootMultiplicity z := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hz
  have hr : r ∉ range (algebraMap ℂ (RatFunc ℂ)) := by
    rintro ⟨a, rfl⟩
    simp [RatFunc.algebraMap_eq_C] at hz
  -- The numerator does not vanish at a root of the coprime denominator.
  have hnum : ¬r.num.IsRoot z := fun h ↦ (irreducible_X_sub_C z).not_isUnit
    (r.isCoprime_num_denom.isUnit_of_dvd' (dvd_iff_isRoot.2 h) (dvd_iff_isRoot.2 hz))
  have h := order_eq_neg_localMultiplicity (exists_ratFuncEquiv_apply_ne hr)
    (ratFuncEquiv_apply_coe_eq_infty_iff.2 hz)
  rw [order_ratFuncEquiv_coe z hr0, rootMultiplicity_eq_zero hnum, WithTop.coe_inj] at h
  omega

/-! #### The point at infinity

At `∞` the behaviour of `r = P / Q` is governed by its degree `RatFunc.intDegree r = p - q`, where
`p` and `q` are the degrees of `P` and `Q`. -/

/-- **The value at `∞` is `∞` exactly when `p > q`.** A rational function has a pole at `∞`
exactly when its numerator has larger degree than its denominator. -/
theorem ratFuncEquiv_apply_infty_eq_infty_iff : ratFuncEquiv r ∞ = ∞ ↔ 0 < r.intDegree := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  rw [← order_neg_iff, order_ratFuncEquiv_infty hr, WithTop.coe_lt_zero, neg_neg_iff_pos]

/-- **The value at `∞` when `p < q`.** A rational function whose numerator has smaller degree than
its denominator vanishes at `∞`. -/
theorem ratFuncEquiv_apply_infty_of_intDegree_neg (h : r.intDegree < 0) :
    ratFuncEquiv r ∞ = ((0 : ℂ) : OnePoint ℂ) := by
  have hr : r ≠ 0 := by
    rintro rfl
    simp at h
  rw [← order_pos_iff, order_ratFuncEquiv_infty hr, WithTop.coe_pos, neg_pos]
  exact h

/-- **The value at `∞` when `p = q`.** A rational function whose numerator and denominator have
equal degrees takes at `∞` the ratio of their leading coefficients. -/
theorem ratFuncEquiv_apply_infty_of_intDegree_eq_zero (h : r.intDegree = 0) :
    ratFuncEquiv r ∞ = ↑(r.num.leadingCoeff / r.denom.leadingCoeff) := by
  set c := r.num.leadingCoeff / r.denom.leadingCoeff
  rcases eq_or_ne (r - algebraMap ℂ (RatFunc ℂ) c) 0 with hrc | hrc
  · rw [sub_eq_zero.1 hrc, AlgEquiv.commutes, coe_algebraMap]
  -- `r - c` vanishes at `∞` and `r` is finite there, so `r` takes the value `c`.
  have hpos : 0 < order (∞ : OnePoint ℂ) (ratFuncEquiv r - algebraMap ℂ _ c) := by
    rw [← AlgEquiv.commutes ratFuncEquiv, ← map_sub, order_ratFuncEquiv_infty hrc,
      WithTop.coe_pos, neg_pos, ← Place.valuation_infty_lt_one_iff hrc]
    exact Place.valuation_infty_sub_leadingCoeff_div_lt_one h
  have hfin : ratFuncEquiv r ∞ ≠ ∞ := by
    rw [ne_eq, ratFuncEquiv_apply_infty_eq_infty_iff, h]
    exact lt_irrefl 0
  obtain ⟨d, hd⟩ := OnePoint.ne_infty_iff_exists.1 hfin
  rw [order_pos_iff, sub_apply_of_eq_coe hd.symm (congrFun (coe_algebraMap c) _)] at hpos
  rw [← hd, sub_eq_zero.1 (OnePoint.coe_injective hpos)]

/-- **Local multiplicity at `∞` when `p ≠ q`.** If the numerator and the denominator of `r` have
different degrees `p` and `q`, the local multiplicity of `r` at `∞` is `|p - q|`: the map takes
the value `∞` there when `p > q`, and the value `0` when `p < q`. -/
theorem localMultiplicity_ratFuncEquiv_infty_of_intDegree_ne_zero (h : r.intDegree ≠ 0) :
    localMultiplicity (ratFuncEquiv r) ∞ = r.intDegree.natAbs := by
  have hr : r ∉ range (algebraMap ℂ (RatFunc ℂ)) := by
    rintro ⟨a, rfl⟩
    simp [RatFunc.algebraMap_eq_C] at h
  have h0 : r ≠ 0 := fun h0 ↦ hr ⟨0, by simp [h0]⟩
  rcases h.lt_or_gt with hneg | hpos
  · have hm := order_sub_algebraMap_eq_localMultiplicity (exists_ratFuncEquiv_apply_ne hr)
      (ratFuncEquiv_apply_infty_of_intDegree_neg hneg)
    rw [map_zero, sub_zero, order_ratFuncEquiv_infty h0] at hm
    have hm' : -r.intDegree = (localMultiplicity (ratFuncEquiv r) ∞ : ℤ) := by exact_mod_cast hm
    omega
  · have hm := order_eq_neg_localMultiplicity (exists_ratFuncEquiv_apply_ne hr)
      (ratFuncEquiv_apply_infty_eq_infty_iff.2 hpos)
    rw [order_ratFuncEquiv_infty h0, WithTop.coe_inj, neg_inj] at hm
    omega

/-- **Local multiplicity at `∞` when `p = q`.** If the numerator `P` and the denominator `Q` of `r`
have equal degree `q`, and `c` is the ratio of their leading coefficients, the value of `r` at `∞`,
then the local multiplicity of `r` at `∞` is `q - deg (P - c Q)`. -/
theorem localMultiplicity_ratFuncEquiv_infty_of_intDegree_eq_zero (h : r.intDegree = 0) :
    localMultiplicity (ratFuncEquiv r) ∞ =
      r.denom.natDegree -
        (r.num - C (r.num.leadingCoeff / r.denom.leadingCoeff) * r.denom).natDegree := by
  set c := r.num.leadingCoeff / r.denom.leadingCoeff
  by_cases hr : r ∈ range (algebraMap ℂ (RatFunc ℂ))
  · obtain ⟨a, rfl⟩ := hr
    rw [localMultiplicity_ratFuncEquiv_algebraMap]
    simp [RatFunc.algebraMap_eq_C]
  have hm := order_sub_algebraMap_eq_localMultiplicity (exists_ratFuncEquiv_apply_ne hr)
    (ratFuncEquiv_apply_infty_of_intDegree_eq_zero h)
  rw [order_ratFuncEquiv_sub_algebraMap_infty (sub_algebraMap_ne_zero hr c)] at hm
  have hm' : (r.denom.natDegree : ℤ) - (r.num - C c * r.denom).natDegree =
      (localMultiplicity (ratFuncEquiv r) ∞ : ℤ) := by exact_mod_cast hm
  omega

end RatFunc

end MeromorphicFunction

/-! ### The rational map of the sphere and its branch values -/

namespace FiniteHolomorphicMap

open MeromorphicFunction

variable {r : RatFunc ℂ} (hr : r ∉ range (algebraMap ℂ (RatFunc ℂ)))

/-- A nonconstant rational function `r` as a finite holomorphic map of the Riemann sphere: the
meromorphic function `ratFuncEquiv r`, which sends the poles of `r` to `∞`. -/
def sphereRatFunc : FiniteHolomorphicMap (OnePoint ℂ) (OnePoint ℂ) :=
  .ofMDifferentiable (ratFuncEquiv r).mdifferentiable (exists_ratFuncEquiv_apply_ne hr)

@[simp]
theorem coe_sphereRatFunc : ⇑(sphereRatFunc hr) = ratFuncEquiv r :=
  coe_ofMDifferentiable _ _

/-- **The branch values of a rational map of the Riemann sphere.** A value `y` is a branch value of
a nonconstant rational function `r = P / Q` exactly when it is the value `r(z)` at a finite root `z`
of the Wronskian `P Q' - P' Q` which is not a pole, or it is `∞` and `r` has a finite pole of order
greater than `1`, or it is the value of `r` at `∞` and the local multiplicity of `r` at `∞`
(computed by `MeromorphicFunction.localMultiplicity_ratFuncEquiv_infty_of_intDegree_ne_zero` and
`MeromorphicFunction.localMultiplicity_ratFuncEquiv_infty_of_intDegree_eq_zero`)
is greater than `1`. -/
theorem mem_branchValues_sphereRatFunc_iff {y : OnePoint ℂ} :
    y ∈ (sphereRatFunc hr).branchValues ↔
      (∃ z : ℂ, ¬r.denom.IsRoot z ∧ (wronskian r.num r.denom).IsRoot z ∧
        ↑(r.eval (RingHom.id ℂ) z) = y) ∨
      (y = ∞ ∧ ∃ z : ℂ, 1 < r.denom.rootMultiplicity z) ∨
      (ratFuncEquiv r ∞ = y ∧ 1 < localMultiplicity (ratFuncEquiv r) ∞) := by
  rw [mem_branchValues_iff, coe_sphereRatFunc]
  constructor
  · rintro ⟨x, rfl, hx⟩
    induction x using OnePoint.rec with
    | infty => exact Or.inr (Or.inr ⟨rfl, hx⟩)
    | coe z =>
      by_cases hz : r.denom.IsRoot z
      · rw [localMultiplicity_ratFuncEquiv_coe_of_isRoot hz] at hx
        exact Or.inr (Or.inl ⟨ratFuncEquiv_apply_coe_eq_infty_iff.2 hz, z, hx⟩)
      · exact Or.inl ⟨z, hz, (one_lt_localMultiplicity_ratFuncEquiv_coe_iff hr hz).1 hx,
          (ratFuncEquiv_apply_coe r hz).symm⟩
  · rintro (⟨z, hz, hw, rfl⟩ | ⟨rfl, z, hz⟩ | ⟨rfl, h⟩)
    · exact ⟨z, ratFuncEquiv_apply_coe r hz,
        (one_lt_localMultiplicity_ratFuncEquiv_coe_iff hr hz).2 hw⟩
    · have hroot : r.denom.IsRoot z :=
        (rootMultiplicity_pos r.denom_ne_zero).1 (zero_lt_one.trans hz)
      exact ⟨z, ratFuncEquiv_apply_coe_eq_infty_iff.2 hroot,
        (localMultiplicity_ratFuncEquiv_coe_of_isRoot hroot).symm ▸ hz⟩
    · exact ⟨∞, rfl, h⟩

/-- The reduced numerator and denominator of `1 / z²` are `1` and `z²`. -/
private theorem num_denom_inv_X_sq :
    ((RatFunc.X : RatFunc ℂ) ^ 2)⁻¹.num = 1 ∧ ((RatFunc.X : RatFunc ℂ) ^ 2)⁻¹.denom = X ^ 2 :=
  (RatFunc.num_eq_and_denom_eq_iff_eq_div isCoprime_one_left (monic_X_pow 2)).2 (by simp)

/-- **The branch values of `z ↦ 1 / z²`** are `0` and `∞`. The derivative `-2 / z³` has no finite
zero; `∞` is a branch value because of the double pole at `0`, and `0` because the map reads
`s ↦ s²` in the chart `s = 1 / z` at `∞`, the point it sends to `0`. -/
theorem branchValues_sphereRatFunc_inv_X_sq
    (hr : ((RatFunc.X : RatFunc ℂ) ^ 2)⁻¹ ∉ range (algebraMap ℂ (RatFunc ℂ))) :
    (sphereRatFunc hr).branchValues = {((0 : ℂ) : OnePoint ℂ), ∞} := by
  have hdeg : ((RatFunc.X : RatFunc ℂ) ^ 2)⁻¹.intDegree = -2 := by
    simp [RatFunc.intDegree, num_denom_inv_X_sq]
  ext y
  rw [mem_branchValues_sphereRatFunc_iff,
    ratFuncEquiv_apply_infty_of_intDegree_neg (by rw [hdeg]; norm_num),
    localMultiplicity_ratFuncEquiv_infty_of_intDegree_ne_zero (by rw [hdeg]; norm_num), hdeg,
    num_denom_inv_X_sq.1, num_denom_inv_X_sq.2]
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (⟨z, hz, hw, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩)
    · -- The Wronskian `2 z` of `1` and `z²` vanishes only at the pole `0`.
      have hz0 : z = 0 := by simpa [wronskian] using hw
      exact absurd (by simp [hz0]) hz
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact Or.inr (Or.inr ⟨rfl, by norm_num⟩)
    · refine Or.inr (Or.inl ⟨rfl, 0, ?_⟩)
      rw [← sub_zero (X : ℂ[X]), ← C_0, rootMultiplicity_X_sub_C_pow]
      norm_num

end FiniteHolomorphicMap

end TauCeti.RiemannSurface
