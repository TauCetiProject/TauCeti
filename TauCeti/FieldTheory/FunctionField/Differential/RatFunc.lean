/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.LocalOrder
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc

/-!
# The canonical Weil differential of the rational function field

The space of Weil differentials of the rational function field `k(x)` is one-dimensional over
`k(x)`, so it has no canonical element until a normalization is chosen.  Stichtenoth pins one down
by prescribing its divisor and one value of one local component: there is exactly one Weil
differential `η` of `k(x) / k` with

`(η) = -2 · P_∞` and `η_{P_∞} (x⁻¹) = -1`,

and it is the differential written `dx` in the classical language, whose local components are the
residues `η_P (z) = res_P (z dx)`.  This is Stichtenoth,
*Algebraic Function Fields and Codes*, 2nd ed., Proposition 1.7.4.

## The construction

The genus of `k(x)` is zero, so `-2 · P_∞` has degree `2g - 2` and lies in the canonical class
(`TauCeti.divisorClass_neg_two_zsmul_ofPoint_infty`); every divisor of that class is the divisor
of a nonzero Weil differential, which produces a differential `ω` with `(ω) = -2 · P_∞`.  Since
`P_∞` is rational with uniformizer `x⁻¹`, the local-order characterization of
`TauCeti.repartitionDualComponent_uniformizer_zpow_ne_zero` says that `ω_{P_∞}` does not kill
`(x⁻¹) ^ (2 - 1) = x⁻¹`, so scaling `ω` by the constant `-(ω_{P_∞} (x⁻¹))⁻¹` — which does not
move the divisor — normalizes that value to `-1`.  Uniqueness is one-dimensionality: a second such
differential is `c · η`, the divisor condition forces `div c = 0`, hence `c ∈ k` by exactness of
the constant field, and the normalization forces `c = 1`.

## The local components

The values of `η` on the powers of `x` are the residues of `xⁿ dx`, that is `-1` for `n = -1` and
`0` otherwise.  Three separate mechanisms produce them: for `n ≤ -2` the bound `(η) = -2 · P_∞`
kills `xⁿ` at `P_∞`; for `n = -1` it is the normalization; and for `n ≥ 0` it is the abstract
residue theorem `∑_P η_P (z) = 0`, whose other summands vanish because `xⁿ` is then a polynomial,
hence regular at every finite place.

## Main definitions

* `TauCeti.ratFuncWeilDifferential`: the Weil differential `η` of Stichtenoth,
  Proposition 1.7.4.

## Main results

* `TauCeti.divisorClass_neg_two_zsmul_ofPoint_infty`: `-2 · P_∞` represents the canonical class
  of `k(x)`.
* `TauCeti.weilDifferentialDivisor_ratFuncWeilDifferential` and
  `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_inv_X`: the two normalizing
  properties `(η) = -2 · P_∞` and `η_{P_∞} (x⁻¹) = -1`.
* `TauCeti.eq_ratFuncWeilDifferential`: **uniqueness** — they determine `η`.
* `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty`,
  `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_algebraMap` and
  `TauCeti.repartitionDualComponent_ratFuncWeilDifferential_zpow`: the local components of `η`
  vanish on the functions regular at a finite place and on the polynomials at infinity, and
  `η_{P_∞} (xⁿ) = -1` for `n = -1` and `0` otherwise.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.7.4.
-/

public section

open Polynomial

namespace TauCeti

open AlgebraicGeometry

variable {k : Type*} [Field k]

/-! ### The canonical class of the rational function field -/

/-- **`-2 · P_∞` represents the canonical class of `k(x)`**: it has degree `-2 = 2g - 2` for the
genus `g = 0` of the rational function field, and `ℓ(-2 · P_∞) ≥ 0 = g` is vacuous. -/
theorem divisorClass_neg_two_zsmul_ofPoint_infty (k : Type*) [Field k] :
    (Place.orderSystem (IsFunctionField.ratFunc k)).divisorClass
        ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)) =
      canonicalClass (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc := by
  rw [divisorClass_eq_canonicalClass_iff, genus_ratFunc]
  refine ⟨?_, Nat.zero_le _⟩
  rw [Divisor.degree_zsmul, Divisor.degree_ofPoint, Place.degree_infty]
  norm_num

/-! ### The differential `η` -/

/-- The normalized Weil differential of `k(x)` exists: this is the existence half of Stichtenoth,
Proposition 1.7.4, in the proof-argument-free `IsGreatest` form that
`TauCeti.ratFuncWeilDifferential` is defined from. -/
private theorem exists_isGreatest_ratFuncWeilDifferential (k : Type*) [Field k] :
    ∃ ω : Module.Dual k ↥(repartitionSpace k (RatFunc k)),
      ω ∈ weilDifferentialSpace k (RatFunc k) ∧
      IsGreatest {D : Divisor k (RatFunc k) | ω ∈ weilDifferentialFiltration D}
        ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)) ∧
      repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ = -1 := by
  obtain ⟨ω, hmem, hω0, hgreat⟩ := exists_isGreatest_of_divisorClass_eq_canonicalClass
    (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc
    (divisorClass_neg_two_zsmul_ofPoint_infty k)
  -- The order of `ω` at `P_∞` is `-2`, so `ω_{P_∞}` does not kill the uniformizer `x⁻¹`.
  have hord : weilDifferentialOrder (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc
      hmem hω0 (Place.infty k) = -2 := by
    rw [← coeff_weilDifferentialDivisor,
      (isGreatest_weilDifferentialDivisor _ _ hmem hω0).unique hgreat,
      WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self, mul_one]
  have hne := repartitionDualComponent_uniformizer_zpow_ne_zero (IsFunctionField.ratFunc k)
    isIntegrallyClosedIn_ratFunc hmem hω0 (Place.degree_infty k) Place.isUniformizer_infty
  rw [hord, show -(-2 : ℤ) - 1 = 1 by norm_num, zpow_one] at hne
  -- Scale by the constant that normalizes that value to `-1`.
  set v := repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ with hv
  refine ⟨repartitionDualMul (IsFunctionField.ratFunc k) (algebraMap k (RatFunc k) (-v⁻¹)) ω,
    repartitionDualMul_mem_weilDifferentialSpace _ _ hmem, ?_, ?_⟩
  · have hc0 : algebraMap k (RatFunc k) (-v⁻¹) ≠ 0 := by
      simpa using inv_ne_zero hne
    obtain ⟨z, hz⟩ : ∃ z : (RatFunc k)ˣ, (z : RatFunc k) = algebraMap k (RatFunc k) (-v⁻¹) :=
      ⟨Units.mk0 _ hc0, rfl⟩
    have hprincipal : Divisor.principal (IsFunctionField.ratFunc k) z = 0 :=
      Divisor.principal_eq_zero_of_isAlgebraic _ (hz ▸ isAlgebraic_algebraMap _)
    have hgreat' := isGreatest_weilDifferentialDivisor (IsFunctionField.ratFunc k)
      isIntegrallyClosedIn_ratFunc
      (repartitionDualMul_mem_weilDifferentialSpace (IsFunctionField.ratFunc k) (z : RatFunc k)
        hmem)
      (repartitionDualMul_ne_zero (IsFunctionField.ratFunc k) (Units.ne_zero z) hω0)
    rw [weilDifferentialDivisor_repartitionDualMul _ _ hmem hω0 z, hprincipal, zero_add,
      (isGreatest_weilDifferentialDivisor _ _ hmem hω0).unique hgreat, hz] at hgreat'
    exact hgreat'
  · rw [repartitionDualComponent_repartitionDualMul_algebraMap, ← hv, smul_eq_mul, neg_mul,
      inv_mul_cancel₀ hne]

/-- **The canonical Weil differential of the rational function field** (Stichtenoth,
Proposition 1.7.4): the unique Weil differential `η` of `k(x) / k` with divisor `-2 · P_∞` whose
local component at `P_∞` sends the uniformizer `x⁻¹` to `-1`.

Classically it is the differential `dx`, and its local components are the residues
`η_P (z) = res_P (z dx)`; `TauCeti.eq_ratFuncWeilDifferential` is the uniqueness that makes the
normalization meaningful. -/
noncomputable def ratFuncWeilDifferential (k : Type*) [Field k] :
    Module.Dual k ↥(repartitionSpace k (RatFunc k)) :=
  (exists_isGreatest_ratFuncWeilDifferential k).choose

/-- `η` is a Weil differential of `k(x) / k`. -/
theorem ratFuncWeilDifferential_mem (k : Type*) [Field k] :
    ratFuncWeilDifferential k ∈ weilDifferentialSpace k (RatFunc k) :=
  (exists_isGreatest_ratFuncWeilDifferential k).choose_spec.1

/-- **`(η) = -2 · P_∞`**, in the form saying that `-2 · P_∞` is the greatest divisor bounding `η`
(Stichtenoth, Proposition 1.7.4). -/
theorem isGreatest_ratFuncWeilDifferential (k : Type*) [Field k] :
    IsGreatest {D : Divisor k (RatFunc k) |
        ratFuncWeilDifferential k ∈ weilDifferentialFiltration D}
      ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)) :=
  (exists_isGreatest_ratFuncWeilDifferential k).choose_spec.2.1

/-- **The normalization `η_{P_∞} (x⁻¹) = -1`** (Stichtenoth, Proposition 1.7.4).

This is deliberately not `@[simp]`: `TauCeti.repartitionDualComponent_apply` already unfolds the
left-hand side to `η (ι_{P_∞} x⁻¹)`, so tagging it would violate simp-normal form. -/
theorem repartitionDualComponent_ratFuncWeilDifferential_inv_X (k : Type*) [Field k] :
    repartitionDualComponent (ratFuncWeilDifferential k) (Place.infty k)
      (RatFunc.X : RatFunc k)⁻¹ = -1 :=
  (exists_isGreatest_ratFuncWeilDifferential k).choose_spec.2.2

/-- `η` is nonzero: its local component at `P_∞` takes the value `-1`. -/
theorem ratFuncWeilDifferential_ne_zero (k : Type*) [Field k] :
    ratFuncWeilDifferential k ≠ 0 := by
  intro h
  have := repartitionDualComponent_ratFuncWeilDifferential_inv_X k
  rw [h, repartitionDualComponent_apply, LinearMap.zero_apply, eq_comm, neg_eq_zero] at this
  exact one_ne_zero this

/-- **The divisor of the canonical Weil differential of `k(x)` is `-2 · P_∞`** (Stichtenoth,
Proposition 1.7.4). -/
theorem weilDifferentialDivisor_ratFuncWeilDifferential (k : Type*) [Field k] :
    weilDifferentialDivisor (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc
        (ratFuncWeilDifferential_mem k) (ratFuncWeilDifferential_ne_zero k) =
      (-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k) :=
  (isGreatest_weilDifferentialDivisor _ _ (ratFuncWeilDifferential_mem k)
    (ratFuncWeilDifferential_ne_zero k)).unique (isGreatest_ratFuncWeilDifferential k)

/-- **Uniqueness in Stichtenoth, Proposition 1.7.4**: a Weil differential of `k(x)` with divisor
`-2 · P_∞` whose local component at `P_∞` sends `x⁻¹` to `-1` is `η`.

Any such differential is a function multiple `c · η`; the two divisors agree, so `div c = 0` and
`c` is a constant because `k` is the exact constant field of `k(x)`; the normalization then makes
that constant `1`. -/
theorem eq_ratFuncWeilDifferential {ω : Module.Dual k ↥(repartitionSpace k (RatFunc k))}
    (hmem : ω ∈ weilDifferentialSpace k (RatFunc k))
    (hgreat : IsGreatest {D : Divisor k (RatFunc k) | ω ∈ weilDifferentialFiltration D}
      ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)))
    (hnorm : repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ = -1) :
    ω = ratFuncWeilDifferential k := by
  obtain ⟨c, hc⟩ := exists_repartitionDualMul_eq (IsFunctionField.ratFunc k)
    isIntegrallyClosedIn_ratFunc (ratFuncWeilDifferential_mem k)
    (ratFuncWeilDifferential_ne_zero k) hmem
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h, repartitionDualComponent_apply, LinearMap.zero_apply, eq_comm, neg_eq_zero] at hnorm
    exact one_ne_zero hnorm
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hω0 (by rw [← hc, map_zero, LinearMap.zero_apply])
  obtain ⟨z, hz⟩ : ∃ z : (RatFunc k)ˣ, (z : RatFunc k) = c := ⟨Units.mk0 c hc0, rfl⟩
  -- Translating the filtration by `div z` compares the two greatest elements.
  have htrans : ∀ D : Divisor k (RatFunc k),
      D + Divisor.principal (IsFunctionField.ratFunc k) z ≤
          (-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k) ↔
        D ≤ (-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k) := by
    intro D
    rw [← mem_weilDifferentialFiltration_iff_le_of_isGreatest hgreat,
      ← mem_weilDifferentialFiltration_iff_le_of_isGreatest (isGreatest_ratFuncWeilDifferential k),
      ← hc, ← hz]
    exact repartitionDualMul_mem_weilDifferentialFiltration_iff (IsFunctionField.ratFunc k) z
  have hprincipal : Divisor.principal (IsFunctionField.ratFunc k) z = 0 := by
    have hle := (htrans _).mpr (le_refl ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)))
    have hge := (htrans ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k) -
      Divisor.principal (IsFunctionField.ratFunc k) z)).mp (by rw [sub_add_cancel])
    refine le_antisymm (by simpa using hle) (by simpa using hge)
  obtain ⟨a, ha⟩ := (Divisor.principal_eq_zero_iff (IsFunctionField.ratFunc k)
    isIntegrallyClosedIn_ratFunc z).mp hprincipal
  -- The normalization pins the constant to `1`.
  rw [hz] at ha
  rw [← hc, ← ha, repartitionDualComponent_repartitionDualMul_algebraMap,
    repartitionDualComponent_ratFuncWeilDifferential_inv_X, smul_eq_mul, mul_neg, mul_one,
    neg_inj] at hnorm
  rw [← hc, ← ha, hnorm]
  simp

/-! ### The local components of `η` -/

/-- **The local components of `η` away from infinity kill every regular function**: the divisor of
`η` is supported at `P_∞` alone, so `η_P` vanishes on the valuation ring of every other place
(Stichtenoth, Proposition 1.7.4).  Classically this says that `z dx` has no residue at a finite
place at which `z` is regular. -/
theorem repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty {P : Place k (RatFunc k)}
    (hP : P ≠ Place.infty k) {z : RatFunc k} (hz : z ∈ P.integers) :
    repartitionDualComponent (ratFuncWeilDifferential k) P z = 0 := by
  refine repartitionDualComponent_apply_eq_zero_of_le (isGreatest_ratFuncWeilDifferential k).1 P ?_
  rw [WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_of_ne hP, mul_zero, WithZero.exp_zero]
  exact P.mem_integers_iff.mp hz

/-- **A polynomial has no residue at infinity**: `η_{P_∞} (p) = 0` for every `p ∈ k[X]`.

This is the abstract residue theorem `∑_P η_P (p) = 0` of Stichtenoth, (1.45): a polynomial is
regular at every finite place, so all the other summands vanish by
`TauCeti.repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty`.  Classically it says that
`p dx` is a regular differential on the affine line, so its only residue — the one at infinity —
must vanish. -/
theorem repartitionDualComponent_ratFuncWeilDifferential_algebraMap (p : k[X]) :
    repartitionDualComponent (ratFuncWeilDifferential k) (Place.infty k)
      (algebraMap k[X] (RatFunc k) p) = 0 := by
  have hzero : ∀ P : Place k (RatFunc k), P ≠ Place.infty k →
      repartitionDualComponent (ratFuncWeilDifferential k) P
        (algebraMap k[X] (RatFunc k) p) = 0 := fun P hP ↦
    repartitionDualComponent_ratFuncWeilDifferential_of_ne_infty hP (by
      by_contra hcon
      exact hP (Place.exists_algebraMap_notMem_integers_iff_eq_infty.mp ⟨p, hcon⟩))
  have hsum := finsum_repartitionDualComponent_eq_zero (IsFunctionField.ratFunc k)
    (ratFuncWeilDifferential_mem k) (algebraMap k[X] (RatFunc k) p)
  rwa [finsum_eq_single _ (Place.infty k) hzero] at hsum

/-- **The local components of `η` on the powers of `x`** (Stichtenoth, Proposition 1.7.4): at the
place at infinity, `η_{P_∞} (xⁿ) = -1` for `n = -1` and `0` otherwise — the residues of `xⁿ dx`.

For `n ≤ -2` the bound `(η) = -2 · P_∞` applies, for `n = -1` this is the normalization, and for
`n ≥ 0` the power is a polynomial, which has no residue at infinity. -/
theorem repartitionDualComponent_ratFuncWeilDifferential_zpow (k : Type*) [Field k] (n : ℤ) :
    repartitionDualComponent (ratFuncWeilDifferential k) (Place.infty k)
      ((RatFunc.X : RatFunc k) ^ n) = if n = -1 then -1 else 0 := by
  split_ifs with hn
  · rw [hn, zpow_neg_one, repartitionDualComponent_ratFuncWeilDifferential_inv_X]
  rcases lt_or_ge n 0 with hneg | hnonneg
  · -- A pole of order at least two at `P_∞` is killed by the bound `(η) = -2 · P_∞`.
    refine repartitionDualComponent_apply_eq_zero_of_le
      (isGreatest_ratFuncWeilDifferential k).1 (Place.infty k) ?_
    rw [WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self, mul_one,
      (Place.infty k).valuation_eq_exp_neg_ord (zpow_ne_zero _ RatFunc.X_ne_zero),
      WithZero.exp_le_exp, Place.ord_zpow, Place.ord_infty, RatFunc.intDegree_X]
    omega
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hnonneg).symm⟩
    rw [zpow_natCast, ← RatFunc.algebraMap_X, ← map_pow]
    exact repartitionDualComponent_ratFuncWeilDifferential_algebraMap _

end TauCeti
