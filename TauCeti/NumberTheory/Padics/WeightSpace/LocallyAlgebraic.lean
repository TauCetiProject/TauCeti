/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.Padics.WeightSpace.Basic
public import TauCeti.RingTheory.RootsOfUnity.Ultrametric
import Mathlib.Analysis.Normed.Algebra.Ultra

/-!
# Coordinates of locally algebraic weights

Put `q = p ^ k` with `k = TauCeti.padicUnitsDepth p`, so `q = p` for odd `p` and `q = 4` for
`p = 2`, and let `γ = exp q` be the topological generator of `1 + qℤ_p`. A weight `κ` of `ℤ_pˣ`
has coordinate `T_κ = κ(γ) - 1` (`TauCeti.WeightSpace.coord`). This file computes the coordinates
of the *locally algebraic* weights `x ↦ x ^ m ψ(x)`, with `m ∈ ℤ` and `ψ` of finite order, with
values in a seminormed commutative `ℚ_p`-algebra `K`, and the norms of the coordinates of
finite-order weights when `K` is a normed field.

**Algebraic part.** Coordinates of products satisfy `1 + T_{κκ'} = (1 + T_κ)(1 + T_κ')`, so the
weight `x ↦ x ^ m ψ(x)` has coordinate `exp (q m) ψ(γ) - 1`
(`TauCeti.WeightSpace.coord_inclusion_zpow_mul`). Since `γ` has infinite order while `ψ(γ)` is a
root of unity, this coordinate vanishes only if `m = 0` and `T_ψ = 0`
(`TauCeti.WeightSpace.coord_inclusion_zpow_mul_eq_zero_iff`).

**Finite part and conductor.** Because `γ ^ (p ^ j)` topologically generates `1 + q pʲ ℤ_p`, a
weight `κ` with values in a Hausdorff monoid is trivial on `1 + q pʲ ℤ_p` exactly when
`κ(γ) ^ (p ^ j) = 1` (`TauCeti.WeightSpace.unitsPrincipal_le_ker_iff`). For `j = 0` this says that
`T_κ = 0` exactly when `κ` is trivial on `1 + qℤ_p`, which covers the conductors dividing `q`
(`TauCeti.WeightSpace.coord_eq_zero_iff`). If instead `κ` has exact conductor `p ^ m` with
`m = k + j + 1`, so that it is trivial on `1 + p ^ m ℤ_p` but not on `1 + p ^ (m - 1) ℤ_p`, then
`κ(γ)` is a primitive `p ^ (j + 1)`-th root of unity
(`TauCeti.WeightSpace.isPrimitiveRoot_apply_padicUnitsGenerator`), of order `p ^ (m - 1)` for odd
`p` and `2 ^ (m - 2)` for `p = 2`. Consequently
`‖T_κ‖ ^ (pʲ (p - 1)) = p⁻¹` (`TauCeti.WeightSpace.norm_coord_pow`), that is, the coordinate has
normalised valuation `1 / (p ^ (m - 2) (p - 1))` for odd `p`, `m ≥ 2`, and `1 / 2 ^ (m - 3)` for
`p = 2`, `m ≥ 3`.

## Main results

* `TauCeti.WeightSpace.coord_inclusion_zpow_mul`: the weight `x ↦ x ^ m ψ(x)` has coordinate
  `exp (q m) ψ(γ) - 1`.
* `TauCeti.WeightSpace.coord_inclusion_zpow_mul_eq_zero_iff`: for `ψ` of finite order, that
  coordinate vanishes exactly when `m = 0` and `T_ψ = 0`.
* `TauCeti.WeightSpace.norm_coord_pow`, `TauCeti.WeightSpace.norm_coord_eq_rpow`: for exact
  conductor `p ^ (k + j + 1)`, `‖T_κ‖ = p ^ (-1 / (pʲ (p - 1)))`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3–4.
-/

public section

open NormedSpace

namespace TauCeti.WeightSpace

variable {p : ℕ} [Fact p.Prime]

section Algebraic

variable {K : Type*} [SeminormedCommRing K] [NormedAlgebra ℚ_[p] K]

/-- **The coordinate of a locally algebraic weight.** The weight `x ↦ x ^ m ψ(x)` has coordinate
`exp (q m) ψ(γ) - 1`. -/
theorem coord_inclusion_zpow_mul (m : ℤ) (ψ : WeightSpace p K) :
    (inclusion K ^ m * ψ).coord =
      algebraMap ℚ_[p] K (exp ((p : ℚ_[p]) ^ padicUnitsDepth p * m)) *
        ψ (padicUnitsGenerator p) - 1 := by
  rw [coord_def, ContinuousMonoidHom.mul_apply, Units.val_mul, ContinuousMonoidHom.zpow_apply,
    ← map_zpow, coe_inclusion_apply, padicIntAlgebraMap_apply, coe_padicUnitsGenerator_zpow]

/-- **Cancellation.** For `ψ` of finite order, the coordinate `exp (q m) ψ(γ) - 1` of the weight
`x ↦ x ^ m ψ(x)` vanishes only if `m = 0` and the coordinate of `ψ` vanishes: `exp (q m)` has
infinite order for `m ≠ 0`, while `ψ(γ)` is a root of unity. -/
theorem coord_inclusion_zpow_mul_eq_zero_iff [Nontrivial K] (m : ℤ) {ψ : WeightSpace p K}
    (hψ : IsOfFinOrder ψ) :
    (inclusion K ^ m * ψ).coord = 0 ↔ m = 0 ∧ ψ.coord = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨hm, hψ⟩ ↦ by simpa [hm] using hψ⟩
  obtain ⟨n, hn, hψn⟩ := isOfFinOrder_iff_pow_eq_one.mp hψ
  set γ := padicUnitsGenerator p
  rw [coord_def, sub_eq_zero, Units.val_eq_one, ContinuousMonoidHom.mul_apply,
    ContinuousMonoidHom.zpow_apply, ← map_zpow] at h
  -- raising to the order of `ψ` kills `ψ(γ)` and leaves `γ ^ (m n)` in the kernel of `x ↦ x`
  have hγ : inclusion K (γ ^ (m * n)) = 1 := by
    have hpow := congrArg (· ^ n) h
    simp only [mul_pow, one_pow, ← ContinuousMonoidHom.pow_apply ψ, hψn,
      ContinuousMonoidHom.one_toFun, mul_one] at hpow
    rw [zpow_mul, zpow_natCast, map_pow, hpow]
  have hγm : γ ^ (m * n) = 1 := inclusion_injective (by rw [hγ, map_one])
  have hm : m * n = 0 := by
    by_contra hmn
    exact not_isOfFinOrder_padicUnitsGenerator (isOfFinOrder_iff_zpow_eq_one.mpr ⟨_, hmn, hγm⟩)
  have hm0 : m = 0 := by simpa [hn.ne'] using hm
  subst hm0
  refine ⟨rfl, ?_⟩
  rw [coord_def, sub_eq_zero, Units.val_eq_one]
  simpa using h

end Algebraic

section Field

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]

/-- **The coordinate of a weight of exact conductor `p ^ (k + j + 1)`**, where `q = p ^ k`:
`‖T_κ‖ ^ (pʲ (p - 1)) = p⁻¹`. Equivalently `T_κ` has normalised valuation `1 / (pʲ (p - 1))`,
which is `1 / (p ^ (m - 2) (p - 1))` for odd `p` and `1 / 2 ^ (m - 3)` for `p = 2`, in terms of
the exponent `m = k + j + 1` of the conductor. -/
theorem norm_coord_pow (κ : WeightSpace p K) {j : ℕ}
    (h : unitsPrincipal p (padicUnitsDepth p + j + 1) ≤ κ.toMonoidHom.ker)
    (h' : ¬unitsPrincipal p (padicUnitsDepth p + j) ≤ κ.toMonoidHom.ker) :
    ‖κ.coord‖ ^ (p ^ j * (p - 1)) = (p : ℝ)⁻¹ := by
  have := IsUltrametricDist.of_normedAlgebra ℚ_[p] (L := K)
  have hζ := (κ.isPrimitiveRoot_apply_padicUnitsGenerator h h').norm'_sub_one_pow_totient_prime_pow
  rw [Nat.totient_prime_pow_succ Fact.out, ← map_natCast (algebraMap ℚ_[p] K), norm_algebraMap',
    Padic.norm_p] at hζ
  rw [coord_def, hζ]

/-- **The coordinate of a weight of exact conductor `p ^ (k + j + 1)`**, where `q = p ^ k`:
`‖T_κ‖ = p ^ (-1 / (pʲ (p - 1)))`. -/
theorem norm_coord_eq_rpow (κ : WeightSpace p K) {j : ℕ}
    (h : unitsPrincipal p (padicUnitsDepth p + j + 1) ≤ κ.toMonoidHom.ker)
    (h' : ¬unitsPrincipal p (padicUnitsDepth p + j) ≤ κ.toMonoidHom.ker) :
    ‖κ.coord‖ = (p : ℝ) ^ (-((p ^ j * (p - 1) : ℕ) : ℝ)⁻¹) := by
  have hp := (Fact.out : p.Prime)
  have hd : p ^ j * (p - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.ne_zero) (Nat.sub_ne_zero_of_lt hp.one_lt)
  rw [← Real.pow_rpow_inv_natCast (norm_nonneg κ.coord) hd, norm_coord_pow κ h h',
    Real.inv_rpow (Nat.cast_nonneg p), Real.rpow_neg (Nat.cast_nonneg p)]

end Field

end TauCeti.WeightSpace
