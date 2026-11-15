/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Sign.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# Line labels and chambers of a symplectic suspension with `b₁ = 1`

Let `φ` be an area-preserving diffeomorphism of a closed connected oriented surface `F` of genus
`g`, let `Y_φ` be its mapping torus, with `b₁(Y_φ) = 1`, and let `X = (ℝ / ℤ)_s × Y_φ` carry the
symplectic form `Ω = ds ∧ dt + ω_v`. Choose a lift `v ∈ H²(Y_φ; ℤ)` with `⟨v, [F]⟩ = 1`, pulled
back to `X`, and put `t = [ds ∧ dt]`. Their intersection numbers are those of a hyperbolic pair:

`v · v = 0`, `t · t = 0`, `v · t = t · v = 1`.

Modulo torsion the canonical class is `κ = (2g - 2) v` and the cohomology class of the
symplectic form is `[Ω] = t + L v` with `L > 0`. A Seiberg–Witten line label `e ∈ H²(X; ℤ)` is
written `e = a v + c t` modulo torsion, and `q = a + 1 - g`. The determinant line of the twisted
`Spinᶜ` structure has class `l = 2e - κ`, and the real dimension of its moduli space is
`d(e) = e · e - κ · e`. This file proves the numerical identities

`l = 2q v + 2c t` (modulo torsion),  `d(e) = 2cq`,  `l · [Ω] = 2(q + L c)`,

and that `l · [Ω]` has the sign of `c` when `c ≠ 0` and `d(e) ≥ 0`. In the Seiberg–Witten wall
coordinate `w = -2π l · [ω_g]`, where `ω_g` is a positive multiple of the self-dual harmonic form
in the class of `Ω`, this sign locates the unperturbed solutions of a nonpullback label
(`c ≠ 0`) in a definite chamber. A pullback label `p^* e_Y` has `c = 0` and so `d(e) = 0`.

Every class `x = a v + c t` (modulo torsion) also has even square `x · x = 2ac`
(`LinearMap.BilinForm.apply_self_eq_two_mul_mul_of_isOfFinAddOrder_sub`). When `v` and `t` span
`H²(X; ℤ)` modulo torsion, the intersection form of `X` is therefore even
(`LinearMap.BilinForm.even_apply_self_of_isOfFinAddOrder_span`); in particular no class has
square `-1`.

The statements are about an arbitrary `ℤ`-valued bilinear form `B` on an abelian group `H`,
playing the role of the intersection form on `H²(X; ℤ)`. Torsion is retained: the classes `e`
and `κ` are only assumed to agree with their coordinate expressions up to elements of finite
order, which every `ℤ`-valued bilinear form annihilates.

## Main results

* `TauCeti.SmoothMappingTorus.isOfFinAddOrder_two_smul_sub_sub`: `l = 2q v + 2c t` modulo
  torsion.
* `TauCeti.SmoothMappingTorus.apply_self_sub_apply_canonical_eq`: `d(e) = 2cq`.
* `TauCeti.SmoothMappingTorus.apply_two_smul_sub_add_mul_apply_eq`: `l · [Ω] = 2(q + L c)`.
* `TauCeti.SmoothMappingTorus.sign_apply_two_smul_sub_add_mul_apply`: for `c ≠ 0`,
  `d(e) ≥ 0` and `L > 0`, the sign of `l · [Ω]` is the sign of `c`.

## References

* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127–158.
-/

public section

open LinearMap (BilinForm)

namespace TauCeti

namespace SmoothMappingTorus

variable {H : Type*} [AddCommGroup H] {B : BilinForm ℤ H} {v t e κ : H} {a c g : ℤ}

/-- The determinant class `l = 2e - κ` of the label `e = a v + c t` is `2q v + 2c t` modulo
torsion, where `κ = (2g - 2) v` and `q = a + 1 - g`. -/
theorem isOfFinAddOrder_two_smul_sub_sub (he : IsOfFinAddOrder (e - (a • v + c • t)))
    (hκ : IsOfFinAddOrder (κ - (2 * g - 2) • v)) :
    IsOfFinAddOrder ((2 : ℤ) • e - κ - ((2 * (a + 1 - g)) • v + (2 * c) • t)) := by
  have h := (he.zsmul (i := 2)).add hκ.neg
  convert h using 1
  simp only [smul_sub, smul_add, smul_smul, neg_sub, add_smul, sub_smul, mul_add, mul_sub,
    mul_one]
  abel

/-- The dimension `d(e) = e · e - κ · e` of the label `e = a v + c t` is `2cq`, where
`κ = (2g - 2) v` and `q = a + 1 - g`. -/
theorem apply_self_sub_apply_canonical_eq (hv : B v v = 0) (ht : B t t = 0) (hvt : B v t = 1)
    (htv : B t v = 1) (he : IsOfFinAddOrder (e - (a • v + c • t)))
    (hκ : IsOfFinAddOrder (κ - (2 * g - 2) • v)) :
    B e e - B κ e = 2 * c * (a + 1 - g) := by
  rw [B.apply_self_eq_two_mul_mul_of_isOfFinAddOrder_sub hv ht hvt htv he,
    B.apply_eq_apply_of_isOfFinAddOrder_sub_left hκ,
    B.apply_eq_apply_of_isOfFinAddOrder_sub_right he]
  simp only [map_add, map_zsmul, LinearMap.smul_apply, smul_eq_mul, hv, hvt]
  ring

/-- The pairing of the determinant class `l = 2e - κ` with `[Ω] = t + L v` is `2(q + L c)`,
where `e = a v + c t`, `κ = (2g - 2) v` and `q = a + 1 - g`. The coefficient `L` lies in any
commutative ring, typically `ℝ`. -/
theorem apply_two_smul_sub_add_mul_apply_eq {R : Type*} [CommRing R] (hv : B v v = 0)
    (ht : B t t = 0) (hvt : B v t = 1) (htv : B t v = 1)
    (he : IsOfFinAddOrder (e - (a • v + c • t))) (hκ : IsOfFinAddOrder (κ - (2 * g - 2) • v))
    (L : R) :
    (B ((2 : ℤ) • e - κ) t : R) + L * B ((2 : ℤ) • e - κ) v = 2 * ((a + 1 - g : ℤ) + L * c) := by
  have hl := isOfFinAddOrder_two_smul_sub_sub he hκ
  rw [B.apply_eq_apply_of_isOfFinAddOrder_sub_left hl,
    B.apply_eq_apply_of_isOfFinAddOrder_sub_left hl]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hv, ht,
    hvt, htv]
  push_cast
  ring

/-- For a nonpullback label `e = a v + c t` (`c ≠ 0`) of nonnegative dimension, the pairing of
`l = 2e - κ` with `[Ω] = t + L v`, `L > 0`, has the sign of `c`. -/
theorem sign_apply_two_smul_sub_add_mul_apply {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (hv : B v v = 0) (ht : B t t = 0) (hvt : B v t = 1) (htv : B t v = 1)
    (he : IsOfFinAddOrder (e - (a • v + c • t))) (hκ : IsOfFinAddOrder (κ - (2 * g - 2) • v))
    (hc : c ≠ 0) (hd : 0 ≤ B e e - B κ e) {L : R} (hL : 0 < L) :
    SignType.sign ((B ((2 : ℤ) • e - κ) t : R) + L * B ((2 : ℤ) • e - κ) v) = SignType.sign c := by
  rw [apply_two_smul_sub_add_mul_apply_eq hv ht hvt htv he hκ]
  rw [apply_self_sub_apply_canonical_eq hv ht hvt htv he hκ] at hd
  rcases hc.lt_or_gt with hc | hc
  · have hq : a + 1 - g ≤ 0 := by nlinarith
    have hq' : ((a + 1 - g : ℤ) : R) ≤ 0 := by exact_mod_cast hq
    have hc' : (c : R) < 0 := by exact_mod_cast hc
    rw [sign_neg hc, sign_neg (by nlinarith)]
  · have hq : 0 ≤ a + 1 - g := by nlinarith
    have hq' : 0 ≤ ((a + 1 - g : ℤ) : R) := by exact_mod_cast hq
    have hc' : 0 < (c : R) := by exact_mod_cast hc
    rw [sign_pos hc, sign_pos (by nlinarith)]

end SmoothMappingTorus

end TauCeti
