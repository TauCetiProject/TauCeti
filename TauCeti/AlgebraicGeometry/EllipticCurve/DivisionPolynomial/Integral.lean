/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# An integral-root criterion for the division polynomials `Φₙ` and `ΨSqₙ`

This file is pure polynomial algebra about Mathlib's division polynomials. Its content is that
`Φₙ − C c * ΨSqₙ` is **monic**, for every `n` and `c` — `Φₙ` is monic of degree `n²` while `ΨSqₙ`
has degree at most `n² - 1` — together with the integral-root consequence: a solution of
`c * ΨSqₙ(x) = Φₙ(x)` is a root of that monic polynomial, so it is integral over `R`, and lies in
`R` when `R` is integrally closed in the ambient algebra.

No point of a curve occurs here. The `x`-coordinates of `P` and `n • P` satisfy exactly the
identity `x' * ΨSqₙ(x) = Φₙ(x)`; combining the two is the descent step of Nagell–Lutz,
`WeierstrassCurve.isInteger_of_zsmul_isInteger` in `DivisionPolynomial/Descent.lean`.

## Main results

* `WeierstrassCurve.monic_Φ_sub_C_mul_ΨSq`: `Φₙ − C c * ΨSqₙ` is monic, unconditionally.
* `WeierstrassCurve.aeval_Φ_sub_C_mul_ΨSq_eq_zero_iff`: `x` is a root of that polynomial exactly
  when it satisfies the coordinate identity `c * ΨSqₙ(x) = Φₙ(x)`.
* `WeierstrassCurve.isInteger_of_mul_eval_ΨSq_eq_eval_Φ`: in any `R`-algebra in which `R`
  is integrally closed, if `x' * ΨSqₙ(x) = Φₙ(x)` with `x'` coming from `R`, then so does `x`.

The last needs only `IsIntegrallyClosedIn R A` — no fraction field, no domain, no unique
factorization: it is an integral-root statement, not a rational-root one. Nor is any condition on
`n` or on the characteristic required: monicity holds for every `n : ℤ`, including when the
characteristic divides `n` and when `n = 0`, because Mathlib's degree bound `natDegree_ΨSq_le` is
itself unconditional.

## Provenance

Ported from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), at
`dev/modular-curves @ 9fec8eba7652`:
`LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean`, declarations `monic_Φ_sub_smul_ΨSq` and the
integral-root half of `x_isInteger_of_nsmul_x_isInteger`.
-/

public section

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- `Φₙ − C c * ΨSqₙ` is monic, for every `n : ℤ` and every `c : R`. -/
theorem monic_Φ_sub_C_mul_ΨSq (n : ℤ) (c : R) : (W.Φ n - C c * W.ΨSq n).Monic := by
  nontriviality R
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Φ_zero]
  refine Monic.sub_of_left (W.leadingCoeff_Φ n) (degree_lt_degree ?_)
  rw [natDegree_Φ]
  exact (natDegree_C_mul_le _ _).trans_lt <|
    (W.natDegree_ΨSq_le n).trans_lt <| Nat.sub_one_lt <| by simpa using hn

section Root

variable {A : Type*} [CommRing A] [Algebra R A]

/-- `x` is a root of `Φₙ − C c * ΨSqₙ` exactly when it satisfies the coordinate identity
`c * ΨSqₙ(x) = Φₙ(x)` over `W.baseChange A`. -/
theorem aeval_Φ_sub_C_mul_ΨSq_eq_zero_iff {n : ℤ} {x : A} {c : R} :
    aeval x (W.Φ n - C c * W.ΨSq n) = 0 ↔
      algebraMap R A c * ((W.baseChange A).ΨSq n).eval x = ((W.baseChange A).Φ n).eval x := by
  rw [map_sub, sub_eq_zero, eq_comm]
  simp [baseChange, eval_map_algebraMap]

/-- **An integral-root criterion for `Φₙ` and `ΨSqₙ`.**

If `x' * ΨSqₙ(x) = Φₙ(x)` and `x'` comes from `R`, then so does `x`: it is a root of the monic
`Φₙ − C c * ΨSqₙ`, and `R` is integrally closed in `A`. -/
theorem isInteger_of_mul_eval_ΨSq_eq_eval_Φ [IsIntegrallyClosedIn R A] (n : ℤ)
    {x x' : A} (hx' : IsLocalization.IsInteger R x')
    (hid : x' * ((W.baseChange A).ΨSq n).eval x = ((W.baseChange A).Φ n).eval x) :
    IsLocalization.IsInteger R x := by
  obtain ⟨c, rfl⟩ := RingHom.mem_rangeS.mp hx'
  exact RingHom.mem_rangeS.mpr <| IsIntegrallyClosedIn.isIntegral_iff.mp
    ⟨_, W.monic_Φ_sub_C_mul_ΨSq n c, W.aeval_Φ_sub_C_mul_ΨSq_eq_zero_iff.mpr hid⟩

end Root

end WeierstrassCurve
