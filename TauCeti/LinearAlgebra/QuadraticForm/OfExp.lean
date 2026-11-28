/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Analysis.SpecialFunctions.Complex.Circle.Basic

/-!
# Quadratic maps from exponentials of a biadditive form

Let `H` be a subgroup of an abelian group `G` with `G ⧸ H` finite, `ψ` a biadditive complex form on
`G`, and `q` a function on `G ⧸ H` with `q (x) = exp (ψ (x, x))` for every representative `x`.
With `n = #(G ⧸ H)`, `n x ∈ H`, so `q (x) ^ (n²) = exp (ψ (n x, n x)) = q (0) = 1`: every value of
`q` is a root of unity, hence `e^{2πi Q (x)}` for a class `Q (x) ∈ ℚ/ℤ`
(`TauCeti.mem_range_expCircle_iff`). The function `Q` is a `ℚ/ℤ`-valued quadratic map on `G ⧸ H`
(`TauCeti.exists_quadraticMap_expCircle_eq`). For any `Q` with `e^{2πi Q} = q`, quadratic or not,
the polar form of `Q` corresponds to `exp (ψ (x, y) + ψ (y, x))` (`TauCeti.expCircle_polar`).

## Main results

* `TauCeti.exists_quadraticMap_expCircle_eq`: `q = e^{2πi Q}` for a `ℚ/ℤ`-valued quadratic map `Q`
  on `G ⧸ H`.
* `TauCeti.expCircle_polar`: `e^{2πi polar Q (x, y)} = exp (ψ (x, y) + ψ (y, x))`.
-/

public section

open Complex

namespace TauCeti

variable {G : Type*} [AddCommGroup G] {H : AddSubgroup G} {ψ : G →+ G →+ ℂ} {q : G ⧸ H → ℂ}

/-- On a finite quotient, every value of `q` is a value of `expCircle`: it is a root of unity. -/
private theorem exists_expCircle_eq [Finite (G ⧸ H)] (hq : ∀ x : G, q x = exp (ψ x x))
    (z : G ⧸ H) : ∃ r : AddCircle (1 : ℚ), expCircle r = q z := by
  induction z using QuotientAddGroup.induction_on with | H x =>
  set n : ℕ := Nat.card (G ⧸ H)
  -- `n x ∈ H`, so `q (n x) = q (0) = 1`.
  have h0 : q ((n • x : G) : G ⧸ H) = 1 := by
    rw [QuotientAddGroup.mk_nsmul, card_nsmul_eq_zero', ← QuotientAddGroup.mk_zero, hq]
    simp
  refine mem_range_expCircle_iff.mpr ⟨n * n, (Nat.mul_pos Nat.card_pos Nat.card_pos).ne', ?_⟩
  rw [← h0, hq, hq, ← exp_natCast_mul]
  congr 1
  simp only [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul]
  push_cast
  ring

/-- **The polar form of an exponent of `q`.** If `q (x) = exp (ψ (x, x))` for every representative
`x` and `e^{2πi Q} = q`, then `e^{2πi polar Q (x, y)} = exp (ψ (x, y) + ψ (y, x))`. -/
theorem expCircle_polar {Q : G ⧸ H → AddCircle (1 : ℚ)} (hq : ∀ x : G, q x = exp (ψ x x))
    (hQ : ∀ z, expCircle (Q z) = q z) (x y : G) :
    expCircle (QuadraticMap.polar Q (x : G ⧸ H) y) = exp (ψ x y + ψ y x) := by
  -- The character turns the polar form into a quotient of three values of `q`.
  have hdiv : expCircle (QuadraticMap.polar Q (x : G ⧸ H) y) =
      q ((x + y : G) : G ⧸ H) / q x / q y := by
    rw [QuadraticMap.polar, AddChar.map_sub_eq_div, AddChar.map_sub_eq_div,
      QuotientAddGroup.mk_add]
    simp only [hQ]
  simp only [hdiv, hq, ← exp_sub]
  congr 1
  simp only [map_add, AddMonoidHom.add_apply]
  ring

/-- **The exponential of a biadditive form on a finite quotient comes from a quadratic map.** If
`G ⧸ H` is finite and `q (x) = exp (ψ (x, x))` for every representative `x`, then
`q = e^{2πi Q}` for a `ℚ/ℤ`-valued quadratic map `Q` on `G ⧸ H`. -/
theorem exists_quadraticMap_expCircle_eq [Finite (G ⧸ H)] (hq : ∀ x : G, q x = exp (ψ x x)) :
    ∃ Q : QuadraticMap ℤ (G ⧸ H) (AddCircle (1 : ℚ)), ∀ z, expCircle (Q z) = q z := by
  choose Q hQ using exists_expCircle_eq hq
  have hpolar := expCircle_polar hq hQ
  refine ⟨QuadraticMap.ofPolar Q (fun a z ↦ ?_) (fun x x' y ↦ ?_) (fun a x y ↦ ?_), hQ⟩
  · induction z using QuotientAddGroup.induction_on with | H x =>
    apply expCircle_injective
    -- Put the argument in constructor form, then evaluate `expCircle ∘ Q = q` everywhere.
    rw [← QuotientAddGroup.mk_zsmul, AddChar.map_zsmul_eq_zpow]
    simp only [hQ, hq, ← exp_intCast_mul]
    congr 1
    simp only [map_zsmul, AddMonoidHom.zsmul_apply, zsmul_eq_mul, Int.cast_mul]
    ring
  · induction x using QuotientAddGroup.induction_on with | H x =>
    induction x' using QuotientAddGroup.induction_on with | H x' =>
    induction y using QuotientAddGroup.induction_on with | H y =>
    apply expCircle_injective
    rw [← QuotientAddGroup.mk_add, AddChar.map_add_eq_mul]
    simp only [hpolar, ← exp_add]
    congr 1
    simp only [map_add, AddMonoidHom.add_apply]
    ring
  · induction x using QuotientAddGroup.induction_on with | H x =>
    induction y using QuotientAddGroup.induction_on with | H y =>
    apply expCircle_injective
    rw [← QuotientAddGroup.mk_zsmul, AddChar.map_zsmul_eq_zpow]
    simp only [hpolar, ← exp_intCast_mul]
    congr 1
    simp only [map_zsmul, AddMonoidHom.zsmul_apply, zsmul_eq_mul]
    ring

end TauCeti
