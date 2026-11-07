/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.Data.ZMod.MulCastHom

/-!
# Integer matrices acting on vectors modulo a prime-power factor

If `p` is odd and prime to the determinant of an integer matrix `A`, then `2 A` is invertible
modulo `p`. Hence, in `ZMod N` with `p * M * p = N`, a vector `x` killed by `2 * (p * M)` after
applying `A` is already killed by `p * M`: both conditions say that `x` vanishes modulo `p`.

## Main results

* `Matrix.natCast_mul_smul_eq_zero_of_two_smul_mulVec_eq_zero`: this cancellation of `2 A`.
-/

public section

open ZMod

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ}

/-- **Killing the `2 A`-image.** If `p` is odd and prime to `det A`, then in `ZMod N` with
`p * M * p = N`, the vanishing of `(2 * (p * M)) • (A x)` forces `(p * M) • x = 0`: both say that
`x` vanishes modulo `p`, since `2 A` is invertible modulo `p`. -/
theorem natCast_mul_smul_eq_zero_of_two_smul_mulVec_eq_zero {N M p : ℕ}
    [NeZero (p * M)] (hpM : p * M * p = N) (hodd : Odd p) (hdet : IsCoprime A.det p)
    (x : ι → ZMod N) :
    (2 * ((p * M : ℕ) : ZMod N)) • (A.map (Int.cast : ℤ → ZMod N) *ᵥ x) = 0 →
      ((p * M : ℕ) : ZMod N) • x = 0 := by
  set φ := castHom (Dvd.intro_left (p * M) hpM) (ZMod p)
  have hker (y : ι → ZMod N) : ((p * M : ℕ) : ZMod N) • y = 0 ↔ φ ∘ y = 0 := by
    simp only [funext_iff, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp_apply,
      ZMod.natCast_mul_eq_zero_iff p hpM (NeZero.ne (p * M)), φ]
  have hAp : (A.map (Int.cast : ℤ → ZMod N)).map φ = A.map (Int.cast : ℤ → ZMod p) := by
    rw [Matrix.map_map]
    exact congrArg A.map (funext fun j ↦ map_intCast φ j)
  have hunit : IsUnit (A.map (Int.cast : ℤ → ZMod p)).det := by
    rw [show (A.map (Int.cast : ℤ → ZMod p)).det = (A.det : ZMod p) from
      ((Int.castRingHom (ZMod p)).map_det A).symm]
    obtain ⟨u, v, huv⟩ := hdet
    refine IsUnit.of_mul_eq_one_right (u : ZMod p) ?_
    simpa using congrArg (Int.cast : ℤ → ZMod p) huv
  have h2 : IsUnit (2 : ZMod p) := by
    simpa using (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.2 hodd)).isUnit
  intro h
  rw [mul_comm, mul_smul, hker, ← mulVec_smul] at h
  rw [hker]
  have h2x : φ ∘ ((2 : ZMod N) • x) = (2 : ZMod p) • (φ ∘ x) :=
    funext fun j ↦ by simp [map_ofNat]
  have h' : A.map (Int.cast : ℤ → ZMod p) *ᵥ ((2 : ZMod p) • (φ ∘ x)) = 0 := by
    ext i
    simpa only [Function.comp_apply, Pi.zero_apply, φ.map_mulVec, hAp, h2x] using congrFun h i
  have h'' := (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 hunit))
    (h'.trans (mulVec_zero _).symm)
  exact (h2.smul_left_cancel).1 (h''.trans (smul_zero _).symm)

end Matrix
