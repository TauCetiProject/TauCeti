/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.Algebra.DualNumber.Basic
public import TauCeti.LinearAlgebra.PerfectPairing.Basis
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
# The Frobenius trace pairing on the dual numbers

This file equips the dual numbers over a commutative semiring with the perfect symmetric
associative bilinear form obtained by taking the infinitesimal coefficient of a product, computes
its Gram matrix `!![0, 1; 1, 0]` in `TauCeti.dualNumberBasis`, and characterizes when a scalar
multiple `r • TrivSqZeroExt.sndHom` defines a perfect pairing versus a Frobenius functional.

In particular, over `ℤ` the scaled functional `2 • TrivSqZeroExt.sndHom ℤ ℤ` has Gram determinant
`-4` and is a nondegenerate Frobenius functional whose multiplication pairing is not perfect.

## Main results

* `TauCeti.dualNumberTracePairing`: the Frobenius trace pairing on the dual numbers.
* `TauCeti.dualNumberTracePairing_isPerfPair` and `TauCeti.isPerfPair_mul_compr₂_sndHom`: the trace
  pairing is perfect.
* `TauCeti.dualNumberTracePairing_isSymm`: the trace pairing is symmetric.
* `TauCeti.dualNumberTracePairing_mul_assoc`: the trace pairing is associative.
* `TauCeti.toMatrix₂_dualNumberTracePairing` and `TauCeti.toMatrix₂_mul_compr₂_smul_sndHom`: Gram
  matrices in the basis `(1, ε)`.
* `TauCeti.isPerfPair_mul_compr₂_smul_sndHom_iff` and
  `TauCeti.isFrobeniusFunctional_smul_sndHom_iff`: `r • sndHom` gives a perfect pairing iff `r` is a
  unit, and a Frobenius functional iff multiplication by `r` has trivial kernel.
* `TauCeti.isFrobeniusFunctional_two_smul_sndHom_int` and
  `TauCeti.not_isPerfPair_mul_compr₂_two_smul_sndHom_int`: over `ℤ`, `2 • sndHom` is nondegenerate
  with determinant `-4` (`TauCeti.det_toMatrix₂_mul_compr₂_two_smul_sndHom_int`) but not perfect.
-/

public section

namespace TauCeti

universe w

section CommSemiring

variable (k : Type w) [CommSemiring k]

/-- The Frobenius pairing on the dual numbers, obtained by taking the infinitesimal coefficient
of a product. -/
noncomputable def dualNumberTracePairing : LinearMap.BilinForm k (DualNumber k) :=
  (LinearMap.mul k (DualNumber k)).compr₂ (TrivSqZeroExt.sndHom k k)

/-- Evaluation of the dual-number Frobenius pairing in scalar and infinitesimal coordinates. -/
@[simp]
theorem dualNumberTracePairing_apply (x y : DualNumber k) :
    dualNumberTracePairing k x y = x.fst * y.snd + x.snd * y.fst := by
  rw [dualNumberTracePairing, LinearMap.compr₂_apply, LinearMap.mul_apply',
    TrivSqZeroExt.sndHom_apply, DualNumber.snd_mul]

/-- The Frobenius trace pairing on the dual numbers is symmetric. -/
theorem dualNumberTracePairing_isSymm : (dualNumberTracePairing k).IsSymm :=
  ⟨fun x y => by simp only [dualNumberTracePairing_apply]; ring⟩

/-- The Frobenius trace pairing on the dual numbers is perfect. -/
instance dualNumberTracePairing_isPerfPair : (dualNumberTracePairing k).IsPerfPair := by
  have hbij : Function.Bijective (dualNumberTracePairing k) := by
    constructor
    · intro x y h
      apply TrivSqZeroExt.ext
      · have he := LinearMap.congr_fun h DualNumber.eps
        simpa using he
      · have h1 := LinearMap.congr_fun h 1
        simpa using h1
    · intro f
      let d : DualNumber k := ⟨f DualNumber.eps, f 1⟩
      refine ⟨d, ?_⟩
      apply LinearMap.ext
      intro y
      calc
        dualNumberTracePairing k d y =
            y.snd * f DualNumber.eps + y.fst * f 1 := by
          rw [dualNumberTracePairing_apply]
          dsimp only [d, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk]
          ring
        _ = f (y.snd • DualNumber.eps + y.fst • (1 : DualNumber k)) := by
          rw [map_add, map_smul, map_smul]
          ring
        _ = f y := by
          congr 1
          apply TrivSqZeroExt.ext <;> simp
  refine ⟨hbij, ?_⟩
  constructor
  · intro x y h
    apply hbij.injective
    apply LinearMap.ext
    intro z
    rw [(dualNumberTracePairing_isSymm k).eq x z,
      (dualNumberTracePairing_isSymm k).eq y z]
    simpa only [LinearMap.flip_apply] using LinearMap.congr_fun h z
  · intro f
    obtain ⟨x, hx⟩ := hbij.surjective f
    refine ⟨x, LinearMap.ext fun z => ?_⟩
    simp only [LinearMap.flip_apply]
    rw [(dualNumberTracePairing_isSymm k).eq z x]
    exact LinearMap.congr_fun hx z

/-- The multiplication-projection pairing `(x, y) ↦ (x * y).snd` on the dual numbers is perfect. -/
instance isPerfPair_mul_compr₂_sndHom :
    ((LinearMap.mul k (DualNumber k)).compr₂ (TrivSqZeroExt.sndHom k k)).IsPerfPair :=
  dualNumberTracePairing_isPerfPair k

/-- The Frobenius trace pairing on the dual numbers is associative with multiplication. -/
theorem dualNumberTracePairing_mul_assoc (x y z : DualNumber k) :
    dualNumberTracePairing k (x * y) z = dualNumberTracePairing k x (y * z) := by
  rw [dualNumberTracePairing, LinearMap.compr₂_apply, LinearMap.compr₂_apply,
    LinearMap.mul_apply', LinearMap.mul_apply', mul_assoc]

/-- In the basis `(1, ε)`, the Gram matrix of a scaled infinitesimal-projection pairing
`r • sndHom` is `!![0, r; r, 0]`. -/
theorem toMatrix₂_mul_compr₂_smul_sndHom (r : k) :
    LinearMap.toMatrix₂ (dualNumberBasis k) (dualNumberBasis k)
      ((LinearMap.mul k (DualNumber k)).compr₂ (r • TrivSqZeroExt.sndHom k k)) =
      !![0, r; r, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix₂_apply]

/-- In the basis `(1, ε)`, the Gram matrix of `dualNumberTracePairing` is `!![0, 1; 1, 0]`. -/
theorem toMatrix₂_dualNumberTracePairing :
    LinearMap.toMatrix₂ (dualNumberBasis k) (dualNumberBasis k) (dualNumberTracePairing k) =
      !![0, 1; 1, 0] := by
  simpa [dualNumberTracePairing] using toMatrix₂_mul_compr₂_smul_sndHom k 1

/-- Over any commutative semiring `k`, the scaled trace `r • sndHom` makes
`(x, y) ↦ r * (x * y).snd` a perfect pairing on `DualNumber k` if and only if `r` is a unit in
`k`. -/
theorem isPerfPair_mul_compr₂_smul_sndHom_iff (r : k) :
    ((LinearMap.mul k (DualNumber k)).compr₂ (r • TrivSqZeroExt.sndHom k k)).IsPerfPair ↔
      IsUnit r := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.bijective_left.surjective (TrivSqZeroExt.sndHom k k)
    have hxε := LinearMap.congr_fun hx DualNumber.eps
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.smul_apply,
      TrivSqZeroExt.sndHom_apply, DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps,
      mul_one, mul_zero, add_zero, smul_eq_mul] at hxε
    exact IsUnit.of_mul_eq_one x.fst hxε
  · rintro ⟨u, rfl⟩
    have heq : (LinearMap.mul k (DualNumber k)).compr₂ ((u : k) • TrivSqZeroExt.sndHom k k) =
        ((dualNumberTracePairing k).toPerfPair.trans
          (DistribMulAction.toLinearEquiv k (Module.Dual k (DualNumber k)) u)).toLinearMap := by
      ext x y
      simp [dualNumberTracePairing, Units.smul_def, mul_add]
    rw [heq]
    infer_instance

/-- Over any commutative semiring `k`, the scaled trace `r • sndHom` is a Frobenius functional on
`DualNumber k` if and only if multiplication by `r` on `k` has trivial kernel. -/
theorem isFrobeniusFunctional_smul_sndHom_iff (r : k) :
    (r • TrivSqZeroExt.sndHom k k).IsFrobeniusFunctional ↔ ∀ x : k, r * x = 0 → x = 0 := by
  rw [LinearMap.isFrobeniusFunctional_iff]
  constructor
  · intro h x hrx
    have ha : TrivSqZeroExt.inl (M := k) x = 0 := h.1 (TrivSqZeroExt.inl x) fun b => by
      simp [smul_eq_mul, ← mul_assoc, hrx]
    simpa using congrArg TrivSqZeroExt.fst ha
  · intro hr
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · apply TrivSqZeroExt.ext
      · exact hr a.fst (by simpa [smul_eq_mul] using ha DualNumber.eps)
      · exact hr a.snd (by simpa [smul_eq_mul] using ha 1)
    · apply TrivSqZeroExt.ext
      · exact hr b.fst (by simpa [smul_eq_mul] using hb DualNumber.eps)
      · exact hr b.snd (by simpa [smul_eq_mul] using hb 1)

end CommSemiring

section CommRing

variable (R : Type w) [CommRing R]

/-- Over a commutative ring `R`, the Gram matrix of `r • sndHom` in `(1, ε)` has determinant
`-(r ^ 2)`. -/
theorem det_toMatrix₂_mul_compr₂_smul_sndHom (r : R) :
    (LinearMap.toMatrix₂ (dualNumberBasis R) (dualNumberBasis R)
      ((LinearMap.mul R (DualNumber R)).compr₂ (r • TrivSqZeroExt.sndHom R R))).det = -(r ^ 2) := by
  rw [toMatrix₂_mul_compr₂_smul_sndHom, Matrix.det_fin_two_of]
  ring

/-- Over `ℤ`, scaling the dual-number trace by `2` gives Gram determinant `-4` in `(1, ε)`. -/
theorem det_toMatrix₂_mul_compr₂_two_smul_sndHom_int :
    (LinearMap.toMatrix₂ (dualNumberBasis ℤ) (dualNumberBasis ℤ)
      ((LinearMap.mul ℤ (DualNumber ℤ)).compr₂ ((2 : ℤ) • TrivSqZeroExt.sndHom ℤ ℤ))).det = -4 := by
  rw [det_toMatrix₂_mul_compr₂_smul_sndHom]
  norm_num

/-- Over `ℤ`, the scaled trace `2 • sndHom` is a Frobenius functional (its bilinear form is
nondegenerate). -/
theorem isFrobeniusFunctional_two_smul_sndHom_int :
    ((2 : ℤ) • TrivSqZeroExt.sndHom ℤ ℤ).IsFrobeniusFunctional :=
  (isFrobeniusFunctional_smul_sndHom_iff ℤ 2).mpr fun _ hx =>
    (mul_eq_zero.mp hx).resolve_left (by decide)

/-- Over `ℤ`, the multiplication pairing of `2 • sndHom` is not perfect, even though `2 • sndHom`
is a Frobenius functional (`TauCeti.isFrobeniusFunctional_two_smul_sndHom_int`). -/
theorem not_isPerfPair_mul_compr₂_two_smul_sndHom_int :
    ¬ ((LinearMap.mul ℤ (DualNumber ℤ)).compr₂
      ((2 : ℤ) • TrivSqZeroExt.sndHom ℤ ℤ)).IsPerfPair := by
  intro h
  have hu := (dualNumberBasis ℤ).isUnit_det_of_isPerfPair (dualNumberBasis ℤ) _ h
  rw [det_toMatrix₂_mul_compr₂_two_smul_sndHom_int, Int.isUnit_iff] at hu
  omega

end CommRing

end TauCeti
