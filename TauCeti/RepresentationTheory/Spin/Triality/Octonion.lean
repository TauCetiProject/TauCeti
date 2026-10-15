/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.TrilinearForm
public import TauCeti.Algebra.Octonion.Basic

/-!
# The type-D4 triality form as octonion multiplication

The three coordinate blocks of the type-`D₄` triality table can each be identified with the
split octonions. The identifications differ by signed coordinate permutations: these signs pin
the integral normalization of the existing triality coefficient table.

Under these identifications, the triality trilinear form is the intrinsic octonion form

`(x, y, z) ↦ Octonion.trace ((x * y) * z)`.

Thus the coordinate form is precisely octonion multiplication paired with the trace. The result
holds over any commutative ring; it needs no field or characteristic assumption.

## Main declarations

* `TauCeti.D4Tripled.blockZeroOctonionEquiv`,
  `TauCeti.D4Tripled.blockOneOctonionEquiv`, and
  `TauCeti.D4Tripled.blockTwoOctonionEquiv`: the three signed coordinate identifications with the
  split octonions.
* `TauCeti.Octonion.trialityTrilinearForm`: the trace of a triple octonion product as a
  bundled trilinear form.
* `TauCeti.D4Tripled.trialityTrilinearForm_eq_octonionBlockTrilinearForm`: the integral coordinate
  triality form equals the octonion form pulled back through the three identifications.

## References

* J. F. Adams, *Lectures on Exceptional Lie Groups*, Chapter 3.
* J. C. Baez, *The Octonions*, Bulletin of the AMS 39 (2002), Section 4.1.
-/

open Matrix
open scoped Matrix

public section

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

universe u

/-! ## Signed coordinate identifications -/

private def blockCoordinateEquiv (R : Type u) [Semiring R] (j : Fin 3) :
    (Block j → R) ≃ₗ[R] (Fin 8 → R) :=
  LinearEquiv.piCongrLeft' R (fun _ ↦ R) (blockLocalIndexEquiv j)

private def zeroCoordinatesOctonionEquiv (R : Type u) [Ring R] :
    (Fin 8 → R) ≃ₗ[R] TauCeti.Octonion R where
  toFun x := ⟨x 0, x 7, ![x 3, x 6, -x 5], ![x 4, x 1, x 2]⟩
  invFun x := ![x.a, x.w 1, x.w 2, x.v 0, x.w 0, -x.v 2, x.v 1, x.b]
  left_inv x := by
    funext i
    fin_cases i <;> simp
  right_inv x := by
    apply TauCeti.Octonion.ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp
    · funext i; fin_cases i <;> simp
  map_add' x y := by
    apply TauCeti.Octonion.ext <;> simp [add_comm]
  map_smul' r x := by
    apply TauCeti.Octonion.ext <;> simp

private def oneCoordinatesOctonionEquiv (R : Type u) [Ring R] :
    (Fin 8 → R) ≃ₗ[R] TauCeti.Octonion R where
  toFun x := ⟨x 7, x 0, ![-x 3, -x 6, x 5], ![-x 4, -x 1, -x 2]⟩
  invFun x := ![x.b, -x.w 1, -x.w 2, -x.v 0, -x.w 0, x.v 2, -x.v 1, x.a]
  left_inv x := by
    funext i
    fin_cases i <;> simp
  right_inv x := by
    apply TauCeti.Octonion.ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp
    · funext i; fin_cases i <;> simp
  map_add' x y := by
    apply TauCeti.Octonion.ext <;> simp [add_comm]
  map_smul' r x := by
    apply TauCeti.Octonion.ext <;> simp

private def twoCoordinatesOctonionEquiv (R : Type u) [Ring R] :
    (Fin 8 → R) ≃ₗ[R] TauCeti.Octonion R where
  toFun x := ⟨x 3, -x 4, ![-x 0, -x 2, x 1], ![x 7, x 5, x 6]⟩
  invFun x := ![-x.v 0, x.v 2, -x.v 1, x.a, -x.b, x.w 1, x.w 2, x.w 0]
  left_inv x := by
    funext i
    fin_cases i <;> simp
  right_inv x := by
    apply TauCeti.Octonion.ext
    · rfl
    · simp
    · funext i; fin_cases i <;> simp
    · funext i; fin_cases i <;> simp
  map_add' x y := by
    apply TauCeti.Octonion.ext <;> simp [add_comm]
  map_smul' r x := by
    apply TauCeti.Octonion.ext <;> simp

/-- The natural coordinate block, identified with the split octonions in the normalization used
by the triality coefficient table. -/
def blockZeroOctonionEquiv (R : Type u) [Ring R] :
    (Block 0 → R) ≃ₗ[R] TauCeti.Octonion R :=
  (blockCoordinateEquiv R 0).trans (zeroCoordinatesOctonionEquiv R)

/-- The odd half-spin coordinate block, identified with the split octonions in the normalization
used by the triality coefficient table. -/
def blockOneOctonionEquiv (R : Type u) [Ring R] :
    (Block 1 → R) ≃ₗ[R] TauCeti.Octonion R :=
  (blockCoordinateEquiv R 1).trans (oneCoordinatesOctonionEquiv R)

/-- The even half-spin coordinate block, identified with the split octonions in the normalization
used by the triality coefficient table. -/
def blockTwoOctonionEquiv (R : Type u) [Ring R] :
    (Block 2 → R) ≃ₗ[R] TauCeti.Octonion R :=
  (blockCoordinateEquiv R 2).trans (twoCoordinatesOctonionEquiv R)

/-- The natural block-to-octonion equivalence as a signed coordinate formula. -/
@[simp]
theorem blockZeroOctonionEquiv_apply (R : Type u) [Ring R] (x : Block 0 → R) :
    blockZeroOctonionEquiv R x =
      ⟨x ((blockLocalIndexEquiv 0).symm 0), x ((blockLocalIndexEquiv 0).symm 7),
        ![x ((blockLocalIndexEquiv 0).symm 3), x ((blockLocalIndexEquiv 0).symm 6),
          -x ((blockLocalIndexEquiv 0).symm 5)],
        ![x ((blockLocalIndexEquiv 0).symm 4), x ((blockLocalIndexEquiv 0).symm 1),
          x ((blockLocalIndexEquiv 0).symm 2)]⟩ :=
  by simp [blockZeroOctonionEquiv, blockCoordinateEquiv, zeroCoordinatesOctonionEquiv]

/-- The odd half-spin block-to-octonion equivalence as a signed coordinate formula. -/
@[simp]
theorem blockOneOctonionEquiv_apply (R : Type u) [Ring R] (x : Block 1 → R) :
    blockOneOctonionEquiv R x =
      ⟨x ((blockLocalIndexEquiv 1).symm 7), x ((blockLocalIndexEquiv 1).symm 0),
        ![-x ((blockLocalIndexEquiv 1).symm 3), -x ((blockLocalIndexEquiv 1).symm 6),
          x ((blockLocalIndexEquiv 1).symm 5)],
        ![-x ((blockLocalIndexEquiv 1).symm 4), -x ((blockLocalIndexEquiv 1).symm 1),
          -x ((blockLocalIndexEquiv 1).symm 2)]⟩ :=
  by simp [blockOneOctonionEquiv, blockCoordinateEquiv, oneCoordinatesOctonionEquiv]

/-- The even half-spin block-to-octonion equivalence as a signed coordinate formula. -/
@[simp]
theorem blockTwoOctonionEquiv_apply (R : Type u) [Ring R] (x : Block 2 → R) :
    blockTwoOctonionEquiv R x =
      ⟨x ((blockLocalIndexEquiv 2).symm 3), -x ((blockLocalIndexEquiv 2).symm 4),
        ![-x ((blockLocalIndexEquiv 2).symm 0), -x ((blockLocalIndexEquiv 2).symm 2),
          x ((blockLocalIndexEquiv 2).symm 1)],
        ![x ((blockLocalIndexEquiv 2).symm 7), x ((blockLocalIndexEquiv 2).symm 5),
          x ((blockLocalIndexEquiv 2).symm 6)]⟩ :=
  by simp [blockTwoOctonionEquiv, blockCoordinateEquiv, twoCoordinatesOctonionEquiv]

/-! ## The octonion triality form -/

/-- The octonion triality form pulled back to the natural and two half-spin coordinate blocks. -/
def octonionBlockTrilinearForm (R : Type u) [CommRing R] :
    (Block 0 → R) →ₗ[R] (Block 1 → R) →ₗ[R] (Block 2 → R) →ₗ[R] R :=
  ((TauCeti.Octonion.trialityTrilinearForm R).compl₁₂
      (blockZeroOctonionEquiv R).toLinearMap
      (blockOneOctonionEquiv R).toLinearMap).compr₂
    (LinearMap.lcomp R R (blockTwoOctonionEquiv R).toLinearMap)

/-- The pulled-back octonion form evaluates as the trace of the product of the three identified
octonions. -/
@[simp]
theorem octonionBlockTrilinearForm_apply (R : Type u) [CommRing R]
    (v₀ : Block 0 → R) (v₁ : Block 1 → R) (v₂ : Block 2 → R) :
    octonionBlockTrilinearForm R v₀ v₁ v₂ =
      TauCeti.Octonion.trace
        (blockZeroOctonionEquiv R v₀ * blockOneOctonionEquiv R v₁ *
          blockTwoOctonionEquiv R v₂) :=
  by simp [octonionBlockTrilinearForm]

private theorem trialityCoefficient_eq_octonion_int
    (a : Block 0) (b : Block 1) (c : Block 2) :
    trialityCoefficient a b c =
      octonionBlockTrilinearForm ℤ (Pi.single a 1) (Pi.single b 1) (Pi.single c 1) := by
  simp only [octonionBlockTrilinearForm_apply, blockZeroOctonionEquiv_apply,
    blockOneOctonionEquiv_apply, blockTwoOctonionEquiv_apply,
    TauCeti.Octonion.trace_apply, TauCeti.Octonion.mul_a, TauCeti.Octonion.mul_b,
    TauCeti.Octonion.mul_v, TauCeti.Octonion.mul_w,
    Matrix.vec3_dotProduct, cross_apply, Pi.single_apply, Equiv.symm_apply_eq, Fin.ext_iff,
    blockLocalIndexEquiv_apply_val, trialityCoefficient_apply]
  revert a b c
  decide +kernel

private def intCastOctonion (R : Type u) [Ring R]
    (x : TauCeti.Octonion ℤ) : TauCeti.Octonion R :=
  ⟨x.a, x.b, fun i ↦ x.v i, fun i ↦ x.w i⟩

private theorem intCastOctonion_mul (R : Type u) [CommRing R]
    (x y : TauCeti.Octonion ℤ) :
    intCastOctonion R (x * y) = intCastOctonion R x * intCastOctonion R y := by
  apply TauCeti.Octonion.ext
  · simp [intCastOctonion, TauCeti.Octonion.mul_a, Matrix.vec3_dotProduct]
  · simp [intCastOctonion, TauCeti.Octonion.mul_b, Matrix.vec3_dotProduct]
  · funext i
    fin_cases i <;>
      simp [intCastOctonion, TauCeti.Octonion.mul_v, cross_apply]
  · funext i
    fin_cases i <;>
      simp [intCastOctonion, TauCeti.Octonion.mul_w, cross_apply]

private theorem trace_intCastOctonion (R : Type u) [CommRing R]
    (x : TauCeti.Octonion ℤ) :
    TauCeti.Octonion.trace (R := R) (intCastOctonion R x) =
      (TauCeti.Octonion.trace (R := ℤ) x : R) := by
  simp [intCastOctonion, TauCeti.Octonion.trace_apply]

private theorem trialityCoefficient_eq_octonion (R : Type u) [CommRing R]
    (a : Block 0) (b : Block 1) (c : Block 2) :
    (trialityCoefficient a b c : R) =
      octonionBlockTrilinearForm R (Pi.single a 1) (Pi.single b 1) (Pi.single c 1) := by
  classical
  have hzero :
      blockZeroOctonionEquiv R (Pi.single a 1) =
        intCastOctonion R (blockZeroOctonionEquiv ℤ (Pi.single a 1)) := by
    apply TauCeti.Octonion.ext
    · simp [intCastOctonion, Pi.single_apply, Int.cast_ite]
    · simp [intCastOctonion, Pi.single_apply, Int.cast_ite]
    · funext i
      fin_cases i <;> simp [intCastOctonion, Pi.single_apply, Int.cast_ite]
    · funext i
      fin_cases i <;> simp [intCastOctonion, Pi.single_apply, Int.cast_ite]
  have hone :
      blockOneOctonionEquiv R (Pi.single b 1) =
        intCastOctonion R (blockOneOctonionEquiv ℤ (Pi.single b 1)) := by
    apply TauCeti.Octonion.ext
    · simp [intCastOctonion, Pi.single_apply, Int.cast_ite]
    · simp [intCastOctonion, Pi.single_apply, Int.cast_ite]
    · funext i
      fin_cases i <;> simp [intCastOctonion, Pi.single_apply, Int.cast_ite]
    · funext i
      fin_cases i <;> simp [intCastOctonion, Pi.single_apply, Int.cast_ite]
  have htwo :
      blockTwoOctonionEquiv R (Pi.single c 1) =
        intCastOctonion R (blockTwoOctonionEquiv ℤ (Pi.single c 1)) := by
    apply TauCeti.Octonion.ext
    · simp [intCastOctonion, Pi.single_apply, Int.cast_ite]
    · simp [intCastOctonion, Pi.single_apply, Int.cast_ite]
    · funext i
      fin_cases i <;> simp [intCastOctonion, Pi.single_apply, Int.cast_ite]
    · funext i
      fin_cases i <;> simp [intCastOctonion, Pi.single_apply, Int.cast_ite]
  have hcast :
      octonionBlockTrilinearForm R (Pi.single a 1) (Pi.single b 1) (Pi.single c 1) =
        (octonionBlockTrilinearForm ℤ (Pi.single a 1) (Pi.single b 1)
          (Pi.single c 1) : R) := by
    simp only [octonionBlockTrilinearForm_apply]
    rw [hzero, hone, htwo, ← intCastOctonion_mul R, ← intCastOctonion_mul R,
      trace_intCastOctonion R]
  rw [hcast]
  exact congrArg (fun z : ℤ ↦ (z : R)) (trialityCoefficient_eq_octonion_int a b c)

/-- The integral type-`D₄` triality form is octonion multiplication paired with the trace,
after the three signed coordinate identifications. -/
theorem trialityTrilinearForm_eq_octonionBlockTrilinearForm
    (R : Type u) [CommRing R] :
    trialityTrilinearForm R = octonionBlockTrilinearForm R := by
  apply (Pi.basisFun R (Block 0)).ext
  intro a
  apply (Pi.basisFun R (Block 1)).ext
  intro b
  apply (Pi.basisFun R (Block 2)).ext
  intro c
  rw [Pi.basisFun_apply, Pi.basisFun_apply, Pi.basisFun_apply,
    trialityTrilinearForm_single_one_single_one_single_one]
  exact trialityCoefficient_eq_octonion R a b c

end TauCeti.D4Tripled
