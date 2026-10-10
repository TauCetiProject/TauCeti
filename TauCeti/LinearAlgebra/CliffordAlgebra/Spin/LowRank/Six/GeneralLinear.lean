/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even
public import TauCeti.RepresentationTheory.Spin.Structure
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Center
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.GroupWithZero.Idempotent

/-!
# The even unitary group of a split six-dimensional quadratic space

A matrix-product model of the even Clifford algebra of a nondegenerate six-dimensional form
identifies its reverse-unitary group with the general linear group of either matrix factor.
Reversal exchanges the two central idempotents, so the second component of a unitary element
is determined by the inverse of its first component. This differs from dimension four, where
reversal preserves both factors and imposes determinant one in each.

The canonical polarization of the hyperbolic space `splitEvenForm K 3` supplies such a model
through `TauCeti.SpinPolarizationData.evenCliffordEquivProdMatrix`. Its matrix factors have size
four. In particular, the even unitary group of three rational hyperbolic planes is `GL₄(ℚ)`.
This file concerns the even unitary carrier, rather than identifying its Spin subgroup.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
* The half-spin matrix-product structure theorem in
  `TauCeti/RepresentationTheory/Spin/Structure.lean`.
-/

public section

namespace TauCeti

open _root_.CliffordAlgebra Module

universe u v w

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {n : Type w} [Fintype n] [DecidableEq n]

private def matrixProdReverse
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) :
    (Matrix n n K × Matrix n n K) →ₗ[K] (Matrix n n K × Matrix n n K) :=
  e.toLinearMap.comp ((reverseEven Q).comp e.symm.toLinearMap)

private theorem matrixProdReverse_apply
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) (x : Matrix n n K × Matrix n n K) :
    matrixProdReverse e x = e (reverseEven Q (e.symm x)) := (rfl)

private theorem matrixProdReverse_mul
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) (x y : Matrix n n K × Matrix n n K) :
    matrixProdReverse e (x * y) = matrixProdReverse e y * matrixProdReverse e x := by
  simp [matrixProdReverse_apply]

private theorem matrixProdReverse_involutive
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) :
    Function.Involutive (matrixProdReverse e) := by
  intro x
  simp [matrixProdReverse_apply]

private theorem matrixProdReverse_one
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) : matrixProdReverse e 1 = 1 := by
  simp [matrixProdReverse_apply]

private theorem matrixProdReverse_mem_center
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) {x : Matrix n n K × Matrix n n K}
    (hx : x ∈ Subalgebra.center K (Matrix n n K × Matrix n n K)) :
    matrixProdReverse e x ∈ Subalgebra.center K (Matrix n n K × Matrix n n K) := by
  rw [Subalgebra.mem_center_iff] at hx ⊢
  intro y
  have h := congrArg (matrixProdReverse e) (hx (matrixProdReverse e y))
  simpa [matrixProdReverse_mul, matrixProdReverse_involutive e y] using h.symm

private theorem matrixProdReverse_one_zero
    [Nonempty n] [Invertible (2 : K)] (hQ : Q.Nondegenerate) (hV : finrank K V = 6)
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) :
    matrixProdReverse e (1, 0) = (0, 1) := by
  let : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let p : Matrix n n K × Matrix n n K := (1, 0)
  have hp : p ∈ Subalgebra.center K (Matrix n n K × Matrix n n K) := by
    simp [p, Subalgebra.mem_center_iff]
  -- The image is a central idempotent, so its matrix coordinates are scalar idempotents.
  have hrcenter := matrixProdReverse_mem_center e hp
  rw [Subalgebra.center_prod, Subalgebra.mem_prod] at hrcenter
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff K).mp hrcenter.1
  obtain ⟨b, hb⟩ := (Algebra.IsCentral.mem_center_iff K).mp hrcenter.2
  have hidem : matrixProdReverse e p * matrixProdReverse e p = matrixProdReverse e p := by
    rw [← matrixProdReverse_mul]
    simp [p]
  have haidem : a * a = a := by
    have h := congrArg (fun z : Matrix n n K × Matrix n n K => z.1) hidem
    simp only [Prod.fst_mul, ha, ← map_mul] at h
    exact (algebraMap K (Matrix n n K)).injective h
  have hbidem : b * b = b := by
    have h := congrArg (fun z : Matrix n n K × Matrix n n K => z.2) hidem
    simp only [Prod.snd_mul, hb, ← map_mul] at h
    exact (algebraMap K (Matrix n n K)).injective h
  -- Involutivity excludes zero and one; the central fixed-point theorem excludes `p` itself.
  have hane : matrixProdReverse e p ≠ 0 := by
    intro h
    have h' := congrArg (matrixProdReverse e) h
    simp [matrixProdReverse_involutive e p, p] at h'
  have hbne : matrixProdReverse e p ≠ 1 := by
    intro h
    have h' := congrArg (matrixProdReverse e) h
    simp [matrixProdReverse_involutive e p, matrixProdReverse_one, p] at h'
  have hpne : matrixProdReverse e p ≠ p := by
    intro h
    have hp' : e.symm p ∈ Subalgebra.center K (even Q) := by
      rw [← Subalgebra.map_center_eq e.symm]
      exact Subalgebra.mem_map.mpr ⟨p, hp, rfl⟩
    have hfix : reverseEven Q (e.symm p) = e.symm p := by
      apply e.injective
      simpa [matrixProdReverse_apply] using h
    obtain ⟨c, hc⟩ :=
      (CliffordAlgebra.reverseEven_eq_self_iff_of_mem_center_of_finrank_eq_six hQ hV hp').mp
        hfix
    have hpScalar : p = algebraMap K (Matrix n n K × Matrix n n K) c := by
      simpa using congrArg e hc
    have hc0 : c = 0 := by
      have h := congrArg (fun z : Matrix n n K × Matrix n n K => z.2) hpScalar
      exact (algebraMap K (Matrix n n K)).injective (by simpa [p] using h.symm)
    simp [p, hc0] at hpScalar
  -- Of the four pairs of scalar idempotents, only the complementary projector remains.
  have ha01 : a = 0 ∨ a = 1 := IsIdempotentElem.iff_eq_zero_or_one.mp haidem
  have hb01 : b = 0 ∨ b = 1 := IsIdempotentElem.iff_eq_zero_or_one.mp hbidem
  have hr : matrixProdReverse e p = (algebraMap K _ a, algebraMap K _ b) :=
    Prod.ext ha hb
  rcases ha01 with rfl | rfl <;> rcases hb01 with rfl | rfl
  · exact False.elim (hane (by simpa [Prod.ext_iff] using hr))
  · simpa [p] using hr
  · exact False.elim (hpne (by simpa [p] using hr))
  · exact False.elim (hbne (by simpa [Prod.ext_iff] using hr))

private theorem matrixProdReverse_fst_one_zero
    [Nonempty n] [Invertible (2 : K)] (hQ : Q.Nondegenerate) (hV : finrank K V = 6)
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) (a : Matrix n n K) :
    (matrixProdReverse e (a, 0)).1 = 0 := by
  have h := matrixProdReverse_mul e (a, 0) (1, 0)
  rw [matrixProdReverse_one_zero hQ hV] at h
  have h' := congrArg (fun z : Matrix n n K × Matrix n n K => z.1) h
  simpa using h'

private theorem matrixProdReverse_fst_recovery
    [Nonempty n] [Invertible (2 : K)] (hQ : Q.Nondegenerate) (hV : finrank K V = 6)
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) (x : Matrix n n K × Matrix n n K) :
    matrixProdReverse e ((matrixProdReverse e x).1, 0) = (0, x.2) := by
  have h := matrixProdReverse_mul e (matrixProdReverse e x) (1, 0)
  have hleft : matrixProdReverse e x * (1, 0) = ((matrixProdReverse e x).1, 0) := by
    apply Prod.ext <;> simp
  have hright : (0, 1) * x = (0, x.2) := by
    apply Prod.ext <;> simp
  simpa only [hleft, matrixProdReverse_one_zero hQ hV,
    matrixProdReverse_involutive e x, hright] using h

private def evenUnitaryGroupMatrixFirst
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) :
    evenUnitaryGroup Q →* Matrix.GeneralLinearGroup n K :=
  ((MonoidHom.fst _ _).comp (e.toMonoidHom.comp (evenUnitaryGroupEvenPart Q))).toHomUnits

private theorem evenUnitaryGroupMatrixFirst_coe
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) (x : evenUnitaryGroup Q) :
    (evenUnitaryGroupMatrixFirst e x : Matrix n n K) =
      (e (evenUnitaryGroupEvenPart Q x)).1 := by
  simp [evenUnitaryGroupMatrixFirst]

private theorem evenUnitaryGroupMatrixFirst_inv_coe
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) (x : evenUnitaryGroup Q) :
    (↑((evenUnitaryGroupMatrixFirst e x)⁻¹) : Matrix n n K) =
      (matrixProdReverse e (e (evenUnitaryGroupEvenPart Q x))).1 := by
  have h : evenUnitaryGroupEvenPart Q (x⁻¹) = reverseEven Q (evenUnitaryGroupEvenPart Q x) := by
    apply Subtype.ext
    simpa only [coe_evenUnitaryGroupEvenPart, coe_reverseEven_apply, Subgroup.coe_inv] using
      (evenUnitaryGroup.reverse_eq_inv Q x).symm
  rw [← map_inv, evenUnitaryGroupMatrixFirst_coe, h]
  simp only [matrixProdReverse_apply, e.symm_apply_apply]

private theorem evenUnitaryGroupMatrixFirst_injective
    [Nonempty n] [Invertible (2 : K)] (hQ : Q.Nondegenerate) (hV : finrank K V = 6)
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) :
    Function.Injective (evenUnitaryGroupMatrixFirst e) := by
  intro x y hxy
  have hfst : (e (evenUnitaryGroupEvenPart Q x)).1 =
      (e (evenUnitaryGroupEvenPart Q y)).1 := by
    simpa only [evenUnitaryGroupMatrixFirst_coe] using congrArg Units.val hxy
  have hinv :
      (matrixProdReverse e (e (evenUnitaryGroupEvenPart Q x))).1 =
        (matrixProdReverse e (e (evenUnitaryGroupEvenPart Q y))).1 := by
    simpa only [evenUnitaryGroupMatrixFirst_inv_coe] using
      congrArg (fun u : Matrix.GeneralLinearGroup n K => (↑(u⁻¹) : Matrix n n K)) hxy
  have hsnd : (e (evenUnitaryGroupEvenPart Q x)).2 =
      (e (evenUnitaryGroupEvenPart Q y)).2 := by
    have h := congrArg (fun a : Matrix n n K => (matrixProdReverse e (a, 0)).2) hinv
    simpa only [matrixProdReverse_fst_recovery hQ hV, Prod.snd] using h
  have heven := e.injective (Prod.ext hfst hsnd)
  apply Subtype.ext
  apply Units.ext
  simpa only [coe_evenUnitaryGroupEvenPart] using congrArg Subtype.val heven

private theorem matrixProdReverse_unit_pair_mul
    [Nonempty n] [Invertible (2 : K)] (hQ : Q.Nondegenerate) (hV : finrank K V = 6)
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) (u : Matrix.GeneralLinearGroup n K) :
    matrixProdReverse e (((u : Matrix n n K), 0) + matrixProdReverse e (↑(u⁻¹), 0)) *
        (((u : Matrix n n K), 0) + matrixProdReverse e (↑(u⁻¹), 0)) = 1 := by
  have hfst := matrixProdReverse_fst_one_zero hQ hV e (u : Matrix n n K)
  have hfstInv := matrixProdReverse_fst_one_zero hQ hV e (↑(u⁻¹) : Matrix n n K)
  have hmul :
      matrixProdReverse e ((u : Matrix n n K), 0) * matrixProdReverse e (↑(u⁻¹), 0) = (0, 1) := by
    rw [← matrixProdReverse_mul]
    simpa [Prod.mk_mul_mk] using matrixProdReverse_one_zero hQ hV e
  rw [map_add, matrixProdReverse_involutive e (↑(u⁻¹), 0)]
  apply Prod.ext
  · simp only [Prod.fst_mul, Prod.fst_add, hfst, hfstInv,
      zero_add, add_zero, Units.inv_mul, Prod.fst_one]
  · have h := congrArg (fun z : Matrix n n K × Matrix n n K => z.2) hmul
    simpa only [Prod.snd_mul, Prod.snd_add, Prod.snd, zero_add, add_zero, Prod.snd_one] using h

private def evenUnitaryGroupMatrixLift
    [Nonempty n] [Invertible (2 : K)] (hQ : Q.Nondegenerate) (hV : finrank K V = 6)
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) (u : Matrix.GeneralLinearGroup n K) :
    evenUnitaryGroup Q := by
  let y : even Q := e.symm (((u : Matrix n n K), 0) + matrixProdReverse e (↑(u⁻¹), 0))
  have hy : reverseEven Q y * y = 1 := by
    apply e.injective
    simpa [y, matrixProdReverse_apply] using matrixProdReverse_unit_pair_mul hQ hV e u
  have hy' : y * reverseEven Q y = 1 := by
    apply e.injective
    have h := matrixProdReverse_unit_pair_mul hQ hV e u⁻¹
    simpa [y, matrixProdReverse_apply, add_comm] using h
  let v : (CliffordAlgebra Q)ˣ :=
    { val := y
      inv := reverseEven Q y
      val_inv := congrArg Subtype.val hy'
      inv_val := congrArg Subtype.val hy }
  refine ⟨v, (evenUnitaryGroup.mem_iff_reverse_mul_self_eq_one Q).mpr ⟨y.2, ?_⟩⟩
  simpa only [v, coe_reverseEven_apply, Subalgebra.coe_mul, Subalgebra.coe_one] using
    congrArg Subtype.val hy

private theorem evenUnitaryGroupMatrixLift_evenPart
    [Nonempty n] [Invertible (2 : K)] (hQ : Q.Nondegenerate) (hV : finrank K V = 6)
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) (u : Matrix.GeneralLinearGroup n K) :
    evenUnitaryGroupEvenPart Q (evenUnitaryGroupMatrixLift hQ hV e u) =
      e.symm (((u : Matrix n n K), 0) + matrixProdReverse e (↑(u⁻¹), 0)) := by
  apply Subtype.ext
  simp [evenUnitaryGroupMatrixLift, coe_evenUnitaryGroupEvenPart]

private theorem evenUnitaryGroupMatrixFirst_surjective
    [Nonempty n] [Invertible (2 : K)] (hQ : Q.Nondegenerate) (hV : finrank K V = 6)
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K) :
    Function.Surjective (evenUnitaryGroupMatrixFirst e) := by
  intro u
  refine ⟨evenUnitaryGroupMatrixLift hQ hV e u, Units.ext ?_⟩
  simp [evenUnitaryGroupMatrixFirst_coe, evenUnitaryGroupMatrixLift_evenPart,
    matrixProdReverse_fst_one_zero hQ hV]

end TauCeti

namespace AlgEquiv

open CliffordAlgebra Module

universe u v w

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {n : Type w} [Fintype n] [DecidableEq n] [Nonempty n]
  [Invertible (2 : K)]

/-- In a matrix-product model of a nondegenerate six-dimensional even Clifford algebra,
reversal exchanges the two central idempotents. -/
@[simp]
theorem map_reverseEven_symm_one_zero_of_finrank_eq_six
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 6) :
    e (reverseEven Q (e.symm (1, 0))) = (0, 1) :=
  TauCeti.matrixProdReverse_one_zero hQ hV e

/-- Projecting to the first matrix factor identifies the reverse-unitary group of a
nondegenerate six-dimensional even Clifford algebra with the general linear group.
The matrix model is part of the data; reversal determines the inverse map uniquely. -/
noncomputable def evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 6) :
    evenUnitaryGroup Q ≃* Matrix.GeneralLinearGroup n K :=
  MulEquiv.ofBijective (TauCeti.evenUnitaryGroupMatrixFirst e)
    ⟨TauCeti.evenUnitaryGroupMatrixFirst_injective hQ hV e,
      TauCeti.evenUnitaryGroupMatrixFirst_surjective hQ hV e⟩

/-- The general linear equivalence evaluates the first factor of the chosen even-Clifford model. -/
@[simp]
theorem coe_evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix_apply
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 6) (x : evenUnitaryGroup Q) :
    (e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix hQ hV x : Matrix n n K) =
      (e (evenUnitaryGroupEvenPart Q x)).1 := by
  rw [evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix]
  exact TauCeti.evenUnitaryGroupMatrixFirst_coe e x

/-- The first matrix component of the inverse unitary transport is the given general linear
matrix. This reconstruction rule runs before simplifying the full inverse Clifford value. -/
@[simp↓]
theorem fst_evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix_symm_apply_evenPart
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 6) (u : Matrix.GeneralLinearGroup n K) :
    (e (evenUnitaryGroupEvenPart Q
      ((e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix hQ hV).symm u))).1 =
        (u : Matrix n n K) := by
  have h := coe_evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix_apply e hQ hV
    ((e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix hQ hV).symm u)
  simpa only [MulEquiv.apply_symm_apply] using h.symm

/-- The inverse general linear equivalence has even Clifford value obtained from the first
matrix and the reversed inverse matrix in the other factor. -/
@[simp]
theorem evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix_symm_apply_evenPart
    (e : even Q ≃ₐ[K] Matrix n n K × Matrix n n K)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 6) (u : Matrix.GeneralLinearGroup n K) :
    evenUnitaryGroupEvenPart Q
        ((e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix hQ hV).symm u) =
      e.symm (((u : Matrix n n K), 0) + e (reverseEven Q (e.symm (↑(u⁻¹), 0)))) := by
  have h : (e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix hQ hV).symm u =
      TauCeti.evenUnitaryGroupMatrixLift hQ hV e u := by
    apply (e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix hQ hV).injective
    apply Units.ext
    simp [TauCeti.evenUnitaryGroupMatrixLift_evenPart,
      TauCeti.matrixProdReverse_fst_one_zero hQ hV]
  rw [h, TauCeti.evenUnitaryGroupMatrixLift_evenPart, TauCeti.matrixProdReverse_apply]

end AlgEquiv

namespace TauCeti

open _root_.CliffordAlgebra Module

universe u

variable (K : Type u) [Field K]

private theorem hyperbolicSix_finrank : finrank K (SplitEvenSpace K 3) = 6 := by
  simp [SplitEvenSpace]

private theorem hyperbolicSix_W_ne_bot : (splitEvenPolarization K 3).W ≠ ⊥ :=
  Submodule.finrank_eq_zero.not.1 <| by
    rw [(splitEvenPolarization K 3).finrank_W_eq_of_finrank_eq_two_mul
      ((hyperbolicSix_finrank K).trans (by norm_num : 6 = 2 * 3))]
    norm_num

variable [NeZero (2 : K)]

/-- The invertibility witness used by the characteristic-not-two Clifford APIs. -/
local instance hyperbolicSixInvertibleTwo : Invertible (2 : K) :=
  invertibleOfNonzero (NeZero.ne (2 : K))

/-- The half-spin matrix-product model of the even Clifford algebra of three hyperbolic planes. -/
noncomputable def hyperbolicSixEvenEquivMatrixProd :
    even (splitEvenForm K 3) ≃ₐ[K]
      Matrix (Fin 4) (Fin 4) K × Matrix (Fin 4) (Fin 4) K := by
  simpa using (splitEvenPolarization K 3).evenCliffordEquivProdMatrix
    (hyperbolicSix_W_ne_bot K) ((hyperbolicSix_finrank K).trans (by norm_num : 6 = 2 * 3))

/-- The hyperbolic matrix-product model is the model of the canonical split polarization. -/
theorem hyperbolicSixEvenEquivMatrixProd_apply (x : even (splitEvenForm K 3)) :
    hyperbolicSixEvenEquivMatrixProd K x =
      (splitEvenPolarization K 3).evenCliffordEquivProdMatrix (l := 3)
        (Submodule.finrank_eq_zero.not.1 <| by
          rw [(splitEvenPolarization K 3).finrank_W_eq_of_finrank_eq_two_mul
            (by simp [SplitEvenSpace] : finrank K (SplitEvenSpace K 3) = 2 * 3)]
          norm_num)
        (by simp [SplitEvenSpace]) x := by
  simp [hyperbolicSixEvenEquivMatrixProd]

/-- The even unitary group of three hyperbolic planes is the four-dimensional general linear
group. In particular, specializing `K` to `ℚ` gives the split rational six-dimensional model. -/
noncomputable def hyperbolicSixEvenUnitaryEquivGeneralLinear :
    evenUnitaryGroup (splitEvenForm K 3) ≃* Matrix.GeneralLinearGroup (Fin 4) K :=
  (hyperbolicSixEvenEquivMatrixProd K).evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix
    (nondegenerate_splitEvenForm K 3) (hyperbolicSix_finrank K)

/-- The hyperbolic general linear equivalence is the first half-spin matrix component. -/
@[simp]
theorem coe_hyperbolicSixEvenUnitaryEquivGeneralLinear_apply
    (x : evenUnitaryGroup (splitEvenForm K 3)) :
    (hyperbolicSixEvenUnitaryEquivGeneralLinear K x : Matrix (Fin 4) (Fin 4) K) =
      (hyperbolicSixEvenEquivMatrixProd K (evenUnitaryGroupEvenPart (splitEvenForm K 3) x)).1 := by
  simp [hyperbolicSixEvenUnitaryEquivGeneralLinear]

/-- Reconstructing a hyperbolic even unitary element recovers the given first matrix component.
The rule precedes simplification of the full inverse Clifford value. -/
@[simp↓]
theorem fst_hyperbolicSixEvenUnitaryEquivGeneralLinear_symm_apply_evenPart
    (u : Matrix.GeneralLinearGroup (Fin 4) K) :
    (hyperbolicSixEvenEquivMatrixProd K
      (evenUnitaryGroupEvenPart (splitEvenForm K 3)
        ((hyperbolicSixEvenUnitaryEquivGeneralLinear K).symm u))).1 =
          (u : Matrix (Fin 4) (Fin 4) K) := by
  simp only [hyperbolicSixEvenUnitaryEquivGeneralLinear,
    AlgEquiv.fst_evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix_symm_apply_evenPart]

/-- The inverse hyperbolic equivalence reconstructs the even Clifford value using reversal
and the inverse of the given general linear matrix. -/
@[simp]
theorem hyperbolicSixEvenUnitaryEquivGeneralLinear_symm_apply_evenPart
    (u : Matrix.GeneralLinearGroup (Fin 4) K) :
    evenUnitaryGroupEvenPart (splitEvenForm K 3)
        ((hyperbolicSixEvenUnitaryEquivGeneralLinear K).symm u) =
      (hyperbolicSixEvenEquivMatrixProd K).symm
        (((u : Matrix (Fin 4) (Fin 4) K), 0) + hyperbolicSixEvenEquivMatrixProd K
          (reverseEven (splitEvenForm K 3)
            ((hyperbolicSixEvenEquivMatrixProd K).symm (↑(u⁻¹), 0)))) := by
  simp only [hyperbolicSixEvenUnitaryEquivGeneralLinear,
    AlgEquiv.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix_symm_apply_evenPart]

end TauCeti
