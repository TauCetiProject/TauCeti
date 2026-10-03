/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Map
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Transvection

/-!
# Extension of scalars for Spin groups

Mathlib's `CliffordAlgebra.ofBaseChangeAux` is the canonical map from a Clifford algebra to the
Clifford algebra of a scalar extension; it preserves the even part and Clifford conjugation, as
recorded in `TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange`. It therefore restricts to a
homomorphism of Spin groups. For the canonical lift of an Eichler transvection, this homomorphism
sends `1 + ι w * ι u` to the lift determined by the pure tensors `1 ⊗ u` and `1 ⊗ w`.

## Main results

* `CliffordAlgebra.spinGroupBaseChange` extends a Spin element's scalars.
* `CliffordAlgebra.spinVectorAction_baseChange_tmul` computes the extended action on pure tensors.
* `CliffordAlgebra.spinToSpecialOrthogonal_baseChange` gives the commuting square with extension
  of special orthogonal automorphisms.
* `CliffordAlgebra.spinGroupBaseChange_spinTransvection` identifies the scalar extension of a
  canonical transvection lift.
* `CliffordAlgebra.spinGroupBaseChange_baseChange` identifies direct and successive scalar
  extension.
-/

public section

open scoped TensorProduct

namespace CliffordAlgebra

universe u v w x

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Invertible (2 : R)]

/-- The homomorphism of Spin groups induced by extension of scalars. -/
def spinGroupBaseChange (Q : QuadraticForm R M) :
    spinGroup Q →* spinGroup (Q.baseChange A) where
  toFun x := ⟨ofBaseChangeAux A Q x, by
    rw [spinGroup.mem_iff, pinGroup.mem_iff]
    refine ⟨⟨?_, ?_⟩, ofBaseChangeAux_mem_even (A := A) Q x.2.2⟩
    · -- `spinGroup.toUnits` leaves the Clifford value untouched, so extending the scalars of
      -- `x`'s underlying Lipschitz unit produces a Lipschitz unit with value
      -- `ofBaseChangeAux A Q x`.
      obtain ⟨y, hy⟩ : ∃ y : lipschitzGroup (Q.baseChange A),
          ((y : (CliffordAlgebra (Q.baseChange A))ˣ) : CliffordAlgebra (Q.baseChange A)) =
            ofBaseChangeAux A Q (x : CliffordAlgebra Q) :=
        ⟨lipschitzGroupBaseChange (A := A) Q
            ⟨spinGroup.toUnits x, spinGroup.units_mem_lipschitzGroup x.2⟩,
          coe_lipschitzGroupBaseChange_apply (A := A) Q _⟩
      rw [← hy]
      exact lipschitzGroup.coe_mem_iff_mem.mpr y.2
    · rw [Unitary.mem_iff]
      constructor
      · rw [← ofBaseChangeAux_star, ← map_mul, spinGroup.star_mul_self_of_mem x.2,
          map_one]
      · rw [← ofBaseChangeAux_star, ← map_mul, spinGroup.mul_star_self_of_mem x.2,
          map_one]⟩
  map_one' := Subtype.ext (map_one (ofBaseChangeAux A Q))
  map_mul' x y := Subtype.ext
    (map_mul (ofBaseChangeAux A Q) (x : CliffordAlgebra Q) (y : CliffordAlgebra Q))

/-- The Clifford value of a scalar-extended Spin element is obtained from the canonical Clifford
map. -/
@[simp]
theorem coe_spinGroupBaseChange_apply (Q : QuadraticForm R M) (x : spinGroup Q) :
    (spinGroupBaseChange (A := A) Q x : CliffordAlgebra (Q.baseChange A)) =
      ofBaseChangeAux A Q (x : CliffordAlgebra Q) :=
  (rfl)

/-- On a pure tensor, the action of a scalar-extended Spin element is the extension of the
original action. -/
@[simp]
theorem spinVectorAction_baseChange_tmul (Q : QuadraticForm R M) (x : spinGroup Q)
    (a : A) (m : M) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    spinVectorAction (Q.baseChange A) (spinGroupBaseChange (A := A) Q x) (a ⊗ₜ[R] m) =
      a ⊗ₜ[R] spinVectorAction Q x m := by
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  suffices hOne :
      spinVectorAction (Q.baseChange A) (spinGroupBaseChange (A := A) Q x) (1 ⊗ₜ[R] m) =
        1 ⊗ₜ[R] spinVectorAction Q x m by
    have ha (n : M) : a ⊗ₜ[R] n = a • (1 ⊗ₜ[R] n) := by
      simpa only [smul_eq_mul, mul_one] using
        (TensorProduct.smul_tmul' a (1 : A) n).symm
    rw [ha, map_smul, hOne, ← ha]
  apply ι_injective (Q.baseChange A)
  rw [ι_spinVectorAction_apply, coe_spinGroupBaseChange_apply,
    ← ofBaseChangeAux_ι A Q m, ← ofBaseChangeAux_star, ← map_mul, ← map_mul,
    ← ι_spinVectorAction_apply, ofBaseChangeAux_ι]

/-- Extension of scalars commutes with the Spin homomorphism to the special orthogonal group. -/
@[simp]
theorem spinToSpecialOrthogonal_baseChange [Module.Free R M] [Module.Finite R M]
    (Q : QuadraticForm R M) (x : spinGroup Q) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    TauCeti.QuadraticMap.specialOrthogonalGroupBaseChange (A := A) Q
        (spinToSpecialOrthogonal Q x) =
      spinToSpecialOrthogonal (Q.baseChange A) (spinGroupBaseChange (A := A) Q x) := by
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      rw [TauCeti.QuadraticMap.specialOrthogonalGroupBaseChange_apply_tmul,
        coe_spinToSpecialOrthogonal_apply, coe_spinToSpecialOrthogonal_apply,
        spinVectorAction_baseChange_tmul]
  | add z w hz hw => simp only [map_add, hz, hw]

section Field

variable {K : Type u} {L : Type v} {V : Type w}
variable [Field K] [Field L] [Algebra K L]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Invertible (2 : K)]
variable {Q : QuadraticForm K V} {u w : V}

/-- Extension of scalars carries the canonical Spin lift of `E_{u,w}` to the canonical lift of
`E_{1 ⊗ u,1 ⊗ w}`. -/
@[simp]
theorem spinGroupBaseChange_spinTransvection (hQ : Q.Nondegenerate) (hu : Q u = 0)
    (huw : QuadraticMap.polar Q u w = 0) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    spinGroupBaseChange (A := L) Q (spinTransvection hQ hu huw) =
      spinTransvection (QuadraticForm.Nondegenerate.baseChange hQ)
        (u := 1 ⊗ₜ[K] u) (w := 1 ⊗ₜ[K] w)
        (by simp [QuadraticForm.baseChange_tmul, hu])
        (by simp [QuadraticForm.polar_baseChange_tmul, huw]) := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  apply Subtype.ext
  rw [coe_spinGroupBaseChange_apply, coe_spinTransvection, coe_spinTransvection, map_add,
    map_one, map_mul, ofBaseChangeAux_ι, ofBaseChangeAux_ι]

end Field

section ScalarTower

variable {B : Type x} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable (Q : QuadraticForm R M)

/-- Direct and successive scalar extension of a Spin element agree after transport along the
canonical scalar-tower isometry. -/
@[simp]
theorem spinGroupBaseChange_baseChange (z : spinGroup Q) :
    letI : Invertible (2 : A) :=
      (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    (QuadraticForm.baseChangeBaseChange (A := A) (B := B) Q).toIsometry.spinGroupMap
        (spinGroupBaseChange (A := B) Q z) =
      spinGroupBaseChange (A := B) (Q.baseChange A)
        (spinGroupBaseChange (A := A) Q z) := by
  let : Invertible (2 : A) :=
    (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  apply Subtype.ext
  rw [QuadraticMap.Isometry.coe_spinGroupMap_apply,
    coe_spinGroupBaseChange_apply, coe_spinGroupBaseChange_apply,
    coe_spinGroupBaseChange_apply]
  exact ofBaseChangeAux_baseChange Q _

end ScalarTower

end CliffordAlgebra
