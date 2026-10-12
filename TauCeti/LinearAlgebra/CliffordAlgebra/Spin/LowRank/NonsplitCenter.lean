/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.NonsplitCenter
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Four

/-!
# Spin groups from quaternion models over nonsplit quaternary Clifford centers

A reversal-preserving quaternion model of the even Clifford algebra identifies the Spin group
with the unitary, equivalently norm-one, group of the quaternion algebra. In dimension four, the
field-center quaternion model supplies such an identification existentially.

## Main results

* `CliffordAlgebra.spinGroupEquivQuaternionUnitaryOverCenter` transports a chosen model to Spin.
* `CliffordAlgebra.normForm_spinGroupEquivQuaternionUnitaryOverCenter` identifies its image as
  norm-one quaternions.
* `CliffordAlgebra.exists_spinGroupEquivQuaternionUnitaryOverCenter_of_finrank_eq_four` packages
  the resulting group equivalence existentially.
-/

public section

open scoped Quaternion

namespace CliffordAlgebra

open Module

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

/-- In positive dimension at most four, a chosen quaternion model over the center identifies the
Spin group with the unitary, equivalently norm-one, group of that quaternion algebra. -/
noncomputable def spinGroupEquivQuaternionUnitaryOverCenter
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4)
    {a b : Subalgebra.center K (even Q)}
    (e : even Q ≃ₐ[Subalgebra.center K (even Q)]
      ℍ[Subalgebra.center K (even Q),a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) :
    spinGroup Q ≃* unitary ℍ[Subalgebra.center K (even Q),a,0,b] := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos hV0
  let eK : even Q ≃ₐ[K] ℍ[Subalgebra.center K (even Q),a,0,b] :=
    @AlgEquiv.restrictScalars K (Subalgebra.center K (even Q)) (even Q)
      ℍ[Subalgebra.center K (even Q),a,0,b]
      _ _ _ _ _ _ _ _ _ Subalgebra.isScalarTower_centerAlgebra (by infer_instance) e
  exact spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour
    Q hQ hV0 hV eK (fun x ↦ by
      -- Restricting scalars changes only the bundled algebra map, so its value is definitionally
      -- the value of the center-linear equivalence `e` used by the supplied involution equation.
      change e (reverseEven Q x) = star (e x)
      exact he x)

/-- The chosen Spin equivalence evaluates the center-linear quaternion model on the underlying
even Clifford element. -/
@[simp]
theorem coe_spinGroupEquivQuaternionUnitaryOverCenter_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4)
    {a b : Subalgebra.center K (even Q)}
    (e : even Q ≃ₐ[Subalgebra.center K (even Q)]
      ℍ[Subalgebra.center K (even Q),a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) (s : spinGroup Q) :
    (spinGroupEquivQuaternionUnitaryOverCenter Q hQ hV0 hV e he s :
        ℍ[Subalgebra.center K (even Q),a,0,b]) =
      e (evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q s)) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos hV0
  rw [spinGroupEquivQuaternionUnitaryOverCenter,
    coe_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour_apply]
  rfl

/-- The inverse chosen Spin equivalence recovers the Clifford value through the inverse
center-linear quaternion model. -/
@[simp]
theorem coe_spinGroupEquivQuaternionUnitaryOverCenter_symm_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4)
    {a b : Subalgebra.center K (even Q)}
    (e : even Q ≃ₐ[Subalgebra.center K (even Q)]
      ℍ[Subalgebra.center K (even Q),a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x))
    (q : unitary ℍ[Subalgebra.center K (even Q),a,0,b]) :
    ((spinGroupEquivQuaternionUnitaryOverCenter Q hQ hV0 hV e he).symm q :
        CliffordAlgebra Q) =
      (e.symm (q : ℍ[Subalgebra.center K (even Q),a,0,b]) : CliffordAlgebra Q) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos hV0
  rw [spinGroupEquivQuaternionUnitaryOverCenter,
    coe_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour_symm_apply]
  rfl

/-- The quaternion attached to a Spin element by a chosen center-linear model has norm one. -/
-- Use pre-simp so this fires before the forward coercion equation erases the model hypotheses.
@[simp↓]
theorem normForm_spinGroupEquivQuaternionUnitaryOverCenter
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4)
    {a b : Subalgebra.center K (even Q)}
    (e : even Q ≃ₐ[Subalgebra.center K (even Q)]
      ℍ[Subalgebra.center K (even Q),a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) (s : spinGroup Q) :
    QuaternionAlgebra.normForm a 0 b
      (spinGroupEquivQuaternionUnitaryOverCenter Q hQ hV0 hV e he s :
        ℍ[Subalgebra.center K (even Q),a,0,b]) = 1 :=
  (QuaternionAlgebra.mem_unitary_iff_normForm_eq_one _ _ _ _).mp
    (spinGroupEquivQuaternionUnitaryOverCenter Q hQ hV0 hV e he s).2

/-- Every regular quaternary Spin group whose even-Clifford center is a field is isomorphic to the
norm-one group of a quaternion algebra over that center. -/
theorem exists_spinGroupEquivQuaternionUnitaryOverCenter_of_finrank_eq_four
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : finrank K V = 4)
    (hfield : IsField (Subalgebra.center K (even Q))) :
    ∃ a b : (Subalgebra.center K (even Q))ˣ,
      Nonempty (spinGroup Q ≃*
        unitary ℍ[Subalgebra.center K (even Q),(a : _),0,(b : _)]) := by
  obtain ⟨a, b, e, he⟩ :=
    exists_evenQuaternionEquiv_of_finrank_eq_four_of_isField_center Q hQ hV hfield
  exact ⟨a, b, ⟨spinGroupEquivQuaternionUnitaryOverCenter Q hQ (by omega) (by omega) e he⟩⟩

end CliffordAlgebra

end
