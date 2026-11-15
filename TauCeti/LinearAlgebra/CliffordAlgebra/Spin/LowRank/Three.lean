/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Quaternion
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Four

/-!
# Ternary Spin groups and norm-one quaternions

For a nondegenerate ternary quadratic space over a field of characteristic different from two,
the even Clifford algebra is a quaternion algebra and Clifford reversal is its conjugation.
Consequently Mathlib's Spin group is isomorphic to the group of quaternions of norm one, including
the nonsplit forms over the base field. A chosen model gives the group equivalence with explicit
forward and inverse equations; existence of a model requires no square-root or splitting
hypothesis. This identifies Spin points; the description of the special orthogonal group by
quaternion units modulo scalars is a separate comparison.

The construction uses `CliffordAlgebra.exists_evenQuaternionEquiv_of_finrank_eq_three`, the
Spin/even-unitary comparison in dimension at most four, and
`CliffordAlgebra.evenUnitaryGroupEquivUnitaryOfAlgEquiv`. The norm-one characterization is
`QuaternionAlgebra.mem_unitary_iff_normForm_eq_one`.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
-/

public section

open scoped Quaternion

namespace CliffordAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

/-- A chosen reversal-preserving quaternion model identifies the ternary Spin group with
the norm-one quaternions in that model. -/
noncomputable def spinGroupEquivQuaternionUnitary (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) {a b : K}
    (e : even Q ≃ₐ[K] ℍ[K,a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) :
    spinGroup Q ≃* unitary ℍ[K,a,0,b] :=
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  (spinGroupEquivEvenUnitaryOfFinrankLeFour Q hQ (by omega) (by omega)).trans
    (evenUnitaryGroupEquivUnitaryOfAlgEquiv Q e he)

/-- The Spin equivalence evaluates the chosen algebra equivalence on the underlying even
Clifford element. -/
@[simp]
theorem coe_spinGroupEquivQuaternionUnitary_apply (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) {a b : K}
    (e : even Q ≃ₐ[K] ℍ[K,a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) (s : spinGroup Q) :
    (spinGroupEquivQuaternionUnitary Q hQ hV e he s : ℍ[K,a,0,b]) =
      e (evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q s)) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  rw [spinGroupEquivQuaternionUnitary, MulEquiv.trans_apply,
    spinGroupEquivEvenUnitaryOfFinrankLeFour_apply]
  exact coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_apply Q e he _

/-- The inverse Spin equivalence recovers the Clifford value from the inverse algebra model. -/
@[simp]
theorem coe_spinGroupEquivQuaternionUnitary_symm_apply (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) {a b : K}
    (e : even Q ≃ₐ[K] ℍ[K,a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) (q : unitary ℍ[K,a,0,b]) :
    ((spinGroupEquivQuaternionUnitary Q hQ hV e he).symm q : CliffordAlgebra Q) =
      (e.symm (q : ℍ[K,a,0,b]) : CliffordAlgebra Q) := by
  let s := (spinGroupEquivQuaternionUnitary Q hQ hV e he).symm q
  have hs : e (evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q s)) =
      (q : ℍ[K,a,0,b]) := by
    rw [← coe_spinGroupEquivQuaternionUnitary_apply Q hQ hV e he]
    exact congrArg Subtype.val
      ((spinGroupEquivQuaternionUnitary Q hQ hV e he).apply_symm_apply q)
  have h := congrArg (fun x : even Q => (x : CliffordAlgebra Q))
    ((e.symm_apply_eq).mpr hs.symm)
  simpa [s] using h.symm

/-- The quaternion attached to a Spin element has norm one. -/
theorem normForm_spinGroupEquivQuaternionUnitary (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) {a b : K}
    (e : even Q ≃ₐ[K] ℍ[K,a,0,b])
    (he : ∀ x, e (reverseEven Q x) = star (e x)) (s : spinGroup Q) :
    QuaternionAlgebra.normForm a 0 b
      (spinGroupEquivQuaternionUnitary Q hQ hV e he s : ℍ[K,a,0,b]) = 1 :=
  (QuaternionAlgebra.mem_unitary_iff_normForm_eq_one _ _ _ _).mp
    (spinGroupEquivQuaternionUnitary Q hQ hV e he s).2

/-- Every nondegenerate ternary Spin group over the base field is isomorphic to the norm-one
group of a quaternion algebra with unit symbols. -/
theorem exists_spinGroupEquivQuaternionUnitary_of_finrank_eq_three
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    ∃ a b : Kˣ, Nonempty (spinGroup Q ≃* unitary ℍ[K,(a : K),0,(b : K)]) := by
  obtain ⟨a, b, e, he⟩ := exists_evenQuaternionEquiv_of_finrank_eq_three Q hQ hV
  exact ⟨a, b, ⟨spinGroupEquivQuaternionUnitary Q hQ hV e he⟩⟩

end CliffordAlgebra
