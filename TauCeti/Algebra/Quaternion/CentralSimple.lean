/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import TauCeti.Algebra.Quaternion.SplittingCriterion
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.Tactic.LinearCombination

/-!
# Central simple quaternion symbol algebras

For a field `K` with `2` invertible, this file proves centrality for the general quaternion algebra
`ℍ[K,a,b,c]` when `c ≠ 0`, and simplicity when `c * (b ^ 2 + 4 * a) ≠ 0`. Completing the square
reduces these cases to a unit-parameter symbol, for which the norm criterion gives either a
division algebra or a two-by-two matrix algebra. The two-parameter symbol `ℍ[K,a,b]` is the
specialization used by the Brauer-valued invariants.

## Main results

* `TauCeti.QuaternionAlgebra.isCentral_of_j_sq_ne_zero`: a quaternion algebra with nonzero
  `j`-square is central.
* `TauCeti.QuaternionAlgebra.isSimpleRing_of_mul_discr_ne_zero`: a quaternion algebra with
  nonzero `j`-square and nonzero discriminant is simple.
* `TauCeti.QuaternionAlgebra.mem_center_iff`: a central element of a unit-parameter symbol has
  zero imaginary coordinates.
* `TauCeti.QuaternionAlgebra.instIsCentral`: unit-parameter symbol algebras are central.
* `TauCeti.QuaternionAlgebra.instIsSimpleRing`: unit-parameter symbol algebras are simple.

The split/division dichotomy used here is the norm-equation criterion in
`TauCeti.Algebra.Quaternion.SplittingCriterion`.
-/

public section

open scoped Quaternion

namespace TauCeti

namespace QuaternionAlgebra

variable {K : Type*} [Field K] [Invertible (2 : K)] (a b : Kˣ)

private def completeSquareBasis (a b c : K) :
    _root_.QuaternionAlgebra.Basis ℍ[K,b ^ 2 + 4 * a,0,c] a b c where
  i := ⟨b / 2, 1 / 2, 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, b / 2, 1 / 2⟩
  i_mul_i := by
    ext <;> simp [div_eq_mul_inv]
    all_goals
      field_simp [show (2 : K) ≠ 0 from two_ne_zero]
      ring
  j_mul_j := by
    ext <;> simp
  i_mul_j := by
    ext <;> simp [div_eq_mul_inv]
  j_mul_i := by
    ext <;> simp [div_eq_mul_inv]
    all_goals
      field_simp [show (2 : K) ≠ 0 from two_ne_zero]
      ring

private def completeSquareInvBasis (a b c : K) :
    _root_.QuaternionAlgebra.Basis ℍ[K,a,b,c] (b ^ 2 + 4 * a) 0 c where
  i := ⟨-b, 2, 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, -b, 2⟩
  i_mul_i := by
    ext <;> simp <;> ring
  j_mul_j := by
    ext <;> simp
  i_mul_j := by
    ext <;> simp
  j_mul_i := by
    ext <;> simp
    all_goals ring

private theorem completeSquareBasis_lift_apply_i (a b c : K) :
    (completeSquareBasis a b c).liftHom (⟨0, 1, 0, 0⟩ : ℍ[K,a,b,c]) =
      ⟨b / 2, 1 / 2, 0, 0⟩ := by
  simp [completeSquareBasis, _root_.QuaternionAlgebra.Basis.lift]

private theorem completeSquareBasis_lift_apply_j (a b c : K) :
    (completeSquareBasis a b c).liftHom (⟨0, 0, 1, 0⟩ : ℍ[K,a,b,c]) =
      ⟨0, 0, 1, 0⟩ := by
  simp [completeSquareBasis, _root_.QuaternionAlgebra.Basis.lift]

omit [Invertible (2 : K)] in
private theorem completeSquareInvBasis_lift_apply_i (a b c : K) :
    (completeSquareInvBasis a b c).liftHom
        (⟨0, 1, 0, 0⟩ : ℍ[K,b ^ 2 + 4 * a,0,c]) =
      ⟨-b, 2, 0, 0⟩ := by
  simp [completeSquareInvBasis, _root_.QuaternionAlgebra.Basis.lift]

omit [Invertible (2 : K)] in
private theorem completeSquareInvBasis_lift_apply_j (a b c : K) :
    (completeSquareInvBasis a b c).liftHom
        (⟨0, 0, 1, 0⟩ : ℍ[K,b ^ 2 + 4 * a,0,c]) =
      ⟨0, 0, 1, 0⟩ := by
  simp [completeSquareInvBasis, _root_.QuaternionAlgebra.Basis.lift]

private def completeSquareEquiv (a b c : K) :
    ℍ[K,a,b,c] ≃ₐ[K] ℍ[K,b ^ 2 + 4 * a,0,c] :=
  AlgEquiv.ofAlgHom (completeSquareBasis a b c).liftHom
    (completeSquareInvBasis a b c).liftHom (by
      apply _root_.QuaternionAlgebra.hom_ext
      · -- Expose the standard generator before applying the two change-of-basis formulas.
        change (completeSquareBasis a b c).liftHom
            ((completeSquareInvBasis a b c).liftHom
              (⟨0, 1, 0, 0⟩ : ℍ[K,b ^ 2 + 4 * a,0,c])) =
          (⟨0, 1, 0, 0⟩ : ℍ[K,b ^ 2 + 4 * a,0,c])
        rw [completeSquareInvBasis_lift_apply_i]
        simp only [_root_.QuaternionAlgebra.Basis.liftHom_apply]
        simp only [completeSquareBasis, _root_.QuaternionAlgebra.Basis.lift]
        ext <;> simp
        all_goals
          field_simp [show (2 : K) ≠ 0 from two_ne_zero]
          ring
      · -- The second generator is fixed by both changes of basis.
        change (completeSquareBasis a b c).liftHom
            ((completeSquareInvBasis a b c).liftHom
              (⟨0, 0, 1, 0⟩ : ℍ[K,b ^ 2 + 4 * a,0,c])) =
          (⟨0, 0, 1, 0⟩ : ℍ[K,b ^ 2 + 4 * a,0,c])
        rw [completeSquareInvBasis_lift_apply_j, completeSquareBasis_lift_apply_j]) (by
      apply _root_.QuaternionAlgebra.hom_ext
      · -- The inverse change sends the completed-square generator back to the original one.
        change (completeSquareInvBasis a b c).liftHom
            ((completeSquareBasis a b c).liftHom
              (⟨0, 1, 0, 0⟩ : ℍ[K,a,b,c])) =
          (⟨0, 1, 0, 0⟩ : ℍ[K,a,b,c])
        rw [completeSquareBasis_lift_apply_i]
        simp only [one_div, _root_.QuaternionAlgebra.Basis.liftHom_apply]
        simp only [completeSquareInvBasis, _root_.QuaternionAlgebra.Basis.lift]
        ext <;> simp
        all_goals
          field_simp [show (2 : K) ≠ 0 from two_ne_zero]
          ring
      · -- Both changes fix the second quaternion generator.
        change (completeSquareInvBasis a b c).liftHom
            ((completeSquareBasis a b c).liftHom
              (⟨0, 0, 1, 0⟩ : ℍ[K,a,b,c])) =
          (⟨0, 0, 1, 0⟩ : ℍ[K,a,b,c])
        rw [completeSquareBasis_lift_apply_j, completeSquareInvBasis_lift_apply_j])

private theorem center_coordinates_eq_zero (a : K) (b : Kˣ)
    {x : ℍ[K,a,(b : K)]}
    (hx : x ∈ Subalgebra.center K ℍ[K,(a : K),(b : K)]) :
    x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0 := by
  rw [Subalgebra.mem_center_iff] at hx
  have hi := hx (⟨0, 1, 0, 0⟩ : ℍ[K,(a : K),(b : K)])
  have hj := hx (⟨0, 0, 1, 0⟩ : ℍ[K,(a : K),(b : K)])
  have hiK := congrArg _root_.QuaternionAlgebra.imK hi
  have hjI := congrArg _root_.QuaternionAlgebra.imI hj
  have hjK := congrArg _root_.QuaternionAlgebra.imK hj
  simp only [_root_.QuaternionAlgebra.imI_mul, _root_.QuaternionAlgebra.imK_mul] at hiK hjI hjK
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hb : (b : K) ≠ 0 := b.ne_zero
  have hI : (2 : K) * x.imI = 0 := by
    linear_combination -hjK
  have hJ : (2 : K) * (b : K) * x.imJ = 0 := by
    linear_combination (b : K) * hiK
  have hK : (2 : K) * (b : K) * x.imK = 0 := by
    linear_combination -hjI
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp hI).resolve_left h2
  · exact (mul_eq_zero.mp hJ).resolve_left (mul_ne_zero h2 hb)
  · exact (mul_eq_zero.mp hK).resolve_left (mul_ne_zero h2 hb)

/-- A central element of a unit-parameter quaternion symbol has no imaginary part. -/
theorem mem_center_iff (a : K) (b : Kˣ) {x : ℍ[K,a,(b : K)]} :
    x ∈ Subalgebra.center K ℍ[K,a,(b : K)] ↔
      x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0 := by
  constructor
  · exact center_coordinates_eq_zero a b
  · intro hx
    rw [Subalgebra.mem_center_iff (R := K)]
    intro y
    refine _root_.QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · simp only [_root_.QuaternionAlgebra.re_mul]
      ring
    · simp only [_root_.QuaternionAlgebra.imI_mul]
      simp [hx.1, hx.2.1, hx.2.2]
      ring
    · simp only [_root_.QuaternionAlgebra.imJ_mul]
      simp [hx.1, hx.2.1, hx.2.2]
      ring
    · simp only [_root_.QuaternionAlgebra.imK_mul]
      simp [hx.1, hx.2.1, hx.2.2]
      ring

/-- A unit-parameter quaternion symbol is central over its base field. -/
instance instIsCentral (a : K) (b : Kˣ) : Algebra.IsCentral K ℍ[K,a,(b : K)] :=
  ⟨fun x hx ↦ Algebra.mem_bot.mpr ⟨x.re, by
    -- The algebra map is the scalar inclusion; expose it before comparing coordinates.
    change (x.re : ℍ[K,a,(b : K)]) = x
    refine _root_.QuaternionAlgebra.ext rfl ?_ ?_ ?_
    · simpa using ((mem_center_iff a b).mp hx |>.1).symm
    · simpa using ((mem_center_iff a b).mp hx |>.2.1).symm
    · simpa using ((mem_center_iff a b).mp hx |>.2.2).symm⟩⟩

private theorem isSimpleRing_of_isUnit_or_split :
    IsSimpleRing ℍ[K,(a : K),(b : K)] := by
  rcases QuaternionAlgebra.forall_isUnit_or_nonempty_algEquiv_matrix a b with hdiv | hsplit
  · apply IsSimpleRing.of_eq_bot_or_eq_top
    intro I
    rw [or_iff_not_imp_left]
    intro hI
    obtain ⟨x, hxI, hx0⟩ := SetLike.exists_of_lt
      (bot_lt_iff_ne_bot.mpr hI : (⊥ : TwoSidedIdeal ℍ[K,(a : K),(b : K)]) < I)
    obtain ⟨u, hu⟩ := hdiv x hx0
    rw [← hu] at hxI
    have hone : (1 : ℍ[K,(a : K),(b : K)]) ∈ I := by
      simpa using I.mul_mem_left (↑(u⁻¹ : ℍ[K,(a : K),(b : K)]ˣ)) (↑u) hxI
    exact (TwoSidedIdeal.one_mem_iff I).mp hone
  · obtain ⟨e⟩ := hsplit
    exact IsSimpleRing.of_ringEquiv e.symm.toRingEquiv inferInstance

/-- A unit-parameter quaternion symbol is a simple ring. -/
instance instIsSimpleRing : IsSimpleRing ℍ[K,(a : K),(b : K)] :=
  isSimpleRing_of_isUnit_or_split a b

/-- A quaternion algebra with nonzero `j`-square is central. -/
theorem isCentral_of_j_sq_ne_zero {a b c : K}
    (hc : c ≠ 0) :
    Algebra.IsCentral K ℍ[K,a,b,c] := by
  let v : Kˣ := Units.mk0 c hc
  have htarget : Algebra.IsCentral K ℍ[K,b ^ 2 + 4 * a,0,c] :=
    instIsCentral (b ^ 2 + 4 * a) v
  exact Algebra.IsCentral.of_algEquiv (K := K) (D := ℍ[K,b ^ 2 + 4 * a,0,c])
    (D' := ℍ[K,a,b,c]) (h := htarget) (completeSquareEquiv a b c).symm

/-- A quaternion algebra with nonzero discriminant and nonzero `j`-square is simple. -/
theorem isSimpleRing_of_mul_discr_ne_zero {a b c : K}
    (h : c * (b ^ 2 + 4 * a) ≠ 0) : IsSimpleRing ℍ[K,a,b,c] := by
  have ⟨hc, hd⟩ := mul_ne_zero_iff.mp h
  let u : Kˣ := Units.mk0 (b ^ 2 + 4 * a) hd
  let v : Kˣ := Units.mk0 c hc
  have htarget : IsSimpleRing ℍ[K,b ^ 2 + 4 * a,0,c] := instIsSimpleRing u v
  exact IsSimpleRing.of_ringEquiv (completeSquareEquiv a b c).symm.toRingEquiv htarget

end QuaternionAlgebra

end TauCeti
