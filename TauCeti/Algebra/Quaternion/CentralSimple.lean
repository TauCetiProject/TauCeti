/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.RingTheory.SimpleRing.Basic
public import TauCeti.Algebra.Quaternion.SymbolEquiv
public import TauCeti.Algebra.Quaternion.SplittingCriterion
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.Tactic.LinearCombination

/-!
# Central simple quaternion symbol algebras

For a field `K` with `2` invertible, this file proves centrality for the general quaternion algebra
`ℍ[K,a,b,c]` when `c ≠ 0 ∨ QuadraticAlgebra.discr a b ≠ 0`, and simplicity when
`c * QuadraticAlgebra.discr a b ≠ 0`. Completing the square
reduces these cases to a unit-parameter symbol, for which the norm criterion gives either a
division algebra or a two-by-two matrix algebra. The two-parameter symbol `ℍ[K,a,b]` is the
specialization used by the Brauer-valued invariants.

## Main results

* `TauCeti.QuaternionAlgebra.isCentral_of_j_sq_ne_zero_or_discr_ne_zero`: a quaternion algebra
  with nonzero `j`-square or discriminant is central.
* `TauCeti.QuaternionAlgebra.isCentral_of_j_sq_ne_zero`: the nonzero `j`-square specialization.
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

variable {K : Type*}

section UnitParameter

variable [CommRing K] [Invertible (2 : K)]

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
  have hI : (2 : K) * x.imI = 0 := by
    linear_combination -hjK
  have hJ : (2 : K) * (b : K) * x.imJ = 0 := by
    linear_combination (b : K) * hiK
  have hK : (2 : K) * (b : K) * x.imK = 0 := by
    linear_combination -hjI
  refine ⟨?_, ?_, ?_⟩
  · apply (mul_right_inj_of_invertible (c := (2 : K))).mp
    simpa [mul_comm] using hI
  · have hJ' : (b : K) * x.imJ = 0 := by
      apply (mul_right_inj_of_invertible (c := (2 : K))).mp
      simpa [mul_assoc, mul_comm, mul_left_comm] using hJ
    apply (mul_right_inj_of_invertible (c := (b : K))).mp
    simpa using hJ'
  · have hK' : (b : K) * x.imK = 0 := by
      apply (mul_right_inj_of_invertible (c := (2 : K))).mp
      simpa [mul_assoc, mul_comm, mul_left_comm] using hK
    apply (mul_right_inj_of_invertible (c := (b : K))).mp
    simpa using hK'

/-- An element of a unit-parameter quaternion symbol is central if and only if all three imaginary
coordinates vanish. -/
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

end UnitParameter

section Field

variable [Field K] [Invertible (2 : K)] (a b : Kˣ)

/-- A quaternion symbol with both parameters units is a simple ring. -/
instance instIsSimpleRing : IsSimpleRing ℍ[K,(a : K),(b : K)] := by
  rcases QuaternionAlgebra.forall_isUnit_or_nonempty_algEquiv_matrix a b with hdiv | hsplit
  · let divisionRing : DivisionRing ℍ[K,(a : K),(b : K)] :=
      DivisionRing.ofIsUnitOrEqZero (fun x ↦ by
        by_cases hx : x = 0
        · exact Or.inr hx
        · exact Or.inl (hdiv x hx))
    exact @DivisionRing.isSimpleRing _ divisionRing
  · obtain ⟨e⟩ := hsplit
    exact IsSimpleRing.of_ringEquiv e.symm.toRingEquiv inferInstance

/-- A quaternion algebra with nonzero `j`-square or discriminant is central. -/
theorem isCentral_of_j_sq_ne_zero_or_discr_ne_zero {a b c : K}
    (h : c ≠ 0 ∨ QuadraticAlgebra.discr a b ≠ 0) :
    Algebra.IsCentral K ℍ[K,a,b,c] := by
  rcases h with hc | hd
  · let v : Kˣ := Units.mk0 c hc
    have htarget : Algebra.IsCentral K ℍ[K,QuadraticAlgebra.discr a b,0,c] :=
      instIsCentral (QuadraticAlgebra.discr a b) v
    exact Algebra.IsCentral.of_algEquiv (K := K) (D := ℍ[K,QuadraticAlgebra.discr a b,0,c])
      (D' := ℍ[K,a,b,c]) (h := htarget) (completeSquareEquiv a b c).symm
  · by_cases hc : c = 0
    · subst c
      let v : Kˣ := Units.mk0 (QuadraticAlgebra.discr a b) hd
      have htarget : Algebra.IsCentral K ℍ[K,0,0,QuadraticAlgebra.discr a b] :=
        instIsCentral 0 v
      have hsource : Algebra.IsCentral K ℍ[K,QuadraticAlgebra.discr a b,0,0] :=
        Algebra.IsCentral.of_algEquiv (K := K) (D := ℍ[K,0,0,QuadraticAlgebra.discr a b])
          (D' := ℍ[K,QuadraticAlgebra.discr a b,0,0]) (h := htarget)
          (_root_.QuaternionAlgebra.swapEquiv (QuadraticAlgebra.discr a b) 0).symm
      exact Algebra.IsCentral.of_algEquiv (K := K) (D := ℍ[K,QuadraticAlgebra.discr a b,0,0])
        (D' := ℍ[K,a,b,0]) (h := hsource) (completeSquareEquiv a b 0).symm
    · let v : Kˣ := Units.mk0 c hc
      have htarget : Algebra.IsCentral K ℍ[K,QuadraticAlgebra.discr a b,0,c] :=
        instIsCentral (QuadraticAlgebra.discr a b) v
      exact Algebra.IsCentral.of_algEquiv (K := K) (D := ℍ[K,QuadraticAlgebra.discr a b,0,c])
        (D' := ℍ[K,a,b,c]) (h := htarget) (completeSquareEquiv a b c).symm

/-- A quaternion algebra with nonzero `j`-square is central. -/
theorem isCentral_of_j_sq_ne_zero {a b c : K}
    (hc : c ≠ 0) :
    Algebra.IsCentral K ℍ[K,a,b,c] :=
  isCentral_of_j_sq_ne_zero_or_discr_ne_zero (Or.inl hc)

/-- A quaternion algebra with nonzero discriminant and nonzero `j`-square is simple. -/
theorem isSimpleRing_of_mul_discr_ne_zero {a b c : K}
    (h : c * QuadraticAlgebra.discr a b ≠ 0) : IsSimpleRing ℍ[K,a,b,c] := by
  have ⟨hc, hd⟩ := mul_ne_zero_iff.mp h
  let u : Kˣ := Units.mk0 (QuadraticAlgebra.discr a b) hd
  let v : Kˣ := Units.mk0 c hc
  have htarget : IsSimpleRing ℍ[K,QuadraticAlgebra.discr a b,0,c] := instIsSimpleRing u v
  exact IsSimpleRing.of_ringEquiv (completeSquareEquiv a b c).symm.toRingEquiv htarget

end Field

end QuaternionAlgebra

end TauCeti
