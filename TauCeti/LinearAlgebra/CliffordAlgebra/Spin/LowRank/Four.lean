/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
-- Private: the Clifford-group characterization of the Lipschitz group and the reversal calculus
-- on odd elements are used only inside the proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.CliffordGroup
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Four

/-!
# The Spin group in dimension at most four

For a nondegenerate quadratic space of positive dimension at most four over a field of
characteristic not two, Mathlib's `spinGroup` fills the even unitary carrier `U(C₀, σ)`: an even
Clifford unit `x` with `reverse x * x = 1` conjugates each vector `ι v` to the odd element
`x * ι v * reverse x`, which is fixed by reversal and hence is again a vector
(`CliffordAlgebra.mem_range_ι_of_mem_evenOdd_one_of_reverse_eq_of_finrank_le_four`); so `x` lies in
the classical Clifford group, which is the Lipschitz group in this setting
(`CliffordAlgebra.mem_lipschitzGroup_of_involute_act_ι_mem_range_ι`).

Dimension zero is excluded, and the exclusion is not decoration: there the Lipschitz group is
trivial while the even unitary carrier is `μ₂`. Dimensions one and two are also covered, without
nondegeneracy, by `TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/One.lean` and
`TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Two.lean`. The bound four is where the
reversal argument stops: in dimension five the odd part also contains the volume element, which
reversal fixes, and the identification needs a further argument
(`TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Five.lean`); in dimension six the even
unitary group is strictly larger than the Spin group.

## Main results

* `CliffordAlgebra.evenUnitaryGroup_le_lipschitzGroup_of_finrank_le_four`: for a nondegenerate
  form in positive dimension at most four, every even unitary Clifford unit is Lipschitz.
* `CliffordAlgebra.range_spinGroup_toUnits_eq_evenUnitaryGroup_of_finrank_le_four`: for a
  nondegenerate form in positive dimension at most four, the Spin image and the even unitary
  carrier coincide.
* `CliffordAlgebra.spinGroupEquivEvenUnitaryOfFinrankLeFour`: the resulting multiplicative
  equivalence between the Spin group and the even unitary carrier.
* `CliffordAlgebra.spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour`: transport of this
  equivalence along any reversal-preserving algebra equivalence.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

open Module

namespace CliffordAlgebra

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

/-- For a nondegenerate quadratic space of positive dimension at most four, the even unitary
carrier lies in the Lipschitz group. -/
theorem evenUnitaryGroup_le_lipschitzGroup_of_finrank_le_four (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V) (hV : finrank K V ≤ 4) :
    evenUnitaryGroup Q ≤ lipschitzGroup Q := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hV0
  intro x hx
  refine mem_lipschitzGroup_of_involute_act_ι_mem_range_ι Q hQ hQ.exists_isUnit fun m => ?_
  have hxe : (x : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    have h := evenUnitaryGroup.mem_even Q hx
    rwa [← Subalgebra.mem_toSubmodule, even_toSubmodule] at h
  have hxie : ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    have h := evenUnitaryGroup.mem_even Q (inv_mem hx)
    rwa [← Subalgebra.mem_toSubmodule, even_toSubmodule] at h
  rw [involute_eq_of_mem_even hxe]
  -- The conjugate of a vector by an even unit is odd.
  have hodd : (x : CliffordAlgebra Q) * ι Q m * ↑x⁻¹ ∈ evenOdd Q 1 := by
    have h : (x : CliffordAlgebra Q) * ι Q m ∈ evenOdd Q 1 :=
      zero_add (1 : ZMod 2) ▸ SetLike.mul_mem_graded hxe (ι_mem_evenOdd_one Q m)
    exact add_zero (1 : ZMod 2) ▸ SetLike.mul_mem_graded h hxie
  -- Reversal inverts an even unitary unit, so it fixes the conjugate.
  have hrev : reverse ((x : CliffordAlgebra Q) * ι Q m *
        ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
      (x : CliffordAlgebra Q) * ι Q m * ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
    have hxr : reverse (x : CliffordAlgebra Q) = ↑x⁻¹ := evenUnitaryGroup.reverse_eq_inv Q ⟨x, hx⟩
    have hxir : reverse ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = x := by
      rw [← hxr, reverse_reverse]
    simp only [reverse.map_mul, reverse_ι, hxr, hxir, mul_assoc]
  exact mem_range_ι_of_mem_evenOdd_one_of_reverse_eq_of_finrank_le_four Q hV hodd hrev

/-- For a nondegenerate quadratic space of positive dimension at most four, the Spin group fills
the even unitary carrier inside Clifford units. -/
-- Not `@[simp]`: `range_spinGroup_toUnits` already simplifies the left-hand side.
theorem range_spinGroup_toUnits_eq_evenUnitaryGroup_of_finrank_le_four
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4) :
    (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range = evenUnitaryGroup Q := by
  rw [range_spinGroup_toUnits]
  exact inf_eq_right.mpr (evenUnitaryGroup_le_lipschitzGroup_of_finrank_le_four Q hQ hV0 hV)

/-- For a nondegenerate quadratic space of positive dimension at most four, the Spin group is
multiplicatively equivalent to the even unitary carrier. -/
noncomputable def spinGroupEquivEvenUnitaryOfFinrankLeFour
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4) : spinGroup Q ≃* evenUnitaryGroup Q :=
  MulEquiv.ofBijective (spinGroupToEvenUnitary Q)
    ⟨spinGroupToEvenUnitary_injective Q, fun x ↦ by
      have hx : (x : (CliffordAlgebra Q)ˣ) ∈
          (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range := by
        rw [range_spinGroup_toUnits_eq_evenUnitaryGroup_of_finrank_le_four Q hQ hV0 hV]
        exact x.2
      obtain ⟨s, hs⟩ := hx
      refine ⟨s, Subtype.ext ?_⟩
      simpa only [coe_spinGroupToEvenUnitary_apply] using hs⟩

/-- The low-rank Spin/even-unitary equivalence is induced by the canonical inclusion. -/
@[simp]
theorem spinGroupEquivEvenUnitaryOfFinrankLeFour_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4) (s : spinGroup Q) :
    spinGroupEquivEvenUnitaryOfFinrankLeFour Q hQ hV0 hV s =
      spinGroupToEvenUnitary Q s :=
  MulEquiv.ofBijective_apply _ _ s

variable {A : Type w} [Semiring A] [Algebra K A] [StarMul A]

/-- A reversal-preserving algebra equivalence transports a positive, at-most-four-dimensional
Spin group to the unitary group of the target algebra. -/
noncomputable def spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4) (e : even Q ≃ₐ[K] A)
    (he : ∀ x, e (reverseEven Q x) = star (e x)) : spinGroup Q ≃* unitary A :=
  (spinGroupEquivEvenUnitaryOfFinrankLeFour Q hQ hV0 hV).trans
    (evenUnitaryGroupEquivUnitaryOfAlgEquiv Q e he)

/-- The transported low-rank Spin equivalence applies the target algebra equivalence to the
underlying even Clifford element. -/
@[simp]
theorem coe_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4) (e : even Q ≃ₐ[K] A)
    (he : ∀ x, e (reverseEven Q x) = star (e x)) (s : spinGroup Q) :
    (spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he s : A) =
      e (evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q s)) := by
  rw [spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour, MulEquiv.trans_apply,
    spinGroupEquivEvenUnitaryOfFinrankLeFour_apply]
  exact coe_evenUnitaryGroupEquivUnitaryOfAlgEquiv_apply Q e he _

/-- The inverse transported low-rank Spin equivalence recovers the Clifford value through the
inverse target algebra equivalence. -/
@[simp]
theorem coe_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour_symm_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V)
    (hV : finrank K V ≤ 4) (e : even Q ≃ₐ[K] A)
    (he : ∀ x, e (reverseEven Q x) = star (e x)) (q : unitary A) :
    ((spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he).symm q :
        CliffordAlgebra Q) = (e.symm (q : A) : CliffordAlgebra Q) := by
  let s := (spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he).symm q
  have hs : e (evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q s)) = (q : A) := by
    rw [← coe_spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour_apply Q hQ hV0 hV e he]
    exact congrArg Subtype.val
      ((spinGroupEquivUnitaryOfAlgEquivOfFinrankLeFour Q hQ hV0 hV e he).apply_symm_apply q)
  have h := congrArg (fun x : even Q ↦ (x : CliffordAlgebra Q))
    ((e.symm_apply_eq).mpr hs.symm)
  simpa [s] using h.symm

end CliffordAlgebra
