/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.Algebra.CharP.Invertible

/-!
# The kernel of the Pin action

For a positive-dimensional finite nondegenerate quadratic space over a field where `2` is
invertible, the kernel of the Pin action is canonically the cyclic group of order two. The proof
identifies a Pin element acting trivially with an even element, then reuses the Spin-kernel
classification.

## Main results

* `CliffordAlgebra.neg_one_ne_one` and `CliffordAlgebra.zsmul_coe_pinGroup_injective`: over a
  nontrivial commutative ring where `2` is invertible, `-1 ≠ 1` in `CliffordAlgebra Q` and distinct
  signs in `ℤˣ` act differently on any element of `Pin(Q)`.
* `CliffordAlgebra.zmodTwoMulEquivKerPinToOrthogonal`: the kernel is canonically
  equivalent to `Multiplicative (ZMod 2)`.
* `CliffordAlgebra.zmodTwoMulEquivKerPinToOrthogonal_apply_ofAdd_one`: the chosen
  generator maps to the scalar `-1` inside the Pin group.
* `CliffordAlgebra.zmodTwoMulEquivKerPinToOrthogonal_symm_apply_negOne`: the inverse
  sends the scalar `-1` to the chosen generator.
* `CliffordAlgebra.pinToOrthogonal_eq_iff` and
  `CliffordAlgebra.existsUnique_zsmul_of_pinToOrthogonal_eq`: two Pin elements have the same
  orthogonal action if and only if they agree up to sign in `CliffordAlgebra Q`, and that sign in
  `ℤˣ` is unique.

## References

See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

namespace CliffordAlgebra

universe u v

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [Nontrivial R] [Invertible (2 : R)]
  [AddCommGroup M] [Module R M]

/-- In a Clifford algebra over a nontrivial commutative ring in which `2` is invertible, `-1` is
distinct from `1`. -/
theorem neg_one_ne_one (Q : QuadraticForm R M) : (-1 : CliffordAlgebra Q) ≠ 1 := fun h =>
  one_ne_zero (TauCeti.eq_zero_of_eq_neg_of_invertible_two (R := R) h.symm)

/-- Distinct signs in `ℤˣ` act differently on any element of `Pin(Q)` over a nontrivial commutative
ring in which `2` is invertible. -/
theorem zsmul_coe_pinGroup_injective {Q : QuadraticForm R M} (g : pinGroup Q) :
    Function.Injective fun s : ℤˣ => (s : ℤ) • (g : CliffordAlgebra Q) := fun a b h => by
  have h1 : (a : ℤ) • (1 : CliffordAlgebra Q) = (b : ℤ) • (1 : CliffordAlgebra Q) := by
    simpa only [smul_mul_assoc, pinGroup.mul_star_self_of_mem g.property] using
      congrArg (· * star (g : CliffordAlgebra Q)) h
  rcases Int.units_eq_one_or a with rfl | rfl <;>
    rcases Int.units_eq_one_or b with rfl | rfl <;>
    simp_all [neg_one_ne_one Q, (neg_one_ne_one Q).symm]

end CommRing

variable {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

private noncomputable def pinKernelToSpinKernel
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (x : MonoidHom.ker (pinToOrthogonal Q)) :
    MonoidHom.ker (spinToSpecialOrthogonal Q) :=
  let s : spinGroup Q :=
    ⟨x, x.val.property, mem_even_of_det_pinToOrthogonal_eq_one Q x.val (by
      rw [MonoidHom.mem_ker.mp x.property]
      simp)⟩
  ⟨s, by
    rw [ker_spinToSpecialOrthogonal, MonoidHom.mem_ker, ← pinToOrthogonal_spinToPin]
    have hspinpin : spinToPin Q s = x.val := Subtype.ext (coe_spinToPin_apply s)
    rw [hspinpin]
    exact MonoidHom.mem_ker.mp x.property⟩

private noncomputable def kerSpinToSpecialOrthogonalEquivKerPinToOrthogonal
    (Q : QuadraticForm K M) [Invertible (2 : K)] :
    MonoidHom.ker (spinToSpecialOrthogonal Q) ≃*
      MonoidHom.ker (pinToOrthogonal Q) where
  toFun x :=
    ⟨spinToPin Q x, by
      rw [MonoidHom.mem_ker, pinToOrthogonal_spinToPin]
      exact MonoidHom.mem_ker.mp (ker_spinToSpecialOrthogonal Q ▸ x.property)⟩
  invFun := pinKernelToSpinKernel Q
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp only
    exact coe_spinToPin_apply x.val
  right_inv x := by
    apply Subtype.ext
    simp only
    apply Subtype.ext
    exact coe_spinToPin_apply (pinKernelToSpinKernel Q x).val
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (map_mul (spinToPin Q) x.val y.val)

private theorem kerSpinToSpecialOrthogonalEquivKerPinToOrthogonal_apply
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (x : MonoidHom.ker (spinToSpecialOrthogonal Q)) :
    (kerSpinToSpecialOrthogonalEquivKerPinToOrthogonal Q x).val =
      spinToPin Q x.val :=
  rfl

/-- The kernel of the Pin action on a positive-dimensional nondegenerate quadratic space over a
field in which `2` is invertible is canonically the cyclic group of order two, with its generator
sent to the scalar `-1`. -/
noncomputable def zmodTwoMulEquivKerPinToOrthogonal [Nontrivial M]
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (hQ : Q.Nondegenerate) :
    Multiplicative (ZMod 2) ≃* MonoidHom.ker (pinToOrthogonal Q) :=
  (zmodTwoMulEquivKerSpinToSpecialOrthogonal Q hQ).trans
    (kerSpinToSpecialOrthogonalEquivKerPinToOrthogonal Q)

/-- The chosen generator of `Multiplicative (ZMod 2)` maps to the scalar `-1` in the Pin
kernel. -/
@[simp]
theorem zmodTwoMulEquivKerPinToOrthogonal_apply_ofAdd_one [Nontrivial M]
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (hQ : Q.Nondegenerate) :
    zmodTwoMulEquivKerPinToOrthogonal Q hQ (Multiplicative.ofAdd 1) =
      ⟨spinToPin Q (spinGroup.negOne Q hQ.ne_zero), by
        rw [MonoidHom.mem_ker, pinToOrthogonal_spinToPin,
          spinGroup.spinToOrthogonal_negOne]⟩ := by
  apply Subtype.ext
  rw [zmodTwoMulEquivKerPinToOrthogonal, MulEquiv.trans_apply,
    kerSpinToSpecialOrthogonalEquivKerPinToOrthogonal_apply]
  exact congrArg (spinToPin Q) <| congrArg Subtype.val
    (zmodTwoMulEquivKerSpinToSpecialOrthogonal_apply_ofAdd_one Q hQ)

/-- The inverse kernel equivalence sends the scalar `-1` to the chosen generator of
`Multiplicative (ZMod 2)`. -/
@[simp]
theorem zmodTwoMulEquivKerPinToOrthogonal_symm_apply_negOne [Nontrivial M]
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (hQ : Q.Nondegenerate) :
    (zmodTwoMulEquivKerPinToOrthogonal Q hQ).symm
        ⟨spinToPin Q (spinGroup.negOne Q hQ.ne_zero), by
          rw [MonoidHom.mem_ker, pinToOrthogonal_spinToPin,
            spinGroup.spinToOrthogonal_negOne]⟩ =
      Multiplicative.ofAdd 1 := by
  rw [MulEquiv.symm_apply_eq]
  exact (zmodTwoMulEquivKerPinToOrthogonal_apply_ofAdd_one Q hQ).symm

/-- Two elements of the Pin group have the same orthogonal action on a positive-dimensional
nondegenerate quadratic space over a field where `2` is invertible if and only if they are equal or
opposite in the Clifford algebra. -/
theorem pinToOrthogonal_eq_iff [Nontrivial M] (Q : QuadraticForm K M) [Invertible (2 : K)]
    (hQ : Q.Nondegenerate) {g₁ g₂ : pinGroup Q} :
    pinToOrthogonal Q g₁ = pinToOrthogonal Q g₂ ↔
      (g₁ : CliffordAlgebra Q) = g₂ ∨ (g₁ : CliffordAlgebra Q) = -g₂ := by
  constructor
  · intro h
    let s := pinKernelToSpinKernel Q
      ⟨g₁ * g₂⁻¹, by rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]⟩
    have hcancel : (s.val : CliffordAlgebra Q) * g₂ = g₁ :=
      (Submonoid.coe_mul (pinGroup Q) (g₁ * g₂⁻¹) g₂).symm.trans
        (congrArg Subtype.val (inv_mul_cancel_right g₁ g₂))
    rcases (mem_ker_spinToSpecialOrthogonal_iff Q hQ s.val).mp s.property with h1 | hneg1
    · exact Or.inl (by simpa [congrArg Subtype.val h1] using hcancel.symm)
    · exact Or.inr (by simpa [congrArg Subtype.val hneg1] using hcancel.symm)
  · rintro (heq | heq)
    · exact congrArg (pinToOrthogonal Q) (Subtype.ext heq)
    · have hg₁ : g₁ = spinToPin Q (spinGroup.negOne Q hQ.ne_zero) * g₂ := Subtype.ext (by
        rw [Submonoid.coe_mul, coe_spinToPin_apply, spinGroup.coe_negOne, neg_one_mul, heq])
      rw [hg₁, map_mul, pinToOrthogonal_spinToPin, spinGroup.spinToOrthogonal_negOne, one_mul]

/-- Two elements of the Pin group with the same orthogonal action on a positive-dimensional
nondegenerate quadratic space over a field where `2` is invertible differ by a unique sign in
`ℤˣ`. -/
theorem existsUnique_zsmul_of_pinToOrthogonal_eq [Nontrivial M] (Q : QuadraticForm K M)
    [Invertible (2 : K)] (hQ : Q.Nondegenerate) {g₁ g₂ : pinGroup Q}
    (h : pinToOrthogonal Q g₁ = pinToOrthogonal Q g₂) :
    ∃! s : ℤˣ, (g₁ : CliffordAlgebra Q) = (s : ℤ) • (g₂ : CliffordAlgebra Q) := by
  refine existsUnique_of_exists_of_unique ?_
    fun _ _ h₁ h₂ => zsmul_coe_pinGroup_injective g₂ (h₁.symm.trans h₂)
  rcases (pinToOrthogonal_eq_iff Q hQ).mp h with heq | heq
  · exact ⟨1, by simpa using heq⟩
  · exact ⟨-1, by simpa using heq⟩

end CliffordAlgebra
