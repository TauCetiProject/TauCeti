/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.NumberTheory.ClassGroup.Equiv
public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport

/-!
# The covariant cyclotomic action on class tensors

`TauCeti.cyclotomicClassAction R m K` is the representation of `(ZMod m)ˣ` on
`R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`, for a rational cyclotomic number field `K`
of conductor `m`. It extends the native class-group automorphisms, rather than defining a
new class group. The coefficient ring `R` can in particular be the ring of `p`-adic integers.

The action is covariant: the residue `a` sends an ideal class to its image under the field
automorphism taking a primitive root `ζ` to `ζ ^ a`. There is no inverse on this action;
inverses in character projectors belong to their coefficients. The pure-tensor and ideal-class
formulas below fix this convention and allow the representation to be used without unfolding it.

## References

* R. Sharifi, *Iwasawa Theory*, §1.3, Propositions 1.3.1–1.3.2.
-/

public section

open NumberField TensorProduct
open scoped nonZeroDivisors

namespace TauCeti

variable (R : Type*) [Ring R] (m : ℕ) [NeZero m]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]

/-- The covariant action of unit residues on scalar-extended cyclotomic ideal classes.
The residue `a` acts through the automorphism `σ_a` satisfying `σ_a(ζ) = ζ ^ a`. -/
noncomputable def cyclotomicClassAction :
    Representation R (ZMod m)ˣ (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) where
  toFun a :=
    let σ := (IsCyclotomicExtension.Rat.galEquivZMod m K).symm a
    let g := ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ.toRingEquiv)
    g.toAdditive.toAddMonoidHom.toIntLinearMap.baseChange R
  map_one' := by
    have h : RingOfIntegers.mapRingEquiv
        (((IsCyclotomicExtension.Rat.galEquivZMod m K).symm 1).toRingEquiv) =
        RingEquiv.refl (𝓞 K) := by
      rw [map_one]
      exact RingOfIntegers.mapRingEquiv_refl
    simp only [h, ClassGroup.mulEquiv_refl]
    ext r
    rfl
  map_mul' a b := by
    have h : RingOfIntegers.mapRingEquiv
        (((IsCyclotomicExtension.Rat.galEquivZMod m K).symm (a * b)).toRingEquiv) =
        (RingOfIntegers.mapRingEquiv
          (((IsCyclotomicExtension.Rat.galEquivZMod m K).symm b).toRingEquiv)).trans
        (RingOfIntegers.mapRingEquiv
          (((IsCyclotomicExtension.Rat.galEquivZMod m K).symm a).toRingEquiv)) := by
      rw [← RingOfIntegers.mapRingEquiv_trans, map_mul]
      rfl
    simp only [h, ClassGroup.mulEquiv_trans]
    ext r
    rfl

/-- On a pure tensor, the residue acts covariantly on the class factor and leaves the
coefficient unchanged. -/
@[simp] theorem cyclotomicClassAction_tmul (a : (ZMod m)ˣ) (r : R)
    (x : Additive (ClassGroup (𝓞 K))) :
    cyclotomicClassAction R m K a (r ⊗ₜ[ℤ] x) =
      r ⊗ₜ[ℤ] Additive.ofMul
        (ClassGroup.mulEquiv
          (RingOfIntegers.mapRingEquiv
            (((IsCyclotomicExtension.Rat.galEquivZMod m K).symm a).toRingEquiv))
          x.toMul) := by
  rfl

/-- The identity residue acts as the identity linear map. -/
@[simp] theorem cyclotomicClassAction_one : cyclotomicClassAction R m K 1 = 1 :=
  map_one _

/-- Multiplication of residues composes their actions, in the covariant order. -/
theorem cyclotomicClassAction_mul (a b : (ZMod m)ˣ) :
    cyclotomicClassAction R m K (a * b) =
      cyclotomicClassAction R m K a * cyclotomicClassAction R m K b :=
  map_mul _ a b

/-- On the class of a nonzero integral ideal, the action is extension along the integer-ring
automorphism induced by `σ_a`. -/
theorem cyclotomicClassAction_tmul_mk0 (a : (ZMod m)ˣ) (r : R) (I : (Ideal (𝓞 K))⁰) :
    cyclotomicClassAction R m K a (r ⊗ₜ[ℤ] Additive.ofMul (ClassGroup.mk0 I)) =
      r ⊗ₜ[ℤ] Additive.ofMul
        (ClassGroup.mk0 ⟨I.1.map
          (RingOfIntegers.mapRingEquiv
            (((IsCyclotomicExtension.Rat.galEquivZMod m K).symm a).toRingEquiv)),
          mem_nonZeroDivisors_iff_ne_zero.mpr
            ((Ideal.map_eq_bot_iff_of_injective (RingEquiv.injective _)).not.mpr
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2))⟩) := by
  simp only [cyclotomicClassAction_tmul, toMul_ofMul, ClassGroup.mulEquiv_mk0]

end TauCeti
