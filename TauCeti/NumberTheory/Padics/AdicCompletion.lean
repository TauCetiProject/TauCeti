/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.Data.ZMod.QuotientRing
public import TauCeti.RingTheory.AdicCompletion.AlgHom

/-!
# The `p`-adic integers are the `p`-adic completion of `ℤ`

The ring `ℤ_[p]` is the `(p)`-adic completion `AdicCompletion (Ideal.span {(p : ℤ)}) ℤ` of the
integers: both are the inverse limit of the rings `ℤ ⧸ (p ^ n) = ZMod (p ^ n)`. The ring
equivalence `PadicInt.adicCompletionRingEquiv` is assembled from the universal properties of the
two sides, Mathlib's `PadicInt.lift` and `AdicCompletion.liftRingHom`. Combined with Mathlib's
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`, it identifies the `p`-adic completion of
a finitely generated abelian group `M` with `ℤ_[p] ⊗ M` (`PadicInt.tensorAdicCompletionEquiv`).

## Main definitions

* `Int.quotientSpanNatPowEquivZMod p n`: `ℤ ⧸ (p) ^ n ≃+* ZMod (p ^ n)`.
* `PadicInt.adicCompletionRingEquiv p`: `ℤ_[p] ≃+* AdicCompletion (Ideal.span {(p : ℤ)}) ℤ`.
* `PadicInt.tensorAdicCompletionEquiv p M`: `ℤ_[p] ⊗[ℤ] M ≃ₗ[ℤ] AdicCompletion (p) M` for a
  finitely generated abelian group `M`.

## Main results

* `PadicInt.evalₐ_adicCompletionRingEquiv`: the residue of the image of `x` modulo `p ^ n` is
  `PadicInt.toZModPow n x`.
-/

public section

open scoped TensorProduct

namespace Int

/-- The residue rings of the `(p)`-adic filtration of `ℤ`: `ℤ ⧸ (p) ^ n ≃+* ZMod (p ^ n)`. -/
noncomputable def quotientSpanNatPowEquivZMod (p n : ℕ) :
    ℤ ⧸ Ideal.span {(p : ℤ)} ^ n ≃+* ZMod (p ^ n) :=
  (Ideal.quotEquivOfEq (by rw [Ideal.span_singleton_pow, Nat.cast_pow])).trans
    (Int.quotientSpanNatEquivZMod (p ^ n))

end Int

namespace PadicInt

open AdicCompletion

variable (p : ℕ) [Fact p.Prime]

/-- The reductions `ℤ_[p] → ZMod (p ^ n) ≃ ℤ ⧸ (p) ^ n` are compatible with the transition maps
`ℤ ⧸ (p) ^ n → ℤ ⧸ (p) ^ m`. -/
theorem factorPow_comp_toZModPow {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : ℤ)}) hle).comp
        (((Int.quotientSpanNatPowEquivZMod p n).symm : ZMod (p ^ n) →+* _).comp (toZModPow n)) =
      ((Int.quotientSpanNatPowEquivZMod p m).symm : ZMod (p ^ m) →+* _).comp (toZModPow m) := by
  rw [← zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  exact congrArg (fun g : ZMod (p ^ n) →+* _ ↦ g.comp (toZModPow n)) (Subsingleton.elim _ _)

/-- The map `ℤ_[p] → AdicCompletion (p) ℤ`, from the compatible reductions
`ℤ_[p] → ZMod (p ^ n) ≃ ℤ ⧸ (p) ^ n`. -/
noncomputable def toAdicCompletion : ℤ_[p] →+* AdicCompletion (Ideal.span {(p : ℤ)}) ℤ :=
  liftRingHom _ (fun n ↦ ((Int.quotientSpanNatPowEquivZMod p n).symm : ZMod (p ^ n) →+* _).comp
      (toZModPow n)) (factorPow_comp_toZModPow p)

/-- The map `AdicCompletion (p) ℤ → ℤ_[p]`, from the compatible projections
`AdicCompletion (p) ℤ → ℤ ⧸ (p) ^ n ≃ ZMod (p ^ n)`. -/
noncomputable def ofAdicCompletion : AdicCompletion (Ideal.span {(p : ℤ)}) ℤ →+* ℤ_[p] :=
  lift (f := fun n ↦ (Int.quotientSpanNatPowEquivZMod p n : _ →+* ZMod (p ^ n)).comp
      (evalₐ (Ideal.span {(p : ℤ)}) n).toRingHom)
    fun m n hle ↦ by
      rw [← (RingHom.ext (factor_evalₐ hle) :
        (Ideal.Quotient.factorPow _ hle).comp (evalₐ _ n).toRingHom = _),
        ← RingHom.comp_assoc, ← RingHom.comp_assoc]
      exact congrArg (fun g : ℤ ⧸ Ideal.span {(p : ℤ)} ^ n →+* ZMod (p ^ m) ↦ g.comp _)
        (Ideal.Quotient.ringHom_ext (RingHom.ext_int _ _))

@[simp]
theorem evalₐ_toAdicCompletion (n : ℕ) (x : ℤ_[p]) :
    evalₐ _ n (toAdicCompletion p x) =
      (Int.quotientSpanNatPowEquivZMod p n).symm (toZModPow n x) :=
  evalₐ_liftRingHom _ _ (factorPow_comp_toZModPow p) n x

@[simp]
theorem toZModPow_ofAdicCompletion (n : ℕ) (x : AdicCompletion (Ideal.span {(p : ℤ)}) ℤ) :
    toZModPow n (ofAdicCompletion p x) = Int.quotientSpanNatPowEquivZMod p n (evalₐ _ n x) := by
  rw [← RingHom.comp_apply, ofAdicCompletion, lift_spec]
  rfl

/-- **`ℤ_[p]` is the `p`-adic completion of `ℤ`.** -/
noncomputable def adicCompletionRingEquiv : ℤ_[p] ≃+* AdicCompletion (Ideal.span {(p : ℤ)}) ℤ :=
  RingEquiv.ofRingHom (toAdicCompletion p) (ofAdicCompletion p)
    (RingHom.ext fun x ↦ ext_evalₐ fun n ↦ by simp)
    (RingHom.ext fun x ↦ ext_of_toZModPow.1 fun n ↦ by simp)

/-- The residue modulo `(p) ^ n` of the image of `x` in the `p`-adic completion of `ℤ` is the
residue `toZModPow n x`. -/
@[simp]
theorem evalₐ_adicCompletionRingEquiv (n : ℕ) (x : ℤ_[p]) :
    evalₐ _ n (adicCompletionRingEquiv p x) =
      (Int.quotientSpanNatPowEquivZMod p n).symm (toZModPow n x) :=
  evalₐ_toAdicCompletion p n x

@[simp]
theorem toZModPow_adicCompletionRingEquiv_symm (n : ℕ)
    (x : AdicCompletion (Ideal.span {(p : ℤ)}) ℤ) :
    toZModPow n ((adicCompletionRingEquiv p).symm x) =
      Int.quotientSpanNatPowEquivZMod p n (evalₐ _ n x) :=
  toZModPow_ofAdicCompletion p n x

/-- **The `p`-adic completion of a finitely generated abelian group `M` is `ℤ_[p] ⊗ M`.** -/
noncomputable def tensorAdicCompletionEquiv (M : Type) [AddCommGroup M] [Module.Finite ℤ M] :
    ℤ_[p] ⊗[ℤ] M ≃ₗ[ℤ] AdicCompletion (Ideal.span {(p : ℤ)}) M :=
  ((adicCompletionRingEquiv p).toAddEquiv.toIntLinearEquiv.rTensor M).trans
    (ofTensorProductEquivOfFiniteNoetherian (Ideal.span {(p : ℤ)}) M).toAddEquiv.toIntLinearEquiv

end PadicInt
