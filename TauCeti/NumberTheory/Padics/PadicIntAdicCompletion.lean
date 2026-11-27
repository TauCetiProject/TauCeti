/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import TauCeti.Data.ZMod.Quotient.Ring
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

* `PadicInt.adicCompletionRingEquiv p`: `ℤ_[p] ≃+* AdicCompletion (Ideal.span {(p : ℤ)}) ℤ`.
* `PadicInt.tensorAdicCompletionEquiv p M`: `ℤ_[p] ⊗[ℤ] M ≃ₗ[ℤ] AdicCompletion (p) M` for a
  finitely generated abelian group `M`.

## Main results

* `PadicInt.evalₐ_adicCompletionRingEquiv`: the residue of the image of `x` modulo `p ^ n` is
  `PadicInt.toZModPow n x`.
* `PadicInt.tensorAdicCompletionEquiv_tmul`: `x ⊗ₜ m` is sent to
  `adicCompletionRingEquiv p x • of _ M m`.
* `PadicInt.tensorAdicCompletionEquiv_smul`: the equivalence intertwines multiplication by
  `a ∈ ℤ_[p]` on the left factor with multiplication by `adicCompletionRingEquiv p a`.
-/

public section

open scoped TensorProduct

namespace PadicInt

open AdicCompletion

variable (p : ℕ) [Fact p.Prime]

/-- The reductions `ℤ_[p] → ZMod (p ^ n) ≃ ℤ ⧸ (p) ^ n` are compatible with the transition maps
`ℤ ⧸ (p) ^ n → ℤ ⧸ (p) ^ m`. -/
private theorem factorPow_comp_toZModPow {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : ℤ)}) hle).comp
        (((Int.quotientSpanNatPowEquivZMod p n).symm : ZMod (p ^ n) →+* _).comp (toZModPow n)) =
      ((Int.quotientSpanNatPowEquivZMod p m).symm : ZMod (p ^ m) →+* _).comp (toZModPow m) := by
  rw [← zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  exact congrArg (fun g : ZMod (p ^ n) →+* _ ↦ g.comp (toZModPow n)) (Subsingleton.elim _ _)

/-- The map `ℤ_[p] → AdicCompletion (p) ℤ`, from the compatible reductions
`ℤ_[p] → ZMod (p ^ n) ≃ ℤ ⧸ (p) ^ n`. -/
private noncomputable def toAdicCompletion : ℤ_[p] →+* AdicCompletion (Ideal.span {(p : ℤ)}) ℤ :=
  liftRingHom _ (fun n ↦ ((Int.quotientSpanNatPowEquivZMod p n).symm : ZMod (p ^ n) →+* _).comp
      (toZModPow n)) (factorPow_comp_toZModPow p)

/-- The map `AdicCompletion (p) ℤ → ℤ_[p]`, from the compatible projections
`AdicCompletion (p) ℤ → ℤ ⧸ (p) ^ n ≃ ZMod (p ^ n)`. -/
private noncomputable def ofAdicCompletion : AdicCompletion (Ideal.span {(p : ℤ)}) ℤ →+* ℤ_[p] :=
  lift (f := fun n ↦ (Int.quotientSpanNatPowEquivZMod p n : _ →+* ZMod (p ^ n)).comp
      (evalₐ (Ideal.span {(p : ℤ)}) n).toRingHom)
    fun m n hle ↦ by
      rw [← (RingHom.ext (factor_evalₐ hle) :
        (Ideal.Quotient.factorPow _ hle).comp (evalₐ _ n).toRingHom = _),
        ← RingHom.comp_assoc, ← RingHom.comp_assoc]
      exact congrArg (fun g : ℤ ⧸ Ideal.span {(p : ℤ)} ^ n →+* ZMod (p ^ m) ↦ g.comp _)
        (Ideal.Quotient.ringHom_ext (RingHom.ext_int _ _))

private theorem evalₐ_toAdicCompletion (n : ℕ) (x : ℤ_[p]) :
    evalₐ _ n (toAdicCompletion p x) =
      (Int.quotientSpanNatPowEquivZMod p n).symm (toZModPow n x) :=
  evalₐ_liftRingHom _ _ (factorPow_comp_toZModPow p) n x

private theorem toZModPow_ofAdicCompletion (n : ℕ) (x : AdicCompletion (Ideal.span {(p : ℤ)}) ℤ) :
    toZModPow n (ofAdicCompletion p x) = Int.quotientSpanNatPowEquivZMod p n (evalₐ _ n x) := by
  rw [← RingHom.comp_apply, ofAdicCompletion, lift_spec]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]

/-- **`ℤ_[p]` is the `p`-adic completion of `ℤ`.** -/
noncomputable def adicCompletionRingEquiv : ℤ_[p] ≃+* AdicCompletion (Ideal.span {(p : ℤ)}) ℤ :=
  RingEquiv.ofRingHom (toAdicCompletion p) (ofAdicCompletion p)
    (RingHom.ext fun x ↦ ext_evalₐ fun n ↦ by
      simp [evalₐ_toAdicCompletion, toZModPow_ofAdicCompletion])
    (RingHom.ext fun x ↦ ext_of_toZModPow.1 fun n ↦ by
      simp [evalₐ_toAdicCompletion, toZModPow_ofAdicCompletion])

/-- The residue modulo `(p) ^ n` of the image of `x` in the `p`-adic completion of `ℤ` is the
residue `toZModPow n x`. -/
@[simp]
theorem evalₐ_adicCompletionRingEquiv (n : ℕ) (x : ℤ_[p]) :
    evalₐ _ n (adicCompletionRingEquiv p x) =
      (Int.quotientSpanNatPowEquivZMod p n).symm (toZModPow n x) :=
  evalₐ_toAdicCompletion p n x

/-- The residue `toZModPow n` of the preimage in `ℤ_[p]` of an element `x` of the `p`-adic
completion of `ℤ` is the image under `ℤ ⧸ (p) ^ n ≃ ZMod (p ^ n)` of its residue modulo
`(p) ^ n`. -/
@[simp]
theorem toZModPow_adicCompletionRingEquiv_symm (n : ℕ)
    (x : AdicCompletion (Ideal.span {(p : ℤ)}) ℤ) :
    toZModPow n ((adicCompletionRingEquiv p).symm x) =
      Int.quotientSpanNatPowEquivZMod p n (evalₐ _ n x) :=
  toZModPow_ofAdicCompletion p n x

/-- **The `p`-adic completion of a finitely generated abelian group `M` is `ℤ_[p] ⊗ M`.** -/
noncomputable def tensorAdicCompletionEquiv (M : Type) [AddCommGroup M] [Module.Finite ℤ M] :
    ℤ_[p] ⊗[ℤ] M ≃ₗ[ℤ] AdicCompletion (Ideal.span {(p : ℤ)}) M :=
  -- Composing as additive equivalences and converting once with `toIntLinearEquiv` gives both
  -- sides the `ℤ`-module structure `AddCommGroup.toIntModule` that the stated type elaborates to.
  ((adicCompletionRingEquiv p).toIntAlgEquiv.toLinearEquiv.rTensor M).toAddEquiv.trans
    (ofTensorProductEquivOfFiniteNoetherian (Ideal.span {(p : ℤ)}) M).toAddEquiv
    |>.toIntLinearEquiv

/-- `tensorAdicCompletionEquiv p M` sends `x ⊗ₜ m` to the image of `x` in the `p`-adic
completion of `ℤ` acting on the image of `m` in the `p`-adic completion of `M`. -/
@[simp]
theorem tensorAdicCompletionEquiv_tmul (M : Type) [AddCommGroup M] [Module.Finite ℤ M]
    (x : ℤ_[p]) (m : M) :
    tensorAdicCompletionEquiv p M (x ⊗ₜ m) = adicCompletionRingEquiv p x • of _ M m := by
  simp [tensorAdicCompletionEquiv, ofTensorProduct_tmul]

/-- `tensorAdicCompletionEquiv p M` is semilinear along `adicCompletionRingEquiv p`: it sends
`a • t` to `adicCompletionRingEquiv p a • tensorAdicCompletionEquiv p M t`. -/
@[simp]
theorem tensorAdicCompletionEquiv_smul (M : Type) [AddCommGroup M] [Module.Finite ℤ M]
    (a : ℤ_[p]) (t : ℤ_[p] ⊗[ℤ] M) :
    tensorAdicCompletionEquiv p M (a • t) =
      adicCompletionRingEquiv p a • tensorAdicCompletionEquiv p M t := by
  induction t using TensorProduct.inductionOn with
  | tmul x m => simp [TensorProduct.smul_tmul', mul_smul]
  | add t u ht hu => rw [smul_add, map_add, ht, hu, map_add, smul_add]

end PadicInt
