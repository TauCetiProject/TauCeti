/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegerGrading
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Twisted derivations of an exterior algebra

Given a commutative `k`-algebra `S`, an `S`-module `M`, and an `S`-algebra endomorphism
`σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M`, a `σ`-twisted derivation of
`ExteriorAlgebra S M` over `k` is a `k`-linear endomorphism `D` obeying the `σ`-Leibniz rule

`D (x * y) = D x * y + σ x * D y`.

Both ordinary (`σ = AlgHom.id S _`) and graded odd (`σ = CliffordAlgebra.involute`) derivations on
exterior algebras have this shape. Following Bourbaki (*Algebra*, Chapter III, §10), any compatible
pair consisting of a `k`-derivation `d₀ : Derivation k S (ExteriorAlgebra S M)` in degree zero and
a `k`-linear map `d₁ : M →ₗ[k] ExteriorAlgebra S M` in degree one extends uniquely to a `σ`-twisted
`k`-linear derivation `liftTwistedDerivation` of `ExteriorAlgebra S M`.

## Main definitions

* `ExteriorAlgebra.liftTwistedDerivation`: extends a compatible pair `(d₀, d₁)` to a
  `σ`-twisted `k`-linear derivation of `ExteriorAlgebra S M`.

## Main results

* `ExteriorAlgebra.liftTwistedDerivation_algebraMap`,
  `ExteriorAlgebra.liftTwistedDerivation_ι`: action on scalars from `S` and generators from `M`.
* `ExteriorAlgebra.liftTwistedDerivation_mul`,
  `ExteriorAlgebra.liftTwistedDerivation_smul`: the `σ`-Leibniz and `S`-scalar Leibniz rules.
* `ExteriorAlgebra.liftTwistedDerivation_unique`: uniqueness of a `σ`-twisted derivation
  from its values on `S` and `M`.
* `ExteriorAlgebra.liftTwistedDerivation_mem_integerGrading`,
  `ExteriorAlgebra.liftTwistedDerivation_mem_exteriorPower`: grading-shift preservation
  when `σ` preserves degree one, `d₀` has degree `r`, and `d₁` has degree `r + 1`.
* `ExteriorAlgebra.map_ιMulti_of_leibniz`: an untwisted Leibniz map extending a linear map `A` of
  `M` acts on `v₀ ∧ ⋯ ∧ vₙ₋₁` as `∑ⱼ v₀ ∧ ⋯ ∧ A vⱼ ∧ ⋯ ∧ vₙ₋₁`.

## Implementation notes

We reuse Mathlib's `TrivSqZeroExt` over a private bimodule wrapper `TwistedMod σ d₀ hd₀` on
`ExteriorAlgebra S M`, equipped with the `σ`-twisted left action `a •> m = σ a * m` and the
ordinary right action `m <• b = m * b` (without an `SMul S` instance, so `TrivSqZeroExt.algebra'`
cannot fire). Equipping `TrivSqZeroExt (ExteriorAlgebra S M) (TwistedMod σ d₀ hd₀)` with the
derivation-twisted `Algebra S` structure `s ↦ (s, d₀ s)` and applying `ExteriorAlgebra.lift` to
`m ↦ (ι m, d₁ m)` produces an `S`-algebra homomorphism whose first projection is the identity and
whose second projection is `liftTwistedDerivation`.

## References

* N. Bourbaki, *Algebra*, Chapter III, §10.
-/

public section

namespace ExteriorAlgebra

open TauCeti.ExteriorAlgebra

variable {k S M : Type*} [CommSemiring k] [CommRing S] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]

/-- Private bimodule wrapper on `ExteriorAlgebra S M` carrying the `σ`-twisted left action
`a •> m = σ a * m` and ordinary right multiplication `m <• b = m * b`, omitting `SMul S` so that
`TrivSqZeroExt.algebra'` cannot fire. The phantom parameters `_d₀` and `_hd₀` index the twisted
`Algebra S` structure on `TrivSqZeroExt (ExteriorAlgebra S M) (TwistedMod σ d₀ hd₀)`. -/
private def TwistedMod (_σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (_d₀ : Derivation k S (ExteriorAlgebra S M))
    (_hd₀ : ∀ (s : S) (m : M),
      _d₀ s * ExteriorAlgebra.ι S m = _σ (ExteriorAlgebra.ι S m) * _d₀ s) : Type _ :=
  ExteriorAlgebra S M

section TwistedDual

variable {σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M}
  {d₀ : Derivation k S (ExteriorAlgebra S M)}
  {hd₀ : ∀ (s : S) (m : M),
    d₀ s * ExteriorAlgebra.ι S m = σ (ExteriorAlgebra.ι S m) * d₀ s}

private noncomputable instance : AddCommGroup (TwistedMod σ d₀ hd₀) :=
  inferInstanceAs (AddCommGroup (ExteriorAlgebra S M))

private noncomputable instance : Module (ExteriorAlgebra S M) (TwistedMod σ d₀ hd₀) :=
  Module.compHom (ExteriorAlgebra S M) σ.toRingHom

private noncomputable instance : Module (ExteriorAlgebra S M)ᵐᵒᵖ (TwistedMod σ d₀ hd₀) :=
  inferInstanceAs (Module (ExteriorAlgebra S M)ᵐᵒᵖ (ExteriorAlgebra S M))

private instance :
    SMulCommClass (ExteriorAlgebra S M) (ExteriorAlgebra S M)ᵐᵒᵖ (TwistedMod σ d₀ hd₀) where
  smul_comm a b m := (mul_assoc (σ a) m b.unop).symm

/-- Additive equivalence identifying `ExteriorAlgebra S M` with `TwistedMod σ d₀ hd₀`. -/
private noncomputable def toTwistedMod (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (m : M),
      d₀ s * ExteriorAlgebra.ι S m = σ (ExteriorAlgebra.ι S m) * d₀ s) :
    ExteriorAlgebra S M ≃+ TwistedMod σ d₀ hd₀ :=
  AddEquiv.refl (ExteriorAlgebra S M)

@[simp]
private theorem toTwistedMod_symm_smul (a : ExteriorAlgebra S M) (m : TwistedMod σ d₀ hd₀) :
    (toTwistedMod σ d₀ hd₀).symm (a • m) = σ a * (toTwistedMod σ d₀ hd₀).symm m := rfl

@[simp]
private theorem toTwistedMod_symm_op_smul (b : ExteriorAlgebra S M) (m : TwistedMod σ d₀ hd₀) :
    (toTwistedMod σ d₀ hd₀).symm (MulOpposite.op b • m) =
      (toTwistedMod σ d₀ hd₀).symm m * b := rfl

private theorem hd₀_all
    (hd₀ : ∀ (s : S) (m : M),
      d₀ s * ExteriorAlgebra.ι S m = σ (ExteriorAlgebra.ι S m) * d₀ s)
    (s : S) (x : ExteriorAlgebra S M) :
    d₀ s * x = σ x * d₀ s := by
  induction x using CliffordAlgebra.induction with
  | algebraMap t => rw [AlgHom.commutes, Algebra.commutes]
  | ι m => exact hd₀ s m
  | mul x y ihx ihy => rw [← mul_assoc, ihx, mul_assoc, ihy, ← mul_assoc, map_mul]
  | add x y ihx ihy => rw [mul_add, ihx, ihy, map_add, add_mul]

private noncomputable def twistedDualRingHom :
    S →+* TrivSqZeroExt (ExteriorAlgebra S M) (TwistedMod σ d₀ hd₀) where
  toFun s := TrivSqZeroExt.inl (algebraMap S _ s) +
    TrivSqZeroExt.inr (toTwistedMod σ d₀ hd₀ (d₀ s))
  map_one' := by
    ext
    · simp
    · apply (toTwistedMod σ d₀ hd₀).symm.injective
      simp
  map_mul' s t := by
    ext
    · simp
    · apply (toTwistedMod σ d₀ hd₀).symm.injective
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        add_zero, map_add, toTwistedMod_symm_smul, toTwistedMod_symm_op_smul,
        AddEquiv.symm_apply_apply, d₀.leibniz, AlgHom.commutes]
      rw [← Algebra.commutes t (d₀ s), ← Algebra.smul_def, ← Algebra.smul_def]
  map_zero' := by
    ext
    · simp
    · apply (toTwistedMod σ d₀ hd₀).symm.injective
      simp
  map_add' s t := by
    ext
    · simp
    · apply (toTwistedMod σ d₀ hd₀).symm.injective
      simp

private noncomputable instance instAlgebraTwistedDual :
    Algebra S (TrivSqZeroExt (ExteriorAlgebra S M) (TwistedMod σ d₀ hd₀)) :=
  (twistedDualRingHom (σ := σ) (d₀ := d₀) (hd₀ := hd₀)).toAlgebra' fun s z ↦ by
    ext
    · simp [twistedDualRingHom, Algebra.commutes]
    · apply (toTwistedMod σ d₀ hd₀).symm.injective
      simp only [twistedDualRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        add_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        map_add, toTwistedMod_symm_smul, toTwistedMod_symm_op_smul, AddEquiv.symm_apply_apply]
      rw [hd₀_all hd₀ s z.fst, AlgHom.commutes,
        Algebra.commutes s ((toTwistedMod σ d₀ hd₀).symm z.snd), add_comm]

private theorem twistedDual_algebraMap :
    algebraMap S (TrivSqZeroExt (ExteriorAlgebra S M) (TwistedMod σ d₀ hd₀)) =
      twistedDualRingHom (σ := σ) (d₀ := d₀) (hd₀ := hd₀) :=
  RingHom.algebraMap_toAlgebra' _ _

private theorem twistedDual_algebraMap_fst (s : S) :
    (algebraMap S (TrivSqZeroExt (ExteriorAlgebra S M) (TwistedMod σ d₀ hd₀)) s).fst =
      algebraMap S (ExteriorAlgebra S M) s := by
  rw [twistedDual_algebraMap]
  simp [twistedDualRingHom]

private theorem twistedDual_algebraMap_snd (s : S) :
    (toTwistedMod σ d₀ hd₀).symm
        (algebraMap S (TrivSqZeroExt (ExteriorAlgebra S M) (TwistedMod σ d₀ hd₀)) s).snd =
      d₀ s := by
  rw [twistedDual_algebraMap]
  simp [twistedDualRingHom]

private theorem twistedDual_smul_snd (s : S)
    (z : TrivSqZeroExt (ExteriorAlgebra S M) (TwistedMod σ d₀ hd₀)) :
    (toTwistedMod σ d₀ hd₀).symm (s • z).snd =
      σ (algebraMap S (ExteriorAlgebra S M) s) * (toTwistedMod σ d₀ hd₀).symm z.snd +
        d₀ s * z.fst := by
  rw [Algebra.smul_def, TrivSqZeroExt.snd_mul, map_add, toTwistedMod_symm_smul,
    toTwistedMod_symm_op_smul, twistedDual_algebraMap_fst, twistedDual_algebraMap_snd]

private noncomputable def twistedDualGenerator (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m) :
    M →ₗ[S] TrivSqZeroExt (ExteriorAlgebra S M) (TwistedMod σ d₀ hd₀) where
  toFun m := TrivSqZeroExt.inl (ExteriorAlgebra.ι S m) +
    TrivSqZeroExt.inr (toTwistedMod σ d₀ hd₀ (d₁ m))
  map_add' m₁ m₂ := by
    ext
    · simp
    · apply (toTwistedMod σ d₀ hd₀).symm.injective
      simp
  map_smul' s m := by
    ext
    · simp [twistedDual_algebraMap_fst, Algebra.smul_def]
    · apply (toTwistedMod σ d₀ hd₀).symm.injective
      simp [twistedDual_algebraMap_fst, twistedDual_algebraMap_snd, hsmul, AlgHom.commutes,
        Algebra.smul_def, add_comm]

private noncomputable def twistedDualLift (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0) :
    ExteriorAlgebra S M →ₐ[S] TrivSqZeroExt (ExteriorAlgebra S M) (TwistedMod σ d₀ hd₀) :=
  ExteriorAlgebra.lift S
    ⟨twistedDualGenerator (σ := σ) (d₀ := d₀) (hd₀ := hd₀) d₁ hsmul, fun m ↦ by
      ext
      · simp [twistedDualGenerator]
      · apply (toTwistedMod σ d₀ hd₀).symm.injective
        simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_zero, map_add, map_zero,
          toTwistedMod_symm_smul, toTwistedMod_symm_op_smul, twistedDualGenerator,
          LinearMap.coe_mk, AddHom.coe_mk, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
          TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
          TrivSqZeroExt.snd_inr, zero_add, AddEquiv.symm_apply_apply]
        rw [add_comm]
        exact hsq m⟩

private noncomputable def twistedDualFstAlgHom :
    TrivSqZeroExt (ExteriorAlgebra S M) (TwistedMod σ d₀ hd₀) →ₐ[S] ExteriorAlgebra S M where
  toFun := TrivSqZeroExt.fst
  map_one' := TrivSqZeroExt.fst_one
  map_mul' := TrivSqZeroExt.fst_mul
  map_zero' := TrivSqZeroExt.fst_zero
  map_add' := TrivSqZeroExt.fst_add
  commutes' := twistedDual_algebraMap_fst

private theorem twistedDualLift_fst (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    (x : ExteriorAlgebra S M) :
    (twistedDualLift (σ := σ) (d₀ := d₀) (hd₀ := hd₀) d₁ hsmul hsq x).fst = x := by
  have h : (twistedDualFstAlgHom (σ := σ) (d₀ := d₀) (hd₀ := hd₀)).comp
      (twistedDualLift (σ := σ) (d₀ := d₀) (hd₀ := hd₀) d₁ hsmul hsq) = AlgHom.id S _ :=
    ExteriorAlgebra.hom_ext <| LinearMap.ext fun m ↦ by
      simp [twistedDualLift, twistedDualFstAlgHom, twistedDualGenerator]
  simpa [twistedDualFstAlgHom] using AlgHom.congr_fun h x

end TwistedDual

/-- **Extension of a compatible `(d₀, d₁)` pair to a `σ`-twisted derivation of
`ExteriorAlgebra S M`**: given an `S`-algebra endomorphism `σ` of `ExteriorAlgebra S M`, a
`k`-derivation `d₀ : Derivation k S (ExteriorAlgebra S M)` satisfying
`d₀ s * ι S m = σ (ι S m) * d₀ s` on generators `m : M`, and a `k`-linear map
`d₁ : M →ₗ[k] ExteriorAlgebra S M` satisfying `d₁ (s • m) = d₀ s * ι m + s • d₁ m` and
`d₁ m * ι m + σ (ι m) * d₁ m = 0`, `liftTwistedDerivation` is the `k`-linear endomorphism of
`ExteriorAlgebra S M` extending `d₀` on `S` and `d₁` on `M` and obeying
`D (x * y) = D x * y + σ x * D y`. -/
noncomputable def liftTwistedDerivation (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (m : M),
      d₀ s * ExteriorAlgebra.ι S m = σ (ExteriorAlgebra.ι S m) * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0) :
    ExteriorAlgebra S M →ₗ[k] ExteriorAlgebra S M where
  toFun x :=
    (toTwistedMod σ d₀ hd₀).symm
      (twistedDualLift (σ := σ) (d₀ := d₀) (hd₀ := hd₀) d₁ hsmul hsq x).snd
  map_add' x y := by rw [map_add, TrivSqZeroExt.snd_add, map_add]
  map_smul' c x := by
    rw [← IsScalarTower.algebraMap_smul S c x, AlgHom.map_smul_of_tower,
      twistedDual_smul_snd, Derivation.map_algebraMap, zero_mul, add_zero,
      AlgHom.commutes, ← Algebra.smul_def, IsScalarTower.algebraMap_smul, RingHom.id_apply]

private theorem liftTwistedDerivation_apply (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (m : M),
      d₀ s * ExteriorAlgebra.ι S m = σ (ExteriorAlgebra.ι S m) * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    (x : ExteriorAlgebra S M) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq x =
      (toTwistedMod σ d₀ hd₀).symm
        (twistedDualLift (σ := σ) (d₀ := d₀) (hd₀ := hd₀) d₁ hsmul hsq x).snd := rfl

/-- On scalars `algebraMap S _ s`, `liftTwistedDerivation` acts by `d₀`. -/
@[simp]
theorem liftTwistedDerivation_algebraMap (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (m : M),
      d₀ s * ExteriorAlgebra.ι S m = σ (ExteriorAlgebra.ι S m) * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    (s : S) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq (algebraMap S (ExteriorAlgebra S M) s) = d₀ s := by
  rw [liftTwistedDerivation_apply, AlgHom.commutes, twistedDual_algebraMap_snd]

/-- `liftTwistedDerivation` annihilates `1`. -/
@[simp]
theorem liftTwistedDerivation_one (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (m : M),
      d₀ s * ExteriorAlgebra.ι S m = σ (ExteriorAlgebra.ι S m) * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq 1 = 0 := by
  rw [← map_one (algebraMap S (ExteriorAlgebra S M)), liftTwistedDerivation_algebraMap,
    Derivation.map_one_eq_zero]

/-- On degree-one generators `ι S m`, `liftTwistedDerivation` acts by `d₁`. -/
@[simp]
theorem liftTwistedDerivation_ι (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (m : M),
      d₀ s * ExteriorAlgebra.ι S m = σ (ExteriorAlgebra.ι S m) * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    (m : M) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq (ExteriorAlgebra.ι S m) = d₁ m := by
  rw [liftTwistedDerivation_apply, twistedDualLift, ExteriorAlgebra.lift_ι_apply]
  simp [twistedDualGenerator]

/-- **The `σ`-twisted Leibniz rule** for `liftTwistedDerivation`. -/
theorem liftTwistedDerivation_mul (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (m : M),
      d₀ s * ExteriorAlgebra.ι S m = σ (ExteriorAlgebra.ι S m) * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    (x y : ExteriorAlgebra S M) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq (x * y) =
      liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq x * y +
        σ x * liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq y := by
  rw [liftTwistedDerivation_apply, map_mul, TrivSqZeroExt.snd_mul, map_add,
    toTwistedMod_symm_smul, toTwistedMod_symm_op_smul, twistedDualLift_fst, twistedDualLift_fst,
    ← liftTwistedDerivation_apply, ← liftTwistedDerivation_apply, add_comm]

/-- Scalar multiplication by `s : S` obeys `D (s • x) = d₀ s * x + s • D x`. -/
@[simp]
theorem liftTwistedDerivation_smul (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (m : M),
      d₀ s * ExteriorAlgebra.ι S m = σ (ExteriorAlgebra.ι S m) * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    (s : S) (x : ExteriorAlgebra S M) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq (s • x) =
      d₀ s * x + s • liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq x := by
  rw [Algebra.smul_def, liftTwistedDerivation_mul, liftTwistedDerivation_algebraMap,
    AlgHom.commutes, ← Algebra.smul_def]

/-- **Uniqueness of `liftTwistedDerivation`**: any `k`-linear map on `ExteriorAlgebra S M` that
extends `d₀` on `S`, extends `d₁` on `M`, and satisfies the `σ`-Leibniz rule equals
`liftTwistedDerivation`. -/
theorem liftTwistedDerivation_unique (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (m : M),
      d₀ s * ExteriorAlgebra.ι S m = σ (ExteriorAlgebra.ι S m) * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    {D : ExteriorAlgebra S M →ₗ[k] ExteriorAlgebra S M}
    (halg : ∀ s : S, D (algebraMap S (ExteriorAlgebra S M) s) = d₀ s)
    (hι : ∀ m : M, D (ExteriorAlgebra.ι S m) = d₁ m)
    (hmul : ∀ x y : ExteriorAlgebra S M, D (x * y) = D x * y + σ x * D y) :
    D = liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq := by
  ext x
  induction x using CliffordAlgebra.induction with
  | algebraMap s => rw [halg, liftTwistedDerivation_algebraMap]
  | ι m => rw [hι, liftTwistedDerivation_ι]
  | mul x y ihx ihy => rw [hmul, liftTwistedDerivation_mul, ihx, ihy]
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]

/-- **Integer grading shift of `liftTwistedDerivation`**: if `σ` sends generators into degree `1`,
`d₀` lands in degree `r : ℤ`, and `d₁` lands in degree `r + 1`, then `liftTwistedDerivation` maps
`integerGrading S M p` into `integerGrading S M (p + r)`. -/
theorem liftTwistedDerivation_mem_integerGrading
    (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (m : M),
      d₀ s * ExteriorAlgebra.ι S m = σ (ExteriorAlgebra.ι S m) * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    {r : ℤ}
    (hσ : ∀ m : M, σ (ExteriorAlgebra.ι S m) ∈ integerGrading S M 1)
    (hd₀_mem : ∀ s : S, d₀ s ∈ integerGrading S M r)
    (hd₁_mem : ∀ m : M, d₁ m ∈ integerGrading S M (r + 1))
    {p : ℤ} {x : ExteriorAlgebra S M} (hx : x ∈ integerGrading S M p) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq x ∈ integerGrading S M (p + r) := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [integerGrading_of_neg hp, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact zero_mem _
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    clear hp
    rw [integerGrading_natCast] at hx
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap s =>
      rw [Nat.cast_zero, zero_add, liftTwistedDerivation_algebraMap]
      exact hd₀_mem s
    | add x y i _ _ ihx ihy =>
      rw [map_add]
      exact add_mem ihx ihy
    | mem_mul m hm i x hx ih =>
      obtain ⟨v, rfl⟩ := hm
      rw [liftTwistedDerivation_mul, liftTwistedDerivation_ι]
      have hx' : x ∈ integerGrading S M (i : ℤ) := by rwa [integerGrading_natCast]
      have h₁ : d₁ v * x ∈ integerGrading S M ((i + 1 : ℕ) + r) := by
        have hi : ((i + 1 : ℕ) : ℤ) + r = (r + 1) + (i : ℤ) := by push_cast; ring
        rw [hi]
        exact SetLike.mul_mem_graded (hd₁_mem v) hx'
      have h₂ : σ (ExteriorAlgebra.ι S v) * liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq x ∈
          integerGrading S M ((i + 1 : ℕ) + r) := by
        have hi : ((i + 1 : ℕ) : ℤ) + r = 1 + ((i : ℤ) + r) := by push_cast; ring
        rw [hi]
        exact SetLike.mul_mem_graded (hσ v) ih
      exact add_mem h₁ h₂

/-- **Exterior-power degree shift of `liftTwistedDerivation`**: if `σ` sends generators into
`⋀[S]^1 M`, `d₀` lands in `⋀[S]^r M`, and `d₁` lands in `⋀[S]^(r + 1) M`, then
`liftTwistedDerivation` maps `⋀[S]^n M` into `⋀[S]^(n + r) M`. -/
theorem liftTwistedDerivation_mem_exteriorPower
    (σ : ExteriorAlgebra S M →ₐ[S] ExteriorAlgebra S M)
    (d₀ : Derivation k S (ExteriorAlgebra S M))
    (hd₀ : ∀ (s : S) (m : M),
      d₀ s * ExteriorAlgebra.ι S m = σ (ExteriorAlgebra.ι S m) * d₀ s)
    (d₁ : M →ₗ[k] ExteriorAlgebra S M)
    (hsmul : ∀ (s : S) (m : M), d₁ (s • m) = d₀ s * ExteriorAlgebra.ι S m + s • d₁ m)
    (hsq : ∀ m : M, d₁ m * ExteriorAlgebra.ι S m + σ (ExteriorAlgebra.ι S m) * d₁ m = 0)
    {r : ℕ}
    (hσ : ∀ m : M, σ (ExteriorAlgebra.ι S m) ∈ ⋀[S]^1 M)
    (hd₀_mem : ∀ s : S, d₀ s ∈ ⋀[S]^r M)
    (hd₁_mem : ∀ m : M, d₁ m ∈ ⋀[S]^(r + 1) M)
    {n : ℕ} {x : ExteriorAlgebra S M} (hx : x ∈ ⋀[S]^n M) :
    liftTwistedDerivation σ d₀ hd₀ d₁ hsmul hsq x ∈ ⋀[S]^(n + r) M := by
  have hx' : x ∈ integerGrading S M (n : ℤ) := by rwa [integerGrading_natCast]
  have hmem := liftTwistedDerivation_mem_integerGrading σ d₀ hd₀ d₁ hsmul hsq (r := (r : ℤ))
    (fun m ↦ by rw [← Nat.cast_one, integerGrading_natCast]; exact hσ m)
    (fun s ↦ by rw [integerGrading_natCast]; exact hd₀_mem s)
    (fun m ↦ by rw [← Nat.cast_add_one, integerGrading_natCast]; exact hd₁_mem m)
    hx'
  rwa [← Nat.cast_add, integerGrading_natCast] at hmem

/-- **A Leibniz map on pure wedges**: if an `S`-linear map `d` of `ExteriorAlgebra S M` obeys the
Leibniz rule `d (x * y) = d x * y + x * d y` and sends each generator `ι S m` to `ι S (A m)`, then
it sends `v₀ ∧ ⋯ ∧ vₙ₋₁` to `∑ⱼ v₀ ∧ ⋯ ∧ A vⱼ ∧ ⋯ ∧ vₙ₋₁`. -/
theorem map_ιMulti_of_leibniz {A : M →ₗ[S] M} {d : ExteriorAlgebra S M →ₗ[S] ExteriorAlgebra S M}
    (hd : ∀ x y, d (x * y) = d x * y + x * d y)
    (hι : ∀ m, d (ExteriorAlgebra.ι S m) = ExteriorAlgebra.ι S (A m)) (n : ℕ) (v : Fin n → M) :
    d (ιMulti S n v) = ∑ j, ιMulti S n (Function.update v j (A (v j))) := by
  induction n with
  | zero => simpa using hd 1 1
  | succ n ih =>
    have h0 (j : Fin n) (x : M) : Function.update v j.succ x 0 = v 0 :=
      Function.update_of_ne (Fin.succ_ne_zero j).symm _ _
    rw [Fin.sum_univ_succ]
    simp only [ιMulti_succ_apply, hd, hι, ih, Function.update_self, h0, Finset.mul_sum]
    simp [Matrix.vecTail, Function.update_comp_eq_of_injective _ (Fin.succ_injective _),
      Function.update_comp_eq_of_forall_ne _ _ Fin.succ_ne_zero]

end ExteriorAlgebra
