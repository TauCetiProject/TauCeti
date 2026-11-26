/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Completion
public import Mathlib.RingTheory.Derivation.Basic

import Mathlib.Topology.Instances.TrivSqZeroExt
import TauCeti.RingTheory.Derivation.TrivSqZeroExt

/-!
# Continuous derivations on the completed tensor ring

Continuous `A`-derivations out of `B ⊗̂_A C` into a Hausdorff space are determined by their values
on `inl` and `inr` (`derivation_ext`). Any compatible pair of continuous `A`-derivations on `B` and
`C` valued in a complete Hausdorff nonarchimedean module extends uniquely to `B ⊗̂_A C`
(`liftDerivation`), lifting both coprojections into `TrivSqZeroExt` via
`Derivation.liftTrivSqZeroExt` and recovering the derivation via
`TauCeti.derivationToTrivSqZeroExtEquivLift`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Definition 1.6.1 and (1.6.2).
-/

public section

open TensorProduct

namespace TauCeti.Huber.CompletedTensor

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- Continuous `A`-derivations out of the completed tensor ring into a Hausdorff space are
determined by their values on the two coprojections. -/
theorem derivation_ext {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [T2Space M]
    [Module A M] [Module (CompletedTensor A B C) M]
    {d₁ d₂ : Derivation A (CompletedTensor A B C) M}
    (hd₁ : Continuous d₁) (hd₂ : Continuous d₂)
    (hB : ∀ b : B, d₁ (inl A B C b) = d₂ (inl A B C b))
    (hC : ∀ c : C, d₁ (inr A B C c) = d₂ (inr A B C c)) : d₁ = d₂ := by
  refine Derivation.coe_injective <|
    (denseRange_toCompletion A B C).equalizer hd₁ hd₂ <| funext fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul b c => simp only [Function.comp_apply, toCompletion_tmul, Derivation.leibniz, hB, hC]
  | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]

section LiftDerivation

private noncomputable def liftDerivationAux
    {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
    [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
    [Module A M] [Module B M] [Module C M] [Module (CompletedTensor A B C) M]
    [IsScalarTower A (CompletedTensor A B C) M] [ContinuousSMul (CompletedTensor A B C) M]
    (hBM : ∀ (b : B) (m : M), inl A B C b • m = b • m)
    (hCM : ∀ (c : C) (m : M), inr A B C c • m = c • m)
    (dB : Derivation A B M) (dC : Derivation A C M)
    (hdB : Continuous dB) (hdC : Continuous dC) :
    {d : Derivation A (CompletedTensor A B C) M //
      Continuous d ∧ (∀ b, d (inl A B C b) = dB b) ∧ (∀ c, d (inr A B C c) = dC c)} := by
  let T := CompletedTensor A B C
  letI : Module Tᵐᵒᵖ M := Module.compHom M ((RingHom.id T).fromOpposite mul_comm)
  letI : IsCentralScalar T M := ⟨fun _ _ ↦ rfl⟩
  haveI : IsScalarTower A Tᵐᵒᵖ M := ⟨fun a r m ↦ smul_assoc a r.unop m⟩
  haveI : ContinuousSMul Tᵐᵒᵖ M :=
    ⟨(MulOpposite.continuous_unop.comp continuous_fst).smul continuous_snd⟩
  letI : NonarchimedeanRing (TrivSqZeroExt T M) :=
    ⟨(inferInstance : NonarchimedeanAddGroup (T × M)).is_nonarchimedean⟩
  let ψB := dB.liftTrivSqZeroExt { toRingHom := inl A B C, commutes' := inl_algebraMap A B C }
    hBM fun b m ↦ by rw [op_smul_eq_smul]; exact hBM b m
  let ψC := dC.liftTrivSqZeroExt { toRingHom := inr A B C, commutes' := inr_algebraMap A B C }
    hCM fun c m ↦ by rw [op_smul_eq_smul]; exact hCM c m
  have hψB : Continuous ψB :=
    ((TrivSqZeroExt.continuous_inl.comp (continuous_inl A B C)).add
      (TrivSqZeroExt.continuous_inr.comp hdB)).congr fun b ↦ by
        dsimp [ψB]
        rw [Derivation.liftTrivSqZeroExt_apply]
        rfl
  have hψC : Continuous ψC :=
    ((TrivSqZeroExt.continuous_inl.comp (continuous_inr A B C)).add
      (TrivSqZeroExt.continuous_inr.comp hdC)).congr fun c ↦ by
        dsimp [ψC]
        rw [Derivation.liftTrivSqZeroExt_apply]
        rfl
  have hcomm : ψB.toRingHom.comp (algebraMap A B) = ψC.toRingHom.comp (algebraMap A C) :=
    RingHom.ext fun a ↦ (ψB.commutes a).trans (ψC.commutes a).symm
  let Φ := CompletedTensor.lift ψB.toRingHom ψC.toRingHom hcomm hψB hψC
  let Φₐ : T →ₐ[A] TrivSqZeroExt T M := { Φ with
    commutes' a := by
      rw [← inl_algebraMap]
      exact (lift_inl ψB.toRingHom ψC.toRingHom hcomm hψB hψC _).trans (ψB.commutes a) }
  have hfst : (TrivSqZeroExt.fstHom A T M).comp Φₐ = IsScalarTower.toAlgHom A T T :=
    AlgHom.toRingHom_injective <| CompletedTensor.hom_ext
      (TrivSqZeroExt.continuous_fst.comp (continuous_lift _ _ hcomm hψB hψC)) continuous_id
      (by ext b; simp [Φₐ, Φ, ψB]) (by ext c; simp [Φₐ, Φ, ψC])
  refine ⟨(TauCeti.derivationToTrivSqZeroExtEquivLift A T T).symm ⟨Φₐ, hfst⟩,
    (TrivSqZeroExt.continuous_snd.comp (continuous_lift _ _ hcomm hψB hψC)).congr fun z ↦
      (TauCeti.derivationToTrivSqZeroExtEquivLift_symm_apply ⟨Φₐ, hfst⟩ z).symm, ?_, ?_⟩
  · intro b; rw [TauCeti.derivationToTrivSqZeroExtEquivLift_symm_apply]
    simp [Φₐ, Φ, ψB]
  · intro c; rw [TauCeti.derivationToTrivSqZeroExtEquivLift_symm_apply]
    simp [Φₐ, Φ, ψC]

section Direct

variable {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
  [Module A M] [Module B M] [Module C M] [Module (CompletedTensor A B C) M]
  [IsScalarTower A (CompletedTensor A B C) M] [ContinuousSMul (CompletedTensor A B C) M]
  (hBM : ∀ (b : B) (m : M), inl A B C b • m = b • m)
  (hCM : ∀ (c : C) (m : M), inr A B C c • m = c • m)
  (dB : Derivation A B M) (dC : Derivation A C M)
  (hdB : Continuous dB) (hdC : Continuous dC)

/-- Extend a pair of continuous `A`-derivations on `B` and `C`, valued in a complete Hausdorff
nonarchimedean module `M` with a continuous `B ⊗̂_A C`-action compatible with `inl` and `inr`,
to a continuous `A`-derivation on `B ⊗̂_A C`. -/
noncomputable def liftDerivation : Derivation A (CompletedTensor A B C) M :=
  (liftDerivationAux hBM hCM dB dC hdB hdC).val

/-- The derivation extended to `B ⊗̂_A C` is continuous. -/
@[fun_prop] theorem continuous_liftDerivation :
    Continuous (liftDerivation hBM hCM dB dC hdB hdC) :=
  (liftDerivationAux hBM hCM dB dC hdB hdC).property.1

/-- The extended derivation agrees with `dB` on the left coprojection. -/
@[simp] theorem liftDerivation_inl (b : B) :
    liftDerivation hBM hCM dB dC hdB hdC (inl A B C b) = dB b :=
  (liftDerivationAux hBM hCM dB dC hdB hdC).property.2.1 b

/-- The extended derivation agrees with `dC` on the right coprojection. -/
@[simp] theorem liftDerivation_inr (c : C) :
    liftDerivation hBM hCM dB dC hdB hdC (inr A B C c) = dC c :=
  (liftDerivationAux hBM hCM dB dC hdB hdC).property.2.2 c

/-- A continuous `A`-derivation on `B ⊗̂_A C` agreeing with `dB` on `inl` and with `dC` on `inr`
equals `liftDerivation`. -/
theorem eq_liftDerivation {d : Derivation A (CompletedTensor A B C) M} (hd : Continuous d)
    (hB : ∀ b, d (inl A B C b) = dB b) (hC : ∀ c, d (inr A B C c) = dC c) :
    d = liftDerivation hBM hCM dB dC hdB hdC :=
  derivation_ext hd (continuous_liftDerivation ..)
    (fun b ↦ (hB b).trans (liftDerivation_inl .. |>.symm))
    (fun c ↦ (hC c).trans (liftDerivation_inr .. |>.symm))

section
include hBM hCM hdB hdC

/-- There is a unique continuous `A`-derivation on `B ⊗̂_A C` extending a pair of continuous
`A`-derivations on `B` and `C`. -/
theorem existsUnique_liftDerivation :
    ∃! d : Derivation A (CompletedTensor A B C) M,
      Continuous d ∧ (∀ b, d (inl A B C b) = dB b) ∧ (∀ c, d (inr A B C c) = dC c) :=
  ⟨liftDerivation hBM hCM dB dC hdB hdC,
    ⟨continuous_liftDerivation ..,
      fun _ ↦ liftDerivation_inl .., fun _ ↦ liftDerivation_inr ..⟩,
    fun _ ⟨hd, hB, hC⟩ ↦ eq_liftDerivation hBM hCM dB dC hdB hdC hd hB hC⟩

end

end Direct

section OfAlgebraMap

variable {R : Type*} [CommRing R] [TopologicalSpace R]
  [Algebra B R] [Algebra C R] [Algebra (CompletedTensor A B C) R]
  {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
  [Module A M] [Module B M] [Module C M] [Module R M] [Module (CompletedTensor A B C) M]
  [IsScalarTower A B M] [IsScalarTower B R M] [IsScalarTower C R M]
  [IsScalarTower (CompletedTensor A B C) R M] [ContinuousSMul R M]
  (dB : Derivation A B M) (dC : Derivation A C M) (hdB : Continuous dB)
  (hdC : Continuous dC) (hcont : Continuous (algebraMap (CompletedTensor A B C) R))
  (hinl : (algebraMap (CompletedTensor A B C) R).comp (inl A B C) = algebraMap B R)
  (hinr : (algebraMap (CompletedTensor A B C) R).comp (inr A B C) = algebraMap C R)

private noncomputable def liftDerivationOfAlgebraMapAux :
    {d : Derivation A (CompletedTensor A B C) M //
      Continuous d ∧ (∀ b, d (inl A B C b) = dB b) ∧ (∀ c, d (inr A B C c) = dC c)} :=
  have hBM : ∀ (b : B) (m : M), inl A B C b • m = b • m := fun b m ↦ by
    rw [← algebraMap_smul R, ← RingHom.comp_apply, hinl, algebraMap_smul]
  have hCM : ∀ (c : C) (m : M), inr A B C c • m = c • m := fun c m ↦ by
    rw [← algebraMap_smul R, ← RingHom.comp_apply, hinr, algebraMap_smul]
  haveI : IsScalarTower A (CompletedTensor A B C) M := ⟨fun a t m ↦ by
    rw [Algebra.smul_def, mul_smul, ← inl_algebraMap, hBM, algebraMap_smul]⟩
  haveI : ContinuousSMul (CompletedTensor A B C) M :=
    ⟨((hcont.comp continuous_fst).smul continuous_snd).congr
      fun ⟨t, m⟩ ↦ algebraMap_smul R t m⟩
  ⟨liftDerivation hBM hCM dB dC hdB hdC, continuous_liftDerivation ..,
    fun _ ↦ liftDerivation_inl .., fun _ ↦ liftDerivation_inr ..⟩

/-- Extend a pair of continuous `A`-derivations on `B` and `C`, valued in a complete Hausdorff
nonarchimedean module `M` over a topological ring `R`, to a continuous `A`-derivation on
`B ⊗̂_A C` along a continuous algebra map `B ⊗̂_A C → R` compatible with `inl` and `inr`. -/
noncomputable def liftDerivationOfAlgebraMap : Derivation A (CompletedTensor A B C) M :=
  (liftDerivationOfAlgebraMapAux dB dC hdB hdC hcont hinl hinr).val

/-- The scalar-restricted derivation extended to `B ⊗̂_A C` is continuous. -/
@[fun_prop] theorem continuous_liftDerivationOfAlgebraMap :
    Continuous (liftDerivationOfAlgebraMap dB dC hdB hdC hcont hinl hinr) :=
  (liftDerivationOfAlgebraMapAux dB dC hdB hdC hcont hinl hinr).property.1

/-- The scalar-restricted extended derivation agrees with `dB` on the left coprojection. -/
@[simp] theorem liftDerivationOfAlgebraMap_inl (b : B) :
    liftDerivationOfAlgebraMap dB dC hdB hdC hcont hinl hinr (inl A B C b) = dB b :=
  (liftDerivationOfAlgebraMapAux dB dC hdB hdC hcont hinl hinr).property.2.1 b

/-- The scalar-restricted extended derivation agrees with `dC` on the right coprojection. -/
@[simp] theorem liftDerivationOfAlgebraMap_inr (c : C) :
    liftDerivationOfAlgebraMap dB dC hdB hdC hcont hinl hinr (inr A B C c) = dC c :=
  (liftDerivationOfAlgebraMapAux dB dC hdB hdC hcont hinl hinr).property.2.2 c

end OfAlgebraMap

end LiftDerivation

end TauCeti.Huber.CompletedTensor
