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
`C` valued in a complete Hausdorff nonarchimedean module `M` over a topological ring `R` extends
uniquely to `B ⊗̂_A C` (`liftDerivation`), built over `T = B ⊗̂_A C` via `CompletedTensor.lift`
into `TrivSqZeroExt T M` and `TauCeti.derivationToTrivSqZeroExtEquivLift` and restricted to `R`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Definition 1.6.1 and (1.6.2).
-/

public section

open TensorProduct

namespace TauCeti.Huber.CompletedTensor

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
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
  | tmul b c =>
    simp only [Function.comp_apply, toCompletion_tmul, Derivation.leibniz, hB, hC]
  | add x y hx hy =>
    simp only [Function.comp_apply, map_add] at hx hy ⊢
    rw [hx, hy]

section LiftDerivation

/-- Package a continuous `A`-derivation `B → M` as an `A`-algebra map `B →ₐ[A] TrivSqZeroExt T M`
over a compatible `B →+* T`. -/
private noncomputable def mkLiftAlgHom {T M : Type*} [CommRing T] [AddCommGroup M]
    [Algebra A T] [Module A M] [Module B M] [Module T M] [Module Tᵐᵒᵖ M]
    [IsScalarTower A T M] [IsCentralScalar T M]
    (ι : B →+* T) (hι : ∀ a, ι (algebraMap A B a) = algebraMap A T a)
    (hBM : ∀ (b : B) (m : M), ι b • m = b • m) (dB : Derivation A B M) :
    B →ₐ[A] TrivSqZeroExt T M where
  toFun b := TrivSqZeroExt.inl (ι b) + TrivSqZeroExt.inr (dB b)
  map_one' := by ext <;> simp
  map_mul' b₁ b₂ := by
    ext <;> simp [TrivSqZeroExt.snd_mul, op_smul_eq_smul, hBM, add_comm]
  map_zero' := by ext <;> simp
  map_add' b₁ b₂ := by ext <;> simp
  commutes' a := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', hι]

/-- Core derivation extension over `T = B ⊗̂_A C`, requiring completeness and nonarchimedeanness
only on `M` (since `T` is already a complete Hausdorff Huber ring). -/
private noncomputable def liftDerivationBase
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
    { is_nonarchimedean := (inferInstance : NonarchimedeanAddGroup (T × M)).is_nonarchimedean }
  let ψB := mkLiftAlgHom (inl A B C) (inl_algebraMap A B C) hBM dB
  let ψC := mkLiftAlgHom (inr A B C) (inr_algebraMap A B C) hCM dC
  have hψB : Continuous ψB :=
    (TrivSqZeroExt.continuous_inl.comp (continuous_inl A B C)).add
      (TrivSqZeroExt.continuous_inr.comp hdB)
  have hψC : Continuous ψC :=
    (TrivSqZeroExt.continuous_inl.comp (continuous_inr A B C)).add
      (TrivSqZeroExt.continuous_inr.comp hdC)
  have hcomm : ψB.toRingHom.comp (algebraMap A B) = ψC.toRingHom.comp (algebraMap A C) :=
    RingHom.ext fun a ↦ (ψB.commutes a).trans (ψC.commutes a).symm
  let Φ : T →+* TrivSqZeroExt T M :=
    CompletedTensor.lift ψB.toRingHom ψC.toRingHom hcomm hψB hψC
  let Φₐ : T →ₐ[A] TrivSqZeroExt T M :=
    { Φ with
      commutes' a := by
        rw [← inl_algebraMap]
        exact (lift_inl ψB.toRingHom ψC.toRingHom hcomm hψB hψC _).trans (ψB.commutes a) }
  have hfst : (TrivSqZeroExt.fstHom A T M).comp Φₐ = IsScalarTower.toAlgHom A T T := by
    apply AlgHom.toRingHom_injective
    refine CompletedTensor.hom_ext
      (TrivSqZeroExt.continuous_fst.comp (continuous_lift _ _ hcomm hψB hψC)) continuous_id ?_ ?_
    · ext b; simp [Φₐ, Φ, ψB, mkLiftAlgHom]
    · ext c; simp [Φₐ, Φ, ψC, mkLiftAlgHom]
  refine ⟨(TauCeti.derivationToTrivSqZeroExtEquivLift A T T).symm ⟨Φₐ, hfst⟩, ?_, ?_, ?_⟩
  · exact (TrivSqZeroExt.continuous_snd.comp (continuous_lift _ _ hcomm hψB hψC)).congr fun z ↦
      (TauCeti.derivationToTrivSqZeroExtEquivLift_symm_apply ⟨Φₐ, hfst⟩ z).symm
  · intro b
    rw [TauCeti.derivationToTrivSqZeroExtEquivLift_symm_apply]; simp [Φₐ, Φ, ψB, mkLiftAlgHom]
  · intro c
    rw [TauCeti.derivationToTrivSqZeroExtEquivLift_symm_apply]; simp [Φₐ, Φ, ψC, mkLiftAlgHom]

variable {R : Type*} [CommRing R] [TopologicalSpace R]
  [Algebra B R] [Algebra C R] [Algebra (CompletedTensor A B C) R]
  {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [CompleteSpace M] [T0Space M]
  [Module A M] [Module B M] [Module C M] [Module R M] [Module (CompletedTensor A B C) M]
  [IsScalarTower A B M] [IsScalarTower B R M] [IsScalarTower C R M]
  [IsScalarTower (CompletedTensor A B C) R M] [ContinuousSMul R M]

variable (dB : Derivation A B M) (dC : Derivation A C M)
  (hdB : Continuous dB) (hdC : Continuous dC)
  (hcont : Continuous (algebraMap (CompletedTensor A B C) R))
  (hinl : (algebraMap (CompletedTensor A B C) R).comp (inl A B C) = algebraMap B R)
  (hinr : (algebraMap (CompletedTensor A B C) R).comp (inr A B C) = algebraMap C R)

include dB dC hdB hdC hcont hinl hinr

private noncomputable def liftDerivationAux :
    {d : Derivation A (CompletedTensor A B C) M //
      Continuous d ∧ (∀ b, d (inl A B C b) = dB b) ∧ (∀ c, d (inr A B C c) = dC c)} := by
  have hBM (b : B) (m : M) : inl A B C b • m = b • m := by
    rw [← algebraMap_smul R, ← RingHom.comp_apply, hinl, algebraMap_smul]
  have hCM (c : C) (m : M) : inr A B C c • m = c • m := by
    rw [← algebraMap_smul R, ← RingHom.comp_apply, hinr, algebraMap_smul]
  haveI : IsScalarTower A (CompletedTensor A B C) M := ⟨fun a t m ↦ by
    rw [Algebra.smul_def, mul_smul, ← inl_algebraMap, hBM, algebraMap_smul]⟩
  haveI : ContinuousSMul (CompletedTensor A B C) M :=
    ⟨((hcont.comp continuous_fst).smul continuous_snd).congr fun ⟨t, m⟩ ↦ algebraMap_smul R t m⟩
  exact liftDerivationBase hBM hCM dB dC hdB hdC

/-- Extend a pair of continuous `A`-derivations on `B` and `C`, valued in a complete Hausdorff
nonarchimedean module `M` over a topological ring `R`, to a continuous `A`-derivation on
`B ⊗̂_A C` along a continuous algebra map `B ⊗̂_A C → R` compatible with `inl` and `inr`. -/
noncomputable def liftDerivation : Derivation A (CompletedTensor A B C) M :=
  (liftDerivationAux dB dC hdB hdC hcont hinl hinr).val

/-- The derivation extended to `B ⊗̂_A C` is continuous. -/
@[fun_prop] theorem continuous_liftDerivation :
    Continuous (liftDerivation dB dC hdB hdC hcont hinl hinr) :=
  (liftDerivationAux dB dC hdB hdC hcont hinl hinr).property.1

/-- The extended derivation agrees with `dB` on the left coprojection. -/
@[simp] theorem liftDerivation_inl (b : B) :
    liftDerivation dB dC hdB hdC hcont hinl hinr (inl A B C b) = dB b :=
  (liftDerivationAux dB dC hdB hdC hcont hinl hinr).property.2.1 b

/-- The extended derivation agrees with `dC` on the right coprojection. -/
@[simp] theorem liftDerivation_inr (c : C) :
    liftDerivation dB dC hdB hdC hcont hinl hinr (inr A B C c) = dC c :=
  (liftDerivationAux dB dC hdB hdC hcont hinl hinr).property.2.2 c

/-- A continuous `A`-derivation on `B ⊗̂_A C` agreeing with `dB` on `inl` and with `dC` on `inr`
equals `liftDerivation`. -/
theorem eq_liftDerivation {d : Derivation A (CompletedTensor A B C) M} (hd : Continuous d)
    (hB : ∀ b, d (inl A B C b) = dB b) (hC : ∀ c, d (inr A B C c) = dC c) :
    d = liftDerivation dB dC hdB hdC hcont hinl hinr :=
  derivation_ext hd (continuous_liftDerivation ..)
    (fun b ↦ (hB b).trans (liftDerivation_inl .. |>.symm))
    (fun c ↦ (hC c).trans (liftDerivation_inr .. |>.symm))

/-- There is a unique continuous `A`-derivation on `B ⊗̂_A C` extending a pair of continuous
`A`-derivations on `B` and `C`. -/
theorem existsUnique_liftDerivation :
    ∃! d : Derivation A (CompletedTensor A B C) M,
      Continuous d ∧ (∀ b, d (inl A B C b) = dB b) ∧ (∀ c, d (inr A B C c) = dC c) :=
  ⟨liftDerivation dB dC hdB hdC hcont hinl hinr,
    ⟨continuous_liftDerivation .., fun _ ↦ liftDerivation_inl .., fun _ ↦ liftDerivation_inr ..⟩,
    fun _ ⟨hd, hB, hC⟩ ↦ eq_liftDerivation dB dC hdB hdC hcont hinl hinr hd hB hC⟩

end LiftDerivation

end TauCeti.Huber.CompletedTensor
