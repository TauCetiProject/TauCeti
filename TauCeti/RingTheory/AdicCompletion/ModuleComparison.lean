/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.UniformCompletion
public import TauCeti.RingTheory.Huber.Adic
public import TauCeti.RingTheory.Huber.ModuleTopology.Completion
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Uniform and adic completions of finite modules

For a finite module `M` over a noetherian adic ring `R`, its separated uniform completion
is linearly isomorphic to its algebraic adic completion. The module has its natural topology;
neither the ring nor the module is assumed separated or complete.

Both completions are scalar extension: `Huber.PairOfDefinition.ofTensorProductEquiv` gives
`M̂ ≃ R̂ ⊗[R] M` and Mathlib's `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` gives
the analogous algebraic statement. The comparison of the completed rings identifies the
scalars. The resulting equivalence sends each original element to its compatible residue
classes. This is useful for computing reductions of completed defining lattices.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, Lemma 2.3(iii).
-/

public section

open TensorProduct UniformSpace

namespace IsAdic

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  {I : Ideal R} {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
  [UniformSpace M] [IsUniformAddGroup M] [IsModuleTopology R M]

local instance : UniformContinuousConstSMul R M :=
  uniformContinuousConstSMul_of_continuousConstSMul R M

/-- The separated completion of a finite naturally topologised module over a noetherian
adic ring is its algebraic adic completion. -/
noncomputable def completionModuleEquivAdicCompletion (hI : IsAdic I) :
    Completion M ≃ₗ[R] AdicCompletion I M :=
  let hfg : I.FG := IsNoetherian.noetherian I
  let P := TauCeti.Huber.PairOfDefinition.adic I hI hfg
  haveI : IsNoetherianRing P.ringOfDefinition := by
    dsimp only [P]
    rw [TauCeti.Huber.PairOfDefinition.adic_ringOfDefinition]
    exact isNoetherianRing_of_ringEquiv R Subring.topEquiv.symm
  let e : Completion R ≃ₐ[R] AdicCompletion I R :=
    AlgEquiv.ofRingEquiv (f := hI.completionEquivAdicCompletion hfg)
      fun r ↦ hI.completionEquivAdicCompletion_coe _ r
  P.ofTensorProductEquiv.symm ≪≫ₗ
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M) ≪≫ₗ
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R

/-- The comparison sends an original module element to its compatible residue classes. -/
@[simp]
theorem completionModuleEquivAdicCompletion_coe (hI : IsAdic I) (m : M) :
    hI.completionModuleEquivAdicCompletion (m : Completion M) = AdicCompletion.of I M m := by
  simp [completionModuleEquivAdicCompletion,
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
    AdicCompletion.ofTensorProduct_tmul]

/-- The inverse comparison sends a compatible system arising from a module element to its
image in the separated completion. -/
@[simp]
theorem completionModuleEquivAdicCompletion_symm_of (hI : IsAdic I) (m : M) :
    hI.completionModuleEquivAdicCompletion.symm (AdicCompletion.of I M m) =
      (m : Completion M) := by
  rw [LinearEquiv.symm_apply_eq, completionModuleEquivAdicCompletion_coe]

end IsAdic
