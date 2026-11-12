/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
import TauCeti.Algebra.Module.Projective.LinearMap

/-!
# Regular sequences on modules of linear maps

A regular element on a module `N` remains regular on `M →ₗ[R] N`. More generally, a weakly
regular sequence on `N` of length at most two remains weakly regular on `M →ₗ[R] N`.
No local-ring, Noetherian, or finiteness hypotheses are needed for these transfer results.

## Main results

* `IsSMulRegular.linearMap`: a regular element remains regular on the module of linear maps.
* `IsSMulRegular.quotSMulTop_linearMap`: the second element remains regular after quotienting
  the module of linear maps by the first regular element.
* `RingTheory.Sequence.IsWeaklyRegular.linearMap`: weak regularity of sequences of length at
  most two passes from the target to the module of linear maps.
-/

public section

open RingTheory.Sequence Pointwise

/-- A regular element on the target is regular on the module of linear maps. -/
theorem IsSMulRegular.linearMap {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    {scalar : R} (regular : IsSMulRegular N scalar) :
    IsSMulRegular (M →ₗ[R] N) scalar := by
  intro first second equality
  ext element
  apply regular
  simpa only [LinearMap.smul_apply] using congrArg (fun linear ↦ linear element) equality

section LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

/-- The second element of a weakly regular pair on the target remains regular after quotienting
the module of linear maps by the first element. -/
theorem IsSMulRegular.quotSMulTop_linearMap {first second : R}
    (regular : IsSMulRegular N first)
    (quotientRegular : IsSMulRegular (QuotSMulTop first N) second) :
    IsSMulRegular (QuotSMulTop first (M →ₗ[R] N)) second := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro linear membership
  obtain ⟨other, -, equality⟩ :=
    (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 membership
  have pointwise (element : M) : linear element ∈ first • (⊤ : Submodule R N) := by
    apply mem_of_isSMulRegular_quotient_of_smul_mem quotientRegular
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨other element, Submodule.mem_top, congrArg (fun map ↦ map element) equality⟩
  have inKernel : linear ∈ LinearMap.ker (LinearMap.compRight (M := M) R
      (Ideal.span {algebraMap R R first} • (⊤ : Submodule R N)).mkQ) := by
    rw [LinearMap.mem_ker]
    ext element
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by
      simpa only [Algebra.algebraMap_self_apply, Submodule.ideal_span_singleton_smul]
        using pointwise element)
  rwa [TauCeti.ker_compRight_mkQ_eq_smul_top M regular] at inKernel

/-- A weakly regular sequence of length at most two on the target is weakly regular on the
module of linear maps. -/
theorem RingTheory.Sequence.IsWeaklyRegular.linearMap {scalars : List R}
    (regular : IsWeaklyRegular N scalars) (length : scalars.length ≤ 2) :
    IsWeaklyRegular (M →ₗ[R] N) scalars := by
  cases scalars with
  | nil => exact .nil _ _
  | cons first tail =>
    obtain ⟨firstRegular, tailRegular⟩ := (isWeaklyRegular_cons_iff _ _ _).1 regular
    cases tail with
    | nil => exact (IsWeaklyRegular.nil _ _).cons firstRegular.linearMap
    | cons second rest =>
      have restEmpty : rest = [] := by
        have : rest.length = 0 := by
          simp only [List.length_cons] at length
          omega
        exact List.length_eq_zero_iff.mp this
      subst rest
      have secondRegular := (isWeaklyRegular_cons_iff _ _ _).1 tailRegular |>.1
      exact ((IsWeaklyRegular.nil _ _).cons
        (firstRegular.quotSMulTop_linearMap secondRegular)).cons firstRegular.linearMap

end LinearMap
