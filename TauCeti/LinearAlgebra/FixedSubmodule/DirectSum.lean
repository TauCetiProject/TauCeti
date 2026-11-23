/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import TauCeti.LinearAlgebra.FixedSubmodule
import TauCeti.Algebra.DirectSum.Internal

/-!
# Fixed submodules and internal direct sums

An internal direct sum of `f`-invariant submodules restricts to an internal direct sum of
`f.fixedSubmodule` (`DirectSum.IsInternal.fixedSubmodule_comap`), because an invariant endomorphism
fixes a vector exactly when it fixes each direct-sum component
(`DirectSum.IsInternal.mem_fixedSubmodule_iff`).
-/

public section

namespace DirectSum.IsInternal

/-- An endomorphism preserving every summand of an internal direct sum fixes a vector exactly
when it fixes every direct-sum component. -/
theorem mem_fixedSubmodule_iff {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [DecidableEq ι] {Q : ι → Submodule R M} (hQ : DirectSum.IsInternal Q) (f : M →ₗ[R] M)
    (hf : ∀ i, (Q i).map f ≤ Q i) {x : M} :
    x ∈ f.fixedSubmodule ↔
      ∀ i, ((LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) hQ).symm x i : M) ∈
        f.fixedSubmodule := by
  classical
  have hQ' : Function.Bijective (DirectSum.coeLinearMap Q) := hQ
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap Q) hQ'
  refine ⟨fun hx i ↦ ?_, fun h ↦ ?_⟩
  · let fQ : (⨁ i, Q i) →ₗ[R] ⨁ i, Q i :=
      DirectSum.lmap fun j ↦ f.restrict fun y hy ↦ hf j (Submodule.mem_map_of_mem hy)
    have hcomm : DirectSum.coeLinearMap Q ∘ₗ fQ = f ∘ₗ DirectSum.coeLinearMap Q := by
      ext j y
      simp [fQ]
    have hfx : fQ (e.symm x) = e.symm (f x) := e.injective <| by
      dsimp only [e]
      rw [LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply,
        ← LinearMap.comp_apply, hcomm, LinearMap.comp_apply]
      exact (congrArg f (e.apply_symm_apply x)).trans (e.apply_symm_apply (f x)).symm
    have hx' : fQ (e.symm x) = e.symm x := by
      rw [hfx, LinearMap.mem_fixedSubmodule_iff.mp hx]
    rw [LinearMap.mem_fixedSubmodule_iff]
    simpa [fQ] using congrArg (fun z : ⨁ i, Q i ↦ (z i : M)) hx'
  · let _ := hQ.chooseDecomposition
    rw [LinearMap.mem_fixedSubmodule_iff]
    conv_lhs => rw [← DirectSum.sum_support_decompose Q x]
    conv_rhs => rw [← DirectSum.sum_support_decompose Q x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ LinearMap.mem_fixedSubmodule_iff.mp ?_
    simpa only [decompose_eq_ofBijective_symm hQ x] using h i

/-- An internal direct sum of `f`-invariant submodules restricts to an internal direct sum of
`f.fixedSubmodule`. -/
theorem fixedSubmodule_comap {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [DecidableEq ι] {Q : ι → Submodule R M} (hQ : DirectSum.IsInternal Q) (f : M →ₗ[R] M)
    (hf : ∀ i, (Q i).map f ≤ Q i) :
    DirectSum.IsInternal fun i ↦ (Q i).comap f.fixedSubmodule.subtype := by
  let _ := hQ.chooseDecomposition
  refine TauCeti.DirectSum.isInternal_comap Q _ f.fixedSubmodule.subtype
    (Submodule.subtype_injective _) (fun _ _ ↦ Iff.rfl) fun i x ↦ ?_
  have hfix := (hQ.mem_fixedSubmodule_iff f hf).mp x.property i
  rw [← decompose_eq_ofBijective_symm hQ (x : M)] at hfix
  exact ⟨⟨_, hfix⟩, rfl⟩

end DirectSum.IsInternal
