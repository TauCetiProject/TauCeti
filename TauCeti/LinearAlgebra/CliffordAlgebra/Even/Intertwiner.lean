/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.End.Intertwiner

/-!
# Clifford modules on which an odd element acts by one

Let `ρ₁` and `ρ₂` be representations of a Clifford algebra `CliffordAlgebra Q` on `M` and `N`, and
suppose some odd element `ω` acts by the identity on both. Then each generator is determined by
an even element: `ω * ι Q v` is even and acts as `ι Q v` does. Consequently a linear map
`T : M → N` intertwining the actions of the even subalgebra intertwines the whole algebra
(`CliffordAlgebra.apply_eq_apply_of_forall_mem_even`).

This is the situation of the odd-dimensional Clifford algebras, where the normalized volume
element is central and odd and acts by `+1` or `-1` on each irreducible module: modules with the
same label are compared through their even parts. Over a field, if the even subalgebra acts on a
finite-dimensional `M` as the whole of `Module.End K M`, any `N` of the same dimension with the
same label is isomorphic to `M` as a Clifford module
(`CliffordAlgebra.exists_linearEquiv_apply_eq_apply_of_mem_odd`), and the isomorphism is unique up
to a scalar (`CliffordAlgebra.exists_eq_smul_of_apply_eq_apply`). Both come from the
corresponding statements for representations through a full endomorphism algebra,
`AlgEquiv.exists_linearEquiv_apply_eq_apply` and `AlgEquiv.exists_eq_smul_of_apply_eq_apply`.

## Main results

* `CliffordAlgebra.apply_eq_apply_of_forall_mem_even`: an intertwiner of the even actions is an
  intertwiner of the Clifford actions when an odd element acts by one on both modules.
* `CliffordAlgebra.exists_linearEquiv_apply_eq_apply_of_mem_odd`: existence of an isomorphism
  of Clifford modules.
* `CliffordAlgebra.exists_eq_smul_of_apply_eq_apply`: its uniqueness up to a scalar.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open Module

namespace CliffordAlgebra

section CommRing

variable {R V M N : Type*} [CommRing R] [AddCommGroup V] [Module R V] {Q : QuadraticForm R V}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {ρ₁ : CliffordAlgebra Q →ₐ[R] Module.End R M} {ρ₂ : CliffordAlgebra Q →ₐ[R] Module.End R N}

/-- **An odd element acting by one reduces intertwining to the even subalgebra.** If an odd
element `ω` acts by the identity on both `M` and `N`, then a linear map `T : M → N` that
intertwines the actions of every even element intertwines the actions of every element. -/
theorem apply_eq_apply_of_forall_mem_even {ω : CliffordAlgebra Q} (hω : ω ∈ evenOdd Q 1)
    (h₁ : ρ₁ ω = 1) (h₂ : ρ₂ ω = 1) {T : M →ₗ[R] N}
    (hT : ∀ x ∈ even Q, ∀ m, T (ρ₁ x m) = ρ₂ x (T m)) (x : CliffordAlgebra Q) (m : M) :
    T (ρ₁ x m) = ρ₂ x (T m) := by
  induction x using CliffordAlgebra.induction generalizing m with
  | algebraMap r => exact hT _ (algebraMap_mem _ r) m
  | ι v =>
    -- `ω * ι Q v` is even and acts as `ι Q v` does on both modules.
    have hv : ω * ι Q v ∈ even Q := by
      rw [← Subalgebra.mem_toSubmodule, even_toSubmodule, show (0 : ZMod 2) = 1 + 1 from rfl]
      exact evenOdd_mul_le Q 1 1 (Submodule.mul_mem_mul hω (ι_mem_evenOdd_one Q v))
    have := hT _ hv m
    rwa [map_mul, map_mul, h₁, h₂, one_mul, one_mul] at this
  | mul x y hx hy =>
    simp only [map_mul, Module.End.mul_eq_comp, LinearMap.comp_apply]
    rw [hx, hy]
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hx,
      hy]

end CommRing

section Field

variable {K V M N : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {ρ₁ : CliffordAlgebra Q →ₐ[K] Module.End K M} {ρ₂ : CliffordAlgebra Q →ₐ[K] Module.End K N}

/-- **Clifford modules with the same odd label are isomorphic.** Suppose the even subalgebra acts
on a finite-dimensional `M` as the whole of `Module.End K M`, and an odd element `ω` acts by the
identity on `M` and on a space `N` of the same dimension. Then some linear isomorphism
`T : M ≃ N` intertwines the two Clifford actions. -/
theorem exists_linearEquiv_apply_eq_apply_of_mem_odd [FiniteDimensional K M]
    [FiniteDimensional K N] (hρ₁ : Function.Bijective (ρ₁.comp (even Q).val))
    {ω : CliffordAlgebra Q} (hω : ω ∈ evenOdd Q 1) (h₁ : ρ₁ ω = 1) (h₂ : ρ₂ ω = 1)
    (h : finrank K M = finrank K N) :
    ∃ T : M ≃ₗ[K] N, ∀ x m, T (ρ₁ x m) = ρ₂ x (T m) := by
  obtain ⟨T, hT⟩ := (AlgEquiv.ofBijective _ hρ₁).exists_linearEquiv_apply_eq_apply
    (ρ₂.comp (even Q).val) h
  refine ⟨T, apply_eq_apply_of_forall_mem_even hω h₁ h₂ (T := T.toLinearMap) fun x hx m ↦ ?_⟩
  simpa using hT ⟨x, hx⟩ m

/-- **Isomorphisms of Clifford modules are unique up to a scalar** when the even subalgebra acts
on the source `M` as the whole of `Module.End K M`: if `T : M ≃ N` intertwines two Clifford
actions, every linear map `U : M → N` intertwining them is a scalar multiple of `T`. -/
theorem exists_eq_smul_of_apply_eq_apply (hρ₁ : Function.Bijective (ρ₁.comp (even Q).val))
    {T : M ≃ₗ[K] N} (hT : ∀ x m, T (ρ₁ x m) = ρ₂ x (T m)) {U : M →ₗ[K] N}
    (hU : ∀ x m, U (ρ₁ x m) = ρ₂ x (U m)) :
    ∃ c : K, U = c • T.toLinearMap :=
  (AlgEquiv.ofBijective _ hρ₁).exists_eq_smul_of_apply_eq_apply (ρ₂.comp (even Q).val)
    (fun x m ↦ by simpa using hT x m) (fun x m ↦ by simpa using hU x m)

end Field

end CliffordAlgebra
