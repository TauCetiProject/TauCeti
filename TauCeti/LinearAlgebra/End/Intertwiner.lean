/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import TauCeti.Algebra.CentralSimple.End

/-!
# Intertwiners of representations through a full endomorphism algebra

Let `ρ : B ≃ₐ[K] Module.End K M` identify a `K`-algebra `B` with the full endomorphism algebra of
a finite-dimensional vector space `M`, and let `σ : B →ₐ[K] Module.End K N` be any representation
of `B` on a vector space `N` of the same dimension. Then `N` is a copy of `M`: there is a linear
isomorphism `T : M ≃ N` with

  `T (ρ b x) = σ b (T x)`,

and every linear map `M → N` intertwining `ρ` with `σ` is a scalar multiple of `T`.

Existence is the Skolem–Noether theorem for endomorphism algebras. The composite
`σ ∘ ρ⁻¹ : Module.End K M → Module.End K N` is injective because `Module.End K M` is a simple
ring, and therefore bijective by comparing dimensions; Mathlib's
`AlgEquiv.eq_linearEquivConjAlgEquiv` writes it as conjugation by some `T`. Uniqueness is Schur's
lemma in this setting: if `T` and `U` both intertwine, then `T⁻¹ ∘ U` commutes with every `ρ b`,
that is with all of `Module.End K M`, so it is a scalar (`Module.End.mem_center_iff`).

## Main results

* `AlgEquiv.exists_linearEquiv_apply_eq_apply`: a representation of the same dimension as a
  full endomorphism representation is isomorphic to it.
* `AlgEquiv.exists_eq_smul_of_apply_eq_apply`: intertwiners out of a full endomorphism
  representation are unique up to a scalar.
-/

public section

open Module

namespace AlgEquiv

variable {K B M N : Type*} [Field K] [Ring B] [Algebra K B] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

/-- **Representations through a full endomorphism algebra are determined by their dimension.**
If `ρ` identifies `B` with the endomorphism algebra of a finite-dimensional space `M`, then every
representation `σ` of `B` on a space `N` of the same dimension is isomorphic to `ρ`: some linear
isomorphism `T : M ≃ N` satisfies `T (ρ b x) = σ b (T x)`. This includes the zero space. -/
theorem exists_linearEquiv_apply_eq_apply [FiniteDimensional K M] [FiniteDimensional K N]
    (ρ : B ≃ₐ[K] Module.End K M) (σ : B →ₐ[K] Module.End K N)
    (h : finrank K M = finrank K N) :
    ∃ T : M ≃ₗ[K] N, ∀ b x, T (ρ b x) = σ b (T x) := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · have : Subsingleton N := finrank_zero_iff.1 (h ▸ finrank_zero_of_subsingleton)
    exact ⟨LinearEquiv.ofFinrankEq M N h, fun _ _ ↦ Subsingleton.elim _ _⟩
  have : Nontrivial N := finrank_pos_iff.1 (h ▸ finrank_pos)
  -- `σ ∘ ρ⁻¹` is injective on the simple ring `Module.End K M`, hence bijective by dimension.
  let f : Module.End K M →ₐ[K] Module.End K N := σ.comp ρ.symm.toAlgHom
  have hinj : Function.Injective f := f.toRingHom.injective
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap)
      (by rw [finrank_linearMap, finrank_linearMap, h])).1 hinj
  obtain ⟨T, hT⟩ := (AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).eq_linearEquivConjAlgEquiv
  refine ⟨T, fun b x ↦ ?_⟩
  have hb := congr($hT (ρ b) (T x))
  have hf : AlgEquiv.ofBijective f ⟨hinj, hsurj⟩ (ρ b) = σ b :=
    (AlgEquiv.ofBijective_apply f _ (ρ b)).trans (by simp [f])
  rw [hf] at hb
  simpa using hb.symm

/-- **Schur's lemma for a full endomorphism representation.** If `ρ` identifies `B` with the
endomorphism algebra of `M` and `T : M ≃ N` intertwines `ρ` with a representation `σ`, then every
linear map `U : M → N` intertwining `ρ` with `σ` is a scalar multiple of `T`. -/
theorem exists_eq_smul_of_apply_eq_apply (ρ : B ≃ₐ[K] Module.End K M)
    (σ : B →ₐ[K] Module.End K N) {T : M ≃ₗ[K] N} (hT : ∀ b x, T (ρ b x) = σ b (T x))
    {U : M →ₗ[K] N} (hU : ∀ b x, U (ρ b x) = σ b (U x)) :
    ∃ c : K, U = c • T.toLinearMap := by
  -- `T⁻¹ ∘ U` commutes with every `ρ b`, that is with every endomorphism of `M`.
  have hcenter : T.symm.toLinearMap ∘ₗ U ∈ Set.center (Module.End K M) := by
    refine Semigroup.mem_center_iff.2 fun g ↦ LinearMap.ext fun x ↦ ?_
    obtain ⟨b, rfl⟩ := ρ.surjective g
    simp only [Module.End.mul_eq_comp, LinearMap.comp_apply, LinearEquiv.coe_coe, hU]
    rw [T.eq_symm_apply, hT, T.apply_symm_apply]
  obtain ⟨c, hc', hc⟩ := Module.End.mem_center_iff.1 hcenter
  refine ⟨c, LinearMap.ext fun x ↦ ?_⟩
  have hx := congr(T ($hc x))
  simpa using hx

end AlgEquiv
