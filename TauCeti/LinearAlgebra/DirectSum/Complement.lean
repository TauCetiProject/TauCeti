/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Degree-preserving retractions onto homogeneous subspaces

A homogeneous subspace of an internally graded vector space admits a degree-preserving
linear retraction. This allows splittings to be chosen compatibly with degree before imposing
additional symmetry, for example by averaging over a finite group.
-/

public section

namespace LinearMap

variable {R ι V : Type*} [DecidableEq ι] [Semiring R] [AddCommMonoid V] [Module R V]
  (f : V →ₗ[R] V) (𝒱 : ι → Submodule R V) [DirectSum.Decomposition 𝒱]

/-- An endomorphism preserving each graded piece commutes with homogeneous components. -/
theorem map_decompose_of_mapsTo
    (hf : ∀ i, Set.MapsTo f (𝒱 i) (𝒱 i)) (x : V) (i : ι) :
    f (DirectSum.decompose 𝒱 x i) = (DirectSum.decompose 𝒱 (f x) i : V) := by
  classical
  let π : V →ₗ[R] V := (𝒱 i).subtype ∘ₗ
    DirectSum.component R ι (fun j ↦ 𝒱 j) i ∘ₗ (DirectSum.decomposeLinearEquiv 𝒱).toLinearMap
  -- This composite is the degree-`i` component, viewed in the ambient module.
  have hπ (y : V) : π y = (DirectSum.decompose 𝒱 y i : V) := rfl
  have h : f ∘ₗ π = π ∘ₗ f := by
    apply DirectSum.decompose_lhom_ext 𝒱
    intro j
    ext y
    by_cases hji : j = i
    · subst j
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, hπ]
      rw [DirectSum.decompose_of_mem_same 𝒱 y.2,
        DirectSum.decompose_of_mem_same 𝒱 (hf i y.2)]
    · simp only [LinearMap.comp_apply, Submodule.subtype_apply, hπ]
      rw [DirectSum.decompose_of_mem_ne 𝒱 y.2 hji,
        DirectSum.decompose_of_mem_ne 𝒱 (hf j y.2) hji, map_zero]
  exact LinearMap.congr_fun h x

/-- The kernel of a degree-preserving endomorphism is homogeneous. -/
theorem isHomogeneous_ker_of_mapsTo
    (hf : ∀ i, Set.MapsTo f (𝒱 i) (𝒱 i)) :
    DirectSum.SetLike.IsHomogeneous 𝒱 (LinearMap.ker f) := by
  intro i x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [f.map_decompose_of_mapsTo 𝒱 hf, hx, DirectSum.decompose_zero]
  rfl

end LinearMap

namespace Submodule

variable {k ι V : Type*} [DecidableEq ι] [DivisionRing k] [AddCommGroup V] [Module k V]
  (U : Submodule k V) (𝒱 : ι → Submodule k V) [DirectSum.Decomposition 𝒱]

/-- A homogeneous subspace of an internally graded vector space admits a linear retraction
whose underlying endomorphism preserves every degree. No finiteness assumption is needed. -/
theorem exists_graded_retraction (hU : DirectSum.SetLike.IsHomogeneous 𝒱 U) :
    ∃ p : V →ₗ[k] U, (∀ x : U, p x = x) ∧
      ∀ i, ∀ x ∈ 𝒱 i, (p x : V) ∈ 𝒱 i := by
  classical
  let W (i : ι) := U.comap (𝒱 i).subtype
  let q (i : ι) : 𝒱 i →ₗ[k] W i := (W i).subtype.leftInverse
  let r (i : ι) : 𝒱 i →ₗ[k] U :=
    (((𝒱 i).subtype ∘ₗ (W i).subtype).codRestrict U (fun x ↦ x.2)) ∘ₗ q i
  let p := DirectSum.toModule k ι U r ∘ₗ (DirectSum.decomposeLinearEquiv 𝒱).toLinearMap
  have hp (i : ι) (x : 𝒱 i) : p x = r i x := by
    simp only [p, LinearMap.comp_apply, LinearEquiv.coe_coe,
      DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
  have hr (i : ι) (x : 𝒱 i) (hx : (x : V) ∈ U) : (r i x : V) = x := by
    have h := LinearMap.leftInverse_apply_of_inj (W i).ker_subtype (⟨x, hx⟩ : W i)
    exact congrArg (fun z : W i ↦ (z : V)) h
  refine ⟨p, ?_, fun i x hx ↦ ?_⟩
  · intro x
    apply Subtype.ext
    rw [← DirectSum.sum_support_decompose 𝒱 (x : V), map_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [hp, hr i _ (hU i x.2)]
  · rw [hp i ⟨x, hx⟩]
    exact (q i ⟨x, hx⟩).1.2

end Submodule
