/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Length
public import TauCeti.Algebra.Module.GradedModule.Quotient
import TauCeti.RingTheory.Length

/-!
# Lengths of the graded pieces of kernels and cokernels

Let `f : M → N` be a homogeneous linear map of degree `r` between internally graded modules, with
kernel `K` and cokernel `C` graded as in `TauCeti.Algebra.Module.GradedModule.Quotient`. In each
degree `p` the sequence `0 → K_p → M_p → N_{p+r} → C_{p+r} → 0` is exact, so additivity of length
gives `ℓ(K_p) + ℓ(N_{p+r}) = ℓ(M_p) + ℓ(C_{p+r})`. For multiplication by a variable on a graded
module over a polynomial ring this is the identity of Hilbert series behind the Hilbert–Serre
theorem.

## Main results

* `TauCeti.InternalGrading.length_ker_piece_add_length_piece_add`: the lengths of the graded
  pieces of the kernel, source, target and cokernel of a homogeneous map satisfy
  `ℓ(K_p) + ℓ(N_{p+r}) = ℓ(M_p) + ℓ(C_{p+r})`.
-/

public section

open DirectSum

namespace TauCeti.InternalGrading

variable {ι R S M N : Type*} [DecidableEq ι] [AddRightCancelMonoid ι] [Ring R] [Ring S] [SMul R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- A homogeneous map `f` of degree `r`, with kernel `K` and cokernel `C`, gives exact sequences
`0 → K_p → M_p → N_{p+r} → C_{p+r} → 0`, hence this identity of lengths. -/
theorem length_ker_piece_add_length_piece_add (G : InternalGrading R M ι)
    {H : InternalGrading R N ι} {f : M →ₗ[S] N} {r : ι}
    (hf : LinearMap.IsHomogeneous f G.piece H.piece r) (p : ι) :
    Module.length R ((G.ker hf).piece p) + Module.length R (H.piece (p + r)) =
      Module.length R (G.piece p) +
        Module.length R ((H.quotient _ hf.isHomogeneous_range).piece (p + r)) := by
  let U := LinearMap.range f
  -- The three maps of the sequence: inclusion, `f`, and the quotient map.
  let f₁ : (G.ker hf).piece p →ₗ[R] G.piece p :=
    ((LinearMap.ker f).subtype.restrictScalars R).restrict fun _ hz ↦ (G.mem_ker_piece hf).1 hz
  let f₂ : G.piece p →ₗ[R] H.piece (p + r) :=
    (f.restrictScalars R).restrict fun _ hx ↦ by
      rw [LinearMap.restrictScalars_apply]
      exact hf.map_mem hx
  let f₃ : H.piece (p + r) →ₗ[R] (H.quotient U hf.isHomogeneous_range).piece (p + r) :=
    (U.mkQ.restrictScalars R).restrict fun _ hx ↦ by
      rw [LinearMap.restrictScalars_apply, Submodule.mkQ_apply]
      exact H.mk_mem_quotient_piece U _ hx
  -- `LinearMap.restrict_apply` does not match `f₁` syntactically through the kernel's module
  -- structure, so `simp` unfolds `LinearMap.restrict` there.
  have hf₁ (z) : (f₁ z : M) = ((z : LinearMap.ker f) : M) := by simp [f₁, LinearMap.restrict]
  have hf₂ (x) : (f₂ x : N) = f x := by simp [f₂]
  have hf₃ (x) : (f₃ x : N ⧸ U) = Submodule.Quotient.mk (x : N) := by simp [f₃]
  refine length_add_length_eq_length_add_length_of_exact (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)
    (fun z₁ z₂ h ↦ ?_) (fun y ↦ ?_) (fun y ↦ ?_) (fun y ↦ ?_)
  · exact Subtype.ext (Subtype.ext (by rw [← hf₁, ← hf₁, h]))
  · rw [← Subtype.coe_inj, hf₂, ZeroMemClass.coe_zero]
    constructor
    · intro hy
      exact ⟨⟨⟨y, hy⟩, (G.mem_ker_piece hf).2 y.property⟩, Subtype.ext (hf₁ _)⟩
    · rintro ⟨z, rfl⟩
      rw [hf₁]
      exact (z : LinearMap.ker f).property
  · rw [← Subtype.coe_inj, hf₃, ZeroMemClass.coe_zero, Submodule.Quotient.mk_eq_zero]
    constructor
    · -- The degree-`p` component of a preimage is a homogeneous preimage.
      rintro ⟨m, hm⟩
      refine ⟨⟨_, (decompose G.piece m p).property⟩, Subtype.ext ?_⟩
      rw [hf₂, hf.map_decompose, hm, decompose_of_mem_same H.piece y.property]
    · rintro ⟨x, rfl⟩
      rw [hf₂]
      exact LinearMap.mem_range_self f x
  · obtain ⟨x, hx, hxy⟩ := (H.mem_quotient_piece_iff U _).mp y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

end TauCeti.InternalGrading
