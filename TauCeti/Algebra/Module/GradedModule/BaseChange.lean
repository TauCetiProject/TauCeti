/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
import TauCeti.Algebra.DirectSum.BaseChange
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Scalar extension of internal gradings

An internal grading extends along any homomorphism of commutative semirings. Its pieces are
Mathlib's scalar-extended submodules; their internality is `DirectSum.IsInternal.baseChange`.
Thus no flatness hypothesis is needed.

Homogeneous projections commute with pure tensors, and scalar extension preserves homogeneous
linear maps, both for arbitrary submodule families and for internal gradings.
-/

public section

namespace TauCeti.InternalGrading

open scoped TensorProduct

variable {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (G : InternalGrading R M ι) (S : Type*) [CommSemiring S] [Algebra R S]

/-- Extend every homogeneous summand along the coefficient homomorphism. -/
noncomputable def baseChange : InternalGrading S (S ⊗[R] M) ι where
  piece i := (G.piece i).baseChange S
  isInternal := G.isInternal.baseChange

/-- The pieces of the extended grading are the scalar extensions of the original pieces. -/
@[simp]
theorem baseChange_piece (i : ι) : (G.baseChange S).piece i = (G.piece i).baseChange S := (rfl)

/-- The homogeneous component of a pure tensor is the tensor of its homogeneous component. -/
@[simp]
theorem coe_decompose_baseChange_tmul (s : S) (x : M) (i : ι) :
    (DirectSum.decompose (G.baseChange S).piece (s ⊗ₜ[R] x) i : S ⊗[R] M) =
      s ⊗ₜ[R] (DirectSum.decompose G.piece x i : M) := by
  have hd : (G.baseChange S).instDecompositionSubmodulePiece =
      DirectSum.Decomposition.baseChange G.piece := Subsingleton.elim _ _
  rw [hd]
  exact DirectSum.coe_decompose_baseChange_tmul G.piece s x i

end TauCeti.InternalGrading

namespace TauCeti.LinearMap.IsHomogeneous

open scoped TensorProduct

section Families

variable {R M N ι : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddMonoid ι]
  {f : M →ₗ[R] N} {ℳ : ι → Submodule R M} {𝓝 : ι → Submodule R N} {q : ι}

/-- Scalar extension preserves the degree of a homogeneous linear map between submodule
families. No decomposition or flatness hypothesis is needed. -/
@[grind =>]
theorem baseChange (hf : IsHomogeneous f ℳ 𝓝 q) (S : Type*) [Semiring S] [Algebra R S] :
    IsHomogeneous (f.baseChange S) (fun p ↦ (ℳ p).baseChange S)
      (fun p ↦ (𝓝 p).baseChange S) q := by
  refine LinearMap.isHomogeneous_def.2 fun p x hx => ?_
  have hmap : (ℳ p).map f ≤ 𝓝 (p + q) :=
    Submodule.map_le_iff_le_comap.mpr fun _ hx ↦ hf.map_mem hx
  have hbase := Submodule.baseChange_mono S hmap
  rw [Submodule.baseChange_map] at hbase
  exact hbase (Submodule.mem_map_of_mem hx)

end Families

variable {R M N ι : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddMonoid ι] [DecidableEq ι] {f : M →ₗ[R] N} {q : ι}

/-- Scalar extension preserves the degree of a homogeneous map of internally graded modules. -/
theorem baseChange_internalGrading {G : InternalGrading R M ι} {H : InternalGrading R N ι}
    (hf : IsHomogeneous f G.piece H.piece q) (S : Type*) [CommSemiring S] [Algebra R S] :
    IsHomogeneous (f.baseChange S) (G.baseChange S).piece (H.baseChange S).piece q := by
  simpa only [LinearMap.isHomogeneous_def, InternalGrading.baseChange_piece] using hf.baseChange S

end TauCeti.LinearMap.IsHomogeneous
