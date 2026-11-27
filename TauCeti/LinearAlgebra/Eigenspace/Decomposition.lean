/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Decomposition into generalized eigenspaces

An injective endomorphism has no generalized eigenvectors with eigenvalue `0`. Over an
algebraically closed field, the generalized eigenspaces of an endomorphism of a finite-dimensional
vector space form an internal direct sum, combining Mathlib's
`Module.End.independent_maxGenEigenspace` and `Module.End.iSup_maxGenEigenspace_eq_top`, so an
endomorphism is determined by its restrictions to them.

## Main results

* `Module.End.maxGenEigenspace_zero_eq_bot_of_injective`: an injective endomorphism has no
  generalized eigenvectors with eigenvalue `0`.
* `Module.End.isInternal_maxGenEigenspace`: the generalized eigenspaces form an internal direct
  sum.
* `Module.End.ext_of_maxGenEigenspace`: two endomorphisms agreeing on every generalized eigenspace
  of `F` are equal.
-/

public section

namespace Module.End

open Function

/-- An injective endomorphism has no generalized eigenvectors with eigenvalue `0`. -/
theorem maxGenEigenspace_zero_eq_bot_of_injective {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {F : End R M} (hF : Injective F) : F.maxGenEigenspace 0 = ⊥ := by
  refine eq_bot_iff.mpr fun v hv ↦ ?_
  obtain ⟨k, hk⟩ := (mem_maxGenEigenspace F 0 v).mp hv
  rw [zero_smul, sub_zero] at hk
  have hinj : Injective ⇑(F ^ k) := by
    rw [FunLike.coe_pow_eq_iterate]
    exact hF.iterate k
  exact (Submodule.mem_bot R).mpr ((injective_iff_map_eq_zero _).mp hinj v hk)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [IsAlgClosed K]
  [FiniteDimensional K V]

/-- The generalized eigenspaces of an endomorphism of a finite-dimensional vector space over an
algebraically closed field form an internal direct sum. -/
theorem isInternal_maxGenEigenspace [DecidableEq K] (F : End K V) :
    DirectSum.IsInternal fun μ ↦ F.maxGenEigenspace μ :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top F.independent_maxGenEigenspace
    (iSup_maxGenEigenspace_eq_top F)

/-- Two endomorphisms of a finite-dimensional vector space over an algebraically closed field which
agree on every generalized eigenspace of an endomorphism `F` are equal. -/
theorem ext_of_maxGenEigenspace {F f g : End K V}
    (h : ∀ μ, ∀ v ∈ F.maxGenEigenspace μ, f v = g v) : f = g := by
  ext v
  have hv : v ∈ ⨆ μ, F.maxGenEigenspace μ := by
    rw [iSup_maxGenEigenspace_eq_top]
    trivial
  refine Submodule.iSup_induction _ (motive := fun v ↦ f v = g v) hv h (by simp) ?_
  intro x y hx hy
  rw [map_add, map_add, hx, hy]

end Module.End
