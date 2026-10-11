/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.Semisimple.Lemmas
public import TauCeti.Algebra.Lie.Symplectic.Basic

/-!
# The Killing form of the symplectic Lie algebra

The standard module `l ⊕ l → K` of the symplectic Lie algebra `LieAlgebra.Symplectic.sp l K` is
irreducible over every field, as soon as `l` is nonempty. Together with faithfulness and
vanishing traces, Mathlib's reductivity criterion for faithful irreducible modules then shows that
`sp l K` has trivial radical in characteristic zero, provided each element acts triangularizably
on the standard module (for instance over an algebraically closed field).
Cartan's criterion turns this into nondegeneracy of the Killing form.

The irreducibility argument uses the elements `v ↦ ω(a, v) a` and `v ↦ ω(a, v) b + ω(b, v) a`
of `sp l K`, where `ω(x, y) = x ⬝ᵥ (J *ᵥ y)` is the standard alternating form. Given a nonzero
`v`, choose `a` with `ω(a, v) = 1`. The first element sends `v` to `a`, and the second, for
`b = w`, sends `v` to `w` plus a multiple of `a`, so a Lie submodule containing `v` contains every
vector.

## Main results

* `TauCeti.isIrreducible_sp_standard`: the standard module of `sp l K` is irreducible.
* `TauCeti.hasTrivialRadical_sp`: `sp l K` has trivial radical in characteristic zero, given
  triangularizability of its standard module; in particular its Killing form is nondegenerate.

## References

* W. Fulton and J. Harris, *Representation Theory*, Lecture 16 (the symplectic Lie algebras).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§1.2, 5 and 19.
-/

public section

namespace TauCeti

open Matrix LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {l : Type*} [DecidableEq l] [Fintype l]

section CommRing

variable {R : Type*} [CommRing R]

/-- The rank-one symplectic matrix `v ↦ ω(a, v) a` attached to a vector, where `ω` is the
standard alternating form. -/
private def rankOneMatrix (a : l ⊕ l → R) : Matrix (l ⊕ l) (l ⊕ l) R :=
  vecMulVec a (a ᵥ* J l R)

private theorem rankOneMatrix_mem_sp (a : l ⊕ l → R) : rankOneMatrix a ∈ Symplectic.sp l R := by
  rw [Symplectic.mem_sp, rankOneMatrix]
  simp only [transpose_vecMulVec, vecMulVec_mul, mul_vecMulVec, J_mulVec, neg_vecMulVec, neg_neg]

private theorem rankOneMatrix_mulVec (a v : l ⊕ l → R) :
    rankOneMatrix a *ᵥ v = ((a ᵥ* J l R) ⬝ᵥ v) • a := by
  simp [rankOneMatrix, vecMulVec_mulVec]

/-- The symplectic matrix `v ↦ ω(a, v) b + ω(b, v) a` attached to two vectors, where `ω` is the
standard alternating form. -/
private def symmetricMatrix (a b : l ⊕ l → R) : Matrix (l ⊕ l) (l ⊕ l) R :=
  vecMulVec b (a ᵥ* J l R) + vecMulVec a (b ᵥ* J l R)

private theorem symmetricMatrix_mem_sp (a b : l ⊕ l → R) :
    symmetricMatrix a b ∈ Symplectic.sp l R := by
  rw [Symplectic.mem_sp, symmetricMatrix]
  simp only [transpose_add, transpose_vecMulVec, add_mul, mul_add, vecMulVec_mul, mul_vecMulVec,
    J_mulVec, neg_vecMulVec, neg_add, neg_neg]
  exact add_comm _ _

private theorem symmetricMatrix_mulVec (a b v : l ⊕ l → R) :
    symmetricMatrix a b *ᵥ v = ((a ᵥ* J l R) ⬝ᵥ v) • b + ((b ᵥ* J l R) ⬝ᵥ v) • a := by
  simp [symmetricMatrix, add_mulVec, vecMulVec_mulVec]

end CommRing

section Field

variable {K : Type*} [Field K] [Nonempty l]

/-- **The standard module of the symplectic Lie algebra is irreducible** over every field, for a
nonempty index type. -/
instance isIrreducible_sp_standard :
    IsIrreducible K (Symplectic.sp l K) (l ⊕ l → K) := by
  apply IsIrreducible.mk
  intro N hN
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((LieSubmodule.toSubmodule_eq_bot N).not.mpr hN)
  -- The standard alternating form is nondegenerate, so some `a` pairs with `v` to one.
  obtain ⟨a, ha⟩ : ∃ a : l ⊕ l → K, (a ᵥ* J l K) ⬝ᵥ v = 1 := by
    have hJv : J l K *ᵥ v ≠ 0 := fun h ↦ hv0 <| by
      simpa [mulVec_mulVec, J_squared, neg_mulVec] using congrArg (J l K *ᵥ ·) h
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hJv
    refine ⟨Pi.single p ((J l K *ᵥ v) p)⁻¹, ?_⟩
    rw [← dotProduct_mulVec, single_dotProduct, inv_mul_cancel₀ hp]
  have hmem (A : Matrix (l ⊕ l) (l ⊕ l) K) (hA : A ∈ Symplectic.sp l K) : A *ᵥ v ∈ N := by
    have h := N.lie_mem (x := ⟨A, hA⟩) hv
    rwa [LieSubalgebra.coe_bracket_of_module, Matrix.lie_apply] at h
  have haN : a ∈ N := by
    simpa [rankOneMatrix_mulVec, ha] using hmem _ (rankOneMatrix_mem_sp a)
  rw [eq_top_iff]
  intro w _
  have h := hmem _ (symmetricMatrix_mem_sp a w)
  rw [symmetricMatrix_mulVec, ha, one_smul] at h
  simpa using N.sub_mem h (N.smul_mem ((w ᵥ* J l K) ⬝ᵥ v) haN)

end Field

section CharZero

variable (K : Type*) [Field K] [CharZero K]

/-- **The symplectic Lie algebra has trivial radical** in characteristic zero, provided each of
its elements acts triangularizably on the standard module, which holds over every algebraically
closed field. By Cartan's criterion its Killing form is then nondegenerate. -/
instance hasTrivialRadical_sp [IsTriangularizable K (Symplectic.sp l K) (l ⊕ l → K)] :
    HasTrivialRadical K (Symplectic.sp l K) := by
  cases isEmpty_or_nonempty l
  · infer_instance
  · refine hasTrivialRadical_of_isIrreducible_of_isFaithful K (Symplectic.sp l K) (l ⊕ l → K)
      fun ⟨_, hx⟩ ↦ by simpa using Symplectic.trace_eq_zero_of_mem_sp hx

end CharZero

end TauCeti
