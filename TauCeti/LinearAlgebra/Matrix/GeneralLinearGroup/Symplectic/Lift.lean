/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import TauCeti.LinearAlgebra.Matrix.IdealEntries
public import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# Lifting symplectic matrices

A symplectic matrix lifts across a quotient by a square-zero ideal. Starting with arbitrary
lifts of its entries, the failure to preserve the standard alternating form is an alternating
matrix with entries in the ideal. Solving the linearized symplectic equation for it
(`Matrix.exists_entries_mem_add_mul_J_add_J_mul_transpose_eq_zero`) avoids division by two and
therefore works in characteristic two. The quadratic correction terms vanish because the ideal
is square-zero.

## Main declaration

* `TauCeti.GLSymplectic.map_quotient_mk_surjective_of_sq_eq_bot`: entrywise reduction modulo a
  square-zero ideal is surjective on symplectic groups.

## References

* The Stacks Project, Tag 00TH, for the infinitesimal lifting criterion for formal smoothness.
* SGA 3, Exposé XXII, for the smooth split symplectic group scheme over `ℤ`.

This is the infinitesimal lifting input for the smoothness of the symplectic group scheme, a
prerequisite for the `Sp_{2n}` reductivity example in Layer 6 of the ReductiveGroups roadmap.
-/

public section

open Matrix

namespace TauCeti.GLSymplectic

universe u

noncomputable section

variable {l : Type*} [DecidableEq l] [Fintype l]
variable {R : Type u} [CommRing R]

/-- Every symplectic matrix modulo a square-zero ideal lifts to a symplectic matrix.

The result is valid over an arbitrary commutative ring, in every characteristic, and for the
zero-dimensional symplectic group. -/
theorem map_quotient_mk_surjective_of_sq_eq_bot
    (I : Ideal R) (hI : I ^ 2 = (⊥ : Ideal R)) :
    Function.Surjective (GLSymplectic.map l (Ideal.Quotient.mk I)) := by
  classical
  intro g
  choose m hm using fun i j => Ideal.Quotient.mk_surjective
    (((g : GL (l ⊕ l) (R ⧸ I)) : Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I)) i j)
  let M : Matrix (l ⊕ l) (l ⊕ l) R := m
  let qMat : Matrix (l ⊕ l) (l ⊕ l) R →+*
      Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I) :=
    RingHom.mapMatrix (Ideal.Quotient.mk I)
  have hM_map : qMat M =
      ((g : GL (l ⊕ l) (R ⧸ I)) : Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I)) := by
    ext i j
    simpa only [qMat, RingHom.mapMatrix_apply, Matrix.map_apply] using hm i j
  have hJ_map : qMat (Matrix.J l R) = Matrix.J l (R ⧸ I) := by
    simpa only [qMat, RingHom.mapMatrix_apply] using
      Matrix.map_J (l := l) (Ideal.Quotient.mk I)
  have hM_transpose_map : qMat M.transpose = (qMat M).transpose := by
    simpa only [qMat, RingHom.mapMatrix_apply] using
      (Matrix.transpose_map (f := Ideal.Quotient.mk I) (M := M))
  set E : Matrix (l ⊕ l) (l ⊕ l) R :=
    M * Matrix.J l R * M.transpose - Matrix.J l R with hE
  have hE_map : qMat E = 0 := by
    rw [hE, map_sub, map_mul, map_mul, hM_transpose_map, hM_map, hJ_map,
      (GLSymplectic.mem_iff).mp g.2]
    exact sub_self _
  have hE_mem : ∀ i j, E i j ∈ I := by
    intro i j
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa only [qMat, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply] using
      congrFun (congrFun hE_map i) j
  obtain ⟨X, hX_mem, hX⟩ :=
    Matrix.exists_entries_mem_add_mul_J_add_J_mul_transpose_eq_zero I _ hE_mem
    (Matrix.transpose_mul_J_mul_transpose_sub_J M) (Matrix.mul_J_mul_transpose_apply_self_sub_J M)
  have hN_mem := one_add_mul_mem_symplecticGroup hI hE.symm hE_mem hX_mem hX
  let s : Matrix.symplecticGroup l R := ⟨(1 + X) * M, hN_mem⟩
  have hX_map : qMat X = 0 := by
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hX_mem a b
  refine ⟨⟨ofSymplecticGroup l R s, ofSymplecticGroup_mem l R s⟩, ?_⟩
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hN_map : qMat ((1 + X) * M) =
      ((g : GL (l ⊕ l) (R ⧸ I)) : Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I)) := by
    rw [map_mul, map_add, map_one, hX_map, add_zero, one_mul, hM_map]
  have hij := congrFun (congrFun hN_map i) j
  simpa only [coe_map, Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, coe_ofSymplecticGroup, s, qMat] using hij

end

end TauCeti.GLSymplectic
