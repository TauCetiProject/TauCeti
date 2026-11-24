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

This is the infinitesimal lifting input for the smoothness of the symplectic group scheme
(`TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth`).

## Main declarations

* `TauCeti.GLSymplectic.coe_coe_map`: the underlying matrix of `GLSymplectic.map l f M` is the
  entrywise image of that of `M`.
* `TauCeti.GLSymplectic.map_quotient_mk_surjective_of_exists_mem_symplecticGroup_sub_mem`:
  entrywise reduction modulo `I` is surjective on symplectic groups as soon as every matrix that
  is symplectic modulo `I` is congruent modulo `I` to a symplectic matrix.
* `TauCeti.GLSymplectic.map_quotient_mk_surjective_of_sq_eq_bot`: entrywise reduction modulo a
  square-zero ideal is surjective on symplectic groups.

## References

* The Stacks Project, Tag 00TH, for the infinitesimal lifting criterion for formal smoothness.
* SGA 3, Exposé XXII, for the smooth split symplectic group scheme over `ℤ`.
-/

public section

open Matrix

namespace TauCeti.GLSymplectic

universe u

noncomputable section

variable {l : Type*} [DecidableEq l] [Fintype l]
variable {R : Type u} [CommRing R]

/-- The underlying matrix of the induced morphism is the entrywise image. -/
theorem coe_coe_map {S : Type*} [CommRing S] (f : R →+* S) (M : GLSymplectic l R) :
    (((map l f M : GLSymplectic l S) : GL (l ⊕ l) S) : Matrix (l ⊕ l) (l ⊕ l) S) =
      ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map f := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

/-- **Lifting from approximate solutions.** If every matrix that is symplectic modulo `I` is
congruent modulo `I` to a symplectic matrix, entrywise reduction modulo `I` is surjective on
symplectic groups. -/
theorem map_quotient_mk_surjective_of_exists_mem_symplecticGroup_sub_mem (I : Ideal R)
    (h : ∀ M : Matrix (l ⊕ l) (l ⊕ l) R, (∀ i j, (M * J l R * Mᵀ - J l R) i j ∈ I) →
      ∃ L ∈ symplecticGroup l R, ∀ i j, (L - M) i j ∈ I) :
    Function.Surjective (GLSymplectic.map l (Ideal.Quotient.mk I)) := by
  intro g
  choose m hm using fun i j => Ideal.Quotient.mk_surjective
    (((g : GL (l ⊕ l) (R ⧸ I)) : Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I)) i j)
  obtain ⟨M, hM_map⟩ : ∃ M : Matrix (l ⊕ l) (l ⊕ l) R, M.map (Ideal.Quotient.mk I) =
      ((g : GL (l ⊕ l) (R ⧸ I)) : Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I)) :=
    ⟨Matrix.of m, Matrix.ext hm⟩
  have hE : ∀ i j, (M * J l R * Mᵀ - J l R) i j ∈ I := by
    rw [← Ideal.mk_ker (I := I), forall_mem_ker_iff_map_eq_zero]
    simp [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.transpose_map, hM_map,
      Matrix.map_J, (GLSymplectic.mem_iff).mp g.property]
  obtain ⟨L, hL, hLM⟩ := h M hE
  refine ⟨⟨ofSymplecticGroup l R ⟨L, hL⟩, ofSymplecticGroup_mem l R ⟨L, hL⟩⟩,
    Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j => ?_)⟩
  rw [coe_coe_map, ← hM_map, Matrix.map_apply, Matrix.map_apply, coe_ofSymplecticGroup,
    Ideal.Quotient.eq]
  exact hLM i j

/-- Every symplectic matrix modulo a square-zero ideal lifts to a symplectic matrix.

The result is valid over an arbitrary commutative ring, in every characteristic, and for the
zero-dimensional symplectic group. -/
theorem map_quotient_mk_surjective_of_sq_eq_bot
    (I : Ideal R) (hI : I ^ 2 = (⊥ : Ideal R)) :
    Function.Surjective (GLSymplectic.map l (Ideal.Quotient.mk I)) := by
  refine map_quotient_mk_surjective_of_exists_mem_symplecticGroup_sub_mem I fun M hE => ?_
  obtain ⟨X, hX_mem, hX⟩ :=
    Matrix.exists_entries_mem_add_mul_J_add_J_mul_transpose_eq_zero I _ hE
    (Matrix.transpose_mul_J_mul_transpose_sub_J M) (Matrix.mul_J_mul_transpose_sub_J_apply_self M)
  refine ⟨(1 + X) * M, one_add_mul_mem_symplecticGroup hI rfl hX_mem hX, fun i j => ?_⟩
  rw [add_mul, one_mul, add_sub_cancel_left]
  exact mul_apply_mem_right hX_mem M i j

end

end TauCeti.GLSymplectic
