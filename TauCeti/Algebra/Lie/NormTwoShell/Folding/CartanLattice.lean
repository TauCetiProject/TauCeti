/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Folding.Basic
public import TauCeti.Algebra.Lie.NormTwoShell.FixedCartan
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# The integral Cartan lattice of a folded frame

For a positive definite invariant integer Gram matrix with diagonal two and nonpositive
off-diagonal entries, the Cartan part of the integral fixed lattice of a pinned diagram action
has the distinct vertex-orbit sums as a basis. The normalized folded coroots multiply these
sums by the folding scales, which are one or two. They need not span the entire integral fixed
Cartan lattice.

This file compares the folded lattice with the fixed Cartan lattice from
`TauCeti.Algebra.Lie.NormTwoShell.FixedCartan`, gives its coordinate membership criterion,
and computes the relative index: the product of the folding scales. Thus the index is a
power of two. The normalized basis and product-index formula only require nonzero folding
scales. No identification of the whole fixed Lie lattice with a normalized folded Chevalley
lattice is asserted.

The construction uses the folded frame of `Matrix.ShellLieAlgebra.isSerreSystem_folded`,
`Equiv.Perm.permutationFixedBasis` for the integral orbit basis, and Mathlib's lattice
determinant formula `AddSubgroup.relIndex_eq_natAbs_det`.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9.
-/

public section

open Finset Module

namespace Matrix.ShellLieAlgebra

variable {I : Type*} [Fintype I] {B : Matrix I I ℤ} (σ : Equiv.Perm I)

-- A bundled projection lets linearity do the coordinate calculations without unfolding the
-- additive-group instance on the shell carrier.
private noncomputable def cartanProjection : ShellLieAlgebra B →ₗ[ℤ] (I → ℤ) :=
  (LinearMap.fst ℤ _ _).comp (equivProd B).toLinearMap

private theorem cartanProjection_apply (x : ShellLieAlgebra B) :
    cartanProjection x = (equivProd B x).1 := (rfl)

variable [LinearOrder I]

variable (B) in
/-- The integral lattice spanned by the normalized folded Cartan generators `H'_O`. -/
noncomputable def foldedCartanLattice : Submodule ℤ (ShellLieAlgebra B) :=
  Submodule.span ℤ (Set.range (foldedH B σ))

/-- Normalized folded Cartan generators lie in the actual fixed Cartan lattice. -/
theorem foldedCartanLattice_le_fixedCartanLattice :
    foldedCartanLattice B σ ≤ fixedCartanLattice B σ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨O, rfl⟩
  rw [foldedH_def, ← coe_fixedCartanBasis]
  exact (fixedCartanLattice B σ).smul_mem _ (SetLike.coe_mem _)

/-- The normalized lattice consists of fixed Cartan vectors whose orbit coordinates are
divisible by the corresponding folding scales. -/
@[simp]
theorem mem_foldedCartanLattice_iff (x : ShellLieAlgebra B) :
    x ∈ foldedCartanLattice B σ ↔ x ∈ fixedCartanLattice B σ ∧
      ∀ O, B.foldingScale σ O ∣ (equivProd B x).1 O.out := by
  classical
  constructor
  · intro hx
    refine ⟨foldedCartanLattice_le_fixedCartanLattice σ hx, ?_⟩
    obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    intro O
    have hcoord : cartanProjection (∑ P, f P • foldedH B σ P) O.out =
        f O * B.foldingScale σ O := by
      simp only [foldedH_def, ← coe_fixedCartanBasis, map_sum, map_smul,
        Finset.sum_apply, Pi.smul_apply]
      simp only [cartanProjection_apply, ← fixedCartanBasis_repr, Basis.repr_self,
        Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        sum_ite_eq', mem_univ, ite_true]
    rw [← cartanProjection_apply, ← hf, hcoord]
    exact dvd_mul_left _ _
  · rintro ⟨hfixed, hdiv⟩
    choose f hf using hdiv
    refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨f, ?_⟩
    have heq : ∑ O, f O • (B.foldingScale σ O • fixedCartanBasis (B := B) σ O) =
        (⟨x, hfixed⟩ : fixedCartanLattice B σ) := by
      apply (fixedCartanBasis (B := B) σ).repr.injective
      ext O
      simp [Finset.sum_apply', Finsupp.single_apply, hf, mul_comm]
    simpa only [Submodule.coe_sum, SetLike.val_smul, coe_fixedCartanBasis,
      ← foldedH_def] using congrArg Subtype.val heq

section NonzeroScales

variable (hscale : ∀ O, B.foldingScale σ O ≠ 0)

include hscale

/-- The normalized folded Cartan generators are integrally linearly independent. -/
theorem linearIndependent_foldedH : LinearIndependent ℤ (foldedH B σ) := by
  have hregular (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
      IsRightRegular (B.foldingScale σ O) :=
    (isRegular_iff_ne_zero.mpr (hscale O)).right
  have h := (fixedCartanBasis (B := B) σ).linearIndependent.map'
    (fixedCartanLattice B σ).subtype (Submodule.ker_subtype _)
  have heq : foldedH B σ = fun O ↦
      B.foldingScale σ O • (fixedCartanBasis (B := B) σ O : ShellLieAlgebra B) := by
    ext O
    rw [coe_fixedCartanBasis, foldedH_def]
  rw [heq]
  exact h.smul_of_isRightRegular hregular

/-- The normalized folded Cartan generators form a basis of their integral span. -/
noncomputable def foldedCartanBasis :
    Basis (Quotient (Equiv.Perm.SameCycle.setoid σ)) ℤ (foldedCartanLattice B σ) :=
  Basis.span (linearIndependent_foldedH σ hscale)

/-- The normalized lattice basis consists of the actual folded Cartan generators. -/
@[simp]
theorem coe_foldedCartanBasis (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (foldedCartanBasis σ hscale O : ShellLieAlgebra B) = foldedH B σ O :=
  Basis.coe_span_apply _ _

/-- Normalized lattice coordinates, multiplied by the folding scale, recover the actual
integral Cartan coordinates. -/
@[simp]
theorem foldingScale_mul_foldedCartanBasis_repr (x : foldedCartanLattice B σ)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    B.foldingScale σ O * (foldedCartanBasis σ hscale).repr x O =
      (equivProd B x).1 O.out := by
  classical
  have h := congrArg (fun y : foldedCartanLattice B σ ↦ cartanProjection (B := B) y O.out)
    ((foldedCartanBasis σ hscale).sum_repr x)
  rw [← cartanProjection_apply]
  simp only [Submodule.coe_sum, SetLike.val_smul, coe_foldedCartanBasis, map_sum,
    map_smul, Finset.sum_apply, Pi.smul_apply, foldedH_def, ← coe_fixedCartanBasis] at h
  simp only [cartanProjection_apply, ← fixedCartanBasis_repr, Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    sum_ite_eq', mem_univ, ite_true] at h
  simpa only [cartanProjection_apply, mul_comm] using h

open Classical in
/-- The index of the normalized Cartan lattice in the actual fixed Cartan lattice is the
product of the folding scales. This is an integral index, not just a rational dimension match. -/
theorem relIndex_foldedCartanLattice_fixedCartanLattice :
    (foldedCartanLattice B σ).toAddSubgroup.relIndex
      (fixedCartanLattice B σ).toAddSubgroup =
        ∏ O : Quotient (Equiv.Perm.SameCycle.setoid σ), (B.foldingScale σ O).natAbs := by
  classical
  let inc (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) : fixedCartanLattice B σ :=
    ⟨foldedCartanBasis σ hscale O,
      foldedCartanLattice_le_fixedCartanLattice σ (SetLike.coe_mem _)⟩
  have hinc (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
      inc O = B.foldingScale σ O • fixedCartanBasis (B := B) σ O := by
    apply Subtype.ext
    simp only [inc, coe_foldedCartanBasis, SetLike.val_smul, coe_fixedCartanBasis, foldedH_def]
  have hmatrix : (fixedCartanBasis (B := B) σ).toMatrix inc =
      Matrix.diagonal (B.foldingScale σ) := by
    ext O P
    by_cases hOP : O = P
    · subst P
      simp [Basis.toMatrix_apply, hinc]
    · simp [Basis.toMatrix_apply, hinc, hOP]
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _
    (foldedCartanLattice_le_fixedCartanLattice σ)
    (foldedCartanBasis σ hscale) (fixedCartanBasis (B := B) σ)]
  -- `inc` is precisely the inclusion of the normalized lattice basis into the fixed lattice.
  change ((fixedCartanBasis (B := B) σ).det inc).natAbs = _
  rw [Basis.det_apply, hmatrix, Matrix.det_diagonal, Int.natAbs_prod]

end NonzeroScales

section PositiveDefinite

variable (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
  (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)

include hB hdiag hoff hσ

open Classical in
/-- Each orbit whose folding scale is two contributes one factor of two to the index. -/
theorem relIndex_foldedCartanLattice_fixedCartanLattice_eq_two_pow :
    (foldedCartanLattice B σ).toAddSubgroup.relIndex
      (fixedCartanLattice B σ).toAddSubgroup =
        2 ^ Fintype.card {O : Quotient (Equiv.Perm.SameCycle.setoid σ) //
          B.foldingScale σ O = 2} := by
  classical
  rw [relIndex_foldedCartanLattice_fixedCartanLattice σ
    (fun O ↦ (foldingScale_pos hB hdiag hoff hσ O).ne')]
  have habs (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
      (B.foldingScale σ O).natAbs = if B.foldingScale σ O = 2 then 2 else 1 := by
    rcases foldingScale_eq_one_or_eq_two hB hdiag hoff hσ O with h | h <;> simp [h]
  simp only [habs, prod_ite, prod_const, one_pow, mul_one, Fintype.card_subtype]

end PositiveDefinite

end Matrix.ShellLieAlgebra
