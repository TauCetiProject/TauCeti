/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Folding.Basic
public import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import TauCeti.LinearAlgebra.FixedSubmodule.Permutation

/-!
# The integral Cartan lattice of a folded frame

For a positive definite invariant integer Gram matrix with diagonal two and nonpositive
off-diagonal entries, the Cartan part of the integral fixed lattice of a pinned diagram action
has the distinct vertex-orbit sums as a basis. The normalized folded coroots multiply these
sums by the folding scales, which are one or two. They need not span the entire integral fixed
Cartan lattice.

This file gives both lattices inside `Matrix.ShellLieAlgebra`, their coordinate membership
criteria, and the relative index: the product of the folding scales. Thus the index is a
power of two. No identification of the whole fixed Lie lattice with a normalized folded
Chevalley lattice is asserted.

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

section Decidable

variable [DecidableEq I]

private noncomputable def orbitCartan (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    ShellLieAlgebra B :=
  ∑ i with σ.SameCycle i O.out, cartan B (Pi.single i 1)

-- Bundled projections let linearity do the coordinate calculations without unfolding the
-- additive-group instance on the shell carrier.
private noncomputable def cartanProjection : ShellLieAlgebra B →ₗ[ℤ] (I → ℤ) :=
  (LinearMap.fst ℤ _ _).comp (equivProd B).toLinearMap

private noncomputable def rootProjection : ShellLieAlgebra B →ₗ[ℤ] (B.normTwoShell →₀ ℤ) :=
  (LinearMap.snd ℤ _ _).comp (equivProd B).toLinearMap

omit [DecidableEq I] in
private theorem cartanProjection_apply (x : ShellLieAlgebra B) :
    cartanProjection x = (equivProd B x).1 := (rfl)

omit [DecidableEq I] in
private theorem rootProjection_apply (x : ShellLieAlgebra B) :
    rootProjection x = (equivProd B x).2 := (rfl)

private theorem cartanProjection_orbitCartan (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    cartanProjection (orbitCartan (B := B) σ O) =
      fun i ↦ if σ.SameCycle i O.out then 1 else 0 := by
  classical
  simp only [orbitCartan, map_sum]
  ext i
  simp [cartanProjection_apply, Pi.single_apply]

private theorem rootProjection_orbitCartan (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    rootProjection (orbitCartan (B := B) σ O) = 0 := by
  classical
  simp [orbitCartan, rootProjection_apply]

omit [Fintype I] [DecidableEq I] in
private theorem sameCycle_out_iff (O P : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    σ.SameCycle O.out P.out ↔ O = P :=
  (Quotient.eq (r := Equiv.Perm.SameCycle.setoid σ)).symm.trans
    (by simp only [Quotient.out_eq])

private theorem orbitCartan_coord [DecidableEq (Quotient (Equiv.Perm.SameCycle.setoid σ))]
    (O P : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    cartanProjection (orbitCartan (B := B) σ P) O.out = if O = P then 1 else 0 := by
  classical
  simp only [cartanProjection_orbitCartan, sameCycle_out_iff]

private theorem cartan_permutationFixedBasis
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    cartan B (σ.permutationFixedBasis (R := ℤ) O).val = orbitCartan σ O := by
  classical
  rw [σ.permutationFixedBasis_eq_sum, map_sum]
  apply sum_congr
  · ext i
    have hcycle : (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) i = O) ↔
        σ.SameCycle i O.out := by
      constructor
      · intro h
        exact Quotient.exact (s := Equiv.Perm.SameCycle.setoid σ)
          (h.trans (Quotient.out_eq O).symm)
      · intro h
        exact (Quotient.sound (s := Equiv.Perm.SameCycle.setoid σ) h).trans (Quotient.out_eq O)
    simp only [mem_filter, mem_univ, true_and, hcycle]
  · intro i _
    rfl

private theorem linearIndependent_orbitCartan :
    LinearIndependent ℤ (orbitCartan (B := B) σ) := by
  classical
  have hinj : Function.Injective (cartan B) := by
    intro v w h
    simpa only [equivProd_cartan] using congrArg (fun x ↦ (equivProd B x).1) h
  have h := (σ.permutationFixedBasis (R := ℤ)).linearIndependent.map'
    ((cartan B).comp (LinearMap.fixedSubmodule _).subtype)
    (LinearMap.ker_eq_bot.mpr (hinj.comp Subtype.val_injective))
  simpa only [Function.comp_def, LinearMap.comp_apply, Submodule.subtype_apply,
    cartan_permutationFixedBasis] using h

variable (B) in
/-- The Cartan lattice fixed by the vertex permutation: the span of the distinct orbit sums
of the integral simple Cartan vectors. -/
noncomputable def fixedCartanLattice : Submodule ℤ (ShellLieAlgebra B) :=
  Submodule.span ℤ (Set.range (orbitCartan (B := B) σ))

/-- The distinct vertex-orbit sums form a basis of the integral fixed Cartan lattice. -/
noncomputable def fixedCartanBasis :
    Basis (Quotient (Equiv.Perm.SameCycle.setoid σ)) ℤ (fixedCartanLattice B σ) :=
  Basis.span (linearIndependent_orbitCartan (B := B) σ)

/-- Each fixed Cartan basis vector is the sum over one vertex orbit, with no multiplicity. -/
@[simp]
theorem coe_fixedCartanBasis (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (fixedCartanBasis (B := B) σ O : ShellLieAlgebra B) =
      ∑ i with σ.SameCycle i O.out, cartan B (Pi.single i 1) :=
  Basis.coe_span_apply _ _

/-- Fixed Cartan coordinates are read at the chosen orbit representatives. -/
@[simp]
theorem fixedCartanBasis_repr (x : fixedCartanLattice B σ)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (fixedCartanBasis (B := B) σ).repr x O = (equivProd B x).1 O.out := by
  classical
  have h := congrArg (fun y : fixedCartanLattice B σ ↦ cartanProjection (B := B) y O.out)
    ((fixedCartanBasis (B := B) σ).sum_repr x)
  rw [← cartanProjection_apply]
  have hb (P : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
      cartanProjection (fixedCartanBasis (B := B) σ P : ShellLieAlgebra B) O.out =
        if O = P then 1 else 0 :=
    (congrArg (fun y ↦ cartanProjection y O.out) (coe_fixedCartanBasis σ P)).trans
      (orbitCartan_coord σ O P)
  simpa only [Submodule.coe_sum, SetLike.val_smul, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, hb, smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq,
    mem_univ, ite_true] using h

/-- A vector belongs to the fixed Cartan lattice exactly when its root part vanishes and
its Cartan coordinates are invariant under the vertex permutation. -/
@[simp]
theorem mem_fixedCartanLattice_iff (x : ShellLieAlgebra B) :
    x ∈ fixedCartanLattice B σ ↔
      (equivProd B x).2 = 0 ∧ ∀ i, (equivProd B x).1 (σ i) = (equivProd B x).1 i := by
  classical
  simp only [← cartanProjection_apply, ← rootProjection_apply]
  constructor
  · intro hx
    obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    constructor
    · simp only [map_sum, map_smul, rootProjection_orbitCartan, smul_zero, sum_const_zero]
    · intro i
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
        cartanProjection_orbitCartan, Equiv.Perm.sameCycle_apply_left]
  · rintro ⟨hroot, hinv⟩
    let v : (LinearEquiv.funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule :=
      ⟨cartanProjection x, LinearMap.mem_fixedSubmodule_iff.mpr (by
        ext i
        exact hinv i)⟩
    have heq : cartan B v.val = x := by
      apply (equivProd B).injective
      rw [equivProd_cartan]
      exact Prod.ext rfl hroot.symm
    have hsum : cartan B v.val = ∑ O,
        (σ.permutationFixedBasis (R := ℤ)).repr v O • orbitCartan (B := B) σ O := by
      have h := congrArg (fun w : (LinearEquiv.funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule ↦
        cartan B w.val) ((σ.permutationFixedBasis (R := ℤ)).sum_repr v)
      simpa only [Submodule.coe_sum, SetLike.val_smul, map_sum, map_smul,
        cartan_permutationFixedBasis] using h.symm
    rw [← heq, hsum]
    exact Submodule.sum_mem _ fun O _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨O, rfl⟩)

end Decidable

variable [LinearOrder I]

/-- The fixed Cartan lattice is contained in the fixed submodule of the pinned diagram action. -/
theorem fixedCartanLattice_le_fixedSubmodule (hσ : B.reindex σ σ = B) :
    fixedCartanLattice B σ ≤ (reindex σ hσ).toLinearMap.fixedSubmodule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨O, rfl⟩
  apply LinearMap.mem_fixedSubmodule_iff.mpr
  simp only [LinearEquiv.coe_coe, orbitCartan, map_sum, reindex_cartan,
    Pi.single_comp_equiv, Equiv.symm_symm]
  exact σ.sum_filter_sameCycle_comp O.out fun i ↦ cartan B (Pi.single i 1)

variable (B) in
/-- The integral lattice spanned by the normalized folded Cartan generators `H'_O`. -/
noncomputable def foldedCartanLattice : Submodule ℤ (ShellLieAlgebra B) :=
  Submodule.span ℤ (Set.range (foldedH B σ))

/-- Normalized folded Cartan generators lie in the actual fixed Cartan lattice. -/
theorem foldedCartanLattice_le_fixedCartanLattice :
    foldedCartanLattice B σ ≤ fixedCartanLattice B σ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨O, rfl⟩
  rw [foldedH_def]
  exact (fixedCartanLattice B σ).smul_mem _ (Submodule.subset_span ⟨O, rfl⟩)

private theorem foldedH_eq_smul_orbitCartan (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    foldedH B σ O = B.foldingScale σ O • orbitCartan σ O := foldedH_def B σ O

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
      simp [map_sum, map_smul, foldedH_eq_smul_orbitCartan, Finset.sum_apply,
        orbitCartan_coord, mul_ite]
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

section PositiveDefinite

variable (hB : B.PosDef) (hdiag : ∀ i, B i i = 2)
  (hoff : ∀ i j, i ≠ j → B i j ≤ 0) (hσ : B.reindex σ σ = B)

include hB hdiag hoff hσ

/-- The normalized folded Cartan generators are integrally linearly independent. -/
theorem linearIndependent_foldedH : LinearIndependent ℤ (foldedH B σ) := by
  have hscale (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
      IsRightRegular (B.foldingScale σ O) :=
    (isRegular_iff_ne_zero.mpr (foldingScale_pos hB hdiag hoff hσ O).ne').right
  have heq : foldedH B σ = B.foldingScale σ • orbitCartan σ :=
    funext (foldedH_eq_smul_orbitCartan σ)
  rw [heq]
  exact (linearIndependent_orbitCartan (B := B) σ).smul_of_isRightRegular hscale

/-- The normalized folded Cartan generators form a basis of their integral span. -/
noncomputable def foldedCartanBasis :
    Basis (Quotient (Equiv.Perm.SameCycle.setoid σ)) ℤ (foldedCartanLattice B σ) :=
  Basis.span (linearIndependent_foldedH σ hB hdiag hoff hσ)

/-- The normalized lattice basis consists of the actual folded Cartan generators. -/
@[simp]
theorem coe_foldedCartanBasis (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    (foldedCartanBasis σ hB hdiag hoff hσ O : ShellLieAlgebra B) = foldedH B σ O :=
  Basis.coe_span_apply _ _

/-- Normalized lattice coordinates, multiplied by the folding scale, recover the actual
integral Cartan coordinates. -/
@[simp]
theorem foldingScale_mul_foldedCartanBasis_repr (x : foldedCartanLattice B σ)
    (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
    B.foldingScale σ O * (foldedCartanBasis σ hB hdiag hoff hσ).repr x O =
      (equivProd B x).1 O.out := by
  classical
  have h := congrArg (fun y : foldedCartanLattice B σ ↦ cartanProjection (B := B) y O.out)
    ((foldedCartanBasis σ hB hdiag hoff hσ).sum_repr x)
  rw [← cartanProjection_apply]
  simp only [Submodule.coe_sum, SetLike.val_smul, coe_foldedCartanBasis, map_sum,
    map_smul, Finset.sum_apply, Pi.smul_apply, foldedH_eq_smul_orbitCartan,
    orbitCartan_coord, smul_eq_mul, mul_ite, mul_one, mul_zero,
    sum_ite_eq, mem_univ, ite_true] at h
  simpa only [mul_comm] using h

open Classical in
/-- The index of the normalized Cartan lattice in the actual fixed Cartan lattice is the
product of the folding scales. This is an integral index, not just a rational dimension match. -/
theorem relIndex_foldedCartanLattice_fixedCartanLattice :
    (foldedCartanLattice B σ).toAddSubgroup.relIndex
      (fixedCartanLattice B σ).toAddSubgroup =
        ∏ O : Quotient (Equiv.Perm.SameCycle.setoid σ), (B.foldingScale σ O).natAbs := by
  classical
  let inc (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) : fixedCartanLattice B σ :=
    ⟨foldedCartanBasis σ hB hdiag hoff hσ O,
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
    (foldedCartanBasis σ hB hdiag hoff hσ) (fixedCartanBasis (B := B) σ)]
  -- `inc` is precisely the inclusion of the normalized lattice basis into the fixed lattice.
  change ((fixedCartanBasis (B := B) σ).det inc).natAbs = _
  rw [Basis.det_apply, hmatrix, Matrix.det_diagonal, Int.natAbs_prod]

open Classical in
/-- Each orbit whose folding scale is two contributes one factor of two to the index. -/
theorem relIndex_foldedCartanLattice_fixedCartanLattice_eq_two_pow :
    (foldedCartanLattice B σ).toAddSubgroup.relIndex
      (fixedCartanLattice B σ).toAddSubgroup =
        2 ^ Fintype.card {O : Quotient (Equiv.Perm.SameCycle.setoid σ) //
          B.foldingScale σ O = 2} := by
  classical
  rw [relIndex_foldedCartanLattice_fixedCartanLattice σ hB hdiag hoff hσ]
  have habs (O : Quotient (Equiv.Perm.SameCycle.setoid σ)) :
      (B.foldingScale σ O).natAbs = if B.foldingScale σ O = 2 then 2 else 1 := by
    rcases foldingScale_eq_one_or_eq_two hB hdiag hoff hσ O with h | h <;> simp [h]
  simp only [habs, prod_ite, prod_const, one_pow, mul_one, Fintype.card_subtype]

end PositiveDefinite

end Matrix.ShellLieAlgebra
