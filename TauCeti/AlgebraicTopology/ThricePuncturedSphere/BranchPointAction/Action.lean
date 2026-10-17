/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.BranchPointAction.Basic
import TauCeti.GroupTheory.Perm.FinThree.Basic

/-!
# The anharmonic action on cover classes

Pulling a connected finite cover of the thrice-punctured sphere back along an anharmonic
self-homeomorphism permutes its branch points. Although most of these homeomorphisms move the
basepoint, a bare cover has the same degree at every point. Thus pullback defines an operation
on cover classes at the fixed basepoint without choosing a connecting path.

These operations form a right action of the permutations of `0, 1, ∞`. The classification by
connected permutation triples is equivariant for this action. In particular the two rotations
act in opposite directions, as required by contravariance of pullback. This identifies covers
up to anharmonic pullback with triples up to branch-point permutation.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, Cambridge University Press, 2012, §2.7.
-/

public section

open Equiv Equiv.Perm

namespace TauCeti

open ThricePuncturedSphere

namespace ConnectedCoverClass

variable {n : ℕ}

private theorem isoClass_pullbackSelf_mob01
    (C : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (C.pullbackSelf mob01 (by simp [PreconnectedSpace.connectedComponent_eq_univ])).isoClass =
      MulOpposite.op (Equiv.swap (0 : Fin 3) 1) • C.isoClass := by
  rw [pullbackSelf_eq_pullback C mob01 mob01_basePt, isoClass_pullback_mob01]

private theorem isoClass_pullbackSelf_mob1Inf
    (C : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (C.pullbackSelf mob1Inf (by simp [PreconnectedSpace.connectedComponent_eq_univ])).isoClass =
      MulOpposite.op (Equiv.swap (1 : Fin 3) 2) • C.isoClass := by
  rw [pullbackSelf_eq_basepointChange_pullback C mob1Inf (mob1Inf_mob1Inf basePt),
    isoClass_basepointChange_pullback_mob1Inf]
  all_goals simp [PreconnectedSpace.connectedComponent_eq_univ]

/-- The monodromy classification intertwines anharmonic pullback with branch-point
reindexing, for all six permutations. The puncture permutation of `anharmonic ρ` is `ρ`,
and pullback acts by `MulOpposite.op ρ`. -/
@[simp] theorem isoClass_pullbackSelf_anharmonic
    (C : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n)
    (ρ : Perm (Fin 3)) :
    (C.pullbackSelf (anharmonic ρ)
      (by simp [PreconnectedSpace.connectedComponent_eq_univ])).isoClass =
      MulOpposite.op ρ • C.isoClass := by
  have hr : mobRot = mob1Inf.trans mob01 := Homeomorph.ext mobRot_apply
  have hi : mobRotInv = mob01.trans mob1Inf := Homeomorph.ext mobRotInv_apply
  have hz : mob0Inf = mob01.trans (mob1Inf.trans mob01) :=
    Homeomorph.ext fun z => (mob01_mob1Inf_mob01 z).symm
  have hst : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 = finRotate 3 := by decide
  have hts : Equiv.swap (1 : Fin 3) 2 * Equiv.swap 0 1 = (finRotate 3)⁻¹ := by decide
  have hsts : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) * Equiv.swap 0 1 =
      Equiv.swap 0 2 := by decide
  rcases Perm.fin_three_cases ρ with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [anharmonic_one, MulOpposite.op_one, one_smul]
    exact congrArg (fun D => D.isoClass) (pullbackSelf_refl C)
  · simpa only [anharmonic_swap_zero_one] using isoClass_pullbackSelf_mob01 C
  · simpa only [anharmonic_swap_one_two] using isoClass_pullbackSelf_mob1Inf C
  · simp only [anharmonic_swap_zero_two, hz]
    rw [pullbackSelf_trans, pullbackSelf_trans,
      isoClass_pullbackSelf_mob01, isoClass_pullbackSelf_mob1Inf,
      isoClass_pullbackSelf_mob01, op_smul_op_smul, op_smul_op_smul, ← mul_assoc, hsts]
    all_goals simp [PreconnectedSpace.connectedComponent_eq_univ]
  · simp only [anharmonic_finRotate, hr]
    rw [pullbackSelf_trans, isoClass_pullbackSelf_mob1Inf,
      isoClass_pullbackSelf_mob01, op_smul_op_smul, hst]
    all_goals simp [PreconnectedSpace.connectedComponent_eq_univ]
  · simp only [anharmonic_finRotate_inv, hi]
    rw [pullbackSelf_trans, isoClass_pullbackSelf_mob01,
      isoClass_pullbackSelf_mob1Inf, op_smul_op_smul, hts]
    all_goals simp [PreconnectedSpace.connectedComponent_eq_univ]

/-- Anharmonic pullback acts on bare cover classes; the opposite group records the
contravariance of pullback. -/
noncomputable instance : SMul (Perm (Fin 3))ᵐᵒᵖ
    (ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) where
  smul ρ C := C.pullbackSelf (anharmonic ρ.unop)
    (by simp [PreconnectedSpace.connectedComponent_eq_univ])

/-- Acting by a puncture permutation is pullback by its anharmonic self-homeomorphism,
with the degree measured again at the original basepoint. -/
theorem smul_def
    (C : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n)
    (ρ : (Perm (Fin 3))ᵐᵒᵖ) : ρ • C = C.pullbackSelf (anharmonic ρ.unop)
    (by simp [PreconnectedSpace.connectedComponent_eq_univ]) := (rfl)

/-- The cover-to-triple classification respects the anharmonic operations. -/
@[simp] theorem isoClass_smul
    (C : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n)
    (ρ : (Perm (Fin 3))ᵐᵒᵖ) : (ρ • C).isoClass = ρ • C.isoClass := by
  rw [smul_def, isoClass_pullbackSelf_anharmonic, MulOpposite.op_unop]

/-- The six pullback operations form a right action of the branch-point permutations. -/
noncomputable instance : MulAction (Perm (Fin 3))ᵐᵒᵖ
    (ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) where
  one_smul C := by
    simpa only [smul_def, MulOpposite.unop_one, anharmonic_one] using pullbackSelf_refl C
  mul_smul ρ τ C := by
    simp only [smul_def, MulOpposite.unop_mul, anharmonic_mul]
    exact pullbackSelf_trans C _ _
      (by simp [PreconnectedSpace.connectedComponent_eq_univ])
      (by simp [PreconnectedSpace.connectedComponent_eq_univ])

/-- Reconstructing a cover class from its monodromy class also respects branch-point
permutations. -/
@[simp] theorem isoClassEquiv_symm_smul (c : ConnectedIsoClass n)
    (ρ : (Perm (Fin 3))ᵐᵒᵖ) :
    isoClassEquiv.symm (ρ • c) = ρ • isoClassEquiv.symm c := by
  apply isoClass_injective
  simp

end ConnectedCoverClass

end TauCeti
