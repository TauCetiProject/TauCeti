/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Symplectic.Integral
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.Base
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup.Basic

/-!
# Numbered Kostant root subgroups in the symplectic group

The integral comparison from the full-weight type-C Kostant carrier to the symplectic group
preserves every numbered raising and lowering root subgroup, including its additive parameter.
The raising subgroups are the Bourbaki-numbered simple root subgroups: adjacent difference roots
before the terminal node, and the positive long root at the terminal node. The lowering subgroups
are the opposite difference roots and the negative terminal long root.

These are equalities of group-scheme morphisms over `ℤ`, so they also preserve parameters over
nonreduced value rings and after arbitrary scalar extension. They connect the divided-power
construction to the root-subgroup parameters used in the standard symplectic pinning.

The comparison reuses the four root-matrix identifications in
`TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Generation`, and evaluates them at the universal
additive point to compare coordinate maps. The integral isomorphism is
`SpStd.symplecticIso`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §§3–4.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate III.
-/

public section

open AlgebraicGeometry CategoryTheory Matrix
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.SpStd

noncomputable section

variable (n : ℕ)

/-- The standard symplectic root corresponding to a numbered Kostant raising or lowering
subgroup. Raising indices use the simple roots in Bourbaki numbering. -/
def symplecticRootIndex (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    GLSymplecticFin.RootSubgroupIndex (n + 1) :=
  match k with
  | .inl i => Symplectic.diagonalSimpleRootIndex (n + 1) i
  | .inr i =>
      if h : (i : ℕ) + 1 < n + 1 then
        .difference ⟨i + 1, h⟩ i (by simp [Fin.ext_iff])
      else .negativeLong i

/-- Raising indices are the simple-root indices of the standard symplectic pinning. -/
@[simp]
theorem symplecticRootIndex_inl (i : Fin (n + 1)) :
    symplecticRootIndex n (.inl i) = Symplectic.diagonalSimpleRootIndex (n + 1) i := (rfl)

/-- The terminal lowering subgroup is the negative long-root subgroup. -/
@[simp]
theorem symplecticRootIndex_inr_last :
    symplecticRootIndex n (.inr (Fin.last n)) = .negativeLong (Fin.last n) := by
  simp [symplecticRootIndex]

/-- A nonterminal lowering subgroup is the reversed adjacent difference-root subgroup. -/
@[simp]
theorem symplecticRootIndex_inr_castSucc (i : Fin n) :
    symplecticRootIndex n (.inr i.castSucc) =
      .difference i.succ i.castSucc (Fin.castSucc_lt_succ (i := i)).ne' := by
  simp only [symplecticRootIndex, Fin.val_castSucc, Nat.add_lt_add_iff_right, i.isLt,
    ↓reduceDIte]
  rfl

private theorem coe_rootSubgroupPoints_symplecticRootIndex
    (k : Fin (n + 1) ⊕ Fin (n + 1)) {A : Type*} [CommRing A] (u : Multiplicative A) :
    (rootSubgroupPoints n k A u : GL (Fin ((n + 1) + (n + 1))) A) =
      ((symplecticRootIndex n k).hom u : GL (Fin ((n + 1) + (n + 1))) A) := by
  cases k with
  | inl i =>
      induction i using Fin.lastCases with
      | last =>
          rw [rootSubgroupPoints_inl_last_eq_positiveLongRootTransvectionUnit,
            symplecticRootIndex_inl,
            Symplectic.diagonalSimpleRootIndex_of_not_lt _ (by simp),
            GLSymplecticFin.RootSubgroupIndex.hom_positiveLong,
            GLSymplecticFin.positiveLongRootTransvectionHom_apply]
      | cast i =>
          rw [rootSubgroupPoints_inl_eq_differenceShortRootUnit_of_ne_last n _
              (Fin.castSucc_ne_last i), symplecticRootIndex_inl,
            Symplectic.diagonalSimpleRootIndex_of_lt _ (by simp),
            GLSymplecticFin.RootSubgroupIndex.hom_difference,
            GLSymplecticFin.differenceShortRootHom_apply]
          simp only [Fin.orderSucc_castSucc]
  | inr i =>
      induction i using Fin.lastCases with
      | last =>
          rw [rootSubgroupPoints_inr_last_eq_negativeLongRootTransvectionUnit,
            symplecticRootIndex_inr_last, GLSymplecticFin.RootSubgroupIndex.hom_negativeLong,
            GLSymplecticFin.negativeLongRootTransvectionHom_apply]
      | cast i =>
          rw [rootSubgroupPoints_inr_eq_differenceShortRootUnit_of_ne_last n _
              (Fin.castSucc_ne_last i), symplecticRootIndex_inr_castSucc,
            GLSymplecticFin.RootSubgroupIndex.hom_difference,
            GLSymplecticFin.differenceShortRootHom_apply]
          simp only [Fin.orderSucc_castSucc]

private theorem rootSubgroupCoordinateMap_eq
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    kostantRootSubgroupCoordinateMap (rootGenerator n) (cartanGenerator n) (rep n)
        (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k
        (isNilpotent_rep_rootGenerator n k) (latticeBasis n) =
      Symplectic.coordinateMap ℤ (n + 1) ≫
        Symplectic.rootSubgroupCoordinateMap (R := ℤ) (symplecticRootIndex n k) := by
  let A := AdditiveGroup.coordinateHopfAlgebra ℤ
  let q : WithConv (A →ₐ[ℤ] A) := WithConv.toConv (AlgHom.id ℤ A)
  have hroot := coe_rootSubgroupPoints_symplecticRootIndex n k
    (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q)
  rw [coe_rootSubgroupPoints] at hroot
  -- The carrier formula writes the additive coordinate algebra as a symmetric algebra;
  -- the universal point uses its bundled Hopf-algebra presentation.
  erw [MulEquiv.symm_apply_apply] at hroot
  have hmatrix := map_genericMatrix_eq_kostantRootSubgroupMatrix
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k
    (isNilpotent_rep_rootGenerator n k) (latticeBasis n)
  -- The same additive-algebra presentation change applies to the universal matrix formula.
  erw [hroot] at hmatrix
  have hpaired := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) hmatrix
  rw [GLSymplecticFin.RootSubgroupIndex.hom_apply_matrix] at hpaired
  have hparam : (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q).toAdd =
      SymmetricAlgebra.ι ℤ ℤ 1 := by
    rw [AdditiveGroup.toAdd_gaPointsMulEquiv]
    -- The universal algebra point evaluates the additive coordinate by the identity map.
    rfl
  rw [hparam] at hpaired
  apply _root_.CommHopfAlgCat.hom_ext
  apply GeneralLinear.coordinateHopfAlgebra_bialgHom_ext
  intro r s
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective r
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective s
  rw [CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
    Symplectic.rootSubgroupCoordinateMap_apply_X]
  simpa only [submatrix_apply, map_apply, GeneralLinear.genericMatrix_apply,
    BialgHom.coe_toAlgHom] using
    congrArg (fun M => M a b) hpaired

/-- The integral carrier--symplectic isomorphism preserves every numbered root subgroup
and its parameter. In particular its raising subgroups are the standard simple root subgroups. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_comp_symplecticIso
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootSubgroup n k ≫ (symplecticIso n).hom =
      Symplectic.rootSubgroup (R := ℤ) (symplecticRootIndex n k) := by
  apply (cancel_mono (Symplectic.inclusion ℤ (n + 1))).mp
  rw [Category.assoc, symplecticIso_hom_comp_inclusion, rootSubgroup_comp_carrierι,
    kostantRootSubgroup_def, Symplectic.rootSubgroup_def, Symplectic.inclusion_def]
  rw [rootSubgroupCoordinateMap_eq, op_comp, Functor.map_comp]
  simp [GeneralLinear.hopfIdealInclusion_def, Symplectic.coordinateMap_def,
    CommHopfAlgCat.quotientSpecι_def, Category.assoc]

end

end TauCeti.SpStd
