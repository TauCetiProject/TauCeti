/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Action
public import TauCeti.Algebra.Lie.F4.ShortRoot.AdmissibleLattice

/-!
# The modular F4 short-root action matrix

This file identifies the structurally constructed adjoint action on the modular short-root ideal
with the existing sparse twenty-six-dimensional root matrices.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.2 and 12.3.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII, for the root
  coordinates and the simple-root numbering.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra LieModule
open TauCeti.F4ShortRoot

noncomputable section

/-- The target of the unique possibly nonzero entry in a simple-root matrix column. -/
def f4SimpleRootTarget : (Fin 4 ⊕ Fin 4) → Fin 26 → Fin 26
  | .inl i => raisingTarget i
  | .inr i => loweringTarget i

@[simp] theorem f4SimpleRootTarget_inl (i : Fin 4) (b : Fin 26) :
    f4SimpleRootTarget (.inl i) b = raisingTarget i b := (rfl)

@[simp] theorem f4SimpleRootTarget_inr (i : Fin 4) (b : Fin 26) :
    f4SimpleRootTarget (.inr i) b = loweringTarget i b := (rfl)

/-- The integral coefficient of the unique possibly nonzero entry in a simple-root matrix
column. -/
def f4SimpleRootCoeff : (Fin 4 ⊕ Fin 4) → Fin 26 → ℤ
  | .inl i => raisingCoeff i
  | .inr i => loweringCoeff i

@[simp] theorem f4SimpleRootCoeff_inl (i : Fin 4) (b : Fin 26) :
    f4SimpleRootCoeff (.inl i) b = raisingCoeff i b := (rfl)

@[simp] theorem f4SimpleRootCoeff_inr (i : Fin 4) (b : Fin 26) :
    f4SimpleRootCoeff (.inr i) b = loweringCoeff i b := (rfl)

/-- Each simple-root matrix column is supported on the single entry named by
`f4SimpleRootTarget`, where it carries the coefficient named by `f4SimpleRootCoeff`. -/
@[simp] theorem rootMatrix_apply (k : Fin 4 ⊕ Fin 4) (a b : Fin 26) :
    rootMatrix k a b = if a = f4SimpleRootTarget k b then f4SimpleRootCoeff k b else 0 := by
  cases k with
  | inl i =>
      rw [rootMatrix_inl, raisingMatrix_apply]
      rfl
  | inr i =>
      rw [rootMatrix_inr, loweringMatrix_apply]
      rfl

private theorem f4SimpleRootTable_root_zero_cases (k : Fin 4 ⊕ Fin 4) (b : Fin 26)
    (β : Fin 48) (hβ : f4Length β = 1) (hw : f4ShortRootWeight b = f4Root β)
    (hcoeff : (f4SimpleRootCoeff k b : ZMod 2) = 0) :
    β = f4SignedSimpleRootIndex k ∨
      (f4Length (f4SignedSimpleRootIndex k) = 1 ∧
        ∃ γ : Fin 48, f4Length γ = 2 ∧ f4Root γ =
          f4Root β + f4Root (f4SignedSimpleRootIndex k)) ∨
      (β ≠ f4SignedSimpleRootIndex k ∧
        β ≠ f4OppositeRootIndex (f4SignedSimpleRootIndex k) ∧
        (f4SimplyConnectedRootDatum.pairing β (f4SignedSimpleRootIndex k) = 1 ∨
          (f4Length (f4SignedSimpleRootIndex k) = 2 ∧
            f4SimplyConnectedRootDatum.pairing β (f4SignedSimpleRootIndex k) = 0))) := by
  cases k with
  | inl i =>
      simp only [f4SignedSimpleRootIndex_inl]
      simp only [f4OppositeRootIndex_castAdd]
      rw [f4Length_def] at hβ ⊢
      simp only [f4SimplyConnectedRootDatum_pairing]
      revert i b β
      decide +kernel
  | inr i =>
      simp only [f4SignedSimpleRootIndex_inr]
      simp only [f4OppositeRootIndex_f4OppositeRootIndex]
      simp only [f4OppositeRootIndex_castAdd]
      rw [f4Length_def] at hβ ⊢
      simp only [f4SimplyConnectedRootDatum_pairing]
      revert i b β
      decide +kernel

private theorem f4SimpleRootTable_coeff_eq_one (k : Fin 4 ⊕ Fin 4) (b : Fin 26)
    (hcoeff : (f4SimpleRootCoeff k b : ZMod 2) ≠ 0) :
    (f4SimpleRootCoeff k b : ZMod 2) = 1 := by
  cases k with
  | inl i =>
      revert i b
      decide +kernel
  | inr i =>
      revert i b
      decide +kernel

private theorem f4SimpleRootTable_root_nonzero_cases (k : Fin 4 ⊕ Fin 4) (b : Fin 26)
    (β : Fin 48) (hβ : f4Length β = 1) (hw : f4ShortRootWeight b = f4Root β)
    (hcoeff : (f4SimpleRootCoeff k b : ZMod 2) ≠ 0) :
    β = f4OppositeRootIndex (f4SignedSimpleRootIndex k) ∨
      ∃ γ : Fin 48, f4Length γ = 1 ∧
        f4Root γ = f4Root β + f4Root (f4SignedSimpleRootIndex k) ∧
        f4ShortRootWeight (f4SimpleRootTarget k b) = f4Root γ := by
  cases k with
  | inl i =>
      simp only [f4SignedSimpleRootIndex_inl, f4SimpleRootTarget]
      simp only [f4OppositeRootIndex_castAdd]
      rw [f4Length_def] at hβ ⊢
      revert i b β
      decide +kernel
  | inr i =>
      simp only [f4SignedSimpleRootIndex_inr, f4SimpleRootTarget]
      simp only [f4OppositeRootIndex_f4OppositeRootIndex]
      simp only [f4OppositeRootIndex_castAdd]
      rw [f4Length_def] at hβ ⊢
      revert i b β
      decide +kernel

private theorem coe_f4ShortRootLieIdealBasis_simpleRootTarget_of_opposite
    (k : Fin 4 ⊕ Fin 4) (b : Fin 26)
    (hw : f4ShortRootWeight b = f4Root (f4OppositeRootIndex (f4SignedSimpleRootIndex k))) :
    (f4ShortRootLieIdealBasis (f4SimpleRootTarget k b) :
      f4ModularChevalleyLieAlgebra) =
        f4ModularCoroot (f4SignedSimpleRootIndex k) := by
  have hcases :
      (f4SimpleRootTarget k b = 12 ∧
        (f4SignedSimpleRootIndex k = Fin.castAdd 44 (2 : Fin 4) ∨
          f4SignedSimpleRootIndex k = Fin.addNat (Fin.castAdd 20 (2 : Fin 4)) 24)) ∨
      (f4SimpleRootTarget k b = 13 ∧
        (f4SignedSimpleRootIndex k = Fin.castAdd 44 (3 : Fin 4) ∨
          f4SignedSimpleRootIndex k = Fin.addNat (Fin.castAdd 20 (3 : Fin 4)) 24)) := by
    cases k with
    | inl i =>
        simp only [f4SignedSimpleRootIndex_inl, f4OppositeRootIndex_castAdd] at hw ⊢
        revert i b
        decide +kernel
    | inr i =>
        simp only [f4SignedSimpleRootIndex_inr, f4OppositeRootIndex_f4OppositeRootIndex] at hw ⊢
        simp only [f4OppositeRootIndex_castAdd]
        revert i b
        decide +kernel
  rcases hcases with ⟨ht, ha | ha⟩ | ⟨ht, ha | ha⟩
  all_goals
    refine (congrArg (fun j => (f4ShortRootLieIdealBasis j :
      f4ModularChevalleyLieAlgebra)) ht).trans ?_
  · exact coe_f4ShortRootLieIdealBasis_twelve.trans
      ((f4ModularCoroot_castAdd 2).symm.trans (congrArg f4ModularCoroot ha.symm))
  · exact coe_f4ShortRootLieIdealBasis_twelve.trans
      ((f4ModularCoroot_addNat_castAdd 2).symm.trans (congrArg f4ModularCoroot ha.symm))
  · exact coe_f4ShortRootLieIdealBasis_thirteen.trans
      ((f4ModularCoroot_castAdd 3).symm.trans (congrArg f4ModularCoroot ha.symm))
  · exact coe_f4ShortRootLieIdealBasis_thirteen.trans
      ((f4ModularCoroot_addNat_castAdd 3).symm.trans (congrArg f4ModularCoroot ha.symm))

private theorem f4ShortRootSignedSimpleAdjoint_basis_root_of_coeff_eq_zero (k : Fin 4 ⊕ Fin 4)
    (b : Fin 26) (β : Fin 48) (hβ : f4Length β = 1)
    (hb : f4ShortRootWeightIndexEquiv b = Sum.inl ⟨β, hβ⟩)
    (hcoeff : (f4SimpleRootCoeff k b : ZMod 2) = 0) :
    f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b) =
      (f4SimpleRootCoeff k b : ZMod 2) •
        f4ShortRootLieIdealBasis (f4SimpleRootTarget k b) := by
  have hw : f4ShortRootWeight b = f4Root β :=
    (f4ShortRootWeightIndexEquiv_apply_eq_inl_iff b ⟨β, hβ⟩).mp hb
  have hzero := f4SimpleRootTable_root_zero_cases k b β hβ hw hcoeff
  have haction : f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b) = 0 := by
    apply Subtype.ext
    rw [coe_f4ShortRootSignedSimpleAdjoint_apply, ZeroMemClass.coe_zero,
      coe_f4ShortRootLieIdealBasis_of_weight_eq_root b β hβ hw]
    rcases hzero with heq | hlong | hnone
    · subst β
      exact lie_self _
    · obtain ⟨hα, γ, hγ, hadd⟩ := hlong
      exact f4Modular_lie_rootVector_eq_zero_of_short_add_short_eq_long
        (f4SignedSimpleRootIndex k) β γ hα hβ hγ (by
          simpa only [f4SimplyConnectedRootDatum_root] using hadd)
    · obtain ⟨hne, hopp, hpair⟩ := hnone
      have hne' : f4SignedSimpleRootIndex k ≠ β := Ne.symm hne
      have hopp' : f4SignedSimpleRootIndex k ≠ f4OppositeRootIndex β := by
        intro h
        apply hopp
        simpa using (congrArg f4OppositeRootIndex h).symm
      apply f4Modular_lie_rootVector_eq_zero_of_chainTopCoeff_eq_zero _ _ hne' hopp'
      rcases hpair with hpair | ⟨hα, hpair⟩
      · exact f4_chainTopCoeff_eq_zero_of_short_pairing_eq_one _ _ hβ hpair
      · exact f4_chainTopCoeff_eq_zero_of_short_long_pairing_eq_zero _ _ hα hβ hpair
  calc
    _ = 0 := haction
    _ = (0 : ZMod 2) • f4ShortRootLieIdealBasis (f4SimpleRootTarget k b) :=
      (zero_smul _ _).symm
    _ = _ := congrArg (fun c : ZMod 2 => c •
      f4ShortRootLieIdealBasis (f4SimpleRootTarget k b)) hcoeff.symm

private theorem f4ShortRootSignedSimpleAdjoint_basis_root_opposite (k : Fin 4 ⊕ Fin 4)
    (b : Fin 26) (β : Fin 48) (hβ : f4Length β = 1)
    (hb : f4ShortRootWeightIndexEquiv b = Sum.inl ⟨β, hβ⟩)
    (hopp : β = f4OppositeRootIndex (f4SignedSimpleRootIndex k)) :
    f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b) =
      f4ShortRootLieIdealBasis (f4SimpleRootTarget k b) := by
  have hw : f4ShortRootWeight b = f4Root β :=
    (f4ShortRootWeightIndexEquiv_apply_eq_inl_iff b ⟨β, hβ⟩).mp hb
  have hwopp : f4ShortRootWeight b =
      f4Root (f4OppositeRootIndex (f4SignedSimpleRootIndex k)) := by rw [hw, hopp]
  have hbidx : b = f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨β, hβ⟩) := by
    rw [← hb, Equiv.symm_apply_apply]
  refine Subtype.ext (Eq.trans ?_
    (coe_f4ShortRootLieIdealBasis_simpleRootTarget_of_opposite k b hwopp).symm)
  rw [f4ShortRootSignedSimpleAdjoint_apply, hbidx]
  subst hopp
  exact coe_f4ShortRootAdjoint_opposite _ hβ

private theorem f4ShortRootSignedSimpleAdjoint_basis_root_edge (k : Fin 4 ⊕ Fin 4)
    (b : Fin 26) (β γ : Fin 48) (hβ : f4Length β = 1) (hγ : f4Length γ = 1)
    (hb : f4ShortRootWeightIndexEquiv b = Sum.inl ⟨β, hβ⟩)
    (hadd : f4Root γ = f4Root β + f4Root (f4SignedSimpleRootIndex k))
    (htarget : f4ShortRootWeight (f4SimpleRootTarget k b) = f4Root γ) :
    f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b) =
      f4ShortRootLieIdealBasis (f4SimpleRootTarget k b) := by
  have hbidx : b = f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨β, hβ⟩) := by
    rw [← hb, Equiv.symm_apply_apply]
  have htargetidx : f4SimpleRootTarget k b =
      f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨γ, hγ⟩) := by
    rw [← (f4ShortRootWeightIndexEquiv_apply_eq_inl_iff (f4SimpleRootTarget k b) ⟨γ, hγ⟩).2
      htarget, Equiv.symm_apply_apply]
  refine Eq.trans ?_ (congrArg f4ShortRootLieIdealBasis htargetidx).symm
  rw [f4ShortRootSignedSimpleAdjoint_apply, hbidx]
  exact f4ShortRootAdjoint_rootVector_of_add_eq_short
    (f4SignedSimpleRootIndex k) β γ hβ hγ
    (by simpa only [f4SimplyConnectedRootDatum_root] using hadd)

private theorem f4ShortRootSignedSimpleAdjoint_basis_root_of_coeff_ne_zero (k : Fin 4 ⊕ Fin 4)
    (b : Fin 26) (β : Fin 48) (hβ : f4Length β = 1)
    (hb : f4ShortRootWeightIndexEquiv b = Sum.inl ⟨β, hβ⟩)
    (hcoeff : (f4SimpleRootCoeff k b : ZMod 2) ≠ 0) :
    f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b) =
      (f4SimpleRootCoeff k b : ZMod 2) •
        f4ShortRootLieIdealBasis (f4SimpleRootTarget k b) := by
  have hw : f4ShortRootWeight b = f4Root β :=
    (f4ShortRootWeightIndexEquiv_apply_eq_inl_iff b ⟨β, hβ⟩).mp hb
  have hcoeff' := f4SimpleRootTable_coeff_eq_one k b hcoeff
  have hone := f4SimpleRootTable_root_nonzero_cases k b β hβ hw hcoeff
  have hscalar : f4ShortRootLieIdealBasis (f4SimpleRootTarget k b) =
      (f4SimpleRootCoeff k b : ZMod 2) •
        f4ShortRootLieIdealBasis (f4SimpleRootTarget k b) := by
    calc
      _ = (1 : ZMod 2) • f4ShortRootLieIdealBasis (f4SimpleRootTarget k b) :=
        (one_smul _ _).symm
      _ = _ := congrArg (fun c : ZMod 2 =>
        c • f4ShortRootLieIdealBasis (f4SimpleRootTarget k b)) hcoeff'.symm
  refine Eq.trans ?_ hscalar
  rcases hone with hopp | ⟨γ, hγ, hadd, htarget⟩
  · exact f4ShortRootSignedSimpleAdjoint_basis_root_opposite k b β hβ hb hopp
  · exact f4ShortRootSignedSimpleAdjoint_basis_root_edge k b β γ hβ hγ hb hadd htarget

private theorem f4SimpleRootTable_cartan_column (k : Fin 4 ⊕ Fin 4)
    (b : Fin 26) (s : Fin 4) (hbs : (b = 12 ∧ s = 2) ∨ (b = 13 ∧ s = 3)) :
    (f4SimpleRootCoeff k b : ZMod 2) =
        -(f4SimplyConnectedRootDatum.pairing (f4SignedSimpleRootIndex k)
          (Fin.castAdd 44 s) : ZMod 2) ∧
      ((f4SimpleRootCoeff k b : ZMod 2) = 0 ∨
        ∃ _hα : f4Length (f4SignedSimpleRootIndex k) = 1,
          f4ShortRootWeight (f4SimpleRootTarget k b) =
            f4Root (f4SignedSimpleRootIndex k)) := by
  rcases hbs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases k with
    | inl i =>
        simp only [f4SignedSimpleRootIndex_inl, f4SimpleRootTarget,
          f4SimplyConnectedRootDatum_pairing]
        rw [f4Length_def]
        revert i
        decide +kernel
    | inr i =>
        simp only [f4SignedSimpleRootIndex_inr, f4SimpleRootTarget,
          f4OppositeRootIndex_castAdd, f4SimplyConnectedRootDatum_pairing]
        rw [f4Length_def]
        revert i
        decide +kernel

private theorem f4ShortRootSignedSimpleAdjoint_basis_cartan (k : Fin 4 ⊕ Fin 4)
    (b : Fin 26) (s : Fin 4)
    (hbs : (b = 12 ∧ s = 2) ∨ (b = 13 ∧ s = 3))
    (hbasis : (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm s)) :
    f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b) =
      (f4SimpleRootCoeff k b : ZMod 2) •
        f4ShortRootLieIdealBasis (f4SimpleRootTarget k b) := by
  have htable := f4SimpleRootTable_cartan_column k b s hbs
  obtain ⟨hscalar, hcase⟩ := htable
  have hcast : Fin.cast rank_F4 (Fin.cast rank_F4.symm s) = s := by
    apply Fin.ext
    rfl
  have hs : Fin.cast rank_F4 (Fin.cast rank_F4.symm s) = 2 ∨
      Fin.cast rank_F4 (Fin.cast rank_F4.symm s) = 3 := by
    rw [hcast]
    exact hbs.imp And.right And.right
  -- The Cartan column is the simple-coroot coordinate, so the action is the one packaged by
  -- `coe_f4ShortRootAdjoint_simpleCoroot`.
  have hadj : f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b) =
      f4ShortRootAdjoint (f4ModularRootVector (f4SignedSimpleRootIndex k))
        ⟨f4ModularSimpleCoroot (Fin.cast rank_F4.symm s),
          mem_f4ShortRootLieIdeal_iff.mpr
            (f4ModularSimpleCoroot_mem_shortRootSubspace _ hs)⟩ :=
    (by
      exact (f4ShortRootSignedSimpleAdjoint_apply k _).trans
        (congrArg (fun y : f4ShortRootLieIdeal =>
        f4ShortRootAdjoint (f4ModularRootVector (f4SignedSimpleRootIndex k)) y)
        (Subtype.ext hbasis)))
  have haction :
      (f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b) :
        f4ModularChevalleyLieAlgebra) =
          (f4SimpleRootCoeff k b : ZMod 2) •
            f4ModularRootVector (f4SignedSimpleRootIndex k) :=
    ((congrArg (fun y : f4ShortRootLieIdeal =>
      (y : f4ModularChevalleyLieAlgebra)) hadj).trans
        (coe_f4ShortRootAdjoint_simpleCoroot (f4SignedSimpleRootIndex k) _ hs)).trans (by
          rw [hcast, hscalar])
  rcases hcase with hzero | hnonzero
  · apply Subtype.ext
    simpa only [hzero, zero_smul, Submodule.coe_zero] using haction
  · obtain ⟨hα, htarget⟩ := hnonzero
    have htargetvec :=
      coe_f4ShortRootLieIdealBasis_of_weight_eq_root _ _ hα htarget
    apply Subtype.ext
    calc
      (f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b) :
          f4ModularChevalleyLieAlgebra) =
          (f4SimpleRootCoeff k b : ZMod 2) •
            f4ModularRootVector (f4SignedSimpleRootIndex k) := haction
      _ = (f4SimpleRootCoeff k b : ZMod 2) •
          (f4ShortRootLieIdealBasis (f4SimpleRootTarget k b) :
            f4ModularChevalleyLieAlgebra) := congrArg
              (fun x : f4ModularChevalleyLieAlgebra =>
                (f4SimpleRootCoeff k b : ZMod 2) • x) htargetvec.symm

private theorem f4ShortRootSignedSimpleAdjoint_basis_twelve (k : Fin 4 ⊕ Fin 4) :
    f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis 12) =
      (f4SimpleRootCoeff k 12 : ZMod 2) •
        f4ShortRootLieIdealBasis (f4SimpleRootTarget k 12) := by
  exact f4ShortRootSignedSimpleAdjoint_basis_cartan k 12 2
    (Or.inl ⟨rfl, rfl⟩) coe_f4ShortRootLieIdealBasis_twelve

private theorem f4ShortRootSignedSimpleAdjoint_basis_thirteen (k : Fin 4 ⊕ Fin 4) :
    f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis 13) =
      (f4SimpleRootCoeff k 13 : ZMod 2) •
        f4ShortRootLieIdealBasis (f4SimpleRootTarget k 13) := by
  exact f4ShortRootSignedSimpleAdjoint_basis_cartan k 13 3
    (Or.inr ⟨rfl, rfl⟩) coe_f4ShortRootLieIdealBasis_thirteen

private theorem f4ShortRootSignedSimpleAdjoint_basis_of_weight_ne_zero
    (k : Fin 4 ⊕ Fin 4) (b : Fin 26) (hnz : f4ShortRootWeight b ≠ 0) :
    f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b) =
      (f4SimpleRootCoeff k b : ZMod 2) •
        f4ShortRootLieIdealBasis (f4SimpleRootTarget k b) := by
  have hex := (f4ShortRootWeight_ne_zero_iff_exists_shortRoot b).mp hnz
  let β : Fin 48 := Classical.choose hex
  have hβ : f4Length β = 1 := (Classical.choose_spec hex).1
  have hw : f4Root β = f4ShortRootWeight b := (Classical.choose_spec hex).2
  have hb : f4ShortRootWeightIndexEquiv b = Sum.inl ⟨β, hβ⟩ :=
    (f4ShortRootWeightIndexEquiv_apply_eq_inl_iff b ⟨β, hβ⟩).2 hw.symm
  by_cases hcoeff : (f4SimpleRootCoeff k b : ZMod 2) = 0
  · exact f4ShortRootSignedSimpleAdjoint_basis_root_of_coeff_eq_zero k b β hβ hb hcoeff
  · exact f4ShortRootSignedSimpleAdjoint_basis_root_of_coeff_ne_zero k b β hβ hb hcoeff

private theorem f4ShortRootSignedSimpleAdjoint_basis (k : Fin 4 ⊕ Fin 4) (b : Fin 26) :
    f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b) =
      (f4SimpleRootCoeff k b : ZMod 2) •
        f4ShortRootLieIdealBasis (f4SimpleRootTarget k b) := by
  by_cases htwelve : b = 12
  · subst b
    exact f4ShortRootSignedSimpleAdjoint_basis_twelve k
  by_cases hthirteen : b = 13
  · subst b
    exact f4ShortRootSignedSimpleAdjoint_basis_thirteen k
  have hnz : f4ShortRootWeight b ≠ 0 := by
    intro hz
    rcases (f4ShortRootWeight_eq_zero_iff b).mp hz with hb | hb
    · exact htwelve hb
    · exact hthirteen hb
  exact f4ShortRootSignedSimpleAdjoint_basis_of_weight_ne_zero k b hnz

/-- The structural adjoint action on the modular short-root ideal is the reduction modulo two
of the original sparse root matrix. -/
theorem f4ShortRootSignedSimpleAdjointMatrix_eq_rootMatrix_map (k : Fin 4 ⊕ Fin 4) :
    f4ShortRootSignedSimpleAdjointMatrix k = (rootMatrix k).map (Int.cast : ℤ → ZMod 2) := by
  ext a b
  rw [f4ShortRootSignedSimpleAdjointMatrix_apply]
  calc
    (f4ShortRootLieIdealBasis.repr
        (f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b))) a =
        (f4ShortRootLieIdealBasis.repr
          ((f4SimpleRootCoeff k b : ZMod 2) •
            f4ShortRootLieIdealBasis (f4SimpleRootTarget k b))) a :=
      congrArg (fun x => (f4ShortRootLieIdealBasis.repr x) a)
        (f4ShortRootSignedSimpleAdjoint_basis k b)
    _ = (rootMatrix k a b : ZMod 2) := by
      have hre :
          (f4ShortRootLieIdealBasis.repr
            ((f4SimpleRootCoeff k b : ZMod 2) •
              f4ShortRootLieIdealBasis (f4SimpleRootTarget k b))) a =
            if a = f4SimpleRootTarget k b then
              (f4SimpleRootCoeff k b : ZMod 2) else 0 := by
        simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single]
        by_cases h : a = f4SimpleRootTarget k b
        · subst a
          simp
        · simp [h]
      have hroot := congrArg (fun z : ℤ => (z : ZMod 2))
        (rootMatrix_apply k a b)
      have hroot' : (rootMatrix k a b : ZMod 2) =
          if a = f4SimpleRootTarget k b then
            (f4SimpleRootCoeff k b : ZMod 2) else 0 := by
        calc
          _ = ((if a = f4SimpleRootTarget k b then
              f4SimpleRootCoeff k b else 0 : ℤ) : ZMod 2) := hroot
          _ = _ := by
            split_ifs <;> rfl
      exact hre.trans hroot'.symm
    _ = ((rootMatrix k).map (Int.cast : ℤ → ZMod 2)) a b := rfl
end

end TauCeti.DynkinType
