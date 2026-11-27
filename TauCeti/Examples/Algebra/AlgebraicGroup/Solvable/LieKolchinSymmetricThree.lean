/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Representation
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.SchemeProperties
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Vector

import Mathlib.Data.Nat.Squarefree

/-!
# Check: Lie–Kolchin needs connectedness

The constant group scheme `S₃` over `ℂ` has solvable group of points
(`TauCeti.Examples.LieKolchinSymmetricThree.isSolvable`) and is not connected
(`TauCeti.Examples.LieKolchinSymmetricThree.not_connectedSpace`), and its two-dimensional
representation on the sum-zero vectors of `ℂ³`, with `S₃` permuting the coordinates, has no
nonzero weight vector (`TauCeti.Examples.LieKolchinSymmetricThree.not_hasNonzeroWeightVector`):
a weight vector would be a common eigenvector of the transposition `(0 1)` and the cycle
`(0 1 2)`, and these have none on the sum-zero plane. So the conclusion of the Lie–Kolchin
theorem (`TauCeti.Comodule.hasNonzeroWeightVector_of_nonzeroJointWeight_commutator` and its
corollaries need a connected group) fails for this disconnected solvable group.
-/

public section

open Equiv TauCeti

noncomputable section

namespace TauCeti.Examples.LieKolchinSymmetricThree

/-- `S₃` is solvable: its order `6` is squarefree, so it is a Z-group. -/
theorem isSolvable : Group.IsSolvable (Perm (Fin 3)) :=
  have : IsZGroup (Perm (Fin 3)) := IsZGroup.of_squarefree <| by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    change Squarefree (2 * 3)
    exact Nat.squarefree_mul_iff.mpr
      ⟨by norm_num, Nat.prime_two.prime.squarefree, Nat.prime_three.prime.squarefree⟩
  inferInstance

/-- The constant group scheme `S₃` over `ℂ` is not connected. -/
theorem not_connectedSpace :
    ¬ConnectedSpace (ConstantGroup.groupScheme ℂ (Perm (Fin 3))).X.left :=
  ConstantGroup.not_connectedSpace_groupScheme (G := Perm (Fin 3)) ℂ

/-- The permutation representation of `S₃` on `ℂ³`: `σ` sends `v` to `v ∘ σ⁻¹`. -/
def permRep : Representation ℂ (Perm (Fin 3)) (Fin 3 → ℂ) where
  toFun σ := LinearMap.funLeft ℂ ℂ (⇑σ⁻¹)
  map_one' := by
    ext v i
    simp
  map_mul' σ τ := by
    ext v i
    simp [LinearMap.funLeft_apply, mul_inv_rev]

/-- The permutation representation sends `v` to `v ∘ σ⁻¹`. -/
theorem permRep_apply (σ : Perm (Fin 3)) (v : Fin 3 → ℂ) (i : Fin 3) :
    permRep σ v i = v (σ⁻¹ i) :=
  (rfl)

/-- The sum-zero vectors of `ℂ³`. -/
def sumZero : Submodule ℂ (Fin 3 → ℂ) :=
  LinearMap.ker (Fintype.linearCombination ℂ (fun _ : Fin 3 ↦ (1 : ℂ)))

/-- A vector lies in `sumZero` when its coordinates sum to zero. -/
theorem mem_sumZero_iff {v : Fin 3 → ℂ} : v ∈ sumZero ↔ v 0 + v 1 + v 2 = 0 := by
  simp [sumZero, Fintype.linearCombination_apply, Fin.sum_univ_three]

/-- The permutations preserve the sum-zero vectors. -/
theorem sumZero_le_comap (σ : Perm (Fin 3)) : sumZero ≤ sumZero.comap (permRep σ) := by
  intro v hv
  simp only [sumZero, LinearMap.mem_ker, Fintype.linearCombination_apply, smul_eq_mul, mul_one,
    Submodule.mem_comap, permRep_apply] at hv ⊢
  rw [Equiv.sum_comp σ⁻¹ v]
  exact hv

/-- The two-dimensional representation of `S₃` on the sum-zero vectors of `ℂ³`. -/
def stdRep : Representation ℂ (Perm (Fin 3)) sumZero :=
  permRep.subrepresentation sumZero sumZero_le_comap

/-- The two-dimensional representation permutes the coordinates. -/
theorem coe_stdRep_apply (σ : Perm (Fin 3)) (v : sumZero) (i : Fin 3) :
    (stdRep σ v : Fin 3 → ℂ) i = (v : Fin 3 → ℂ) (σ⁻¹ i) :=
  (rfl)

/-- The transposition `(0 1)` and the cycle `(0 1 2)` have no common eigenvector on the sum-zero
vectors. -/
theorem eq_zero_of_forall_exists_smul {v : sumZero}
    (hv : ∀ σ : Perm (Fin 3), ∃ a : ℂ, stdRep σ v = a • v) : v = 0 := by
  obtain ⟨a, ha⟩ := hv (swap 0 1)
  obtain ⟨b, hb⟩ := hv (finRotate 3)
  have hs := (mem_sumZero_iff.mp v.property)
  have ha' (i : Fin 3) := congrFun (congrArg Subtype.val ha) i
  have hb' (i : Fin 3) := congrFun (congrArg Subtype.val hb) i
  simp only [coe_stdRep_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at ha' hb'
  have a0 := ha' 0
  have a1 := ha' 1
  have a2 := ha' 2
  have b0 := hb' 0
  have b1 := hb' 1
  have b2 := hb' 2
  have s0 : (swap (0 : Fin 3) 1)⁻¹ 0 = 1 := by decide
  have s1 : (swap (0 : Fin 3) 1)⁻¹ 1 = 0 := by decide
  have s2 : (swap (0 : Fin 3) 1)⁻¹ 2 = 2 := by decide
  have r0 : (finRotate 3)⁻¹ 0 = 2 := by decide
  have r1 : (finRotate 3)⁻¹ 1 = 0 := by decide
  have r2 : (finRotate 3)⁻¹ 2 = 1 := by decide
  rw [s0] at a0
  rw [s1] at a1
  rw [s2] at a2
  rw [r0] at b0
  rw [r1] at b1
  rw [r2] at b2
  have hx : (v : Fin 3 → ℂ) 0 = 0 := by
    by_contra hx
    have e1 : 1 + b + b ^ 2 = 0 :=
      mul_left_cancel₀ hx (by linear_combination hs - b0 - b2 - b * b0)
    have ea : a = b ^ 2 := mul_left_cancel₀ hx (by linear_combination -a0 + b2 + b * b0)
    have eb : b = a * b := mul_left_cancel₀ hx (by linear_combination -b0 + a2 + a * b0)
    have hb0 : b ≠ 0 := by
      rintro rfl
      norm_num at e1
    have ha1 : a = 1 := (mul_left_cancel₀ hb0 (by linear_combination eb : b * 1 = b * a)).symm
    have hb : b = -2 := by linear_combination e1 + ea - ha1
    have h3 : (3 : ℂ) = 0 := by linear_combination (ha1 - ea) - (b - 2) * hb
    norm_num at h3
  have hz : (v : Fin 3 → ℂ) 2 = 0 := by rw [b0, hx, mul_zero]
  have hy : (v : Fin 3 → ℂ) 1 = 0 := by rw [b2, hz, mul_zero]
  refine Subtype.ext (funext fun i ↦ ?_)
  fin_cases i
  exacts [hx, hy, hz]

/-- **The two-dimensional representation of `S₃` has no weight vector.** As a comodule over the
coordinate ring of the constant group `S₃` over `ℂ`, the sum-zero vectors of `ℂ³` have no nonzero
weight vector, although the group of points `S₃` is solvable: the constant group is not
connected. -/
theorem not_hasNonzeroWeightVector :
    letI := ConstantGroup.representationComodule ℂ stdRep
    ¬Comodule.HasNonzeroWeightVector ℂ (ConstantGroup.coordinateRing ℂ (Perm (Fin 3))) sumZero := by
  let := ConstantGroup.representationComodule ℂ stdRep
  rw [Comodule.hasNonzeroWeightVector_iff]
  rintro ⟨v, c, hv, -, hcoact⟩
  refine hv (eq_zero_of_forall_exists_smul fun σ ↦ ⟨(ConstantGroup.toPoints ℂ _ σ).ofConv c, ?_⟩)
  rw [← ConstantGroup.basePointsRepresentation_toPoints, Comodule.basePointsRepresentation_apply,
    Comodule.endOfPoint_tmul, hcoact]
  simp

end TauCeti.Examples.LieKolchinSymmetricThree
