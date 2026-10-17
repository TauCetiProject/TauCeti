/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Binary.Orientation
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Binary isometries and reflected proper classes

An improper automorphism of an integral binary lattice exists exactly when its primitive norm
form is properly equivalent to its reflection `(a, -b, c)`. Consequently the special orthogonal
group has index two exactly in this case, and otherwise has index one.

The comparison uses the actual lattice isometry group and the existing proper action on binary
forms. It does not require an ideal-class correspondence.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, Section 2.
-/

public section

open Module Matrix
open scoped MatrixGroups

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {L : IntegralLattice V} (b : Basis (Fin 2) ℤ L)
variable {M : IntegralLattice W}

/-- Transporting a carrier basis between lattices by an isometry preserves its norm form. -/
theorem binaryNormForm_map_isometry (e : Isometry L M) :
    M.binaryNormForm (e.carrierBasisEquiv (Fin 2) b) = L.binaryNormForm b := by
  ext <;> simp only [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c,
    e.gramMatrix_carrierBasisEquiv]

/-- Equal binary norm forms in two carrier bases determine a lattice isometry taking the first
basis to the second. -/
theorem exists_isometry_map_basis_iff (b' : Basis (Fin 2) ℤ M) :
    (∃ e : Isometry L M, e.carrierBasisEquiv (Fin 2) b = b') ↔
      M.binaryNormForm b' = L.binaryNormForm b := by
  constructor
  · rintro ⟨e, rfl⟩
    exact binaryNormForm_map_isometry b e
  · intro h
    have ha := congrArg BinaryQuadraticForm.a h
    have hb := congrArg BinaryQuadraticForm.b h
    have hc := congrArg BinaryQuadraticForm.c h
    simp only [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c] at ha hb hc
    have hb' : M.gramMatrix b' 0 1 = L.gramMatrix b 0 1 :=
      mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hb
    have hg : M.gramMatrix b' = L.gramMatrix b := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact ha
      · exact hb'
      · exact ((M.isSymm_gramMatrix b').apply 0 1).trans
          (hb'.trans ((L.isSymm_gramMatrix b).apply 0 1).symm)
      · exact hc
    let e := Isometry.ofGramMatrixEq b b' hg.symm
    refine ⟨e, ?_⟩
    ext i
    simp only [Isometry.carrierBasisEquiv_apply, Basis.map_apply, Isometry.coe_carrierEquiv_apply]
    exact Isometry.ofGramMatrixEq_apply_basis b b' hg.symm i

/-- An improper lattice automorphism exists exactly when the primitive norm form is properly
equivalent to its reflection. -/
theorem exists_improper_isometry_iff :
    (∃ e : Isometry L L, Isometry.det L e = -1) ↔
      ∃ γ : SL(2, ℤ), (L.binaryNormForm b).primPart =
        γ • (L.binaryNormForm b).primPart.reflected := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨γ, hγ⟩ := L.exists_primPart_eq_smul_of_orientation_neg b
      (b.map e.carrierEquiv) ((e.orientation_map_eq_neg_iff b).mpr he)
    rw [← e.carrierBasisEquiv_apply, binaryNormForm_map_isometry] at hγ
    exact ⟨γ, hγ⟩
  · rintro ⟨γ, hγ⟩
    let bRev := b.unitsSMul (Function.update 1 (1 : Fin 2) (-1))
    let f := Matrix.toLinearEquiv bRev ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (by rw [SpecialLinearGroup.det_coe]; exact isUnit_one)
    let b' := bRev.map f
    have hf : f.toLinearMap = Matrix.toLin bRev bRev
        ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      apply LinearMap.ext
      intro x
      exact Matrix.toLinearEquiv_apply bRev _ _ x
    have hm : bRev.toMatrix b' = ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      calc
        bRev.toMatrix b' = LinearMap.toMatrix bRev bRev f.toLinearMap := by
          ext i j
          simp only [Basis.toMatrix_apply, b', Basis.map_apply, LinearMap.toMatrix_apply,
            LinearEquiv.coe_coe]
        _ = _ := by rw [hf, LinearMap.toMatrix_toLin]
    have hp : (L.binaryNormForm b').primPart = (L.binaryNormForm b).primPart := by
      rw [L.binaryNormForm_eq_inv_smul bRev b' γ⁻¹ hm,
        BinaryQuadraticForm.primPart_smul, inv_inv]
      exact (congrArg (γ • ·) (L.primPart_binaryNormForm_unitsSMul_neg b)).trans hγ.symm
    have hn : L.binaryNormForm b' = L.binaryNormForm b := by
      have h := congrArg (fun g : BinaryQuadraticForm ℤ ↦ (L.binaryNormForm b).content • g) hp
      rw [L.content_binaryNormForm_eq b b', BinaryQuadraticForm.content_smul_primPart] at h
      simpa only [← L.content_binaryNormForm_eq b b',
        BinaryQuadraticForm.content_smul_primPart] using h
    obtain ⟨e, he⟩ := (exists_isometry_map_basis_iff b b').mpr hn
    refine ⟨e, (e.orientation_map_eq_neg_iff b).mp ?_⟩
    rw [← e.carrierBasisEquiv_apply, he]
    have ho : b'.orientation = bRev.orientation := by
      apply (Basis.orientation_comp_linearEquiv_eq_iff_det_pos bRev f).mpr
      rw [hf, LinearMap.det_toLin, SpecialLinearGroup.det_coe]
      norm_num
    exact ho.trans (b.orientation_neg_single 1)

/-- The special orthogonal group has index two exactly when the primitive binary norm form
is properly equivalent to its reflection. -/
theorem index_specialOrthogonalGroup_eq_two_iff_reflected :
    (specialOrthogonalGroup L).index = 2 ↔
      ∃ γ : SL(2, ℤ), (L.binaryNormForm b).primPart =
        γ • (L.binaryNormForm b).primPart.reflected :=
  (index_specialOrthogonalGroup_eq_two_iff L).trans (exists_improper_isometry_iff b)

end TauCeti.IntegralLattice
