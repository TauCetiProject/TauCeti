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

The determinant of a lattice isometry detects whether it preserves or reverses the orientation
of an integral binary basis. An improper automorphism exists exactly when the primitive norm
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
variable {L : IntegralLattice V} (b : Basis (Fin 2) ℤ L)

namespace Isometry

/-- A lattice isometry preserves a binary basis orientation exactly when its determinant is one. -/
theorem orientation_map_eq_iff (e : Isometry L L) :
    (b.map e.carrierEquiv).orientation = b.orientation ↔ det L e = 1 := by
  rw [Basis.orientation_comp_linearEquiv_eq_iff_det_pos, ← coe_det]
  rcases det_eq_one_or_neg_one e with h | h <;> simp [h]

/-- A lattice isometry reverses a binary basis orientation exactly when its determinant is minus
one. -/
theorem orientation_map_eq_neg_iff (e : Isometry L L) :
    (b.map e.carrierEquiv).orientation = -b.orientation ↔ det L e = -1 := by
  rw [Basis.orientation_comp_linearEquiv_eq_neg_iff_det_neg, ← coe_det]
  rcases det_eq_one_or_neg_one e with h | h <;> simp [h]

end Isometry

/-- Transporting a carrier basis by an isometry leaves its norm form unchanged. -/
@[simp] theorem binaryNormForm_map_isometry (e : Isometry L L) :
    L.binaryNormForm (b.map e.carrierEquiv) = L.binaryNormForm b := by
  ext <;> simp only [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c,
    gramMatrix_apply, Basis.map_apply, Isometry.carrierEquiv_map_integralForm]

/-- Equal binary norm forms in two carrier bases determine a lattice isometry taking the first
basis to the second. -/
theorem exists_isometry_map_basis_iff (b' : Basis (Fin 2) ℤ L) :
    (∃ e : Isometry L L, b.map e.carrierEquiv = b') ↔
      L.binaryNormForm b' = L.binaryNormForm b := by
  constructor
  · rintro ⟨e, rfl⟩
    exact binaryNormForm_map_isometry b e
  · intro h
    have ha := congrArg BinaryQuadraticForm.a h
    have hb := congrArg BinaryQuadraticForm.b h
    have hc := congrArg BinaryQuadraticForm.c h
    simp only [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c] at ha hb hc
    have hb' : L.gramMatrix b' 0 1 = L.gramMatrix b 0 1 :=
      mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hb
    have hg : L.gramMatrix b' = L.gramMatrix b := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact ha
      · exact hb'
      · rw [gramMatrix_apply, gramMatrix_apply]
        change L.integralForm (b' 1) (b' 0) = L.integralForm (b 1) (b 0)
        rw [L.isSymm_integralForm.eq (b' 1) (b' 0),
          L.isSymm_integralForm.eq (b 1) (b 0)]
        simpa only [gramMatrix_apply] using hb'
      · exact hc
    let e := Isometry.ofGramMatrixEq b b' hg.symm
    refine ⟨e, ?_⟩
    ext i
    simp only [Basis.map_apply, Isometry.coe_carrierEquiv_apply]
    exact Isometry.ofGramMatrixEq_apply_basis b b' hg.symm i

/-- An improper lattice automorphism exists exactly when the primitive norm form is properly
equivalent to its reflection. -/
theorem exists_improper_isometry_iff :
    (∃ e : Isometry L L, Isometry.det L e = -1) ↔
      ∃ γ : SL(2, ℤ), (L.binaryNormForm b).primPart =
        γ • (⟨(L.binaryNormForm b).primPart.a, -(L.binaryNormForm b).primPart.b,
          (L.binaryNormForm b).primPart.c⟩ : BinaryQuadraticForm ℤ) := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨γ, hγ⟩ := L.exists_primPart_eq_smul_of_orientation_neg b
      (b.map e.carrierEquiv) ((e.orientation_map_eq_neg_iff b).mpr he)
    exact ⟨γ, by simpa using hγ⟩
  · rintro ⟨γ, hγ⟩
    let bRev := b.unitsSMul (Function.update 1 (1 : Fin 2) (-1))
    let f := Matrix.toLinearEquiv bRev ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (by rw [SpecialLinearGroup.det_coe]; exact isUnit_one)
    let b' := bRev.map f
    have hm : bRev.toMatrix b' = ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      have hf : f.toLinearMap = Matrix.toLin bRev bRev
          ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl
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
    rw [he]
    have ho : b'.orientation = bRev.orientation := by
      apply (Basis.orientation_comp_linearEquiv_eq_iff_det_pos bRev f).mpr
      change 0 < LinearMap.det (Matrix.toLin bRev bRev
        ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      rw [LinearMap.det_toLin, SpecialLinearGroup.det_coe]
      norm_num
    exact ho.trans (b.orientation_neg_single 1)

/-- The special orthogonal group has index two exactly when the primitive binary norm form
is properly equivalent to its reflection. -/
theorem index_specialOrthogonalGroup_eq_two_iff_reflected :
    (specialOrthogonalGroup L).index = 2 ↔
      ∃ γ : SL(2, ℤ), (L.binaryNormForm b).primPart =
        γ • (⟨(L.binaryNormForm b).primPart.a, -(L.binaryNormForm b).primPart.b,
          (L.binaryNormForm b).primPart.c⟩ : BinaryQuadraticForm ℤ) :=
  (index_specialOrthogonalGroup_eq_two_iff L).trans (exists_improper_isometry_iff b)

end TauCeti.IntegralLattice
