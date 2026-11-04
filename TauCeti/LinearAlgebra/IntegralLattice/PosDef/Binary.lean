/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Basic
public import TauCeti.NumberTheory.IntegralLattice.Binary.Isometry
import TauCeti.NumberTheory.BinaryQuadraticForm.Reduction

/-!
# The even binary lattice of determinant three

Every positive definite even integral lattice of rank two and determinant three is isometric
to `A₂`. Binary reduction supplies a basis with norm form `2x² + 2xy + 2y²`; reversing the
second vector gives the Cartan Gram matrix. This classification also determines the genus of
`A₂`, without a mass formula.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §2, reduction of positive definite binary forms.
-/

public section

open Module

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-- A positive definite even binary lattice of determinant three has a basis whose norm form
is `2x² + 2xy + 2y²`. -/
private theorem IsPosDef.exists_binaryNormForm_eq_two_two_two (hL : L.IsPosDef) (he : L.IsEven)
    (hn : finrank ℤ L = 2) (hd : L.determinant = 3) :
    ∃ b : Basis (Fin 2) ℤ L, L.binaryNormForm b = ⟨2, 2, 2⟩ := by
  let b := Module.finBasisOfFinrankEq ℤ L hn
  have hf : L.binaryNormForm b ∈ BinaryQuadraticForm.posDef 12 := by
    refine BinaryQuadraticForm.mem_posDef.mpr ⟨?_, ?_⟩
    · rw [discrim_binaryNormForm, hd]; norm_num
    · rw [binaryNormForm_a, gramMatrix_apply, ← integralNorm_apply]
      exact hL.posDef_integralNorm _ (b.ne_zero 0)
  obtain ⟨γ, hγ⟩ := BinaryQuadraticForm.exists_smul_isReducedForm ⟨_, hf⟩
  obtain ⟨b', hb'⟩ := L.exists_binaryNormForm_eq_smul b γ
  have hr : IsReducedForm (L.binaryNormForm b') := by
    simpa only [hb', SubMulAction.val_smul] using hγ
  obtain ⟨hba, hac, hsign⟩ := isReducedForm_iff.mp hr
  have hdisc := L.discrim_binaryNormForm b'
  rw [hd, BinaryQuadraticForm.discrim_def, discrim] at hdisc
  have ha : 0 < (L.binaryNormForm b').a := by
    rw [binaryNormForm_a, gramMatrix_apply, ← integralNorm_apply]
    exact hL.posDef_integralNorm _ (b'.ne_zero 0)
  have hea : Even (L.binaryNormForm b').a := by
    simpa only [binaryNormForm_a, gramMatrix_apply, ← integralNorm_apply] using
      (L.isEven_iff_basis b').mp he 0
  have hbb := sq_le_sq' (neg_le_of_abs_le hba) (le_of_abs_le hba)
  have haa := mul_le_mul_of_nonneg_left hac ha.le
  have ha2 : (L.binaryNormForm b').a = 2 := by
    obtain ⟨k, hk⟩ := hea
    have haLower : 2 ≤ (L.binaryNormForm b').a := by omega
    nlinarith [sq_nonneg ((L.binaryNormForm b').a - 2)]
  have hc2 : (L.binaryNormForm b').c = 2 := by nlinarith
  have hb2 : (L.binaryNormForm b').b = 2 := by
    have := hsign (Or.inr (ha2.trans hc2.symm))
    nlinarith
  exact ⟨b', BinaryQuadraticForm.ext ha2 hb2 hc2⟩

/-- **Uniqueness of `A₂`.** Every positive definite even rank-two lattice of determinant three
is isometric to the `A₂` root lattice. -/
theorem IsPosDef.nonempty_isometry_typeARootLattice_two (hL : L.IsPosDef) (he : L.IsEven)
    (hn : finrank ℤ L = 2) (hd : L.determinant = 3) :
    Nonempty (Isometry L (typeARootLattice 2)) := by
  obtain ⟨b, hb⟩ := hL.exists_binaryNormForm_eq_two_two_two he hn hd
  let b' := b.unitsSMul (Function.update 1 (1 : Fin 2) (-1))
  have hnorm : L.binaryNormForm b' =
      (typeARootLattice 2).binaryNormForm (typeASimpleRootBasis 2) := by
    rw [binaryNormForm_unitsSMul_neg, hb]
    ext <;> simp only [BinaryQuadraticForm.reflected_a, BinaryQuadraticForm.reflected_b,
      BinaryQuadraticForm.reflected_c, binaryNormForm_a, binaryNormForm_b, binaryNormForm_c,
      gramMatrix_typeASimpleRootBasis] <;> norm_num [CartanMatrix.A]
  obtain ⟨e, -⟩ := (exists_isometry_map_basis_iff b' (typeASimpleRootBasis 2)).mpr hnorm.symm
  exact ⟨e⟩

end TauCeti.IntegralLattice
