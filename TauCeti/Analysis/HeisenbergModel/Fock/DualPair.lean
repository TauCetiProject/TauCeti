/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Fock.Basic
import TauCeti.Analysis.Matrix.Kronecker

/-!
# Commuting unitary actions on matrix Fock space

For signs `ε` on rows and `ε'` on columns, the action `x ↦ h x g⁻¹` preserves the
Hermitian form with signs `ε r * ε' c`. Pulling back the Weil representation along this
homomorphism gives commuting actions on matrix Fock space. Multiplying by arbitrary integral
powers of the two determinants preserves the bounded positive definite sesquilinear form.
We prove joint continuity, the Heisenberg intertwining law, and an operator bound in terms of
the two unitary matrices, with exponent the number of entries.

These are the continuous group actions underlying the oscillator representation; no
infinitesimal action or assertion about harmonic vectors is made here.

## References

* M. Kashiwara, M. Vergne, *On the Segal–Shale–Weil representations and harmonic polynomials*,
  Invent. Math. 44 (1978), 1–48.
* R. Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989), 535–552.
-/

public noncomputable section

open Matrix Complex
open scoped Kronecker ComplexConjugate

namespace TauCeti.Fock

variable {R C : Type*}
variable (ε : R → ℤˣ) (ε' : C → ℤˣ)

/-- The signs of the Hermitian form on matrix entries. -/
def pairSigns (i : R × C) : ℤˣ := ε i.1 * ε' i.2

@[simp]
theorem pairSigns_apply (r : R) (c : C) : pairSigns ε ε' (r, c) = ε r * ε' c := (rfl)

variable [DecidableEq R] [DecidableEq C]

/-- The matrix-entry Gram matrix is the Kronecker product of the two signed Gram matrices. -/
theorem signMatrix_pairSigns :
    signMatrix (pairSigns ε ε') = signMatrix ε ⊗ₖ signMatrix ε' := by
  simp [signMatrix_eq_diagonal, diagonal_kronecker_diagonal, pairSigns]

variable [Fintype R] [Fintype C]

/-- The action of a unitary pair on matrix entries: `x ↦ h x g⁻¹`. -/
def pairHom : unitaryGroup ε × unitaryGroup ε' →* unitaryGroup (pairSigns ε ε') where
  toFun p := Matrix.unitaryGroupOf.ofMatrix (isUnit_signMatrix (ε := pairSigns ε ε'))
    (((p.1 : GL R ℂ) : Matrix R R ℂ) ⊗ₖ ((p.2⁻¹ : GL C ℂ) : Matrix C C ℂ)ᵀ) (by
      have hg := (Matrix.mem_unitaryGroupOf_iff' (isUnit_signMatrix (ε := ε'))).mp p.2⁻¹.property
      rw [inv_signMatrix] at hg
      have ht := congrArg Matrix.transpose hg
      -- Transposition turns preservation of the inverse form into preservation by the dual.
      have hd : star (((p.2⁻¹ : GL C ℂ) : Matrix C C ℂ)ᵀ) * signMatrix ε' *
          ((p.2⁻¹ : GL C ℂ) : Matrix C C ℂ)ᵀ = signMatrix ε' := by
        simpa [transpose_mul, star_eq_conjTranspose, signMatrix_eq_diagonal, Matrix.mul_assoc,
          conjTranspose_transpose_eq_transpose_conjTranspose] using ht
      rw [signMatrix_pairSigns, star_eq_conjTranspose, conjTranspose_kronecker,
        ← mul_kronecker_mul, ← mul_kronecker_mul]
      exact congrArg₂ (fun a b ↦ a ⊗ₖ b)
        (Matrix.mem_unitaryGroupOf_iff.mp p.1.property) hd)
  map_one' := by
    apply Matrix.unitaryGroupOf.ext
    simp [Matrix.unitaryGroupOf.val_ofMatrix]
  map_mul' p q := by
    apply Matrix.unitaryGroupOf.ext
    simp [Matrix.unitaryGroupOf.val_ofMatrix, _root_.mul_inv_rev, transpose_mul,
      mul_kronecker_mul]

@[simp]
theorem pairHom_val (p : unitaryGroup ε × unitaryGroup ε') :
    ((pairHom ε ε' p : GL (R × C) ℂ) : Matrix (R × C) (R × C) ℂ) =
      ((p.1 : GL R ℂ) : Matrix R R ℂ) ⊗ₖ ((p.2⁻¹ : GL C ℂ) : Matrix C C ℂ)ᵀ := by
  exact Matrix.unitaryGroupOf.val_ofMatrix _ _ _

/-- Entry formula for the action of a unitary pair. -/
@[simp]
theorem pairHom_apply (p : unitaryGroup ε × unitaryGroup ε') (i j : R × C) :
    ((pairHom ε ε' p : GL (R × C) ℂ) : Matrix (R × C) (R × C) ℂ) i j =
      ((p.1 : GL R ℂ) : Matrix R R ℂ) i.1 j.1 *
        ((p.2⁻¹ : GL C ℂ) : Matrix C C ℂ) j.2 i.2 := by
  rw [pairHom_val]
  rfl

/-- The entry action is left multiplication and inverse right multiplication on matrices. -/
theorem pairHom_smul (p : unitaryGroup ε × unitaryGroup ε') (x : Matrix R C ℂ) :
    pairHom ε ε' p • (fun i : R × C ↦ x i.1 i.2) =
      fun i : R × C ↦ (((p.1 : GL R ℂ) : Matrix R R ℂ) * x *
        ((p.2⁻¹ : GL C ℂ) : Matrix C C ℂ)) i.1 i.2 := by
  ext i
  simp only [smul_def, pairHom_val, mulVec, dotProduct, kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.mul_apply, Finset.sum_mul, transpose_apply]
  rw [Finset.sum_comm]
  congr 1
  ext c
  congr 1
  ext r
  ring

/-- The homomorphism on matrix entries is continuous. -/
theorem continuous_pairHom : Continuous (pairHom ε ε') := by
  apply (Matrix.unitaryGroupOf.isClosedEmbedding_val
    (isUnit_signMatrix (ε := pairSigns ε ε'))).isEmbedding.continuous_iff.mpr
  simp only [Function.comp_def, pairHom_val]
  exact continuous_pi fun i ↦ continuous_pi fun j ↦ by
    simp only [kroneckerMap_apply, transpose_apply]
    exact (((Units.continuous_val.comp continuous_subtypeVal).comp
      continuous_fst).matrix_elem _ _).mul
      (((Units.continuous_coe_inv.comp continuous_subtypeVal).comp continuous_snd).matrix_elem _ _)

/-- The two determinant characters, with integral weights, as one unit-valued character. -/
def pairCharacter (γ γ' : ℤ) : unitaryGroup ε × unitaryGroup ε' →* ℂˣ where
  toFun p := (p.1 : GL R ℂ).det ^ γ * (p.2 : GL C ℂ).det ^ γ'
  map_one' := by simp
  map_mul' p q := by simp [mul_zpow, mul_left_comm, mul_assoc]

/-- Evaluate the determinant character. Explicit rewriting preserves the norm simplifier. -/
theorem pairCharacter_apply (γ γ' : ℤ) (p : unitaryGroup ε × unitaryGroup ε') :
    pairCharacter ε ε' γ γ' p = (p.1 : GL R ℂ).det ^ γ * (p.2 : GL C ℂ).det ^ γ' := (rfl)

/-- The determinant character has modulus one, for every pair of integer weights. -/
@[simp]
theorem norm_pairCharacter (γ γ' : ℤ) (p : unitaryGroup ε × unitaryGroup ε') :
    ‖(pairCharacter ε ε' γ γ' p : ℂ)‖ = 1 := by
  have hr := CStarRing.norm_of_mem_unitary
    (Matrix.det_mem_unitary_of_mem_unitaryGroupOf (isUnit_signMatrix (ε := ε)) p.1.property)
  have hc := CStarRing.norm_of_mem_unitary
    (Matrix.det_mem_unitary_of_mem_unitaryGroupOf (isUnit_signMatrix (ε := ε')) p.2.property)
  simp only [pairCharacter_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul,
    norm_zpow, GeneralLinearGroup.val_det_apply, hr, hc, _root_.one_zpow, mul_one]

/-- The scalar determinant character is continuous. -/
theorem continuous_pairCharacter (γ γ' : ℤ) :
    Continuous fun p ↦ (pairCharacter ε ε' γ γ' p : ℂ) := by
  have hr : Continuous fun p : unitaryGroup ε × unitaryGroup ε' ↦
      (((p.1 : GL R ℂ).det : ℂˣ) : ℂ) ^ γ := by
    apply Continuous.zpow₀
    · exact ((Units.continuous_val.comp continuous_subtypeVal).comp continuous_fst).matrix_det
    · intro p
      exact Or.inl (Units.ne_zero ((p.1 : GL R ℂ).det))
  have hc : Continuous fun p : unitaryGroup ε × unitaryGroup ε' ↦
      (((p.2 : GL C ℂ).det : ℂˣ) : ℂ) ^ γ' := by
    apply Continuous.zpow₀
    · exact ((Units.continuous_val.comp continuous_subtypeVal).comp continuous_snd).matrix_det
    · intro p
      exact Or.inl (Units.ne_zero ((p.2 : GL C ℂ).det))
  apply (hr.mul hc).congr
  intro p
  simp [pairCharacter_apply]

/-- Determinant-twisted Weil action of a pair of unitary groups on matrix Fock space. -/
def pairWeil (γ γ' : ℤ) : unitaryGroup ε × unitaryGroup ε' →*
    FockSpace (pairSigns ε ε') →L[ℂ] FockSpace (pairSigns ε ε') where
  toFun p := (pairCharacter ε ε' γ γ' p : ℂ) • weilRep _ (pairHom ε ε' p)
  map_one' := by simp
  map_mul' p q := by
    simp only [map_mul, Units.val_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm]

/-- Unfold the determinant twist without unfolding the underlying Weil representation. -/
theorem pairWeil_def (γ γ' : ℤ) (p : unitaryGroup ε × unitaryGroup ε') :
    pairWeil ε ε' γ γ' p =
      (pairCharacter ε ε' γ γ' p : ℂ) • weilRep _ (pairHom ε ε' p) := (rfl)

/-- Evaluate the twisted action. Explicit rewriting preserves the inner-form simplifier. -/
theorem pairWeil_apply (γ γ' : ℤ) (p : unitaryGroup ε × unitaryGroup ε')
    (v : FockSpace (pairSigns ε ε')) :
    pairWeil ε ε' γ γ' p v =
      (pairCharacter ε ε' γ γ' p : ℂ) • (weilRep _ (pairHom ε ε' p) v) := (rfl)

/-- Determinant twists preserve the bounded positive definite form of the Fock model. -/
@[simp]
theorem innerSL_pairWeil (γ γ' : ℤ) (p : unitaryGroup ε × unitaryGroup ε')
    (v w : FockSpace (pairSigns ε ε')) :
    ReproducingModel.innerSL (pairWeil ε ε' γ γ' p v) (pairWeil ε ε' γ γ' p w) =
      ReproducingModel.innerSL v w := by
  simp only [pairWeil_apply, map_smulₛₗ, smul_apply, RingHom.id_apply, starRingEnd_apply,
    smul_eq_mul]
  rw [mul_left_comm, ← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, norm_pairCharacter, one_pow, Complex.ofReal_one, one_mul]
  exact ReproducingModel.innerSL_weilRep (multiplier _) (pairHom ε ε' p) v w cocycle_multiplier

/-- The determinant-twisted action is jointly continuous. -/
theorem continuous_pairWeil (γ γ' : ℤ) :
    Continuous fun p : (unitaryGroup ε × unitaryGroup ε') × FockSpace (pairSigns ε ε') ↦
      pairWeil ε ε' γ γ' p.1 p.2 := by
  exact (((continuous_pairCharacter ε ε' γ γ').comp continuous_fst).smul
    ((continuous_weilRep (ε := pairSigns ε ε')).comp
      (((continuous_pairHom ε ε').comp continuous_fst).prodMk continuous_snd)))

/-- The pair action carries a Heisenberg translation to the translation of `h x g⁻¹`. -/
theorem pairWeil_heisenbergRep (γ γ' : ℤ) (p : unitaryGroup ε × unitaryGroup ε')
    (x : R × C → ℂ) (v : FockSpace (pairSigns ε ε')) :
    pairWeil ε ε' γ γ' p (ReproducingModel.heisenbergRep x v) =
      ReproducingModel.heisenbergRep (pairHom ε ε' p • x) (pairWeil ε ε' γ γ' p v) := by
  simp only [pairWeil_apply, ReproducingModel.weilRep_heisenbergRep, map_smul]

/-- The two determinant-twisted unitary actions commute. -/
theorem pairWeil_commute (γ γ' : ℤ) (h : unitaryGroup ε) (g : unitaryGroup ε') :
    Commute (pairWeil ε ε' γ γ' (h, 1)) (pairWeil ε ε' γ γ' (1, g)) :=
  (Commute.prod (Commute.one_right h) (Commute.one_left g)).map _

open scoped Matrix.Norms.L2Operator in
/-- The action on matrix entries has norm bounded by the product of the two group norms. -/
theorem norm_pairHom_le (p : unitaryGroup ε × unitaryGroup ε') :
    ‖((pairHom ε ε' p : GL (R × C) ℂ) : Matrix (R × C) (R × C) ℂ)‖ ≤
      ‖((p.1 : GL R ℂ) : Matrix R R ℂ)‖ * ‖((p.2 : GL C ℂ) : Matrix C C ℂ)‖ := by
  rw [pairHom_val]
  refine (Matrix.l2_opNorm_kronecker_le _ _).trans_eq ?_
  rw [Matrix.l2_opNorm_transpose,
    Matrix.norm_val_inv_of_mem_unitaryGroupOf signMatrix_mem_unitary p.2.property]

open scoped Matrix.Norms.L2Operator in
/-- Polynomial growth of the pair action, independently of the determinant weights. -/
theorem norm_pairWeil_le (γ γ' : ℤ) (p : unitaryGroup ε × unitaryGroup ε') :
    ‖pairWeil ε ε' γ γ' p‖ ≤
      ‖(ReproducingModel.vacuum : FockSpace (pairSigns ε ε'))‖ *
        (‖((p.1 : GL R ℂ) : Matrix R R ℂ)‖ *
          ‖((p.2 : GL C ℂ) : Matrix C C ℂ)‖) ^ Fintype.card (R × C) := by
  rw [pairWeil_def, norm_smul, norm_pairCharacter, one_mul]
  exact (norm_weilRep_le _).trans (by gcongr; exact norm_pairHom_le ε ε' p)

open scoped Matrix.Norms.L2Operator in
/-- Polynomial growth for the action of the row group alone. -/
theorem norm_pairWeil_left_le (γ γ' : ℤ) (h : unitaryGroup ε) :
    ‖pairWeil ε ε' γ γ' (h, 1)‖ ≤
      ‖(ReproducingModel.vacuum : FockSpace (pairSigns ε ε'))‖ *
        ‖((h : GL R ℂ) : Matrix R R ℂ)‖ ^ Fintype.card (R × C) := by
  refine (norm_pairWeil_le ε ε' γ γ' (h, 1)).trans ?_
  simp only [Units.val_one, OneMemClass.coe_one]
  gcongr
  exact mul_le_of_le_one_right (norm_nonneg _) Matrix.l2_opNorm_one_le

open scoped Matrix.Norms.L2Operator in
/-- Polynomial growth for the action of the column group alone. -/
theorem norm_pairWeil_right_le (γ γ' : ℤ) (g : unitaryGroup ε') :
    ‖pairWeil ε ε' γ γ' (1, g)‖ ≤
      ‖(ReproducingModel.vacuum : FockSpace (pairSigns ε ε'))‖ *
        ‖((g : GL C ℂ) : Matrix C C ℂ)‖ ^ Fintype.card (R × C) := by
  refine (norm_pairWeil_le ε ε' γ γ' (1, g)).trans ?_
  simp only [Units.val_one, OneMemClass.coe_one]
  gcongr
  exact mul_le_of_le_one_left (norm_nonneg _) Matrix.l2_opNorm_one_le

end TauCeti.Fock
