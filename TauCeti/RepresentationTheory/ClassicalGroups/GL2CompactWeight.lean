/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.GL2Coefficient
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Decomposition

/-!
# Compact weights of representations of `GL₂(ℂ)`

The rotations `r_θ = [[cos θ, -sin θ], [sin θ, cos θ]]` form the compact torus `SO(2)` of
`GL₂(ℂ)`. A vector `w` of a representation `ρ` has *compact weight* `ℓ ∈ ℤ` when
`ρ(r_θ) w = e^{iℓθ} w` for every real `θ`.

The Cayley matrix `c = [[1, 1], [-i, i]]` has columns the eigenvectors `(1, -i)` and `(1, i)` of
every `r_θ`, so `r_θ c = c diag(e^{iθ}, e^{-iθ})` (`TauCeti.rotationGL_mul_cayleyGL`). Hence `ρ(c)`
carries the weight space of weight `l` for the diagonal torus into the compact weight space of
compact weight `l 0 - l 1` (`TauCeti.map_weightSpace_le_compactWeightSpace`). For a rational
representation, whose weight spaces span it, the compact weight space of `ℓ` is exactly the image
under `ρ(c)` of the sum of the weight spaces with `l 0 - l 1 = ℓ`
(`TauCeti.IsRationalRep.compactWeightSpace_eq_iSup`).

For the algebraic coefficient `V_(a,b) = Sym^{a-b}(Std) ⊗ det^b` with `a ≥ b`, whose weights are
the `(a - i, b + i)`, `0 ≤ i ≤ a - b`, the compact weights are therefore the `a - b - 2i`, each with
multiplicity one.

## Main definitions

* `TauCeti.rotationGL θ`: the rotation `r_θ` as an element of `GL₂(ℂ)`.
* `TauCeti.cayleyGL`: the Cayley matrix `[[1, 1], [-i, i]]`.
* `TauCeti.compactWeightSpace ρ ℓ`: the vectors on which every `ρ(r_θ)` acts by `e^{iℓθ}`.

## Main results

* `TauCeti.rotationGL_mul_cayleyGL`: `r_θ c = c diag(e^{iθ}, e^{-iθ})`.
* `TauCeti.iSupIndep_compactWeightSpace`: the compact weight spaces are independent.
* `TauCeti.IsRationalRep.compactWeightSpace_eq_iSup`: for a rational representation, the compact
  weight space of `ℓ` is the image under `ρ(c)` of the weight spaces with `l 0 - l 1 = ℓ`.
* `TauCeti.compactWeightSpace_gl2CoefficientRep_ne_bot_iff`: the compact weights of `V_(a,b)` are
  the `a - b - 2i` with `0 ≤ i ≤ a - b`.
* `TauCeti.finrank_compactWeightSpace_gl2CoefficientRep`: each has multiplicity one.
-/

public section

noncomputable section

open Complex Matrix Module

namespace TauCeti

/-- The rotation `r_θ = [[cos θ, -sin θ], [sin θ, cos θ]]` as an element of `GL₂(ℂ)`. -/
def rotationGL (θ : ℝ) : GL (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero !![cos θ, -sin θ; sin θ, cos θ] (by
    simp [det_fin_two_of, ← sq, cos_sq_add_sin_sq])

/-- The matrix of `rotationGL θ`. -/
@[simp]
theorem coe_rotationGL (θ : ℝ) :
    (rotationGL θ : Matrix (Fin 2) (Fin 2) ℂ) = !![cos θ, -sin θ; sin θ, cos θ] := by
  simp [rotationGL, GeneralLinearGroup.mkOfDetNeZero]

/-- The Cayley matrix `[[1, 1], [-i, i]]`, whose columns are the common eigenvectors `(1, -i)` and
`(1, i)` of the rotations. -/
def cayleyGL : GL (Fin 2) ℂ :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 1; -I, I] (by
    simp [det_fin_two_of, I_ne_zero])

/-- The matrix of `cayleyGL`. -/
@[simp]
theorem coe_cayleyGL : (cayleyGL : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 1; -I, I] := by
  simp [cayleyGL, GeneralLinearGroup.mkOfDetNeZero]

/-- The unit `e^{iθ}` of `ℂ`. -/
def expIUnit (θ : ℝ) : ℂˣ :=
  Units.mk0 (exp (θ * I)) (exp_ne_zero _)

/-- The value of `expIUnit θ`. -/
@[simp]
theorem coe_expIUnit (θ : ℝ) : (expIUnit θ : ℂ) = exp (θ * I) := by
  simp [expIUnit]

/-- **The Cayley matrix diagonalizes the rotations**: `r_θ c = c diag(e^{iθ}, e^{-iθ})`. -/
theorem rotationGL_mul_cayleyGL (θ : ℝ) :
    rotationGL θ * cayleyGL = cayleyGL * diagGL ![expIUnit θ, expIUnit (-θ)] := by
  have hc : exp (-(θ * I)) = cos θ - sin θ * I := by
    rw [← neg_mul, exp_mul_I, cos_neg, sin_neg]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Units.val_mul, coe_rotationGL, coe_cayleyGL,
      cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, smul_cons, smul_eq_mul,
      mul_one, smul_empty, tail_cons, neg_smul, mul_neg, neg_cons, neg_neg, neg_empty, empty_vecMul,
      add_zero, add_cons, empty_add_empty, Matrix.symm_of, empty_mul, coe_rowEquiv, row_of,
      of_apply,
      cons_val', cons_val_zero, cons_val_one, cons_val_fin_one, diagGL_coe, mul_diagonal,
      coe_expIUnit, ofReal_neg, neg_mul, one_mul, exp_mul_I, hc] <;>
    first
    | ring1
    | linear_combination (sin θ : ℂ) * I_sq

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The **compact weight space** of compact weight `ℓ ∈ ℤ`: the vectors on which every rotation
`r_θ` acts by `e^{iℓθ}`. -/
def compactWeightSpace (ρ : Representation ℂ (GL (Fin 2) ℂ) W) (ℓ : ℤ) : Submodule ℂ W :=
  ⨅ θ : ℝ, Module.End.eigenspace (ρ (rotationGL θ)) (exp (ℓ * θ * I))

/-- Membership in a compact weight space. -/
@[simp]
theorem mem_compactWeightSpace_iff (ρ : Representation ℂ (GL (Fin 2) ℂ) W) (ℓ : ℤ) (w : W) :
    w ∈ compactWeightSpace ρ ℓ ↔ ∀ θ : ℝ, ρ (rotationGL θ) w = exp (ℓ * θ * I) • w := by
  simp [compactWeightSpace]

/-- The characters `θ ↦ e^{iℓθ}` of the rotation group are distinct for distinct `ℓ`. -/
theorem injective_exp_intCast_mul_mul_I :
    Function.Injective fun (ℓ : ℤ) (θ : ℝ) ↦ exp (ℓ * θ * I) := by
  intro ℓ ℓ' h
  by_contra hne
  set x : ℝ := Real.pi / (ℓ - ℓ' : ℤ)
  have hd : ((ℓ - ℓ' : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hx : ((ℓ - ℓ' : ℤ) : ℝ) * x = Real.pi := by
    simp only [x]
    field_simp
  have h1 : exp (ℓ * x * I) = exp (ℓ' * x * I) := congrFun h x
  have h2 : exp (ℓ * x * I) = exp (ℓ' * x * I) * exp (Real.pi * I) := by
    rw [← exp_add]
    congr 1
    have := congrArg (fun r : ℝ ↦ (r : ℂ) * I) hx
    push_cast at this
    linear_combination this
  rw [h2, exp_pi_mul_I] at h1
  exact exp_ne_zero _ (by linear_combination (-1 / 2 : ℂ) * h1)

/-- **The compact weight spaces are independent.** -/
theorem iSupIndep_compactWeightSpace (ρ : Representation ℂ (GL (Fin 2) ℂ) W) :
    iSupIndep (compactWeightSpace ρ) :=
  (iSupIndep_iInf_eigenspace fun θ : ℝ ↦ ρ (rotationGL θ)).comp injective_exp_intCast_mul_mul_I

/-- **The Cayley matrix carries weights to compact weights.** The image under `ρ(c)` of the weight
space of weight `l` lies in the compact weight space of compact weight `l 0 - l 1`. -/
theorem map_weightSpace_le_compactWeightSpace (ρ : Representation ℂ (GL (Fin 2) ℂ) W)
    (l : Fin 2 → ℤ) :
    (weightSpace ρ l).map (ρ cayleyGL) ≤ compactWeightSpace ρ (l 0 - l 1) := by
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_compactWeightSpace_iff]
  intro θ
  rw [← mul_apply_eq_comp, ← map_mul, rotationGL_mul_cayleyGL, map_mul, mul_apply_eq_comp,
    apply_of_mem_weightSpace hv, map_smul]
  congr 1
  simp only [weightChar_apply, torusCharacter_def, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Units.val_mul, Units.val_zpow_eq_zpow_val, coe_expIUnit]
  rw [← exp_intCast_mul, ← exp_intCast_mul, ← exp_add]
  push_cast
  ring_nf

/-- **The compact weight spaces of a rational representation.** For a rational representation of
`GL₂(ℂ)`, the compact weight space of `ℓ` is the image under the Cayley matrix of the sum of the
weight spaces of the weights `l` with `l 0 - l 1 = ℓ`. -/
theorem IsRationalRep.compactWeightSpace_eq_iSup {ρ : Representation ℂ (GL (Fin 2) ℂ) W}
    (h : IsRationalRep ρ) (ℓ : ℤ) :
    compactWeightSpace ρ ℓ = ⨆ (l : Fin 2 → ℤ) (_ : l 0 - l 1 = ℓ),
      (weightSpace ρ l).map (ρ cayleyGL) := by
  refine iInf_eigenspace_eq_of_iSup_eq_top (fun θ : ℝ ↦ ρ (rotationGL θ))
    (W := fun ℓ ↦ ⨆ (l : Fin 2 → ℤ) (_ : l 0 - l 1 = ℓ), (weightSpace ρ l).map (ρ cayleyGL))
    (fun ℓ ↦ iSup₂_le fun l hl ↦ hl ▸ map_weightSpace_le_compactWeightSpace ρ l) ?_
    injective_exp_intCast_mul_mul_I ℓ
  have hsurj : Function.Surjective (ρ cayleyGL) := fun w ↦
    ⟨ρ cayleyGL⁻¹ w, by rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one,
      one_apply_eq_self]⟩
  rw [iSup_comm, iSup_congr fun l ↦ iSup_iSup_eq_right, ← Submodule.map_iSup,
    h.iSup_weightSpace_eq_top, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]


section GL2Coefficient

variable {a b : ℤ}

/-- **`V_(a,b)` is a rational representation** of `GL₂(ℂ)`. -/
theorem isRationalRep_gl2CoefficientRep (a b : ℤ) : IsRationalRep (gl2CoefficientRep ℂ a b) :=
  IsRationalRep.tprod (IsPolynomialRep.isRationalRep (isPolynomialRep_symPowerRep _ _))
    (isRationalRep_detPowerRep b)

omit [AddCommGroup W] [Module ℂ W] in
/-- The action of the Cayley matrix is injective. -/
private theorem injective_cayleyGL {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) ℂ) V) : Function.Injective (ρ cayleyGL) :=
  fun x y h ↦ by
    simpa [← mul_apply_eq_comp, ← map_mul] using congrArg (ρ cayleyGL⁻¹) h

omit [AddCommGroup W] [Module ℂ W] in
private theorem map_cayleyGL_eq_bot_iff {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) ℂ) V) (p : Submodule ℂ V) :
    p.map (ρ cayleyGL) = ⊥ ↔ p = ⊥ :=
  (Submodule.map_injective_of_injective (injective_cayleyGL ρ)).eq_iff' (Submodule.map_bot _)

/-- The weights of `V_(a,b)` over `ℂ`, whose weight characters separate weights. -/
private theorem weightSpace_gl2CoefficientRep_ne_bot_iff' (hab : b ≤ a) (l : Fin 2 → ℤ) :
    weightSpace (W := GL2CoefficientSpace ℂ a b) (gl2CoefficientRep ℂ a b) l ≠ ⊥ ↔
      b ≤ l 0 ∧ b ≤ l 1 ∧ l 0 + l 1 = a + b :=
  weightSpace_gl2CoefficientRep_ne_bot_iff weightChar_injective hab l

/-- **The compact weights of `V_(a,b)`** are the `a - b - 2i` with `0 ≤ i ≤ a - b`. -/
theorem compactWeightSpace_gl2CoefficientRep_ne_bot_iff (hab : b ≤ a) (ℓ : ℤ) :
    compactWeightSpace (W := GL2CoefficientSpace ℂ a b) (gl2CoefficientRep ℂ a b) ℓ ≠ ⊥ ↔
      ∃ i : ℤ, 0 ≤ i ∧ i ≤ a - b ∧ ℓ = a - b - 2 * i := by
  rw [(isRationalRep_gl2CoefficientRep a b).compactWeightSpace_eq_iSup, Ne, iSup_eq_bot]
  simp only [iSup_eq_bot, not_forall, map_cayleyGL_eq_bot_iff]
  constructor
  · rintro ⟨l, hl, h⟩
    have := (weightSpace_gl2CoefficientRep_ne_bot_iff' hab l).mp h
    exact ⟨a - l 0, by omega, by omega, by omega⟩
  · rintro ⟨i, hi₀, hi, rfl⟩
    refine ⟨![a - i, b + i], by simp; omega, ?_⟩
    exact (weightSpace_gl2CoefficientRep_ne_bot_iff' hab _).mpr (by simp; omega)

/-- The compact weight space of `V_(a,b)` of compact weight `a - b - 2i` is the image under the
Cayley matrix of the weight space of weight `(a - i, b + i)`. -/
theorem compactWeightSpace_gl2CoefficientRep_eq_map (hab : b ≤ a) (i : ℤ) :
    compactWeightSpace (W := GL2CoefficientSpace ℂ a b) (gl2CoefficientRep ℂ a b) (a - b - 2 * i) =
      (weightSpace (W := GL2CoefficientSpace ℂ a b) (gl2CoefficientRep ℂ a b)
        ![a - i, b + i]).map (gl2CoefficientRep ℂ a b cayleyGL) := by
  rw [(isRationalRep_gl2CoefficientRep a b).compactWeightSpace_eq_iSup]
  refine le_antisymm (iSup₂_le fun l hl ↦ ?_)
    (le_iSup₂_of_le ![a - i, b + i] (by simp; omega) le_rfl)
  by_cases h : weightSpace (W := GL2CoefficientSpace ℂ a b) (gl2CoefficientRep ℂ a b) l = ⊥
  · simp [h]
  · have := (weightSpace_gl2CoefficientRep_ne_bot_iff' hab l).mp h
    have hl' : l = ![a - i, b + i] := by
      ext j
      fin_cases j <;> simp <;> omega
    rw [hl']

/-- **The compact weights of `V_(a,b)` have multiplicity one.** -/
theorem finrank_compactWeightSpace_gl2CoefficientRep (hab : b ≤ a) {i : ℤ} (hi₀ : 0 ≤ i)
    (hi : i ≤ a - b) :
    finrank ℂ (compactWeightSpace (W := GL2CoefficientSpace ℂ a b) (gl2CoefficientRep ℂ a b)
      (a - b - 2 * i)) = 1 := by
  rw [compactWeightSpace_gl2CoefficientRep_eq_map hab,
    ← (Submodule.equivMapOfInjective _ (injective_cayleyGL _) _).finrank_eq]
  exact finrank_weightSpace_gl2CoefficientRep weightChar_injective (by simp; omega)

end GL2Coefficient

end TauCeti
