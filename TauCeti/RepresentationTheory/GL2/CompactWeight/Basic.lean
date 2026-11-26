/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.GL2Coefficient
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Decomposition
public import TauCeti.RepresentationTheory.GL2.CompactCayley
import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.Analysis.SpecialFunctions.Trigonometric.MatrixFinTwo.Basic

/-!
# Compact weights of representations of `GL₂(ℂ)`

The rotations `r_θ = exp(θJ) = [[cos θ, sin θ], [-sin θ, cos θ]]`, with
`J = TauCeti.gl2RotationGenerator`, form the compact torus `SO(2)` of `GL₂(ℂ)`. A vector `w` of a
representation `ρ` has *compact weight* `ℓ ∈ ℤ` when `ρ(r_θ) w = e^{iℓθ} w` for every real `θ`.

The Cayley matrix `C = [[1, 1], [i, -i]]` (`TauCeti.compactCayley`) has columns the eigenvectors
`(1, i)` and `(1, -i)` of every `r_θ`, so `r_θ C = C diag(e^{iθ}, e^{-iθ})`
(`TauCeti.gl2Rotation_mul_gl2Cayley`). Hence `ρ(C)` carries the weight space of weight `l` for the
diagonal torus into the compact weight space of compact weight `l 0 - l 1`
(`TauCeti.map_weightSpace_le_compactWeightSpace`). For a rational representation, whose weight
spaces span it, the compact weight space of `ℓ` is exactly the image under `ρ(C)` of the sum of the
weight spaces with `l 0 - l 1 = ℓ` (`TauCeti.IsRationalRep.compactWeightSpace_eq_iSup`).

For the algebraic coefficient `V_(a,b) = Sym^{a-b}(Std) ⊗ det^b` with `a ≥ b`, whose weights are
the `(a - i, b + i)`, `0 ≤ i ≤ a - b`, the compact weights are therefore the `a - b - 2i`, each with
multiplicity one.

## Main definitions

* `TauCeti.gl2Rotation θ`: the rotation `r_θ` (`Matrix.SpecialLinearGroup.rotation θ`) as an
  element of `GL₂(ℂ)`.
* `TauCeti.compactWeightSpace ρ ℓ`: the vectors on which every `ρ(r_θ)` acts by `e^{iℓθ}`.

## Main results

* `TauCeti.gl2Rotation_add`: `r_{θ + φ} = r_θ r_φ`.
* `TauCeti.gl2Rotation_mul_gl2Cayley`: `r_θ C = C diag(e^{iθ}, e^{-iθ})`, with
  `C = TauCeti.gl2Cayley`.
* `TauCeti.coe_gl2Rotation_eq_exp`: `r_θ = exp(θJ)`.
* `TauCeti.iSupIndep_compactWeightSpace`: the compact weight spaces are independent.
* `TauCeti.IsRationalRep.compactWeightSpace_eq_iSup`: for a rational representation, the compact
  weight space of `ℓ` is the image under `ρ(C)` of the weight spaces with `l 0 - l 1 = ℓ`.
* `TauCeti.compactWeightSpace_gl2CoefficientRep_ne_bot_iff`: the compact weights of `V_(a,b)` are
  the `a - b - 2i` with `0 ≤ i ≤ a - b`.
* `TauCeti.finrank_compactWeightSpace_gl2CoefficientRep`: each has multiplicity one.
-/

public section

noncomputable section

open Complex Matrix Module

namespace TauCeti

/-- The rotation `r_θ = exp(θJ) = [[cos θ, sin θ], [-sin θ, cos θ]]`, with
`J = TauCeti.gl2RotationGenerator`, as an element of `GL₂(ℂ)`: the image of
`Matrix.SpecialLinearGroup.rotation θ ∈ SL(2, ℝ)`. -/
def gl2Rotation (θ : ℝ) : GL (Fin 2) ℂ :=
  SpecialLinearGroup.mapGL ℂ (SpecialLinearGroup.rotation θ)

/-- The matrix of `gl2Rotation θ`. -/
@[simp]
theorem coe_gl2Rotation (θ : ℝ) :
    (gl2Rotation θ : Matrix (Fin 2) (Fin 2) ℂ) = !![cos θ, sin θ; -sin θ, cos θ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl2Rotation]

/-- The rotation by `0` is the identity. -/
@[simp]
theorem gl2Rotation_zero : gl2Rotation 0 = 1 := by
  simp [gl2Rotation]

/-- The rotations form a one-parameter subgroup: `r_{θ + φ} = r_θ r_φ`. -/
theorem gl2Rotation_add (θ φ : ℝ) : gl2Rotation (θ + φ) = gl2Rotation θ * gl2Rotation φ := by
  rw [gl2Rotation, SpecialLinearGroup.rotation_add, map_mul, gl2Rotation, gl2Rotation]

/-- **The Cayley matrix diagonalizes the rotations**: `r_θ C = C diag(e^{iθ}, e^{-iθ})`. -/
theorem gl2Rotation_mul_gl2Cayley (θ : ℝ) :
    gl2Rotation θ * gl2Cayley =
      gl2Cayley * diagGL ![Circle.toUnits (Circle.exp θ), Circle.toUnits (Circle.exp (-θ))] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compactCayley_def, mul_diagonal, ← neg_mul, -Circle.exp_neg, exp_mul_I] <;>
    grind [I_sq]

/-- **The rotations are the exponentials of the generator `J`**: `r_θ = exp(θJ)`. Since
`θJ = C diag(iθ, -iθ) C⁻¹`, this is `TauCeti.gl2Rotation_mul_gl2Cayley`. -/
theorem coe_gl2Rotation_eq_exp (θ : ℝ) :
    (gl2Rotation θ : Matrix (Fin 2) (Fin 2) ℂ) =
      NormedSpace.exp ((θ : ℂ) • gl2RotationGenerator) := by
  have hJC : (θ : ℂ) • gl2RotationGenerator * compactCayley =
      compactCayley * diagonal ![θ * I, -(θ * I)] := by
    rw [gl2RotationGenerator_def, compactCayley_def]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_diagonal] <;> grind [I_sq]
  have hJ : (θ : ℂ) • gl2RotationGenerator =
      compactCayley * diagonal ![θ * I, -(θ * I)] * compactCayley⁻¹ := by
    rw [← hJC, mul_nonsing_inv_cancel_right _ _ isUnit_det_compactCayley]
  have h := congrArg (fun g : GL (Fin 2) ℂ ↦ (g : Matrix (Fin 2) (Fin 2) ℂ) * compactCayley⁻¹)
    (gl2Rotation_mul_gl2Cayley θ)
  simp only [Units.val_mul, coe_gl2Cayley, mul_assoc, mul_nonsing_inv _ isUnit_det_compactCayley,
    mul_one] at h
  rw [h, hJ, exp_conj _ _ ((isUnit_iff_isUnit_det _).mpr isUnit_det_compactCayley), exp_diagonal,
    mul_assoc]
  congr 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi.exp_def, ← Complex.exp_eq_exp_ℂ, -Circle.exp_neg, ← neg_mul]

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The **compact weight space** of compact weight `ℓ ∈ ℤ`: the vectors on which every rotation
`r_θ` acts by `e^{iℓθ}`. -/
def compactWeightSpace (ρ : Representation ℂ (GL (Fin 2) ℂ) W) (ℓ : ℤ) : Submodule ℂ W :=
  ⨅ θ : ℝ, Module.End.eigenspace (ρ (gl2Rotation θ)) (exp (ℓ * θ * I))

/-- Membership in a compact weight space. -/
@[simp]
theorem mem_compactWeightSpace_iff (ρ : Representation ℂ (GL (Fin 2) ℂ) W) (ℓ : ℤ) (w : W) :
    w ∈ compactWeightSpace ρ ℓ ↔ ∀ θ : ℝ, ρ (gl2Rotation θ) w = exp (ℓ * θ * I) • w := by
  simp [compactWeightSpace]

/-- **The compact weight spaces are independent.** -/
theorem iSupIndep_compactWeightSpace (ρ : Representation ℂ (GL (Fin 2) ℂ) W) :
    iSupIndep (compactWeightSpace ρ) :=
  (iSupIndep_iInf_eigenspace fun θ : ℝ ↦ ρ (gl2Rotation θ)).comp injective_exp_intCast_mul_mul_I

/-- **The Cayley matrix carries weights to compact weights.** The image under `ρ(C)` of the weight
space of weight `l` lies in the compact weight space of compact weight `l 0 - l 1`. -/
theorem map_weightSpace_le_compactWeightSpace (ρ : Representation ℂ (GL (Fin 2) ℂ) W)
    (l : Fin 2 → ℤ) :
    (weightSpace ρ l).map (ρ gl2Cayley) ≤ compactWeightSpace ρ (l 0 - l 1) := by
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_compactWeightSpace_iff]
  intro θ
  -- The weight character of `l` at `diag(e^{iθ}, e^{-iθ})` is `e^{i(l 0 - l 1)θ}`.
  have hchar : (weightChar ℂ l ![Circle.toUnits (Circle.exp θ), Circle.toUnits (Circle.exp (-θ))] :
      ℂ) = exp ((l 0 - l 1 : ℤ) * θ * I) := by
    simp [weightChar_apply, torusCharacter_def, Fin.prod_univ_two, -Circle.exp_neg,
      ← exp_intCast_mul, ← exp_add]
    congr 1
    ring
  rw [← mul_apply_eq_comp, ← map_mul, gl2Rotation_mul_gl2Cayley, map_mul, mul_apply_eq_comp,
    apply_of_mem_weightSpace hv, map_smul, hchar]

/-- **The compact weight spaces of a rational representation.** For a rational representation of
`GL₂(ℂ)`, the compact weight space of `ℓ` is the image under the Cayley matrix of the sum of the
weight spaces of the weights `l` with `l 0 - l 1 = ℓ`. -/
theorem IsRationalRep.compactWeightSpace_eq_iSup {ρ : Representation ℂ (GL (Fin 2) ℂ) W}
    (h : IsRationalRep ρ) (ℓ : ℤ) :
    compactWeightSpace ρ ℓ = ⨆ (l : Fin 2 → ℤ) (_ : l 0 - l 1 = ℓ),
      (weightSpace ρ l).map (ρ gl2Cayley) := by
  refine iInf_eigenspace_eq_of_iSup_eq_top (fun θ : ℝ ↦ ρ (gl2Rotation θ))
    (W := fun ℓ ↦ ⨆ (l : Fin 2 → ℤ) (_ : l 0 - l 1 = ℓ), (weightSpace ρ l).map (ρ gl2Cayley))
    (fun ℓ ↦ iSup₂_le fun l hl ↦ hl ▸ map_weightSpace_le_compactWeightSpace ρ l) ?_
    injective_exp_intCast_mul_mul_I ℓ
  rw [iSup_comm, iSup_congr fun l ↦ iSup_iSup_eq_right, ← Submodule.map_iSup,
    h.iSup_weightSpace_eq_top, Submodule.map_top,
    LinearMap.range_eq_top.mpr (ρ.apply_bijective gl2Cayley).surjective]


section GL2Coefficient

variable {a b : ℤ}

/-- **The compact weights of `V_(a,b)`** are the `a - b - 2i` with `0 ≤ i ≤ a - b`. -/
theorem compactWeightSpace_gl2CoefficientRep_ne_bot_iff (hab : b ≤ a) (ℓ : ℤ) :
    compactWeightSpace (W := GL2CoefficientSpace ℂ a b) (gl2CoefficientRep ℂ a b) ℓ ≠ ⊥ ↔
      ∃ i : ℤ, 0 ≤ i ∧ i ≤ a - b ∧ ℓ = a - b - 2 * i := by
  rw [(isRationalRep_gl2CoefficientRep a b).compactWeightSpace_eq_iSup, Ne, iSup_eq_bot]
  simp only [iSup_eq_bot, not_forall, (Submodule.map_injective_of_injective
    ((gl2CoefficientRep ℂ a b).apply_bijective gl2Cayley).injective).eq_iff' (Submodule.map_bot _)]
  constructor
  · rintro ⟨l, hl, h⟩
    have := (weightSpace_gl2CoefficientRep_ne_bot_iff weightChar_injective hab l).mp h
    exact ⟨a - l 0, by omega, by omega, by omega⟩
  · rintro ⟨i, hi₀, hi, rfl⟩
    refine ⟨![a - i, b + i], by simp; omega, ?_⟩
    exact (weightSpace_gl2CoefficientRep_ne_bot_iff weightChar_injective hab _).mpr (by simp; omega)

/-- The compact weight space of `V_(a,b)` of compact weight `a - b - 2i` is the image under the
Cayley matrix of the weight space of weight `(a - i, b + i)`. -/
theorem compactWeightSpace_gl2CoefficientRep_eq_map (hab : b ≤ a) (i : ℤ) :
    compactWeightSpace (W := GL2CoefficientSpace ℂ a b) (gl2CoefficientRep ℂ a b) (a - b - 2 * i) =
      (weightSpace (W := GL2CoefficientSpace ℂ a b) (gl2CoefficientRep ℂ a b)
        ![a - i, b + i]).map (gl2CoefficientRep ℂ a b gl2Cayley) := by
  rw [(isRationalRep_gl2CoefficientRep a b).compactWeightSpace_eq_iSup]
  refine le_antisymm (iSup₂_le fun l hl ↦ ?_)
    (le_iSup₂_of_le ![a - i, b + i] (by simp; omega) le_rfl)
  by_cases h : weightSpace (W := GL2CoefficientSpace ℂ a b) (gl2CoefficientRep ℂ a b) l = ⊥
  · simp [h]
  · have := (weightSpace_gl2CoefficientRep_ne_bot_iff weightChar_injective hab l).mp h
    have hl' : l = ![a - i, b + i] := by
      ext j
      fin_cases j <;> simp <;> omega
    rw [hl']

/-- **The compact weights of `V_(a,b)` have multiplicity one.** -/
theorem finrank_compactWeightSpace_gl2CoefficientRep (hab : b ≤ a) {i : ℤ} (hi₀ : 0 ≤ i)
    (hi : i ≤ a - b) :
    finrank ℂ (compactWeightSpace (W := GL2CoefficientSpace ℂ a b) (gl2CoefficientRep ℂ a b)
      (a - b - 2 * i)) = 1 := by
  rw [compactWeightSpace_gl2CoefficientRep_eq_map hab, ← (Submodule.equivMapOfInjective _
    ((gl2CoefficientRep ℂ a b).apply_bijective gl2Cayley).injective _).finrank_eq]
  exact finrank_weightSpace_gl2CoefficientRep weightChar_injective (by simp; omega)

end GL2Coefficient

end TauCeti
