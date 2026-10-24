/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Content
public import TauCeti.NumberTheory.QuadraticOrder.NormOne
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import TauCeti.NumberTheory.BinaryQuadraticForm.OfMatrix

/-!
# Automorphs of a binary quadratic form and norm-one units

The stabilizer of an integral binary quadratic form `f = (a, b, c)` in `SL(2, ℤ)` is its group of
proper automorphs. For primitive `f` of discriminant `D = b² - 4ac` it is isomorphic to the group
of norm-one units of the quadratic order `ℤ[(D + √D)/2]` of discriminant `D`. The unit
`x + y√D` corresponds to the automorph
```
!![x - b y, -2 c y; 2 a y, x + b y],
```
classically written `!![(t - b u)/2, -c u; a u, (t + b u)/2]` with `t² - D u² = 4`. The assignment
is the regular representation of the order on `ℤ²`: the generator `(D + √D)/2` acts by the integral
matrix `M = !![(D - b)/2, -c; a, (D + b)/2]` of trace `D`, which satisfies
`M² = (D - D²)/4 + D M` and whose form `Q_M` (`TauCeti.BinaryQuadraticForm.ofMatrix`) is `f`.
The determinant of the representation is the norm. Matrices commuting with `M` fix `Q_M = f`;
conversely an automorph of `f` commutes with `M`, because `Q_M` and the trace determine `M`, and
primitivity of `f` makes its coordinates against `M` integral.

The isomorphism holds for every primitive form, including those of square or zero discriminant.
The discriminant is a parameter `D` with a proof of `f.discrim = D`, so that the target needs no
transport along an equality of discriminants.

## Main results

* `TauCeti.BinaryQuadraticForm.stabilizerEquivNormOneUnits`: for primitive `f` of discriminant
  `D`, the automorphs of `f` are the norm-one units of the order of discriminant `D`.
* `TauCeti.BinaryQuadraticForm.map_stabilizerEquivNormOneUnits_symm_apply`: the automorph attached
  to the unit `x + y√D`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §2 and §7.
* L. E. Dickson, *Introduction to the Theory of Numbers*, Chapter VII.
-/

public section

open Matrix MulAction QuadraticAlgebra
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

variable (f : BinaryQuadraticForm ℤ) {D : ℤ}

/-! ### The regular representation of the order -/

/-- `f` has discriminant `D² - 4 n` for the norm `n = -(D - D²)/4` of `(D + √D)/2`. -/
private theorem discrim_eq_sq_sub_four_mul (hfD : f.discrim = D) :
    f.discrim = D ^ 2 - 4 * -((D - D ^ 2) / 4) := by
  have h := QuadraticOrder.parameter_discr D (hfD ▸ f.discrim_emod_four_eq_zero_or_one)
  rw [QuadraticAlgebra.discr_def] at h
  linear_combination hfD - h

/-- The matrix of trace `D` and determinant `-(D - D²)/4` whose form `Q_M` is `f`. The generator
`(D + √D)/2` of the order acts on `ℤ²` by this matrix. -/
private def generatorMatrix (hfD : f.discrim = D) : Matrix (Fin 2) (Fin 2) ℤ :=
  (ofMatrixEquiv D (-((D - D ^ 2) / 4))).symm ⟨f, discrim_eq_sq_sub_four_mul f hfD⟩

private theorem generatorMatrix_eq (hfD : f.discrim = D) :
    generatorMatrix f hfD = !![(D - f.b) / 2, -f.c; f.a, D - (D - f.b) / 2] :=
  coe_ofMatrixEquiv_symm_apply _

private theorem ofMatrix_generatorMatrix (hfD : f.discrim = D) :
    ofMatrix (generatorMatrix f hfD) = f := by
  rw [generatorMatrix, ← coe_ofMatrixEquiv_apply, Equiv.apply_symm_apply]

private theorem trace_generatorMatrix (hfD : f.discrim = D) :
    (generatorMatrix f hfD).trace = D :=
  ((ofMatrixEquiv _ _).symm _).2.1

private theorem det_generatorMatrix (hfD : f.discrim = D) :
    (generatorMatrix f hfD).det = -((D - D ^ 2) / 4) :=
  ((ofMatrixEquiv _ _).symm _).2.2

private theorem generatorMatrix_mul_self (hfD : f.discrim = D) :
    generatorMatrix f hfD * generatorMatrix f hfD =
      ((D - D ^ 2) / 4) • 1 + D • generatorMatrix f hfD := by
  rw [← sq, sq_eq_trace_smul_sub_det_smul_one_fin_two, trace_generatorMatrix,
    det_generatorMatrix, neg_smul, sub_neg_eq_add, add_comm]

/-- The regular representation of the order of discriminant `D` in the coordinates of `f`. -/
private def regularRep (hfD : f.discrim = D) :
    QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D →ₐ[ℤ] Matrix (Fin 2) (Fin 2) ℤ :=
  QuadraticAlgebra.lift ⟨generatorMatrix f hfD, generatorMatrix_mul_self f hfD⟩

private theorem regularRep_apply (hfD : f.discrim = D)
    (z : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) :
    regularRep f hfD z = z.re • 1 + z.im • generatorMatrix f hfD :=
  lift_apply_apply _ z

private theorem regularRep_eq (hfD : f.discrim = D)
    (z : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) :
    regularRep f hfD z = !![z.re + z.im * ((D - f.b) / 2), -f.c * z.im;
      f.a * z.im, z.re + z.im * (D - (D - f.b) / 2)] := by
  rw [regularRep_apply, generatorMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [intCast_apply] <;> ring

/-- The determinant of the regular representation is the norm. -/
private theorem det_regularRep (hfD : f.discrim = D)
    (z : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) :
    (regularRep f hfD z).det = z.norm := by
  have hW := det_generatorMatrix f hfD
  rw [generatorMatrix_eq, det_fin_two_of] at hW
  rw [regularRep_eq, det_fin_two_of, norm_def]
  linear_combination z.im ^ 2 * hW

/-- An element of the order acts by a matrix commuting with the generator matrix, hence by an
automorph of `f = Q_M` for the generator matrix `M`. -/
private theorem regularRep_smul_eq (hfD : f.discrim = D)
    {z : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D} {γ : SL(2, ℤ)}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = regularRep f hfD z) : γ • f = f := by
  have hc : (γ : Matrix (Fin 2) (Fin 2) ℤ) * generatorMatrix f hfD =
      generatorMatrix f hfD * γ := by
    have hω : regularRep f hfD ω = generatorMatrix f hfD := by simp [regularRep_apply]
    rw [hγ, ← hω, ← map_mul, ← map_mul, mul_comm]
  have hinv :
      (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  conv_lhs => rw [← ofMatrix_generatorMatrix f hfD]
  rw [← ofMatrix_conj, hc, Matrix.mul_assoc, hinv, Matrix.mul_one, ofMatrix_generatorMatrix]

/-- The norm-one elements of the order act on `ℤ²` by automorphs of `f`. -/
private def unitaryToStabilizer (hfD : f.discrim = D) :
    unitary (QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) →* stabilizer SL(2, ℤ) f where
  toFun z := ⟨⟨regularRep f hfD z, (det_regularRep f hfD z).trans
      (norm_eq_one_iff_mem_unitary.mpr z.prop)⟩, regularRep_smul_eq f hfD rfl⟩
  map_one' := Subtype.ext <| Subtype.ext <| map_one (regularRep f hfD)
  map_mul' z w := Subtype.ext <| Subtype.ext <| map_mul (regularRep f hfD) z.1 w.1

private theorem coe_unitaryToStabilizer (hfD : f.discrim = D)
    (z : unitary (QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D)) :
    ((unitaryToStabilizer f hfD z : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      regularRep f hfD z := (rfl)

/-- Distinct elements of the order act differently on the coordinates of a nonzero form: the form
`Q_M` of the action of `z` is `z.im • f`, and its trace is `2 z.re + D z.im`. -/
private theorem regularRep_injective (hfD : f.discrim = D) (hf : f ≠ 0) :
    Function.Injective (regularRep f hfD) := by
  intro z w h
  have hQ (z : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) :
      ofMatrix (regularRep f hfD z) = z.im • f := by
    conv_rhs => rw [← ofMatrix_generatorMatrix f hfD]
    rw [generatorMatrix_eq, regularRep_eq]
    ext <;> simp [ofMatrix_a, ofMatrix_b, ofMatrix_c] <;> ring
  have htr (z : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) :
      (regularRep f hfD z).trace = 2 * z.re + D * z.im := by
    rw [regularRep_eq, trace_fin_two_of]
    ring
  have him : z.im = w.im := by
    have hzw : z.im • f = w.im • f := by rw [← hQ, ← hQ, h]
    exact smul_left_injective ℤ hf hzw
  have hre := (htr z).symm.trans ((congrArg Matrix.trace h).trans (htr w))
  ext
  · exact mul_left_cancel₀ (two_ne_zero (α := ℤ)) (by linear_combination hre - D * him)
  · exact him

/-- An automorph of `f = Q_M` commutes with the generator matrix `M`, since `Q_M` and the trace
determine `M`. Its coordinates against `M` are integral by primitivity of `f`, so it is the image
of a norm-one element of the order. -/
private theorem unitaryToStabilizer_surjective (hfD : f.discrim = D) (hf : f.IsPrimitive) :
    Function.Surjective (unitaryToStabilizer f hfD) := by
  rintro ⟨γ, hγ⟩
  rw [mem_stabilizer_iff] at hγ
  have hconj : (γ : Matrix (Fin 2) (Fin 2) ℤ) * generatorMatrix f hfD *
      ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = generatorMatrix f hfD := by
    refine (ofMatrix_inj_of_trace_eq ?_).mp ?_
    · exact ConjAct.trace_specialLinearGroup_smul (ConjAct.toConjAct γ) _
    · rw [ofMatrix_conj, ofMatrix_generatorMatrix, hγ]
  have hcomm : (γ : Matrix (Fin 2) (Fin 2) ℤ) * generatorMatrix f hfD =
      generatorMatrix f hfD * γ := by
    conv_rhs => rw [← hconj]
    rw [Matrix.mul_assoc _ _ (γ : Matrix (Fin 2) (Fin 2) ℤ), ← SpecialLinearGroup.coe_mul,
      inv_mul_cancel, SpecialLinearGroup.coe_one, Matrix.mul_one]
  have he := two_mul_ediv_two_of_discrim_eq (discrim_eq_sq_sub_four_mul f hfD)
  rw [generatorMatrix_eq] at hcomm
  have h₀₀ := congrFun₂ hcomm 0 0
  have h₀₁ := congrFun₂ hcomm 0 1
  have h₁₀ := congrFun₂ hcomm 1 0
  simp only [mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one] at h₀₀ h₀₁ h₁₀
  set p := γ 0 0
  set q := γ 0 1
  set r := γ 1 0
  set s := γ 1 1
  -- Commuting with the generator matrix: three linear relations in the entries.
  have hT₁ : f.a * q + f.c * r = 0 := by linear_combination h₀₀
  have hT₂ : f.b * q + f.c * (s - p) = 0 := by linear_combination h₀₁ + q * he
  have hT₃ : f.b * r - f.a * (s - p) = 0 := by linear_combination -h₁₀ + r * he
  -- Primitivity turns proportionality to `(c, a, b)` into an integral multiple.
  obtain ⟨u, v, w, huvw⟩ := hf.exists_linearCombination_eq_one
  set n := u * r + v * (s - p) - w * q
  have hr : r = f.a * n := by linear_combination v * hT₃ + w * hT₁ - r * huvw
  have hq : q = -f.c * n := by linear_combination u * hT₁ + v * hT₂ - q * huvw
  have hs : s = p + f.b * n := by linear_combination (-u) * hT₃ + w * hT₂ - (s - p) * huvw
  set z : QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D := ⟨p - n * ((D - f.b) / 2), n⟩
  have hz : regularRep f hfD z = γ := by
    refine Eq.trans ?_ (eta_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)).symm
    rw [regularRep_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [z, p, q, r, s, hq, hr, hs]
    linear_combination -n * he
  have hzu : z ∈ unitary (QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) := by
    rw [← norm_eq_one_iff_mem_unitary, ← det_regularRep f hfD, hz, SpecialLinearGroup.det_coe]
  refine ⟨⟨z, hzu⟩, ?_⟩
  ext : 2
  rw [coe_unitaryToStabilizer, hz]

/-- For primitive `f`, the norm-one elements of the integral model of the order are its
automorphs. -/
private noncomputable def unitaryEquivStabilizer (hfD : f.discrim = D) (hf : f.IsPrimitive) :
    unitary (QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D) ≃* stabilizer SL(2, ℤ) f :=
  MulEquiv.ofBijective (unitaryToStabilizer f hfD)
    ⟨fun z w h ↦ Subtype.ext <| regularRep_injective f hfD hf.ne_zero <| by
      simpa only [coe_unitaryToStabilizer] using
        congrArg (fun γ : stabilizer SL(2, ℤ) f ↦ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) h,
      unitaryToStabilizer_surjective f hfD hf⟩

private theorem unitaryEquivStabilizer_apply (hfD : f.discrim = D) (hf : f.IsPrimitive)
    (z : unitary (QuadraticAlgebra ℤ ((D - D ^ 2) / 4) D)) :
    unitaryEquivStabilizer f hfD hf z = unitaryToStabilizer f hfD z :=
  MulEquiv.ofBijective_apply _ _ _

/-! ### Automorphs and norm-one units -/

variable {f}

/-- **Automorphs are norm-one units.** For a primitive integral binary quadratic form `f` of
discriminant `D`, the proper automorphs of `f` form a group isomorphic to the norm-one units of the
quadratic order `ℤ[(D + √D)/2]` of discriminant `D`. The inverse is described by
`map_stabilizerEquivNormOneUnits_symm_apply`. -/
noncomputable def stabilizerEquivNormOneUnits (hf : f.IsPrimitive) (hfD : f.discrim = D) :
    stabilizer SL(2, ℤ) f ≃*
      QuadraticOrder.normOneUnits D (hfD ▸ f.discrim_emod_four_eq_zero_or_one) :=
  ((QuadraticOrder.normOneUnitsEquivUnitary D _).trans (unitaryEquivStabilizer f hfD hf)).symm

/-- The automorph attached to the norm-one unit `x + y√D` of the order is
`!![x - b y, -2 c y; 2 a y, x + b y]`, read over `ℚ`. -/
theorem map_stabilizerEquivNormOneUnits_symm_apply (hf : f.IsPrimitive) (hfD : f.discrim = D)
    (u : QuadraticOrder.normOneUnits D (hfD ▸ f.discrim_emod_four_eq_zero_or_one)) :
    (((stabilizerEquivNormOneUnits hf hfD).symm u : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) =
      let O := QuadraticOrder.toSubalgebra D (hfD ▸ f.discrim_emod_four_eq_zero_or_one)
      let x := ((u : Oˣ) : QuadraticAlgebra ℚ (D : ℚ) 0).re
      let y := ((u : Oˣ) : QuadraticAlgebra ℚ (D : ℚ) 0).im
      !![x - f.b * y, -2 * f.c * y; 2 * f.a * y, x + f.b * y] := by
  have hD : D % 4 = 0 ∨ D % 4 = 1 := hfD ▸ f.discrim_emod_four_eq_zero_or_one
  set z := QuadraticOrder.normOneUnitsEquivUnitary D hD u
  have hu : ((u : (QuadraticOrder.toSubalgebra D hD)ˣ) : QuadraticAlgebra ℚ (D : ℚ) 0) =
      QuadraticOrder.lift D hD z := by
    rw [← QuadraticOrder.coe_equivToSubalgebra_apply,
      QuadraticOrder.coe_normOneUnitsEquivUnitary_apply, AlgEquiv.apply_symm_apply]
  have hsymm : ((stabilizerEquivNormOneUnits hf hfD).symm u : SL(2, ℤ)) =
      (unitaryToStabilizer f hfD z : SL(2, ℤ)) := by
    rw [stabilizerEquivNormOneUnits, MulEquiv.symm_symm, MulEquiv.trans_apply,
      unitaryEquivStabilizer_apply]
  have he : (2 : ℚ) * (((D - f.b) / 2 : ℤ) : ℚ) = D - f.b := by
    exact_mod_cast two_mul_ediv_two_of_discrim_eq (discrim_eq_sq_sub_four_mul f hfD)
  rw [hsymm, coe_unitaryToStabilizer, regularRep_eq, hu, QuadraticOrder.lift_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (z.1.im : ℚ) / 2 * he
  · ring
  · ring
  · linear_combination -(z.1.im : ℚ) / 2 * he

end TauCeti.BinaryQuadraticForm
