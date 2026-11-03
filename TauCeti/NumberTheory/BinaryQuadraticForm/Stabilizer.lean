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
of norm-one units of the quadratic order `𝒪_D = ℤ[(D + √D)/2]` of discriminant `D`. The unit
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

The same argument works with coefficients in any commutative ring `R` in which `2` is not a zero
divisor, such as `ℤ_p`, `ℚ_p`, `ℝ` or `ℚ`. Reading `f` over `R`, its automorphs in `SL(2, R)` are
the norm-one elements of `R ⊗ 𝒪_D`, in the integral model
`R[ω]/(ω² - D ω + (D² - D)/4)` of `𝒪_D` with coefficients in `R`. This is the group of `R`-points of
the norm-one group scheme of `𝒪_D`. This group scheme is a torus over `R` only when `D` is
invertible in `R`: for `f = x²`, of discriminant `0`, it is `μ₂ × 𝔾ₐ` over `ℚ`. The identification
is natural in `R`: a ring homomorphism `R →+* S` maps automorphs entrywise exactly as it maps the
coordinates of norm-one elements. The hypothesis on `2` cannot be dropped: over `𝔽₂` the coordinate
swap is an automorph of `x y` of determinant one, but `x y` corresponds to the order `𝔽₂ × 𝔽₂`,
whose only norm-one element is `1`.

The isomorphism holds for every primitive form, including those of square or zero discriminant.
The discriminant is a parameter `D` with a proof of `f.discrim = D`, so that the target needs no
transport along an equality of discriminants.

## Main results

* `TauCeti.BinaryQuadraticForm.stabilizerEquivUnitary`: for primitive `f` of discriminant `D` and
  `R` without `2`-torsion, the automorphs of `f` over `R` are the norm-one elements of the order
  of discriminant `D` with coefficients in `R`.
* `TauCeti.BinaryQuadraticForm.coe_stabilizerEquivUnitary_symm_apply`: the automorph attached to a
  norm-one element `x + y ω`.
* `TauCeti.BinaryQuadraticForm.map_stabilizerEquivUnitary_symm_apply`: naturality in the
  coefficient ring.
* `TauCeti.BinaryQuadraticForm.stabilizerEquivNormOneUnits`: over `ℤ`, the automorphs of `f` are
  the norm-one units of the order of discriminant `D`.
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

variable {R : Type*} [CommRing R] (f : BinaryQuadraticForm ℤ) {D : ℤ}

/-! ### The integral generator matrix -/

/-- `f` has discriminant `D² - 4 n` for the norm `n = -(D - D²)/4` of `(D + √D)/2`. -/
private theorem discrim_eq_sq_sub_four_mul (hfD : f.discrim = D) :
    f.discrim = D ^ 2 - 4 * -((D - D ^ 2) / 4) := by
  have h := QuadraticOrder.parameter_discr D (hfD ▸ f.discrim_emod_four_eq_zero_or_one)
  rw [QuadraticAlgebra.discr_def] at h
  linear_combination hfD - h

/-- The integral matrix of trace `D` and determinant `-(D - D²)/4` whose form `Q_M` is `f`. The
generator `(D + √D)/2` of the order acts on `ℤ²` by this matrix. -/
private def generatorMatrix (hfD : f.discrim = D) : Matrix (Fin 2) (Fin 2) ℤ :=
  (ofMatrixEquiv D (-((D - D ^ 2) / 4))).symm ⟨f, discrim_eq_sq_sub_four_mul f hfD⟩

private theorem generatorMatrix_eq (hfD : f.discrim = D) :
    generatorMatrix f hfD = !![(D - f.b) / 2, -f.c; f.a, D - (D - f.b) / 2] :=
  coe_ofMatrixEquiv_symm_apply _

private theorem det_generatorMatrix (hfD : f.discrim = D) :
    (generatorMatrix f hfD).det = -((D - D ^ 2) / 4) :=
  ((ofMatrixEquiv _ _).symm _).2.2

/-! ### The regular representation over a coefficient ring -/

variable (R) in
/-- The generator matrix with its entries read in `R`. -/
private def castGeneratorMatrix (hfD : f.discrim = D) : Matrix (Fin 2) (Fin 2) R :=
  (generatorMatrix f hfD).map (Int.cast : ℤ → R)

private theorem castGeneratorMatrix_eq (hfD : f.discrim = D) :
    castGeneratorMatrix R f hfD = !![(((D - f.b) / 2 : ℤ) : R), -(f.c : R); (f.a : R),
      ((D - (D - f.b) / 2 : ℤ) : R)] := by
  rw [castGeneratorMatrix, generatorMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The form `Q_M` of the generator matrix over `R` is `f` read over `R`. -/
private theorem ofMatrix_castGeneratorMatrix (hfD : f.discrim = D) :
    ofMatrix (castGeneratorMatrix R f hfD) = f.map (Int.castRingHom R) := by
  have he := two_mul_ediv_two_of_discrim_eq (discrim_eq_sq_sub_four_mul f hfD)
  rw [castGeneratorMatrix_eq]
  ext
  · simp [ofMatrix_a]
  · simp only [ofMatrix_b, of_apply, cons_val', cons_val_one, cons_val_zero, empty_val',
      cons_val_fin_one, map_b, eq_intCast]
    have h := congrArg (Int.cast : ℤ → R)
      (by linear_combination -he : D - (D - f.b) / 2 - (D - f.b) / 2 = f.b)
    push_cast at h ⊢
    exact h
  · simp [ofMatrix_c]

private theorem trace_castGeneratorMatrix (hfD : f.discrim = D) :
    (castGeneratorMatrix R f hfD).trace = D := by
  rw [castGeneratorMatrix_eq, trace_fin_two_of]
  push_cast
  ring

private theorem det_castGeneratorMatrix (hfD : f.discrim = D) :
    (castGeneratorMatrix R f hfD).det = -(((D - D ^ 2) / 4 : ℤ) : R) := by
  rw [castGeneratorMatrix, ← Int.cast_det, det_generatorMatrix, Int.cast_neg]

private theorem castGeneratorMatrix_mul_self (hfD : f.discrim = D) :
    castGeneratorMatrix R f hfD * castGeneratorMatrix R f hfD =
      (((D - D ^ 2) / 4 : ℤ) : R) • 1 + (D : R) • castGeneratorMatrix R f hfD := by
  rw [← sq, sq_eq_trace_smul_sub_det_smul_one_fin_two, trace_castGeneratorMatrix,
    det_castGeneratorMatrix, neg_smul, sub_neg_eq_add, add_comm]

variable (R) in
/-- The regular representation of the order of discriminant `D`, with coefficients in `R`, in the
coordinates of `f`. -/
private def regularRep (hfD : f.discrim = D) :
    QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  QuadraticAlgebra.lift ⟨castGeneratorMatrix R f hfD, castGeneratorMatrix_mul_self f hfD⟩

private theorem regularRep_apply (hfD : f.discrim = D)
    (z : QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D) :
    regularRep R f hfD z = z.re • 1 + z.im • castGeneratorMatrix R f hfD :=
  lift_apply_apply _ z

private theorem regularRep_eq (hfD : f.discrim = D)
    (z : QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D) :
    regularRep R f hfD z = !![z.re + z.im * (((D - f.b) / 2 : ℤ) : R), -f.c * z.im;
      f.a * z.im, z.re + z.im * ((D - (D - f.b) / 2 : ℤ) : R)] := by
  rw [regularRep_apply, castGeneratorMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The determinant of the regular representation is the norm. -/
private theorem det_regularRep (hfD : f.discrim = D)
    (z : QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D) :
    (regularRep R f hfD z).det = z.norm := by
  have hW := det_castGeneratorMatrix (R := R) f hfD
  rw [castGeneratorMatrix_eq, det_fin_two_of] at hW
  rw [regularRep_eq, det_fin_two_of, norm_def]
  push_cast at hW ⊢
  linear_combination z.im ^ 2 * hW

/-- An element of the order acts by a matrix commuting with the generator matrix, hence by an
automorph of `f = Q_M` for the generator matrix `M`. -/
private theorem regularRep_smul_eq (hfD : f.discrim = D)
    {z : QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D} {γ : SL(2, R)}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) R) = regularRep R f hfD z) :
    γ • f.map (Int.castRingHom R) = f.map (Int.castRingHom R) := by
  have hc : (γ : Matrix (Fin 2) (Fin 2) R) * castGeneratorMatrix R f hfD =
      castGeneratorMatrix R f hfD * γ := by
    have hω : regularRep R f hfD ω = castGeneratorMatrix R f hfD := by simp [regularRep_apply]
    rw [hγ, ← hω, ← map_mul, ← map_mul, mul_comm]
  have hinv :
      (γ : Matrix (Fin 2) (Fin 2) R) * ((γ⁻¹ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  rw [← ofMatrix_castGeneratorMatrix f hfD, ← ofMatrix_conj, hc, Matrix.mul_assoc, hinv,
    Matrix.mul_one]

/-- The norm-one elements of the order act on `R²` by automorphs of `f`. -/
private def unitaryToStabilizer (hfD : f.discrim = D) :
    unitary (QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D) →*
      stabilizer SL(2, R) (f.map (Int.castRingHom R)) where
  toFun z := ⟨⟨regularRep R f hfD z, by
      rw [det_regularRep, norm_eq_one_iff_mem_unitary]
      exact z.prop⟩, mem_stabilizer_iff.mpr <| regularRep_smul_eq f hfD (z := z) rfl⟩
  map_one' := Subtype.ext <| Subtype.ext <| map_one (regularRep R f hfD)
  map_mul' z w := Subtype.ext <| Subtype.ext <| map_mul (regularRep R f hfD) z.1 w.1

private theorem coe_unitaryToStabilizer (hfD : f.discrim = D)
    (z : unitary (QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D)) :
    ((unitaryToStabilizer f hfD z : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) =
      regularRep R f hfD z := (rfl)

/-- For primitive `f`, distinct elements of the order act differently on `R²`: the off-diagonal
entries and the difference of the diagonal entries of the action of `z` are `z.im` times the
coefficients `a`, `-c` and `b` of `f`, which generate the unit ideal. -/
private theorem regularRep_injective (hfD : f.discrim = D) (hf : f.IsPrimitive) :
    Function.Injective (regularRep R f hfD) := by
  intro z w h
  obtain ⟨u, v, t, huvt⟩ := hf.exists_linearCombination_eq_one
  have he := two_mul_ediv_two_of_discrim_eq (discrim_eq_sq_sub_four_mul f hfD)
  have he' := congrArg (Int.cast : ℤ → R) he
  have h1 := congrArg (Int.cast : ℤ → R) huvt
  rw [regularRep_eq, regularRep_eq] at h
  have h₀₀ := congrFun₂ h 0 0
  have h₀₁ := congrFun₂ h 0 1
  have h₁₀ := congrFun₂ h 1 0
  have h₁₁ := congrFun₂ h 1 1
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    at h₀₀ h₀₁ h₁₀ h₁₁
  push_cast at h1 h₀₀ h₀₁ h₁₀ h₁₁ he'
  -- `a`, `b` and `c` times `z.im - w.im` vanish, so primitivity forces `z.im = w.im`
  have him : z.im = w.im := by
    linear_combination -(z.im - w.im) * h1 + u * h₁₀ - t * h₀₁ + v * (h₁₁ - h₀₀) +
      v * (z.im - w.im) * he'
  ext
  · linear_combination h₀₀ - (((D - f.b) / 2 : ℤ) : R) * him
  · exact him

/-- When `2` is not a zero divisor, an automorph of `f = Q_M` commutes with the generator matrix
`M`, since `Q_M` and the trace determine `M`. Its coordinates against `M` lie in `R` by
primitivity of `f`, so it is the image of a norm-one element of the order. -/
private theorem unitaryToStabilizer_surjective (hfD : f.discrim = D) (hf : f.IsPrimitive)
    (h2 : IsLeftRegular (2 : R)) : Function.Surjective (unitaryToStabilizer (R := R) f hfD) := by
  rintro ⟨γ, hγ⟩
  rw [mem_stabilizer_iff] at hγ
  have hconj : (γ : Matrix (Fin 2) (Fin 2) R) * castGeneratorMatrix R f hfD *
      ((γ⁻¹ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = castGeneratorMatrix R f hfD := by
    refine (ofMatrix_inj_of_trace_eq h2 ?_).mp ?_
    · exact ConjAct.trace_specialLinearGroup_smul (ConjAct.toConjAct γ) _
    · rw [ofMatrix_conj, ofMatrix_castGeneratorMatrix, hγ]
  have hcomm : (γ : Matrix (Fin 2) (Fin 2) R) * castGeneratorMatrix R f hfD =
      castGeneratorMatrix R f hfD * γ := by
    conv_rhs => rw [← hconj]
    rw [Matrix.mul_assoc _ _ (γ : Matrix (Fin 2) (Fin 2) R), ← SpecialLinearGroup.coe_mul,
      inv_mul_cancel, SpecialLinearGroup.coe_one, Matrix.mul_one]
  have he := two_mul_ediv_two_of_discrim_eq (discrim_eq_sq_sub_four_mul f hfD)
  have he' := congrArg (Int.cast : ℤ → R) he
  rw [castGeneratorMatrix_eq] at hcomm
  have h₀₀ := congrFun₂ hcomm 0 0
  have h₀₁ := congrFun₂ hcomm 0 1
  have h₁₀ := congrFun₂ hcomm 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one] at h₀₀ h₀₁ h₁₀
  push_cast at h₀₀ h₀₁ h₁₀ he'
  set p := γ 0 0
  set q := γ 0 1
  set r := γ 1 0
  set s := γ 1 1
  -- Commuting with the generator matrix: three linear relations in the entries.
  have hT₁ : (f.a : R) * q + f.c * r = 0 := by linear_combination h₀₀
  have hT₂ : (f.b : R) * q + f.c * (s - p) = 0 := by linear_combination h₀₁ + q * he'
  have hT₃ : (f.b : R) * r - f.a * (s - p) = 0 := by linear_combination -h₁₀ + r * he'
  -- Primitivity turns proportionality to `(c, a, b)` into a multiple with coefficient in `R`.
  obtain ⟨u, v, w, huvw⟩ := hf.exists_linearCombination_eq_one
  have h1 := congrArg (Int.cast : ℤ → R) huvw
  push_cast at h1
  set n := (u : R) * r + v * (s - p) - w * q
  have hr : r = f.a * n := by linear_combination v * hT₃ + w * hT₁ - r * h1
  have hq : q = -f.c * n := by linear_combination u * hT₁ + v * hT₂ - q * h1
  have hs : s = p + f.b * n := by linear_combination (-u) * hT₃ + w * hT₂ - (s - p) * h1
  set z : QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D :=
    ⟨p - n * (((D - f.b) / 2 : ℤ) : R), n⟩
  have hz : regularRep R f hfD z = γ := by
    refine Eq.trans ?_ (eta_fin_two (γ : Matrix (Fin 2) (Fin 2) R)).symm
    rw [regularRep_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [z, p, q, r, s, hq, hr, hs]
    linear_combination -n * he'
  have hzu : z ∈ unitary (QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D) := by
    rw [← norm_eq_one_iff_mem_unitary, ← det_regularRep f hfD, hz, SpecialLinearGroup.det_coe]
  refine ⟨⟨z, hzu⟩, ?_⟩
  ext : 2
  rw [coe_unitaryToStabilizer, hz]

/-- For primitive `f`, the norm-one elements of the order with coefficients in `R` are the
automorphs of `f` over `R`. -/
private noncomputable def unitaryEquivStabilizer (hfD : f.discrim = D) (hf : f.IsPrimitive)
    (h2 : IsLeftRegular (2 : R)) :
    unitary (QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D) ≃*
      stabilizer SL(2, R) (f.map (Int.castRingHom R)) :=
  MulEquiv.ofBijective (unitaryToStabilizer f hfD)
    ⟨fun z w h ↦ Subtype.ext <| regularRep_injective f hfD hf <| by
      simpa only [coe_unitaryToStabilizer] using
        congrArg (fun γ : stabilizer SL(2, R) (f.map (Int.castRingHom R)) ↦
          ((γ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)) h,
      unitaryToStabilizer_surjective f hfD hf h2⟩

private theorem unitaryEquivStabilizer_apply (hfD : f.discrim = D) (hf : f.IsPrimitive)
    (h2 : IsLeftRegular (2 : R)) (z : unitary (QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D)) :
    unitaryEquivStabilizer f hfD hf h2 z = unitaryToStabilizer f hfD z :=
  MulEquiv.ofBijective_apply _ _ _

/-! ### Automorphs and norm-one elements over a coefficient ring -/

variable {f}

/-- **Automorphs are norm-one elements of the order.** Let `f` be a primitive integral binary
quadratic form of discriminant `D`, and let `R` be a commutative ring in which `2` is not a zero
divisor. The proper automorphs of `f` with coefficients in `R` form a group isomorphic to the
norm-one elements of `R[ω]/(ω² - D ω + (D² - D)/4)`, the quadratic order `ℤ[(D + √D)/2]` of
discriminant `D` with coefficients in `R`. The inverse is described by
`coe_stabilizerEquivUnitary_symm_apply`. -/
noncomputable def stabilizerEquivUnitary (hf : f.IsPrimitive) (hfD : f.discrim = D)
    (h2 : IsLeftRegular (2 : R)) :
    stabilizer SL(2, R) (f.map (Int.castRingHom R)) ≃*
      unitary (QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D) :=
  (unitaryEquivStabilizer f hfD hf h2).symm

/-- The automorph attached to the norm-one element `x + y ω`, where `ω` is the image of
`(D + √D)/2`, is `!![x + y (D - b)/2, -c y; a y, x + y (D + b)/2]`. -/
theorem coe_stabilizerEquivUnitary_symm_apply (hf : f.IsPrimitive) (hfD : f.discrim = D)
    (h2 : IsLeftRegular (2 : R)) (z : unitary (QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D)) :
    (((stabilizerEquivUnitary hf hfD h2).symm z : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) =
      let x := (z : QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D).re
      let y := (z : QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D).im
      !![x + y * (((D - f.b) / 2 : ℤ) : R), -f.c * y;
        f.a * y, x + y * (((D + f.b) / 2 : ℤ) : R)] := by
  have he := two_mul_ediv_two_of_discrim_eq (discrim_eq_sq_sub_four_mul f hfD)
  have hD : D - (D - f.b) / 2 = (D + f.b) / 2 := by omega
  rw [stabilizerEquivUnitary, MulEquiv.symm_symm, unitaryEquivStabilizer_apply,
    coe_unitaryToStabilizer, regularRep_eq, hD]

/-- **Naturality in the coefficient ring.** A ring homomorphism `φ : R →+* S` maps the automorph
attached to a norm-one element `z` over `R` entrywise to the automorph attached to the norm-one
element over `S` whose coordinates are the images of those of `z`. -/
theorem map_stabilizerEquivUnitary_symm_apply {S : Type*} [CommRing S] (φ : R →+* S)
    (hf : f.IsPrimitive) (hfD : f.discrim = D) (hR : IsLeftRegular (2 : R))
    (hS : IsLeftRegular (2 : S)) (z : unitary (QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D))
    (w : unitary (QuadraticAlgebra S (((D - D ^ 2) / 4 : ℤ) : S) D))
    (hre : (w : QuadraticAlgebra S (((D - D ^ 2) / 4 : ℤ) : S) D).re =
      φ (z : QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D).re)
    (him : (w : QuadraticAlgebra S (((D - D ^ 2) / 4 : ℤ) : S) D).im =
      φ (z : QuadraticAlgebra R (((D - D ^ 2) / 4 : ℤ) : R) D).im) :
    SpecialLinearGroup.map φ ((stabilizerEquivUnitary hf hfD hR).symm z : SL(2, R)) =
      ((stabilizerEquivUnitary hf hfD hS).symm w : SL(2, S)) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    coe_stabilizerEquivUnitary_symm_apply, coe_stabilizerEquivUnitary_symm_apply]
  fin_cases i <;> fin_cases j <;> simp [hre, him]

/-! ### Integral automorphs and norm-one units -/

/-- **Automorphs are norm-one units.** For a primitive integral binary quadratic form `f` of
discriminant `D`, the proper automorphs of `f` form a group isomorphic to the norm-one units of the
quadratic order `ℤ[(D + √D)/2]` of discriminant `D`. This is the case `R = ℤ` of
`stabilizerEquivUnitary`, read in the embedded order. The inverse is described by
`map_stabilizerEquivNormOneUnits_symm_apply`. -/
noncomputable def stabilizerEquivNormOneUnits (hf : f.IsPrimitive) (hfD : f.discrim = D) :
    stabilizer SL(2, ℤ) f ≃*
      QuadraticOrder.normOneUnits D (hfD ▸ f.discrim_emod_four_eq_zero_or_one) :=
  -- `Int.cast : ℤ → ℤ` is the identity by definition (`Int.cast_id` is `rfl`), so the
  -- parameters of the integral model read over `ℤ` are those of `normOneUnitsEquivUnitary`.
  (MulEquiv.subgroupCongr (by rw [Int.castRingHom_int, map_id])).trans <|
    (stabilizerEquivUnitary hf hfD (IsRegular.of_ne_zero two_ne_zero).left).trans
      (QuadraticOrder.normOneUnitsEquivUnitary D _).symm

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
      ((stabilizerEquivUnitary hf hfD (IsRegular.of_ne_zero two_ne_zero).left).symm z :
        SL(2, ℤ)) := by
    rw [stabilizerEquivNormOneUnits, MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply,
      MulEquiv.symm_symm, MulEquiv.subgroupCongr_symm_apply]
  have heZ := two_mul_ediv_two_of_discrim_eq (discrim_eq_sq_sub_four_mul f hfD)
  have he : (2 : ℚ) * (((D - f.b) / 2 : ℤ) : ℚ) = D - f.b := by exact_mod_cast heZ
  have he' : (2 : ℚ) * (((D + f.b) / 2 : ℤ) : ℚ) = D + f.b := by
    exact_mod_cast (by omega : 2 * ((D + f.b) / 2) = D + f.b)
  rw [hsymm, coe_stabilizerEquivUnitary_symm_apply, hu, QuadraticOrder.lift_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (z.1.im : ℚ) / 2 * he
  · ring
  · ring
  · linear_combination (z.1.im : ℚ) / 2 * he'

end TauCeti.BinaryQuadraticForm
