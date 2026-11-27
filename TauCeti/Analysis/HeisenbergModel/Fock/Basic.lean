/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.WeilOperators
public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.Matrix.DeterminantBound.L2OpNorm
import TauCeti.LinearAlgebra.Matrix.DotProduct
import TauCeti.Analysis.SpecialFunctions.Gaussian.Accretive
import TauCeti.Analysis.SpecialFunctions.Gaussian.Reproducing
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Fock model of `U(ε)`: datum, vacuum and multiplier

For a finite type `ι` and signs `ε : ι → ℤˣ`, let `U(ε)` be the unitary group of the hermitian form
`star x ⬝ᵥ diag(ε) *ᵥ y` on `ι → ℂ` (`Matrix.unitaryGroupOf (signMatrix ε)`, which is `U(p, q)` for
`p` positive and `q` negative signs). This file builds the Fock model of the Weil representation of
`U(ε)` as a reproducing model in the sense of `TauCeti.ReproducingModel`.

The Heisenberg datum on `ι → ℂ` is `β_ε(x, y) = exp ((y* ε x - x* ε y) / 2)`, the measure is
`π^{-|ι|} dx`, and the Gaussian `e(x) = exp (-|x|² / 2)` is a vacuum: with the holomorphic
coordinates `ζ(x) i = conj (x i)` for `ε i = 1` and `ζ(x) i = x i` for `ε i = -1`, a translate of
the vacuum is `β_ε(y, x) e(x - y) = e(x) e(y) exp (∑ i, conj (ζ(y) i) ζ(x) i)`, so the vacuum
identity is the Gaussian reproducing formula `TauCeti.integral_cexp_reproducing`.

The group `U(ε)` acts on `ι → ℂ` by matrices, preserving `β_ε` and the measure, and
`Δ_∞(u) = conj (det u₋₋)`, for the block `u₋₋` of `u` on the indices of sign `-1`, is a multiplier.
Its cocycle is trivial: the double integral defining it is the Gaussian `exp (-z* A z)` on
`(ι → ℂ)²` of the strictly accretive matrix `A = ½ (J* J + (1, 1 + ε; 1 - ε, 1))`,
`J = diag(h, g h)`, whose integral is `π^{2|ι|} / det A`
(`TauCeti.integral_cexp_neg_star_dotProduct_mulVec`), and `A` factors into three block matrices
whose determinants give `det A = Δ_∞(g) Δ_∞(h) Δ_∞((g h)⁻¹)`. So the Weil operators of `Δ_∞` form a
jointly continuous representation `ω_ε` of `U(ε)` on the Fock space `𝓕(ε) = M(β_ε, e)` preserving
`⟨·, ·⟩`, with `‖ω_ε(u)‖ ≤ ‖e‖ ‖u‖^{|ι|}` for the operator norm of the standard hermitian norm.

## Main definitions

* `TauCeti.Fock.unitaryGroup`: the group `U(ε)`.
* `TauCeti.Fock.heisenbergDatum`, `TauCeti.Fock.gaussian`, `TauCeti.Fock.measure`: `β_ε`, `e` and
  `π^{-|ι|} dx`.
* `TauCeti.Fock.holomorphicCoord`: the holomorphic coordinates `ζ`.
* `TauCeti.Fock.multiplier`: the multiplier `Δ_∞`.
* `TauCeti.Fock.FockSpace`, `TauCeti.Fock.weilRep`: the Fock space `𝓕(ε)` and the Weil
  representation `ω_ε`.

## Main results

* `TauCeti.Fock.heisenbergDatum_mul_gaussian`, `TauCeti.Fock.isVacuum_gaussian`: the reproducing
  kernel of the Gaussian, and the Gaussian is a vacuum.
* `TauCeti.Fock.cocycle_multiplier`: the cocycle of `Δ_∞` is trivial.
* `TauCeti.Fock.norm_multiplier_le`, `TauCeti.Fock.norm_weilRep_le`,
  `TauCeti.Fock.continuous_weilRep`: the bounds `|Δ_∞(u)| ≤ ‖u‖^{|ι|}` and
  `‖ω_ε(u)‖ ≤ ‖e‖ ‖u‖^{|ι|}`, and the joint continuity of `ω_ε`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/Lib/Weil/Fock/Basic.lean` (`New.Fock.realHeisenberg`, `New.Fock.realVac`,
`New.Fock.posProj`, `New.Fock.holomorphicCoord`, `New.Fock.principalMinor_sign_eq_det`,
`New.Fock.realMultiplier`, `New.Fock.norm_realMultiplier_le`, `New.Fock.beta_mul_realVac`,
`New.Fock.isVacuum_realVac`, `New.Fock.realMultiplier_mul_integral_eq_one`, `New.Fock.realAction`,
`New.Fock.fockSpace`, `New.Fock.realWeil`), with `New.Fock.norm_realWeil_le` from
`src/Lib/Weil/Fock/OscillatorPair.lean`. The vacuum identity uses Tau Ceti's Gaussian reproducing
formula in place of the source's accretive Gaussian integral.

## References

* V. Bargmann, *On a Hilbert space of analytic functions and an associated integral transform,
  part I*, Comm. Pure Appl. Math. 14 (1961), 187–214.
* M. Kashiwara, M. Vergne, *On the Segal–Shale–Weil representations and harmonic polynomials*,
  Invent. Math. 44 (1978), 1–48.
* R. Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989), 535–552.
* G. B. Folland, *Harmonic analysis in phase space*, Ann. of Math. Stud. 122 (1989), Chapter 1.
-/

public noncomputable section

open MeasureTheory Matrix Complex Finset
open scoped ComplexConjugate ComplexOrder

namespace TauCeti.Fock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ι → ℤˣ)

/-! ### Signs -/

/-- The diagonal matrix `diag(ε)` of a sign vector `ε : ι → ℤˣ`, over `ℂ`. -/
def signMatrix : Matrix ι ι ℂ := diagonal fun i ↦ ((ε i : ℤ) : ℂ)

omit [Fintype ι] in
theorem signMatrix_eq_diagonal : signMatrix ε = diagonal fun i ↦ ((ε i : ℤ) : ℂ) := (rfl)

/-- The unitary group `U(ε)` of the hermitian form `star x ⬝ᵥ diag(ε) *ᵥ y` on `ι → ℂ`. -/
abbrev unitaryGroup : Subgroup (GL ι ℂ) := Matrix.unitaryGroupOf (signMatrix ε)

variable {ε}

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem sign_mul_sign (i : ι) : ((ε i : ℤ) : ℂ) * ((ε i : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
theorem conj_sign (i : ι) : conj ((ε i : ℤ) : ℂ) = ((ε i : ℤ) : ℂ) := by
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem norm_sign (i : ι) : ‖((ε i : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]

omit [Fintype ι] in
@[simp]
theorem signMatrix_mul_signMatrix [Fintype ι] : signMatrix ε * signMatrix ε = 1 := by
  simp [signMatrix, diagonal_mul_diagonal, ← diagonal_one]

omit [Fintype ι] in
@[simp]
theorem conjTranspose_signMatrix : (signMatrix ε)ᴴ = signMatrix ε := by
  simp [signMatrix]

theorem isUnit_signMatrix : IsUnit (signMatrix ε) :=
  ⟨⟨_, _, signMatrix_mul_signMatrix, signMatrix_mul_signMatrix⟩, rfl⟩

/-- `U(ε)` is second countable, being a subspace of the matrices. -/
instance : SecondCountableTopology (unitaryGroup ε) :=
  (unitaryGroupOf.isClosedEmbedding_val isUnit_signMatrix).isEmbedding.secondCountableTopology

/-- `U(ε)` is locally compact, being a closed subset of the matrices. -/
instance : LocallyCompactSpace (unitaryGroup ε) :=
  (unitaryGroupOf.isClosedEmbedding_val isUnit_signMatrix).locallyCompactSpace

theorem signMatrix_mem_unitary : signMatrix ε ∈ unitary (Matrix ι ι ℂ) := by
  simp [Unitary.mem_iff, star_eq_conjTranspose]

theorem inv_signMatrix : (signMatrix ε)⁻¹ = signMatrix ε :=
  inv_eq_left_inv signMatrix_mul_signMatrix

omit [DecidableEq ι] in
theorem star_dotProduct_signMatrix_mulVec [DecidableEq ι] (x y : ι → ℂ) :
    star x ⬝ᵥ signMatrix ε *ᵥ y = ∑ i, ((ε i : ℤ) : ℂ) * (conj (x i) * y i) := by
  simp only [signMatrix, mulVec_diagonal, dotProduct, Pi.star_apply, RCLike.star_def]
  exact sum_congr rfl fun i _ ↦ by ring

theorem conj_star_dotProduct_signMatrix_mulVec (x y : ι → ℂ) :
    conj (star x ⬝ᵥ signMatrix ε *ᵥ y) = star y ⬝ᵥ signMatrix ε *ᵥ x := by
  simp only [star_dotProduct_signMatrix_mulVec, map_sum, map_mul, conj_sign, conj_conj]
  exact sum_congr rfl fun i _ ↦ by ring

/-- For `g ∈ U(ε)`, `g • x = g *ᵥ x`. -/
theorem smul_def (g : unitaryGroup ε) (x : ι → ℂ) :
    g • x = ((g : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ x := rfl

/-! ### The Heisenberg datum, the Gaussian vacuum and the measure -/

variable (ε) in
/-- The Heisenberg datum `β_ε(x, y) = exp ((y* ε x - x* ε y) / 2)` on `ι → ℂ`, of modulus one since
the exponent is purely imaginary. -/
def heisenbergDatum : HeisenbergDatum (ι → ℂ) where
  toFun x y := cexp ((star y ⬝ᵥ signMatrix ε *ᵥ x - star x ⬝ᵥ signMatrix ε *ᵥ y) / 2)
  map_add_left' x x' y := by
    rw [← Complex.exp_add]
    congr 1
    simp only [mulVec_add, dotProduct_add, star_add, add_dotProduct]
    ring
  map_add_right' x y y' := by
    rw [← Complex.exp_add]
    congr 1
    simp only [mulVec_add, dotProduct_add, star_add, add_dotProduct]
    ring
  apply_self' x := by simp
  norm_apply' x y := by
    rw [Complex.norm_exp, ← conj_star_dotProduct_signMatrix_mulVec]
    simp
  continuous_uncurry' := by
    simp only [star_dotProduct_signMatrix_mulVec]
    fun_prop

theorem heisenbergDatum_apply (x y : ι → ℂ) :
    heisenbergDatum ε x y =
      cexp ((star y ⬝ᵥ signMatrix ε *ᵥ x - star x ⬝ᵥ signMatrix ε *ᵥ y) / 2) := (rfl)

variable (ι) in
/-- The Gaussian `e(x) = exp (-|x|² / 2)` on `ι → ℂ`, for the Euclidean norm `|x|`. -/
def gaussian (x : ι → ℂ) : ℂ := cexp (-(∑ i, (‖x i‖ : ℂ) ^ 2) / 2)

omit [DecidableEq ι] in
theorem gaussian_apply (x : ι → ℂ) : gaussian ι x = cexp (-(∑ i, (‖x i‖ : ℂ) ^ 2) / 2) := (rfl)

variable (ι) in
/-- The measure `π^{-|ι|} dx` on `ι → ℂ`, for Lebesgue measure `dx`. -/
def measure : Measure (ι → ℂ) := ENNReal.ofReal ((1 / Real.pi) ^ Fintype.card ι) • volume

omit [DecidableEq ι] in
theorem measure_def :
    measure ι = ENNReal.ofReal ((1 / Real.pi) ^ Fintype.card ι) • volume := (rfl)

omit [DecidableEq ι] in
instance : (measure ι).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _ (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top

variable (ε) in
/-- The holomorphic coordinates `ζ(x)`: `ζ(x) i` is `conj (x i)` if `ε i = 1` and `x i` if
`ε i = -1`. -/
def holomorphicCoord (x : ι → ℂ) : ι → ℂ := fun i ↦ if ε i = 1 then conj (x i) else x i

omit [Fintype ι] [DecidableEq ι] in
theorem holomorphicCoord_apply (x : ι → ℂ) (i : ι) :
    holomorphicCoord ε x i = if ε i = 1 then conj (x i) else x i := (rfl)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem holomorphicCoord_apply_of_eq_one {x : ι → ℂ} {i : ι} (h : ε i = 1) :
    holomorphicCoord ε x i = conj (x i) := by
  simp [holomorphicCoord_apply, h]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem holomorphicCoord_apply_of_eq_neg_one {x : ι → ℂ} {i : ι} (h : ε i = -1) :
    holomorphicCoord ε x i = x i := by
  simp [holomorphicCoord_apply, h]

omit [Fintype ι] [DecidableEq ι] in
@[fun_prop]
theorem continuous_holomorphicCoord : Continuous (holomorphicCoord (ι := ι) ε) :=
  continuous_pi fun i ↦ by simp only [holomorphicCoord]; split_ifs <;> fun_prop

omit [Fintype ι] [DecidableEq ι] in
theorem holomorphicCoord_sub (x y : ι → ℂ) :
    holomorphicCoord ε (x - y) = holomorphicCoord ε x - holomorphicCoord ε y := by
  ext i
  simp only [holomorphicCoord, Pi.sub_apply]
  split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem norm_holomorphicCoord_apply (x : ι → ℂ) (i : ι) : ‖holomorphicCoord ε x i‖ = ‖x i‖ := by
  simp only [holomorphicCoord]
  split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem holomorphicCoord_holomorphicCoord (x : ι → ℂ) :
    holomorphicCoord ε (holomorphicCoord ε x) = x := by
  ext i
  simp only [holomorphicCoord]
  split_ifs <;> simp

omit [DecidableEq ι] in
private theorem ofReal_norm_sq (z : ℂ) : (‖z‖ : ℂ) ^ 2 = conj z * z := (conj_mul' z).symm

/-- **The reproducing kernel of the Gaussian**: with `ζ` the holomorphic coordinates,
`β(y, x) e(x - y) = e(x) e(y) exp (∑ i, conj (ζ(y) i) * ζ(x) i)`. -/
theorem heisenbergDatum_mul_gaussian (x y : ι → ℂ) :
    heisenbergDatum ε y x * gaussian ι (x - y) =
      gaussian ι x * gaussian ι y *
        cexp (∑ i, conj (holomorphicCoord ε y i) * holomorphicCoord ε x i) := by
  simp only [heisenbergDatum_apply, gaussian, ← Complex.exp_add]
  congr 1
  rw [← sub_eq_zero]
  simp only [star_dotProduct_signMatrix_mulVec, sum_div, ← sum_neg_distrib, ← sum_sub_distrib,
    ← sum_add_distrib]
  refine sum_eq_zero fun i _ ↦ ?_
  simp only [holomorphicCoord, Pi.sub_apply, ofReal_norm_sq, map_sub]
  rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h] <;> ring

omit [DecidableEq ι] in
private theorem gaussian_eq_exp_sum (x : ι → ℂ) :
    gaussian ι x = cexp (-∑ i, (1 / 2 : ℂ) * (‖x i‖ : ℂ) ^ 2 + ∑ i, (0 : ℂ) * x i +
      ∑ i, (0 : ℂ) * conj (x i)) := by
  simp [gaussian, ← mul_sum, div_eq_inv_mul]

omit [DecidableEq ι] in
theorem integrable_gaussian : Integrable (gaussian ι) (measure ι) := by
  have h := integrable_cexp_neg_sum_mul_norm_sq_add (ι := ι) (a := fun _ ↦ 1 / 2)
    (fun _ ↦ by norm_num) 0 0
  simp only [Pi.zero_apply] at h
  rw [funext gaussian_eq_exp_sum]
  exact h.smul_measure ENNReal.ofReal_ne_top

omit [DecidableEq ι] in
@[fun_prop]
theorem continuous_gaussian : Continuous (gaussian ι) := by
  unfold gaussian
  fun_prop

/-- The integrand of the vacuum identity, as a product of the exponentials of
`TauCeti.integral_cexp_reproducing`. -/
private theorem gaussian_mul_heisenbergDatum (x y z : ι → ℂ) :
    gaussian ι z * (heisenbergDatum ε z y *
        (heisenbergDatum ε (z + y) x * gaussian ι (x - (z + y)))) =
      gaussian ι y * gaussian ι x *
        cexp (∑ i, conj (holomorphicCoord ε y i) * holomorphicCoord ε x i) *
        (cexp (∑ i, -conj (holomorphicCoord ε y i) *
            (if decide (ε i = 1) then conj (z i) else z i)) *
          cexp (((1 : ℝ) : ℂ) * ∑ i, conj (if decide (ε i = 1) then conj (z i) else z i) *
            holomorphicCoord ε x i) *
          cexp (-((1 : ℝ) : ℂ) * ∑ i, (‖z i‖ : ℂ) ^ 2)) := by
  simp only [heisenbergDatum_apply, gaussian, ← Complex.exp_add]
  congr 1
  rw [← sub_eq_zero]
  simp only [star_dotProduct_signMatrix_mulVec, sum_div, ← sum_neg_distrib, ← sum_sub_distrib,
    ← sum_add_distrib, mul_sum, ofReal_one]
  refine sum_eq_zero fun i _ ↦ ?_
  simp only [holomorphicCoord, Pi.sub_apply, Pi.add_apply, ofReal_norm_sq, map_sub, map_add]
  rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h] <;> ring

/-- The Gaussian is a vacuum for `β_ε` and the measure `π^{-|ι|} dx`. -/
instance isVacuum_gaussian : (heisenbergDatum ε).IsVacuum (measure ι) (gaussian ι) where
  continuous := continuous_gaussian
  integrable := integrable_gaussian
  apply_zero := by simp [gaussian]
  apply_neg x := by simp [gaussian]
  conj_apply x := by
    simp only [gaussian, ← Complex.exp_conj, map_div₀, map_neg, map_sum, map_pow, conj_ofReal,
      map_ofNat]
  integral_mul_apply y x := by
    simp_rw [gaussian_mul_heisenbergDatum, integral_const_mul]
    rw [measure, integral_cexp_reproducing one_pos]
    simp [← Complex.exp_add, mul_assoc]

/-! ### The multiplier -/

variable (ε) in
/-- The block `u₋₋` of a square matrix on the indices of sign `-1`. -/
def negBlock (u : Matrix ι ι ℂ) : Matrix {i // ε i = -1} {i // ε i = -1} ℂ :=
  u.submatrix Subtype.val Subtype.val

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem negBlock_apply (u : Matrix ι ι ℂ) (i j : {i // ε i = -1}) : negBlock ε u i j = u i j :=
  (rfl)

/-- The negative block of `g⁻¹` is the conjugate transpose of that of `g`, for `g ∈ U(ε)`. -/
theorem negBlock_inv (g : unitaryGroup ε) :
    negBlock ε (((g⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ) =
      (negBlock ε ((g : GL ι ℂ) : Matrix ι ι ℂ))ᴴ := by
  rw [Subgroup.coe_inv, val_inv_of_mem_unitaryGroupOf isUnit_signMatrix g.property, inv_signMatrix]
  ext i j
  simp [negBlock, signMatrix, diagonal_mul, mul_diagonal, i.property, j.property,
    star_eq_conjTranspose]

theorem continuous_negBlock_det :
    Continuous fun g : unitaryGroup ε ↦ (negBlock ε ((g : GL ι ℂ) : Matrix ι ι ℂ)).det :=
  ((Units.continuous_val.comp continuous_subtypeVal).matrix_submatrix _ _).matrix_det

theorem measurePreserving_smul (g : unitaryGroup ε) :
    MeasurePreserving (g • · : (ι → ℂ) → ι → ℂ) (measure ι) (measure ι) := by
  have h_norm : ‖((g : GL ι ℂ) : Matrix ι ι ℂ).det‖ = 1 :=
    CStarRing.norm_of_mem_unitary
      (det_mem_unitary_of_mem_unitaryGroupOf isUnit_signMatrix g.property)
  refine ⟨(continuous_const.matrix_mulVec continuous_id).measurable, ?_⟩
  rw [funext (smul_def g), map_mulVec_addHaar_eq_smul fun h ↦ by simp [h] at h_norm]
  simp [h_norm]

variable (ε) in
/-- The multiplier `Δ_∞(u) = conj (det u₋₋)` of `U(ε)` for `β_ε` and `π^{-|ι|} dx`. -/
def multiplier : (heisenbergDatum ε).Multiplier (measure ι) (unitaryGroup ε) where
  toFun g := conj (negBlock ε ((g : GL ι ℂ) : Matrix ι ι ℂ)).det
  apply_smul_smul g x y := by
    simp only [heisenbergDatum_apply, smul_def,
      (mem_unitaryGroupOf_iff_forall_dotProduct.mp g.property)]
  measurePreserving_smul := measurePreserving_smul
  continuous_toFun := Complex.continuous_conj.comp continuous_negBlock_det
  map_one' := by simp [negBlock, submatrix_one _ Subtype.val_injective]
  map_inv' g := by rw [negBlock_inv, det_conjTranspose, Complex.star_def]

theorem multiplier_apply (g : unitaryGroup ε) :
    multiplier ε g = conj (negBlock ε ((g : GL ι ℂ) : Matrix ι ι ℂ)).det := (rfl)

open scoped Matrix.Norms.L2Operator in
/-- `|Δ_∞(u)| ≤ ‖u‖^{|ι|}` for the operator norm of the standard hermitian norm. -/
theorem norm_multiplier_le (g : unitaryGroup ε) :
    ‖multiplier ε g‖ ≤ ‖((g : GL ι ℂ) : Matrix ι ι ℂ)‖ ^ Fintype.card ι := by
  rw [multiplier_apply, RCLike.norm_conj]
  refine (Matrix.norm_det_le_l2_opNorm_pow _).trans ?_
  calc ‖negBlock ε ((g : GL ι ℂ) : Matrix ι ι ℂ)‖ ^ Fintype.card {i // ε i = -1}
      ≤ ‖((g : GL ι ℂ) : Matrix ι ι ℂ)‖ ^ Fintype.card {i // ε i = -1} :=
        pow_le_pow_left₀ (norm_nonneg _)
          (l2_opNorm_submatrix_le _ Subtype.val_injective Subtype.val_injective) _
    _ ≤ ‖((g : GL ι ℂ) : Matrix ι ι ℂ)‖ ^ Fintype.card ι := by
      cases isEmpty_or_nonempty ι
      · simp
      · exact pow_le_pow_right₀
          (one_le_norm_val_of_mem_unitaryGroupOf signMatrix_mem_unitary g.property)
          (Fintype.card_subtype_le _)

/-! ### The cocycle is trivial -/

variable (ε) in
/-- The projection `P₊` onto the coordinates of sign `1`. -/
private def posProj : Matrix ι ι ℂ := diagonal fun i ↦ if ε i = 1 then 1 else 0

variable (ε) in
/-- `P₊ + P₋ x`, for the projections `P₊` and `P₋ = 1 - P₊` onto the coordinates of sign `1` and
`-1`. -/
private def posProjAdd (x : Matrix ι ι ℂ) : Matrix ι ι ℂ := posProj ε + (1 - posProj ε) * x

omit [Fintype ι] in
private theorem signMatrix_eq_posProj_sub : signMatrix ε = posProj ε - (1 - posProj ε) := by
  rw [signMatrix, posProj, ← diagonal_one, diagonal_sub, diagonal_sub]
  congr 1
  funext i
  rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]

private theorem posProj_mul_posProj : posProj ε * posProj ε = posProj ε := by
  simp [posProj]

omit [Fintype ι] in
private theorem conjTranspose_posProj : (posProj ε)ᴴ = posProj ε := by
  simp [posProj]

/-- The determinant of `P₊ + P₋ x` is the minor of `x` on the indices of sign `-1`. -/
private theorem det_posProjAdd (x : Matrix ι ι ℂ) : (posProjAdd ε x).det = (negBlock ε x).det := by
  let e := Equiv.sumCompl fun i ↦ ε i = -1
  have h_pos (i : {i // ¬ ε i = -1}) : ε i = 1 :=
    (Int.units_eq_one_or (ε i)).resolve_right i.property
  have h_blocks : (posProjAdd ε x).submatrix e e =
      fromBlocks (negBlock ε x) (x.submatrix Subtype.val Subtype.val) 0 1 := by
    ext (i | i) (j | j)
    · simp [e, posProjAdd, negBlock, posProj, sub_mul, diagonal_mul, diagonal_apply, i.property]
    · simp [e, posProjAdd, posProj, sub_mul, diagonal_mul, diagonal_apply, i.property]
    · have h_ne : (i : ι) ≠ j := fun h ↦ i.property (h ▸ j.property)
      simp [e, posProjAdd, posProj, sub_mul, diagonal_mul, h_pos, h_ne]
    · simp [e, posProjAdd, posProj, sub_mul, diagonal_mul, diagonal_apply, Matrix.one_apply, h_pos,
        Subtype.ext_iff]
  rw [← det_submatrix_equiv_self e, h_blocks, det_fromBlocks_zero₂₁, det_one, mul_one]

/-- `conj (det (P₊ + P₋ x)) = Δ_∞(x)`. -/
private theorem conj_det_posProjAdd (x : unitaryGroup ε) :
    conj (posProjAdd ε ((x : GL ι ℂ) : Matrix ι ι ℂ)).det = multiplier ε x := by
  rw [det_posProjAdd, multiplier_apply]

/-- `det (P₊ + P₋ x⁻¹) = Δ_∞(x)`. -/
private theorem det_posProjAdd_inv (x : unitaryGroup ε) :
    (posProjAdd ε (((x⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ)).det = multiplier ε x := by
  rw [det_posProjAdd, negBlock_inv, det_conjTranspose, multiplier_apply, Complex.star_def]

variable (ε) in
/-- The matrix `A = ½ (J* J + (1, 1 + ε; 1 - ε, 1))`, `J = diag(h, g h)`, of the Gaussian on
`(ι → ℂ)²` whose integral is the cocycle of `Δ_∞` at `(g, h)`. -/
private def cocycleMatrix (g h : unitaryGroup ε) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  (2⁻¹ : ℂ) • ((fromBlocks ((h : GL ι ℂ) : Matrix ι ι ℂ) 0 0
      (((g * h : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ))ᴴ *
      fromBlocks ((h : GL ι ℂ) : Matrix ι ι ℂ) 0 0
        (((g * h : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ) +
      fromBlocks 1 (1 + signMatrix ε) (1 - signMatrix ε) 1)

/-- For `u ∈ U(ε)`, `½ (u* u + 1) = P₊ + u* P₋ u`, as `u* (P₊ - P₋) u = P₊ - P₋`. -/
private theorem two_inv_smul_conjTranspose_mul_add_one (u : unitaryGroup ε) :
    (2⁻¹ : ℂ) • ((((u : GL ι ℂ) : Matrix ι ι ℂ))ᴴ * ((u : GL ι ℂ) : Matrix ι ι ℂ) + 1) =
      posProj ε +
        (((u : GL ι ℂ) : Matrix ι ι ℂ))ᴴ * (1 - posProj ε) * ((u : GL ι ℂ) : Matrix ι ι ℂ) := by
  have hu := mem_unitaryGroupOf_iff.mp u.property
  rw [star_eq_conjTranspose, signMatrix_eq_posProj_sub] at hu
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one] at hu ⊢
  linear_combination (norm := module) (2⁻¹ : ℂ) • hu

/-- For `u ∈ U(ε)`, `½ (u* u + 1) = P₋ + u* P₊ u`, as `u* (P₊ - P₋) u = P₊ - P₋`. -/
private theorem two_inv_smul_conjTranspose_mul_add_one' (u : unitaryGroup ε) :
    (2⁻¹ : ℂ) • ((((u : GL ι ℂ) : Matrix ι ι ℂ))ᴴ * ((u : GL ι ℂ) : Matrix ι ι ℂ) + 1) =
      (1 - posProj ε) +
        (((u : GL ι ℂ) : Matrix ι ι ℂ))ᴴ * posProj ε * ((u : GL ι ℂ) : Matrix ι ι ℂ) := by
  have hu := mem_unitaryGroupOf_iff.mp u.property
  rw [star_eq_conjTranspose, signMatrix_eq_posProj_sub] at hu
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one] at hu ⊢
  linear_combination (norm := module) (-2⁻¹ : ℂ) • hu

/-- The blocks of the cocycle matrix, by the unitarity of `h` and `k = g h`:
`A = (P₊ + h* P₋ h, P₊; P₋, P₋ + k* P₊ k)`. -/
private theorem cocycleMatrix_eq_fromBlocks (g h : unitaryGroup ε) :
    cocycleMatrix ε g h = fromBlocks
      (posProj ε +
        (((h : GL ι ℂ) : Matrix ι ι ℂ))ᴴ * (1 - posProj ε) * ((h : GL ι ℂ) : Matrix ι ι ℂ))
      (posProj ε) (1 - posProj ε)
      ((1 - posProj ε) + (((g * h : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ)ᴴ * posProj ε *
        (((g * h : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ)) := by
  rw [← two_inv_smul_conjTranspose_mul_add_one, ← two_inv_smul_conjTranspose_mul_add_one',
    cocycleMatrix, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_add, fromBlocks_smul,
    signMatrix_eq_posProj_sub]
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1 <;> module

/-- The cocycle matrix factors as `X* M Y` with `T x = P₊ + P₋ x`, `k = g h` and
`X = (T h, P₋; 0, T k⁻¹ k)`, `M = (P₊, -P₋; 1, 1)`, `Y = (1, 1; -T h, -T h + T g⁻¹ k)`:
indeed `M Y = (T h, P₊; P₋ (1 - h), P₋ + P₊ k)`. -/
private theorem cocycleMatrix_eq_mul (g h : unitaryGroup ε) :
    cocycleMatrix ε g h =
      (fromBlocks (posProjAdd ε ((h : GL ι ℂ) : Matrix ι ι ℂ)) (1 - posProj ε) 0
          (posProjAdd ε ((((g * h)⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ) *
            (((g * h : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ)))ᴴ *
        fromBlocks (posProj ε) (posProj ε - 1) 1 1 *
        fromBlocks 1 1 (-posProjAdd ε ((h : GL ι ℂ) : Matrix ι ι ℂ))
          (-posProjAdd ε ((h : GL ι ℂ) : Matrix ι ι ℂ) +
            posProjAdd ε (((g⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ) *
              (((g * h : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ)) := by
  have hPP (x : Matrix ι ι ℂ) : posProj ε * (posProj ε * x) = posProj ε * x := by
    rw [← Matrix.mul_assoc, posProj_mul_posProj]
  have hGK : (((g⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ) *
      (((g * h : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ) = ((h : GL ι ℂ) : Matrix ι ι ℂ) := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel_left]
  have hKK : ((((g * h : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ))ᴴ *
      (((((g * h)⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ))ᴴ = 1 := by
    rw [← conjTranspose_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    simp
  rw [cocycleMatrix_eq_fromBlocks, fromBlocks_conjTranspose, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [posProjAdd, conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one,
    conjTranspose_zero, conjTranspose_posProj, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_neg,
    Matrix.mul_assoc, hPP, hGK, hKK, posProj_mul_posProj]
  congr 1 <;> abel

/-- The determinant of the cocycle matrix is `Δ_∞(g) Δ_∞(h) Δ_∞((g h)⁻¹)`. -/
private theorem det_cocycleMatrix (g h : unitaryGroup ε) :
    (cocycleMatrix ε g h).det = multiplier ε g * multiplier ε h * multiplier ε (g * h)⁻¹ := by
  set k : unitaryGroup ε := g * h
  have h_det_k : conj (((k : GL ι ℂ) : Matrix ι ι ℂ)).det * (((k : GL ι ℂ) : Matrix ι ι ℂ)).det =
      1 := by
    rw [conj_mul', CStarRing.norm_of_mem_unitary
      (det_mem_unitary_of_mem_unitaryGroupOf isUnit_signMatrix k.property)]
    simp
  have h_middle : posProj ε - (posProj ε - 1) * 1 = 1 := by simp
  rw [cocycleMatrix_eq_mul, det_mul, det_mul, det_conjTranspose, det_fromBlocks_zero₂₁,
    det_fromBlocks_one₂₂, det_fromBlocks_one₁₁, h_middle, Matrix.mul_one, sub_neg_eq_add,
    neg_add_cancel_comm, det_one, det_mul, det_mul, Complex.star_def, map_mul, map_mul,
    conj_det_posProjAdd, conj_det_posProjAdd, det_posProjAdd_inv]
  linear_combination (multiplier ε g * multiplier ε h * multiplier ε k⁻¹) * h_det_k

omit [DecidableEq ι] in
theorem gaussian_eq_exp_star_dotProduct (x : ι → ℂ) : gaussian ι x = cexp (-(star x ⬝ᵥ x) / 2) := by
  simp [gaussian, dotProduct, ofReal_norm_sq]

/-- The quadratic form of the Gaussian integrand of the cocycle is strictly accretive. -/
private theorem isStrictlyAccretive_cocycleMatrix (g h : unitaryGroup ε) :
    (cocycleMatrix ε g h).IsStrictlyAccretive := by
  set J : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := fromBlocks ((h : GL ι ℂ) : Matrix ι ι ℂ) 0 0
    (((g * h : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ)
  set C : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := fromBlocks 1 1 0 0
  have h_add : cocycleMatrix ε g h + (cocycleMatrix ε g h)ᴴ = Jᴴ * J + Cᴴ * C := by
    simp only [cocycleMatrix, J, C, conjTranspose_smul, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, fromBlocks_conjTranspose, conjTranspose_one, conjTranspose_zero,
      conjTranspose_sub, conjTranspose_signMatrix, fromBlocks_multiply, fromBlocks_add,
      fromBlocks_smul, star_inv₀, star_ofNat, Matrix.mul_one, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> module
  rw [isStrictlyAccretive_iff_posDef, h_add]
  refine (PosDef.conjTranspose_mul_self J ?_).add_posSemidef (posSemidef_conjTranspose_mul_self C)
  rw [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det]
  simpa [J, det_fromBlocks_zero₂₁] using
    ⟨(isUnits_det_units (h : GL ι ℂ)).ne_zero, (isUnits_det_units (g : GL ι ℂ)).ne_zero,
      (isUnits_det_units (h : GL ι ℂ)).ne_zero⟩

/-- The integrand of the cocycle is the Gaussian `exp (-z* A z)` of `z = (x, y)`. -/
private theorem cocycle_integrand (g h : unitaryGroup ε) (x y : ι → ℂ) :
    gaussian ι (h • x) * gaussian ι ((g * h) • y) * heisenbergDatum ε x y * gaussian ι (x + y) =
      cexp (-(star (Sum.elim x y) ⬝ᵥ cocycleMatrix ε g h *ᵥ (Sum.elim x y - 0))) := by
  simp only [gaussian_eq_exp_star_dotProduct, heisenbergDatum_apply, smul_def, ← Complex.exp_add]
  congr 1
  simp only [cocycleMatrix, sub_zero, fromBlocks_conjTranspose, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_zero, fromBlocks_add,
    smul_mulVec, fromBlocks_mulVec, Function.star_sumElim, sumElim_dotProduct_sumElim, add_mulVec,
    sub_mulVec, one_mulVec, dotProduct_add, dotProduct_sub, dotProduct_smul, star_add,
    add_dotProduct, Sum.elim_comp_inl, Sum.elim_comp_inr, star_dotProduct_conjTranspose_mul_mulVec,
    smul_eq_mul]
  ring

/-- **The cocycle of `Δ_∞` is trivial**: for `g, h ∈ U(ε)`,
`Δ_∞(g) Δ_∞(h) Δ_∞((gh)⁻¹) ∫∫ e(hx) e(ghy) β_ε(x, y) e(x + y) dμ(x) dμ(y) = 1`. -/
theorem cocycle_multiplier (g h : unitaryGroup ε) :
    (multiplier ε).cocycle (gaussian ι) g h = 1 := by
  set A := cocycleMatrix ε g h
  have hA : A.IsStrictlyAccretive := isStrictlyAccretive_cocycleMatrix g h
  have h_det : A.det = multiplier ε g * multiplier ε h * multiplier ε (g * h)⁻¹ :=
    det_cocycleMatrix g h
  have h_gauss := integral_cexp_neg_star_dotProduct_mulVec hA 0
  -- Write the Gaussian integral over `ι ⊕ ι → ℂ` as an iterated integral.
  have h_int : Integrable (fun z : ι ⊕ ι → ℂ ↦ cexp (-(star z ⬝ᵥ A *ᵥ (z - 0)))) :=
    .of_integral_ne_zero (by
      rw [h_gauss]
      exact mul_ne_zero (by simp [Real.pi_ne_zero]) (inv_ne_zero hA.det_ne_zero))
  have h_mp := volume_measurePreserving_sumPiEquivProdPi_symm fun _ : ι ⊕ ι ↦ ℂ
  have h_symm (x y : ι → ℂ) :
      (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι ↦ ℂ).symm (x, y) = Sum.elim x y := by
    ext (i | i) <;> rfl
  have h_int' : Integrable (fun p ↦ cexp (-(star ((MeasurableEquiv.sumPiEquivProdPi
      fun _ : ι ⊕ ι ↦ ℂ).symm p) ⬝ᵥ A *ᵥ ((MeasurableEquiv.sumPiEquivProdPi
        fun _ : ι ⊕ ι ↦ ℂ).symm p - 0)))) (volume.prod volume) :=
    (h_mp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr h_int
  rw [← h_mp.integral_comp', Measure.volume_eq_prod, integral_prod _ h_int'] at h_gauss
  simp only [h_symm] at h_gauss
  rw [HeisenbergDatum.Multiplier.cocycle_def]
  simp_rw [cocycle_integrand, measure_def, integral_smul_measure]
  rw [integral_smul, h_gauss, ← h_det, ENNReal.toReal_ofReal (by positivity), Fintype.card_sum]
  have hd := hA.det_ne_zero
  generalize A.det = d at hd ⊢
  simp only [Complex.real_smul, ofReal_pow, ofReal_div, ofReal_one]
  field_simp
  rw [one_div, inv_pow, inv_pow, ← pow_mul, ← mul_two]
  exact inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero))

/-! ### The Fock space and the Weil representation -/

variable (ε) in
/-- The *Fock space* `𝓕(ε) = M(β_ε, e)`: the integrable functions on `ι → ℂ` reproduced by twisted
convolution with the Gaussian, with the `L¹` norm for `π^{-|ι|} dx`. -/
abbrev FockSpace : Type _ := ReproducingModel (heisenbergDatum ε) (measure ι) (gaussian ι)

variable (ε) in
/-- The *Weil representation* `ω_ε` of `U(ε)` on the Fock space, the Weil representation of the
multiplier `Δ_∞`, whose cocycle is trivial. It preserves `⟨·, ·⟩`
(`TauCeti.ReproducingModel.innerSL_weilRep`) and moves the Heisenberg operators
(`TauCeti.ReproducingModel.weilRep_heisenbergRep`). -/
abbrev weilRep : unitaryGroup ε →* FockSpace ε →L[ℂ] FockSpace ε :=
  ReproducingModel.weilRep (gaussian ι) (multiplier ε) cocycle_multiplier

open scoped Matrix.Norms.L2Operator in
/-- `‖ω_ε(u)‖ ≤ ‖e‖ ‖u‖^{|ι|}` for the operator norm of the standard hermitian norm. -/
theorem norm_weilRep_le (g : unitaryGroup ε) :
    ‖weilRep ε g‖ ≤ ‖(ReproducingModel.vacuum : FockSpace ε)‖ *
        ‖((g : GL ι ℂ) : Matrix ι ι ℂ)‖ ^ Fintype.card ι :=
  (ReproducingModel.norm_weilRep_le _ _ _).trans
    (mul_le_mul_of_nonneg_left (norm_multiplier_le g) (norm_nonneg _))

/-- The Weil representation of `U(ε)` is jointly continuous. -/
theorem continuous_weilRep :
    Continuous fun p : unitaryGroup ε × FockSpace ε ↦ weilRep ε p.1 p.2 :=
  ReproducingModel.continuous_weilRep _ _

end TauCeti.Fock
