/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import TauCeti.Analysis.StarAlgebra.GNS.Basic

/-!
# The Gaussian polynomial positive functional on `[-1, 1]`

This file constructs the classical counterexample showing that completeness cannot be omitted from
automatic continuity of positive functionals or from boundedness of the GNS representation on
normed ⋆-algebras.

Let `UnitIntervalStarPoly` be the complex polynomial algebra `ℂ[X]` equipped with coefficientwise
complex conjugation as its involution and the supremum norm on `[-1, 1]`. Its involution is
isometric (`NormedStarGroup`), and every monomial `X ^ n` has norm `1`. The Gaussian functional

`φ(p) = ∫ t : ℝ, p(t) * exp (-t ^ 2)`

is an algebraically square-positive linear functional (`StarPositiveFunctional`) on
`UnitIntervalStarPoly`. Its GNS norms satisfy `‖X ^ 0‖_φ² = √π`, `‖X‖_φ² = √π / 2`, and
`‖X ^ (n + 1)‖_φ² / ‖X ^ n‖_φ² = n + 1 / 2` for every `n : ℕ`. Consequently:

* `not_continuous_gaussianFunctional`: `φ` is unbounded on the unit sphere `‖X ^ (2 * n)‖ = 1`.
* `not_continuous_leftMul_X`: left multiplication by `X` is unbounded on the GNS pre-Hilbert
  space of `φ`.

## References

* M. A. Rieffel, *C⋆-algebras*, Math 208 lectures, UC Berkeley, Spring 2008, notes by
  T. Johnson-Freyd, p. 10.
-/

public section

noncomputable section

open MeasureTheory Polynomial
open scoped ComplexOrder

namespace TauCeti.Examples

/-- Complex polynomials equipped with coefficientwise conjugation and the supremum norm on
`[-1, 1]`. -/
structure UnitIntervalStarPoly : Type where
  /-- The underlying polynomial in `ℂ[X]`. -/
  toPoly : Polynomial ℂ

namespace UnitIntervalStarPoly

@[ext]
theorem ext {p q : UnitIntervalStarPoly} (h : p.toPoly = q.toPoly) : p = q := by
  cases p
  cases q
  congr

instance : Zero UnitIntervalStarPoly := ⟨⟨0⟩⟩
instance : One UnitIntervalStarPoly := ⟨⟨1⟩⟩
instance : Add UnitIntervalStarPoly := ⟨fun p q => ⟨p.toPoly + q.toPoly⟩⟩
instance : Neg UnitIntervalStarPoly := ⟨fun p => ⟨-p.toPoly⟩⟩
instance : Sub UnitIntervalStarPoly := ⟨fun p q => ⟨p.toPoly - q.toPoly⟩⟩
instance : Mul UnitIntervalStarPoly := ⟨fun p q => ⟨p.toPoly * q.toPoly⟩⟩
instance : NatCast UnitIntervalStarPoly := ⟨fun n => ⟨n⟩⟩
instance : IntCast UnitIntervalStarPoly := ⟨fun n => ⟨n⟩⟩
instance : SMul ℕ UnitIntervalStarPoly := ⟨fun n p => ⟨n • p.toPoly⟩⟩
instance : SMul ℤ UnitIntervalStarPoly := ⟨fun n p => ⟨n • p.toPoly⟩⟩
instance : SMul ℂ UnitIntervalStarPoly := ⟨fun c p => ⟨c • p.toPoly⟩⟩
instance : Pow UnitIntervalStarPoly ℕ := ⟨fun p n => ⟨p.toPoly ^ n⟩⟩
instance : Star UnitIntervalStarPoly := ⟨fun p => ⟨p.toPoly.map (starRingEnd ℂ)⟩⟩

@[simp] theorem toPoly_zero : (0 : UnitIntervalStarPoly).toPoly = 0 := rfl
@[simp] theorem toPoly_one : (1 : UnitIntervalStarPoly).toPoly = 1 := rfl
@[simp] theorem toPoly_add (p q : UnitIntervalStarPoly) :
    (p + q).toPoly = p.toPoly + q.toPoly := rfl
@[simp] theorem toPoly_neg (p : UnitIntervalStarPoly) : (-p).toPoly = -p.toPoly := rfl
@[simp] theorem toPoly_sub (p q : UnitIntervalStarPoly) :
    (p - q).toPoly = p.toPoly - q.toPoly := rfl
@[simp] theorem toPoly_mul (p q : UnitIntervalStarPoly) :
    (p * q).toPoly = p.toPoly * q.toPoly := rfl
@[simp] theorem toPoly_smul (c : ℂ) (p : UnitIntervalStarPoly) :
    (c • p).toPoly = c • p.toPoly := rfl
@[simp] theorem toPoly_pow (p : UnitIntervalStarPoly) (n : ℕ) :
    (p ^ n).toPoly = p.toPoly ^ n := rfl
@[simp] theorem toPoly_star (p : UnitIntervalStarPoly) :
    (star p).toPoly = p.toPoly.map (starRingEnd ℂ) := rfl

theorem toPoly_injective : Function.Injective toPoly :=
  fun _ _ h => ext h

instance : Ring UnitIntervalStarPoly :=
  toPoly_injective.ring toPoly toPoly_zero toPoly_one toPoly_add toPoly_mul toPoly_neg
    toPoly_sub (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

instance : Algebra ℂ UnitIntervalStarPoly where
  algebraMap :=
    { toFun c := ⟨Polynomial.C c⟩
      map_one' := ext Polynomial.C_1
      map_mul' _ _ := ext Polynomial.C_mul
      map_zero' := ext Polynomial.C_0
      map_add' _ _ := ext Polynomial.C_add }
  commutes' c p := ext (by dsimp; rw [mul_comm])
  smul_def' c p := ext (by simp [Polynomial.smul_eq_C_mul])

@[simp]
theorem toPoly_algebraMap (c : ℂ) : (algebraMap ℂ UnitIntervalStarPoly c).toPoly = Polynomial.C c :=
  rfl

/-- The coordinate generator `X` in `UnitIntervalStarPoly`. -/
@[expose] def X : UnitIntervalStarPoly := ⟨Polynomial.X⟩

@[simp] theorem toPoly_X : X.toPoly = Polynomial.X := rfl

/-- Coefficientwise complex conjugation on `UnitIntervalStarPoly`. -/
instance : StarRing UnitIntervalStarPoly where
  star_involutive p := ext (by
    have hcomp : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
      ext z; simp
    rw [toPoly_star, toPoly_star, Polynomial.map_map, hcomp, Polynomial.map_id])
  star_mul p q := ext (by simp [Polynomial.map_mul, mul_comm])
  star_add p q := ext (by simp [Polynomial.map_add])

instance : StarModule ℂ UnitIntervalStarPoly where
  star_smul c p := ext (by
    simp only [toPoly_star, toPoly_smul, Polynomial.smul_eq_C_mul, Polynomial.map_mul,
      Polynomial.map_C]
    rfl)

/-- Evaluation on `Set.Icc (-1 : ℝ) 1` as a complex-algebra homomorphism into continuous functions
on `[-1, 1]`. -/
def evalIccHom : UnitIntervalStarPoly →ₐ[ℂ] C(Set.Icc (-1 : ℝ) 1, ℂ) where
  toFun p := ⟨fun t => p.toPoly.eval (t.1 : ℂ),
    p.toPoly.continuous.comp (Complex.continuous_ofReal.comp continuous_subtype_val)⟩
  map_one' := by ext t; simp
  map_mul' p q := by ext t; simp
  map_zero' := by ext t; simp
  map_add' p q := by ext t; simp
  commutes' c := by ext t; simp

theorem evalIccHom_injective : Function.Injective evalIccHom := by
  intro p q hpq
  by_contra hne
  have hsub : p.toPoly - q.toPoly ≠ 0 := sub_ne_zero.mpr (fun h => hne (ext h))
  have hinf : (Set.Icc (-1 : ℝ) 1).Infinite := Set.Icc_infinite (by norm_num)
  obtain ⟨t, ht, hnt⟩ :=
    (hinf.image Complex.ofReal_injective.injOn).exists_notMem_finset
      (p.toPoly - q.toPoly).roots.toFinset
  rcases ht with ⟨x, hx, rfl⟩
  have hev : (p.toPoly - q.toPoly).eval (x : ℂ) = 0 := by
    have := congrArg (fun f : C(Set.Icc (-1 : ℝ) 1, ℂ) => f ⟨x, hx⟩) hpq
    simpa [evalIccHom, sub_eq_zero] using this
  exact hnt (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hsub).mpr hev))

noncomputable instance : NormedRing UnitIntervalStarPoly :=
  NormedRing.induced UnitIntervalStarPoly C(Set.Icc (-1 : ℝ) 1, ℂ) evalIccHom evalIccHom_injective

noncomputable instance : NormedAlgebra ℂ UnitIntervalStarPoly :=
  NormedAlgebra.induced ℂ UnitIntervalStarPoly C(Set.Icc (-1 : ℝ) 1, ℂ) evalIccHom

private theorem norm_def (p : UnitIntervalStarPoly) : ‖p‖ = ‖evalIccHom p‖ := rfl

private theorem eval_toPoly_star (p : UnitIntervalStarPoly) (t : ℝ) :
    (star p).toPoly.eval (t : ℂ) = star (p.toPoly.eval (t : ℂ)) := by
  rw [toPoly_star, Polynomial.eval_map, Complex.star_def]
  have h := (Polynomial.hom_eval₂ p.toPoly (RingHom.id ℂ) (starRingEnd ℂ) (t : ℂ)).symm
  rw [RingHom.comp_id, Complex.conj_ofReal] at h
  exact h

instance : NormedStarGroup UnitIntervalStarPoly where
  norm_star_le p := by
    rw [norm_def, norm_def]
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun t => ?_
    calc
      ‖evalIccHom (star p) t‖ = ‖star (p.toPoly.eval (t.1 : ℂ))‖ := by
        simpa [evalIccHom] using congrArg norm (eval_toPoly_star p t.1)
      _ = ‖evalIccHom p t‖ := norm_star _
      _ ≤ ‖evalIccHom p‖ := ContinuousMap.norm_coe_le_norm _ t

/-- Every monomial `X ^ n` has supremum norm `1` on `[-1, 1]`. -/
theorem norm_X_pow (n : ℕ) : ‖X ^ n‖ = 1 := by
  rw [norm_def]
  refine le_antisymm ?_ ?_
  · rw [ContinuousMap.norm_le _ zero_le_one]
    intro t
    have ht : ‖(t.1 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact t.2
    have hpow : ‖(t.1 : ℂ) ^ n‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) ht
    simpa [evalIccHom] using hpow
  · have h1 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hcoe := ContinuousMap.norm_coe_le_norm (evalIccHom (X ^ n)) ⟨1, h1⟩
    simpa [evalIccHom] using hcoe

/-- The real `n`-th Gaussian moment `∫ t, t ^ n * exp (-t ^ 2)`. -/
def gaussianMoment (n : ℕ) : ℝ :=
  ∫ t : ℝ, t ^ n * Real.exp (-t ^ 2)

/-- Every real monomial times `exp (-t ^ 2)` is integrable on `ℝ`. -/
private theorem integrable_pow_mul_exp_neg_sq (n : ℕ) :
    Integrable fun t : ℝ => t ^ n * Real.exp (-t ^ 2) := by
  have hg : Integrable fun t : ℝ => t ^ (n : ℝ) * Real.exp (-1 * t ^ 2) :=
    integrable_rpow_mul_exp_neg_mul_sq one_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
  refine (hg.norm.add hg.comp_neg.norm).mono' ?_ ?_
  · exact ((continuous_id.pow n).mul (Real.continuous_exp.comp
      (continuous_id.pow 2).neg)).aestronglyMeasurable
  · filter_upwards with t
    simp only [neg_mul, one_mul, Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _), neg_sq]
    rcases le_or_gt 0 t with ht | ht
    · have hle : |t| ^ n * Real.exp (-t ^ 2) = |t ^ (n : ℝ)| * Real.exp (-t ^ 2) := by
        rw [abs_of_nonneg ht, abs_of_nonneg (Real.rpow_nonneg ht _), Real.rpow_natCast]
      exact hle.le.trans (le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))
    · have ht' : 0 ≤ -t := neg_nonneg.mpr ht.le
      have hle : |t| ^ n * Real.exp (-t ^ 2) = |(-t) ^ (n : ℝ)| * Real.exp (-t ^ 2) := by
        rw [← abs_neg t, abs_of_nonneg ht', abs_of_nonneg (Real.rpow_nonneg ht' _),
          Real.rpow_natCast]
      exact hle.le.trans (le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))

/-- Every complex polynomial times `exp (-t ^ 2)` is integrable on `ℝ`. -/
private theorem integrable_eval_mul_exp_neg_sq (p : Polynomial ℂ) :
    Integrable fun t : ℝ => p.eval (t : ℂ) * Real.exp (-t ^ 2) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    ext t
    simp [add_mul]
  | monomial n c =>
    have hreal : Integrable fun t : ℝ => ((t ^ n * Real.exp (-t ^ 2) : ℝ) : ℂ) :=
      (integrable_pow_mul_exp_neg_sq n).ofReal
    simpa [Polynomial.eval_monomial, mul_assoc, ← Complex.ofReal_pow] using hreal.const_mul c

/-- Integration by parts recurrence for the Gaussian moments:
`gaussianMoment (k + 2) = ((k : ℝ) + 1) / 2 * gaussianMoment k`. -/
theorem gaussianMoment_add_two (k : ℕ) :
    gaussianMoment (k + 2) = ((k : ℝ) + 1) / 2 * gaussianMoment k := by
  let u : ℝ → ℝ := fun x => x ^ (k + 1)
  let u' : ℝ → ℝ := fun x => ((k : ℝ) + 1) * x ^ k
  let v : ℝ → ℝ := fun x => -(1 / 2 : ℝ) * Real.exp (-x ^ 2)
  let v' : ℝ → ℝ := fun x => x * Real.exp (-x ^ 2)
  have hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x := fun x _ => by
    simpa [u, u'] using hasDerivAt_pow (k + 1) x
  have hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x := fun x _ => by
    have hsq : HasDerivAt (fun t : ℝ => -t ^ 2) (-2 * x) x := by
      simpa [Pi.neg_def, two_mul] using (hasDerivAt_pow 2 x).neg
    have hexp := hsq.exp
    convert hexp.const_mul (-(1 / 2 : ℝ)) using 1
    simp only [v', neg_mul]
    ring
  have huv' : Integrable (u * v') := by
    refine (integrable_pow_mul_exp_neg_sq (k + 2)).congr (ae_of_all _ fun x => ?_)
    simp only [u, v', Pi.mul_apply]
    ring
  have hu'v : Integrable (u' * v) := by
    have h := (integrable_pow_mul_exp_neg_sq k).const_mul (((k : ℝ) + 1) * -(1 / 2 : ℝ))
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [u', v, Pi.mul_apply]
    ring
  have huv : Integrable (u * v) := by
    have h := (integrable_pow_mul_exp_neg_sq (k + 1)).const_mul (-(1 / 2 : ℝ))
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [u, v, Pi.mul_apply]
    ring
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable hu hv huv' hu'v huv
  have hL : ∫ x : ℝ, u x * v' x = gaussianMoment (k + 2) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [u, v']
    ring
  have hR : -∫ x : ℝ, u' x * v x = ((k : ℝ) + 1) / 2 * gaussianMoment k := by
    have heq : (fun x : ℝ => u' x * v x) =
        fun x : ℝ => -(((k : ℝ) + 1) / 2) * (x ^ k * Real.exp (-x ^ 2)) := by
      ext x
      simp only [u', v]
      ring
    rw [heq, integral_const_mul, neg_mul_eq_neg_mul, neg_neg]
    rfl
  rw [← hL, ← hR]
  exact hibp

/-- The zeroth Gaussian moment is `√π`. -/
theorem gaussianMoment_zero : gaussianMoment 0 = √Real.pi := by
  simpa [gaussianMoment] using integral_gaussian (1 : ℝ)

/-- The second Gaussian moment is `√π / 2`. -/
theorem gaussianMoment_two : gaussianMoment 2 = √Real.pi / 2 := by
  have h := gaussianMoment_add_two 0
  rw [zero_add, gaussianMoment_zero] at h
  linarith

/-- Every even Gaussian moment is strictly positive. -/
theorem gaussianMoment_two_mul_pos (n : ℕ) : 0 < gaussianMoment (2 * n) := by
  induction n with
  | zero =>
    rw [mul_zero, gaussianMoment_zero]
    exact Real.sqrt_pos.mpr Real.pi_pos
  | succ n ih =>
    rw [mul_add, mul_one, gaussianMoment_add_two (2 * n)]
    positivity

/-- Successive even Gaussian moments grow by `n + 1 / 2`. -/
theorem gaussianMoment_two_mul_succ (n : ℕ) :
    gaussianMoment (2 * (n + 1)) = ((n : ℝ) + 1 / 2) * gaussianMoment (2 * n) := by
  rw [mul_add, mul_one, gaussianMoment_add_two (2 * n)]
  congr 1
  push_cast
  ring

/-- The Gaussian integral functional `p ↦ ∫ t : ℝ, p(t) * exp (-t ^ 2)` on `UnitIntervalStarPoly`,
bundled as an algebraically positive functional. -/
def gaussianFunctional : StarPositiveFunctional UnitIntervalStarPoly where
  toFun p := ∫ t : ℝ, p.toPoly.eval (t : ℂ) * Real.exp (-t ^ 2)
  map_add' p q := by
    simp only [toPoly_add, Polynomial.eval_add, add_mul]
    exact integral_add (integrable_eval_mul_exp_neg_sq p.toPoly)
      (integrable_eval_mul_exp_neg_sq q.toPoly)
  map_smul' c p := by
    simp only [toPoly_smul, Polynomial.eval_smul, smul_eq_mul, mul_assoc, RingHom.id_apply]
    exact integral_const_mul c _
  square_nonneg p := by
    have hpt : (fun t : ℝ => (star p * p).toPoly.eval (t : ℂ) * Real.exp (-t ^ 2)) =
        fun t : ℝ => ((‖p.toPoly.eval (t : ℂ)‖ ^ 2 * Real.exp (-t ^ 2) : ℝ) : ℂ) := by
      ext t
      have hmul : (star p * p).toPoly.eval (t : ℂ) =
          star (p.toPoly.eval (t : ℂ)) * p.toPoly.eval (t : ℂ) := by
        rw [toPoly_mul, Polynomial.eval_mul, eval_toPoly_star]
      rw [hmul, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [hpt, integral_complex_ofReal, Complex.nonneg_iff]
    exact ⟨integral_nonneg fun t => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le, rfl⟩

/-- On monomials `X ^ n`, `gaussianFunctional (X ^ n)` is the `n`-th Gaussian moment. -/
theorem gaussianFunctional_X_pow (n : ℕ) :
    gaussianFunctional (X ^ n) = gaussianMoment n := by
  have hpt : (fun t : ℝ => (X ^ n).toPoly.eval (t : ℂ) * Real.exp (-t ^ 2)) =
      fun t : ℝ => ((t ^ n * Real.exp (-t ^ 2) : ℝ) : ℂ) := by
    ext t
    simp [toPoly_pow, toPoly_X, ← Complex.ofReal_pow]
  have hval : gaussianFunctional (X ^ n) =
      ∫ t : ℝ, (X ^ n).toPoly.eval (t : ℂ) * Real.exp (-t ^ 2) := rfl
  rw [hval, hpt, integral_complex_ofReal]
  rfl

/-- In the GNS space of `gaussianFunctional`, `‖[X ^ n]‖² = gaussianMoment (2 * n)`. -/
theorem norm_classMap_X_pow_sq (n : ℕ) :
    ‖gaussianFunctional.classMap (X ^ n)‖ ^ 2 = gaussianMoment (2 * n) := by
  rw [gaussianFunctional.norm_classMap_sq]
  have hstar : star (X ^ n) = X ^ n := by
    ext
    simp
  rw [hstar, ← pow_add, ← two_mul, gaussianFunctional_X_pow, Complex.ofReal_re]

/-- `‖X ^ 0‖_φ² = √π`. -/
theorem norm_classMap_X_zero_sq :
    ‖gaussianFunctional.classMap (X ^ 0)‖ ^ 2 = √Real.pi := by
  rw [norm_classMap_X_pow_sq 0, mul_zero, gaussianMoment_zero]

/-- `‖X ^ 1‖_φ² = √π / 2`. -/
theorem norm_classMap_X_one_sq :
    ‖gaussianFunctional.classMap (X ^ 1)‖ ^ 2 = √Real.pi / 2 := by
  rw [norm_classMap_X_pow_sq 1, mul_one, gaussianMoment_two]

/-- The successive GNS norm ratios of `X ^ n` are `n + 1 / 2`. -/
theorem norm_classMap_X_pow_succ_sq_div (n : ℕ) :
    ‖gaussianFunctional.classMap (X ^ (n + 1))‖ ^ 2 /
      ‖gaussianFunctional.classMap (X ^ n)‖ ^ 2 = (n : ℝ) + 1 / 2 := by
  rw [norm_classMap_X_pow_sq (n + 1), norm_classMap_X_pow_sq n, gaussianMoment_two_mul_succ,
    mul_div_cancel_right₀ _ (gaussianMoment_two_mul_pos n).ne']

/-- The Gaussian functional is unbounded on `UnitIntervalStarPoly` (showing completeness cannot be
dropped from automatic continuity of positive functionals). -/
theorem not_continuous_gaussianFunctional : ¬ Continuous gaussianFunctional := by
  intro hc
  obtain ⟨C, _, hC⟩ :=
    (⟨gaussianFunctional.toLinearMap, hc⟩ : UnitIntervalStarPoly →L[ℂ] ℂ).bound
  have hge : ∀ n : ℕ, 1 ≤ n → √Real.pi / 2 ≤ gaussianMoment (2 * n) := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      rcases n with _ | n
      · simpa using gaussianMoment_two.ge
      · rw [gaussianMoment_two_mul_succ]
        have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 / 2 := by push_cast; linarith
        calc
          √Real.pi / 2 ≤ gaussianMoment (2 * (n + 1)) := ih (by omega)
          _ = 1 * gaussianMoment (2 * (n + 1)) := (one_mul _).symm
          _ ≤ (((n + 1 : ℕ) : ℝ) + 1 / 2) * gaussianMoment (2 * (n + 1)) :=
            mul_le_mul_of_nonneg_right h1 (gaussianMoment_two_mul_pos _).le
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * C / √Real.pi)
  have h1N : 1 ≤ N + 1 := by omega
  have hbound : gaussianMoment (2 * ((N + 1) + 1)) ≤ C := by
    have hb := hC (X ^ (2 * ((N + 1) + 1)))
    rw [norm_X_pow, mul_one] at hb
    simpa only [ContinuousLinearMap.coe_mk', LinearMap.coe_toAddHom,
      StarPositiveFunctional.toLinearMap_apply, gaussianFunctional_X_pow,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (gaussianMoment_two_mul_pos _)] using hb
  have hposN : (0 : ℝ) ≤ (N + 1 : ℝ) + 1 / 2 := by positivity
  have hgrow : ((N + 1 : ℝ) + 1 / 2) * (√Real.pi / 2) ≤ gaussianMoment (2 * ((N + 1) + 1)) := by
    rw [gaussianMoment_two_mul_succ]
    simpa [Nat.cast_add, Nat.cast_one] using mul_le_mul_of_nonneg_left (hge (N + 1) h1N) hposN
  have hpi : 0 < √Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hlt : C < ((N + 1 : ℝ) + 1 / 2) * (√Real.pi / 2) := by
    have : 2 * C / √Real.pi < (N + 1 : ℝ) + 1 / 2 := hN.trans (by linarith)
    rw [div_lt_iff₀ hpi] at this
    linarith
  linarith

/-- Left multiplication by `X` is unbounded on the GNS pre-Hilbert space of `gaussianFunctional`
(showing completeness cannot be dropped from boundedness of the GNS representation). -/
theorem not_continuous_leftMul_X : ¬ Continuous (gaussianFunctional.leftMul X) := by
  intro hc
  obtain ⟨C, _, hC⟩ :=
    (⟨gaussianFunctional.leftMul X, hc⟩ : gaussianFunctional.GNS →L[ℂ] gaussianFunctional.GNS).bound
  obtain ⟨N, hN⟩ := exists_nat_gt (C ^ 2)
  have hle : ‖gaussianFunctional.leftMul X (gaussianFunctional.classMap (X ^ N))‖ ≤
      C * ‖gaussianFunctional.classMap (X ^ N)‖ := by
    simpa using hC (gaussianFunctional.classMap (X ^ N))
  have hsq : ‖gaussianFunctional.classMap (X ^ (N + 1))‖ ^ 2 ≤
      C ^ 2 * ‖gaussianFunctional.classMap (X ^ N)‖ ^ 2 := by
    have hmul : X * X ^ N = X ^ (N + 1) := by rw [pow_succ']
    have hact : gaussianFunctional.leftMul X (gaussianFunctional.classMap (X ^ N)) =
        gaussianFunctional.classMap (X ^ (N + 1)) := by
      rw [gaussianFunctional.leftMul_classMap, hmul]
    rw [hact] at hle
    calc
      ‖gaussianFunctional.classMap (X ^ (N + 1))‖ ^ 2
        ≤ (C * ‖gaussianFunctional.classMap (X ^ N)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = C ^ 2 * ‖gaussianFunctional.classMap (X ^ N)‖ ^ 2 := by ring
  rw [norm_classMap_X_pow_sq (N + 1), norm_classMap_X_pow_sq N,
    gaussianMoment_two_mul_succ] at hsq
  have hpos := gaussianMoment_two_mul_pos N
  have hle' : (N : ℝ) + 1 / 2 ≤ C ^ 2 := (mul_le_mul_iff_left₀ hpos).mp (by linarith)
  linarith

end UnitIntervalStarPoly

end TauCeti.Examples
