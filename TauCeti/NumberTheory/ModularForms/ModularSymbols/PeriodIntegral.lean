/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.NumberTheory.ModularForms.BinaryForms
public import TauCeti.NumberTheory.ModularForms.GeodesicIntegral
public import TauCeti.RingTheory.MvPolynomial.Homogeneous
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.ExpDecay
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The period integral of a cusp form against a binary form

Let `f` be a cusp form of weight `k = w + 2` on an arithmetic subgroup and `P` a binary form of
degree `w` with coefficients in a commutative semiring `R` mapping to `ℂ`. The **period integrand**
is the
one-form `f(z) P(z, 1) dz`, and its integrals

`∫_β^α f(z) P(z, 1) dz`

along the geodesics between cusps `α, β ∈ ℙ¹(ℚ)` are the **periods** of `f`. They are the values
of the period pairing between cusp forms and modular symbols, under which the symbol
`{α, β} ⊗ P` is sent to the integral above; the pairing itself, its descent to the coinvariants
`𝕄_w(Γ; R)` and its Hecke equivariance are built on the results of this file.

Two facts about the integrand are established. First, its **transformation law** under a matrix
`g ∈ GL(2, ℚ)` of positive determinant: substituting `z ↦ g • z` in `f(z) P(z, 1) dz` produces
`(det g)⁻ʷ · (f ∣[k] g)(z) · P(az + b, cz + d) dz`, and for `γ ∈ SL(2, ℤ)` this is the one-form
of `f ∣[k] γ` against `P ∣ γ`, the right action of `TauCeti.binaryFormRep`. This is what makes
the periods compatible with the relation `{γα, γβ} ⊗ P = {α, β} ⊗ (P ∣ γ)` defining modular
symbols. Second, **absolute convergence**: both endpoints of the geodesic are cusps, and the
integrand is integrable along the whole geodesic. Moving each endpoint to `i∞` reduces this to
the exponential decay of a cusp form there, which beats the polynomial growth of `P`. Only the
`SL(2, ℤ)` form of the transformation law, stated through `TauCeti.binaryFormRep`, needs `R` to be
a ring.

## Main definitions

* `TauCeti.ModularSymbols.periodIntegrand f P`: the function `z ↦ f(z) · P(z, 1)` on `ℍ`.

## Main results

* `TauCeti.ModularSymbols.periodIntegrand_add_left`,
  `TauCeti.ModularSymbols.periodIntegrand_smul_left`: the integrand is `ℂ`-linear in the
  function, so that the periods define a linear map on cusp forms.
* `TauCeti.ModularSymbols.periodIntegrand_add_right`,
  `TauCeti.ModularSymbols.periodIntegrand_smul_right`: the integrand is `R`-linear in the binary
  form, so that the periods extend linearly to the module of modular symbols.
* `TauCeti.ModularSymbols.periodIntegrand_slash_apply`: the weight-`2` slash of the integrand by a
  rational matrix `g` of positive determinant is
  `(det g)⁻ʷ · (f ∣[k] g)(τ) · P(aτ + b, cτ + d)`.
* `TauCeti.ModularSymbols.mdifferentiable_periodIntegrand`: the integrand of a holomorphic `f` is
  holomorphic.
* `TauCeti.ModularSymbols.integrableOn_resToImagAxis_periodIntegrand_slash`: **absolute
  convergence** of the period integral of a cusp form of weight `w + 2` against a binary form of
  degree `w` along the geodesic between any two distinct cusps.
* `TauCeti.ModularSymbols.periodIntegrand_slash_mapGL`: for `γ ∈ SL(2, ℤ)`, slashing the
  integrand of `f` against `P` by `γ` gives the integrand of `f ∣[k] γ` against `P ∣ γ`.
* `TauCeti.ModularSymbols.geodesicIntegral_mapGL_mul_periodIntegrand`: the transformation law
  `∫_{γβ}^{γα} f(z) P(z, 1) dz = ∫_β^α (f ∣[k] γ)(z) (P ∣ γ)(z, 1) dz` for `γ ∈ SL(2, ℤ)`, and
  `TauCeti.ModularSymbols.geodesicIntegral_mapGL_mul_periodIntegrand_of_mem`: its form for `γ`
  in the level of `f`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §8.2, (8.2.15)–(8.2.16).
* Y. I. Manin, *Parabolic points and zeta functions of modular curves*, Izv. Akad. Nauk SSSR
  Ser. Mat. **36** (1972), 19–66, §1.
-/

public section

open Asymptotics Complex Filter Matrix Matrix.SpecialLinearGroup MeasureTheory ModularGroup
  MulOpposite MvPolynomial Set
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm Pointwise

namespace TauCeti.ModularSymbols

variable {R : Type*} {w : ℕ}

section CommSemiring

variable [CommSemiring R] [Algebra R ℂ]

/-- The **period integrand** `z ↦ f(z) · P(z, 1)` of a function `f : ℍ → ℂ` against a binary form
`P` of degree `w`: the one-form `f(z) P(z, 1) dz` whose integrals along geodesics between cusps
are the periods of `f`. -/
noncomputable def periodIntegrand (f : ℍ → ℂ) (P : homogeneousSubmodule (Fin 2) R w) : ℍ → ℂ :=
  fun z ↦ f z * aeval ![(z : ℂ), 1] (P : MvPolynomial (Fin 2) R)

@[simp]
theorem periodIntegrand_apply (f : ℍ → ℂ) (P : homogeneousSubmodule (Fin 2) R w) (z : ℍ) :
    periodIntegrand f P z = f z * aeval ![(z : ℂ), 1] (P : MvPolynomial (Fin 2) R) := by
  rw [periodIntegrand]

/-- The period integrand of the zero function vanishes. -/
@[simp]
theorem periodIntegrand_zero_left (P : homogeneousSubmodule (Fin 2) R w) :
    periodIntegrand (0 : ℍ → ℂ) P = 0 := by
  funext z
  simp

/-- The period integrand is additive in the function. -/
@[simp]
theorem periodIntegrand_add_left (f g : ℍ → ℂ) (P : homogeneousSubmodule (Fin 2) R w) :
    periodIntegrand (f + g) P = periodIntegrand f P + periodIntegrand g P := by
  funext z
  simp [add_mul]

/-- The period integrand is `ℂ`-linear in the function. -/
@[simp]
theorem periodIntegrand_smul_left (c : ℂ) (f : ℍ → ℂ) (P : homogeneousSubmodule (Fin 2) R w) :
    periodIntegrand (c • f) P = c • periodIntegrand f P := by
  funext z
  simp [mul_assoc]

/-- The period integrand against the zero form vanishes. -/
@[simp]
theorem periodIntegrand_zero_right (f : ℍ → ℂ) :
    periodIntegrand f (0 : homogeneousSubmodule (Fin 2) R w) = 0 := by
  funext z
  simp

/-- The period integrand is additive in the binary form. -/
@[simp]
theorem periodIntegrand_add_right (f : ℍ → ℂ) (P Q : homogeneousSubmodule (Fin 2) R w) :
    periodIntegrand f (P + Q) = periodIntegrand f P + periodIntegrand f Q := by
  funext z
  simp [mul_add]

/-- The period integrand is `R`-linear in the binary form. -/
@[simp]
theorem periodIntegrand_smul_right (f : ℍ → ℂ) (r : R) (P : homogeneousSubmodule (Fin 2) R w) :
    periodIntegrand f (r • P) = r • periodIntegrand f P := by
  funext z
  simp [Algebra.smul_def, mul_left_comm]

/-! ### The transformation law -/

/-- **The transformation law of the period integrand.** Slashing `f(z) P(z, 1)` in weight `2` by
a rational matrix `g` of positive determinant gives `(det g)⁻ʷ · (f ∣[k] g)(τ) · P(aτ + b, cτ + d)`,
where `k = w + 2` and `aτ + b`, `cτ + d` are the numerator and denominator of the Möbius action
of `g`: the factors `(cτ + d)` of the two slashes combine with the homogeneity of `P` in degree
`w`. -/
theorem periodIntegrand_slash_apply {k : ℤ} (hk : k = w + 2) (f : ℍ → ℂ)
    (P : homogeneousSubmodule (Fin 2) R w) {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) (τ : ℍ) :
    (periodIntegrand f P ∣[(2 : ℤ)] g) τ =
      ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℂ) ^ (-(w : ℤ)) * (f ∣[k] g) τ *
        aeval ![num (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) τ,
          denom (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) τ]
          (P : MvPolynomial (Fin 2) R) := by
  subst hk
  set g' := Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g with hg'
  have hdet' : (g' : Matrix (Fin 2) (Fin 2) ℝ).det = ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℝ) := by
    rw [hg', Matrix.GeneralLinearGroup.val_map_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      eq_ratCast]
  have hdetpos : 0 < (g'.det : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hdet']
    exact_mod_cast hg
  have hden : denom g' τ ≠ 0 := denom_ne_zero g' τ
  have hD : ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  -- homogeneity: `P(aτ + b, cτ + d) = (cτ + d) ^ w · P(g • τ, 1)`
  have hP : aeval ![num g' τ, denom g' τ] (P : MvPolynomial (Fin 2) R) =
      denom g' τ ^ w * aeval ![((g' • τ : ℍ) : ℂ), 1] (P : MvPolynomial (Fin 2) R) := by
    have h := ((mem_homogeneousSubmodule w _).mp P.2).aeval_smul ![((g' • τ : ℍ) : ℂ), 1]
      (denom g' τ)
    rw [smul_eq_mul] at h
    rw [← h]
    congr 1
    ext i
    fin_cases i
    · simp [coe_smul_of_det_pos hdetpos]
      field_simp
    · simp
  rw [ModularForm.rat_slash_apply_of_det_pos _ hg, ModularForm.rat_slash_apply_of_det_pos _ hg,
    periodIntegrand_apply, ← hg', hP]
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  have hcast : ((((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℝ)) : ℂ) =
      ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℂ) := by norm_cast
  rw [hdet', abs_of_pos (by exact_mod_cast hg), hcast]
  -- the determinant and denominator exponents combine as `-w + (w + 1) = 1` and
  -- `-(w + 2) + w = -2`
  have e1 : ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℂ) ^ (-(w : ℤ)) *
      ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℂ) ^ ((w : ℤ) + 2 - 1) =
        ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℂ) ^ ((2 : ℤ) - 1) := by
    rw [← zpow_add₀ hD]
    congr 1
    ring
  have e2 : denom g' τ ^ (-((w : ℤ) + 2)) * denom g' τ ^ w = denom g' τ ^ (-(2 : ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ hden]
    congr 1
    ring
  calc _ = (((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℂ) ^ (-(w : ℤ)) *
        ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℂ) ^ ((w : ℤ) + 2 - 1)) *
        (denom g' τ ^ (-((w : ℤ) + 2)) * denom g' τ ^ w) * f (g' • τ) *
        aeval ![((g' • τ : ℍ) : ℂ), 1] (P : MvPolynomial (Fin 2) R) := by
        rw [e1, e2]
        ring
    _ = _ := by ring

/-! ### Absolute convergence -/

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

/-- The period integrand of a holomorphic function is holomorphic. -/
theorem mdifferentiable_periodIntegrand {f : ℍ → ℂ} (hf : MDiff f)
    (P : homogeneousSubmodule (Fin 2) R w) : MDiff (periodIntegrand f P) :=
  hf.mul (MvPolynomial.mdifferentiable_aeval_coe _)

/-- **Convergence at `i∞`**: for a cusp form `f` of weight `w + 2` and a binary form `P` of degree
`w`, the slashed integrand `(f(z) P(z, 1)) ∣[2] g` is integrable along the imaginary axis away
from `0`, by exponential decay of `f ∣[k] g` against polynomial growth of `P`. -/
theorem integrableOn_resToImagAxis_periodIntegrand_slash_Ici [Γ.IsArithmetic] [CuspFormClass F Γ k]
    (f : F) (hk : k = w + 2) (P : homogeneousSubmodule (Fin 2) R w) {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
    IntegrableOn (resToImagAxis (periodIntegrand f P ∣[(2 : ℤ)] g)) (Ici 1) := by
  set g' := Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g with hg'
  -- continuity along the axis, from holomorphy
  have hmd : MDiff (periodIntegrand f P ∣[(2 : ℤ)] g) := by
    rw [ModularForm.rat_slash]
    exact (mdifferentiable_periodIntegrand (ModularFormClass.holo f) P).slash 2 g'
  have hcont : ContinuousOn (resToImagAxis (periodIntegrand f P ∣[(2 : ℤ)] g)) (Ici 1) :=
    fun t ht ↦ (differentiableAt_resToImagAxis_of_mDiffAt _ (zero_lt_one.trans_le ht)
      (hmd _)).continuousAt.continuousWithinAt
  -- exponential decay of `f ∣[k] g`, polynomial growth of `P`
  obtain ⟨c, hc, hdecay⟩ := exists_isBigO_resToImagAxis_rat_slash_exp f g
  have hpoly := isBigO_aeval_num_denom ((mem_homogeneousSubmodule w _).mp P.2).totalDegree_le g'
  have hO : resToImagAxis (periodIntegrand f P ∣[(2 : ℤ)] g) =O[atTop]
      fun t ↦ Real.exp (-(c / 2) * t) := by
    have h1 : resToImagAxis (periodIntegrand f P ∣[(2 : ℤ)] g) =ᶠ[atTop]
        fun t ↦ ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℂ) ^ (-(w : ℤ)) *
          (resToImagAxis (f ∣[k] g) t *
            aeval ![num g' (Complex.I * t), denom g' (Complex.I * t)]
              (P : MvPolynomial (Fin 2) R)) := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [resToImagAxis_of_pos _ ht, resToImagAxis_of_pos _ ht,
        periodIntegrand_slash_apply hk f P hg, mul_assoc, ← hg']
    have h2 : (fun t : ℝ ↦ Real.exp (-c * t) * t ^ w) =O[atTop]
        fun t ↦ Real.exp (-(c / 2) * t) := by
      refine ((isBigO_refl (fun t : ℝ ↦ Real.exp (-c * t)) atTop).mul
        (isLittleO_pow_exp_pos_mul_atTop w (half_pos hc)).isBigO).congr_right fun t ↦ ?_
      rw [← Real.exp_add]
      ring_nf
    exact ((hdecay.mul hpoly).const_mul_left _).congr' h1.symm EventuallyEq.rfl |>.trans h2
  exact LocallyIntegrableOn.integrableOn_of_isBigO_atTop
    (hcont.locallyIntegrableOn measurableSet_Ici) hO
    ⟨Ioi 0, Ioi_mem_atTop 0, exp_neg_integrableOn_Ioi 0 (half_pos hc)⟩

/-- **Absolute convergence of the period integral.** For a cusp form `f` of weight `w + 2` on an
arithmetic subgroup, a binary form `P` of degree `w`, and a rational matrix `g` of positive
determinant, the integrand of `∫_{g • 0}^{g • ∞} f(z) P(z, 1) dz` is integrable along the whole
geodesic between the two distinct cusps `g • 0` and `g • ∞`: each endpoint is moved to `i∞`, the
finite one by the reflection `S`. -/
theorem integrableOn_resToImagAxis_periodIntegrand_slash [Γ.IsArithmetic] [CuspFormClass F Γ k]
    (f : F) (hk : k = w + 2) (P : homogeneousSubmodule (Fin 2) R w) {g : GL (Fin 2) ℚ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) :
    IntegrableOn (resToImagAxis (periodIntegrand f P ∣[(2 : ℤ)] g)) (Ioi 0) := by
  refine integrableOn_resToImagAxis_Ioi_of_slash_S
    (integrableOn_resToImagAxis_periodIntegrand_slash_Ici f hk P hg) ?_
  have hS : ((mapGL ℚ S : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
  have hgS : 0 < ((g * mapGL ℚ S : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [Units.val_mul, Matrix.det_mul, hS, mul_one]
    exact hg
  have := integrableOn_resToImagAxis_periodIntegrand_slash_Ici f hk P hgS
  rwa [SlashAction.slash_mul, ModularForm.rat_slash_mapGL,
    ← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash] at this

end CommSemiring

/-! ### The transformation law under `SL(2, ℤ)` -/

variable [CommRing R] [Algebra R ℂ] {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

/-- **The transformation law under `SL(2, ℤ)`**: slashing the integrand of `f` against `P` by
`γ ∈ SL(2, ℤ)` gives the integrand of `f ∣[k] γ` against `P ∣ γ`, the right action of `γ` on
binary forms (`TauCeti.binaryFormRep`). -/
theorem periodIntegrand_slash_mapGL {k : ℤ} (hk : k = w + 2) (f : ℍ → ℂ)
    (P : homogeneousSubmodule (Fin 2) R w) (γ : SL(2, ℤ)) :
    periodIntegrand f P ∣[(2 : ℤ)] (mapGL ℚ γ) =
      periodIntegrand (f ∣[k] γ) (binaryFormRep R w (op (γ : Matrix (Fin 2) (Fin 2) ℤ)) P) := by
  have hdet : ((mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
  funext τ
  rw [periodIntegrand_slash_apply hk f P (by rw [hdet]; exact one_pos) τ, periodIntegrand_apply,
    hdet, ModularForm.rat_slash_mapGL, ← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
    ← ModularForm.SL_slash, map_mapGL, coe_binaryFormRep_apply, aeval_linearSubst]
  push_cast
  rw [one_zpow, one_mul]
  congr 2
  ext i
  fin_cases i <;> simp [num, denom, mapGL_coe_matrix, Matrix.map_apply]

/-- **The transformation law of the periods under `SL(2, ℤ)`**:
`∫_{γ g • 0}^{γ g • ∞} f(z) P(z, 1) dz = ∫_{g • 0}^{g • ∞} (f ∣[k] γ)(z) (P ∣ γ)(z, 1) dz`,
the substitution `z ↦ γ • z` in the period integral. The identity holds for every rational `g`
(it is `Matrix.GeneralLinearGroup.geodesicIntegral_mul` and the transformation law of the
integrand); both sides are period integrals along geodesics when `0 < det g`. -/
theorem geodesicIntegral_mapGL_mul_periodIntegrand {k : ℤ} (hk : k = w + 2) (f : ℍ → ℂ)
    (P : homogeneousSubmodule (Fin 2) R w) (γ : SL(2, ℤ)) (g : GL (Fin 2) ℚ) :
    (mapGL ℚ γ * g).geodesicIntegral (periodIntegrand f P) =
      g.geodesicIntegral
        (periodIntegrand (f ∣[k] γ) (binaryFormRep R w (op (γ : Matrix (Fin 2) (Fin 2) ℤ)) P)) := by
  rw [Matrix.GeneralLinearGroup.geodesicIntegral_mul, periodIntegrand_slash_mapGL hk]

/-- **The periods of a form respect the modular-symbol relation**: for `γ` in the level `Γ` of a
slash-invariant `f`,
`∫_{γ g • 0}^{γ g • ∞} f(z) P(z, 1) dz = ∫_{g • 0}^{g • ∞} f(z) (P ∣ γ)(z, 1) dz`, the analytic
counterpart of `{γα, γβ} ⊗ P = {α, β} ⊗ (P ∣ γ)` in `𝕄_w(Γ; R)`. As for
`geodesicIntegral_mapGL_mul_periodIntegrand`, the identity holds for every rational `g`, and both
sides are period integrals along geodesics when `0 < det g`. -/
theorem geodesicIntegral_mapGL_mul_periodIntegrand_of_mem {Γ : Subgroup SL(2, ℤ)}
    [SlashInvariantFormClass F (Γ.map (mapGL ℝ)) k] (f : F) (hk : k = w + 2)
    (P : homogeneousSubmodule (Fin 2) R w) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (g : GL (Fin 2) ℚ) :
    (mapGL ℚ γ * g).geodesicIntegral (periodIntegrand f P) =
      g.geodesicIntegral
        (periodIntegrand f (binaryFormRep R w (op (γ : Matrix (Fin 2) (Fin 2) ℤ)) P)) := by
  rw [geodesicIntegral_mapGL_mul_periodIntegrand hk, ModularForm.SL_slash,
    TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)]

end TauCeti.ModularSymbols

end
