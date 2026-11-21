/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.Algebra.PontryaginDual
public import TauCeti.MeasureTheory.Function.Lp.PiLp

import Mathlib.Analysis.Convolution
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.MeasureTheory.Integral.Bochner.Star
import TauCeti.Topology.Circle.AddCircle

/-!
# The continuous characters of the circle are the Fourier monomials

Mathlib's `fourier n : C(AddCircle T, ℂ)` is developed as a family of `L²` monomials: the lemmas
about it record how it behaves in the *index* `n` (`fourier_add`, `fourier_neg`) and what it
contributes to the Fourier basis. Read the other way, as a family of *characters* of the group
`AddCircle T` indexed by `n`, the two facts a representation-theoretic consumer needs are that the
family is **faithful** (distinct indices give distinct characters, so the corresponding
one-dimensional representations are pairwise inequivalent) and that it is **exhaustive** (there are
no other continuous characters). This file proves both, and packages them as an isomorphism of
groups between `Multiplicative ℤ` and the Pontryagin dual of the circle group.

Both halves need the period to be nondegenerate, and they need it to differing extents.
Faithfulness holds as soon as `T ≠ 0`, and that hypothesis is carried explicitly. Exhaustiveness
rests on Mathlib's Fourier analysis on `AddCircle T`, which is set up under `[Fact (0 < T)]`, so
that instance is assumed for the classification results and for the isomorphism of groups.

Faithfulness is elementary: two monomials already differ at the point `T / 2 / (m - n)`.
Exhaustiveness is where analysis enters. A continuous character `χ` is in particular a nonzero
continuous function, so some Fourier coefficient `fourierCoeff χ n` is nonzero — that is Mathlib's
`fourierBasis`, a Hilbert basis of `L²`, together with the injectivity of the map
`C(AddCircle T, ℂ) → L²`. Translating that coefficient by `y` and using that both `fourier (-n)`
and `χ` turn a sum into a product rewrites `fourierCoeff χ n` as
`fourier (-n) y * χ y * fourierCoeff χ n`, whence `fourier (-n) y * χ y = 1`, and therefore
`χ y = fourier n y`.

Nothing here assumes that `χ` takes values in the unit circle: on a compact group that is
automatic, and here it comes out as a corollary, since a continuous character *is* a Fourier
monomial.

`TauCeti/RepresentationTheory/Compact/Circle.lean` reads this classification for the circle group
`Multiplicative (AddCircle T)` with `[Fact (0 < T)]`, where the group is compact and the statement
becomes that the continuous representations of the circle on `ℂ` are exactly the Fourier ones.

## Main definitions

* `TauCeti.fourierAddChar`: the `n`-th Fourier monomial as a bundled additive character
  `AddChar (AddCircle T) ℂ`.
* `TauCeti.fourierPontryaginDual`: the `n`-th Fourier monomial as an element of the Pontryagin dual
  `PontryaginDual (Multiplicative (AddCircle T))` of the circle group, i.e. as a continuous
  homomorphism to the unit circle.
* `TauCeti.fourierPontryaginDualEquiv`: the resulting isomorphism of groups between
  `Multiplicative ℤ` and that Pontryagin dual.

## Main statements

* `TauCeti.fourier_injective`: `n ↦ fourier n` is injective, so distinct indices give distinct
  characters.
* `TauCeti.fourier_apply_ne_zero`, `TauCeti.fourier_neg_mul_fourier`: the monomials vanish
  nowhere, and `fourier (-n)` is the pointwise inverse of `fourier n`.
* `TauCeti.fourier_one_coe_apply`, `TauCeti.fourier_neg_one_coe_apply`: the first harmonics
  `fourier (±1)` evaluated at a real point, in terms of the cosine and sine of `2π t / T`.
* `TauCeti.fourier_apply_eq_coe_toCircle_zpow`: `fourier n` is the `n`-th power of the point of
  the unit circle, and `TauCeti.coe_toCircle_coe_eq_circleMap` identifies that point with
  `circleMap 0 1 θ` for the period `2π`.
* `TauCeti.exists_polynomial_of_mem_span_fourier`: every trigonometric polynomial on `AddCircle T`
  factors as `fourier (-N) x * P.eval (fourier 1 x)`.
* `ContinuousMap.eq_zero_of_forall_fourierCoeff_eq_zero`: a continuous function on the circle all
  of whose Fourier coefficients vanish is the zero function.
* `AddChar.exists_fourierAddChar_eq`: **every continuous additive character of the circle is a
  Fourier monomial.**
* `AddChar.norm_apply_eq_one_of_continuous`: consequently a continuous additive character of the
  circle takes values of modulus one.
* `ContinuousMonoidHom.existsUnique_circle_eq_zpow`: every continuous character of the
  multiplicative unit circle is a unique integer power.
* `TauCeti.norm_fourierLp`, `TauCeti.fourierLp_smul_fourierLp`, `TauCeti.star_fourierLp`: norm,
  multiplication, and conjugation of `Lᵖ` Fourier monomials.
* `TauCeti.fourierCoeff_smul_fourierBasis`: multiplying the `L²` Fourier mode `e_m` by an
  essentially bounded function `a` shifts the Fourier coefficients of `a` by `m`.
* `TauCeti.fourierCoeff_fourierLp_smul`: multiplying an `Lᵖ` function by the monomial `e_n`
  shifts its Fourier coefficients by `n`.
* `TauCeti.fourierCoeff_star`, `MeasureTheory.Lp.fourierCoeff_star`: in a complex normed star
  module, the Fourier coefficients of `star f` are `star` of the reflected coefficients of `f`.
* `TauCeti.fourierCoeff_fourierLp`: the Fourier coefficients of the `Lᵖ` monomial `e_n` are `1`
  at `n` and `0` elsewhere.
* `TauCeti.fourierCoeff_sub`: the Fourier coefficients of a difference of integrable functions.
* `TauCeti.fourierCoeff_fourier_mul_conj`: twisting by `fourier k` and conjugating sends the
  `n`-th Fourier coefficient to the conjugate of the `(k - n)`-th one.
* `TauCeti.fourierCoeff_comp_neg`: circle reflection reverses Fourier indices, including
  the native `Lᵖ` pullback form `MeasureTheory.Lp.fourierCoeff_compMeasurePreserving_neg`.
* `TauCeti.fourierCoeff_comp_add_right`: translation by `θ` multiplies the `n`-th Fourier
  coefficient by `fourier n θ`; at the half period `fourier n (T / 2) = (-1) ^ n`
  (`TauCeti.fourier_coe_half_period`).
* `ContinuousLinearMap.fourierCoeff_comp`, `ContinuousLinearMap.fourierCoeff_compLpL`: Fourier
  coefficients commute with continuous linear maps on integrable and `Lᵖ` functions.
* `MeasureTheory.Integrable.fourierCoeff_piLp_apply`, `MeasureTheory.Lp.fourierCoeff_piLp_apply`:
  the `i`-th coordinate of the `n`-th Fourier coefficient of an integrable or `Lᵖ` `PiLp`-valued
  circle function is the `n`-th Fourier coefficient of its `i`-th coordinate.
* `Function.Periodic.intervalIntegrable_fourier_smul_lift`,
  `ContinuousLinearMap.integral_smul_sub_haarAddCircle_comp`,
  `TauCeti.integral_fourier_smul_sub_eq`, `Continuous.exists_continuousMap_integral_smul_sub_lt`,
  `Continuous.exists_mem_span_fourier_integral_smul_sub_lt`: periodic lift integrability,
  convolution commutation with CLMs, and uniform approximation on `AddCircle T`.

## Tags

Fourier, additive circle, character, Pontryagin dual
-/

public section

open MeasureTheory AddCircle
open scoped ENNReal

variable {T : ℝ}

namespace TauCeti

/-- **Distinct indices give distinct Fourier monomials.** At the point `T / 2 / (m - n)` the two
monomials `fourier m` and `fourier n` differ by `Complex.exp (π * I) = -1`, so they are already
different there. Only `T ≠ 0` is needed: for `T = 0` the circle is trivial and every monomial is
the constant `1`. -/
theorem fourier_injective (hT : T ≠ 0) : Function.Injective (fourier (T := T)) := by
  intro m n hmn
  by_contra hne
  have hd : ((m : ℂ) - n) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
  set y : ℝ := T / 2 / ((m : ℝ) - n) with hy
  have hx : fourier m (y : AddCircle T) = fourier n (y : AddCircle T) := by rw [hmn]
  rw [fourier_coe_apply, fourier_coe_apply] at hx
  have he : 2 * (Real.pi : ℂ) * Complex.I * m * y / T
      - 2 * (Real.pi : ℂ) * Complex.I * n * y / T = (Real.pi : ℂ) * Complex.I := by
    rw [hy]
    push_cast
    field_simp
  have hcontra : (-1 : ℂ) = 1 := by
    calc (-1 : ℂ) = Complex.exp ((Real.pi : ℂ) * Complex.I) := Complex.exp_pi_mul_I.symm
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * m * y / T)
            / Complex.exp (2 * (Real.pi : ℂ) * Complex.I * n * y / T) := by
          rw [← Complex.exp_sub, he]
      _ = 1 := by rw [hx, div_self (Complex.exp_ne_zero _)]
  norm_num at hcontra

/-- The Fourier monomial of frequency `1` in terms of the cosine and sine of `2π t / T`. -/
theorem fourier_one_coe_apply (t : ℝ) :
    fourier 1 (t : AddCircle T) =
      Real.cos (2 * Real.pi * t / T) + Real.sin (2 * Real.pi * t / T) * Complex.I := by
  have : 2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * t / (T : ℂ) =
      ((2 * Real.pi * t / T : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [fourier_coe_apply, this, Complex.exp_mul_I]
  simp

/-- The Fourier monomial of frequency `-1` in terms of the cosine and sine of `2π t / T`. -/
theorem fourier_neg_one_coe_apply (t : ℝ) :
    fourier (-1) (t : AddCircle T) =
      Real.cos (2 * Real.pi * t / T) - Real.sin (2 * Real.pi * t / T) * Complex.I := by
  have : 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * t / (T : ℂ) =
      ((-(2 * Real.pi * t / T)) : ℝ) * Complex.I := by
    push_cast
    ring
  rw [fourier_coe_apply, this, Complex.exp_mul_I]
  simp [sub_eq_add_neg]

/-- At the half period `T / 2` the Fourier monomial of frequency `n` is `(-1) ^ n`. -/
theorem fourier_coe_half_period (hT : T ≠ 0) (n : ℤ) :
    fourier n ((T / 2 : ℝ) : AddCircle T) = (-1) ^ n := by
  rw [fourier_apply, toCircle_zsmul, toCircle_half_period hT, Circle.coe_zpow, Circle.coe_neg,
    Circle.coe_one]

/-- The Fourier monomials take values in the unit circle, so they vanish nowhere. -/
theorem fourier_apply_ne_zero (n : ℤ) (x : AddCircle T) : fourier n x ≠ 0 := by
  rw [fourier_apply]
  exact Circle.coe_ne_zero _

/-- The monomial `fourier (-n)` is the pointwise inverse of `fourier n`. -/
theorem fourier_neg_mul_fourier (n : ℤ) (x : AddCircle T) : fourier (-n) x * fourier n x = 1 := by
  rw [← fourier_add, neg_add_cancel, fourier_zero]

/-- The Fourier monomial `fourier n` is the `n`-th power of the point `toCircle x` of the unit
circle. -/
theorem fourier_apply_eq_coe_toCircle_zpow (n : ℤ) (x : AddCircle T) :
    fourier n x = (toCircle x : ℂ) ^ n := by
  rw [fourier_apply, toCircle_zsmul, Circle.coe_zpow]

/-- For the period `2π`, the point `toCircle θ` of the unit circle is `e^{iθ} = circleMap 0 1 θ`. -/
theorem coe_toCircle_coe_eq_circleMap (θ : ℝ) :
    (toCircle (θ : AddCircle (2 * Real.pi)) : ℂ) = circleMap 0 1 θ := by
  rw [toCircle_apply_mk, Circle.coe_exp, circleMap, div_self Real.two_pi_pos.ne']
  simp

/-- **The `n`-th Fourier monomial as a bundled additive character of the circle.** It is Mathlib's
`AddCircle.toCircle_addChar` precomposed with multiplication by `n` and postcomposed with the
inclusion of the unit circle into `ℂ`; `TauCeti.fourierAddChar_apply` identifies its value with
`fourier n`. -/
noncomputable def fourierAddChar (n : ℤ) : AddChar (AddCircle T) ℂ :=
  Circle.coeHom.compAddChar (toCircle_addChar.compAddMonoidHom (zsmulAddGroupHom n))

@[simp]
theorem fourierAddChar_apply (n : ℤ) (x : AddCircle T) :
    fourierAddChar n x = fourier n x := by
  rw [fourierAddChar, MonoidHom.compAddChar_apply, Function.comp_apply,
    AddChar.compAddMonoidHom_apply, toCircle_addChar, AddChar.coe_mk, fourier_apply]
  rfl

theorem continuous_fourierAddChar (n : ℤ) : Continuous (fourierAddChar (T := T) n) :=
  (fourier n).continuous.congr fun x => (fourierAddChar_apply n x).symm

/-- **The `n`-th Fourier monomial as an element of the Pontryagin dual of the circle group.** The
circle group is `Multiplicative (AddCircle T)`, and this character sends `x` to
`AddCircle.toCircle (n • x)`, the value of `fourier n` read in the unit circle rather than in `ℂ`;
`TauCeti.coe_fourierPontryaginDual` identifies its value with `fourier n`. -/
noncomputable def fourierPontryaginDual (n : ℤ) :
    PontryaginDual (Multiplicative (AddCircle T)) where
  toFun x := toCircle (n • Multiplicative.toAdd x)
  map_one' := by simp
  map_mul' x y := by rw [toAdd_mul, smul_add, toCircle_add]
  continuous_toFun := (continuous_toCircle.comp (continuous_zsmul n) :
    Continuous fun x : AddCircle T => toCircle (n • x))

@[simp]
theorem coe_fourierPontryaginDual (n : ℤ) (x : Multiplicative (AddCircle T)) :
    (fourierPontryaginDual n x : ℂ) = fourier n (Multiplicative.toAdd x) := by
  rw [fourier_apply]
  rfl

/-- Distinct indices give distinct elements of the Pontryagin dual: `TauCeti.fourier_injective`
again. -/
theorem fourierPontryaginDual_injective (hT : T ≠ 0) :
    Function.Injective (fourierPontryaginDual (T := T)) := fun _ _ h =>
  fourier_injective hT (ContinuousMap.ext fun x => by
    simpa using congrArg
      (fun ψ : PontryaginDual (Multiplicative (AddCircle T)) => (ψ (.ofAdd x) : ℂ)) h)

/-- Distinct indices give distinct additive characters: `TauCeti.fourier_injective` again. -/
theorem fourierAddChar_injective (hT : T ≠ 0) :
    Function.Injective (fourierAddChar (T := T)) := fun _ _ h =>
  fourier_injective hT (ContinuousMap.ext fun x => DFunLike.congr_fun h x)

/-- Every trigonometric polynomial on `AddCircle T` has the form
`x ↦ fourier (-N) x * P.eval (fourier 1 x)` for some `N : ℕ` and `P : Polynomial ℂ`. -/
theorem exists_polynomial_of_mem_span_fourier
    {q : C(AddCircle T, ℂ)} (hq : q ∈ Submodule.span ℂ (Set.range (fourier (T := T)))) :
    ∃ (N : ℕ) (P : Polynomial ℂ), ∀ x, q x = fourier (-N) x * P.eval (fourier 1 x) := by
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hq
  obtain ⟨c, rfl⟩ := hq
  let N : ℕ := c.support.sup fun k => (-k).toNat
  let P : Polynomial ℂ := ∑ k ∈ c.support, Polynomial.C (c k) * Polynomial.X ^ (k + N).toNat
  have heval (z : ℂ) : P.eval z = ∑ k ∈ c.support, c k * z ^ (k + N).toNat := by
    simp [P, Polynomial.eval_finsetSum]
  refine ⟨N, P, fun x => ?_⟩
  rw [Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply, heval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  have hkN : 0 ≤ k + (N : ℤ) := by
    have hle : (-k).toNat ≤ N := Finset.le_sup (f := fun k : ℤ => (-k).toNat) hk
    omega
  rw [← ContinuousMap.pow_apply, fourier_one_pow, Int.toNat_of_nonneg hkN,
    mul_left_comm (fourier (T := T) (-↑N) x), ← fourier_add]
  have hsub : -(N : ℤ) + (k + N) = k := by omega
  rw [hsub]

end TauCeti

open TauCeti

variable [Fact (0 < T)]

namespace ContinuousMap

/-- **A continuous function on the circle with vanishing Fourier coefficients is zero.** The
separation statement for the Fourier coefficients of a continuous function, at the level of
`C(AddCircle T, ℂ)` rather than of `L²`; it is what makes a nonzero continuous function have a
nonzero Fourier coefficient. -/
theorem eq_zero_of_forall_fourierCoeff_eq_zero (F : C(AddCircle T, ℂ))
    (h : ∀ n : ℤ, fourierCoeff (⇑F) n = 0) : F = 0 := by
  refine ContinuousMap.toLp_injective (𝕜 := ℂ) (p := 2) haarAddCircle ?_
  refine fourierBasis.repr.injective ?_
  rw [map_zero, map_zero]
  ext n
  rw [fourierBasis_repr, fourierCoeff_toLp, h n]
  rfl

end ContinuousMap

namespace TauCeti

/-- The zero-frequency Fourier coefficient is the integral against normalized Haar measure. -/
theorem fourierCoeff_zero_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : AddCircle T → E) :
    fourierCoeff f 0 = ∫ x, f x ∂haarAddCircle := by
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul]

/-- Reflection of a circle function reverses its Fourier indices. -/
theorem fourierCoeff_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : AddCircle T → E) (n : ℤ) :
    fourierCoeff (fun x ↦ f (-x)) n = fourierCoeff f (-n) := by
  rw [fourierCoeff, fourierCoeff, ← integral_neg_eq_self]
  congr 1
  funext x
  simp only [fourier_apply, smul_neg, neg_smul, neg_neg]

/-- Translating a circle function by `θ` multiplies its `n`-th Fourier coefficient by
`fourier n θ`. -/
theorem fourierCoeff_comp_add_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : AddCircle T → E) (θ : AddCircle T) (n : ℤ) :
    fourierCoeff (fun x ↦ f (x + θ)) n = fourier n θ • fourierCoeff f n := by
  rw [fourierCoeff, fourierCoeff, ← integral_smul,
    ← integral_add_right_eq_self (fun x ↦ fourier n θ • fourier (-n) x • f x) θ]
  congr 1
  funext x
  rw [fourier_apply_add, smul_smul]
  congr 1
  linear_combination -fourier (-n) x * fourier_neg_mul_fourier n θ

/-- The Fourier coefficients of a difference of integrable functions. -/
theorem fourierCoeff_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : AddCircle T → E} (hf : Integrable f haarAddCircle) (hg : Integrable g haarAddCircle)
    (n : ℤ) :
    fourierCoeff (fun x ↦ f x - g x) n = fourierCoeff f n - fourierCoeff g n := by
  have hfg : (fun x ↦ f x - g x) = f + (-1 : ℂ) • g := by
    ext
    simp [sub_eq_add_neg]
  rw [hfg, fourierCoeff.add hf (hg.smul (-1 : ℂ)), Pi.add_apply, fourierCoeff.const_smul]
  simp [sub_eq_add_neg]

/-- Twisting by the monomial `fourier k` and conjugating reflects the Fourier coefficients about
`k / 2`: the `n`-th coefficient of `fourier k x * conj (g x)` is the conjugate of the `(k - n)`-th
coefficient of `g`. -/
theorem fourierCoeff_fourier_mul_conj (g : AddCircle T → ℂ) (k n : ℤ) :
    fourierCoeff (fun x ↦ fourier k x * starRingEnd ℂ (g x)) n =
      starRingEnd ℂ (fourierCoeff g (k - n)) := by
  rw [fourierCoeff, fourierCoeff, ← integral_conj]
  congr 1
  funext x
  rw [smul_eq_mul, smul_eq_mul, map_mul, ← fourier_neg, ← mul_assoc, ← fourier_add, neg_neg,
    neg_add_eq_sub]

/-- Fourier coefficients commute with continuous linear maps: the coefficients of `x ↦ φ (f x)`
are the images under `φ` of those of an integrable `f`. -/
theorem _root_.ContinuousLinearMap.fourierCoeff_comp {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (φ : E →L[ℂ] F) {f : AddCircle T → E} (hf : Integrable f haarAddCircle)
    (n : ℤ) :
    fourierCoeff (fun x ↦ φ (f x)) n = φ (fourierCoeff f n) := by
  simp only [fourierCoeff, ← φ.integral_comp_comm (hf.fourier_smul (-n)), map_smul]

/-- Fourier coefficients commute with `ContinuousLinearMap.compLpL` on `Lᵖ` (`1 ≤ p ≤ ∞`). -/
theorem _root_.ContinuousLinearMap.fourierCoeff_compLpL {p : ℝ≥0∞} [Fact (1 ≤ p)] {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (φ : E →L[ℂ] F) (f : Lp E p (haarAddCircle (T := T)))
    (n : ℤ) : fourierCoeff (φ.compLpL p (haarAddCircle (T := T)) f) n = φ (fourierCoeff f n) := by
  rw [fourierCoeff_congr_ae (φ.coeFn_compLpL f),
    φ.fourierCoeff_comp ((Lp.memLp f).integrable Fact.out) n]

/-- The `i`-th coordinate of the `n`-th Fourier coefficient of an integrable `PiLp`-valued function
on `AddCircle T` is the `n`-th Fourier coefficient of its `i`-th coordinate. -/
theorem _root_.MeasureTheory.Integrable.fourierCoeff_piLp_apply {ι : Type*} [Fintype ι] {q : ℝ≥0∞}
    [Fact (1 ≤ q)] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] {f : AddCircle T → PiLp q E}
    (hf : Integrable f (haarAddCircle (T := T))) (n : ℤ) (i : ι) :
    fourierCoeff f n i = fourierCoeff (fun x ↦ f x i) n := by
  simpa only [PiLp.proj_apply] using ((PiLp.proj (𝕜 := ℂ) q E i).fourierCoeff_comp hf n).symm

/-- The `i`-th coordinate of the `n`-th Fourier coefficient of a `PiLp`-valued `Lᵖ` function on
`AddCircle T` (`1 ≤ p ≤ ∞`) is the `n`-th Fourier coefficient of its `i`-th coordinate under
`MeasureTheory.Lp.piLpEquiv`. -/
theorem _root_.MeasureTheory.Lp.fourierCoeff_piLp_apply {ι : Type*} [Fintype ι] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] (f : Lp (PiLp p E) p (haarAddCircle (T := T))) (n : ℤ) (i : ι) :
    fourierCoeff f n i = fourierCoeff (Lp.piLpEquiv p ℂ E (haarAddCircle (T := T)) f i) n := by
  rw [Lp.piLpEquiv_apply_eq_compLpL, (PiLp.proj (𝕜 := ℂ) p E i).fourierCoeff_compLpL f n,
    PiLp.proj_apply]

/-- Pulling back an `Lᵖ` function by circle reflection reverses its Fourier indices. -/
theorem _root_.MeasureTheory.Lp.fourierCoeff_compMeasurePreserving_neg {p : ℝ≥0∞}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Lp E p (haarAddCircle (T := T))) (n : ℤ) :
    fourierCoeff (Lp.compMeasurePreserving (fun x ↦ -x)
      (Measure.measurePreserving_neg haarAddCircle) f) n = fourierCoeff f (-n) := by
  rw [fourierCoeff_congr_ae (Lp.coeFn_compMeasurePreserving f _)]
  exact fourierCoeff_comp_neg f n

/-- Convolving a continuous map `f : AddCircle T → E` against a continuous `R : AddCircle T → 𝕜`
gives an integrable integrand with respect to `haarAddCircle`. -/
theorem _root_.Continuous.integrable_smul_sub_haarAddCircle {𝕜 E : Type*} [TopologicalSpace 𝕜]
    [NormedAddCommGroup E] [SMul 𝕜 E] [ContinuousSMul 𝕜 E] {R : AddCircle T → 𝕜}
    (hR : Continuous R) {f : AddCircle T → E} (hf : Continuous f) (x : AddCircle T) :
    Integrable (fun u : AddCircle T ↦ R u • f (x - u)) haarAddCircle :=
  (hR.smul (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
    (.of_compactSpace _)

omit [Fact (0 < T)] in
/-- For continuous `T`-periodic `p`, `y ↦ fourier m y • hp.lift y` is interval integrable. -/
theorem _root_.Function.Periodic.intervalIntegrable_fourier_smul_lift {E : Type*}
    [NormedAddCommGroup E] [SMul ℂ E] [ContinuousSMul ℂ E] {p : ℝ → E}
    (hp : Function.Periodic p T) (hp_cont : Continuous p) (m : ℤ)
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] (a b : ℝ) :
    IntervalIntegrable (fun y : ℝ ↦ @fourier T m y • hp.lift y) μ a b :=
  have hl : Continuous hp.lift := continuous_coinduced_dom.2 hp_cont
  (((@fourier T m).continuous.comp continuous_quotient_mk').smul
    (hl.comp continuous_quotient_mk')).intervalIntegrable a b

/-- Convolving `x ↦ L (f x)` against a continuous kernel `R` commutes with `L`. -/
theorem _root_.ContinuousLinearMap.integral_smul_sub_haarAddCircle_comp {𝕜 E F : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[𝕜] F) {R : AddCircle T → 𝕜} (hR : Continuous R) {f : AddCircle T → E}
    (hf : Continuous f) (x : AddCircle T) :
    ∫ u : AddCircle T, R u • L (f (x - u)) ∂haarAddCircle =
      L (∫ u : AddCircle T, R u • f (x - u) ∂haarAddCircle) := by
  simpa only [map_smul] using L.integral_comp_comm (hR.integrable_smul_sub_haarAddCircle hf x)

/-- Convolving `f : AddCircle T → E` against `fourier m` yields `fourier m x • fourierCoeff f m`. -/
theorem integral_fourier_smul_sub_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (m : ℤ) (f : AddCircle T → E) (x : AddCircle T) :
    ∫ u : AddCircle T, fourier m u • f (x - u) ∂haarAddCircle =
      fourier m x • fourierCoeff f m := by
  rw [← integral_sub_left_eq_self (fun u ↦ fourier m u • f (x - u)) haarAddCircle x, fourierCoeff]
  simp_rw [sub_sub_cancel, fourier_apply_sub, mul_smul, integral_smul]

/-- **Uniform convolution approximation by continuous kernels.** Every continuous Banach-valued map
`f : AddCircle T → E` is uniformly approximated by convolving against `K : C(AddCircle T, ℂ)`. -/
theorem _root_.Continuous.exists_continuousMap_integral_smul_sub_lt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : AddCircle T → E}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) : ∃ K : C(AddCircle T, ℂ),
      ∀ x : AddCircle T, ‖(∫ u : AddCircle T, K u • f (x - u) ∂haarAddCircle) - f x‖ < ε := by
  obtain ⟨η, hη, huc⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hf) (ε / 2) (half_pos hε)
  let tent : AddCircle T → ℝ := fun u ↦ max 0 (1 - ‖u‖ / η)
  have htent : Continuous tent := by fun_prop
  let c : ℝ := ∫ u, tent u ∂haarAddCircle
  have hc : 0 < c := integral_pos_of_integrable_nonneg_ne_zero htent
    (htent.integrable_of_hasCompactSupport (.of_compactSpace _)) (fun _ ↦ le_max_left _ _)
    (by simp [tent] : tent 0 ≠ 0)
  let k : AddCircle T → ℝ := fun u ↦ c⁻¹ * tent u
  have hsupp : Function.support k ⊆ Metric.ball 0 η := fun u hu ↦ by
    rw [Metric.mem_ball, dist_zero_right]; by_contra h
    exact hu (by simp [k, tent, max_eq_left (sub_nonpos.2 ((one_le_div hη).2 (not_lt.1 h)))])
  refine ⟨⟨fun u ↦ (k u : ℂ), by fun_prop⟩, fun x ↦ ?_⟩
  have hconv := MeasureTheory.dist_convolution_le (μ := haarAddCircle) (x₀ := x) (z₀ := f x)
    (half_pos hε).le hsupp (fun _ ↦ mul_nonneg (inv_nonneg.2 hc.le) (le_max_left _ _))
    (by rw [integral_const_mul, inv_mul_cancel₀ hc.ne']) hf.aestronglyMeasurable
    fun y hy ↦ (huc (Metric.mem_ball.1 hy)).le
  rw [MeasureTheory.convolution_def, dist_eq_norm] at hconv
  simpa [Complex.coe_smul] using hconv.trans_lt (half_lt_self hε)

/-- **Uniform convolution approximation by scalar trigonometric polynomials.** Every continuous
Banach-valued map `f : AddCircle T → E` is uniformly approximated by convolving against
`Q ∈ Submodule.span ℂ (Set.range fourier)`. -/
theorem _root_.Continuous.exists_mem_span_fourier_integral_smul_sub_lt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : AddCircle T → E}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q ∈ Submodule.span ℂ (Set.range (fourier (T := T))),
      ∀ x : AddCircle T, ‖(∫ u : AddCircle T, Q u • f (x - u) ∂haarAddCircle) - f x‖ < ε := by
  obtain ⟨K, hconvK⟩ := hf.exists_continuousMap_integral_smul_sub_lt (half_pos hε)
  obtain ⟨M, hM, hfb⟩ := (isCompact_univ.image hf).isBounded.exists_pos_norm_le
  have hdense : K ∈ (Submodule.span ℂ (Set.range (fourier (T := T)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; trivial
  obtain ⟨Q, hQmem, hQK⟩ :=
    Metric.mem_closure_iff.1 hdense (ε / (2 * M)) (div_pos hε (by positivity))
  rw [dist_comm, dist_eq_norm] at hQK
  refine ⟨Q, hQmem, fun x ↦ (norm_sub_le_norm_sub_add_norm_sub _
    (∫ u, K u • f (x - u) ∂haarAddCircle) _).trans_lt ?_⟩
  rw [← integral_sub (Q.continuous.integrable_smul_sub_haarAddCircle hf x)
    (K.continuous.integrable_smul_sub_haarAddCircle hf x)]
  have hdiff : ‖∫ u, (Q u • f (x - u) - K u • f (x - u)) ∂haarAddCircle‖ < ε / 2 :=
    (norm_integral_le_of_norm_le_const (.of_forall fun u ↦ by
      rw [← sub_smul, norm_smul]
      exact mul_le_mul ((Q - K).norm_coe_le_norm u)
        (hfb _ (Set.mem_image_of_mem _ (Set.mem_univ _))) (norm_nonneg _) (norm_nonneg _))).trans_lt
      (by rw [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]
          exact (mul_lt_mul_of_pos_right hQK hM).trans_eq (by field_simp))
  linarith [hconvK x]

/-- The `Lp` class of a Fourier monomial has modulus one almost everywhere. -/
theorem ae_norm_fourierLp_eq_one (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :
    ∀ᵐ x ∂haarAddCircle (T := T), ‖fourierLp (T := T) p n x‖ = 1 := by
  filter_upwards [coeFn_fourierLp (T := T) p n] with x hx
  rw [hx]
  exact Circle.norm_coe _

/-- Every `Lp` Fourier monomial on `AddCircle T` (`1 ≤ p`) has `Lp` norm `1` with respect to
normalized Haar measure. -/
@[simp]
theorem norm_fourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :
    ‖fourierLp (T := T) p n‖ = 1 := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hae : (fun x => ‖fourierLp (T := T) p n x‖) =ᵐ[haarAddCircle (T := T)]
      fun x => ‖Lp.const p (haarAddCircle (T := T)) (1 : ℂ) x‖ := by
    filter_upwards [ae_norm_fourierLp_eq_one (T := T) p n,
      Lp.coeFn_const p (haarAddCircle (T := T)) (1 : ℂ)] with x hx h1
    rw [hx, h1, Function.const_apply, norm_one]
  rw [Lp.norm_def,
    eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) hae,
    ← Lp.norm_def, Lp.norm_const p (haarAddCircle (T := T)) (1 : ℂ) hp0]
  simp

/-- Multiplying an `Lᵖ` function by the bounded Fourier monomial `e_n` multiplies it pointwise
by `fourier n`, almost everywhere. -/
theorem coeFn_fourierLp_smul {p : ℝ≥0∞} (n : ℤ)
    (f : Lp ℂ p (haarAddCircle (T := T))) :
    ⇑(fourierLp (T := T) ∞ n • f : Lp ℂ p (haarAddCircle (T := T))) =ᵐ[haarAddCircle]
      fun x ↦ fourier n x * f x := by
  filter_upwards [Lp.coeFn_lpSMul (r := p) (fourierLp (T := T) ∞ n) f,
    coeFn_fourierLp (T := T) ∞ n] with x h hn
  rw [h, Pi.smul_apply', hn, smul_eq_mul]

/-- Multiplying the `Lᵖ` Fourier monomial `fourierLp p n` by the bounded monomial `fourierLp ∞ m`
gives `fourierLp p (m + n)`. -/
theorem fourierLp_smul_fourierLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (m n : ℤ) :
    (fourierLp (T := T) ∞ m • fourierLp (T := T) p n : Lp ℂ p (haarAddCircle (T := T))) =
      fourierLp (T := T) p (m + n) := by
  apply Lp.ext
  filter_upwards [coeFn_fourierLp_smul m (fourierLp (T := T) p n),
    coeFn_fourierLp (T := T) p n, coeFn_fourierLp (T := T) p (m + n)] with x hx hn hmn
  rw [hx, hn, hmn, fourier_add]

/-- Multiplying the `L²` Fourier mode `e_n` by the bounded monomial `e_m` gives `e_(m+n)`. -/
theorem fourierLp_smul_fourierBasis (m n : ℤ) :
    (fourierLp (T := T) ∞ m • fourierBasis (T := T) n : Lp ℂ 2 (haarAddCircle (T := T))) =
      fourierBasis (T := T) (m + n) := by
  apply Lp.ext
  filter_upwards [coeFn_fourierLp_smul m (fourierBasis (T := T) n),
    coeFn_fourierLp (T := T) 2 n, coeFn_fourierLp (T := T) 2 (m + n)] with x hx hn hmn
  rw [hx, coe_fourierBasis, hn, hmn, fourier_add]

/-- Multiplying an `Lᵖ` function successively by the Fourier monomials `e_n` and `e_m` is
multiplying it by `e_(m + n)`. -/
theorem fourierLp_smul_fourierLp_smul {p : ℝ≥0∞} (m n : ℤ)
    (f : Lp ℂ p (haarAddCircle (T := T))) :
    (fourierLp (T := T) ∞ m • (fourierLp (T := T) ∞ n • f) :
        Lp ℂ p (haarAddCircle (T := T))) = fourierLp (T := T) ∞ (m + n) • f := by
  apply Lp.ext
  filter_upwards [coeFn_fourierLp_smul m (fourierLp (T := T) ∞ n • f),
    coeFn_fourierLp_smul n f, coeFn_fourierLp_smul (m + n) f] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, fourier_add, mul_assoc]

/-- Multiplying an `Lᵖ` function by the bounded Fourier monomial `e_0 = 1` leaves it unchanged. -/
@[simp]
theorem fourierLp_zero_smul {p : ℝ≥0∞} (f : Lp ℂ p (haarAddCircle (T := T))) :
    (fourierLp (T := T) ∞ 0 • f : Lp ℂ p (haarAddCircle (T := T))) = f := by
  apply Lp.ext
  filter_upwards [coeFn_fourierLp_smul 0 f] with x hx
  rw [hx, fourier_zero, one_mul]

/-- The complex conjugate of the `Lᵖ` Fourier monomial `e_n` is `e_(-n)`. -/
@[simp]
theorem star_fourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :
    star (fourierLp (T := T) p n) = fourierLp (T := T) p (-n) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (fourierLp (T := T) p n), coeFn_fourierLp (T := T) p n,
    coeFn_fourierLp (T := T) p (-n)] with x h hn hneg
  rw [h, Pi.star_apply, hn, hneg, fourier_neg, RCLike.star_def]

/-- Multiplying an `Lᵖ` function by the bounded Fourier monomial `e_n` shifts its Fourier
coefficients by `n`.

Not a `simp` lemma: `simp` tries `SetLike.val_smul` on the product, whose search for an `SMul`
of `L^∞` on almost-everywhere-equal functions times out in large environments. -/
theorem fourierCoeff_fourierLp_smul {p : ℝ≥0∞} (n : ℤ) (f : Lp ℂ p (haarAddCircle (T := T)))
    (m : ℤ) :
    fourierCoeff (fourierLp (T := T) ∞ n • f : Lp ℂ p (haarAddCircle (T := T))) m =
      fourierCoeff f (m - n) := by
  rw [fourierCoeff_congr_ae (coeFn_fourierLp_smul n f), fourierCoeff, fourierCoeff]
  congr 1
  funext x
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← fourier_add]
  congr 3
  ring

/-- Multiplying an `L²` Fourier mode `e_m` by an essentially bounded function `a` shifts the
Fourier coefficients of `a` by `m`. -/
theorem fourierCoeff_smul_fourierBasis (a : Lp ℂ ∞ (haarAddCircle (T := T))) (m n : ℤ) :
    fourierCoeff (a • fourierBasis (T := T) m : Lp ℂ 2 (haarAddCircle (T := T))) n =
      fourierCoeff a (n - m) := by
  have hae : (a • fourierBasis (T := T) m : Lp ℂ 2 (haarAddCircle (T := T))) =ᵐ[haarAddCircle]
      (fourierLp (T := T) ∞ m • a : Lp ℂ ∞ (haarAddCircle (T := T))) := by
    filter_upwards [Lp.coeFn_lpSMul (r := 2) a (fourierBasis (T := T) m),
      coeFn_fourierLp (T := T) 2 m, coeFn_fourierLp_smul m a] with x hx hm hma
    rw [hx, Pi.smul_apply', coe_fourierBasis, hm, hma, smul_eq_mul, mul_comm]
  rw [fourierCoeff_congr_ae hae, fourierCoeff_fourierLp_smul]

/-- In a complex normed star module with continuous `star`, the Fourier coefficients of
`x ↦ star (f x)` are `star` of the reflected Fourier coefficients of `f`. -/
theorem fourierCoeff_star {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [StarAddMonoid E] [ContinuousStar E] [StarModule ℂ E] (f : AddCircle T → E) (n : ℤ) :
    fourierCoeff (fun x ↦ star (f x)) n = star (fourierCoeff f (-n)) := by
  rw [fourierCoeff, fourierCoeff, ← integral_star]
  congr 1; funext x
  rw [neg_neg, star_smul, fourier_neg, RCLike.star_def]

/-- In a normed complex star module, the Fourier coefficients of `star f` are `star` of the
reflected Fourier coefficients of `f`. -/
@[simp]
theorem _root_.MeasureTheory.Lp.fourierCoeff_star {p : ℝ≥0∞} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [StarAddMonoid E] [NormedStarGroup E]
    [StarModule ℂ E] (f : Lp E p (haarAddCircle (T := T))) (n : ℤ) :
    fourierCoeff (star f : Lp E p (haarAddCircle (T := T))) n =
      star (fourierCoeff f (-n)) :=
  (congrFun (fourierCoeff_congr_ae (Lp.coeFn_star f)) n).trans (TauCeti.fourierCoeff_star f n)

/-- The Fourier coefficients of the `Lᵖ` monomial `e_n` are those of the continuous monomial
`e_n`: `1` at `n` and `0` elsewhere. -/
theorem fourierCoeff_fourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n k : ℤ) :
    fourierCoeff (fourierLp (T := T) p n) k = if k = n then 1 else 0 := by
  rw [fourierCoeff_congr_ae (coeFn_fourierLp p n), fourierCoeff_fourier, Pi.single_apply]

end TauCeti

namespace AddChar

/-- **Every continuous additive character of the circle is a Fourier monomial.** Continuity is the
only hypothesis: no unitarity is assumed, and none is needed. Together with
`TauCeti.fourierAddChar_injective` this identifies the continuous characters of `AddCircle T` with
`ℤ`, which is the content of `TauCeti.fourierPontryaginDualEquiv`. -/
theorem exists_fourierAddChar_eq (χ : AddChar (AddCircle T) ℂ) (hχ : Continuous χ) :
    ∃ n : ℤ, fourierAddChar n = χ := by
  have hcoeff : ∀ n : ℤ, fourierCoeff (⇑(⟨χ, hχ⟩ : C(AddCircle T, ℂ))) n
      = ∫ x : AddCircle T, fourier (-n) x * χ x ∂haarAddCircle := fun _ => by
    simp only [fourierCoeff, ContinuousMap.coe_mk, smul_eq_mul]
  have hFne : (⟨χ, hχ⟩ : C(AddCircle T, ℂ)) ≠ 0 := by
    intro h
    have hzero := DFunLike.congr_fun h (0 : AddCircle T)
    simp at hzero
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ∫ x : AddCircle T, fourier (-n) x * χ x ∂haarAddCircle ≠ 0 := by
    by_contra hcon
    refine hFne (ContinuousMap.eq_zero_of_forall_fourierCoeff_eq_zero ⟨χ, hχ⟩ fun n => ?_)
    rw [hcoeff n]
    by_contra hne
    exact hcon ⟨n, hne⟩
  refine ⟨n, AddChar.ext _ _ fun y => ?_⟩
  have hfactor : (∫ x : AddCircle T, fourier (-n) x * χ x ∂haarAddCircle)
      = (fourier (-n) y * χ y) * ∫ x : AddCircle T, fourier (-n) x * χ x ∂haarAddCircle :=
    calc (∫ x : AddCircle T, fourier (-n) x * χ x ∂haarAddCircle)
        = ∫ x : AddCircle T, fourier (-n) (x + y) * χ (x + y) ∂haarAddCircle :=
          (integral_add_right_eq_self _ y).symm
      _ = ∫ x : AddCircle T, (fourier (-n) y * χ y) * (fourier (-n) x * χ x) ∂haarAddCircle :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by
            simp only [← fourierAddChar_apply, AddChar.map_add_eq_mul]; ring)
      _ = (fourier (-n) y * χ y) * ∫ x : AddCircle T, fourier (-n) x * χ x ∂haarAddCircle :=
          integral_const_mul _ _
  have hone : fourier (-n) y * χ y = 1 :=
    mul_right_cancel₀ hn (by rw [one_mul]; exact hfactor.symm)
  have hprod : fourier (-n) y * fourier n y = 1 := by
    rw [← fourier_add, neg_add_cancel]
    exact fourier_zero
  have hne0 : fourier (-n) y ≠ 0 := by
    rw [fourier_apply]
    exact Circle.coe_ne_zero _
  exact mul_left_cancel₀ hne0 (hprod.trans hone.symm)

/-- The Fourier index of a continuous additive character of the circle is unique. -/
theorem existsUnique_fourierAddChar_eq (χ : AddChar (AddCircle T) ℂ) (hχ : Continuous χ) :
    ∃! n : ℤ, fourierAddChar n = χ := by
  obtain ⟨n, hn⟩ := exists_fourierAddChar_eq χ hχ
  exact ⟨n, hn, fun m hm =>
    fourierAddChar_injective (Fact.out (p := (0 < T))).ne' (hm.trans hn.symm)⟩

/-- **A continuous additive character of the circle takes values of modulus one.** No unitarity
hypothesis is needed anywhere above: continuity alone forces the character to be a Fourier
monomial, and `fourier n` is valued in the unit circle. -/
theorem norm_apply_eq_one_of_continuous (χ : AddChar (AddCircle T) ℂ) (hχ : Continuous χ)
    (x : AddCircle T) : ‖χ x‖ = 1 := by
  obtain ⟨n, rfl⟩ := exists_fourierAddChar_eq χ hχ
  rw [fourierAddChar_apply, fourier_apply]
  exact Circle.norm_coe _

end AddChar

namespace ContinuousMonoidHom

/-- A continuous character of the circle is a unique integer power. -/
theorem existsUnique_circle_eq_zpow (χ : Circle →ₜ* Circle) :
    ∃! n : ℤ, ∀ z : Circle, χ z = z ^ n := by
  let ψ : AddChar (AddCircle (1 : ℝ)) ℂ :=
    { toFun := fun x ↦ (χ (AddCircle.toCircle x) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun x y ↦ by simp [AddCircle.toCircle_add] }
  have hψ : Continuous ψ :=
    (continuous_induced_dom (f := ((↑) : Circle → ℂ))).comp
      (χ.continuous.comp AddCircle.continuous_toCircle)
  obtain ⟨n, hn⟩ := AddChar.exists_fourierAddChar_eq ψ hψ
  have hn' (z : Circle) : χ z = z ^ n := by
    obtain ⟨x, rfl⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective z
    apply Circle.ext
    simpa only [AddCircle.homeomorphCircle_apply, TauCeti.fourierAddChar_apply,
      fourier_apply, AddCircle.toCircle_zsmul, ψ, AddChar.coe_mk] using
      (DFunLike.congr_fun hn x).symm
  refine ⟨n, hn', fun m hm ↦ ?_⟩
  apply TauCeti.fourier_injective (T := (1 : ℝ)) one_ne_zero
  ext x
  simp only [fourier_apply, AddCircle.toCircle_zsmul]
  exact congrArg (fun z : Circle ↦ (z : ℂ)) ((hm _).symm.trans (hn' _))

end ContinuousMonoidHom

namespace TauCeti

/-- **The Fourier monomials are the Pontryagin dual of the circle.** The map
`n ↦ fourierPontryaginDual n` is an isomorphism of groups from `Multiplicative ℤ` onto
`PontryaginDual (Multiplicative (AddCircle T))`, the group of continuous characters of the circle
group: it is a homomorphism because `fourier (m + n) = fourier m * fourier n`, injective by
`TauCeti.fourierPontryaginDual_injective`, and surjective by `AddChar.exists_fourierAddChar_eq`.

The multiplicative type tags are what make this a statement about groups: the dual multiplies
characters pointwise, and that multiplication corresponds to addition of Fourier indices. -/
noncomputable def fourierPontryaginDualEquiv :
    Multiplicative ℤ ≃* PontryaginDual (Multiplicative (AddCircle T)) :=
  MulEquiv.ofBijective
    ({ toFun := fun n => fourierPontryaginDual (Multiplicative.toAdd n)
       map_one' := PontryaginDual.ext fun _ => Circle.ext (by simp)
       map_mul' := fun m n => PontryaginDual.ext fun x => Circle.ext <| by
         -- the dual multiplies characters pointwise by definition, so this `change` only
         -- spells the right-hand side out; `fourier_add` then closes the goal through `simp`
         change ((fourierPontryaginDual (Multiplicative.toAdd (m * n)) x : Circle) : ℂ) =
           (fourierPontryaginDual (Multiplicative.toAdd m) x : ℂ) *
             (fourierPontryaginDual (Multiplicative.toAdd n) x : ℂ)
         simp } :
      Multiplicative ℤ →* PontryaginDual (Multiplicative (AddCircle T)))
    ⟨fun _ _ h => Multiplicative.toAdd.injective
        (fourierPontryaginDual_injective (Fact.out (p := (0 < T))).ne' h),
      fun ψ => by
        have hcoe : Continuous ((↑) : Circle → ℂ) := continuous_induced_dom
        have hcont : Continuous fun x : AddCircle T => (ψ (Multiplicative.ofAdd x) : ℂ) :=
          hcoe.comp (map_continuous ψ)
        obtain ⟨n, hn⟩ := AddChar.exists_fourierAddChar_eq
          { toFun := fun x : AddCircle T => (ψ (Multiplicative.ofAdd x) : ℂ)
            map_zero_eq_one' := by simp
            map_add_eq_mul' := fun x y => by rw [ofAdd_add, map_mul, Circle.coe_mul] } hcont
        exact ⟨Multiplicative.ofAdd n, PontryaginDual.ext fun x => Circle.ext (by
          simpa using DFunLike.congr_fun hn (Multiplicative.toAdd x))⟩⟩

@[simp]
theorem fourierPontryaginDualEquiv_apply (n : Multiplicative ℤ) :
    fourierPontryaginDualEquiv (T := T) n = fourierPontryaginDual (Multiplicative.toAdd n) := (rfl)

/-- The inverse of `TauCeti.fourierPontryaginDualEquiv` returns the Fourier index of a continuous
character: the monomial at that index is the character one started from. -/
@[simp]
theorem fourierPontryaginDualEquiv_apply_symm_apply
    (ψ : PontryaginDual (Multiplicative (AddCircle T))) :
    fourierPontryaginDual (Multiplicative.toAdd (fourierPontryaginDualEquiv.symm ψ)) = ψ :=
  fourierPontryaginDualEquiv.apply_symm_apply ψ

end TauCeti
