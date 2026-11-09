/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import TauCeti.Analysis.Calculus.Hadamard
public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Analysis.Normed.Algebra.SquareRoot
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv

/-!
# The Morse lemma

Near a nondegenerate critical point a `C^{n+2}` function, with `1 ≤ n ≤ ∞`, is, in suitable
`C^n` coordinates, exactly its Hessian quadratic form. This file proves that for a real-valued
function on a Banach space, in the form
`TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart`: there is a chart `ψ` at the critical
point `x`, carrying `x` to `0`, with both coordinate maps `C^n` on their domains, and with

`f y = f x + 2⁻¹ * fderiv ℝ (fderiv ℝ f) x (ψ y) (ψ y)`

on the whole of its source.  Nondegeneracy is the one from
`TauCeti.Analysis.Calculus.Morse.Basic`: the second derivative, read as a map from the space to
its dual, is a linear homeomorphism.  In finite dimensions that is the classical condition that
the Hessian be a nondegenerate bilinear form, so this is the classical Morse lemma; in infinite
dimensions it is the strong nondegeneracy of Morse theory on Banach and Hilbert manifolds, and
the statement is the Morse--Palais lemma of Palais (1969).

The proof is Palais's.  Write `f (x + v) - f x - fderiv ℝ f x v = 2⁻¹ * B v v v`, where `B v` is
the **averaged Hessian** `TauCeti.hessianAverage f x v`, the average of the second derivative
along the segment from `x` to `x + v`, weighted so that `B 0` is the Hessian itself.  Then `B` is
a `C^n` family of symmetric continuous bilinear forms with `B 0` invertible, so
`TauCeti.exists_congruence_of_symmetric_family` produces a `C^n` family of operators `R v`,
equal to the identity at `v = 0`, with `B v w w' = B 0 (R v w) (R v w')`.  Taking `w = w' = v`
turns the second-order term into the Hessian evaluated at `φ v = R v v`, and `φ` has derivative
the identity at `0`, so it is a chart by the inverse function theorem.

The weight `2 * (1 - t)` is what makes `B 0` the Hessian on the nose.  Iterating the smooth
Hadamard factorisation of `TauCeti.Analysis.Calculus.Hadamard` twice would also produce a smooth
family with `f (x + v) - f x = B v v v` at a critical point, but its value at `0` is then the
derivative of a parametrised integral rather than the Hessian, and it is not symmetric; both are
needed here.  The averaged Hessian and its Taylor formula are stated for a map into an arbitrary
Banach space, nothing in them being special to real-valued functions; only the congruence and the
Morse lemma itself need `f` real-valued.

The family `R` is manufactured from a square root: the operator `C v = (B 0)⁻¹ ∘ B v` is close to
the identity for `v` close to `0`, so it has a unique square root there
(`TauCeti.sqrtNearOne`), and that square root is automatically self-adjoint for the pairing
`B 0`, because the adjoint of a square root is a square root of the adjoint and the two are close
to the identity.  Self-adjointness is exactly what turns `R v * R v = C v` into the congruence
identity.

The Morse lemma supplies the local model of a Morse function: the index of the critical point,
the local handle structure, and the local form of the gradient flow are all read off it.  The
averaged Hessian of a `C^{n+2}` function is `C^n`, and the congruence construction preserves the
regularity of the family. The Morse lemma therefore gives a `C^n` chart for a `C^{n+2}`
function when `1 ≤ n ≤ ∞`; taking `n = ∞` recovers the smooth Morse lemma.

The operators are a definite choice: the canonical congruence `TauCeti.morseCongruence B₀ B`
is the square root near the identity of `B₀⁻¹ ∘ B`. It is a congruence for every pair of symmetric
forms near a pair `(B₀, B₀)` with `B₀` invertible (`TauCeti.eventually_morseCongruence_apply`),
and it depends smoothly on both forms, so the reference form may vary too. Being canonical, it
is compatible with linear changes of coordinates, which is what the parametric Morse lemma on a
vector bundle needs to glue local normal forms.

The varying-reference variant `TauCeti.exists_parametric_congruence_of_symmetric_family`
compares a jointly smooth family `B (b, v)` to `B (b, 0)` by jointly smooth invertible
operators `R (b, v)`, with `R (b, 0) = 1` throughout a base neighbourhood and jointly smooth
inverses. This is the linear normalization needed for a parameter-dependent Morse change of
coordinates fixing the zero section, with its Hessian as the reference quadratic form.
The construction uses `TauCeti.exists_congruence_of_symmetric_family` to compare all forms
to `B (a, 0)`, then divides by the resulting operator on the zero section. Inversion is smooth
on a product neighbourhood of invertible operators. This preserves the differentiability
order, including order zero.

## Main declarations

* `TauCeti.hessianAverage`: the averaged Hessian along a segment, normalised so that
  `TauCeti.hessianAverage_zero` identifies its value at `0` with the Hessian.
* `TauCeti.map_add_eq_add_hessianAverage`: the second-order Taylor formula it satisfies.
* `TauCeti.hessianAverage_comp_continuousLinearEquiv_apply`: the averaged Hessian under a linear
  change of variables.
* `TauCeti.morseCongruence`: the canonical congruence `√(B₀⁻¹ ∘ B)` comparing a form `B` with a
  reference form `B₀`, with `TauCeti.eventually_morseCongruence_apply` (it is a congruence),
  `TauCeti.eventually_contDiffAt_morseCongruence` (it is smooth in both forms) and
  `TauCeti.tendsto_morseCongruence`.
* `TauCeti.exists_congruence_of_symmetric_family`: a `C^n` family of symmetric continuous
  bilinear forms whose value at a basepoint is invertible is, near that point, the congruence of
  that value by a `C^n` family of operators equal to the identity at the basepoint.
* `TauCeti.exists_parametric_congruence_of_symmetric_family`: congruence to the varying
  reference `B (b, 0)`, with identity operators on the zero section and jointly `C^n` inverses.
* `TauCeti.IsNondegenerateCriticalPoint.exists_normal_form`: **the Morse lemma**, in the form of a
  `C^n` map `φ` fixing `0` with derivative the identity there.
* `TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart`: the Morse lemma as a chart at the
  critical point.

## References

* R. S. Palais, *The Morse lemma for Banach spaces*, Bull. Amer. Math. Soc. **75** (1969),
  968--971, for the statement proved here: the theorem below asks only that `E` be a Banach
  space, which is that note's setting rather than the Hilbert one.
* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology **2** (1963), 299--340, Section 2,
  for the proof by an operator square root used here.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, 1963, Lemma 2.2, for the classical
  finite-dimensional statement.
* M. Audin, M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014, Chapter 1.
-/

public section

noncomputable section

open Filter MeasureTheory Topology

open scoped ContDiff

namespace TauCeti

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {x : E}

section HessianAverage

variable [CompleteSpace F] {f : E → F}

/-- The **averaged Hessian** of `f` at `x` in the direction `v`: the average of the second
derivative of `f` along the segment from `x` to `x + v`, against the weight `2 * (1 - t)`.  The
weight is normalised so that the value at `v = 0` is the Hessian at `x` itself
(`TauCeti.hessianAverage_zero`), while `TauCeti.map_add_eq_add_hessianAverage` says that
`f (x + v)` differs from its first-order Taylor polynomial by `2⁻¹ • hessianAverage f x v v v`. -/
def hessianAverage (f : E → F) (x v : E) : E →L[ℝ] E →L[ℝ] F :=
  segmentAverage (fun t ↦ 2 * (1 - t)) (fderiv ℝ (fderiv ℝ f)) x v

omit [CompleteSpace F] in
/-- The averaged Hessian as an integral over the compact unit interval, the shape in which the
regularity theorem for parametrised integrals applies to it. -/
theorem hessianAverage_eq_integral_Icc (f : E → F) (x : E) :
    hessianAverage f x = fun v ↦ ∫ t in Set.Icc (0 : ℝ) 1,
      (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (x + t • v) := by
  exact segmentAverage_eq_integral_Icc _ _ _

/-- At the basepoint the averaged Hessian is the Hessian: the weight `2 * (1 - t)` has integral
`1` over the unit interval. -/
@[simp]
theorem hessianAverage_zero (f : E → F) (x : E) :
    hessianAverage f x 0 = fderiv ℝ (fderiv ℝ f) x := by
  rw [hessianAverage, segmentAverage_zero]
  have hI : (∫ t in (0 : ℝ)..1, 2 * (1 - t)) = 1 := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    norm_num [integral_id]
  rw [hI, one_smul]

omit [CompleteSpace F] in
/-- The averaged fiber Hessian of a jointly `C^{n+2}` family is jointly `C^n` in the parameter
and the fiber displacement. -/
theorem contDiff_hessianAverage_param
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : ℕ∞} {g : P × E → F} (hg : ContDiff ℝ (n + 2) g) (x : E) :
    ContDiff ℝ n (fun p : P × E ↦ hessianAverage (fun y ↦ g (p.1, y)) x p.2) := by
  have hD : ContDiff ℝ (n + 1)
      (fun p : P × E ↦ fderiv ℝ (fun y ↦ g (p.1, y)) p.2) := by
    apply ContDiff.fderiv (f := fun p : P × E ↦ fun y : E ↦ g (p.1, y))
    · exact hg.comp (by fun_prop)
    · fun_prop
    · norm_num [add_assoc]
  have hDD : ContDiff ℝ n
      (fun p : P × E ↦ fderiv ℝ (fderiv ℝ (fun y ↦ g (p.1, y))) p.2) := by
    apply ContDiff.fderiv
      (f := fun p : P × E ↦ fderiv ℝ (fun y ↦ g (p.1, y)))
    · exact hD.comp (by fun_prop :
        ContDiff ℝ (n + 1) (fun p : (P × E) × E ↦ (p.1.1, p.2)))
    · fun_prop
    · exact le_rfl
  exact hDD.contDiff_segmentAverage_param
    ((by fun_prop : Continuous fun t : ℝ ↦ 2 * (1 - t)).intervalIntegrable 0 1) x

omit [CompleteSpace F] in
/-- The averaged Hessian of a `C^{n+2}` function is `C^n` in the direction. -/
theorem contDiff_hessianAverage {n : ℕ∞} (hf : ContDiff ℝ (n + 2) f) (x : E) :
    ContDiff ℝ n (hessianAverage f x) := by
  exact (contDiff_hessianAverage_param (hf.comp contDiff_snd) x).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ n (fun v : E ↦ ((0 : E), v)))

omit [CompleteSpace F] in
private theorem continuous_hessianAverage_integrand (hf : ContDiff ℝ 2 f) (x v : E) :
    Continuous fun t : ℝ ↦ (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (x + t • v) := by
  -- The scalar action on iterated continuous linear maps is definitionally equal to the
  -- normed-space action, but instance search does not identify the two instances.
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] F) :=
    @NormedSpace.toIsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] F) _ _ _
  have hd : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  exact (by fun_prop : Continuous fun t : ℝ ↦ 2 * (1 - t)).smul (hd.comp (by fun_prop))

/-- Evaluating the averaged Hessian on a pair of vectors commutes with the integral. -/
theorem hessianAverage_apply (hf : ContDiff ℝ 2 f) (x v w w' : E) :
    hessianAverage f x v w w'
      = ∫ t in (0 : ℝ)..1, (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (x + t • v) w w' := by
  have h1 := continuous_hessianAverage_integrand hf x v
  have h2 : Continuous fun t : ℝ ↦ ((2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (x + t • v)) w :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] F) w).continuous.comp h1
  have hApply := ContinuousLinearMap.segmentAverage_apply
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] F) w) (fun t ↦ 2 * (1 - t))
      (fderiv ℝ (fderiv ℝ f)) x v (h1.intervalIntegrable 0 1)
  simp only [ContinuousLinearMap.apply_apply] at hApply
  rw [hessianAverage, hApply,
    ContinuousLinearMap.intervalIntegral_apply (h2.intervalIntegrable 0 1) w']
  simp

/-- The averaged Hessian is a symmetric bilinear form, since each second derivative along the
segment is. -/
theorem hessianAverage_symm (hf : ContDiff ℝ 2 f) (x v w w' : E) :
    hessianAverage f x v w w' = hessianAverage f x v w' w := by
  rw [hessianAverage_apply hf, hessianAverage_apply hf]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [(hf.contDiffAt.isSymmSndFDerivAt (by norm_num) :
    IsSymmSndFDerivAt ℝ f (x + t • v)) w w']

/-- **The averaged Hessian under a linear change of variables.** For a continuous linear
equivalence `e`, the averaged Hessian of `f ∘ e` at `x` in the direction `v`, applied to `w` and
`w'`, is that of `f` at `e x` in the direction `e v`, applied to `e w` and `e w'`. -/
theorem hessianAverage_comp_continuousLinearEquiv_apply {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (hf : ContDiff ℝ 2 f) (e : G ≃L[ℝ] E) (x v w w' : G) :
    hessianAverage (f ∘ e) x v w w' = hessianAverage f (e x) (e v) (e w) (e w') := by
  rw [hessianAverage_apply (hf.comp e.contDiff), hessianAverage_apply hf]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [e.fderiv_fderiv_comp_right_apply_apply, map_add, map_smul]

/-- **Taylor's formula to second order**, with the remainder written as the averaged Hessian
evaluated twice on the increment. -/
theorem map_add_eq_add_hessianAverage (hf : ContDiff ℝ 2 f) (x v : E) :
    f (x + v) = f x + fderiv ℝ f x v + (2 : ℝ)⁻¹ • hessianAverage f x v v v := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (n := 1) (x := x) (y := v)
    (fun _ _ ↦ hf.contDiffAt)
  norm_num [Finset.sum_range_succ] at h
  -- `iteratedFDeriv_two_apply` is stated with the numeral `2`, while Taylor's theorem leaves the
  -- order as `1 + 1`; expose that definitional equality before rewriting.
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  simp only [iteratedFDeriv_two_apply] at h
  rw [h, hessianAverage_apply hf, ← intervalIntegral.integral_smul]
  refine congrArg (fun z ↦ f x + fderiv ℝ f x v + z) ?_
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [smul_smul]
  congr 1
  ring

end HessianAverage

section Congruence

open Set

variable [CompleteSpace E]

/-- The **canonical Morse congruence** comparing a bilinear form `B` with a reference form `B₀`:
the square root near the identity of the comparison operator `B₀⁻¹ ∘ B`. When `B₀` is
invertible, both forms are symmetric and `B` is close to `B₀`, it is a congruence,
`B₀ (R w) (R w') = B w w'` (`TauCeti.eventually_morseCongruence_apply`). Its value is only
meaningful for `B` close to an invertible `B₀`. -/
def morseCongruence (B₀ B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  sqrtNearOne (E →L[ℝ] E) (B₀.inverse ∘L B)

/-- The canonical congruence is the square root near the identity of `B₀⁻¹ ∘ B`. -/
theorem morseCongruence_def (B₀ B : E →L[ℝ] E →L[ℝ] ℝ) :
    morseCongruence B₀ B = sqrtNearOne (E →L[ℝ] E) (B₀.inverse ∘L B) := by
  rw [morseCongruence]

variable {B₀ : E →L[ℝ] E →L[ℝ] ℝ}

/-- The canonical congruence of an invertible form with itself is the identity. -/
theorem morseCongruence_self (hB₀ : B₀.IsInvertible) : morseCongruence B₀ B₀ = 1 := by
  rw [morseCongruence, hB₀.inverse_comp_self, ← ContinuousLinearMap.one_def, sqrtNearOne_one]

/-- The comparison operator `B₀⁻¹ ∘ B` tends to the identity as both forms tend to an invertible
form. -/
private theorem tendsto_inverse_comp (hB₀ : B₀.IsInvertible) :
    Tendsto (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦ p.1.inverse ∘L p.2)
      (𝓝 (B₀, B₀)) (𝓝 1) := by
  have h₁ : ContinuousAt (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦ p.1.inverse)
      (B₀, B₀) :=
    ContinuousAt.comp (f := Prod.fst) (x := (B₀, B₀))
      (hB₀.contDiffAt_map_inverse (n := 0)).continuousAt continuousAt_fst
  have h := h₁.clm_comp continuousAt_snd
  simpa only [hB₀.inverse_comp_self, ← ContinuousLinearMap.one_def] using h.tendsto

/-- The canonical congruence tends to the identity as both forms tend to an invertible form. -/
theorem tendsto_morseCongruence (hB₀ : B₀.IsInvertible) :
    Tendsto (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦ morseCongruence p.1 p.2)
      (𝓝 (B₀, B₀)) (𝓝 1) := by
  simpa only [Function.comp_def, sqrtNearOne_one, morseCongruence] using
    (continuousAt_sqrtNearOne (A := E →L[ℝ] E)).tendsto.comp (tendsto_inverse_comp hB₀)

/-- Near a pair of equal invertible forms, the canonical congruence is a square root of the
comparison operator `B₀⁻¹ ∘ B`. -/
theorem eventually_morseCongruence_mul_self (hB₀ : B₀.IsInvertible) :
    ∀ᶠ p in 𝓝 (B₀, B₀), morseCongruence p.1 p.2 * morseCongruence p.1 p.2 = p.1.inverse ∘L p.2 :=
  (tendsto_inverse_comp hB₀).eventually eventually_mul_self_sqrtNearOne

/-- Near a pair of equal invertible forms, the canonical congruence depends smoothly, to every
order, on the pair. -/
theorem eventually_contDiffAt_morseCongruence (hB₀ : B₀.IsInvertible) {n : ℕ∞ω} :
    ∀ᶠ p in 𝓝 (B₀, B₀),
      ContDiffAt ℝ n (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
        morseCongruence p.1 p.2) p := by
  filter_upwards [(tendsto_inverse_comp hB₀).eventually ((isOpen_analyticAt ℝ
      (sqrtNearOne (E →L[ℝ] E))).mem_nhds analyticAt_sqrtNearOne),
    continuousAt_fst.eventually hB₀.eventually_nhds] with p hp hp₁
  exact hp.contDiffAt.comp p ((hp₁.contDiffAt_map_inverse.comp p contDiffAt_fst).clm_comp
    contDiffAt_snd)

/-- The adjoint of an operator `X` for the pairing `B₀`, characterized by
`B₀ (adj X w) w' = B₀ w (X w')` when `B₀` is invertible. -/
private def pairingAdjoint (B₀ : E →L[ℝ] E →L[ℝ] ℝ) (X : E →L[ℝ] E) : E →L[ℝ] E :=
  B₀.inverse ∘L ((ContinuousLinearMap.compL ℝ E E ℝ).flip X ∘L B₀)

omit [CompleteSpace E] in
private theorem pairingAdjoint_apply (hB₀ : B₀.IsInvertible) (X : E →L[ℝ] E) (w w' : E) :
    B₀ (pairingAdjoint B₀ X w) w' = B₀ w (X w') := by
  simp [pairingAdjoint, hB₀.self_apply_inverse]

omit [CompleteSpace E] in
private theorem ext_of_pairing (hB₀ : B₀.IsInvertible) {X Y : E →L[ℝ] E}
    (h : ∀ w w', B₀ (X w) w' = B₀ (Y w) w') : X = Y :=
  ContinuousLinearMap.ext fun w ↦ hB₀.bijective.injective (ContinuousLinearMap.ext (h w))

omit [CompleteSpace E] in
private theorem pairingAdjoint_mul (hB₀ : B₀.IsInvertible) (X Y : E →L[ℝ] E) :
    pairingAdjoint B₀ (X * Y) = pairingAdjoint B₀ Y * pairingAdjoint B₀ X :=
  ext_of_pairing hB₀ fun w w' ↦ by
    simp only [pairingAdjoint_apply hB₀, mul_apply_eq_comp]

private theorem tendsto_pairingAdjoint (hB₀ : B₀.IsInvertible) :
    Tendsto (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) ↦ pairingAdjoint q.1 q.2)
      (𝓝 (B₀, 1)) (𝓝 1) := by
  have h₁ : ContinuousAt (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) ↦ q.1.inverse) (B₀, 1) :=
    ContinuousAt.comp (f := Prod.fst) (x := (B₀, 1))
      (hB₀.contDiffAt_map_inverse (n := 0)).continuousAt continuousAt_fst
  have h₂ : ContinuousAt (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) ↦
      (ContinuousLinearMap.compL ℝ E E ℝ).flip q.2) (B₀, 1) :=
    ((ContinuousLinearMap.compL ℝ E E ℝ).flip).continuous.continuousAt.comp continuousAt_snd
  have h : ContinuousAt (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E) ↦
      pairingAdjoint q.1 q.2) (B₀, 1) :=
    h₁.clm_comp (h₂.clm_comp continuousAt_fst)
  have h1 : pairingAdjoint B₀ 1 = 1 := ext_of_pairing hB₀ fun w w' ↦ by
    simp [pairingAdjoint_apply hB₀]
  simpa only [h1] using h.tendsto

/-- **The canonical congruence is a congruence.** Near a pair of equal invertible forms, if both
forms are symmetric then `B₀ (R w) (R w') = B w w'` for `R = morseCongruence B₀ B`.

The square root `R` of `C = B₀⁻¹ ∘ B` is self-adjoint for the pairing `B₀`: its adjoint is a
square root of the adjoint of `C`, which is `C` itself, and both are close to the identity. -/
theorem eventually_morseCongruence_apply (hB₀ : B₀.IsInvertible) :
    ∀ᶠ p in 𝓝 (B₀, B₀), (∀ w w', p.1 w w' = p.1 w' w) → (∀ w w', p.2 w w' = p.2 w' w) →
      ∀ w w', p.1 (morseCongruence p.1 p.2 w) (morseCongruence p.1 p.2 w') = p.2 w w' := by
  have hadj : Tendsto (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
      pairingAdjoint p.1 (morseCongruence p.1 p.2)) (𝓝 (B₀, B₀)) (𝓝 1) :=
    (tendsto_pairingAdjoint hB₀).comp
      (continuousAt_fst.tendsto.prodMk_nhds (tendsto_morseCongruence hB₀))
  filter_upwards [eventually_morseCongruence_mul_self hB₀,
    hadj.eventually eventually_sqrtNearOne_mul_self,
    continuousAt_fst.eventually hB₀.eventually_nhds] with p hsq hu hp₁ h₁ h₂ w w'
  obtain ⟨B₁, B⟩ := p
  simp only at hsq hu hp₁ h₁ h₂ ⊢
  set R := morseCongruence B₁ B with hRdef
  -- The comparison operator `C = B₁⁻¹ ∘ B` is self-adjoint for `B₁`.
  have hC (w w' : E) : B₁ ((B₁.inverse ∘L B) w) w' = B w w' := by
    simp [hp₁.self_apply_inverse]
  have hCadj : pairingAdjoint B₁ (B₁.inverse ∘L B) = B₁.inverse ∘L B :=
    ext_of_pairing hp₁ fun w w' ↦ by rw [pairingAdjoint_apply hp₁, h₁, hC, hC, h₂]
  -- Hence so is its square root `R`.
  have hR : pairingAdjoint B₁ R = R := by
    rw [← hu, ← pairingAdjoint_mul hp₁, hsq, hCadj, hRdef, morseCongruence_def]
  calc B₁ (R w) (R w') = B₁ (pairingAdjoint B₁ R w) (R w') := by rw [hR]
    _ = B₁ w ((R * R) w') := by rw [pairingAdjoint_apply hp₁, mul_apply_eq_comp]
    _ = B w w' := by rw [hsq, h₁, hC, h₂]

/-- A `C^n` family `B` of symmetric continuous bilinear forms on a Banach space whose value at
`a` is invertible is, near `a`, the congruence of that value by a `C^n` family of continuous
linear operators equal to the identity at `a`: there is `R` with `R a = 1` and
`B₀ (R v w) (R v w') = B v w w'`. The parameter space `F` is independent of the Banach
space `E` on which the forms act. In particular, continuity of the family suffices to obtain
continuous congruences. The operators are the canonical congruences
`TauCeti.morseCongruence (B a) (B v)`. -/
theorem exists_congruence_of_symmetric_family
    {n : ℕ∞ω} {a : F} {B : F → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContDiff ℝ n B)
    (hsymm : ∀ v w w', B v w w' = B v w' w)
    (B₀ : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hB₀ : (B₀ : E →L[ℝ] E →L[ℝ] ℝ) = B a) :
    ∃ (R : F → (E →L[ℝ] E)) (U : Set F), IsOpen U ∧ a ∈ U ∧ R a = 1 ∧
      ContDiffOn ℝ n R U ∧ ∀ v ∈ U, ∀ w w', B₀ (R v w) (R v w') = B v w w' := by
  have hBa : (B a).IsInvertible := ⟨B₀, hB₀⟩
  have hpair : ContDiff ℝ n fun v ↦ (B a, B v) := contDiff_const.prodMk hB
  have hT : Tendsto (fun v ↦ (B a, B v)) (𝓝 a) (𝓝 (B a, B a)) :=
    hpair.continuous.tendsto a
  let R : F → E →L[ℝ] E := fun v ↦ morseCongruence (B a) (B v)
  have hS : {v | ContDiffAt ℝ n R v ∧ ∀ w w', B₀ (R v w) (R v w') = B v w w'} ∈ 𝓝 a := by
    filter_upwards [hT.eventually (eventually_contDiffAt_morseCongruence hBa (n := n)),
      hT.eventually (eventually_morseCongruence_apply hBa)] with v hv hv'
    refine ⟨ContDiffAt.comp (g := fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
      morseCongruence p.1 p.2) v hv hpair.contDiffAt, fun w w' ↦ ?_⟩
    rw [show ⇑B₀ = ⇑(B a) by rw [← hB₀, ContinuousLinearEquiv.coe_coe]]
    exact hv' (hsymm a) (hsymm v) w w'
  refine ⟨R, interior _, isOpen_interior, mem_interior_iff_mem_nhds.mpr hS,
    morseCongruence_self hBa, fun v hv ↦ (interior_subset hv).1.contDiffWithinAt,
    fun v hv ↦ (interior_subset hv).2⟩

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **Congruence with a varying reference form.** A jointly `C^n` symmetric family `B (b, v)`
whose value at `(a, 0)` is invertible is, on a product neighbourhood, congruent to `B (b, 0)`
by jointly `C^n` invertible operators. The operators are the identity on the entire zero
section in that neighbourhood, and their inverses are jointly `C^n` there as well.

The parameter spaces `P` and `F` need not be complete or finite-dimensional. No definiteness
or constant-signature hypothesis is required. -/
theorem exists_parametric_congruence_of_symmetric_family
    {n : ℕ∞ω} {a : P} {B : P × F → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiff ℝ n B) (hsymm : ∀ z w w', B z w w' = B z w' w)
    (hBa : (B (a, 0)).IsInvertible) :
    ∃ (R : P × F → E →L[ℝ] E) (U : Set P) (V : Set F),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ (0 : F) ∈ V ∧
      (∀ b ∈ U, R (b, 0) = 1) ∧ ContDiffOn ℝ n R (U ×ˢ V) ∧
      ContDiffOn ℝ n (fun z ↦ (R z).inverse) (U ×ˢ V) ∧
      (∀ z ∈ U ×ˢ V, (R z).IsInvertible) ∧
      ∀ z ∈ U ×ˢ V, ∀ w w', B (z.1, 0) (R z w) (R z w') = B z w w' := by
  obtain ⟨A, hA⟩ := hBa
  obtain ⟨T, W, hW, haW, hTa, hT, hspec⟩ :=
    exists_congruence_of_symmetric_family hB hsymm A hA
  -- Shrink to a product neighbourhood where the fixed-reference operators are invertible.
  have hTa_inv : (T (a, 0)).IsInvertible := by
    rw [hTa]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  have hnear : ∀ᶠ z in 𝓝 (a, (0 : F)), (T z).IsInvertible :=
    (hT.continuousOn.continuousAt (hW.mem_nhds haW)).eventually hTa_inv.eventually_nhds
  obtain ⟨U, V, hU, haU, hV, h0V, hUV⟩ :=
    mem_nhds_prod_iff'.mp (Filter.inter_mem (hW.mem_nhds haW) hnear)
  have hsub : U ×ˢ V ⊆ W := fun z hz ↦ (hUV hz).1
  have hTi (z : P × F) (hz : z ∈ U ×ˢ V) : (T z).IsInvertible := (hUV hz).2
  let S : P × F → E →L[ℝ] E := fun z ↦ T (z.1, 0)
  have hS : ContDiffOn ℝ n S (U ×ˢ V) :=
    hT.comp (contDiffOn_fst.prodMk contDiffOn_const)
      (fun z hz ↦ hsub ⟨hz.1, h0V⟩)
  have hSi (z : P × F) (hz : z ∈ U ×ˢ V) : (S z).IsInvertible :=
    hTi (z.1, 0) ⟨hz.1, h0V⟩
  have hSinv : ContDiffOn ℝ n (fun z ↦ (S z).inverse) (U ×ˢ V) := by
    intro z hz
    exact (hSi z hz).contDiffAt_map_inverse.comp_contDiffWithinAt z (hS z hz)
  let R : P × F → E →L[ℝ] E := fun z ↦ (S z).inverse.comp (T z)
  have hR : ContDiffOn ℝ n R (U ×ˢ V) := hSinv.clm_comp (hT.mono hsub)
  have hRi (z : P × F) (hz : z ∈ U ×ˢ V) : (R z).IsInvertible :=
    (hSi z hz).inverse.comp (hTi z hz)
  refine ⟨R, U, V, hU, hV, haU, h0V, ?_, hR, ?_, hRi, ?_⟩
  · intro b hb
    exact (hTi (b, 0) ⟨hb, h0V⟩).inverse_comp_self
  · intro z hz
    exact (hRi z hz).contDiffAt_map_inverse.comp_contDiffWithinAt z (hR z hz)
  · intro z hz w w'
    -- Divide by the zero-section operator on both arguments of the reference form.
    calc
      B (z.1, 0) (R z w) (R z w') =
          A (S z (R z w)) (S z (R z w')) :=
        (hspec (z.1, 0) (hsub ⟨hz.1, h0V⟩) _ _).symm
      _ = A (T z w) (T z w') := by
        simp only [R, ContinuousLinearMap.comp_apply, (hSi z hz).self_apply_inverse]
      _ = B z w w' := hspec z (hsub hz) w w'

end Congruence

section MorseLemma

variable [CompleteSpace E] {f : E → ℝ} {n : ℕ∞}

/-- **The Morse lemma.** Near a nondegenerate critical point `x` of a `C^{n+2}` function `f`,
with `1 ≤ n ≤ ∞`, there is a `C^n` map `φ`, fixing `0` and with derivative the identity there,
in terms of which `f` is exactly its Hessian quadratic form:
`f (x + v) = f x + 2⁻¹ * fderiv ℝ (fderiv ℝ f) x (φ v) (φ v)` for `v` near `0`.

`TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart` repackages this as a chart at
`x`. -/
theorem IsNondegenerateCriticalPoint.exists_normal_form (hf : ContDiff ℝ (n + 2) f)
    (h : IsNondegenerateCriticalPoint f x) (hn : n ≠ 0) :
    ∃ (φ : E → E) (U : Set E), IsOpen U ∧ 0 ∈ U ∧ φ 0 = 0 ∧ ContDiffOn ℝ n φ U ∧
      HasFDerivAt φ (ContinuousLinearMap.id ℝ E) 0 ∧ ∀ v ∈ U,
      f (x + v) = f x + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ f) x (φ v) (φ v) := by
  have hf₂ : ContDiff ℝ 2 f := hf.of_le le_add_self
  obtain ⟨B₀, hB₀⟩ := h.isInvertible
  obtain ⟨R, U, hUopen, h0U, hR0, hRsmooth, hRspec⟩ :=
    exists_congruence_of_symmetric_family (a := (0 : E)) (B := hessianAverage f x)
      (contDiff_hessianAverage hf x)
      (fun v w w' ↦ hessianAverage_symm hf₂ x v w w') B₀
      (by rw [hB₀, hessianAverage_zero])
  have hRsmoothAt : ContDiffAt ℝ n R 0 :=
    (hRsmooth 0 h0U).contDiffAt (hUopen.mem_nhds h0U)
  have hφsmooth : ContDiffOn ℝ n (fun v ↦ R v v) U :=
    hRsmooth.clm_apply contDiffOn_id
  refine ⟨fun v ↦ R v v, U, hUopen, h0U, by simp [hR0], hφsmooth, ?_, ?_⟩
  · have hd : HasFDerivAt (fun v ↦ R v v)
        ((R 0).comp (ContinuousLinearMap.id ℝ E) + (fderiv ℝ R 0).flip 0) 0 :=
      ((hRsmoothAt.differentiableAt (by simpa using hn)).hasFDerivAt).clm_apply
        (hasFDerivAt_id (𝕜 := ℝ) (0 : E))
    have he : (R 0).comp (ContinuousLinearMap.id ℝ E) + (fderiv ℝ R 0).flip 0
        = ContinuousLinearMap.id ℝ E := by
      rw [hR0]
      ext w
      simp
    rw [← he]
    exact hd
  · intro v hv
    rw [map_add_eq_add_hessianAverage hf₂, ← hRspec v hv v v, ← hB₀]
    simp [h.fderiv_eq_zero]

/-- **The Morse lemma, as a chart.** At a nondegenerate critical point `x` of a `C^{n+2}`
function `f`, with `1 ≤ n ≤ ∞`, there is a chart `ψ` sending `x` to `0`, `C^n` in both
directions, on whose whole source `f` is its Hessian quadratic form read in that chart. -/
theorem IsNondegenerateCriticalPoint.exists_morse_chart (hf : ContDiff ℝ (n + 2) f)
    (h : IsNondegenerateCriticalPoint f x) (hn : n ≠ 0) :
    ∃ ψ : OpenPartialHomeomorph E E, x ∈ ψ.source ∧ ψ x = 0 ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ y ∈ ψ.source, f y = f x + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ f) x (ψ y) (ψ y) := by
  obtain ⟨φ, U, hUopen, h0U, hφ0, hφsmooth, hφderiv, hφeq⟩ := h.exists_normal_form hf hn
  have hn' : (n : ℕ∞ω) ≠ 0 := by simpa using hn
  let V : Set E := (fun y ↦ y - x) ⁻¹' U
  have hVopen : IsOpen V := hUopen.preimage (by fun_prop)
  have hxV : x ∈ V := by simp [V, h0U]
  have hΦsmoothOn : ContDiffOn ℝ n (φ ∘ fun y : E ↦ y - x) V :=
    hφsmooth.comp (by fun_prop) fun _ hy ↦ hy
  have hΦsmoothAt {y : E} (hy : y ∈ V) : ContDiffAt ℝ n (φ ∘ fun y : E ↦ y - x) y :=
    (hΦsmoothOn y hy).contDiffAt (hVopen.mem_nhds hy)
  have hΦderiv : HasFDerivAt (φ ∘ fun y : E ↦ y - x)
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) x := by
    simpa using HasFDerivAt.comp x (by simpa using hφderiv) (hasFDerivAt_sub_const (𝕜 := ℝ) x)
  have hgood : {y | y ∈ V ∧ ∃ e : E ≃L[ℝ] E,
      (e : E →L[ℝ] E) = fderiv ℝ (φ ∘ fun y : E ↦ y - x) y} ∈ 𝓝 x := by
    have ht := ((hΦsmoothAt hxV).continuousAt_fderiv hn').tendsto
    rw [hΦderiv.fderiv] at ht
    exact Filter.inter_mem (hVopen.mem_nhds hxV)
      (ht.eventually (ContinuousLinearEquiv.refl ℝ E).nhds)
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.1 hgood
  let p := (hΦsmoothAt hxV).toOpenPartialHomeomorph _ hΦderiv hn'
  let ψ := p.restrOpen W hWopen
  have hψsrc : ψ.source = p.source ∩ W := p.restrOpen_source W hWopen
  have hψ : ⇑ψ = φ ∘ fun y : E ↦ y - x := by
    rw [OpenPartialHomeomorph.coe_restrOpen, ContDiffAt.toOpenPartialHomeomorph_coe]
  refine ⟨ψ, hψsrc ▸ ⟨(hΦsmoothAt hxV).mem_toOpenPartialHomeomorph_source hΦderiv hn', hxW⟩,
    by simp [hψ, hφ0], ?_, fun z hz ↦ ?_, ?_⟩
  · rw [hψ, hψsrc]
    exact hΦsmoothOn.mono fun z hz ↦ (hWsub hz.2).1
  · obtain ⟨hyV, e, he⟩ := hWsub (hψsrc ▸ ψ.map_target hz).2
    refine (ψ.contDiffAt_symm hz (f₀' := e) ?_ (hψ ▸ hΦsmoothAt hyV)).contDiffWithinAt
    rw [hψ, he]
    exact ((hΦsmoothAt hyV).differentiableAt hn').hasFDerivAt
  · rw [hψsrc, hψ]
    exact fun y hy ↦ by simpa using hφeq (y - x) (hWsub hy.2).1

end MorseLemma

end TauCeti
