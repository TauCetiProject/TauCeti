/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import TauCeti.Analysis.Normed.Algebra.SquareRoot
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Sqrt.Basic

/-!
# Analyticity of the square root of strictly positive elements

Let `A` be a Banach algebra over `ℝ` with an isometric continuous functional calculus for its
self-adjoint elements, for instance a C⋆-algebra such as the bounded operators on a Hilbert space,
or the real or complex square matrices with the operator norm of `EuclideanSpace`. This file proves
that the positive square root `CFC.sqrt` is real analytic at every strictly positive element, and so
is the inverse square root `a ↦ (√a)⁻¹`. Since the strictly positive elements need not form an open
subset of `A` (in a complex C⋆-algebra they lie in the real subspace of self-adjoint elements),
analyticity is stated within the set of nonnegative elements: near a strictly positive `a₀`, the
square root agrees on nonnegative elements with a function analytic on a neighbourhood of `a₀`.
Unlike `CFC.contDiffOn_sqrt`, which goes through the logarithm and needs the derivative of the
exponential to be invertible at every self-adjoint element, this needs no hypothesis beyond the
functional calculus.

The local analytic function is a rescaled binomial series. The square root near the identity
`TauCeti.sqrtNearOne` is analytic on the open unit ball about `1`, and on the nonnegative elements
of this ball it is the positive square root (`CFC.sqrt_eq_sqrtNearOne`): for the function `f = id`
on the spectrum of `a`, the binomial series of `f` converges in the Banach algebra of continuous
functions on the spectrum to the real square root, and the continuous functional calculus, a
continuous algebra homomorphism, carries it to the binomial series of `a`. A strictly positive
`a₀` has its spectrum in `(0, ‖a₀‖]`, so `c • a₀` lies in the unit ball about `1` for
`c = (‖a₀‖ + 1)⁻¹` (`IsStrictlyPositive.exists_norm_smul_sub_one_lt_one`), and so does `c • a` for
every `a` near `a₀`. On these elements `√a = (√c)⁻¹ • sqrtNearOne (c • a)`
(`CFC.sqrt_eq_inv_sqrt_smul_sqrtNearOne`). Different choices of `c` give the same function on
nonnegative elements, since each of them computes the positive square root; this uniqueness is what
glues the local power series into the single map `CFC.sqrt`.

Analyticity gives smoothness of every order, and with it smooth families `y ↦ √(f y)` of strictly
positive elements, such as the square roots of the Gram operators of smooth frames of a vector
bundle with a fibre metric. No eigenvectors are chosen, so no smooth eigenbasis is needed.

## Main statements

* `CFC.sqrt_eq_sqrtNearOne`: on nonnegative elements at distance less than `1` from `1`, the
  positive square root is the binomial series.
* `CFC.analyticWithinAt_sqrt`, `CFC.analyticOn_sqrt`: the positive square root is analytic at
  strictly positive elements.
* `CFC.contDiffWithinAt_sqrt`: it is smooth there, of every order.
* `CFC.analyticWithinAt_ringInverse_sqrt`, `CFC.analyticOn_ringInverse_sqrt`: the same for the
  inverse square root.
* `ContDiffWithinAt.cfcSqrt`, `ContDiffOn.cfcSqrt`, `ContDiff.cfcSqrt`: square roots of smooth
  families of strictly positive elements are smooth.

## References

* N. J. Higham, *Functions of Matrices: Theory and Computation*, SIAM (2008), Chapter 6.
-/

public section

open Filter Topology
open scoped NNReal ContinuousFunctionalCalculus Ring

namespace CFC

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- **The positive square root is the binomial series near the identity.** For a nonnegative
element `a` with `‖a - 1‖ < 1`, the positive square root `CFC.sqrt a` is the sum
`TauCeti.sqrtNearOne A a = ∑ₙ (1/2 choose n) (a - 1)ⁿ` of the binomial series. -/
theorem sqrt_eq_sqrtNearOne {a : A} (ha : 0 ≤ a) (h : ‖a - 1‖ < 1) :
    sqrt a = TauCeti.sqrtNearOne A a := by
  have hsa : IsSelfAdjoint a := ha.isSelfAdjoint
  -- The continuous functional calculus of `a`, as a continuous algebra homomorphism.
  let φ : C(spectrum ℝ a, ℝ) →A[ℝ] A := ⟨(cfcHom hsa).toAlgHom, cfcHom_continuous hsa⟩
  let f : C(spectrum ℝ a, ℝ) := (ContinuousMap.id ℝ).restrict (spectrum ℝ a)
  have hφf : φ f = a := cfcHom_id hsa
  have hf : ‖f - 1‖ < 1 := by
    rwa [← norm_cfcHom a (f - 1) hsa, map_sub, map_one, cfcHom_id]
  -- On the spectrum, the binomial series of `f` sums to the real square root `g`.
  let g : C(spectrum ℝ a, ℝ) := ⟨fun x ↦ √(x : ℝ), by fun_prop⟩
  have hsq : TauCeti.sqrtNearOne _ f = g := by
    ext x
    have hx : |(x : ℝ) - 1| < 1 := by
      simpa [f] using (ContinuousMap.norm_coe_le_norm (f - 1) x).trans_lt hf
    let ev : C(spectrum ℝ a, ℝ) →A[ℝ] ℝ :=
      ⟨ContinuousMap.evalAlgHom ℝ ℝ x, continuous_eval_const x⟩
    have hev : ∀ y, ev y = y x := fun _ ↦ rfl
    simpa [hev, f, g, TauCeti.sqrtNearOne_real_eq_sqrt hx] using ev.map_sqrtNearOne hf
  calc sqrt a = φ g := by
        rw [sqrt_eq_real_sqrt a ha, cfcₙ_eq_cfc, cfc_apply Real.sqrt a]
        -- `φ` is `cfcHom hsa` as a continuous algebra homomorphism, and `g` is the restriction
        -- of `Real.sqrt` to the spectrum that `cfc_apply` produces.
        rfl
    _ = TauCeti.sqrtNearOne A a := by rw [← hsq, φ.map_sqrtNearOne hf, hφf]

/-- **The positive square root as a rescaled binomial series.** If `c > 0` and the nonnegative
element `a` satisfies `‖c • a - 1‖ < 1`, then `√a = (√c)⁻¹ • ∑ₙ (1/2 choose n) (c • a - 1)ⁿ`. -/
theorem sqrt_eq_inv_sqrt_smul_sqrtNearOne {a : A} (ha : 0 ≤ a) {c : ℝ} (hc : 0 < c)
    (h : ‖c • a - 1‖ < 1) : sqrt a = (√c)⁻¹ • TauCeti.sqrtNearOne A (c • a) := by
  rw [← sqrt_eq_sqrtNearOne (CFC.smul_nonneg hc.le ha) h, sqrt_smul hc.le, smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.2 hc).ne', one_smul]

end CFC

namespace IsStrictlyPositive

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- A strictly positive element has a positive multiple at distance less than `1` from `1`. One
can take the multiple `(‖a‖ + 1)⁻¹`, which puts the spectrum into `(0, 1)`. -/
theorem exists_norm_smul_sub_one_lt_one {a : A} (ha : IsStrictlyPositive a) :
    ∃ c : ℝ, 0 < c ∧ ‖c • a - 1‖ < 1 := by
  have hsa : IsSelfAdjoint a := ha.nonneg.isSelfAdjoint
  set c : ℝ := (‖a‖ + 1)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, ?_⟩
  have heq : cfc (fun x : ℝ ↦ c * x - 1) a = c • a - 1 := by
    rw [cfc_sub _ _ a, cfc_const_mul_id c a, cfc_const_one ℝ a]
  rw [← heq]
  refine norm_cfc_lt one_pos fun x hx ↦ ?_
  have hx0 : 0 < x := (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos a).1 ha x hx
  have hxa : x ≤ ‖a‖ :=
    (le_abs_self x).trans (IsometricContinuousFunctionalCalculus.norm_spectrum_le a hx)
  have hcx : c * x < 1 := by
    rw [hc, inv_mul_lt_iff₀ (by positivity)]
    linarith
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> nlinarith

end IsStrictlyPositive

namespace CFC

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- **The positive square root is analytic at strictly positive elements**, within the
nonnegative elements: near a strictly positive `a`, it agrees on nonnegative elements with a
function analytic on a neighbourhood of `a`. -/
theorem analyticWithinAt_sqrt {a : A} (ha : IsStrictlyPositive a) :
    AnalyticWithinAt ℝ sqrt {b : A | 0 ≤ b} a := by
  obtain ⟨c, hc, hca⟩ := ha.exists_norm_smul_sub_one_lt_one
  have hg : AnalyticAt ℝ (fun b : A ↦ (√c)⁻¹ • TauCeti.sqrtNearOne A (c • b)) a := by
    have h1 : AnalyticAt ℝ (TauCeti.sqrtNearOne A) (c • a) :=
      TauCeti.analyticOnNhd_sqrtNearOne _ (by rwa [Metric.mem_ball, dist_eq_norm])
    have h2 : AnalyticAt ℝ (fun b : A ↦ c • b) a := by fun_prop
    exact (analyticAt_const (v := (√c)⁻¹)).smul (h1.comp h2)
  have hev : ∀ᶠ b in 𝓝 a, ‖c • b - 1‖ < 1 :=
    ((continuous_const.smul continuous_id).sub continuous_const).norm.continuousAt.eventually_lt
      continuousAt_const hca
  refine hg.analyticWithinAt.congr_of_eventuallyEq ?_
    (sqrt_eq_inv_sqrt_smul_sqrtNearOne ha.nonneg hc hca)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with b hb hb0
  exact sqrt_eq_inv_sqrt_smul_sqrtNearOne hb0 hc hb

/-- **The positive square root is analytic on the strictly positive elements.** -/
theorem analyticOn_sqrt : AnalyticOn ℝ sqrt {a : A | IsStrictlyPositive a} :=
  fun _ ha ↦ (analyticWithinAt_sqrt ha).mono fun _ hb ↦ hb.nonneg

/-- **The positive square root is smooth at strictly positive elements**, of every order, within
the nonnegative elements. -/
theorem contDiffWithinAt_sqrt {n : WithTop ℕ∞} {a : A} (ha : IsStrictlyPositive a) :
    ContDiffWithinAt ℝ n sqrt {b : A | 0 ≤ b} a :=
  (analyticWithinAt_sqrt ha).contDiffWithinAt

/-- **The inverse square root is analytic at strictly positive elements**, within the nonnegative
elements. By `CFC.sqrt_ringInverse` it is also the square root of the inverse. -/
theorem analyticWithinAt_ringInverse_sqrt {a : A} (ha : IsStrictlyPositive a) :
    AnalyticWithinAt ℝ (fun b : A ↦ (sqrt b)⁻¹ʳ) {b : A | 0 ≤ b} a := by
  have hinv : AnalyticAt ℝ Ring.inverse (sqrt a) := by
    simpa using analyticAt_inverse (𝕜 := ℝ) (ha.sqrt a).isUnit.unit
  exact hinv.comp_analyticWithinAt (analyticWithinAt_sqrt ha)

/-- **The inverse square root is analytic on the strictly positive elements.** -/
theorem analyticOn_ringInverse_sqrt :
    AnalyticOn ℝ (fun a : A ↦ (sqrt a)⁻¹ʳ) {a : A | IsStrictlyPositive a} :=
  fun _ ha ↦ (analyticWithinAt_ringInverse_sqrt ha).mono fun _ hb ↦ hb.nonneg

end CFC

section Family

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞} {f : E → A} {s : Set E}
  {x : E}

/-- The square roots of a family of elements, smooth within `s` at `x`, are smooth within `s` at
`x` when `f x` is strictly positive and `f` is nonnegative near `x` in `s`. -/
theorem ContDiffWithinAt.cfcSqrt (hf : ContDiffWithinAt ℝ n f s x)
    (hs : ∀ᶠ y in 𝓝[s] x, 0 ≤ f y) (hx : IsStrictlyPositive (f x)) :
    ContDiffWithinAt ℝ n (fun y ↦ CFC.sqrt (f y)) s x :=
  (CFC.contDiffWithinAt_sqrt hx).comp_of_preimage_mem_nhdsWithin x hf hs

/-- The square roots of a smooth family of strictly positive elements form a smooth family. -/
theorem ContDiffOn.cfcSqrt (hf : ContDiffOn ℝ n f s) (hs : ∀ y ∈ s, IsStrictlyPositive (f y)) :
    ContDiffOn ℝ n (fun y ↦ CFC.sqrt (f y)) s :=
  CFC.analyticOn_sqrt.contDiffOn_of_completeSpace.comp hf hs

/-- The square roots of a smooth family of strictly positive elements form a smooth family. -/
theorem ContDiff.cfcSqrt (hf : ContDiff ℝ n f) (hs : ∀ y, IsStrictlyPositive (f y)) :
    ContDiff ℝ n (fun y ↦ CFC.sqrt (f y)) :=
  contDiffOn_univ.1 (hf.contDiffOn.cfcSqrt fun y _ ↦ hs y)

end Family

