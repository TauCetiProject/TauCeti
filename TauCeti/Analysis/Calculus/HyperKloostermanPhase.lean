/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.DivNearOne
import TauCeti.Analysis.SpecialFunctions.Complex.Log.SumNearOne
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The phase `∑ₖ xₖ + D / ∏ₖ xₖ`: critical points and Hessian

For a field `𝕜`, a finite index type `ι` with `n` elements and `D : 𝕜`, the
*hyper-Kloosterman phase* is

  `g_D(x) = ∑ₖ xₖ + D / ∏ₖ xₖ`,

a function on `(𝕜ˣ)ⁿ`, written here on all of `ι → 𝕜` (where some `xₖ = 0` the quotient is `0`
by convention). It is the phase of the oscillatory integrals whose stationary-phase evaluation
over `ℂ` and over non-archimedean fields gives the archimedean and `p`-adic analogues of the
hyper-Kloosterman sums `TauCeti.hyperKloosterman`.

On `(𝕜ˣ)ⁿ` its partial derivatives are `∂ₖ g_D(x) = 1 - D / (xₖ ∏ᵢ xᵢ)`
(`TauCeti.hyperKloostermanPhaseGrad`), the critical points are the diagonal points `(z, …, z)`
with `z ^ (n + 1) = D`, the value there is `(n + 1) z`, the Hessian there is
`z⁻¹ (1 + 𝟙𝟙ᵀ)` and its determinant is `(n + 1) / zⁿ`. Over `ℂ`, a point where every partial
derivative is smaller than `η ≤ 1/3` in modulus lies within `6 η |z|` of such a critical point in
every coordinate; hence the gradient is bounded below away from the critical points, uniformly in
`D` in a bounded set.

## Main definitions

* `TauCeti.hyperKloostermanPhase D x`: the phase `∑ₖ xₖ + D / ∏ₖ xₖ`.
* `TauCeti.hyperKloostermanPhaseGrad D x k`: its `k`-th partial derivative `1 - D / (xₖ ∏ᵢ xᵢ)`.

## Main statements

* `TauCeti.hasFDerivAt_hyperKloostermanPhase`: the Fréchet derivative on `(𝕜ˣ)ⁿ`, with
  `TauCeti.fderiv_hyperKloostermanPhase_apply_single` for the partial derivatives.
* `TauCeti.hyperKloostermanPhaseGrad_eq_zero_iff`,
  `TauCeti.fderiv_hyperKloostermanPhase_eq_zero_iff`: the critical points are the points
  `(z, …, z)` with `z ^ (n + 1) = D`.
* `TauCeti.hyperKloostermanPhase_const`: the value `(n + 1) z` there.
* `TauCeti.hasFDerivAt_hyperKloostermanPhaseGrad`,
  `TauCeti.iteratedFDeriv_hyperKloostermanPhase_single`: the second partial derivatives
  `∂ⱼ∂ₖ g_D(x) = D (δⱼₖ + 1) / (xⱼ xₖ ∏ᵢ xᵢ)`.
* `TauCeti.of_iteratedFDeriv_hyperKloostermanPhase_const`,
  `TauCeti.det_of_iteratedFDeriv_hyperKloostermanPhase_const`: at a critical point the Hessian
  is `z⁻¹ (1 + 𝟙𝟙ᵀ)`, of determinant `(n + 1) / zⁿ`.
* `TauCeti.exists_pow_eq_norm_sub_le_of_norm_hyperKloostermanPhaseGrad_lt`: over `ℂ`, if
  `η ≤ 1/3` and `|∂ₖ g_D(x)| < η` for all `k`, some `z` with `z ^ (n + 1) = D` has
  `|xₖ - z| ≤ 6 η |z|` for all `k`.
* `TauCeti.exists_pos_le_norm_hyperKloostermanPhaseGrad`: over `ℂ`, for `D` in a bounded set and
  `x` at sup-distance at least `δ > 0` from every critical point, the gradient has sup norm at
  least some `c > 0`.

## References

The statements are those of the critical-point lemmas
`Formalism.FourierDecayAlt.G.PhaseFunctionCritical`, `Formalism.FourierDecayAlt.G.HessCrit`,
`Formalism.FourierDecayAlt.G.HessDet` and `Formalism.FourierDecayAlt.G.GradLower`
(`Formalism/HermitianCurvature/StatementG.lean`) and
`Formalism.FourierDecayAlt.P.G1.gradSmall6`
(`Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean`) of
L. Alpöge's Lean formalization of the Riemann hypothesis for Dirichlet L-functions,
https://github.com/leanprover-community/riemann-hypothesis.
-/

public section

open Finset Matrix ContinuousLinearMap Topology Filter

namespace TauCeti

variable {ι 𝕜 : Type*} [Fintype ι]

section Field

variable [Field 𝕜]

/-- The *hyper-Kloosterman phase* `g_D(x) = ∑ₖ xₖ + D / ∏ₖ xₖ`. It is meant on `(𝕜ˣ)ⁿ`; where
some `xₖ = 0` the quotient is `0`. -/
def hyperKloostermanPhase (D : 𝕜) (x : ι → 𝕜) : 𝕜 :=
  ∑ k, x k + D / ∏ k, x k

/-- The defining formula of `TauCeti.hyperKloostermanPhase`. -/
theorem hyperKloostermanPhase_apply (D : 𝕜) (x : ι → 𝕜) :
    hyperKloostermanPhase D x = ∑ k, x k + D / ∏ k, x k := by
  rw [hyperKloostermanPhase]

/-- The `k`-th partial derivative `1 - D / (xₖ ∏ᵢ xᵢ)` of the hyper-Kloosterman phase
(`TauCeti.fderiv_hyperKloostermanPhase_apply_single`), as a function of `x` on all of `ι → 𝕜`.
Where some `xᵢ = 0` it is `1`. -/
def hyperKloostermanPhaseGrad (D : 𝕜) (x : ι → 𝕜) (k : ι) : 𝕜 :=
  1 - D / (x k * ∏ i, x i)

/-- The defining formula of `TauCeti.hyperKloostermanPhaseGrad`. -/
theorem hyperKloostermanPhaseGrad_apply (D : 𝕜) (x : ι → 𝕜) (k : ι) :
    hyperKloostermanPhaseGrad D x k = 1 - D / (x k * ∏ i, x i) := by
  rw [hyperKloostermanPhaseGrad]

/-- For `D = 0` the phase is the linear form `∑ₖ xₖ`. -/
@[simp]
theorem hyperKloostermanPhase_zero (x : ι → 𝕜) : hyperKloostermanPhase 0 x = ∑ k, x k := by
  simp [hyperKloostermanPhase]

/-- For `D = 0` every partial derivative is `1`. -/
@[simp]
theorem hyperKloostermanPhaseGrad_zero (x : ι → 𝕜) (k : ι) :
    hyperKloostermanPhaseGrad 0 x k = 1 := by
  simp [hyperKloostermanPhaseGrad]

/-- At a diagonal point `(z, …, z)` with `z ^ (n + 1) = D` the phase takes the value
`(n + 1) z`. -/
theorem hyperKloostermanPhase_const {D z : 𝕜} (hz : z ^ (Fintype.card ι + 1) = D) :
    hyperKloostermanPhase D (fun _ : ι ↦ z) = (Fintype.card ι + 1) * z := by
  subst hz
  rcases eq_or_ne z 0 with rfl | hz
  · simp [hyperKloostermanPhase]
  · simp only [hyperKloostermanPhase, sum_const, card_univ, nsmul_eq_mul, prod_const]
    field_simp
    ring

/-- **The critical points of the hyper-Kloosterman phase.** On `(𝕜ˣ)ⁿ`, all partial derivatives
of `g_D` vanish at `x` exactly when `x = (z, …, z)` with `z ^ (n + 1) = D`. -/
theorem hyperKloostermanPhaseGrad_eq_zero_iff {D : 𝕜} {x : ι → 𝕜} (hx : ∀ i, x i ≠ 0) :
    (∀ k, hyperKloostermanPhaseGrad D x k = 0) ↔
      ∃ z, z ^ (Fintype.card ι + 1) = D ∧ x = fun _ ↦ z := by
  have hP : ∏ i, x i ≠ 0 := prod_ne_zero_iff.2 fun i _ ↦ hx i
  simp only [hyperKloostermanPhaseGrad, sub_eq_zero, eq_comm (a := (1 : 𝕜)),
    div_eq_one_iff_eq (mul_ne_zero (hx _) hP)]
  constructor
  · intro h
    cases isEmpty_or_nonempty ι with
    | inl _ => exact ⟨D, by simp, Subsingleton.elim _ _⟩
    | inr hne =>
      obtain ⟨k₀⟩ := hne
      have hconst : x = fun _ ↦ x k₀ :=
        funext fun k ↦ mul_right_cancel₀ hP ((h k).symm.trans (h k₀))
      refine ⟨x k₀, ?_, hconst⟩
      rw [h k₀, pow_succ', hconst]
      simp
  · rintro ⟨z, rfl, rfl⟩ k
    simp [pow_succ']

/-- The second partial derivatives `D (δⱼₖ + 1) / (xⱼ xₖ ∏ᵢ xᵢ)` at `x = (z, …, z)` with
`z ^ (n + 1) = D` form the matrix `z⁻¹ (1 + 𝟙𝟙ᵀ)`. -/
private theorem of_hessian_const [DecidableEq ι] {D z : 𝕜} (hz : z ^ (Fintype.card ι + 1) = D) :
    (Matrix.of fun j k : ι ↦ D * ((1 : Matrix ι ι 𝕜) j k + 1) / (z * z * ∏ _ : ι, z)) =
      z⁻¹ • (1 + Matrix.of fun _ _ ↦ 1) := by
  subst hz
  ext j k
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · simp only [of_apply, prod_const, card_univ, Matrix.smul_apply, Matrix.add_apply,
      smul_eq_mul]
    field_simp
    ring

end Field

section Deriv

variable [NontriviallyNormedField 𝕜] {x : ι → 𝕜}

/-- **The derivative of the hyper-Kloosterman phase.** On `(𝕜ˣ)ⁿ`, the Fréchet derivative of
`g_D` is `∑ₖ ∂ₖ g_D(x) dxₖ` with `∂ₖ g_D(x) = 1 - D / (xₖ ∏ᵢ xᵢ)`. -/
theorem hasFDerivAt_hyperKloostermanPhase (D : 𝕜) (hx : ∀ i, x i ≠ 0) :
    HasFDerivAt (hyperKloostermanPhase D)
      (∑ k, hyperKloostermanPhaseGrad D x k • (proj k : (ι → 𝕜) →L[𝕜] 𝕜)) x := by
  classical
  have hP : ∏ i, x i ≠ 0 := prod_ne_zero_iff.2 fun i _ ↦ hx i
  have e : hyperKloostermanPhase D = fun y : ι → 𝕜 ↦ ∑ k, y k + D * (∏ k, y k)⁻¹ :=
    funext fun y ↦ by rw [hyperKloostermanPhase_apply, div_eq_mul_inv]
  have h := (HasFDerivAt.fun_sum (u := univ) fun k _ ↦ hasFDerivAt_apply k x).add
    (((hasDerivAt_inv hP).comp_hasFDerivAt x
      (hasFDerivAt_finsetProd (𝕜 := 𝕜) (u := univ) (x := x))).const_mul D)
  rw [e]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  simp only [add_apply, FunLike.coe_sum, Finset.sum_apply, proj_apply, smul_apply, smul_eq_mul,
    hyperKloostermanPhaseGrad_apply, sub_mul, one_mul, sum_sub_distrib, mul_sum]
  rw [sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun i _ ↦ ?_
  have := hx i
  have : ∏ j ∈ univ.erase i, x j ≠ 0 := prod_ne_zero_iff.2 fun j _ ↦ hx j
  rw [← mul_prod_erase univ x (mem_univ i)]
  field_simp

/-- The partial derivatives of the hyper-Kloosterman phase on `(𝕜ˣ)ⁿ`:
`∂ₖ g_D(x) = 1 - D / (xₖ ∏ᵢ xᵢ)`. -/
theorem fderiv_hyperKloostermanPhase_apply_single [DecidableEq ι] (D : 𝕜) (hx : ∀ i, x i ≠ 0)
    (k : ι) :
    fderiv 𝕜 (hyperKloostermanPhase D) x (Pi.single k 1) = hyperKloostermanPhaseGrad D x k := by
  simp [(hasFDerivAt_hyperKloostermanPhase D hx).fderiv, Pi.single_apply]

/-- **The critical points of the hyper-Kloosterman phase**, for the Fréchet derivative: on
`(𝕜ˣ)ⁿ`, `D g_D(x) = 0` exactly when `x = (z, …, z)` with `z ^ (n + 1) = D`. -/
theorem fderiv_hyperKloostermanPhase_eq_zero_iff {D : 𝕜} (hx : ∀ i, x i ≠ 0) :
    fderiv 𝕜 (hyperKloostermanPhase D) x = 0 ↔
      ∃ z, z ^ (Fintype.card ι + 1) = D ∧ x = fun _ ↦ z := by
  classical
  rw [← hyperKloostermanPhaseGrad_eq_zero_iff hx]
  refine ⟨fun h k ↦ ?_, fun h ↦ ?_⟩
  · rw [← fderiv_hyperKloostermanPhase_apply_single D hx k, h, zero_apply]
  · rw [(hasFDerivAt_hyperKloostermanPhase D hx).fderiv]
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp [h]

/-- The derivative of the `k`-th partial derivative `y ↦ 1 - D / (yₖ ∏ᵢ yᵢ)` of the phase on
`(𝕜ˣ)ⁿ`: `∂ⱼ∂ₖ g_D(x) = D (δⱼₖ + 1) / (xⱼ xₖ ∏ᵢ xᵢ)`. -/
theorem hasFDerivAt_hyperKloostermanPhaseGrad [DecidableEq ι] (D : 𝕜) (hx : ∀ i, x i ≠ 0)
    (k : ι) :
    HasFDerivAt (fun y ↦ hyperKloostermanPhaseGrad D y k)
      (∑ j, (D * ((1 : Matrix ι ι 𝕜) j k + 1) / (x j * x k * ∏ i, x i)) •
        (proj j : (ι → 𝕜) →L[𝕜] 𝕜)) x := by
  have hP : ∏ i, x i ≠ 0 := prod_ne_zero_iff.2 fun i _ ↦ hx i
  have e : (fun y ↦ hyperKloostermanPhaseGrad D y k) =
      fun y : ι → 𝕜 ↦ 1 - D * (y k * ∏ i, y i)⁻¹ :=
    funext fun y ↦ by rw [hyperKloostermanPhaseGrad_apply, div_eq_mul_inv]
  have h := (((hasDerivAt_inv (mul_ne_zero (hx k) hP)).comp_hasFDerivAt x
    ((hasFDerivAt_apply k x).fun_mul
      (hasFDerivAt_finsetProd (𝕜 := 𝕜) (u := univ) (x := x)))).const_mul D).const_sub 1
  rw [e]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  have hc : ∀ c, D * ((1 : Matrix ι ι 𝕜) c k + 1) / (x c * x k * ∏ i, x i) * v c =
      (if c = k then D / (x k * ∏ i, x i) * (v k / x k) else 0) +
        D / (x k * ∏ i, x i) * (v c / x c) := by
    intro c
    have := hx c
    have := hx k
    by_cases hck : c = k
    · subst hck
      simp only [Matrix.one_apply_eq, ↓reduceIte]
      field_simp
    · simp only [Matrix.one_apply_ne hck, hck, ↓reduceIte, zero_add]
      field_simp
  have hs : ∑ i, x k * ((∏ j ∈ univ.erase i, x j) * v i) =
      x k * (∏ j, x j) * ∑ i, v i / x i := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    have := hx i
    rw [← mul_prod_erase univ x (mem_univ i)]
    field_simp
  simp only [FunLike.coe_sum, Finset.sum_apply, proj_apply, smul_apply, smul_eq_mul, neg_apply,
    add_apply, mul_sum]
  rw [sum_congr rfl fun c _ ↦ hc c, sum_add_distrib, sum_ite_eq', ite_eq_left (mem_univ k),
    ← mul_sum univ (fun c ↦ v c / x c), hs]
  have := hx k
  field_simp
  ring

/-- At a point with a zero coordinate the second derivative of the phase is `0`: for `D = 0` the
phase is linear, and for `D ≠ 0` its derivative is not continuous there. -/
private theorem iteratedFDeriv_hyperKloostermanPhase_of_eq_zero (D : 𝕜) {k₀ : ι}
    (hk₀ : x k₀ = 0) : iteratedFDeriv 𝕜 2 (hyperKloostermanPhase D) x = 0 := by
  classical
  ext m
  rw [iteratedFDeriv_two_apply]
  rcases eq_or_ne D 0 with rfl | hD
  · set L : (ι → 𝕜) →L[𝕜] 𝕜 := ∑ k, proj k
    have h : hyperKloostermanPhase (0 : 𝕜) = ⇑L := funext fun y ↦ by simp [L]
    have h' : fderiv 𝕜 (hyperKloostermanPhase (0 : 𝕜)) = fun _ ↦ L := by
      rw [h]
      exact funext fun y ↦ L.fderiv
    simp [h']
  suffices hnd : ¬DifferentiableAt 𝕜 (fderiv 𝕜 (hyperKloostermanPhase D)) x by
    simp [fderiv_zero_of_not_differentiableAt hnd]
  -- `y ↦ ∂ₖ₀ g_D(y) · yₖ₀ ∏ᵢ yᵢ` would be continuous at `x` with value `0`, but it is
  -- `yₖ₀ ∏ᵢ yᵢ - D → -D` on the dense set `(𝕜ˣ)ⁿ`.
  intro hd
  set U : Set (ι → 𝕜) := {y | ∀ i, y i ≠ 0}
  have hU : (𝓝[U] x).NeBot := by
    have : U = Set.univ.pi fun _ ↦ {0}ᶜ := by ext; simp [U]
    rw [← mem_closure_iff_nhdsWithin_neBot, this, closure_pi_set]
    simp
  have hP : Continuous fun y : ι → 𝕜 ↦ y k₀ * ∏ i, y i :=
    (continuous_apply k₀).mul (continuous_finsetProd _ fun i _ ↦ continuous_apply i)
  have c1 : ContinuousAt (fun y ↦ fderiv 𝕜 (hyperKloostermanPhase D) y (Pi.single k₀ 1) *
      (y k₀ * ∏ i, y i)) x := (hd.continuousAt.clm_apply continuousAt_const).mul hP.continuousAt
  have c2 : Continuous fun y : ι → 𝕜 ↦ y k₀ * ∏ i, y i - D := hP.sub continuous_const
  have h1 := c1.tendsto.mono_left (nhdsWithin_le_nhds (s := U))
  have h2 := (c2.tendsto x).mono_left (nhdsWithin_le_nhds (s := U))
  simp only [hk₀, zero_mul, mul_zero, zero_sub] at h1 h2
  refine hD (neg_eq_zero.1 (tendsto_nhds_unique (h2.congr' ?_) h1))
  refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
  have : y k₀ * ∏ i, y i ≠ 0 := mul_ne_zero (hy k₀) (prod_ne_zero_iff.2 fun i _ ↦ hy i)
  simp only [fderiv_hyperKloostermanPhase_apply_single D hy, hyperKloostermanPhaseGrad_apply,
    sub_mul, one_mul, div_mul_cancel₀ _ this]

/-- **The second partial derivatives of the hyper-Kloosterman phase.** On `(𝕜ˣ)ⁿ`,
`∂ⱼ∂ₖ g_D(x) = D (δⱼₖ + 1) / (xⱼ xₖ ∏ᵢ xᵢ)`, as the second Fréchet derivative evaluated on the
basis vectors `eⱼ`, `eₖ`. Off `(𝕜ˣ)ⁿ` both sides are `0`. -/
theorem iteratedFDeriv_hyperKloostermanPhase_single [DecidableEq ι] (D : 𝕜) (x : ι → 𝕜)
    (j k : ι) :
    iteratedFDeriv 𝕜 2 (hyperKloostermanPhase D) x ![Pi.single j 1, Pi.single k 1] =
      D * ((1 : Matrix ι ι 𝕜) j k + 1) / (x j * x k * ∏ i, x i) := by
  by_cases hx : ∀ i, x i ≠ 0
  swap
  · push Not at hx
    obtain ⟨i, hi⟩ := hx
    simp [iteratedFDeriv_hyperKloostermanPhase_of_eq_zero D hi, prod_eq_zero (mem_univ i) hi]
  have hU : {y : ι → 𝕜 | ∀ i, y i ≠ 0} ∈ 𝓝 x := by
    rw [Set.ofPred_forall]
    exact (isOpen_iInter_of_finite fun i ↦ isOpen_ne_fun (continuous_apply i)
      continuous_const).mem_nhds (Set.mem_iInter.2 hx)
  have hG := HasFDerivAt.fun_sum (u := univ) fun k _ ↦
    (hasFDerivAt_hyperKloostermanPhaseGrad D hx k).smul_const (proj k : (ι → 𝕜) →L[𝕜] 𝕜)
  have hfd : fderiv 𝕜 (hyperKloostermanPhase D) =ᶠ[𝓝 x]
      fun y ↦ ∑ k, hyperKloostermanPhaseGrad D y k • (proj k : (ι → 𝕜) →L[𝕜] 𝕜) :=
    Filter.mem_of_superset hU fun y hy ↦ (hasFDerivAt_hyperKloostermanPhase D hy).fderiv
  rw [iteratedFDeriv_two_apply, (hG.congr_of_eventuallyEq hfd).fderiv]
  simp [Pi.single_apply]

/-- **The Hessian of the hyper-Kloosterman phase at a critical point.** At `(z, …, z)` with
`z ^ (n + 1) = D`, the matrix of second partial derivatives `∂ⱼ∂ₖ g_D` is `z⁻¹ (1 + 𝟙𝟙ᵀ)`. (For
`z = 0`, which is not in `(𝕜ˣ)ⁿ`, both sides are `0`: then `g_0` is linear.) -/
theorem of_iteratedFDeriv_hyperKloostermanPhase_const [DecidableEq ι] {D z : 𝕜}
    (hz : z ^ (Fintype.card ι + 1) = D) :
    (Matrix.of fun j k : ι ↦ iteratedFDeriv 𝕜 2 (hyperKloostermanPhase D) (fun _ ↦ z)
      ![Pi.single j 1, Pi.single k 1]) = z⁻¹ • (1 + Matrix.of fun _ _ ↦ 1) := by
  rw [← of_hessian_const hz]
  ext j k
  rw [of_apply, of_apply, iteratedFDeriv_hyperKloostermanPhase_single]

/-- **The Hessian determinant of the hyper-Kloosterman phase at a critical point.** At
`(z, …, z)` with `z ^ (n + 1) = D`, the determinant of the matrix of second partial derivatives
is `(n + 1) / zⁿ`. -/
theorem det_of_iteratedFDeriv_hyperKloostermanPhase_const [DecidableEq ι] {D z : 𝕜}
    (hz : z ^ (Fintype.card ι + 1) = D) :
    (Matrix.of fun j k : ι ↦ iteratedFDeriv 𝕜 2 (hyperKloostermanPhase D) (fun _ ↦ z)
      ![Pi.single j 1, Pi.single k 1]).det = (Fintype.card ι + 1) / z ^ Fintype.card ι := by
  have h : (Matrix.of fun _ _ ↦ (1 : 𝕜) : Matrix ι ι 𝕜) =
      replicateCol Unit (fun _ : ι ↦ (1 : 𝕜)) * replicateRow Unit (fun _ : ι ↦ (1 : 𝕜)) := by
    ext; simp [replicateCol, replicateRow, Matrix.mul_apply]
  rw [of_iteratedFDeriv_hyperKloostermanPhase_const hz, det_smul, h,
    det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, inv_pow, div_eq_mul_inv, add_comm, mul_comm]

end Deriv

section Complex

open Complex

/-- **Points of small gradient are near a critical point** (with constant `6`). Over `ℂ`, if
`η ≤ 1/3` and every partial derivative of the hyper-Kloosterman phase at `x` has modulus `< η`,
there is `z` with `z ^ (n + 1) = D` and `‖xₖ - z‖ ≤ 6 η ‖z‖` for all `k`. In particular this holds
for `0 < η ≤ 1 / (4 (n + 1))`. -/
theorem exists_pow_eq_norm_sub_le_of_norm_hyperKloostermanPhaseGrad_lt {D : ℂ} {x : ι → ℂ}
    {η : ℝ} (hη : η ≤ 1 / 3) (h : ∀ k, ‖hyperKloostermanPhaseGrad D x k‖ < η) :
    ∃ z : ℂ, z ^ (Fintype.card ι + 1) = D ∧ ∀ k, ‖x k - z‖ ≤ 6 * η * ‖z‖ := by
  set P := ∏ i, x i with hPdef
  set u : ι → ℂ := fun k ↦ D / (x k * P)
  have hu : ∀ k, ‖u k - 1‖ < η := fun k ↦ by
    rw [norm_sub_rev]; exact h k
  have hu0 : ∀ k, u k ≠ 0 := fun k h0 ↦ by
    have := hu k
    rw [h0, zero_sub, norm_neg, norm_one] at this
    linarith
  have hx : ∀ k, x k ≠ 0 := fun k h0 ↦ hu0 k (by simp [u, h0])
  have hP : P ≠ 0 := prod_ne_zero_iff.2 fun i _ ↦ hx i
  -- `exp L` is the `(n + 1)`-th root of `∏ₖ uₖ` given by the mean of the principal logarithms.
  set L := (∑ k, log (u k)) / (Fintype.card ι + 1)
  have hW : exp L ^ (Fintype.card ι + 1) = ∏ k, u k := by
    rw [← exp_natCast_mul, Nat.cast_add_one, mul_div_cancel₀ _ (Nat.cast_add_one_ne_zero _),
      exp_sum]
    exact prod_congr rfl fun k _ ↦ exp_log (hu0 k)
  have hW0 : exp L ≠ 0 := exp_ne_zero _
  refine ⟨D / P / exp L, ?_, fun k ↦ ?_⟩
  · rcases eq_or_ne D 0 with rfl | hD
    · simp
    rw [div_pow, hW, prod_div_distrib, prod_mul_distrib, prod_const, prod_const, card_univ,
      ← hPdef]
    have := pow_ne_zero (Fintype.card ι) hP
    field_simp
    rw [div_pow, pow_succ, pow_succ]
    field_simp
  · have hη0 : 0 ≤ η := (norm_nonneg _).trans (h k).le
    -- `‖L‖ ≤ 3 η / 2`, the mean of `n` logarithms each of norm at most `3 η / 2`.
    have hL : ‖L‖ ≤ 3 / 2 * η := by
      have hn : ‖(Fintype.card ι : ℂ) + 1‖ = Fintype.card ι + 1 := by exact_mod_cast norm_natCast _
      rw [norm_div, hn, div_le_iff₀ (by positivity)]
      calc ‖∑ i, log (u i)‖ ≤ 3 / 2 * ∑ i, ‖u i - 1‖ :=
            norm_sum_log_le_sum_norm_sub_one fun i _ ↦ by linarith [hu i]
        _ ≤ 3 / 2 * ∑ _i : ι, η := by gcongr with i; exact (hu i).le
        _ ≤ 3 / 2 * η * (Fintype.card ι + 1) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          linarith
    have hb := norm_exp_div_sub_one_le (by linarith) ((hu k).trans_le (by linarith))
    have h6 : (2 * ‖L‖ + ‖u k - 1‖) / (1 - ‖u k - 1‖) ≤ 6 * η := by
      rw [div_le_iff₀ (by linarith [hu k])]
      linarith [hu k, mul_nonneg hη0 (by linarith [hu k] : (0 : ℝ) ≤ 2 - 6 * ‖u k - 1‖)]
    have e : x k - D / P / exp L = D / P / exp L * (exp L / u k - 1) := by
      have := hx k
      have : D ≠ 0 := (div_ne_zero_iff.1 (hu0 k)).1
      simp only [u]
      field_simp
    rw [e, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hb.trans h6) (norm_nonneg _)

/-- **The gradient of the hyper-Kloosterman phase is bounded below away from its critical
points**, uniformly in `D` in a bounded set `K` (for instance a compact subset of `ℂˣ`): for every
`δ > 0` there is `c > 0` such that `‖∇g_D(x)‖ ≥ c` (sup norm of the vector of partial
derivatives) whenever `D ∈ K` and `x` is at sup distance at least `δ` from every point
`(z, …, z)` with `z ^ (n + 1) = D` (the critical points when `D ≠ 0`). -/
theorem exists_pos_le_norm_hyperKloostermanPhaseGrad {K : Set ℂ} (hK : Bornology.IsBounded K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c > 0, ∀ D ∈ K, ∀ x : ι → ℂ,
      (∀ z : ℂ, z ^ (Fintype.card ι + 1) = D → δ ≤ ‖x - fun _ ↦ z‖) →
        c ≤ ‖hyperKloostermanPhaseGrad D x‖ := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  set M := max 1 R
  have hM : 0 < M := lt_max_of_lt_left one_pos
  refine ⟨min (1 / 3) (δ / (7 * M)), by positivity, fun D hD x hfar ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  have hc : 0 < min (1 / 3) (δ / (7 * M)) := by positivity
  obtain ⟨z, hz, hxz⟩ := exists_pow_eq_norm_sub_le_of_norm_hyperKloostermanPhaseGrad_lt
    (min_le_left _ _) ((pi_norm_lt_iff hc).1 hlt)
  have hzM : ‖z‖ ≤ M := by
    rcases le_or_gt ‖z‖ 1 with h1 | h1
    · exact h1.trans (le_max_left _ _)
    · calc ‖z‖ ≤ ‖z‖ ^ (Fintype.card ι + 1) := le_self_pow₀ h1.le (by omega)
        _ = ‖D‖ := by rw [← norm_pow, hz]
        _ ≤ M := (hR D hD).trans (le_max_right _ _)
  refine (hfar z hz).not_gt ((pi_norm_lt_iff hδ).2 fun k ↦ ?_)
  calc ‖(x - fun _ ↦ z : ι → ℂ) k‖ = ‖x k - z‖ := rfl
    _ ≤ 6 * min (1 / 3) (δ / (7 * M)) * ‖z‖ := hxz k
    _ ≤ 6 * (δ / (7 * M)) * M := by gcongr; exact min_le_right _ _
    _ < δ := by field_simp; linarith

end Complex

end TauCeti
