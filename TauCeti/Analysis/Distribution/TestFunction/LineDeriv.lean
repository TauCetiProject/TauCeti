/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Directional derivatives of test functions

Mathlib equips the test functions `𝓓(Ω, F)` with the directional derivative `∂_{v}` and its
iteration `∂^{m}`. This file evaluates them pointwise as the classical directional and iterated
Fréchet derivatives, and shows that two directional derivatives of a test function commute,
`∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ)`, because the second derivative of a smooth function is
symmetric. Moving derivatives between the two sides of an integration-by-parts identity uses
exactly this, for instance to show that weak derivatives commute. Summing over an orthonormal basis,
the Laplacian of a test function commutes with every directional derivative. Pairing a `Cⁿ` test
function `φ ∈ 𝓓^{n}(Ω, F₁)` with a function `g : E → F₂` that is `Cⁿ` on an open neighbourhood `U`
of `tsupport φ` via a continuous bilinear map (in particular, multiplying a scalar cutoff `χ` by
`g : E → F` or scaling `φ` by a scalar `g` smooth on `Ω`) produces a test function on `Ω`, with
the classical product rule for its directional derivatives; this is what lets a weak derivative or
distribution be tested against cutoffs of locally smooth functions. On a real inner product space,
the directional derivative of a scalar test function is the pairing with its gradient, and the
product of a scalar test function with a smooth function supported in `Ω` is a test function on
`Ω` whose gradient obeys the product rule.

## Main declarations

* `TestFunction.lineDerivOp_apply`: `∂_{v} φ` is the classical directional derivative of `φ`.
* `TestFunction.lineDerivOp_apply_eq_fderiv`, `TestFunction.coe_lineDerivOp_eq_fderiv`:
  `∂_{v} φ x = Dφ(x) v`.
* `TestFunction.tsupport_lineDerivOp_subset`: `∂_{v} φ` is supported in the support of `φ`.
* `TestFunction.tsupport_iteratedLineDerivOp_subset`: iterated directional derivatives of `φ`
  are supported in `tsupport φ`.
* `TestFunction.norm_iteratedFDeriv_lineDerivOp_le`: the derivatives of order at most `r` of
  `∂_{v} φ` are bounded by `‖v‖` times a bound on those of order at most `r + 1` of `φ`.
* `TestFunction.iteratedLineDerivOp_apply_eq_iteratedFDeriv`,
  `TestFunction.iteratedLineDerivOp_apply_eq_iteratedFDerivAlong`: `∂^{m} φ` agrees pointwise with
  the iterated Fréchet derivative and `TauCeti.iteratedFDerivAlong`.
* `TestFunction.smul_neg_one_pow_iteratedLineDerivOp_sub_apply`: `((-1)^k • ∂^{m} φ) (y - z)` is
  the iterated directional derivative of `w ↦ φ (y - w)` at `z`.
* `TestFunction.smul_fderiv_apply_eq_of_eqOn_one`: a first derivative of `φ` is unchanged by a
  factor equal to `1` on `Ω`.
* `TestFunction.lineDerivOp_one_apply_eq_deriv`: on the real line, `∂_{1} φ` is the derivative
  of `φ`.
* `TestFunction.coe_iterate_lineDerivOp_one`: repeated derivatives on the real line agree with
  the iterates of the ordinary derivative.
* `TestFunction.im_lineDerivOp_ofReal_apply_ofReal`: in the plane, a derivative along a real
  direction of a complex test function real on the real axis is real there.
* `TestFunction.lineDeriv_eq_fderiv`: the classical directional derivative of a test function is
  its Fréchet derivative in that direction.
* `TestFunction.lineDerivCLM_postcompCLM`: directional derivatives commute with postcomposition
  by a continuous linear map.
* `TestFunction.iteratedLineDerivOp_postcompCLM`: so do iterated directional derivatives.
* `TestFunction.lineDerivOp_comm`, `TestFunction.lineDeriv_lineDerivOp_comm`,
  `TestFunction.iteratedLineDerivOp_lineDerivOp`, `TestFunction.iteratedLineDerivOp_comp_rev`:
  directional and iterated directional derivatives of test functions commute.
* `TestFunction.lineDerivOp_laplacianCLM`: the Laplacian of test functions commutes with
  directional derivatives.
* `TestFunction.bilinOfContDiffOn`, `TestFunction.smulOfContDiffOn`: pairing a test function with a
  function `Cⁿ` on an open neighbourhood of its support via a continuous bilinear map or scalar
  multiplication produces a test function on `Ω`.
* `TestFunction.exists_coe_eq_smul_of_contDiffOn`: the product of a test function on `Ω` with a
  function smooth on `Ω` is a test function on `Ω`.
* `TestFunction.lineDeriv_fun_smul_of_differentiableOn`: its directional derivatives obey the
  product rule.
* `TestFunction.laplacianCLM_apply`: the test-function Laplacian agrees pointwise with the
  classical Laplacian.
* `TestFunction.integrable_laplacian_smul`: `x ↦ Δφ(x) • u x` is integrable when `u` is locally
  integrable on `Ω`.
* `TestFunction.lineDerivCLM_apply_eq_inner`: `∂_{v} φ x = ⟪v, ∇φ x⟫` for a scalar test function.
* `TauCeti.exists_testFunction_mul`: for `ζ` smooth with `tsupport ζ ⊆ Ω`, the product `ζ φ` is a
  test function on `Ω` with gradient `ζ ∇φ + φ ∇ζ`.
-/

public section

namespace TestFunction

open LineDeriv TopologicalSpace
open scoped ContDiff Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- The directional derivative of a test function is its classical directional derivative. -/
@[simp]
theorem lineDerivOp_apply (φ : 𝓓(Ω, F)) (v x : E) : ∂_{v} φ x = lineDeriv ℝ φ x v :=
  lineDerivCLM_apply_of_le le_top

/-- The directional derivative of a test function is its Fréchet derivative applied to the
direction. -/
theorem lineDerivOp_apply_eq_fderiv (φ : 𝓓(Ω, F)) (v x : E) : ∂_{v} φ x = fderiv ℝ φ x v := by
  rw [lineDerivOp_apply, (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]

/-- The underlying function of a directional derivative of a test function is its Fréchet
derivative applied to the direction. -/
theorem coe_lineDerivOp_eq_fderiv (φ : 𝓓(Ω, F)) (v : E) :
    ⇑(∂_{v} φ : 𝓓(Ω, F)) = fun x ↦ fderiv ℝ (φ : E → F) x v :=
  funext (lineDerivOp_apply_eq_fderiv φ v)

/-- A directional derivative of a test function is supported in the support of the function. -/
theorem tsupport_lineDerivOp_subset (φ : 𝓓(Ω, F)) (v : E) :
    tsupport (∂_{v} φ : 𝓓(Ω, F)) ⊆ tsupport φ := by
  rw [coe_lineDerivOp_eq_fderiv]
  exact tsupport_fderiv_apply_subset ℝ v

/-- The derivatives of order at most `r` of `∂_v φ` are bounded by `‖v‖` times a bound on the
derivatives of order at most `r + 1` of `φ`. -/
theorem norm_iteratedFDeriv_lineDerivOp_le (φ : 𝓓(Ω, F)) (v : E) {r : ℕ} {B : ℝ}
    (hB : ∀ i ≤ r + 1, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ B) :
    ∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i (∂_{v} φ : 𝓓(Ω, F)) y‖ ≤ ‖v‖ * B := by
  rw [coe_lineDerivOp_eq_fderiv]
  exact fun i hi y ↦ (φ.contDiff.norm_iteratedFDeriv_fderiv_apply_le_of_forall_le (by simp) hB v i
    hi y).trans_eq (mul_comm _ _)

/-- Scaling a first derivative of a test function on `Ω` by a function equal to `1` on `Ω` does not
change it, since the derivative vanishes off `Ω`. -/
theorem smul_fderiv_apply_eq_of_eqOn_one (φ : 𝓓(Ω, F)) {χ : E → ℝ} (hχ : Set.EqOn χ 1 Ω)
    (x v : E) : χ x • fderiv ℝ (φ : E → F) x v = fderiv ℝ (φ : E → F) x v := by
  by_cases hx : x ∈ Ω
  · rw [hχ hx, Pi.one_apply, one_smul]
  · rw [fderiv_of_notMem_tsupport ℝ fun h => hx (φ.tsupport_subset h)]
    simp

/-- On the real line, the directional derivative of a test function in the direction `1` is its
derivative. -/
theorem lineDerivOp_one_apply_eq_deriv {Ω : Opens ℝ} (φ : 𝓓(Ω, F)) (x : ℝ) :
    ∂_{(1 : ℝ)} φ x = deriv φ x := by
  rw [lineDerivOp_apply, (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv,
    fderiv_apply_one_eq_deriv]

/-- Iterating the directional derivative in direction `1` on a real-line test function
agrees with iterating its ordinary derivative. -/
@[simp]
theorem coe_iterate_lineDerivOp_one {Ω : Opens ℝ} (φ : 𝓓(Ω, F)) (n : ℕ) :
    ⇑((LineDeriv.lineDerivOp (1 : ℝ))^[n] φ) = deriv^[n] (φ : ℝ → F) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (funext (lineDerivOp_one_apply_eq_deriv _)).trans (congrArg deriv ih)

/-- In the plane, the derivative along a real direction of a complex test function real on the
real axis is real on the real axis. -/
theorem im_lineDerivOp_ofReal_apply_ofReal {Ω : Opens ℂ} (φ : 𝓓(Ω, ℂ))
    (hφ : ∀ x : ℝ, (φ (x : ℂ)).im = 0) (v x : ℝ) :
    ((∂_{(v : ℂ)} φ : 𝓓(Ω, ℂ)) (x : ℂ)).im = 0 := by
  rw [lineDerivOp_apply_eq_fderiv]
  have hd : HasFDerivAt (φ : ℂ → ℂ) (fderiv ℝ (φ : ℂ → ℂ) x) x :=
    (φ.contDiff.differentiable (by simp) x).hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ ↦ ((x + t * v : ℝ) : ℂ)) v 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const v).const_add x).ofReal_comp
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hd.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp))
  have h0 := him.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t ↦ by simpa using hφ (x + t * v)))
  simpa using h0

/-- The underlying function of a directional derivative of a test function is its classical
directional derivative. -/
@[simp]
theorem coe_lineDerivCLM (φ : 𝓓(Ω, F)) (v : E) :
    ⇑(lineDerivCLM ℝ v φ : 𝓓(Ω, F)) = fun x ↦ lineDeriv ℝ (φ : E → F) x v :=
  funext (lineDerivOp_apply φ v)

/-- The classical directional derivative of a test function is its Fréchet derivative evaluated in
that direction. -/
theorem lineDeriv_eq_fderiv (φ : 𝓓(Ω, F)) (x v : E) :
    lineDeriv ℝ (φ : E → F) x v = fderiv ℝ (φ : E → F) x v :=
  (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv

/-- Directional derivatives of test functions commute with postcomposition by a continuous linear
map, at every pair of orders. -/
theorem lineDerivCLM_postcompCLM {𝕜 : Type*} [NontriviallyNormedField 𝕜] [Algebra ℝ 𝕜]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] {n k : ℕ∞} {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [IsScalarTower ℝ 𝕜 F'] (L : F →L[𝕜] F') (v : E)
    (φ : 𝓓^{n}(Ω, F)) :
    (lineDerivCLM 𝕜 v (postcompCLM L φ) : 𝓓^{k}(Ω, F')) = postcompCLM L (lineDerivCLM 𝕜 v φ) := by
  ext x
  simp only [lineDerivCLM_eq_fderivCLM, fderivCLM_apply, postcompCLM_apply, Function.comp_apply]
  split_ifs with hk
  · have hn : (n : WithTop ℕ∞) ≠ 0 := by
      have : (0 : ℕ∞) < n := (add_pos_of_right zero_lt_one k).trans_le hk
      exact_mod_cast this.ne'
    have hφ : DifferentiableAt ℝ φ x := (φ.contDiff.differentiable hn).differentiableAt
    have hL := ((L.restrictScalars ℝ).hasFDerivAt.comp x hφ.hasFDerivAt).fderiv
    rw [ContinuousLinearMap.coe_restrictScalars'] at hL
    rw [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  · simp

/-- Iterated directional derivatives of test functions commute with postcomposition by a
continuous linear map. -/
theorem iteratedLineDerivOp_postcompCLM {𝕜 : Type*} [NontriviallyNormedField 𝕜] [Algebra ℝ 𝕜]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [IsScalarTower ℝ 𝕜 F'] (L : F →L[𝕜] F') {k : ℕ}
    (m : Fin k → E) (φ : 𝓓(Ω, F)) :
    ∂^{m} (postcompCLM L φ) = postcompCLM L (∂^{m} φ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left, ih,
      lineDerivOp_eq_lineDerivCLM 𝕜, lineDerivOp_eq_lineDerivCLM 𝕜, lineDerivCLM_postcompCLM]

/-- Iterated directional derivatives of a test function agree with its iterated Fréchet
derivatives evaluated in those directions. -/
theorem lineDeriv_lineDeriv_eq_fderiv_fderiv (φ : 𝓓(Ω, F)) (v w x : E) :
    lineDeriv ℝ (fun y ↦ lineDeriv ℝ (φ : E → F) y v) x w =
      fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → F) y v) x w := by
  have hφ : ∀ y, lineDeriv ℝ (φ : E → F) y v = fderiv ℝ (φ : E → F) y v := fun y ↦
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv
  simp_rw [hφ]
  exact (((φ.contDiff.fderiv_right (by simp)).clm_apply contDiff_const).differentiable
    one_ne_zero x).lineDeriv_eq_fderiv

/-- **Directional derivatives of test functions commute.** -/
theorem lineDerivOp_comm (φ : 𝓓(Ω, F)) (v w : E) : ∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ) := by
  ext x
  have hd : DifferentiableAt ℝ (fderiv ℝ (φ : E → F)) x :=
    (φ.contDiff.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero x
  rw [lineDerivOp_apply, lineDerivOp_apply]
  simp only [lineDerivOp_eq_lineDerivCLM ℝ]
  rw [coe_lineDerivCLM, coe_lineDerivCLM,
    lineDeriv_lineDeriv_eq_fderiv_fderiv, lineDeriv_lineDeriv_eq_fderiv_fderiv]
  simpa [fderiv_clm_apply hd (differentiableAt_const _)] using
    ((φ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)).eq v w

/-- The classical directional derivative of `∂_{v} φ` in the direction `w` is that of `∂_{w} φ`
in the direction `v`. -/
theorem lineDeriv_lineDerivOp_comm (φ : 𝓓(Ω, F)) (v w x : E) :
    lineDeriv ℝ (∂_{v} φ : 𝓓(Ω, F)) x w = lineDeriv ℝ (∂_{w} φ : 𝓓(Ω, F)) x v := by
  rw [← lineDerivOp_apply, ← lineDerivOp_apply, lineDerivOp_comm]

/-! ### Iterated directional derivatives -/

/-- An iterated directional derivative of a test function is supported in the support of the
function. -/
theorem tsupport_iteratedLineDerivOp_subset (φ : 𝓓(Ω, F)) {k : ℕ} (m : Fin k → E) :
    tsupport (∂^{m} φ : 𝓓(Ω, F)) ⊆ tsupport φ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left]
    exact (tsupport_lineDerivOp_subset _ (m 0)).trans (ih (Fin.tail m))

/-- An iterated directional derivative of a test function agrees pointwise with its iterated
Fréchet derivative evaluated on those directions. -/
theorem iteratedLineDerivOp_apply_eq_iteratedFDeriv (φ : 𝓓(Ω, F)) {k : ℕ} (m : Fin k → E)
    (x : E) :
    ∂^{m} φ x = iteratedFDeriv ℝ k (φ : E → F) x m := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedFDeriv_succ_apply_left,
      ← fderiv_continuousMultilinear_apply_const_apply]
    · simp only [lineDerivOp_apply_eq_fderiv, ← ih]
    · exact φ.contDiff.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top k) x

/-- An iterated directional derivative of a test function agrees pointwise with
`TauCeti.iteratedFDerivAlong` along the list of directions. -/
theorem iteratedLineDerivOp_apply_eq_iteratedFDerivAlong (φ : 𝓓(Ω, F)) {k : ℕ} (m : Fin k → E)
    (x : E) :
    ∂^{m} φ x = TauCeti.iteratedFDerivAlong ℝ (List.ofFn m) (φ : E → F) x := by
  rw [iteratedLineDerivOp_apply_eq_iteratedFDeriv,
    (φ.contDiff.contDiffAt.of_le (mod_cast le_top)).iteratedFDerivAlong_ofFn_eq_iteratedFDeriv
      le_rfl]

/-- An iterated directional derivative of a test function commutes with a single directional
derivative. -/
theorem iteratedLineDerivOp_lineDerivOp (φ : 𝓓(Ω, F)) {k : ℕ} (m : Fin k → E) (v : E) :
    ∂^{m} (∂_{v} φ) = ∂_{v} (∂^{m} φ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left, ih, lineDerivOp_comm]

/-- Reversing the order of directions does not change an iterated directional derivative of a test
function. -/
theorem iteratedLineDerivOp_comp_rev (φ : 𝓓(Ω, F)) {k : ℕ} (m : Fin k → E) :
    ∂^{m ∘ Fin.rev} φ = ∂^{m} φ := by
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    have hinit : Fin.init (m ∘ Fin.rev) = Fin.tail m ∘ Fin.rev := by
      ext i
      simp [Fin.init_def, Fin.tail_def, Fin.rev_castSucc]
    rw [iteratedLineDerivOp_succ_right, iteratedLineDerivOp_succ_left,
      iteratedLineDerivOp_lineDerivOp]
    simp only [Function.comp_apply, Fin.rev_last, hinit, ih]

/-- Differentiating `w ↦ φ (y - w)` along the directions `m` at `z` agrees with evaluating
`(-1)^k • ∂^{m} φ` at `y - z`. -/
theorem smul_neg_one_pow_iteratedLineDerivOp_sub_apply (φ : 𝓓(Ω, F)) {k : ℕ} (m : Fin k → E)
    (y z : E) :
    ((-1 : ℝ) ^ k • ∂^{m} φ) (y - z) =
      TauCeti.iteratedFDerivAlong ℝ (List.ofFn m) (fun w ↦ φ (y - w)) z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    let η : 𝓓(Ω, F) := ∂^{Fin.tail m} φ
    let ψ : 𝓓(Ω, F) := (-1 : ℝ) ^ k • η
    have hd := (ψ.contDiff.differentiable (by simp) (y - z)).hasFDerivAt.comp z
      ((hasFDerivAt_const y z).sub (hasFDerivAt_id z))
    have hdf : fderiv ℝ (fun w ↦ ψ (y - w)) z (m 0) = -fderiv ℝ (ψ : E → F) (y - z) (m 0) := by
      simpa [Function.comp_def] using congrArg (· (m 0)) hd.fderiv
    have hψ_coe : (ψ : E → F) = (-1 : ℝ) ^ k • (η : E → F) := by
      ext w
      simp [ψ]
    have hψ : fderiv ℝ (ψ : E → F) (y - z) (m 0) =
        (-1 : ℝ) ^ k • fderiv ℝ (η : E → F) (y - z) (m 0) := by
      rw [hψ_coe, fderiv_const_smul (η.contDiff.differentiable (by simp) (y - z)), smul_apply]
    have hih : TauCeti.iteratedFDerivAlong ℝ (List.ofFn fun i ↦ m i.succ)
        (fun w ↦ φ (y - w)) = fun w ↦ ψ (y - w) :=
      funext fun w ↦ (ih (Fin.tail m) w).symm
    rw [List.ofFn_succ, TauCeti.iteratedFDerivAlong_cons_apply, hih, hdf, hψ,
      iteratedLineDerivOp_succ_left, smul_apply, lineDerivOp_apply_eq_fderiv, pow_succ, mul_comm,
      mul_smul, neg_one_smul]

/-! ### Multiplication by a function `Cⁿ` on a neighbourhood of the support -/

/-- **Pairing a test function with a function `Cⁿ` near its support.** Given a test function
`φ ∈ 𝓓^{n}(Ω, F₁)`, a continuous bilinear map `B : F₁ →L[ℝ] F₂ →L[ℝ] F₃`, and a function
`g : E → F₂` that is `Cⁿ` on an open neighbourhood `U` of `tsupport φ` (with no regularity
requirement outside `U`), the pointwise product `x ↦ B (φ x) (g x)` is a test function in
`𝓓^{n}(Ω, F₃)` supported in `tsupport φ`. -/
def bilinOfContDiffOn {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    {n : ℕ∞} (φ : 𝓓^{n}(Ω, F₁)) (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {U : Set E} (hU : IsOpen U)
    (hφU : tsupport (φ : E → F₁) ⊆ U) {g : E → F₂} (hg : ContDiffOn ℝ n g U) :
    𝓓^{n}(Ω, F₃) where
  toFun x := B (φ x) (g x)
  contDiff' :=
    contDiff_of_contDiffOn_union_of_isOpen
      (B.isBoundedBilinearMap.contDiff.comp_contDiffOn (φ.contDiff.contDiffOn.prodMk hg))
      ((contDiffOn_const (c := (0 : F₃))).congr fun _ hx ↦ by
        simp [image_eq_zero_of_notMem_tsupport (f := (φ : E → F₁)) hx])
      (Set.eq_univ_of_forall fun x ↦ (em (x ∈ tsupport (φ : E → F₁))).imp (hφU ·) id)
      hU (isClosed_tsupport (φ : E → F₁)).isOpen_compl
  hasCompactSupport' :=
    HasCompactSupport.of_support_subset_isCompact φ.hasCompactSupport fun _ hx ↦
      subset_tsupport _ fun h0 ↦ Function.mem_support.1 hx (by simp [h0])
  tsupport_subset' :=
    (closure_minimal
      (fun _ hx ↦ subset_tsupport _ fun h0 ↦ Function.mem_support.1 hx (by simp [h0]))
      (isClosed_tsupport (φ : E → F₁))).trans φ.tsupport_subset

@[simp]
theorem bilinOfContDiffOn_apply {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    {n : ℕ∞} (φ : 𝓓^{n}(Ω, F₁)) (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {U : Set E} (hU : IsOpen U)
    (hφU : tsupport (φ : E → F₁) ⊆ U) {g : E → F₂} (hg : ContDiffOn ℝ n g U) (x : E) :
    φ.bilinOfContDiffOn B hU hφU hg x = B (φ x) (g x) := by
  rfl

/-- The support of `φ.bilinOfContDiffOn B hU hφU hg` is contained in `tsupport φ`. -/
theorem tsupport_bilinOfContDiffOn_subset {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁]
    [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃]
    [NormedSpace ℝ F₃] {n : ℕ∞} (φ : 𝓓^{n}(Ω, F₁)) (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {U : Set E}
    (hU : IsOpen U) (hφU : tsupport (φ : E → F₁) ⊆ U) {g : E → F₂} (hg : ContDiffOn ℝ n g U) :
    tsupport (φ.bilinOfContDiffOn B hU hφU hg : E → F₃) ⊆ tsupport (φ : E → F₁) :=
  closure_minimal (fun _ hx ↦ subset_tsupport _ fun h0 ↦ Function.mem_support.1 hx (by simp [h0]))
    (isClosed_tsupport (φ : E → F₁))

/-- **Multiplying a scalar cutoff by a function `Cⁿ` near its support.** Given a scalar test
function `χ ∈ 𝓓^{n}(Ω, ℝ)` and a function `g : E → F` that is `Cⁿ` on an open neighbourhood `U` of
`tsupport χ`, the pointwise product `x ↦ χ x • g x` is a test function in `𝓓^{n}(Ω, F)`. -/
noncomputable def smulOfContDiffOn {n : ℕ∞} (χ : 𝓓^{n}(Ω, ℝ)) {U : Set E} (hU : IsOpen U)
    (hχU : tsupport (χ : E → ℝ) ⊆ U) {g : E → F} (hg : ContDiffOn ℝ n g U) : 𝓓^{n}(Ω, F) :=
  χ.bilinOfContDiffOn (ContinuousLinearMap.lsmul ℝ ℝ) hU hχU hg

@[simp]
theorem smulOfContDiffOn_apply {n : ℕ∞} (χ : 𝓓^{n}(Ω, ℝ)) {U : Set E} (hU : IsOpen U)
    (hχU : tsupport (χ : E → ℝ) ⊆ U) {g : E → F} (hg : ContDiffOn ℝ n g U) (x : E) :
    χ.smulOfContDiffOn hU hχU hg x = χ x • g x := by
  rfl

/-- The support of `χ.smulOfContDiffOn hU hχU hg` is contained in `tsupport χ`. -/
theorem tsupport_smulOfContDiffOn_subset {n : ℕ∞} (χ : 𝓓^{n}(Ω, ℝ)) {U : Set E} (hU : IsOpen U)
    (hχU : tsupport (χ : E → ℝ) ⊆ U) {g : E → F} (hg : ContDiffOn ℝ n g U) :
    tsupport (χ.smulOfContDiffOn hU hχU hg : E → F) ⊆ tsupport (χ : E → ℝ) :=
  χ.tsupport_bilinOfContDiffOn_subset (ContinuousLinearMap.lsmul ℝ ℝ) hU hχU hg

@[simp]
theorem smulOfContDiffOn_zero {n : ℕ∞} (χ : 𝓓^{n}(Ω, ℝ)) {U : Set E} (hU : IsOpen U)
    (hχU : tsupport (χ : E → ℝ) ⊆ U) (hg : ContDiffOn ℝ n (0 : E → F) U) :
    χ.smulOfContDiffOn hU hχU hg = 0 := by
  ext x
  simp

@[simp]
theorem smulOfContDiffOn_add {n : ℕ∞} (χ : 𝓓^{n}(Ω, ℝ)) {U : Set E} (hU : IsOpen U)
    (hχU : tsupport (χ : E → ℝ) ⊆ U) {g₁ g₂ : E → F} (hg₁ : ContDiffOn ℝ n g₁ U)
    (hg₂ : ContDiffOn ℝ n g₂ U) :
    χ.smulOfContDiffOn hU hχU (hg₁.add hg₂) =
      χ.smulOfContDiffOn hU hχU hg₁ + χ.smulOfContDiffOn hU hχU hg₂ := by
  ext x
  simp [smul_add]

@[simp]
theorem smulOfContDiffOn_neg {n : ℕ∞} (χ : 𝓓^{n}(Ω, ℝ)) {U : Set E} (hU : IsOpen U)
    (hχU : tsupport (χ : E → ℝ) ⊆ U) {g : E → F} (hg : ContDiffOn ℝ n g U) :
    χ.smulOfContDiffOn hU hχU hg.neg = -χ.smulOfContDiffOn hU hχU hg := by
  ext x
  simp

@[simp]
theorem smulOfContDiffOn_sub {n : ℕ∞} (χ : 𝓓^{n}(Ω, ℝ)) {U : Set E} (hU : IsOpen U)
    (hχU : tsupport (χ : E → ℝ) ⊆ U) {g₁ g₂ : E → F} (hg₁ : ContDiffOn ℝ n g₁ U)
    (hg₂ : ContDiffOn ℝ n g₂ U) :
    χ.smulOfContDiffOn hU hχU (hg₁.sub hg₂) =
      χ.smulOfContDiffOn hU hχU hg₁ - χ.smulOfContDiffOn hU hχU hg₂ := by
  ext x
  simp [smul_sub]

@[simp]
theorem smulOfContDiffOn_smul {n : ℕ∞} (χ : 𝓓^{n}(Ω, ℝ)) {U : Set E} (hU : IsOpen U)
    (hχU : tsupport (χ : E → ℝ) ⊆ U) (c : ℝ) {g : E → F} (hg : ContDiffOn ℝ n g U) :
    χ.smulOfContDiffOn hU hχU (hg.const_smul c : ContDiffOn ℝ n (c • g) U) =
      c • χ.smulOfContDiffOn hU hχU hg := by
  ext x
  rw [smulOfContDiffOn_apply, smul_apply, smulOfContDiffOn_apply, smul_comm]

/-- **A test function times a function smooth on `Ω` is a test function.** If `g` is smooth on
`Ω`, with no condition off `Ω`, and `φ ∈ 𝓓(Ω, F)`, then `x ↦ g x • φ x` is again a test function
on `Ω`: it is smooth on `Ω` and vanishes on the open complement of `tsupport φ`, and these two
open sets cover `E`. -/
theorem exists_coe_eq_smul_of_contDiffOn {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g Ω) (φ : 𝓓(Ω, F)) :
    ∃ ψ : 𝓓(Ω, F), ⇑ψ = fun x => g x • φ x :=
  ⟨φ.bilinOfContDiffOn (ContinuousLinearMap.lsmul ℝ ℝ).flip Ω.isOpen φ.tsupport_subset hg,
    by ext x; simp⟩

/-- **The product rule for a test function times a function differentiable on `Ω`**:
`∂_v (g φ) = g ∂_v φ + (∂_v g) φ` at every point of `E`. Off `tsupport φ` both sides vanish, so
nothing is needed of `g` outside `Ω`. -/
theorem lineDeriv_fun_smul_of_differentiableOn {g : E → ℝ} (hg : DifferentiableOn ℝ g Ω)
    (φ : 𝓓(Ω, F)) (x v : E) :
    lineDeriv ℝ (fun y => g y • φ y) x v = g x • lineDeriv ℝ φ x v + fderiv ℝ g x v • φ x := by
  have hφx : DifferentiableAt ℝ φ x := φ.contDiff.differentiable (by simp) x
  by_cases hx : x ∈ tsupport φ
  · have hgx : DifferentiableAt ℝ g x :=
      hg.differentiableAt (Ω.isOpen.mem_nhds (φ.tsupport_subset hx))
    rw [(hgx.fun_smul hφx).lineDeriv_eq_fderiv, hφx.lineDeriv_eq_fderiv, fderiv_fun_smul hgx hφx]
    simp
  · -- Near `x` both `φ` and `g φ` vanish identically.
    have hnhds : (tsupport φ)ᶜ ∈ nhds x := (isClosed_tsupport φ).isOpen_compl.mem_nhds hx
    have h0 : (fun y => g y • φ y) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [hnhds] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    have hφ0 : (φ : E → F) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [hnhds] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    rw [(((hasFDerivAt_const (0 : F) x).congr_of_eventuallyEq h0).hasLineDerivAt v).lineDeriv,
      (((hasFDerivAt_const (0 : F) x).congr_of_eventuallyEq hφ0).hasLineDerivAt v).lineDeriv,
      image_eq_zero_of_notMem_tsupport hx]
    simp

end TestFunction

namespace TestFunction

open LineDeriv TopologicalSpace
open scoped Distributions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- **The Laplacian of test functions commutes with directional derivatives**:
`∂_{v} (Δφ) = Δ (∂_{v} φ)`. -/
theorem lineDerivOp_laplacianCLM (φ : 𝓓(Ω, F)) (v : E) :
    ∂_{v} (laplacianCLM ℝ E 𝓓(Ω, F) φ) = laplacianCLM ℝ E 𝓓(Ω, F) (∂_{v} φ) := by
  simp only [laplacianCLM_eq_sum (stdOrthonormalBasis ℝ E), lineDerivOp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lineDerivOp_comm, lineDerivOp_comm φ v]

open InnerProductSpace Laplacian in
/-- The test-function Laplacian agrees pointwise with the classical Laplacian. -/
@[simp]
theorem laplacianCLM_apply (φ : 𝓓(Ω, F)) (x : E) :
    (laplacianCLM ℝ E (𝓓(Ω, F)) φ) x = Δ (φ : E → F) x := by
  have hcoe (v : E) : ⇑(lineDerivCLM ℝ v φ : 𝓓(Ω, F)) =
      fun y ↦ fderiv ℝ (φ : E → F) y v := by
    funext y
    rw [lineDerivCLM_eq_fderivCLM, fderivCLM_apply_of_le _ le_top]
  simp only [LineDeriv.laplacianCLM, sum_apply,
    ContinuousLinearMap.comp_apply, lineDerivOpCLM_eq_lineDerivCLM,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [lineDerivCLM_eq_fderivCLM, fderivCLM_apply_of_le _ le_top, hcoe,
    fderiv_clm_apply ((φ.contDiff.fderiv_right (by simp)).differentiable one_ne_zero x)
      (differentiableAt_const _)]
  simp

open MeasureTheory InnerProductSpace Laplacian in
/-- The Laplacian of a test function on `Ω` scales a function locally integrable on `Ω` to a
globally integrable one. -/
theorem integrable_laplacian_smul [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}
    (φ : 𝓓(Ω, ℝ)) {u : E → F} (hu : LocallyIntegrableOn u Ω μ) :
    Integrable (fun x ↦ Δ (φ : E → ℝ) x • u x) μ := by
  simpa only [laplacianCLM_apply] using (laplacianCLM ℝ E 𝓓(Ω, ℝ) φ).integrable_smul hu

end TestFunction

namespace TestFunction

open TopologicalSpace
open scoped Distributions Gradient InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {Ω : Opens E}

/-- The directional derivative of a test function along `v` is the pairing of `v` with its
gradient. -/
theorem lineDerivCLM_apply_eq_inner (phi : 𝓓(Ω, ℝ)) (v x : E) :
    (lineDerivCLM (n := ⊤) (k := ⊤) ℝ v phi : E → ℝ) x = ⟪v, ∇ (phi : E → ℝ) x⟫_ℝ := by
  rw [lineDerivCLM_apply_of_le le_top, real_inner_comm, gradient,
    InnerProductSpace.toDual_symm_apply,
    (phi.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]

end TestFunction

namespace TauCeti

open TopologicalSpace
open scoped ContDiff Distributions Gradient InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {Ω : Opens E}

/-- The product `ζ φ` of a test function `φ` with a smooth function `ζ` whose support lies in
`Ω` is a test function on `Ω`, with gradient `ζ ∇φ + φ ∇ζ`. -/
theorem exists_testFunction_mul {U : Opens E} {ζ : E → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hts : tsupport ζ ⊆ Ω) (phi : 𝓓(U, ℝ)) :
    ∃ psi : 𝓓(Ω, ℝ), (psi : E → ℝ) = (fun x => ζ x * phi x) ∧
      ∀ x, ∇ (psi : E → ℝ) x = ζ x • ∇ (phi : E → ℝ) x + phi x • ∇ ζ x := by
  refine ⟨⟨fun x => ζ x * phi x, hζ.mul phi.contDiff, phi.hasCompactSupport.mul_left,
    tsupport_mul_subset_left.trans hts⟩, TestFunction.coe_mk, fun x => ?_⟩
  rw [TestFunction.coe_mk]
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [toDual_gradient, map_add, map_smul]
  exact fderiv_fun_mul (hζ.differentiable (by simp) x) (phi.contDiff.differentiable (by simp) x)

end TauCeti
