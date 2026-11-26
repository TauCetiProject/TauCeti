/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.CouplingForm
public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Model
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Calculus.DifferentialForm.Const
import TauCeti.Analysis.Calculus.DifferentialForm.LocalPotentials
import TauCeti.Analysis.InnerProductSpace.TwoDim
import TauCeti.Geometry.Symplectic.Complex.Line
import TauCeti.LinearAlgebra.BilinearMap.Multilinear

/-!
# The normal model structure of a unitary connection and its coupling form

Let `A` be a real one-form on a planar base `ℂ`, so that `∇ = d + i A` is a unitary connection on
the trivial line `ℂ × ℂ → ℂ`. Its normal Cauchy–Riemann operator is `∂bar + ν` with
(`TauCeti.normalModelConnectionCoeff`)

`ν = (I A(1) - A(I)) / 2`,

the `(0,1)`-part of `i A`: a section has holomorphic graph for the normal model structure
`J_N = TauCeti.normalModelStructure ν 0` exactly when it is `∇`-holomorphic, `∇_I s = I ∇_1 s`
(`TauCeti.isJHolomorphicAt_graph_normalModelStructure_normalModelConnectionCoeff_iff`).
This file shows that the coupling form of the same connection,

`ω_N = π^* ω + d((ρ² / 2) (dθ + A))`

(`TauCeti.normalCouplingForm`, in polar coordinates `w = ρ e^{iθ}` on the fibre), is compatible
with `J_N`, and that `J_N` is integrable when `A` is flat. This is the model normal geometry of an
embedded torus with a flat unitary normal connection, near which Taubes installs a compatible
integrable almost complex structure.

## Compatibility

`J_N` is the structure of the horizontal distribution of `∇`: it carries the horizontal lift
`(ξ, -i A(ξ) w)` of `ξ` at `(z, w)` to the horizontal lift of `I ξ`. A tangent vector `X = (ξ, η)`
is the sum of a horizontal lift and the vertical vector `∇_X w = η + i A(ξ) w`
(`TauCeti.normalCovariantDeriv`), and `J_N` multiplies both by `I`
(`TauCeti.normalCovariantDeriv_normalModelStructure`). The coupling form is
`ω_N(X, Y) = ω(ξ, ξ') + Im (conj (∇_X w) ∇_Y w) + (|w|² / 2) dA(ξ, ξ')`
(`TauCeti.normalCouplingForm_apply_eq_normalCovariantDeriv`), and every two-form on the plane is
invariant under `I` (`ContinuousAlternatingMap.apply_I_mul_I_mul`), so `ω_N` is `J_N`-invariant
(`TauCeti.normalCouplingForm_apply_normalModelStructure_normalModelStructure`) and

`ω_N(X, J_N X) = (ω(1, I) + (|w|² / 2) dA(1, I)) |ξ|² + |∇_X w|²`

(`TauCeti.normalCouplingForm_apply_normalModelStructure`). So `ω_N` tames `J_N` at `(z, w)` exactly
when `ω(z)(1, I) + (|w|² / 2) dA(z)(1, I) > 0`
(`TauCeti.forall_normalCouplingForm_apply_normalModelStructure_pos_iff`), and it is then a
symplectic form compatible with `J_N`
(`TauCeti.SymplecticForm.compatible_normalModelStructure_normalModelConnectionCoeff_iff`,
`TauCeti.SymplecticForm.exists_compatible_normalModelStructure_normalModelConnectionCoeff`). For a
flat connection, `dA = 0`, this holds on the whole total space as soon as `ω` is positive, with no
bound on the fibre radius.

## Gauge transformations and integrability

For a real function `φ` on the base, the gauge transformation `Φ(z, w) = (z, exp (i φ(z)) w)`
(`TauCeti.normalModelGauge`, with inverse the gauge transformation of `-φ`) carries the normal
model of `A` to that of `A - dφ`: it is holomorphic for the two normal model structures
(`TauCeti.isJHolomorphicAt_normalModelGauge`), and, where the two connections have the same
curvature, it pulls the coupling form of `A - dφ` back to that of `A`
(`TauCeti.normalCouplingForm_normalModelGauge_apply`). A flat `C¹` connection has local potentials
(`TauCeti.hasLocalPotentials_of_extDeriv_eq_zero`), so over a disc around every point of the base
it is gauge equivalent to the trivial connection. The normal model structure of the trivial
connection is the standard complex structure of `ℂ × ℂ`
(`TauCeti.normalModelStructure_normalModelConnectionCoeff_zero`), and its coupling form is
`π^* ω` plus the area form of the fibre. So the normal model structure of a flat connection is
integrable, and Kähler for the coupling form where `ω` is positive
(`TauCeti.exists_normalModelGauge_of_extDeriv_eq_zero`).

The global questions for a torus, the holonomy of the flat connection and the comparison with the
ambient almost complex structure, are not treated here.

## References

* S. Sternberg, *Minimal coupling and the symplectic mechanics of a classical particle in the
  presence of a Yang–Mills field*, Proc. Nat. Acad. Sci. U.S.A. 74 (1977), 5253–5254.
* C. H. Taubes, *GR = SW: counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
-/

public section

namespace TauCeti

open Complex ComplexConjugate

/-! ### The normal model structure of a connection -/

variable (A : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ)

/-- The coefficient `ν = (I A(1) - A(I)) / 2` of the normal operator `∂bar + ν` of the unitary
connection `d + i A` on the trivial line over `ℂ`: the `(0,1)`-part of `i A`, evaluated on `1`. -/
noncomputable def normalModelConnectionCoeff (z : ℂ) : ℂ :=
  (I * A z (fun _ ↦ 1) - A z (fun _ ↦ I)) / 2

theorem normalModelConnectionCoeff_def (z : ℂ) :
    normalModelConnectionCoeff A z = (I * A z (fun _ ↦ 1) - A z (fun _ ↦ I)) / 2 :=
  (rfl)

/-- The shear `2 I ν(z) conj ξ` of `J_N` in terms of the connection: `-(A(ξ) + I A(I ξ))`. -/
private theorem two_mul_I_mul_normalModelConnectionCoeff_mul_conj (z ξ : ℂ) :
    2 * I * normalModelConnectionCoeff A z * conj ξ =
      -((A z (fun _ ↦ ξ) : ℂ) + I * A z (fun _ ↦ I * ξ)) := by
  have h₁ := (A z).apply_const_eq_re_mul_add_im_mul ξ
  have h₂ := (A z).apply_const_eq_re_mul_add_im_mul (I * ξ)
  simp only [mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, mul_im] at h₂
  rw [h₁, h₂, normalModelConnectionCoeff_def]
  apply Complex.ext <;> simp <;> ring

/-- **The normal model structure of a connection**: at `p = (z, w)`,
`J_N(ξ, η) = (I ξ, I η - (A(ξ) + I A(I ξ)) w)`. -/
theorem normalModelStructure_normalModelConnectionCoeff_apply (p ξ : ℂ × ℂ) :
    normalModelStructure (normalModelConnectionCoeff A) 0 p ξ =
      (I * ξ.1, I * ξ.2 - ((A p.1 (fun _ ↦ ξ.1) : ℂ) + I * A p.1 (fun _ ↦ I * ξ.1)) * p.2) := by
  rw [normalModelStructure_apply]
  congr 1
  have h := two_mul_I_mul_normalModelConnectionCoeff_mul_conj A p.1 ξ.1
  simp only [Pi.zero_apply, zero_mul, add_zero]
  linear_combination p.2 * h

/-- The normal model structure of the trivial connection is the standard complex structure of
`ℂ × ℂ`. -/
@[simp]
theorem normalModelStructure_normalModelConnectionCoeff_zero :
    normalModelStructure (normalModelConnectionCoeff 0) 0 =
      fun _ ↦ AlmostComplexStructure.ofComplexModule (ℂ × ℂ) := by
  funext p
  refine AlmostComplexStructure.ext fun X ↦ ?_
  rw [normalModelStructure_normalModelConnectionCoeff_apply,
    AlmostComplexStructure.ofComplexModule_apply]
  simp [Prod.smul_def]

/-- **Holomorphic sections are the `∇`-holomorphic sections.** A section `s` has `J_N`-holomorphic
graph at `z` exactly when it is differentiable at `z` and `∇_I s = I ∇_1 s` there, with
`∇_v s = ds(v) + i A(v) s` the covariant derivative of the connection `d + i A`. -/
theorem isJHolomorphicAt_graph_normalModelStructure_normalModelConnectionCoeff_iff {s : ℂ → ℂ}
    {z : ℂ} :
    IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
        (normalModelStructure (normalModelConnectionCoeff A) 0) (fun z ↦ (z, s z)) z ↔
      DifferentiableAt ℝ s z ∧ fderiv ℝ s z I + I * A z (fun _ ↦ I) * s z =
        I * (fderiv ℝ s z 1 + I * A z (fun _ ↦ 1) * s z) := by
  rw [isJHolomorphicAt_graph_normalModelStructure_iff]
  refine and_congr_right fun _ ↦ ?_
  rw [conjWirtingerDeriv_apply, normalModelConnectionCoeff_def]
  simp only [Pi.zero_apply, zero_mul, add_zero, smul_eq_mul, mul_one]
  constructor <;> intro h
  · linear_combination (-2 * I) * h + fderiv ℝ s z I * I_sq
  · linear_combination (I / 2) * h + (fderiv ℝ s z 1 / 2 - A z (fun _ ↦ I) * s z / 2 +
      I * A z (fun _ ↦ 1) * s z / 2) * I_sq

/-- The **covariant derivative** `∇_X w = η + i A(z)(ξ) w` of the fibre coordinate along a tangent
vector `X = (ξ, η)` at `p = (z, w)`, for the connection `d + i A`: the vertical part of `X`, which
is `X` minus the horizontal lift `(ξ, -i A(z)(ξ) w)` of `ξ`. -/
noncomputable def normalCovariantDeriv (p X : ℂ × ℂ) : ℂ :=
  X.2 + I * A p.1 (fun _ ↦ X.1) * p.2

theorem normalCovariantDeriv_def (p X : ℂ × ℂ) :
    normalCovariantDeriv A p X = X.2 + I * A p.1 (fun _ ↦ X.1) * p.2 :=
  (rfl)

/-- `J_N` acts on vertical parts as multiplication by `I`: `∇_{J_N X} w = I ∇_X w`. So `J_N`
preserves the horizontal distribution of the connection. -/
theorem normalCovariantDeriv_normalModelStructure (p X : ℂ × ℂ) :
    normalCovariantDeriv A p (normalModelStructure (normalModelConnectionCoeff A) 0 p X) =
      I * normalCovariantDeriv A p X := by
  rw [normalModelStructure_normalModelConnectionCoeff_apply, normalCovariantDeriv_def,
    normalCovariantDeriv_def]
  ring_nf
  simp only [I_sq]
  ring

/-! ### Compatibility of the coupling form -/

variable {ω : ℂ → ℂ [⋀^Fin 2]→L[ℝ] ℝ} {A} {p : ℂ × ℂ}

/-- **The coupling form in terms of the covariant derivative** of the fibre coordinate: at
`p = (z, w)`, `ω_N(X, Y) = ω(ξ, ξ') + ω_ℂ(∇_X w, ∇_Y w) + (|w|² / 2) dA(ξ, ξ')`, with `ω_ℂ` the
area form of the fibre. -/
theorem normalCouplingForm_apply_eq_normalCovariantDeriv (hA : DifferentiableAt ℝ A p.1)
    (X Y : ℂ × ℂ) :
    normalCouplingForm ω A p ![X, Y] =
      ω p.1 ![X.1, Y.1] +
        stdComplexSymplecticForm (normalCovariantDeriv A p X) (normalCovariantDeriv A p Y) +
          normSq p.2 / 2 * extDeriv A p.1 ![X.1, Y.1] := by
  rw [normalCouplingForm_apply_pair (w := p.2) hA X.1 Y.1 X.2 Y.2, stdComplexSymplecticForm_apply,
    normalCovariantDeriv_def, normalCovariantDeriv_def, mul_im, conj_re, conj_im]
  ring

/-- **The coupling form is `J_N`-invariant**: `ω_N(J_N X, J_N Y) = ω_N(X, Y)`. -/
theorem normalCouplingForm_apply_normalModelStructure_normalModelStructure
    (hA : DifferentiableAt ℝ A p.1) (X Y : ℂ × ℂ) :
    normalCouplingForm ω A p ![normalModelStructure (normalModelConnectionCoeff A) 0 p X,
        normalModelStructure (normalModelConnectionCoeff A) 0 p Y] =
      normalCouplingForm ω A p ![X, Y] := by
  rw [normalCouplingForm_apply_eq_normalCovariantDeriv hA,
    normalCouplingForm_apply_eq_normalCovariantDeriv hA,
    normalCovariantDeriv_normalModelStructure, normalCovariantDeriv_normalModelStructure,
    normalModelStructure_normalModelConnectionCoeff_apply,
    normalModelStructure_normalModelConnectionCoeff_apply]
  dsimp only
  rw [ContinuousAlternatingMap.apply_I_mul_I_mul,
    ContinuousAlternatingMap.apply_I_mul_I_mul (extDeriv A p.1)]
  simp only [stdComplexSymplecticForm_mul_mul, norm_I, one_pow, one_mul]

/-- **The metric of the coupling form**:
`ω_N(X, J_N X) = (ω(1, I) + (|w|² / 2) dA(1, I)) |ξ|² + |∇_X w|²` at `p = (z, w)`. -/
theorem normalCouplingForm_apply_normalModelStructure (hA : DifferentiableAt ℝ A p.1)
    (X : ℂ × ℂ) :
    normalCouplingForm ω A p ![X, normalModelStructure (normalModelConnectionCoeff A) 0 p X] =
      (ω p.1 ![1, I] + normSq p.2 / 2 * extDeriv A p.1 ![1, I]) * ‖X.1‖ ^ 2 +
        ‖normalCovariantDeriv A p X‖ ^ 2 := by
  have hv := stdComplexSymplecticForm_apply_ofComplexModule (normalCovariantDeriv A p X)
  rw [AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul] at hv
  rw [normalCouplingForm_apply_eq_normalCovariantDeriv hA,
    normalCovariantDeriv_normalModelStructure,
    normalModelStructure_normalModelConnectionCoeff_apply]
  dsimp only
  rw [ContinuousAlternatingMap.apply_I_mul_eq_apply_one_I_mul_norm_sq,
    ContinuousAlternatingMap.apply_I_mul_eq_apply_one_I_mul_norm_sq (extDeriv A p.1),
    ← normSq_eq_norm_sq (normalCovariantDeriv A p X)]
  simp only [hv]
  ring

/-- **Taming criterion.** The coupling form tames `J_N` at `p = (z, w)` exactly when
`ω(z)(1, I) + (|w|² / 2) dA(z)(1, I) > 0`. -/
theorem forall_normalCouplingForm_apply_normalModelStructure_pos_iff
    (hA : DifferentiableAt ℝ A p.1) :
    (∀ X : ℂ × ℂ, X ≠ 0 → 0 < normalCouplingForm ω A p
        ![X, normalModelStructure (normalModelConnectionCoeff A) 0 p X]) ↔
      0 < ω p.1 ![1, I] + normSq p.2 / 2 * extDeriv A p.1 ![1, I] := by
  constructor
  · intro h
    -- the horizontal lift of `1` has no vertical part
    have hX := h (1, -(I * A p.1 (fun _ ↦ 1) * p.2)) (by simp [Prod.ext_iff])
    have hv : normalCovariantDeriv A p (1, -(I * A p.1 (fun _ ↦ 1) * p.2)) = 0 := by
      simp [normalCovariantDeriv_def]
    rw [normalCouplingForm_apply_normalModelStructure hA, hv] at hX
    simpa using hX
  · intro hc X hX
    rw [normalCouplingForm_apply_normalModelStructure hA]
    rcases eq_or_ne X.1 0 with h₁ | h₁
    · have h₂ : X.2 ≠ 0 := fun h₂ ↦ hX (Prod.ext h₁ h₂)
      have hA₀ : A p.1 (fun _ ↦ (0 : ℂ)) = 0 := (A p.1).map_coord_zero (m := fun _ ↦ 0) 0 rfl
      have hv : normalCovariantDeriv A p X = X.2 := by
        simp [normalCovariantDeriv_def, h₁, hA₀]
      have := norm_pos_iff.2 h₂
      rw [hv, h₁, norm_zero]
      positivity
    · have := norm_pos_iff.2 h₁
      positivity

/-! ### Gauge transformations -/

/-- The **gauge transformation** `(z, w) ↦ (z, exp (i φ(z)) w)` of the trivial line over `ℂ`, for
a real function `φ` on the base. -/
noncomputable def normalModelGauge (φ : ℂ → ℝ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.1, exp (φ p.1 * I) * p.2)

@[simp]
theorem normalModelGauge_fst (φ : ℂ → ℝ) (p : ℂ × ℂ) : (normalModelGauge φ p).1 = p.1 :=
  (rfl)

@[simp]
theorem normalModelGauge_snd (φ : ℂ → ℝ) (p : ℂ × ℂ) :
    (normalModelGauge φ p).2 = exp (φ p.1 * I) * p.2 :=
  (rfl)

/-- The gauge transformation of `-φ` inverts that of `φ`. -/
@[simp]
theorem normalModelGauge_neg_normalModelGauge (φ : ℂ → ℝ) (p : ℂ × ℂ) :
    normalModelGauge (-φ) (normalModelGauge φ p) = p := by
  ext
  · rfl
  · simp only [normalModelGauge_snd, normalModelGauge_fst, Pi.neg_apply, ofReal_neg, neg_mul,
      ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-- The gauge transformation of `φ` inverts that of `-φ`. -/
@[simp]
theorem normalModelGauge_normalModelGauge_neg (φ : ℂ → ℝ) (p : ℂ × ℂ) :
    normalModelGauge φ (normalModelGauge (-φ) p) = p := by
  simpa using normalModelGauge_neg_normalModelGauge (-φ) p

variable {φ : ℂ → ℝ}

/-- The derivative of the phase `exp (i φ(z))`. -/
private theorem hasFDerivAt_exp_ofReal_mul_I (hφ : DifferentiableAt ℝ φ p.1) :
    HasFDerivAt (fun q : ℂ × ℂ ↦ exp (φ q.1 * I))
      (exp (φ p.1 * I) • (I • (Complex.ofRealCLM.comp ((fderiv ℝ φ p.1).comp
        (ContinuousLinearMap.fst ℝ ℂ ℂ))))) p := by
  have h₁ : HasFDerivAt (fun q : ℂ × ℂ ↦ (φ q.1 : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ φ p.1).comp (ContinuousLinearMap.fst ℝ ℂ ℂ))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (hφ.hasFDerivAt.comp p hasFDerivAt_fst)
  have h₂ := (h₁.mul_const I).cexp
  convert h₂ using 2

/-- The gauge transformation is differentiable over every point where `φ` is. -/
theorem differentiableAt_normalModelGauge (hφ : DifferentiableAt ℝ φ p.1) :
    DifferentiableAt ℝ (normalModelGauge φ) p :=
  differentiableAt_fst.prodMk
    ((hasFDerivAt_exp_ofReal_mul_I hφ).differentiableAt.mul differentiableAt_snd)

/-- The derivative of the gauge transformation:
`D(z, w)(ξ, η) = (ξ, exp (i φ(z)) (η + i dφ(z)(ξ) w))`. -/
theorem fderiv_normalModelGauge_apply (hφ : DifferentiableAt ℝ φ p.1) (X : ℂ × ℂ) :
    fderiv ℝ (normalModelGauge φ) p X =
      (X.1, exp (φ p.1 * I) * (X.2 + I * fderiv ℝ φ p.1 X.1 * p.2)) := by
  have h : HasFDerivAt (normalModelGauge φ) ((ContinuousLinearMap.fst ℝ ℂ ℂ).prod _) p :=
    hasFDerivAt_fst.prodMk ((hasFDerivAt_exp_ofReal_mul_I hφ).mul hasFDerivAt_snd)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    add_apply, smul_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_comp, Function.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    Prod.mk.injEq, true_and]
  ring


variable {A' : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ}

/-- The gauge transformation of `φ` carries the covariant derivative of `A` to that of `A - dφ`,
multiplied by the phase `exp (i φ)`. -/
theorem normalCovariantDeriv_normalModelGauge (hφ : DifferentiableAt ℝ φ p.1)
    (hA' : ∀ v, A' p.1 (fun _ ↦ v) = A p.1 (fun _ ↦ v) - fderiv ℝ φ p.1 v) (X : ℂ × ℂ) :
    normalCovariantDeriv A' (normalModelGauge φ p) (fderiv ℝ (normalModelGauge φ) p X) =
      exp (φ p.1 * I) * normalCovariantDeriv A p X := by
  rw [fderiv_normalModelGauge_apply hφ, normalCovariantDeriv_def, normalCovariantDeriv_def,
    normalModelGauge_fst, normalModelGauge_snd, hA' X.1]
  push_cast
  ring

/-- **Gauge transformations are holomorphic.** If `A' = A - dφ` at `z`, the gauge transformation
of `φ` is holomorphic, at every point over `z`, from the normal model structure of `A` to that of
`A'`. -/
theorem isJHolomorphicAt_normalModelGauge (hφ : DifferentiableAt ℝ φ p.1)
    (hA' : ∀ v, A' p.1 (fun _ ↦ v) = A p.1 (fun _ ↦ v) - fderiv ℝ φ p.1 v) :
    IsJHolomorphicAt (normalModelStructure (normalModelConnectionCoeff A) 0)
      (normalModelStructure (normalModelConnectionCoeff A') 0) (normalModelGauge φ) p := by
  refine isJHolomorphicAt_of_hasFDerivAt (differentiableAt_normalModelGauge hφ).hasFDerivAt ?_
  rw [isComplexLinearMap_iff_apply]
  intro X
  simp only [ContinuousLinearMap.coe_coe, fderiv_normalModelGauge_apply hφ,
    normalModelStructure_normalModelConnectionCoeff_apply, normalModelGauge_fst,
    normalModelGauge_snd, hA']
  ext
  · rfl
  · simp only [ofReal_sub]
    ring_nf
    rw [I_sq]
    ring

/-- **Gauge transformations preserve the coupling form.** If `A' = A - dφ` at `z` and `A'` has the
same curvature as `A` there, as when `φ` is `C²`, the gauge transformation of `φ` pulls the
coupling form of `A'` back to that of `A` at every point over `z`. -/
theorem normalCouplingForm_normalModelGauge_apply (hφ : DifferentiableAt ℝ φ p.1)
    (hA : DifferentiableAt ℝ A p.1) (hA'd : DifferentiableAt ℝ A' p.1)
    (hA' : ∀ v, A' p.1 (fun _ ↦ v) = A p.1 (fun _ ↦ v) - fderiv ℝ φ p.1 v)
    (hdA : extDeriv A' p.1 = extDeriv A p.1) (X Y : ℂ × ℂ) :
    normalCouplingForm ω A' (normalModelGauge φ p)
        ![fderiv ℝ (normalModelGauge φ) p X, fderiv ℝ (normalModelGauge φ) p Y] =
      normalCouplingForm ω A p ![X, Y] := by
  rw [normalCouplingForm_apply_eq_normalCovariantDeriv (p := normalModelGauge φ p) hA'd,
    normalCouplingForm_apply_eq_normalCovariantDeriv hA,
    normalCovariantDeriv_normalModelGauge hφ hA', normalCovariantDeriv_normalModelGauge hφ hA',
    stdComplexSymplecticForm_mul_mul, norm_exp_ofReal_mul_I, one_pow, one_mul]
  simp only [normalModelGauge_fst, normalModelGauge_snd, fderiv_normalModelGauge_apply hφ, hdA,
    normSq_mul, normSq_eq_norm_sq (exp _), norm_exp_ofReal_mul_I, one_pow, one_mul]

/-- **Flat connections are locally trivial.** Let `A` be a `C¹` connection with vanishing
curvature `dA = 0` on an open set `s` of the base. Every point of `s` has a disc in `s` and a gauge
transformation `Φ` over it that is holomorphic from the normal model structure of `A` to the
standard complex structure of `ℂ × ℂ`, and pulls the coupling form of the trivial connection,
`π^* ω` plus the area form of the fibre, back to the coupling form of `A`. The inverse of `Φ` is
the gauge transformation of `-φ` (`TauCeti.normalModelGauge_neg_normalModelGauge`). So the normal
model structure of a flat connection is integrable. -/
theorem exists_normalModelGauge_of_extDeriv_eq_zero {s : Set ℂ} (hs : IsOpen s)
    (hA : ContDiffOn ℝ 1 A s) (hdA : ∀ z ∈ s, extDeriv A z = 0) {z₀ : ℂ} (hz₀ : z₀ ∈ s) :
    ∃ r > 0, Metric.ball z₀ r ⊆ s ∧ ∃ φ : ℂ → ℝ, ∀ p : ℂ × ℂ, p.1 ∈ Metric.ball z₀ r →
      IsJHolomorphicAt (normalModelStructure (normalModelConnectionCoeff A) 0)
        (fun _ ↦ AlmostComplexStructure.ofComplexModule (ℂ × ℂ)) (normalModelGauge φ) p ∧
      ∀ X Y, normalCouplingForm ω 0 (normalModelGauge φ p)
          ![fderiv ℝ (normalModelGauge φ) p X, fderiv ℝ (normalModelGauge φ) p Y] =
        normalCouplingForm ω A p ![X, Y] := by
  -- the one-form `A` as a field of linear maps
  set e := ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℂ) (F := ℝ) (0 : Fin 1)
  have he (z : ℂ) : e (e.symm (A z)) = A z := e.apply_symm_apply _
  obtain ⟨r, hr, hrs, φ, -, hφ⟩ := hasLocalPotentials_iff.1
    (hasLocalPotentials_of_extDeriv_eq_zero (φ := fun z ↦ e.symm (A z)) hs
      (e.symm.contDiff.comp_contDiffOn hA)
      fun z hz ↦ (congrArg (extDeriv · z) (funext he)).trans (hdA z hz)) z₀ hz₀
  refine ⟨r, hr, hrs, φ, fun p hp ↦ ?_⟩
  have hφp := hφ p.1 hp
  have hA' (v : ℂ) : (0 : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ) p.1 (fun _ ↦ v) =
      A p.1 (fun _ ↦ v) - fderiv ℝ φ p.1 v := by
    rw [hφp.fderiv, ← he p.1]
    simp [e]
  have hAp : DifferentiableAt ℝ A p.1 :=
    (hA.contDiffAt (hs.mem_nhds (hrs hp))).differentiableAt one_ne_zero
  refine ⟨?_, normalCouplingForm_normalModelGauge_apply hφp.differentiableAt hAp
    (differentiableAt_const _) hA' ?_⟩
  · simpa using isJHolomorphicAt_normalModelGauge (A' := 0) hφp.differentiableAt hA'
  · rw [hdA p.1 (hrs hp)]
    exact congrFun (ContinuousAlternatingMap.extDeriv_const 0) p.1

end TauCeti

namespace TauCeti.SymplecticForm

open Complex

variable {ω : ℂ → ℂ [⋀^Fin 2]→L[ℝ] ℝ} {A : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ} {p : ℂ × ℂ}

/-- **Compatibility criterion.** A symplectic form with the values of the coupling form at
`p = (z, w)` is compatible with `J_N` exactly when `ω(z)(1, I) + (|w|² / 2) dA(z)(1, I) > 0`. -/
theorem compatible_normalModelStructure_normalModelConnectionCoeff_iff
    (hA : DifferentiableAt ℝ A p.1) {σ : SymplecticForm (ℂ × ℂ)}
    (hσ : ∀ X Y, σ X Y = normalCouplingForm ω A p ![X, Y]) :
    σ.Compatible (normalModelStructure (normalModelConnectionCoeff A) 0 p) ↔
      0 < ω p.1 ![1, I] + normSq p.2 / 2 * extDeriv A p.1 ![1, I] := by
  rw [compatible_iff, invariant_iff,
    ← forall_normalCouplingForm_apply_normalModelStructure_pos_iff hA]
  simp only [Tames, hσ, normalCouplingForm_apply_normalModelStructure_normalModelStructure hA,
    implies_true, true_and]

/-- **The coupling form is compatible with `J_N`** at every point `p = (z, w)` with
`ω(z)(1, I) + (|w|² / 2) dA(z)(1, I) > 0`: it is then a symplectic form, compatible with
`J_N`. -/
theorem exists_compatible_normalModelStructure_normalModelConnectionCoeff
    (hA : DifferentiableAt ℝ A p.1)
    (hc : 0 < ω p.1 ![1, I] + normSq p.2 / 2 * extDeriv A p.1 ![1, I]) :
    ∃ σ : SymplecticForm (ℂ × ℂ), (∀ X Y, σ X Y = normalCouplingForm ω A p ![X, Y]) ∧
      σ.Compatible (normalModelStructure (normalModelConnectionCoeff A) 0 p) := by
  set Ω := normalCouplingForm ω A p
  have hB (X Y : ℂ × ℂ) : Ω.toAlternatingMap.toMultilinearMap.toBilinMap X Y = Ω ![X, Y] :=
    MultilinearMap.toBilinMap_apply _ X Y
  let σ := ofTames _ Ω.toAlternatingMap.isAlt_toBilinMap fun X hX ↦ by
    rw [hB]
    exact (forall_normalCouplingForm_apply_normalModelStructure_pos_iff hA).2 hc X hX
  have hσ (X Y : ℂ × ℂ) : σ X Y = Ω ![X, Y] := (ofTames_apply _ _ X Y).trans (hB X Y)
  exact ⟨σ, hσ, (compatible_normalModelStructure_normalModelConnectionCoeff_iff hA hσ).2 hc⟩

end TauCeti.SymplecticForm
