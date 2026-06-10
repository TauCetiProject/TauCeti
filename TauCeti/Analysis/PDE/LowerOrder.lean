/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Lower-order pointwise forms for divergence-form PDEs

The divergence-form roadmap keeps the principal elliptic coefficient, first-order drift,
and zeroth-order mass coefficient as separate named hypotheses.  The principal matrix
coefficient lives in `TauCeti.Analysis.PDE.UniformEllipticity`; this file records the
pointwise explicit bounds for the lower-order terms

* `u ↦ b(x) · ∇u`, represented by `driftForm (b x)`;
* `u ↦ c(x) u`, represented in the weak form by `massForm (c x)`.

These are only pointwise finite-dimensional estimates, later integrated over `Ω` once the
weak-derivative Sobolev spaces are available.

## Main declarations

* `TauCeti.PDE.LowerOrderBoundedOn`: explicit bounds for drift and mass coefficients on a
  domain.
* `TauCeti.PDE.NonnegMassOn`: nonnegative bounded mass coefficients.
* `TauCeti.PDE.driftForm`, `TauCeti.PDE.massForm`: named pointwise lower-order forms.
-/

namespace TauCeti

namespace PDE

open scoped InnerProductSpace

variable {X n : Type*} [Fintype n]

/-- The pointwise first-order drift form `(u, ξ) ↦ ⟪b, ξ⟫ u`. -/
noncomputable def driftForm (b : EuclideanSpace ℝ n) :
    ℝ →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ n) ℝ (innerSL ℝ b)

/-- The pointwise zeroth-order mass form `(u, v) ↦ c u v`. -/
noncomputable def massForm (c : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  c • ContinuousLinearMap.mul ℝ ℝ

/-- Applying the drift form is the scalar product with the drift coefficient times `u`. -/
@[simp]
lemma driftForm_apply (b : EuclideanSpace ℝ n) (u : ℝ) (ξ : EuclideanSpace ℝ n) :
    driftForm b u ξ = ⟪b, ξ⟫_ℝ * u := by
  rw [driftForm, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]

/-- Applying the mass form is multiplication by the mass coefficient. -/
@[simp]
lemma massForm_apply (c u v : ℝ) :
    massForm c u v = c * u * v := by
  rw [massForm, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul]
  ring

/-- Bounded lower-order coefficients on a domain, with explicit constants.

`LowerOrderBoundedOn Ω b c beta gamma` means that on `Ω`, the drift coefficient vector
has norm at most `beta` and the mass coefficient has absolute value at most `gamma`. -/
def LowerOrderBoundedOn (Ω : Set X) (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (beta gamma : ℝ) : Prop :=
  0 ≤ beta ∧ 0 ≤ gamma ∧
    ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta ∧ ‖c x‖ ≤ gamma

/-- Characteristic restatement of bounded lower-order coefficients. -/
lemma lowerOrderBoundedOn_iff {Ω : Set X} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
    {beta gamma : ℝ} :
    LowerOrderBoundedOn Ω b c beta gamma ↔
      0 ≤ beta ∧ 0 ≤ gamma ∧
        ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta ∧ ‖c x‖ ≤ gamma :=
  Iff.rfl

namespace LowerOrderBoundedOn

variable {Ω Ω' : Set X} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
variable {beta gamma beta' gamma' : ℝ}

/-- The drift bound is nonnegative. -/
@[grind →]
lemma beta_nonneg (h : LowerOrderBoundedOn Ω b c beta gamma) : 0 ≤ beta :=
  h.1

/-- The mass bound is nonnegative. -/
@[grind →]
lemma gamma_nonneg (h : LowerOrderBoundedOn Ω b c beta gamma) : 0 ≤ gamma :=
  h.2.1

/-- The pointwise drift coefficient bound. -/
@[grind =>]
lemma drift_bound (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X} (hx : x ∈ Ω) :
    ‖b x‖ ≤ beta :=
  (h.2.2 hx).1

/-- The pointwise mass coefficient bound. -/
@[grind =>]
lemma mass_bound (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X} (hx : x ∈ Ω) :
    ‖c x‖ ≤ gamma :=
  (h.2.2 hx).2

/-- Restricting the domain preserves bounded lower-order coefficients. -/
lemma mono_set (h : LowerOrderBoundedOn Ω b c beta gamma) (hΩ : Ω' ⊆ Ω) :
    LowerOrderBoundedOn Ω' b c beta gamma :=
  ⟨h.beta_nonneg, h.gamma_nonneg, fun {_} hx => h.2.2 (hΩ hx)⟩

/-- Increasing either bound preserves bounded lower-order coefficients. -/
lemma mono_constants (h : LowerOrderBoundedOn Ω b c beta gamma)
    (hbeta : beta ≤ beta') (hgamma : gamma ≤ gamma') :
    LowerOrderBoundedOn Ω b c beta' gamma' :=
  ⟨h.beta_nonneg.trans hbeta, h.gamma_nonneg.trans hgamma,
    fun {_} hx => ⟨(h.drift_bound hx).trans hbeta, (h.mass_bound hx).trans hgamma⟩⟩

/-- Constructor from separate side conditions and pointwise bounds. -/
lemma of_bounds (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → ‖c x‖ ≤ gamma) :
    LowerOrderBoundedOn Ω b c beta gamma :=
  ⟨hbeta, hgamma, fun {_} hx => ⟨hb hx, hc hx⟩⟩

/-- Pointwise boundedness of the drift form supplied by bounded lower-order coefficients. -/
@[grind =>]
lemma norm_driftForm_le (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X}
    (hx : x ∈ Ω) (u : ℝ) (ξ : EuclideanSpace ℝ n) :
    ‖driftForm (b x) u ξ‖ ≤ beta * ‖u‖ * ‖ξ‖ := by
  rw [driftForm_apply, norm_mul]
  calc
    ‖⟪b x, ξ⟫_ℝ‖ * ‖u‖ ≤ (‖b x‖ * ‖ξ‖) * ‖u‖ := by
      gcongr
      exact norm_inner_le_norm (b x) ξ
    _ ≤ (beta * ‖ξ‖) * ‖u‖ := by
      gcongr
      exact h.drift_bound hx
    _ = beta * ‖u‖ * ‖ξ‖ := by ring

/-- Operator-norm boundedness of the drift form supplied by bounded lower-order coefficients. -/
@[grind =>]
lemma opNorm_driftForm_le (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X}
    (hx : x ∈ Ω) :
    ‖driftForm (b x)‖ ≤ beta := by
  rw [driftForm, ContinuousLinearMap.norm_smulRightL, innerSL_apply_norm]
  exact h.drift_bound hx

/-- Pointwise boundedness of the mass form supplied by bounded lower-order coefficients. -/
@[grind =>]
lemma norm_massForm_le (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X}
    (hx : x ∈ Ω) (u v : ℝ) :
    ‖massForm (c x) u v‖ ≤ gamma * ‖u‖ * ‖v‖ := by
  rw [massForm_apply, norm_mul, norm_mul]
  calc
    ‖c x‖ * ‖u‖ * ‖v‖ ≤ gamma * ‖u‖ * ‖v‖ := by
      gcongr
      exact h.mass_bound hx

/-- Operator-norm boundedness of the mass form supplied by bounded lower-order coefficients. -/
@[grind =>]
lemma opNorm_massForm_le (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X}
    (hx : x ∈ Ω) :
    ‖massForm (c x)‖ ≤ gamma := by
  calc
    ‖massForm (c x)‖ ≤ ‖c x‖ * ‖ContinuousLinearMap.mul ℝ ℝ‖ := by
      rw [massForm]
      exact ContinuousLinearMap.opNorm_smul_le (c x) (ContinuousLinearMap.mul ℝ ℝ)
    _ ≤ ‖c x‖ * 1 := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    _ = ‖c x‖ := by ring
    _ ≤ gamma := h.mass_bound hx

end LowerOrderBoundedOn

/-- Nonnegative bounded zeroth-order coefficients on a domain. -/
def NonnegMassOn (Ω : Set X) (c : X → ℝ) (gamma : ℝ) : Prop :=
  0 ≤ gamma ∧ ∀ ⦃x⦄, x ∈ Ω → 0 ≤ c x ∧ c x ≤ gamma

/-- Characteristic restatement of nonnegative bounded mass coefficients. -/
lemma nonnegMassOn_iff {Ω : Set X} {c : X → ℝ} {gamma : ℝ} :
    NonnegMassOn Ω c gamma ↔
      0 ≤ gamma ∧ ∀ ⦃x⦄, x ∈ Ω → 0 ≤ c x ∧ c x ≤ gamma :=
  Iff.rfl

namespace NonnegMassOn

variable {Ω Ω' : Set X} {c : X → ℝ} {gamma gamma' : ℝ}

/-- The mass bound is nonnegative. -/
@[grind →]
lemma gamma_nonneg (h : NonnegMassOn Ω c gamma) : 0 ≤ gamma :=
  h.1

/-- The mass coefficient is pointwise nonnegative. -/
@[grind =>]
lemma nonneg (h : NonnegMassOn Ω c gamma) {x : X} (hx : x ∈ Ω) : 0 ≤ c x :=
  (h.2 hx).1

/-- The mass coefficient is pointwise bounded above. -/
@[grind =>]
lemma upper_bound (h : NonnegMassOn Ω c gamma) {x : X} (hx : x ∈ Ω) :
    c x ≤ gamma :=
  (h.2 hx).2

/-- A nonnegative bounded mass coefficient is absolutely bounded. -/
@[grind =>]
lemma norm_bound (h : NonnegMassOn Ω c gamma) {x : X} (hx : x ∈ Ω) :
    ‖c x‖ ≤ gamma := by
  simpa [Real.norm_eq_abs, abs_of_nonneg (h.nonneg hx)] using h.upper_bound hx

/-- Restricting the domain preserves nonnegative bounded mass coefficients. -/
lemma mono_set (h : NonnegMassOn Ω c gamma) (hΩ : Ω' ⊆ Ω) :
    NonnegMassOn Ω' c gamma :=
  ⟨h.gamma_nonneg, fun {_} hx => h.2 (hΩ hx)⟩

/-- Increasing the upper bound preserves nonnegative bounded mass coefficients. -/
lemma mono_constant (h : NonnegMassOn Ω c gamma) (hgamma : gamma ≤ gamma') :
    NonnegMassOn Ω c gamma' :=
  ⟨h.gamma_nonneg.trans hgamma,
    fun {_} hx => ⟨h.nonneg hx, (h.upper_bound hx).trans hgamma⟩⟩

/-- Nonnegative bounded mass coefficients produce lower-order bounds with zero drift. -/
lemma lowerOrderBoundedOn_zero_drift (h : NonnegMassOn Ω c gamma) :
    LowerOrderBoundedOn Ω (fun _ => (0 : EuclideanSpace ℝ n)) c 0 gamma :=
  LowerOrderBoundedOn.of_bounds le_rfl h.gamma_nonneg
    (fun {_} _ => by simp) (fun {_} hx => h.norm_bound hx)

end NonnegMassOn

/-- Zero lower-order coefficients are bounded by zero. -/
lemma lowerOrderBoundedOn_zero (Ω : Set X) :
    LowerOrderBoundedOn Ω (fun _ => (0 : EuclideanSpace ℝ n)) (fun _ => 0) 0 0 :=
  LowerOrderBoundedOn.of_bounds le_rfl le_rfl (fun {_} _ => by simp) (fun {_} _ => by simp)

/-- A constant nonnegative mass coefficient is nonnegative and bounded by itself. -/
lemma nonnegMassOn_const_self (Ω : Set X) {c : ℝ} (hc : 0 ≤ c) :
    NonnegMassOn Ω (fun _ => c) c :=
  ⟨hc, fun {_} _ => ⟨hc, le_rfl⟩⟩

end PDE

end TauCeti
