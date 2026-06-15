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

* `TauCeti.PDE.DriftBoundedOn`, `TauCeti.PDE.MassBoundedOn`: explicit separate bounds for
  drift and mass coefficients on a domain.
* `TauCeti.PDE.LowerOrderBoundedOn`: the bundled lower-order bounds.
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
  rw [massForm, smul_apply, smul_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul]
  ring

/-- Bounded drift coefficients on a domain, with an explicit constant. -/
def DriftBoundedOn (Ω : Set X) (b : X → EuclideanSpace ℝ n) (beta : ℝ) : Prop :=
  0 ≤ beta ∧ ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta

/-- Characteristic restatement of bounded drift coefficients. -/
lemma driftBoundedOn_iff {Ω : Set X} {b : X → EuclideanSpace ℝ n} {beta : ℝ} :
    DriftBoundedOn Ω b beta ↔
      0 ≤ beta ∧ ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta :=
  Iff.rfl

namespace DriftBoundedOn

variable {Ω Ω' : Set X} {b : X → EuclideanSpace ℝ n} {beta beta' : ℝ}

/-- The drift bound is nonnegative. -/
@[grind →]
lemma beta_nonneg (h : DriftBoundedOn Ω b beta) : 0 ≤ beta :=
  h.1

/-- The pointwise drift coefficient bound. -/
@[grind =>]
lemma bound (h : DriftBoundedOn Ω b beta) {x : X} (hx : x ∈ Ω) :
    ‖b x‖ ≤ beta :=
  h.2 hx

/-- Restricting the domain preserves bounded drift coefficients. -/
lemma mono_set (h : DriftBoundedOn Ω b beta) (hΩ : Ω' ⊆ Ω) :
    DriftBoundedOn Ω' b beta :=
  ⟨h.beta_nonneg, fun {_} hx => h.bound (hΩ hx)⟩

/-- Increasing the bound preserves bounded drift coefficients. -/
lemma mono_constant (h : DriftBoundedOn Ω b beta) (hbeta : beta ≤ beta') :
    DriftBoundedOn Ω b beta' :=
  ⟨h.beta_nonneg.trans hbeta, fun {_} hx => (h.bound hx).trans hbeta⟩

/-- Constructor from separate side conditions and pointwise bounds. -/
lemma of_bound (hbeta : 0 ≤ beta) (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta) :
    DriftBoundedOn Ω b beta :=
  ⟨hbeta, hb⟩

/-- Pointwise boundedness of the drift form supplied by a drift coefficient bound. -/
@[grind =>]
lemma norm_driftForm_le (h : DriftBoundedOn Ω b beta) {x : X}
    (hx : x ∈ Ω) (u : ℝ) (ξ : EuclideanSpace ℝ n) :
    ‖driftForm (b x) u ξ‖ ≤ beta * ‖u‖ * ‖ξ‖ := by
  rw [driftForm_apply, norm_mul]
  calc
    ‖⟪b x, ξ⟫_ℝ‖ * ‖u‖ ≤ (‖b x‖ * ‖ξ‖) * ‖u‖ := by
      gcongr
      exact norm_inner_le_norm (b x) ξ
    _ ≤ (beta * ‖ξ‖) * ‖u‖ := by
      gcongr
      exact h.bound hx
    _ = beta * ‖u‖ * ‖ξ‖ := by ring

/-- Operator-norm boundedness of the drift form supplied by a drift coefficient bound. -/
@[grind =>]
lemma opNorm_driftForm_le (h : DriftBoundedOn Ω b beta) {x : X}
    (hx : x ∈ Ω) :
    ‖driftForm (b x)‖ ≤ beta := by
  rw [driftForm, ContinuousLinearMap.norm_smulRightL, innerSL_apply_norm]
  exact h.bound hx

end DriftBoundedOn

/-- Bounded mass coefficients on a domain, with an explicit constant. -/
def MassBoundedOn (Ω : Set X) (c : X → ℝ) (gamma : ℝ) : Prop :=
  0 ≤ gamma ∧ ∀ ⦃x⦄, x ∈ Ω → ‖c x‖ ≤ gamma

/-- Characteristic restatement of bounded mass coefficients. -/
lemma massBoundedOn_iff {Ω : Set X} {c : X → ℝ} {gamma : ℝ} :
    MassBoundedOn Ω c gamma ↔
      0 ≤ gamma ∧ ∀ ⦃x⦄, x ∈ Ω → ‖c x‖ ≤ gamma :=
  Iff.rfl

namespace MassBoundedOn

variable {Ω Ω' : Set X} {c : X → ℝ} {gamma gamma' : ℝ}

/-- The mass bound is nonnegative. -/
@[grind →]
lemma gamma_nonneg (h : MassBoundedOn Ω c gamma) : 0 ≤ gamma :=
  h.1

/-- The pointwise mass coefficient bound. -/
@[grind =>]
lemma bound (h : MassBoundedOn Ω c gamma) {x : X} (hx : x ∈ Ω) :
    ‖c x‖ ≤ gamma :=
  h.2 hx

/-- Restricting the domain preserves bounded mass coefficients. -/
lemma mono_set (h : MassBoundedOn Ω c gamma) (hΩ : Ω' ⊆ Ω) :
    MassBoundedOn Ω' c gamma :=
  ⟨h.gamma_nonneg, fun {_} hx => h.bound (hΩ hx)⟩

/-- Increasing the bound preserves bounded mass coefficients. -/
lemma mono_constant (h : MassBoundedOn Ω c gamma) (hgamma : gamma ≤ gamma') :
    MassBoundedOn Ω c gamma' :=
  ⟨h.gamma_nonneg.trans hgamma, fun {_} hx => (h.bound hx).trans hgamma⟩

/-- Constructor from separate side conditions and pointwise bounds. -/
lemma of_bound (hgamma : 0 ≤ gamma) (hc : ∀ ⦃x⦄, x ∈ Ω → ‖c x‖ ≤ gamma) :
    MassBoundedOn Ω c gamma :=
  ⟨hgamma, hc⟩

/-- Pointwise boundedness of the mass form supplied by a mass coefficient bound. -/
@[grind =>]
lemma norm_massForm_le (h : MassBoundedOn Ω c gamma) {x : X}
    (hx : x ∈ Ω) (u v : ℝ) :
    ‖massForm (c x) u v‖ ≤ gamma * ‖u‖ * ‖v‖ := by
  rw [massForm_apply, norm_mul, norm_mul]
  calc
    ‖c x‖ * ‖u‖ * ‖v‖ ≤ gamma * ‖u‖ * ‖v‖ := by
      gcongr
      exact h.bound hx

/-- Operator-norm boundedness of the mass form supplied by a mass coefficient bound. -/
@[grind =>]
lemma opNorm_massForm_le (h : MassBoundedOn Ω c gamma) {x : X}
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
    _ ≤ gamma := h.bound hx

end MassBoundedOn

/-- Bounded lower-order coefficients on a domain, with explicit constants.

`LowerOrderBoundedOn Ω b c beta gamma` means that on `Ω`, the drift coefficient vector
has norm at most `beta` and the mass coefficient has absolute value at most `gamma`. -/
def LowerOrderBoundedOn (Ω : Set X) (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (beta gamma : ℝ) : Prop :=
  DriftBoundedOn Ω b beta ∧ MassBoundedOn Ω c gamma

/-- Characteristic restatement of bounded lower-order coefficients. -/
lemma lowerOrderBoundedOn_iff {Ω : Set X} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
    {beta gamma : ℝ} :
    LowerOrderBoundedOn Ω b c beta gamma ↔
      DriftBoundedOn Ω b beta ∧ MassBoundedOn Ω c gamma :=
  Iff.rfl

namespace LowerOrderBoundedOn

variable {Ω Ω' : Set X} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
variable {beta gamma beta' gamma' : ℝ}

/-- The drift bound is nonnegative. -/
@[grind →]
lemma beta_nonneg (h : LowerOrderBoundedOn Ω b c beta gamma) : 0 ≤ beta :=
  h.1.beta_nonneg

/-- The mass bound is nonnegative. -/
@[grind →]
lemma gamma_nonneg (h : LowerOrderBoundedOn Ω b c beta gamma) : 0 ≤ gamma :=
  h.2.gamma_nonneg

/-- The bundled drift coefficient bound. -/
lemma drift_boundedOn (h : LowerOrderBoundedOn Ω b c beta gamma) :
    DriftBoundedOn Ω b beta :=
  h.1

/-- The bundled mass coefficient bound. -/
lemma mass_boundedOn (h : LowerOrderBoundedOn Ω b c beta gamma) :
    MassBoundedOn Ω c gamma :=
  h.2

/-- The pointwise drift coefficient bound. -/
@[grind =>]
lemma drift_bound (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X} (hx : x ∈ Ω) :
    ‖b x‖ ≤ beta :=
  h.1.bound hx

/-- The pointwise mass coefficient bound. -/
@[grind =>]
lemma mass_bound (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X} (hx : x ∈ Ω) :
    ‖c x‖ ≤ gamma :=
  h.2.bound hx

/-- Restricting the domain preserves bounded lower-order coefficients. -/
lemma mono_set (h : LowerOrderBoundedOn Ω b c beta gamma) (hΩ : Ω' ⊆ Ω) :
    LowerOrderBoundedOn Ω' b c beta gamma :=
  ⟨h.1.mono_set hΩ, h.2.mono_set hΩ⟩

/-- Increasing either bound preserves bounded lower-order coefficients. -/
lemma mono_constants (h : LowerOrderBoundedOn Ω b c beta gamma)
    (hbeta : beta ≤ beta') (hgamma : gamma ≤ gamma') :
    LowerOrderBoundedOn Ω b c beta' gamma' :=
  ⟨h.1.mono_constant hbeta, h.2.mono_constant hgamma⟩

/-- Constructor from separate side conditions and pointwise bounds. -/
lemma of_bounds (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → ‖c x‖ ≤ gamma) :
    LowerOrderBoundedOn Ω b c beta gamma :=
  ⟨DriftBoundedOn.of_bound hbeta hb, MassBoundedOn.of_bound hgamma hc⟩

/-- Convenience pointwise drift-form bound from bundled lower-order bounds. -/
@[grind =>]
lemma norm_driftForm_le (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X}
    (hx : x ∈ Ω) (u : ℝ) (ξ : EuclideanSpace ℝ n) :
    ‖driftForm (b x) u ξ‖ ≤ beta * ‖u‖ * ‖ξ‖ :=
  h.drift_boundedOn.norm_driftForm_le hx u ξ

/-- Convenience operator-norm drift-form bound from bundled lower-order bounds. -/
@[grind =>]
lemma opNorm_driftForm_le (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X}
    (hx : x ∈ Ω) :
    ‖driftForm (b x)‖ ≤ beta :=
  h.drift_boundedOn.opNorm_driftForm_le hx

/-- Convenience pointwise mass-form bound from bundled lower-order bounds. -/
@[grind =>]
lemma norm_massForm_le (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X}
    (hx : x ∈ Ω) (u v : ℝ) :
    ‖massForm (c x) u v‖ ≤ gamma * ‖u‖ * ‖v‖ :=
  h.mass_boundedOn.norm_massForm_le hx u v

/-- Convenience operator-norm mass-form bound from bundled lower-order bounds. -/
@[grind =>]
lemma opNorm_massForm_le (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X}
    (hx : x ∈ Ω) :
    ‖massForm (c x)‖ ≤ gamma :=
  h.mass_boundedOn.opNorm_massForm_le hx

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

variable {Ω Ω' : Set X} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
variable {beta gamma gamma' : ℝ}

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

/-- The mass form associated to a nonnegative mass coefficient is nonnegative on the diagonal. -/
@[grind =>]
lemma massForm_self_nonneg (h : NonnegMassOn Ω c gamma) {x : X} (hx : x ∈ Ω) (u : ℝ) :
    0 ≤ massForm (c x) u u := by
  rw [massForm_apply, mul_assoc]
  exact mul_nonneg (h.nonneg hx) (mul_self_nonneg u)

/-- Restricting the domain preserves nonnegative bounded mass coefficients. -/
lemma mono_set (h : NonnegMassOn Ω c gamma) (hΩ : Ω' ⊆ Ω) :
    NonnegMassOn Ω' c gamma :=
  ⟨h.gamma_nonneg, fun {_} hx => h.2 (hΩ hx)⟩

/-- Increasing the upper bound preserves nonnegative bounded mass coefficients. -/
lemma mono_constant (h : NonnegMassOn Ω c gamma) (hgamma : gamma ≤ gamma') :
    NonnegMassOn Ω c gamma' :=
  ⟨h.gamma_nonneg.trans hgamma,
    fun {_} hx => ⟨h.nonneg hx, (h.upper_bound hx).trans hgamma⟩⟩

/-- Nonnegative bounded mass coefficients are bounded mass coefficients. -/
lemma mass_boundedOn (h : NonnegMassOn Ω c gamma) :
    MassBoundedOn Ω c gamma :=
  MassBoundedOn.of_bound h.gamma_nonneg fun {_} hx => h.norm_bound hx

/-- A drift bound and nonnegative bounded mass coefficient produce lower-order bounds. -/
lemma lowerOrderBoundedOn (h : NonnegMassOn Ω c gamma)
    (hb : DriftBoundedOn (n := n) Ω b beta) :
    LowerOrderBoundedOn Ω b c beta gamma :=
  ⟨hb, h.mass_boundedOn⟩

/-- Nonnegative bounded mass coefficients produce lower-order bounds with zero drift. -/
lemma lowerOrderBoundedOn_zero_drift (h : NonnegMassOn Ω c gamma) :
    LowerOrderBoundedOn Ω (fun _ => (0 : EuclideanSpace ℝ n)) c 0 gamma :=
  h.lowerOrderBoundedOn
    (DriftBoundedOn.of_bound (n := n) le_rfl fun {_} _ => by simp)

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
