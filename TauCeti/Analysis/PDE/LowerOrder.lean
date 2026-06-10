/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Analysis.PDE.UniformEllipticity
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Lower-order pointwise forms for divergence-form PDEs

The divergence-form roadmap keeps the principal elliptic coefficient, first-order drift,
and zeroth-order mass coefficient as separate named hypotheses.  The principal matrix
coefficient lives in `TauCeti.Analysis.PDE.UniformEllipticity`; this file records the
pointwise bundled forms and explicit bounds for the lower-order terms

* `u ↦ b(x) · ∇u`, represented here by `driftForm b`;
* `u ↦ c(x) u`, represented in the weak form by `massForm c`.

These are only pointwise continuous bilinear maps.  They are the finite-dimensional
estimates later integrated over `Ω` once the weak-derivative Sobolev spaces are available.

## Main declarations

* `TauCeti.PDE.driftForm`: the continuous bilinear map `(u, ξ) ↦ u * ⟪b, ξ⟫`.
* `TauCeti.PDE.massForm`: the continuous bilinear map `(u, v) ↦ c * u * v`.
* `TauCeti.PDE.LowerOrderBoundedOn`: explicit bounds for drift and mass coefficients on a
  domain.
* `TauCeti.PDE.NonnegativeMassOn`: nonnegative bounded mass coefficients.
-/

namespace TauCeti

namespace PDE

open scoped InnerProductSpace

variable {X n : Type*} [Fintype n]

/-- The pointwise first-order drift form `(u, ξ) ↦ u * ⟪b, ξ⟫`.

In a weak formulation this is the integrand modelling a lower-order term such as
`bᵢ ∂ᵢu v`, after one scalar argument represents the test function and the vector argument
represents the gradient. -/
noncomputable def driftForm (b : EuclideanSpace ℝ n) :
    ℝ →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun u ξ => u * ⟪b, ξ⟫_ℝ)
      (fun u v ξ => by ring)
      (fun a u ξ => by ring)
      (fun u ξ η => by simp [inner_add_right, mul_add])
      (fun a u ξ => by rw [inner_smul_right]; ring))
    ‖b‖
    (fun u ξ => by
      rw [LinearMap.mk₂_apply, norm_mul]
      calc
        ‖u‖ * ‖⟪b, ξ⟫_ℝ‖ ≤ ‖u‖ * (‖b‖ * ‖ξ‖) := by
          gcongr
          exact norm_inner_le_norm b ξ
        _ = ‖b‖ * ‖u‖ * ‖ξ‖ := by ring)

/-- The drift form is the expected scalar times dot-product expression. -/
@[simp]
lemma driftForm_apply (b : EuclideanSpace ℝ n) (u : ℝ) (ξ : EuclideanSpace ℝ n) :
    driftForm b u ξ = u * ⟪b, ξ⟫_ℝ := by
  simp [driftForm]

/-- The pointwise drift form is linear under scalar multiplication of the coefficient vector. -/
@[simp]
lemma driftForm_smul_apply (a : ℝ) (b : EuclideanSpace ℝ n) (u : ℝ)
    (ξ : EuclideanSpace ℝ n) :
    driftForm (a • b) u ξ = a * driftForm b u ξ := by
  rw [driftForm_apply, driftForm_apply, real_inner_smul_left]
  ring

/-- A norm bound for the pointwise drift form in terms of the coefficient norm. -/
lemma norm_driftForm_apply_le (b : EuclideanSpace ℝ n) (u : ℝ) (ξ : EuclideanSpace ℝ n) :
    ‖driftForm b u ξ‖ ≤ ‖b‖ * ‖u‖ * ‖ξ‖ := by
  rw [driftForm_apply, norm_mul]
  calc
    ‖u‖ * ‖⟪b, ξ⟫_ℝ‖ ≤ ‖u‖ * (‖b‖ * ‖ξ‖) := by
      gcongr
      exact norm_inner_le_norm b ξ
    _ = ‖b‖ * ‖u‖ * ‖ξ‖ := by ring

/-- A bound on the coefficient norm gives the corresponding pointwise drift estimate. -/
lemma norm_driftForm_apply_le_of_norm_le {b : EuclideanSpace ℝ n} {beta : ℝ}
    (hb : ‖b‖ ≤ beta) (u : ℝ) (ξ : EuclideanSpace ℝ n) :
    ‖driftForm b u ξ‖ ≤ beta * ‖u‖ * ‖ξ‖ := by
  exact (norm_driftForm_apply_le b u ξ).trans <| by
    gcongr

/-- The operator norm of the drift form is bounded by the coefficient norm. -/
lemma opNorm_driftForm_le (b : EuclideanSpace ℝ n) :
    ‖driftForm b‖ ≤ ‖b‖ :=
  (driftForm b).opNorm_le_bound₂ (norm_nonneg b) (norm_driftForm_apply_le b)

/-- A bound on the coefficient norm bounds the operator norm of the drift form. -/
lemma opNorm_driftForm_le_of_norm_le {b : EuclideanSpace ℝ n} {beta : ℝ}
    (hb : ‖b‖ ≤ beta) :
    ‖driftForm b‖ ≤ beta :=
  (opNorm_driftForm_le b).trans hb

/-- The pointwise zeroth-order mass form `(u, v) ↦ c * u * v`. -/
noncomputable def massForm (c : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun u v => c * u * v)
      (fun u v w => by ring)
      (fun a u v => by ring)
      (fun u v w => by ring)
      (fun a u v => by ring))
    ‖c‖
    (fun u v => by
      rw [LinearMap.mk₂_apply, norm_mul, norm_mul, mul_assoc])

/-- The mass form is the expected product expression. -/
@[simp]
lemma massForm_apply (c u v : ℝ) :
    massForm c u v = c * u * v := by
  simp [massForm]

/-- The zero mass coefficient gives the zero pointwise mass form. -/
@[simp]
lemma massForm_zero_apply (u v : ℝ) :
    massForm 0 u v = 0 := by
  simp [massForm_apply]

/-- The mass form is additive in the coefficient. -/
@[simp]
lemma massForm_add_apply (c d u v : ℝ) :
    massForm (c + d) u v = massForm c u v + massForm d u v := by
  simp [massForm_apply]
  ring

/-- The mass form is linear under scalar multiplication of the coefficient. -/
@[simp]
lemma massForm_smul_apply (a c u v : ℝ) :
    massForm (a * c) u v = a * massForm c u v := by
  simp [massForm_apply]
  ring

/-- A norm bound for the pointwise mass form in terms of the coefficient absolute value. -/
lemma norm_massForm_apply_le (c u v : ℝ) :
    ‖massForm c u v‖ ≤ ‖c‖ * ‖u‖ * ‖v‖ := by
  rw [massForm_apply, norm_mul, norm_mul, mul_assoc]

/-- A bound on the coefficient absolute value gives the corresponding pointwise mass estimate. -/
lemma norm_massForm_apply_le_of_norm_le {c gamma : ℝ} (hc : ‖c‖ ≤ gamma) (u v : ℝ) :
    ‖massForm c u v‖ ≤ gamma * ‖u‖ * ‖v‖ := by
  exact (norm_massForm_apply_le c u v).trans <| by
    gcongr

/-- The operator norm of the mass form is bounded by the coefficient absolute value. -/
lemma opNorm_massForm_le (c : ℝ) :
    ‖massForm c‖ ≤ ‖c‖ :=
  (massForm c).opNorm_le_bound₂ (norm_nonneg c) (norm_massForm_apply_le c)

/-- A bound on the coefficient absolute value bounds the operator norm of the mass form. -/
lemma opNorm_massForm_le_of_norm_le {c gamma : ℝ} (hc : ‖c‖ ≤ gamma) :
    ‖massForm c‖ ≤ gamma :=
  (opNorm_massForm_le c).trans hc

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
    ‖driftForm (b x) u ξ‖ ≤ beta * ‖u‖ * ‖ξ‖ :=
  norm_driftForm_apply_le_of_norm_le (h.drift_bound hx) u ξ

/-- Operator-norm boundedness of the drift form supplied by bounded lower-order coefficients. -/
@[grind =>]
lemma opNorm_driftForm_le (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X}
    (hx : x ∈ Ω) :
    ‖driftForm (b x)‖ ≤ beta :=
  PDE.opNorm_driftForm_le_of_norm_le (h.drift_bound hx)

/-- Pointwise boundedness of the mass form supplied by bounded lower-order coefficients. -/
@[grind =>]
lemma norm_massForm_le (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X}
    (hx : x ∈ Ω) (u v : ℝ) :
    ‖massForm (c x) u v‖ ≤ gamma * ‖u‖ * ‖v‖ :=
  norm_massForm_apply_le_of_norm_le (h.mass_bound hx) u v

/-- Operator-norm boundedness of the mass form supplied by bounded lower-order coefficients. -/
@[grind =>]
lemma opNorm_massForm_le (h : LowerOrderBoundedOn Ω b c beta gamma) {x : X}
    (hx : x ∈ Ω) :
    ‖massForm (c x)‖ ≤ gamma :=
  PDE.opNorm_massForm_le_of_norm_le (h.mass_bound hx)

end LowerOrderBoundedOn

/-- Nonnegative bounded zeroth-order coefficients on a domain. -/
def NonnegativeMassOn (Ω : Set X) (c : X → ℝ) (gamma : ℝ) : Prop :=
  0 ≤ gamma ∧ ∀ ⦃x⦄, x ∈ Ω → 0 ≤ c x ∧ c x ≤ gamma

/-- Characteristic restatement of nonnegative bounded mass coefficients. -/
lemma nonnegativeMassOn_iff {Ω : Set X} {c : X → ℝ} {gamma : ℝ} :
    NonnegativeMassOn Ω c gamma ↔
      0 ≤ gamma ∧ ∀ ⦃x⦄, x ∈ Ω → 0 ≤ c x ∧ c x ≤ gamma :=
  Iff.rfl

namespace NonnegativeMassOn

variable {Ω Ω' : Set X} {c : X → ℝ} {gamma gamma' : ℝ}

/-- The mass bound is nonnegative. -/
@[grind →]
lemma gamma_nonneg (h : NonnegativeMassOn Ω c gamma) : 0 ≤ gamma :=
  h.1

/-- The mass coefficient is pointwise nonnegative. -/
@[grind =>]
lemma nonneg (h : NonnegativeMassOn Ω c gamma) {x : X} (hx : x ∈ Ω) : 0 ≤ c x :=
  (h.2 hx).1

/-- The mass coefficient is pointwise bounded above. -/
@[grind =>]
lemma upper_bound (h : NonnegativeMassOn Ω c gamma) {x : X} (hx : x ∈ Ω) :
    c x ≤ gamma :=
  (h.2 hx).2

/-- A nonnegative bounded mass coefficient is absolutely bounded. -/
@[grind =>]
lemma norm_bound (h : NonnegativeMassOn Ω c gamma) {x : X} (hx : x ∈ Ω) :
    ‖c x‖ ≤ gamma := by
  simpa [Real.norm_eq_abs, abs_of_nonneg (h.nonneg hx)] using h.upper_bound hx

/-- Restricting the domain preserves nonnegative bounded mass coefficients. -/
lemma mono_set (h : NonnegativeMassOn Ω c gamma) (hΩ : Ω' ⊆ Ω) :
    NonnegativeMassOn Ω' c gamma :=
  ⟨h.gamma_nonneg, fun {_} hx => h.2 (hΩ hx)⟩

/-- Increasing the upper bound preserves nonnegative bounded mass coefficients. -/
lemma mono_constant (h : NonnegativeMassOn Ω c gamma) (hgamma : gamma ≤ gamma') :
    NonnegativeMassOn Ω c gamma' :=
  ⟨h.gamma_nonneg.trans hgamma,
    fun {_} hx => ⟨h.nonneg hx, (h.upper_bound hx).trans hgamma⟩⟩

/-- Nonnegative bounded mass coefficients produce lower-order bounds with zero drift. -/
lemma lowerOrderBoundedOn_zero_drift (h : NonnegativeMassOn Ω c gamma) :
    LowerOrderBoundedOn Ω (fun _ => (0 : EuclideanSpace ℝ n)) c 0 gamma :=
  LowerOrderBoundedOn.of_bounds le_rfl h.gamma_nonneg
    (fun {_} _ => by simp) (fun {_} hx => h.norm_bound hx)

end NonnegativeMassOn

/-- Zero lower-order coefficients are bounded by zero. -/
lemma lowerOrderBoundedOn_zero (Ω : Set X) :
    LowerOrderBoundedOn Ω (fun _ => (0 : EuclideanSpace ℝ n)) (fun _ => 0) 0 0 :=
  LowerOrderBoundedOn.of_bounds le_rfl le_rfl (fun {_} _ => by simp) (fun {_} _ => by simp)

/-- A constant nonnegative mass coefficient is nonnegative and bounded by itself. -/
lemma nonnegativeMassOn_const_self (Ω : Set X) {c : ℝ} (hc : 0 ≤ c) :
    NonnegativeMassOn Ω (fun _ => c) c :=
  ⟨hc, fun {_} _ => ⟨hc, le_rfl⟩⟩

end PDE

end TauCeti
