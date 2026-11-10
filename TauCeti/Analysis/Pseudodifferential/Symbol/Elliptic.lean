/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.CutoffInverse
public import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Elliptic symbols

A symbol `a ∈ S^m_{1,0}` with values in `V →L[ℂ] W` is *elliptic above the radius `R`*
(`TauCeti.Symbol.IsEllipticAbove`) if at every frequency `ξ` with `R ≤ ‖ξ‖` the value `a(x, ξ)`
is invertible, with

`‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`

for `x` in each compact set, where `⟨ξ⟩ = (1 + ‖ξ‖²)^(1/2)`. It is *uniformly elliptic above `R`*
(`TauCeti.Symbol.IsUniformlyEllipticAbove`) if one constant `C` works for all positions `x`. In
both notions the radius `R` is the same for all positions.

An elliptic symbol satisfies the hypotheses of the cut-off inverse `TauCeti.Symbol.cutoffInverse`
at every radius `R' ≥ R` (`TauCeti.Symbol.IsEllipticAbove.isInvertible`,
`TauCeti.Symbol.IsEllipticAbove.exists_norm_inverse_le`), which is a symbol of order `-m` inverting
`a` at all large frequencies. Conversely, a symbol that a symbol of order `-m` inverts at all large
frequencies is elliptic (`TauCeti.Symbol.isEllipticAbove_of_comp_eq_id`), so a symbol is elliptic
above some radius exactly when it has such an inverse (`TauCeti.Symbol.exists_isEllipticAbove_iff`),
and similarly for uniform ellipticity (`TauCeti.Symbol.exists_isUniformlyEllipticAbove_iff`). For
example the Bessel weight `⟨ξ / 2π⟩^s` is uniformly elliptic of order `s`
(`TauCeti.Symbol.isUniformlyEllipticAbove_besselPotential`).

## Main declarations

* `TauCeti.Symbol.IsEllipticAbove`, `TauCeti.Symbol.IsUniformlyEllipticAbove`: ellipticity of a
  symbol above a radius, with locally uniform and uniform constants.
* `TauCeti.Symbol.IsEllipticAbove.comp`, `TauCeti.Symbol.IsUniformlyEllipticAbove.comp`: pointwise
  products of elliptic symbols are elliptic.
* `TauCeti.Symbol.exists_isEllipticAbove_iff`, `TauCeti.Symbol.exists_isUniformlyEllipticAbove_iff`:
  ellipticity is the existence of an inverse symbol at large frequencies.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.6).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Set

namespace TauCeti

variable {n : ℕ}

namespace Symbol

variable {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' R R' : ℝ}

/-! ### Elliptic symbols -/

/-- A symbol `a` of order `m` is *elliptic above the radius `R`* if at every frequency `ξ` with
`R ≤ ‖ξ‖` its value `a(x, ξ)` is an invertible continuous linear map, with
`‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` for all positions `x` in each compact set, where
`⟨ξ⟩ = (1 + ‖ξ‖²)^(1/2)`. -/
def IsEllipticAbove (a : Symbol n V W m) (R : ℝ) : Prop :=
  ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
    (a.coefficient (x, ξ)).IsInvertible ∧
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)

/-- A symbol `a` of order `m` is *uniformly elliptic above the radius `R`* if at every frequency
`ξ` with `R ≤ ‖ξ‖` its value `a(x, ξ)` is an invertible continuous linear map, with
`‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` for one constant `C` and all positions `x`. -/
def IsUniformlyEllipticAbove (a : Symbol n V W m) (R : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x ξ, R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible ∧
    ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)

theorem isEllipticAbove_iff {a : Symbol n V W m} :
    a.IsEllipticAbove R ↔ ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ ξ,
      R ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible ∧
        ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) :=
  Iff.rfl

theorem isUniformlyEllipticAbove_iff {a : Symbol n V W m} :
    a.IsUniformlyEllipticAbove R ↔ ∃ C : ℝ, ∀ x ξ, R ≤ ‖ξ‖ →
      (a.coefficient (x, ξ)).IsInvertible ∧
        ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) :=
  Iff.rfl

/-- The value of a symbol elliptic above `R` is invertible at every frequency of norm at least
`R`. -/
theorem IsEllipticAbove.isInvertible {a : Symbol n V W m} (ha : a.IsEllipticAbove R)
    (x : CoordinateSpace n) {ξ : CoordinateSpace n} (hξ : R ≤ ‖ξ‖) :
    (a.coefficient (x, ξ)).IsInvertible := by
  obtain ⟨C, hC⟩ := ha {x} isCompact_singleton
  exact (hC x rfl ξ hξ).1

/-- The inverse bound of a symbol elliptic above `R`, in the form of the hypothesis of
`TauCeti.Symbol.cutoffInverse`. -/
theorem IsEllipticAbove.exists_norm_inverse_le {a : Symbol n V W m} (ha : a.IsEllipticAbove R)
    (K : Set (CoordinateSpace n)) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) :=
  (ha K hK).imp fun _ hC x hx ξ hξ => (hC x hx ξ hξ).2

/-- Ellipticity above a radius implies ellipticity above every larger radius. -/
theorem IsEllipticAbove.mono {a : Symbol n V W m} (ha : a.IsEllipticAbove R) (h : R ≤ R') :
    a.IsEllipticAbove R' :=
  fun K hK => (ha K hK).imp fun _ hC x hx ξ hξ => hC x hx ξ (h.trans hξ)

/-- Uniform ellipticity above a radius implies uniform ellipticity above every larger radius. -/
theorem IsUniformlyEllipticAbove.mono {a : Symbol n V W m} (ha : a.IsUniformlyEllipticAbove R)
    (h : R ≤ R') : a.IsUniformlyEllipticAbove R' :=
  ha.imp fun _ hC x ξ hξ => hC x ξ (h.trans hξ)

/-- A uniformly elliptic symbol is elliptic. -/
theorem IsUniformlyEllipticAbove.isEllipticAbove {a : Symbol n V W m}
    (ha : a.IsUniformlyEllipticAbove R) : a.IsEllipticAbove R :=
  fun _ _ => ha.imp fun _ hC x _ ξ hξ => hC x ξ hξ

/-- An invertible constant symbol is uniformly elliptic above every radius. -/
theorem isUniformlyEllipticAbove_const {T : V →L[ℂ] W} (hT : T.IsInvertible) (R : ℝ) :
    (const T : Symbol n V W 0).IsUniformlyEllipticAbove R :=
  ⟨‖T.inverse‖, fun x ξ _ => ⟨by rw [coefficient_const]; exact hT, by simp⟩⟩

/-- The pointwise estimate behind the products of elliptic symbols: if `b(x, ξ)` and `a(x, ξ)` are
invertible with inverses bounded by `C ⟨ξ⟩^(-m')` and `D ⟨ξ⟩^(-m)`, then `b(x, ξ) ∘ a(x, ξ)` is
invertible with inverse bounded by `D C ⟨ξ⟩^(-(m' + m))`. -/
private theorem isInvertible_comp_and_norm_inverse_le {b : W →L[ℂ] U} {a : V →L[ℂ] W}
    {C D : ℝ} {ξ : CoordinateSpace n}
    (hb : b.IsInvertible ∧ ‖b.inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m' / 2))
    (ha : a.IsInvertible ∧ ‖a.inverse‖ ≤ D * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) :
    (b ∘L a).IsInvertible ∧
      ‖(b ∘L a).inverse‖ ≤ D * C * (1 + ‖ξ‖ ^ 2) ^ (-(m' + m) / 2) := by
  refine ⟨hb.1.comp ha.1, ?_⟩
  rw [hb.1.inverse_comp_of_left]
  calc ‖a.inverse ∘L b.inverse‖ ≤ ‖a.inverse‖ * ‖b.inverse‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (D * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) * (C * (1 + ‖ξ‖ ^ 2) ^ (-m' / 2)) :=
        mul_le_mul ha.2 hb.2 (norm_nonneg _) ((norm_nonneg _).trans ha.2)
    _ = D * C * (1 + ‖ξ‖ ^ 2) ^ (-(m' + m) / 2) := by
        rw [show -(m' + m) / 2 = -m / 2 + -m' / 2 by ring, Real.rpow_add (by positivity)]
        ring

/-- The pointwise composition of elliptic symbols is elliptic. -/
theorem IsEllipticAbove.comp {b : Symbol n W U m'} {a : Symbol n V W m}
    (hb : b.IsEllipticAbove R') (ha : a.IsEllipticAbove R) :
    (b.comp a).IsEllipticAbove (max R' R) := by
  intro K hK
  obtain ⟨C, hC⟩ := hb K hK
  obtain ⟨D, hD⟩ := ha K hK
  refine ⟨D * C, fun x hx ξ hξ => ?_⟩
  rw [coefficient_comp]
  exact isInvertible_comp_and_norm_inverse_le (hC x hx ξ ((le_max_left _ _).trans hξ))
    (hD x hx ξ ((le_max_right _ _).trans hξ))

/-- The pointwise composition of uniformly elliptic symbols is uniformly elliptic. -/
theorem IsUniformlyEllipticAbove.comp {b : Symbol n W U m'} {a : Symbol n V W m}
    (hb : b.IsUniformlyEllipticAbove R') (ha : a.IsUniformlyEllipticAbove R) :
    (b.comp a).IsUniformlyEllipticAbove (max R' R) := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨D, hD⟩ := ha
  refine ⟨D * C, fun x ξ hξ => ?_⟩
  rw [coefficient_comp]
  exact isInvertible_comp_and_norm_inverse_le (hC x ξ ((le_max_left _ _).trans hξ))
    (hD x ξ ((le_max_right _ _).trans hξ))

/-! ### Characterizations -/

/-- A symbol of order `m` that a symbol of order `-m` inverts at all frequencies of norm at least
`R` is elliptic above `R`. -/
theorem isEllipticAbove_of_comp_eq_id {a : Symbol n V W m} {b : Symbol n W V (-m)}
    (h : ∀ x ξ, R ≤ ‖ξ‖ → b.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V ∧
      a.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = .id ℂ W) :
    a.IsEllipticAbove R := by
  refine fun K hK => (b.exists_norm_coefficient_le K hK).imp fun C hC x hx ξ hξ => ?_
  obtain ⟨h₁, h₂⟩ := h x ξ hξ
  refine ⟨.of_inverse h₂ h₁, ?_⟩
  rw [ContinuousLinearMap.inverse_eq h₂ h₁]
  exact hC x hx ξ

/-- A symbol of order `m` that a uniform symbol of order `-m` inverts at all frequencies of norm
at least `R` is uniformly elliptic above `R`. -/
theorem isUniformlyEllipticAbove_of_comp_eq_id {a : Symbol n V W m} {b : Symbol n W V (-m)}
    (hb : b.IsUniform)
    (h : ∀ x ξ, R ≤ ‖ξ‖ → b.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V ∧
      a.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = .id ℂ W) :
    a.IsUniformlyEllipticAbove R := by
  obtain ⟨C, -, hC⟩ := isUniform_iff.1 hb [] []
  refine ⟨C, fun x ξ hξ => ?_⟩
  obtain ⟨h₁, h₂⟩ := h x ξ hξ
  refine ⟨.of_inverse h₂ h₁, ?_⟩
  rw [ContinuousLinearMap.inverse_eq h₂ h₁]
  simpa using hC x ξ

/-- A symbol of order `m` is elliptic above some radius exactly when a symbol of order `-m`
inverts it at all large frequencies. -/
theorem exists_isEllipticAbove_iff [CompleteSpace V] {a : Symbol n V W m} :
    (∃ R, a.IsEllipticAbove R) ↔ ∃ b : Symbol n W V (-m), ∃ R, ∀ x ξ, R ≤ ‖ξ‖ →
      b.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V ∧
        a.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = .id ℂ W := by
  refine ⟨fun ⟨R, ha⟩ => ?_, fun ⟨_, R, h⟩ => ⟨R, isEllipticAbove_of_comp_eq_id h⟩⟩
  have hr : max R 1 ≠ 0 := (lt_max_of_lt_right one_pos).ne'
  have ha' := ha.mono ((le_max_left R 1).trans (le_abs_self _))
  refine ⟨a.cutoffInverse default (max R 1) (fun x _ hξ => ha'.isInvertible x hξ)
    ha'.exists_norm_inverse_le, 2 * |max R 1|, fun x ξ hξ => ?_⟩
  have hi := ha'.isInvertible x (ξ := ξ) (by linarith [abs_nonneg (max R 1)])
  rw [coefficient_cutoffInverse_of_two_mul_abs_le _ _ _ _ _ hr hξ]
  exact ⟨hi.inverse_comp_self, hi.self_comp_inverse⟩

/-- A uniform symbol of order `m` is uniformly elliptic above some radius exactly when a uniform
symbol of order `-m` inverts it at all large frequencies. -/
theorem exists_isUniformlyEllipticAbove_iff [CompleteSpace V] {a : Symbol n V W m}
    (hau : a.IsUniform) :
    (∃ R, a.IsUniformlyEllipticAbove R) ↔ ∃ b : Symbol n W V (-m), b.IsUniform ∧ ∃ R, ∀ x ξ,
      R ≤ ‖ξ‖ → b.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V ∧
        a.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = .id ℂ W := by
  refine ⟨fun ⟨R, hu⟩ => ?_, fun ⟨_, hb, R, h⟩ => ⟨R, isUniformlyEllipticAbove_of_comp_eq_id hb h⟩⟩
  have hr : max R 1 ≠ 0 := (lt_max_of_lt_right one_pos).ne'
  have hu' := hu.mono ((le_max_left R 1).trans (le_abs_self _))
  have ha' := hu'.isEllipticAbove
  refine ⟨a.cutoffInverse default (max R 1) (fun x _ hξ => ha'.isInvertible x hξ)
    ha'.exists_norm_inverse_le, hau.cutoffInverse _ _ _ _
      (hu'.imp fun _ hC x ξ hξ => (hC x ξ hξ).2), 2 * |max R 1|, fun x ξ hξ => ?_⟩
  have hi := ha'.isInvertible x (ξ := ξ) (by linarith [abs_nonneg (max R 1)])
  rw [coefficient_cutoffInverse_of_two_mul_abs_le _ _ _ _ _ hr hξ]
  exact ⟨hi.inverse_comp_self, hi.self_comp_inverse⟩

/-- The Bessel weight `⟨ξ / 2π⟩^s` is uniformly elliptic of order `s` above every radius: its
inverse is the Bessel weight of order `-s`. -/
theorem isUniformlyEllipticAbove_besselPotential (s R : ℝ) :
    (besselPotential s : Symbol n V V s).IsUniformlyEllipticAbove R := by
  refine isUniformlyEllipticAbove_of_comp_eq_id (isUniform_besselPotential (-s)) fun x ξ _ => ?_
  have hw : (0 : ℝ) < 1 + ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2 := by positivity
  have h₁ : (1 + ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2) ^ (-s / 2) * (1 + ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2) ^ (s / 2) =
      1 := by
    rw [← Real.rpow_add hw, neg_div, neg_add_cancel, Real.rpow_zero]
  have h₂ : (1 + ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2) ^ (s / 2) * (1 + ‖(2 * Real.pi)⁻¹ • ξ‖ ^ 2) ^ (-s / 2) =
      1 := by
    rw [mul_comm, h₁]
  simp only [coefficient_besselPotential, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_id, smul_smul, ← Complex.ofReal_mul,
    h₁, h₂, Complex.ofReal_one, one_smul, and_self]

end Symbol

end TauCeti
