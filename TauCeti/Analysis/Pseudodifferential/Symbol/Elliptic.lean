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
# Elliptic symbols and their inverse symbols

A symbol `a ∈ S^m_{1,0}` with values in `V →L[ℂ] W` is *elliptic above the radius `R`*
(`TauCeti.Symbol.IsEllipticAbove`) if at every frequency `ξ` with `R ≤ ‖ξ‖` the value `a(x, ξ)`
is invertible, with

`‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`

for `x` in each compact set, where `⟨ξ⟩ = (1 + ‖ξ‖²)^(1/2)`. It is *uniformly elliptic above `R`*
(`TauCeti.Symbol.IsUniformlyEllipticAbove`) if one constant `C` works for all positions `x`. In
both notions the radius `R` is the same for all positions.

A symbol elliptic above `|t|` supplies the hypotheses of the cut-off inverse
`TauCeti.Symbol.cutoffInverse χ t (x, ξ) = χ(ξ / t) a(x, ξ)⁻¹`, a symbol of order `-m`
(`TauCeti.Symbol.IsEllipticAbove.exists_norm_inverse_le`). For `t ≠ 0` it equals `a(x, ξ)⁻¹` for
`‖ξ‖ ≥ 2 |t|`, so its pointwise products with `a` in either order are the identity up to a
smoothing symbol (`TauCeti.Symbol.isSmoothing_cutoffInverse_comp_sub` and
`TauCeti.Symbol.isSmoothing_comp_cutoffInverse_sub`), and it does not depend on the cutoff and the
radius modulo smoothing symbols (`TauCeti.Symbol.isSmoothing_cutoffInverse_sub_cutoffInverse`).
This is the first step in the construction of a parametrix of an elliptic pseudodifferential
operator.

Conversely, a symbol that a symbol of order `-m` inverts at all large frequencies is elliptic
(`TauCeti.Symbol.isEllipticAbove_of_comp_eq_id`), so a symbol is elliptic above some radius
exactly when it has such an inverse (`TauCeti.Symbol.exists_isEllipticAbove_iff`), and similarly
for uniform ellipticity (`TauCeti.Symbol.exists_isUniformlyEllipticAbove_iff`). For example the
Bessel weight `⟨ξ / 2π⟩^s` is uniformly elliptic of order `s`
(`TauCeti.Symbol.isUniformlyEllipticAbove_besselPotential`).

## Main declarations

* `TauCeti.Symbol.IsEllipticAbove`, `TauCeti.Symbol.IsUniformlyEllipticAbove`: ellipticity of a
  symbol above a radius, with locally uniform and uniform constants.
* `TauCeti.Symbol.isSmoothing_cutoffInverse_comp_sub`,
  `TauCeti.Symbol.isSmoothing_comp_cutoffInverse_sub`: the cut-off inverse is a pointwise
  two-sided inverse of `a` modulo smoothing symbols, and
  `TauCeti.Symbol.isSmoothing_cutoffInverse_sub_cutoffInverse`: it does not depend on the cutoff
  and the radius modulo smoothing symbols.
* `TauCeti.Symbol.exists_isEllipticAbove_iff`, `TauCeti.Symbol.exists_isUniformlyEllipticAbove_iff`:
  characterizations of ellipticity by inverse symbols.
* `TauCeti.Symbol.IsEllipticAbove.comp`, `TauCeti.Symbol.IsUniformlyEllipticAbove.comp`: pointwise
  products of elliptic symbols are elliptic.

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

/-! ### The inverse symbol -/

/-- The locally uniform inverse bound of a symbol elliptic above `R`, in the form required by the
cut-off inverse `TauCeti.Symbol.cutoffInverse` when `R = |t|`. -/
theorem IsEllipticAbove.exists_norm_inverse_le {a : Symbol n V W m} (ha : a.IsEllipticAbove R)
    (K : Set (CoordinateSpace n)) (hK : IsCompact K) :
    ∃ C, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) :=
  (ha K hK).imp fun _ hC x hx ξ hξ => (hC x hx ξ hξ).2

/-- The uniform inverse bound of a symbol uniformly elliptic above `R`, in the form required by
`TauCeti.Symbol.IsUniform.cutoffInverse` when `R = |t|`. -/
theorem IsUniformlyEllipticAbove.exists_norm_inverse_le {a : Symbol n V W m}
    (ha : a.IsUniformlyEllipticAbove R) :
    ∃ C, ∀ x ξ, R ≤ ‖ξ‖ → ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) :=
  ha.imp fun _ hC x ξ hξ => (hC x ξ hξ).2

section CutoffInverse

variable [CompleteSpace V] (a : Symbol n V W m) (χ : FrequencyCutoff (CoordinateSpace n)) {t : ℝ}
  (hinv : ∀ x ξ, |t| ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible)
  (hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, |t| ≤ ‖ξ‖ →
    ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2))

/-- The cut-off inverse vanishes at the frequencies of norm at most `|t|`. -/
theorem coefficient_cutoffInverse_of_norm_le (x : CoordinateSpace n) {ξ : CoordinateSpace n}
    (hξ : ‖ξ‖ ≤ |t|) : (a.cutoffInverse χ t hinv hbound).coefficient (x, ξ) = 0 := by
  have h : ‖t⁻¹ • ξ‖ ≤ 1 := by
    rcases eq_or_ne t 0 with rfl | _
    · simp
    · rw [norm_smul, norm_inv, Real.norm_eq_abs]
      exact inv_mul_le_one_of_le₀ hξ (abs_nonneg t)
  rw [coefficient_cutoffInverse, χ.apply_eq_zero_of_norm_le_one h, zero_smul]

/-- **The cut-off inverse is a pointwise left inverse modulo smoothing symbols**: for `t ≠ 0` the
pointwise product `χ(ξ / t) a⁻¹ ∘ a` is the identity up to a smoothing symbol. For symbols
depending on the position this is not the symbol of the composed operators; the cut-off inverse is
only the leading term of a parametrix. -/
theorem isSmoothing_cutoffInverse_comp_sub (ht : t ≠ 0) :
    ((a.cutoffInverse χ t hinv hbound).comp a -
      inclusion (neg_add_cancel m).ge (const (.id ℂ V))).IsSmoothing :=
  isSmoothing_of_coefficient_eq_zero (2 * |t|) fun x ξ hξ => by
    simp only [coefficient_sub, Pi.sub_apply, coefficient_comp, coefficient_inclusion,
      coefficient_const]
    rw [coefficient_cutoffInverse_of_two_mul_abs_le a χ t hinv hbound ht hξ x,
      (hinv x ξ (by linarith [abs_nonneg t])).inverse_comp_self, sub_self]

/-- **The cut-off inverse is a pointwise right inverse modulo smoothing symbols**: for `t ≠ 0` the
pointwise product `a ∘ χ(ξ / t) a⁻¹` is the identity up to a smoothing symbol. -/
theorem isSmoothing_comp_cutoffInverse_sub (ht : t ≠ 0) :
    (a.comp (a.cutoffInverse χ t hinv hbound) -
      inclusion (add_neg_cancel m).ge (const (.id ℂ W))).IsSmoothing :=
  isSmoothing_of_coefficient_eq_zero (2 * |t|) fun x ξ hξ => by
    simp only [coefficient_sub, Pi.sub_apply, coefficient_comp, coefficient_inclusion,
      coefficient_const]
    rw [coefficient_cutoffInverse_of_two_mul_abs_le a χ t hinv hbound ht hξ x,
      (hinv x ξ (by linarith [abs_nonneg t])).self_comp_inverse, sub_self]

/-- **Independence of the choices.** For nonzero radii, changing the frequency cutoff and the
radius changes the cut-off inverse by a smoothing symbol. -/
theorem isSmoothing_cutoffInverse_sub_cutoffInverse (ht : t ≠ 0)
    (χ' : FrequencyCutoff (CoordinateSpace n)) {t' : ℝ} (ht' : t' ≠ 0)
    (hinv' : ∀ x ξ, |t'| ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible)
    (hbound' : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, |t'| ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) :
    (a.cutoffInverse χ t hinv hbound - a.cutoffInverse χ' t' hinv' hbound').IsSmoothing :=
  isSmoothing_of_coefficient_eq_zero (2 * max |t| |t'|) fun x ξ hξ => by
    rw [coefficient_sub, Pi.sub_apply,
      coefficient_cutoffInverse_of_two_mul_abs_le a χ t hinv hbound ht
        ((mul_le_mul_of_nonneg_left (le_max_left _ _) zero_le_two).trans hξ) x,
      coefficient_cutoffInverse_of_two_mul_abs_le a χ' t' hinv' hbound' ht'
        ((mul_le_mul_of_nonneg_left (le_max_right _ _) zero_le_two).trans hξ) x, sub_self]

end CutoffInverse

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

/-- A symbol elliptic above `R` is elliptic above the nonzero radius `|R| + 1`, written as an
absolute value so that it supplies the hypotheses of `TauCeti.Symbol.cutoffInverse`. -/
private theorem IsEllipticAbove.abs_add_one {a : Symbol n V W m} (ha : a.IsEllipticAbove R) :
    a.IsEllipticAbove |(|R| + 1)| :=
  ha.mono (by rw [abs_of_pos (by positivity)]; linarith [le_abs_self R])

/-- The cut-off inverse at the radius `|R| + 1` of a symbol elliptic above `R` is a two-sided
inverse at all frequencies of norm at least `2 (|R| + 1)`. -/
private theorem IsEllipticAbove.cutoffInverse_comp_eq_id [CompleteSpace V]
    {a : Symbol n V W m} (ha : a.IsEllipticAbove R) (x ξ : CoordinateSpace n)
    (hξ : 2 * |(|R| + 1)| ≤ ‖ξ‖) :
    (a.cutoffInverse default (|R| + 1) (fun x _ hξ => ha.abs_add_one.isInvertible x hξ)
        ha.abs_add_one.exists_norm_inverse_le).coefficient (x, ξ) ∘L a.coefficient (x, ξ) =
        .id ℂ V ∧
      a.coefficient (x, ξ) ∘L (a.cutoffInverse default (|R| + 1)
        (fun x _ hξ => ha.abs_add_one.isInvertible x hξ)
        ha.abs_add_one.exists_norm_inverse_le).coefficient (x, ξ) = .id ℂ W := by
  have hinv := ha.abs_add_one.isInvertible x (ξ := ξ) (by linarith [abs_nonneg (|R| + 1)])
  rw [coefficient_cutoffInverse_of_two_mul_abs_le _ _ _ _ _ (by positivity) hξ]
  exact ⟨hinv.inverse_comp_self, hinv.self_comp_inverse⟩

/-- A symbol of order `m` is elliptic above some radius exactly when a symbol of order `-m`
inverts it at all large frequencies. -/
theorem exists_isEllipticAbove_iff [CompleteSpace V] {a : Symbol n V W m} :
    (∃ R, a.IsEllipticAbove R) ↔ ∃ b : Symbol n W V (-m), ∃ R, ∀ x ξ, R ≤ ‖ξ‖ →
      b.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V ∧
        a.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = .id ℂ W := by
  refine ⟨fun ⟨R, ha⟩ => ?_, fun ⟨_, R, h⟩ => ⟨R, isEllipticAbove_of_comp_eq_id h⟩⟩
  exact ⟨_, _, ha.cutoffInverse_comp_eq_id⟩

/-- A uniform symbol of order `m` is uniformly elliptic above some radius exactly when a uniform
symbol of order `-m` inverts it at all large frequencies. -/
theorem exists_isUniformlyEllipticAbove_iff [CompleteSpace V] {a : Symbol n V W m}
    (hau : a.IsUniform) :
    (∃ R, a.IsUniformlyEllipticAbove R) ↔ ∃ b : Symbol n W V (-m), b.IsUniform ∧ ∃ R, ∀ x ξ,
      R ≤ ‖ξ‖ → b.coefficient (x, ξ) ∘L a.coefficient (x, ξ) = .id ℂ V ∧
        a.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = .id ℂ W := by
  refine ⟨fun ⟨R, hu⟩ => ?_, fun ⟨_, hb, R, h⟩ => ⟨R, isUniformlyEllipticAbove_of_comp_eq_id hb h⟩⟩
  have ha := hu.isEllipticAbove
  have hu' : a.IsUniformlyEllipticAbove |(|R| + 1)| :=
    hu.mono (by rw [abs_of_pos (by positivity)]; linarith [le_abs_self R])
  exact ⟨_, hau.cutoffInverse default _ _ _ hu'.exists_norm_inverse_le, _,
    ha.cutoffInverse_comp_eq_id⟩

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
