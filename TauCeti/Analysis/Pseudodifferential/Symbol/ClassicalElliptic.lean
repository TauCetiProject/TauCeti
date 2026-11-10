/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Elliptic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Elliptic classical symbols

A classical symbol `a ∼ ∑ⱼ χ(ξ) a_{m-j}(x, ξ)` of order `m` is *elliptic* when its principal
symbol `a_m` is invertible at every position `x` and every nonzero frequency `ξ`
(`TauCeti.ClassicalSymbol.IsElliptic`). This is the ellipticity of the classical
pseudodifferential operators, and the inverse `a_m⁻¹`, a homogeneous symbol of degree `-m`, is the
principal symbol of their parametrices.

For symbols that are not classical, ellipticity is instead phrased through the full symbol: `a` is
invertible at large frequencies, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` there, locally uniformly in `x`
(here `⟨ξ⟩ = (1 + ‖ξ‖²)^(1/2)`). This is the hypothesis under which the cut-off inverse
`TauCeti.Symbol.cutoffInverse` is a symbol of order `-m`. The main result of this file is that the
two notions agree for classical symbols
(`TauCeti.ClassicalSymbol.isElliptic_iff_exists_isInvertible_and_norm_inverse_le`): the full
symbol differs from its principal symbol by a symbol of order `m - 1`, which is small against
`a_m⁻¹ = O(⟨ξ⟩^(-m))` at large frequencies, and conversely homogeneity transports invertibility at
large frequencies to every nonzero frequency.

Here the radius beyond which `a` is invertible depends on the compact set of positions, since the
remainder estimates of a classical symbol are only locally uniform. This is weaker than
`TauCeti.Symbol.IsEllipticAbove`, which fixes one radius for all positions.

## Main declarations

* `TauCeti.ClassicalSymbol.IsElliptic`: ellipticity of the principal symbol.
* `TauCeti.ClassicalSymbol.existsUnique_inversePrincipalSymbol`: the principal symbol of an
  elliptic classical symbol of order `m` has a unique two-sided inverse, a homogeneous symbol of
  degree `-m`.
* `TauCeti.ClassicalSymbol.IsElliptic.exists_isInvertible_and_norm_inverse_le`: on each compact
  set of positions, an elliptic classical symbol is invertible at large frequencies with
  `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`.
* `TauCeti.ClassicalSymbol.isElliptic_of_forall_exists_isInvertible_and_norm_inverse_le`: the
  converse, from the same estimate at each single position.
* `TauCeti.ClassicalSymbol.IsElliptic.comp`, `TauCeti.ClassicalSymbol.isElliptic_smul_iff` and
  `TauCeti.ClassicalSymbol.isElliptic_add_iff`: ellipticity is preserved by pointwise composition
  and nonzero scalars, and does not see terms of order `m - 1`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.6).
-/

public section

namespace TauCeti

namespace ClassicalSymbol

open HomogeneousSymbol

variable {n : ℕ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' : ℝ}

/-! ### Elliptic classical symbols -/

/-- A classical symbol is elliptic if its principal symbol is: its value at every position and
every nonzero frequency is an invertible continuous linear map. -/
def IsElliptic (a : ClassicalSymbol n V W m) : Prop :=
  a.principal.IsElliptic

@[simp]
theorem isElliptic_principal_iff {a : ClassicalSymbol n V W m} :
    a.principal.IsElliptic ↔ a.IsElliptic :=
  Iff.rfl

theorem isElliptic_iff {a : ClassicalSymbol n V W m} :
    a.IsElliptic ↔ ∀ x ξ, ξ ≠ 0 → (a.principal.coefficient (x, ξ)).IsInvertible :=
  HomogeneousSymbol.isElliptic_iff

/-- Between Banach spaces, a classical symbol is elliptic exactly when its principal symbol is
bijective at every nonzero frequency. -/
theorem isElliptic_iff_bijective [CompleteSpace V] [CompleteSpace W]
    {a : ClassicalSymbol n V W m} :
    a.IsElliptic ↔ ∀ x ξ, ξ ≠ 0 → Function.Bijective (a.principal.coefficient (x, ξ)) :=
  HomogeneousSymbol.isElliptic_iff_bijective

/-- The classical symbol `χ(ξ) a(x, ξ)` of a single homogeneous term is elliptic exactly when the
term is. -/
@[simp]
theorem isElliptic_ofHomogeneous_iff (χ : FrequencyCutoff (CoordinateSpace n))
    {a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} :
    (ofHomogeneous χ a).IsElliptic ↔ a.IsElliptic := by
  rw [← isElliptic_principal_iff, principal_ofHomogeneous]

/-- Multiplying by a nonzero complex number does not change ellipticity. -/
@[simp]
theorem isElliptic_smul_iff {c : ℂ} (hc : c ≠ 0) {a : ClassicalSymbol n V W m} :
    (c • a).IsElliptic ↔ a.IsElliptic := by
  rw [← isElliptic_principal_iff, principal_smul, HomogeneousSymbol.isElliptic_smul_iff hc,
    isElliptic_principal_iff]

/-- The pointwise composition of elliptic classical symbols is elliptic. -/
theorem IsElliptic.comp {b : ClassicalSymbol n W U m'} {a : ClassicalSymbol n V W m}
    (hb : b.IsElliptic) (ha : a.IsElliptic) : (b.comp a).IsElliptic := by
  rw [← isElliptic_principal_iff, principal_comp]
  exact HomogeneousSymbol.IsElliptic.comp hb ha

/-- Adding a classical symbol with vanishing principal symbol, that is, of order `m - 1`
(`TauCeti.ClassicalSymbol.principal_eq_zero_iff`), does not change ellipticity. -/
theorem isElliptic_add_iff {a b : ClassicalSymbol n V W m} (hb : b.principal = 0) :
    (a + b).IsElliptic ↔ a.IsElliptic := by
  rw [← isElliptic_principal_iff, principal_add, hb, add_zero, isElliptic_principal_iff]

/-- **The inverse principal symbol.** The principal symbol `a_m` of an elliptic classical symbol of
order `m` has a unique two-sided inverse at every nonzero frequency that is a homogeneous symbol of
degree `-m`, namely `TauCeti.HomogeneousSymbol.inverse`. -/
theorem existsUnique_inversePrincipalSymbol [CompleteSpace V] {a : ClassicalSymbol n V W m}
    (ha : a.IsElliptic) :
    ∃! b : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) W V (-m),
      ∀ x ξ, ξ ≠ 0 →
        b.coefficient (x, ξ) ∘L a.principal.coefficient (x, ξ) = ContinuousLinearMap.id ℂ V ∧
          a.principal.coefficient (x, ξ) ∘L b.coefficient (x, ξ) = ContinuousLinearMap.id ℂ W :=
  have hp := isElliptic_principal_iff.2 ha
  ⟨a.principal.inverse hp, fun _ _ hξ => ⟨coefficient_inverse_comp_coefficient _ hp hξ,
    coefficient_comp_coefficient_inverse _ hp hξ⟩, fun b hb =>
      eq_inverse_of_comp_eq_id_left _ hp <| ext_of_ne_zero fun x ξ hξ => by
        simpa [hξ] using (hb x ξ hξ).1⟩

/-! ### Ellipticity through the full symbol -/

/-- Away from the unit ball, `c ⟨ξ⟩^(-m) ⟨ξ⟩^(m - 1) = c ⟨ξ⟩⁻¹` is at most `1 / 2` once
`2 c ≤ ‖ξ‖`. -/
private theorem mul_rpow_mul_rpow_le_half {c : ℝ} (hc : 0 ≤ c) {ξ : CoordinateSpace n}
    (h1 : 1 ≤ ‖ξ‖) (hc' : 2 * c ≤ ‖ξ‖) :
    c * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2) ≤ 1 / 2 := by
  have h0 : 0 < ‖ξ‖ := one_pos.trans_le h1
  have hexp : -m / 2 + (m - 1) / 2 = -((1 : ℕ) : ℝ) / 2 := by
    push_cast
    ring
  rw [mul_assoc, ← Real.rpow_add (by positivity), hexp]
  calc c * (1 + ‖ξ‖ ^ 2) ^ (-((1 : ℕ) : ℝ) / 2) ≤ c * (1 / ‖ξ‖ ^ 1) := by
        gcongr
        exact Real.one_add_sq_rpow_neg_le h0 1
    _ ≤ 1 / 2 := by
        rw [pow_one, mul_one_div, div_le_iff₀ h0]
        linarith

/-- At frequencies of norm at least `2`, a classical symbol is its principal symbol plus the
remainder of order `m - 1`. -/
private theorem coefficient_toSymbol_eq_principal_add (a : ClassicalSymbol n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) {x ξ : CoordinateSpace n} (hξ : 2 ≤ ‖ξ‖) :
    a.toSymbol.coefficient (x, ξ) =
      a.principal.coefficient (x, ξ) + (a.remainder χ 1).coefficient (x, ξ) := by
  simp [χ.apply_eq_one_of_two_le_norm hξ]

/-- The remainder of order `m - 1` after the principal term satisfies its estimate. -/
private theorem exists_norm_remainder_le (a : ClassicalSymbol n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖(a.remainder χ 1).coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2) := by
  obtain ⟨C, hC, h⟩ := (a.remainder χ 1).exists_bound K hK [] []
  exact ⟨C, hC, fun x hx ξ => by simpa using h x hx ξ⟩

/-- **Elliptic classical symbols are invertible at large frequencies.** On each compact set `K` of
positions, an elliptic classical symbol `a` of order `m` is invertible at all frequencies of norm
at least some `R`, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` there. -/
theorem IsElliptic.exists_isInvertible_and_norm_inverse_le [CompleteSpace V]
    {a : ClassicalSymbol n V W m} (ha : a.IsElliptic) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) :
    ∃ R C : ℝ, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ → (a.toSymbol.coefficient (x, ξ)).IsInvertible ∧
      ‖(a.toSymbol.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) := by
  -- `a = a_m + r` at large frequencies, with `‖a_m⁻¹‖ ≤ C₁ ⟨ξ⟩^(-m)` and `‖r‖ ≤ C₂ ⟨ξ⟩^(m - 1)`,
  -- so `‖a_m⁻¹‖ ‖r‖ ≤ C₁ C₂ ⟨ξ⟩⁻¹ ≤ 1 / 2` and `‖a⁻¹‖ ≤ 2 ‖a_m⁻¹‖`.
  have hp := isElliptic_principal_iff.2 ha
  obtain ⟨C₀, hC₀, hq⟩ := (a.principal.inverse hp).exists_norm_coefficient_le hK
  obtain ⟨C₂, hC₂, hr⟩ := a.exists_norm_remainder_le default hK
  set C₁ := C₀ * 2 ^ (|m| / 2)
  refine ⟨max 2 (2 * (C₁ * C₂)), 2 * C₁, fun x hx ξ hξ => ?_⟩
  have h2 : 2 ≤ ‖ξ‖ := (le_max_left _ _).trans hξ
  have hL : (a.principal.coefficient (x, ξ)).IsInvertible :=
    isElliptic_iff.1 ha x ξ (norm_pos_iff.1 (by linarith))
  have hq' : ‖(a.principal.coefficient (x, ξ)).inverse‖ ≤ C₁ * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) := by
    have hw := norm_rpow_le_one_add_norm_sq_rpow (by linarith : 1 ≤ ‖ξ‖) (-m)
    rw [abs_neg] at hw
    calc ‖(a.principal.coefficient (x, ξ)).inverse‖ ≤ C₀ * ‖ξ‖ ^ (-m) := by
          simpa only [coefficient_inverse] using hq x hx ξ
      _ ≤ C₀ * (2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) := by gcongr
      _ = C₁ * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) := by ring
  have hsmall : ‖(a.principal.coefficient (x, ξ)).inverse‖ *
      ‖(a.remainder default 1).coefficient (x, ξ)‖ ≤ 1 / 2 :=
    calc _ ≤ C₁ * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) * (C₂ * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2)) := by
          gcongr
          exact hr x hx ξ
      _ = C₁ * C₂ * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2) := by ring
      _ ≤ 1 / 2 :=
          mul_rpow_mul_rpow_le_half (by positivity) (by linarith) ((le_max_right _ _).trans hξ)
  rw [a.coefficient_toSymbol_eq_principal_add default h2]
  refine ⟨hL.add (hsmall.trans_lt (by norm_num)), ?_⟩
  calc _ ≤ ‖(a.principal.coefficient (x, ξ)).inverse‖ /
        (1 - ‖(a.principal.coefficient (x, ξ)).inverse‖ *
          ‖(a.remainder default 1).coefficient (x, ξ)‖) :=
        hL.norm_inverse_add_le (hsmall.trans_lt (by norm_num))
    _ ≤ 2 * ‖(a.principal.coefficient (x, ξ)).inverse‖ := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [norm_nonneg (a.principal.coefficient (x, ξ)).inverse]
    _ ≤ 2 * C₁ * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) := by
        rw [mul_assoc]
        gcongr

/-- **Invertibility at large frequencies forces ellipticity.** If at each position `x` a classical
symbol `a` of order `m` is invertible at all large frequencies, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`
there, then `a` is elliptic. -/
theorem isElliptic_of_forall_exists_isInvertible_and_norm_inverse_le [CompleteSpace V]
    {a : ClassicalSymbol n V W m}
    (h : ∀ x, ∃ R C : ℝ, ∀ ξ, R ≤ ‖ξ‖ → (a.toSymbol.coefficient (x, ξ)).IsInvertible ∧
      ‖(a.toSymbol.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) :
    a.IsElliptic := by
  refine isElliptic_iff.2 fun x ξ hξ => ?_
  obtain ⟨R, C, hRC⟩ := h x
  obtain ⟨C₂, hC₂, hr⟩ := a.exists_norm_remainder_le default isCompact_singleton (K := {x})
  -- Rescale `ξ` to a frequency `η = t ξ` of norm `S`, so large that `a(x, η)` is invertible and
  -- `‖a(x, η)⁻¹‖ ‖r(x, η)‖ < 1`; then `a_m(x, η) = a(x, η) - r(x, η)` is invertible.
  set S := max (max R 2) (2 * (max C 0 * C₂))
  have hS2 : 2 ≤ S := (le_max_right _ _).trans (le_max_left _ _)
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set t := S / ‖ξ‖
  have ht : 0 < t := div_pos (by linarith) hξ0
  have hη : ‖t • ξ‖ = S := by
    rw [norm_smul, Real.norm_of_nonneg ht.le, div_mul_cancel₀ _ hξ0.ne']
  obtain ⟨hA, hAb⟩ := hRC (t • ξ) (hη ▸ (le_max_left _ _).trans (le_max_left _ _))
  have hsmall : ‖(a.toSymbol.coefficient (x, t • ξ)).inverse‖ *
      ‖-(a.remainder default 1).coefficient (x, t • ξ)‖ < 1 := by
    rw [norm_neg]
    calc _ ≤ max C 0 * (1 + ‖t • ξ‖ ^ 2) ^ (-m / 2) *
          (C₂ * (1 + ‖t • ξ‖ ^ 2) ^ ((m - 1) / 2)) := by
          gcongr
          · exact hAb.trans (by gcongr; exact le_max_left _ _)
          · exact hr x rfl _
      _ = max C 0 * C₂ * (1 + ‖t • ξ‖ ^ 2) ^ (-m / 2) * (1 + ‖t • ξ‖ ^ 2) ^ ((m - 1) / 2) := by
          ring
      _ ≤ 1 / 2 := mul_rpow_mul_rpow_le_half (by positivity) (by linarith)
          (hη ▸ le_max_right _ _)
      _ < 1 := by norm_num
  have hp := hA.add hsmall
  rw [a.coefficient_toSymbol_eq_principal_add default (hη ▸ hS2), add_neg_cancel_right,
    a.principal.homogeneous x ξ t ht, ← Complex.coe_smul,
    ContinuousLinearMap.isInvertible_smul_iff (by exact_mod_cast (Real.rpow_pos_of_pos ht m).ne')]
    at hp
  exact hp

/-- **Ellipticity of a classical symbol through its full symbol.** A classical symbol `a` of order
`m` is elliptic exactly when, on each compact set of positions, it is invertible at all large
frequencies with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` there. -/
theorem isElliptic_iff_exists_isInvertible_and_norm_inverse_le [CompleteSpace V]
    {a : ClassicalSymbol n V W m} :
    a.IsElliptic ↔ ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ R C : ℝ, ∀ x ∈ K, ∀ ξ,
      R ≤ ‖ξ‖ → (a.toSymbol.coefficient (x, ξ)).IsInvertible ∧
        ‖(a.toSymbol.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) :=
  ⟨fun ha _ hK => ha.exists_isInvertible_and_norm_inverse_le hK, fun h =>
    isElliptic_of_forall_exists_isInvertible_and_norm_inverse_le fun x =>
      (h {x} isCompact_singleton).imp fun _ => Exists.imp fun _ hC ξ hξ => hC x rfl ξ hξ⟩

end ClassicalSymbol

end TauCeti
