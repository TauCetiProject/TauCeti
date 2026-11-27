/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Bounds

/-!
# Ellipticity of classical symbols at large frequencies

The principal symbol `a_m` of a classical symbol `a` of order `m` governs the full symbol at large
frequencies: `a(x, ξ) - a_m(x, ξ)` has order `m - 1`. This file reads invertibility of `a_m` off
invertibility of the full symbol with the inverse bound `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`
(`TauCeti.Symbol.IsEllipticOn`), and conversely, both globally and microlocally.

* `TauCeti.ClassicalSymbol.isElliptic_iff_forall_isCompact`: `a` is elliptic, that is `a_m(x, ξ)`
  is invertible at every nonzero frequency, exactly when on every compact set of positions the full
  symbol is invertible with the inverse bound at all large frequencies.
* `TauCeti.ClassicalSymbol.exists_isEllipticOn_of_isInvertible_coefficient_principal`: **microlocal
  ellipticity.** If `a_m(x₀, ξ₀)` is invertible at one point with `ξ₀ ≠ 0`, then the full symbol is
  invertible with the inverse bound at the points `(x, ξ)` with `x` near `x₀`, `ξ` in an open cone
  around `ξ₀` and `‖ξ‖` large. Since `a_m` is continuous away from `ξ = 0` and homogeneous, it is
  invertible with `‖a_m(x, ξ)⁻¹‖ ≤ B ‖ξ‖^(-m)` on such a conic neighbourhood
  (`TauCeti.HomogeneousSymbol.exists_isInvertible_and_norm_inverse_le_rpow`), and the full symbol
  is a small perturbation of it there.
* `TauCeti.ClassicalSymbol.isInvertible_coefficient_principal_of_isEllipticOn`: the converse,
  along the ray through `ξ₀`
  (`TauCeti.ClassicalSymbol.isInvertible_coefficient_principal_of_eventually`).

Together these say that the characteristic set of a classical symbol is the set of nonzero
covectors at which its principal symbol is not invertible
(`TauCeti.ClassicalSymbol.mem_characteristicSet_toSymbol_iff`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (classical
  symbols, their principal symbols and the characteristic set).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.6).
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

namespace ClassicalSymbol

/-! ### Global ellipticity -/

/-- **Ellipticity from invertibility at large frequencies.** If at every position `x` the full
symbol `a(x, ξ)` is invertible at all frequencies of norm at least some `R`, with
`‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`, then the classical symbol is elliptic. -/
theorem isElliptic_of_forall_exists_norm_inverse_le {a : ClassicalSymbol n V W m}
    (h : ∀ x, ∃ R C : ℝ, ∀ ξ, R ≤ ‖ξ‖ → (a.toSymbol.coefficient (x, ξ)).IsInvertible ∧
      ‖(a.toSymbol.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) :
    a.IsElliptic := by
  refine isElliptic_iff.2 fun x ξ hξ ↦ (h x).elim fun R ⟨C, hRC⟩ ↦
    isInvertible_coefficient_principal_of_eventually hξ (C := C) ?_
  filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (R / ‖ξ‖)] with t ht htR
  exact hRC _ (by rwa [norm_smul, Real.norm_of_nonneg ht.le, ← div_le_iff₀ (norm_pos_iff.2 hξ)])

/-- **Ellipticity as invertibility at large frequencies.** A classical symbol of order `m` is
elliptic exactly when, on every compact set of positions, its full symbol `a(x, ξ)` is invertible
at all frequencies of norm at least some radius `R`, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`. -/
theorem isElliptic_iff_forall_isCompact {a : ClassicalSymbol n V W m} :
    a.IsElliptic ↔ ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ R C : ℝ, ∀ x ∈ K, ∀ ξ,
      R ≤ ‖ξ‖ → (a.toSymbol.coefficient (x, ξ)).IsInvertible ∧
        ‖(a.toSymbol.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2) :=
  ⟨fun ha _ hK ↦ ha.exists_isInvertible_and_norm_inverse_le hK, fun h ↦
    isElliptic_of_forall_exists_norm_inverse_le fun x ↦
      (h {x} isCompact_singleton).imp fun _ ↦ .imp fun _ hC ξ ↦ hC x rfl ξ⟩

/-! ### Microlocal ellipticity -/

/-- **Microlocal ellipticity from the principal symbol.** If the principal symbol of a classical
symbol of order `m` is invertible at `(x₀, ξ₀)` with `ξ₀ ≠ 0`, then the symbol is elliptic
(`TauCeti.Symbol.IsEllipticOn`) at the points `(x, ξ)` with `x` in a neighbourhood `U` of `x₀`,
`ξ` in an open cone `Γ` containing `ξ₀` and `‖ξ‖` at least some radius. -/
theorem exists_isEllipticOn_of_isInvertible_coefficient_principal {a : ClassicalSymbol n V W m}
    {x₀ ξ₀ : CoordinateSpace n} (hξ₀ : ξ₀ ≠ 0)
    (ha : (a.principal.coefficient (x₀, ξ₀)).IsInvertible) :
    ∃ U ∈ 𝓝 x₀, ∃ Γ : Set (CoordinateSpace n), IsOpen Γ ∧ ξ₀ ∈ Γ ∧
      (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
        ∃ R : ℝ, a.toSymbol.IsEllipticOn {q | q.1 ∈ U ∧ q.2 ∈ Γ ∧ R ≤ ‖q.2‖} := by
  obtain ⟨U, hU, Γ, hΓ, hξ₀Γ, hcone, B, hB⟩ :=
    a.principal.exists_isInvertible_and_norm_inverse_le_rpow hξ₀ ha
  obtain ⟨δ, hδ, hδU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hU
  -- For `‖ξ‖ ≥ 2`, `‖ξ‖^(-m) ≤ 2^(|m| / 2) ⟨ξ⟩^(-m)`, so the principal symbol satisfies the inverse
  -- bound of order `-m` over `closedBall x₀ δ × Γ`, and the full symbol is a small perturbation.
  obtain ⟨R, C, hRC⟩ := exists_isInvertible_and_norm_inverse_le_of_principal
    (isCompact_closedBall x₀ δ) (Γ := Γ) (C₀ := B * 2 ^ (|m| / 2)) fun x hx ξ hξ h2 ↦ by
      obtain ⟨hinv, hbound⟩ := hB x (hδU hx) ξ hξ (norm_pos_iff.1 (by linarith))
      have hw := Real.abs_rpow_le_two_rpow_mul_one_add_sq_rpow (t := ‖ξ‖)
        (by rw [abs_norm]; linarith) (-m)
      rw [abs_norm, abs_neg] at hw
      have hB0 : 0 ≤ B :=
        nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hbound) (by positivity)
      refine ⟨hinv, hbound.trans ?_⟩
      calc B * ‖ξ‖ ^ (-m) ≤ B * (2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) := by gcongr
        _ = _ := by ring
  exact ⟨Metric.closedBall x₀ δ, Metric.closedBall_mem_nhds x₀ hδ, Γ, hΓ, hξ₀Γ, hcone, R,
    Symbol.isEllipticOn_iff.2 fun _ _ ↦ ⟨C, fun p hp _ ↦ hRC p.1 hp.1 p.2 hp.2.1 hp.2.2⟩⟩

/-- **The principal symbol where the symbol is microlocally elliptic.** If a classical symbol of
order `m` is elliptic (`TauCeti.Symbol.IsEllipticOn`) at the points `(x, ξ)` with `x ∈ U`, `ξ ∈ Γ`
and `‖ξ‖ ≥ R`, then its principal symbol is invertible at every `(x₀, ξ₀)` with `x₀ ∈ U` and
`ξ₀ ≠ 0` whose ray `{t ξ₀ | t > 0}` lies in `Γ`. -/
theorem isInvertible_coefficient_principal_of_isEllipticOn {a : ClassicalSymbol n V W m}
    {x₀ ξ₀ : CoordinateSpace n} (hξ₀ : ξ₀ ≠ 0) {U Γ : Set (CoordinateSpace n)} (hx₀ : x₀ ∈ U)
    (hray : ∀ t : ℝ, 0 < t → t • ξ₀ ∈ Γ) {R : ℝ}
    (ha : a.toSymbol.IsEllipticOn {q | q.1 ∈ U ∧ q.2 ∈ Γ ∧ R ≤ ‖q.2‖}) :
    (a.principal.coefficient (x₀, ξ₀)).IsInvertible := by
  obtain ⟨C, hC⟩ := Symbol.isEllipticOn_iff.1 ha {x₀} isCompact_singleton
  refine isInvertible_coefficient_principal_of_eventually hξ₀ (C := C) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (R / ‖ξ₀‖)] with t ht htR
  refine hC (x₀, t • ξ₀) ⟨hx₀, hray t ht, ?_⟩ rfl
  rw [norm_smul, Real.norm_of_nonneg ht.le]
  exact (div_le_iff₀ (norm_pos_iff.2 hξ₀)).1 htR

end ClassicalSymbol

end TauCeti
