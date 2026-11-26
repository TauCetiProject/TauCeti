/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.Basic
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Normed.Module.Cone
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
* `TauCeti.ClassicalSymbol.exists_isEllipticOn_of_isInvertible_principal`: **microlocal
  ellipticity.** If `a_m(x₀, ξ₀)` is invertible at one point with `ξ₀ ≠ 0`, then the full symbol is
  invertible with the inverse bound at the points `(x, ξ)` with `x` near `x₀`, `ξ` in an open cone
  around `ξ₀` and `‖ξ‖` large. Since `a_m` is continuous away from `ξ = 0` and homogeneous, it is
  invertible with `‖a_m(x, ξ)⁻¹‖ ≤ B ‖ξ‖^(-m)` on such a conic neighbourhood
  (`TauCeti.HomogeneousSymbol.exists_isInvertible_and_norm_inverse_le_rpow`), and the full symbol
  is a small perturbation of it there.
* `TauCeti.ClassicalSymbol.isInvertible_principal_of_isEllipticOn`: the converse, along the ray
  through `ξ₀` (`TauCeti.ClassicalSymbol.isInvertible_principal_of_forall_smul`).

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

open Topology

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
  refine isElliptic_iff.2 fun x ξ hξ ↦ ?_
  obtain ⟨R, C, hRC⟩ := h x
  exact isInvertible_principal_of_forall_smul (R := R) (C := C) hξ fun t _ ↦ hRC (t • ξ)

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

end ClassicalSymbol

/-! ### Microlocal ellipticity -/

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

omit [CompleteSpace V] in
/-- Near `(x₀, ξ₀)` with `ξ₀ ≠ 0`, a homogeneous symbol read on the sphere of radius `‖ξ₀‖` is
close to its value at `(x₀, ξ₀)`, on a neighbourhood of `x₀` times an open cone around `ξ₀`. -/
private theorem exists_cone_norm_sub_lt (h : HomogeneousSymbol X E V W m) {x₀ : X} {ξ₀ : E}
    (hξ₀ : ξ₀ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 x₀, ∃ Γ : Set E, IsOpen Γ ∧ ξ₀ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ x ∈ U, ∀ ξ ∈ Γ,
        ‖h.coefficient (x, (‖ξ₀‖ * ‖ξ‖⁻¹) • ξ) - h.coefficient (x₀, ξ₀)‖ < ε := by
  have hn₀ : 0 < ‖ξ₀‖ := norm_pos_iff.2 hξ₀
  -- The point `ν(x, ξ)` of the sphere of radius `‖ξ₀‖` on the ray through `ξ`, unchanged by
  -- positive rescalings of `ξ`.
  set ν : X × E → X × E := fun q ↦ (q.1, (‖ξ₀‖ * ‖q.2‖⁻¹) • q.2)
  have hν₀ : ν (x₀, ξ₀) = (x₀, ξ₀) := by simp [ν, hn₀.ne']
  have hν (x : X) (ξ : E) {t : ℝ} (ht : 0 < t) : ν (x, t • ξ) = ν (x, ξ) := by
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp [ν]
    have hξ' : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
    simp only [ν, norm_smul, Real.norm_of_nonneg ht.le, smul_smul, Prod.mk.injEq, true_and]
    congr 1
    field_simp
  have hc : ContinuousAt (fun q ↦ ‖h.coefficient (ν q) - h.coefficient (x₀, ξ₀)‖) (x₀, ξ₀) := by
    refine (ContinuousAt.comp (f := ν) ?_ (continuousAt_fst.prodMk ((continuousAt_const.mul
      (continuous_snd.norm.continuousAt.inv₀ hn₀.ne')).smul continuousAt_snd))).sub
      continuousAt_const |>.norm
    rw [hν₀]
    exact h.continuousOn_coefficient.continuousAt
      ((isOpen_ne_fun continuous_snd continuous_const).mem_nhds hξ₀)
  -- A product neighbourhood `u × v` where the bound holds, and the cone `Γ` of the rays through
  -- the interior of `v`.
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 <|
    hc.eventually_lt (continuousAt_const (y := ε)) (by simpa [hν₀] using hε)
  obtain ⟨Γ, hΓ, hξ₀Γ, hcone, hΓv⟩ :=
    isOpen_interior.exists_cone_exists_smul_mem (mem_interior_iff_mem_nhds.2 hv)
  refine ⟨u, hu, Γ, hΓ, hξ₀Γ, hcone, fun x hx ξ hξ ↦ ?_⟩
  obtain ⟨t, ht, htξ⟩ := hΓv ξ hξ
  have h' : ‖h.coefficient (ν (x, t • ξ)) - h.coefficient (x₀, ξ₀)‖ < ε :=
    huv (Set.mk_mem_prod hx (interior_subset htξ))
  rwa [hν x ξ ht] at h'

/-- **A homogeneous symbol invertible at a point is invertible on a conic neighbourhood.** If a
homogeneous symbol `h` of degree `m` is invertible at `(x₀, ξ₀)` with `ξ₀ ≠ 0`, then for some
neighbourhood `U` of `x₀`, some open cone `Γ` containing `ξ₀` and some constant `B`, the value
`h(x, ξ)` is invertible with `‖h(x, ξ)⁻¹‖ ≤ B ‖ξ‖^(-m)` for all `x ∈ U` and nonzero `ξ ∈ Γ`. -/
theorem exists_isInvertible_and_norm_inverse_le_rpow (h : HomogeneousSymbol X E V W m) {x₀ : X}
    {ξ₀ : E} (hξ₀ : ξ₀ ≠ 0) (ha : (h.coefficient (x₀, ξ₀)).IsInvertible) :
    ∃ U ∈ 𝓝 x₀, ∃ Γ : Set E, IsOpen Γ ∧ ξ₀ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∃ B : ℝ, ∀ x ∈ U, ∀ ξ ∈ Γ, ξ ≠ 0 → (h.coefficient (x, ξ)).IsInvertible ∧
        ‖(h.coefficient (x, ξ)).inverse‖ ≤ B * ‖ξ‖ ^ (-m) := by
  set A := h.coefficient (x₀, ξ₀)
  set M := ‖A.inverse‖ + 1
  have hAM : ‖A.inverse‖ ≤ M := le_add_of_nonneg_right zero_le_one
  have hM : 0 < M := by positivity
  have hn₀ : 0 < ‖ξ₀‖ := norm_pos_iff.2 hξ₀
  obtain ⟨U, hU, Γ, hΓ, hξ₀Γ, hcone, hUΓ⟩ :=
    h.exists_cone_norm_sub_lt hξ₀ (ε := (2 * M)⁻¹) (by positivity)
  refine ⟨U, hU, Γ, hΓ, hξ₀Γ, hcone, 2 * M * ‖ξ₀‖ ^ m, fun x hx ξ hξ hξ0 ↦ ?_⟩
  -- `B = h(x, ‖ξ₀‖ ‖ξ‖⁻¹ ξ)` is within `(2 M)⁻¹` of `A`, so it is invertible with `‖B⁻¹‖ ≤ 2 M`;
  -- and `h(x, ξ) = s^m B` for `s = ‖ξ‖ / ‖ξ₀‖`, so `‖h(x, ξ)⁻¹‖ = s^(-m) ‖B⁻¹‖`.
  set B := h.coefficient (x, (‖ξ₀‖ * ‖ξ‖⁻¹) • ξ)
  have hsmall : M * ‖B - A‖ < 1 / 2 :=
    calc M * ‖B - A‖ < M * (2 * M)⁻¹ := mul_lt_mul_of_pos_left (hUΓ x hx ξ hξ) hM
      _ = 1 / 2 := by field_simp
  have hB : B.IsInvertible := ha.of_mul_norm_sub_lt hAM (by linarith)
  have hBM : ‖B.inverse‖ ≤ 2 * M := by
    refine (ha.norm_inverse_le_of_mul_norm_sub_lt hAM (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ0
  set s := ‖ξ‖ / ‖ξ₀‖ with hs_def
  have hs : 0 < s := div_pos hn hn₀
  have hsm : (0 : ℝ) < s ^ m := Real.rpow_pos_of_pos hs m
  have hP : h.coefficient (x, ξ) = ((s ^ m : ℝ) : ℂ) • B := by
    rw [Complex.coe_smul, ← h.homogeneous x _ s hs, smul_smul,
      show s * (‖ξ₀‖ * ‖ξ‖⁻¹) = 1 by rw [hs_def]; field_simp, one_smul]
  refine ⟨hP ▸ (ContinuousLinearMap.isInvertible_smul_iff
    (Complex.ofReal_ne_zero.2 hsm.ne')).2 hB, ?_⟩
  rw [hP, ContinuousLinearMap.inverse_smul, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hsm.le, Real.div_rpow hn.le hn₀.le, inv_div, Real.rpow_neg hn.le]
  calc ‖ξ₀‖ ^ m / ‖ξ‖ ^ m * ‖B.inverse‖ ≤ ‖ξ₀‖ ^ m / ‖ξ‖ ^ m * (2 * M) := by gcongr
    _ = _ := by ring

end HomogeneousSymbol

namespace ClassicalSymbol

/-- **Microlocal ellipticity from the principal symbol.** If the principal symbol of a classical
symbol of order `m` is invertible at `(x₀, ξ₀)` with `ξ₀ ≠ 0`, then the symbol is elliptic
(`TauCeti.Symbol.IsEllipticOn`) at the points `(x, ξ)` with `x` in a neighbourhood `U` of `x₀`,
`ξ` in an open cone `Γ` containing `ξ₀` and `‖ξ‖` at least some radius. -/
theorem exists_isEllipticOn_of_isInvertible_principal {a : ClassicalSymbol n V W m}
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
theorem isInvertible_principal_of_isEllipticOn {a : ClassicalSymbol n V W m}
    {x₀ ξ₀ : CoordinateSpace n} (hξ₀ : ξ₀ ≠ 0) {U Γ : Set (CoordinateSpace n)} (hx₀ : x₀ ∈ U)
    (hray : ∀ t : ℝ, 0 < t → t • ξ₀ ∈ Γ) {R : ℝ}
    (ha : a.toSymbol.IsEllipticOn {q | q.1 ∈ U ∧ q.2 ∈ Γ ∧ R ≤ ‖q.2‖}) :
    (a.principal.coefficient (x₀, ξ₀)).IsInvertible := by
  obtain ⟨C, hC⟩ := Symbol.isEllipticOn_iff.1 ha {x₀} isCompact_singleton
  exact isInvertible_principal_of_forall_smul (R := R) (C := C) hξ₀ fun t ht htR ↦
    hC (x₀, t • ξ₀) ⟨hx₀, hray t ht, htR⟩ rfl

end ClassicalSymbol

end TauCeti
