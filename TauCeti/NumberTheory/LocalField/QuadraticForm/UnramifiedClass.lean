/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.NumberTheory.LocalField.Uniformizer

import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.Algebra.QuadraticAlgebra.NormTrace
import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup
import TauCeti.RingTheory.Finite.ArtinSchreier
import TauCeti.NumberTheory.LocalField.UnitsDecomposition
import TauCeti.RingTheory.Norm.Henselian

/-!
# The unramified quadratic class of a local field

Let `K` be a nonarchimedean local field with `2 ≠ 0`. This file produces the square class of the
unramified quadratic extension in norm-equation form: a unit `Δ` of `𝒪[K]` such that `b ∈ Kˣ` is
a norm from `K(√Δ)`, that is `b = x² - Δ y²` for some `x y : K`, exactly when the normalized
valuation `v_K(b)` is even. Equivalently, every unit is a norm and a uniformizer is not. No
extension of `K` is constructed; the statement is about the binary form `x² - Δ y²` over `K`.

The class is explicit. Choose `c ∈ 𝒪[K]` whose residue is not of the form `t² + t` in the finite
residue field `𝓀[K]`; such a residue exists because the Artin–Schreier map `t ↦ t² + t` identifies
`0` and `-1`. Then `Δ = 1 + 4c`. Since `2` is invertible,

`x² - (1 + 4c) y² = (x - y)² + (x - y)(2y) - c (2y)²`,

so the norm equation for `Δ` is the one for the norm form `x² + xy - cy²` of
`QuadraticAlgebra 𝒪[K] c 1`, the ring `𝒪[K][ω]` with `ω² = c + ω`. Its reduction
`x² + xy - residue(c)y²`
is anisotropic over `𝓀[K]` by the choice of `c`. Hence a value of the form at a primitive integral
vector is a unit, and every value has even valuation. Conversely the residue norm form is the norm
of the quadratic extension of the finite field `𝓀[K]`, which is surjective, and Hensel's lemma for
the norm (`TauCeti.Algebra.exists_norm_eq_of_norm_sub_mem_maximalIdeal`, with the unit `ω` of
unit trace `1`) lifts it to every unit of `𝒪[K]`. The argument does not distinguish odd from even
residue characteristic. In odd residue characteristic `Δ` is a unit with nonsquare residue, and
over `ℚ₂` the choice `c = -1` gives `Δ = -3`, in the square class of `5`.

With the Hilbert symbol this reads `(Δ, b)_K = (-1)^{v_K(b)}`.

## Main results

* `TauCeti.exists_eq_sq_sub_one_add_four_mul_mul_sq_iff_even`: for `c` as above, `b` is a norm
  from `K(√(1 + 4c))` exactly when `v_K(b)` is even.
* `TauCeti.exists_unramified_class`: there is a nonsquare `Δ` of valuation zero whose norms are
  exactly the elements of even valuation.
* `TauCeti.not_isSquare_of_unramified_class`: every class with this norm criterion is nonsquare.
* `TauCeti.unramified_class_of_isSquare_mul`: the criterion is invariant under square classes.
* `TauCeti.hilbertSymbol_unramified`: for such a `Δ`, `(Δ, b)_K = (-1)^{v_K(b)}`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *Local Fields*, Chapter V, §2.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section NormForm

variable {c : 𝒪[K]}

/-- If the residue of `c` is not of the form `t² + t`, the residue quadratic algebra
`𝓀[K][ω]`, `ω² = residue(c) + ω`, is a field. -/
private theorem fact_residue (hc : ∀ t : 𝓀[K], t ^ 2 + t ≠ residue 𝒪[K] c) :
    Fact (∀ r : 𝓀[K], r ^ 2 ≠ residue 𝒪[K] c + 1 * r) :=
  ⟨fun r hr ↦ hc (-r) (by linear_combination hr)⟩

/-- The value of `x² + xy - cy²` at an integral vector that is nonzero modulo `𝓂[K]` is a unit:
the reduction of the form is anisotropic. -/
private theorem isUnit_sq_add_mul_sub_mul_sq (hc : ∀ t : 𝓀[K], t ^ 2 + t ≠ residue 𝒪[K] c)
    {s t : 𝒪[K]} (hst : s ∉ 𝓂[K] ∨ t ∉ 𝓂[K]) : IsUnit (s ^ 2 + s * t - c * t ^ 2) := by
  have := fact_residue hc
  rw [← residue_ne_zero_iff_isUnit]
  intro h
  have h0 : (⟨residue 𝒪[K] s, residue 𝒪[K] t⟩ : QuadraticAlgebra 𝓀[K] (residue 𝒪[K] c) 1) = 0 := by
    rw [← QuadraticAlgebra.norm_eq_zero_iff_eq_zero, QuadraticAlgebra.norm_def]
    simp only [map_add, map_sub, map_mul, map_pow] at h
    linear_combination h
  rcases hst with hs | ht
  · exact hs ((residue_eq_zero_iff s).mp (congrArg QuadraticAlgebra.re h0))
  · exact ht ((residue_eq_zero_iff t).mp (congrArg QuadraticAlgebra.im h0))

/-- Every nonzero value of `x² + xy - cy²` on `K` has even valuation. -/
private theorem even_of_eq_sq_add_mul_sub_mul_sq (hc : ∀ t : 𝓀[K], t ^ 2 + t ≠ residue 𝒪[K] c)
    {b : Kˣ} {x y : K} (hb : (b : K) = x ^ 2 + x * y - c * y ^ 2) :
    Even (normalizedValuation K b).toAdd := by
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra! h
    exact b.ne_zero (by simp [hb, h.1, h.2])
  -- Dividing by the coordinate of larger valuation gives a primitive integral vector, at which the
  -- form takes a unit value. So `b` is a square times a unit of `𝒪[K]`.
  obtain ⟨p, w, hpw⟩ : ∃ (p : Kˣ) (w : 𝒪[K]ˣ), (b : K) = (p : K) ^ 2 * ((w : 𝒪[K]) : K) := by
    rcases le_total (valuation K y) (valuation K x) with h | h
    · have hx : x ≠ 0 := by
        rintro rfl
        exact hxy.resolve_left (not_not.mpr rfl) ((valuation K).zero_iff.mp (by simpa using h))
      have ht : y / x ∈ 𝒪[K] := by
        rw [Valuation.mem_integer_iff, map_div₀]
        exact div_le_one_of_le₀ h zero_le
      have hu := isUnit_sq_add_mul_sub_mul_sq hc (s := 1) (t := ⟨y / x, ht⟩) (Or.inl (by simp))
      refine ⟨Units.mk0 x hx, hu.unit, ?_⟩
      rw [IsUnit.unit_spec, Units.val_mk0, hb]
      push_cast
      field_simp
    · have hy : y ≠ 0 := by
        rintro rfl
        exact hxy.resolve_right (not_not.mpr rfl) ((valuation K).zero_iff.mp (by simpa using h))
      have hs : x / y ∈ 𝒪[K] := by
        rw [Valuation.mem_integer_iff, map_div₀]
        exact div_le_one_of_le₀ h zero_le
      have hu := isUnit_sq_add_mul_sub_mul_sq hc (s := ⟨x / y, hs⟩) (t := 1) (Or.inr (by simp))
      refine ⟨Units.mk0 y hy, hu.unit, ?_⟩
      rw [IsUnit.unit_spec, Units.val_mk0, hb]
      push_cast
      field_simp
  have hbpw : b = p ^ 2 * Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) w :=
    Units.ext (by simpa using hpw)
  rw [hbpw, map_mul, normalizedValuation_integerUnits, mul_one]
  exact even_toAdd_normalizedValuation_of_isSquare (IsSquare.sq p)

/-- Every unit of `𝒪[K]` is a value of `x² + xy - cy²` on `𝒪[K]`, by Hensel's lemma for the norm
of `𝒪[K][ω]`, `ω² = c + ω`, from the surjectivity of the norm of the residue extension. -/
private theorem exists_sq_add_mul_sub_mul_sq_eq (hc : ∀ t : 𝓀[K], t ^ 2 + t ≠ residue 𝒪[K] c)
    (u : 𝒪[K]ˣ) : ∃ s t : 𝒪[K], s ^ 2 + s * t - c * t ^ 2 = u := by
  have := fact_residue hc
  have : Finite (QuadraticAlgebra 𝓀[K] (residue 𝒪[K] c) 1) := Module.finite_of_finite 𝓀[K]
  -- The residue norm form represents the residue of `u`. The algebra structure is pinned to the
  -- quadratic algebra's own: instance search would build one through
  -- `ResidueField.algebraOfIsIntegral`, which is not reducibly the same.
  obtain ⟨z, hz⟩ := @FiniteField.norm_surjective 𝓀[K]
    (QuadraticAlgebra 𝓀[K] (residue 𝒪[K] c) 1) _ _ QuadraticAlgebra.instAlgebra _
    (residue 𝒪[K] u)
  replace hz : z.norm = residue 𝒪[K] u := (QuadraticAlgebra.algebraNorm_eq_norm z).symm.trans hz
  obtain ⟨s, hs⟩ := residue_surjective z.re
  obtain ⟨t, ht⟩ := residue_surjective z.im
  -- `ω` is a unit of unit trace, so Hensel's lemma for the norm applies.
  have hc0 : IsUnit c := by
    rw [← residue_ne_zero_iff_isUnit]
    exact fun h ↦ hc 0 (by simp [h])
  have hw : IsUnit (QuadraticAlgebra.omega : QuadraticAlgebra 𝒪[K] c 1) := by
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, QuadraticAlgebra.norm_def]
    simpa using hc0.neg
  have htr : IsUnit (Algebra.trace 𝒪[K] (QuadraticAlgebra 𝒪[K] c 1) QuadraticAlgebra.omega) := by
    rw [QuadraticAlgebra.algebraTrace_eq_trace, QuadraticAlgebra.trace_omega]
    exact isUnit_one
  obtain ⟨y, hy, -⟩ := Algebra.exists_norm_eq_of_norm_sub_mem_maximalIdeal hw htr
    (a := (⟨s, t⟩ : QuadraticAlgebra 𝒪[K] c 1)) u.isUnit (by
      rw [QuadraticAlgebra.algebraNorm_eq_norm, ← residue_eq_zero_iff, map_sub, ← hz,
        QuadraticAlgebra.norm_def, QuadraticAlgebra.norm_def]
      simp [hs, ht])
  refine ⟨y.re, y.im, ?_⟩
  rw [QuadraticAlgebra.algebraNorm_eq_norm, QuadraticAlgebra.norm_def] at hy
  linear_combination hy

/-- **The unramified quadratic class, explicitly.** Let `c ∈ 𝒪[K]` have residue outside the image
of `t ↦ t² + t`. Then `b ∈ Kˣ` is a norm from `K(√(1 + 4c))`, that is `b = x² - (1 + 4c) y²` for
some `x y : K`, exactly when `v_K(b)` is even. -/
theorem exists_eq_sq_sub_one_add_four_mul_mul_sq_iff_even (h2 : (2 : K) ≠ 0) {c : 𝒪[K]}
    (hc : ∀ t : 𝓀[K], t ^ 2 + t ≠ residue 𝒪[K] c) (b : Kˣ) :
    (∃ x y : K, (b : K) = x ^ 2 - (1 + 4 * (c : K)) * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd := by
  constructor
  · rintro ⟨x, y, hb⟩
    exact even_of_eq_sq_add_mul_sub_mul_sq hc (x := x - y) (y := 2 * y) (by rw [hb]; ring)
  · rintro ⟨k, hk⟩
    -- Write `b = ϖ^{2k} u` with `ϖ` a uniformizer and `u` a unit of `𝒪[K]`.
    obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
    rw [isUniformizer_def] at hϖ
    have hmem := mul_zpow_neg_mem_unitFiltration_zero hϖ b
    obtain ⟨u, -, hu⟩ := mem_unitFiltration_iff_exists.mp hmem
    obtain ⟨s, t, hst⟩ := exists_sq_add_mul_sub_mul_sq_eq hc u
    have hbu : (b : K) = ((ϖ : K) ^ k) ^ 2 * ((u : 𝒪[K]) : K) := by
      have : b = (ϖ ^ k) ^ 2 * (b * ϖ ^ (-(normalizedValuation K b).toAdd)) := by
        rw [hk, mul_left_comm]
        group
      rw [hu]
      exact_mod_cast congrArg Units.val this
    refine ⟨(ϖ : K) ^ k * ((s : K) + (t : K) / 2), (ϖ : K) ^ k * ((t : K) / 2), ?_⟩
    rw [hbu, ← hst]
    push_cast
    field_simp
    ring

end NormForm

/-- **The unramified quadratic class.** There is a nonsquare `Δ ∈ Kˣ` of valuation
zero such that `b ∈ Kˣ` is a norm from `K(√Δ)`, that is `b = x² - Δ y²` for some `x y : K`,
exactly when `v_K(b)` is even. -/
theorem exists_unramified_class (h2 : (2 : K) ≠ 0) :
    ∃ Δ : Kˣ, ¬IsSquare Δ ∧ (normalizedValuation K Δ).toAdd = 0 ∧
      ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
        Even (normalizedValuation K b).toAdd := by
  obtain ⟨a, ha_range⟩ := exists_not_mem_range_sq_add_self (𝓀[K])
  have ha : ∀ t : 𝓀[K], t ^ 2 + t ≠ a := fun t ht => ha_range ⟨t, ht⟩
  obtain ⟨c, rfl⟩ := residue_surjective a
  -- `1 + 4c = -((1 - 2)² + (1 - 2) · 2 - c · 2²)` is a unit.
  have hΔ : IsUnit (1 + 4 * c) := by
    have := (isUnit_sq_add_mul_sub_mul_sq ha (s := 1) (t := -2) (Or.inl (by simp))).neg
    convert this using 1
    ring
  let Δ : Kˣ := Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) hΔ.unit
  have hcrit := exists_eq_sq_sub_one_add_four_mul_mul_sq_iff_even h2 ha
  have h4 : ((4 : 𝒪[K]) : K) = 4 := map_ofNat 𝒪[K].subtype 4
  have hΔK : (Δ : K) = 1 + 4 * (c : K) := by simp [Δ, h4]
  simp only [← hΔK] at hcrit
  refine ⟨Δ, fun hsq ↦ ?_, by simp [Δ, normalizedValuation_integerUnits], hcrit⟩
  -- A square `Δ` would make a uniformizer, of odd valuation, a norm.
  have : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
  have := (hcrit ϖ).mp ((hilbertSymbol_eq_one_iff Δ ϖ).mp
    (hilbertSymbol_eq_one_of_isSquare_left hsq ϖ))
  rw [(isUniformizer_def ϖ).mp hϖ, toAdd_ofAdd] at this
  exact Int.not_even_one this

/-- If the norms from `K(√a)` are exactly the elements of even normalized valuation, then
`a` is not a square. -/
theorem not_isSquare_of_unramified_class (h2 : (2 : K) ≠ 0) {a : Kˣ}
    (ha : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd) :
    ¬IsSquare a := by
  intro hsq
  have : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
  have h := (ha ϖ).mp ((hilbertSymbol_eq_one_iff a ϖ).mp
    (hilbertSymbol_eq_one_of_isSquare_left hsq ϖ))
  rw [(isUniformizer_def ϖ).mp hϖ, toAdd_ofAdd] at h
  exact Int.not_even_one h

/-- The norm criterion only depends on the square class of `a`. -/
theorem unramified_class_of_isSquare_mul {a Δ : Kˣ} (h : IsSquare (a * Δ))
    (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd) (b : Kˣ) :
    (∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2) ↔ Even (normalizedValuation K b).toAdd := by
  rw [← hilbertSymbol_eq_one_iff, hilbertSymbol_congr_sq a Δ b b h ⟨b, rfl⟩,
    hilbertSymbol_eq_one_iff]
  exact hΔ b

/-- **Evaluation against the unramified class.** If the norms from `K(√Δ)` are exactly the
elements of even valuation, as for the class of `TauCeti.exists_unramified_class`, then
`(Δ, b)_K = (-1)^{v_K(b)}`. -/
theorem hilbertSymbol_unramified {Δ : Kˣ}
    (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd) (b : Kˣ) :
    hilbertSymbol Δ b = if Even (normalizedValuation K b).toAdd then 1 else -1 := by
  split_ifs with h
  · exact (hilbertSymbol_eq_one_iff Δ b).mpr ((hΔ b).mpr h)
  · exact (hilbertSymbol_eq_neg_one_iff Δ b).mpr (mt (hΔ b).mp h)

end TauCeti
