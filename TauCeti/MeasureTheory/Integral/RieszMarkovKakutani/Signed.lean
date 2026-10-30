/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import TauCeti.Topology.ContinuousMap.CompactlySupported

/-!
# The Riesz–Markov–Kakutani theorem for order-bounded functionals

Mathlib's Riesz–Markov–Kakutani theorem (`RealRMK.integral_rieszMeasure`) represents a *positive*
linear functional on `C_c(X, ℝ)` by a regular measure. A linear functional
`Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ` which is only *order bounded*, meaning that `Λ` is bounded above on every
order interval `[0, f]`, is represented by the difference of two regular measures, which need
not be finite. For instance, a functional bounded in the sup norm on the functions supported in
each compact set is order bounded, since `0 ≤ g ≤ f` forces `tsupport g ⊆ tsupport f` and
`g ≤ f`; distributional derivatives of locally finite total variation, tested against continuous
functions, are of this kind.

The proof is the Jordan decomposition of `Λ`. Its **positive part** `Λ⁺` is defined on
nonnegative functions by
`Λ⁺ f = ⨆ { Λ g | 0 ≤ g ≤ f }`,
which is additive by the Riesz decomposition property of `C_c(X, ℝ≥0)`: a function below
`f₁ + f₂` is a sum of a function below `f₁` and one below `f₂`. It extends to a positive linear
functional on `C_c(X, ℝ)` (`CompactlySupportedContinuousMap.toRealPositiveLinear`), and so does
the **negative part** `Λ⁻ = Λ⁺ - Λ`. The two parts are the least positive functionals dominating
`Λ` and `-Λ`, and the Riesz measures of `Λ⁺` and `Λ⁻` represent `Λ`.

## Main declarations

* `TauCeti.RealRMK.posPart Λ hΛ`, `TauCeti.RealRMK.negPart Λ hΛ`: the positive and negative parts
  of an order-bounded linear functional `Λ`, positive linear functionals with
  `Λ = posPart Λ hΛ - negPart Λ hΛ` (`TauCeti.RealRMK.posPart_sub_negPart_apply`).
* `TauCeti.RealRMK.posPart_apply_of_nonneg`, `TauCeti.RealRMK.negPart_apply_of_nonneg`: on a
  nonnegative `f` they are the suprema of `Λ` and of `-Λ` over `[0, f]`.
* `TauCeti.RealRMK.posPart_apply_le_of_le`, `TauCeti.RealRMK.negPart_apply_le_of_le`: minimality
  among positive functionals dominating `Λ` and `-Λ`.
* `TauCeti.RealRMK.integral_rieszMeasure_posPart_sub_integral_rieszMeasure_negPart`: the
  Riesz–Markov–Kakutani representation of an order-bounded functional.
* `TauCeti.RealRMK.forall_bddAbove_image_Icc_iff_exists_regular`: a linear functional on
  `C_c(X, ℝ)` is a difference of integrals against two regular measures if and only if it is
  order bounded.

## References

* G. B. Folland, *Real Analysis*, §7.3: the decomposition of a real functional into positive
  parts.
-/

public section

noncomputable section

open CompactlySupportedContinuousMap MeasureTheory Set
open scoped NNReal CompactlySupported

namespace TauCeti.RealRMK

variable {X : Type*} [TopologicalSpace X] {Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ}

section Construction

/-- The positive part of `Λ` on a nonnegative function `f`, the supremum of `Λ` over the
functions between `0` and `f`. -/
private def posPartAux (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (f : C_c(X, ℝ≥0)) : ℝ :=
  ⨆ g : Iic f, Λ (g : C_c(X, ℝ≥0)).toReal

variable (hΛ : ∀ f : C_c(X, ℝ), BddAbove (Λ '' Icc 0 f))
include hΛ

private lemma bddAbove_range_posPartAux (f : C_c(X, ℝ≥0)) :
    BddAbove (range fun g : Iic f => Λ (g : C_c(X, ℝ≥0)).toReal) :=
  (hΛ f.toReal).mono <| by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g.toReal, ⟨toReal_nonneg, toReal_le_toReal_iff.2 hg⟩, rfl⟩

private lemma apply_le_posPartAux {f g : C_c(X, ℝ≥0)} (hg : g ≤ f) :
    Λ g.toReal ≤ posPartAux Λ f :=
  le_ciSup (f := fun g : Iic f => Λ (g : C_c(X, ℝ≥0)).toReal) (bddAbove_range_posPartAux hΛ f)
    ⟨g, hg⟩

omit hΛ in
private lemma posPartAux_le {f : C_c(X, ℝ≥0)} {c : ℝ} (h : ∀ g ≤ f, Λ g.toReal ≤ c) :
    posPartAux Λ f ≤ c :=
  have : Nonempty (Iic f) := ⟨⟨f, mem_Iic.2 le_rfl⟩⟩
  ciSup_le fun g => h g g.2

private lemma posPartAux_nonneg (f : C_c(X, ℝ≥0)) : 0 ≤ posPartAux Λ f := by
  simpa using apply_le_posPartAux hΛ (le_def.2 fun x => by simp : 0 ≤ f)

private lemma posPartAux_add (f₁ f₂ : C_c(X, ℝ≥0)) :
    posPartAux Λ (f₁ + f₂) = posPartAux Λ f₁ + posPartAux Λ f₂ := by
  refine le_antisymm (posPartAux_le fun g hg => ?_) ?_
  · -- Riesz decomposition: `g = g ⊓ f₁ + g₂` with `g₂ ≤ f₂`.
    obtain ⟨g₂, hg₂⟩ := CompactlySupportedContinuousMap.exists_add_of_le (inf_le_left : g ⊓ f₁ ≤ g)
    have hg₂f₂ : g₂ ≤ f₂ := le_def.2 fun x => by
      have hx : min (g x) (f₁ x) + g₂ x = g x := by simpa using congr($hg₂ x)
      have hgx : g x ≤ f₁ x + f₂ x := by simpa using le_def.1 hg x
      rcases le_total (g x) (f₁ x) with h | h
      · rw [min_eq_left h, add_eq_left] at hx
        simp [hx]
      · rw [min_eq_right h] at hx
        exact le_of_add_le_add_left (hx ▸ hgx)
    rw [← hg₂, toReal_add, map_add]
    exact add_le_add (apply_le_posPartAux hΛ inf_le_right) (apply_le_posPartAux hΛ hg₂f₂)
  · rw [← le_sub_iff_add_le]
    refine posPartAux_le fun g₁ hg₁ => ?_
    rw [le_sub_comm]
    refine posPartAux_le fun g₂ hg₂ => ?_
    rw [le_sub_iff_add_le', ← map_add, ← toReal_add]
    exact apply_le_posPartAux hΛ (add_le_add hg₁ hg₂)

omit hΛ in
private lemma apply_toReal_smul (c : ℝ≥0) (g : C_c(X, ℝ≥0)) :
    Λ (c • g).toReal = c * Λ g.toReal := by
  rw [toReal_smul, NNReal.smul_def, map_smul, smul_eq_mul]

private lemma posPartAux_smul (c : ℝ≥0) (f : C_c(X, ℝ≥0)) :
    posPartAux Λ (c • f) = c * posPartAux Λ f := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine le_antisymm (posPartAux_le fun g hg => ?_) (by simpa using posPartAux_nonneg hΛ 0)
    have hg0 : g = 0 := le_antisymm (by simpa using hg) (le_def.2 fun x => by simp)
    simp [hg0]
  have hc₀ : (0 : ℝ) < c := by positivity
  refine le_antisymm (posPartAux_le fun g hg => ?_) ?_
  · -- `g = c • (c⁻¹ • g)` with `c⁻¹ • g ≤ f`.
    have hle : c⁻¹ • g ≤ f := le_def.2 fun x => by
      have hx : g x ≤ c * f x := by simpa using le_def.1 hg x
      simpa [inv_mul_le_iff₀ (pos_iff_ne_zero.2 hc)] using hx
    have hg' : g = c • c⁻¹ • g := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [hg', apply_toReal_smul]
    exact mul_le_mul_of_nonneg_left (apply_le_posPartAux hΛ hle) hc₀.le
  · rw [← le_div_iff₀' hc₀]
    refine posPartAux_le fun g hg => ?_
    rw [le_div_iff₀' hc₀, ← apply_toReal_smul]
    refine apply_le_posPartAux hΛ (le_def.2 fun x => ?_)
    simpa using mul_le_mul_of_nonneg_left (le_def.1 hg x) c.2

/-- The positive part of `Λ` as an `ℝ≥0`-linear functional on `C_c(X, ℝ≥0)`. -/
private def posPartNNReal : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun f := ⟨posPartAux Λ f, posPartAux_nonneg hΛ f⟩
  map_add' f₁ f₂ := NNReal.eq (posPartAux_add hΛ f₁ f₂)
  map_smul' c f := NNReal.eq (posPartAux_smul hΛ c f)

private lemma coe_posPartNNReal_apply (f : C_c(X, ℝ≥0)) :
    (posPartNNReal hΛ f : ℝ) = posPartAux Λ f :=
  (rfl)

end Construction

variable (Λ) (hΛ : ∀ f : C_c(X, ℝ), BddAbove (Λ '' Icc 0 f))

/-- The **positive part** of an order-bounded linear functional `Λ` on `C_c(X, ℝ)`: the positive
linear functional which on a nonnegative `f` is the supremum of `Λ g` over `0 ≤ g ≤ f`
(`TauCeti.RealRMK.posPart_apply_of_nonneg`). It is the least positive functional dominating `Λ`
on nonnegative functions (`TauCeti.RealRMK.posPart_apply_le_of_le`). -/
def posPart : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  toRealPositiveLinear (posPartNNReal hΛ)

variable {Λ}

private lemma posPart_apply_eq_posPartAux {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    posPart Λ hΛ f = posPartAux Λ f.nnrealPart := by
  simp [posPart, toRealPositiveLinear_apply, nnrealPart_neg_eq_zero_of_nonneg hf,
    coe_posPartNNReal_apply]

/-- Every `Λ g` with `0 ≤ g ≤ f` is bounded by the positive part of `Λ` at `f`. -/
theorem apply_le_posPart_apply {f g : C_c(X, ℝ)} (hg : 0 ≤ g) (hgf : g ≤ f) :
    Λ g ≤ posPart Λ hΛ f := by
  rw [posPart_apply_eq_posPartAux hΛ (hg.trans hgf)]
  have h := apply_le_posPartAux hΛ (f := f.nnrealPart) (g := g.nnrealPart) <|
    toReal_le_toReal_iff.1 <| by
      rwa [toReal_nnrealPart_of_nonneg hg, toReal_nnrealPart_of_nonneg (hg.trans hgf)]
  rwa [toReal_nnrealPart_of_nonneg hg] at h

/-- On a nonnegative `f`, the positive part of `Λ` is at most every upper bound of `Λ` on
`[0, f]`. -/
theorem posPart_apply_le {f : C_c(X, ℝ)} (hf : 0 ≤ f) {c : ℝ}
    (h : ∀ g : C_c(X, ℝ), 0 ≤ g → g ≤ f → Λ g ≤ c) : posPart Λ hΛ f ≤ c := by
  rw [posPart_apply_eq_posPartAux hΛ hf]
  exact posPartAux_le fun g hg => h _ toReal_nonneg
    ((toReal_le_toReal_iff.2 hg).trans_eq (toReal_nnrealPart_of_nonneg hf))

/-- On a nonnegative `f`, the positive part of `Λ` is the supremum of `Λ` over `[0, f]`. -/
theorem posPart_apply_of_nonneg {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    posPart Λ hΛ f = ⨆ g : Icc 0 f, Λ g := by
  have : Nonempty (Icc 0 f) := ⟨⟨0, le_rfl, hf⟩⟩
  refine le_antisymm (posPart_apply_le hΛ hf fun g hg hgf => ?_)
    (ciSup_le fun g => apply_le_posPart_apply hΛ g.2.1 g.2.2)
  exact le_ciSup (f := fun g : Icc 0 f => Λ g) (by simpa [image_eq_range] using hΛ f) ⟨g, hg, hgf⟩

/-- **Minimality of the positive part**: a positive functional dominating `Λ` on nonnegative
functions dominates the positive part of `Λ` there. -/
theorem posPart_apply_le_of_le (P : C_c(X, ℝ) →ₚ[ℝ] ℝ) (hP : ∀ f, 0 ≤ f → Λ f ≤ P f)
    {f : C_c(X, ℝ)} (hf : 0 ≤ f) : posPart Λ hΛ f ≤ P f :=
  posPart_apply_le hΛ hf fun g hg hgf => (hP g hg).trans (OrderHomClass.mono P hgf)

variable (Λ) in
/-- The **negative part** `posPart Λ hΛ - Λ` of an order-bounded linear functional `Λ` on
`C_c(X, ℝ)`, a positive linear functional. On a nonnegative `f` it is the supremum of `-Λ g`
over `0 ≤ g ≤ f` (`TauCeti.RealRMK.negPart_apply_of_nonneg`). -/
def negPart : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ ((posPart Λ hΛ).toLinearMap - Λ) fun f hf => by
    simpa using apply_le_posPart_apply hΛ hf le_rfl

/-- The negative part of `Λ` is its positive part minus `Λ`. -/
@[simp]
theorem negPart_apply (f : C_c(X, ℝ)) : negPart Λ hΛ f = posPart Λ hΛ f - Λ f :=
  (rfl)

/-- The **Jordan decomposition** `Λ = posPart Λ hΛ - negPart Λ hΛ`. -/
theorem posPart_sub_negPart_apply (f : C_c(X, ℝ)) :
    posPart Λ hΛ f - negPart Λ hΛ f = Λ f := by
  simp

/-- Every `-Λ g` with `0 ≤ g ≤ f` is bounded by the negative part of `Λ` at `f`. -/
theorem neg_apply_le_negPart_apply {f g : C_c(X, ℝ)} (hg : 0 ≤ g) (hgf : g ≤ f) :
    -Λ g ≤ negPart Λ hΛ f := by
  have := apply_le_posPart_apply hΛ (sub_nonneg.2 hgf) (sub_le_self f hg)
  rw [map_sub] at this
  rw [negPart_apply]
  linarith

/-- On a nonnegative `f`, the negative part of `Λ` is at most every upper bound of `-Λ` on
`[0, f]`. -/
theorem negPart_apply_le {f : C_c(X, ℝ)} (hf : 0 ≤ f) {c : ℝ}
    (h : ∀ g : C_c(X, ℝ), 0 ≤ g → g ≤ f → -Λ g ≤ c) : negPart Λ hΛ f ≤ c := by
  rw [negPart_apply, sub_le_iff_le_add]
  refine posPart_apply_le hΛ hf fun g hg hgf => ?_
  have := h (f - g) (sub_nonneg.2 hgf) (sub_le_self f hg)
  rw [map_sub] at this
  linarith

/-- On a nonnegative `f`, the negative part of `Λ` is the supremum of `-Λ` over `[0, f]`. -/
theorem negPart_apply_of_nonneg {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    negPart Λ hΛ f = ⨆ g : Icc 0 f, -Λ g := by
  have : Nonempty (Icc 0 f) := ⟨⟨0, le_rfl, hf⟩⟩
  have hbdd : BddAbove (range fun g : Icc 0 f => -Λ g) :=
    ⟨negPart Λ hΛ f, by
      rintro _ ⟨g, rfl⟩
      exact neg_apply_le_negPart_apply hΛ g.2.1 g.2.2⟩
  exact le_antisymm (negPart_apply_le hΛ hf fun g hg hgf =>
      le_ciSup (f := fun g : Icc 0 f => -Λ g) hbdd ⟨g, hg, hgf⟩)
    (ciSup_le fun g => neg_apply_le_negPart_apply hΛ g.2.1 g.2.2)

/-- **Minimality of the negative part**: a positive functional dominating `-Λ` on nonnegative
functions dominates the negative part of `Λ` there. -/
theorem negPart_apply_le_of_le (P : C_c(X, ℝ) →ₚ[ℝ] ℝ) (hP : ∀ f, 0 ≤ f → -Λ f ≤ P f)
    {f : C_c(X, ℝ)} (hf : 0 ≤ f) : negPart Λ hΛ f ≤ P f :=
  negPart_apply_le hΛ hf fun g hg hgf => (hP g hg).trans (OrderHomClass.mono P hgf)

section Measure

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The **Riesz–Markov–Kakutani representation theorem** for an order-bounded linear functional
`Λ` on `C_c(X, ℝ)`: `Λ` is integration against the Riesz measure of its positive part minus
integration against the Riesz measure of its negative part. -/
theorem integral_rieszMeasure_posPart_sub_integral_rieszMeasure_negPart (f : C_c(X, ℝ)) :
    ∫ x, f x ∂(_root_.RealRMK.rieszMeasure (posPart Λ hΛ)) -
      ∫ x, f x ∂(_root_.RealRMK.rieszMeasure (negPart Λ hΛ)) = Λ f := by
  rw [_root_.RealRMK.integral_rieszMeasure, _root_.RealRMK.integral_rieszMeasure,
    posPart_sub_negPart_apply]

variable (Λ) in
/-- A linear functional on `C_c(X, ℝ)` is the difference of the integrals against two regular
measures if and only if it is order bounded, that is, bounded above on every order interval
`[0, f]`. The two measures need not be finite. -/
theorem forall_bddAbove_image_Icc_iff_exists_regular :
    (∀ f : C_c(X, ℝ), BddAbove (Λ '' Icc 0 f)) ↔
      ∃ μ ν : Measure X, μ.Regular ∧ ν.Regular ∧
        ∀ f : C_c(X, ℝ), Λ f = ∫ x, f x ∂μ - ∫ x, f x ∂ν := by
  refine ⟨fun hΛ => ⟨_, _, inferInstance, inferInstance, fun f =>
    (integral_rieszMeasure_posPart_sub_integral_rieszMeasure_negPart hΛ f).symm⟩, ?_⟩
  rintro ⟨μ, ν, hμ, hν, hΛ⟩ f
  refine ⟨∫ x, f x ∂μ, ?_⟩
  rintro _ ⟨g, ⟨hg, hgf⟩, rfl⟩
  rw [hΛ, sub_le_iff_le_add]
  exact (integral_mono g.integrable f.integrable (le_def.1 hgf)).trans
    (le_add_of_nonneg_right (integral_nonneg (le_def.1 hg)))

end Measure

end TauCeti.RealRMK
