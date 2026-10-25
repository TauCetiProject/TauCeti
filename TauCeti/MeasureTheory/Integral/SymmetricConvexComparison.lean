/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.PrekopaLeindler
-- Proof-only: the layer-cake formula in `ℝ≥0∞`.
import TauCeti.Analysis.SpecialFunctions.Pow.Integral

/-!
# Comparing measures on symmetric convex sets, and products

Vaaler's cube-slicing theorem rests on a comparison between two measures on symmetric convex
sets. If `γ` is the Gaussian measure `exp (-π ‖x‖ ^ 2) dx` on `ℝⁿ = ℝ^{n₁} × ⋯ × ℝ^{n_k}` and `B`
is a product of balls `B₁ × ⋯ × B_k` of volume one, then `γ A ≤ volume (A ∩ B)` for every
symmetric convex body `A` (Bombieri–Gubler, Lemma C.3.7). The case of a single ball is a
comparison along rays. The general case follows from it by induction on the number of factors,
and this file proves that induction step for arbitrary measures.

Say that `μ` is dominated by `ν` on symmetric convex sets if `μ s ≤ ν s` for every measurable
convex `s` with `-s = s`. By the layer-cake formula, `μ` is then dominated by `ν` on even
log-concave functions as well, since their superlevel sets are symmetric and convex. The
domination passes to products. For a symmetric convex `s ⊆ E × F`, integrate first over `F`: the
slice measures `x ↦ μ₂ (Prod.mk x ⁻¹' s)` form an even log-concave function by the
Prékopa–Leindler inequality for `μ₂`, so their `μ₁`-integral is at most their `ν₁`-integral.
After exchanging the order of integration, the slices `y ↦ ν₁ ((·, y) ⁻¹' s)` are even and
log-concave by the Prékopa–Leindler inequality for `ν₁`, and their `μ₂`-integral is at most their
`ν₂`-integral. Iterating gives the statement for finite products.

For the Gaussian-against-ball comparison, each factor measure is a log-concave density times
Lebesgue measure. These have the Prékopa–Leindler property by
`MeasureTheory.Measure.HasPrekopaLeindler.withDensity` and
`MeasureTheory.Measure.HasPrekopaLeindler.restrict`.

## Main results

* `TauCeti.lintegral_le_lintegral_of_forall_convex`: domination on symmetric convex sets implies
  domination on even log-concave functions.
* `MeasureTheory.MeasurePreserving.measure_le_of_forall_convex`: domination transfers along a
  linear map preserving both measures.
* `TauCeti.prod_apply_le_prod_apply_of_forall_convex`: domination on symmetric convex sets passes
  to product measures.
* `TauCeti.pi_apply_le_pi_apply_of_forall_convex`: the same for finite products.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Appendix C.3: Lemma C.3.4 (marginals of log-concave functions) and the proof of Lemma C.3.7.
* J. D. Vaaler, *A geometric inequality with applications to linear forms*, Pacific J. Math.
  **83** (1979), 543–553.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {E F : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
  [MeasurableSpace F] [AddCommGroup F] [Module ℝ F]

/-- **Domination on symmetric convex sets gives domination on even log-concave functions.** If
`μ s ≤ ν s` for every measurable convex set `s` with `-s = s`, then
`∫⁻ x, f x ∂μ ≤ ∫⁻ x, f x ∂ν` for every measurable, even, log-concave `f : E → ℝ≥0∞`. Each
superlevel set of `f` is symmetric and convex, and the layer-cake formula integrates their
measures. -/
theorem lintegral_le_lintegral_of_forall_convex {μ ν : Measure E}
    (h : ∀ s : Set E, MeasurableSet s → Convex ℝ s → (∀ x ∈ s, -x ∈ s) → μ s ≤ ν s)
    {f : E → ℝ≥0∞} (hf : Measurable f) (hlc : LogConcave f) (hfe : f.Even) :
    ∫⁻ x, f x ∂μ ≤ ∫⁻ x, f x ∂ν := by
  have hlayer (ρ : Measure E) :
      ∫⁻ x, f x ∂ρ = ∫⁻ t in Ioi 0, ρ {x | ENNReal.ofReal t < f x} := by
    simpa using lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul ρ hf.aemeasurable one_pos
  rw [hlayer μ, hlayer ν]
  exact lintegral_mono fun t ↦ h _ (measurableSet_lt measurable_const hf) (hlc.convex_gt _)
    fun x hx ↦ by simpa only [mem_ofPred_eq, hfe x] using hx

end TauCeti

namespace MeasureTheory.MeasurePreserving

variable {E F : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
  [MeasurableSpace F] [AddCommGroup F] [Module ℝ F]

/-- **Domination on symmetric convex sets transfers along linear maps.** If a linear map `L`
sends `μ` to `μ'` and `ν` to `ν'`, and `μ` is dominated by `ν` on symmetric convex sets, then so
is `μ'` by `ν'`: the preimage under `L` of a symmetric convex set is symmetric and convex. -/
theorem measure_le_of_forall_convex {μ ν : Measure E} {μ' ν' : Measure F} {L : E →ₗ[ℝ] F}
    (hμ : MeasurePreserving L μ μ') (hν : MeasurePreserving L ν ν')
    (h : ∀ s : Set E, MeasurableSet s → Convex ℝ s → (∀ x ∈ s, -x ∈ s) → μ s ≤ ν s)
    {s : Set F} (hs : MeasurableSet s) (hsc : Convex ℝ s) (hneg : ∀ x ∈ s, -x ∈ s) :
    μ' s ≤ ν' s := by
  rw [← hμ.measure_preimage hs.nullMeasurableSet, ← hν.measure_preimage hs.nullMeasurableSet]
  exact h _ (hμ.measurable hs) (hsc.linear_preimage L) fun x hx ↦ by
    simpa only [mem_preimage, map_neg] using hneg _ hx

end MeasureTheory.MeasurePreserving

namespace TauCeti

variable {E F : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
  [MeasurableSpace F] [AddCommGroup F] [Module ℝ F]

/-- **Domination on symmetric convex sets passes to products** (the induction step of
Bombieri–Gubler, Lemma C.3.7). Let `μ₁` be dominated by `ν₁` on symmetric convex subsets of `E`,
and `μ₂` by `ν₂` on symmetric convex subsets of `F`. Suppose that `ν₁` and `μ₂` are
negation-invariant and have the Prékopa–Leindler property at every weight. Then
`μ₁.prod μ₂ s ≤ ν₁.prod ν₂ s` for every measurable convex set `s ⊆ E × F` with `-s = s`.

Applied to the Gaussian measure against the uniform measure on a ball of volume one in each
factor, this reduces the comparison for a product of balls to the comparison for one ball. -/
theorem prod_apply_le_prod_apply_of_forall_convex [MeasurableNeg E] [MeasurableNeg F]
    {μ₁ ν₁ : Measure E} {μ₂ ν₂ : Measure F} [SFinite ν₁] [SFinite μ₂] [SFinite ν₂]
    [ν₁.IsNegInvariant] [μ₂.IsNegInvariant]
    (hν₁ : ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → ν₁.HasPrekopaLeindler θ)
    (hμ₂ : ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → μ₂.HasPrekopaLeindler θ)
    (h₁ : ∀ s : Set E, MeasurableSet s → Convex ℝ s → (∀ x ∈ s, -x ∈ s) → μ₁ s ≤ ν₁ s)
    (h₂ : ∀ s : Set F, MeasurableSet s → Convex ℝ s → (∀ y ∈ s, -y ∈ s) → μ₂ s ≤ ν₂ s)
    {s : Set (E × F)} (hs : MeasurableSet s) (hsc : Convex ℝ s) (hneg : ∀ p ∈ s, -p ∈ s) :
    μ₁.prod μ₂ s ≤ ν₁.prod ν₂ s := by
  have hmem (x : E) (y : F) : (-x, -y) ∈ s ↔ (x, y) ∈ s :=
    ⟨fun h ↦ by simpa using hneg _ h, fun h ↦ by simpa using hneg _ h⟩
  -- The slices of `s` along either factor have even measure.
  have hevenF (x : E) : μ₂ (Prod.mk (-x) ⁻¹' s) = μ₂ (Prod.mk x ⁻¹' s) := by
    rw [← Measure.measure_preimage_neg]
    congr 1 with y
    exact hmem x y
  have hevenE (y : F) : ν₁ ((·, -y) ⁻¹' s) = ν₁ ((·, y) ⁻¹' s) := by
    rw [← Measure.measure_preimage_neg]
    congr 1 with x
    exact hmem x y
  -- The slices along `E`, seen as slices of the swapped set.
  have hswap : Convex ℝ (Prod.swap ⁻¹' s : Set (F × E)) :=
    hsc.linear_preimage (LinearEquiv.prodComm ℝ F E).toLinearMap
  calc μ₁.prod μ₂ s = ∫⁻ x, μ₂ (Prod.mk x ⁻¹' s) ∂μ₁ := Measure.prod_apply hs
    _ ≤ ∫⁻ x, μ₂ (Prod.mk x ⁻¹' s) ∂ν₁ :=
      lintegral_le_lintegral_of_forall_convex h₁ (measurable_measure_prodMk_left hs)
        (hsc.logConcave_measure_preimage_prodMk hμ₂ hs) hevenF
    _ = ∫⁻ y, ν₁ ((·, y) ⁻¹' s) ∂μ₂ := by
      rw [← Measure.prod_apply hs, Measure.prod_apply_symm hs]
    _ ≤ ∫⁻ y, ν₁ ((·, y) ⁻¹' s) ∂ν₂ :=
      lintegral_le_lintegral_of_forall_convex h₂ (measurable_measure_prodMk_right hs)
        (hswap.logConcave_measure_preimage_prodMk hν₁ (hs.preimage measurable_swap)) hevenE
    _ = ν₁.prod ν₂ s := (Measure.prod_apply_symm hs).symm

/-- **Domination on symmetric convex sets passes to finite products** (Bombieri–Gubler, the
induction in the proof of Lemma C.3.7). Let `μ i` be dominated by `ν i` on symmetric convex
subsets of `α i` for each `i`, where all these measures are σ-finite, negation-invariant and have
the Prékopa–Leindler property at every weight. Then `Measure.pi μ s ≤ Measure.pi ν s` for every
measurable convex set `s ⊆ ∀ i, α i` with `-s = s`. -/
theorem pi_apply_le_pi_apply_of_forall_convex {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, AddCommGroup (α i)] [∀ i, Module ℝ (α i)]
    [∀ i, MeasurableNeg (α i)] {μ ν : ∀ i, Measure (α i)} [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] [∀ i, (μ i).IsNegInvariant] [∀ i, (ν i).IsNegInvariant]
    (hμ : ∀ i ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → (μ i).HasPrekopaLeindler θ)
    (hν : ∀ i ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → (ν i).HasPrekopaLeindler θ)
    (h : ∀ i (s : Set (α i)), MeasurableSet s → Convex ℝ s → (∀ x ∈ s, -x ∈ s) → μ i s ≤ ν i s)
    {s : Set (∀ i, α i)} (hs : MeasurableSet s) (hsc : Convex ℝ s) (hneg : ∀ x ∈ s, -x ∈ s) :
    Measure.pi μ s ≤ Measure.pi ν s := by
  -- First treat the index types `Fin n`, splitting off the zeroth coordinate inductively.
  have hfin : ∀ (n : ℕ) (α : Fin n → Type _) [∀ i, MeasurableSpace (α i)]
      [∀ i, AddCommGroup (α i)] [∀ i, Module ℝ (α i)] [∀ i, MeasurableNeg (α i)]
      (μ ν : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
      [∀ i, (μ i).IsNegInvariant] [∀ i, (ν i).IsNegInvariant],
      (∀ i ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → (μ i).HasPrekopaLeindler θ) →
      (∀ i ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 → (ν i).HasPrekopaLeindler θ) →
      (∀ i (s : Set (α i)), MeasurableSet s → Convex ℝ s → (∀ x ∈ s, -x ∈ s) →
        μ i s ≤ ν i s) →
      ∀ s : Set (∀ i, α i), MeasurableSet s → Convex ℝ s → (∀ x ∈ s, -x ∈ s) →
        Measure.pi μ s ≤ Measure.pi ν s := by
    intro n
    induction n with
    | zero =>
      intro α _ _ _ _ μ ν _ _ _ _ _ _ _ s _ _ _
      rw [Measure.pi_of_empty μ isEmptyElim, Measure.pi_of_empty ν isEmptyElim]
    | succ n ih =>
      intro α _ _ _ _ μ ν _ _ _ _ hμ hν h s hs hsc hneg
      -- `Fin.cons` is linear and identifies the product measures.
      have hcons (ρ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (ρ i)] :
          MeasurePreserving (Fin.consLinearEquiv ℝ α).toLinearMap
            ((ρ 0).prod (Measure.pi fun j ↦ ρ j.succ)) (Measure.pi ρ) := by
        have hL : ⇑(Fin.consLinearEquiv ℝ α).toLinearMap =
            ⇑(MeasurableEquiv.piFinSuccAbove α 0).symm := by
          -- At the index `0`, `Fin.insertNth` is `Fin.cons` by definition.
          ext p i
          cases i using Fin.cases <;> rfl
        rw [hL]
        exact (measurePreserving_piFinSuccAbove ρ 0).symm
      refine (hcons μ).measure_le_of_forall_convex (hcons ν) ?_ hs hsc hneg
      intro t ht htc htneg
      exact prod_apply_le_prod_apply_of_forall_convex (hν 0)
        (fun _ hθ₀ hθ₁ ↦ Measure.HasPrekopaLeindler.pi fun j ↦ hμ j.succ hθ₀ hθ₁) (h 0)
        (ih _ _ _ (fun j ↦ hμ j.succ) (fun j ↦ hν j.succ) fun j ↦ h j.succ) ht htc htneg
  -- Then reindex along `Fintype.equivFin ι`.
  let e := Fintype.equivFin ι
  have hcongr (ρ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (ρ i)] :
      MeasurePreserving (LinearEquiv.piCongrLeft ℝ α e.symm).toLinearMap
        (Measure.pi fun j ↦ ρ (e.symm j)) (Measure.pi ρ) :=
    measurePreserving_piCongrLeft ρ e.symm
  exact (hcongr μ).measure_le_of_forall_convex (hcongr ν)
    (hfin _ _ _ _ (fun j ↦ hμ _) (fun j ↦ hν _) fun j ↦ h _) hs hsc hneg

end TauCeti
