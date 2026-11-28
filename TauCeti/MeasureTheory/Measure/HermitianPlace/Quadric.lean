/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Bessel
public import TauCeti.MeasureTheory.Measure.HermitianPlace.Basic
public import TauCeti.Topology.Algebra.Star.SkewAdjoint
import TauCeti.MeasureTheory.Constructions.Polish.Units
import TauCeti.MeasureTheory.Integral.CompactlySupported
import TauCeti.MeasureTheory.Measure.Disintegration.Continuous

/-!
# Quadric measures and disintegrations at a place

Let `A` be a place (`TauCeti.HermitianPlace`) and `T` a matrix on `A^ι`. The form `h` of a
hyperbolic plane `(e, e')` plus `T` lives on `A^{e ⊔ ι ⊔ e'}`, with Gram matrix
`TauCeti.splitGram 1 T`, so `h(v, v) = star x * t + star t * x + w*Tw` for `v = xe + w + te'`.
For a skew element `β`, the **quadric measure** of `h(v, v) = δ⁻¹β` is the image of
`dt · dw · dν(a)` under the chart

`(t, w, a) ↦ ((star t)⁻¹ τ (δ⁻¹β - w*Tw) + t a) e + w + t e'`,

with `(star t)⁻¹ = 0` when `star t` is not a unit (`TauCeti.HermitianPlace.quadricMeasure`). For
a hermitian `T` the chart lands on the quadric whenever `t` is a unit, so the quadric measure is
carried by the quadric (`TauCeti.HermitianPlace.ae_quadricMeasure`).

A family `(l_β)` of measures on `A^ι` indexed by the skew elements **disintegrates** a measure `μ`
along a matrix `J` (`TauCeti.HermitianPlace.IsDisintegration`) if the integrals of compactly
supported continuous `f ≥ 0` against `l_β` are finite and continuous in `β`, and
`∫ f(x*Jx, x) dμ(x) = ∫∫ f(δ⁻¹β, x) dl_β(x) dν(β)` for measurable `f ≥ 0`. So `l_β` lives on the
quadric `x*Jx = δ⁻¹β`, and the continuity makes the family unique at every `β`
(`TauCeti.HermitianPlace.IsDisintegration.unique`).

## Main definitions

* `TauCeti.HermitianPlace.quadricChart`, `TauCeti.HermitianPlace.quadricMeasure`: the chart of a
  quadric of a hyperbolic plane plus `T`, and the quadric measure.
* `TauCeti.HermitianPlace.IsDisintegration`: disintegration of a measure along a form.

## Main results

* `TauCeti.HermitianPlace.star_quadricChart_dotProduct_splitGram_mulVec`: the chart lands on the
  quadric over units.
* `TauCeti.HermitianPlace.lintegral_quadricMeasure`, `TauCeti.HermitianPlace.ae_quadricMeasure`:
  integration against the quadric measure, and its support.
* `TauCeti.HermitianPlace.IsDisintegration.regular`: the fibres of a disintegration are regular.
* `TauCeti.HermitianPlace.IsDisintegration.unique`: a measure has at most one disintegration
  along a form.

## References

The definitions follow `New.Floors.Place.quadricMeasure` and `New.Floors.Place.IsDisintegration`
in the Lean project grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic, PBC), file `src/Lib/General/Measure/QuadricDisintegration.lean`.
-/

public section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal CompactlySupported

namespace TauCeti.HermitianPlace

variable {A : Type*} [CommRing A] [StarRing A] {ι : Type*} [Fintype ι]

/-! ### Quadric measures -/

variable [TopologicalSpace A] [MeasureSpace A] (P : HermitianPlace A)

/-- The chart `(t, w, a) ↦ ((star t)⁻¹ τ (δ⁻¹β - w*Tw) + t a) e + w + t e'` of the quadric
`h(v, v) = δ⁻¹β` of a hyperbolic plane `(e, e')` plus `T`, with `(star t)⁻¹ = 0` when `star t`
is not a unit. -/
noncomputable def quadricChart (T : Matrix ι ι A) (β : skewAdjoint A)
    (p : A × (ι → A) × skewAdjoint A) : SplitIndex 1 ι → A :=
  Sum.elim (fun _ ↦ Ring.inverse (star p.1) * P.τ * (↑P.δ⁻¹ * β - star p.2.1 ⬝ᵥ T *ᵥ p.2.1) +
    p.1 * p.2.2) (Sum.elim p.2.1 fun _ ↦ p.1)

variable (T : Matrix ι ι A) (β : skewAdjoint A) (p : A × (ι → A) × skewAdjoint A)

@[simp]
theorem quadricChart_inl (a : Fin 1) : P.quadricChart T β p (.inl a) =
    Ring.inverse (star p.1) * P.τ * (↑P.δ⁻¹ * β - star p.2.1 ⬝ᵥ T *ᵥ p.2.1) + p.1 * p.2.2 :=
  (rfl)

@[simp]
theorem quadricChart_inr_inl (i : ι) : P.quadricChart T β p (.inr (.inl i)) = p.2.1 i := (rfl)

@[simp]
theorem quadricChart_inr_inr (a : Fin 1) : P.quadricChart T β p (.inr (.inr a)) = p.1 := (rfl)

/-- The chart lands on the quadric `h(v, v) = δ⁻¹β` over the units `t`, for hermitian `T`. -/
theorem star_quadricChart_dotProduct_splitGram_mulVec {T : Matrix ι ι A} (hT : T.IsHermitian) {p}
    (hp : IsUnit p.1) :
    star (P.quadricChart T β p) ⬝ᵥ splitGram 1 T *ᵥ P.quadricChart T β p = ↑P.δ⁻¹ * β := by
  obtain ⟨t, w, a⟩ := p
  have hr : star t * Ring.inverse (star t) = 1 := Ring.mul_inverse_cancel _ hp.star
  have hr' : star (Ring.inverse (star t)) * t = 1 := by simpa [mul_comm] using congrArg star hr
  have hc : star (↑P.δ⁻¹ * (β : A)) = ↑P.δ⁻¹ * β := by
    simp [skewAdjoint.star_val_eq, mul_comm]
  have ha : star (a : A) = -a := skewAdjoint.star_val_eq
  rw [star_dotProduct_splitGram_mulVec]
  simp only [quadricChart_inl, quadricChart_inr_inl, quadricChart_inr_inr, star_add, star_mul,
    star_sub, hc, hT.star_dotProduct_mulVec_comm, ha]
  linear_combination (↑P.δ⁻¹ * (β : A) - star w ⬝ᵥ T *ᵥ w) *
    (P.τ_add_star + star P.τ * hr' + P.τ * hr)

/-- The **quadric measure** of `h(v, v) = δ⁻¹β` for a hyperbolic plane plus `T`: the image of
`dt · dw · dν(a)` under `TauCeti.HermitianPlace.quadricChart`. -/
noncomputable def quadricMeasure : Measure (SplitIndex 1 ι → A) :=
  ((volume : Measure A).prod ((volume : Measure (ι → A)).prod P.ν)).map (P.quadricChart T β)

/-- The quadric measure is the image of `dt · dw · dν(a)` under the chart. -/
theorem quadricMeasure_def : P.quadricMeasure T β =
    ((volume : Measure A).prod ((volume : Measure (ι → A)).prod P.ν)).map (P.quadricChart T β) :=
  (rfl)

section Measurability

variable [IsTopologicalRing A] [ContinuousStar A] [PolishSpace A] [BorelSpace A]

/-- The chart of a quadric is measurable. -/
theorem measurable_quadricChart : Measurable (P.quadricChart T β) := by
  have hr : Measurable fun p : A × (ι → A) × skewAdjoint A ↦ Ring.inverse (star p.1) :=
    Ring.measurable_inverse.comp (continuous_star.comp continuous_fst).measurable
  have hx : Continuous fun p : A × (ι → A) × skewAdjoint A ↦
      ↑P.δ⁻¹ * (β : A) - star p.2.1 ⬝ᵥ T *ᵥ p.2.1 := by fun_prop
  have ha : Continuous fun p : A × (ι → A) × skewAdjoint A ↦ p.1 * (p.2.2 : A) := by fun_prop
  refine measurable_pi_iff.2 fun i ↦ ?_
  rcases i with _ | i | _
  · exact ((hr.mul_const _).mul hx.measurable).add ha.measurable
  · exact ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).measurable
  · exact measurable_fst

/-- For hermitian `T`, the quadric measure is carried by the quadric `h(v, v) = δ⁻¹β`. -/
theorem ae_quadricMeasure {T : Matrix ι ι A} (hT : T.IsHermitian) :
    ∀ᵐ v ∂P.quadricMeasure T β, star v ⬝ᵥ splitGram 1 T *ᵥ v = ↑P.δ⁻¹ * β := by
  have hs : MeasurableSet {v : SplitIndex 1 ι → A | star v ⬝ᵥ splitGram 1 T *ᵥ v = ↑P.δ⁻¹ * β} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  rw [quadricMeasure_def, ae_map_iff (P.measurable_quadricChart T β).aemeasurable hs]
  exact (Measure.quasiMeasurePreserving_fst.ae P.ae_isUnit).mono fun p hp ↦
    P.star_quadricChart_dotProduct_splitGram_mulVec β hT hp

/-- The quadric measure of a measurable set is the measure of its preimage under the chart. -/
theorem quadricMeasure_apply {s : Set (SplitIndex 1 ι → A)} (hs : MeasurableSet s) :
    P.quadricMeasure T β s = ((volume : Measure A).prod ((volume : Measure (ι → A)).prod P.ν))
      (P.quadricChart T β ⁻¹' s) := by
  rw [quadricMeasure_def, Measure.map_apply (P.measurable_quadricChart T β) hs]

variable [LocallyCompactSpace A] [(volume : Measure A).IsAddHaarMeasure]

/-- Integration against the quadric measure: `∫ f dl = ∫∫∫ f(chart(t, w, a)) dν(a) dw dt`. -/
theorem lintegral_quadricMeasure {f : (SplitIndex 1 ι → A) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ v, f v ∂P.quadricMeasure T β =
      ∫⁻ t, ∫⁻ w, ∫⁻ a, f (P.quadricChart T β (t, w, a)) ∂P.ν ∂volume ∂volume := by
  have hfc : Measurable fun p ↦ f (P.quadricChart T β p) :=
    hf.comp (P.measurable_quadricChart T β)
  rw [quadricMeasure_def, lintegral_map hf (P.measurable_quadricChart T β),
    lintegral_prod _ hfc.aemeasurable]
  exact lintegral_congr fun t ↦ lintegral_prod _ (hfc.comp measurable_prodMk_left).aemeasurable

end Measurability

/-! ### Disintegrations along a form -/

/-- A family `(l_β)` of measures on `A^ι`, indexed by the skew elements `β`, **disintegrates** `μ`
along the matrix `J` if the integrals of every compactly supported continuous `f ≥ 0` against
`l_β` are finite and continuous in `β`, and `∫ f(x*Jx, x) dμ(x) = ∫∫ f(δ⁻¹β, x) dl_β(x) dν(β)`
for every measurable `f ≥ 0`. Then `l_β` lives on the quadric `x*Jx = δ⁻¹β`. -/
structure IsDisintegration (J : Matrix ι ι A) (μ : Measure (ι → A))
    (l : skewAdjoint A → Measure (ι → A)) : Prop where
  lintegral_lt_top (f : C_c(ι → A, ℝ≥0)) (β : skewAdjoint A) : ∫⁻ x, f x ∂l β < ∞
  continuous_lintegral (f : C_c(ι → A, ℝ≥0)) : Continuous fun β ↦ ∫⁻ x, f x ∂l β
  lintegral_eq (f : A × (ι → A) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f (star x ⬝ᵥ J *ᵥ x, x) ∂μ = ∫⁻ β, ∫⁻ x, f (↑P.δ⁻¹ * β, x) ∂l β ∂P.ν

/-- The fibres of a disintegration are regular: the integrals of compactly supported continuous
functions against them are finite, so they are finite on compact sets. -/
theorem IsDisintegration.regular [PolishSpace A] [BorelSpace A] [LocallyCompactSpace A]
    {J : Matrix ι ι A} {μ : Measure (ι → A)} {l : skewAdjoint A → Measure (ι → A)}
    (hl : P.IsDisintegration J μ l) (β : skewAdjoint A) : (l β).Regular :=
  have := isFiniteMeasureOnCompacts_of_lintegral_lt_top fun f ↦ hl.lintegral_lt_top f β
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-- **Disintegrations are unique**: two families that disintegrate the same measure along the
same form agree at every skew element. -/
theorem IsDisintegration.unique [IsTopologicalRing A] [ContinuousStar A] [PolishSpace A]
    [BorelSpace A] [LocallyCompactSpace A] {J : Matrix ι ι A} {μ : Measure (ι → A)}
    {l l' : skewAdjoint A → Measure (ι → A)} (hl : P.IsDisintegration J μ l)
    (hl' : P.IsDisintegration J μ l') : l = l' := by
  classical
  have := hl.regular
  have := hl'.regular
  -- The skew element `β` with `δ⁻¹β = c`, read off measurably from `c`.
  set g : A → A := fun c ↦ if ↑P.δ * c ∈ skewAdjoint A then ↑P.δ * c else 0
  have hg_mem (c : A) : g c ∈ skewAdjoint A := by
    simp only [g]
    split_ifs with h
    exacts [h, zero_mem _]
  set π : A → skewAdjoint A := fun c ↦ ⟨g c, hg_mem c⟩
  have hg : Measurable g := Measurable.ite
    (TauCeti.isClosed_skewAdjoint.measurableSet.preimage (measurable_const_mul _))
    (measurable_const_mul _) measurable_const
  have hπ : Measurable π := hg.subtype_mk
  have hπδ (β : skewAdjoint A) : π (↑P.δ⁻¹ * β) = β := by
    ext
    simp [π, g, ← mul_assoc]
  have key (m : skewAdjoint A → Measure (ι → A)) (hm : P.IsDisintegration J μ m)
      (F : skewAdjoint A × (ι → A) → ℝ≥0∞) (hF : Measurable F) :
      ∫⁻ x, F (π (star x ⬝ᵥ J *ᵥ x), x) ∂μ = ∫⁻ β, ∫⁻ x, F (β, x) ∂m β ∂P.ν := by
    simpa [hπδ] using hm.lintegral_eq (fun p ↦ F (π p.1, p.2)) (hF.comp (hπ.prodMap measurable_id))
  exact eq_of_continuous_lintegral_of_disintegration hl.continuous_lintegral
    hl'.continuous_lintegral (key l hl) (key l' hl')

end TauCeti.HermitianPlace
