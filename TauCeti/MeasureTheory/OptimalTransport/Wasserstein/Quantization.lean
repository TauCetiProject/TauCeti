/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.Metric
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FiniteSupport
public import TauCeti.Topology.Compactification.OnePoint.Nhds
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow

/-!
# Best `N`-point quantizers

The `N`-point quantization error `TauCeti.wassersteinQuantizationError p N μ` is the infimum of
the Wasserstein distances from `μ` to the probability measures carried by at most `N` points. This
file reduces it to a problem about finite sets, and shows that on a proper space the infimum is
attained.

For a law `ν` carried by a set `s`, every coupling of `μ` and `ν` moves each point `x` at least as
far as `s`, so `W_p (μ, ν)` is at least the `L^p (μ)` seminorm of the distance function
`x ↦ infEDist x s`. When `s` is finite this bound is attained, by pushing `μ` forward along a
measurable nearest-point projection onto `s` (a Voronoi quantizer). Hence the quantization error is
the infimum, over nonempty sets `s` of at most `N` points, of `‖infEDist · s‖_{L^p (μ)}`.

On a proper pseudometric space, and for a finite exponent, this infimum over finite sets is a
minimum, for an arbitrary measure `μ`. The argument runs on the compact space of `N`-tuples of
points of the one-point compactification, where a coordinate at infinity contributes nothing to
the distance function. The `p`-th power of the objective is lower semicontinuous there, by Fatou's
lemma along neighbourhood filters, which are countably generated because the one-point
compactification of a proper space is first countable. A minimising tuple then gives a best set,
namely its finite coordinates. No rate of decay of the error is claimed, and the exponent
`p = ∞` is not treated.

## Main statements

* `TauCeti.eLpNorm_infEDist_le_wassersteinEDist` — the Wasserstein distance from `μ` to a law
  carried by `s` is at least the `L^p (μ)` seminorm of the distance to `s`;
* `TauCeti.exists_map_wassersteinEDist_eq_eLpNorm_infEDist` — for a nonempty finite set `s`, a
  measurable nearest-point projection onto `s` attains this bound;
* `TauCeti.wassersteinQuantizationError_eq_iInf_eLpNorm_infEDist` — the quantization error as an
  infimum over sets of at most `N` points;
* `TauCeti.exists_forall_eLpNorm_infEDist_le` — on a proper space and for a finite exponent, a
  best set of at most `N` points exists;
* `TauCeti.exists_map_wassersteinEDist_eq_wassersteinQuantizationError` and
  `TauCeti.exists_wassersteinEDist_eq_wassersteinQuantizationError` — the existence of a best
  `N`-point quantizer, as a Voronoi map and as a law carried by at most `N` points.

## References

* S. Graf and H. Luschgy, *Foundations of Quantization for Probability Distributions*, Lecture
  Notes in Mathematics 1730, Springer 2000, Chapter I, Lemma 3.4 for the reduction to finite
  sets and Theorem 4.12 for the existence of optimal quantizers.
* G. Pagès, *Introduction to vector quantization and its applications for numerics*,
  ESAIM Proc. Surveys 48 (2015), 29--79, §2.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace TauCeti

universe u

variable {X : Type u} {p : ℝ≥0∞} {N : ℕ}

section Voronoi

variable [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X] {μ ν : Measure X}

/-- **The distance to the carrier bounds the Wasserstein distance from below.** If `ν` is carried
by `s`, then under every coupling of `μ` and `ν` each point `x` is transported into `s`, so at
least the distance `infEDist x s`. Hence `W_p (μ, ν)` is at least the `L^p (μ)` seminorm of
`x ↦ infEDist x s`. -/
theorem eLpNorm_infEDist_le_wassersteinEDist {s : Set X} (hν : ∀ᵐ y ∂ν, y ∈ s) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ infEDist x s) p μ ≤ wassersteinEDist p μ ν := by
  refine le_wassersteinEDist fun π hπ ↦ ?_
  have hs : ∀ᵐ z ∂π, z.2 ∈ s := hπ.measurePreserving_snd.quasiMeasurePreserving.ae hν
  have hm : AEStronglyMeasurable (fun x ↦ infEDist x s) μ :=
    continuous_infEDist.measurable.aestronglyMeasurable
  rw [← eLpNorm_comp_measurePreserving hm hπ.measurePreserving_fst]
  exact eLpNorm_mono_enorm_ae (hm.comp_measurePreserving hπ.measurePreserving_fst)
    (hs.mono fun z hz ↦ by simpa using infEDist_le_edist_of_mem hz)

variable [MeasurableSingletonClass X]

/-- **The Voronoi quantizer.** For a nonempty finite set `s`, pushing `μ` forward along a
measurable nearest-point projection `T` onto `s` gives the law carried by `s` closest to `μ`: its
Wasserstein distance to `μ` is exactly the `L^p (μ)` seminorm of the distance to `s`, the lower
bound `TauCeti.eLpNorm_infEDist_le_wassersteinEDist` for every law carried by `s`. -/
theorem exists_map_wassersteinEDist_eq_eLpNorm_infEDist
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) {s : Finset X} (hs : s.Nonempty)
    (μ : Measure X) (p : ℝ≥0∞) :
    ∃ T : X → X, Measurable T ∧ (∀ x, T x ∈ s) ∧
      wassersteinEDist p μ (μ.map T) = eLpNorm (fun x ↦ infEDist x s) p μ := by
  obtain ⟨T, hT, hTs, hTd⟩ := exists_measurable_edist_eq_infEDist hs
  refine ⟨T, hT, hTs, le_antisymm ?_ (eLpNorm_infEDist_le_wassersteinEDist ?_ p)⟩
  · simpa only [hTd] using wassersteinEDist_map_le hd hT.aemeasurable p
  · exact (ae_map_iff hT.aemeasurable s.measurableSet).2 (.of_forall hTs)

/-- **The quantization error as a problem on finite sets.** For a probability measure `μ`, the
`N`-point quantization error is the infimum, over the nonempty sets `s` of at most `N` points, of
the `L^p (μ)` seminorm of the distance to `s`. -/
theorem wassersteinQuantizationError_eq_iInf_eLpNorm_infEDist
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) [IsProbabilityMeasure μ] (p : ℝ≥0∞)
    (N : ℕ) :
    wassersteinQuantizationError p N μ =
      ⨅ (s : Finset X) (_ : s.Nonempty) (_ : s.card ≤ N),
        eLpNorm (fun x ↦ infEDist x s) p μ := by
  refine le_antisymm (le_iInf₂ fun s hs ↦ le_iInf fun hsN ↦ ?_)
    (le_wassersteinQuantizationError fun ν hν hcarrier ↦ ?_)
  · obtain ⟨T, hT, hTs, hTeq⟩ := exists_map_wassersteinEDist_eq_eLpNorm_infEDist hd hs μ p
    refine (wassersteinQuantizationError_le inferInstance ⟨s, hsN, mem_ae_iff.1 ?_⟩).trans hTeq.le
    exact (ae_map_iff hT.aemeasurable s.measurableSet).2 (.of_forall hTs)
  · obtain ⟨s, hsN, hνs⟩ := hcarrier
    have hs : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp at hνs
    exact (iInf₂_le s hs).trans ((iInf_le _ hsN).trans
      (eLpNorm_infEDist_le_wassersteinEDist (mem_ae_iff.2 hνs) p))

end Voronoi

section Existence

/-! ### Existence on a proper space

A tuple `b : Fin N → OnePoint X` stands for the finite set of its coordinates that lie in `X`;
coordinates at infinity are discarded. The distance from `x` to that set is the minimum over `i`
of the extended distance from `x` to `b i`, with value `⊤` at infinity, and on a proper space this
extended distance is continuous on the one-point compactification. -/

open scoped Classical in
/-- The finite set of the coordinates of a tuple of points of the one-point compactification that
lie in `X`. -/
private def finitePart (b : Fin N → OnePoint X) : Finset X :=
  (Finset.univ.image b).preimage (↑) OnePoint.coe_injective.injOn

private theorem mem_finitePart {b : Fin N → OnePoint X} {y : X} :
    y ∈ finitePart b ↔ ∃ i, b i = ↑y := by
  simp [finitePart]

private theorem card_finitePart_le (b : Fin N → OnePoint X) : (finitePart b).card ≤ N := by
  classical
  calc (finitePart b).card ≤ (Finset.univ.image b).card :=
        Finset.card_le_card_of_injOn (↑) (fun y hy ↦ by
          obtain ⟨i, hi⟩ := mem_finitePart.1 hy
          simp [← hi]) OnePoint.coe_injective.injOn
    _ ≤ N := Finset.card_image_le.trans (by simp)

/-- Every set of at most `N` points is the finite part of some tuple: list its points and fill the
remaining coordinates with the point at infinity. -/
private theorem exists_finitePart_eq {s : Finset X} (hs : s.card ≤ N) :
    ∃ b : Fin N → OnePoint X, finitePart b = s := by
  refine ⟨fun i ↦
    if h : (i : ℕ) < s.card then ↑(s.equivFin.symm ⟨i, h⟩ : X) else OnePoint.infty, ?_⟩
  ext y
  rw [mem_finitePart]
  constructor
  · rintro ⟨i, hi⟩
    split_ifs at hi with h
    · rw [← OnePoint.coe_injective hi]
      exact (s.equivFin.symm ⟨i, h⟩).2
    · exact absurd hi.symm (OnePoint.coe_ne_infty y)
  · intro hy
    refine ⟨⟨s.equivFin ⟨y, hy⟩, (s.equivFin ⟨y, hy⟩).2.trans_le hs⟩, ?_⟩
    simp

variable [PseudoMetricSpace X]

private theorem infEDist_finitePart (x : X) (b : Fin N → OnePoint X) :
    infEDist x (finitePart b) = Finset.univ.inf fun i ↦ (b i).elim ⊤ (edist x) := by
  refine le_antisymm (Finset.le_inf fun i _ ↦ ?_) (le_infEDist.2 fun y hy ↦ ?_)
  · induction hi : b i using OnePoint.rec with
    | infty => exact le_top
    | coe y => exact infEDist_le_edist_of_mem (mem_finitePart.2 ⟨i, hi⟩)
  · obtain ⟨i, hi⟩ := mem_finitePart.1 hy
    exact Finset.inf_le_of_le (Finset.mem_univ i) (by simp [hi])

variable [ProperSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- On a proper space, the integral of a power of the distance to the finite part of a tuple is
lower semicontinuous in the tuple. -/
private theorem lowerSemicontinuous_lintegral_infEDist_finitePart (μ : Measure X) (r : ℝ) :
    LowerSemicontinuous fun b : Fin N → OnePoint X ↦ ∫⁻ x, infEDist x (finitePart b) ^ r ∂μ := by
  refine lowerSemicontinuous_iff_le_liminf.2 fun b ↦ ?_
  have hcont (x : X) : Continuous fun b' : Fin N → OnePoint X ↦ infEDist x (finitePart b') ^ r := by
    simp_rw [infEDist_finitePart]
    exact ENNReal.continuous_rpow_const.comp <| Continuous.finset_inf_apply fun i _ ↦
      (continuous_elim_edist x).comp (continuous_apply i)
  calc ∫⁻ x, infEDist x (finitePart b) ^ r ∂μ
      = ∫⁻ x, liminf (fun b' ↦ infEDist x (finitePart b') ^ r) (𝓝 b) ∂μ :=
        lintegral_congr fun x ↦ ((hcont x).tendsto b).liminf_eq.symm
    _ ≤ _ := lintegral_liminf_le fun b' ↦
        (ENNReal.continuous_rpow_const.comp continuous_infEDist).measurable

/-- **Existence of a best set of at most `N` points.** On a proper pseudometric space, for a finite
exponent `p`, every measure `μ` and `N ≠ 0`, some nonempty set `s` of at most `N` points
minimises the `L^p (μ)` seminorm of the distance to `s` among all such sets. The measure need not
be finite, nor have a finite moment: if every set gives the value `⊤`, every set is a minimiser. -/
theorem exists_forall_eLpNorm_infEDist_le [Nonempty X] (hp_top : p ≠ ∞) (hN : N ≠ 0)
    (μ : Measure X) :
    ∃ s : Finset X, s.Nonempty ∧ s.card ≤ N ∧ ∀ t : Finset X, t.Nonempty → t.card ≤ N →
      eLpNorm (fun x ↦ infEDist x s) p μ ≤ eLpNorm (fun x ↦ infEDist x t) p μ := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hx₀N : ({x₀} : Finset X).card ≤ N := by simpa using Nat.one_le_iff_ne_zero.2 hN
  rcases eq_or_ne p 0 with rfl | hp0
  · exact ⟨{x₀}, Finset.singleton_nonempty _, hx₀N, fun t _ _ ↦
      (eLpNorm_exponent_zero continuous_infEDist.measurable.aestronglyMeasurable).trans_le
        zero_le⟩
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  -- the `p`-th power of the objective, on the compact space of tuples, attains its minimum
  set G : (Fin N → OnePoint X) → ℝ≥0∞ :=
    fun b ↦ ∫⁻ x, infEDist x (finitePart b) ^ p.toReal ∂μ with hG_def
  obtain ⟨b, -, hb⟩ :=
    ((lowerSemicontinuous_lintegral_infEDist_finitePart μ p.toReal).lowerSemicontinuousOn
      univ).exists_isMinOn univ_nonempty isCompact_univ
  -- a minimising tuple with a coordinate in `X`: if all coordinates of `b` are at infinity, then
  -- `G b = ∫⁻ ⊤` and every tuple is a minimiser
  obtain ⟨b₀, hb₀ne, hb₀⟩ : ∃ b₀, (finitePart b₀).Nonempty ∧ ∀ b', G b₀ ≤ G b' := by
    by_cases hne : (finitePart b).Nonempty
    · exact ⟨b, hne, fun b' ↦ hb (mem_univ b')⟩
    · obtain ⟨b₀, hb₀⟩ := exists_finitePart_eq hx₀N
      refine ⟨b₀, hb₀ ▸ Finset.singleton_nonempty x₀, fun b' ↦ le_trans ?_ (hb (mem_univ b'))⟩
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp only [hG_def, hne, Finset.coe_empty, infEDist_empty, ENNReal.top_rpow_of_pos hr]
      exact lintegral_mono fun _ ↦ le_top
  refine ⟨finitePart b₀, hb₀ne, card_finitePart_le b₀, fun t _ ht ↦ ?_⟩
  obtain ⟨b', rfl⟩ := exists_finitePart_eq ht
  refine (ENNReal.rpow_le_rpow_iff hr).1 ?_
  rw [eLpNorm_rpow_eq_lintegral hp0 hp_top continuous_infEDist.measurable.aemeasurable,
    eLpNorm_rpow_eq_lintegral hp0 hp_top continuous_infEDist.measurable.aemeasurable]
  exact hb₀ b'

variable [MeasurableSingletonClass X]

/-- **Existence of a best `N`-point quantizer.** On a proper pseudometric space with measurable
singletons, for a finite exponent `p`, a probability measure `μ` and `N ≠ 0`, the `N`-point
quantization error is attained by the pushforward of `μ` along a measurable map with values in
a set of at most `N` points, namely a nearest-point projection onto a best such set. -/
theorem exists_map_wassersteinEDist_eq_wassersteinQuantizationError (hp_top : p ≠ ∞)
    (hN : N ≠ 0) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃ (s : Finset X) (T : X → X), s.card ≤ N ∧ Measurable T ∧ (∀ x, T x ∈ s) ∧
      wassersteinEDist p μ (μ.map T) = wassersteinQuantizationError p N μ := by
  have : Nonempty X := nonempty_of_isProbabilityMeasure μ
  obtain ⟨s, hs, hsN, hmin⟩ := exists_forall_eLpNorm_infEDist_le hp_top hN μ
  obtain ⟨T, hT, hTs, hTeq⟩ :=
    exists_map_wassersteinEDist_eq_eLpNorm_infEDist measurable_edist hs μ p
  refine ⟨s, T, hsN, hT, hTs, hTeq.trans ?_⟩
  rw [wassersteinQuantizationError_eq_iInf_eLpNorm_infEDist measurable_edist]
  exact le_antisymm (le_iInf₂ fun t ht ↦ le_iInf fun htN ↦ hmin t ht htN)
    (iInf₂_le_of_le s hs (iInf_le _ hsN))

/-- **The quantization error is attained.** On a proper pseudometric space with measurable
singletons, for a finite exponent `p`, a probability measure `μ` and `N ≠ 0`, some probability
measure carried by at most `N` points is at Wasserstein distance from `μ` exactly the `N`-point
quantization error. -/
theorem exists_wassersteinEDist_eq_wassersteinQuantizationError (hp_top : p ≠ ∞)
    (hN : N ≠ 0) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧
      (∃ s : Finset X, s.card ≤ N ∧ ν ((s : Set X)ᶜ) = 0) ∧
        wassersteinEDist p μ ν = wassersteinQuantizationError p N μ := by
  obtain ⟨s, T, hsN, hT, hTs, hTeq⟩ :=
    exists_map_wassersteinEDist_eq_wassersteinQuantizationError hp_top hN μ
  refine ⟨μ.map T, inferInstance, ⟨s, hsN, mem_ae_iff.1 ?_⟩, hTeq⟩
  exact (ae_map_iff hT.aemeasurable s.measurableSet).2 (.of_forall hTs)

end Existence

end TauCeti
