/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
public import TauCeti.Analysis.Sobolev.W1p.SobolevEmbedding
import TauCeti.Analysis.InnerProductSpace.OfLinearIsometry
import TauCeti.Analysis.Normed.Module.DiamFrontier
import TauCeti.Analysis.Sobolev.W1p.AddHaar
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The Sobolev embedding on bounded Lipschitz domains

For a bounded Lipschitz domain `Ω ⊆ ℝ × E` of dimension `n`, an exponent `1 ≤ p < n` and the
Sobolev conjugate `p⋆ = np/(n - p)`, so that `1/p⋆ + 1/n = 1/p`, the inclusion
`W^{1,p}(Ω) → L^{p⋆}(Ω)` is a continuous linear map, and so `‖u‖_{L^q(Ω)} ≤ C ‖u‖_{W^{1,p}(Ω)}`
for every `q ≤ p⋆`. Unlike `TauCeti.W1p0.sobolevEmbeddingL`, this concerns the whole Sobolev
space, with no vanishing boundary values; unlike the interior form
`TauCeti.W1p.exists_sobolevEmbeddingL_of_isCompact_closure`, the estimate reaches the boundary.

The boundary regularity enters only through the extension operator
`TauCeti.W1p.exists_extensionL_of_isLipschitzDomainWith`: the inclusion factors as extension to
`W^{1,p}(ℝ × E)`, the whole-space embedding `TauCeti.W1p.sobolevEmbeddingTopL`, and restriction
to `Ω`. Some regularity of `∂Ω` is genuinely needed: on a bounded domain with a sufficiently
sharp outward cusp, `W^{1,p}(Ω)` is not contained in `L^{p⋆}(Ω)`.

The same estimates hold on a bounded Lipschitz domain `Ω` of a finite-dimensional real inner
product space `F`, such as `EuclideanSpace ℝ (Fin n)`, in the sense of the intrinsic predicate
`Set.IsLipschitzDomain`, and for every additive Haar measure `μ` on `F`. A boundary chart is an
affine isometry `g : F ≃ᵃⁱ[ℝ] ℝ × E` carrying `Ω` onto a bounded Lipschitz domain of the model
space (`Set.IsLipschitzDomain.exists_isLipschitzDomainWith_image`). Precomposition with `g⁻¹`
(`TauCeti.W1p.compAffineIsometryEquivL`) does not increase the `W^{1,p}` norm and preserves `Lˢ`
norms (`TauCeti.W1p.eLpNorm_value_le_of_affineIsometryEquiv`), and `μ` is a constant multiple of
Lebesgue measure, whose Sobolev space is the same
(`TauCeti.W1p.exists_eLpNorm_value_le_of_isAddHaarMeasure`).

## Main declarations

* `TauCeti.W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith`: the embedding
  `W^{1,p}(Ω) →L[ℝ] L^{p⋆}(Ω)`.
* `TauCeti.W1p.exists_eLpNorm_value_le_of_isLipschitzDomainWith`: the estimate
  `‖u‖_{L^q(Ω)} ≤ C ‖u‖_{W^{1,p}(Ω)}` for `q ≤ p⋆`.
* `TauCeti.W1p.memLp_value_of_isLipschitzDomainWith`: every `u ∈ W^{1,p}(Ω)` lies in `L^q(Ω)`
  for `q ≤ p⋆`.
* `TauCeti.W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith`: the
  estimate `‖u‖_{L^s(Ω)} ≤ C ‖u‖_{W^{1,p}(Ω)}` for every finite `s` with `1/p - 1/s < 1/n`,
  including `p ≥ n`, where there is no Sobolev conjugate.
* `TauCeti.W1p.exists_sobolevEmbeddingL_of_isLipschitzDomain`,
  `TauCeti.W1p.exists_eLpNorm_value_le_of_isLipschitzDomain`,
  `TauCeti.W1p.memLp_value_of_isLipschitzDomain` and
  `TauCeti.W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomain`: the same on
  bounded Lipschitz domains of a Euclidean space, for every additive Haar measure.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.6.1, Theorem 2.
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12, Part I, Case B.
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {p pstar : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The Sobolev embedding on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded Lipschitz
domain of dimension `n`, `1 ≤ p` and `1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, then inclusion is a
continuous linear map `W^{1,p}(Ω) → L^{p⋆}(Ω)`. -/
theorem W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ S : W1p volume Ω p →L[ℝ] Lp ℝ pstar (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      ∀ u, S u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨T, hT, _⟩ := W1p.exists_extensionL_of_isLipschitzDomainWith (p := p) hΩ hb
  have hle : volume.restrict (Ω : Set (WithLp 2 (ℝ × E))) ≤
      (1 : ℝ≥0∞) • volume.restrict ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))) := by
    rw [one_smul]
    exact Measure.restrict_mono_set volume (by simp)
  refine ⟨(Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top hle).comp
    ((W1p.sobolevEmbeddingTopL hpstar hexp).comp T), fun u => ?_⟩
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top hle
      (W1p.sobolevEmbeddingTopL hpstar hexp (T u)),
    ae_restrict_of_ae_restrict_of_subset (by simp)
      (W1p.coeFn_sobolevEmbeddingTopL hpstar hexp (T u)),
    W1p.value_ae_eq_of_restrictL_comp_eq_id le_top hT u] with x h1 h2 h3
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1, h2, h3]

/-- **The Sobolev inequality on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded Lipschitz
domain of dimension `n`, `1 ≤ p` and `1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, then for every `q ≤ p⋆`
there is a constant `C` with `‖u‖_{L^q(Ω)} ≤ C ‖u‖_{W^{1,p}(Ω)}` for all `u ∈ W^{1,p}(Ω)`. -/
theorem W1p.exists_eLpNorm_value_le_of_isLipschitzDomainWith (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {q : ℝ≥0∞} (hq : q ≤ pstar) :
    ∃ C : ℝ≥0, ∀ u : W1p volume Ω p,
      eLpNorm (W1p.value u) q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) ≤ C * ‖u‖ₑ := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨S, hS⟩ := W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith hpstar hexp hΩ hb
  exact W1p.exists_eLpNorm_value_le_of_ae_eq hb.measure_lt_top.ne hq S hS

/-- **Integrability on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded Lipschitz domain
of dimension `n`, every `u ∈ W^{1,p}(Ω)` lies in `L^q(Ω)` for every `q ≤ p⋆`, where
`1/p⋆ + 1/n = 1/p` and `p⋆ < ∞`. -/
theorem W1p.memLp_value_of_isLipschitzDomainWith (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {q : ℝ≥0∞} (hq : q ≤ pstar)
    (u : W1p volume Ω p) :
    MemLp (W1p.value u) q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) := by
  obtain ⟨C, hC⟩ := W1p.exists_eLpNorm_value_le_of_isLipschitzDomainWith hpstar hexp hΩ hb hq
  have hfin : C * ‖u‖ₑ < ∞ := by finiteness
  exact (hC u).trans_lt hfin

/-- **The Sobolev inequality on bounded Lipschitz domains for subcritical exponents.** If
`Ω ⊆ ℝ × E` is a bounded Lipschitz domain of dimension `n` and `1 ≤ p`, then for every finite `s`
with `1/p - 1/s < 1/n` there is a constant `C` with `‖u‖_{L^s(Ω)} ≤ C ‖u‖_{W^{1,p}(Ω)}` for all
`u ∈ W^{1,p}(Ω)`. For `p < n` this is every `s < p⋆`; for `p ≥ n` it is every finite `s`. -/
theorem W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith {s : ℝ≥0∞}
    (hs : s ≠ ∞) (hps : p⁻¹ < s⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ C : ℝ≥0, ∀ u : W1p volume Ω p,
      eLpNorm (W1p.value u) s (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) ≤ C * ‖u‖ₑ := by
  rcases le_total s p with hsp | hps'
  · -- Below `p`, Hölder's inequality on the set `Ω` of finite measure suffices.
    exact W1p.exists_eLpNorm_value_le_of_ae_eq hb.measure_lt_top.ne hsp W1p.valueL
      fun u => by rw [W1p.valueL_apply]
  -- Above `p`, extend to the whole space and use the interior estimate on `Ω`.
  have hC : ∃ C : ℝ≥0, ∀ v : W1p volume (⊤ : Opens (WithLp 2 (ℝ × E))) p,
      eLpNorm (W1p.value v) s (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) ≤ C * ‖v‖ₑ := by
    have hn : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Module.finrank_pos.ne'
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
    have hs0 : s ≠ 0 := (zero_lt_one.trans_le ((Fact.out : (1 : ℝ≥0∞) ≤ p).trans hps')).ne'
    have hgap : p.toReal⁻¹ - s.toReal⁻¹ < (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ)⁻¹ := by
      have h := (ENNReal.toReal_lt_toReal (ENNReal.inv_ne_top.2 hp0)
        (ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.2 hs0, ENNReal.inv_ne_top.2 hn⟩)).2 hps
      rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 hs0) (ENNReal.inv_ne_top.2 hn)] at h
      simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast] at h
      linarith
    have hp : p ≠ ∞ := ne_top_of_le_ne_top hs hps'
    lift p to ℝ≥0 using hp
    lift s to ℝ≥0 using hs
    rw [ENNReal.coe_toReal, ENNReal.coe_toReal] at hgap
    exact W1p.exists_eLpNorm_value_le_of_subcritical_gain (Ω := ⊤)
      (by exact_mod_cast hps') hgap hb.isCompact_closure (subset_univ _)
  obtain ⟨C, hC⟩ := hC
  obtain ⟨T, hT, _⟩ := W1p.exists_extensionL_of_isLipschitzDomainWith (p := p) hΩ hb
  refine ⟨(C * ‖T‖ₑ).toNNReal, fun u => ?_⟩
  have hu : W1p.restrictL le_top (T u) = u := by
    simpa using congrArg (· u) hT
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.coe_ne_top eNorm_ne_top)]
  calc eLpNorm (W1p.value u) s (volume.restrict (Ω : Set (WithLp 2 (ℝ × E))))
      = eLpNorm (W1p.value (W1p.restrictL le_top (T u))) s
          (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) := by rw [hu]
    _ = eLpNorm (W1p.value (T u)) s (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) :=
        eLpNorm_congr_ae (W1p.value_restrictL_ae le_top (T u))
    _ ≤ C * ‖T u‖ₑ := hC (T u)
    _ ≤ C * (‖T‖ₑ * ‖u‖ₑ) := by gcongr; exact T.le_opENorm u
    _ = C * ‖T‖ₑ * ‖u‖ₑ := (mul_assoc _ _ _).symm

end ModelSpace

/-! ### Bounded Lipschitz domains of a Euclidean space -/

section Intrinsic

universe u

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {Ω : Opens F} {mu : Measure F} [mu.IsAddHaarMeasure]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {p pstar : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An `Lˢ` bound on the values that holds on every bounded Lipschitz domain of every model space
`ℝ × E₀` holds, for Lebesgue measure, on a bounded Lipschitz domain `Ω` of `F`: a boundary chart
carries `Ω` onto such a domain, and the tangential model `E` inherits an inner product from `F`. -/
private theorem exists_eLpNorm_value_le_volume_of_isLipschitzDomain [Nontrivial F]
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) {s : ℝ≥0∞}
    (H : ∀ (E₀ : Type u) [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [FiniteDimensional ℝ E₀]
      [MeasurableSpace E₀] [BorelSpace E₀] (W : Opens (WithLp 2 (ℝ × E₀))) (L : ℝ≥0),
      (W : Set (WithLp 2 (ℝ × E₀))).IsLipschitzDomainWith L →
      IsBounded (W : Set (WithLp 2 (ℝ × E₀))) → finrank ℝ (WithLp 2 (ℝ × E₀)) = finrank ℝ F →
      ∃ C : ℝ≥0, ∀ v : W1p volume W p,
        eLpNorm (W1p.value v) s (volume.restrict (W : Set (WithLp 2 (ℝ × E₀)))) ≤ C * ‖v‖ₑ) :
    ∃ C : ℝ≥0, ∀ u : W1p volume Ω p,
      eLpNorm (W1p.value u) s (volume.restrict (Ω : Set F)) ≤ C * ‖u‖ₑ := by
  rcases (frontier (Ω : Set F)).eq_empty_or_nonempty with hfr | hne
  · -- A bounded open set with empty frontier is empty.
    exact ⟨0, fun u => by simp [hb.eq_empty_of_frontier_eq_empty hfr]⟩
  obtain ⟨g, L, hL⟩ := hΩ.exists_isLipschitzDomainWith_image hb hne
  let e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E) := g.linearIsometryEquiv
  let _ : InnerProductSpace ℝ E := .ofLinearIsometry e.symmInr
  have _ : FiniteDimensional ℝ E := e.finiteDimensional_snd
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  obtain ⟨C, hC⟩ := H E ⟨g '' (Ω : Set F), ((isLipschitzDomainWith_iff _ _).1 hL).1⟩ L hL
    (g.lipschitzWith.isBounded_image hb) e.toLinearEquiv.finrank_eq.symm
  exact ⟨C, W1p.eLpNorm_value_le_of_affineIsometryEquiv g (g.toHomeomorph.preimage_image _).symm hC⟩

/-- **The Sobolev inequality on bounded Lipschitz domains of a Euclidean space.** Let `Ω` be a
bounded Lipschitz domain in a finite-dimensional real inner product space `F` of dimension `n`,
such as `EuclideanSpace ℝ (Fin n)`, and let `μ` be an additive Haar measure on `F`. If `1 ≤ p` and
`1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, then for every `q ≤ p⋆` there is a constant `C` with
`‖u‖_{L^q(Ω)} ≤ C ‖u‖_{W^{1,p}(Ω)}` for all `u ∈ W^{1,p}(Ω)`. -/
theorem W1p.exists_eLpNorm_value_le_of_isLipschitzDomain (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ F : ℝ≥0∞)⁻¹ = p⁻¹) (hΩ : (Ω : Set F).IsLipschitzDomain E)
    (hb : IsBounded (Ω : Set F)) {q : ℝ≥0∞} (hq : q ≤ pstar) :
    ∃ C : ℝ≥0, ∀ u : W1p mu Ω p,
      eLpNorm (W1p.value u) q (mu.restrict (Ω : Set F)) ≤ C * ‖u‖ₑ := by
  -- The exponent relation forces `n ≥ 1`, since `p ≠ 0`.
  have : Nontrivial F := by
    refine Module.nontrivial_of_finrank_pos (R := ℝ) (Nat.pos_of_ne_zero fun h => ?_)
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
    simp only [h, CharP.cast_eq_zero, ENNReal.inv_zero, add_top] at hexp
    exact hp0 (ENNReal.inv_eq_top.1 hexp.symm)
  exact W1p.exists_eLpNorm_value_le_of_isAddHaarMeasure volume mu
    (exists_eLpNorm_value_le_volume_of_isLipschitzDomain hΩ hb fun _ _ _ _ _ _ _ _ hL hbW hn =>
      W1p.exists_eLpNorm_value_le_of_isLipschitzDomainWith hpstar (by rwa [hn]) hL hbW hq)

/-- **The Sobolev embedding on bounded Lipschitz domains of a Euclidean space.** Let `Ω` be a
bounded Lipschitz domain in a finite-dimensional real inner product space `F` of dimension `n` and
let `μ` be an additive Haar measure on `F`. If `1 ≤ p` and `1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, then
inclusion is a continuous linear map `W^{1,p}(Ω) → L^{p⋆}(Ω)`. -/
theorem W1p.exists_sobolevEmbeddingL_of_isLipschitzDomain (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ F : ℝ≥0∞)⁻¹ = p⁻¹) (hΩ : (Ω : Set F).IsLipschitzDomain E)
    (hb : IsBounded (Ω : Set F)) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ S : W1p mu Ω p →L[ℝ] Lp ℝ pstar (mu.restrict (Ω : Set F)),
      ∀ u, S u =ᵐ[mu.restrict (Ω : Set F)] W1p.value u :=
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  W1p.exists_lpEmbeddingL_of_eLpNorm_value_le subset_rfl
    (W1p.exists_eLpNorm_value_le_of_isLipschitzDomain hpstar hexp hΩ hb le_rfl)

/-- **Integrability on bounded Lipschitz domains of a Euclidean space.** If `Ω` is a bounded
Lipschitz domain in a finite-dimensional real inner product space of dimension `n` with an
additive Haar measure, every `u ∈ W^{1,p}(Ω)` lies in `L^q(Ω)` for every `q ≤ p⋆`, where
`1/p⋆ + 1/n = 1/p` and `p⋆ < ∞`. -/
theorem W1p.memLp_value_of_isLipschitzDomain (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ F : ℝ≥0∞)⁻¹ = p⁻¹) (hΩ : (Ω : Set F).IsLipschitzDomain E)
    (hb : IsBounded (Ω : Set F)) {q : ℝ≥0∞} (hq : q ≤ pstar) (u : W1p mu Ω p) :
    MemLp (W1p.value u) q (mu.restrict (Ω : Set F)) := by
  obtain ⟨C, hC⟩ :=
    W1p.exists_eLpNorm_value_le_of_isLipschitzDomain (mu := mu) hpstar hexp hΩ hb hq
  exact (hC u).trans_lt (by finiteness)

/-- **The Sobolev inequality on bounded Lipschitz domains of a Euclidean space for subcritical
exponents.** If `Ω` is a bounded Lipschitz domain in a nontrivial finite-dimensional real inner
product space `F` of dimension `n`, `μ` is an additive Haar measure on `F` and `1 ≤ p`, then for
every finite `s` with `1/p - 1/s < 1/n` there is a constant `C` with
`‖u‖_{L^s(Ω)} ≤ C ‖u‖_{W^{1,p}(Ω)}` for all `u ∈ W^{1,p}(Ω)`. For `p < n` this is every `s < p⋆`;
for `p ≥ n` it is every finite `s`. -/
theorem W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomain [Nontrivial F]
    {s : ℝ≥0∞} (hs : s ≠ ∞) (hps : p⁻¹ < s⁻¹ + (finrank ℝ F : ℝ≥0∞)⁻¹)
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) :
    ∃ C : ℝ≥0, ∀ u : W1p mu Ω p,
      eLpNorm (W1p.value u) s (mu.restrict (Ω : Set F)) ≤ C * ‖u‖ₑ := by
  exact W1p.exists_eLpNorm_value_le_of_isAddHaarMeasure volume mu
    (exists_eLpNorm_value_le_volume_of_isLipschitzDomain hΩ hb fun _ _ _ _ _ _ _ _ hL hbW hn =>
      W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith hs (by rwa [hn]) hL
        hbW)

end Intrinsic

end TauCeti

end
