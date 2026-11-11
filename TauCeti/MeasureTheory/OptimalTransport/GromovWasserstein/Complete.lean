/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Point
import TauCeti.MeasureTheory.Function.Lp.Complete
import TauCeti.MeasureTheory.OptimalTransport.Chain
import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Size

/-!
# Common-parametrization convergence and completeness of the Gromov–Wasserstein space

This file characterizes sequential Gromov–Wasserstein convergence by `Lᵖ` convergence on a common
probability space and characterizes completeness of the Gromov–Wasserstein space by completeness of
its metric target `Z`, for every exponent `1 ≤ p ≤ ∞`.

1. **Common-parametrization convergence.** Gluing a countable star of optimal couplings over a
   reference kernel via `MeasureTheory.Measure.starMeasure` produces a single standard Borel
   probability space realizing the exact Gromov–Wasserstein distance `edist (Ks n) L` as an `Lᵖ`
   discrepancy simultaneously for every `n : ℕ`
   (`exists_isProbabilityMeasure_eLpNorm_eq_gromovWassersteinEDist` and
   `GromovWassersteinPresentation.exists_measurePreserving_eLpNorm_eq_edist`). Consequently,
   sequential convergence in `GromovWassersteinPresentation` and `GromovWassersteinSpace` is
   equivalent to `Lᵖ` convergence of pulled-back kernels on a common standard Borel probability
   carrier, with no completeness or separability assumption on `Z`.
2. **Completeness (BMNN Theorem 39).** Gluing consecutive couplings along a summable chain via
   `TauCeti.Measure.chainMeasure` and taking a metric-valued `Lᵖ` limit on the square of the path
   space (`TauCeti.exists_eLpNorm_edist_le_tsum`) produces a strongly measurable limit kernel with
   explicit `Lᵖ` and Gromov–Wasserstein tail bounds. Because almost-everywhere strongly measurable
   kernels have essentially separable ranges, no global separability assumption on `Z` is needed,
   and `eLpNorm` treats finite exponents and `p = ∞` uniformly. Passing through the surjective
   isometry `GromovWassersteinSpace.mk` and combining with the closed isometric copy of one-point
   kernels from `TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Point` yields
   `CompleteSpace (GromovWassersteinSpace.{u} p Z) ↔ CompleteSpace Z` and
   `CompleteSpace (GromovWassersteinPresentation.{u} p Z) ↔ CompleteSpace Z`.

## Main statements

* `TauCeti.exists_isProbabilityMeasure_eLpNorm_eq_gromovWassersteinEDist` — simultaneous optimal
  common parametrization of a countable family of measured kernels against a reference kernel.
* `TauCeti.GromovWassersteinPresentation.tendsto_atTop_iff_exists_tendsto_eLpNorm`,
  `TauCeti.GromovWassersteinSpace.tendsto_mk_atTop_iff_exists_tendsto_eLpNorm`, and
  `TauCeti.GromovWassersteinSpace.tendsto_atTop_iff_exists_presentation_tendsto_eLpNorm` —
  sequential GW convergence is equivalent to `Lᵖ` convergence on a common standard Borel probability
  space.
* `TauCeti.exists_isProbabilityMeasure_gromovWassersteinEDist_le_tsum` and
  `TauCeti.exists_isProbabilityMeasure_gromovWassersteinEDist_le_tsum_of_lt` — countable chains of
  measured kernels with summable GW jumps converge almost everywhere and in `Lᵖ` on the glued path
  space, with the tail bound on GW distances to the limit.
* `TauCeti.GromovWassersteinPresentation.instCompleteSpace` and
  `TauCeti.GromovWassersteinSpace.instCompleteSpace` — completeness over a complete target `Z` for
  all `1 ≤ p ≤ ∞`.
* `TauCeti.GromovWassersteinSpace.completeSpace_iff` and
  `TauCeti.GromovWassersteinPresentation.completeSpace_iff` — completeness of the GW space (or of
  presentations) is equivalent to completeness of `Z`.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), Theorem 39.
* K.-T. Sturm, *The Space of Spaces: Curvature Bounds and Gradient Flows on the Space of Metric
  Measure Spaces*, Mem. Amer. Math. Soc. 290 (2023), no. 1443, Lemma 1.6 and Theorem 5.8.
* F. Mémoli, *Gromov–Wasserstein distances and the metric approach to object matching*,
  Found. Comput. Math. 11 (2011), 417–487, Section 5.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

universe u v

section PseudoEMetricSpace

variable {Z : Type v} [PseudoEMetricSpace Z]

/-- **Simultaneous optimal common parametrization.** Given a standard Borel probability measured
kernel `(X₀, μ₀, ω₀)` and a sequence of standard Borel probability measured kernels
`(Y n, ν n, ω n)` with values in any pseudo-extended-metric space `Z`, gluing optimal couplings over
`μ₀` produces a probability measure `γ` on `X₀ × (∀ n, Y n)` whose coordinate projections
simultaneously realize `gromovWassersteinEDist p (ν n) (ω n) μ₀ ω₀` as an `Lᵖ (γ ⊗ γ)` kernel
discrepancy for every `n`. -/
theorem exists_isProbabilityMeasure_eLpNorm_eq_gromovWassersteinEDist {X₀ : Type u}
    [MeasurableSpace X₀] [StandardBorelSpace X₀] {Y : ℕ → Type u} [∀ n, MeasurableSpace (Y n)]
    [∀ n, StandardBorelSpace (Y n)] (μ₀ : Measure X₀) [IsProbabilityMeasure μ₀]
    (ν : ∀ n, Measure (Y n)) [∀ n, IsProbabilityMeasure (ν n)] {ω₀ : X₀ × X₀ → Z}
    {ω : ∀ n, Y n × Y n → Z} (hω₀ : AEStronglyMeasurable ω₀ (μ₀.prod μ₀))
    (hω : ∀ n, AEStronglyMeasurable (ω n) ((ν n).prod (ν n))) (p : ℝ≥0∞) :
    ∃ γ : Measure (X₀ × ((n : ℕ) → Y n)), IsProbabilityMeasure γ ∧
      MeasurePreserving Prod.fst γ μ₀ ∧
      (∀ n, MeasurePreserving (fun w ↦ w.2 n) γ (ν n)) ∧
      ∀ n, eLpNorm (fun q ↦ edist (ω n (q.1.2 n, q.2.2 n)) (ω₀ (q.1.1, q.2.1))) p (γ.prod γ) =
        gromovWassersteinEDist p (ν n) (ω n) μ₀ ω₀ := by
  have : ∀ n, Nonempty (Y n) := fun n ↦ Measure.nonempty_of_neZero (ν n)
  choose π hπ hπeq using fun n ↦
    exists_isCoupling_gromovWassersteinDistortion_eq_of_standardBorelSpace
      μ₀ (ν n) hω₀ (hω n) p
  have : ∀ n, IsProbabilityMeasure (π n) := fun n ↦ (hπ n).isProbabilityMeasure
  let γ : Measure (X₀ × ((n : ℕ) → Y n)) := μ₀.starMeasure π
  have hg : MeasurePreserving Prod.fst γ μ₀ :=
    μ₀.measurePreserving_fst_starMeasure π
  have hf : ∀ n, MeasurePreserving (fun w : X₀ × ((k : ℕ) → Y k) ↦ w.2 n) γ (ν n) :=
    MeasureTheory.Measure.measurePreserving_eval_snd_starMeasure hπ
  refine ⟨γ, inferInstance, hg, hf, fun n ↦ ?_⟩
  have hmap : γ.map (fun w ↦ (w.1, w.2 n)) = π n :=
    MeasureTheory.Measure.map_prodMk_starMeasure_of_isCoupling hπ n
  calc eLpNorm (fun q ↦ edist (ω n (q.1.2 n, q.2.2 n)) (ω₀ (q.1.1, q.2.1))) p (γ.prod γ)
      = eLpNorm (fun q ↦ edist (ω₀ (q.1.1, q.2.1)) (ω n (q.1.2 n, q.2.2 n))) p (γ.prod γ) :=
        eLpNorm_congr_ae (.of_forall fun _ ↦ edist_comm _ _)
    _ = gromovWassersteinDistortion p ω₀ (ω n) (γ.map fun w ↦ (w.1, w.2 n)) :=
        (gromovWassersteinDistortion_map_prodMk hg (hf n) hω₀ (hω n) p).symm
    _ = gromovWassersteinEDist p μ₀ ω₀ (ν n) (ω n) := by rw [hmap, hπeq n]
    _ = gromovWassersteinEDist p (ν n) (ω n) μ₀ ω₀ := gromovWassersteinEDist_comm _ _ _ _ _

variable {p : ℝ≥0∞}

private theorem exists_limit_of_chain_couplings [CompleteSpace Z] (hp : 1 ≤ p)
    {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X (n + 1))]
    {μ : ∀ n, Measure (X n)} [∀ n, IsProbabilityMeasure (μ n)]
    {ω : ∀ n, X n × X n → Z} (hω : ∀ n, AEStronglyMeasurable (ω n) ((μ n).prod (μ n)))
    {b : ℕ → ℝ≥0∞} (hb : ∑' n, b n ≠ ∞)
    {π : ∀ n, Measure (X n × X (n + 1))} (hπ : ∀ n, IsCoupling (π n) (μ n) (μ (n + 1)))
    (hπb : ∀ n, gromovWassersteinDistortion p (ω n) (ω (n + 1)) (π n) ≤ b n) :
    ∃ (P : Measure ((n : ℕ) → X n)) (ωLim : ((n : ℕ) → X n) × ((n : ℕ) → X n) → Z),
      IsProbabilityMeasure P ∧ StronglyMeasurable ωLim ∧
      (∀ n, MeasurePreserving (fun x ↦ x n) P (μ n)) ∧
      (∀ᵐ q ∂P.prod P, Tendsto (fun n ↦ ω n (q.1 n, q.2 n)) atTop (𝓝 (ωLim q))) ∧
      (∀ n, eLpNorm (fun q ↦ edist (ω n (q.1 n, q.2 n)) (ωLim q)) p (P.prod P) ≤
        ∑' k, b (n + k)) ∧
      ∀ n, gromovWassersteinEDist p (μ n) (ω n) P ωLim ≤ ∑' k, b (n + k) := by
  have : ∀ n, Nonempty (X (n + 1)) := fun n ↦ Measure.nonempty_of_neZero (μ (n + 1))
  have : ∀ n, IsProbabilityMeasure (π n) := fun n ↦ (hπ n).isProbabilityMeasure
  let P : Measure ((n : ℕ) → X n) := TauCeti.Measure.chainMeasure π
  have hmatch : ∀ k, (π k).snd = (π (k + 1)).fst :=
    fun k ↦ (hπ k).snd_eq.trans (hπ (k + 1)).fst_eq.symm
  have hev : ∀ n, MeasurePreserving (fun x : (k : ℕ) → X k ↦ x n) P (μ n) := fun n ↦
    ⟨measurable_pi_apply n,
      (TauCeti.Measure.map_eval_chainMeasure π n fun k _ ↦ hmatch k).trans (hπ n).fst_eq⟩
  have hadj : ∀ n, P.map (fun x ↦ (x n, x (n + 1))) = π n :=
    fun n ↦ TauCeti.Measure.map_adjacent_chainMeasure π n fun k _ ↦ hmatch k
  let F : ℕ → ((k : ℕ) → X k) × ((k : ℕ) → X k) → Z := fun n q ↦ ω n (q.1 n, q.2 n)
  have hF : ∀ n, AEStronglyMeasurable (F n) (P.prod P) := fun n ↦
    (hω n).comp_quasiMeasurePreserving ((hev n).prod (hev n)).quasiMeasurePreserving
  have hjump : ∀ n, eLpNorm (fun q ↦ edist (F n q) (F (n + 1) q)) p (P.prod P) ≤ b n := fun n ↦ by
    rw [← gromovWassersteinDistortion_map_prodMk (hev n) (hev (n + 1)) (hω n) (hω (n + 1)) p,
      hadj n]
    exact hπb n
  obtain ⟨ωLim, hωLim, hae, htail⟩ := exists_eLpNorm_edist_le_tsum hp hF hb hjump
  refine ⟨P, ωLim, inferInstance, hωLim, hev, hae, htail, fun n ↦ ?_⟩
  exact (gromovWassersteinEDist_le_eLpNorm (hev n) (.id P) (hω n)
    hωLim.aestronglyMeasurable p).trans (htail n)

/-- **Countable chain limit for measured kernels under strict jump bounds.** For `1 ≤ p ≤ ∞` and a
complete target `Z`, if consecutive `p`-Gromov–Wasserstein distances along `(X n, μ n, ω n)` are
strictly bounded by a summable sequence `b` and `X (n + 1)` is standard Borel for each `n` (with no
topological hypothesis on `X 0` or separability hypothesis on `Z`), then the glued path law `P` on
`∀ n, X n` carries a strongly measurable limit kernel `ωLim` to which the pulled-back kernels
converge both `P ⊗ P`-almost everywhere and in `Lᵖ`, with the tail bound
`gromovWassersteinEDist p (μ n) (ω n) P ωLim ≤ ∑' k, b (n + k)`. -/
theorem exists_isProbabilityMeasure_gromovWassersteinEDist_le_tsum_of_lt [CompleteSpace Z]
    (hp : 1 ≤ p) {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]
    [∀ n, StandardBorelSpace (X (n + 1))] {μ : ∀ n, Measure (X n)}
    [∀ n, IsProbabilityMeasure (μ n)] {ω : ∀ n, X n × X n → Z}
    (hω : ∀ n, AEStronglyMeasurable (ω n) ((μ n).prod (μ n))) {b : ℕ → ℝ≥0∞}
    (hb : ∑' n, b n ≠ ∞)
    (hjump : ∀ n, gromovWassersteinEDist p (μ n) (ω n) (μ (n + 1)) (ω (n + 1)) < b n) :
    ∃ (P : Measure ((n : ℕ) → X n)) (ωLim : ((n : ℕ) → X n) × ((n : ℕ) → X n) → Z),
      IsProbabilityMeasure P ∧ StronglyMeasurable ωLim ∧
      (∀ n, MeasurePreserving (fun x ↦ x n) P (μ n)) ∧
      (∀ᵐ q ∂P.prod P, Tendsto (fun n ↦ ω n (q.1 n, q.2 n)) atTop (𝓝 (ωLim q))) ∧
      (∀ n, eLpNorm (fun q ↦ edist (ω n (q.1 n, q.2 n)) (ωLim q)) p (P.prod P) ≤
        ∑' k, b (n + k)) ∧
      ∀ n, gromovWassersteinEDist p (μ n) (ω n) P ωLim ≤ ∑' k, b (n + k) := by
  choose π hπ hπb using fun n ↦ gromovWassersteinEDist_lt_iff.1 (hjump n)
  exact exists_limit_of_chain_couplings hp hω hb hπ fun n ↦ (hπb n).le

/-- **Countable chain limit for standard Borel measured kernels.** When all carriers `X n` are
standard Borel, optimal couplings attain consecutive `p`-Gromov–Wasserstein distances at every
exponent `1 ≤ p ≤ ∞`, so weak jump bounds `≤ b n` (including `b n = 0`) suffice for the chain limit
and tail estimate. -/
theorem exists_isProbabilityMeasure_gromovWassersteinEDist_le_tsum [CompleteSpace Z]
    (hp : 1 ≤ p) {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    {μ : ∀ n, Measure (X n)} [∀ n, IsProbabilityMeasure (μ n)] {ω : ∀ n, X n × X n → Z}
    (hω : ∀ n, AEStronglyMeasurable (ω n) ((μ n).prod (μ n))) {b : ℕ → ℝ≥0∞}
    (hb : ∑' n, b n ≠ ∞)
    (hjump : ∀ n, gromovWassersteinEDist p (μ n) (ω n) (μ (n + 1)) (ω (n + 1)) ≤ b n) :
    ∃ (P : Measure ((n : ℕ) → X n)) (ωLim : ((n : ℕ) → X n) × ((n : ℕ) → X n) → Z),
      IsProbabilityMeasure P ∧ StronglyMeasurable ωLim ∧
      (∀ n, MeasurePreserving (fun x ↦ x n) P (μ n)) ∧
      (∀ᵐ q ∂P.prod P, Tendsto (fun n ↦ ω n (q.1 n, q.2 n)) atTop (𝓝 (ωLim q))) ∧
      (∀ n, eLpNorm (fun q ↦ edist (ω n (q.1 n, q.2 n)) (ωLim q)) p (P.prod P) ≤
        ∑' k, b (n + k)) ∧
      ∀ n, gromovWassersteinEDist p (μ n) (ω n) P ωLim ≤ ∑' k, b (n + k) := by
  choose π hπ hπeq using fun n ↦
    exists_isCoupling_gromovWassersteinDistortion_eq_of_standardBorelSpace
      (μ n) (μ (n + 1)) (hω n) (hω (n + 1)) p
  exact exists_limit_of_chain_couplings hp hω hb hπ fun n ↦ (hπeq n).trans_le (hjump n)

end PseudoEMetricSpace

namespace GromovWassersteinPresentation

variable {p : ℝ≥0∞} {Z : Type v} [MetricSpace Z] [Fact (1 ≤ p)]

/-- Any sequence of presentations `Ks` and reference presentation `L` admit a common standard Borel
probability parametrization in the same carrier universe realizing `edist (Ks n) L` exactly as an
`Lᵖ` discrepancy for every `n`. -/
theorem exists_measurePreserving_eLpNorm_eq_edist
    (Ks : ℕ → GromovWassersteinPresentation.{u} p Z)
    (L : GromovWassersteinPresentation.{u} p Z) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (γ : Measure Ω)
      (_ : IsProbabilityMeasure γ) (f : ∀ n, Ω → (Ks n).Carrier) (g : Ω → L.Carrier),
      (∀ n, MeasurePreserving (f n) γ (Ks n).measure) ∧
      MeasurePreserving g γ L.measure ∧
      ∀ n, eLpNorm
        (fun q : Ω × Ω ↦ edist ((Ks n).kernel (f n q.1, f n q.2)) (L.kernel (g q.1, g q.2)))
        p (γ.prod γ) = edist (Ks n) L := by
  obtain ⟨γ, hγ, hg, hf, heq⟩ :=
    exists_isProbabilityMeasure_eLpNorm_eq_gromovWassersteinEDist L.measure
      (fun n ↦ (Ks n).measure) L.aestronglyMeasurable_kernel
      (fun n ↦ (Ks n).aestronglyMeasurable_kernel) p
  exact ⟨L.Carrier × ((n : ℕ) → (Ks n).Carrier), inferInstance, inferInstance, γ, hγ,
    fun n w ↦ w.2 n, Prod.fst, hf, hg, heq⟩

/-- **Common-parametrization characterization of sequential presentation convergence.** A sequence
`Ks` of presentations converges to `L` in the GW pseudometric if and only if there is a standard
Borel probability space `(Ω, γ)` in the carrier universe and measure-preserving maps onto `(Ks n)`
and `L` along which the pulled-back kernels converge in `Lᵖ (γ ⊗ γ)`. Neither completeness nor
separability of `Z` is required. -/
theorem tendsto_atTop_iff_exists_tendsto_eLpNorm
    {Ks : ℕ → GromovWassersteinPresentation.{u} p Z}
    {L : GromovWassersteinPresentation.{u} p Z} :
    Tendsto Ks atTop (𝓝 L) ↔
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (γ : Measure Ω)
        (_ : IsProbabilityMeasure γ) (f : ∀ n, Ω → (Ks n).Carrier) (g : Ω → L.Carrier),
        (∀ n, MeasurePreserving (f n) γ (Ks n).measure) ∧
        MeasurePreserving g γ L.measure ∧
        Tendsto (fun n ↦ eLpNorm
          (fun q : Ω × Ω ↦ edist ((Ks n).kernel (f n q.1, f n q.2)) (L.kernel (g q.1, g q.2)))
          p (γ.prod γ)) atTop (𝓝 0) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨Ω, mΩ, sΩ, γ, hγ, f, g, hf, hg, heq⟩ :=
      exists_measurePreserving_eLpNorm_eq_edist Ks L
    refine ⟨Ω, mΩ, sΩ, γ, hγ, f, g, hf, hg, ?_⟩
    simpa only [heq] using tendsto_iff_edist_tendsto_0.1 h
  · rintro ⟨Ω, mΩ, _, γ, hγ, f, g, hf, hg, hlim⟩
    exact tendsto_of_tendsto_eLpNorm (.of_forall hf) hg hlim

/-- **Summable chains of presentations converge.** Over a complete target `Z`, if
`∑' n, edist (Ks n) (Ks (n + 1)) ≠ ∞`, there exist a limit presentation `KLim` and
measure-preserving maps `f n : KLim.Carrier → (Ks n).Carrier` along which the pulled-back kernels
converge almost everywhere and in `Lᵖ`, with `edist (Ks n) KLim` bounded by the `n`th tail. -/
theorem exists_edist_le_tsum [CompleteSpace Z]
    {Ks : ℕ → GromovWassersteinPresentation.{u} p Z}
    (hb : ∑' n, edist (Ks n) (Ks (n + 1)) ≠ ∞) :
    ∃ (KLim : GromovWassersteinPresentation.{u} p Z) (f : ∀ n, KLim.Carrier → (Ks n).Carrier),
      (∀ n, MeasurePreserving (f n) KLim.measure (Ks n).measure) ∧
      (∀ᵐ q ∂KLim.measure.prod KLim.measure,
        Tendsto (fun n ↦ (Ks n).kernel (f n q.1, f n q.2)) atTop (𝓝 (KLim.kernel q))) ∧
      (∀ n, eLpNorm
        (fun q ↦ edist ((Ks n).kernel (f n q.1, f n q.2)) (KLim.kernel q))
        p (KLim.measure.prod KLim.measure) ≤ ∑' k, edist (Ks (n + k)) (Ks (n + k + 1))) ∧
      ∀ n, edist (Ks n) KLim ≤ ∑' k, edist (Ks (n + k)) (Ks (n + k + 1)) := by
  obtain ⟨P, ωLim, hP, hωLim, hev, hae, htail, hgw⟩ :=
    exists_isProbabilityMeasure_gromovWassersteinEDist_le_tsum (Fact.out : 1 ≤ p)
      (fun n ↦ (Ks n).aestronglyMeasurable_kernel) hb fun n ↦ le_rfl
  obtain ⟨z₀, hz₀⟩ := (Ks 0).finite_moment
  have hmem : MemLp (fun q ↦ edist (ωLim q) z₀) p (P.prod P) :=
    memLp_edist_of_gromovWassersteinEDist_ne_top Fact.out (Ks 0).aestronglyMeasurable_kernel
      hωLim.aestronglyMeasurable hz₀ (ne_top_of_le_ne_top hb (by simpa using hgw 0))
  let KLim : GromovWassersteinPresentation.{u} p Z :=
    { Carrier := (n : ℕ) → (Ks n).Carrier
      measure := P
      kernel := ωLim
      aestronglyMeasurable_kernel := hωLim.aestronglyMeasurable
      finite_moment := ⟨z₀, hmem⟩ }
  exact ⟨KLim, fun n x ↦ x n, hev, hae, htail, hgw⟩

/-- Measured-kernel presentations form a complete pseudometric space over any complete metric
target `Z`, for every exponent `1 ≤ p ≤ ∞` and with no global separability hypothesis on `Z`. -/
instance instCompleteSpace [CompleteSpace Z] :
    CompleteSpace (GromovWassersteinPresentation.{u} p Z) := by
  refine EMetric.complete_of_convergent_controlled_sequences (fun n ↦ 2⁻¹ ^ n)
    (fun n ↦ ENNReal.pow_pos (by simp) n) fun Ks hKs ↦ ?_
  have h2 : ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n ≠ ∞ := by
    simp [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
  have hle : ∀ n, edist (Ks n) (Ks (n + 1)) ≤ 2⁻¹ ^ n :=
    fun n ↦ (hKs n n (n + 1) le_rfl (Nat.le_succ n)).le
  have hb : ∑' n, edist (Ks n) (Ks (n + 1)) ≠ ∞ :=
    ne_top_of_le_ne_top h2 (tsum_le_tsum hle)
  obtain ⟨KLim, -, -, -, -, hgw⟩ := exists_edist_le_tsum hb
  refine ⟨KLim, tendsto_iff_edist_tendsto_0.2 ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hgw
  simpa only [add_comm] using ENNReal.tendsto_sum_nat_add _ hb

end GromovWassersteinPresentation

namespace GromovWassersteinSpace

variable {p : ℝ≥0∞} {Z : Type v} [MetricSpace Z] [Fact (1 ≤ p)]

/-- **Common-parametrization characterization of sequential GW convergence** for presented classes:
`mk (Ks n)` converges to `mk L` in `GromovWassersteinSpace` if and only if `(Ks n)` and `L` admit
measure-preserving parametrizations from a single standard Borel probability space in the carrier
universe along which the pulled-back kernels converge in `Lᵖ`. -/
theorem tendsto_mk_atTop_iff_exists_tendsto_eLpNorm
    {Ks : ℕ → GromovWassersteinPresentation.{u} p Z}
    {L : GromovWassersteinPresentation.{u} p Z} :
    Tendsto (fun n ↦ mk (Ks n)) atTop (𝓝 (mk L)) ↔
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (γ : Measure Ω)
        (_ : IsProbabilityMeasure γ) (f : ∀ n, Ω → (Ks n).Carrier) (g : Ω → L.Carrier),
        (∀ n, MeasurePreserving (f n) γ (Ks n).measure) ∧
        MeasurePreserving g γ L.measure ∧
        Tendsto (fun n ↦ eLpNorm
          (fun q : Ω × Ω ↦ edist ((Ks n).kernel (f n q.1, f n q.2)) (L.kernel (g q.1, g q.2)))
          p (γ.prod γ)) atTop (𝓝 0) := by
  rw [← GromovWassersteinPresentation.tendsto_atTop_iff_exists_tendsto_eLpNorm]
  simp_rw [tendsto_iff_edist_tendsto_0, edist_mk, ← GromovWassersteinPresentation.edist_eq]

/-- **Common-parametrization characterization of sequential GW convergence** on weak-isomorphism
classes: `xs` converges to `x` in `GromovWassersteinSpace` if and only if `xs` and `x` admit
presentations converging in `Lᵖ` on a common standard Borel probability space in the carrier
universe. -/
theorem tendsto_atTop_iff_exists_presentation_tendsto_eLpNorm
    {xs : ℕ → GromovWassersteinSpace.{u} p Z} {x : GromovWassersteinSpace.{u} p Z} :
    Tendsto xs atTop (𝓝 x) ↔
      ∃ (Ks : ℕ → GromovWassersteinPresentation.{u} p Z)
        (L : GromovWassersteinPresentation.{u} p Z)
        (Ω : Type u) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (γ : Measure Ω)
        (_ : IsProbabilityMeasure γ) (f : ∀ n, Ω → (Ks n).Carrier) (g : Ω → L.Carrier),
        (∀ n, mk (Ks n) = xs n) ∧ mk L = x ∧
        (∀ n, MeasurePreserving (f n) γ (Ks n).measure) ∧
        MeasurePreserving g γ L.measure ∧
        Tendsto (fun n ↦ eLpNorm
          (fun q : Ω × Ω ↦ edist ((Ks n).kernel (f n q.1, f n q.2)) (L.kernel (g q.1, g q.2)))
          p (γ.prod γ)) atTop (𝓝 0) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · choose Ks hKs using fun n ↦ mk_surjective (xs n)
    obtain ⟨L, rfl⟩ := mk_surjective x
    rw [← funext hKs] at h
    obtain ⟨Ω, mΩ, sΩ, γ, hγ, f, g, hf, hg, hlim⟩ :=
      tendsto_mk_atTop_iff_exists_tendsto_eLpNorm.1 h
    exact ⟨Ks, L, Ω, mΩ, sΩ, γ, hγ, f, g, hKs, rfl, hf, hg, hlim⟩
  · rintro ⟨Ks, L, Ω, mΩ, sΩ, γ, hγ, f, g, hKs, rfl, hf, hg, hlim⟩
    rw [← funext hKs]
    exact tendsto_mk_atTop_iff_exists_tendsto_eLpNorm.2
      ⟨Ω, mΩ, sΩ, γ, hγ, f, g, hf, hg, hlim⟩

/-- Completeness of presentations and of weak-isomorphism classes are equivalent, since `mk` is a
surjective isometry. -/
theorem completeSpace_iff_completeSpace_presentation :
    CompleteSpace (GromovWassersteinSpace.{u} p Z) ↔
      CompleteSpace (GromovWassersteinPresentation.{u} p Z) :=
  ((isometry_mk.{u} (p := p) (Z := Z)).isUniformInducing.completeSpace_congr mk_surjective).symm

/-- **Completeness of the Gromov–Wasserstein space** over a complete metric target `Z`, for every
exponent `1 ≤ p ≤ ∞` (including `p = ∞`) and with no global separability assumption on `Z`. -/
instance instCompleteSpace [CompleteSpace Z] :
    CompleteSpace (GromovWassersteinSpace.{u} p Z) :=
  completeSpace_iff_completeSpace_presentation.2 inferInstance

/-- **Characterization of completeness of the Gromov–Wasserstein space (BMNN Theorem 39).** For
every `1 ≤ p ≤ ∞`, `GromovWassersteinSpace.{u} p Z` is complete if and only if the ground metric
space `Z` is complete. -/
theorem completeSpace_iff :
    CompleteSpace (GromovWassersteinSpace.{u} p Z) ↔ CompleteSpace Z :=
  ⟨fun _ ↦ completeSpace_of_completeSpace_gromovWassersteinSpace (p := p), fun _ ↦ inferInstance⟩

end GromovWassersteinSpace

/-- Measured-kernel presentations are complete if and only if the ground metric space `Z` is
complete. -/
theorem GromovWassersteinPresentation.completeSpace_iff {p : ℝ≥0∞} {Z : Type v} [MetricSpace Z]
    [Fact (1 ≤ p)] :
    CompleteSpace (GromovWassersteinPresentation.{u} p Z) ↔ CompleteSpace Z :=
  GromovWassersteinSpace.completeSpace_iff_completeSpace_presentation.symm.trans
    GromovWassersteinSpace.completeSpace_iff

end TauCeti
