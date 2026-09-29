/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the coding map and its defining property appear in every statement below.
public import TauCeti.Probability.Kernel.Randomization
-- Public: the barycenter is the right-hand side of the mixture identity, and this module
-- re-exports the mixing-law existence theorem the representation consumes.
public import TauCeti.Probability.DeFinetti.Barycenter
-- Public: `jointPathLaw` and `iidMixtureLaw` appear in the joint statements.
public import TauCeti.Probability.Exchangeability.ConditionallyIID.PathDisintegration
-- Non-public: de Finetti's theorem, via its subsequence form, is used only inside proofs.
import TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge
import TauCeti.MeasureTheory.Measure.GiryMonad
import TauCeti.Probability.DeFinetti.Subsequence
import TauCeti.Probability.Independence.InfinitePi

/-!
# The coding representation of an exchangeable sequence

De Finetti's theorem describes an exchangeable sequence by a *conditional law*: there is a random
probability measure `ν` such that, given `ν`, the coordinates are i.i.d. `ν`. This file converts
that description into a *functional* one. Writing `ϑ` for a sequence of independent uniform
variables on the unit interval, independent of `ν`, there is a single jointly measurable

```text
f : ProbabilityMeasure α → I → α
```

with

```text
(ν, X) =ᵈ (ν, (f ν ϑᵢ)ᵢ).
```

Thus, in distribution, an exchangeable sequence is a fixed measurable function of one random
parameter — its directing measure — and an independent i.i.d. uniform noise sequence, with all the
randomness of the sequence carried by the noise. This is the sequence case of the representations
in the Aldous–Hoover family, and the shape in which those representations are stated.

The function is `unitIntervalCoding α` of
`TauCeti.Probability.Kernel.Randomization`, the same one for every process on `α`; only the law of
the parameter changes. The converse holds for an arbitrary jointly measurable `f`, without a
standard Borel hypothesis and for an arbitrary parameter space and arbitrary exchangeable noise
(`exchangeableLaw_map_prod_coding`), so the two together characterize exchangeability
(`exchangeableLaw_iff_exists_coding`).

## Main results

* `TauCeti.Probability.map_prod_unitIntervalCoding_eq_deFinettiBarycenter` and
  `TauCeti.Probability.map_prod_unitIntervalCoding_eq_iidMixtureLaw` — coding a mixing law by
  uniform noise reproduces the de Finetti barycenter, and, keeping the parameter, the canonical
  conditionally i.i.d. law.
* `TauCeti.Probability.ConditionallyIIDWith.jointPathLaw_eq_map_unitIntervalCoding` — the joint law
  of a directing measure and its process is the law of the coded pair.
* `TauCeti.Probability.deFinetti_coding` — **the representation**: the joint law of an exchangeable
  process and its directing measure is the law of the coded parameter-noise pair.
* `TauCeti.Probability.ExchangeableLaw.exists_eq_map_unitIntervalCoding` and
  `TauCeti.Probability.exchangeableLaw_iff_exists_coding` — the path-law forms, the second an
  equivalence.
* `TauCeti.Probability.ConditionallyIIDWith.map_comp_eq_map_unitIntervalCoding_of_ae_eq` and
  `TauCeti.Probability.ConditionallyIIDWith.exists_map_comp_eq_map_unitIntervalCoding` — **coding
  given observed coordinates**: once observed coordinates determine the directing measure, the
  remaining coordinates are coded from them by fresh i.i.d. uniform noise.
* `TauCeti.Probability.Exchangeable.exists_map_prodMk_comp_eq_map_coding` — the same coding for a
  sequence exchangeable over a random element `Z`, with `Z` among the observed data.

## Implementation

Everything reduces to one identity about `Measure.prod`: a parameter drawn from `π` together with
independent i.i.d. noise, pushed through a map carrying the noise law to `P t`, has the canonical
law `iidMixtureLaw` (`map_prod_infinitePi_eq_iidMixtureLaw`). At the coding map this is
`map_volume_unitIntervalCoding`, and forgetting the parameter gives the barycenter. No new measure
theory is needed: the analytic content is Mathlib's
`ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval` and the probabilistic content is
the already-proved de Finetti theorem.

This advances `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "exchangeable arrays and the
Aldous–Hoover representation": a functional representation is the form those theorems take, and the
sequence case built here is the base of that tower. No material is adapted from
`cameronfreer/exchangeability`, which stops at the conditional-law form of de Finetti.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Chapter 1, Proposition 1.4.
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Lemma 4.22.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

section Coding

variable [StandardBorelSpace α] [Nonempty α]

/-- Joint measurability of the canonical coordinatewise coding map. -/
theorem measurable_unitIntervalCodingPath :
    Measurable fun p : ProbabilityMeasure α × (ℕ → I) =>
      fun i => unitIntervalCoding α p.1 (p.2 i) :=
  measurable_pi_uncurry_prod (measurable_uncurry_unitIntervalCoding α)

/-- **Coding a mixing law, keeping the parameter.** Retaining the drawn probability measure as a
coordinate, the same construction produces the canonical conditionally i.i.d. law `iidMixtureLaw`:
the parameter is not merely a mixing representative of the coded sequence but its directing
measure. -/
@[simp]
theorem map_prod_unitIntervalCoding_eq_iidMixtureLaw (π : Measure (ProbabilityMeasure α)) :
    (π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        (fun p => (p.1, fun i => unitIntervalCoding α p.1 (p.2 i)))
      = iidMixtureLaw π id :=
  map_prod_infinitePi_eq_iidMixtureLaw _ (measurable_uncurry_unitIntervalCoding α)
    map_volume_unitIntervalCoding

/-- **Coding a mixing law.** Drawing a probability measure from `π`, then coding an independent
i.i.d. uniform sequence by it, produces the de Finetti barycenter of `π`. -/
@[simp]
theorem map_prod_unitIntervalCoding_eq_deFinettiBarycenter (π : Measure (ProbabilityMeasure α)) :
    (π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        (fun p i => unitIntervalCoding α p.1 (p.2 i))
      = deFinettiBarycenter π := by
  have hG : Measurable fun p : ProbabilityMeasure α × (ℕ → I) =>
      (p.1, fun i => unitIntervalCoding α p.1 (p.2 i)) :=
    measurable_fst.prodMk measurable_unitIntervalCodingPath
  calc
    (π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
          (fun p i => unitIntervalCoding α p.1 (p.2 i))
        = ((π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
            (fun p => (p.1, fun i => unitIntervalCoding α p.1 (p.2 i)))).map Prod.snd := by
              rw [Measure.map_map measurable_snd hG]
              rfl
    _ = (iidMixtureLaw π id).map Prod.snd := by
          rw [map_prod_unitIntervalCoding_eq_iidMixtureLaw]
    _ = deFinettiBarycenter π := by
          rw [iidMixtureLaw_def, TauCeti.MeasureTheory.map_bind
            (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const
              (id : ProbabilityMeasure α → ProbabilityMeasure α) measurable_id).aemeasurable
            measurable_snd, deFinettiBarycenter_def]
          simp

/-- **The coding representation of a conditionally i.i.d. process.** The joint law of a directing
measure and the whole path is the joint law of a parameter drawn from the mixing law and the path
obtained by coding independent uniform noise by that parameter.

Keeping the directing measure as a coordinate is what makes this a representation of the process
and not merely of its path law. -/
theorem ConditionallyIIDWith.jointPathLaw_eq_map_unitIntervalCoding {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWith μ X ν) :
    jointPathLaw μ X ν =
      ((μ.map ν).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        (fun p => (p.1, fun i => unitIntervalCoding α p.1 (p.2 i))) := by
  rw [h.jointPathLaw_eq_iidMixtureLaw, map_prod_unitIntervalCoding_eq_iidMixtureLaw]

/-- **The coding representation of an exchangeable process.** An exchangeable sequence in a nonempty
standard Borel space has a directing measure `ν` — it is conditionally i.i.d. `ν` — such that the
joint law of `(ν, X)` equals the law of the pair obtained by applying one fixed measurable map
coordinatewise to `ν` and independent i.i.d. uniform noise.

This is the functional form of de Finetti's theorem: all the randomness of the sequence beyond its
directing measure is the uniform noise. -/
theorem deFinetti_coding {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX_meas : ∀ n, AEMeasurable (X n) μ) (hX : Exchangeable μ X) :
    ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν ∧
      jointPathLaw μ X ν =
        ((μ.map ν).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
          (fun p => (p.1, fun i => unitIntervalCoding α p.1 (p.2 i))) := by
  obtain ⟨ν, hν⟩ := conditionallyIID_iff.mp (deFinetti hX_meas hX)
  exact ⟨ν, hν, hν.jointPathLaw_eq_map_unitIntervalCoding⟩

/-- **The coding representation of an exchangeable path law.** An exchangeable probability measure
on `ℕ → α` is the law of a coded i.i.d. uniform sequence, for a mixing law on
`ProbabilityMeasure α`. -/
theorem ExchangeableLaw.exists_eq_map_unitIntervalCoding {ρ : Measure (ℕ → α)}
    [IsProbabilityMeasure ρ]
    (hρ : ExchangeableLaw ρ) :
    ∃ π : ProbabilityMeasure (ProbabilityMeasure α),
      ρ = ((π : Measure (ProbabilityMeasure α)).prod
            (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
          fun p i => unitIntervalCoding α p.1 (p.2 i) := by
  obtain ⟨π, hπ, -⟩ := hρ.existsUnique_mixingLaw
  exact ⟨π, by rw [map_prod_unitIntervalCoding_eq_deFinettiBarycenter, ← hπ]⟩

/-- **Exchangeability is exactly codability.** A probability law on `ℕ → α`, with `α` nonempty
standard Borel, is exchangeable iff it is the law of a jointly measurable function of a random
parameter and an independent i.i.d. uniform sequence, applied coordinatewise.

The forward direction produces the canonical coding map `unitIntervalCoding α` and takes the
parameter to be the directing measure itself; the converse holds for an arbitrary jointly
measurable `f`. -/
theorem exchangeableLaw_iff_exists_coding {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ] :
    ExchangeableLaw ρ ↔
      ∃ (π : ProbabilityMeasure (ProbabilityMeasure α)) (f : ProbabilityMeasure α → I → α),
        Measurable (Function.uncurry f) ∧
          ρ = ((π : Measure (ProbabilityMeasure α)).prod
                (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
              fun p i => f p.1 (p.2 i) := by
  refine ⟨fun hρ => ?_, fun ⟨π, f, hf, hρ⟩ => ?_⟩
  · obtain ⟨π, hπ⟩ := hρ.exists_eq_map_unitIntervalCoding
    exact ⟨π, unitIntervalCoding α, measurable_uncurry_unitIntervalCoding α, hπ⟩
  · have : IsProbabilityMeasure (π : Measure (ProbabilityMeasure α)) := π.2
    have hnoise : ExchangeableLaw (Measure.infinitePi fun _ : ℕ => (volume : Measure I)) := by
      simpa only [ProbabilityMeasure.coe_mk] using
        exchangeableLaw_infinitePi_const (⟨volume, inferInstance⟩ : ProbabilityMeasure I)
    rw [hρ]
    exact exchangeableLaw_map_prod_coding _ hnoise hf

/-- The path-law form of `deFinetti_coding`: the law of an exchangeable process is the law of a
coded i.i.d. uniform sequence. -/
theorem exists_pathLaw_eq_map_unitIntervalCoding {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX_meas : ∀ n, AEMeasurable (X n) μ) (hX : Exchangeable μ X) :
    ∃ π : ProbabilityMeasure (ProbabilityMeasure α),
      pathLaw μ X = ((π : Measure (ProbabilityMeasure α)).prod
          (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        fun p i => unitIntervalCoding α p.1 (p.2 i) := by
  have : IsProbabilityMeasure (pathLaw μ X) := by
    rw [pathLaw_def]
    infer_instance
  exact ((exchangeable_iff_exchangeableLaw_pathLaw hX_meas).mp hX).exists_eq_map_unitIntervalCoding

/-- **Coding the unobserved coordinates, keeping the directing measure.** For a conditionally
i.i.d. process, the coordinates along an injective `g` are, jointly with the directing measure and
the coordinates along any `e` whose range avoids that of `g`, obtained by coding fresh i.i.d.
uniform variables by the directing measure. The selection `e` need not be injective. -/
theorem ConditionallyIIDWith.map_directing_comp_eq_map_unitIntervalCoding {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWith μ X ν) {ι κ : Type*} {e : ι → ℕ} {g : κ → ℕ}
    (hg : Function.Injective g) (heg : Disjoint (Set.range e) (Set.range g)) :
    μ.map (fun ω => ((ν ω, fun a => X (e a) ω), fun b => X (g b) ω)) =
      ((μ.map fun ω => (ν ω, fun a => X (e a) ω)).prod
          (Measure.infinitePi fun _ : κ => (volume : Measure I))).map
        (fun q => (q.1, fun b => unitIntervalCoding α q.1.1 (q.2 b))) := by
  -- Both sides are pushforwards of `π ⊗ (λ_e ⊗ λ_κ)`, where `π = μ.map ν`, `λ_e` is the law of
  -- the uniform noise read along `e` and `λ_κ` the i.i.d. uniform law on `κ → I`: the coded
  -- representation of `(ν, X)` reads `X ∘ e` and `X ∘ g` off independent parts of one noise.
  set c := unitIntervalCoding α
  set U := Measure.infinitePi fun _ : ℕ => (volume : Measure I)
  set Uκ := Measure.infinitePi fun _ : κ => (volume : Measure I)
  set π := μ.map ν
  have hc := measurable_uncurry_unitIntervalCoding α
  have hpe : Measurable fun (u : ℕ → I) a => u (e a) :=
    Measurable.of_eval fun a => measurable_pi_apply (e a)
  have hpg : Measurable fun (u : ℕ → I) b => u (g b) :=
    Measurable.of_eval fun b => measurable_pi_apply (g b)
  have hpath : AEMeasurable (fun ω n => X n ω) μ := AEMeasurable.of_eval h.aemeasurable
  have hνpath : AEMeasurable (fun ω => (ν ω, fun n => X n ω)) μ :=
    h.measurable_directing.aemeasurable.prodMk hpath
  have hjoint : μ.map (fun ω => (ν ω, fun n => X n ω)) =
      (π.prod U).map fun p => (p.1, fun n => c p.1 (p.2 n)) := by
    simpa only [jointPathLaw_def] using h.jointPathLaw_eq_map_unitIntervalCoding
  have hcode : Measurable fun p : ProbabilityMeasure α × (ℕ → I) =>
      (p.1, fun n => c p.1 (p.2 n)) :=
    measurable_fst.prodMk measurable_unitIntervalCodingPath
  have hcodeι : Measurable fun p : ProbabilityMeasure α × (ι → I) =>
      (p.1, fun a => c p.1 (p.2 a)) :=
    measurable_fst.prodMk (measurable_pi_uncurry_prod hc)
  let Θ : ProbabilityMeasure α × ((ι → I) × (κ → I)) →
      (ProbabilityMeasure α × (ι → α)) × (κ → α) :=
    fun p => ((p.1, fun a => c p.1 (p.2.1 a)), fun b => c p.1 (p.2.2 b))
  have hΘ : Measurable Θ :=
    (measurable_fst.prodMk (measurable_pi_uncurry_prod (ι := ι) hc |>.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).prodMk
      (measurable_pi_uncurry_prod (ι := κ) hc |>.comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  -- The coded law of `(ν, X ∘ e)`.
  have hleft : μ.map (fun ω => (ν ω, fun a => X (e a) ω)) =
      (π.prod (U.map fun u a => u (e a))).map fun p => (p.1, fun a => c p.1 (p.2 a)) := by
    have hF : Measurable fun q : ProbabilityMeasure α × (ℕ → α) => (q.1, fun a => q.2 (e a)) :=
      measurable_fst.prodMk ((Measurable.of_eval fun a => measurable_pi_apply (e a)).comp
        measurable_snd)
    calc μ.map (fun ω => (ν ω, fun a => X (e a) ω))
        = (μ.map fun ω => (ν ω, fun n => X n ω)).map
            fun q => (q.1, fun a => q.2 (e a)) :=
          (AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hνpath).symm
      _ = ((π.prod U).map (Prod.map id fun u a => u (e a))).map
            fun p => (p.1, fun a => c p.1 (p.2 a)) := by
          rw [hjoint, Measure.map_map hF hcode, Measure.map_map hcodeι
            (measurable_id.prodMap hpe)]
          rfl
      _ = _ := by rw [← Measure.map_prod_map _ _ measurable_id hpe, Measure.map_id]
  -- The coded law of `((ν, X ∘ e), X ∘ g)`.
  have hright : μ.map (fun ω => ((ν ω, fun a => X (e a) ω), fun b => X (g b) ω)) =
      (π.prod ((U.map fun u a => u (e a)).prod Uκ)).map Θ := by
    have hF : Measurable fun q : ProbabilityMeasure α × (ℕ → α) =>
        ((q.1, fun a => q.2 (e a)), fun b => q.2 (g b)) :=
      (measurable_fst.prodMk ((Measurable.of_eval fun a => measurable_pi_apply (e a)).comp
        measurable_snd)).prodMk
        ((Measurable.of_eval fun b => measurable_pi_apply (g b)).comp measurable_snd)
    have hsplit : Measurable fun u : ℕ → I => ((fun a => u (e a)), fun b => u (g b)) :=
      hpe.prodMk hpg
    calc μ.map (fun ω => ((ν ω, fun a => X (e a) ω), fun b => X (g b) ω))
        = (μ.map fun ω => (ν ω, fun n => X n ω)).map
            fun q => ((q.1, fun a => q.2 (e a)), fun b => q.2 (g b)) :=
          (AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hνpath).symm
      _ = ((π.prod U).map (Prod.map id fun u => ((fun a => u (e a)), fun b => u (g b)))).map
            Θ := by
          rw [hjoint, Measure.map_map hF hcode, Measure.map_map hΘ
            (measurable_id.prodMap hsplit)]
          rfl
      _ = _ := by
          rw [← Measure.map_prod_map _ _ measurable_id hsplit, Measure.map_id,
            infinitePi_map_pair_comp _ hg heg]
  have hΨ : Measurable fun q : (ProbabilityMeasure α × (ι → α)) × (κ → I) =>
      (q.1, fun b => c q.1.1 (q.2 b)) :=
    measurable_fst.prodMk (measurable_pi_uncurry_prod (ι := κ) hc |>.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  rw [hright, hleft]
  calc (π.prod ((U.map fun u a => u (e a)).prod Uκ)).map Θ
      = (((π.prod (U.map fun u a => u (e a))).prod Uκ).map MeasurableEquiv.prodAssoc).map Θ := by
        rw [Measure.prodAssoc_prod]
    _ = (((π.prod (U.map fun u a => u (e a))).prod Uκ).map
          (Prod.map (fun p => (p.1, fun a => c p.1 (p.2 a))) id)).map
          fun q => (q.1, fun b => c q.1.1 (q.2 b)) := by
        rw [Measure.map_map hΘ MeasurableEquiv.prodAssoc.measurable,
          Measure.map_map hΨ (hcodeι.prodMap measurable_id)]
        rfl
    _ = _ := by rw [← Measure.map_prod_map _ _ hcodeι measurable_id, Measure.map_id]

/-- **Coding the unobserved coordinates from an observed statistic.** Let `Y = φ (X ∘ e)` be a
measurable statistic of the coordinates along `e` which determines the directing measure almost
surely, `ν = G Y`. Then the coordinates along an injective `g` whose range avoids that of `e` are
jointly distributed with `Y` as the coding of fresh i.i.d. uniform variables by `G Y`: given `Y`,
they are i.i.d. with law `G Y`. -/
theorem ConditionallyIIDWith.map_comp_eq_map_unitIntervalCoding_of_ae_eq {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWith μ X ν) {ι κ γ : Type*} [MeasurableSpace γ] {e : ι → ℕ}
    {g : κ → ℕ} (hg : Function.Injective g) (heg : Disjoint (Set.range e) (Set.range g))
    {φ : (ι → α) → γ} (hφ : Measurable φ) {G : γ → ProbabilityMeasure α} (hG : Measurable G)
    (hνG : ν =ᵐ[μ] fun ω => G (φ fun a => X (e a) ω)) :
    μ.map (fun ω => (φ fun a => X (e a) ω, fun b => X (g b) ω)) =
      ((μ.map fun ω => φ fun a => X (e a) ω).prod
          (Measure.infinitePi fun _ : κ => (volume : Measure I))).map
        (fun p => (p.1, fun b => unitIntervalCoding α (G p.1) (p.2 b))) := by
  -- Push `map_directing_comp_eq_map_unitIntervalCoding` forward along `φ`, then replace the
  -- directing measure by `G (φ (X ∘ e))` in the coding. The replacement is made on the product of
  -- the sample space with the noise, where the a.e. identity `hνG` is available.
  set c := unitIntervalCoding α
  set Uκ := Measure.infinitePi fun _ : κ => (volume : Measure I)
  have hc := measurable_uncurry_unitIntervalCoding α
  -- Replace the observed pair `(ν, X ∘ e)` by a measurable version `Y'`.
  have hpath : AEMeasurable (fun ω n => X n ω) μ := AEMeasurable.of_eval h.aemeasurable
  have hY : AEMeasurable (fun ω => (ν ω, fun a => X (e a) ω)) μ :=
    h.measurable_directing.aemeasurable.prodMk
      ((Measurable.of_eval fun a => measurable_pi_apply (e a)).comp_aemeasurable hpath)
  have hYW : AEMeasurable (fun ω => ((ν ω, fun a => X (e a) ω), fun b => X (g b) ω)) μ :=
    hY.prodMk ((Measurable.of_eval fun b => measurable_pi_apply (g b)).comp_aemeasurable hpath)
  obtain ⟨Y', hY', hYY'⟩ := hY
  have hkey : ∀ᵐ ω ∂μ, (Y' ω).1 = G (φ (Y' ω).2) := by
    filter_upwards [hνG, hYY'] with ω h1 h2
    rw [← h2]
    exact h1
  have hS : Measurable fun q : ProbabilityMeasure α × (ι → α) => φ q.2 := hφ.comp measurable_snd
  have hΨ : Measurable fun q : (ProbabilityMeasure α × (ι → α)) × (κ → I) =>
      (φ q.1.2, fun b => c q.1.1 (q.2 b)) :=
    (hS.comp measurable_fst).prodMk (measurable_pi_uncurry_prod (ι := κ) hc |>.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hΦ : Measurable fun p : γ × (κ → I) => (p.1, fun b => c (G p.1) (p.2 b)) :=
    measurable_fst.prodMk (measurable_pi_uncurry_prod (ι := κ) hc |>.comp
      ((hG.comp measurable_fst).prodMk measurable_snd))
  have hΨ₀ : Measurable fun q : (ProbabilityMeasure α × (ι → α)) × (κ → I) =>
      (q.1, fun b => c q.1.1 (q.2 b)) :=
    measurable_fst.prodMk (measurable_pi_uncurry_prod (ι := κ) hc |>.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hSY : Measurable fun ω => φ (Y' ω).2 := hS.comp hY'
  have hprodY : (μ.map Y').prod Uκ = (μ.prod Uκ).map (Prod.map Y' id) := by
    rw [← Measure.map_prod_map _ _ hY' measurable_id, Measure.map_id]
  have hprodSY : (μ.map fun ω => φ (Y' ω).2).prod Uκ =
      (μ.prod Uκ).map (Prod.map (fun ω => φ (Y' ω).2) id) := by
    rw [← Measure.map_prod_map _ _ hSY measurable_id, Measure.map_id]
  calc μ.map (fun ω => (φ fun a => X (e a) ω, fun b => X (g b) ω))
      = (μ.map fun ω => ((ν ω, fun a => X (e a) ω), fun b => X (g b) ω)).map
          (Prod.map (fun q => φ q.2) id) :=
        (AEMeasurable.map_map_of_aemeasurable (hS.prodMap measurable_id).aemeasurable hYW).symm
    _ = ((μ.map Y').prod Uκ).map fun q => (φ q.1.2, fun b => c q.1.1 (q.2 b)) := by
        rw [h.map_directing_comp_eq_map_unitIntervalCoding hg heg, Measure.map_congr hYY',
          Measure.map_map (hS.prodMap measurable_id) hΨ₀]
        rfl
    _ = (μ.prod Uκ).map fun q => (φ (Y' q.1).2, fun b => c (Y' q.1).1 (q.2 b)) := by
        rw [hprodY, Measure.map_map hΨ (hY'.prodMap measurable_id)]
        rfl
    _ = (μ.prod Uκ).map fun q => (φ (Y' q.1).2, fun b => c (G (φ (Y' q.1).2)) (q.2 b)) := by
        refine Measure.map_congr ?_
        filter_upwards [Measure.quasiMeasurePreserving_fst.ae hkey] with q hq
        rw [hq]
    _ = ((μ.map fun ω => φ (Y' ω).2).prod Uκ).map
          fun p => (p.1, fun b => c (G p.1) (p.2 b)) := by
        rw [hprodSY, Measure.map_map hΦ (hSY.prodMap measurable_id)]
        rfl
    _ = _ := by
        congr 2
        refine Measure.map_congr ?_
        filter_upwards [hYY'] with ω hω
        rw [← hω]

/-- **Coding the unobserved coordinates from infinitely many observed ones.** The coordinates along
an injective `e` determine the directing measure through a measurable map `G`, and the coordinates
along an injective `g` whose range avoids that of `e` are coded from the observed ones by `G` and
fresh i.i.d. uniform variables. -/
theorem ConditionallyIIDWith.exists_map_comp_eq_map_unitIntervalCoding {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWith μ X ν) {κ : Type*} {e : ℕ → ℕ} {g : κ → ℕ}
    (he : Function.Injective e) (hg : Function.Injective g)
    (heg : Disjoint (Set.range e) (Set.range g)) :
    ∃ G : (ℕ → α) → ProbabilityMeasure α, Measurable G ∧
      (ν =ᵐ[μ] fun ω => G fun a => X (e a) ω) ∧
        μ.map (fun ω => (fun a => X (e a) ω, fun b => X (g b) ω)) =
          ((μ.map fun ω a => X (e a) ω).prod
              (Measure.infinitePi fun _ : κ => (volume : Measure I))).map
            (fun p => (p.1, fun b => unitIntervalCoding α (G p.1) (p.2 b))) := by
  obtain ⟨G, hG, hνG⟩ := h.exists_measurable_directing_eq_comp he
  exact ⟨G, hG, hνG, h.map_comp_eq_map_unitIntervalCoding_of_ae_eq hg heg measurable_id hG hνG⟩

/-- **Coding a sequence exchangeable over a random element.** Let `Z` be a random element and `Y` a
sequence such that the pairs `(Z, Y n)` form an exchangeable sequence; equivalently, the law of `Y`
is invariant under finite permutations jointly with `Z`. Then, along injective `e` and `g` with
disjoint ranges, the coordinates along `g` are coded from `Z` and the coordinates along `e` by one
measurable map applied to fresh i.i.d. uniform variables.

Conditioning on `Z` as well as on `Y ∘ e` is what the exchangeability over `Z` buys: the coded
coordinates are conditionally i.i.d. given `(Z, Y ∘ e)`, not merely given `Y ∘ e`. -/
theorem Exchangeable.exists_map_prodMk_comp_eq_map_coding {γ β : Type*} [MeasurableSpace γ]
    [StandardBorelSpace γ] [Nonempty γ] [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Z : Ω → γ} {Y : ℕ → Ω → β}
    (hZY : Exchangeable μ fun n ω => (Z ω, Y n ω)) (hZ : AEMeasurable Z μ)
    (hY : ∀ n, AEMeasurable (Y n) μ) {κ : Type*} {e : ℕ → ℕ} {g : κ → ℕ}
    (he : Function.Injective e) (hg : Function.Injective g)
    (heg : Disjoint (Set.range e) (Set.range g)) :
    ∃ v : γ × (ℕ → β) → I → β, Measurable (Function.uncurry v) ∧
      μ.map (fun ω => ((Z ω, fun a => Y (e a) ω), fun b => Y (g b) ω)) =
        ((μ.map fun ω => (Z ω, fun a => Y (e a) ω)).prod
            (Measure.infinitePi fun _ : κ => (volume : Measure I))).map
          (fun p => (p.1, fun b => v p.1 (p.2 b))) := by
  -- By de Finetti, the pairs `(Z, Y n)` are conditionally i.i.d. Their directing measure is a
  -- measurable function `F` of the pairs along `e`, hence of `(Z, Y ∘ e)`; code the pairs along `g`
  -- from it, then forget their constant first coordinate `Z`.
  obtain ⟨ν, hν⟩ := (deFinetti (fun n => hZ.prodMk (hY n)) hZY).exists_directing
  obtain ⟨F, hF, hνF⟩ := hν.exists_measurable_directing_eq_comp he
  have hψ : Measurable fun s : γ × (ℕ → β) => fun a => (s.1, s.2 a) :=
    Measurable.of_eval fun a => measurable_fst.prodMk ((measurable_pi_apply a).comp measurable_snd)
  have hφ : Measurable fun t : ℕ → γ × β => ((t 0).1, fun a => (t a).2) :=
    (measurable_pi_apply 0).fst.prodMk (Measurable.of_eval fun a => (measurable_pi_apply a).snd)
  have hcode := hν.map_comp_eq_map_unitIntervalCoding_of_ae_eq hg heg hφ (hF.comp hψ) hνF
  have hv : Measurable (Function.uncurry fun (s : γ × (ℕ → β)) (t : I) =>
      (unitIntervalCoding (γ × β) (F fun a => (s.1, s.2 a)) t).2) :=
    measurable_snd.comp
      ((measurable_uncurry_unitIntervalCoding (γ × β)).comp ((hF.comp hψ).prodMap measurable_id))
  have hsnd : Measurable fun p : (γ × (ℕ → β)) × (κ → γ × β) => (p.1, fun b => (p.2 b).2) :=
    measurable_fst.prodMk
      (Measurable.of_eval fun b => ((measurable_pi_apply b).comp measurable_snd).snd)
  refine ⟨_, hv, ?_⟩
  have h := congrArg (fun m => m.map fun p : (γ × (ℕ → β)) × (κ → γ × β) =>
    (p.1, fun b => (p.2 b).2)) hcode
  beta_reduce at h
  have : Countable κ := hg.countable
  rwa [AEMeasurable.map_map_of_aemeasurable hsnd.aemeasurable (by fun_prop),
    Measure.map_map hsnd (by fun_prop)] at h

end Coding

end Probability

end TauCeti
