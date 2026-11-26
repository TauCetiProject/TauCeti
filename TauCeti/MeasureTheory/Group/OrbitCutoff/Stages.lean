/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.OrbitCutoff.Discrete
public import TauCeti.MeasureTheory.Measure.Count.Basic

/-!
# Quotient integrals in stages, and two vanishing criteria

Let `G`, `H` be second countable locally compact groups with left Haar measures `μ`, `ν`, and
`Γ ⊂ G`, `Λ ⊂ H` discrete subgroups. Integrals over `Γ \ G` are integrals against
`Γ.cutoffMeasure μ` (`TauCeti/MeasureTheory/Group/OrbitCutoff/Basic.lean`). This file compares them
with integrals over `Λ \ H`, writes them as iterated integrals with inner integral over `Λ \ H`, and
deduces two criteria for the integral of a continuous left `Γ`-invariant function to vanish.

## Main results

* `Subgroup.exists_integral_comp_cutoffMeasure_eq_smul`: for a continuous surjective homomorphism
  `π : H → G` of unimodular groups with `π(Λ) ⊂ Γ`, the integral over `Λ \ H` of `F ∘ π` is a fixed
  multiple of the integral of `F` over `Γ \ G`.
* `Subgroup.integral_cutoffMeasure_stages`: if `(z, a) ↦ i(a) T(z)` carries `m × ν` to `μ`, with
  `i(Λ) = Γ`, the integral over `Γ \ G` is an iterated integral with inner integral over `Λ \ H`.
* `MeasureTheory.Measure.cosetMeasure μ ν i`: the measure computing integrals over `i(H) \ G`, and
  `MeasureTheory.Measure.measurePreserving_cosetMeasure`, its unfolding along a closed embedding
  `i : H → G`.
* `Subgroup.integral_cutoffMeasure_eq_integral_cosetMeasure`: the case of a closed embedding
  `i : H → G`, with outer integral over `i(H) \ G`.
* `Subgroup.integral_cutoffMeasure_eq_zero_of_mean`: the integral vanishes if an average of right
  translates by elements of a closed subgroup `H ⊇ Γ` multiplies `F` by `a`, while these elements
  scale the Haar measure of `H` by `d ≠ a`.
* `Subgroup.integral_cutoffMeasure_eq_zero_of_twist`: the integral vanishes if
  `F (u y) = c F (y)` with `|c| = 1`, `c ≠ 1`.

## References

* N. Bourbaki, *Intégration*, chapitre VII, Hermann, 1963.

The statements and proofs are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache
2.0, Copyright 2026 Anthropic PBC), `src/Lib/Adelic/QuotientMeasure/UnfoldingInStages.lean`
(`New.exists_integral_comp_quotMeasure_eq_smul`, `New.integral_quotMeasure_stages`,
`New.cosetMeasure`, `New.integral_quotMeasure_eq_integral_cosetMeasure`,
`New.integral_quotMeasure_eq_zero_of_mean`, `New.integral_quotMeasure_eq_zero_of_twist`).
-/

public section

open MeasureTheory Measure Topology Function ProbabilityTheory Set

open scoped ENNReal NNReal Pointwise

/-! ### The measure computing integrals over `i(H) \ G` -/

namespace MeasureTheory.Measure

variable {G H : Type*} [Group G] [MeasurableSpace G] [Group H] [MeasurableSpace H]

/-- The measure computing integrals over `i(H) \ G`, carried by `G`: `μ` weighted by an orbit cutoff
of the action of `H` on `G` by left translation through `i`, for the measure `ν`. -/
noncomputable def cosetMeasure (μ : Measure G) (ν : Measure H) (i : H →* G) : Measure G :=
  letI := MulAction.compHom G i
  ν.cutoffMeasure μ

/-- The measure `μ.cosetMeasure ν i` is `ν.cutoffMeasure μ` for the action of `H` on `G` by left
translation through `i`. -/
theorem cosetMeasure_def (μ : Measure G) (ν : Measure H) (i : H →* G) :
    μ.cosetMeasure ν i = letI := MulAction.compHom G i; ν.cutoffMeasure μ :=
  (rfl)

/-- The coset measure of the zero measure is zero. -/
@[simp]
theorem cosetMeasure_zero (ν : Measure H) (i : H →* G) : (0 : Measure G).cosetMeasure ν i = 0 := by
  let := MulAction.compHom G i
  rw [cosetMeasure_def, cutoffMeasure_zero]

/-- The coset measure is additive in the measure on `G`. -/
theorem cosetMeasure_add (μ μ' : Measure G) (ν : Measure H) (i : H →* G) :
    (μ + μ').cosetMeasure ν i = μ.cosetMeasure ν i + μ'.cosetMeasure ν i := by
  let := MulAction.compHom G i
  rw [cosetMeasure_def, cosetMeasure_def, cosetMeasure_def, cutoffMeasure_add]

/-- The coset measure commutes with scaling the measure on `G`. -/
theorem cosetMeasure_smul (c : ℝ≥0∞) (μ : Measure G) (ν : Measure H) (i : H →* G) :
    (c • μ).cosetMeasure ν i = c • μ.cosetMeasure ν i := by
  let := MulAction.compHom G i
  rw [cosetMeasure_def, cosetMeasure_def, cutoffMeasure_smul]

instance (μ : Measure G) [SFinite μ] (ν : Measure H) (i : H →* G) :
    SFinite (μ.cosetMeasure ν i) := by
  let := MulAction.compHom G i
  rw [cosetMeasure_def]
  infer_instance

/-- **Unfolding along a closed subgroup.** For a closed embedding `i : H → G`, a left Haar measure
`μ` on `G` and a left Haar measure `ν` on `H` that is also right invariant, the map
`(g, a) ↦ i(a) g` carries `μ.cosetMeasure ν i × ν` to `μ`. -/
theorem measurePreserving_cosetMeasure [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [BorelSpace G]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] {i : H →* G} (hi : IsClosedEmbedding i) :
    MeasurePreserving (fun p : G × H ↦ i p.2 * p.1) ((μ.cosetMeasure ν i).prod ν) μ := by
  -- `μ.cosetMeasure ν i` is the cutoff measure of the proper action of `H` through `i`, and
  -- `h • g` is `i h * g` for this action.
  let := MulAction.compHom G i
  have : SMulInvariantMeasure H G μ := ⟨by simp [MulAction.compHom_smul_def]⟩
  have : MeasurableSMul₂ H G :=
    ⟨((hi.continuous.comp continuous_fst).mul continuous_snd).measurable⟩
  have : ProperSMul H G := properSMul_of_isClosedEmbedding i hi fun _ _ ↦ rfl
  have : ν.IsInvInvariant := isInvInvariant_of_isMulRightInvariant ν
  rw [cosetMeasure_def]
  exact measurePreserving_cutoffMeasure

end MeasureTheory.Measure

namespace Subgroup

variable {G H V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  {Γ : Subgroup G} [DiscreteTopology Γ] (Λ : Subgroup H) [DiscreteTopology Λ]
  (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]

/-- **Pushing quotient integrals forward.** Let `π : H → G` be a continuous surjective homomorphism
with `π(Λ) ⊂ Γ`, and let the left Haar measures `μ` and `ν` be also right invariant. There is
`c ∈ ℝ` such that `∫_{Λ\H} F (π r) dr = c ∫_{Γ\G} F` for every measurable left `Γ`-invariant `F`. -/
theorem exists_integral_comp_cutoffMeasure_eq_smul [μ.IsMulRightInvariant] [ν.IsMulRightInvariant]
    {π : H →* G} (hπ : Continuous π) (hπ_surj : Surjective π) (hΛ : Λ ≤ Γ.comap π) :
    ∃ c : ℝ, ∀ F : G → V, Measurable F → (∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) →
      ∫ r, F (π r) ∂Λ.cutoffMeasure ν = c • ∫ g, F g ∂Γ.cutoffMeasure μ := by
  -- The image `κ` of `Λ.cutoffMeasure ν × count` under `(r, γ) ↦ γ π(r)` is right invariant, hence
  -- equal to `d • μ`; then `F ∘ π` on `Λ \ H` is distributed as `F` on `Γ \ G` for `d • μ`.
  let κ : Measure G := ((Λ.cutoffMeasure ν).prod count).map fun p : H × Γ ↦ (p.2 : G) * π p.1
  have hκ : κ.IsMulRightInvariant := by
    refine ⟨hπ_surj.forall.2 fun a ↦ ext_of_lintegral _ fun f hf ↦ ?_⟩
    -- the sum of `f` over the orbit `Γ π(r)` is a `Λ`-invariant function of `r`
    let S (r : H) : ℝ≥0∞ := ∫⁻ γ : Γ, f (γ * π r) ∂count
    have hS (δ : Λ) (r : H) : S (δ • r) = S r := by
      simpa [S, Subgroup.smul_def, mul_assoc] using
        lintegral_mul_right_eq_self (μ := count) (fun γ : Γ ↦ f (γ * π r)) ⟨π δ, hΛ δ.property⟩
    have h_transl : ∫⁻ r, S (r * a) ∂Λ.cutoffMeasure ν = ∫⁻ r, S r ∂Λ.cutoffMeasure ν :=
      (identDistrib_cutoffMeasure_mul_right a (by fun_prop) hS).lintegral_eq
    simpa (disch := fun_prop) [κ, lintegral_map, lintegral_prod, S, mul_assoc] using h_transl
  obtain ⟨d, hd⟩ := exists_eq_smul_of_isMulRightInvariant μ (ν := κ)
  refine ⟨d.toReal, fun F hF hF_inv ↦ ?_⟩
  have h_dist : IdentDistrib F (F ∘ π) ((d • μ).withDensity (count : Measure Γ).orbitCutoff)
      (Λ.cutoffMeasure ν) :=
    (isOrbitCutoff_orbitCutoff _).identDistrib_withDensity_of_measurePreserving (.id _)
      ⟨by fun_prop, hd⟩ hF (by fun_prop) fun γ ↦ hF_inv γ γ.property
  simpa [cutoffMeasure_def, withDensity_smul_measure] using h_dist.integral_eq.symm

omit [μ.IsHaarMeasure] in
/-- **Unfolding in stages.** Let `i : H → G` be an injective homomorphism with `i(Λ) = Γ`, and let
`(z, a) ↦ i(a) T(z)` carry `m × ν` to `μ`, with `m` s-finite. If `F` is measurable, left
`Γ`-invariant and integrable over `Γ \ G`, then `z ↦ ∫_{Λ\H} F (i(a) T(z)) da` is `m`-integrable
and `∫_{Γ\G} F = ∫_Z ∫_{Λ\H} F (i(a) T(z)) da dm(z)`. -/
theorem integral_cutoffMeasure_stages {Z : Type*} [MeasurableSpace Z] {m : Measure Z} [SFinite m]
    (T : Z → G) {i : H →* G} (hi : Injective i)
    (hT : MeasurePreserving (fun p : Z × H ↦ i p.2 * T p.1) (m.prod ν) μ) (hΓ : Λ.map i = Γ)
    {F : G → V} (hF : Measurable F) (hF_inv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g)
    (hF_int : Integrable F (Γ.cutoffMeasure μ)) :
    Integrable (fun z ↦ ∫ a, F (i a * T z) ∂Λ.cutoffMeasure ν) m ∧
      ∫ g, F g ∂Γ.cutoffMeasure μ = ∫ z, ∫ a, F (i a * T z) ∂Λ.cutoffMeasure ν ∂m := by
  -- `((z, a), l) ↦ i(l) i(a) T(z)` unfolds `(m × Λ.cutoffMeasure ν) × count` to `μ`, so `F` on
  -- `Γ \ G` is distributed as `(z, a) ↦ F (i(a) T(z))`; then Fubini.
  let e : Λ ≃* Γ := (Λ.equivMapOfInjective _ hi).trans (.subgroupCongr hΓ)
  have : Countable Λ := countable_of_Lindelof_of_discrete
  have h_unfold : MeasurePreserving (fun p : (Z × H) × Λ ↦ e p.2 • (i p.1.2 * T p.1.1))
      ((m.prod (Λ.cutoffMeasure ν)).prod count) μ := by
    simpa [Function.comp_def, MeasurableEquiv.prodAssoc, Subgroup.smul_def, e, mul_assoc] using
      hT.comp (((MeasurePreserving.id m).prod measurePreserving_cutoffMeasure).comp
        (measurePreserving_prodAssoc m (Λ.cutoffMeasure ν) count))
  have h_dist : IdentDistrib F (fun p : Z × H ↦ F (i p.2 * T p.1)) (Γ.cutoffMeasure μ)
      (m.prod (Λ.cutoffMeasure ν)) :=
    identDistrib_cutoffMeasure_of_measurePreserving e.toEquiv.measurePreserving_count h_unfold hF
      hT.measurable fun γ ↦ hF_inv γ γ.property
  have h_int := h_dist.integrable_snd hF_int
  exact ⟨h_int.integral_prod_left, h_dist.integral_eq.trans (integral_prod _ h_int)⟩

/-- **Integration in stages along a closed subgroup.** Let `i : H → G` be a closed embedding with
`ν` also right invariant, and `F` measurable, left `i(Λ)`-invariant and integrable over
`i(Λ) \ G`. Then `g ↦ ∫_{Λ\H} F (i(a) g) da` is integrable over `i(H) \ G`, and
`∫_{i(Λ)\G} F = ∫_{i(H)\G} ∫_{Λ\H} F (i(a) g) da dg`. -/
theorem integral_cutoffMeasure_eq_integral_cosetMeasure [ν.IsMulRightInvariant] {i : H →* G}
    (hi : IsClosedEmbedding i) {F : G → V} (hF : Measurable F)
    (hF_inv : ∀ γ ∈ Λ.map i, ∀ g, F (γ * g) = F g)
    (hF_int : Integrable F ((Λ.map i).cutoffMeasure μ)) :
    Integrable (fun g ↦ ∫ a, F (i a * g) ∂Λ.cutoffMeasure ν) (μ.cosetMeasure ν i) ∧
      ∫ g, F g ∂(Λ.map i).cutoffMeasure μ =
        ∫ g, ∫ a, F (i a * g) ∂Λ.cutoffMeasure ν ∂μ.cosetMeasure ν i := by
  have : DiscreteTopology (Λ.map i) := (hi.isEmbedding.homeomorphImage Λ).discreteTopology
  exact integral_cutoffMeasure_stages Λ μ ν (fun g ↦ g) hi.injective
    (measurePreserving_cosetMeasure μ ν hi) rfl hF hF_inv hF_int

/-! ### Vanishing of quotient integrals by averaging or by a twist -/

section Vanishing

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  (μ : Measure G) [μ.IsHaarMeasure] {Γ : Subgroup G} [DiscreteTopology Γ] {F : G → V}

/-- **Vanishing by a mean.** Let `Γ ⊂ H ⊂ G` with `H` closed, and `F` continuous and left
`Γ`-invariant. Let `κ` be a probability measure on `C` and `t x b ∈ H` elements, measurable in `b`,
such that right translation by `t x b` multiplies a left Haar measure `ν` of `H` by `d`, and
`∫ F (s t(x, b) x) dκ(b) = a F (s x)` for all `s ∈ H` and `x ∈ G`. If `a ≠ d`, then
`∫_{Γ\G} F = 0`. -/
theorem integral_cutoffMeasure_eq_zero_of_mean (hF : Continuous F)
    (hF_inv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) {H : Subgroup G} (hH : IsClosed (H : Set G))
    (hΓH : Γ ≤ H) (ν : Measure H) [ν.IsHaarMeasure] {C : Type*} [MeasurableSpace C] (κ : Measure C)
    [IsProbabilityMeasure κ] (t : G → C → H) (ht : ∀ x, Measurable (t x)) (d : ℝ≥0)
    (h_scale : ∀ x b, ν.map (· * t x b) = d • ν) {a : ℂ} (ha : a ≠ d)
    (h_mean : ∀ (s : H) (x : G), ∫ b, F (↑(s * t x b) * x) ∂κ = a • F (s * x)) :
    ∫ g, F g ∂Γ.cutoffMeasure μ = 0 := by
  -- If the integral is not zero, unfolding along `H` gives `x` for which the integral `I` of
  -- `s ↦ F (s x)` over `Γ \ H` is not zero; integrating `F (s t(x, b) x)` over `s` and `b` in both
  -- orders gives `a I = d I`.
  have : LocallyCompactSpace H := hH.locallyCompactSpace
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have : MeasurableSMul₂ H G := ⟨(continuous_subtypeVal.comp continuous_fst).mul
    continuous_snd |>.measurable⟩
  obtain ⟨β, hβ⟩ := (inferInstance : HasOrbitCutoff ν.inv G).exists_isOrbitCutoff
  contrapose! ha with h_ne
  borelize V
  let Λ : Subgroup H := Γ.subgroupOf H
  let σ : Measure H := Λ.cutoffMeasure ν
  have h_unfold :
      MeasurePreserving (fun p : G × H ↦ (p.2 : G) * p.1) ((μ.withDensity β).prod ν) μ := by
    have h_one (x : G) : ∫⁻ h : H, β (h * x) ∂ν.inv = 1 := hβ.lintegral_smul x
    simpa [h_one, Subgroup.smul_def] using
      measurePreserving_smul_prod_withDensity (ν := ν) (μ := μ) hβ.measurable
  have h_integral_eq : ∫ g, F g ∂Γ.cutoffMeasure μ = ∫ x, ∫ s, F (s * x) ∂σ ∂μ.withDensity β :=
    (integral_cutoffMeasure_stages Λ μ ν (fun x ↦ x) H.subtype_injective h_unfold
      (map_subgroupOf_eq_of_le hΓH) hF.measurable hF_inv (.of_integral_ne_zero h_ne)).2
  obtain ⟨x, hx⟩ : ∃ x : G, ∫ s, F (s * x) ∂σ ≠ 0 :=
    exists_ne_zero_of_integral_ne_zero (by rwa [← h_integral_eq])
  -- right translation by `t x b` multiplies the measure of `Γ \ H` by `d`
  -- supplied explicitly: instance search for it exhausts its budget in this context
  have : HasOrbitCutoff (count : Measure Λ) H := hasOrbitCutoff_of_properSMul
  have h_dist (b : C) :
      IdentDistrib (fun s : H ↦ F (s * t x b * x)) (fun s : H ↦ F (s * x)) σ (d • σ) := by
    simpa [σ, cutoffMeasure_def, ← coe_nnreal_smul, withDensity_smul_measure, Function.comp_def]
      using identDistrib_cutoffMeasure_comp (.id (count : Measure Λ)) (F := fun s : H ↦ F (s * x))
        ⟨measurable_mul_const (t x b), h_scale x b⟩ (fun γ s ↦ smul_mul_assoc γ s (t x b))
        (by fun_prop) fun γ s ↦ by
          simpa [Subgroup.smul_def, mul_assoc] using hF_inv γ γ.property (s * x)
  have h_prod : Integrable (uncurry fun (s : H) b ↦ F (s * t x b * x)) (σ.prod κ) := by
    have h_slice (b : C) : Integrable (fun s : H ↦ F (s * t x b * x)) σ :=
      (h_dist b).integrable_iff.2 (Integrable.of_integral_ne_zero hx).smul_measure_nnreal
    rw [integrable_prod_iff' (by fun_prop)]
    simp [h_slice, fun b ↦ (h_dist b).norm.integral_eq]
  apply smul_left_injective ℂ hx
  calc a • ∫ s, F (s * x) ∂σ
      = ∫ s, ∫ b, F (s * t x b * x) ∂κ ∂σ := by simp [← h_mean, ← integral_smul a]
    _ = ∫ b, ∫ s, F (s * t x b * x) ∂σ ∂κ := integral_integral_swap h_prod
    _ = (d : ℂ) • ∫ s, F (s * x) ∂σ := by simp [(h_dist _).integral_eq, NNReal.smul_def]

/-- **Vanishing by a twist.** Let `F` be continuous and left `Γ`-invariant. If left translation by
some `u` multiplies `F` by a constant `c ≠ 1` with `|c| = 1`, then `∫_{Γ\G} F = 0`. -/
theorem integral_cutoffMeasure_eq_zero_of_twist (hF : Continuous F)
    (hF_inv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) {u : G} {c : ℂ} (hc : ‖c‖ = 1) (hc_ne : c ≠ 1)
    (hu : ∀ y, F (u * y) = c • F y) : ∫ g, F g ∂Γ.cutoffMeasure μ = 0 := by
  -- Apply the mean criterion to the Dirac mass at `u` and the closed subgroup `S` of the left
  -- translations preserving the defect `F (s u y) - c F (s y)`; it contains `Γ` and `u`.
  let defect (s y : G) : ℝ := dist (F (s * u * y)) (c • F (s * y))
  let S : Subgroup G :=
    { carrier := {s | ∀ r y, defect (s * r) y = defect r y}
      one_mem' := by simp
      mul_mem' := fun {r s} hr hs t y ↦ by rw [mul_assoc, hr, hs]
      inv_mem' := fun {s} hs t y ↦ by simpa using (hs (s⁻¹ * t) y).symm }
  have hS : IsClosed (S : Set G) := by
    -- the carrier of `S` is the set defining it, an intersection of closed sets
    change IsClosed {s : G | ∀ r y, defect (s * r) y = defect r y}
    simp only [ofPred_forall]
    exact isClosed_iInter fun r ↦ isClosed_iInter fun y ↦ isClosed_eq (by fun_prop) continuous_const
  have hΓS : Γ ≤ S := fun γ hγ r y ↦ by simp [defect, mul_assoc, hF_inv γ hγ]
  have huS : u ∈ S := fun r y ↦ by simp [defect, mul_assoc, hu, dist_smul₀, hc]
  have h_twist (s : S) (x : G) : F (s * u * x) = c • F (s * x) := by
    simpa [defect, hu] using s.property 1 x
  have : LocallyCompactSpace S := hS.locallyCompactSpace
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology (S : Set G)
  -- right translation by `u` scales the Haar measure of `S` by some `d ≥ 0`, and `c ≠ d`
  obtain ⟨d, hd⟩ : ∃ d : ℝ≥0, (haar : Measure S).map (· * ⟨u, huS⟩) = d • haar :=
    ⟨_, isMulLeftInvariant_eq_smul _ haar⟩
  have hcd : c ≠ d := fun h ↦ hc_ne (by simpa [h] using hc)
  exact integral_cutoffMeasure_eq_zero_of_mean μ hF hF_inv hS hΓS haar (dirac u)
    (fun _ _ ↦ ⟨u, huS⟩) (fun _ ↦ measurable_const) d (fun _ _ ↦ hd) hcd
    fun s x ↦ by simpa using h_twist s x

end Vanishing

end Subgroup
