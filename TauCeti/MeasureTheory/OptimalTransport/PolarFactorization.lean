/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier

/-!
# Brenier's polar factorization

Let `(α, m)` be a probability space and `U : α → E` a map into a finite-dimensional real inner
product space, such as `ℝⁿ`, whose law `m.map U` is absolutely continuous with respect to
Lebesgue measure. Let `P` be another absolutely continuous probability law on `E`, at finite
quadratic transport cost from the law of `U`. **Brenier's polar factorization theorem** writes

`U = ∇u ∘ s` almost everywhere,

where `u : E → EReal` is convex and `s : α → E` has law `P`, that is, `s` is measure-preserving
from `(α, m)` to `(E, P)`. A vector field thus factors as a measure-preserving map followed by the
gradient of a convex function, as a square matrix factors as an orthogonal matrix followed by a
positive semidefinite one. The two factors are unique in different senses.

* The gradient `∇u` is the *monotone rearrangement* of `U` on `(E, P)`: it is the Brenier map
  from `P` to the law of `U`, so it is determined `P`-almost everywhere. Among gradients of convex
  functions pushing `P` to the law of `U` it is unique when both laws have finite second moments.
* Once `u` is fixed, the measure-preserving factor is determined `m`-almost everywhere: it is
  `s = ∇u⋆ ∘ U`, where `u⋆` is the Legendre–Fenchel conjugate of `u`. Variationally, `s` is the
  unique map of law `P` closest to `U`, minimising `∫ ‖s' - U‖ ^ 2 / 2 dm`; when `P` and the law
  of `U` have finite second moments, it is the unique map of law `P` maximising the correlation
  `∫ ⟪s', U⟫ dm`.

Both factors come from Brenier's theorem applied in the two directions between `P` and the law
of `U`: the conjugate gradients `∇u` and `∇u⋆` are inverse to each other almost everywhere, so
`s = ∇u⋆ ∘ U` has law `P` and `∇u ∘ s = U`. The variational characterisation rests on a fact
valid for every cost: if `T` is an optimal transport map from `μ` to the law of `U` and
`U = T ∘ s` with `s` of law `μ`, the pair `(s, U)` pushes `m` to the graph plan of `T`, so `s`
minimises the transport cost of `(s', U)` among all maps `s'` of law `μ`. Uniqueness of the
minimiser is uniqueness of the optimal quadratic plan out of an absolutely continuous source.

## Main statements

* `TauCeti.lintegral_eq_transportCost_of_ae_eq_comp` and `TauCeti.lintegral_le_of_ae_eq_comp`:
  for any measurable cost, a factor `s` of `U = T ∘ s` through an optimal transport map `T`
  attains the transport cost, and minimises the cost of `(s', U)` among maps `s'` of the same
  law;
* `TauCeti.integral_inner_le_of_ae_eq_comp`: on a real inner product space, for the quadratic
  cost and laws with finite second moments, such a factor maximises the correlation
  `∫ ⟪s', U⟫ dm`;
* `TauCeti.exists_hasLaw_and_ae_eq_gradient_comp`, **Brenier's polar factorization**:
  `U = ∇u ∘ (∇u⋆ ∘ U)` almost everywhere, where `∇u` is an optimal transport map from `P` to the
  law of `U` and `∇u⋆ ∘ U` has law `P`;
* `TauCeti.ae_eq_gradient_fenchelConjugate_comp_of_ae_eq_gradient_comp`: the measure-preserving
  factor is determined by the convex one; if `U = ∇u ∘ s` with `s` of law `P`, then
  `s = ∇u⋆ ∘ U` almost everywhere;
* `TauCeti.ae_eq_of_lintegral_norm_sub_sq_le` and `TauCeti.ae_eq_of_integral_inner_le`: the
  measure-preserving factor is the unique map of law `P` minimising the quadratic cost to `U`,
  and, for laws with finite second moments, the unique one maximising the correlation with `U`;
* `TauCeti.gradient_ae_eq_gradient_of_hasLaw`: uniqueness of the monotone rearrangement; two
  gradients of convex functions pushing an absolutely continuous `P` to the same law agree
  `P`-almost everywhere, when both laws have finite second moments.

## References

* Y. Brenier, *Polar factorization and monotone rearrangement of vector-valued functions*, Comm.
  Pure Appl. Math. 44 (1991), 375--417, Theorem 1.2.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology Gradient RealInnerProductSpace

namespace TauCeti

section Cost

variable {α X Y : Type*} [MeasurableSpace α] [MeasurableSpace X] [MeasurableSpace Y]
  {m : Measure α} {μ : Measure X} {c : X × Y → ℝ≥0∞} {T : X → Y} {U : α → Y} {s s' : α → X}

/-- **A factor through an optimal map attains the transport cost.** Let `T` be an optimal
transport map for a measurable cost `c` from `μ` to the law of `U : α → Y`, and let `s : α → X`
have law `μ` with `U = T ∘ s` almost everywhere. Then the pair `(s, U)` pushes `m` to the graph
plan of `T`, so `∫⁻ c (s ω, U ω) dm` is the optimal transport cost from `μ` to the law of `U`. -/
theorem lintegral_eq_transportCost_of_ae_eq_comp (hc : Measurable c)
    (hT : IsKantorovichOptimalTransportMap c μ (m.map U) T) (hs : HasLaw s μ m)
    (h : U =ᵐ[m] T ∘ s) :
    ∫⁻ ω, c (s ω, U ω) ∂m = transportCost c μ (m.map U) := by
  have hT' : AEMeasurable T (m.map s) := hs.map_eq ▸ hT.aemeasurable
  have hU : AEMeasurable U m := (hT'.comp_aemeasurable hs.aemeasurable).congr h.symm
  have hgraph : m.map (fun ω => (s ω, U ω)) = graphPlan T μ := by
    rw [Measure.map_congr (f := fun ω => (s ω, U ω)) (g := fun ω => (s ω, T (s ω)))
        (h.mono fun ω hω => Prod.ext rfl hω), graphPlan_def, ← hs.map_eq,
      AEMeasurable.map_map_of_aemeasurable (aemeasurable_prodMk_self hT') hs.aemeasurable]
    rfl
  refine (lintegral_map' hc.aemeasurable (hs.aemeasurable.prodMk hU)).symm.trans ?_
  rw [hgraph]
  exact ((isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hT.toHasLaw
    hc.aemeasurable).1 hT).lintegral_eq

/-- **A factor through an optimal map is cost-minimising.** Let `T` be an optimal transport map
for a measurable cost `c` from `μ` to the law of `U : α → Y`, and let `s : α → X` have law `μ`
with `U = T ∘ s` almost everywhere. Then among all maps `s'` of law `μ`, `s` minimises the cost
`∫⁻ c (s' ω, U ω) dm`. -/
theorem lintegral_le_of_ae_eq_comp (hc : Measurable c)
    (hT : IsKantorovichOptimalTransportMap c μ (m.map U) T) (hs : HasLaw s μ m)
    (h : U =ᵐ[m] T ∘ s) (hs' : HasLaw s' μ m) :
    ∫⁻ ω, c (s ω, U ω) ∂m ≤ ∫⁻ ω, c (s' ω, U ω) ∂m := by
  have hU : AEMeasurable U m :=
    ((hs.map_eq ▸ hT.aemeasurable).comp_aemeasurable hs.aemeasurable).congr h.symm
  rw [lintegral_eq_transportCost_of_ae_eq_comp hc hT hs h]
  refine le_of_le_of_eq ?_ (lintegral_map' hc.aemeasurable (hs'.aemeasurable.prodMk hU))
  exact transportCost_le_lintegral ⟨(Measure.fst_map_prodMk₀ hs'.aemeasurable hU).trans
    hs'.map_eq, Measure.snd_map_prodMk₀ hs'.aemeasurable hU⟩ c

end Cost

section InnerProduct

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace (E × E)] {m : Measure α} {μ : Measure E} {T : E → E}
  {U s s' : α → E}

/-- For an a.e. measurable `U` and a map `s`, with laws of finite second moment, the quadratic
cost of the pair `(s, U)` is a second-moment term minus the correlation `∫ ⟪s, U⟫`, and the
correlation is at most that term. -/
private theorem lintegral_norm_sub_sq_div_two_eq (hUm : AEMeasurable U m) (hμ : MemLp id 2 μ)
    (hν : MemLp id 2 (m.map U)) (hs : HasLaw s μ m) :
    ∫⁻ ω, ENNReal.ofReal (‖s ω - U ω‖ ^ 2 / 2) ∂m =
        ENNReal.ofReal ((∫ x, ‖x‖ ^ 2 ∂μ + ∫ y, ‖y‖ ^ 2 ∂m.map U) / 2 - ∫ ω, ⟪s ω, U ω⟫ ∂m) ∧
      ∫ ω, ⟪s ω, U ω⟫ ∂m ≤ (∫ x, ‖x‖ ^ 2 ∂μ + ∫ y, ‖y‖ ^ 2 ∂m.map U) / 2 := by
  have hc : Measurable fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) :=
    (ENNReal.continuous_ofReal.comp (((continuous_fst.sub continuous_snd).norm.pow 2).div_const
      2)).measurable
  have hpair := hs.aemeasurable.prodMk hUm
  have hσ : IsCoupling (m.map fun ω => (s ω, U ω)) μ (m.map U) :=
    ⟨(Measure.fst_map_prodMk₀ hs.aemeasurable hUm).trans hs.map_eq,
      Measure.snd_map_prodMk₀ hs.aemeasurable hUm⟩
  have hinner : ∫ z, ⟪z.1, z.2⟫ ∂m.map (fun ω => (s ω, U ω)) = ∫ ω, ⟪s ω, U ω⟫ ∂m :=
    integral_map hpair (continuous_fst.inner continuous_snd).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · refine (lintegral_map' hc.aemeasurable hpair).symm.trans ?_
    rw [hσ.lintegral_norm_sub_sq_div_two hμ hν, hinner]
  · -- Integrate `⟪x, y⟫ ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2` against the coupling `(s, U)_# m`.
    have hμ2 : Integrable (fun x : E => ‖x‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm hμ.aestronglyMeasurable).1 hμ
    have hν2 : Integrable (fun y : E => ‖y‖ ^ 2) (m.map U) :=
      (memLp_two_iff_integrable_sq_norm hν.aestronglyMeasurable).1 hν
    rw [← hinner, ← hσ.integral_comp_fst hμ2.aestronglyMeasurable,
      ← hσ.integral_comp_snd hν2.aestronglyMeasurable,
      ← integral_add (hσ.integrable_comp_fst hμ2) (hσ.integrable_comp_snd hν2), ← integral_div]
    refine integral_mono (hσ.integrable_inner hμ hν)
      (((hσ.integrable_comp_fst hμ2).add (hσ.integrable_comp_snd hν2)).div_const 2) fun z => ?_
    nlinarith [real_inner_le_norm z.1 z.2, sq_nonneg (‖z.1‖ - ‖z.2‖)]

/-- **A factor through an optimal map maximises the correlation.** On a real inner product space,
let `μ` and the law of `U : α → E` have finite second moments, and let `T` be an optimal transport
map for the cost `‖x - y‖ ^ 2 / 2` from `μ` to the law of `U`. If `s` has law `μ` and `U = T ∘ s`
almost everywhere, then among all maps `s'` of law `μ`, `s` maximises the correlation
`∫ ⟪s', U⟫ dm`. -/
theorem integral_inner_le_of_ae_eq_comp (hμ : MemLp id 2 μ) (hν : MemLp id 2 (m.map U))
    (hT : IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      μ (m.map U) T)
    (hs : HasLaw s μ m) (h : U =ᵐ[m] T ∘ s) (hs' : HasLaw s' μ m) :
    ∫ ω, ⟪s' ω, U ω⟫ ∂m ≤ ∫ ω, ⟪s ω, U ω⟫ ∂m := by
  have hUm : AEMeasurable U m :=
    ((hs.map_eq ▸ hT.aemeasurable).comp_aemeasurable hs.aemeasurable).congr h.symm
  have hc : Measurable fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) :=
    (ENNReal.continuous_ofReal.comp (((continuous_fst.sub continuous_snd).norm.pow 2).div_const
      2)).measurable
  have hle := lintegral_le_of_ae_eq_comp hc hT hs h hs'
  beta_reduce at hle
  obtain ⟨h₁, -⟩ := lintegral_norm_sub_sq_div_two_eq hUm hμ hν hs
  obtain ⟨h₂, h₂'⟩ := lintegral_norm_sub_sq_div_two_eq hUm hμ hν hs'
  rw [h₁, h₂, ENNReal.ofReal_le_ofReal_iff (sub_nonneg.2 h₂')] at hle
  linarith

end InnerProduct

section FiniteDimensional

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ρ : Measure E}
  [ρ.IsAddHaarMeasure] {m : Measure α} {P ν : Measure E} {U s s' : α → E} {u : E → EReal}

/-- **The measure-preserving factor is determined by the convex factor.** Let `u : E → EReal` be
convex, lower semicontinuous and never `⊥`, finite with differentiable real representative at
`P`-almost every point, where `P` is absolutely continuous with respect to an additive Haar
measure, and let `U : α → E` have absolutely continuous law. If `U = ∇u ∘ s` almost everywhere for
a map `s` of law `P`, then `s = ∇u⋆ ∘ U` almost everywhere, where `u⋆` is the Legendre–Fenchel
conjugate of `u`. In particular any two such factors agree almost everywhere. -/
theorem ae_eq_gradient_fenchelConjugate_comp_of_ae_eq_gradient_comp (hUρ : m.map U ≪ ρ)
    (hP : P ≪ ρ) (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) (hlsc : LowerSemicontinuous u)
    (hbot : ∀ x, u x ≠ ⊥)
    (hdiff : ∀ᵐ x ∂P, u x ≠ ⊤ ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x)
    (hs : HasLaw s P m) (h : U =ᵐ[m] (∇ fun x => (u x).toReal) ∘ s) :
    s =ᵐ[m] (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) ∘ U := by
  have hT := measurable_gradient fun x => (u x).toReal
  -- `∇u` pushes `P` to the law of `U`, and its graph plan lies in the subdifferential graph.
  have hlaw : HasLaw (∇ fun x => (u x).toReal) (m.map U) P :=
    ⟨hT.aemeasurable, (((hasLaw_map hT.aemeasurable).comp hs).congr h).map_eq.symm⟩
  have hπ := isCoupling_graphPlan hlaw
  have hinv := hπ.gradient_fenchelConjugate_comp_gradient_ae_eq_id hP hUρ hconv hlsc hbot (by
    filter_upwards [hπ.measurePreserving_fst.quasiMeasurePreserving.ae hdiff,
      ae_snd_eq_graphPlan hT.aemeasurable] with z hz hz'
    rw [hz']
    exact gradient_toReal_mem_subdifferential hconv hbot hz.1 hz.2)
  -- Read the inverse relation `∇u⋆ ∘ ∇u = id` along `s`, whose law is `P`.
  rw [← hs.map_eq] at hinv
  filter_upwards [ae_eq_comp hs.aemeasurable hinv, h] with ω hω hω'
  simp only [Function.comp_apply, id] at hω hω' ⊢
  rw [hω', hω]

/-- **Brenier's polar factorization.** Let `(α, m)` be a probability space and `U : α → E` an
a.e. measurable map into a finite-dimensional real inner product space, and let `P` be a
probability law on `E`. Suppose that `P` and the law of `U` are absolutely continuous with
respect to an additive Haar measure and that the optimal cost between them for `‖x - y‖ ^ 2 / 2`
is finite, as it is for laws with finite second moment. Then there is a convex, lower
semicontinuous `u : E → EReal` that never takes the value `⊥`, finite near `P`-almost every point
with differentiable real representative there, such that:

* the gradient `∇u` is an optimal transport map from `P` to the law of `U`, the monotone
  rearrangement of `U` on `(E, P)`;
* the map `s = ∇u⋆ ∘ U` has law `P`, where `u⋆` is the Legendre–Fenchel conjugate of `u`;
* `U = ∇u ∘ s` almost everywhere.

The factor `s` is determined by `u`
(`TauCeti.ae_eq_gradient_fenchelConjugate_comp_of_ae_eq_gradient_comp`) and is the unique map of
law `P` minimising the quadratic cost to `U` (`TauCeti.ae_eq_of_lintegral_norm_sub_sq_le`). -/
theorem exists_hasLaw_and_ae_eq_gradient_comp [IsProbabilityMeasure m] [IsProbabilityMeasure P]
    (hU : AEMeasurable U m) (hUρ : m.map U ≪ ρ) (hP : P ≪ ρ)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) P (m.map U) ≠ ∞) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      (∀ᵐ x ∂P, (∀ᶠ x' in 𝓝 x, u x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        P (m.map U) (∇ fun x => (u x).toReal) ∧
      HasLaw ((∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) ∘ U) P m ∧
      U =ᵐ[m] (∇ fun x => (u x).toReal) ∘
        (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) ∘ U := by
  obtain ⟨u, hconv, hlsc, hbot, hdiff, -, hT, hS, -, hinv⟩ :=
    exists_isKantorovichOptimalTransportMap_gradient_and_gradient_fenchelConjugate hP hUρ hfin
  refine ⟨u, hconv, hlsc, hbot, hdiff, hT, hS.toHasLaw.comp (hasLaw_map hU), ?_⟩
  filter_upwards [ae_eq_comp hU hinv] with ω hω using hω.symm

/-- **The measure-preserving factor is the unique cost minimiser.** Let `u : E → EReal` be convex,
lower semicontinuous and never `⊥`, finite with differentiable real representative at `P`-almost
every point, such that `∇u` is an optimal transport map for `‖x - y‖ ^ 2 / 2` from `P` to the law
of `U : α → E`, at finite optimal cost, both laws being absolutely continuous with respect to an
additive Haar measure. Let `s` have law `P` with `U = ∇u ∘ s` almost everywhere. If a map `s'` of
law `P` is at most as far from `U` as `s`, in the sense that
`∫ ‖s' - U‖ ^ 2 / 2 dm ≤ ∫ ‖s - U‖ ^ 2 / 2 dm`, then `s' = s` almost everywhere. -/
theorem ae_eq_of_lintegral_norm_sub_sq_le [IsFiniteMeasure m] (hUρ : m.map U ≪ ρ) (hP : P ≪ ρ)
    (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) (hlsc : LowerSemicontinuous u)
    (hbot : ∀ x, u x ≠ ⊥)
    (hdiff : ∀ᵐ x ∂P, u x ≠ ⊤ ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x)
    (hT : IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      P (m.map U) (∇ fun x => (u x).toReal))
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) P (m.map U) ≠ ∞)
    (hs : HasLaw s P m) (h : U =ᵐ[m] (∇ fun x => (u x).toReal) ∘ s) (hs' : HasLaw s' P m)
    (hle : ∫⁻ ω, ENNReal.ofReal (‖s' ω - U ω‖ ^ 2 / 2) ∂m ≤
      ∫⁻ ω, ENNReal.ofReal (‖s ω - U ω‖ ^ 2 / 2) ∂m) :
    s' =ᵐ[m] s := by
  have hc : Measurable fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) :=
    (ENNReal.continuous_ofReal.comp (((continuous_fst.sub continuous_snd).norm.pow 2).div_const
      2)).measurable
  have hT' := measurable_gradient fun x => (u x).toReal
  have hU : AEMeasurable U m := (hT'.comp_aemeasurable hs.aemeasurable).congr h.symm
  have : IsFiniteMeasure P := hs.map_eq ▸ inferInstance
  have hpair := hs'.aemeasurable.prodMk hU
  -- The plan of `(s', U)` is optimal, so by uniqueness of the optimal plan out of an absolutely
  -- continuous source it is the graph plan of `∇u`.
  have hopt : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      (m.map fun ω => (s' ω, U ω)) P (m.map U) := by
    have hσ : IsCoupling (m.map fun ω => (s' ω, U ω)) P (m.map U) :=
      ⟨(Measure.fst_map_prodMk₀ hs'.aemeasurable hU).trans hs'.map_eq,
        Measure.snd_map_prodMk₀ hs'.aemeasurable hU⟩
    refine ⟨hσ, le_antisymm ?_ (transportCost_le_lintegral hσ _)⟩
    rw [lintegral_map' hc.aemeasurable hpair, ← lintegral_eq_transportCost_of_ae_eq_comp hc hT hs h]
    exact hle
  have hgraph := ((isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hT.toHasLaw
    hc.aemeasurable).1 hT).unique hP hopt hfin
  -- So `U = ∇u ∘ s'` almost everywhere, and both `s` and `s'` are `∇u⋆ ∘ U`.
  have h' : U =ᵐ[m] (∇ fun x => (u x).toReal) ∘ s' := by
    have hae := ae_snd_eq_graphPlan (μ := P) hT'.aemeasurable
    rw [hgraph] at hae
    exact ae_of_ae_map hpair hae
  filter_upwards [ae_eq_gradient_fenchelConjugate_comp_of_ae_eq_gradient_comp hUρ hP hconv hlsc
      hbot hdiff hs' h',
    ae_eq_gradient_fenchelConjugate_comp_of_ae_eq_gradient_comp hUρ hP hconv hlsc hbot hdiff hs h]
    with ω h₁ h₂
  rw [h₁, h₂]

/-- **The measure-preserving factor is the unique correlation maximiser.** Let `P` and the law of
`U : α → E` have finite second moments and be absolutely continuous with respect to an additive
Haar measure. Let `u : E → EReal` be convex, lower semicontinuous and never `⊥`, finite with
differentiable real representative at `P`-almost every point, and let `s` have law `P` with
`U = ∇u ∘ s` almost everywhere. By `TauCeti.integral_inner_le_of_ae_eq_comp`, `s` maximises the
correlation `∫ ⟪s', U⟫ dm` among maps `s'` of law `P`; it is the unique maximiser: if `s'` has law
`P` and `∫ ⟪s, U⟫ dm ≤ ∫ ⟪s', U⟫ dm`, then `s' = s` almost everywhere. -/
theorem ae_eq_of_integral_inner_le [IsFiniteMeasure m] (hP2 : MemLp id 2 P)
    (hν : MemLp id 2 (m.map U)) (hUρ : m.map U ≪ ρ) (hP : P ≪ ρ)
    (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2})
    (hlsc : LowerSemicontinuous u) (hbot : ∀ x, u x ≠ ⊥)
    (hdiff : ∀ᵐ x ∂P, u x ≠ ⊤ ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x)
    (hs : HasLaw s P m) (h : U =ᵐ[m] (∇ fun x => (u x).toReal) ∘ s) (hs' : HasLaw s' P m)
    (hle : ∫ ω, ⟪s ω, U ω⟫ ∂m ≤ ∫ ω, ⟪s' ω, U ω⟫ ∂m) :
    s' =ᵐ[m] s := by
  have hc : Measurable fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) :=
    (ENNReal.continuous_ofReal.comp (((continuous_fst.sub continuous_snd).norm.pow 2).div_const
      2)).measurable
  have hT' := measurable_gradient fun x => (u x).toReal
  have hUm : AEMeasurable U m := (hT'.comp_aemeasurable hs.aemeasurable).congr h.symm
  have : IsFiniteMeasure P := hs.map_eq ▸ inferInstance
  -- `∇u` pushes `P` to the law of `U`, so it is an optimal transport map, both laws having
  -- finite second moments.
  have hT : IsKantorovichOptimalTransportMap
      (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) P (m.map U)
      (∇ fun x => (u x).toReal) :=
    isKantorovichOptimalTransportMap_gradient hP2 hν hconv hbot hdiff
      ⟨hT'.aemeasurable, (((hasLaw_map hT'.aemeasurable).comp hs).congr h).map_eq.symm⟩
  obtain ⟨h₁, -⟩ := lintegral_norm_sub_sq_div_two_eq hUm hP2 hν hs
  obtain ⟨h₂, -⟩ := lintegral_norm_sub_sq_div_two_eq hUm hP2 hν hs'
  have hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) P (m.map U)
      ≠ ∞ := by
    rw [← lintegral_eq_transportCost_of_ae_eq_comp hc hT hs h]
    dsimp only
    rw [h₁]
    exact ENNReal.ofReal_ne_top
  refine ae_eq_of_lintegral_norm_sub_sq_le hUρ hP hconv hlsc hbot hdiff hT hfin hs h hs' ?_
  rw [h₁, h₂]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Uniqueness of the monotone rearrangement.** Let `P` and `ν` be finite measures with finite
second moments on a finite-dimensional real inner product space, with `P` absolutely continuous
with respect to an additive Haar measure. If `u` and `v : E → EReal` are convex and never `⊥`,
finite with differentiable real representatives at `P`-almost every point, and both gradients push
`P` to `ν`, then `∇u = ∇v` `P`-almost everywhere. -/
theorem gradient_ae_eq_gradient_of_hasLaw [IsFiniteMeasure P] (hP2 : MemLp id 2 P)
    (hν2 : MemLp id 2 ν) (hP : P ≪ ρ) {v : E → EReal}
    (hu : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) (hubot : ∀ x, u x ≠ ⊥)
    (hudiff : ∀ᵐ x ∂P, u x ≠ ⊤ ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x)
    (huν : HasLaw (∇ fun x => (u x).toReal) ν P)
    (hv : Convex ℝ {p : E × ℝ | v p.1 ≤ p.2}) (hvbot : ∀ x, v x ≠ ⊥)
    (hvdiff : ∀ᵐ x ∂P, v x ≠ ⊤ ∧ DifferentiableAt ℝ (fun x' => (v x').toReal) x)
    (hvν : HasLaw (∇ fun x => (v x).toReal) ν P) :
    (∇ fun x => (u x).toReal) =ᵐ[P] ∇ fun x => (v x).toReal := by
  have hc : Measurable fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) :=
    (ENNReal.continuous_ofReal.comp (((continuous_fst.sub continuous_snd).norm.pow 2).div_const
      2)).measurable
  have hu' := (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan huν
    hc.aemeasurable).1 (isKantorovichOptimalTransportMap_gradient hP2 hν2 hu hubot hudiff huν)
  have hv' := (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hvν
    hc.aemeasurable).1 (isKantorovichOptimalTransportMap_gradient hP2 hν2 hv hvbot hvdiff hvν)
  have hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) P ν ≠ ∞ := by
    rw [← hu'.lintegral_eq, hu'.toIsCoupling.lintegral_norm_sub_sq_div_two hP2 hν2]
    exact ENNReal.ofReal_ne_top
  exact (graphPlan_eq_graphPlan_iff huν.aemeasurable hvν.aemeasurable).1
    (hu'.unique hP hv' hfin)

end FiniteDimensional

end TauCeti
