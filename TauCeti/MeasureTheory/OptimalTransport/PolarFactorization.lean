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
valid for every cost, `TauCeti.lintegral_le_of_ae_eq_comp`: if `T` is an optimal transport map
from `μ` to the law of `U` and `U = T ∘ s` with `s` of law `μ`, the pair `(s, U)` pushes `m` to
the graph plan of `T`, so `s` minimises the transport cost of `(s', U)` among all maps `s'` of
law `μ`; for the quadratic cost this is `TauCeti.integral_inner_le_of_ae_eq_comp`, maximality of
the correlation. Uniqueness of the minimiser is uniqueness of the optimal quadratic plan out of
the absolutely continuous law of `U`, the quadratic cost being symmetric. Uniqueness of the
monotone rearrangement is `TauCeti.gradient_ae_eq_gradient_of_hasLaw`.

## Main statements

* `TauCeti.exists_hasLaw_and_ae_eq_gradient_comp`, **Brenier's polar factorization**:
  `U = ∇u ∘ (∇u⋆ ∘ U)` almost everywhere, where `∇u` is an optimal transport map from `P` to the
  law of `U` and `∇u⋆ ∘ U` has law `P`;
* `TauCeti.ae_eq_gradient_fenchelConjugate_comp_of_ae_eq_gradient_comp`: the measure-preserving
  factor is determined by the convex one; if `U = ∇u ∘ s` with `s` of law `P`, then
  `s = ∇u⋆ ∘ U` almost everywhere;
* `TauCeti.ae_eq_of_lintegral_norm_sub_sq_div_two_le` and `TauCeti.ae_eq_of_integral_inner_le`:
  the measure-preserving factor is the unique map of law `P` minimising the quadratic cost to `U`,
  and, for laws with finite second moments, the unique one maximising the correlation with `U`.

## References

* Y. Brenier, *Polar factorization and monotone rearrangement of vector-valued functions*, Comm.
  Pure Appl. Math. 44 (1991), 375--417, Theorem 1.2.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology Gradient RealInnerProductSpace

namespace TauCeti

section FiniteDimensional

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ρ : Measure E}
  [ρ.IsAddHaarMeasure] {m : Measure α} {P : Measure E} {U s s' : α → E} {u : E → EReal}

/-- **The measure-preserving factor is determined by the convex factor.** Let `u : E → EReal` be
convex and never `⊥`, finite with differentiable real representative at `P`-almost every point,
and let `U : α → E` have law absolutely continuous with respect to an additive Haar measure. If
`U = ∇u ∘ s` almost everywhere for a map `s` of law `P`, then `s = ∇u⋆ ∘ U` almost everywhere,
where `u⋆` is the Legendre–Fenchel conjugate of `u`. In particular any two such factors agree
almost everywhere. -/
theorem ae_eq_gradient_fenchelConjugate_comp_of_ae_eq_gradient_comp (hUρ : m.map U ≪ ρ)
    (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) (hbot : ∀ x, u x ≠ ⊥)
    (hdiff : ∀ᵐ x ∂P, u x ≠ ⊤ ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x)
    (hs : HasLaw s P m) (h : U =ᵐ[m] (∇ fun x => (u x).toReal) ∘ s) :
    s =ᵐ[m] (∇ fun y => (fenchelConjugate (innerₗ E) u y).toReal) ∘ U := by
  have hT := measurable_gradient fun x => (u x).toReal
  -- `∇u` pushes `P` to the law of `U`, and its graph plan lies in the subdifferential graph.
  have hlaw : HasLaw (∇ fun x => (u x).toReal) (m.map U) P :=
    ⟨hT.aemeasurable, (((hasLaw_map hT.aemeasurable).comp hs).congr h).map_eq.symm⟩
  have hπ := isCoupling_graphPlan hlaw
  have hsub : ∀ᵐ z ∂graphPlan (∇ fun x => (u x).toReal) P,
      z.2 ∈ subdifferential (innerₗ E) u z.1 := by
    filter_upwards [hπ.measurePreserving_fst.quasiMeasurePreserving.ae hdiff,
      ae_snd_eq_graphPlan hT.aemeasurable] with z hz hz'
    rw [hz']
    exact gradient_toReal_mem_subdifferential hconv hbot hz.1 hz.2
  -- Exchanging the coordinates gives the graph plan of `∇u⋆`, so `∇u⋆ ∘ ∇u = id` `P`-a.e.
  have hinv := (comp_ae_eq_id_of_map_swap_graphPlan_eq hT.aemeasurable
    (measurable_gradient _).aemeasurable
    (map_swap_eq_graphPlan_gradient_fenchelConjugate hπ.snd_eq hUρ hsub).2).1
  -- Read the inverse relation along `s`, whose law is `P`.
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
law `P` minimising the quadratic cost to `U`
(`TauCeti.ae_eq_of_lintegral_norm_sub_sq_div_two_le`). -/
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

/-- **The measure-preserving factor is the unique cost minimiser.** Let `T : E → E` be an optimal
transport map for `‖x - y‖ ^ 2 / 2` from `P` to the law of `U : α → E`, at finite optimal cost,
the law of `U` being absolutely continuous with respect to an additive Haar measure. Let `s` have
law `P` with `U = T ∘ s` almost everywhere. If a map `s'` of law `P` is at most as far from `U` as
`s`, in the sense that `∫ ‖s' - U‖ ^ 2 / 2 dm ≤ ∫ ‖s - U‖ ^ 2 / 2 dm`, then `s' = s` almost
everywhere. For the polar factorization, `T` is the gradient `∇u`. -/
theorem ae_eq_of_lintegral_norm_sub_sq_div_two_le [IsFiniteMeasure m] (hUρ : m.map U ≪ ρ)
    {T : E → E}
    (hT : IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      P (m.map U) T)
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) P (m.map U) ≠ ∞)
    (hs : HasLaw s P m) (h : U =ᵐ[m] T ∘ s) (hs' : HasLaw s' P m)
    (hle : ∫⁻ ω, ENNReal.ofReal (‖s' ω - U ω‖ ^ 2 / 2) ∂m ≤
      ∫⁻ ω, ENNReal.ofReal (‖s ω - U ω‖ ^ 2 / 2) ∂m) :
    s' =ᵐ[m] s := by
  have hc := (continuous_ofReal_norm_sub_sq_div_two (F := E)).measurable
  have hU : AEMeasurable U m := hs.aemeasurable_of_ae_eq_comp hT.aemeasurable h
  have : IsFiniteMeasure P := hs.map_eq ▸ inferInstance
  -- The quadratic cost is symmetric, so exchanging coordinates turns plans out of `P` into plans
  -- out of the absolutely continuous law of `U`, where the optimal plan is unique.
  have hsymm : (fun z : E × E => ENNReal.ofReal (‖z.swap.1 - z.swap.2‖ ^ 2 / 2)) =
      fun z => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) := by
    funext z
    rw [Prod.fst_swap, Prod.snd_swap, norm_sub_rev]
  have hfin' : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) (m.map U) P
      ≠ ∞ := by
    rwa [← hsymm, transportCost_comp_swap hc]
  -- The plan of `(t, U)` for a map `t` of law `P` at most as far from `U` as `s` is optimal, so
  -- the plan of `(U, t)` is optimal out of the law of `U`.
  have hopt : ∀ {t : α → E}, HasLaw t P m →
      ∫⁻ ω, ENNReal.ofReal (‖t ω - U ω‖ ^ 2 / 2) ∂m ≤
        ∫⁻ ω, ENNReal.ofReal (‖s ω - U ω‖ ^ 2 / 2) ∂m →
      IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        ((m.map fun ω => (t ω, U ω)).map Prod.swap) (m.map U) P := by
    intro t ht hle
    have hσ := isCoupling_map_prodMk_of_aemeasurable ht.aemeasurable hU ht.map_eq rfl
    have hopt : IsOptimalCoupling (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        (m.map fun ω => (t ω, U ω)) P (m.map U) := by
      refine ⟨hσ, le_antisymm ?_ (transportCost_le_lintegral hσ _)⟩
      rw [lintegral_map' hc.aemeasurable (ht.aemeasurable.prodMk hU),
        ← lintegral_eq_transportCost_of_ae_eq_comp hc hT hs h]
      exact hle
    exact hsymm ▸ hopt.swap hc
  -- That optimal plan is the graph plan of a gradient `∇v`, so `s` and `s'` are both `∇v ∘ U`.
  obtain ⟨v, -, -, -, -, hgraph⟩ := (hopt hs le_rfl).exists_eq_graphPlan_gradient hUρ hfin'
  have hS := measurable_gradient fun y => (v y).toReal
  have hfactor : ∀ {t : α → E}, HasLaw t P m →
      (m.map fun ω => (t ω, U ω)).map Prod.swap = graphPlan (∇ fun y => (v y).toReal) (m.map U) →
      t =ᵐ[m] (∇ fun y => (v y).toReal) ∘ U := by
    intro t ht heq
    have hae := ae_snd_eq_graphPlan (μ := m.map U) hS.aemeasurable
    rw [← heq] at hae
    exact ae_of_ae_map (ht.aemeasurable.prodMk hU) (ae_of_ae_map measurable_swap.aemeasurable hae)
  filter_upwards [hfactor hs' (((hopt hs le_rfl).unique hUρ (hopt hs' hle) hfin').symm.trans
      hgraph), hfactor hs hgraph] with ω h₁ h₂
  rw [h₁, h₂]

/-- **The measure-preserving factor is the unique correlation maximiser.** Let `P` and the law of
`U : α → E` have finite second moments, the law of `U` being absolutely continuous with respect
to an additive Haar measure. Let `u : E → EReal` be convex and never `⊥`, finite with
differentiable real representative at `P`-almost every point, and let `s` have law `P` with
`U = ∇u ∘ s` almost everywhere. By `TauCeti.integral_inner_le_of_ae_eq_comp`, `s` maximises the
correlation `∫ ⟪s', U⟫ dm` among maps `s'` of law `P`; it is the unique maximiser: if `s'` has law
`P` and `∫ ⟪s, U⟫ dm ≤ ∫ ⟪s', U⟫ dm`, then `s' = s` almost everywhere. -/
theorem ae_eq_of_integral_inner_le [IsFiniteMeasure m] (hP2 : MemLp id 2 P)
    (hν : MemLp id 2 (m.map U)) (hUρ : m.map U ≪ ρ)
    (hconv : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) (hbot : ∀ x, u x ≠ ⊥)
    (hdiff : ∀ᵐ x ∂P, u x ≠ ⊤ ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x)
    (hs : HasLaw s P m) (h : U =ᵐ[m] (∇ fun x => (u x).toReal) ∘ s) (hs' : HasLaw s' P m)
    (hle : ∫ ω, ⟪s ω, U ω⟫ ∂m ≤ ∫ ω, ⟪s' ω, U ω⟫ ∂m) :
    s' =ᵐ[m] s := by
  have hT' := measurable_gradient fun x => (u x).toReal
  have hUm : AEMeasurable U m := hs.aemeasurable_of_ae_eq_comp hT'.aemeasurable h
  have : IsFiniteMeasure P := hs.map_eq ▸ inferInstance
  -- `∇u` pushes `P` to the law of `U`, so it is an optimal transport map, both laws having
  -- finite second moments.
  have hT : IsKantorovichOptimalTransportMap
      (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) P (m.map U)
      (∇ fun x => (u x).toReal) :=
    isKantorovichOptimalTransportMap_gradient hP2 hν hconv hbot hdiff
      ⟨hT'.aemeasurable, (((hasLaw_map hT'.aemeasurable).comp hs).congr h).map_eq.symm⟩
  have h₁ := hs.lintegral_norm_sub_sq_div_two (hasLaw_map hUm) hP2 hν
  have h₂ := hs'.lintegral_norm_sub_sq_div_two (hasLaw_map hUm) hP2 hν
  have hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) P (m.map U)
      ≠ ∞ := by
    rw [← lintegral_eq_transportCost_of_ae_eq_comp
      (continuous_ofReal_norm_sub_sq_div_two (F := E)).measurable hT hs h]
    dsimp only
    rw [h₁]
    exact ENNReal.ofReal_ne_top
  refine ae_eq_of_lintegral_norm_sub_sq_div_two_le hUρ hT hfin hs h hs' ?_
  rw [h₁, h₂]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end FiniteDimensional

end TauCeti
