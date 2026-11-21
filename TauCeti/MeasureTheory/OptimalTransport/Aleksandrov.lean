/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Brenier and Aleksandrov solutions of the Monge–Ampère equation

Between absolutely continuous probability laws `μ = (ρ.restrict X).withDensity f` and
`ν = (ρ.restrict Y).withDensity g` at finite quadratic transport cost on a finite-dimensional real
inner product space `E`, Brenier's theorem represents any optimal quadratic transport map `T` almost
everywhere by the gradient `∇ u` of a convex potential `u : E → EReal`, which solves the weighted
(weak, or Brenier) Monge–Ampère equation `MA_{u,ν} = μ`.

Passing from the weak equation `MA_{u,ν} = μ` to the unweighted Aleksandrov Monge–Ampère equation

  `det D²u = f / (g ∘ ∇u)` on `X`, i.e. `(MA_u)|_X = (f / g ∘ ∇u) ρ|_X`,

splits into an unconditional half and a geometric half:

* **Unconditional Aleksandrov subsolution.** With no convexity, openness, or measurability
  assumption on `X` or `Y`, every optimal quadratic transport map `T` is represented `μ`-almost
  everywhere by the gradient of a convex potential `u` satisfying both the weak equation
  `MA_{u,ν} = μ` and the lower density bound `(f / g ∘ ∇u) ρ|_X ≤ MA_u`
  (`TauCeti.exists_withDensity_div_le_mongeAmpereMeasure_of_isKantorovichOptimalTransportMap`).
* **Convex target gives an Aleksandrov solution.** When `X` is open with `f ≠ 0` almost everywhere
  on `X` and `Y` is convex with `0 < g` almost everywhere on `Y`, `T` is represented
  `ρ.restrict X`-almost everywhere by a convex potential `u` with `X ⊆ interior {x | u x ≠ ⊤}`,
  `∂u(x) ⊆ closure Y` everywhere, and `MA_u = (f / g ∘ ∇u) ρ|_X`
  (`TauCeti.exists_mongeAmpereMeasure_eq_withDensity_div_of_isKantorovichOptimalTransportMap`).
  When `X` and `Y` are also bounded, quadratic transport cost is automatically finite, giving
  unconditional existence of an optimal Brenier–Aleksandrov potential without assuming a prior
  optimal map or finite cost (`TauCeti.exists_mongeAmpereMeasure_eq_withDensity_div_of_isBounded`),
  while universality across all transporting convex gradients holds without boundedness by
  `TauCeti.subgradientImage_subset_and_restrict_mongeAmpereMeasure_eq_withDensity_div`.
  Under uniform density bounds `lam ≤ f ≤ Lam` on `X` and `m ≤ g ≤ M` on `Y`, any optimal map is
  represented by a potential satisfying the two-sided Aleksandrov Monge–Ampère pinch
  `(lam / M) • ρ|_Ω ≤ MA_u^Ω ≤ (Lam / m) • ρ|_Ω` on every open convex subdomain `Ω ⊆ X`
  (`TauCeti.exists_mongeAmpereMeasure_ite_bounds_of_isKantorovichOptimalTransportMap`).
* **Sharpness of target convexity.** On `ℝ`, transporting the uniform law on `X = (-1, 1)` to the
  uniform law on the disconnected target `Y = (-2, -1) ∪ (1, 2)` has optimal convex potential
  `u(x) = x ^ 2 / 2 + |x|`. It solves the weak equation `MA_{u,ν} = μ` and the unconditional lower
  bound `volume|_X ≤ MA_u`, yet `∂u(0) = [-1, 1]` gives an atom `MA_u({0}) = 2`, so `(MA_u)|_X` is
  not absolutely continuous with respect to Lebesgue measure and `∂u(X)` is not contained in
  `closure Y`
  (`TauCeti.isKantorovichOptimalTransportMap_sq_div_two_add_abs_and_not_absolutelyContinuous`).

## Main statements

* `TauCeti.exists_withDensity_div_le_mongeAmpereMeasure_of_isKantorovichOptimalTransportMap` —
  unconditional Aleksandrov subsolution potential representing an optimal quadratic map;
* `TauCeti.exists_mongeAmpereMeasure_eq_withDensity_div_of_isKantorovichOptimalTransportMap` —
  convex-target Aleksandrov solution potential representing an optimal quadratic map on an open
  source `X`;
* `TauCeti.exists_mongeAmpereMeasure_eq_withDensity_div_of_isBounded` — unconditional existence of
  an optimal Brenier–Aleksandrov potential between bounded open `X` and bounded convex `Y`;
* `TauCeti.exists_mongeAmpereMeasure_ite_bounds_of_isKantorovichOptimalTransportMap` — two-sided
  Aleksandrov Monge–Ampère pinch on open convex subdomains `Ω ⊆ X` for pinched densities;
* `TauCeti.subdifferential_sq_div_two_add_abs_zero`,
  `TauCeti.mongeAmpereMeasure_sq_div_two_add_abs_singleton_zero`, and
  `TauCeti.isKantorovichOptimalTransportMap_sq_div_two_add_abs_and_not_absolutelyContinuous` —
  1D split-interval sharpness counterexample when target convexity is dropped.

## References

* L. A. Caffarelli, *The regularity of mappings with a convex potential*, J. Amer. Math. Soc. 5
  (1992), 99–104.
* A. Figalli, *The Monge–Ampère Equation and Its Applications*, Zurich Lectures in Advanced
  Mathematics, EMS, 2017, §4.6.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, AMS, 2003,
  §4.1–4.2.
-/

public section

noncomputable section

open MeasureTheory Measure Set Filter ProbabilityTheory
open scoped Topology Gradient NNReal ENNReal

namespace TauCeti

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure]

/-- **Every optimal quadratic transport map is represented by an Aleksandrov subsolution.** Let `X`
and `Y` be arbitrary subsets of `E` (neither need be open, convex, bounded, or measurable), let
`μ = (ρ.restrict X).withDensity f` be a probability measure, and let
`ν = (ρ.restrict Y).withDensity g` have finite quadratic transport cost from `μ`. Any optimal
quadratic transport map `T` from `μ` to `ν` agrees `μ`-almost everywhere with the gradient of a
convex, lower semicontinuous `u : E → EReal` (never `⊥`) solving the weak equation `MA_{u,ν} = μ`
and the unconditional Aleksandrov lower bound `(f / g ∘ ∇u) ρ|_X ≤ MA_u`. -/
theorem exists_withDensity_div_le_mongeAmpereMeasure_of_isKantorovichOptimalTransportMap
    {X Y : Set E} {f g : E → ℝ≥0∞} {T : E → E}
    (hf : AEMeasurable f (ρ.restrict X)) (hg : Measurable g)
    [IsProbabilityMeasure ((ρ.restrict X).withDensity f)]
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      ((ρ.restrict X).withDensity f) ((ρ.restrict Y).withDensity g) ≠ ∞)
    (hT : IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      ((ρ.restrict X).withDensity f) ((ρ.restrict Y).withDensity g) T) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      (T =ᵐ[(ρ.restrict X).withDensity f] ∇ fun x => (u x).toReal) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        ((ρ.restrict X).withDensity f) ((ρ.restrict Y).withDensity g)
        (∇ fun x => (u x).toReal) ∧
      mongeAmpereMeasure ((ρ.restrict Y).withDensity g) u = (ρ.restrict X).withDensity f ∧
      (ρ.restrict X).withDensity (fun x => f x / g ((∇ fun x' => (u x').toReal) x)) ≤
        mongeAmpereMeasure ρ u := by
  have hμρ : (ρ.restrict X).withDensity f ≪ ρ :=
    (withDensity_absolutelyContinuous _ _).trans (absolutelyContinuous_of_le restrict_le_self)
  have hνρ : (ρ.restrict Y).withDensity g ≪ ρ :=
    (withDensity_absolutelyContinuous _ _).trans (absolutelyContinuous_of_le restrict_le_self)
  obtain ⟨u, hconv, hlsc, hbot, hdiff, hopt, -, huniq⟩ :=
    exists_isKantorovichOptimalTransportMap_gradient
      (isCCRegular_of_absolutelyContinuous hμρ) hfin
  have hdom : ∀ᵐ x ∂(ρ.restrict X).withDensity f, u x ≠ ⊤ :=
    hdiff.mono fun _ hx => hx.1.self_of_nhds
  have hMA : mongeAmpereMeasure ((ρ.restrict Y).withDensity g) u =
      (ρ.restrict X).withDensity f :=
    ((hasLaw_gradient_and_ae_ne_top_iff_mongeAmpereMeasure_eq_and_ae_mem_subgradientImage
      hconv hbot hμρ hνρ).1 ⟨hopt.toHasLaw, hdom⟩).1
  exact ⟨u, hconv, hlsc, hbot, huniq T hT, hopt, hMA,
    withDensity_div_le_mongeAmpereMeasure hconv hbot hf hg hdom hopt.toHasLaw⟩

/-- **Optimal quadratic transport into a convex target is represented by an Aleksandrov solution.**
Let `X` be open and `Y` convex (neither need be bounded, and `Y` need not be open, closed, or Borel
measurable), let `μ = (ρ.restrict X).withDensity f` be a probability measure with `f ≠ 0` almost
everywhere on `X`, and let `ν = (ρ.restrict Y).withDensity g` have `g ≠ 0` almost everywhere on
`Y` and finite quadratic transport cost from `μ`. Any optimal quadratic transport map `T` from `μ`
to `ν` agrees `ρ.restrict X`-almost everywhere with the gradient of a convex, lower semicontinuous
`u : E → EReal` (never `⊥`) satisfying `X ⊆ interior {x | u x ≠ ⊤}`, `∂u(x) ⊆ closure Y` for all
`x`, and the global Aleksandrov equation `MA_u = (f / g ∘ ∇u) ρ|_X`. -/
theorem exists_mongeAmpereMeasure_eq_withDensity_div_of_isKantorovichOptimalTransportMap
    {X Y : Set E} {f g : E → ℝ≥0∞} {T : E → E} (hX : IsOpen X) (hY : Convex ℝ Y)
    (hf : AEMeasurable f (ρ.restrict X)) (hg : Measurable g)
    (hfpos : ∀ᵐ x ∂ρ.restrict X, f x ≠ 0) (hgpos : ∀ᵐ y ∂ρ.restrict Y, g y ≠ 0)
    [IsProbabilityMeasure ((ρ.restrict X).withDensity f)]
    (hfin : transportCost (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      ((ρ.restrict X).withDensity f) ((ρ.restrict Y).withDensity g) ≠ ∞)
    (hT : IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      ((ρ.restrict X).withDensity f) ((ρ.restrict Y).withDensity g) T) :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      (T =ᵐ[ρ.restrict X] ∇ fun x => (u x).toReal) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        ((ρ.restrict X).withDensity f) ((ρ.restrict Y).withDensity g)
        (∇ fun x => (u x).toReal) ∧
      X ⊆ interior {x | u x ≠ ⊤} ∧ (∀ x, subdifferential (innerₗ E) u x ⊆ closure Y) ∧
      mongeAmpereMeasure ρ u =
        (ρ.restrict X).withDensity fun x => f x / g ((∇ fun x' => (u x').toReal) x) := by
  set μ' := (ρ.restrict X).withDensity f
  set ν' := (ρ.restrict Y).withDensity g
  have hμ'ρ : μ' ≪ ρ :=
    (withDensity_absolutelyContinuous _ _).trans (absolutelyContinuous_of_le restrict_le_self)
  have hg'm : Measurable ((interior Y).indicator g) := hg.indicator isOpen_interior.measurableSet
  have hint : ∀ᵐ y ∂ν', y ∈ interior Y := hY.ae_withDensity_restrict_mem_interior ρ g
  obtain ⟨u, hconv, hlsc, hbot, hopt, hsubcl, hMA⟩ :=
    exists_isKantorovichOptimalTransportMap_gradient_and_mongeAmpereMeasure_eq_withDensity
      (isCCRegular_of_absolutelyContinuous hμ'ρ) hg'm
      (hY.withDensity_restrict_eq_withDensity_indicator_interior ρ g) hY.closure
      isClosed_closure ((mem_ae_iff (s := closure Y)).1 (hint.mono fun _ hy =>
        interior_subset_closure hy))
      (hY.ae_mem_closure_imp_indicator_interior_ne_zero_iff.2 hgpos) hfin
  obtain ⟨_, -, -, -, -, -, -, huniq⟩ :=
    exists_isKantorovichOptimalTransportMap_gradient
      (isCCRegular_of_absolutelyContinuous hμ'ρ) hfin
  have hXμ : ρ.restrict X ≪ μ' := withDensity_absolutelyContinuous' hf hfpos
  have hTu : T =ᵐ[ρ.restrict X] ∇ fun x => (u x).toReal :=
    hXμ.ae_le ((huniq T hT).trans (huniq _ hopt).symm)
  -- `g` is finite along `∇ u`, so `μ' ≪ MA_u`, forcing `X ⊆ interior {u ≠ ⊤}`.
  have := isProbabilityMeasure_right_of_transportCost_ne_top hfin
  have hgtop : ∀ᵐ y ∂ρ.restrict Y, g y ≠ ∞ := by
    refine (ae_lt_top hg ?_).mono fun _ hy => hy.ne
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ]
    exact measure_ne_top ν' univ
  have hν'map : ∀ᵐ y ∂Measure.map (∇ fun x' => (u x').toReal) μ', y ∈ interior Y ∧ g y ≠ ∞ := by
    rw [hopt.toHasLaw.map_eq]
    exact hint.and ((withDensity_absolutelyContinuous _ _).ae_le hgtop)
  have hGgood := ae_of_ae_map hopt.toHasLaw.aemeasurable hν'map
  have hμ'MA : μ' ≪ mongeAmpereMeasure ρ u := by
    rw [hMA]
    refine withDensity_absolutelyContinuous' (hg'm.inv.comp (measurable_gradient _)).aemeasurable ?_
    exact hGgood.mono fun _ hx => ENNReal.inv_ne_zero.2 (by simpa [hx.1] using hx.2)
  have hXD : X ⊆ interior {x | u x ≠ ⊤} :=
    hX.subset_interior_of_ae_le (μ := ρ) (convex_setOf_ne_top hconv) <| ae_imp_of_ae_restrict <|
      (hXμ.trans hμ'MA).ae_le <|
        (measure_eq_zero_iff_ae_notMem.1 (mongeAmpereMeasure_compl_interior ρ (f := u))).mono
          fun _ hx => interior_subset (notMem_compl_iff.1 hx)
  refine ⟨u, hconv, hlsc, hbot, hTu, hopt, hXD, hsubcl, hMA.trans ?_⟩
  trans μ'.withDensity (g⁻¹ ∘ (∇ fun x => (u x).toReal))
  · exact withDensity_congr_ae (hGgood.mono fun _ hx => by simp [hx.1])
  · rw [← withDensity_mul₀ hf (hg.inv.comp (measurable_gradient _)).aemeasurable]
    exact withDensity_congr_ae (.of_forall fun _ => (div_eq_mul_inv _ _).symm)

/-- **Existence of an optimal Aleksandrov solution on bounded domains.** Let `X` be bounded and open
and `Y` bounded and convex, with probability densities `μ = (ρ.restrict X).withDensity f` (`f ≠ 0`
almost everywhere on `X`) and `ν = (ρ.restrict Y).withDensity g` (`g ≠ 0` almost everywhere on `Y`).
Then the quadratic transport cost from `μ` to `ν` is finite automatically, and there exists a
convex, lower semicontinuous `u : E → EReal` (never `⊥`) whose gradient is Kantorovich-optimal from
`μ` to `ν`, with `X ⊆ interior {x | u x ≠ ⊤}`, `∂u(x) ⊆ closure Y` for all `x`, and
`MA_u = (f / g ∘ ∇u) ρ|_X`. -/
theorem exists_mongeAmpereMeasure_eq_withDensity_div_of_isBounded
    {X Y : Set E} {f g : E → ℝ≥0∞} (hX : IsOpen X) (hXb : Bornology.IsBounded X)
    (hY : Convex ℝ Y) (hYb : Bornology.IsBounded Y)
    (hf : AEMeasurable f (ρ.restrict X)) (hg : Measurable g)
    (hfpos : ∀ᵐ x ∂ρ.restrict X, f x ≠ 0) (hgpos : ∀ᵐ y ∂ρ.restrict Y, g y ≠ 0)
    [IsProbabilityMeasure ((ρ.restrict X).withDensity f)]
    [IsProbabilityMeasure ((ρ.restrict Y).withDensity g)] :
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        ((ρ.restrict X).withDensity f) ((ρ.restrict Y).withDensity g)
        (∇ fun x => (u x).toReal) ∧
      X ⊆ interior {x | u x ≠ ⊤} ∧ (∀ x, subdifferential (innerₗ E) u x ⊆ closure Y) ∧
      mongeAmpereMeasure ρ u =
        (ρ.restrict X).withDensity fun x => f x / g ((∇ fun x' => (u x').toReal) x) := by
  have hfin := transportCost_norm_sub_sq_div_two_ne_top_of_withDensity_isBounded
    (ρ₁ := ρ) (ρ₂ := ρ) (f := f) (g := g) hXb hYb
  have hμρ : (ρ.restrict X).withDensity f ≪ ρ :=
    (withDensity_absolutelyContinuous _ _).trans (absolutelyContinuous_of_le restrict_le_self)
  obtain ⟨_, -, -, -, -, hopt₀, -, -⟩ :=
    exists_isKantorovichOptimalTransportMap_gradient (isCCRegular_of_absolutelyContinuous hμρ) hfin
  obtain ⟨u, hconv, hlsc, hbot, -, hopt, hXD, hsubcl, hMA⟩ :=
    exists_mongeAmpereMeasure_eq_withDensity_div_of_isKantorovichOptimalTransportMap
      hX hY hf hg hfpos hgpos hfin hopt₀
  exact ⟨u, hconv, hlsc, hbot, hopt, hXD, hsubcl, hMA⟩

/-- **Two-sided Aleksandrov Monge–Ampère pinch for optimal quadratic transport maps.** Let `X` be
bounded and open, `Y` bounded and convex, `0 < lam`, and `0 < m`, with `lam ≤ f ≤ Lam` almost
everywhere on `X` and `m ≤ g ≤ M` almost everywhere on `Y`, where `μ = (ρ.restrict X).withDensity f`
is a probability measure. Any optimal quadratic transport map `T` from `μ` to
`ν = (ρ.restrict Y).withDensity g` agrees `ρ.restrict X`-almost everywhere with the gradient of a
convex, lower semicontinuous `u : E → EReal` (never `⊥`) satisfying `0 < lam / M`,
`X ⊆ interior {x | u x ≠ ⊤}`, `∂u(x) ⊆ closure Y`, and the localised two-sided Aleksandrov pinch
`((lam / M : ℝ≥0) : ℝ≥0∞) • ρ.restrict Ω ≤ MA_u^Ω ≤ ((Lam / m : ℝ≥0) : ℝ≥0∞) • ρ.restrict Ω` on
every open convex subdomain `Ω ⊆ X`. -/
theorem exists_mongeAmpereMeasure_ite_bounds_of_isKantorovichOptimalTransportMap
    {X Y : Set E} {f g : E → ℝ≥0∞} {T : E → E} {lam Lam m M : ℝ≥0}
    (hX : IsOpen X) (hXb : Bornology.IsBounded X)
    (hY : Convex ℝ Y) (hYb : Bornology.IsBounded Y)
    (hf : AEMeasurable f (ρ.restrict X)) (hg : Measurable g)
    (hlam : 0 < lam) (hm : 0 < m)
    (hflo : ∀ᵐ x ∂ρ.restrict X, (lam : ℝ≥0∞) ≤ f x)
    (hfhi : ∀ᵐ x ∂ρ.restrict X, f x ≤ Lam)
    (hglo : ∀ᵐ y ∂ρ.restrict Y, (m : ℝ≥0∞) ≤ g y)
    (hghi : ∀ᵐ y ∂ρ.restrict Y, g y ≤ M)
    [IsProbabilityMeasure ((ρ.restrict X).withDensity f)]
    (hT : IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      ((ρ.restrict X).withDensity f) ((ρ.restrict Y).withDensity g) T) :
    0 < lam / M ∧
    ∃ u : E → EReal, Convex ℝ {p : E × ℝ | u p.1 ≤ p.2} ∧ LowerSemicontinuous u ∧
      (∀ x, u x ≠ ⊥) ∧
      (T =ᵐ[ρ.restrict X] ∇ fun x => (u x).toReal) ∧
      IsKantorovichOptimalTransportMap (fun z : E × E => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
        ((ρ.restrict X).withDensity f) ((ρ.restrict Y).withDensity g)
        (∇ fun x => (u x).toReal) ∧
      X ⊆ interior {x | u x ≠ ⊤} ∧ (∀ x, subdifferential (innerₗ E) u x ⊆ closure Y) ∧
      ((lam / M : ℝ≥0) : ℝ≥0∞) • ρ.restrict X ≤ (mongeAmpereMeasure ρ u).restrict X ∧
      (mongeAmpereMeasure ρ u).restrict X ≤ ((Lam / m : ℝ≥0) : ℝ≥0∞) • ρ.restrict X ∧
      ∀ (Ω : Set E) [DecidablePred (· ∈ Ω)], IsOpen Ω → Convex ℝ Ω → Ω ⊆ X →
        ((lam / M : ℝ≥0) : ℝ≥0∞) • ρ.restrict Ω ≤
          mongeAmpereMeasure ρ (fun y => if y ∈ Ω then ((u y).toReal : EReal) else ⊤) ∧
        mongeAmpereMeasure ρ (fun y => if y ∈ Ω then ((u y).toReal : EReal) else ⊤) ≤
          ((Lam / m : ℝ≥0) : ℝ≥0∞) • ρ.restrict Ω := by
  have : IsProbabilityMeasure ((ρ.restrict Y).withDensity g) := by
    refine ⟨?_⟩
    rw [← hT.toHasLaw.map_eq,
      map_apply₀ hT.toHasLaw.aemeasurable MeasurableSet.univ.nullMeasurableSet, preimage_univ,
      measure_univ]
  have hMpos : 0 < M := by
    by_contra! hM0
    have hMzero : M = 0 := nonpos_iff_eq_zero.1 hM0
    have hg0 : g =ᵐ[ρ.restrict Y] 0 :=
      hghi.mono fun _ hy => nonpos_iff_eq_zero.1 (by simpa [hMzero] using hy)
    have hν0 : ((ρ.restrict Y).withDensity g) univ = 0 := by
      simp [withDensity_congr_ae hg0]
    exact one_ne_zero (measure_univ.symm.trans hν0)
  have hfpos : ∀ᵐ x ∂ρ.restrict X, f x ≠ 0 :=
    hflo.mono fun _ hx => ne_of_gt ((ENNReal.coe_pos.2 hlam).trans_le hx)
  have hgpos : ∀ᵐ y ∂ρ.restrict Y, g y ≠ 0 :=
    hglo.mono fun _ hy => ne_of_gt ((ENNReal.coe_pos.2 hm).trans_le hy)
  obtain ⟨u, hconv, hlsc, hbot, hTu, hopt, hXD, hsubcl, -⟩ :=
    exists_mongeAmpereMeasure_eq_withDensity_div_of_isKantorovichOptimalTransportMap
      hX hY hf hg hfpos hgpos
      (transportCost_norm_sub_sq_div_two_ne_top_of_withDensity_isBounded hXb hYb) hT
  have hdom : ∀ᵐ x ∂(ρ.restrict X).withDensity f, u x ≠ ⊤ :=
    (withDensity_absolutelyContinuous (ρ.restrict X) f).ae_le <|
      ae_restrict_of_forall_mem hX.measurableSet fun _ hx => interior_subset (hXD hx)
  obtain ⟨-, -, hlo, hhi, hΩ⟩ := smul_restrict_le_mongeAmpereMeasure_and_le_smul_restrict
    hconv hbot hX hY hf hg (ENNReal.coe_ne_zero.2 hlam.ne') (ENNReal.coe_ne_zero.2 hm.ne')
    ENNReal.coe_ne_top hflo hfhi hglo hghi hdom hopt.toHasLaw
  rw [← ENNReal.coe_div hMpos.ne'] at hlo
  rw [← ENNReal.coe_div hm.ne'] at hhi
  refine ⟨div_pos hlam hMpos, u, hconv, hlsc, hbot, hTu, hopt, hXD, hsubcl, hlo, hhi,
    fun Ω _ hΩo hΩc hΩX => ?_⟩
  obtain ⟨h1, h2⟩ := hΩ Ω hΩo hΩc hΩX
  exact ⟨ENNReal.coe_div hMpos.ne' ▸ h1, ENNReal.coe_div hm.ne' ▸ h2⟩

end FiniteDimensional

/-! ### Sharpness of target convexity -/

section NonconvexCounterexample

/-- The potential `x ↦ x ^ 2 / 2 + |x|` on `ℝ` has convex real epigraph. -/
private lemma convex_epigraph_sq_div_two_add_abs :
    Convex ℝ {p : ℝ × ℝ | ((p.1 ^ 2 / 2 + |p.1| : ℝ) : EReal) ≤ p.2} := by
  have h : ConvexOn ℝ univ (fun x : ℝ => (2⁻¹ : ℝ) • x ^ 2 + ‖x‖) :=
    ((Even.convexOn_pow (𝕜 := ℝ) even_two).smul (by positivity)).add convexOn_univ_norm
  simpa only [smul_eq_mul, inv_mul_eq_div, Real.norm_eq_abs, EReal.coe_le_coe_iff, mem_univ,
    true_and] using h.convex_epigraph

/-- On `ℝ`, `y` belongs to `∂u(x)` for `u(x') = x' ^ 2 / 2 + |x'|` if and only if
`(x ^ 2 / 2 + |x|) + y * (x' - x) ≤ x' ^ 2 / 2 + |x'|` for every `x'`. -/
private lemma mem_subdifferential_sq_div_two_add_abs_iff {x y : ℝ} :
    y ∈ subdifferential (innerₗ ℝ) (fun x' : ℝ => ((x' ^ 2 / 2 + |x'| : ℝ) : EReal)) x ↔
      ∀ x' : ℝ, (x ^ 2 / 2 + |x|) + y * (x' - x) ≤ x' ^ 2 / 2 + |x'| := by
  simpa only [innerₗ_apply_apply, RCLike.inner_apply, conj_trivial] using
    mem_subdifferential_coe_iff (innerₗ ℝ) (fun t : ℝ => t ^ 2 / 2 + |t|) (x := x) (y := y)

/-- At `0`, the subdifferential of `u(x) = x ^ 2 / 2 + |x|` on `ℝ` is the interval `[-1, 1]`. -/
theorem subdifferential_sq_div_two_add_abs_zero :
    subdifferential (innerₗ ℝ) (fun x : ℝ => ((x ^ 2 / 2 + |x| : ℝ) : EReal)) 0 =
      Icc (-1 : ℝ) 1 := by
  ext y
  rw [mem_subdifferential_sq_div_two_add_abs_iff, mem_Icc]
  constructor
  · intro h
    refine ⟨by by_contra! hy; have h1 := h (y + 1)
               rw [abs_zero, sub_zero, abs_of_neg (by linarith)] at h1
               nlinarith [sq_nonneg (y + 1)],
            by by_contra! hy; have h1 := h (y - 1)
               rw [abs_zero, sub_zero, abs_of_pos (by linarith)] at h1
               nlinarith [sq_nonneg (y - 1)]⟩
  · rintro ⟨hy₁, hy₂⟩ x
    rw [abs_zero, sub_zero]
    have hxy : y * x ≤ |x| := (le_abs_self _).trans <| by
      simpa only [abs_mul, one_mul] using
        mul_le_mul_of_nonneg_right (abs_le.2 ⟨hy₁, hy₂⟩) (abs_nonneg x)
    nlinarith [sq_nonneg x]

/-- The unweighted Aleksandrov Monge–Ampère measure of `u(x) = x ^ 2 / 2 + |x|` on `ℝ` charges the
origin with mass `2`, so it has a nontrivial singular atom. -/
theorem mongeAmpereMeasure_sq_div_two_add_abs_singleton_zero :
    mongeAmpereMeasure (volume : Measure ℝ)
      (fun x : ℝ => ((x ^ 2 / 2 + |x| : ℝ) : EReal)) {0} = 2 := by
  set u : ℝ → EReal := fun x => ((x ^ 2 / 2 + |x| : ℝ) : EReal)
  have hdom : interior {x : ℝ | u x ≠ ⊤} = univ := by
    rw [eq_univ_of_forall (s := {x : ℝ | u x ≠ ⊤}) fun _ => EReal.coe_ne_top _, interior_univ]
  rw [mongeAmpereMeasure_apply volume convex_epigraph_sq_div_two_add_abs
    (fun _ => EReal.coe_ne_bot _) Measure.AbsolutelyContinuous.rfl (measurableSet_singleton 0),
    hdom, inter_univ, subgradientImage_singleton, subdifferential_sq_div_two_add_abs_zero,
    Real.volume_Icc]
  norm_num

/-- Away from `0`, `x ↦ x ^ 2 / 2 + |x|` is differentiable and its gradient is `x + 1` for `x > 0`
and `x - 1` for `x < 0`. -/
private lemma differentiableAt_and_gradient_sq_div_two_add_abs {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun x' : ℝ => (((x' ^ 2 / 2 + |x'| : ℝ) : EReal)).toReal) x ∧
      (∇ fun x' : ℝ => (((x' ^ 2 / 2 + |x'| : ℝ) : EReal)).toReal) x =
        if 0 < x then x + 1 else x - 1 := by
  set u : ℝ → EReal := fun x' => ((x' ^ 2 / 2 + |x'| : ℝ) : EReal)
  rcases lt_trichotomy 0 x with hpos | rfl | hneg
  · have hev : (fun x' : ℝ => (u x').toReal) =ᶠ[𝓝 x] fun x' => x' ^ 2 / 2 + x' :=
      eventually_of_mem (Ioi_mem_nhds hpos) fun x' hx' => by
        simp only [u, EReal.toReal_coe, abs_of_pos hx']
    have hdiff : DifferentiableAt ℝ (fun x' : ℝ => (u x').toReal) x :=
      hev.differentiableAt_iff.2 (by fun_prop)
    have hsub : x + 1 ∈ subdifferential (innerₗ ℝ) u x :=
      mem_subdifferential_sq_div_two_add_abs_iff.2 fun x' => by
        rw [abs_of_pos hpos]; nlinarith [sq_nonneg (x' - x), le_abs_self x']
    refine ⟨hdiff, ?_⟩
    split_ifs with h
    · exact gradient_toReal_eq_of_mem_subdifferential hsub
        (.of_forall fun _ => EReal.coe_ne_top _) hdiff
    · exact (h hpos).elim
  · exact (hx rfl).elim
  · have hev : (fun x' : ℝ => (u x').toReal) =ᶠ[𝓝 x] fun x' => x' ^ 2 / 2 - x' :=
      eventually_of_mem (Iio_mem_nhds hneg) fun x' hx' => by
        simp only [u, EReal.toReal_coe, abs_of_neg hx', ← sub_eq_add_neg]
    have hdiff : DifferentiableAt ℝ (fun x' : ℝ => (u x').toReal) x :=
      hev.differentiableAt_iff.2 (by fun_prop)
    have hsub : x - 1 ∈ subdifferential (innerₗ ℝ) u x :=
      mem_subdifferential_sq_div_two_add_abs_iff.2 fun x' => by
        rw [abs_of_neg hneg]; nlinarith [sq_nonneg (x' - x), neg_le_abs x']
    refine ⟨hdiff, ?_⟩
    split_ifs with h
    · exact (not_lt_of_gt hneg h).elim
    · exact gradient_toReal_eq_of_mem_subdifferential hsub
        (.of_forall fun _ => EReal.coe_ne_top _) hdiff

/-- The gradient of `x ↦ x ^ 2 / 2 + |x|` pushes `volume|_{(-1, 1)}` to
`volume|_{(-2, -1) ∪ (1, 2)}`. -/
private lemma map_gradient_sq_div_two_add_abs_restrict_Ioo :
    Measure.map (∇ fun x' : ℝ => (((x' ^ 2 / 2 + |x'| : ℝ) : EReal)).toReal)
      (volume.restrict (Ioo (-1 : ℝ) 1)) =
      volume.restrict (Ioo (-2 : ℝ) (-1) ∪ Ioo 1 2) := by
  set G := ∇ fun x' : ℝ => (((x' ^ 2 / 2 + |x'| : ℝ) : EReal)).toReal
  have hsplitX : volume.restrict (Ioo (-1 : ℝ) 1) =
      volume.restrict (Ioo (-1 : ℝ) 0) + volume.restrict (Ioo (0 : ℝ) 1) := by
    rw [← Ioo_union_Ico_eq_Ioo (by norm_num : (-1 : ℝ) < 0) zero_le_one,
      Measure.restrict_union
        (disjoint_left.2 fun _ (h1 : _ ∈ Ioo (-1 : ℝ) 0) (h2 : _ ∈ Ico 0 1) => h1.2.not_ge h2.1)
        measurableSet_Ico,
      Measure.restrict_congr_set Ioo_ae_eq_Ico.symm]
  have hshift (a b c : ℝ) (hcongr : G =ᵐ[volume.restrict (Ioo a b)] (· + c)) :
      Measure.map G (volume.restrict (Ioo a b)) = volume.restrict (Ioo (a + c) (b + c)) := by
    have hpre : (· + c) ⁻¹' Ioo (a + c) (b + c) = Ioo a b := by
      simp [preimage_add_const_Ioo]
    rw [Measure.map_congr hcongr, ← hpre,
      ← Measure.restrict_map (measurable_add_const c) measurableSet_Ioo, map_add_right_eq_self]
  have hneg := hshift (-1) 0 (-1) <| ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => by
    dsimp only [G]; rw [(differentiableAt_and_gradient_sq_div_two_add_abs hx.2.ne).2]
    split_ifs with h
    · exact (not_lt_of_gt hx.2 h).elim
    · exact sub_eq_add_neg x 1
  have hpos := hshift 0 1 1 <| ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => by
    dsimp only [G]; rw [(differentiableAt_and_gradient_sq_div_two_add_abs hx.1.ne').2]
    split_ifs with h
    · rfl
    · exact (h hx.1).elim
  norm_num at hneg hpos
  rw [hsplitX, Measure.map_add _ _ (measurable_gradient _), hneg, hpos,
    Measure.restrict_union (disjoint_left.2 fun _ hy₁ hy₂ => by linarith [hy₁.2, hy₂.1])
      measurableSet_Ioo]

/-- Probability and Kantorovich-optimality properties for the 1D split-interval potential
`u(x) = x ^ 2 / 2 + |x|`. -/
private lemma isProbabilityMeasure_and_optimal_sq_div_two_add_abs :
    let X : Set ℝ := Ioo (-1 : ℝ) 1
    let Y : Set ℝ := Ioo (-2 : ℝ) (-1) ∪ Ioo 1 2
    let μ : Measure ℝ := (volume.restrict X).withDensity fun _ => (2 : ℝ≥0∞)⁻¹
    let ν : Measure ℝ := (volume.restrict Y).withDensity fun _ => (2 : ℝ≥0∞)⁻¹
    let u : ℝ → EReal := fun x => ((x ^ 2 / 2 + |x| : ℝ) : EReal)
    IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
      HasLaw (∇ fun x => (u x).toReal) ν μ ∧
      IsKantorovichOptimalTransportMap
        (fun z : ℝ × ℝ => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν
        (∇ fun x => (u x).toReal) := by
  intro X Y μ ν u
  have hdisjY : Disjoint (Ioo (-2 : ℝ) (-1)) (Ioo (1 : ℝ) 2) :=
    disjoint_left.2 fun _ hy₁ hy₂ => by linarith [hy₁.2, hy₂.1]
  have hprobμ : IsProbabilityMeasure μ := ⟨by
    rw [show μ = (2 : ℝ≥0∞)⁻¹ • volume.restrict X from withDensity_const _, smul_apply,
      restrict_apply_univ, Real.volume_Ioo]
    norm_num [ENNReal.inv_mul_cancel]⟩
  have hprobν : IsProbabilityMeasure ν := ⟨by
    rw [show ν = (2 : ℝ≥0∞)⁻¹ • volume.restrict Y from withDensity_const _, smul_apply,
      restrict_apply_univ, measure_union hdisjY measurableSet_Ioo, Real.volume_Ioo,
      Real.volume_Ioo]
    norm_num [ENNReal.inv_mul_cancel]⟩
  have hlaw : HasLaw (∇ fun x => (u x).toReal) ν μ := ⟨(measurable_gradient _).aemeasurable, by
    rw [show μ = (2 : ℝ≥0∞)⁻¹ • volume.restrict X from withDensity_const _,
      show ν = (2 : ℝ≥0∞)⁻¹ • volume.restrict Y from withDensity_const _,
      Measure.map_smul _ (measurable_gradient _).aemeasurable,
      map_gradient_sq_div_two_add_abs_restrict_Ioo]⟩
  have hμρ : μ ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans (absolutelyContinuous_of_le restrict_le_self)
  have hdiff : ∀ᵐ x ∂μ, u x ≠ ⊤ ∧ DifferentiableAt ℝ (fun x' => (u x').toReal) x := by
    have h0ae : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := (mem_ae_iff (s := ({0} : Set ℝ)ᶜ)).2 (by simp)
    exact hμρ.ae_le (h0ae.mono fun _ hx0 =>
      ⟨EReal.coe_ne_top _, (differentiableAt_and_gradient_sq_div_two_add_abs hx0).1⟩)
  have hν2 : MemLp id 2 ν := MemLp.of_bound aemeasurable_id.aestronglyMeasurable 2 <|
    (withDensity_absolutelyContinuous _ _).ae_le <|
      ae_restrict_of_forall_mem (measurableSet_Ioo.union measurableSet_Ioo) fun y hy => by
        rcases hy with ⟨hy₁, hy₂⟩ | ⟨hy₁, hy₂⟩ <;> simp only [id_eq, Real.norm_eq_abs, abs_le] <;>
          exact ⟨by linarith, by linarith⟩
  have hμ2 : MemLp id 2 μ := MemLp.of_bound aemeasurable_id.aestronglyMeasurable 1 <|
    (withDensity_absolutelyContinuous _ _).ae_le <|
      ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => by
        simp only [id_eq, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact ⟨hprobμ, hprobν, hlaw, isKantorovichOptimalTransportMap_gradient hμ2 hν2
    convex_epigraph_sq_div_two_add_abs (fun _ => EReal.coe_ne_bot _) hdiff hlaw⟩

/-- **Sharpness of target convexity for Aleksandrov solutions.** Let `X = (-1, 1)` and
`Y = (-2, -1) ∪ (1, 2)` on `ℝ`, with uniform probability laws
`μ = (volume.restrict X).withDensity (fun _ => 2⁻¹)` and
`ν = (volume.restrict Y).withDensity (fun _ => 2⁻¹)` (so both densities equal `1 / 2` on their
domains), and let `u(x) = x ^ 2 / 2 + |x|`. Then `u` is convex and never `⊥`, its gradient is a
Kantorovich-optimal quadratic transport map from `μ` to `ν`, `u` solves the weak (Brenier) equation
`MA_{u,ν} = μ` and satisfies the unconditional lower bound `volume.restrict X ≤ MA_u`, yet
`∂u(X)` is not contained in `closure Y` and `(MA_u).restrict X` is not absolutely continuous with
respect to Lebesgue measure (it has an atom of mass `2` at `0`). -/
theorem isKantorovichOptimalTransportMap_sq_div_two_add_abs_and_not_absolutelyContinuous :
    let X : Set ℝ := Ioo (-1 : ℝ) 1
    let Y : Set ℝ := Ioo (-2 : ℝ) (-1) ∪ Ioo 1 2
    let μ : Measure ℝ := (volume.restrict X).withDensity fun _ => (2 : ℝ≥0∞)⁻¹
    let ν : Measure ℝ := (volume.restrict Y).withDensity fun _ => (2 : ℝ≥0∞)⁻¹
    let u : ℝ → EReal := fun x => ((x ^ 2 / 2 + |x| : ℝ) : EReal)
    IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
      Convex ℝ {p : ℝ × ℝ | u p.1 ≤ p.2} ∧ (∀ x, u x ≠ ⊥) ∧
      IsKantorovichOptimalTransportMap
        (fun z : ℝ × ℝ => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν
        (∇ fun x => (u x).toReal) ∧
      mongeAmpereMeasure ν u = μ ∧
      volume.restrict X ≤ mongeAmpereMeasure volume u ∧
      ¬subgradientImage (innerₗ ℝ) u X ⊆ closure Y ∧
      ¬(mongeAmpereMeasure volume u).restrict X ≪ volume := by
  intro X Y μ ν u
  obtain ⟨hprobμ, hprobν, hlaw, hopt⟩ := isProbabilityMeasure_and_optimal_sq_div_two_add_abs
  have hμρ : μ ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans (absolutelyContinuous_of_le restrict_le_self)
  have hνρ : ν ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans (absolutelyContinuous_of_le restrict_le_self)
  have hMA : mongeAmpereMeasure ν u = μ :=
    ((hasLaw_gradient_and_ae_ne_top_iff_mongeAmpereMeasure_eq_and_ae_mem_subgradientImage
      convex_epigraph_sq_div_two_add_abs (fun _ => EReal.coe_ne_bot _) hμρ hνρ).1
      ⟨hlaw, .of_forall fun _ => EReal.coe_ne_top _⟩).1
  have hlo : volume.restrict X ≤ mongeAmpereMeasure volume u := by
    have h := smul_restrict_le_mongeAmpereMeasure (f := u) (lam := 2⁻¹) (M := 2⁻¹)
      convex_epigraph_sq_div_two_add_abs (fun _ => EReal.coe_ne_bot _)
      aemeasurable_const measurable_const (.of_forall fun _ => le_rfl) (.of_forall fun _ => le_rfl)
      (.of_forall fun _ => EReal.coe_ne_top _) hlaw
    have hdiv : (2 : ℝ≥0∞)⁻¹ / (2 : ℝ≥0∞)⁻¹ = 1 :=
      ENNReal.div_self (by norm_num) (by norm_num)
    simpa only [hdiv, one_smul] using h
  have hnot_sub : ¬subgradientImage (innerₗ ℝ) u X ⊆ closure Y := by
    intro hsub
    have h0mem : (0 : ℝ) ∈ subgradientImage (innerₗ ℝ) u X := by
      refine (mem_subgradientImage_iff _).2 ⟨0, by simp [X], ?_⟩
      rw [subdifferential_sq_div_two_add_abs_zero]
      exact ⟨by norm_num, by norm_num⟩
    obtain ⟨y, hyY, hydist⟩ := Metric.mem_closure_iff.1 (hsub h0mem) 1 one_pos
    rcases hyY with ⟨_, hy₂⟩ | ⟨hy₁, _⟩ <;>
      simp only [Real.dist_eq, zero_sub, abs_neg] at hydist <;>
      linarith [le_abs_self y, neg_le_abs y]
  have hnot_ac : ¬(mongeAmpereMeasure volume u).restrict X ≪ volume := by
    intro hac
    have h0 : ((mongeAmpereMeasure volume u).restrict X) {0} = 0 := hac (measure_singleton 0)
    rw [Measure.restrict_apply (measurableSet_singleton 0),
      inter_eq_left.2 (singleton_subset_iff.2 (by simp [X] : (0 : ℝ) ∈ X)),
      mongeAmpereMeasure_sq_div_two_add_abs_singleton_zero] at h0
    norm_num at h0
  exact ⟨hprobμ, hprobν, convex_epigraph_sq_div_two_add_abs, fun _ => EReal.coe_ne_bot _,
    hopt, hMA, hlo, hnot_sub, hnot_ac⟩

end NonconvexCounterexample

end TauCeti
