/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Basic
public import Mathlib.Probability.HasLaw
import TauCeti.Analysis.Convex.GradientCluster
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Weighted Monge–Ampère measures of transport potentials

Let `E` be a finite-dimensional real inner product space, `f : E → EReal` convex (convex real
epigraph, never `⊥`) with `D` the interior of its effective domain, and let `μ` and `ν` be
measures on `E` with `ν` absolutely continuous with respect to an additive Haar measure. The
weighted Monge–Ampère measure `MA_{f,ν}(s) = ν(∂f(s ∩ D))` (`TauCeti.mongeAmpereMeasure ν f`)
gives the weak sense in which `f` solves the transport equation `g₁(∇f) det D²f = g₀` for
densities `μ = g₀ dx` and `ν = g₁ dy`: then `MA_{f,ν}(s) = ∫_{∂f(s ∩ D)} g₁`, and the equation
`MA_{f,ν} = μ` says `∫_{∂f(s ∩ D)} g₁ = ∫_s g₀` for every measurable `s`, without dividing by
`g₁(∇f)` or differentiating `∇f`.

This file shows that a transport map selecting subgradients of `f` makes `f` a weak solution:
if `T x ∈ ∂f(x)` for `μ`-almost every `x`, `μ` is carried by `D`, and `T` pushes `μ` to `ν`,
then `MA_{f,ν} = μ` (`TauCeti.mongeAmpereMeasure_eq_of_hasLaw`). Absolute continuity of `ν` is
what makes the subgradient images of disjoint sets `ν`-almost disjoint: almost no point is a
subgradient at two distinct points (`TauCeti.measure_setOf_exists_ne_mem_subdifferential_eq_zero`),
so `T⁻¹(∂f(s ∩ D))` agrees with `s` up to a `μ`-null set.

Conversely, if `μ` is absolutely continuous as well and `ν` is carried by the subgradient image
`∂f(D)`, then `MA_{f,ν} = μ` forces the gradient of `f` to push `μ` to `ν`
(`TauCeti.hasLaw_gradient_of_mongeAmpereMeasure_eq`). The coverage hypothesis cannot be dropped:
`MA_{f,ν}` does not see the part of `ν` outside `∂f(D)`. Together, these characterise the
potentials whose gradient pushes an absolutely continuous `μ` to an absolutely continuous `ν`
(`TauCeti.hasLaw_gradient_and_ae_ne_top_iff_mongeAmpereMeasure_eq_and_ae_mem_subgradientImage`).
Applied to the potential of Brenier's theorem, this says that the Brenier potential is a weak
solution of its transport equation
(`TauCeti.exists_isKantorovichOptimalTransportMap_gradient_and_mongeAmpereMeasure_eq`, in
`TauCeti.MeasureTheory.OptimalTransport.Brenier`).

A weak solution need not be an *Aleksandrov* solution, one whose unweighted measure
`MA_f(s) = ρ(∂f(s ∩ D))`, for an additive Haar measure `ρ`, is `g₀ / g₁(∇f) dx`. Because
`g⁻¹ (g ρ) ≤ ρ`, the lower inequality `(g ∘ T)⁻¹ μ ≤ MA_f` holds unconditionally for any target
set, with no convexity or finiteness assumption on `g`
(`TauCeti.withDensity_inv_le_mongeAmpereMeasure`,
`TauCeti.withDensity_div_le_mongeAmpereMeasure`). For `ν = g ρ` with `g` finite almost everywhere,
the transport identity holds for every weight `h`, `MA_{f, h ν} = h (T x) μ`, and splitting `ρ`
into `g⁻¹ ν` and its restriction to `{g = 0}` gives

  `MA_f = (g ∘ T)⁻¹ μ + MA_{f, ρ|{g = 0}}`.

The second term is subgradient mass that the target does not see, and it vanishes (globally or on
a measurable source set `X`) exactly when `∂f(D) ∩ {g = 0}` or `∂f(X ∩ D) ∩ {g = 0}` is `ρ`-null.
When `μ = f₀ ρ|_X` has almost-everywhere positive density on an open set `X` and `∇f` pushes `μ`
to `g ρ|_Y` on a convex set `Y` where `0 < g < ∞` almost everywhere, Rockafellar's gradient-cluster
theorem forces `X ⊆ D` and `∂f(X) ⊆ closure Y` automatically, so `(MA_f)|_X = (f₀ / g ∘ ∇f) ρ|_X`
for *every* such transporting convex potential
(`TauCeti.subgradientImage_subset_and_restrict_mongeAmpereMeasure_eq_withDensity_div`).

## Main statements

* `TauCeti.mongeAmpereMeasure_eq_of_hasLaw` — a transport map from `μ` to `ν` selecting
  subgradients of `f` gives `MA_{f,ν} = μ`;
* `TauCeti.hasLaw_gradient_of_mongeAmpereMeasure_eq` — for absolutely continuous `μ`, if
  `MA_{f,ν} = μ` and `ν` is carried by `∂f(D)`, the gradient of `f` pushes `μ` to `ν`;
* `TauCeti.hasLaw_gradient_and_ae_ne_top_iff_mongeAmpereMeasure_eq_and_ae_mem_subgradientImage` —
  for absolutely continuous `μ` and `ν`, the gradient of `f` pushes `μ` to `ν` with `f` finite
  `μ`-almost everywhere exactly when `MA_{f,ν} = μ` and `ν` is carried by `∂f(D)`;
* `TauCeti.mongeAmpereMeasure_withDensity_eq_of_hasLaw` — the weighted identity
  `MA_{f, h ν} = h (T x) μ`;
* `TauCeti.withDensity_inv_le_mongeAmpereMeasure`,
  `TauCeti.withDensity_div_le_mongeAmpereMeasure`, and
  `TauCeti.smul_restrict_le_mongeAmpereMeasure` — the unconditional lower bound
  `(g ∘ T)⁻¹ μ ≤ MA_f`, needing no convexity or measurability of the source or target sets;
* `TauCeti.mongeAmpereMeasure_eq_withDensity_inv_add` — for `ν = g ρ`, the decomposition
  `MA_f = (g ∘ T)⁻¹ μ + MA_{f, ρ|{g = 0}}`;
* `TauCeti.mongeAmpereMeasure_eq_withDensity_inv_iff` and
  `TauCeti.restrict_mongeAmpereMeasure_eq_withDensity_inv_iff` — `f` is an Aleksandrov solution
  globally or on a measurable set `X` exactly when the subgradient image meets `{g = 0}` in a null
  set;
* `TauCeti.mongeAmpereMeasure_eq_withDensity_inv_of_convex` and
  `TauCeti.restrict_mongeAmpereMeasure_eq_withDensity_inv_of_convex` — this holds when the slopes
  lie in the closure of a convex set on which `g` is positive almost everywhere;
* `TauCeti.subgradientImage_subset_and_restrict_mongeAmpereMeasure_eq_withDensity_div` and
  `TauCeti.smul_restrict_le_mongeAmpereMeasure_and_le_smul_restrict` — when `∇f` pushes `f₀ ρ|_X`
  on an open `X` (`f₀ > 0` a.e.) to `g ρ|_Y` on a convex `Y` (`0 < g < ∞` a.e.), `X ⊆ D`,
  `∂f(X) ⊆ closure Y`, and `(MA_f)|_X = (f₀ / g ∘ ∇f) ρ|_X`, giving the two-sided Aleksandrov
  pinch `(lam / M) • ρ|_X ≤ (MA_f)|_X ≤ (Lam / m) • ρ|_X` when `lam ≤ f₀ ≤ Lam` and `m ≤ g ≤ M`.

## References

* A. Figalli, *The Monge–Ampère Equation and Its Applications*, Zurich Lectures in Advanced
  Mathematics, EMS, 2017, §4.6, for Brenier solutions of the second boundary value problem and
  their relation to Aleksandrov solutions.
* L. A. Caffarelli, *The regularity of mappings with a convex potential*, J. Amer. Math. Soc. 5
  (1992), 99–104, for Aleksandrov solutions from a convex target.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §4.1.
-/

public section

noncomputable section

open MeasureTheory Measure Set Filter ProbabilityTheory
open scoped Topology Gradient ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure] {μ ν : Measure E}
  {f : E → EReal}

/-- **A transport map selecting subgradients gives a weak solution of the Monge–Ampère
equation.** Let `f : E → EReal` be convex and never `⊥` on a finite-dimensional real inner
product space, with `D` the interior of its effective domain, and let `ν` be absolutely continuous
with respect to an additive Haar measure. If `T` pushes `μ` to `ν`, `μ` is carried by `D`, and
`T x ∈ ∂f(x)` for `μ`-almost every `x`, then the Monge–Ampère measure of `f` weighted by `ν` is
`μ`: `ν(∂f(s ∩ D)) = μ(s)` for every measurable `s`. -/
theorem mongeAmpereMeasure_eq_of_hasLaw (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) (hν : ν ≪ ρ) {T : E → E} (hT : HasLaw T ν μ)
    (hD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    (hsub : ∀ᵐ x ∂μ, T x ∈ subdifferential (innerₗ E) f x) :
    mongeAmpereMeasure ν f = μ := by
  set D := interior {x | f x ≠ ⊤}
  -- Almost no value of `T` is a subgradient at two distinct points, since `ν` is absolutely
  -- continuous.
  have hN : ∀ᵐ x ∂μ, ¬∃ x₁ x₂, x₁ ≠ x₂ ∧ T x ∈ subdifferential (innerₗ E) f x₁ ∧
      T x ∈ subdifferential (innerₗ E) f x₂ := by
    refine ae_of_ae_map (p := fun y => ¬∃ x₁ x₂, x₁ ≠ x₂ ∧ y ∈ subdifferential (innerₗ E) f x₁ ∧
      y ∈ subdifferential (innerₗ E) f x₂) hT.aemeasurable ?_
    rw [hT.map_eq]
    exact measure_eq_zero_iff_ae_notMem.1
      (hν (measure_setOf_exists_ne_mem_subdifferential_eq_zero ρ f))
  ext s hs
  have hm := (nullMeasurableSet_subgradientImage hf ρ hs).mono_ac hν
  rw [mongeAmpereMeasure_apply ν hf hbot hν hs, ← hT.map_eq,
    map_apply₀ hT.aemeasurable (hT.map_eq ▸ hm)]
  -- Up to a `μ`-null set, `T x` is a subgradient at a point of `s ∩ D` exactly when `x ∈ s`.
  refine measure_congr (eventuallyEqSet_iff.2 ?_)
  filter_upwards [hD, hsub, hN] with x hxD hx hxN
  simp only [mem_preimage, mem_subgradientImage_iff]
  refine ⟨fun ⟨x', hx', hTx⟩ => ?_, fun hxs => ⟨x, ⟨hxs, hxD⟩, hx⟩⟩
  by_contra hxs
  exact hxN ⟨x', x, fun h => hxs (h ▸ hx'.1), hTx, hx⟩

/-- **A weak solution of the Monge–Ampère equation transports by its gradient.** Let
`f : E → EReal` be convex and never `⊥` on a finite-dimensional real inner product space, with
`D` the interior of its effective domain, and let `μ` and `ν` be absolutely continuous with
respect to an additive Haar measure. If the Monge–Ampère measure of `f` weighted by `ν` is `μ`
and `ν`-almost every point is a subgradient of `f` at a point of `D`, then the gradient of the
real representative of `f` pushes `μ` to `ν`. -/
theorem hasLaw_gradient_of_mongeAmpereMeasure_eq (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hMA : mongeAmpereMeasure ν f = μ)
    (hcov : ∀ᵐ y ∂ν, y ∈ subgradientImage (innerₗ E) f (interior {x | f x ≠ ⊤})) :
    HasLaw (∇ fun x => (f x).toReal) ν μ := by
  set D := interior {x | f x ≠ ⊤}
  set G := ∇ fun x => (f x).toReal
  -- The set `S` of points of `D` where the real representative is differentiable carries `μ`,
  -- by Rademacher's theorem, since `μ = MA_{f,ν}` is carried by `D`.
  set S := D ∩ {x | DifferentiableAt ℝ (fun x' => (f x').toReal) x}
  have hSm : MeasurableSet S :=
    isOpen_interior.measurableSet.inter (measurableSet_of_differentiableAt ℝ _)
  have hSc : μ Sᶜ = 0 := by
    have hDc : μ Dᶜ = 0 := hMA ▸ mongeAmpereMeasure_compl_interior ν
    refine measure_mono_null (fun x hx => ?_)
      (measure_union_null hDc (ae_iff.1 (hμ.ae_le (ae_eventually_ne_top_and_differentiableAt_toReal
        (μ := ρ) hf hbot))))
    by_cases hxD : x ∈ D
    · exact Or.inr fun h => hx ⟨hxD, (h (interior_subset hxD : f x ≠ ⊤)).2⟩
    · exact Or.inl hxD
  -- On `S` the subdifferential is the gradient.
  have hG : ∀ x ∈ S, ∀ y, y ∈ subdifferential (innerₗ E) f x ↔ y = G x := fun x hx y =>
    ⟨fun hy => (gradient_toReal_eq_of_mem_subdifferential hy (mem_interior_iff_mem_nhds.1 hx.1)
        hx.2).symm,
      fun hy => hy ▸ gradient_toReal_mem_subdifferential hf hbot (interior_subset hx.1) hx.2⟩
  -- `ν` is carried by the subgradient image of `S`, since that of `D \ S` has `ν`-measure
  -- `μ (D \ S) = 0`.
  have hcovS : ∀ᵐ y ∂ν, y ∈ subgradientImage (innerₗ E) f S := by
    have h₀ : ν (subgradientImage (innerₗ E) f (Sᶜ ∩ D)) = 0 := by
      rw [← mongeAmpereMeasure_apply ν hf hbot hν hSm.compl, hMA, hSc]
    filter_upwards [hcov, measure_eq_zero_iff_ae_notMem.1 h₀] with y hy hy₀
    obtain ⟨x, hxD, hxy⟩ := (mem_subgradientImage_iff _).1 hy
    by_cases hxS : x ∈ S
    · exact (mem_subgradientImage_iff _).2 ⟨x, hxS, hxy⟩
    · exact (hy₀ ((mem_subgradientImage_iff _).2 ⟨x, ⟨hxS, hxD⟩, hxy⟩)).elim
  have hGm : Measurable G := measurable_gradient _
  refine ⟨hGm.aemeasurable, ext fun B hB => ?_⟩
  -- `μ (G⁻¹ B) = MA_{f,ν} (G⁻¹ B ∩ S) = ν (∂f (G⁻¹ B ∩ S)) = ν (B ∩ ∂f(S)) = ν B`.
  have himage : subgradientImage (innerₗ E) f ((G ⁻¹' B ∩ S) ∩ D) =
      B ∩ subgradientImage (innerₗ E) f S := by
    ext y
    simp only [mem_subgradientImage_iff, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨x, ⟨⟨hxB, hxS⟩, -⟩, hy⟩
      exact ⟨(hG x hxS y).1 hy ▸ hxB, x, hxS, hy⟩
    · rintro ⟨hyB, x, hxS, hy⟩
      exact ⟨x, ⟨⟨(hG x hxS y).1 hy ▸ hyB, hxS⟩, hxS.1⟩, hy⟩
  calc Measure.map G μ B = μ (G ⁻¹' B ∩ S) := by rw [map_apply hGm hB, measure_inter_conull hSc]
    _ = ν (B ∩ subgradientImage (innerₗ E) f S) := by
      rw [← himage, ← mongeAmpereMeasure_apply ν hf hbot hν ((hGm hB).inter hSm), hMA]
    _ = ν B := measure_inter_conull (mem_ae_iff.1 hcovS)

/-- **Weak solutions of the Monge–Ampère equation are the transporting potentials.** Let
`f : E → EReal` be convex and never `⊥` on a finite-dimensional real inner product space, with
`D` the interior of its effective domain, and let `μ` and `ν` be absolutely continuous with
respect to an additive Haar measure. The gradient of the real representative of `f` pushes `μ`
to `ν`, with `f` finite `μ`-almost everywhere, exactly when the Monge–Ampère measure of `f`
weighted by `ν` is `μ` and `ν`-almost every point is a subgradient of `f` at a point of `D`. -/
theorem hasLaw_gradient_and_ae_ne_top_iff_mongeAmpereMeasure_eq_and_ae_mem_subgradientImage
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) (hμ : μ ≪ ρ) (hν : ν ≪ ρ) :
    HasLaw (∇ fun x => (f x).toReal) ν μ ∧ (∀ᵐ x ∂μ, f x ≠ ⊤) ↔
      mongeAmpereMeasure ν f = μ ∧
        ∀ᵐ y ∂ν, y ∈ subgradientImage (innerₗ E) f (interior {x | f x ≠ ⊤}) := by
  constructor
  · rintro ⟨hT, hdom⟩
    -- By Rademacher's theorem, `μ`-almost every point is in `D`, where `f` is differentiable
    -- and its gradient is a subgradient.
    have hdiff : ∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧
        DifferentiableAt ℝ (fun x' => (f x').toReal) x := by
      filter_upwards [hμ.ae_le (ae_eventually_ne_top_and_differentiableAt_toReal hf hbot), hdom]
        with x hx hx' using hx hx'
    have hD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤} := by
      filter_upwards [hdiff] with x hx using mem_interior_iff_mem_nhds.2 hx.1
    have hsub : ∀ᵐ x ∂μ, (∇ fun x => (f x).toReal) x ∈ subdifferential (innerₗ E) f x := by
      filter_upwards [hdiff] with x hx
      exact gradient_toReal_mem_subdifferential hf hbot hx.1.self_of_nhds hx.2
    refine ⟨mongeAmpereMeasure_eq_of_hasLaw hf hbot hν hT hD hsub, ?_⟩
    -- `ν`-almost every point is the image of a point of `D` under the gradient.
    have hm : NullMeasurableSet (subgradientImage (innerₗ E) f (univ ∩ interior {x | f x ≠ ⊤}))
        (Measure.map (∇ fun x => (f x).toReal) μ) :=
      hT.map_eq ▸ (nullMeasurableSet_subgradientImage hf ρ MeasurableSet.univ).mono_ac hν
    rw [univ_inter] at hm
    rw [← hT.map_eq]
    refine (mem_ae_iff (s := subgradientImage (innerₗ E) f (interior {x | f x ≠ ⊤}))).2 ?_
    rw [map_apply₀ hT.aemeasurable hm.compl]
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 (hD.and hsub))
    exact fun h => hx ((mem_subgradientImage_iff _).2 ⟨x, h⟩)
  · rintro ⟨hMA, hcov⟩
    refine ⟨hasLaw_gradient_of_mongeAmpereMeasure_eq hf hbot hμ hν hMA hcov, ?_⟩
    rw [← hMA]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (mongeAmpereMeasure_compl_interior ν (f := f))]
      with x hx
    exact interior_subset (notMem_compl_iff.1 hx)


/-! ### Aleksandrov solutions -/

/-- **A transport map selecting subgradients computes the weighted Monge–Ampère measures.** Let
`f : E → EReal` be convex and never `⊥`, with `D` the interior of its effective domain, and let
`ν` be absolutely continuous with respect to an additive Haar measure. If `T` pushes `μ` to `ν`,
`μ` is carried by `D`, and `T x ∈ ∂f(x)` for `μ`-almost every `x`, then for every measurable
weight `h` the Monge–Ampère measure of `f` weighted by `h ν` is `h (T x) μ`:
`∫_{∂f(s ∩ D)} h dν = ∫_s h (T x) dμ` for every measurable `s`. -/
theorem mongeAmpereMeasure_withDensity_eq_of_hasLaw (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) (hν : ν ≪ ρ) {T : E → E} (hT : HasLaw T ν μ)
    (hD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    (hsub : ∀ᵐ x ∂μ, T x ∈ subdifferential (innerₗ E) f x) {h : E → ℝ≥0∞} (hh : Measurable h) :
    mongeAmpereMeasure (ν.withDensity h) f = μ.withDensity fun x => h (T x) := by
  -- Replace `T` by a measurable representative `T'`; it carries `h (T' x) μ` to `h ν`.
  set T' := hT.aemeasurable.mk T
  have hTT' : T =ᵐ[μ] T' := hT.aemeasurable.ae_eq_mk
  have hlaw : HasLaw T' (ν.withDensity h) (μ.withDensity fun x => h (T' x)) := by
    refine ⟨hT.aemeasurable.measurable_mk.aemeasurable,
      (map_withDensity_comp hT.aemeasurable.measurable_mk hh).trans
        (by rw [(hT.congr hTT'.symm).map_eq])⟩
  have hac := withDensity_absolutelyContinuous μ fun x => h (T' x)
  have hcongr : (μ.withDensity fun x => h (T x)) = μ.withDensity fun x => h (T' x) :=
    withDensity_congr_ae (by filter_upwards [hTT'] with x hx; rw [hx])
  rw [hcongr]
  refine mongeAmpereMeasure_eq_of_hasLaw hf hbot ((withDensity_absolutelyContinuous ν h).trans hν)
    hlaw (hac.ae_le hD) (hac.ae_le ?_)
  filter_upwards [hsub, hTT'] with x hx hx'
  rwa [← hx']

/-- **The Aleksandrov measure of a transporting potential.** Let `f : E → EReal` be convex and
never `⊥`, with `D` the interior of its effective domain, let `ρ` be an additive Haar measure, and
let `g` be a measurable density, finite almost everywhere. If `T` pushes `μ` to `g ρ`, `μ` is
carried by `D`, and `T x ∈ ∂f(x)` for `μ`-almost every `x`, then the Aleksandrov Monge–Ampère
measure of `f` is

  `MA_f = (g ∘ T)⁻¹ μ + MA_{f, ρ|{g = 0}}`,

where the second term `s ↦ ρ(∂f(s ∩ D) ∩ {g = 0})` is the subgradient mass that falls where the
target density vanishes. For `μ = g₀ ρ` the first term is the right-hand side `g₀ / g(∇f)` of the
Monge–Ampère equation `det D²f = g₀ / g(∇f)`. -/
theorem mongeAmpereMeasure_eq_withDensity_inv_add (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {g : E → ℝ≥0∞} (hg : Measurable g) (hgtop : ∀ᵐ y ∂ρ, g y ≠ ⊤)
    {T : E → E} (hT : HasLaw T (ρ.withDensity g) μ) (hD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    (hsub : ∀ᵐ x ∂μ, T x ∈ subdifferential (innerₗ E) f x) :
    mongeAmpereMeasure ρ f =
      μ.withDensity (fun x => (g (T x))⁻¹) + mongeAmpereMeasure (ρ.restrict {y | g y = 0}) f := by
  have hν := withDensity_absolutelyContinuous ρ g
  have hZ : MeasurableSet {y | g y = 0} := hg (measurableSet_singleton 0)
  -- `ρ` is `g⁻¹ (g ρ)` on `{g ≠ 0}` plus its restriction to `{g = 0}`.
  have hsplit : ρ = (ρ.withDensity g).withDensity g⁻¹ + ρ.restrict {y | g y = 0} := by
    have hpos : (ρ.withDensity g).withDensity g⁻¹ = ρ.restrict {y | g y = 0}ᶜ := by
      rw [← withDensity_mul ρ hg hg.inv, ← withDensity_indicator_one hZ.compl]
      refine withDensity_congr_ae ?_
      filter_upwards [hgtop] with y hy
      by_cases h0 : g y = 0
      · simp [h0]
      · simp [h0, ENNReal.mul_inv_cancel h0 hy]
    rw [hpos, add_comm, restrict_add_restrict_compl hZ]
  conv_lhs => rw [hsplit]
  rw [mongeAmpereMeasure_add ((withDensity_absolutelyContinuous _ _).trans hν)
      (absolutelyContinuous_of_le restrict_le_self),
    mongeAmpereMeasure_withDensity_eq_of_hasLaw hf hbot hν hT hD hsub hg.inv]
  simp only [Pi.inv_apply]

/-- **When a transporting potential is an Aleksandrov solution.** Let `f : E → EReal` be convex
and never `⊥`, with `D` the interior of its effective domain, let `ρ` be an additive Haar measure,
and let `g` be a measurable density, finite almost everywhere. If `T` pushes `μ` to `g ρ`, `μ` is
carried by `D`, and `T x ∈ ∂f(x)` for `μ`-almost every `x`, then `f` is an Aleksandrov solution
of the Monge–Ampère equation `MA_f = (g ∘ T)⁻¹ μ` exactly when the subgradient image of `D` meets
the zero set of the target density in a null set. Subgradient mass where `g` vanishes is the
zero-density remainder of `mongeAmpereMeasure_eq_withDensity_inv_add`, invisible to the weighted
transport equation `MA_{f, g ρ} = μ`, and it is exactly the obstruction. -/
theorem mongeAmpereMeasure_eq_withDensity_inv_iff (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {g : E → ℝ≥0∞} (hg : Measurable g) (hgtop : ∀ᵐ y ∂ρ, g y ≠ ⊤)
    {T : E → E} (hT : HasLaw T (ρ.withDensity g) μ) (hD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    (hsub : ∀ᵐ x ∂μ, T x ∈ subdifferential (innerₗ E) f x) :
    mongeAmpereMeasure ρ f = μ.withDensity (fun x => (g (T x))⁻¹) ↔
      ρ (subgradientImage (innerₗ E) f (interior {x | f x ≠ ⊤}) ∩ {y | g y = 0}) = 0 := by
  have hZ : MeasurableSet {y | g y = 0} := hg (measurableSet_singleton 0)
  have hsing : mongeAmpereMeasure (ρ.restrict {y | g y = 0}) f univ =
      ρ (subgradientImage (innerₗ E) f (interior {x | f x ≠ ⊤}) ∩ {y | g y = 0}) := by
    rw [mongeAmpereMeasure_apply _ hf hbot (absolutelyContinuous_of_le restrict_le_self)
      MeasurableSet.univ, univ_inter, restrict_apply' hZ]
  have hσ := sigmaFinite_mongeAmpereMeasure ρ f
  have hsplit := mongeAmpereMeasure_eq_withDensity_inv_add hf hbot hg hgtop hT hD hsub
  rw [← hsing, measure_univ_eq_zero]
  refine ⟨fun h => ?_, fun h => by rw [hsplit, h, add_zero]⟩
  -- `MA_f` is σ-finite, so the absolutely continuous part can be cancelled.
  have : SigmaFinite (μ.withDensity fun x => (g (T x))⁻¹) := by rw [← h]; exact hσ
  exact (Measure.add_right_inj _ _ 0).1 (hsplit.symm.trans (h.trans (add_zero _).symm))

/-- **Transporting potentials with slopes in a convex target are Aleksandrov solutions.** Let
`f : E → EReal` be convex and never `⊥`, with `D` the interior of its effective domain, let `ρ` be
an additive Haar measure, and let `g` be a measurable density, finite almost everywhere. Suppose
`T` pushes `μ` to `g ρ`, `μ` is carried by `D`, and `T x ∈ ∂f(x)` for `μ`-almost every `x`. If every
subgradient of `f` at a point of `D` lies in the closure of a convex set `Y` on which `g` is
almost everywhere positive, then `f` is an Aleksandrov solution of `MA_f = (g ∘ T)⁻¹ μ`.
Convexity enters because the frontier of a convex set is null. -/
theorem mongeAmpereMeasure_eq_withDensity_inv_of_convex
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {g : E → ℝ≥0∞}
    (hg : Measurable g) (hgtop : ∀ᵐ y ∂ρ, g y ≠ ⊤) {T : E → E} (hT : HasLaw T (ρ.withDensity g) μ)
    (hD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    (hsub : ∀ᵐ x ∂μ, T x ∈ subdifferential (innerₗ E) f x) {Y : Set E} (hY : Convex ℝ Y)
    (hsubY : subgradientImage (innerₗ E) f (interior {x | f x ≠ ⊤}) ⊆ closure Y)
    (hgY : ∀ᵐ y ∂ρ, y ∈ Y → g y ≠ 0) :
    mongeAmpereMeasure ρ f = μ.withDensity fun x => (g (T x))⁻¹ := by
  refine (mongeAmpereMeasure_eq_withDensity_inv_iff hf hbot hg hgtop hT hD hsub).2
    (measure_mono_null ?_ (measure_union_null (hY.addHaar_frontier ρ) (ae_iff.1 hgY)))
  rintro y ⟨hy, hy0⟩
  by_cases hyY : y ∈ Y
  · exact Or.inr fun h => h hyY hy0
  · exact Or.inl ⟨hsubY hy, fun h => hyY (interior_subset h)⟩

/-- **Unconditional lower bound on the Aleksandrov measure of a transporting potential.** Let
`f : E → EReal` be convex and never `⊥`, with `D` the interior of its effective domain, let `ρ` be
an additive Haar measure, and let `g` be a measurable density. If `T` pushes `μ` to `g ρ`, `μ` is
carried by `D`, and `T x ∈ ∂f(x)` for `μ`-almost every `x`, then `(g ∘ T)⁻¹ μ ≤ MA_f` holds with no
convexity assumption on the support of `g` and no finiteness assumption on `g`. -/
theorem withDensity_inv_le_mongeAmpereMeasure (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {g : E → ℝ≥0∞} (hg : Measurable g)
    {T : E → E} (hT : HasLaw T (ρ.withDensity g) μ) (hD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    (hsub : ∀ᵐ x ∂μ, T x ∈ subdifferential (innerₗ E) f x) :
    μ.withDensity (fun x => (g (T x))⁻¹) ≤ mongeAmpereMeasure ρ f := by
  have hle := mongeAmpereMeasure_mono (f := f) (withDensity_inv_same_le hg.aemeasurable)
    (Measure.AbsolutelyContinuous.rfl : ρ ≪ ρ)
  rwa [mongeAmpereMeasure_withDensity_eq_of_hasLaw hf hbot (withDensity_absolutelyContinuous ρ g)
    hT hD hsub hg.inv] at hle

/-- **Unconditional density lower bound for a transporting gradient.** Let `f : E → EReal` be
convex and never `⊥`, let `X` and `Y` be arbitrary subsets of `E` (neither need be measurable, open,
or convex), let `f₀` be almost-everywhere measurable on `ρ.restrict X`, and let `g` be measurable.
If `f` is finite almost everywhere for `μ = (ρ.restrict X).withDensity f₀` and `∇ (f ·).toReal`
pushes `μ` to `ν = (ρ.restrict Y).withDensity g`, then `(f₀ / g ∘ ∇f) ρ|_X ≤ MA_f`. -/
theorem withDensity_div_le_mongeAmpereMeasure {X Y : Set E} {f₀ g : E → ℝ≥0∞}
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hf₀ : AEMeasurable f₀ (ρ.restrict X)) (hg : Measurable g)
    (hdom : ∀ᵐ x ∂(ρ.restrict X).withDensity f₀, f x ≠ ⊤)
    (hT : HasLaw (∇ fun x => (f x).toReal)
      ((ρ.restrict Y).withDensity g) ((ρ.restrict X).withDensity f₀)) :
    (ρ.restrict X).withDensity (fun x => f₀ x / g ((∇ fun x' => (f x').toReal) x)) ≤
      mongeAmpereMeasure ρ f := by
  set G := ∇ fun x => (f x).toReal
  set μ' := (ρ.restrict X).withDensity f₀
  set ν' := (ρ.restrict Y).withDensity g
  have hμ'ρ : μ' ≪ ρ :=
    (withDensity_absolutelyContinuous _ _).trans (absolutelyContinuous_of_le restrict_le_self)
  have hν'ρ : ν' ≪ ρ :=
    (withDensity_absolutelyContinuous _ _).trans (absolutelyContinuous_of_le restrict_le_self)
  have hdiff : ∀ᵐ x ∂μ', (∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧
      DifferentiableAt ℝ (fun x' => (f x').toReal) x := by
    filter_upwards [hμ'ρ.ae_le (ae_eventually_ne_top_and_differentiableAt_toReal hf hbot), hdom]
      with x hx hx' using hx hx'
  have hD : ∀ᵐ x ∂μ', x ∈ interior {x | f x ≠ ⊤} :=
    hdiff.mono fun _ hx => mem_interior_iff_mem_nhds.2 hx.1
  have hsub : ∀ᵐ x ∂μ', G x ∈ subdifferential (innerₗ E) f x :=
    hdiff.mono fun _ hx => gradient_toReal_mem_subdifferential hf hbot hx.1.self_of_nhds hx.2
  have hle : ν'.withDensity g⁻¹ ≤ ρ :=
    (withDensity_inv_same_le hg.aemeasurable).trans restrict_le_self
  have hMA := mongeAmpereMeasure_mono (f := f) hle (Measure.AbsolutelyContinuous.rfl : ρ ≪ ρ)
  rw [mongeAmpereMeasure_withDensity_eq_of_hasLaw hf hbot hν'ρ hT hD hsub hg.inv] at hMA
  have hmul : μ'.withDensity (g⁻¹ ∘ G) =
      (ρ.restrict X).withDensity (fun x => f₀ x / g (G x)) := by
    rw [← withDensity_mul₀ hf₀ (hg.inv.comp (measurable_gradient _)).aemeasurable]
    exact withDensity_congr_ae (.of_forall fun _ => (div_eq_mul_inv _ _).symm)
  exact hmul ▸ hMA

/-- **Localised Aleksandrov solution criterion on a measurable set.** Under the hypotheses of
`TauCeti.mongeAmpereMeasure_eq_withDensity_inv_add`, for any measurable `X` the restricted identity
`(MA_f)|_X = ((g ∘ T)⁻¹ μ)|_X` holds if and only if `∂f(X ∩ D) ∩ {g = 0}` is `ρ`-null. -/
theorem restrict_mongeAmpereMeasure_eq_withDensity_inv_iff
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {g : E → ℝ≥0∞}
    (hg : Measurable g) (hgtop : ∀ᵐ y ∂ρ, g y ≠ ⊤) {T : E → E} (hT : HasLaw T (ρ.withDensity g) μ)
    (hD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    (hsub : ∀ᵐ x ∂μ, T x ∈ subdifferential (innerₗ E) f x) {X : Set E} (hX : MeasurableSet X) :
    (mongeAmpereMeasure ρ f).restrict X = (μ.withDensity fun x => (g (T x))⁻¹).restrict X ↔
      ρ (subgradientImage (innerₗ E) f (X ∩ interior {x | f x ≠ ⊤}) ∩ {y | g y = 0}) = 0 := by
  have hZ : MeasurableSet {y | g y = 0} := hg (measurableSet_singleton 0)
  have hsing : (mongeAmpereMeasure (ρ.restrict {y | g y = 0}) f).restrict X univ =
      ρ (subgradientImage (innerₗ E) f (X ∩ interior {x | f x ≠ ⊤}) ∩ {y | g y = 0}) := by
    rw [restrict_apply_univ,
      mongeAmpereMeasure_apply _ hf hbot (absolutelyContinuous_of_le restrict_le_self) hX,
      restrict_apply' hZ]
  have hsplit := congrArg (fun m : Measure E => m.restrict X)
    (mongeAmpereMeasure_eq_withDensity_inv_add hf hbot hg hgtop hT hD hsub)
  rw [restrict_add] at hsplit
  have hσ : SigmaFinite ((mongeAmpereMeasure ρ f).restrict X) := by
    have := sigmaFinite_mongeAmpereMeasure ρ f
    infer_instance
  rw [← hsing, measure_univ_eq_zero]
  refine ⟨fun h => ?_, fun h => by rw [hsplit, h, add_zero]⟩
  have : SigmaFinite ((μ.withDensity fun x => (g (T x))⁻¹).restrict X) := h ▸ hσ
  exact (Measure.add_right_inj _ _ 0).1 (hsplit.symm.trans (h.trans (add_zero _).symm))

/-- **Localised Aleksandrov solution for slopes in a convex target.** Under the hypotheses of
`TauCeti.restrict_mongeAmpereMeasure_eq_withDensity_inv_iff`, if `∂f(X ∩ D)` lies in the closure of
a convex set `Y` on which `g` is almost everywhere positive, then `(MA_f)|_X = ((g ∘ T)⁻¹ μ)|_X`. -/
theorem restrict_mongeAmpereMeasure_eq_withDensity_inv_of_convex
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {g : E → ℝ≥0∞}
    (hg : Measurable g) (hgtop : ∀ᵐ y ∂ρ, g y ≠ ⊤) {T : E → E} (hT : HasLaw T (ρ.withDensity g) μ)
    (hD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    (hsub : ∀ᵐ x ∂μ, T x ∈ subdifferential (innerₗ E) f x) {X Y : Set E} (hX : MeasurableSet X)
    (hY : Convex ℝ Y) (hsubY : subgradientImage (innerₗ E) f (X ∩ interior {x | f x ≠ ⊤}) ⊆
      closure Y) (hgY : ∀ᵐ y ∂ρ, y ∈ Y → g y ≠ 0) :
    (mongeAmpereMeasure ρ f).restrict X = (μ.withDensity fun x => (g (T x))⁻¹).restrict X := by
  refine (restrict_mongeAmpereMeasure_eq_withDensity_inv_iff hf hbot hg hgtop hT hD hsub hX).2
    (measure_mono_null ?_ (measure_union_null (hY.addHaar_frontier ρ) (ae_iff.1 hgY)))
  rintro y ⟨hy, hy0⟩
  by_cases hyY : y ∈ Y
  · exact Or.inr fun h => h hyY hy0
  · exact Or.inl ⟨hsubY hy, fun h => hyY (interior_subset h)⟩

/-- **Every gradient transporting an open domain to a convex target solves the Aleksandrov
Monge–Ampère equation on the domain.** Let `f : E → EReal` be convex and never `⊥`, let `X` be open
and `Y` convex (neither need be bounded, `X` need not be convex, and `Y` need not be open, closed,
or Borel measurable). Let `μ = (ρ.restrict X).withDensity f₀` with `f₀ ≠ 0` almost everywhere on
`X`, and `ν = (ρ.restrict Y).withDensity g` with `0 < g < ∞` almost everywhere on `Y`. If `f` is
finite `μ`-almost everywhere and `∇ (f ·).toReal` pushes `μ` to `ν`, then automatically `X` lies in
the interior of the effective domain of `f`, `∂f(X) ⊆ closure Y`, and
`(MA_f)|_X = (f₀ / g ∘ ∇f) ρ|_X`. -/
theorem subgradientImage_subset_and_restrict_mongeAmpereMeasure_eq_withDensity_div
    {X Y : Set E} {f₀ g : E → ℝ≥0∞} (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) (hX : IsOpen X) (hY : Convex ℝ Y)
    (hf₀ : AEMeasurable f₀ (ρ.restrict X)) (hg : Measurable g)
    (hf₀pos : ∀ᵐ x ∂ρ.restrict X, f₀ x ≠ 0) (hgpos : ∀ᵐ y ∂ρ.restrict Y, g y ≠ 0)
    (hgtop : ∀ᵐ y ∂ρ.restrict Y, g y ≠ ∞)
    (hdom : ∀ᵐ x ∂(ρ.restrict X).withDensity f₀, f x ≠ ⊤)
    (hT : HasLaw (∇ fun x => (f x).toReal)
      ((ρ.restrict Y).withDensity g) ((ρ.restrict X).withDensity f₀)) :
    X ⊆ interior {x | f x ≠ ⊤} ∧ subgradientImage (innerₗ E) f X ⊆ closure Y ∧
      (mongeAmpereMeasure ρ f).restrict X =
        (ρ.restrict X).withDensity fun x => f₀ x / g ((∇ fun x' => (f x').toReal) x) := by
  set G := ∇ fun x => (f x).toReal
  set μ' := (ρ.restrict X).withDensity f₀
  -- Replace `Y` by `interior Y` up to `ρ`-null frontier so the target has measurable density `g'`.
  set g' := (interior Y).indicator g
  have hg'm : Measurable g' := hg.indicator isOpen_interior.measurableSet
  have hT' : HasLaw G (ρ.withDensity g') μ' :=
    hY.withDensity_restrict_eq_withDensity_indicator_interior ρ g ▸ hT
  -- Positivity of `f₀` transfers `μ'`-a.e. finiteness and target membership to `ρ`-a.e. on `X`.
  have hXμ : ρ.restrict X ≪ μ' := withDensity_absolutelyContinuous' hf₀ hf₀pos
  have hGint : ∀ᵐ x ∂μ', G x ∈ interior Y :=
    ae_of_ae_map hT.aemeasurable (hT.map_eq ▸ hY.ae_withDensity_restrict_mem_interior ρ g)
  obtain ⟨hXD, hsubY⟩ := subgradientImage_subset_closure_of_convex_of_ae_mem hf hbot hX hY
    (ae_imp_of_ae_restrict (hXμ.ae_le hdom))
    (ae_imp_of_ae_restrict (hXμ.ae_le (hGint.mono fun _ hx => interior_subset hx)))
  refine ⟨hXD, hsubY, ?_⟩
  -- Apply the localised convex-target theorem with `g'` on `Y` and simplify the density.
  have hμ'ρ : μ' ≪ ρ :=
    (withDensity_absolutelyContinuous _ _).trans (absolutelyContinuous_of_le restrict_le_self)
  have hdiff : ∀ᵐ x ∂μ', (∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧
      DifferentiableAt ℝ (fun x' => (f x').toReal) x := by
    filter_upwards [hμ'ρ.ae_le (ae_eventually_ne_top_and_differentiableAt_toReal hf hbot), hdom]
      with x hx hx' using hx hx'
  have hg'top : ∀ᵐ y ∂ρ, g' y ≠ ⊤ := by
    filter_upwards [ae_imp_of_ae_restrict hgtop] with y hy
    by_cases hyi : y ∈ interior Y
    · simpa [g', hyi] using hy (interior_subset hyi)
    · simp [g', hyi]
  have hg'pos : ∀ᵐ y ∂ρ, y ∈ Y → g' y ≠ 0 :=
    (hY.ae_mem_closure_imp_indicator_interior_ne_zero_iff.2 hgpos).mono fun _ h hy =>
      h (subset_closure hy)
  have hMA := restrict_mongeAmpereMeasure_eq_withDensity_inv_of_convex hf hbot hg'm hg'top hT'
    (hdiff.mono fun _ hx => mem_interior_iff_mem_nhds.2 hx.1)
    (hdiff.mono fun _ hx => gradient_toReal_mem_subdifferential hf hbot hx.1.self_of_nhds hx.2)
    hX.measurableSet hY ((subgradientImage_mono (innerₗ E) inter_subset_left).trans hsubY) hg'pos
  have hcongr : μ'.withDensity (fun x => (g' (G x))⁻¹) =
      (ρ.restrict X).withDensity (fun x => f₀ x / g (G x)) := by
    trans μ'.withDensity (g⁻¹ ∘ G)
    · exact withDensity_congr_ae (hGint.mono fun x hx => by simp [g', hx])
    · rw [← withDensity_mul₀ hf₀ (hg.inv.comp (measurable_gradient _)).aemeasurable]
      exact withDensity_congr_ae (.of_forall fun _ => (div_eq_mul_inv _ _).symm)
  rw [hMA, hcongr, restrict_withDensity hX.measurableSet, restrict_restrict hX.measurableSet,
    inter_self]

/-- **Unconditional constant-density lower bound on the Monge–Ampère measure.** For arbitrary
source and target sets `X` and `Y` (neither need be open, convex, or measurable), if `lam ≤ f₀`
almost everywhere on `X` and `g ≤ M` almost everywhere on `Y`, any convex potential `f` (never `⊥`,
finite `μ`-almost everywhere) whose gradient pushes `μ = (ρ.restrict X).withDensity f₀` to
`ν = (ρ.restrict Y).withDensity g` satisfies `(lam / M) • ρ.restrict X ≤ MA_f`. -/
theorem smul_restrict_le_mongeAmpereMeasure {X Y : Set E} {f₀ g : E → ℝ≥0∞} {lam M : ℝ≥0∞}
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hf₀ : AEMeasurable f₀ (ρ.restrict X)) (hg : Measurable g)
    (hf₀lo : ∀ᵐ x ∂ρ.restrict X, lam ≤ f₀ x) (hghi : ∀ᵐ y ∂ρ.restrict Y, g y ≤ M)
    (hdom : ∀ᵐ x ∂(ρ.restrict X).withDensity f₀, f x ≠ ⊤)
    (hT : HasLaw (∇ fun x => (f x).toReal)
      ((ρ.restrict Y).withDensity g) ((ρ.restrict X).withDensity f₀)) :
    (lam / M) • ρ.restrict X ≤ mongeAmpereMeasure ρ f := by
  by_cases hlam : lam = 0
  · simp [hlam, Measure.zero_le]
  have hXμ : ρ.restrict X ≪ (ρ.restrict X).withDensity f₀ :=
    withDensity_absolutelyContinuous' hf₀
      (hf₀lo.mono fun _ hx => ne_of_gt ((pos_iff_ne_zero.2 hlam).trans_le hx))
  have hνhi : ∀ᵐ y ∂(ρ.restrict Y).withDensity g, g y ≤ M :=
    (withDensity_absolutelyContinuous (ρ.restrict Y) g).ae_le hghi
  have hGhi : ∀ᵐ x ∂ρ.restrict X, g ((∇ fun x' => (f x').toReal) x) ≤ M :=
    hXμ.ae_le (ae_of_ae_map (p := fun y => g y ≤ M) hT.aemeasurable (hT.map_eq ▸ hνhi))
  calc (lam / M) • ρ.restrict X
      = (ρ.restrict X).withDensity (fun _ => lam / M) := (withDensity_const (lam / M)).symm
    _ ≤ (ρ.restrict X).withDensity (fun x => f₀ x / g ((∇ fun x' => (f x').toReal) x)) :=
        withDensity_mono (by
          filter_upwards [hf₀lo, hGhi] with x hx hy using ENNReal.div_le_div hx hy)
    _ ≤ mongeAmpereMeasure ρ f :=
        withDensity_div_le_mongeAmpereMeasure hf hbot hf₀ hg hdom hT

/-- **Two-sided Aleksandrov Monge–Ampère pinch for a convex target.** Let `X` be open and `Y`
convex, `0 < lam`, `0 < m`, and `M ≠ ∞`, with `lam ≤ f₀ ≤ Lam` almost everywhere on `X` and
`m ≤ g ≤ M` almost everywhere on `Y`. Every convex potential `f` (never `⊥`, finite `μ`-almost
everywhere) whose gradient pushes `μ = (ρ.restrict X).withDensity f₀` to
`ν = (ρ.restrict Y).withDensity g` satisfies `X ⊆ interior {x | f x ≠ ⊤}`, `∂f(X) ⊆ closure Y`, and
`(lam / M) • ρ.restrict X ≤ (MA_f).restrict X ≤ (Lam / m) • ρ.restrict X`, together with the
localised pinch on every open convex subdomain `Ω ⊆ X`. -/
theorem smul_restrict_le_mongeAmpereMeasure_and_le_smul_restrict
    {X Y : Set E} {f₀ g : E → ℝ≥0∞} {lam Lam m M : ℝ≥0∞}
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
    (hX : IsOpen X) (hY : Convex ℝ Y)
    (hf₀ : AEMeasurable f₀ (ρ.restrict X)) (hg : Measurable g)
    (hlam : lam ≠ 0) (hm : m ≠ 0) (hM : M ≠ ∞)
    (hf₀lo : ∀ᵐ x ∂ρ.restrict X, lam ≤ f₀ x) (hf₀hi : ∀ᵐ x ∂ρ.restrict X, f₀ x ≤ Lam)
    (hglo : ∀ᵐ y ∂ρ.restrict Y, m ≤ g y) (hghi : ∀ᵐ y ∂ρ.restrict Y, g y ≤ M)
    (hdom : ∀ᵐ x ∂(ρ.restrict X).withDensity f₀, f x ≠ ⊤)
    (hT : HasLaw (∇ fun x => (f x).toReal)
      ((ρ.restrict Y).withDensity g) ((ρ.restrict X).withDensity f₀)) :
    X ⊆ interior {x | f x ≠ ⊤} ∧ subgradientImage (innerₗ E) f X ⊆ closure Y ∧
      (lam / M) • ρ.restrict X ≤ (mongeAmpereMeasure ρ f).restrict X ∧
      (mongeAmpereMeasure ρ f).restrict X ≤ (Lam / m) • ρ.restrict X ∧
      ∀ (Ω : Set E) [DecidablePred (· ∈ Ω)], IsOpen Ω → Convex ℝ Ω → Ω ⊆ X →
        (lam / M) • ρ.restrict Ω ≤
          mongeAmpereMeasure ρ (fun y => if y ∈ Ω then ((f y).toReal : EReal) else ⊤) ∧
        mongeAmpereMeasure ρ (fun y => if y ∈ Ω then ((f y).toReal : EReal) else ⊤) ≤
          (Lam / m) • ρ.restrict Ω := by
  have hf₀pos : ∀ᵐ x ∂ρ.restrict X, f₀ x ≠ 0 :=
    hf₀lo.mono fun _ hx => ne_of_gt ((pos_iff_ne_zero.2 hlam).trans_le hx)
  have hgpos : ∀ᵐ y ∂ρ.restrict Y, g y ≠ 0 :=
    hglo.mono fun _ hy => ne_of_gt ((pos_iff_ne_zero.2 hm).trans_le hy)
  have hgtop : ∀ᵐ y ∂ρ.restrict Y, g y ≠ ∞ :=
    hghi.mono fun _ hy => ne_top_of_le_ne_top hM hy
  obtain ⟨hXD, hsubY, hMA⟩ :=
    subgradientImage_subset_and_restrict_mongeAmpereMeasure_eq_withDensity_div
      hf hbot hX hY hf₀ hg hf₀pos hgpos hgtop hdom hT
  have hXμ : ρ.restrict X ≪ (ρ.restrict X).withDensity f₀ :=
    withDensity_absolutelyContinuous' hf₀ hf₀pos
  have hνbd : ∀ᵐ y ∂(ρ.restrict Y).withDensity g, m ≤ g y ∧ g y ≤ M :=
    (withDensity_absolutelyContinuous (ρ.restrict Y) g).ae_le (hglo.and hghi)
  have hGbd : ∀ᵐ x ∂ρ.restrict X,
      m ≤ g ((∇ fun x' => (f x').toReal) x) ∧ g ((∇ fun x' => (f x').toReal) x) ≤ M :=
    hXμ.ae_le (ae_of_ae_map (p := fun y => m ≤ g y ∧ g y ≤ M) hT.aemeasurable (hT.map_eq ▸ hνbd))
  have hlo : (lam / M) • ρ.restrict X ≤ (mongeAmpereMeasure ρ f).restrict X := by
    rw [hMA, ← withDensity_const (lam / M)]
    exact withDensity_mono (by
      filter_upwards [hf₀lo, hGbd] with x hx hy using ENNReal.div_le_div hx hy.2)
  have hhi : (mongeAmpereMeasure ρ f).restrict X ≤ (Lam / m) • ρ.restrict X := by
    rw [hMA, ← withDensity_const (Lam / m)]
    exact withDensity_mono (by
      filter_upwards [hf₀hi, hGbd] with x hx hy using ENNReal.div_le_div hx hy.1)
  refine ⟨hXD, hsubY, hlo, hhi, fun Ω _ hΩo hΩc hΩX => ?_⟩
  rw [mongeAmpereMeasure_ite_toReal_eq_restrict ρ hf hbot hΩo hΩc
    (hΩX.trans (hXD.trans interior_subset))]
  have hloΩ := Measure.restrict_mono (s := Ω) subset_rfl hlo
  have hhiΩ := Measure.restrict_mono (s := Ω) subset_rfl hhi
  simp only [Measure.restrict_smul, restrict_restrict_of_subset hΩX] at hloΩ hhiΩ
  exact ⟨hloΩ, hhiΩ⟩

end TauCeti
