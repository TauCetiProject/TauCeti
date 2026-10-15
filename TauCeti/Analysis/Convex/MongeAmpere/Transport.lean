/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Basic
public import Mathlib.Probability.HasLaw
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
`MA_f(s) = ρ(∂f(s ∩ D))`, for an additive Haar measure `ρ`, is `g₀ / g₁(∇f) dx`. For `ν = g ρ` with
`g` finite almost everywhere, the transport identity holds for every weight `h`,
`MA_{f, h ν} = h (T x) μ`, and splitting `ρ` into `g⁻¹ ν` and its restriction to `{g = 0}` gives

  `MA_f = (g ∘ T)⁻¹ μ + MA_{f, ρ|{g = 0}}`.

The second term is subgradient mass that the target does not see, and it vanishes exactly when
`ρ(∂f(D) ∩ {g = 0}) = 0`. This holds when every slope of `f` lies in the closure of a convex set
on which `g` is positive almost everywhere, because the frontier of a convex set is null. The
Brenier corollary is
`TauCeti.exists_isKantorovichOptimalTransportMap_gradient_and_mongeAmpereMeasure_eq_withDensity`,
in `TauCeti.MeasureTheory.OptimalTransport.Brenier`.

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
* `TauCeti.mongeAmpereMeasure_eq_withDensity_inv_add` — for `ν = g ρ`, the decomposition
  `MA_f = (g ∘ T)⁻¹ μ + MA_{f, ρ|{g = 0}}`;
* `TauCeti.mongeAmpereMeasure_eq_withDensity_inv_iff` — `f` is an Aleksandrov solution of
  `MA_f = (g ∘ T)⁻¹ μ` exactly when `ρ(∂f(D) ∩ {g = 0}) = 0`;
* `TauCeti.mongeAmpereMeasure_eq_withDensity_inv_of_convex` — this holds when the slopes of `f`
  lie in the closure of a convex set on which `g` is positive almost everywhere.

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
  have hm := (nullMeasurableSet_subgradientImage hf hbot ρ hs).mono_ac hν
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
      hT.map_eq ▸ (nullMeasurableSet_subgradientImage hf hbot ρ MeasurableSet.univ).mono_ac hν
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
      map_withDensity_eq_withDensity hT.aemeasurable.measurable_mk measurable_one hh ?_
        (ae_of_all _ fun x => one_mul _)⟩
    rw [withDensity_one]
    exact (hT.congr hTT'.symm).map_eq
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

end TauCeti
