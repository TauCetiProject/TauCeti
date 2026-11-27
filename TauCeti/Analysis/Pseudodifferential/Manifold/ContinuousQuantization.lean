/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.BesselPotentialSpace
public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol.Topology
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Manifold.SymbolQuantization
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.LocalizedChangeOfVariables
import TauCeti.Geometry.Manifold.Sobolev.ChartReading

/-!
# Continuous quantization of principal symbols on a compact manifold

Let `M` be a compact manifold modelled on `ℝⁿ`, with the Sobolev spaces `H^s(M)` of a chart
partition (`TauCeti.chartSobolevSpace`), to which every classical pseudodifferential operator `P`
of order `m` extends as a bounded operator `H^s(M) → H^t(M)`, `t ≤ s - m`
(`TauCeti.chartSobolevExtension`). This file shows that the quantization of principal symbols

`Q(σ) = ∑ᵢ Op_{cᵢ}(χ(η) θᵢ(y) σ(cᵢ⁻¹ y, ⟪η, ·⟫ ∘ dcᵢ))`

(`TauCeti.principalSymbolQuantization`), where the chart quantization `Op_{cᵢ}` is localized by
cutoffs `ρᵢ` and `θᵢ`, is continuous for the `C^∞` topology of homogeneous symbols on compact sets
of positions times the unit sphere of frequencies, read in charts, and the operator norm of
`H^s(M) → H^t(M)`. This linear map inverts the principal symbol map, `σ_m(Q(σ)) = σ`, when
`θᵢ = 1` on the support of `ρᵢ` and the `ρᵢ ∘ cᵢ` add up to `1`. As a consequence, a continuous
family `σ_y` of principal symbols, for instance a homotopy of elliptic symbols, lifts to a family of
classical pseudodifferential operators `P_y` with `σ_m(P_y) = σ_y`, continuous in the operator
norm, which starts at any prescribed operator `P₀` with principal symbol `σ_{y₀}`: take
`P_y = Q(σ_y) + P₀ - Q(σ_{y₀})`.

## The argument

The estimate behind all of this is that the extension of a single chart quantization `Op_e(a)`,
localized by cutoffs `φ` and `ψ` in a chart `e`, is bounded by a continuous seminorm of the symbol
`a`, for all symbols vanishing at positions outside a fixed compact set `K`
(`OpenPartialHomeomorph.exists_norm_chartSobolevExtension_chartQuantization_le`). Indeed,
`Op_e(a) u` is `(φ · Op(a) w) ∘ e` for the reading `w = ψ · (u ∘ e⁻¹)` of `u` in `e`,
so

* its reading in another chart `e'` is a localized change of variables of `φ · Op(a) w`, bounded
  in `H^t` by a constant independent of `a`
  (`TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le`);
* multiplication by `φ` is bounded on `H^t`, and `‖Op(a) w‖_{H^{s - m}} ≤ q(a) ‖w‖_{H^s}` for a
  continuous seminorm `q` on the symbols of order `m`
  (`TauCeti.Symbol.exists_norm_quantizeUniformBesselPotentialSpace_le_seminorm`);
* the reading `w` of `u` in `e` is bounded in `H^s` by the readings of `u` in the chart partition
  (`TauCeti.exists_norm_chartReading_le`).

Since `Op_e(a)` is additive in `a`, the extension is then continuous in `a`
(`OpenPartialHomeomorph.continuous_chartSobolevExtension_chartQuantization`). The cut-off term
`χ(ξ) h(x, ξ)` depends continuously on the homogeneous symbol `h`
(`TauCeti.HomogeneousSymbol.continuous_cutoffSymbol`), which gives the continuity of `Q`.

## Main results

* `OpenPartialHomeomorph.exists_norm_chartSobolevExtension_chartQuantization_le`: the operator norm
  of the extension of `Op_e(a)` is bounded by a continuous seminorm of `a`.
* `OpenPartialHomeomorph.continuous_chartSobolevExtension_chartQuantization`: a continuous family
  of symbols with a common compact spatial support has a continuous family of extensions.
* `TauCeti.continuous_chartSobolevExtension_principalSymbolQuantization`: the quantization of a
  family of principal symbols whose chart readings are continuous is continuous in the operator
  norm.
* `TauCeti.exists_linearMap_classicalPrincipalSymbol_eq_and_continuous`: on a compact manifold
  there is a linear map `Q` from principal symbols to classical pseudodifferential operators with
  `σ_m(Q(σ)) = σ`, continuous in the above sense.
* `TauCeti.exists_classicalPrincipalSymbol_eq_and_continuous_chartSobolevExtension`: continuous
  families of principal symbols lift to continuous families of operators with a prescribed initial
  value.

## References

* R. Melrose, *Introduction to Microlocal Analysis*, §5.3, Proposition 5.2 and its proof,
  (5.35)–(5.36) (the quantization of principal symbols by patching and its continuity).
* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §5 (continuous families of symbols and operators).
-/

public section

noncomputable section

open Set TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace

namespace OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M) {m : ℝ}
  {ι κ : Type*} [Fintype ι] [Fintype κ] {c : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {ψ : ∀ i, 𝓓(⟨(c i).target, (c i).open_target⟩, ℝ)}
  {c' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc' : ∀ j, c' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {φ : ∀ j, 𝓓(⟨(c' j).target, (c' j).open_target⟩, ℝ)} {s t : ℝ}

include he

/-- The reading in a chart `e'` through `φ'` of a chart quantization `Op_e(a) u` is bounded in `H^t`
by `C q₀(a) ‖w‖_{H^s}`, for the reading `w` of `u` in `e` and any seminorm `q₀` bounding the
Euclidean operators `Op(a) : H^s → H^{s - m}` on the symbols vanishing at positions outside `K`. -/
private theorem exists_norm_cutoffPushforwardSchwartz_chartQuantization_le
    {e' : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) (φ₀ ψ₀ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    {K : TopologicalSpace.Compacts (CoordinateSpace n)} {q₀ : Seminorm ℂ (Symbol n ℂ ℂ m)}
    (hq₀ : ∀ (a : Symbol n ℂ ℂ m) (ha : a.HasCompactSpatialSupport),
      (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) →
        ‖a.quantizeUniformBesselPotentialSpace ha.isUniform s 2‖ ≤ q₀ a) (ht : t ≤ s - m) :
    ∃ C, 0 ≤ C ∧ ∀ a : ClassicalSymbol n ℂ ℂ m, (∀ x ∉ K, ∀ ξ, a.toSymbol.coefficient (x, ξ) = 0) →
      ∀ u, ‖SchwartzMap.toBesselPotentialSpaceCLM t 2
          (e'.cutoffPushforwardSchwartz he' φ' (e.chartQuantization he φ₀ ψ₀ a u))‖ ≤
        C * (q₀ a.toSymbol *
          ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (e.cutoffPushforwardSchwartz he ψ₀ u)‖) := by
  -- Multiplication by `φ₀` is bounded on `H^t`.
  obtain ⟨Cφ, hCφ⟩ := BesselPotentialSpace.exists_norm_toBesselPotentialSpaceCLM_le_of_eq_smul_comp
    (F := ℂ) (e := OpenPartialHomeomorph.refl (CoordinateSpace n)) (by simpa using contDiffOn_id)
    (by simpa using contDiffOn_id) φ₀.contDiff φ₀.hasCompactSupport (by simp) ENNReal.one_lt_two
    ENNReal.ofNat_ne_top t
  -- Reading `φ₀ · G` in the chart `e'` is bounded by its reading in `e`.
  obtain ⟨B, hB⟩ := exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le he'
    he φ' φ₀ ENNReal.one_lt_two ENNReal.ofNat_ne_top t
  -- A cutoff `θ` equal to `1` on the support of `φ₀`.
  obtain ⟨θ, hθ, -⟩ := TestFunction.exists_eventually_eq_one (Ω := ⟨e.target, e.open_target⟩)
    (n := ⊤) φ₀.hasCompactSupport.isCompact φ₀.tsupport_subset
  have hθ' (y : CoordinateSpace n) (hy : y ∈ tsupport φ₀) : θ y = 1 := hθ.self_of_nhdsSet y hy
  refine ⟨|B| * |Cφ|, by positivity, fun a haK u ↦ ?_⟩
  have ha : a.toSymbol.HasCompactSpatialSupport :=
    Symbol.hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK⟩
  set w := e.cutoffPushforwardSchwartz he ψ₀ u
  set g := e.complexCutoffPullback he θ (ContMDiffMap.ofContDiff
    (quantizeSchwartzValue a.toSymbol.coefficient w) (a.toSymbol.contDiff_quantizeSchwartzValue _))
  -- `‖φ₀ · Op(a) w‖_{H^t} ≤ |Cφ| q₀(a) ‖w‖_{H^s}`.
  have hG : ‖SchwartzMap.toBesselPotentialSpaceCLM t 2 (e.cutoffPushforwardSchwartz he φ₀ g)‖ ≤
      |Cφ| * (q₀ a.toSymbol * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 w‖) := by
    refine (hCφ (Symbol.quantizeUniformCLM a.toSymbol ha.isUniform w) _ fun y ↦ ?_).trans
      (mul_le_mul (le_abs_self _) ?_ (norm_nonneg _) (abs_nonneg _))
    · rw [cutoffPushforwardSchwartz_complexCutoffPullback_apply_of_eq_one he hθ',
        ContMDiffMap.coe_ofContDiff, OpenPartialHomeomorph.refl_apply, id,
        Symbol.quantizeUniformCLM_apply]
    · rw [← BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM ht,
        ← ha.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM s ENNReal.one_lt_two
          ENNReal.ofNat_ne_top]
      exact (BesselPotentialSpace.norm_inclusion_apply_le ht _).trans
        ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hq₀ _ ha haK) (norm_nonneg _)))
  rw [← mulLeft_complexCutoffPullback_eq_chartQuantization he hθ', mul_assoc]
  exact (hB g).trans (mul_le_mul (le_abs_self _) hG (norm_nonneg _) (abs_nonneg _))

/-- **A chart quantization is bounded by a seminorm of its symbol.** Let `φ₀` and `ψ₀` be cutoffs in
a chart `e`, `K` a compact set of positions, `ψᵢ` cutoffs in charts `cᵢ` whose readings on `M` add
up to `1`, and `φⱼ` finitely many cutoffs in charts `c'ⱼ`. For `t ≤ s - m` there is a continuous
seminorm `q` on the symbols of order `m` such that for every classical symbol `a` of order `m`
vanishing at positions outside `K` and every smooth `u` on `M`, the chart quantization `Op_e(a)`
localized by `φ₀` and `ψ₀` satisfies

`‖(φⱼ · ((Op_e(a) u) ∘ c'ⱼ⁻¹))ⱼ‖_{⨁ H^t} ≤ q(a) ‖(ψᵢ · (u ∘ cᵢ⁻¹))ᵢ‖_{⨁ H^s}`. -/
theorem exists_norm_chartReading_chartQuantization_le (φ₀ ψ₀ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (K : TopologicalSpace.Compacts (CoordinateSpace n))
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1) (ht : t ≤ s - m) :
    ∃ q : Seminorm ℂ (Symbol n ℂ ℂ m), Continuous q ∧ ∀ a : ClassicalSymbol n ℂ ℂ m,
      (∀ x ∉ K, ∀ ξ, a.toSymbol.coefficient (x, ξ) = 0) → ∀ u,
        ‖chartReading hc' φ t (e.chartQuantization he φ₀ ψ₀ a u)‖ ≤
          q a.toSymbol * ‖chartReading hc ψ s u‖ := by
  -- The Euclidean bound `‖Op(a) w‖_{H^{s - m}} ≤ q₀(a) ‖w‖_{H^s}`.
  obtain ⟨q₀, hq₀, hq₀a⟩ := Symbol.exists_norm_quantizeUniformBesselPotentialSpace_le_seminorm
    (V := ℂ) (W := ℂ) (m := m) K s ENNReal.one_lt_two ENNReal.ofNat_ne_top
  -- Each reading of `Op_e(a) u` is bounded by the reading of `u` in `e`.
  choose C hC0 hC using fun j ↦
    exists_norm_cutoffPushforwardSchwartz_chartQuantization_le he (hc' j) (φ j) φ₀ ψ₀ hq₀a ht
  -- The reading of `u` in `e` is bounded by its readings in the partition.
  obtain ⟨D, hD⟩ := exists_norm_chartReading_le hc ψ (e' := fun _ : Unit ↦ e) (fun _ ↦ he)
    (fun _ ↦ ψ₀) hψ s
  have hC' : 0 ≤ (∑ j, C j) * |D| := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ hC0 j
    positivity
  refine ⟨((∑ j, C j) * |D|).toNNReal • q₀,
    by simpa [FunLike.coe_smul] using hq₀.const_smul ((∑ j, C j) * |D|).toNNReal,
    fun a haK u ↦ ?_⟩
  have hw : ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (e.cutoffPushforwardSchwartz he ψ₀ u)‖ ≤
      |D| * ‖chartReading hc ψ s u‖ := by
    have h := (PiLp.norm_apply_le (chartReading (fun _ : Unit ↦ he) (fun _ ↦ ψ₀) s u) ()).trans
      ((hD u).trans (mul_le_mul_of_nonneg_right (le_abs_self D) (norm_nonneg _)))
    simpa using h
  calc ‖chartReading hc' φ t (e.chartQuantization he φ₀ ψ₀ a u)‖
      ≤ ∑ j, ‖chartReading hc' φ t (e.chartQuantization he φ₀ ψ₀ a u) j‖ :=
        PiLp.norm_le_sum_norm _
    _ ≤ ∑ j, C j * (q₀ a.toSymbol * (|D| * ‖chartReading hc ψ s u‖)) :=
        Finset.sum_le_sum fun j _ ↦ by
          rw [chartReading_apply]
          exact (hC j a haK u).trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hw (apply_nonneg _ _)) (hC0 j))
    _ = (((∑ j, C j) * |D|).toNNReal • q₀) a.toSymbol * ‖chartReading hc ψ s u‖ := by
        rw [smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hC']
        simp only [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **The extension of a chart quantization is bounded by a seminorm of its symbol.** With the
notation of `OpenPartialHomeomorph.exists_norm_chartReading_chartQuantization_le`, there is a
continuous seminorm `q` on the symbols of order `m` such that the extension
`H^s(M) → H^t(M)` of the chart quantization `Op_e(a)` has operator norm at most `q(a)`, for every
classical symbol `a` of order `m` vanishing at positions outside `K`. -/
theorem exists_norm_chartSobolevExtension_chartQuantization_le
    (φ₀ ψ₀ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (K : TopologicalSpace.Compacts (CoordinateSpace n))
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1) (ht : t ≤ s - m) :
    ∃ q : Seminorm ℂ (Symbol n ℂ ℂ m), Continuous q ∧ ∀ a : ClassicalSymbol n ℂ ℂ m,
      (∀ x ∉ K, ∀ ξ, a.toSymbol.coefficient (x, ξ) = 0) →
        ‖chartSobolevExtension hc ψ hc' φ (e.chartQuantization he φ₀ ψ₀ a) s t‖ ≤ q a.toSymbol := by
  obtain ⟨q, hq, hqa⟩ := exists_norm_chartReading_chartQuantization_le (hc' := hc') (φ := φ) he φ₀
    ψ₀ K hψ ht
  exact ⟨q, hq, fun a haK ↦ ContinuousLinearMap.opNorm_le_bound _ (apply_nonneg _ _)
    (norm_chartSobolevExtension_apply_le (hqa a haK))⟩

/-- **Continuity of chart quantizations in the symbol.** If `y ↦ a y` is a continuous family of
classical symbols of order `m`, all vanishing at positions outside a fixed compact set `K`, then
the extensions `H^s(M) → H^t(M)`, `t ≤ s - m`, of the chart quantizations `Op_e(a y)` depend
continuously on `y` in the operator norm. -/
theorem continuous_chartSobolevExtension_chartQuantization [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
    (φ₀ ψ₀ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (K : TopologicalSpace.Compacts (CoordinateSpace n))
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1) (ht : t ≤ s - m) {X : Type*}
    [TopologicalSpace X] {a : X → ClassicalSymbol n ℂ ℂ m}
    (hcont : Continuous fun y ↦ (a y).toSymbol)
    (haK : ∀ y, ∀ x ∉ K, ∀ ξ, (a y).toSymbol.coefficient (x, ξ) = 0) :
    Continuous fun y ↦
      chartSobolevExtension hc ψ hc' φ (e.chartQuantization he φ₀ ψ₀ (a y)) s t := by
  obtain ⟨q, hq, hqa⟩ := exists_norm_chartSobolevExtension_chartQuantization_le (hc' := hc')
    (φ := φ) he φ₀ ψ₀ K hψ ht
  -- `‖Op_e(a y) - Op_e(a y₀)‖ ≤ q(a y - a y₀)`, since `Op_e(a y) - Op_e(a y₀) = Op_e(a y - a y₀)`
  -- and `a y - a y₀` vanishes outside `K`.
  have hdiff (y y₀ : X) :
      ‖chartSobolevExtension hc ψ hc' φ (e.chartQuantization he φ₀ ψ₀ (a y)) s t -
          chartSobolevExtension hc ψ hc' φ (e.chartQuantization he φ₀ ψ₀ (a y₀)) s t‖ ≤
        q ((a y).toSymbol - (a y₀).toSymbol) := by
    have hsub : e.chartQuantization he φ₀ ψ₀ (a y) - e.chartQuantization he φ₀ ψ₀ (a y₀) =
        e.chartQuantization he φ₀ ψ₀ (a y - a y₀) :=
      sub_eq_of_eq_add (e.chartQuantization_eq_add he φ₀ ψ₀ (by
        rw [ClassicalSymbol.toSymbol_sub, Symbol.coefficient_sub, sub_add_cancel]))
    rw [← chartSobolevExtension_sub_of_mem
      (e.chartQuantization_mem_classicalPseudodifferentialOperators he φ₀ ψ₀ _)
      (e.chartQuantization_mem_classicalPseudodifferentialOperators he φ₀ ψ₀ _) hψ ht, hsub,
      ← ClassicalSymbol.toSymbol_sub]
    exact hqa _ fun x hx ξ ↦ by
      rw [ClassicalSymbol.toSymbol_sub, Symbol.coefficient_sub, Pi.sub_apply, haK y x hx ξ,
        haK y₀ x hx ξ, sub_zero]
  refine continuous_iff_continuousAt.2 fun y₀ ↦ (tendsto_iff_norm_sub_tendsto_zero
    (E := chartSobolevSpace hc ψ s →L[ℂ] chartSobolevSpace hc' φ t)).2 ?_
  refine squeeze_zero (fun _ ↦ by positivity) (fun y ↦ hdiff y y₀) ?_
  simpa [Function.comp_def] using
    (hq.comp (hcont.sub (continuous_const (y := (a y₀).toSymbol)))).tendsto y₀

end OpenPartialHomeomorph

namespace TauCeti

open OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
  {ι κ : Type*} [Fintype ι] [Fintype κ] {c : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {ψ : ∀ i, 𝓓(⟨(c i).target, (c i).open_target⟩, ℝ)}
  {c' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc' : ∀ j, c' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {φ : ∀ j, 𝓓(⟨(c' j).target, (c' j).open_target⟩, ℝ)} {s t : ℝ}

variable {ν : Type*} [Fintype ν] {c₀ : ν → OpenPartialHomeomorph M (CoordinateSpace n)}

/-- **Continuity of the quantization of principal symbols.** Let `Q` be the quantization of
principal symbols for charts `c₀ₖ`, cutoffs `ρₖ` and `θₖ` and a frequency cutoff `χ`
(`TauCeti.principalSymbolQuantization`). If `y ↦ σ y` is a family of smooth homogeneous functions of
degree `m` on the cotangent bundle whose chart readings `(z, η) ↦ θₖ(z) σ_y(c₀ₖ⁻¹ z, ⟪η, ·⟫ ∘ dc₀ₖ)`
depend continuously on `y` as homogeneous symbols, for instance when every chart reading of `σ y`
does, then the extensions `H^s(M) → H^t(M)`, `t ≤ s - m`, of the operators `Q(σ y)` depend
continuously on `y` in the operator norm. -/
theorem continuous_chartSobolevExtension_principalSymbolQuantization
    (hc₀ : ∀ k, c₀ k ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ρ θ : ∀ k, 𝓓(⟨(c₀ k).target, (c₀ k).open_target⟩, ℝ)) (χ : FrequencyCutoff (CoordinateSpace n))
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1) (ht : t ≤ s - m) {X : Type*}
    [TopologicalSpace X] {σ : X → homogeneousCotangentSymbols n M m}
    (hσ : ∀ k, Continuous fun y ↦ (c₀ k).chartHomogeneousSymbol (hc₀ k) (θ k) (σ y).property) :
    Continuous fun y ↦
      chartSobolevExtension hc ψ hc' φ (principalSymbolQuantization m hc₀ ρ θ χ (σ y)) s t := by
  simp_rw [principalSymbolQuantization_apply]
  simp_rw [chartSobolevExtension_sum_of_mem _ (fun k _ ↦
    (c₀ k).chartQuantization_mem_classicalPseudodifferentialOperators (hc₀ k) _ _ _) hψ ht]
  refine continuous_finsetSum _ fun k _ ↦ ?_
  -- The cut-off term of the chart reading vanishes at positions outside the support of `θₖ`.
  refine (c₀ k).continuous_chartSobolevExtension_chartQuantization (hc₀ k) (ρ k) (θ k)
    ⟨tsupport (θ k), (θ k).hasCompactSupport.isCompact⟩ hψ ht ?_ fun y x hx ξ ↦ ?_
  · simp only [ClassicalSymbol.toSymbol_ofHomogeneous, ← HomogeneousSymbol.cutoffSymbolCLM_apply]
    exact (HomogeneousSymbol.cutoffSymbolCLM χ).continuous.comp (hσ k)
  · rw [ClassicalSymbol.toSymbol_ofHomogeneous, HomogeneousSymbol.coefficient_cutoffSymbol,
      chartHomogeneousSymbol_coefficient, image_eq_zero_of_notMem_tsupport hx]
    simp

/-- **A continuous linear quantization of principal symbols.** On a compact manifold there is a
linear map `Q` from the smooth positively homogeneous functions of degree `m` on the cotangent
bundle to the classical pseudodifferential operators of order `m` that inverts the principal symbol
map, `σ_m(Q(σ)) = σ`, and is continuous: for every family `y ↦ σ y` whose readings in every chart
of the maximal atlas, localized by every cutoff, depend continuously on `y` as homogeneous symbols,
the extensions `H^s(M) → H^t(M)`, `t ≤ s - m`, of the operators `Q(σ y)` depend continuously on `y`
in the operator norm, for the Sobolev spaces of every chart partition. -/
theorem exists_linearMap_classicalPrincipalSymbol_eq_and_continuous [CompactSpace M] :
    ∃ Q : homogeneousCotangentSymbols n M m →ₗ[ℂ]
        (C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
          C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯),
      (∀ σ, Q σ ∈ classicalPseudodifferentialOperators m) ∧
      (∀ σ, classicalPrincipalSymbol m (Q σ) = σ) ∧
      ∀ {ι κ : Type*} [Fintype ι] [Fintype κ] {c : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
        {hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
        {ψ : ∀ i, 𝓓(⟨(c i).target, (c i).open_target⟩, ℝ)}
        {c' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
        {hc' : ∀ j, c' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
        {φ : ∀ j, 𝓓(⟨(c' j).target, (c' j).open_target⟩, ℝ)} {s t : ℝ},
        (∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1) → t ≤ s - m →
        ∀ {X : Type*} [TopologicalSpace X] {σ : X → homogeneousCotangentSymbols n M m},
          (∀ (e : OpenPartialHomeomorph M (CoordinateSpace n))
            (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
            (θ : 𝓓(⟨e.target, e.open_target⟩, ℝ)),
            Continuous fun y ↦ e.chartHomogeneousSymbol he θ (σ y).property) →
          Continuous fun y ↦ chartSobolevExtension hc ψ hc' φ (Q (σ y)) s t := by
  -- Chart cutoffs `ρₖ` whose pullbacks sum to `1`, and cutoffs `θₖ` equal to `1` on their supports.
  obtain ⟨N, c₀, ρ, hρ⟩ := (isCompact_univ (X := M)).exists_sum_cutoffPullback_eq_one
    (E := CoordinateSpace n)
  choose θ hθ using fun k ↦ TestFunction.exists_eventually_eq_one
    (Ω := ⟨(chartAt (CoordinateSpace n) (c₀ k)).target,
      (chartAt (CoordinateSpace n) (c₀ k)).open_target⟩) (n := ⊤)
    (ρ k).hasCompactSupport.isCompact (ρ k).tsupport_subset
  have hc₀ (k : Fin N) := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, CoordinateSpace n))
    (n := ∞) (c₀ k)
  refine ⟨principalSymbolQuantization m hc₀ ρ θ default,
    principalSymbolQuantization_mem_classicalPseudodifferentialOperators hc₀ ρ θ default,
    classicalPrincipalSymbol_principalSymbolQuantization hc₀ ρ θ default
      (fun k z hz ↦ (hθ k).1.self_of_nhdsSet z hz) fun x ↦ hρ x (mem_univ x),
    fun hψ ht _ _ _ hσ ↦ continuous_chartSobolevExtension_principalSymbolQuantization hc₀ ρ θ
      default hψ ht fun k ↦ hσ _ (hc₀ k) (θ k)⟩

/-- **Continuous lifts of families of principal symbols, with a prescribed initial value.** On a
compact manifold, let `y ↦ σ y` be a family of smooth positively homogeneous functions of degree `m`
on the cotangent bundle whose readings in every chart of the maximal atlas, localized by every
cutoff, depend continuously on `y` as homogeneous symbols, and let `P₀` be a classical
pseudodifferential operator of order `m` with principal symbol `σ y₀`. Then there are classical
pseudodifferential operators `P y` of order `m` with principal symbols `σ y` and `P y₀ = P₀`, whose
extensions `H^s(M) → H^t(M)`, `t ≤ s - m`, depend continuously on `y` in the operator norm, for the
Sobolev spaces of every chart partition. They are `P y = Q(σ y) + P₀ - Q(σ y₀)` for the continuous
linear quantization `Q` of `TauCeti.exists_linearMap_classicalPrincipalSymbol_eq_and_continuous`. -/
theorem exists_classicalPrincipalSymbol_eq_and_continuous_chartSobolevExtension [CompactSpace M]
    {X : Type*} [TopologicalSpace X] {σ : X → homogeneousCotangentSymbols n M m}
    (hσ : ∀ (e : OpenPartialHomeomorph M (CoordinateSpace n))
      (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
      (θ : 𝓓(⟨e.target, e.open_target⟩, ℝ)),
      Continuous fun y ↦ e.chartHomogeneousSymbol he θ (σ y).property)
    (y₀ : X) {P₀ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hP₀ : P₀ ∈ classicalPseudodifferentialOperators m)
    (hP₀σ : classicalPrincipalSymbol m P₀ = σ y₀) :
    ∃ P : X → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
        C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      (∀ y, P y ∈ classicalPseudodifferentialOperators m) ∧
      (∀ y, classicalPrincipalSymbol m (P y) = σ y) ∧ P y₀ = P₀ ∧
      ∀ {ι κ : Type*} [Fintype ι] [Fintype κ] {c : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
        {hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
        {ψ : ∀ i, 𝓓(⟨(c i).target, (c i).open_target⟩, ℝ)}
        {c' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
        {hc' : ∀ j, c' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
        {φ : ∀ j, 𝓓(⟨(c' j).target, (c' j).open_target⟩, ℝ)} {s t : ℝ},
        (∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1) → t ≤ s - m →
          Continuous fun y ↦ chartSobolevExtension hc ψ hc' φ (P y) s t := by
  obtain ⟨Q, hQ, hQσ, hQc⟩ :=
    exists_linearMap_classicalPrincipalSymbol_eq_and_continuous (n := n) (M := M) (m := m)
  have hmem (y : X) : Q (σ y) + P₀ - Q (σ y₀) ∈ classicalPseudodifferentialOperators m :=
    sub_mem (add_mem (hQ _) hP₀) (hQ _)
  refine ⟨fun y ↦ Q (σ y) + P₀ - Q (σ y₀), hmem, fun y ↦ ?_, add_sub_cancel_left _ _,
    fun {ι κ} _ _ c hc ψ c' hc' φ s t hψ ht ↦ ?_⟩
  · ext x ξ
    rw [classicalPrincipalSymbol_sub (add_mem (hQ _) hP₀) (hQ _),
      classicalPrincipalSymbol_add (hQ _) hP₀, hQσ, hQσ, hP₀σ, add_sub_cancel_right]
  · simp_rw [chartSobolevExtension_sub_of_mem (add_mem (hQ _) hP₀) (hQ _) hψ ht,
      chartSobolevExtension_add_of_mem (hQ _) hP₀ hψ ht]
    exact ((hQc hψ ht hσ).add continuous_const).sub continuous_const

end TauCeti
