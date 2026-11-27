/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Composition
public import TauCeti.Analysis.Pseudodifferential.Manifold.Smoothing
import TauCeti.Analysis.Pseudodifferential.Composition.Compression
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Commutators of pseudodifferential operators on a manifold

Let `P` be a classical pseudodifferential operator of order `m` on a manifold `M` modelled on `ℝⁿ`
(`TauCeti.classicalPseudodifferentialOperators`) and `f` a real smooth function on `M`. The
commutator `⁅f, P⁆ = f P - P f` has order `m - 1`
(`TauCeti.lie_mulLeft_mem_classicalPseudodifferentialOperators`), because the principal symbols of
`f P` and `P f` agree. This file computes its principal symbol of order `m - 1`, the Poisson bracket
formula (Hörmander III, Theorem 18.1.8; Taylor, Lecture I, (2.5)–(2.7)): at a nonzero covector
`ξ ∈ T*ₓM`,

`σ_{m-1}(⁅f, P⁆)(x, ξ) = i d/dt σ_m(P)(x, ξ + t df_x)|_{t = 0}`

(`TauCeti.classicalPrincipalSymbol_lie_mulLeft_ofReal`), the derivative of `σ_m(P)(x, ·)` in the
direction of the covector `df_x`. In coordinates this is `i ∑ₖ ∂ₖf ∂_{ξₖ} σ_m(P)`.

More generally, if `P` and `Q` are classical pseudodifferential operators of orders `m'` and `m`,
the commutator `⁅P, Q⁆` has order `m' + m - 1`
(`TauCeti.lie_mem_classicalPseudodifferentialOperators`), and its principal symbol is `-i` times the
Poisson bracket of the principal symbols `p = σ_{m'}(P)` and `q = σ_m(Q)`. In a chart `e`, where
the principal symbols are functions of a position `y` and a frequency `η`
(`TauCeti.chartClassicalPrincipalSymbol`), this reads

`σ_{m'+m-1}(⁅P, Q⁆)(y, η) = -i ∑ₖ (∂_{ηₖ} p ∂_{yₖ} q - ∂_{yₖ} p ∂_{ηₖ} q)`

at nonzero frequencies (`TauCeti.chartClassicalPrincipalSymbol_lie`). The proof reads `⁅P, Q⁆` in
the chart as `φ Op(a # b - b # a) φ` up to an operator of order `-∞`, for the chart symbols `a`, `b`
of `P`, `Q` and a cutoff `φ` equal to `1` near `y`: the part of `⁅P, Q⁆` that leaves the chart is
removed by pseudolocality. The Euclidean Poisson bracket formula
(`TauCeti.ClassicalSymbol.exists_inclusion_eq_sharpCommutator_of_scalar`) then applies to `a` and
`b`, whose principal symbols near `y` are those of `P` and `Q` read in the chart.

It then treats **square partitions of unity**, smooth functions `gᵢ` with `∑ᵢ gᵢ² = 1`. The
operator `∑ᵢ gᵢ P gᵢ` is `P` up to order `m - 2`, not only `m - 1`
(`TauCeti.sum_mulLeft_comp_comp_mulLeft_sub_mem_classicalPseudodifferentialOperators`), since

`∑ᵢ gᵢ P gᵢ - P = -½ ∑ᵢ ⁅gᵢ, ⁅gᵢ, P⁆⁆`.

For real `gᵢ` the first-order terms `i ∑ᵢ gᵢ ∂_ξ σ_m(P) (dgᵢ) = (i/2) ∂_ξ σ_m(P) (d ∑ᵢ gᵢ²)` cancel,
as the formula above shows. Take cutoffs `ρᵢ` in charts `eᵢ` whose squares add up to `1`, and let
`aᵢ` be the symbol of the chart compression of `P` by `ρᵢ` and `ρᵢ`, that is, the chart symbol of
`ρᵢ P ρᵢ`. The symmetric patched quantization `∑ᵢ Op_{eᵢ}(aᵢ)`, localized by cutoffs `φᵢ` and `ψᵢ`
equal to `1` on the support of `ρᵢ`, is `∑ᵢ ρᵢ P ρᵢ`, and therefore `P` up to order `m - 2`
(`TauCeti.sum_chartQuantization_sub_mem_classicalPseudodifferentialOperators`). It differs by
an operator of order `m - 2` from the ordinary patched quantization over a partition of unity,
which is `P` up to order `-∞` (the theorem
`sum_chartQuantization_sub_sum_chartQuantization_mem_classicalPseudodifferentialOperators`).
In general the difference does not have lower order: on `ℝ`, with `D = -i ∂`, square partitions
give `∑ᵢ χᵢ D² χᵢ = D² + ∑ᵢ (χᵢ')²`. This is the manifold form of the Euclidean comparison
`TauCeti.Symbol.exists_coefficient_eq_sum_compress_sub_sum_compress`.

## The argument

In the preferred chart `e` at `x`, take a cutoff `φ` equal to `1` near `e x` and a cutoff `χ` equal
to `1` on the support of `φ`, and let `c` be the symbol of the chart compression of `P` by `χ` and
`χ`. With `h = φ · (f ∘ e⁻¹)`, the chart compression of `⁅f, P⁆` by `φ` and `φ` is
`u ↦ h Op(c) (φ u) - φ Op(c) (h u)`, the quantization of the difference `h (c # φ) - φ (c # h)` of
two compressions (`TauCeti.Symbol.compress`). Their expansions to second order
(`TauCeti.Symbol.exists_coefficient_compress_eq`) leave `i ∑ₖ ∂ₖh ∂_{ξₖ} c` at `e x`, up to a symbol
of order `m - 2`, which does not change the principal symbol at `e x`
(`TauCeti.ClassicalSymbol.coefficient_principal_eq_of_forall_coefficient_eq_add`). Reading the
frequency derivative of `σ(c)(e x, ·)` on `T*ₓM` gives the formula.

## Main results

* `TauCeti.classicalPrincipalSymbol_lie_mulLeft_ofReal`: the principal symbol of `⁅f, P⁆`.
* `TauCeti.chartClassicalPrincipalSymbol_lie`: the Poisson bracket formula for the principal symbol
  of `⁅P, Q⁆`, in a chart.
* `TauCeti.sum_mulLeft_comp_comp_mulLeft_sub_mem_classicalPseudodifferentialOperators`: square
  partitions of unity reproduce `P` up to order `m - 2`.
* `TauCeti.sum_chartQuantization_sub_mem_classicalPseudodifferentialOperators` and
  `sum_chartQuantization_sub_sum_chartQuantization_mem_classicalPseudodifferentialOperators`: the
  symmetric patched quantization over a square partition of unity, compared with `P` and with the
  ordinary patched quantization.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.8.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §§2 and 8.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

/-! ### The Euclidean computation -/

section Euclidean

variable {n : ℕ} {m : ℝ}

/-- Let `c` be a classical symbol of order `m`, and `φ`, `h` compactly supported smooth real
functions with `φ = 1` near `y`. If the classical symbol `s` of order `m - 1` has the coefficient
`h (c # φ) - φ (c # h)` of the operator `u ↦ h Op(c) (φ u) - φ Op(c) (h u)`, then its principal
symbol at `y` is `i ∑ₖ ∂ₖh(y) ∂_{ξₖ} σ(c)(y, ·)`. -/
private theorem coefficient_principal_eq_of_coefficient_eq_compress_sub
    (c : ClassicalSymbol n ℂ ℂ m) (s : ClassicalSymbol n ℂ ℂ (m - 1))
    {φ h : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h)
    (hs : ∀ p, s.toSymbol.coefficient p = (c.toSymbol.compress h φ hh hφ hφc).coefficient p -
      (c.toSymbol.compress φ h hφ hh hhc).coefficient p)
    {y : CoordinateSpace n} (hφy : φ =ᶠ[𝓝 y] fun _ ↦ 1) (η : CoordinateSpace n) :
    s.principal.coefficient (y, η) = Complex.I • ∑ k, coordinateDeriv [k] h y •
      (c.principal.frequencyDeriv (EuclideanSpace.single k 1)).coefficient (y, η) := by
  obtain ⟨r₁, hr₁⟩ := c.toSymbol.exists_coefficient_compress_eq hh hφ hφc
  obtain ⟨r₂, hr₂⟩ := c.toSymbol.exists_coefficient_compress_eq hφ hh hhc
  have hφ1 : φ y = 1 := hφy.self_of_nhds
  have hdφ (k : Fin n) : coordinateDeriv [k] φ y = 0 := by
    rw [coordinateDeriv_singleton, hφy.fderiv_eq]
    simp
  -- At `y`, `s = i ∑ₖ ∂ₖh(y) ∂_{ξₖ} c + (r₁ - r₂)` with `r₁ - r₂` of order `m - 2`.
  set c' : ClassicalSymbol n ℂ ℂ (m - 1) :=
    Complex.I • ∑ k, ((coordinateDeriv [k] h y : ℝ) : ℂ) • ClassicalSymbol.frequencyDeriv k c
  have hcoef (ζ : CoordinateSpace n) : s.toSymbol.coefficient (y, ζ) =
      c'.toSymbol.coefficient (y, ζ) + (r₁ - r₂).coefficient (y, ζ) := by
    simp_rw [c', ClassicalSymbol.toSymbol_smul, ClassicalSymbol.toSymbol_sum,
      ClassicalSymbol.toSymbol_smul, ClassicalSymbol.toSymbol_frequencyDeriv,
      Symbol.coefficient_smul, Symbol.coefficient_sum, Symbol.coefficient_smul]
    rw [hs, hr₁, hr₂, Symbol.coefficient_sub]
    simp only [hφ1, hdφ, mul_one, one_mul, mul_zero, zero_smul, Finset.sum_const_zero, smul_zero,
      sub_zero, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, Complex.coe_smul]
    abel
  rw [ClassicalSymbol.coefficient_principal_eq_of_forall_coefficient_eq_add (by linarith) hcoef]
  simp_rw [c', ClassicalSymbol.principal_smul, ClassicalSymbol.principal_sum,
    ClassicalSymbol.principal_smul, ClassicalSymbol.principal_frequencyDeriv]
  simp [Complex.coe_smul]

/-- Let `c` and `s` be classical symbols of order `m`, `φ` a compactly supported smooth real
function with `φ = 1` near `y`, and `d` a symbol of order `m - 1`. If `s` has the coefficient
`φ (c # φ) + d`, then `s` and `c` have the same principal symbol at `y`. -/
private theorem coefficient_principal_eq_of_coefficient_eq_compress_add
    (c s : ClassicalSymbol n ℂ ℂ m) (d : Symbol n ℂ ℂ (m - 1))
    {φ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hs : ∀ p, s.toSymbol.coefficient p =
      (c.toSymbol.compress φ φ hφ hφ hφc).coefficient p + d.coefficient p)
    {y : CoordinateSpace n} (hφy : φ =ᶠ[𝓝 y] fun _ ↦ 1) (η : CoordinateSpace n) :
    s.principal.coefficient (y, η) = c.principal.coefficient (y, η) := by
  obtain ⟨r, hr⟩ := c.toSymbol.exists_coefficient_compress_eq hφ hφ hφc
  have hφ1 : φ y = 1 := hφy.self_of_nhds
  have hdφ (k : Fin n) : coordinateDeriv [k] φ y = 0 := by
    rw [coordinateDeriv_singleton, hφy.fderiv_eq]
    simp
  -- At `y`, `s = c + (r + d)` with `r + d` of order `m - 1`.
  refine ClassicalSymbol.coefficient_principal_eq_of_forall_coefficient_eq_add (m' := m - 1)
    (by linarith) (t := Symbol.inclusion (by linarith) r + d) (fun ζ ↦ ?_) η
  rw [hs, hr]
  simp [hφ1, hdφ, add_assoc]

/-- Let `a` and `b` be classical symbols of compact spatial support and `c₀` the classical symbol
of order `m' + m - 1` of their commutator `a # b - b # a`. If a classical symbol `s` quantizes to
`u ↦ φ Op(a # b - b # a) (φ u) + Op(d) u`, then `s` has the coefficient `φ (c₀ # φ) + d`. -/
private theorem coefficient_eq_compress_add_of_sharpCommutator {m m' : ℝ}
    {a : ClassicalSymbol n ℂ ℂ m'} {b : ClassicalSymbol n ℂ ℂ m}
    {ha : a.toSymbol.HasCompactSpatialSupport} {hb : b.toSymbol.HasCompactSpatialSupport}
    {c₀ : ClassicalSymbol n ℂ ℂ (m' + m - 1)}
    (hc₀ : ClassicalSymbol.inclusion 1 (by simp) c₀ = a.sharpCommutator b ha hb)
    {s : ClassicalSymbol n ℂ ℂ (m' + m - 1)} {d : Symbol n ℂ ℂ (m' + m - 1 - 1)}
    {φ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (h : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (z : CoordinateSpace n),
      quantizeSchwartzValue s.toSymbol.coefficient u z =
        φ z • (quantizeSchwartzValue (a.sharp b hb).toSymbol.coefficient
            (SchwartzMap.smulLeftCLM ℂ φ u) z -
          quantizeSchwartzValue (b.sharp a ha).toSymbol.coefficient
            (SchwartzMap.smulLeftCLM ℂ φ u) z) +
        quantizeSchwartzValue d.coefficient u z)
    (p : CoordinateSpace n × CoordinateSpace n) :
    s.toSymbol.coefficient p =
      (c₀.toSymbol.compress φ φ hφ hφ hφc).coefficient p + d.coefficient p := by
  -- The coefficient of `c₀` is that of `a # b - b # a`.
  have hc₀coef : c₀.toSymbol.coefficient + (b.sharp a ha).toSymbol.coefficient =
      (a.sharp b hb).toSymbol.coefficient := by
    funext z
    have h := congrArg (fun t : ClassicalSymbol n ℂ ℂ (m' + m) ↦ t.toSymbol.coefficient z) hc₀
    simp only [ClassicalSymbol.toSymbol_inclusion, Symbol.coefficient_inclusion,
      ClassicalSymbol.coefficient_toSymbol_sharpCommutator] at h
    rw [Pi.add_apply, h, ClassicalSymbol.toSymbol_sharp, ClassicalSymbol.toSymbol_sharp,
      sub_add_cancel]
  have hs := Symbol.coefficient_eq_of_forall_quantizeSchwartzValue_eq (a := s.toSymbol)
    (b := c₀.toSymbol.compress φ φ hφ hφ hφc + Symbol.inclusion (by linarith) d)
    fun u _ ↦ funext fun z ↦ by
      rw [Symbol.coefficient_add, Symbol.coefficient_inclusion,
        Symbol.quantizeSchwartzValue_coefficient_add, Symbol.quantizeSchwartzValue_compress, h,
        ← hc₀coef, Symbol.quantizeSchwartzValue_coefficient_add, add_sub_cancel_right]
  rw [hs, Symbol.coefficient_add, Symbol.coefficient_inclusion, Pi.add_apply]

end Euclidean

/-! ### The commutator in a chart -/

section Chart

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
  {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)

include he

/-- **The commutator with a real function in a chart.** Let `c` be the symbol of the chart
compression of `P` by a cutoff `χ` equal to `1` on the support of `φ`. Then the chart compression of
`⁅f, P⁆` by `φ` and `φ` is `u ↦ h Op(c) (φ u) - φ Op(c) (h u)`, where `h = φ · (f ∘ e⁻¹)`. -/
private theorem complexChartCompression_lie_mulLeft_ofReal_apply {m : ℝ}
    {φ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hχ : ∀ y ∈ tsupport φ, χ y = 1)
    {c : ClassicalSymbol n ℂ ℂ m}
    (hc : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue c.toSymbol.coefficient u y =
        e.complexChartCompression he χ χ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (u : 𝓢(CoordinateSpace n, ℂ))
    (y : CoordinateSpace n) :
    e.complexChartCompression he φ φ ⁅LinearMap.mulLeft ℂ (ContMDiffMap.ofReal f), P⁆
        (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y =
      e.cutoffPushforward he φ f y •
          quantizeSchwartzValue c.toSymbol.coefficient (SchwartzMap.smulLeftCLM ℂ ⇑φ u) y -
        φ y • quantizeSchwartzValue c.toSymbol.coefficient
          (SchwartzMap.smulLeftCLM ℂ ⇑(e.cutoffPushforward he φ f) u) y := by
  set h := e.cutoffPushforward he φ f
  have hh : (⇑h : CoordinateSpace n → ℝ) = fun y ↦ φ y * f (e.symm y) :=
    funext (e.cutoffPushforward_apply he φ f)
  have hht : (⇑h : CoordinateSpace n → ℝ).HasTemperateGrowth :=
    (e.hasCompactSupport_cutoffPushforward he φ f).hasTemperateGrowth
      (e.contDiff_cutoffPushforward he φ f)
  set g := e.complexCutoffPullback he φ (ContMDiffMap.ofContDiff u (u.smooth ⊤))
  -- Read on `M` through `χ`, the inputs `φ u` and `h u` are `g` and `f g`.
  have h₁ : e.complexCutoffPullback he χ (ContMDiffMap.ofContDiff
      (SchwartzMap.smulLeftCLM ℂ ⇑φ u) (SchwartzMap.smooth _ ⊤)) = g :=
    e.complexCutoffPullback_ofContDiff_smulLeftCLM he hχ u
  have h₂ : e.complexCutoffPullback he χ (ContMDiffMap.ofContDiff
      (SchwartzMap.smulLeftCLM ℂ ⇑h u) (SchwartzMap.smooth _ ⊤)) = ContMDiffMap.ofReal f * g := by
    ext q
    by_cases hq : q ∈ e.source
    · simp only [g, OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he _ _ hq,
        ContMDiffMap.coe_ofContDiff, SchwartzMap.smulLeftCLM_apply_apply hht, ContMDiffMap.coe_mul,
        Pi.mul_apply, ContMDiffMap.ofReal_apply, h, OpenPartialHomeomorph.cutoffPushforward_apply,
        e.left_inv hq]
      by_cases hφq : φ (e q) = 0
      · simp [hφq]
      · rw [hχ _ (subset_tsupport _ hφq), one_smul]
        simp only [Complex.real_smul]
        push_cast
        ring
    · simp [g, OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he _ _ hq]
  rw [hc, hc, OpenPartialHomeomorph.complexChartCompression_apply,
    OpenPartialHomeomorph.complexChartCompression_apply,
    OpenPartialHomeomorph.complexChartCompression_apply, h₁, h₂, Ring.lie_def,
    LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, LinearMap.mulLeft_apply,
    LinearMap.mulLeft_apply, congrFun hh y]
  by_cases hφy : φ y = 0
  · simp [hφy]
  rw [hχ _ (subset_tsupport _ hφy), one_smul, one_smul]
  simp only [ContMDiffMap.coe_sub, ContMDiffMap.coe_mul, Pi.sub_apply, Pi.mul_apply,
    ContMDiffMap.ofReal_apply, smul_sub, Complex.real_smul]
  push_cast
  ring

/-- **The chart symbol of the commutator with a real function.** In the setting of
`complexChartCompression_lie_mulLeft_ofReal_apply`, the symbol `s` of the chart compression of
`⁅f, P⁆` by `φ` and `φ` has the coefficient `h (c # φ) - φ (c # h)` of two compressions of `c`. -/
private theorem coefficient_eq_compress_sub_of_lie_mulLeft_ofReal {m m' : ℝ}
    {φ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hχ : ∀ y ∈ tsupport φ, χ y = 1)
    {c : ClassicalSymbol n ℂ ℂ m}
    (hc : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue c.toSymbol.coefficient u y =
        e.complexChartCompression he χ χ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) {s : ClassicalSymbol n ℂ ℂ m'}
    (hs : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue s.toSymbol.coefficient u y =
        e.complexChartCompression he φ φ ⁅LinearMap.mulLeft ℂ (ContMDiffMap.ofReal f), P⁆
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (hhd : ContDiff ℝ ∞ (⇑(e.cutoffPushforward he φ f) : CoordinateSpace n → ℝ))
    (hhc : HasCompactSupport (⇑(e.cutoffPushforward he φ f) : CoordinateSpace n → ℝ))
    (p : CoordinateSpace n × CoordinateSpace n) :
    s.toSymbol.coefficient p =
      (c.toSymbol.compress (e.cutoffPushforward he φ f) φ hhd φ.contDiff
          φ.hasCompactSupport).coefficient p -
        (c.toSymbol.compress φ (e.cutoffPushforward he φ f) φ.contDiff hhd hhc).coefficient p := by
  set A := c.toSymbol.compress (e.cutoffPushforward he φ f) φ hhd φ.contDiff φ.hasCompactSupport
  set B := c.toSymbol.compress φ (e.cutoffPushforward he φ f) φ.contDiff hhd hhc
  have hcs := Symbol.coefficient_eq_of_forall_quantizeSchwartzValue_eq (a := s.toSymbol)
    (b := A - B) fun u _ ↦ funext fun y ↦ by
    have hsub := Symbol.quantizeSchwartzValue_coefficient_add (A - B) B u y
    rw [← Symbol.coefficient_add, sub_add_cancel] at hsub
    rw [hs, complexChartCompression_lie_mulLeft_ofReal_apply he hχ hc,
      eq_sub_of_add_eq hsub.symm, Symbol.quantizeSchwartzValue_compress,
      Symbol.quantizeSchwartzValue_compress]
  rw [hcs, Symbol.coefficient_sub, Pi.sub_apply]

end Chart

/-! ### The principal symbol of the commutator -/

section PrincipalSymbol

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **Fibre derivatives of the principal symbol in a chart.** Let `c` be the symbol of the chart
compression of `P` by a cutoff `χ` with `χ (e x) = 1`, and `η` the frequency of the nonzero
covector `ξ ∈ T*ₓM` in the chart. If `h` agrees with `f ∘ e⁻¹` near `e x`, the derivative of
`σ_m(P)(x, ·)` at `ξ` in the direction `df_x` is `∑ₖ ∂ₖh(e x) ∂_{ξₖ} σ(c)(e x, η)`. -/
private theorem deriv_classicalPrincipalSymbol_eq_sum_coefficient_frequencyDeriv {m : ℝ}
    (hP : P ∈ classicalPseudodifferentialOperators m)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {c : ClassicalSymbol n ℂ ℂ m}
    (hc : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue c.toSymbol.coefficient u y =
        e.complexChartCompression he χ χ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    {x : M} (hx : x ∈ e.source) (hχx : χ (e x) = 1)
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0)
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) {h : CoordinateSpace n → ℝ}
    (hh : h =ᶠ[𝓝 (e x)] fun y ↦ f (e.symm y)) :
    deriv (fun t : ℝ ↦ classicalPrincipalSymbol m P x
        (ξ + t • mvfderiv 𝓘(ℝ, CoordinateSpace n) f x)) 0 =
      (∑ k, coordinateDeriv [k] h (e x) •
        (c.principal.frequencyDeriv (EuclideanSpace.single k 1)).coefficient
          (e x, (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
            (ξ.comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x).inverse))) 1 := by
  have he₁ : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  -- The linear map `L : ξ' ↦ η'` from covectors at `x` to their frequencies in the chart.
  set D := mvfderiv 𝓘(ℝ, CoordinateSpace n) e x
  let L : (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) →ₗ[ℝ] CoordinateSpace n :=
    { toFun := fun ξ' ↦ (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm (ξ'.comp D.inverse)
      map_add' := fun ξ₁ ξ₂ ↦ by simp [ContinuousLinearMap.add_comp]
      map_smul' := fun a ξ' ↦ by simp [ContinuousLinearMap.smul_comp] }
  have hL (ξ' : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
      L ξ' = (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm (ξ'.comp D.inverse) :=
    rfl
  set η := L ξ
  have hη : η ≠ 0 := toDual_symm_comp_inverse_mvfderiv_ne_zero he₁ hx hξ
  -- `σ_m(P)(x, ·) = g ∘ L` for the principal symbol `g` of `c` at `e x`, read at `1`.
  set ev := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).restrictScalars ℝ
  set g : CoordinateSpace n → ℂ := ev ∘ fun η' ↦ c.principal.coefficient (e x, η')
  have hσ (ξ' : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
      classicalPrincipalSymbol m P x ξ' = g (L ξ') := by
    have h' := coefficient_principal_apply_eq_classicalPrincipalSymbol hP he χ χ hc hx ξ'
    rw [hχx, mul_one, Complex.ofReal_one, one_mul] at h'
    exact h'.symm
  have hcd : DifferentiableAt ℝ (fun η' ↦ c.principal.coefficient (e x, η')) η :=
    (c.principal.differentiableAt_coefficient (p := (e x, η)) hη).comp η
      ((differentiableAt_const _).prodMk differentiableAt_id)
  -- Along the line `t ↦ ξ + t df_x`, `σ_m(P)(x, ·)` is `g` along `t ↦ η + t v`, `v = L(df_x)`.
  obtain ⟨v, hvL⟩ : ∃ v, L (mvfderiv 𝓘(ℝ, CoordinateSpace n) f x) = v := ⟨_, rfl⟩
  have hline : (fun t : ℝ ↦ classicalPrincipalSymbol m P x
      (ξ + t • mvfderiv 𝓘(ℝ, CoordinateSpace n) f x)) = g ∘ fun t : ℝ ↦ η + t • v :=
    funext fun t ↦ by simp [hσ, η, ← hvL]
  have hlin : HasDerivAt (fun t : ℝ ↦ η + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add η
  have hgη : HasFDerivAt g (ev.comp (fderiv ℝ (fun η' ↦ c.principal.coefficient (e x, η')) η))
      (η + (0 : ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact ev.hasFDerivAt.comp η hcd.hasFDerivAt
  -- The vector `v` is the gradient `∑ₖ ∂ₖh(e x) eₖ` of `f ∘ e⁻¹` at `e x`.
  have hv : v = ∑ k, coordinateDeriv [k] h (e x) • EuclideanSpace.single k 1 := by
    rw [← hvL, hL, toDual_symm_mvfderiv_comp_inverse_eq_gradient he₁ hx hh, gradient,
      ← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr' (InnerProductSpace.toDual ℝ
        (CoordinateSpace n) |>.symm (fderiv ℝ h (e x)))]
    simp only [EuclideanSpace.basisFun_apply, real_inner_comm _ (EuclideanSpace.single _ _),
      InnerProductSpace.toDual_symm_apply, coordinateDeriv_singleton]
  rw [hline, (hgη.comp_hasDerivAt 0 hlin).deriv, hv, map_sum]
  simp only [map_smul, FunLike.coe_sum, Finset.sum_apply, smul_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [c.principal.coefficient_frequencyDeriv (EuclideanSpace.single k 1)
    (ξ := (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm (ξ.comp D.inverse)) hη]
  simp only [ev, η, hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.apply_apply]

/-- **The principal symbol of a commutator with a multiplication operator.** Let `P` be a
classical pseudodifferential operator of order `m` on `M` and `f` a real smooth function. The
commutator `⁅f, P⁆ = f P - P f`, of order `m - 1`, has the principal symbol

`σ_{m-1}(⁅f, P⁆)(x, ξ) = i d/dt σ_m(P)(x, ξ + t df_x)|_{t = 0}`

at every nonzero covector `ξ ∈ T*ₓM`: the derivative of `σ_m(P)(x, ·)` at `ξ` in the direction of
the covector `df_x`. In coordinates this is `i ∑ₖ ∂ₖf ∂_{ξₖ} σ_m(P) = -i {f, σ_m(P)}`, the Poisson
bracket formula. At `ξ = 0` the left side vanishes while the right side need not, for instance
when `σ_m(P)(x, ·)` is linear. -/
theorem classicalPrincipalSymbol_lie_mulLeft_ofReal {m : ℝ}
    (hP : P ∈ classicalPseudodifferentialOperators m) (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (x : M) {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    classicalPrincipalSymbol (m - 1) ⁅LinearMap.mulLeft ℂ (ContMDiffMap.ofReal f), P⁆ x ξ =
      Complex.I * deriv (fun t : ℝ ↦ classicalPrincipalSymbol m P x
        (ξ + t • mvfderiv 𝓘(ℝ, CoordinateSpace n) f x)) 0 := by
  set e := chartAt (CoordinateSpace n) x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source _ x
  -- Cutoffs: `φ = 1` near `e x`, and `χ = 1` on the support of `φ`.
  obtain ⟨φ, hφx⟩ := TestFunction.exists_eventually_eq_one_nhds (n := ⊤)
    (Ω := ⟨e.target, e.open_target⟩) (e.map_source hx)
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    (Ω := ⟨e.target, e.open_target⟩) φ.hasCompactSupport.isCompact φ.tsupport_subset
  have hφ1 : φ (e x) = 1 := hφx.self_of_nhds
  have hχ1 : ∀ y ∈ tsupport φ, χ y = 1 := fun y hy ↦ hχ.self_of_nhdsSet y hy
  have hχx : χ (e x) = 1 := hχ1 _ (subset_tsupport _ (by simp [hφ1]))
  -- The chart symbols `c` of `P` by `χ`, `χ` and `s` of `⁅f, P⁆` by `φ`, `φ`.
  obtain ⟨c, hc⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 e he χ χ
  have hQ := lie_mulLeft_mem_classicalPseudodifferentialOperators hP (ContMDiffMap.ofReal f)
  obtain ⟨s, hs⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hQ).2 e he φ φ
  -- The function `h = φ · (f ∘ e⁻¹)` on the chart, equal to `f ∘ e⁻¹` near `e x`.
  set h := e.cutoffPushforward he φ f
  have hhd : ContDiff ℝ ∞ (⇑h : CoordinateSpace n → ℝ) := e.contDiff_cutoffPushforward he φ f
  have hhc : HasCompactSupport (⇑h : CoordinateSpace n → ℝ) :=
    e.hasCompactSupport_cutoffPushforward he φ f
  have hhe : (⇑h : CoordinateSpace n → ℝ) =ᶠ[𝓝 (e x)] fun y ↦ f (e.symm y) := by
    filter_upwards [hφx] with y hy
    rw [e.cutoffPushforward_apply he φ f, hy, one_mul]
  -- Read the principal symbol of `⁅f, P⁆` in the chart, where its symbol is
  -- `h (c # φ) - φ (c # h)`.
  have hL' := coefficient_principal_apply_eq_classicalPrincipalSymbol hQ he φ φ hs hx ξ
  rw [hφ1, mul_one, Complex.ofReal_one, one_mul] at hL'
  rw [← hL', coefficient_principal_eq_of_coefficient_eq_compress_sub c s φ.contDiff
    φ.hasCompactSupport hhd hhc (coefficient_eq_compress_sub_of_lie_mulLeft_ofReal he hχ1 hc f hs
      hhd hhc) hφx,
    deriv_classicalPrincipalSymbol_eq_sum_coefficient_frequencyDeriv hP he hc hx hχx hξ f hhe,
    smul_apply, smul_eq_mul]

end PrincipalSymbol

/-! ### The Poisson bracket formula -/

section PoissonBracket

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)

include he

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **The commutator away from the diagonal.** With `X = χ` and `Θ = θ` read on `M` and `χ = 1`
near the support of `θ`, the parts `Θ P (1 - X) Q` and `Θ Q (1 - X) P` of `Θ ⁅P, Q⁆` have order
`-∞` by pseudolocality, so their difference has order `m' + m - 2`. -/
private theorem mulLeft_comp_comp_mulLeft_one_sub_comp_sub_mem {m m' : ℝ}
    (hP : P ∈ classicalPseudodifferentialOperators m')
    (hQ : Q ∈ classicalPseudodifferentialOperators m) {θ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}
    (hχ : ∀ᶠ z in 𝓝ˢ (tsupport θ), χ z = 1) :
    (LinearMap.mulLeft ℂ (e.complexCutoffPullback he θ 1) ∘ₗ P ∘ₗ
          LinearMap.mulLeft ℂ (1 - e.complexCutoffPullback he χ 1)) ∘ₗ Q -
        (LinearMap.mulLeft ℂ (e.complexCutoffPullback he θ 1) ∘ₗ Q ∘ₗ
          LinearMap.mulLeft ℂ (1 - e.complexCutoffPullback he χ 1)) ∘ₗ P ∈
      classicalPseudodifferentialOperators (m' + m - 1 - 1) := by
  have hdisj := e.disjoint_tsupport_complexCutoffPullback_one_sub he hχ
  refine sub_mem ?_ ?_
  · have h := comp_mem_classicalPseudodifferentialOperators
      (smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators (m' - 2)
        (mulLeft_comp_comp_mulLeft_mem_smoothingPseudodifferentialOperators hP hdisj)) hQ
    rwa [show m' - 2 + m = m' + m - 1 - 1 by ring] at h
  · have h := comp_mem_classicalPseudodifferentialOperators
      (smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators (m - 2)
        (mulLeft_comp_comp_mulLeft_mem_smoothingPseudodifferentialOperators hQ hdisj)) hP
    rwa [show m - 2 + m' = m' + m - 1 - 1 by ring] at h

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- **The commutator in a chart.** Let `a` and `b` be the symbols of the chart compressions of `P`
and `Q` by `χ` and `χ₂`, where `χ = 1` near the support of `θ`, `θ = 1` on the support of `φ`,
and `χ₂ = 1` on the support of `χ`. Then the chart compression of `⁅P, Q⁆` by `φ` and `φ` is
`u ↦ φ Op(a # b - b # a) (φ u) + Op(d) u`, where `d` is the chart symbol of the part of `⁅P, Q⁆`
away from the diagonal (`mulLeft_comp_comp_mulLeft_one_sub_comp_sub_mem`). -/
private theorem complexChartCompression_lie_apply {m m' : ℝ}
    {φ θ χ χ₂ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hθφ : ∀ z ∈ tsupport φ, θ z = 1)
    (hχφ : ∀ z ∈ tsupport φ, χ z = 1) (hχ₂χ : ∀ z ∈ tsupport χ, χ₂ z = 1)
    (hχ₂φ : ∀ z ∈ tsupport φ, χ₂ z = 1) {a : ClassicalSymbol n ℂ ℂ m'}
    {b : ClassicalSymbol n ℂ ℂ m}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he χ χ₂ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (hb : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue b.toSymbol.coefficient u y =
        e.complexChartCompression he χ χ₂ Q (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (u : 𝓢(CoordinateSpace n, ℂ)) (z : CoordinateSpace n) :
    e.complexChartCompression he φ φ ⁅P, Q⁆ (ContMDiffMap.ofContDiff u (u.smooth ⊤)) z =
      φ z • (quantizeSchwartzValue (a.sharp b
            (hasCompactSpatialSupport_of_eq_complexChartCompression he hb)).toSymbol.coefficient
            (SchwartzMap.smulLeftCLM ℂ ⇑φ u) z -
          quantizeSchwartzValue (b.sharp a
            (hasCompactSpatialSupport_of_eq_complexChartCompression he ha)).toSymbol.coefficient
            (SchwartzMap.smulLeftCLM ℂ ⇑φ u) z) +
        e.complexChartCompression he φ φ
          ((LinearMap.mulLeft ℂ (e.complexCutoffPullback he θ 1) ∘ₗ P ∘ₗ
              LinearMap.mulLeft ℂ (1 - e.complexCutoffPullback he χ 1)) ∘ₗ Q -
            (LinearMap.mulLeft ℂ (e.complexCutoffPullback he θ 1) ∘ₗ Q ∘ₗ
              LinearMap.mulLeft ℂ (1 - e.complexCutoffPullback he χ 1)) ∘ₗ P)
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) z := by
  -- Split `⁅P, Q⁆ = (P X Q - Q X P) + (P (1 - X) Q - Q (1 - X) P)`; `φ` sees the second part
  -- only through `Θ`, and the first one is `φ Op(a # b - b # a) φ`.
  set X := e.complexCutoffPullback he χ 1
  have hsplit (A B : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
      A ∘ₗ B = A ∘ₗ LinearMap.mulLeft ℂ X ∘ₗ B + A ∘ₗ LinearMap.mulLeft ℂ (1 - X) ∘ₗ B := by
    have hid : LinearMap.mulLeft ℂ X + LinearMap.mulLeft ℂ (1 - X) = LinearMap.id := by
      ext f q
      simp [sub_mul]
    rw [← LinearMap.comp_add, ← LinearMap.add_comp, hid, LinearMap.id_comp]
  rw [quantizeSchwartzValue_sharp_eq_complexChartCompression_comp_mulLeft_comp he hχ₂χ ha hb,
    quantizeSchwartzValue_sharp_eq_complexChartCompression_comp_mulLeft_comp he hχ₂χ hb ha,
    smul_sub, OpenPartialHomeomorph.smul_complexChartCompression_smulLeftCLM he hχφ hχ₂φ,
    OpenPartialHomeomorph.smul_complexChartCompression_smulLeftCLM he hχφ hχ₂φ, Ring.lie_def,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp, hsplit P Q, hsplit Q P]
  simp only [X, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
    ContMDiffMap.coe_add, ContMDiffMap.coe_sub, Pi.add_apply, Pi.sub_apply, LinearMap.comp_assoc,
    OpenPartialHomeomorph.complexChartCompression_mulLeft_comp_of_eq_one he hθφ]
  ring

/-- **The commutator symbol in a chart.** Let `a` and `b` be the symbols of the chart compressions
of `P` and `Q` by cutoffs `χ` and `χ₂` equal to `1` near `y`. The classical symbol `c₀` of order
`m' + m - 1` of their commutator `a # b - b # a` has, at `(y, η)` with `η ≠ 0`, the principal
symbol `-i {p, q}`, for the principal symbols `p` of `P` and `q` of `Q` read in the chart. -/
private theorem exists_inclusion_eq_sharpCommutator_and_coefficient_principal_eq {m m' : ℝ}
    (hP : P ∈ classicalPseudodifferentialOperators m')
    (hQ : Q ∈ classicalPseudodifferentialOperators m) {χ χ₂ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}
    {a : ClassicalSymbol n ℂ ℂ m'} {b : ClassicalSymbol n ℂ ℂ m}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he χ χ₂ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (hb : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue b.toSymbol.coefficient u y =
        e.complexChartCompression he χ χ₂ Q (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    {y η : CoordinateSpace n} (hy : y ∈ e.target) (hχ : ∀ᶠ z in 𝓝 y, χ z = 1)
    (hχ₂ : ∀ᶠ z in 𝓝 y, χ₂ z = 1) (hη : η ≠ 0) :
    ∃ c₀ : ClassicalSymbol n ℂ ℂ (m' + m - 1),
      ClassicalSymbol.inclusion 1 (by simp) c₀ = a.sharpCommutator b
        (hasCompactSpatialSupport_of_eq_complexChartCompression he ha)
        (hasCompactSpatialSupport_of_eq_complexChartCompression he hb) ∧
      c₀.principal.coefficient (y, η) 1 = -Complex.I * ∑ k,
        (fderiv ℝ (chartClassicalPrincipalSymbol m' P e) (y, η) (0, EuclideanSpace.single k 1) *
            fderiv ℝ (chartClassicalPrincipalSymbol m Q e) (y, η) (EuclideanSpace.single k 1, 0) -
          fderiv ℝ (chartClassicalPrincipalSymbol m' P e) (y, η) (EuclideanSpace.single k 1, 0) *
            fderiv ℝ (chartClassicalPrincipalSymbol m Q e) (y, η)
              (0, EuclideanSpace.single k 1)) := by
  obtain ⟨c₀, hc₀, hσ₀⟩ := ClassicalSymbol.exists_inclusion_eq_sharpCommutator_of_scalar a b
    (hasCompactSpatialSupport_of_eq_complexChartCompression he ha)
    (hasCompactSpatialSupport_of_eq_complexChartCompression he hb)
  refine ⟨c₀, hc₀, ?_⟩
  have hlin (f : ℂ →L[ℂ] ℂ) (w : ℂ) : f w = f 1 * w := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [hσ₀]
  simp only [smul_apply, sum_apply, sub_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    fderiv_chartClassicalPrincipalSymbol hP he ha hy hχ hχ₂ hη,
    fderiv_chartClassicalPrincipalSymbol hQ he hb hy hχ hχ₂ hη,
    HomogeneousSymbol.coefficient_frequencyDeriv_eq_fderiv _ _ hη,
    HomogeneousSymbol.coefficient_spatialDeriv_eq_fderiv]
  refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ ?_)
  rw [hlin (fderiv ℝ a.principal.coefficient (y, η) (0, EuclideanSpace.single k 1)),
    hlin (fderiv ℝ a.principal.coefficient (y, η) (EuclideanSpace.single k 1, 0))]

/-- **The Poisson bracket formula.** Let `P` and `Q` be classical pseudodifferential operators of
orders `m'` and `m` on `M`, so that their commutator `⁅P, Q⁆ = P ∘ Q - Q ∘ P` has order
`m' + m - 1`. Read the principal symbols `p = σ_{m'}(P)` and `q = σ_m(Q)` in a chart `e` as
functions of a position `y` and a frequency `η` (`TauCeti.chartClassicalPrincipalSymbol`). Then at
every point of the chart target and every nonzero frequency,

`σ_{m'+m-1}(⁅P, Q⁆) = -i {p, q}`, `{p, q} = ∑ₖ (∂_{ηₖ} p ∂_{yₖ} q - ∂_{yₖ} p ∂_{ηₖ} q)`,

`-i` times the Poisson bracket of the principal symbols. -/
theorem chartClassicalPrincipalSymbol_lie {m m' : ℝ}
    (hP : P ∈ classicalPseudodifferentialOperators m')
    (hQ : Q ∈ classicalPseudodifferentialOperators m) {y η : CoordinateSpace n}
    (hy : y ∈ e.target) (hη : η ≠ 0) :
    chartClassicalPrincipalSymbol (m' + m - 1) ⁅P, Q⁆ e (y, η) =
      -Complex.I * ∑ k,
        (fderiv ℝ (chartClassicalPrincipalSymbol m' P e) (y, η) (0, EuclideanSpace.single k 1) *
            fderiv ℝ (chartClassicalPrincipalSymbol m Q e) (y, η) (EuclideanSpace.single k 1, 0) -
          fderiv ℝ (chartClassicalPrincipalSymbol m' P e) (y, η) (EuclideanSpace.single k 1, 0) *
            fderiv ℝ (chartClassicalPrincipalSymbol m Q e) (y, η)
              (0, EuclideanSpace.single k 1)) := by
  -- Cutoffs in the chart: `φ = 1` near `y`, `θ = 1` near the support of `φ`, `χ = 1` near the
  -- support of `θ`, and `χ₂ = 1` near the support of `χ`.
  obtain ⟨φ, hφy⟩ := TestFunction.exists_eventually_eq_one_nhds (n := ⊤)
    (Ω := ⟨e.target, e.open_target⟩) hy
  obtain ⟨θ, hθ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    (Ω := ⟨e.target, e.open_target⟩) φ.hasCompactSupport.isCompact φ.tsupport_subset
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    (Ω := ⟨e.target, e.open_target⟩) θ.hasCompactSupport.isCompact θ.tsupport_subset
  obtain ⟨χ₂, hχ₂, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    (Ω := ⟨e.target, e.open_target⟩) χ.hasCompactSupport.isCompact χ.tsupport_subset
  have hθφ : ∀ z ∈ tsupport φ, θ z = 1 := fun z hz ↦ hθ.self_of_nhdsSet z hz
  have hχ₂χ : ∀ z ∈ tsupport χ, χ₂ z = 1 := fun z hz ↦ hχ₂.self_of_nhdsSet z hz
  have hχφ : ∀ z ∈ tsupport φ, χ z = 1 := fun z hz ↦
    hχ.self_of_nhdsSet z (subset_tsupport _ (by simp [hθφ z hz]))
  have hχ₂φ : ∀ z ∈ tsupport φ, χ₂ z = 1 := fun z hz ↦
    hχ₂χ z (subset_tsupport _ (by simp [hχφ z hz]))
  have hφsupp : ∀ᶠ z in 𝓝 y, z ∈ tsupport φ :=
    hφy.mono fun z hz ↦ subset_tsupport _ (by simp [hz])
  -- The chart symbols: `a` of `P` and `b` of `Q` by `χ` and `χ₂`, `s` of `⁅P, Q⁆` by `φ` and
  -- `φ`, `d` of its part away from the diagonal, and `c₀` of the commutator `a # b - b # a`.
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 e he χ χ₂
  obtain ⟨b, hb⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hQ).2 e he χ χ₂
  have hPQ := lie_mem_classicalPseudodifferentialOperators hP hQ
  obtain ⟨s, hs⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hPQ).2 e he φ φ
  obtain ⟨d, hd⟩ := (mem_classicalPseudodifferentialOperators_iff.1
    (mulLeft_comp_comp_mulLeft_one_sub_comp_sub_mem he hP hQ hχ)).2 e he φ φ
  obtain ⟨c₀, hc₀, hσ₀⟩ := exists_inclusion_eq_sharpCommutator_and_coefficient_principal_eq he
    hP hQ ha hb hy (hφsupp.mono hχφ) (hφsupp.mono hχ₂φ) hη
  -- In the chart `s = φ (c₀ # φ) + d`, so `s` and `c₀` have the same principal symbol at `y`.
  have hσ := coefficient_principal_eq_of_coefficient_eq_compress_add c₀ s d.toSymbol φ.contDiff
    φ.hasCompactSupport (coefficient_eq_compress_add_of_sharpCommutator hc₀ φ.contDiff
      φ.hasCompactSupport fun u z ↦ by
      rw [hs, complexChartCompression_lie_apply he hθφ hχφ hχ₂χ hχ₂φ ha hb, hd]) hφy η
  have hL : s.principal.coefficient (y, η) 1 =
      chartClassicalPrincipalSymbol (m' + m - 1) ⁅P, Q⁆ e (y, η) :=
    (eventuallyEq_chartClassicalPrincipalSymbol hPQ he hs hy hφy hφy η).self_of_nhds
  rw [← hL, hσ, hσ₀]

end PoissonBracket

/-! ### Square partitions of unity -/

section SquarePartition

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m : ℝ} {ι : Type*} {s : Finset ι}

/-- **Square partitions reproduce an operator modulo order `m - 2`.** If `P` is a classical
pseudodifferential operator of order `m` and the smooth functions `gᵢ` satisfy `∑ᵢ gᵢ² = 1`, then
`∑ᵢ gᵢ P gᵢ - P` has order `m - 2`, not only `m - 1`: it is `-½ ∑ᵢ ⁅gᵢ, ⁅gᵢ, P⁆⁆`, and each
commutator with a multiplication operator lowers the order by one. -/
theorem sum_mulLeft_comp_comp_mulLeft_sub_mem_classicalPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m)
    {g : ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} (hg : ∑ i ∈ s, g i ^ 2 = 1) :
    ∑ i ∈ s, LinearMap.mulLeft ℂ (g i) ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ (g i) - P ∈
      classicalPseudodifferentialOperators (m - 2) := by
  set A := fun i ↦ LinearMap.mulLeft ℂ (g i)
  -- Composition in `Module.End` is multiplication.
  have hcomp : ∑ i ∈ s, LinearMap.mulLeft ℂ (g i) ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ (g i) =
      ∑ i ∈ s, A i * P * A i := by
    simp only [A, Module.End.mul_eq_comp, LinearMap.comp_assoc]
  have hA : ∑ i ∈ s, A i * A i = 1 := by
    ext u : 1
    rw [LinearMap.sum_apply, one_apply_eq_self]
    calc ∑ i ∈ s, (A i * A i) u = (∑ i ∈ s, g i ^ 2) * u := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp only [A, mul_apply_eq_comp, LinearMap.mulLeft_apply, sq, mul_assoc]
      _ = u := by rw [hg, one_mul]
  -- `∑ᵢ ⁅gᵢ, ⁅gᵢ, P⁆⁆ = 2 (P - ∑ᵢ gᵢ P gᵢ)`.
  have key : ∑ i ∈ s, ⁅A i, ⁅A i, P⁆⁆ = (2 : ℂ) • (P - ∑ i ∈ s, A i * P * A i) := by
    have hexp (i : ι) : ⁅A i, ⁅A i, P⁆⁆ =
        A i * A i * P - A i * P * A i - A i * P * A i + P * (A i * A i) := by
      rw [Ring.lie_def, Ring.lie_def, mul_sub, sub_mul]
      simp only [mul_assoc]
      abel
    rw [Finset.sum_congr rfl fun i _ ↦ hexp i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hA, one_mul, mul_one, two_smul]
    abel
  have hmem : ∑ i ∈ s, ⁅A i, ⁅A i, P⁆⁆ ∈ classicalPseudodifferentialOperators (m - 2) :=
    Submodule.sum_mem _ fun i _ ↦ by
      simpa [sub_sub, one_add_one_eq_two] using lie_mulLeft_mem_classicalPseudodifferentialOperators
        (lie_mulLeft_mem_classicalPseudodifferentialOperators hP (g i)) (g i)
  have h := Submodule.smul_mem _ (-(1 / 2 : ℂ)) hmem
  rwa [key, smul_smul, show -(1 / 2 : ℂ) * 2 = -1 by norm_num, neg_one_smul, neg_sub, ← hcomp]
    at h

variable {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  {he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {ρ φ ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ)} {a : ι → ClassicalSymbol n ℂ ℂ m}

/-- **Symmetric quantization over a square partition of unity.** Let `ρᵢ` be cutoffs in charts
`eᵢ` whose squares, read on `M`, add up to `1`, and `aᵢ` the symbol of the chart compression of a
classical pseudodifferential operator `P` of order `m` by `ρᵢ` and `ρᵢ`. If `φᵢ` and `ψᵢ` are
cutoffs equal to `1` on the supports of the `ρᵢ`, the symmetric patched operator `∑ᵢ Op_{eᵢ}(aᵢ)`,
localized by `φᵢ` on the left and `ψᵢ` on the right, is `∑ᵢ ρᵢ P ρᵢ`, and it differs from `P` by an
operator of order `m - 2`. -/
theorem sum_chartQuantization_sub_mem_classicalPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hρ : ∑ i ∈ s, (e i).complexCutoffPullback (he i) (ρ i) 1 ^ 2 = 1)
    (ha : ∀ i ∈ s, ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
      quantizeSchwartzValue (a i).toSymbol.coefficient u x =
        (e i).complexChartCompression (he i) (ρ i) (ρ i) P
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    (hφ : ∀ i ∈ s, EqOn (φ i) 1 (tsupport (ρ i)))
    (hψ : ∀ i ∈ s, EqOn (ψ i) 1 (tsupport (ρ i))) :
    ∑ i ∈ s, (e i).chartQuantization (he i) (φ i) (ψ i) (a i) - P ∈
      classicalPseudodifferentialOperators (m - 2) := by
  rw [Finset.sum_congr rfl fun i hi ↦ (e i).chartQuantization_eq_mulLeft_comp_comp_mulLeft (he i)
    (ha i hi) (hφ i hi) (hψ i hi)]
  exact sum_mulLeft_comp_comp_mulLeft_sub_mem_classicalPseudodifferentialOperators hP hρ

/-- **The symmetric and the ordinary patched quantizations differ by order `m - 2`.** The symmetric
quantization of `P` over a square partition of unity
(`TauCeti.sum_chartQuantization_sub_mem_classicalPseudodifferentialOperators`) and the ordinary
quantization over a partition of unity
(`TauCeti.sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators`) differ by an
operator of order `m - 2`. -/
theorem sum_chartQuantization_sub_sum_chartQuantization_mem_classicalPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hρ : ∑ i ∈ s, (e i).complexCutoffPullback (he i) (ρ i) 1 ^ 2 = 1)
    (ha : ∀ i ∈ s, ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
      quantizeSchwartzValue (a i).toSymbol.coefficient u x =
        (e i).complexChartCompression (he i) (ρ i) (ρ i) P
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    (hφ : ∀ i ∈ s, EqOn (φ i) 1 (tsupport (ρ i))) (hψ : ∀ i ∈ s, EqOn (ψ i) 1 (tsupport (ρ i)))
    {κ : Type*} {t : Finset κ}
    {e' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
    {he' : ∀ j, e' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
    {ρ' χ' φ' ψ' : ∀ j, 𝓓(⟨(e' j).target, (e' j).open_target⟩, ℝ)}
    {b : κ → ClassicalSymbol n ℂ ℂ m}
    (hρ' : ∑ j ∈ t, (e' j).complexCutoffPullback (he' j) (ρ' j) 1 = 1)
    (hχ' : ∀ j ∈ t, ∀ᶠ y in 𝓝ˢ (tsupport (ρ' j)), χ' j y = 1)
    (hb : ∀ j ∈ t, ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
      quantizeSchwartzValue (b j).toSymbol.coefficient u x =
        (e' j).complexChartCompression (he' j) (ρ' j) (χ' j) P
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    (hφ' : ∀ j ∈ t, EqOn (φ' j) 1 (tsupport (ρ' j)))
    (hψ' : ∀ j ∈ t, EqOn (ψ' j) 1 (tsupport (χ' j))) :
    ∑ i ∈ s, (e i).chartQuantization (he i) (φ i) (ψ i) (a i) -
        ∑ j ∈ t, (e' j).chartQuantization (he' j) (φ' j) (ψ' j) (b j) ∈
      classicalPseudodifferentialOperators (m - 2) := by
  rw [← sub_add_sub_cancel _ P]
  exact add_mem (sum_chartQuantization_sub_mem_classicalPseudodifferentialOperators hP hρ ha hφ hψ)
    (smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators _
      (sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators hP hρ' hχ' hb hφ' hψ'))

end SquarePartition

end TauCeti
