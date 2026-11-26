/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.PrincipalSymbol
public import TauCeti.Analysis.Pseudodifferential.Manifold.Smoothing
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Pseudodifferential.Composition.Classical
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
import TauCeti.Geometry.Manifold.IsManifold.MaximalAtlas

/-!
# Composition of classical pseudodifferential operators on a manifold

Let `M` be a manifold modelled on `ℝⁿ`. This file shows that the classical pseudodifferential
operators on `M` (`TauCeti.classicalPseudodifferentialOperators`) are closed under composition: if
`P` has order `m'` and `Q` has order `m`, then `P ∘ Q` has order `m' + m`
(`TauCeti.comp_mem_classicalPseudodifferentialOperators`). In particular the operators of order
`0` are closed under composition. Composition is what parametrices on a manifold need: a
parametrix `Q` of an elliptic `P` is checked through the compositions `P ∘ Q` and `Q ∘ P`.

The principal symbol is multiplicative:

`σ_{m'+m}(P ∘ Q)(x, ξ) = σ_{m'}(P)(x, ξ) σ_m(Q)(x, ξ)`

(`TauCeti.classicalPrincipalSymbol_comp`). As these principal symbols are scalar, the commutator
`⁅P, Q⁆` has order `m' + m - 1` (`TauCeti.lie_mem_classicalPseudodifferentialOperators`); for
instance the commutator of `P` with multiplication by a smooth function has order `m - 1`
(`TauCeti.lie_mulLeft_mem_classicalPseudodifferentialOperators`).

An operator `L` on the complex-valued smooth functions on `M` is **local** when `L f` vanishes at
every point near which `f` vanishes; differential operators are the main examples. When one factor
is local, the composition is already seen in a single chart
(`TauCeti.comp_mem_classicalPseudodifferentialOperators_of_local_left` and
`TauCeti.comp_mem_classicalPseudodifferentialOperators_of_local_right`). In particular a classical
pseudodifferential operator can be composed on either side with the complexification of a
differential operator `D` of order `k`, and then the principal symbol of the composition is
`i ^ k σ(D)(ξ) σ_m(P)(x, ξ)` at nonzero covectors, where `σ(D)` is the geometric principal symbol
of `D` (`TauCeti.classicalPrincipalSymbol_complexifyLinearMap_comp`).

## The general composition

Fix a chart `e` and cutoffs `φ`, `ψ` in its target. The operator `Q` is properly supported, so it
sends the functions supported in `e⁻¹(supp ψ)` to functions supported in a compact set `K'`, which
need not lie in the source of `e`. A partition of unity `ρᵢ` on `K'` splits the compression of
`P ∘ Q` into the compressions of `P ∘ (ρᵢ Q)`. Each `ρᵢ` is supported in the source of a chart `Eᵢ`
that agrees with `e` over the supports of `φ` and `ψ`: either `e` itself, or, when the support of
`ρᵢ` leaves the source of `e`, a chart made of a neighbourhood of `e⁻¹(supp φ ∪ supp ψ)` read
through `e` and a neighbourhood of the support of `ρᵢ`, with disjoint images in `ℝⁿ`
(`IsCompact.exists_smoothPartition_mem_maximalAtlas_eqOn_symm`). Such a chart exists in
positive dimension because the maximal atlas contains every chart, not only those of a fixed
atlas.

In the chart `Eᵢ`, with a cutoff `χᵢ` equal to `1` on the image of the support of `ρᵢ`, the
compression of `P ∘ (ρᵢ Q)` is the compression of `P` by `φ` and `χᵢ` after that of `ρᵢ Q` by `χᵢ`
and `ψ` (`OpenPartialHomeomorph.complexChartCompression_comp_apply`). These are `Op(aᵢ)` and
`Op(bᵢ)` for classical symbols of orders `m'` and `m`, and `bᵢ` vanishes at positions outside the
support of `χᵢ`. So their composition is `Op(aᵢ # bᵢ)`, with `aᵢ # bᵢ` classical of order `m' + m`
(`TauCeti.ClassicalSymbol.sharp`), and the compression of `P ∘ Q` is the quantization of
`∑ᵢ aᵢ # bᵢ`. No smoothing remainder has to be estimated separately: the parts of `P ∘ Q` between
distant points are part of the compressions in the charts `Eᵢ`.

In dimension `0` every properly supported operator has every order
(`TauCeti.mem_classicalPseudodifferentialOperators_of_dim_eq_zero`), so only proper support has to
be checked (`TauCeti.IsProperlySupported.comp`).

## The principal symbol of a composition

In the preferred chart `e` at `x`, let `X` be a cutoff equal to `1` near `x`, read on `M`, and split
`P ∘ Q = P X Q + P (1 - X) Q`. The part `P X Q` is seen in the chart: its compression is
`Op(a # b)` for chart symbols `a` of `P` and `b` of `Q`, since the factor `X` keeps the output of
`Q` inside the chart, and the principal symbol of `a # b` is the product of those of `a` and `b`.
The rest `P (1 - X) Q` has vanishing principal symbol at `x`: near `x` it agrees with
`Θ P (1 - X) Q` for a cutoff `Θ` equal to `1` near `x` and supported where `X = 1`, and
`Θ P (1 - X)` has order `-∞` by pseudolocality
(`TauCeti.mulLeft_comp_comp_mulLeft_mem_smoothingPseudodifferentialOperators`).

## Composition with a local operator

Locality is what makes a composition visible in a single chart `e`. Let `φ`, `ψ` be cutoffs in the
chart target, and `g = (ψ u) ∘ e` for a Schwartz function `u`. Choose cutoffs `χ` equal to `1` near
the support of `φ`, and `χ₂` equal to `1` on the support of `χ`. Since `L` is local, `L (P g)`
agrees near the support of `φ ∘ e` with `L ((χ ∘ e) P g)`, and `(χ ∘ e) P g` is the pullback by
`χ₂` of the chart compression `v = χ · (P g) ∘ e⁻¹`. So the compression of `L ∘ P` by `φ` and `ψ` is
the compression of `L` by `φ` and `χ₂` applied to `v`, that is `Op(a) (Op(b) u)` for the chart
symbols `a` of `L` and `b` of `P`. The symbol `b` vanishes at positions outside the support of `χ`,
so the composition theorem for symbols of compact spatial support
(`TauCeti.Symbol.quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue`) gives
`Op(a) ∘ Op(b) = Op(a # b)`, and `a # b` is a classical symbol of order `k + m`
(`TauCeti.ClassicalSymbol.sharp`) whose principal symbol is the product of those of `a` and `b`
(`TauCeti.ClassicalSymbol.principal_sharp`). For `P ∘ L` the roles are exchanged: `L g` is
supported in the support of `g`, so it is the pullback by `χ₂` of the compression of `L` by `χ`
and `ψ`, for `χ` equal to `1` on the support of `ψ`.

## Main results

* `TauCeti.comp_mem_classicalPseudodifferentialOperators`: the composition of classical
  pseudodifferential operators of orders `m'` and `m` is classical of order `m' + m`.
* `TauCeti.comp_mem_smoothingPseudodifferentialOperators_of_left`,
  `TauCeti.comp_mem_smoothingPseudodifferentialOperators_of_right`: the operators of order `-∞`
  form a two-sided ideal in the classical pseudodifferential operators of all orders.
* `TauCeti.pow_mem_classicalPseudodifferentialOperators`: the `k`-th power of a classical
  pseudodifferential operator of order `m` is classical of order `k m`.
* `TauCeti.comp_mem_classicalPseudodifferentialOperators_of_local_left` and
  `TauCeti.comp_mem_classicalPseudodifferentialOperators_of_local_right`: the composition of a
  classical pseudodifferential operator with a local one, on either side, is a classical
  pseudodifferential operator, and the orders add.
* `TauCeti.classicalPrincipalSymbol_comp`: the principal symbol of a composition is the product
  of the principal symbols.
* `TauCeti.lie_mem_classicalPseudodifferentialOperators` and
  `TauCeti.lie_mulLeft_mem_classicalPseudodifferentialOperators`: commutators, for instance with
  multiplication by smooth functions, lose one order.
* `TauCeti.classicalPrincipalSymbol_comp_mulLeft`: multiplying an operator on the right by a smooth
  function `g` multiplies its principal symbol at `x` by `g(x)`.
* `TauCeti.complexifyLinearMap_comp_mem_classicalPseudodifferentialOperators`,
  `TauCeti.comp_complexifyLinearMap_mem_classicalPseudodifferentialOperators`,
  `TauCeti.classicalPrincipalSymbol_complexifyLinearMap_comp` and
  `TauCeti.classicalPrincipalSymbol_comp_complexifyLinearMap`: the same for the complexification
  of a differential operator, whose principal symbol is `i ^ k` times its geometric one.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.8
  (composition of pseudodifferential operators on `ℝⁿ`) and the discussion after Definition
  18.1.20 (operators on manifolds).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §§2 and 8.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  {L P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} [T2Space M]

/-! ### Chart symbols of compositions -/

section Chart

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)

include he

/-- For the symbol `b` of the chart compression of `P` by `χ` and `ψ`, the Schwartz function
`Op(b) u`, pulled back to `M` by a cutoff `χ₂` equal to `1` on the support of `χ`, is
`(χ ∘ e) · P ((ψ u) ∘ e)` on the chart source. -/
private theorem complexCutoffPullback_apply_of_eq_complexChartCompression {m : ℝ}
    {χ χ₂ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hχ₂ : ∀ y ∈ tsupport χ, χ₂ y = 1)
    {b : ClassicalSymbol n ℂ ℂ m}
    (hb : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue b.toSymbol.coefficient u y =
        e.complexChartCompression he χ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (u : 𝓢(CoordinateSpace n, ℂ)) {q : M} (hq : q ∈ e.source) :
    e.complexCutoffPullback he χ₂ (ContMDiffMap.ofContDiff
      (((hasCompactSpatialSupport_of_eq_complexChartCompression he
        hb).hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
          (b.toSymbol.contDiff_quantizeSchwartzValue u)) (SchwartzMap.smooth _ ⊤)) q =
      χ (e q) • P (e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff u (u.smooth ⊤))) q := by
  rw [OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he _ _ hq,
    ContMDiffMap.coe_ofContDiff, HasCompactSupport.toSchwartzMap_toFun, hb,
    OpenPartialHomeomorph.complexChartCompression_apply, e.left_inv hq]
  by_cases hχ : χ (e q) = 0
  · simp [hχ]
  · rw [hχ₂ _ (subset_tsupport _ hχ), one_smul]

/-- **The chart symbol of `L ∘ P` for a local `L`.** If `χ` equals `1` near the support of `φ`
and `χ₂` equals `1` on the support of `χ`, and `a`, `b` are the symbols of the compressions of `L`
by `φ`, `χ₂` and of `P` by `χ`, `ψ`, then `a # b` is the symbol of the compression of `L ∘ P` by
`φ` and `ψ`. -/
private theorem quantizeSchwartzValue_sharp_eq_complexChartCompression_comp_of_local_left
    (hL : ∀ f x, (∀ᶠ y in 𝓝 x, f y = 0) → L f x = 0) {k m : ℝ}
    {φ ψ χ χ₂ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hχ : ∀ᶠ y in 𝓝ˢ (tsupport φ), χ y = 1)
    (hχ₂ : ∀ y ∈ tsupport χ, χ₂ y = 1) {a : ClassicalSymbol n ℂ ℂ k}
    {b : ClassicalSymbol n ℂ ℂ m}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he φ χ₂ L (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (hb : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue b.toSymbol.coefficient u y =
        e.complexChartCompression he χ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.sharp b
        (hasCompactSpatialSupport_of_eq_complexChartCompression he hb)).toSymbol.coefficient u x =
      e.complexChartCompression he φ ψ (L ∘ₗ P) (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x := by
  rw [ClassicalSymbol.toSymbol_sharp, Symbol.quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue,
    ha, OpenPartialHomeomorph.complexChartCompression_apply,
    OpenPartialHomeomorph.complexChartCompression_apply, LinearMap.comp_apply]
  by_cases hφ : φ x = 0
  · simp [hφ]
  -- Near `q = e⁻¹ x`, the pullback of `Op(b) u` is `P ((ψ u) ∘ e)`, since `χ = 1` near `x`.
  have hx : x ∈ e.target := φ.tsupport_subset (subset_tsupport _ hφ)
  have hq : e.symm x ∈ e.source := e.map_target hx
  congr 1
  refine apply_eq_of_eventuallyEq_of_local hL ?_
  have hχx : ∀ᶠ q in 𝓝 (e.symm x), χ (e q) = 1 :=
    (e.continuousAt hq).eventually (show ∀ᶠ y in 𝓝 (e (e.symm x)), χ y = 1 by
      rw [e.right_inv hx]
      exact hχ.filter_mono (nhds_le_nhdsSet (subset_tsupport _ hφ)))
  filter_upwards [hχx, e.open_source.mem_nhds hq] with q hχq hq'
  rw [complexCutoffPullback_apply_of_eq_complexChartCompression he hχ₂ hb u hq', hχq, one_smul]

/-- **The chart symbol of `P ∘ L` for a local `L`.** If `χ` equals `1` on the support of `ψ` and
`χ₂` equals `1` on the support of `χ`, and `a`, `d` are the symbols of the compressions of `P` by
`φ`, `χ₂` and of `L` by `χ`, `ψ`, then `a # d` is the symbol of the compression of `P ∘ L` by `φ`
and `ψ`. -/
private theorem quantizeSchwartzValue_sharp_eq_complexChartCompression_comp_of_local_right
    (hL : ∀ f x, (∀ᶠ y in 𝓝 x, f y = 0) → L f x = 0) {k m : ℝ}
    {φ ψ χ χ₂ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hχ : ∀ y ∈ tsupport ψ, χ y = 1)
    (hχ₂ : ∀ y ∈ tsupport χ, χ₂ y = 1) {a : ClassicalSymbol n ℂ ℂ m}
    {d : ClassicalSymbol n ℂ ℂ k}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he φ χ₂ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (hd : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue d.toSymbol.coefficient u y =
        e.complexChartCompression he χ ψ L (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.sharp d
        (hasCompactSpatialSupport_of_eq_complexChartCompression he hd)).toSymbol.coefficient u x =
      e.complexChartCompression he φ ψ (P ∘ₗ L) (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x := by
  rw [ClassicalSymbol.toSymbol_sharp, Symbol.quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue,
    ha, OpenPartialHomeomorph.complexChartCompression_apply,
    OpenPartialHomeomorph.complexChartCompression_apply, LinearMap.comp_apply]
  -- `L g` is the pullback of `Op(d) u`, for `g = (ψ u) ∘ e`: both vanish off the support of `g`,
  -- which lies in the chart source where `χ ∘ e = 1`.
  set g := e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff u (u.smooth ⊤))
  congr 3
  ext q
  by_cases hqg : q ∈ tsupport g
  · obtain ⟨y, hy, rfl⟩ := e.tsupport_complexCutoffPullback_subset he ψ _ hqg
    have hq : e.symm y ∈ e.source := e.map_target (ψ.tsupport_subset hy)
    rw [complexCutoffPullback_apply_of_eq_complexChartCompression he hχ₂ hd u hq,
      e.right_inv (ψ.tsupport_subset hy), hχ y hy, one_smul]
  · rw [apply_eq_zero_of_notMem_tsupport_of_local hL hqg]
    by_cases hq : q ∈ e.source
    · rw [complexCutoffPullback_apply_of_eq_complexChartCompression he hχ₂ hd u hq,
        apply_eq_zero_of_notMem_tsupport_of_local hL hqg, smul_zero]
    · exact OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he _ _ hq

end Chart

omit [ChartedSpace (CoordinateSpace n) M] [T2Space M] in
/-- A cutoff in the target of the chart `e`, equal to `1` near a compact subset of the target. -/
private theorem exists_cutoff_eventually_eq_one {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hKe : K ⊆ e.target) :
    ∃ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ), ∀ᶠ y in 𝓝ˢ K, χ y = 1 :=
  (TestFunction.exists_eventually_eq_one (Ω := ⟨e.target, e.open_target⟩) (n := ⊤) hK
    hKe).imp fun _ h ↦ h.1

omit [ChartedSpace (CoordinateSpace n) M] [T2Space M] in
/-- Nested cutoffs in the target of the chart `e`: `χ` equal to `1` near a compact subset of the
target, and `χ₂` equal to `1` on the support of `χ`. -/
private theorem exists_nested_cutoffs {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hKe : K ⊆ e.target) :
    ∃ χ χ₂ : 𝓓(⟨e.target, e.open_target⟩, ℝ),
      (∀ᶠ y in 𝓝ˢ K, χ y = 1) ∧ ∀ y ∈ tsupport χ, χ₂ y = 1 := by
  obtain ⟨χ, hχ⟩ := exists_cutoff_eventually_eq_one hK hKe
  obtain ⟨χ₂, hχ₂⟩ := exists_cutoff_eventually_eq_one χ.hasCompactSupport.isCompact
    χ.tsupport_subset
  exact ⟨χ, χ₂, hχ, hχ₂.self_of_nhdsSet⟩

/-! ### Composition with a local operator -/

/-- **Composition on the left with a local operator.** If `L` is a local classical
pseudodifferential operator of order `k`, such as a differential operator, and `P` a classical
pseudodifferential operator of order `m`, then `L ∘ P` is a classical pseudodifferential operator of
order `k + m`. -/
theorem comp_mem_classicalPseudodifferentialOperators_of_local_left {k m : ℝ}
    (hL : L ∈ classicalPseudodifferentialOperators k)
    (hLloc : ∀ f x, (∀ᶠ y in 𝓝 x, f y = 0) → L f x = 0)
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    L ∘ₗ P ∈ classicalPseudodifferentialOperators (k + m) := by
  obtain ⟨hL₁, hL₂⟩ := mem_classicalPseudodifferentialOperators_iff.1 hL
  obtain ⟨hP₁, hP₂⟩ := mem_classicalPseudodifferentialOperators_iff.1 hP
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨hL₁.comp hP₁, fun e he φ ψ ↦ ?_⟩
  obtain ⟨χ, χ₂, hχ, hχ₂⟩ := exists_nested_cutoffs φ.hasCompactSupport.isCompact φ.tsupport_subset
  obtain ⟨a, ha⟩ := hL₂ e he φ χ₂
  obtain ⟨b, hb⟩ := hP₂ e he χ ψ
  exact ⟨_, quantizeSchwartzValue_sharp_eq_complexChartCompression_comp_of_local_left he hLloc hχ
    hχ₂ ha hb⟩

/-- **Composition on the right with a local operator.** If `L` is a local classical
pseudodifferential operator of order `k`, such as a differential operator, and `P` a classical
pseudodifferential operator of order `m`, then `P ∘ L` is a classical pseudodifferential operator of
order `m + k`. -/
theorem comp_mem_classicalPseudodifferentialOperators_of_local_right {k m : ℝ}
    (hL : L ∈ classicalPseudodifferentialOperators k)
    (hLloc : ∀ f x, (∀ᶠ y in 𝓝 x, f y = 0) → L f x = 0)
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    P ∘ₗ L ∈ classicalPseudodifferentialOperators (m + k) := by
  obtain ⟨hL₁, hL₂⟩ := mem_classicalPseudodifferentialOperators_iff.1 hL
  obtain ⟨hP₁, hP₂⟩ := mem_classicalPseudodifferentialOperators_iff.1 hP
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨hP₁.comp hL₁, fun e he φ ψ ↦ ?_⟩
  obtain ⟨χ, χ₂, hχ, hχ₂⟩ := exists_nested_cutoffs ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  obtain ⟨a, ha⟩ := hP₂ e he φ χ₂
  obtain ⟨d, hd⟩ := hL₂ e he χ ψ
  exact ⟨_, quantizeSchwartzValue_sharp_eq_complexChartCompression_comp_of_local_right he hLloc
    hχ.self_of_nhdsSet hχ₂ ha hd⟩

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-! ### Composition of two classical pseudodifferential operators -/

section General

variable {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
  C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m m' : ℝ}

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- **One piece of the composition.** Let `ρ` be a smooth function with compact support in the
source of a chart `E` that agrees with the chart `e` over the supports of the cutoffs `φ` and `ψ`.
Then the compression of `P ∘ (ρ Q)` by `φ` and `ψ` in `e` is `Op(a # b)`, where `a` and `b` are the
symbols of the compressions of `P` and of `ρ Q` in `E`, through a cutoff `χ` equal to `1` on the
image of the support of `ρ`. -/
private theorem exists_quantizeSchwartzValue_eq_complexChartCompression_comp_mulLeft
    (hP : P ∈ classicalPseudodifferentialOperators m')
    (hQ : Q ∈ classicalPseudodifferentialOperators m)
    {e E : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (hE : E ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯}
    (hρc : IsCompact (tsupport ρ)) (hρE : tsupport ρ ⊆ E.source)
    (hCE : tsupport φ ∪ tsupport ψ ⊆ E.target)
    (hEe : EqOn E.symm e.symm (tsupport φ ∪ tsupport ψ)) :
    ∃ c : ClassicalSymbol n ℂ ℂ (m' + m), ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
      quantizeSchwartzValue c.toSymbol.coefficient u x =
        e.complexChartCompression he φ ψ
          (P ∘ₗ LinearMap.mulLeft ℂ (ContMDiffMap.ofReal ρ) ∘ₗ Q)
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x := by
  set Qρ := LinearMap.mulLeft ℂ (ContMDiffMap.ofReal ρ) ∘ₗ Q with hQρ
  -- The cutoffs `φ` and `ψ` read in the chart `E`, and a cutoff `χ` equal to `1` on the image of
  -- the support of `ρ`.
  let φ' : 𝓓(⟨E.target, E.open_target⟩, ℝ) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, subset_union_left.trans hCE⟩
  let ψ' : 𝓓(⟨E.target, E.open_target⟩, ℝ) :=
    ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, subset_union_right.trans hCE⟩
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    (Ω := ⟨E.target, E.open_target⟩) (hρc.image_of_continuousOn (E.continuousOn.mono hρE))
    (image_subset_iff.2 fun x hx ↦ E.map_source (hρE hx))
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 E hE φ' χ
  obtain ⟨b, hb⟩ := (mem_classicalPseudodifferentialOperators_iff.1
    (mulLeft_comp_mem_classicalPseudodifferentialOperators hQ (ContMDiffMap.ofReal ρ))).2 E hE χ ψ'
  -- The symbol of the compression of `ρ Q` vanishes off the support of `χ`.
  have hbs : b.toSymbol.HasCompactSpatialSupport :=
    Symbol.hasCompactSpatialSupport_iff_exists_tsupport_quantizeSchwartzValue_subset.2
      ⟨tsupport χ, χ.hasCompactSupport.isCompact, fun u _ ↦ closure_mono <|
        Function.support_subset_iff'.2 fun y hy ↦ by
          rw [hb u y, OpenPartialHomeomorph.complexChartCompression_apply,
            Function.notMem_support.1 hy, zero_smul]⟩
  refine ⟨a.sharp b hbs, fun u x ↦ ?_⟩
  set U := ContMDiffMap.ofContDiff u (u.smooth ⊤)
  -- The outputs of `ρ Q` lie in the source of `E`, at points where `χ ∘ E = 1`.
  have hfactor : ∀ y, Qρ (E.complexCutoffPullback hE ψ' U) y ≠ 0 →
      y ∈ E.source ∧ χ (E y) = 1 := fun y hy ↦ by
    have hρy : ρ y ≠ 0 := fun h ↦ hy (by simp [hQρ, h])
    exact ⟨hρE (subset_tsupport _ hρy),
      hχ.self_of_nhdsSet _ (mem_image_of_mem _ (subset_tsupport _ hρy))⟩
  set w := (hbs.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
    (b.toSymbol.contDiff_quantizeSchwartzValue u)
  have hw : ContMDiffMap.ofContDiff w (w.smooth ⊤) = E.complexChartCompression hE χ ψ' Qρ U := by
    ext y
    rw [ContMDiffMap.coe_ofContDiff, HasCompactSupport.toSchwartzMap_toFun, hb u y]
  rw [ClassicalSymbol.toSymbol_sharp, Symbol.quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue,
    ha, hw, ← OpenPartialHomeomorph.complexChartCompression_comp_apply _ _ _ _ _ _ hfactor,
    ← OpenPartialHomeomorph.complexChartCompression_congr he hE rfl rfl hEe.symm]

/-- **Composition of classical pseudodifferential operators.** If `P` is a classical
pseudodifferential operator of order `m'` and `Q` one of order `m` on a manifold modelled on `ℝⁿ`,
then `P ∘ Q` is a classical pseudodifferential operator of order `m' + m`. -/
theorem comp_mem_classicalPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m')
    (hQ : Q ∈ classicalPseudodifferentialOperators m) :
    P ∘ₗ Q ∈ classicalPseudodifferentialOperators (m' + m) := by
  have hPQ := (mem_classicalPseudodifferentialOperators_iff.1 hP).1.comp
    (mem_classicalPseudodifferentialOperators_iff.1 hQ).1
  rcases eq_or_ne n 0 with hn | hn
  · exact mem_classicalPseudodifferentialOperators_of_dim_eq_zero hn hPQ _
  have : NeZero n := ⟨hn⟩
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨hPQ, fun e he φ ψ ↦ ?_⟩
  -- `Q` sends the functions supported in `e⁻¹(supp ψ)` to functions supported in `K'`, and a
  -- partition of unity `ρᵢ` on `K'` splits `Q` there into pieces `ρᵢ Q`, each seen in a chart `Eᵢ`
  -- that agrees with `e` over the supports of `φ` and `ψ`.
  obtain ⟨K', hK', hQK', -⟩ :=
    isProperlySupported_iff.1 (mem_classicalPseudodifferentialOperators_iff.1 hQ).1 _
    (ψ.hasCompactSupport.isCompact.image_of_continuousOn
    (e.continuousOn_symm.mono ψ.tsupport_subset))
  obtain ⟨ι, _, ρ, E, hρ1, hE⟩ := hK'.exists_smoothPartition_mem_maximalAtlas_eqOn_symm he
    (φ.hasCompactSupport.isCompact.union ψ.hasCompactSupport.isCompact)
    (union_subset φ.tsupport_subset ψ.tsupport_subset)
  choose hEa hρc hρE hCE hEe using hE
  choose c hc using fun i ↦ exists_quantizeSchwartzValue_eq_complexChartCompression_comp_mulLeft
    hP hQ he (hEa i) φ ψ (hρc i) (hρE i) (hCE i) (hEe i)
  refine ⟨∑ i, c i, fun u x ↦ ?_⟩
  set F := e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff u (u.smooth ⊤))
  -- The pieces `ρᵢ Q F` add up to `Q F`, which is supported in `K'`.
  have hsplit : Q F = ∑ i, LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (ρ i)) (Q F) :=
    ContMDiffMap.eq_sum_mulLeft_ofReal _ ρ ((subset_tsupport _).trans
      (hQK' F (OpenPartialHomeomorph.tsupport_complexCutoffPullback_subset he ψ _))) hρ1
  simp only [ClassicalSymbol.toSymbol_sum, Symbol.quantizeSchwartzValue_sum_left, hc,
    OpenPartialHomeomorph.complexChartCompression_apply, LinearMap.comp_apply]
  rw [← Finset.smul_sum]
  conv_rhs => rw [hsplit, map_sum, ContMDiffMap.coe_sum, Finset.sum_apply]

/-- **Powers of classical pseudodifferential operators.** If `P` is a classical pseudodifferential
operator of order `m`, then `P ^ k` is one of order `k m`. -/
theorem pow_mem_classicalPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m) (k : ℕ) :
    P ^ k ∈ classicalPseudodifferentialOperators (k * m) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, Module.End.one_eq_id]
    exact id_mem_classicalPseudodifferentialOperators
  | succ k ih =>
    rw [pow_succ', Module.End.mul_eq_comp, Nat.cast_succ, add_one_mul, add_comm]
    exact comp_mem_classicalPseudodifferentialOperators hP ih

/-- **Operators of order `-∞` absorb composition on the right.** If `P` has order `-∞` and `Q` is
a classical pseudodifferential operator of some order `m`, then `P ∘ Q` has order `-∞`. -/
theorem comp_mem_smoothingPseudodifferentialOperators_of_left
    (hP : P ∈ smoothingPseudodifferentialOperators)
    (hQ : Q ∈ classicalPseudodifferentialOperators m) :
    P ∘ₗ Q ∈ smoothingPseudodifferentialOperators :=
  mem_smoothingPseudodifferentialOperators_iff.2 fun m' ↦ sub_add_cancel m' m ▸
    comp_mem_classicalPseudodifferentialOperators
      (mem_smoothingPseudodifferentialOperators_iff.1 hP (m' - m)) hQ

/-- **Operators of order `-∞` absorb composition on the left.** If `Q` is a classical
pseudodifferential operator of some order `m` and `P` has order `-∞`, then `Q ∘ P` has order
`-∞`. -/
theorem comp_mem_smoothingPseudodifferentialOperators_of_right
    (hQ : Q ∈ classicalPseudodifferentialOperators m)
    (hP : P ∈ smoothingPseudodifferentialOperators) :
    Q ∘ₗ P ∈ smoothingPseudodifferentialOperators :=
  mem_smoothingPseudodifferentialOperators_iff.2 fun m' ↦ add_sub_cancel m m' ▸
    comp_mem_classicalPseudodifferentialOperators hQ
      (mem_smoothingPseudodifferentialOperators_iff.1 hP (m' - m))

end General

/-! ### Principal symbols of compositions -/

section Principal

variable {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
  C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m m' : ℝ}

/-- **The principal symbol of a composition, read off in a chart.** Let `x` be a point of `M`
with chart `e`, `φ` a cutoff equal to `1` at `e x`, `χ` equal to `1` on the support of `φ`, and
`χ₂` equal to `1` on the support of `χ`. If `a` and `b` are the symbols of the compressions of
`B ∈ Ψ^k` by `φ`, `χ₂` and of `C ∈ Ψ^m` by `χ`, `φ`, and `a # b` is the symbol of the compression
of `A ∈ Ψ^{k+m}` by `φ`, `φ`, then `σ_{k+m}(A)(x, ξ) = σ_k(B)(x, ξ) σ_m(C)(x, ξ)`. -/
private theorem classicalPrincipalSymbol_eq_mul_of_eq_sharp
    {A B C : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {k m : ℝ}
    (hA : A ∈ classicalPseudodifferentialOperators (k + m))
    (hB : B ∈ classicalPseudodifferentialOperators k)
    (hC : C ∈ classicalPseudodifferentialOperators m)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {φ χ χ₂ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hχ : ∀ y ∈ tsupport φ, χ y = 1)
    (hχ₂ : ∀ y ∈ tsupport χ, χ₂ y = 1) {a : ClassicalSymbol n ℂ ℂ k}
    {b : ClassicalSymbol n ℂ ℂ m} (hb' : b.toSymbol.HasCompactSpatialSupport)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he φ χ₂ B (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (hb : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue b.toSymbol.coefficient u y =
        e.complexChartCompression he χ φ C (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (hab : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue (a.sharp b hb').toSymbol.coefficient u y =
        e.complexChartCompression he φ φ A (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    {x : M} (hx : x ∈ e.source) (hφx : φ (e x) = 1)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol (k + m) A x ξ =
      classicalPrincipalSymbol k B x ξ * classicalPrincipalSymbol m C x ξ := by
  have hχx : χ (e x) = 1 := hχ _ (subset_tsupport _ (by simp [hφx]))
  have hχ₂x : χ₂ (e x) = 1 := hχ₂ _ (subset_tsupport _ (by simp [hχx]))
  have hlin (f : ℂ →L[ℂ] ℂ) (w : ℂ) : f w = f 1 * w := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  have h := coefficient_principal_apply_eq_classicalPrincipalSymbol hA he φ φ hab hx ξ
  rw [ClassicalSymbol.principal_sharp, HomogeneousSymbol.coefficient_comp,
    ContinuousLinearMap.comp_apply, coefficient_principal_apply_eq_classicalPrincipalSymbol hC he
      χ φ hb hx ξ, hlin, coefficient_principal_apply_eq_classicalPrincipalSymbol hB he φ χ₂ ha hx ξ,
    hφx, hχx, hχ₂x] at h
  simp only [mul_one, Complex.ofReal_one, one_mul] at h
  exact h.symm

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- **The chart symbol of `P ∘ X Q`.** Let `X` be a cutoff `χ` in the chart target read on `M`,
`(χ ∘ e)` on the chart source and `0` off it, and let `χ₂` equal `1` on the support of `χ`. If `a`
and `b` are the symbols of the compressions of `P` by `φ`, `χ₂` and of `Q` by `χ`, `ψ`, then `a # b`
is the symbol of the compression of `P ∘ X Q` by `φ` and `ψ`: the factor `X` keeps the output of
`Q` inside the chart, where it is read off by `Op(b)`. -/
private theorem quantizeSchwartzValue_sharp_eq_complexChartCompression_comp_mulLeft_comp
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {φ ψ χ χ₂ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hχ₂ : ∀ y ∈ tsupport χ, χ₂ y = 1)
    {a : ClassicalSymbol n ℂ ℂ m'} {b : ClassicalSymbol n ℂ ℂ m}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he φ χ₂ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (hb : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue b.toSymbol.coefficient u y =
        e.complexChartCompression he χ ψ Q (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.sharp b
        (hasCompactSpatialSupport_of_eq_complexChartCompression he hb)).toSymbol.coefficient u x =
      e.complexChartCompression he φ ψ
        (P ∘ₗ LinearMap.mulLeft ℂ (e.complexCutoffPullback he χ 1) ∘ₗ Q)
        (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x := by
  rw [ClassicalSymbol.toSymbol_sharp, Symbol.quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue,
    ha, OpenPartialHomeomorph.complexChartCompression_apply,
    OpenPartialHomeomorph.complexChartCompression_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  -- The pullback of `Op(b) u` by `χ₂` is `X · Q ((ψ u) ∘ e)`, on the chart source and off it.
  congr 3
  ext q
  rw [LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply]
  by_cases hq : q ∈ e.source
  · rw [complexCutoffPullback_apply_of_eq_complexChartCompression he hχ₂ hb u hq,
      e.complexCutoffPullback_apply_of_mem he _ _ hq]
    simp [Complex.real_smul]
  · simp [OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he _ _ hq]

/-- **The part of a composition away from a point.** In a chart `e`, let `φ` be a cutoff equal to
`1` at `e x`, `θ` equal to `1` on the support of `φ`, and `χ` equal to `1` near the support of `θ`,
read on `M` as `X`. Then `P (1 - X) Q` has vanishing principal symbol of order `m' + m` at `x`:
its compression by `φ` is that of `Θ P (1 - X) Q`, where `Θ` is `θ` read on `M`, and
`Θ P (1 - X)` has order `-∞` by pseudolocality. -/
private theorem classicalPrincipalSymbol_comp_mulLeft_one_sub_comp_eq_zero
    (hP : P ∈ classicalPseudodifferentialOperators m')
    (hQ : Q ∈ classicalPseudodifferentialOperators m)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {φ θ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hθφ : ∀ y ∈ tsupport φ, θ y = 1)
    (hχ : ∀ᶠ y in 𝓝ˢ (tsupport θ), χ y = 1) {x : M} (hx : x ∈ e.source) (hφx : φ (e x) = 1)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol (m' + m)
      (P ∘ₗ LinearMap.mulLeft ℂ (1 - e.complexCutoffPullback he χ 1) ∘ₗ Q) x ξ = 0 := by
  set X := e.complexCutoffPullback he χ 1
  set Θ := e.complexCutoffPullback he θ 1
  have hPXQ := comp_mem_classicalPseudodifferentialOperators hP
    (mulLeft_comp_mem_classicalPseudodifferentialOperators hQ (1 - X))
  have hS : (LinearMap.mulLeft ℂ Θ ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ (1 - X)) ∘ₗ Q ∈
      classicalPseudodifferentialOperators (m' + m - 1) := by
    have h := comp_mem_classicalPseudodifferentialOperators
      (smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators (m' - 1)
        (mulLeft_comp_comp_mulLeft_mem_smoothingPseudodifferentialOperators hP
          (e.disjoint_tsupport_complexCutoffPullback_one_sub he hχ))) hQ
    rwa [sub_add_eq_add_sub] at h
  -- A chart symbol of `P (1 - X) Q` by `φ` is one of `Θ P (1 - X) Q`, since `θ = 1` where `φ ≠ 0`.
  obtain ⟨c, hc⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hPXQ).2 e he φ φ
  have hc' (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n) :
      quantizeSchwartzValue c.toSymbol.coefficient u y =
        e.complexChartCompression he φ φ
          ((LinearMap.mulLeft ℂ Θ ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ (1 - X)) ∘ₗ Q)
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y := by
    rw [hc, OpenPartialHomeomorph.complexChartCompression_apply,
      OpenPartialHomeomorph.complexChartCompression_apply]
    by_cases hy : φ y = 0
    · simp [hy]
    have hyt : y ∈ e.target := φ.tsupport_subset (subset_tsupport _ hy)
    simp [Θ, e.complexCutoffPullback_apply_of_mem he _ _ (e.map_target hyt), e.right_inv hyt,
      hθφ y (subset_tsupport _ hy)]
  have h₁ := coefficient_principal_apply_eq_classicalPrincipalSymbol hPXQ he φ φ hc hx ξ
  have h₂ := coefficient_principal_apply_eq_classicalPrincipalSymbol
    (classicalPseudodifferentialOperators_le 1 (by simp) hS) he φ φ hc' hx ξ
  rw [h₁, classicalPrincipalSymbol_eq_zero_of_mem_sub_one hS, hφx] at h₂
  simpa using h₂

/-- **The principal symbol of a composition** is the product of the principal symbols:
`σ_{m'+m}(P ∘ Q)(x, ξ) = σ_{m'}(P)(x, ξ) σ_m(Q)(x, ξ)` for classical pseudodifferential operators
`P` of order `m'` and `Q` of order `m`. -/
theorem classicalPrincipalSymbol_comp (hP : P ∈ classicalPseudodifferentialOperators m')
    (hQ : Q ∈ classicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol (m' + m) (P ∘ₗ Q) x ξ =
      classicalPrincipalSymbol m' P x ξ * classicalPrincipalSymbol m Q x ξ := by
  set e := chartAt (CoordinateSpace n) x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source _ x
  -- Cutoffs in the chart: `φ = 1` near `e x`, `θ = 1` near the support of `φ`, `χ = 1` near the
  -- support of `θ` and `χ₂ = 1` on the support of `χ`.
  obtain ⟨φ, hφ⟩ := exists_cutoff_eventually_eq_one isCompact_singleton
    (singleton_subset_iff.2 (mem_chart_target (CoordinateSpace n) x))
  obtain ⟨θ, hθ⟩ := exists_cutoff_eventually_eq_one φ.hasCompactSupport.isCompact
    φ.tsupport_subset
  obtain ⟨χ, χ₂, hχ, hχ₂⟩ := exists_nested_cutoffs θ.hasCompactSupport.isCompact θ.tsupport_subset
  have hθφ : ∀ y ∈ tsupport φ, θ y = 1 := fun y hy ↦ hθ.self_of_nhdsSet y hy
  have hχφ : ∀ y ∈ tsupport φ, χ y = 1 := fun y hy ↦
    hχ.self_of_nhdsSet y (subset_tsupport _ (by simp [hθφ y hy]))
  -- Split `P ∘ Q = P X Q + P (1 - X) Q`, with `X` the cutoff `χ` read on `M`.
  set X := e.complexCutoffPullback he χ 1
  have hPXQ := comp_mem_classicalPseudodifferentialOperators hP
    (mulLeft_comp_mem_classicalPseudodifferentialOperators hQ X)
  have hsplit : P ∘ₗ Q = P ∘ₗ LinearMap.mulLeft ℂ X ∘ₗ Q +
      P ∘ₗ LinearMap.mulLeft ℂ (1 - X) ∘ₗ Q := by
    have hid : LinearMap.mulLeft ℂ X + LinearMap.mulLeft ℂ (1 - X) = LinearMap.id := by
      ext f q
      simp [sub_mul]
    rw [← LinearMap.comp_add, ← LinearMap.add_comp, hid, LinearMap.id_comp]
  -- `P X Q` is seen in the chart, as `Op(a # b)` for the chart symbols `a` of `P` and `b` of `Q`.
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 e he φ χ₂
  obtain ⟨b, hb⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hQ).2 e he χ φ
  rw [hsplit, classicalPrincipalSymbol_add hPXQ (comp_mem_classicalPseudodifferentialOperators hP
      (mulLeft_comp_mem_classicalPseudodifferentialOperators hQ (1 - X))),
    classicalPrincipalSymbol_eq_mul_of_eq_sharp hPXQ hP hQ he hχφ hχ₂ _ ha hb
      (quantizeSchwartzValue_sharp_eq_complexChartCompression_comp_mulLeft_comp he hχ₂ ha hb) hx
      (hφ.self_of_nhdsSet _ rfl) ξ,
    classicalPrincipalSymbol_comp_mulLeft_one_sub_comp_eq_zero hP hQ he hθφ hχ hx
      (hφ.self_of_nhdsSet _ rfl) ξ, add_zero]

/-- **Commutators lose one order.** If `P` and `Q` are classical pseudodifferential operators of
orders `m'` and `m`, then `⁅P, Q⁆ = P ∘ Q - Q ∘ P` is a classical pseudodifferential operator of
order `m' + m - 1`, since the scalar principal symbols of `P ∘ Q` and `Q ∘ P` agree. -/
theorem lie_mem_classicalPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m')
    (hQ : Q ∈ classicalPseudodifferentialOperators m) :
    ⁅P, Q⁆ ∈ classicalPseudodifferentialOperators (m' + m - 1) := by
  have h₁ := comp_mem_classicalPseudodifferentialOperators hP hQ
  have h₂ : Q ∘ₗ P ∈ classicalPseudodifferentialOperators (m' + m) := by
    rw [add_comm]
    exact comp_mem_classicalPseudodifferentialOperators hQ hP
  rw [Ring.lie_def, Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  refine (classicalPrincipalSymbol_eq_zero_iff (sub_mem h₁ h₂)).1 fun x ξ ↦ ?_
  have h₃ : classicalPrincipalSymbol (m' + m) (Q ∘ₗ P) x ξ =
      classicalPrincipalSymbol m Q x ξ * classicalPrincipalSymbol m' P x ξ := by
    rw [add_comm]
    exact classicalPrincipalSymbol_comp hQ hP x ξ
  rw [classicalPrincipalSymbol_sub h₁ h₂, classicalPrincipalSymbol_comp hP hQ, h₃, mul_comm,
    sub_self]

/-- **Commutators with multiplication operators lose one order.** If `P` is a classical
pseudodifferential operator of order `m` and `g` a complex-valued smooth function on `M`, then
`⁅g, P⁆ = g P - P g` is a classical pseudodifferential operator of order `m - 1`. -/
theorem lie_mulLeft_mem_classicalPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ⁅LinearMap.mulLeft ℂ g, P⁆ ∈ classicalPseudodifferentialOperators (m - 1) := by
  simpa using lie_mem_classicalPseudodifferentialOperators
    (mulLeft_mem_classicalPseudodifferentialOperators g) hP

/-- **Multiplication on the right.** For a complex-valued smooth function `g`, the principal symbol
of `u ↦ P (g u)` is `σ_m(P g)(x, ξ) = σ_m(P)(x, ξ) g(x)`: the commutator `⁅g, P⁆` has order
`m - 1`, so `P g` has the principal symbol of `g P`. -/
theorem classicalPrincipalSymbol_comp_mulLeft (hP : P ∈ classicalPseudodifferentialOperators m)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (P ∘ₗ LinearMap.mulLeft ℂ g) x ξ =
      classicalPrincipalSymbol m P x ξ * g x := by
  have h := classicalPrincipalSymbol_eq_zero_of_mem_sub_one
    (lie_mulLeft_mem_classicalPseudodifferentialOperators hP g) x ξ
  rw [Ring.lie_def, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    classicalPrincipalSymbol_sub (mulLeft_comp_mem_classicalPseudodifferentialOperators hP g)
      (comp_mulLeft_mem_classicalPseudodifferentialOperators hP g),
    classicalPrincipalSymbol_mulLeft_comp hP, sub_eq_zero] at h
  rw [← h, mul_comm]

end Principal

/-! ### Differential operators -/

section DifferentialOperator

variable {k : ℕ} {m : ℝ}
  {D : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯}
  (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ k)
  (hP : P ∈ classicalPseudodifferentialOperators m)

include hD hP

/-- **Composition on the left with a differential operator.** If `D` is a differential operator of
order at most `k` on the real-valued smooth functions on `M`, in Grothendieck's sense, and `P` a
classical pseudodifferential operator of order `m`, then `D ∘ P`, with `D` complexified, is a
classical pseudodifferential operator of order `k + m`. -/
theorem complexifyLinearMap_comp_mem_classicalPseudodifferentialOperators :
    ContMDiffMap.complexifyLinearMap D ∘ₗ P ∈ classicalPseudodifferentialOperators (k + m) :=
  comp_mem_classicalPseudodifferentialOperators_of_local_left
    (complexifyLinearMap_mem_classicalPseudodifferentialOperators hD)
    (fun _ _ ↦ complexifyLinearMap_apply_eq_zero_of_mem_differentialOperators hD) hP

/-- **Composition on the right with a differential operator.** If `D` is a differential operator
of order at most `k` on the real-valued smooth functions on `M`, in Grothendieck's sense, and `P` a
classical pseudodifferential operator of order `m`, then `P ∘ D`, with `D` complexified, is a
classical pseudodifferential operator of order `m + k`. -/
theorem comp_complexifyLinearMap_mem_classicalPseudodifferentialOperators :
    P ∘ₗ ContMDiffMap.complexifyLinearMap D ∈ classicalPseudodifferentialOperators (m + k) :=
  comp_mem_classicalPseudodifferentialOperators_of_local_right
    (complexifyLinearMap_mem_classicalPseudodifferentialOperators hD)
    (fun _ _ ↦ complexifyLinearMap_apply_eq_zero_of_mem_differentialOperators hD) hP

/-- **The principal symbol of `D ∘ P`** for a differential operator `D` of order at most `k` is
`i ^ k σ(D)(ξ) σ_m(P)(x, ξ)` at every nonzero covector `ξ ∈ T*ₓM`, where `σ(D)` is the geometric
principal symbol of `D`. -/
theorem classicalPrincipalSymbol_complexifyLinearMap_comp (x : M)
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    classicalPrincipalSymbol (k + m) (ContMDiffMap.complexifyLinearMap D ∘ₗ P) x ξ =
      Complex.I ^ k * smoothPrincipalSymbol 𝓘(ℝ, CoordinateSpace n)
        BoundarylessManifold.isInteriorPoint ⟨D, hD⟩ ξ * classicalPrincipalSymbol m P x ξ := by
  rw [classicalPrincipalSymbol_comp
    (complexifyLinearMap_mem_classicalPseudodifferentialOperators hD) hP,
    classicalPrincipalSymbol_complexifyLinearMap hD x hξ]

/-- **The principal symbol of `P ∘ D`** for a differential operator `D` of order at most `k` is
`σ_m(P)(x, ξ) i ^ k σ(D)(ξ)` at every nonzero covector `ξ ∈ T*ₓM`, where `σ(D)` is the geometric
principal symbol of `D`. -/
theorem classicalPrincipalSymbol_comp_complexifyLinearMap (x : M)
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    classicalPrincipalSymbol (m + k) (P ∘ₗ ContMDiffMap.complexifyLinearMap D) x ξ =
      classicalPrincipalSymbol m P x ξ * (Complex.I ^ k * smoothPrincipalSymbol
        𝓘(ℝ, CoordinateSpace n) BoundarylessManifold.isInteriorPoint ⟨D, hD⟩ ξ) := by
  rw [classicalPrincipalSymbol_comp hP
    (complexifyLinearMap_mem_classicalPseudodifferentialOperators hD),
    classicalPrincipalSymbol_complexifyLinearMap hD x hξ]

end DifferentialOperator

end TauCeti
