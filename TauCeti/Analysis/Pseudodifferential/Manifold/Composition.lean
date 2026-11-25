/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.PrincipalSymbol
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Pseudodifferential.Composition.Classical
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic

/-!
# Composition with local operators on a manifold

Let `M` be a manifold modelled on `ℝⁿ`. An operator `L` on the complex-valued smooth functions on
`M` is **local** when `L f` vanishes at every point near which `f` vanishes; differential operators
are the main examples. This file shows that composing a classical pseudodifferential operator `P`
of order `m` (`TauCeti.classicalPseudodifferentialOperators`) on either side with a local classical
pseudodifferential operator `L` of order `k` gives a classical pseudodifferential operator, of
order `k + m` (`TauCeti.comp_mem_classicalPseudodifferentialOperators_of_local_left`) or `m + k`
(`TauCeti.comp_mem_classicalPseudodifferentialOperators_of_local_right`), and that the principal
symbol is multiplicative:

`σ_{k+m}(L ∘ P)(x, ξ) = σ_k(L)(x, ξ) σ_m(P)(x, ξ)`

(`TauCeti.classicalPrincipalSymbol_comp_of_local_left`, and
`TauCeti.classicalPrincipalSymbol_comp_of_local_right` for `P ∘ L`). As these principal symbols are
scalar, the commutator `⁅L, P⁆` has order `k + m - 1`
(`TauCeti.lie_mem_classicalPseudodifferentialOperators_of_local`); for instance the commutator of
`P` with multiplication by a smooth function has order `m - 1`
(`TauCeti.lie_mulLeft_mem_classicalPseudodifferentialOperators`). In particular a classical
pseudodifferential operator can be composed on either side with the complexification of a
differential operator `D` of order `k`, and then the principal symbol of the composition is
`i ^ k σ(D)(ξ) σ_m(P)(x, ξ)` at nonzero covectors, where `σ(D)` is the geometric principal symbol
of `D` (`TauCeti.classicalPrincipalSymbol_complexifyLinearMap_comp`).

## The argument

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

The composition of two general classical pseudodifferential operators on `M` also involves the
part of `P` between distant points, which no single chart sees; locality of one factor removes it.

## Main results

* `TauCeti.comp_mem_classicalPseudodifferentialOperators_of_local_left` and
  `TauCeti.comp_mem_classicalPseudodifferentialOperators_of_local_right`: the composition of a
  classical pseudodifferential operator with a local one, on either side, is a classical
  pseudodifferential operator, and the orders add.
* `TauCeti.classicalPrincipalSymbol_comp_of_local_left` and
  `TauCeti.classicalPrincipalSymbol_comp_of_local_right`: the principal symbol of such a
  composition is the product of the principal symbols.
* `TauCeti.lie_mem_classicalPseudodifferentialOperators_of_local` and
  `TauCeti.lie_mulLeft_mem_classicalPseudodifferentialOperators`: commutators with local operators,
  such as multiplication by smooth functions, lose one order.
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
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  {L P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-! ### Local operators -/

/-- A local operator takes the same value at `x` on two functions that agree near `x`. -/
private theorem apply_eq_of_eventuallyEq_of_local
    (hL : ∀ f x, (∀ᶠ y in 𝓝 x, f y = 0) → L f x = 0)
    {f g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {x : M} (hfg : (f : M → ℂ) =ᶠ[𝓝 x] g) :
    L f x = L g x := by
  rw [← sub_eq_zero, ← Pi.sub_apply, ← ContMDiffMap.coe_sub, ← map_sub]
  exact hL _ x (hfg.mono fun y hy ↦ by simp [hy])

/-- A local operator does not enlarge supports. -/
private theorem apply_eq_zero_of_notMem_tsupport_of_local
    (hL : ∀ f x, (∀ᶠ y in 𝓝 x, f y = 0) → L f x = 0)
    {f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {x : M} (hx : x ∉ tsupport f) :
    L f x = 0 :=
  hL f x (notMem_tsupport_iff_eventuallyEq.1 hx)

variable [T2Space M]

/-! ### Chart symbols of compositions -/

section Chart

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)

include he

/-- The symbol of a chart compression by `φ` and `ψ` vanishes at positions outside the support of
`φ`, since every output of the compression does. -/
private theorem hasCompactSpatialSupport_of_eq_complexChartCompression {m : ℝ}
    {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {b : ClassicalSymbol n ℂ ℂ m}
    (hb : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue b.toSymbol.coefficient u y =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y) :
    b.toSymbol.HasCompactSpatialSupport := by
  refine Symbol.hasCompactSpatialSupport_iff_exists_tsupport_quantizeSchwartzValue_subset.2
    ⟨tsupport φ, φ.hasCompactSupport.isCompact, fun u _ ↦ ?_⟩
  rw [show quantizeSchwartzValue b.toSymbol.coefficient u = fun y ↦ φ y •
      P (e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff u (u.smooth ⊤))) (e.symm y) from
    funext fun y ↦ by rw [hb, OpenPartialHomeomorph.complexChartCompression_apply]]
  exact tsupport_smul_subset_left _ _

/-- The output `v` of a chart compression by `χ` and `ψ`, read as a Schwartz function and pulled
back to `M` by a cutoff `χ₂` equal to `1` on the support of `χ`, is `(χ ∘ e) · P ((ψ u) ∘ e)` on the
chart source. -/
private theorem complexCutoffPullback_apply_of_eq_complexChartCompression
    {χ χ₂ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hχ₂ : ∀ y ∈ tsupport χ, χ₂ y = 1)
    {u v : 𝓢(CoordinateSpace n, ℂ)}
    (hv : ∀ y, v y =
      e.complexChartCompression he χ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    {q : M} (hq : q ∈ e.source) :
    e.complexCutoffPullback he χ₂ (ContMDiffMap.ofContDiff v (v.smooth ⊤)) q =
      χ (e q) • P (e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff u (u.smooth ⊤))) q := by
  rw [OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he _ _ hq,
    ContMDiffMap.coe_ofContDiff, hv, OpenPartialHomeomorph.complexChartCompression_apply,
    e.left_inv hq]
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
  have hb' := hasCompactSpatialSupport_of_eq_complexChartCompression he hb
  set v := (hb'.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
    (b.toSymbol.contDiff_quantizeSchwartzValue u)
  have hv (y : CoordinateSpace n) : v y =
      e.complexChartCompression he χ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y := by
    rw [← hb, HasCompactSupport.toSchwartzMap_toFun]
  rw [ClassicalSymbol.toSymbol_sharp, Symbol.quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue,
    ha, OpenPartialHomeomorph.complexChartCompression_apply,
    OpenPartialHomeomorph.complexChartCompression_apply, LinearMap.comp_apply]
  by_cases hφ : φ x = 0
  · simp [hφ]
  -- Near `q = e⁻¹ x`, the pullback of `v` is `P ((ψ u) ∘ e)`, since `χ = 1` near `x`.
  have hx : x ∈ e.target := φ.tsupport_subset (subset_tsupport _ hφ)
  have hq : e.symm x ∈ e.source := e.map_target hx
  congr 1
  refine apply_eq_of_eventuallyEq_of_local hL ?_
  have hχx : ∀ᶠ q in 𝓝 (e.symm x), χ (e q) = 1 :=
    (e.continuousAt hq).eventually (show ∀ᶠ y in 𝓝 (e (e.symm x)), χ y = 1 by
      rw [e.right_inv hx]
      exact hχ.filter_mono (nhds_le_nhdsSet (subset_tsupport _ hφ)))
  filter_upwards [hχx, e.open_source.mem_nhds hq] with q hχq hq'
  rw [complexCutoffPullback_apply_of_eq_complexChartCompression he hχ₂ hv hq', hχq, one_smul]

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
  have hd' := hasCompactSpatialSupport_of_eq_complexChartCompression he hd
  set v := (hd'.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
    (d.toSymbol.contDiff_quantizeSchwartzValue u)
  have hv (y : CoordinateSpace n) : v y =
      e.complexChartCompression he χ ψ L (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y := by
    rw [← hd, HasCompactSupport.toSchwartzMap_toFun]
  set g := e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff u (u.smooth ⊤))
  -- `L g` is the pullback of `v`: both vanish off the support of `g`, which lies in the chart
  -- source where `χ ∘ e = 1`.
  have hLg : e.complexCutoffPullback he χ₂ (ContMDiffMap.ofContDiff v (v.smooth ⊤)) = L g := by
    ext q
    by_cases hqg : q ∈ tsupport g
    · obtain ⟨y, hy, rfl⟩ := e.tsupport_complexCutoffPullback_subset he ψ _ hqg
      have hq : e.symm y ∈ e.source := e.map_target (ψ.tsupport_subset hy)
      rw [complexCutoffPullback_apply_of_eq_complexChartCompression he hχ₂ hv hq,
        e.right_inv (ψ.tsupport_subset hy), hχ y hy, one_smul]
    · rw [apply_eq_zero_of_notMem_tsupport_of_local hL hqg]
      by_cases hq : q ∈ e.source
      · rw [complexCutoffPullback_apply_of_eq_complexChartCompression he hχ₂ hv hq,
          apply_eq_zero_of_notMem_tsupport_of_local hL hqg, smul_zero]
      · exact OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he _ _ hq
  rw [ClassicalSymbol.toSymbol_sharp, Symbol.quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue,
    ha, OpenPartialHomeomorph.complexChartCompression_apply,
    OpenPartialHomeomorph.complexChartCompression_apply, LinearMap.comp_apply, hLg]

end Chart

omit [ChartedSpace (CoordinateSpace n) M] [T2Space M] in
/-- A cutoff in the target of the chart `e`, equal to `1` near a compact subset of the target. -/
private theorem exists_cutoff_eventually_eq_one {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hKe : K ⊆ e.target) :
    ∃ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ), ∀ᶠ y in 𝓝ˢ K, χ y = 1 :=
  (TestFunction.exists_eventually_eq_one (Ω := ⟨e.target, e.open_target⟩) (n := ⊤) hK
    hKe).imp fun _ h ↦ h.1

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
  obtain ⟨χ, hχ⟩ := exists_cutoff_eventually_eq_one φ.hasCompactSupport.isCompact φ.tsupport_subset
  obtain ⟨χ₂, hχ₂⟩ := exists_cutoff_eventually_eq_one χ.hasCompactSupport.isCompact
    χ.tsupport_subset
  obtain ⟨a, ha⟩ := hL₂ e he φ χ₂
  obtain ⟨b, hb⟩ := hP₂ e he χ ψ
  exact ⟨_, quantizeSchwartzValue_sharp_eq_complexChartCompression_comp_of_local_left he hLloc hχ
    hχ₂.self_of_nhdsSet ha hb⟩

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
  obtain ⟨χ, hχ⟩ := exists_cutoff_eventually_eq_one ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  obtain ⟨χ₂, hχ₂⟩ := exists_cutoff_eventually_eq_one χ.hasCompactSupport.isCompact
    χ.tsupport_subset
  obtain ⟨a, ha⟩ := hP₂ e he φ χ₂
  obtain ⟨d, hd⟩ := hL₂ e he χ ψ
  exact ⟨_, quantizeSchwartzValue_sharp_eq_complexChartCompression_comp_of_local_right he hLloc
    hχ.self_of_nhdsSet hχ₂.self_of_nhdsSet ha hd⟩

/-! ### Principal symbols -/

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- A complex-linear map `ℂ → ℂ` is multiplication by its value at `1`. -/
private theorem apply_eq_mul_apply_one (f : ℂ →L[ℂ] ℂ) (w : ℂ) : f w = w * f 1 := by
  simpa using f.map_smul w 1

/-- **The principal symbol of a composition with a local operator on the left** is the product of
the principal symbols: `σ_{k+m}(L ∘ P)(x, ξ) = σ_k(L)(x, ξ) σ_m(P)(x, ξ)`. -/
theorem classicalPrincipalSymbol_comp_of_local_left {k m : ℝ}
    (hL : L ∈ classicalPseudodifferentialOperators k)
    (hLloc : ∀ f x, (∀ᶠ y in 𝓝 x, f y = 0) → L f x = 0)
    (hP : P ∈ classicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol (k + m) (L ∘ₗ P) x ξ =
      classicalPrincipalSymbol k L x ξ * classicalPrincipalSymbol m P x ξ := by
  obtain ⟨-, hL₂⟩ := mem_classicalPseudodifferentialOperators_iff.1 hL
  obtain ⟨-, hP₂⟩ := mem_classicalPseudodifferentialOperators_iff.1 hP
  set e := chartAt (CoordinateSpace n) x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source _ x
  -- Cutoffs `φ`, `χ`, `χ₂`, each equal to `1` near the support of the previous one and `φ`
  -- equal to `1` at `e x`, as in the chart symbol of `L ∘ P`.
  obtain ⟨φ, hφ⟩ := exists_cutoff_eventually_eq_one isCompact_singleton
    (singleton_subset_iff.2 (e.map_source hx))
  obtain ⟨χ, hχ⟩ := exists_cutoff_eventually_eq_one φ.hasCompactSupport.isCompact φ.tsupport_subset
  obtain ⟨χ₂, hχ₂⟩ := exists_cutoff_eventually_eq_one χ.hasCompactSupport.isCompact
    χ.tsupport_subset
  have hφx : φ (e x) = 1 := hφ.self_of_nhdsSet _ rfl
  have hχx : χ (e x) = 1 := hχ.self_of_nhdsSet _ (subset_tsupport _ (by simp [hφx]))
  have hχ₂x : χ₂ (e x) = 1 := hχ₂.self_of_nhdsSet _ (subset_tsupport _ (by simp [hχx]))
  obtain ⟨a, ha⟩ := hL₂ e he φ χ₂
  obtain ⟨b, hb⟩ := hP₂ e he χ φ
  have h := coefficient_principal_apply_eq_classicalPrincipalSymbol
    (comp_mem_classicalPseudodifferentialOperators_of_local_left hL hLloc hP) he φ φ
    (quantizeSchwartzValue_sharp_eq_complexChartCompression_comp_of_local_left he hLloc hχ
      hχ₂.self_of_nhdsSet ha hb) hx ξ
  rw [ClassicalSymbol.principal_sharp, HomogeneousSymbol.coefficient_comp,
    ContinuousLinearMap.comp_apply, coefficient_principal_apply_eq_classicalPrincipalSymbol hP he
      χ φ hb hx ξ, apply_eq_mul_apply_one,
    coefficient_principal_apply_eq_classicalPrincipalSymbol hL he φ χ₂ ha hx ξ] at h
  simp only [hφx, hχx, hχ₂x, mul_one, Complex.ofReal_one, one_mul] at h
  rw [← h, mul_comm]

/-- **The principal symbol of a composition with a local operator on the right** is the product of
the principal symbols: `σ_{m+k}(P ∘ L)(x, ξ) = σ_m(P)(x, ξ) σ_k(L)(x, ξ)`. -/
theorem classicalPrincipalSymbol_comp_of_local_right {k m : ℝ}
    (hL : L ∈ classicalPseudodifferentialOperators k)
    (hLloc : ∀ f x, (∀ᶠ y in 𝓝 x, f y = 0) → L f x = 0)
    (hP : P ∈ classicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol (m + k) (P ∘ₗ L) x ξ =
      classicalPrincipalSymbol m P x ξ * classicalPrincipalSymbol k L x ξ := by
  obtain ⟨-, hL₂⟩ := mem_classicalPseudodifferentialOperators_iff.1 hL
  obtain ⟨-, hP₂⟩ := mem_classicalPseudodifferentialOperators_iff.1 hP
  set e := chartAt (CoordinateSpace n) x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source _ x
  -- Cutoffs `ψ`, `χ`, `χ₂`, each equal to `1` near the support of the previous one and `ψ`
  -- equal to `1` at `e x`, as in the chart symbol of `P ∘ L`.
  obtain ⟨ψ, hψ⟩ := exists_cutoff_eventually_eq_one isCompact_singleton
    (singleton_subset_iff.2 (e.map_source hx))
  obtain ⟨χ, hχ⟩ := exists_cutoff_eventually_eq_one ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  obtain ⟨χ₂, hχ₂⟩ := exists_cutoff_eventually_eq_one χ.hasCompactSupport.isCompact
    χ.tsupport_subset
  have hψx : ψ (e x) = 1 := hψ.self_of_nhdsSet _ rfl
  have hχx : χ (e x) = 1 := hχ.self_of_nhdsSet _ (subset_tsupport _ (by simp [hψx]))
  have hχ₂x : χ₂ (e x) = 1 := hχ₂.self_of_nhdsSet _ (subset_tsupport _ (by simp [hχx]))
  obtain ⟨a, ha⟩ := hP₂ e he ψ χ₂
  obtain ⟨d, hd⟩ := hL₂ e he χ ψ
  have h := coefficient_principal_apply_eq_classicalPrincipalSymbol
    (comp_mem_classicalPseudodifferentialOperators_of_local_right hL hLloc hP) he ψ ψ
    (quantizeSchwartzValue_sharp_eq_complexChartCompression_comp_of_local_right he hLloc
      hχ.self_of_nhdsSet hχ₂.self_of_nhdsSet ha hd) hx ξ
  rw [ClassicalSymbol.principal_sharp, HomogeneousSymbol.coefficient_comp,
    ContinuousLinearMap.comp_apply, coefficient_principal_apply_eq_classicalPrincipalSymbol hL he
      χ ψ hd hx ξ, apply_eq_mul_apply_one,
    coefficient_principal_apply_eq_classicalPrincipalSymbol hP he ψ χ₂ ha hx ξ] at h
  simp only [hψx, hχx, hχ₂x, mul_one, Complex.ofReal_one, one_mul] at h
  rw [← h, mul_comm]

/-- **Commutators with a local operator lose one order.** If `L` is a local classical
pseudodifferential operator of order `k` and `P` a classical pseudodifferential operator of order
`m`, then the commutator `⁅L, P⁆ = L ∘ P - P ∘ L` is a classical pseudodifferential operator of
order `k + m - 1`, since the scalar principal symbols of `L ∘ P` and `P ∘ L` agree. -/
theorem lie_mem_classicalPseudodifferentialOperators_of_local {k m : ℝ}
    (hL : L ∈ classicalPseudodifferentialOperators k)
    (hLloc : ∀ f x, (∀ᶠ y in 𝓝 x, f y = 0) → L f x = 0)
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    ⁅L, P⁆ ∈ classicalPseudodifferentialOperators (k + m - 1) := by
  have h₁ := comp_mem_classicalPseudodifferentialOperators_of_local_left hL hLloc hP
  have h₂ : P ∘ₗ L ∈ classicalPseudodifferentialOperators (k + m) := by
    rw [add_comm]
    exact comp_mem_classicalPseudodifferentialOperators_of_local_right hL hLloc hP
  rw [Ring.lie_def, Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  refine (classicalPrincipalSymbol_eq_zero_iff (sub_mem h₁ h₂)).1 fun x ξ ↦ ?_
  have h₃ : classicalPrincipalSymbol (k + m) (P ∘ₗ L) x ξ =
      classicalPrincipalSymbol m P x ξ * classicalPrincipalSymbol k L x ξ := by
    rw [add_comm]
    exact classicalPrincipalSymbol_comp_of_local_right hL hLloc hP x ξ
  rw [classicalPrincipalSymbol_sub h₁ h₂, classicalPrincipalSymbol_comp_of_local_left hL hLloc hP,
    h₃, mul_comm, sub_self]

/-- **Commutators with multiplication operators lose one order.** If `P` is a classical
pseudodifferential operator of order `m` and `g` a complex-valued smooth function on `M`, then
`⁅g, P⁆ = g P - P g` is a classical pseudodifferential operator of order `m - 1`. -/
theorem lie_mulLeft_mem_classicalPseudodifferentialOperators {m : ℝ}
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ⁅LinearMap.mulLeft ℂ g, P⁆ ∈ classicalPseudodifferentialOperators (m - 1) := by
  simpa using lie_mem_classicalPseudodifferentialOperators_of_local
    (mulLeft_mem_classicalPseudodifferentialOperators g)
    (fun f x hf ↦ by simp [hf.self_of_nhds]) hP

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
  rw [classicalPrincipalSymbol_comp_of_local_left
    (complexifyLinearMap_mem_classicalPseudodifferentialOperators hD)
    (fun _ _ ↦ complexifyLinearMap_apply_eq_zero_of_mem_differentialOperators hD) hP,
    classicalPrincipalSymbol_complexifyLinearMap hD x hξ]

/-- **The principal symbol of `P ∘ D`** for a differential operator `D` of order at most `k` is
`σ_m(P)(x, ξ) i ^ k σ(D)(ξ)` at every nonzero covector `ξ ∈ T*ₓM`, where `σ(D)` is the geometric
principal symbol of `D`. -/
theorem classicalPrincipalSymbol_comp_complexifyLinearMap (x : M)
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    classicalPrincipalSymbol (m + k) (P ∘ₗ ContMDiffMap.complexifyLinearMap D) x ξ =
      classicalPrincipalSymbol m P x ξ * (Complex.I ^ k * smoothPrincipalSymbol
        𝓘(ℝ, CoordinateSpace n) BoundarylessManifold.isInteriorPoint ⟨D, hD⟩ ξ) := by
  rw [classicalPrincipalSymbol_comp_of_local_right
    (complexifyLinearMap_mem_classicalPseudodifferentialOperators hD)
    (fun _ _ ↦ complexifyLinearMap_apply_eq_zero_of_mem_differentialOperators hD) hP,
    classicalPrincipalSymbol_complexifyLinearMap hD x hξ]

end DifferentialOperator

end TauCeti
