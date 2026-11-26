/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartQuantization
public import TauCeti.Analysis.Pseudodifferential.Manifold.PrincipalSymbol
import TauCeti.Algebra.GroupWithZero.Indicator
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Pseudodifferential.CoordinateChange.Chart
import TauCeti.Analysis.Pseudodifferential.Manifold.Composition
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
import TauCeti.Topology.Compactness.Compact

/-!
# Smoothing operators and pseudolocality on a manifold

Let `M` be a manifold modelled on `ℝⁿ`. The **operators of order `-∞`** on `M` are the
operators that are classical pseudodifferential operators of every real order
(`TauCeti.smoothingPseudodifferentialOperators`). Equivalently, they are the properly supported
operators all of whose chart compressions are quantizations of smoothing symbols
(`TauCeti.mem_smoothingPseudodifferentialOperators_iff_isSmoothing`). Their principal symbols
vanish in every order.

The patching of pseudodifferential operators from local data rests on two facts, as in
Hörmander (III, §18.1) and Melrose (*Introduction to Microlocal Analysis*, §5.3):

* **Pseudolocality.** If `P` is a classical pseudodifferential operator and `f`, `g` are smooth
  functions with disjoint supports, then `f P g` has order `-∞`
  (`TauCeti.mulLeft_comp_comp_mulLeft_mem_smoothingPseudodifferentialOperators`). In a chart, its
  compression only involves the kernel of the chart symbol away from the diagonal, which is
  smooth (`TauCeti.Symbol.exists_isSmoothing_smul_quantizeSchwartzValue_comp_eq`).
* **Localization.** If `φ` and `ψ` are cutoffs in a chart `e` and `a` is the symbol of the chart
  compression of `P` by `φ` and `ψ`, then `φ P ψ`, with the cutoffs read on `M`, is exactly the
  chart quantization of `a`
  (`OpenPartialHomeomorph.chartQuantization_eq_mulLeft_comp_comp_mulLeft`, next to the chart
  quantization itself).

Together they show that a classical pseudodifferential operator is, modulo an operator of order
`-∞`, the sum of the chart quantizations of its chart symbols: for cutoffs `ρᵢ` in charts `eᵢ`
and cutoffs `χᵢ` equal to `1` near the supports of the `ρᵢ`, the operator `(∑ᵢ ρᵢ) P` differs from
`∑ᵢ Op_{eᵢ}(aᵢ)` by an operator of order `-∞`, where `aᵢ` is the symbol of the compression of `P`
by `ρᵢ` and `χᵢ`
(`TauCeti.mulLeft_sum_comp_sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators`).
When the `ρᵢ` add up to `1`, this is `P` itself
(`TauCeti.sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators`), and on a compact
manifold such cutoffs exist. This is the converse of
`OpenPartialHomeomorph.chartQuantization_mem_classicalPseudodifferentialOperators`.

## Main definitions

* `TauCeti.smoothingPseudodifferentialOperators`: the operators of order `-∞` on `M`.

## Main results

* `TauCeti.mem_smoothingPseudodifferentialOperators_iff_isSmoothing`: an operator has order `-∞`
  exactly when it is properly supported and its chart compressions are quantizations of smoothing
  symbols.
* `TauCeti.classicalPrincipalSymbol_eq_zero_of_mem_smoothingPseudodifferentialOperators`: the
  principal symbol of an operator of order `-∞` vanishes in every order.
* `TauCeti.comp_mem_smoothingPseudodifferentialOperators_of_left`,
  `TauCeti.comp_mem_smoothingPseudodifferentialOperators_of_right`: the operators of order `-∞`
  form a two-sided ideal in the classical pseudodifferential operators of all orders.
* `TauCeti.mulLeft_comp_comp_mulLeft_mem_smoothingPseudodifferentialOperators`: pseudolocality.
* `TauCeti.sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators`: a classical
  pseudodifferential operator is a sum of chart quantizations modulo an operator of order `-∞`,
  given cutoffs in charts adding up to `1`.
* `TauCeti.exists_sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators`: on a compact
  manifold, every classical pseudodifferential operator of order `m` is a finite sum of chart
  quantizations of classical symbols of order `m`, modulo an operator of order `-∞`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.17
  and Definition 18.1.20.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3, Proposition 5.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

open Set Filter
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-! ### Operators of order `-∞` -/

/-- The **operators of order `-∞`** on a manifold `M` modelled on `ℝⁿ`: the classical
pseudodifferential operators of every real order. Their chart compressions are the quantizations
of smoothing symbols (`TauCeti.mem_smoothingPseudodifferentialOperators_iff_isSmoothing`). -/
noncomputable def smoothingPseudodifferentialOperators :
    Submodule ℂ (C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :=
  ⨅ m : ℝ, classicalPseudodifferentialOperators m

theorem mem_smoothingPseudodifferentialOperators_iff :
    P ∈ smoothingPseudodifferentialOperators ↔
      ∀ m : ℝ, P ∈ classicalPseudodifferentialOperators m :=
  Submodule.mem_iInf _

/-- An operator of order `-∞` is a classical pseudodifferential operator of every order `m`. -/
theorem smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators (m : ℝ) :
    smoothingPseudodifferentialOperators (n := n) (M := M) ≤
      classicalPseudodifferentialOperators m :=
  iInf_le _ m

/-- **Operators of order `-∞` in charts.** For any real `m`, an operator has order `-∞` exactly
when it is properly supported and, for every chart `e` of the maximal atlas and all cutoffs `φ`,
`ψ`, its chart compression is the quantization of a smoothing symbol of order `m`. -/
theorem mem_smoothingPseudodifferentialOperators_iff_isSmoothing (m : ℝ) :
    P ∈ smoothingPseudodifferentialOperators ↔ IsProperlySupported P ∧
      ∀ (e : OpenPartialHomeomorph M (CoordinateSpace n))
        (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
        (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)), ∃ r : Symbol n ℂ ℂ m, r.IsSmoothing ∧
          ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
            quantizeSchwartzValue r.coefficient u x =
              e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x := by
  refine ⟨fun hP ↦ ⟨(mem_classicalPseudodifferentialOperators_iff.1
      (mem_smoothingPseudodifferentialOperators_iff.1 hP m)).1, fun e he φ ψ ↦ ?_⟩,
    fun ⟨hP, h⟩ ↦ mem_smoothingPseudodifferentialOperators_iff.2 fun m' ↦ ?_⟩
  · -- The chart symbols of order `m` and of order `m'` have the same quantization, hence the
    -- same coefficient.
    obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1
      (mem_smoothingPseudodifferentialOperators_iff.1 hP m)).2 e he φ ψ
    refine ⟨a.toSymbol, Symbol.isSmoothing_iff.2 fun m' ↦ ?_, ha⟩
    obtain ⟨b, hb⟩ := (mem_classicalPseudodifferentialOperators_iff.1
      (mem_smoothingPseudodifferentialOperators_iff.1 hP m')).2 e he φ ψ
    exact ⟨b.toSymbol, Symbol.coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u _ ↦
      funext fun x ↦ (hb u x).trans (ha u x).symm⟩
  · refine mem_classicalPseudodifferentialOperators_iff.2 ⟨hP, fun e he φ ψ ↦ ?_⟩
    obtain ⟨r, hr, hop⟩ := h e he φ ψ
    obtain ⟨b, hb⟩ := Symbol.isSmoothing_iff.1 hr m'
    refine ⟨ClassicalSymbol.ofIsSmoothing b (Symbol.isSmoothing_iff.2 fun m'' ↦
      (Symbol.isSmoothing_iff.1 hr m'').imp fun _ h ↦ h.trans hb.symm),
      fun u x ↦ ?_⟩
    rw [ClassicalSymbol.toSymbol_ofIsSmoothing, hb, hop]

/-- An operator of order `-∞` has principal symbol `0` in every order. -/
theorem classicalPrincipalSymbol_eq_zero_of_mem_smoothingPseudodifferentialOperators
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (hP : P ∈ smoothingPseudodifferentialOperators)
    (m : ℝ) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m P x ξ = 0 :=
  classicalPrincipalSymbol_eq_zero_of_mem_sub_one
    (smoothingPseudodifferentialOperators_le_classicalPseudodifferentialOperators (m - 1) hP) x ξ

/-- Multiplying an operator of order `-∞` on the left by a smooth function keeps it of order
`-∞`. -/
theorem mulLeft_comp_mem_smoothingPseudodifferentialOperators
    (hP : P ∈ smoothingPseudodifferentialOperators)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    LinearMap.mulLeft ℂ g ∘ₗ P ∈ smoothingPseudodifferentialOperators :=
  mem_smoothingPseudodifferentialOperators_iff.2 fun m ↦
    mulLeft_comp_mem_classicalPseudodifferentialOperators
      (mem_smoothingPseudodifferentialOperators_iff.1 hP m) g

/-- Multiplying an operator of order `-∞` on the right by a smooth function keeps it of order
`-∞`. -/
theorem comp_mulLeft_mem_smoothingPseudodifferentialOperators
    (hP : P ∈ smoothingPseudodifferentialOperators)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    P ∘ₗ LinearMap.mulLeft ℂ g ∈ smoothingPseudodifferentialOperators :=
  mem_smoothingPseudodifferentialOperators_iff.2 fun m ↦
    comp_mulLeft_mem_classicalPseudodifferentialOperators
      (mem_smoothingPseudodifferentialOperators_iff.1 hP m) g

/-- **Operators of order `-∞` absorb composition on the right.** If `P` has order `-∞` and `Q` is
a classical pseudodifferential operator of some order `m`, then `P ∘ Q` has order `-∞`. -/
theorem comp_mem_smoothingPseudodifferentialOperators_of_left
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
    {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
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
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}
    {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hQ : Q ∈ classicalPseudodifferentialOperators m)
    (hP : P ∈ smoothingPseudodifferentialOperators) :
    Q ∘ₗ P ∈ smoothingPseudodifferentialOperators :=
  mem_smoothingPseudodifferentialOperators_iff.2 fun m' ↦ add_sub_cancel m m' ▸
    comp_mem_classicalPseudodifferentialOperators hQ
      (mem_smoothingPseudodifferentialOperators_iff.1 hP (m' - m))

/-! ### Pseudolocality -/

/-- In a chart `e`, the compression of `f P g` by `φ` and `ψ` vanishes off the set of points of
`tsupport φ` read on `M` inside `tsupport f`, and only sees its input on the set of points of
`tsupport ψ` read on `M` inside `tsupport g`. So the input may be multiplied by a cutoff `ψ₁` equal
to `1` on the second set, and the output by a cutoff `φ₁` equal to `1` on the first. -/
private theorem complexChartCompression_mulLeft_comp_comp_mulLeft_eq_smul
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {f g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    {φ₁ ψ₁ : CoordinateSpace n → ℝ} (hφ₁ : EqOn φ₁ 1 (tsupport φ ∩ e.symm ⁻¹' tsupport f))
    (hψ₁ : EqOn ψ₁ 1 (tsupport ψ ∩ e.symm ⁻¹' tsupport g)) {u w : 𝓢(CoordinateSpace n, ℂ)}
    (hw : ∀ y, w y = ψ₁ y • u y) (x : CoordinateSpace n) :
    φ₁ x • e.complexChartCompression he φ ψ
        (LinearMap.mulLeft ℂ f ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ g)
        (ContMDiffMap.ofContDiff w (w.smooth ⊤)) x =
      e.complexChartCompression he φ ψ (LinearMap.mulLeft ℂ f ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ g)
        (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x := by
  have hinput : g * e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff w (w.smooth ⊤)) =
      g * e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff u (u.smooth ⊤)) := by
    ext p
    by_cases hp : p ∈ e.source
    · rw [ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.coe_mul, Pi.mul_apply,
        e.mul_complexCutoffPullback_apply_of_eq_smul he ψ hψ₁
          (fun y ↦ by rw [ContMDiffMap.coe_ofContDiff, hw]) hp,
        e.complexCutoffPullback_apply_of_mem he _ _ hp, ContMDiffMap.coe_ofContDiff]
    · simp [OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he _ _ hp]
  simp only [OpenPartialHomeomorph.complexChartCompression_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, hinput, ContMDiffMap.coe_mul, Pi.mul_apply]
  exact smul_eq_right_of_ne_zero_imp_eq_one fun h ↦
    hφ₁ ⟨subset_tsupport _ (left_ne_zero_of_smul h),
      subset_tsupport _ (left_ne_zero_of_mul (right_ne_zero_of_smul h))⟩

/-- **Pseudolocality.** If `P` is a classical pseudodifferential operator and `f`, `g` are smooth
functions with disjoint supports, then `u ↦ f · P (g u)` has order `-∞`. -/
theorem mulLeft_comp_comp_mulLeft_mem_smoothingPseudodifferentialOperators {m : ℝ}
    (hP : P ∈ classicalPseudodifferentialOperators m)
    {f g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hfg : Disjoint (tsupport f) (tsupport g)) :
    LinearMap.mulLeft ℂ f ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ g ∈
      smoothingPseudodifferentialOperators := by
  have hQ := mem_classicalPseudodifferentialOperators_iff.1
    (mulLeft_comp_mem_classicalPseudodifferentialOperators
      (comp_mulLeft_mem_classicalPseudodifferentialOperators hP g) f)
  refine (mem_smoothingPseudodifferentialOperators_iff_isSmoothing m).2
    ⟨hQ.1, fun e he φ ψ ↦ ?_⟩
  obtain ⟨a, ha⟩ := hQ.2 e he φ ψ
  -- In the chart, the output of the compression is supported in the compact set `F` and only
  -- depends on the input on the compact set `G`; these are disjoint since `f` and `g` are. Choose
  -- cutoffs `φ₁ = 1` on `F` and `ψ₁ = 1` on `G` with disjoint supports.
  have hF := φ.hasCompactSupport.isCompact.inter_preimage
    (e.continuousOn_symm.mono φ.tsupport_subset) (isClosed_tsupport f)
  have hG := ψ.hasCompactSupport.isCompact.inter_preimage
    (e.continuousOn_symm.mono ψ.tsupport_subset) (isClosed_tsupport g)
  obtain ⟨U, V, hU, hV, hFU, hGV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact hF hG
    (disjoint_left.2 fun x hxF hxG ↦ hfg.ne_of_mem hxF.2 hxG.2 rfl)
  obtain ⟨φ₁, hφ₁, -, hφ₁1, hφ₁c, hφ₁U⟩ := hF.exists_contDiff_cutoff hU hFU
  obtain ⟨ψ₁, hψ₁, -, hψ₁1, hψ₁c, hψ₁V⟩ := hG.exists_contDiff_cutoff hV hGV
  -- Away from the diagonal the kernel of `Op(a)` is smooth, so `φ₁ Op(a) ψ₁` is smoothing.
  obtain ⟨r, hr, hop⟩ := a.toSymbol.exists_isSmoothing_smul_quantizeSchwartzValue_comp_eq
    (κ := OpenPartialHomeomorph.refl (CoordinateSpace n)) contDiff_id.contDiffOn
    contDiff_id.contDiffOn hφ₁ hφ₁c (subset_univ _) hψ₁ hψ₁c (subset_univ _)
    (hUV.mono hφ₁U hψ₁V)
  refine ⟨r, hr, fun u x ↦ ?_⟩
  -- The compression of `f P g` is `φ₁ Op(a) ψ₁`.
  set w : 𝓢(CoordinateSpace n, ℂ) :=
    (hψ₁c.smul_right (f' := ⇑u)).toSchwartzMap (hψ₁.smul (u.smooth ⊤))
  have hw (y : CoordinateSpace n) : w y = ψ₁ y • u y := HasCompactSupport.toSchwartzMap_toFun _ _ y
  rw [← hop u w (fun y _ ↦ hw y) (fun z hz ↦ (hz (mem_univ z)).elim) x,
    ← complexChartCompression_mulLeft_comp_comp_mulLeft_eq_smul he φ ψ
      (fun y hy ↦ interior_subset (hφ₁1 hy)) (fun y hy ↦ interior_subset (hψ₁1 hy)) hw x, ← ha]
  simp

end TauCeti

/-! ### Chart quantizations modulo operators of order `-∞` -/

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {m : ℝ}
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
  {ι : Type*} {s : Finset ι} {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  {he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {ρ χ φ ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ)} {a : ι → ClassicalSymbol n ℂ ℂ m}

/-- **Classical pseudodifferential operators are patched from their chart symbols, modulo order
`-∞`.** Let `P` be a classical pseudodifferential operator of order `m`. For finitely many charts
`eᵢ`, let `ρᵢ` be cutoffs, `χᵢ` cutoffs equal to `1` near the supports of the `ρᵢ`, and `aᵢ` the
symbol of the chart compression of `P` by `ρᵢ` and `χᵢ`. If `φᵢ` and `ψᵢ` are cutoffs equal to
`1` on the supports of `ρᵢ` and `χᵢ`, then `(∑ᵢ ρᵢ) P` and the patched operator
`∑ᵢ Op_{eᵢ}(aᵢ)`, localized by the `φᵢ` and `ψᵢ`, differ by an operator of order `-∞`. -/
theorem mulLeft_sum_comp_sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hχ : ∀ i ∈ s, ∀ᶠ y in 𝓝ˢ (tsupport (ρ i)), χ i y = 1)
    (ha : ∀ i ∈ s, ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
      quantizeSchwartzValue (a i).toSymbol.coefficient u x =
        (e i).complexChartCompression (he i) (ρ i) (χ i) P
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    (hφ : ∀ i ∈ s, EqOn (φ i) 1 (tsupport (ρ i))) (hψ : ∀ i ∈ s, EqOn (ψ i) 1 (tsupport (χ i))) :
    LinearMap.mulLeft ℂ (∑ i ∈ s, (e i).complexCutoffPullback (he i) (ρ i) 1) ∘ₗ P -
        ∑ i ∈ s, (e i).chartQuantization (he i) (φ i) (ψ i) (a i) ∈
      smoothingPseudodifferentialOperators := by
  -- Each chart quantization is `ρᵢ P χᵢ`, so the difference is `∑ᵢ ρᵢ P (1 - χᵢ)`.
  have key : LinearMap.mulLeft ℂ (∑ i ∈ s, (e i).complexCutoffPullback (he i) (ρ i) 1) ∘ₗ P -
      ∑ i ∈ s, (e i).chartQuantization (he i) (φ i) (ψ i) (a i) =
      ∑ i ∈ s, LinearMap.mulLeft ℂ ((e i).complexCutoffPullback (he i) (ρ i) 1) ∘ₗ P ∘ₗ
        LinearMap.mulLeft ℂ (1 - (e i).complexCutoffPullback (he i) (χ i) 1) := by
    rw [Finset.sum_congr rfl fun i hi ↦ (e i).chartQuantization_eq_mulLeft_comp_comp_mulLeft (he i)
      (ha i hi) (hφ i hi) (hψ i hi)]
    ext u : 1
    simp [Finset.sum_mul, sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [key]
  exact Submodule.sum_mem _ fun i hi ↦
    mulLeft_comp_comp_mulLeft_mem_smoothingPseudodifferentialOperators hP
      (OpenPartialHomeomorph.disjoint_tsupport_complexCutoffPullback_one_sub (he i) (hχ i hi))

/-- **A classical pseudodifferential operator is a sum of chart quantizations modulo order
`-∞`.** In the setting of
`TauCeti.mulLeft_sum_comp_sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators`, if
the cutoffs `ρᵢ`, read on `M`, add up to `1`, then `P - ∑ᵢ Op_{eᵢ}(aᵢ)` has order `-∞`. -/
theorem sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hρ : ∑ i ∈ s, (e i).complexCutoffPullback (he i) (ρ i) 1 = 1)
    (hχ : ∀ i ∈ s, ∀ᶠ y in 𝓝ˢ (tsupport (ρ i)), χ i y = 1)
    (ha : ∀ i ∈ s, ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
      quantizeSchwartzValue (a i).toSymbol.coefficient u x =
        (e i).complexChartCompression (he i) (ρ i) (χ i) P
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    (hφ : ∀ i ∈ s, EqOn (φ i) 1 (tsupport (ρ i))) (hψ : ∀ i ∈ s, EqOn (ψ i) 1 (tsupport (χ i))) :
    P - ∑ i ∈ s, (e i).chartQuantization (he i) (φ i) (ψ i) (a i) ∈
      smoothingPseudodifferentialOperators := by
  simpa [hρ, LinearMap.mulLeft_one] using
    mulLeft_sum_comp_sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators hP hχ ha hφ
      hψ

/-- **On a compact manifold, a classical pseudodifferential operator is a finite sum of chart
quantizations modulo order `-∞`.** If `M` is compact and `P` is a classical pseudodifferential
operator of order `m`, there are finitely many points `x`, cutoffs `φₓ`, `ψₓ` in the preferred
charts at these points and classical symbols `aₓ` of order `m` such that `P - ∑ₓ Op_{eₓ}(aₓ)`
has order `-∞`. Conversely every such sum is a classical pseudodifferential operator of order `m`
(`OpenPartialHomeomorph.chartQuantization_mem_classicalPseudodifferentialOperators`). -/
theorem exists_sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators
    [CompactSpace M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    ∃ (s : Finset M) (φ ψ : ∀ x : M, 𝓓(⟨(chartAt (CoordinateSpace n) x).target,
        (chartAt (CoordinateSpace n) x).open_target⟩, ℝ)) (a : M → ClassicalSymbol n ℂ ℂ m),
      P - ∑ x ∈ s, (chartAt (CoordinateSpace n) x).chartQuantization
          (IsManifold.chart_mem_maximalAtlas x) (φ x) (ψ x) (a x) ∈
        smoothingPseudodifferentialOperators := by
  -- A smooth partition of unity `f` subordinate to the chart sources; on the compact space `M`
  -- only the finitely many `x ∈ s` have `f x ≠ 0`.
  obtain ⟨f, hf⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source 𝓘(ℝ, CoordinateSpace n) M
  have hs := f.locallyFinite.finite_nonempty_of_compact
  -- Each `f x` is the pullback of a cutoff `ρ x` in the chart at `x`; `χ x` and `ψ x` are cutoffs
  -- equal to `1` near the supports of `ρ x` and `χ x`, and `a x` is the chart symbol of `P`.
  choose ρ hρ using fun x ↦ OpenPartialHomeomorph.exists_cutoffPullback_one_eq
    (IsManifold.chart_mem_maximalAtlas x) (isCompact_univ.of_isClosed_subset (isClosed_tsupport _)
      (subset_univ _)) (hf x)
  choose χ hχ using fun x ↦ TestFunction.exists_eventually_eq_one (n := ⊤)
    (ρ x).hasCompactSupport.isCompact (ρ x).tsupport_subset
  choose ψ hψ using fun x ↦ TestFunction.exists_eventually_eq_one (n := ⊤)
    (χ x).hasCompactSupport.isCompact (χ x).tsupport_subset
  choose a ha using fun x ↦ (mem_classicalPseudodifferentialOperators_iff.1 hP).2 _
    (IsManifold.chart_mem_maximalAtlas x) (ρ x) (χ x)
  refine ⟨hs.toFinset, χ, ψ, a, sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators
    hP ?_ (fun x _ ↦ (hχ x).1) (fun x _ ↦ ha x) (fun x _ y hy ↦ (hχ x).1.self_of_nhdsSet y hy)
    (fun x _ y hy ↦ (hψ x).1.self_of_nhdsSet y hy)⟩
  ext p
  have hsum : ∑ x ∈ hs.toFinset, f x p = 1 :=
    f.sum_finsupport' p (mem_univ p) fun x hx ↦ hs.mem_toFinset.2 ⟨p, (f.mem_finsupport p).1 hx⟩
  simp only [ContMDiffMap.coe_sum, Finset.sum_apply,
    OpenPartialHomeomorph.complexCutoffPullback_one_apply, hρ,
    ContMDiffMap.coe_one, Pi.one_apply]
  exact_mod_cast hsum

end TauCeti
