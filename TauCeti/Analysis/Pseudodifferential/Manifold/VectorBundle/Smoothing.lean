/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Smoothing
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Basic
import TauCeti.Topology.Algebra.Support

/-!
# Operators of order `-∞` between vector bundles and pseudolocality

Let `M` be a manifold modelled on `ℝⁿ` and let `E`, `F` be smooth complex vector bundles over `M`
with model fibres `V` and `W`. The **operators of order `-∞`** from the smooth sections of `E` to
those of `F` are the classical pseudodifferential operators between the bundles of every real order
(`TauCeti.sectionSmoothingPseudodifferentialOperators`). This is the bundle version of
`TauCeti.smoothingPseudodifferentialOperators`, and the class modulo which parametrices of
elliptic operators `Γ(E) → Γ(F)` invert them.

An operator has order `-∞` exactly when it is properly supported and all its matrix entries
`f ↦ χ ℓ(t' (P (f ψ t⁻¹ v)))` in cut-off frames (`TauCeti.sectionEntry`) have order `-∞`
(`TauCeti.mem_sectionSmoothingPseudodifferentialOperators_iff_sectionEntry`). In a chart over which
both bundles are trivial, the compression of an operator of order `-∞` is the quantization of a
smoothing symbol with values in `V →L[ℂ] W`
(`TauCeti.exists_isSmoothing_quantizeSchwartzValue_eq_apply_chartCutoffSection`).

The patching of pseudodifferential operators between bundles from local data rests on
**pseudolocality** (Hörmander III, §18.1; Melrose, §5.3): if `P` is a classical pseudodifferential
operator between the bundles and `f`, `g` are smooth functions with disjoint supports, then
`s ↦ f P (g s)` has order `-∞`
(`TauCeti.smul_comp_smul_mem_sectionSmoothingPseudodifferentialOperators`). Its entries are
`f` times the entries of `P` times `g`, so this is the scalar pseudolocality
`TauCeti.mulLeft_comp_comp_mulLeft_mem_smoothingPseudodifferentialOperators` entry by entry.

## Main definitions

* `TauCeti.sectionSmoothingPseudodifferentialOperators`: the operators of order `-∞` from `Γ(E)`
  to `Γ(F)`.

## Main results

* `TauCeti.mem_sectionSmoothingPseudodifferentialOperators_iff_sectionEntry`: an operator has order
  `-∞` exactly when it is properly supported and its entries have order `-∞`.
* `TauCeti.exists_isSmoothing_quantizeSchwartzValue_eq_apply_chartCutoffSection`: the chart
  compressions of an operator of order `-∞` are quantizations of smoothing symbols.
* `TauCeti.smul_mem_sectionSmoothingPseudodifferentialOperators`,
  `TauCeti.comp_smul_mem_sectionSmoothingPseudodifferentialOperators`: multiplying by smooth
  functions on either side keeps the order `-∞`.
* `TauCeti.smul_comp_smul_mem_sectionSmoothingPseudodifferentialOperators`: pseudolocality.
* `TauCeti.smul_sub_smul_comp_smul_mem_sectionSmoothingPseudodifferentialOperators`: localization,
  `ρ P` and `ρ P χ` differ by an operator of order `-∞` when `χ = 1` near the support of `ρ`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1
  (pseudodifferential operators on manifolds and between sections of vector bundles).
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
-/

public section

noncomputable section

open Bundle Set
open scoped ContDiff Distributions Manifold SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M] [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}


/-! ### Operators of order `-∞` -/

/-- The **operators of order `-∞`** from the smooth sections of `E` to those of `F`: the classical
pseudodifferential operators between the bundles of every real order. Their entries in cut-off
frames are the operators of order `-∞` on `M`
(`TauCeti.mem_sectionSmoothingPseudodifferentialOperators_iff_sectionEntry`). -/
def sectionSmoothingPseudodifferentialOperators :
    Submodule ℂ
      (Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯) :=
  ⨅ m : ℝ, sectionClassicalPseudodifferentialOperators m

theorem mem_sectionSmoothingPseudodifferentialOperators_iff :
    P ∈ sectionSmoothingPseudodifferentialOperators ↔
      ∀ m : ℝ, P ∈ sectionClassicalPseudodifferentialOperators m :=
  Submodule.mem_iInf _

/-- An operator of order `-∞` between bundles is a classical pseudodifferential operator of every
order `m`. -/
theorem sectionSmoothingPseudodifferentialOperators_le_sectionClassicalPseudodifferentialOperators
    (m : ℝ) :
    sectionSmoothingPseudodifferentialOperators (n := n) (M := M) (V := V) (E := E) (W := W)
      (F := F) ≤ sectionClassicalPseudodifferentialOperators m :=
  iInf_le _ m

/-- **Operators of order `-∞` in frames.** An operator between bundles has order `-∞` exactly when
it is properly supported and, for all trivializations `t` of `E` and `t'` of `F` in their atlases,
real smooth functions `ψ` and `χ` supported in their base sets, vectors `v` of the model fibre of
`E` and complex-linear functionals `ℓ` on the model fibre of `F`, its entry
`f ↦ χ ℓ(t' (P (f ψ t⁻¹ v)))` is an operator of order `-∞` on `M`. -/
theorem mem_sectionSmoothingPseudodifferentialOperators_iff_sectionEntry :
    P ∈ sectionSmoothingPseudodifferentialOperators ↔ IsSectionProperlySupported P ∧
      ∀ (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
        (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
        (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
        (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ),
        sectionEntry t ψ hψ v t' χ hχ ℓ P ∈ smoothingPseudodifferentialOperators := by
  simp only [mem_sectionSmoothingPseudodifferentialOperators_iff,
    mem_sectionClassicalPseudodifferentialOperators_iff,
    mem_smoothingPseudodifferentialOperators_iff]
  exact ⟨fun hP ↦ ⟨(hP 0).1, fun t _ ψ hψ v t' _ χ hχ ℓ m ↦ (hP m).2 t ψ hψ v t' χ hχ ℓ⟩,
    fun hP m ↦ ⟨hP.1, fun t _ ψ hψ v t' _ χ hχ ℓ ↦ hP.2 t ψ hψ v t' χ hχ ℓ m⟩⟩

/-- **Multiplication on the left.** If `P` has order `-∞` between bundles, then so does
`s ↦ g P s` for every complex-valued smooth function `g`. -/
theorem smul_mem_sectionSmoothingPseudodifferentialOperators
    (hP : P ∈ sectionSmoothingPseudodifferentialOperators)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    g • P ∈ sectionSmoothingPseudodifferentialOperators :=
  mem_sectionSmoothingPseudodifferentialOperators_iff.2 fun m ↦
    smul_mem_sectionClassicalPseudodifferentialOperators
      (mem_sectionSmoothingPseudodifferentialOperators_iff.1 hP m) g

/-- **Multiplication on the right.** If `P` has order `-∞` between bundles, then so does
`s ↦ P (g s)` for every complex-valued smooth function `g`. -/
theorem comp_smul_mem_sectionSmoothingPseudodifferentialOperators
    (hP : P ∈ sectionSmoothingPseudodifferentialOperators)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    P ∘ₗ (g • LinearMap.id) ∈ sectionSmoothingPseudodifferentialOperators :=
  mem_sectionSmoothingPseudodifferentialOperators_iff.2 fun m ↦
    comp_smul_mem_sectionClassicalPseudodifferentialOperators
      (mem_sectionSmoothingPseudodifferentialOperators_iff.1 hP m) g

/-- **Operators of order `-∞` in charts.** Let `P` have order `-∞` between bundles, `e` a chart of
the maximal atlas whose source lies in the base sets of trivializations `t` of `E` and `t'` of `F`,
and `φ`, `ψ` cutoffs with compact supports in the chart target. Then for every real `m` the
compression

`u ↦ φ · t' (P (t⁻¹ ((ψ u) ∘ e))) ∘ e⁻¹`

of `P` agrees on Schwartz functions `u : ℝⁿ → V` with the quantization `Op(r)` of a smoothing
symbol `r` of order `m` with values in `V →L[ℂ] W`. -/
theorem exists_isSmoothing_quantizeSchwartzValue_eq_apply_chartCutoffSection
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hP : P ∈ sectionSmoothingPseudodifferentialOperators)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t] (hE : e.source ⊆ t.baseSet)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t'] (hF : e.source ⊆ t'.baseSet)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (m : ℝ) :
    ∃ r : Symbol n V W m, r.IsSmoothing ∧
      ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
        quantizeSchwartzValue r.coefficient u y =
          φ y • t'.continuousLinearMapAt ℂ (e.symm y)
            (P (t.chartCutoffSection he hE ψ u) (e.symm y)) := by
  -- The chart symbols of order `m` and of every order `m'` have the same quantization, hence the
  -- same coefficient.
  obtain ⟨a, ha⟩ := exists_quantizeSchwartzValue_eq_apply_chartCutoffSection he t hE
    (mem_sectionSmoothingPseudodifferentialOperators_iff.1 hP m) t' hF φ ψ
  refine ⟨a.toSymbol,
    Symbol.isSmoothing_iff_forall_exists_quantizeSchwartzValue_eq.2 fun m' ↦ ?_, ha⟩
  obtain ⟨b, hb⟩ := exists_quantizeSchwartzValue_eq_apply_chartCutoffSection he t hE
    (mem_sectionSmoothingPseudodifferentialOperators_iff.1 hP m') t' hF φ ψ
  exact ⟨b.toSymbol, fun u _ ↦ funext fun y ↦ (hb u y).trans (ha u y).symm⟩

/-! ### Pseudolocality -/

omit [T2Space M] in
/-- The entries of `s ↦ f P (g s)` are the entries of `P`, multiplied by `f` on the left and by `g`
on the right. -/
theorem sectionEntry_smul_comp_smul (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
    (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ)
    (f g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    sectionEntry t ψ hψ v t' χ hχ ℓ (f • (P ∘ₗ (g • LinearMap.id))) =
      LinearMap.mulLeft ℂ f ∘ₗ sectionEntry t ψ hψ v t' χ hχ ℓ P ∘ₗ LinearMap.mulLeft ℂ g := by
  ext u x
  simp [mul_smul, mul_left_comm]

/-- **Pseudolocality.** If `P` is a classical pseudodifferential operator between bundles and `f`,
`g` are smooth functions with disjoint supports, then `s ↦ f P (g s)` has order `-∞`. -/
theorem smul_comp_smul_mem_sectionSmoothingPseudodifferentialOperators {m : ℝ}
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    {f g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hfg : Disjoint (tsupport f) (tsupport g)) :
    f • (P ∘ₗ (g • LinearMap.id)) ∈ sectionSmoothingPseudodifferentialOperators := by
  refine mem_sectionSmoothingPseudodifferentialOperators_iff_sectionEntry.2
    ⟨(mem_sectionClassicalPseudodifferentialOperators_iff.1
      (smul_mem_sectionClassicalPseudodifferentialOperators
        (comp_smul_mem_sectionClassicalPseudodifferentialOperators hP g) f)).1,
      fun t _ ψ hψ v t' _ χ hχ ℓ ↦ ?_⟩
  rw [sectionEntry_smul_comp_smul]
  exact mulLeft_comp_comp_mulLeft_mem_smoothingPseudodifferentialOperators
    ((mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2 t ψ hψ v t' χ hχ ℓ) hfg

/-- **Localization modulo order `-∞`.** If `P` is a classical pseudodifferential operator between
bundles and the smooth function `χ` equals `1` near the support of the smooth function `ρ`, then
`s ↦ ρ P s` and `s ↦ ρ P (χ s)` differ by an operator of order `-∞`. -/
theorem smul_sub_smul_comp_smul_mem_sectionSmoothingPseudodifferentialOperators {m : ℝ}
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    {ρ χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hχ : ∀ᶠ x in 𝓝ˢ (tsupport ρ), χ x = 1) :
    ρ • P - ρ • (P ∘ₗ (χ • LinearMap.id)) ∈ sectionSmoothingPseudodifferentialOperators := by
  -- The difference is `ρ P (1 - χ)`, and `1 - χ` vanishes near the support of `ρ`.
  have hdiff : ρ • P - ρ • (P ∘ₗ (χ • LinearMap.id)) = ρ • (P ∘ₗ ((1 - χ) • LinearMap.id)) := by
    ext s x
    simp [sub_smul, smul_sub]
  rw [hdiff]
  exact smul_comp_smul_mem_sectionSmoothingPseudodifferentialOperators hP
    (disjoint_tsupport_iff_eventuallyEq.2 (hχ.mono fun x hx ↦ by simp [hx]))

end TauCeti
