/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Basic
public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.Local.Norm
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Local

/-!
# Order-one local Sobolev functions, `W1p`, and `WeakDerivStep`

Let `Ω` be an open subset of a finite-dimensional real normed space `E` with its Borel σ-algebra.
This file compares the order-one local Sobolev class `TauCeti.MemWkpLoc p Ω 1` with two global
quotient carriers:

1. For any locally finite measure `μ` on `E`, any Banach codomain `F`, and `1 ≤ p`, a function
   `u : E → F` lies in `MemWkpLoc p Ω 1 u μ` exactly when its restriction to every open `W` with
   compact closure contained in `Ω` is represented by an element of the complete closed-graph space
   `TauCeti.WeakDerivStep μ W p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict W)))`
   (`TauCeti.MemWkpLoc.exists_weakDerivStep`, `TauCeti.memWkpLoc_one_iff_forall_weakDerivStep`).
   No inner product on `E`, Haar assumption on `μ`, or basis/separability of `F` is used.

2. For an inner product space `E`, an additive Haar measure `μ` on `E`, and real-valued functions,
   `MemWkpLoc p Ω 1 u μ` agrees with `TauCeti.W1p μ W p` on every open `W` with compact closure
   contained in `Ω` (`TauCeti.MemWkpLoc.exists_w1p`, `TauCeti.memWkpLoc_one_iff_forall_w1p`).
   The weak gradient of that element is dual, through `InnerProductSpace.toDual`, to the weak
   derivative of `u` on `Ω`. A real function of finite `W^{1,p}(Ω)` norm `TauCeti.eLpNormWkp p Ω 1`
   is represented by an element of `W1p μ Ω p` whose norm is at most that size
   (`TauCeti.exists_w1p_enorm_le_eLpNormWkp`).

## Main declarations

* `TauCeti.MemWkpLoc.exists_weakDerivStep`: a Banach-valued member of `MemWkpLoc p Ω 1` is
  represented in `WeakDerivStep` over the identity of `Lp F p` on every relatively compact open
  subdomain.
* `TauCeti.memWkpLoc_one_iff_forall_weakDerivStep`: the Banach-valued order-one comparison with
  `WeakDerivStep`.
* `TauCeti.WeakDerivStep.tendsto_iff_eLpNorm_of_ae_eq`: convergence in `WeakDerivStep` over the
  identity of `Lp F p` in terms of the extended Bochner `Lᵖ` norms of arbitrary representatives.
* `TauCeti.MemWkpLoc.exists_w1p`: a real member of `MemWkpLoc p Ω 1` is represented by an element
  of `W1p` on every relatively compact open subset of `Ω`, with the dual weak gradient.
* `TauCeti.exists_w1p_enorm_le_eLpNormWkp`: a real function of finite `W^{1,p}(Ω)` norm is
  represented in `W1p μ Ω p` with no larger norm.
* `TauCeti.memWkpLoc_one_iff_forall_w1p`: the order-one comparison with `W1p`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces).
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2, pp. 2–3.
-/

public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

section WeakDerivStep

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsLocallyFiniteMeasure μ]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E}

/-- **Banach-valued local Sobolev functions are represented in `WeakDerivStep` on relatively
compact subdomains.** Let `u ∈ MemWkpLoc p Ω 1` with values in a Banach space `F` and weak
derivative `D` on `Ω`. On every open `W` whose closure is compact and contained in `Ω`, `(u, D)`
is represented by an element of the complete closed-graph space
`WeakDerivStep μ W p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict W)))`. -/
theorem MemWkpLoc.exists_weakDerivStep {u : E → F} (hu : MemWkpLoc p Ω 1 u μ)
    {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn μ Ω u D) {W : Opens E}
    (hWc : IsCompact (closure (W : Set E))) (hWΩ : closure (W : Set E) ⊆ Ω) :
    ∃ v : WeakDerivStep μ W p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict W))),
      ⇑(WeakDerivStep.prev _ v) =ᵐ[μ.restrict W] u ∧
      ⇑(WeakDerivStep.weakFDeriv _ v) =ᵐ[μ.restrict W] D := by
  have huW : MemLp u p (μ.restrict W) := hu.memLpLoc.memLp_of_closure_subset hWc hWΩ
  have hDW : MemLp D p (μ.restrict W) :=
    (hu.memLpLoc_of_hasWeakFDerivOn hD).memLp_of_closure_subset hWc hWΩ
  let base := ContinuousLinearMap.id ℝ (Lp F p (μ.restrict W))
  have hDw : HasWeakFDerivOn μ W (base (huW.toLp u)) (hDW.toLp D) :=
    ((hD.mono (SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ))).congr_ae
      huW.coeFn_toLp.symm).congr_ae_deriv hDW.coeFn_toLp.symm
  refine ⟨WeakDerivStep.mk base (huW.toLp u) (hDW.toLp D) hDw, ?_, ?_⟩
  · rw [WeakDerivStep.prev_mk]; exact huW.coeFn_toLp
  · rw [WeakDerivStep.weakFDeriv_mk]; exact hDW.coeFn_toLp

/-- **Comparison with `WeakDerivStep` at order one for Banach-valued maps.** A map `u : E → F` into
a Banach space lies in `MemWkpLoc p Ω 1` exactly when its restriction to every open `W` with compact
closure contained in `Ω` is represented by an element of the complete graph space
`WeakDerivStep μ W p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict W)))`. -/
theorem memWkpLoc_one_iff_forall_weakDerivStep {u : E → F} :
    MemWkpLoc p Ω 1 u μ ↔
      ∀ W : Opens E, IsCompact (closure (W : Set E)) → closure (W : Set E) ⊆ Ω →
        ∃ v : WeakDerivStep μ W p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict W))),
          ⇑(WeakDerivStep.prev _ v) =ᵐ[μ.restrict W] u := by
  constructor
  · intro hu W hWc hWΩ
    obtain ⟨D, hD, -⟩ := hu.exists_weakFDeriv_of_isOpen
    obtain ⟨v, hv, -⟩ := hu.exists_weakDerivStep hD hWc hWΩ
    exact ⟨v, hv⟩
  · intro h
    have hcover : ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ W : Opens E, K ⊆ W ∧ W ≤ Ω ∧
        ∃ v : WeakDerivStep μ W p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict W))),
          ⇑(WeakDerivStep.prev _ v) =ᵐ[μ.restrict W] u := by
      intro K hK hKΩ
      obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
      exact ⟨W, hKW, SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ), h W hWc hWΩ⟩
    obtain ⟨D, hD⟩ : ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω u D := by
      refine exists_hasWeakFDerivOn_iff_locally.2 fun x hx => ?_
      obtain ⟨W, hxW, -, v, hv⟩ := hcover {x} isCompact_singleton (singleton_subset_iff.2 hx)
      exact ⟨W, hxW rfl, _, (WeakDerivStep.hasWeakFDerivOn_base_prev _ v).congr_ae hv⟩
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨memLpLoc_iff.2 fun K hKΩ hK => ?_, D, hD,
      memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKΩ hK => ?_)⟩
    · obtain ⟨W, hKW, -, v, hv⟩ := hcover K hK hKΩ
      have hmono : μ.restrict K ≤ μ.restrict (W : Set E) := Measure.restrict_mono hKW le_rfl
      exact ((Lp.memLp (WeakDerivStep.prev _ v)).mono_measure hmono).ae_eq (ae_mono hmono hv)
    · obtain ⟨W, hKW, hWΩ, v, hv⟩ := hcover K hK hKΩ
      have hmono : μ.restrict K ≤ μ.restrict (W : Set E) := Measure.restrict_mono hKW le_rfl
      have hae : ⇑(WeakDerivStep.weakFDeriv _ v) =ᵐ[μ.restrict W] D :=
        ((WeakDerivStep.hasWeakFDerivOn_base_prev _ v).congr_ae hv).ae_eq (hD.mono hWΩ)
      exact ((Lp.memLp (WeakDerivStep.weakFDeriv _ v)).mono_measure hmono).ae_eq (ae_mono hmono hae)

/-- **Convergence in `WeakDerivStep` through arbitrary representatives.** A net in the complete
graph space `WeakDerivStep μ Ω p (id : Lp F p →L Lp F p)` converges exactly when any choice of
almost-everywhere representatives of the functions and their weak derivatives converge in their
extended Bochner `Lᵖ` norms. This includes `p = ∞`. -/
theorem WeakDerivStep.tendsto_iff_eLpNorm_of_ae_eq {I : Type*} {l : Filter I}
    {v : I → WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))}
    {v₀ : WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))}
    {u : I → E → F} {u₀ : E → F} {D : I → E → E →L[ℝ] F} {D₀ : E → E →L[ℝ] F}
    (hu : ∀ i, ⇑(WeakDerivStep.prev _ (v i)) =ᵐ[μ.restrict Ω] u i)
    (hu₀ : ⇑(WeakDerivStep.prev _ v₀) =ᵐ[μ.restrict Ω] u₀)
    (hD : ∀ i, ⇑(WeakDerivStep.weakFDeriv _ (v i)) =ᵐ[μ.restrict Ω] D i)
    (hD₀ : ⇑(WeakDerivStep.weakFDeriv _ v₀) =ᵐ[μ.restrict Ω] D₀) :
    Filter.Tendsto v l (nhds v₀) ↔
      Filter.Tendsto (fun i => eLpNorm (u i - u₀) p (μ.restrict Ω)) l (nhds 0) ∧
      Filter.Tendsto (fun i => eLpNorm (D i - D₀) p (μ.restrict Ω)) l (nhds 0) := by
  rw [WeakDerivStep.tendsto_iff_prev_weakFDeriv,
    tendsto_iff_edist_tendsto_0, tendsto_iff_edist_tendsto_0]
  have heu : ∀ i, edist (WeakDerivStep.prev _ (v i)) (WeakDerivStep.prev _ v₀) =
      eLpNorm (u i - u₀) p (μ.restrict Ω) := fun i => by
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((hu i).sub hu₀)
  have heD : ∀ i, edist (WeakDerivStep.weakFDeriv _ (v i)) (WeakDerivStep.weakFDeriv _ v₀) =
      eLpNorm (D i - D₀) p (μ.restrict Ω) := fun i => by
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((hD i).sub hD₀)
  simp only [heu, heD]

end WeakDerivStep

section W1p

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens E}

/-- **Local Sobolev functions are Sobolev on relatively compact subdomains.** Let
`u ∈ MemWkpLoc p Ω 1` be real-valued, with weak derivative `D` on `Ω`. On every open `W` whose
closure is compact and contained in `Ω`, `u` is represented by an element of `W1p μ W p`
whose weak gradient is dual to `D`. -/
theorem MemWkpLoc.exists_w1p {u : E → ℝ} (hu : MemWkpLoc p Ω 1 u μ)
    {D : E → E →L[ℝ] ℝ} (hD : HasWeakFDerivOn μ Ω u D) {W : Opens E}
    (hWc : IsCompact (closure (W : Set E))) (hWΩ : closure (W : Set E) ⊆ Ω) :
    ∃ v : W1p μ W p, W1p.value v =ᵐ[μ.restrict W] u ∧
      W1p.gradient v =ᵐ[μ.restrict W]
        fun z => (InnerProductSpace.toDual ℝ E).symm (D z) := by
  have hmono : μ.restrict (W : Set E) ≤ μ.restrict (closure (W : Set E)) :=
    Measure.restrict_mono subset_closure le_rfl
  exact W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn
    ((memLpLoc_iff.1 hu.memLpLoc _ hWΩ hWc).mono_measure hmono)
    ((memLpLoc_iff.1 (hu.memLpLoc_of_hasWeakFDerivOn hD) _ hWΩ hWc).mono_measure hmono)
    (hD.mono (SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ)))

/-- **The `W1p` norm is bounded by the `W^{1,p}` norm.** A real function `u` whose `W^{1,p}(Ω)`
norm `TauCeti.eLpNormWkp p Ω 1 u μ` is finite is represented by an element of `W1p μ Ω p` whose
extended norm is at most `eLpNormWkp p Ω 1 u μ`. -/
theorem exists_w1p_enorm_le_eLpNormWkp {u : E → ℝ} (hu : eLpNormWkp p Ω 1 u μ ≠ ∞) :
    ∃ v : W1p μ Ω p, W1p.value v =ᵐ[μ.restrict Ω] u ∧ ‖v‖ₑ ≤ eLpNormWkp p Ω 1 u μ := by
  obtain ⟨D, hD, hDfin⟩ := exists_hasWeakFDerivOn_of_eLpNormWkp_succ_ne_top hu
  rw [Opens.interior_coe] at hD
  rw [eLpNormWkp_zero, ← lt_top_iff_ne_top] at hDfin
  have hu1 : MemLp u p (μ.restrict Ω) :=
    memLp_iff.2 (lt_top_iff_ne_top.2 (ne_top_of_le_ne_top hu eLpNorm_le_eLpNormWkp))
  obtain ⟨v, hv, hg⟩ :=
    W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn hu1 (memLp_iff.2 hDfin) hD
  rw [eLpNormWkp_succ_eq_of_hasWeakFDerivOn hD, eLpNormWkp_zero]
  exact ⟨v, hv, W1p.enorm_le_eLpNorm_add_eLpNorm_of_ae_eq hv hg⟩

/-- **Comparison with `W1p` at order one.** A real function lies in `MemWkpLoc p Ω 1` exactly when
its restriction to every open `W` with compact closure contained in `Ω` is represented by an element
of `W1p μ W p`. The weak gradients then correspond to the weak derivative of `u` on `Ω`
through `InnerProductSpace.toDual`, by `TauCeti.MemWkpLoc.exists_w1p`. -/
theorem memWkpLoc_one_iff_forall_w1p {u : E → ℝ} :
    MemWkpLoc p Ω 1 u μ ↔ ∀ W : Opens E, IsCompact (closure (W : Set E)) →
      closure (W : Set E) ⊆ Ω → ∃ v : W1p μ W p, W1p.value v =ᵐ[μ.restrict W] u := by
  constructor
  · intro hu W hWc hWΩ
    obtain ⟨D, hD, -⟩ := hu.exists_weakFDeriv_of_isOpen
    obtain ⟨v, hv, -⟩ := hu.exists_w1p hD hWc hWΩ
    exact ⟨v, hv⟩
  · intro h
    have hcover : ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ W : Opens E, K ⊆ W ∧ W ≤ Ω ∧
        ∃ v : W1p μ W p, W1p.value v =ᵐ[μ.restrict W] u := by
      intro K hK hKΩ
      obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
      exact ⟨W, hKW, SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ), h W hWc hWΩ⟩
    obtain ⟨D, hD⟩ : ∃ D : E → E →L[ℝ] ℝ, HasWeakFDerivOn μ Ω u D := by
      refine exists_hasWeakFDerivOn_iff_locally.2 fun x hx => ?_
      obtain ⟨W, hxW, -, v, hv⟩ := hcover {x} isCompact_singleton (singleton_subset_iff.2 hx)
      exact ⟨W, hxW rfl, _, (W1p.hasWeakFDerivOn v).congr_ae hv⟩
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨memLpLoc_iff.2 fun K hKΩ hK => ?_, D, hD,
      memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKΩ hK => ?_)⟩
    · obtain ⟨W, hKW, -, v, hv⟩ := hcover K hK hKΩ
      have hmono : μ.restrict K ≤ μ.restrict (W : Set E) := Measure.restrict_mono hKW le_rfl
      exact ((Lp.memLp (W1p.value v)).mono_measure hmono).ae_eq (ae_mono hmono hv)
    · obtain ⟨W, hKW, hWΩ, v, hv⟩ := hcover K hK hKΩ
      have hmono : μ.restrict K ≤ μ.restrict (W : Set E) := Measure.restrict_mono hKW le_rfl
      have hae : (fun z => innerSL ℝ (W1p.gradient v z)) =ᵐ[μ.restrict W] D :=
        ((W1p.hasWeakFDerivOn v).congr_ae hv).ae_eq (hD.mono hWΩ)
      exact (((innerSL ℝ).comp_memLp' (Lp.memLp (W1p.gradient v))).mono_measure hmono).ae_eq
        (ae_mono hmono hae)

end W1p

end TauCeti
