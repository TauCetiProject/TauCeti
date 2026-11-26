/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartQuantization
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle

/-!
# Quantizing a matrix-valued symbol in a chart between vector bundles

Let `M` be a manifold modelled on `ℝⁿ` and `E`, `F` smooth complex vector bundles over `M` with
model fibres `V` and `W`. Let `e` be a chart of the maximal smooth atlas whose source lies in the
base sets of trivializations `t` of `E` and `t'` of `F`, let `φ` and `ψ` be cutoffs with compact
supports in the chart target, and let `a` be a classical symbol of order `m` on `ℝⁿ` with values
in `V →L[ℂ] W`. The **chart quantization** of `a` between the bundles is the operator

`s ↦ t'⁻¹ ((φ · Op(a) (ψ · t (s ∘ e⁻¹))) ∘ e)`

from the smooth sections of `E` to those of `F`, extended by `0` off the chart source
(`OpenPartialHomeomorph.sectionChartQuantization`). Here `ψ · t (s ∘ e⁻¹)` is the reading of the
section `s` in the chart and the frame, a Schwartz function with values in `V`
(`Bundle.Trivialization.cutoffPushforwardSchwartz`). This is the local building block of
pseudodifferential operators between bundles (Hörmander III, §18.1; Taylor, Lecture I, §8;
Melrose, §5.3): an operator on `M` is assembled from such pieces by a partition of unity
subordinate to an atlas trivializing both bundles.

In frames of the model fibres the chart quantization is a matrix of scalar chart quantizations
(`OpenPartialHomeomorph.chartQuantization`) of the entries `wₖ* ∘ a ∘ vᵢ` of the symbol, read
against the cut-off frame coefficients of `s` and recombined along cut-off frame sections of `F`
(`OpenPartialHomeomorph.sectionChartQuantization_eq_sum`). Consequently it is a classical
pseudodifferential operator of order `m` between the bundles
(`OpenPartialHomeomorph.sectionChartQuantization_mem_sectionClassicalPseudodifferentialOperators`):
each matrix entry of the operator, in arbitrary trivializations and cut-off frames, is a finite
sum of scalar chart quantizations multiplied on both sides by smooth functions.

Conversely, a classical pseudodifferential operator `P` between the bundles, localized as
`φ P ψ` with the cutoffs read on `M`, is the chart quantization of the symbol of its chart
compression (`OpenPartialHomeomorph.exists_sectionChartQuantization_eq_smul_comp`), exactly and
not only modulo smoothing operators.

## Main definitions

* `OpenPartialHomeomorph.sectionChartQuantization`: the quantization `Op_{e,t,t'}(a)` of a
  classical symbol with values in `V →L[ℂ] W` in the chart `e` and the frames `t`, `t'`, localized
  by cutoffs `φ` and `ψ`.

## Main results

* `OpenPartialHomeomorph.isSectionProperlySupported_sectionChartQuantization`: the chart
  quantization is properly supported.
* `OpenPartialHomeomorph.sectionChartQuantization_eq_sum`: the chart quantization in frames, as a
  matrix of scalar chart quantizations.
* `OpenPartialHomeomorph.sectionChartQuantization_mem_sectionClassicalPseudodifferentialOperators`:
  the chart quantization of a classical symbol of order `m` is a classical pseudodifferential
  operator of order `m` between the bundles.
* `OpenPartialHomeomorph.sectionChartQuantization_eq_smul_comp` and
  `OpenPartialHomeomorph.exists_sectionChartQuantization_eq_smul_comp`: localization, `φ P ψ` is
  the chart quantization of the symbol of the compression of `P` by `φ` and `ψ`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1
  (pseudodifferential operators between sections of vector bundles).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
-/

public section

noncomputable section

open Bundle Filter Set TauCeti
open scoped ContDiff Distributions Manifold SchwartzMap Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M] [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (t : Trivialization V (π V E)) [MemTrivializationAtlas t] (hE : e.source ⊆ t.baseSet)
  (t' : Trivialization W (π W F)) [MemTrivializationAtlas t'] (hF : e.source ⊆ t'.baseSet)
  {m : ℝ}

namespace OpenPartialHomeomorph

/-! ### The chart quantization -/

/-- The section `x ↦ t'⁻¹ₓ (φ(e x) Op(a) v (e x))` of `F` on the chart source, extended by `0`, for
the reading `v = ψ · t (s ∘ e⁻¹)` of a section `s` of `E`. -/
private def sectionChartQuantizationFun (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n V W m) (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ :=
  (t'.chartTestSection (n := ⊤) e (contMDiffOn_of_mem_maximalAtlas he) hF
    (TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ)
      (a.toSymbol.contDiff_quantizeSchwartzValue (t.cutoffPushforwardSchwartz he hE ψ s)) φ)).val

omit [∀ x, Module ℂ (F x)] [VectorBundle ℂ W F] in
private theorem sectionChartQuantizationFun_apply_of_mem (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n V W m) (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) {x : M}
    (hx : x ∈ e.source) :
    sectionChartQuantizationFun he t hE t' hF φ ψ a s x = t'.symm x (φ (e x) •
      quantizeSchwartzValue a.toSymbol.coefficient (t.cutoffPushforwardSchwartz he hE ψ s) (e x))
    := by
  rw [sectionChartQuantizationFun, t'.chartTestSection_apply_of_mem (n := ⊤) e _ hF _ hx,
    t'.symmL_apply (hF hx), TestFunction.bilinLeftCLM_apply]
  simp only [ContinuousLinearMap.lsmul_apply]

omit [∀ x, Module ℂ (F x)] [VectorBundle ℂ W F] in
private theorem sectionChartQuantizationFun_apply_of_notMem
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n V W m)
    (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) {x : M} (hx : x ∉ e.source) :
    sectionChartQuantizationFun he t hE t' hF φ ψ a s x = 0 :=
  t'.chartTestSection_apply_of_notMem (n := ⊤) e _ hF _ hx

/-- The **quantization of a classical symbol `a` with values in `V →L[ℂ] W` in the chart `e`
between the bundles `E` and `F`**, read in the trivializations `t` of `E` and `t'` of `F` over the
chart source and localized by cutoffs `φ` and `ψ` with compact supports in the chart target: the
operator `s ↦ t'⁻¹ ((φ · Op(a) (ψ · t (s ∘ e⁻¹))) ∘ e)` from the smooth sections of `E` to those
of `F`, extended by `0` off the chart source. Here `Op(a)` is the left quantization of `a` on
Schwartz functions. -/
def sectionChartQuantization (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n V W m) :
    Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ where
  toFun := sectionChartQuantizationFun he t hE t' hF φ ψ a
  map_add' s s' := by
    ext x
    rw [ContMDiffSection.coe_add, Pi.add_apply]
    by_cases hx : x ∈ e.source
    · obtain ⟨C, -, hC⟩ := a.toSymbol.exists_bound_coefficient_slice (e x)
      simp only [sectionChartQuantizationFun_apply_of_mem he t hE t' hF _ _ _ _ hx, map_add,
        quantizeSchwartzValue_add_right
          (a.toSymbol.continuous_coefficient_slice (e x)).aestronglyMeasurable hC, smul_add]
      exact t'.symm_apply_add ℂ (hF hx) _ _
    · simp [sectionChartQuantizationFun_apply_of_notMem he t hE t' hF _ _ _ _ hx]
  map_smul' c s := by
    ext x
    rw [ContMDiffSection.coe_smul_of_normedAlgebra, Pi.smul_apply, RingHom.id_apply]
    by_cases hx : x ∈ e.source
    · simp only [sectionChartQuantizationFun_apply_of_mem he t hE t' hF _ _ _ _ hx, map_smul,
        quantizeSchwartzValue_smul_right, smul_comm (φ (e x))]
      exact t'.symm_apply_smul (hF hx) c _
    · simp [sectionChartQuantizationFun_apply_of_notMem he t hE t' hF _ _ _ _ hx]

/-- On the chart source, the chart quantization of `a` is `t'⁻¹ (φ · Op(a) v)` read through the
chart, for the reading `v = ψ · t (s ∘ e⁻¹)` of the section `s`. -/
theorem sectionChartQuantization_apply_of_mem (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n V W m) (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) {x : M}
    (hx : x ∈ e.source) :
    e.sectionChartQuantization he t hE t' hF φ ψ a s x = t'.symm x (φ (e x) •
      quantizeSchwartzValue a.toSymbol.coefficient (t.cutoffPushforwardSchwartz he hE ψ s) (e x)) :=
  sectionChartQuantizationFun_apply_of_mem he t hE t' hF φ ψ a s hx

/-- Off the chart source, the chart quantization vanishes. -/
theorem sectionChartQuantization_apply_of_notMem (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n V W m) (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) {x : M}
    (hx : x ∉ e.source) : e.sectionChartQuantization he t hE t' hF φ ψ a s x = 0 :=
  sectionChartQuantizationFun_apply_of_notMem he t hE t' hF φ ψ a s hx

/-- On the chart source, the chart quantization of `a`, read in the frame `t'`, is `φ · Op(a) v`
read through the chart, for the reading `v = ψ · t (s ∘ e⁻¹)` of the section `s`. -/
theorem continuousLinearMapAt_sectionChartQuantization (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n V W m) (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) {x : M}
    (hx : x ∈ e.source) :
    t'.continuousLinearMapAt ℂ x (e.sectionChartQuantization he t hE t' hF φ ψ a s x) = φ (e x) •
      quantizeSchwartzValue a.toSymbol.coefficient (t.cutoffPushforwardSchwartz he hE ψ s) (e x)
    := by
  rw [sectionChartQuantization_apply_of_mem he t hE t' hF φ ψ a s hx,
    ← t'.symmL_apply (R := ℂ) (hF hx), t'.continuousLinearMapAt_symmL (hF hx)]

/-- The chart quantization is supported in the image of the support of `φ` under the inverse of
the chart. -/
theorem tsupport_sectionChartQuantization_subset (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n V W m) (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    (e.sectionChartQuantization he t hE t' hF φ ψ a s).tsupport ⊆ e.symm '' tsupport φ := by
  refine (ContMDiffSection.tsupport_subset_iff (e.isCompact_symm_image_tsupport φ).isClosed).2
    fun x hx ↦ ?_
  by_cases hxs : x ∈ e.source
  · have hφ : φ (e x) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx ⟨e x, h, e.left_inv hxs⟩
    rw [sectionChartQuantization_apply_of_mem he t hE t' hF φ ψ a s hxs, hφ, zero_smul,
      t'.symm_apply_zero ℂ (hF hxs)]
  · exact sectionChartQuantization_apply_of_notMem he t hE t' hF φ ψ a s hxs

/-- The chart quantization only sees its input on the image of the support of `ψ` under the
inverse of the chart: it vanishes on every section vanishing there. -/
theorem sectionChartQuantization_eq_zero (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n V W m) {s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯}
    (hs : ∀ p ∈ e.symm '' tsupport ψ, s p = 0) :
    e.sectionChartQuantization he t hE t' hF φ ψ a s = 0 := by
  -- Since `s` vanishes on `e⁻¹(supp ψ)`, its reading `ψ · t (s ∘ e⁻¹)` is zero.
  have hv : t.cutoffPushforwardSchwartz he hE ψ s = 0 := by
    ext y
    by_cases hy : y ∈ tsupport ψ
    · simp [hs _ (mem_image_of_mem _ hy)]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  ext x
  rw [ContMDiffSection.coe_zero, Pi.zero_apply]
  by_cases hx : x ∈ e.source
  · rw [sectionChartQuantization_apply_of_mem he t hE t' hF φ ψ a s hx, hv,
      quantizeSchwartzValue_zero_right, smul_zero, t'.symm_apply_zero ℂ (hF hx)]
  · exact sectionChartQuantization_apply_of_notMem he t hE t' hF φ ψ a s hx

/-- **Chart quantizations between bundles are properly supported.** For every compact set, one may
take `K' = e⁻¹(supp φ) ∪ e⁻¹(supp ψ)`: the output is always supported in `e⁻¹(supp φ)`, and it
vanishes when the input vanishes near `e⁻¹(supp ψ)`. -/
theorem isSectionProperlySupported_sectionChartQuantization
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n V W m) :
    IsSectionProperlySupported (e.sectionChartQuantization he t hE t' hF φ ψ a) :=
  isSectionProperlySupported_iff.2 fun _ _ ↦ ⟨e.symm '' tsupport φ ∪ e.symm '' tsupport ψ,
    (e.isCompact_symm_image_tsupport φ).union (e.isCompact_symm_image_tsupport ψ),
    fun s _ ↦ (tsupport_sectionChartQuantization_subset he t hE t' hF φ ψ a s).trans
      subset_union_left,
    fun s hs p _ ↦ by
      rw [sectionChartQuantization_eq_zero he t hE t' hF φ ψ a fun q hq ↦
        (hs.filter_mono (nhdsSet_mono subset_union_right)).self_of_nhdsSet q hq,
        ContMDiffSection.coe_zero, Pi.zero_apply]⟩

/-! ### The chart quantization in frames -/

section Frame

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- **The chart quantization in frames.** Let `ρ` be a real smooth function on `M`, supported in
the base sets of `t` and `t'`, which equals `1` on `e⁻¹(supp φ ∪ supp ψ)`, and let `(vᵢ)` and
`(wₖ)` be bases of `V` and `W` with coordinate functionals `vᵢ*` and `wₖ*`. Then the chart
quantization of `a` applied to `s` is the sum over `i` and `k` of the scalar chart quantizations of
the entries `wₖ* ∘ a ∘ vᵢ`, applied to the cut-off frame coefficients `ρ vᵢ*(t s)` of `s` and
multiplied by the cut-off frame sections `ρ t'⁻¹ wₖ` of `F`. -/
theorem sectionChartQuantization_eq_sum (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n V W m) (ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
    (hρE : tsupport ρ ⊆ t.baseSet) (hρF : tsupport ρ ⊆ t'.baseSet)
    (hρ : ∀ y ∈ tsupport φ ∪ tsupport ψ, ρ (e.symm y) = 1) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (bV : Module.Basis ι ℂ V) (bW : Module.Basis κ ℂ W)
    (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    e.sectionChartQuantization he t hE t' hF φ ψ a s = ∑ k, ∑ i,
      e.chartQuantization he φ ψ
        (a.map (Symbol.entryMap (bW.coord k).toContinuousLinearMap (bV i)))
        (t.cutoffFrameCoeff ρ hρE (bV.coord i).toContinuousLinearMap s) •
          t'.cutoffFrameSection ρ hρF (bW k) := by
  ext x
  simp only [ContMDiffSection.coe_sum, Finset.sum_apply,
    ContMDiffSection.smul_apply_of_normedAlgebra]
  by_cases hx : x ∈ e.source
  swap
  · simp [sectionChartQuantization_apply_of_notMem he t hE t' hF φ ψ a s hx,
      chartQuantization_apply_of_notMem he _ _ _ _ hx]
  set v := t.cutoffPushforwardSchwartz he hE ψ s
  -- The scalar input of the `i`-th column is the `i`-th coordinate of the reading `v` of `s`.
  have hv (i : ι) (y : CoordinateSpace n) :
      v.postcompCLM (bV.coord i).toContinuousLinearMap y =
        ψ y • t.cutoffFrameCoeff ρ hρE (bV.coord i).toContinuousLinearMap s (e.symm y) := by
    rw [SchwartzMap.postcompCLM_apply, Bundle.Trivialization.cutoffPushforwardSchwartz_apply,
      Bundle.Trivialization.cutoffFrameCoeff_apply]
    by_cases hψ : ψ y = 0
    · simp [hψ]
    rw [hρ y (Or.inr (subset_tsupport _ hψ))]
    simp
  simp only [chartQuantization_apply_of_mem he φ ψ _ _ (hv _) hx,
    Bundle.Trivialization.cutoffFrameSection_apply, ClassicalSymbol.toSymbol_map]
  rw [sectionChartQuantization_apply_of_mem he t hE t' hF φ ψ a s hx]
  by_cases hφ : φ (e x) = 0
  · simp [hφ, t'.symm_apply_zero ℂ (hF hx)]
  have hρx : ρ x = 1 := by
    simpa [e.left_inv hx] using hρ (e x) (Or.inl (subset_tsupport _ hφ))
  rw [hρx, ← Symbol.sum_quantizeSchwartzValue_map_entryMap_smul a.toSymbol bV bW v (e x),
    ← Complex.coe_smul, t'.symm_apply_smul (hF hx), ← t'.symmL_apply (R := ℂ) (hF hx), map_sum]
  simp only [map_smul]
  simp only [t'.symmL_apply (R := ℂ) (hF hx), one_smul, Finset.smul_sum, smul_smul,
    Finset.sum_smul, Complex.real_smul]

/-- **Chart quantizations between bundles are classical pseudodifferential operators.** The
quantization of a classical symbol of order `m` with values in `V →L[ℂ] W`, in a chart of the
maximal atlas over whose source both bundles are trivialized, localized by cutoffs with compact
supports in the chart target, is a classical pseudodifferential operator of order `m` from the
sections of `E` to those of `F`. -/
theorem sectionChartQuantization_mem_sectionClassicalPseudodifferentialOperators
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n V W m) :
    e.sectionChartQuantization he t hE t' hF φ ψ a ∈ sectionClassicalPseudodifferentialOperators m
    := by
  refine mem_sectionClassicalPseudodifferentialOperators_iff.2
    ⟨isSectionProperlySupported_sectionChartQuantization he t hE t' hF φ ψ a,
      fun t₂ _ ψ₂ hψ₂ v t₂' _ χ hχ ℓ ↦ ?_⟩
  -- A cutoff `ρ` on `M`, supported in the chart source and equal to `1` over the supports of `φ`
  -- and `ψ`, gives cut-off frames which are frames there.
  obtain ⟨ρ, hρs, hρ⟩ := e.exists_tsupport_subset_source_and_eq_one he φ ψ
  set bV := Module.finBasis ℂ V
  set bW := Module.finBasis ℂ W
  -- In these frames the chart quantization is a sum of operators `s ↦ Q (c s) σ`.
  have hsum : e.sectionChartQuantization he t hE t' hF φ ψ a = ∑ k, ∑ i,
      (e.chartQuantization he φ ψ
        (a.map (Symbol.entryMap (bW.coord k).toContinuousLinearMap (bV i))) ∘ₗ
          t.cutoffFrameCoeff ρ (hρs.trans hE) (bV.coord i).toContinuousLinearMap).smulRight
        (t'.cutoffFrameSection ρ (hρs.trans hF) (bW k)) := by
    ext1 s
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply]
    exact sectionChartQuantization_eq_sum he t hE t' hF φ ψ a ρ (hρs.trans hE) (hρs.trans hF) hρ
      bV bW s
  rw [hsum, map_sum]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  -- The cut-off frame coefficients are linear over functions.
  have hc (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
      (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
      t.cutoffFrameCoeff ρ (hρs.trans hE) (bV.coord i).toContinuousLinearMap (f • s) =
        f * t.cutoffFrameCoeff ρ (hρs.trans hE) (bV.coord i).toContinuousLinearMap s := by
    ext y
    simp [mul_left_comm]
  rw [sectionEntry_smulRight t₂ ψ₂ hψ₂ v t₂' χ hχ ℓ _ hc]
  exact comp_mulLeft_mem_classicalPseudodifferentialOperators
    (mulLeft_comp_mem_classicalPseudodifferentialOperators
      (chartQuantization_mem_classicalPseudodifferentialOperators he φ ψ _) _) _

end Frame

/-! ### Localization -/

section Localization

variable {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

/-- **Localization.** Let `a` be the symbol of the compression of an operator `P` between the
bundles by cutoffs `φ` and `ψ` in the chart `e` and the frames `t`, `t'`: on Schwartz functions
`u : ℝⁿ → V`, `Op(a) u = φ · t' (P (t⁻¹ ((ψ u) ∘ e))) ∘ e⁻¹`. For cutoffs `φ₁` and `ψ₁` equal to
`1` on the supports of `φ` and `ψ`, the chart quantization of `a` localized by `φ₁` and `ψ₁` is
`s ↦ φ · P (ψ s)`, where `φ` and `ψ` are read on `M` through the chart and extended by `0`. -/
theorem sectionChartQuantization_eq_smul_comp {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}
    {a : ClassicalSymbol n V W m}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        φ y • t'.continuousLinearMapAt ℂ (e.symm y) (P (t.chartCutoffSection he hE ψ u) (e.symm y)))
    {φ₁ ψ₁ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hφ₁ : ∀ y ∈ tsupport φ, φ₁ y = 1)
    (hψ₁ : ∀ y ∈ tsupport ψ, ψ₁ y = 1) :
    e.sectionChartQuantization he t hE t' hF φ₁ ψ₁ a =
      e.complexCutoffPullback he φ 1 • (P ∘ₗ (e.complexCutoffPullback he ψ 1 • LinearMap.id)) := by
  ext s x
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
    ContMDiffSection.smul_apply_of_normedAlgebra]
  by_cases hx : x ∈ e.source
  swap
  · simp [sectionChartQuantization_apply_of_notMem he t hE t' hF _ _ a s hx,
      complexCutoffPullback_apply_of_notMem he _ _ hx]
  rw [sectionChartQuantization_apply_of_mem he t hE t' hF φ₁ ψ₁ a s hx, ha, e.left_inv hx,
    t.chartCutoffSection_cutoffPushforwardSchwartz he hE hψ₁, complexCutoffPullback_apply_of_mem
      he _ _ hx]
  by_cases hφ : φ (e x) = 0
  · simp [hφ, t'.symm_apply_zero ℂ (hF hx)]
  rw [hφ₁ _ (subset_tsupport _ hφ), one_smul, ← Complex.coe_smul, t'.symm_apply_smul (hF hx),
    ← t'.symmL_apply (R := ℂ) (hF hx), t'.symmL_continuousLinearMapAt (hF hx)]
  simp

/-- **Localized operators are chart quantizations.** Let `P` be a classical pseudodifferential
operator of order `m` between the bundles, and `φ`, `ψ` cutoffs in a chart `e` over whose source
both bundles are trivialized. Then `s ↦ φ · P (ψ s)`, with `φ` and `ψ` read on `M` through the
chart, is the chart quantization, localized by any cutoffs `φ₁` and `ψ₁` equal to `1` on the
supports of `φ` and `ψ`, of a classical symbol of order `m` with values in `V →L[ℂ] W`. -/
theorem exists_sectionChartQuantization_eq_smul_comp [FiniteDimensional ℂ V]
    [FiniteDimensional ℂ W] (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {φ₁ ψ₁ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}
    (hφ₁ : ∀ y ∈ tsupport φ, φ₁ y = 1) (hψ₁ : ∀ y ∈ tsupport ψ, ψ₁ y = 1) :
    ∃ a : ClassicalSymbol n V W m, e.sectionChartQuantization he t hE t' hF φ₁ ψ₁ a =
      e.complexCutoffPullback he φ 1 • (P ∘ₗ (e.complexCutoffPullback he ψ 1 • LinearMap.id)) :=
  let ⟨a, ha⟩ := exists_quantizeSchwartzValue_eq_apply_chartCutoffSection he t hE hP t' hF φ ψ
  ⟨a, sectionChartQuantization_eq_smul_comp he t hE t' hF ha hφ₁ hψ₁⟩

end Localization

end OpenPartialHomeomorph
