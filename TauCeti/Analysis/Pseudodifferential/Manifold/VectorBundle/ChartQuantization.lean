/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartQuantization
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Basic

/-!
# Quantizing a matrix-valued symbol in a chart and frames of vector bundles

Let `M` be a manifold modelled on `ℝⁿ`, let `E` and `F` be smooth complex vector bundles over `M`
with finite-dimensional model fibres `V` and `W`, let `e` be a chart of the maximal smooth atlas of
`M`, and let `t` and `t'` be trivializations of `E` and `F` in their atlases. For cutoffs `φ` and
`ψ` with compact supports in the chart target, such that `e⁻¹(supp ψ)` lies in the base set of `t`
and `e⁻¹(supp φ)` in that of `t'`, and a classical symbol `a` of order `m` with values in
`V →L[ℂ] W`, the **chart quantization** of `a` is the operator

`s ↦ (x ↦ t'⁻¹ₓ (φ(e x) · Op(a) (ψ · t(s ∘ e⁻¹)) (e x)))`

from the smooth sections of `E` to those of `F`, extended by `0` off the chart source
(`OpenPartialHomeomorph.sectionChartQuantization`). Here `ψ · t(s ∘ e⁻¹)` is the section `s` read
in the chart and the frame `t`, a compactly supported smooth function `ℝⁿ → V`
(`OpenPartialHomeomorph.sectionCutoffPushforwardSchwartz`), and `Op(a)` is the left quantization.
This is how a pseudodifferential operator between bundles is assembled from local data (Hörmander
III, §18.1; Taylor, Lecture I, §8): it is the bundle version of the scalar chart quantization
`OpenPartialHomeomorph.chartQuantization`. The two trivializations are only used near
`e⁻¹(supp ψ)` and `e⁻¹(supp φ)`, which need not lie in a common base set; on the charts of the
maximal atlas whose domain has two components these may be far apart.

The main result is that a chart quantization is a classical pseudodifferential operator of order
`m` between bundles (`TauCeti.sectionClassicalPseudodifferentialOperators`), the class defined by
the scalar entries `f ↦ χ ℓ(T' (P (f ψ' T⁻¹ v)))` in all cut-off frames
(`OpenPartialHomeomorph.sectionChartQuantization_mem_sectionClassicalPseudodifferentialOperators`).
The proof writes it in bases `(bᵢ)` of `V` and `(cⱼ)` of `W` as the finite sum

`∑ᵢ ∑ⱼ Op_e(cⱼ* ∘ a ∘ bᵢ) (ρ bᵢ*(t s)) · ρ' t'⁻¹ cⱼ`

of scalar chart quantizations of the entries of `a`, applied to cut-off frame coefficients of `s`
and multiplied by cut-off frame sections of `F`, for real cutoffs `ρ` and `ρ'` equal to `1` on
`e⁻¹(supp ψ)` and `e⁻¹(supp φ)` (`OpenPartialHomeomorph.sectionChartQuantization_eq_sum`). Each
term is a scalar classical pseudodifferential operator tensored with frame data, and such an
operator `s ↦ A (ρ ℓ(t s)) σ` is a classical pseudodifferential operator between bundles, since
its entries are `A` multiplied on both sides by smooth functions
(`toSpanSingleton_comp_comp_cutoffFrameCoeff_mem_sectionClassicalPseudodifferentialOperators`).

Conversely, localizing a classical pseudodifferential operator `P` between bundles in a chart over
whose source both bundles are trivialized gives a chart quantization: if `a` is the symbol of the
compression of `P` by `φ` and `ψ`
(`TauCeti.exists_quantizeSchwartzValue_eq_apply_chartCutoffSection`), then the chart quantization
of `a`, localized by cutoffs equal to `1` on the supports of `φ` and `ψ`, is
`s ↦ (φ ∘ e) · P ((ψ ∘ e) · s)`
(`OpenPartialHomeomorph.sectionChartQuantization_eq_smul_comp_comp_smul`,
`OpenPartialHomeomorph.exists_sectionChartQuantization_eq_smul_comp_comp_smul`).

## Main definitions

* `OpenPartialHomeomorph.sectionCutoffPushforwardSchwartz`: a section `s` of `E` read in a chart
  and a frame, as the Schwartz function `y ↦ ψ(y) t(s(e⁻¹ y))`.
* `OpenPartialHomeomorph.sectionChartQuantization`: the chart quantization of a symbol with values
  in `V →L[ℂ] W`, from the sections of `E` to those of `F`.

## Main results

* `OpenPartialHomeomorph.isSectionProperlySupported_sectionChartQuantization`: the chart
  quantization is properly supported.
* `OpenPartialHomeomorph.sectionChartQuantization_eq_sum`: the chart quantization as a sum of
  scalar chart quantizations of the entries of the symbol.
* `OpenPartialHomeomorph.sectionChartQuantization_mem_sectionClassicalPseudodifferentialOperators`:
  a chart quantization of a classical symbol of order `m` is a classical pseudodifferential
  operator of order `m` between bundles.
* `OpenPartialHomeomorph.sectionChartQuantization_eq_smul_comp_comp_smul`: localization, the chart
  quantization of the symbol of a chart compression of `P` by `φ` and `ψ` is `(φ ∘ e) P (ψ ∘ e)`.

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

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {m : ℝ}

namespace OpenPartialHomeomorph

omit [ChartedSpace (CoordinateSpace n) M] [T2Space M] in
/-- At a point `x` of the source of `e` with `φ (e x) ≠ 0`, a function `ρ` equal to `1` on
`e⁻¹(supp φ)` takes the value `1`, and `x` lies in every set containing `e⁻¹(supp φ)`. -/
private theorem eq_one_and_mem_of_apply_ne_zero {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    {φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {U : Set M} (hφ : e.symm '' tsupport φ ⊆ U)
    {ρ : M → ℝ} (hρφ : ∀ y ∈ tsupport φ, ρ (e.symm y) = 1) {x : M} (hx : x ∈ e.source)
    (hφx : φ (e x) ≠ 0) : ρ x = 1 ∧ x ∈ U := by
  have hxφ : e x ∈ tsupport φ := subset_tsupport _ hφx
  exact ⟨by simpa [e.left_inv hx] using hρφ (e x) hxφ, hφ ⟨e x, hxφ, e.left_inv hx⟩⟩

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)

include he

variable (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
  (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']

/-! ### Reading a section in a chart and a frame -/

section Reading

omit [T2Space M] in
/-- The frame coefficients of a section read in a chart and a frame are the readings of its cut-off
frame coefficients, for a cutoff `ρ` equal to `1` on `e⁻¹(supp ψ)`. -/
private theorem apply_smul_continuousLinearMapAt_eq (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    {ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯} (hρ : tsupport ρ ⊆ t.baseSet)
    (hρψ : ∀ y ∈ tsupport ψ, ρ (e.symm y) = 1) (ℓ : V →L[ℂ] ℂ)
    (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) (y : CoordinateSpace n) :
    ℓ (ψ y • t.continuousLinearMapAt ℂ (e.symm y) (s (e.symm y))) =
      e.cutoffPushforwardSchwartz he ψ (t.cutoffFrameCoeff ρ hρ ℓ s) y := by
  rw [cutoffPushforwardSchwartz_apply, Trivialization.cutoffFrameCoeff_apply]
  by_cases hy : ψ y = 0
  · simp [hy]
  · simp [hρψ y (subset_tsupport _ hy)]

/-- The reading `y ↦ ψ(y) t(s(e⁻¹ y))` of a section is smooth: in a basis of `V`, its coordinates
are the readings of cut-off frame coefficients of `s`. -/
private theorem contDiff_smul_continuousLinearMapAt [FiniteDimensional ℂ V]
    (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (hψ : e.symm '' tsupport ψ ⊆ t.baseSet)
    (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    ContDiff ℝ ∞ fun y ↦ ψ y • t.continuousLinearMapAt ℂ (e.symm y) (s (e.symm y)) := by
  obtain ⟨ρ, hρ, hρψ⟩ := e.exists_tsupport_subset_eq_one he ψ t.open_baseSet hψ
  set b := Module.finBasis ℂ V
  have h : (fun y ↦ ψ y • t.continuousLinearMapAt ℂ (e.symm y) (s (e.symm y))) = fun y ↦
      ∑ i, e.cutoffPushforwardSchwartz he ψ
        (t.cutoffFrameCoeff ρ hρ (b.coord i).toContinuousLinearMap s) y • b i := by
    funext y
    simp_rw [← apply_smul_continuousLinearMapAt_eq he t ψ hρ hρψ]
    exact (b.sum_repr _).symm
  rw [h]
  exact ContDiff.sum fun i _ ↦ (SchwartzMap.smooth _ ⊤).smul contDiff_const

/-- **Reading a section in a chart and a frame.** For a trivialization `t` of `E` in its atlas and
a cutoff `ψ` with compact support in the target of the chart `e` such that `e⁻¹(supp ψ)` lies in the
base set of `t`, the compactly supported smooth function `y ↦ ψ(y) t(s(e⁻¹ y))` on `ℝⁿ`, as a
Schwartz function, complex-linear in the section `s` of `E`. -/
def sectionCutoffPushforwardSchwartz [FiniteDimensional ℂ V] (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (hψ : e.symm '' tsupport ψ ⊆ t.baseSet) :
    Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] 𝓢(CoordinateSpace n, V) where
  toFun s := HasCompactSupport.toSchwartzMap
    (f := fun y ↦ ψ y • t.continuousLinearMapAt ℂ (e.symm y) (s (e.symm y)))
    ψ.hasCompactSupport.smul_right (contDiff_smul_continuousLinearMapAt he t ψ hψ s)
  map_add' s s' := by
    ext y
    simp [smul_add]
  map_smul' c s := by
    ext y
    simp [smul_comm (ψ y) c]

@[simp]
theorem sectionCutoffPushforwardSchwartz_apply [FiniteDimensional ℂ V]
    (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (hψ : e.symm '' tsupport ψ ⊆ t.baseSet)
    (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) (y : CoordinateSpace n) :
    e.sectionCutoffPushforwardSchwartz he t ψ hψ s y =
      ψ y • t.continuousLinearMapAt ℂ (e.symm y) (s (e.symm y)) :=
  (rfl)

/-- **Coordinates of the reading of a section.** For a cutoff `ρ` on `M`, supported in the base set
of `t` and equal to `1` on `e⁻¹(supp ψ)`, the composition of the reading of `s` with a functional
`ℓ` on `V` is the reading in the chart of the cut-off frame coefficient `ρ ℓ(t s)`. -/
theorem postcompCLM_sectionCutoffPushforwardSchwartz [FiniteDimensional ℂ V]
    (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (hψ : e.symm '' tsupport ψ ⊆ t.baseSet)
    {ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯} (hρ : tsupport ρ ⊆ t.baseSet)
    (hρψ : ∀ y ∈ tsupport ψ, ρ (e.symm y) = 1) (ℓ : V →L[ℂ] ℂ)
    (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    (e.sectionCutoffPushforwardSchwartz he t ψ hψ s).postcompCLM ℓ =
      e.cutoffPushforwardSchwartz he ψ (t.cutoffFrameCoeff ρ hρ ℓ s) := by
  ext y
  rw [SchwartzMap.postcompCLM_apply, sectionCutoffPushforwardSchwartz_apply,
    apply_smul_continuousLinearMapAt_eq he t ψ hρ hρψ]

end Reading

/-! ### The chart quantization -/

section Quantization

/-- The section `x ↦ t'⁻¹ₓ (φ(e x) g(e x))` of `F`, extended by `0` off the chart source, is smooth
for every smooth `g : ℝⁿ → W`: in a basis of `W`, it is a sum of cut-off frame sections with
smooth coefficients. -/
private theorem contMDiff_symmL_cutoffPullback_smul [FiniteDimensional ℂ W]
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (hφ : e.symm '' tsupport φ ⊆ t'.baseSet)
    {g : CoordinateSpace n → W} (hg : ContDiff ℝ ∞ g) :
    ContMDiff 𝓘(ℝ, CoordinateSpace n) (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, W)) ∞ fun x ↦
      TotalSpace.mk' W x (t'.symmL ℂ x (e.cutoffPullback he φ 1 x • g (e x))) := by
  obtain ⟨ρ, hρ, hρφ⟩ := e.exists_tsupport_subset_eq_one he φ t'.open_baseSet hφ
  set b := Module.finBasis ℂ W
  set S := ∑ j, e.complexCutoffPullback he φ (ContMDiffMap.ofContDiff (fun y ↦ b.coord j (g y))
      (((b.coord j).toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hg)) •
    t'.cutoffFrameSection ρ hρ (b j)
  have h (x : M) : t'.symmL ℂ x (e.cutoffPullback he φ 1 x • g (e x)) = S x := by
    rw [ContMDiffSection.coe_sum, Finset.sum_apply]
    by_cases hx : x ∈ e.source
    · simp only [ContMDiffSection.smul_apply_of_normedAlgebra,
        e.complexCutoffPullback_apply_of_mem he _ _ hx,
        Trivialization.cutoffFrameSection_apply, e.cutoffPullback_one_apply_of_mem he _ hx]
      by_cases hφx : φ (e x) = 0
      · simp [hφx]
      obtain ⟨hρx, hxt⟩ := eq_one_and_mem_of_apply_ne_zero hφ hρφ hx hφx
      simp only [hρx, one_smul, ← t'.symmL_apply (R := ℂ) hxt, ← map_smul, ← map_sum]
      congr 1
      conv_lhs => rw [← b.sum_repr (g (e x)), Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [← smul_assoc, Complex.real_smul]
    · simp [e.cutoffPullback_apply_of_notMem he _ _ hx,
        e.complexCutoffPullback_apply_of_notMem he _ _ hx]
  simp_rw [h]
  exact S.contMDiff

/-- The **quantization of a symbol `a` with values in `V →L[ℂ] W` in the chart `e` and the frames
`t` of `E` and `t'` of `F`**, localized by cutoffs `φ` and `ψ` with compact supports in the chart
target such that `e⁻¹(supp φ)` lies in the base set of `t'` and `e⁻¹(supp ψ)` in that of `t`: the
operator

`s ↦ (x ↦ t'⁻¹ₓ (φ(e x) · Op(a) (ψ · t(s ∘ e⁻¹)) (e x)))`

from the smooth sections of `E` to those of `F`, extended by `0` off the chart source. Here `Op(a)`
is the left quantization of `a` on Schwartz functions. -/
def sectionChartQuantization [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (hφ : e.symm '' tsupport φ ⊆ t'.baseSet)
    (hψ : e.symm '' tsupport ψ ⊆ t.baseSet) (a : ClassicalSymbol n V W m) :
    Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ where
  toFun s := ⟨fun x ↦ t'.symmL ℂ x (e.cutoffPullback he φ 1 x •
      quantizeSchwartzValue a.toSymbol.coefficient (e.sectionCutoffPushforwardSchwartz he t ψ hψ s)
        (e x)),
    contMDiff_symmL_cutoffPullback_smul he t' φ hφ (a.toSymbol.contDiff_quantizeSchwartzValue _)⟩
  map_add' s s' := by
    ext x
    obtain ⟨C, -, hC⟩ := a.toSymbol.exists_bound_coefficient_slice (e x)
    simp [quantizeSchwartzValue_add_right
      (a.toSymbol.continuous_coefficient_slice (e x)).aestronglyMeasurable hC, smul_add]
  map_smul' c s := by
    ext x
    simp [quantizeSchwartzValue_smul_right, smul_comm (e.cutoffPullback he φ 1 x) c]

end Quantization

section Basic

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
  (hφ : e.symm '' tsupport φ ⊆ t'.baseSet) (hψ : e.symm '' tsupport ψ ⊆ t.baseSet)
  (a : ClassicalSymbol n V W m)

/-- The chart quantization of `a` at `x` is `t'⁻¹ₓ (φ(e x) · Op(a) v (e x))`, with `φ ∘ e` extended
by `0` off the chart source, for the reading `v = ψ · t(s ∘ e⁻¹)` of the section `s`. -/
theorem sectionChartQuantization_apply (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) (x : M) :
    e.sectionChartQuantization he t t' φ ψ hφ hψ a s x =
      t'.symmL ℂ x (e.cutoffPullback he φ 1 x • quantizeSchwartzValue a.toSymbol.coefficient
        (e.sectionCutoffPushforwardSchwartz he t ψ hψ s) (e x)) :=
  (rfl)

/-- On the chart source, the chart quantization of `a` is `t'⁻¹ (φ · Op(a) v)` read through the
chart, for the reading `v = ψ · t(s ∘ e⁻¹)` of the section `s`. -/
theorem sectionChartQuantization_apply_of_mem (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) {x : M}
    (hx : x ∈ e.source) :
    e.sectionChartQuantization he t t' φ ψ hφ hψ a s x =
      t'.symmL ℂ x (φ (e x) • quantizeSchwartzValue a.toSymbol.coefficient
        (e.sectionCutoffPushforwardSchwartz he t ψ hψ s) (e x)) := by
  rw [sectionChartQuantization_apply, e.cutoffPullback_one_apply_of_mem he _ hx]

/-- Off the chart source, the chart quantization vanishes. -/
theorem sectionChartQuantization_apply_of_notMem (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯)
    {x : M} (hx : x ∉ e.source) : e.sectionChartQuantization he t t' φ ψ hφ hψ a s x = 0 := by
  rw [sectionChartQuantization_apply, e.cutoffPullback_apply_of_notMem he _ _ hx, zero_smul,
    map_zero]

/-- The chart quantization is supported in the image of the support of `φ` under the inverse of
the chart. -/
theorem tsupport_sectionChartQuantization_subset (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    (e.sectionChartQuantization he t t' φ ψ hφ hψ a s).tsupport ⊆ e.symm '' tsupport φ := by
  refine (ContMDiffSection.tsupport_subset_iff
    (e.isCompact_symm_image_tsupport φ).isClosed).2 fun x hx ↦ ?_
  rw [sectionChartQuantization_apply, image_eq_zero_of_notMem_tsupport
    (f := e.cutoffPullback he φ 1) (by rwa [tsupport_cutoffPullback_one]), zero_smul, map_zero]

/-- The chart quantization only sees its input on the image of the support of `ψ` under the
inverse of the chart: it vanishes on every section vanishing there. -/
theorem sectionChartQuantization_eq_zero {s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯}
    (hs : ∀ p ∈ e.symm '' tsupport ψ, s p = 0) :
    e.sectionChartQuantization he t t' φ ψ hφ hψ a s = 0 := by
  have hv : e.sectionCutoffPushforwardSchwartz he t ψ hψ s = 0 := by
    ext y
    rw [sectionCutoffPushforwardSchwartz_apply, zero_apply]
    by_cases hy : y ∈ tsupport ψ
    · rw [hs _ (mem_image_of_mem _ hy), map_zero, smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  ext x
  rw [sectionChartQuantization_apply, hv, quantizeSchwartzValue_zero_right, smul_zero, map_zero,
    ContMDiffSection.coe_zero, Pi.zero_apply]

/-- **Chart quantizations between bundles are properly supported.** For every compact set, one may
take `K' = e⁻¹(supp φ) ∪ e⁻¹(supp ψ)`: the output is always supported in `e⁻¹(supp φ)`, and it
vanishes when the input vanishes near `e⁻¹(supp ψ)`. -/
theorem isSectionProperlySupported_sectionChartQuantization :
    IsSectionProperlySupported (e.sectionChartQuantization he t t' φ ψ hφ hψ a) :=
  isSectionProperlySupported_iff.2 fun _ _ ↦ ⟨e.symm '' tsupport φ ∪ e.symm '' tsupport ψ,
    (e.isCompact_symm_image_tsupport φ).union (e.isCompact_symm_image_tsupport ψ),
    fun s _ ↦ (tsupport_sectionChartQuantization_subset he t t' φ ψ hφ hψ a s).trans
      subset_union_left,
    fun s hs p _ ↦ by
      rw [sectionChartQuantization_eq_zero he t t' φ ψ hφ hψ a fun q hq ↦
        (hs.filter_mono (nhdsSet_mono subset_union_right)).self_of_nhdsSet q hq,
        ContMDiffSection.coe_zero, Pi.zero_apply]⟩

/-- **The chart quantization in bases.** Let `(bᵢ)` be a basis of `V` and `(cⱼ)` a basis of `W`,
and let `ρ` and `ρ'` be real smooth functions on `M`, supported in the base sets of `t` and `t'`
and equal to `1` on `e⁻¹(supp ψ)` and `e⁻¹(supp φ)`. Then the chart quantization of `a` is the sum
over `i` and `j` of the scalar chart quantizations of the entries `cⱼ* ∘ a ∘ bᵢ` of `a`, applied
to the cut-off frame coefficients `ρ bᵢ*(t s)` and multiplied by the cut-off frame sections
`ρ' t'⁻¹ cⱼ`. -/
theorem sectionChartQuantization_eq_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (bV : Module.Basis ι ℂ V) (bW : Module.Basis κ ℂ W)
    {ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯} (hρ : tsupport ρ ⊆ t.baseSet)
    (hρψ : ∀ y ∈ tsupport ψ, ρ (e.symm y) = 1)
    {ρ' : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯} (hρ' : tsupport ρ' ⊆ t'.baseSet)
    (hρ'φ : ∀ y ∈ tsupport φ, ρ' (e.symm y) = 1) :
    e.sectionChartQuantization he t t' φ ψ hφ hψ a = ∑ i, ∑ j,
      (LinearMap.toSpanSingleton _ _ (t'.cutoffFrameSection ρ' hρ' (bW j))).restrictScalars ℂ ∘ₗ
        e.chartQuantization he φ ψ
          (a.map (Symbol.entryMap (bW.coord j).toContinuousLinearMap (bV i))) ∘ₗ
          t.cutoffFrameCoeff ρ hρ (bV.coord i).toContinuousLinearMap := by
  ext s x
  simp only [LinearMap.sum_apply, ContMDiffSection.coe_sum, Finset.sum_apply,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply,
    ContMDiffSection.smul_apply_of_normedAlgebra, Trivialization.cutoffFrameSection_apply]
  by_cases hx : x ∈ e.source
  · simp only [sectionChartQuantization_apply_of_mem he t t' φ ψ hφ hψ a s hx,
      e.chartQuantization_apply_of_mem he φ ψ _ _ (cutoffPushforwardSchwartz_apply he ψ _) hx]
    by_cases hφx : φ (e x) = 0
    · simp [hφx]
    obtain ⟨hρx, hxt⟩ := eq_one_and_mem_of_apply_ne_zero hφ hρ'φ hx hφx
    -- Expand `Op(a) v` in the basis `(cⱼ)`, and each coordinate in the entries of `a`.
    have key : quantizeSchwartzValue a.toSymbol.coefficient
        (e.sectionCutoffPushforwardSchwartz he t ψ hψ s) (e x) = ∑ j, (∑ i,
          quantizeSchwartzValue
            (a.map (Symbol.entryMap (bW.coord j).toContinuousLinearMap (bV i))).toSymbol.coefficient
            (e.cutoffPushforwardSchwartz he ψ
              (t.cutoffFrameCoeff ρ hρ (bV.coord i).toContinuousLinearMap s)) (e x)) • bW j := by
      conv_lhs => rw [← bW.sum_repr (quantizeSchwartzValue a.toSymbol.coefficient _ (e x))]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Module.Basis.coord_apply, ← LinearMap.coe_toContinuousLinearMap',
        Symbol.apply_quantizeSchwartzValue_eq_sum a.toSymbol bV]
      simp_rw [postcompCLM_sectionCutoffPushforwardSchwartz he t ψ hψ hρ hρψ,
        ClassicalSymbol.toSymbol_map]
    simp only [hρx, one_smul, ← t'.symmL_apply (R := ℂ) hxt]
    rw [key, Finset.smul_sum, map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← smul_assoc, map_smul, Finset.smul_sum, Finset.sum_smul]
  · simp [sectionChartQuantization_apply_of_notMem he t t' φ ψ hφ hψ a s hx,
      e.chartQuantization_apply_of_notMem he φ ψ _ _ hx]

/-- **Chart quantizations are classical pseudodifferential operators between bundles.** The
quantization of a classical symbol of order `m` with values in `V →L[ℂ] W` in a chart of the
maximal atlas and frames of `E` and `F`, localized by cutoffs with compact supports in the chart
target, is a classical pseudodifferential operator of order `m` from the sections of `E` to those
of `F`. -/
theorem sectionChartQuantization_mem_sectionClassicalPseudodifferentialOperators :
    e.sectionChartQuantization he t t' φ ψ hφ hψ a ∈
      sectionClassicalPseudodifferentialOperators m := by
  obtain ⟨ρ, hρ, hρψ⟩ := e.exists_tsupport_subset_eq_one he ψ t.open_baseSet hψ
  obtain ⟨ρ', hρ', hρ'φ⟩ := e.exists_tsupport_subset_eq_one he φ t'.open_baseSet hφ
  rw [sectionChartQuantization_eq_sum he t t' φ ψ hφ hψ a (Module.finBasis ℂ V)
    (Module.finBasis ℂ W) hρ hρψ hρ' hρ'φ]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
    toSpanSingleton_comp_comp_cutoffFrameCoeff_mem_sectionClassicalPseudodifferentialOperators
      (e.chartQuantization_mem_classicalPseudodifferentialOperators he φ ψ _) t ρ hρ _ _

end Basic

/-! ### Localization -/

section Localization

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (hE : e.source ⊆ t.baseSet)
  (hF : e.source ⊆ t'.baseSet)
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

include hE hF

/-- **Localization.** Let `e` be a chart whose source lies in the base sets of `t` and `t'`, and
let `a` be the symbol of the compression `u ↦ φ · t' (P (t⁻¹ ((ψ u) ∘ e))) ∘ e⁻¹` of an operator
`P` from the sections of `E` to those of `F`. For cutoffs `φ₁` and `ψ₁` equal to `1` on the
supports of `φ` and `ψ`, the chart quantization of `a` localized by `φ₁` and `ψ₁` is
`s ↦ (φ ∘ e) · P ((ψ ∘ e) · s)`, where `φ` and `ψ` are read on `M` through the chart and extended
by `0`. -/
theorem sectionChartQuantization_eq_smul_comp_comp_smul {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}
    {a : ClassicalSymbol n V W m}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        φ y • t'.continuousLinearMapAt ℂ (e.symm y)
          (P (t.chartCutoffSection he hE ψ u) (e.symm y)))
    {φ₁ ψ₁ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hφ₁ : ∀ y ∈ tsupport φ, φ₁ y = 1)
    (hψ₁ : ∀ y ∈ tsupport ψ, ψ₁ y = 1) :
    e.sectionChartQuantization he t t' φ₁ ψ₁
        ((e.symm_image_tsupport_subset_source φ₁).trans hF)
        ((e.symm_image_tsupport_subset_source ψ₁).trans hE) a =
      e.complexCutoffPullback he φ 1 • (P ∘ₗ (e.complexCutoffPullback he ψ 1 • LinearMap.id)) := by
  -- The chart cut-off section of the reading of `s` by `ψ₁`, cut off by `ψ`, is `(ψ ∘ e) s`.
  have hsec (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
      t.chartCutoffSection he hE ψ (e.sectionCutoffPushforwardSchwartz he t ψ₁
        ((e.symm_image_tsupport_subset_source ψ₁).trans hE) s) =
        e.complexCutoffPullback he ψ 1 • s := by
    ext y
    rw [ContMDiffSection.smul_apply_of_normedAlgebra]
    by_cases hy : y ∈ e.source
    · rw [t.chartCutoffSection_apply_of_mem he hE _ _ hy, sectionCutoffPushforwardSchwartz_apply,
        e.left_inv hy, e.complexCutoffPullback_apply_of_mem he _ _ hy]
      by_cases hψy : ψ (e y) = 0
      · simp [hψy, ← t.symmL_apply (R := ℂ) (hE hy)]
      · rw [hψ₁ _ (subset_tsupport _ hψy), one_smul, ← t.symmL_apply (R := ℂ) (hE hy),
          ← Complex.coe_smul, map_smul, t.symmL_continuousLinearMapAt (hE hy)]
        simp [Complex.real_smul]
    · simp [t.chartCutoffSection_apply_of_notMem he hE _ _ hy,
        e.complexCutoffPullback_apply_of_notMem he _ _ hy]
  ext s x
  rw [LinearMap.smul_apply, ContMDiffSection.smul_apply_of_normedAlgebra, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply]
  by_cases hx : x ∈ e.source
  · rw [sectionChartQuantization_apply_of_mem he t t' _ _ _ _ a s hx, ha, e.left_inv hx, hsec,
      e.complexCutoffPullback_apply_of_mem he _ _ hx]
    by_cases hφx : φ (e x) = 0
    · simp [hφx]
    · rw [hφ₁ _ (subset_tsupport _ hφx), one_smul, ← Complex.coe_smul, map_smul,
        t'.symmL_continuousLinearMapAt (hF hx)]
      simp [Complex.real_smul]
  · simp [sectionChartQuantization_apply_of_notMem he t t' _ _ _ _ a s hx,
      e.complexCutoffPullback_apply_of_notMem he _ _ hx]

/-- **Localized operators between bundles are chart quantizations.** Let `P` be a classical
pseudodifferential operator of order `m` from the sections of `E` to those of `F`, and `e` a chart
whose source lies in the base sets of `t` and `t'`. For cutoffs `φ` and `ψ` with compact supports in
the chart target, the operator `s ↦ (φ ∘ e) · P ((ψ ∘ e) · s)`, with `φ` and `ψ` read on `M`
through the chart and extended by `0`, is the chart quantization of a classical symbol of order `m`
with values in `V →L[ℂ] W`. -/
theorem exists_sectionChartQuantization_eq_smul_comp_comp_smul
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    ∃ (φ₁ ψ₁ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n V W m),
      e.sectionChartQuantization he t t' φ₁ ψ₁
          ((e.symm_image_tsupport_subset_source φ₁).trans hF)
          ((e.symm_image_tsupport_subset_source ψ₁).trans hE) a =
        e.complexCutoffPullback he φ 1 •
          (P ∘ₗ (e.complexCutoffPullback he ψ 1 • LinearMap.id)) := by
  obtain ⟨a, ha⟩ := exists_quantizeSchwartzValue_eq_apply_chartCutoffSection he t hE hP t' hF φ ψ
  obtain ⟨φ₁, hφ₁, -⟩ := TestFunction.exists_eventually_eq_one (Ω := ⟨e.target, e.open_target⟩)
    (n := ⊤) φ.hasCompactSupport.isCompact φ.tsupport_subset
  obtain ⟨ψ₁, hψ₁, -⟩ := TestFunction.exists_eventually_eq_one (Ω := ⟨e.target, e.open_target⟩)
    (n := ⊤) ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  exact ⟨φ₁, ψ₁, a, sectionChartQuantization_eq_smul_comp_comp_smul he t t' hE hF ha
    (fun y hy ↦ hφ₁.self_of_nhdsSet y hy) fun y hy ↦ hψ₁.self_of_nhdsSet y hy⟩

end Localization

end OpenPartialHomeomorph
