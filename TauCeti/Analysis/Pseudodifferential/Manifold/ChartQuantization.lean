/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.CoordinateChange.Chart
public import TauCeti.Analysis.Pseudodifferential.Manifold.Basic
import TauCeti.Algebra.GroupWithZero.Indicator
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Quantizing a symbol in a chart of a manifold

Let `M` be a manifold modelled on `ℝⁿ`, `e` a chart of its maximal smooth atlas, `φ` and `ψ` cutoffs
with compact supports in the chart target and `a` a classical symbol of order `m` on `ℝⁿ`. The
**chart quantization** of `a` is the operator

`u ↦ (φ · Op(a) (ψ · (u ∘ e⁻¹))) ∘ e`

on the complex-valued smooth functions on `M`, extended by `0` off the chart source
(`OpenPartialHomeomorph.chartQuantization`). This is how a pseudodifferential operator on `M` is
assembled from local data: for a finite atlas `eᵢ` with cutoffs `φᵢ`, `ψᵢ` and local symbols `aᵢ`,
the patched operator is `∑ᵢ Op_{eᵢ}(aᵢ)`.

The main result is that a chart quantization is a classical pseudodifferential operator of order
`m` in the sense of `TauCeti.classicalPseudodifferentialOperators`, defined by its compressions to
every chart of the maximal atlas
(`OpenPartialHomeomorph.chartQuantization_mem_classicalPseudodifferentialOperators`). Since these
operators form a submodule, so are the finite sums `∑ᵢ Op_{eᵢ}(aᵢ)`.

The compression of the chart quantization in a second chart `e'`, by cutoffs `φ'` and `ψ'`, is the
operator `u ↦ Φ · Op(a) ((Ψ u) ∘ κ⁻¹) ∘ κ` for the transition map `κ = e ∘ e'⁻¹` and the cutoffs
`Φ = φ' · (φ ∘ κ)` and `Ψ = ψ' · (ψ ∘ κ)` on the chart overlap. By the change of coordinates
theorem between open sets (`TauCeti.ClassicalSymbol.exists_smul_quantizeSchwartzValue_comp_eq`) it
is `Op(b)` for a classical symbol `b` of order `m` whose principal symbol is

`σ(b)(x, ξ) = φ'(x) φ(κ x) ψ'(x) ψ(κ x) σ(a)(κ x, (Dκ(x)*)⁻¹ ξ)`

on the overlap and vanishes off it
(`OpenPartialHomeomorph.exists_complexChartCompression_chartQuantization_eq`).

## Main definitions

* `OpenPartialHomeomorph.chartQuantization`: the quantization `Op_e(a)` of a classical symbol `a`
  in a chart `e`, localized by cutoffs `φ` and `ψ`.
* `OpenPartialHomeomorph.cutoffPushforwardSchwartz`: a function `u` on `M` read in the chart `e`
  through a cutoff `ψ`, as the Schwartz function `ψ · (u ∘ e⁻¹)` on `ℝⁿ`.
* `OpenPartialHomeomorph.overlapCutoff`: the product `φ' · (φ ∘ e ∘ e'⁻¹)` of cutoffs in two charts,
  read in the chart `e'`; it is smooth with compact support in the source of the transition map
  (`OpenPartialHomeomorph.overlapCutoff_spec`).

## Main results

* `OpenPartialHomeomorph.isProperlySupported_chartQuantization`: a chart quantization is properly
  supported.
* `OpenPartialHomeomorph.chartQuantization_eq_mulLeft_comp_comp_mulLeft`: localization, the chart
  quantization of the symbol of a chart compression of `P` by `φ` and `ψ` is `φ P ψ`, with the
  cutoffs read on `M`.
* `OpenPartialHomeomorph.exists_complexChartCompression_chartQuantization_eq`: the compression of a
  chart quantization in any chart is the quantization of a classical symbol of the same order, with
  principal symbol transformed by the cotangent map of the transition map.
* `OpenPartialHomeomorph.chartQuantization_mem_classicalPseudodifferentialOperators`: a chart
  quantization of a classical symbol of order `m` is a classical pseudodifferential operator of
  order `m`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.17
  and Definition 18.1.20.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
-/

public section

noncomputable section

open Set Filter TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M) {m : ℝ}

include he

/-! ### The chart quantization -/

/-- **Reading a function in a chart.** The compactly supported smooth function `ψ · (u ∘ e⁻¹)` on
`ℝⁿ`, as a Schwartz function, complex-linear in the function `u` on `M`. -/
def cutoffPushforwardSchwartz (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] 𝓢(CoordinateSpace n, ℂ) where
  toFun u := HasCompactSupport.toSchwartzMap (f := e.complexCutoffPushforward he ψ u)
    (by
      have h : ⇑(e.complexCutoffPushforward he ψ u) = fun y ↦ ψ y • u (e.symm y) :=
        funext (e.complexCutoffPushforward_apply he ψ u)
      rw [h]
      exact ψ.hasCompactSupport.smul_right)
    (contMDiff_iff_contDiff.1 (e.complexCutoffPushforward he ψ u).contMDiff)
  map_add' u v := by
    ext y
    simp
  map_smul' c u := by
    ext y
    simp

omit [T2Space M] in
@[simp]
theorem cutoffPushforwardSchwartz_apply (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (y : CoordinateSpace n) :
    cutoffPushforwardSchwartz he ψ u y = ψ y • u (e.symm y) :=
  e.complexCutoffPushforward_apply he ψ u y

/-- The **quantization of a classical symbol `a` in the chart `e`**, localized by cutoffs `φ` and
`ψ` with compact supports in the chart target: the operator
`u ↦ (φ · Op(a) (ψ · (u ∘ e⁻¹))) ∘ e` on the complex-valued smooth functions on `M`, extended by
`0` off the chart source. Here `Op(a)` is the left quantization of `a` on Schwartz functions. -/
def chartQuantization (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n ℂ ℂ m) :
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun u := e.complexCutoffPullback he φ (ContMDiffMap.ofContDiff
    (quantizeSchwartzValue a.toSymbol.coefficient (cutoffPushforwardSchwartz he ψ u))
    (a.toSymbol.contDiff_quantizeSchwartzValue _))
  map_add' u u' := by
    rw [← map_add]
    congr 1
    ext x
    obtain ⟨C, -, hC⟩ := a.toSymbol.exists_bound_coefficient_slice x
    rw [ContMDiffMap.coe_add, Pi.add_apply, ContMDiffMap.coe_ofContDiff,
      ContMDiffMap.coe_ofContDiff, ContMDiffMap.coe_ofContDiff,
      ← quantizeSchwartzValue_add_right
        (a.toSymbol.continuous_coefficient_slice x).aestronglyMeasurable hC]
    rw [map_add]
  map_smul' c u := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    ext x
    rw [ContMDiffMap.complex_smul_apply, ContMDiffMap.coe_ofContDiff, ContMDiffMap.coe_ofContDiff,
      ← smul_eq_mul, ← quantizeSchwartzValue_smul_right]
    rw [map_smul]

/-- On the chart source, the chart quantization of `a` is `φ · Op(a) v` read through the chart,
for the Schwartz function `v = ψ · (u ∘ e⁻¹)`. -/
theorem chartQuantization_apply_of_mem (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n ℂ ℂ m) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
    {v : 𝓢(CoordinateSpace n, ℂ)} (hv : ∀ y, v y = ψ y • u (e.symm y)) {p : M}
    (hp : p ∈ e.source) :
    e.chartQuantization he φ ψ a u p =
      φ (e p) • quantizeSchwartzValue a.toSymbol.coefficient v (e p) := by
  have hv' : cutoffPushforwardSchwartz he ψ u = v :=
    SchwartzMap.ext fun y ↦ by rw [cutoffPushforwardSchwartz_apply, hv]
  simp only [chartQuantization, LinearMap.coe_mk, AddHom.coe_mk,
    complexCutoffPullback_apply_of_mem he _ _ hp, ContMDiffMap.coe_ofContDiff, hv']

/-- Off the chart source, the chart quantization vanishes. -/
theorem chartQuantization_apply_of_notMem (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n ℂ ℂ m) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) {p : M}
    (hp : p ∉ e.source) : e.chartQuantization he φ ψ a u p = 0 :=
  complexCutoffPullback_apply_of_notMem he _ _ hp

/-- The chart quantization is supported in the image of the support of `φ` under the inverse of
the chart. -/
theorem tsupport_chartQuantization_subset (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n ℂ ℂ m) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    tsupport (e.chartQuantization he φ ψ a u) ⊆ e.symm '' tsupport φ :=
  tsupport_complexCutoffPullback_subset he φ _

/-- The chart quantization only sees its input on the image of the support of `ψ` under the
inverse of the chart: it vanishes on every input vanishing there. -/
theorem chartQuantization_eq_zero (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n ℂ ℂ m) {u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hu : ∀ p ∈ e.symm '' tsupport ψ, u p = 0) : e.chartQuantization he φ ψ a u = 0 := by
  -- Since `u` vanishes on `e⁻¹(supp ψ)`, the function `ψ · (u ∘ e⁻¹)` is zero.
  have hv (y : CoordinateSpace n) : (0 : 𝓢(CoordinateSpace n, ℂ)) y = ψ y • u (e.symm y) := by
    by_cases hy : y ∈ tsupport ψ
    · rw [hu _ (mem_image_of_mem _ hy), smul_zero, zero_apply]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_smul, zero_apply]
  ext p
  rw [ContMDiffMap.coe_zero, Pi.zero_apply]
  by_cases hp : p ∈ e.source
  · rw [chartQuantization_apply_of_mem he φ ψ a u hv hp, quantizeSchwartzValue_zero_right,
      smul_zero]
  · exact chartQuantization_apply_of_notMem he φ ψ a u hp

/-- **Chart quantizations are properly supported.** For every compact set, one may take
`K' = e⁻¹(supp φ) ∪ e⁻¹(supp ψ)`: the output is always supported in `e⁻¹(supp φ)`, and it vanishes
when the input vanishes near `e⁻¹(supp ψ)`. -/
theorem isProperlySupported_chartQuantization (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n ℂ ℂ m) : IsProperlySupported (e.chartQuantization he φ ψ a) :=
  isProperlySupported_iff.2 fun _ _ ↦ ⟨e.symm '' tsupport φ ∪ e.symm '' tsupport ψ,
    (e.isCompact_symm_image_tsupport φ).union (e.isCompact_symm_image_tsupport ψ),
    fun u _ ↦ (tsupport_chartQuantization_subset he φ ψ a u).trans subset_union_left,
    fun u hu p _ ↦ by
      rw [chartQuantization_eq_zero he φ ψ a fun q hq ↦
        (hu.filter_mono (nhdsSet_mono subset_union_right)).self_of_nhdsSet q hq,
        ContMDiffMap.coe_zero, Pi.zero_apply]⟩

/-! ### Localization -/

section Localization

variable {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
  C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **Localization.** Let `a` be the symbol of the chart compression of an operator `P` by cutoffs
`φ` and `ψ` in a chart `e`. For cutoffs `φ₁` and `ψ₁` equal to `1` on the supports of `φ` and
`ψ`, the chart quantization of `a` localized by `φ₁` and `ψ₁` is `u ↦ φ · P (ψ u)`, where `φ` and
`ψ` are read on `M` through the chart and extended by `0`. -/
theorem chartQuantization_eq_mulLeft_comp_comp_mulLeft {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}
    {a : ClassicalSymbol n ℂ ℂ m}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u x =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    {φ₁ ψ₁ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hφ₁ : EqOn φ₁ 1 (tsupport φ))
    (hψ₁ : EqOn ψ₁ 1 (tsupport ψ)) :
    e.chartQuantization he φ₁ ψ₁ a =
      LinearMap.mulLeft ℂ (e.complexCutoffPullback he φ 1) ∘ₗ P ∘ₗ
        LinearMap.mulLeft ℂ (e.complexCutoffPullback he ψ 1) := by
  ext u p
  -- The input `ψ₁ · (u ∘ e⁻¹)` of `Op(a)`, as a Schwartz function.
  set v := cutoffPushforwardSchwartz he ψ₁ u
  have hv (y : CoordinateSpace n) : v y = ψ₁ y • u (e.symm y) :=
    cutoffPushforwardSchwartz_apply he ψ₁ u y
  -- Read on `M`, the pullback of `v` by `ψ` is `ψ u`, since `ψ₁ = 1` on the support of `ψ`.
  have hpull : e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff v (v.smooth ⊤)) =
      e.complexCutoffPullback he ψ 1 * u := by
    ext q
    by_cases hq : q ∈ e.source
    · have h := mul_complexCutoffPullback_apply_of_eq_smul he ψ (g := 1)
        (hψ₁.mono inter_subset_left) (f := ContMDiffMap.ofContDiff v (v.smooth ⊤))
        (fun y ↦ by rw [ContMDiffMap.coe_ofContDiff, hv]) hq
      rw [Pi.one_apply, one_mul, one_mul, e.left_inv hq] at h
      rw [h, ContMDiffMap.coe_mul, Pi.mul_apply, complexCutoffPullback_apply_of_mem he _ _ hq,
        ContMDiffMap.coe_one, Pi.one_apply, smul_one_mul]
    · simp [complexCutoffPullback_apply_of_notMem he _ _ hq]
  by_cases hp : p ∈ e.source
  · rw [chartQuantization_apply_of_mem he φ₁ ψ₁ a u hv hp, ha, complexChartCompression_apply,
      e.left_inv hp, hpull]
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply,
      complexCutoffPullback_apply_of_mem he _ _ hp, ContMDiffMap.coe_one, Pi.one_apply,
      smul_one_mul]
    exact smul_eq_right_of_ne_zero_imp_eq_one fun h ↦
      hφ₁ (subset_tsupport _ (left_ne_zero_of_smul h))
  · simp [chartQuantization_apply_of_notMem he _ _ a u hp,
      complexCutoffPullback_apply_of_notMem he _ _ hp]

end Localization

/-! ### Compressions of a chart quantization -/

section Compression

variable {e' : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)

include he'

/-- The cutoff `φ' · (φ ∘ e ∘ e'⁻¹)` on `ℝⁿ`, extended by `0` off the overlap of the charts: the
product of a cutoff `φ'` in the chart `e'` with a cutoff `φ` in the chart `e` read through `e'`. -/
def overlapCutoff (φ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) : CoordinateSpace n → ℝ :=
  e'.cutoffPushforward he' φ' (e.cutoffPullback he φ 1)

/-- The overlap cutoff is the coercion of a smooth function on `ℝⁿ`. -/
theorem overlapCutoff_eq (φ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    overlapCutoff he he' φ' φ = ⇑(e'.cutoffPushforward he' φ' (e.cutoffPullback he φ 1)) :=
  (rfl)

theorem overlapCutoff_apply (φ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (x : CoordinateSpace n) :
    overlapCutoff he he' φ' φ x = φ' x * e.cutoffPullback he φ 1 (e'.symm x) := by
  rw [overlapCutoff_eq, cutoffPushforward_apply]

theorem overlapCutoff_apply_of_mem (φ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {x : CoordinateSpace n}
    (hx : e'.symm x ∈ e.source) :
    overlapCutoff he he' φ' φ x = φ' x * φ (e (e'.symm x)) := by
  rw [overlapCutoff_apply, cutoffPullback_one_apply_of_mem he _ hx]

theorem overlapCutoff_apply_of_notMem (φ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {x : CoordinateSpace n}
    (hx : x ∉ (e'.symm.trans e).source) : overlapCutoff he he' φ' φ x = 0 := by
  rw [overlapCutoff_apply]
  by_cases hx' : x ∈ e'.target
  · rw [cutoffPullback_apply_of_notMem he _ _ (x := e'.symm x) fun h ↦ hx ⟨hx', h⟩, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx' (φ'.tsupport_subset h), zero_mul]

/-- The overlap cutoff is smooth, compactly supported, and supported in the source of the
transition map `e ∘ e'⁻¹`. -/
theorem overlapCutoff_spec (φ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    ContDiff ℝ ∞ (overlapCutoff he he' φ' φ) ∧ HasCompactSupport (overlapCutoff he he' φ' φ) ∧
      tsupport (overlapCutoff he he' φ' φ) ⊆ (e'.symm.trans e).source := by
  have hfun : overlapCutoff he he' φ' φ = fun x ↦ φ' x * e.cutoffPullback he φ 1 (e'.symm x) :=
    funext (overlapCutoff_apply he he' φ' φ)
  refine ⟨overlapCutoff_eq he he' φ' φ ▸ contMDiff_iff_contDiff.1 (ContMDiffMap.contMDiff _),
    hfun ▸ φ'.hasCompactSupport.mul_right, ?_⟩
  -- The support lies in the set of `x ∈ supp φ'` with `e'⁻¹ x ∈ e⁻¹(supp φ)`, which is closed.
  have hS : IsClosed (tsupport φ' ∩ e'.symm ⁻¹' (e.symm '' tsupport φ)) :=
    (e'.continuousOn_symm.mono φ'.tsupport_subset).preimage_isClosed_of_isClosed
      (isClosed_tsupport _) (e.isCompact_symm_image_tsupport φ).isClosed
  refine (closure_minimal (fun x hx ↦ ?_) hS).trans fun x ⟨hx', y, hy, hyx⟩ ↦ ?_
  · rw [Function.mem_support, hfun, ne_eq, mul_eq_zero, not_or] at hx
    exact ⟨subset_tsupport _ hx.1,
      tsupport_cutoffPullback_subset he φ 1 (subset_tsupport _ hx.2)⟩
  · rw [trans_source, symm_source]
    exact ⟨φ'.tsupport_subset hx', mem_preimage.2 (hyx ▸ e.map_target (φ.tsupport_subset hy))⟩

/-- The input of `Op(a)` in the compression of the chart quantization to the chart `e'`: on the
chart overlap, the Schwartz function `ψ · (((ψ' u) ∘ e') ∘ e⁻¹)` read through the transition map
`κ = e ∘ e'⁻¹` is `Ψ u`, for the overlap cutoff `Ψ = ψ' · (ψ ∘ κ)`. -/
private theorem cutoffPushforwardSchwartz_complexCutoffPullback_apply
    (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (u : 𝓢(CoordinateSpace n, ℂ)) :
    ∀ y ∈ (e'.symm.trans e).source, cutoffPushforwardSchwartz he ψ
      (e'.complexCutoffPullback he' ψ' (ContMDiffMap.ofContDiff u (u.smooth ⊤)))
        ((e'.symm.trans e) y) = overlapCutoff he he' ψ' ψ y • u y := by
  intro y hy
  rw [trans_source, symm_source] at hy
  rw [cutoffPushforwardSchwartz_apply, overlapCutoff_apply_of_mem he he' ψ' ψ hy.2, coe_trans,
    Function.comp_apply, e.left_inv hy.2,
    complexCutoffPullback_apply_of_mem he' _ _ (e'.map_target hy.1), e'.right_inv hy.1]
  simp [mul_comm, mul_left_comm]

/-- Off the target of the transition map `e ∘ e'⁻¹`, the Schwartz function
`ψ · (((ψ' u) ∘ e') ∘ e⁻¹)` vanishes: either `ψ` or the pullback by `ψ'` does. -/
private theorem cutoffPushforwardSchwartz_complexCutoffPullback_eq_zero
    (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ψ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ))
    (u : 𝓢(CoordinateSpace n, ℂ)) :
    ∀ z ∉ (e'.symm.trans e).target, cutoffPushforwardSchwartz he ψ
      (e'.complexCutoffPullback he' ψ' (ContMDiffMap.ofContDiff u (u.smooth ⊤))) z = 0 := by
  intro z hz
  rw [cutoffPushforwardSchwartz_apply]
  by_cases hz' : z ∈ e.target
  · rw [complexCutoffPullback_apply_of_notMem he' _ _ fun h ↦ hz ⟨hz', h⟩, smul_zero]
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hz' (ψ.tsupport_subset h), zero_smul]

/-- **The compression of a chart quantization in another chart.** Let `Op_e(a)` be the
quantization of a classical symbol `a` of order `m` in the chart `e`, localized by `φ` and `ψ`.
Its compression to any chart `e'` of the maximal atlas, by cutoffs `φ'` and `ψ'`, is `Op(b)` for a
classical symbol `b` of order `m`. On the overlap, where the transition map `κ = e ∘ e'⁻¹` is
defined, the principal symbol of `b` is

`σ(b)(x, ξ) = φ'(x) φ(κ x) ψ'(x) ψ(κ x) σ(a)(κ x, (Dκ(x)*)⁻¹ ξ)`,

and off the overlap it vanishes. -/
theorem exists_complexChartCompression_chartQuantization_eq
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n ℂ ℂ m)
    (φ' ψ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) :
    ∃ b : ClassicalSymbol n ℂ ℂ m,
      (∀ x ∈ (e'.symm.trans e).source, ∀ ξ, b.principal.coefficient (x, ξ) =
        (φ' x * φ (e (e'.symm x)) * (ψ' x * ψ (e (e'.symm x)))) •
          a.principal.coefficient (e (e'.symm x),
            ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ (e ∘ e'.symm) x)) ξ)) ∧
      (∀ x ∉ (e'.symm.trans e).source, ∀ ξ, b.principal.coefficient (x, ξ) = 0) ∧
      ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
        quantizeSchwartzValue b.toSymbol.coefficient u x =
          e'.complexChartCompression he' φ' ψ' (e.chartQuantization he φ ψ a)
            (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x := by
  set κ := e'.symm.trans e with hκ_def
  have hκ : ContDiffOn ℝ ∞ κ κ.source := contDiffOn_symm_trans_of_mem_maximalAtlas he' he
  have hκ' : ContDiffOn ℝ ∞ κ.symm κ.target := fun _ hz ↦
    (contDiffAt_symm_trans_symm_of_mem_maximalAtlas he' he hz).contDiffWithinAt
  obtain ⟨hΦ, hΦc, hΦs⟩ := overlapCutoff_spec he he' φ' φ
  obtain ⟨hΨ, hΨc, hΨs⟩ := overlapCutoff_spec he he' ψ' ψ
  obtain ⟨b, hb, hop⟩ := a.exists_smul_quantizeSchwartzValue_comp_eq κ hκ hκ' hΦ hΦc hΦs hΨ hΨc hΨs
  refine ⟨b, fun x hx ξ ↦ ?_, fun x hx ξ ↦ ?_, fun u x ↦ ?_⟩
  · rw [hb, overlapCutoff_apply_of_mem he he' φ' φ hx.2,
      overlapCutoff_apply_of_mem he he' ψ' ψ hx.2]
    simp [hκ_def]
  · rw [hb, overlapCutoff_apply_of_notMem he he' φ' φ hx, zero_mul, zero_smul]
  rw [← hop u _ (cutoffPushforwardSchwartz_complexCutoffPullback_apply he he' ψ ψ' u)
    (cutoffPushforwardSchwartz_complexCutoffPullback_eq_zero he he' ψ ψ' u),
    complexChartCompression_apply, overlapCutoff_apply]
  by_cases hx : e'.symm x ∈ e.source
  · rw [chartQuantization_apply_of_mem he φ ψ a _ (cutoffPushforwardSchwartz_apply he ψ _) hx,
      cutoffPullback_one_apply_of_mem he _ hx]
    simp [hκ_def, mul_assoc]
  · rw [chartQuantization_apply_of_notMem he φ ψ a _ hx, cutoffPullback_apply_of_notMem he _ _ hx,
      mul_zero, zero_smul, smul_zero]

end Compression

/-- **Chart quantizations are classical pseudodifferential operators.** The quantization of a
classical symbol of order `m` in a chart of the maximal atlas, localized by cutoffs with compact
supports in the chart target, is a classical pseudodifferential operator of order `m` on `M`. -/
theorem chartQuantization_mem_classicalPseudodifferentialOperators
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n ℂ ℂ m) :
    e.chartQuantization he φ ψ a ∈ classicalPseudodifferentialOperators m :=
  mem_classicalPseudodifferentialOperators_iff.2 ⟨isProperlySupported_chartQuantization he φ ψ a,
    fun _ he' φ' ψ' ↦
      let ⟨b, _, _, hb⟩ := exists_complexChartCompression_chartQuantization_eq he he' φ ψ a φ' ψ'
      ⟨b, hb⟩⟩

end OpenPartialHomeomorph
