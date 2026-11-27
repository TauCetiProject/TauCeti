/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import TauCeti.Analysis.Calculus.CoordinateDeriv
public import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Basic
import TauCeti.Analysis.Distribution.TestFunction.Basic

/-!
# Reading functions on a manifold in a chart as Schwartz functions

Let `M` be a manifold modelled on `ℝⁿ`, `e` a chart of its maximal smooth atlas and `ψ` a cutoff
with compact support in the chart target. A complex-valued smooth function `u` on `M` is read in
the chart as the compactly supported smooth function `ψ · (u ∘ e⁻¹)` on `ℝⁿ`, which is a Schwartz
function (`OpenPartialHomeomorph.cutoffPushforwardSchwartz`). Two cutoffs in different charts are
combined on the chart overlap by the cutoff `φ' · (φ ∘ e ∘ e'⁻¹)`
(`OpenPartialHomeomorph.overlapCutoff`).

## Main definitions

* `OpenPartialHomeomorph.cutoffPushforwardSchwartz`: a function `u` on `M` read in the chart `e`
  through a cutoff `ψ`, as the Schwartz function `ψ · (u ∘ e⁻¹)` on `ℝⁿ`.
* `OpenPartialHomeomorph.overlapCutoff`: the product `φ' · (φ ∘ e ∘ e'⁻¹)` of cutoffs in two charts,
  read in the chart `e'`.

## Main results

* `OpenPartialHomeomorph.overlapCutoff_spec`: the overlap cutoff is smooth with compact support in
  the source of the transition map.
* `mulLeft_ofReal_cutoffPullback_one_complexCutoffPullback_eq_complexCutoffPullback` (in the
  `OpenPartialHomeomorph` namespace): a cutoff `τ` read on `M` absorbs a pullback through a cutoff
  equal to `1` on the support of `τ`.
* `OpenPartialHomeomorph.mulLeft_ofReal_cutoffPullback_one_eq_complexCutoffPullback`: multiplying a
  function by a cutoff `τ` read on `M` is pushing it forward to the chart by `τ` and pulling it back
  by a cutoff equal to `1` on the support of `τ`.
* `OpenPartialHomeomorph.cutoffPushforwardSchwartz_complexCutoffPullback_apply_of_eq_one`: reading
  through `τ` the pullback of `G` by a cutoff equal to `1` on the support of `τ` gives `τ · G`.
* `OpenPartialHomeomorph.eq_zero_of_forall_cutoffPushforwardSchwartz_eq_zero`: a function is
  determined by its readings through cutoffs whose readings on `M` add up to `1`.
* `OpenPartialHomeomorph.sum_indicator_cutoffPushforwardSchwartz_apply`: such a function is
  recovered by gluing its readings back along the charts.
-/

public section

noncomputable section

open Set TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap

namespace OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)

include he

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

/-- On the chart source, the reading `ψ · (u ∘ e⁻¹)` composed with the chart is `(ψ ∘ e) u`. -/
theorem cutoffPushforwardSchwartz_apply_eq_of_mem (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) {x : M} (hx : x ∈ e.source) :
    e.cutoffPushforwardSchwartz he ψ u (e x) = (e.cutoffPullback he ψ 1 x : ℂ) * u x := by
  rw [cutoffPushforwardSchwartz_apply, e.left_inv hx, cutoffPullback_one_apply_of_mem he _ hx,
    Complex.real_smul]

omit [T2Space M] in
/-- The reading `ψ · (u ∘ e⁻¹)` is supported in the support of `ψ`. -/
theorem support_cutoffPushforwardSchwartz_subset (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    Function.support (e.cutoffPushforwardSchwartz he ψ u) ⊆ tsupport ψ := fun y hy ↦
  subset_tsupport _ fun h ↦ hy (by rw [cutoffPushforwardSchwartz_apply, h, zero_smul])

/-- **Absorbing a cutoff into a pullback.** Multiplying the pullback `(χ₁ f) ∘ e` by a cutoff `τ`
read on `M` through the chart, where `χ₁` equals `1` on the support of `τ`, gives the pullback
`(τ f) ∘ e`. -/
theorem mulLeft_ofReal_cutoffPullback_one_complexCutoffPullback_eq_complexCutoffPullback
    {τ χ₁ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hχ₁ : ∀ y ∈ tsupport τ, χ₁ y = 1)
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; 𝓘(ℝ, ℂ), ℂ⟯) :
    LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e.cutoffPullback he τ 1))
      (e.complexCutoffPullback he χ₁ f) = e.complexCutoffPullback he τ f := by
  ext p
  by_cases hp : p ∈ e.source
  · simp only [LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply,
      ContMDiffMap.ofReal_apply, cutoffPullback_one_apply_of_mem he _ hp,
      complexCutoffPullback_apply_of_mem he _ _ hp]
    by_cases hτ : τ (e p) = 0
    · simp [hτ]
    · rw [hχ₁ _ (subset_tsupport _ hτ), one_smul, Complex.real_smul]
  · simp [complexCutoffPullback_apply_of_notMem he _ _ hp]

/-- **Multiplying by a cutoff read through a chart.** Multiplying a function `g` on `M` by a
cutoff `τ` in the chart `e`, read on `M` as `τ ∘ e` extended by `0`, is pushing `g` forward to the
chart as the Schwartz function `τ · (g ∘ e⁻¹)` and pulling it back to `M` through a cutoff `χ`
equal to `1` on the support of `τ`. -/
theorem mulLeft_ofReal_cutoffPullback_one_eq_complexCutoffPullback
    {τ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hχ : ∀ y ∈ tsupport τ, χ y = 1)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (e.cutoffPullback he τ 1)) g =
      e.complexCutoffPullback he χ (ContMDiffMap.ofContDiff (e.cutoffPushforwardSchwartz he τ g)
        ((e.cutoffPushforwardSchwartz he τ g).smooth ⊤)) := by
  ext p
  by_cases hp : p ∈ e.source
  · rw [complexCutoffPullback_apply_of_mem he _ _ hp, ContMDiffMap.coe_ofContDiff,
      cutoffPushforwardSchwartz_apply, e.left_inv hp]
    simp only [LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply,
      ContMDiffMap.ofReal_apply, cutoffPullback_one_apply_of_mem he _ hp]
    by_cases hτ : τ (e p) = 0
    · simp [hτ]
    · rw [hχ _ (subset_tsupport _ hτ), one_smul, Complex.real_smul]
  · simp [complexCutoffPullback_apply_of_notMem he _ _ hp,
      cutoffPullback_apply_of_notMem he _ _ hp]

/-- **Reading a pullback in its own chart.** The reading through a cutoff `τ` of the pullback of a
function `G` on `ℝⁿ` through a cutoff `χ` in the same chart, equal to `1` on the support of `τ`, is
`τ · G`. -/
theorem cutoffPushforwardSchwartz_complexCutoffPullback_apply_of_eq_one
    {τ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hχ : ∀ y ∈ tsupport τ, χ y = 1)
    (G : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; 𝓘(ℝ, ℂ), ℂ⟯) (y : CoordinateSpace n) :
    e.cutoffPushforwardSchwartz he τ (e.complexCutoffPullback he χ G) y = τ y • G y := by
  rw [cutoffPushforwardSchwartz_apply]
  by_cases hτ : τ y = 0
  · simp [hτ]
  have hy : y ∈ e.target := τ.tsupport_subset (subset_tsupport _ hτ)
  rw [complexCutoffPullback_apply_of_mem he _ _ (e.map_target hy), e.right_inv hy,
    hχ _ (subset_tsupport _ hτ), one_smul]

omit he in
/-- **A function is recovered from its readings.** If the readings `ψᵢ ∘ eᵢ` on `M` of finitely
many cutoffs `ψᵢ` in charts `eᵢ` add up to `1`, then gluing the readings `ψᵢ · (u ∘ eᵢ⁻¹)` of a
function `u` back along the charts, each extended by `0` outside the chart source, gives `u`. -/
theorem sum_indicator_cutoffPushforwardSchwartz_apply {ι : Type*} [Fintype ι]
    {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    ∑ i, (e i).source.indicator
      (fun p ↦ (e i).cutoffPushforwardSchwartz (he i) (ψ i) u (e i p)) x = u x := by
  calc _ = ∑ i, ((e i).cutoffPullback (he i) (ψ i) 1 x) • u x := Finset.sum_congr rfl fun i _ ↦ by
          by_cases hx : x ∈ (e i).source
          · rw [indicator_of_mem hx, cutoffPushforwardSchwartz_apply,
              cutoffPullback_one_apply_of_mem (he i) _ hx, (e i).left_inv hx]
          · rw [indicator_of_notMem hx, cutoffPullback_apply_of_notMem (he i) _ _ hx, zero_smul]
    _ = u x := by rw [← Finset.sum_smul, hψ x, one_smul]

omit he in
/-- **A function is determined by its readings.** If the readings `ψᵢ ∘ eᵢ` on `M` of finitely
many cutoffs `ψᵢ` in charts `eᵢ` add up to `1`, a smooth function `u` on `M` all of whose readings
`ψᵢ · (u ∘ eᵢ⁻¹)` vanish is zero, since `u = ∑ᵢ (ψᵢ ∘ eᵢ) u`. -/
theorem eq_zero_of_forall_cutoffPushforwardSchwartz_eq_zero {ι : Type*} [Fintype ι]
    {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    {u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hu : ∀ i, (e i).cutoffPushforwardSchwartz (he i) (ψ i) u = 0) : u = 0 := by
  ext x
  rw [← sum_indicator_cutoffPushforwardSchwartz_apply he ψ hψ u x]
  simp [hu]

section Overlap

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
  refine ⟨overlapCutoff_eq he he' φ' φ ▸ e'.contDiff_cutoffPushforward he' φ' _,
    overlapCutoff_eq he he' φ' φ ▸ e'.hasCompactSupport_cutoffPushforward he' φ' _, ?_⟩
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

end Overlap

end OpenPartialHomeomorph
