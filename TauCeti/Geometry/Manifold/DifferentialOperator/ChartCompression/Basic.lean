/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Basic
public import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Algebra.GroupWithZero.Indicator
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.MFDeriv.Localized
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.PartitionOfUnity.Square
import TauCeti.Topology.OpenPartialHomeomorph.Basic

/-!
# Differential operators on a manifold, compressed to a chart

Let `M` be a manifold modelled on a real normed space `E`, and let `e` be a chart of its maximal
smooth atlas. An operator `D` on the smooth functions `C^∞(M)` is read in the chart through two
cutoffs `φ` and `ψ` with compact supports in the chart target: its **chart compression** is the
operator

`f ↦ φ · (D ((ψ f) ∘ e)) ∘ e⁻¹`

on the smooth functions `C^∞(E)` (`OpenPartialHomeomorph.chartCompression`). Here `(ψ f) ∘ e` is
extended by zero outside the chart source (`OpenPartialHomeomorph.cutoffPullback`), and
`φ · (h ∘ e⁻¹)` vanishes outside the chart target (`OpenPartialHomeomorph.cutoffPushforward`).
Compressions are how an operator on a manifold is described in local coordinates: an operator on
`M` is pseudodifferential when all its chart compressions are quantizations of symbols modulo
smoothing operators (Hörmander III, §18.1), and a differential operator is identified with the
quantization of its polynomial symbol in every chart.

This file shows that compression preserves Grothendieck's differential operators
(`TauCeti.differentialOperators`, defined by iterated commutators with multiplication operators,
with no continuity assumed) and computes their principal symbols:

* `OpenPartialHomeomorph.chartCompression_mem_differentialOperators`: the chart compression of a
  differential operator of order at most `m` on `C^∞(M)` is a differential operator of order at
  most `m` on `C^∞(E)`. Indeed, if a cutoff `χ` equals `1` near the supports of `φ` and `ψ`, then
  multiplication by `g ∈ C^∞(E)` is intertwined by the pullback and the pushforward with
  multiplication by `(χ g) ∘ e`, so the commutator of the compression with `g` is the compression
  of the commutator of `D` with `(χ g) ∘ e`
  (`OpenPartialHomeomorph.smulCommutator_pow_chartCompression`,
  `TauCeti.comp_comp_mem_differentialOperators`).
* `OpenPartialHomeomorph.smoothPrincipalSymbol_chartCompressionDifferentialOperators`: at a point
  `x` of the chart target, the principal symbol of the compression at a covector `η` is
  `φ(x) ψ(x) σ(D)(e⁻¹ x)(η ∘ de)`: the principal symbol transforms as a function on the cotangent
  bundle, multiplied by the cutoffs.
* `OpenPartialHomeomorph.complexChartCompression_conj`: for a diffeomorphism `Φ : M → N`, the chart
  compression in a chart `e` of `M` of the transport `f ↦ (D (f ∘ Φ⁻¹)) ∘ Φ` of an operator `D` on
  `N` is the chart compression of `D` in the chart `e ∘ Φ⁻¹` of `N`, by the same cutoffs.
* `OpenPartialHomeomorph.complexChartCompression_intrinsicConj`: the chart compression of the
  conjugate `f ↦ conj (D (conj f))` of an operator is the conjugate of its chart compression,
  since the cutoffs are real.

## Main definitions

* `OpenPartialHomeomorph.cutoffPullback`: `f ↦ (ψ f) ∘ e`, extended by zero, as a linear map
  `C^∞(E) → C^∞(M)`.
* `OpenPartialHomeomorph.cutoffPushforward`: `h ↦ φ · (h ∘ e⁻¹)`, as a linear map
  `C^∞(M) → C^∞(E)`.
* `OpenPartialHomeomorph.chartCompression`: the chart compression of an operator on `C^∞(M)`.
* `OpenPartialHomeomorph.chartCompressionDifferentialOperators`: the chart compression of
  differential operators of order at most `m`.
* `OpenPartialHomeomorph.complexCutoffPullback`, `OpenPartialHomeomorph.complexCutoffPushforward`
  and `OpenPartialHomeomorph.complexChartCompression`: the same constructions for complex-linear
  operators on complex-valued smooth functions, through which pseudodifferential operators on `M`
  are read in charts.

## Main results

* `IsCompact.exists_sum_cutoffPullback_eq_one`: a compact set has finitely many cutoffs in preferred
  charts whose pullbacks sum to `1` on it, through which operators on `M` are assembled from
  operators in charts.
* `TauCeti.exists_locallyFinite_finsum_sq_cutoffPullback_eq_one`: a Hausdorff σ-compact manifold
  has a locally finite family of cutoffs in preferred charts whose pullbacks have squares summing
  to `1` everywhere, through which operators on a noncompact manifold are assembled symmetrically.
* `OpenPartialHomeomorph.complexChartCompression_congr`: two charts with the same inverse on the
  supports of the cutoffs give the same chart compressions.
* `OpenPartialHomeomorph.complexChartCompression_comp_apply`: the compression of a composition
  `A ∘ B` is the compression of `A` after that of `B`, through a cutoff equal to `1` where the
  outputs of `B` live.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §19.
-/

public section

noncomputable section

open Set Filter Topology TauCeti
open scoped ContDiff Manifold Distributions

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)

include he

/-! ### Pulling back and pushing forward through a chart -/

/-- **Pulling a function on a chart back to the manifold.** For a cutoff `ψ` with compact support
in the target of the chart `e`, the smooth function on `M` equal to `(ψ f) ∘ e` on the chart source
and to `0` elsewhere, as a linear map `C^∞(E) → C^∞(M)` in `f`. -/
def cutoffPullback (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), M; ℝ⟯ where
  toFun f := ⟨e.source.indicator ((fun y ↦ ψ y * f y) ∘ e),
    -- The extended chart `e.extend 𝓘(ℝ, E)` is `e` by definition.
    e.contMDiff_indicator_comp_extend he
      (ψ.contDiff.mul (contMDiff_iff_contDiff.1 f.contMDiff)) ψ.hasCompactSupport.mul_right
      (by rw [extend_target', modelWithCornersSelf_coe, image_id]
          exact tsupport_mul_subset_left.trans ψ.tsupport_subset)⟩
  map_add' f g := by
    ext x
    -- The anonymous constructor elaborates to a bare subtype, so `ContMDiffMap.coe_add` cannot
    -- rewrite it; `change` unfolds the coercions of `⟨u, _⟩` to `u` and of sums to pointwise sums.
    change e.source.indicator ((fun y ↦ ψ y * (f + g) y) ∘ e) x =
      e.source.indicator ((fun y ↦ ψ y * f y) ∘ e) x +
        e.source.indicator ((fun y ↦ ψ y * g y) ∘ e) x
    by_cases hx : x ∈ e.source <;> simp [hx, mul_add]
  map_smul' c f := by
    ext x
    -- As for `map_add'`, with scalar multiples evaluated pointwise.
    change e.source.indicator ((fun y ↦ ψ y * (c • f) y) ∘ e) x =
      c * e.source.indicator ((fun y ↦ ψ y * f y) ∘ e) x
    by_cases hx : x ∈ e.source <;> simp [hx, mul_left_comm]

theorem cutoffPullback_apply_of_mem (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) {x : M} (hx : x ∈ e.source) :
    e.cutoffPullback he ψ f x = ψ (e x) * f (e x) :=
  indicator_of_mem hx _

theorem cutoffPullback_apply_of_notMem (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) {x : M} (hx : x ∉ e.source) :
    e.cutoffPullback he ψ f x = 0 :=
  indicator_of_notMem hx _

/-- On the chart source, the pullback of the constant function `1` is the cutoff read through the
chart. -/
@[simp]
theorem cutoffPullback_one_apply_of_mem (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {x : M}
    (hx : x ∈ e.source) : e.cutoffPullback he ψ 1 x = ψ (e x) := by
  rw [cutoffPullback_apply_of_mem he _ _ hx, ContMDiffMap.coe_one, Pi.one_apply, mul_one]

/-- The pullback `(ψ f) ∘ e` is supported in the image of the support of `ψ` under the inverse of
the chart. -/
theorem tsupport_cutoffPullback_subset (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) : tsupport (e.cutoffPullback he ψ f) ⊆ e.symm '' tsupport ψ :=
  e.tsupport_subset_symm_image_tsupport ψ
    (fun x hx h ↦ by rw [cutoffPullback_apply_of_mem he _ _ hx, h, zero_mul])
    fun _ hx ↦ cutoffPullback_apply_of_notMem he _ _ hx

/-- The pullback `ψ ∘ e` of a cutoff, extended by `0`, is supported exactly in the image of the
support of `ψ` under the inverse of the chart. -/
@[simp]
theorem tsupport_cutoffPullback_one (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    tsupport (e.cutoffPullback he ψ 1) = e.symm '' tsupport ψ := by
  refine subset_antisymm (e.tsupport_cutoffPullback_subset he ψ 1) ?_
  rintro _ ⟨y, hy, rfl⟩
  -- `e⁻¹` is continuous on the chart target and maps the support of `ψ` into that of `ψ ∘ e`.
  refine closure_mono ?_ ((e.continuousAt_symm (ψ.tsupport_subset hy)).continuousWithinAt
    |>.mem_closure_image hy)
  rintro _ ⟨z, hz, rfl⟩
  have hzt : z ∈ e.target := ψ.tsupport_subset (subset_tsupport _ hz)
  rwa [Function.mem_support, cutoffPullback_one_apply_of_mem he _ (e.map_target hzt),
    e.right_inv hzt]

/-- **Pushing a function on the manifold forward to a chart.** For a cutoff `φ` with compact
support in the target of the chart `e`, the smooth function `φ · (h ∘ e⁻¹)` on `E`, which vanishes
outside the chart target, as a linear map `C^∞(M) → C^∞(E)` in `h`. -/
def cutoffPushforward (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    C^∞⟮𝓘(ℝ, E), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯ where
  toFun h := ⟨fun y ↦ φ y * h (e.symm y), by
    simpa only [smul_eq_mul, Function.comp_apply] using
      ContMDiffOn.contMDiff_smul_of_tsupport_subset
        (h.contMDiff.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)) e.open_target
        φ.contDiff.contMDiff.contMDiffOn φ.tsupport_subset⟩
  map_add' g h := by
    ext y
    -- As for `cutoffPullback`, `change` unfolds the coercions of the anonymous constructors.
    change φ y * (g + h) (e.symm y) = φ y * g (e.symm y) + φ y * h (e.symm y)
    rw [ContMDiffMap.coe_add, Pi.add_apply, mul_add]
  map_smul' c h := by
    ext y
    change φ y * (c • h) (e.symm y) = c * (φ y * h (e.symm y))
    rw [ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]

omit [T2Space M] in
@[simp]
theorem cutoffPushforward_apply (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (h : C^∞⟮𝓘(ℝ, E), M; ℝ⟯) (y : E) :
    e.cutoffPushforward he φ h y = φ y * h (e.symm y) :=
  (rfl)

omit [T2Space M] in
/-- The pushforward `φ · (h ∘ e⁻¹)` is smooth as a function on `E`. -/
theorem contDiff_cutoffPushforward (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (h : C^∞⟮𝓘(ℝ, E), M; ℝ⟯) : ContDiff ℝ ∞ (e.cutoffPushforward he φ h : E → ℝ) :=
  contMDiff_iff_contDiff.1 (e.cutoffPushforward he φ h).contMDiff

omit [T2Space M] in
/-- The pushforward `φ · (h ∘ e⁻¹)` has compact support, contained in that of `φ`. -/
theorem hasCompactSupport_cutoffPushforward (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (h : C^∞⟮𝓘(ℝ, E), M; ℝ⟯) : HasCompactSupport (e.cutoffPushforward he φ h : E → ℝ) :=
  funext (e.cutoffPushforward_apply he φ h) ▸ φ.hasCompactSupport.mul_right

/-- **Functions supported in a chart are cutoffs.** A smooth function `g` on `M` with compact
support in the chart source is the pullback `ρ ∘ e`, extended by `0`, of a cutoff `ρ` with compact
support in the chart target. This turns a partition of unity subordinate to chart sources into
cutoffs in the charts. -/
theorem exists_cutoffPullback_one_eq [FiniteDimensional ℝ E] {g : C^∞⟮𝓘(ℝ, E), M; ℝ⟯}
    (hgc : HasCompactSupport g) (hg : tsupport g ⊆ e.source) :
    ∃ ρ : 𝓓(⟨e.target, e.open_target⟩, ℝ), e.cutoffPullback he ρ 1 = g := by
  -- A cutoff `θ` equal to `1` near the image `e (supp g)`, and `ρ = θ · (g ∘ e⁻¹)`.
  obtain ⟨θ, hθ, -⟩ := TestFunction.exists_eventually_eq_one
    (Ω := ⟨e.target, e.open_target⟩) (n := ⊤)
    (hgc.isCompact.image_of_continuousOn (e.continuousOn.mono hg))
    (image_subset_iff.2 fun p hp ↦ e.map_source (hg hp))
  have hρ : ContDiff ℝ ∞ fun y ↦ θ y * g (e.symm y) :=
    funext (e.cutoffPushforward_apply he θ g) ▸ e.contDiff_cutoffPushforward he θ g
  refine ⟨⟨fun y ↦ θ y * g (e.symm y), hρ, θ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans θ.tsupport_subset⟩, ?_⟩
  ext p
  by_cases hp : p ∈ e.source
  · rw [cutoffPullback_one_apply_of_mem he _ hp, TestFunction.coe_mk, e.left_inv hp]
    exact mul_eq_right_of_ne_zero_imp_eq_one fun hgp ↦
      hθ.self_of_nhdsSet _ (mem_image_of_mem e (subset_tsupport _ hgp))
  · rw [cutoffPullback_apply_of_notMem he _ _ hp,
      image_eq_zero_of_notMem_tsupport fun h ↦ hp (hg h)]

/-! ### Chart compressions -/

/-- The **chart compression** of an operator `D` on the smooth functions on `M` by cutoffs `φ`
and `ψ` with compact supports in the target of the chart `e`: the operator
`f ↦ φ · (D ((ψ f) ∘ e)) ∘ e⁻¹` on the smooth functions on `E`, linear in `D`. It reads `D` in
the chart, localized on the left by `φ` and on the right by `ψ`. -/
def chartCompression (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    (C^∞⟮𝓘(ℝ, E), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), M; ℝ⟯) →ₗ[ℝ]
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯ where
  toFun D := e.cutoffPushforward he φ ∘ₗ D ∘ₗ e.cutoffPullback he ψ
  map_add' D₁ D₂ := by rw [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c D := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

theorem chartCompression_def (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (D : C^∞⟮𝓘(ℝ, E), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), M; ℝ⟯) :
    e.chartCompression he φ ψ D = e.cutoffPushforward he φ ∘ₗ D ∘ₗ e.cutoffPullback he ψ :=
  (rfl)

@[simp]
theorem chartCompression_apply (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (D : C^∞⟮𝓘(ℝ, E), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), M; ℝ⟯) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (y : E) :
    e.chartCompression he φ ψ D f y = φ y * D (e.cutoffPullback he ψ f) (e.symm y) :=
  (rfl)

section Intertwining

variable {φ ψ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}

/-- Pulling back by `ψ` intertwines multiplication by `g` with multiplication by the pullback of
`g` by a cutoff `χ` equal to `1` on the support of `ψ`. -/
theorem cutoffPullback_mul (hχ : tsupport ψ ⊆ χ ⁻¹' {1}) (g f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    e.cutoffPullback he ψ (g * f) = e.cutoffPullback he χ g * e.cutoffPullback he ψ f := by
  ext x
  by_cases hx : x ∈ e.source
  · simp only [ContMDiffMap.coe_mul, Pi.mul_apply, cutoffPullback_apply_of_mem he _ _ hx]
    by_cases hψ : ψ (e x) = 0
    · simp [hψ]
    · rw [show χ (e x) = 1 from hχ (subset_tsupport _ hψ)]
      ring
  · simp [cutoffPullback_apply_of_notMem he _ _ hx]

/-- A cutoff `χ` equal to `1` on the support of `ψ` absorbs `ψ`, both read on `M` through the
chart: `ψ(e x) χ(e x) = ψ(e x)`. -/
theorem cutoffPullback_one_mul_cutoffPullback_one_of_tsupport_subset
    (hχ : tsupport ψ ⊆ χ ⁻¹' {1}) (x : M) :
    e.cutoffPullback he ψ 1 x * e.cutoffPullback he χ 1 x = e.cutoffPullback he ψ 1 x := by
  rw [mul_comm, ← Pi.mul_apply, ← ContMDiffMap.coe_mul, ← cutoffPullback_mul he hχ, mul_one]

/-- Pushing forward by `φ` intertwines multiplication by the pullback of `g` by a cutoff `χ` equal
to `1` on the support of `φ` with multiplication by `g`. -/
theorem cutoffPushforward_mul (hχ : tsupport φ ⊆ χ ⁻¹' {1}) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯)
    (h : C^∞⟮𝓘(ℝ, E), M; ℝ⟯) :
    e.cutoffPushforward he φ (e.cutoffPullback he χ g * h) = g * e.cutoffPushforward he φ h := by
  ext y
  simp only [cutoffPushforward_apply, ContMDiffMap.coe_mul, Pi.mul_apply]
  by_cases hφ : φ y = 0
  · simp [hφ]
  · have hy : y ∈ e.target := φ.tsupport_subset (subset_tsupport _ hφ)
    rw [cutoffPullback_apply_of_mem he _ _ (e.map_target hy), e.right_inv hy,
      show χ y = 1 from hχ (subset_tsupport _ hφ)]
    ring

/-- Pulling back by `ψ` and pushing forward by `φ` intertwine multiplication by `g` with
multiplication by the pullback of `g` by a cutoff `χ` equal to `1` on the supports of `φ` and
`ψ`. -/
private theorem smul_intertwining (hχ : tsupport φ ∪ tsupport ψ ⊆ χ ⁻¹' {1})
    (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    (∀ f, e.cutoffPullback he ψ (g • f) = e.cutoffPullback he χ g • e.cutoffPullback he ψ f) ∧
      ∀ h, e.cutoffPushforward he φ (e.cutoffPullback he χ g • h) =
        g • e.cutoffPushforward he φ h :=
  ⟨fun f ↦ by simpa only [smul_eq_mul] using
      cutoffPullback_mul he (subset_union_right.trans hχ) g f,
    fun h ↦ by simpa only [smul_eq_mul] using
      cutoffPushforward_mul he (subset_union_left.trans hχ) g h⟩

/-- The iterated commutator of a chart compression with `g` is the chart compression of the
iterated commutator with the pullback of `g` by a cutoff `χ` equal to `1` on the supports of `φ`
and `ψ`. -/
theorem smulCommutator_pow_chartCompression (hχ : tsupport φ ∪ tsupport ψ ⊆ χ ⁻¹' {1})
    (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (D : C^∞⟮𝓘(ℝ, E), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), M; ℝ⟯) (k : ℕ) :
    (smulCommutator ℝ g ^ k) (e.chartCompression he φ ψ D) =
      e.chartCompression he φ ψ ((smulCommutator ℝ (e.cutoffPullback he χ g) ^ k) D) :=
  smulCommutator_pow_comp_comp (smul_intertwining he hχ g).1 (smul_intertwining he hχ g).2 D k

end Intertwining

/-- **Chart compressions of differential operators.** The chart compression of a differential
operator of order at most `m` on `C^∞(M)` is a differential operator of order at most `m` on
`C^∞(E)`. -/
theorem chartCompression_mem_differentialOperators [FiniteDimensional ℝ E]
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {D : C^∞⟮𝓘(ℝ, E), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), M; ℝ⟯}
    {m : ℕ} (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ C^∞⟮𝓘(ℝ, E), M; ℝ⟯
      C^∞⟮𝓘(ℝ, E), M; ℝ⟯ m) :
    e.chartCompression he φ ψ D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m := by
  obtain ⟨χ, hχ⟩ := TestFunction.exists_eventually_eq_one_nhdsSet_tsupport_union φ ψ
  exact comp_comp_mem_differentialOperators
    (fun g ↦ ⟨_, smul_intertwining he hχ.self_of_nhdsSet g⟩) hD

/-- The chart compression of differential operators of order at most `m` on `C^∞(M)`, as a linear
map to the differential operators of order at most `m` on `C^∞(E)`. -/
def chartCompressionDifferentialOperators [FiniteDimensional ℝ E]
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (m : ℕ) :
    differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ m →ₗ[ℝ]
      differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m :=
  (e.chartCompression he φ ψ).restrict fun _ ↦ e.chartCompression_mem_differentialOperators he φ ψ

@[simp]
theorem coe_chartCompressionDifferentialOperators [FiniteDimensional ℝ E]
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ m) :
    (e.chartCompressionDifferentialOperators he φ ψ m D :
        C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) =
      e.chartCompression he φ ψ D :=
  (rfl)

theorem chartCompressionDifferentialOperators_apply [FiniteDimensional ℝ E]
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ m)
    (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (y : E) :
    (e.chartCompressionDifferentialOperators he φ ψ m D).val f y =
      φ y * D.val (e.cutoffPullback he ψ f) (e.symm y) :=
  (rfl)

/-! ### The principal symbol of a chart compression -/

section PrincipalSymbol

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Near a point `e⁻¹ x` at which the cutoff `χ` is `1` near `x`, the pullback of `g` by `χ` is
`g ∘ e`, so its differential is the differential of `g` composed with that of the chart. -/
theorem mvfderiv_cutoffPullback {χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}
    (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) {x : E} (hx : x ∈ e.target) (hχ : ∀ᶠ y in 𝓝 x, χ y = 1) :
    mvfderiv 𝓘(ℝ, E) (e.cutoffPullback he χ g) (e.symm x) =
      (mvfderiv 𝓘(ℝ, E) g x).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (e.symm x)) := by
  have hxs : e.symm x ∈ e.source := e.map_target hx
  have hχ' : ∀ᶠ z in 𝓝 (e.symm x), χ (e z) = 1 :=
    (e.continuousAt hxs).eventually (by rwa [e.right_inv hx])
  have hev : (e.cutoffPullback he χ g : M → ℝ) =ᶠ[𝓝 (e.symm x)] g ∘ e := by
    filter_upwards [e.open_source.mem_nhds hxs, hχ'] with z hz hχz
    rw [cutoffPullback_apply_of_mem he _ _ hz, hχz, one_mul, Function.comp_apply]
  ext v
  rw [hev.mvfderiv_eq, mvfderiv_comp_apply_of_eq _
    (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    ((contMDiffAt_of_mem_maximalAtlas he hxs).mdifferentiableAt (by simp)) (e.right_inv hx)]
  rfl

/-- **The principal symbol of a chart compression.** At a point `x` of the chart target, the
principal symbol of the chart compression of `D` by `φ` and `ψ` at a covector `η` is `φ(x) ψ(x)`
times the principal symbol of `D` at `e⁻¹ x`, at the covector `η ∘ de` obtained by composing with
the differential of the chart. -/
theorem smoothPrincipalSymbol_chartCompressionDifferentialOperators
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ m)
    {x : E} (hx : x ∈ e.target) (η : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) :
    smoothPrincipalSymbol 𝓘(ℝ, E) BoundarylessManifold.isInteriorPoint
        (e.chartCompressionDifferentialOperators he φ ψ m D) η =
      φ x * ψ x * smoothPrincipalSymbol 𝓘(ℝ, E) (x := e.symm x)
        BoundarylessManifold.isInteriorPoint D (η.comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (e.symm x))) := by
  obtain ⟨χ, hχ⟩ := TestFunction.exists_eventually_eq_one_nhdsSet_tsupport_union φ ψ
  obtain ⟨g, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := 𝓘(ℝ, E)) x (0 : ℝ) η
  -- The `m`-fold commutator of the compression with `g` is the compression of the `m`-fold
  -- commutator `Q` of `D` with the pullback of `g`, an operator of order zero.
  set Q := (smulCommutator ℝ (e.cutoffPullback he χ g) ^ m)
    (D : C^∞⟮𝓘(ℝ, E), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), M; ℝ⟯) with hQ
  have hQ0 := mem_differentialOperators_zero_iff.1 <|
    smulCommutator_pow_mem_differentialOperators (m := 0) (j := m)
      (by rw [zero_add]; exact D.property) (e.cutoffPullback he χ g)
  have hQ1 : Q (e.cutoffPullback he ψ 1) = e.cutoffPullback he ψ 1 * Q 1 := by
    simpa using hQ0 (e.cutoffPullback he ψ 1) 1
  rw [smoothPrincipalSymbol_mvfderiv, coe_chartCompressionDifferentialOperators,
    smulCommutator_pow_chartCompression he hχ.self_of_nhdsSet, ← hQ]
  by_cases hφ : φ x = 0
  · simp [hφ]
  · rw [← mvfderiv_cutoffPullback he g hx
        (hχ.filter_mono (nhds_le_nhdsSet (subset_union_left (subset_tsupport _ hφ)))),
      smoothPrincipalSymbol_mvfderiv, ← hQ]
    simp only [chartCompression_apply, hQ1, ContMDiffMap.coe_mul, Pi.mul_apply,
      cutoffPullback_apply_of_mem he _ _ (e.map_target hx), e.right_inv hx, ContMDiffMap.coe_one,
      Pi.one_apply, mul_one]
    ring

end PrincipalSymbol

/-! ### Complex-valued functions

Operators with complex symbols, such as pseudodifferential operators, act on complex-valued smooth
functions. Their chart compressions use the same real cutoffs, acting on complex values by real
scalar multiplication, and are complex-linear in the operator and in the function. -/

section Complex

/-- **Pulling a complex-valued function on a chart back to the manifold.** For a cutoff `ψ` with
compact support in the target of the chart `e`, the smooth complex-valued function on `M` equal to
`(ψ f) ∘ e` on the chart source and to `0` elsewhere, as a complex-linear map in `f`: the
complexification of `cutoffPullback`. -/
def complexCutoffPullback (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  ContMDiffMap.complexifyLinearMap (e.cutoffPullback he ψ)

/-- The real part of the complex pullback is the pullback of the real part. -/
@[simp]
theorem complexCutoffPullback_re (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯) :
    (e.complexCutoffPullback he ψ f).re = e.cutoffPullback he ψ f.re := by
  ext x
  simp [complexCutoffPullback]

/-- The imaginary part of the complex pullback is the pullback of the imaginary part. -/
@[simp]
theorem complexCutoffPullback_im (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯) :
    (e.complexCutoffPullback he ψ f).im = e.cutoffPullback he ψ f.im := by
  ext x
  simp [complexCutoffPullback]

theorem complexCutoffPullback_apply_of_mem (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯) {x : M} (hx : x ∈ e.source) :
    e.complexCutoffPullback he ψ f x = ψ (e x) • f (e x) := by
  apply Complex.ext <;> simp [complexCutoffPullback, cutoffPullback_apply_of_mem he _ _ hx]

theorem complexCutoffPullback_apply_of_notMem (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯) {x : M} (hx : x ∉ e.source) :
    e.complexCutoffPullback he ψ f x = 0 := by
  simp [complexCutoffPullback, cutoffPullback_apply_of_notMem he _ _ hx]

/-- On the chart source, the complex pullback `(ψ f) ∘ e` multiplied by `g` only sees `f` on the
points of the support of `ψ` read on `M` inside the support of `g`: if `f = ψ₁ • F` for a function
`ψ₁` equal to `1` there, then `g · (ψ f) ∘ e = g · (ψ F) ∘ e`. -/
theorem mul_complexCutoffPullback_apply_of_eq_smul (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    {g : M → ℂ} {ψ₁ : E → ℝ} (hψ₁ : EqOn ψ₁ 1 (tsupport ψ ∩ e.symm ⁻¹' tsupport g))
    {f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯} {F : E → ℂ} (hf : ∀ y, f y = ψ₁ y • F y) {x : M}
    (hx : x ∈ e.source) :
    g x * e.complexCutoffPullback he ψ f x = g x * (ψ (e x) • F (e x)) := by
  rw [complexCutoffPullback_apply_of_mem he _ _ hx, hf, smul_comm (ψ (e x)), mul_smul_comm]
  refine smul_eq_right_of_ne_zero_imp_eq_one fun h ↦ hψ₁ ⟨subset_tsupport _
    (left_ne_zero_of_smul (right_ne_zero_of_mul h)), ?_⟩
  rw [mem_preimage, e.left_inv hx]
  exact subset_tsupport _ (left_ne_zero_of_mul h)

/-- The complex pullback of the constant `1` by a cutoff is the real pullback of `1`, read as a
complex number. -/
theorem complexCutoffPullback_one_apply (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (x : M) :
    e.complexCutoffPullback he ψ 1 x = (e.cutoffPullback he ψ 1 x : ℂ) := by
  by_cases hx : x ∈ e.source
  · simp [complexCutoffPullback_apply_of_mem he _ _ hx, cutoffPullback_apply_of_mem he _ _ hx]
  · simp [complexCutoffPullback_apply_of_notMem he _ _ hx, cutoffPullback_apply_of_notMem he _ _ hx]

/-- The complex pullback `(ψ f) ∘ e` is supported in the image under the inverse of the chart of
the common support of `ψ` and `f`, a compact subset of the chart target. -/
theorem tsupport_complexCutoffPullback_subset_inter (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯) :
    tsupport (e.complexCutoffPullback he ψ f) ⊆ e.symm '' (tsupport ψ ∩ tsupport f) := by
  have hK : IsCompact (tsupport ψ ∩ tsupport f) :=
    ψ.hasCompactSupport.isCompact.inter_right (isClosed_tsupport f)
  refine closure_minimal (fun x hx ↦ ?_) (hK.image_of_continuousOn
    (e.continuousOn_symm.mono (inter_subset_left.trans ψ.tsupport_subset))).isClosed
  have hxs : x ∈ e.source := by_contra fun h ↦ hx (complexCutoffPullback_apply_of_notMem he _ _ h)
  rw [Function.mem_support, complexCutoffPullback_apply_of_mem he _ _ hxs] at hx
  exact ⟨e x, ⟨subset_tsupport _ (left_ne_zero_of_smul hx),
    subset_tsupport _ (right_ne_zero_of_smul hx)⟩, e.left_inv hxs⟩

/-- The complex pullback `(ψ f) ∘ e` is supported in the image of the support of `ψ` under the
inverse of the chart. -/
theorem tsupport_complexCutoffPullback_subset (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯) :
    tsupport (e.complexCutoffPullback he ψ f) ⊆ e.symm '' tsupport ψ :=
  (tsupport_complexCutoffPullback_subset_inter he ψ f).trans (image_mono inter_subset_left)

/-- If a cutoff `χ` in a chart `e` is `1` near the support of a cutoff `ρ`, then on `M` the
supports of `ρ` and of `1 - χ`, read through the chart, are disjoint. -/
theorem disjoint_tsupport_complexCutoffPullback_one_sub {ρ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}
    (hχ : ∀ᶠ y in 𝓝ˢ (tsupport ρ), χ y = 1) :
    Disjoint (tsupport (e.complexCutoffPullback he ρ 1))
      (tsupport ⇑((1 : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯) - e.complexCutoffPullback he χ 1)) := by
  -- `χ = 1` on an open set `N ⊇ supp ρ`, so `1 - χ` vanishes on the open set `e⁻¹(N ∩ target)`.
  obtain ⟨N, hN, hρN, hNχ⟩ := mem_nhdsSet_iff_exists.1 hχ
  have hO : IsOpen (e.symm '' (N ∩ e.target)) :=
    e.symm.isOpen_image_of_subset_source (hN.inter e.open_target) inter_subset_right
  refine Disjoint.mono_left ((tsupport_complexCutoffPullback_subset he ρ 1).trans
      (image_mono (subset_inter hρN ρ.tsupport_subset))) (disjoint_compl_right.mono_right ?_)
  refine closure_minimal (fun q hq hqO ↦ hq ?_) hO.isClosed_compl
  obtain ⟨y, ⟨hyN, hyt⟩, rfl⟩ := hqO
  have hχy : χ y = 1 := hNχ hyN
  simp [complexCutoffPullback_apply_of_mem he _ _ (e.map_target hyt), e.right_inv hyt, hχy]

/-- **Pushing a complex-valued function on the manifold forward to a chart.** For a cutoff `φ`
with compact support in the target of the chart `e`, the smooth complex-valued function
`φ · (h ∘ e⁻¹)` on `E`, which vanishes outside the chart target, as a complex-linear map in
`h`: the complexification of `cutoffPushforward`. -/
def complexCutoffPushforward (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯ :=
  ContMDiffMap.complexifyLinearMap (e.cutoffPushforward he φ)

omit [T2Space M] in
@[simp]
theorem complexCutoffPushforward_apply (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (h : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯) (y : E) :
    e.complexCutoffPushforward he φ h y = φ y • h (e.symm y) := by
  apply Complex.ext <;> simp [complexCutoffPushforward]

/-- The **chart compression** of a complex-linear operator `D` on the complex-valued smooth
functions on `M` by cutoffs `φ` and `ψ` with compact supports in the target of the chart `e`: the
operator `f ↦ φ · (D ((ψ f) ∘ e)) ∘ e⁻¹` on the complex-valued smooth functions on `E`, linear in
`D`. -/
def complexChartCompression (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    (C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯) →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun D := e.complexCutoffPushforward he φ ∘ₗ D ∘ₗ e.complexCutoffPullback he ψ
  map_add' D₁ D₂ := by rw [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c D := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

/-- The chart compression of `D` is `D` between the pullback by `ψ` and the pushforward by `φ`. -/
theorem complexChartCompression_def (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (D : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    e.complexChartCompression he φ ψ D =
      e.complexCutoffPushforward he φ ∘ₗ D ∘ₗ e.complexCutoffPullback he ψ :=
  LinearMap.ext fun _ ↦ rfl

@[simp]
theorem complexChartCompression_apply (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (D : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯)
    (f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯) (y : E) :
    e.complexChartCompression he φ ψ D f y = φ y • D (e.complexCutoffPullback he ψ f) (e.symm y) :=
  e.complexCutoffPushforward_apply he φ _ y

/-- The chart compression of the complexification of a real-linear operator `D` on the
real-valued smooth functions on `M` is the complexification of the chart compression of `D`. -/
theorem complexChartCompression_complexifyLinearMap (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (D : C^∞⟮𝓘(ℝ, E), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), M; ℝ⟯) :
    e.complexChartCompression he φ ψ (ContMDiffMap.complexifyLinearMap D) =
      ContMDiffMap.complexifyLinearMap (e.chartCompression he φ ψ D) := by
  ext f y
  apply Complex.ext <;> simp

/-- The chart compression commutes with complex conjugation of operators, `D ↦ conj ∘ D ∘ conj`:
the cutoffs are real, so pulling back and pushing forward through them commutes with conjugation. -/
theorem complexChartCompression_intrinsicConj (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (D : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    e.complexChartCompression he φ ψ (ContMDiffMap.intrinsicConj D) =
      ContMDiffMap.intrinsicConj (e.complexChartCompression he φ ψ D) := by
  simp only [complexChartCompression, complexCutoffPushforward, complexCutoffPullback,
    LinearMap.coe_mk, AddHom.coe_mk, ContMDiffMap.intrinsicConj_comp,
    ContMDiffMap.intrinsicConj_complexifyLinearMap]

section Diffeomorph

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N]

/-- **Chart compressions under a diffeomorphism.** Transport an operator `D` on the complex-valued
smooth functions on `N` to `M` along a diffeomorphism `Φ : M → N`, by conjugation with the pullback
`f ↦ f ∘ Φ`. Its chart compression in a chart `e` of `M` is the chart compression of `D`, by the
same cutoffs, in the chart `e ∘ Φ⁻¹` of `N`, which has the same target as `e`. -/
theorem complexChartCompression_conj (Φ : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ N)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (D : C^∞⟮𝓘(ℝ, E), N; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮𝓘(ℝ, E), N; 𝓘(ℝ, ℂ), ℂ⟯) :
    e.complexChartCompression he φ ψ (Φ.compRightComplexAlgEquiv.toLinearEquiv.conj D) =
      (Φ.symm.toHomeomorph.transOpenPartialHomeomorph e).complexChartCompression
        (Φ.symm.transOpenPartialHomeomorph_mem_maximalAtlas le_rfl he) φ ψ D := by
  have he' := Φ.symm.transOpenPartialHomeomorph_mem_maximalAtlas le_rfl he
  -- Pulling back through `e` and then along `Φ⁻¹` is pulling back through `e ∘ Φ⁻¹`. The cutoff
  -- `ψ` lives on `e.target`, which is the target of `e ∘ Φ⁻¹` only up to unfolding, so the two
  -- pullbacks are compared by explicit terms rather than by rewriting.
  have hpull (f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯) :
      Φ.compRightComplexAlgEquiv.symm (e.complexCutoffPullback he ψ f) =
        (Φ.symm.toHomeomorph.transOpenPartialHomeomorph e).complexCutoffPullback he' ψ f := by
    ext z
    by_cases hz : Φ.symm z ∈ e.source
    · exact ((Φ.compRightComplexAlgEquiv_symm_apply _ z).trans
        (complexCutoffPullback_apply_of_mem he ψ f hz)).trans
          (complexCutoffPullback_apply_of_mem he' ψ f hz).symm
    · exact ((Φ.compRightComplexAlgEquiv_symm_apply _ z).trans
        (complexCutoffPullback_apply_of_notMem he ψ f hz)).trans
          (complexCutoffPullback_apply_of_notMem he' ψ f hz).symm
  ext f y
  refine (complexChartCompression_apply he φ ψ _ f y).trans
    (Eq.trans ?_ (complexChartCompression_apply he' φ ψ D f y).symm)
  rw [LinearEquiv.conj_apply_apply, AlgEquiv.toLinearEquiv_apply,
    Diffeomorph.compRightComplexAlgEquiv_apply]
  exact congrArg₂ (fun g z ↦ φ y • D g z) (hpull f) (by simp)

end Diffeomorph

/-! ### Changing the chart and composing -/

/-- **Changing the chart of a pullback.** If two charts have the same inverse on the support of
the cutoff `ψ`, read as a test function on both chart targets, then pulling back through either
chart gives the same function on `M`. -/
theorem complexCutoffPullback_congr {e' : OpenPartialHomeomorph M E}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}
    {ψ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)} (hψ : (ψ : E → ℝ) = ψ')
    (h : EqOn e.symm e'.symm (tsupport ψ)) :
    e.complexCutoffPullback he ψ = e'.complexCutoffPullback he' ψ' := by
  have hts : tsupport (ψ : E → ℝ) = tsupport ψ' := by rw [hψ]
  have h₁ : tsupport ψ ⊆ e'.target := hts ▸ ψ'.tsupport_subset
  have h₂ : tsupport ψ' ⊆ e.target := hts ▸ ψ.tsupport_subset
  have h' : EqOn e'.symm e.symm (tsupport ψ') := hts ▸ h.symm
  ext f x
  by_cases hx : x ∈ e.source ∧ e x ∈ tsupport ψ
  · obtain ⟨hx', hex⟩ := mem_source_and_apply_eq_of_eqOn_symm h₁ h hx.1 hx.2
    rw [complexCutoffPullback_apply_of_mem he _ _ hx.1,
      complexCutoffPullback_apply_of_mem he' _ _ hx', hex, hψ]
  by_cases hx' : x ∈ e'.source ∧ e' x ∈ tsupport ψ'
  · obtain ⟨hxe, hex⟩ := mem_source_and_apply_eq_of_eqOn_symm h₂ h' hx'.1 hx'.2
    exact absurd ⟨hxe, hex ▸ hts ▸ hx'.2⟩ hx
  -- Away from the chart preimages of the supports, both pullbacks vanish.
  have hzero : ∀ {e'' : OpenPartialHomeomorph M E}
      (he'' : e'' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (χ : 𝓓(⟨e''.target, e''.open_target⟩, ℝ)),
      ¬(x ∈ e''.source ∧ e'' x ∈ tsupport χ) → e''.complexCutoffPullback he'' χ f x = 0 := by
    intro e'' he'' χ hχ
    by_cases hxs : x ∈ e''.source
    · rw [complexCutoffPullback_apply_of_mem he'' _ _ hxs,
        image_eq_zero_of_notMem_tsupport fun h ↦ hχ ⟨hxs, h⟩, zero_smul]
    · exact complexCutoffPullback_apply_of_notMem he'' _ _ hxs
  rw [hzero he ψ hx, hzero he' ψ' hx']

omit [T2Space M] in
/-- **Changing the chart of a pushforward.** If two charts have the same inverse on the support of
the cutoff `φ`, read as a test function on both chart targets, then pushing forward through either
chart gives the same function. -/
theorem complexCutoffPushforward_congr {e' : OpenPartialHomeomorph M E}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}
    {φ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)} (hφ : (φ : E → ℝ) = φ')
    (h : EqOn e.symm e'.symm (tsupport φ)) :
    e.complexCutoffPushforward he φ = e'.complexCutoffPushforward he' φ' := by
  ext g y
  rw [complexCutoffPushforward_apply, complexCutoffPushforward_apply, ← hφ]
  by_cases hy : φ y = 0
  · simp [hy]
  · rw [h (subset_tsupport _ hy)]

/-- **Changing the chart of a chart compression.** If two charts have the same inverse on the
supports of the cutoffs `φ` and `ψ`, read as test functions on both chart targets, the chart
compressions of every operator in the two charts agree. -/
theorem complexChartCompression_congr {e' : OpenPartialHomeomorph M E}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}
    {φ' ψ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)} (hφ : (φ : E → ℝ) = φ')
    (hψ : (ψ : E → ℝ) = ψ') (h : EqOn e.symm e'.symm (tsupport φ ∪ tsupport ψ)) :
    e.complexChartCompression he φ ψ = e'.complexChartCompression he' φ' ψ' := by
  ext D : 1
  rw [complexChartCompression_def, complexChartCompression_def,
    complexCutoffPushforward_congr he he' hφ (h.mono subset_union_left),
    complexCutoffPullback_congr he he' hψ (h.mono subset_union_right)]

/-- Pushing a function forward by a cutoff `χ` and pulling it back by `χ` again gives the function
back when it is supported in the chart source, at points where `χ` equals `1`. -/
theorem complexCutoffPullback_complexCutoffPushforward (χ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    {g : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯} (hg : ∀ x, g x ≠ 0 → x ∈ e.source ∧ χ (e x) = 1) :
    e.complexCutoffPullback he χ (e.complexCutoffPushforward he χ g) = g := by
  ext x
  by_cases hx : x ∈ e.source
  · rw [complexCutoffPullback_apply_of_mem he _ _ hx, complexCutoffPushforward_apply,
      e.left_inv hx]
    by_cases hgx : g x = 0
    · simp [hgx]
    · simp [(hg x hgx).2]
  · rw [complexCutoffPullback_apply_of_notMem he _ _ hx]
    by_contra hgx
    exact hx (hg x (Ne.symm hgx)).1

/-- **Chart compressions of a composition.** If a cutoff `χ` equals `1` at the chart images of
the points where `B` applied to the pullback of `f` does not vanish, which all lie in the chart
source, the compression of `A ∘ B` by `φ` and `ψ` applied to `f` is the compression of `A` by `φ`
and `χ` applied to the compression of `B` by `χ` and `ψ` applied to `f`. -/
theorem complexChartCompression_comp_apply (φ ψ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (A B : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯)
    {f : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℂ), ℂ⟯}
    (hB : ∀ x, B (e.complexCutoffPullback he ψ f) x ≠ 0 → x ∈ e.source ∧ χ (e x) = 1) :
    e.complexChartCompression he φ ψ (A ∘ₗ B) f =
      e.complexChartCompression he φ χ A (e.complexChartCompression he χ ψ B f) := by
  simp only [complexChartCompression_def, LinearMap.comp_apply,
    complexCutoffPullback_complexCutoffPushforward he χ hB]

end Complex

end OpenPartialHomeomorph

/-! ### Chart cutoffs summing to one -/

section ChartPartition

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **Chart cutoffs summing to one on a compact set.** A compact set `K` of a Hausdorff manifold
modelled on a finite-dimensional space has finitely many points `cᵢ` and cutoffs `ρᵢ` with compact
supports in the targets of the preferred charts at the `cᵢ` such that the functions
`ρᵢ ∘ chartAt cᵢ`, extended by `0` off the chart sources (`OpenPartialHomeomorph.cutoffPullback`),
add up to `1` on `K`. These are the cutoffs through which operators on `M` are assembled from
operators in charts. -/
theorem IsCompact.exists_sum_cutoffPullback_eq_one {K : Set M} (hK : IsCompact K) :
    ∃ (N : ℕ) (c : Fin N → M)
      (ρ : ∀ i, 𝓓(⟨(chartAt E (c i)).target, (chartAt E (c i)).open_target⟩, ℝ)),
      ∀ y ∈ K, ∑ i, (chartAt E (c i)).cutoffPullback (IsManifold.chart_mem_maximalAtlas (c i))
        (ρ i) 1 y = 1 := by
  obtain ⟨ι, _, fs, -⟩ := hK.exists_smoothBumpCovering_isSubordinate 𝓘(ℝ, E)
    (U := fun _ ↦ univ) fun _ _ ↦ univ_mem
  set f := fs.toSmoothPartitionOfUnity
  -- The partition function `fᵢ` is supported in the compact support of the bump function at `cᵢ`,
  -- which lies in the source of the chart at `cᵢ`.
  have hf (i : ι) : tsupport (f i) ⊆ tsupport (fs i) :=
    closure_mono (fs.support_toSmoothPartitionOfUnity_subset i)
  have hfe (i : ι) : tsupport (f i) ⊆ (chartAt E (fs.c i)).source :=
    (hf i).trans (fs i).tsupport_subset_chartAt_source
  have hK' (i : ι) : IsCompact (chartAt E (fs.c i) '' tsupport (f i)) :=
    ((fs i).hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport _)
      (hf i)).image_of_continuousOn ((chartAt E (fs.c i)).continuousOn.mono (hfe i))
  -- In the chart at `cᵢ`, `ρᵢ` is `fᵢ ∘ (chartAt cᵢ)⁻¹` times a cutoff equal to `1` on the image of
  -- the support of `fᵢ`.
  choose θ hθ using fun i ↦ TestFunction.exists_eventually_eq_one
    (Ω := ⟨(chartAt E (fs.c i)).target, (chartAt E (fs.c i)).open_target⟩) (n := ⊤) (hK' i)
    (image_subset_iff.2 fun y hy ↦ (chartAt E (fs.c i)).map_source (hfe i hy))
  have hg (i : ι) : ContDiffOn ℝ ∞ (f i ∘ (chartAt E (fs.c i)).symm) (chartAt E (fs.c i)).target :=
    contMDiffOn_iff_contDiffOn.1 ((f i).contMDiff.comp_contMDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (fs.c i))))
  have hρ (i : ι) (y : M) : (chartAt E (fs.c i)).cutoffPullback
      (IsManifold.chart_mem_maximalAtlas (fs.c i))
      (TestFunction.smulLeftCLMOfContDiffOn (hg i) (θ i)) 1 y = f i y := by
    by_cases hy : y ∈ (chartAt E (fs.c i)).source
    · rw [OpenPartialHomeomorph.cutoffPullback_one_apply_of_mem _ _ hy,
        TestFunction.smulLeftCLMOfContDiffOn_apply, Function.comp_apply,
        (chartAt E (fs.c i)).left_inv hy, smul_eq_mul]
      by_cases hfy : f i y = 0
      · rw [hfy, zero_mul]
      · rw [(hθ i).1.self_of_nhdsSet _ (mem_image_of_mem _ (subset_tsupport _ hfy)), mul_one]
    · rw [OpenPartialHomeomorph.cutoffPullback_apply_of_notMem _ _ _ hy,
        image_eq_zero_of_notMem_tsupport fun h ↦ hy (hfe i h)]
  -- Index the finitely many charts by `Fin N`.
  set σ := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j ↦ fs.c (σ.symm j),
    fun j ↦ TestFunction.smulLeftCLMOfContDiffOn (hg (σ.symm j)) (θ (σ.symm j)), fun y hy ↦ ?_⟩
  rw [← f.sum_eq_one hy, finsum_eq_sum_of_fintype, ← σ.symm.sum_comp]
  exact Finset.sum_congr rfl fun j _ ↦ hρ (σ.symm j) y

namespace TauCeti

/-- **Chart cutoffs whose squares sum to one.** A Hausdorff σ-compact manifold modelled on a
finite-dimensional space has points `cᵢ` and cutoffs `χᵢ` with compact supports in the targets of
the preferred charts at the `cᵢ`, such that the chart preimages `(chartAt cᵢ)⁻¹(supp χᵢ)` form a
locally finite family and the squares of the functions `χᵢ ∘ chartAt cᵢ`, extended by `0` off the
chart sources (`OpenPartialHomeomorph.cutoffPullback`), add up to `1` everywhere. Such cutoffs
glue operators `Pᵢ` in the charts symmetrically, as `∑ᵢ χᵢ Pᵢ χᵢ`. -/
theorem exists_locallyFinite_finsum_sq_cutoffPullback_eq_one [SigmaCompactSpace M] :
    ∃ (ι : Type u) (c : ι → M)
      (χ : ∀ i, 𝓓(⟨(chartAt E (c i)).target, (chartAt E (c i)).open_target⟩, ℝ)),
      (LocallyFinite fun i ↦ (chartAt E (c i)).symm '' tsupport (χ i)) ∧
        ∀ y, ∑ᶠ i, (chartAt E (c i)).cutoffPullback (IsManifold.chart_mem_maximalAtlas (c i))
          (χ i) 1 y ^ 2 = 1 := by
  obtain ⟨ι, fs, -⟩ := SmoothBumpCovering.exists_isSubordinate 𝓘(ℝ, E)
    (isClosed_univ : IsClosed (univ : Set M)) (U := fun _ ↦ univ) fun _ _ ↦ univ_mem
  -- Normalize the partition of unity of the bump covering to a square partition `gᵢ`. Each `gᵢ`
  -- is supported in the compact support of the bump function at `cᵢ`, inside the chart source.
  set g := fs.toSmoothPartitionOfUnity.sqrtNormalized
  have hg (i : ι) : tsupport (g i) ⊆ tsupport (fs i) := by
    rw [SmoothPartitionOfUnity.tsupport_sqrtNormalized]
    exact closure_mono (fs.support_toSmoothPartitionOfUnity_subset i)
  choose χ hχ using fun i ↦ (chartAt E (fs.c i)).exists_cutoffPullback_one_eq
    (IsManifold.chart_mem_maximalAtlas (fs.c i))
    ((fs i).hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport _) (hg i))
    ((hg i).trans (fs i).tsupport_subset_chartAt_source)
  refine ⟨ι, fs.c, χ, fs.locallyFinite.closure.subset fun i ↦ ?_, fun y ↦ ?_⟩
  · rw [← OpenPartialHomeomorph.tsupport_cutoffPullback_one
      (IsManifold.chart_mem_maximalAtlas (fs.c i)), hχ i]
    exact hg i
  · simp_rw [hχ]
    exact fs.toSmoothPartitionOfUnity.sum_sq_sqrtNormalized_eq_one (mem_univ y)

end TauCeti

end ChartPartition
