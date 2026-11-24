/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Basic
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.MFDeriv.Localized
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

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

## Main definitions

* `OpenPartialHomeomorph.cutoffPullback`: `f ↦ (ψ f) ∘ e`, extended by zero, as a linear map
  `C^∞(E) → C^∞(M)`.
* `OpenPartialHomeomorph.cutoffPushforward`: `h ↦ φ · (h ∘ e⁻¹)`, as a linear map
  `C^∞(M) → C^∞(E)`.
* `OpenPartialHomeomorph.chartCompression`: the chart compression of an operator on `C^∞(M)`.
* `OpenPartialHomeomorph.chartCompressionDifferentialOperators`: the chart compression of
  differential operators of order at most `m`.

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

end OpenPartialHomeomorph
