/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.NormalizedChart
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.EuclideanMetric
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local.Basic
-- Private: used only inside proofs.
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic

/-!
# Metrics that are Euclidean in normalized Morse coordinates

A `TauCeti.MorseChart` writes a function as `f = f x + (1/2) Σᵢ wᵢ zᵢ²` with weights `wᵢ = ±1`,
while its normalized chart `ψ` (`TauCeti.MorseChart.normalizedChart`) writes it as

`f = f x - |v⁻|² + |v⁺|²`,

the coordinates `v⁻` of negative weight first. This file treats the metrics which are the
Euclidean metric of the normalized coordinates near the critical points
(`TauCeti.MorseChart.IsNormalizedEuclidean`). Wehrheim's standard metrics near the critical
points, used to construct smooth structures on Morse trajectory spaces by gluing, are stated in the
half-quadratic convention of the Euclidean metric of a Morse chart
(`TauCeti.MorseChart.IsEuclidean`). The metrics here are their normalized-coordinate version, half
the Euclidean metric of the chart, and their conventions differ from the half-quadratic ones by
factors of `2`, such as the time conversion `T = 2t`, which this file makes explicit.

* The normalized coordinates are `zᵢ / √2`, reordered, so the Euclidean metric of the normalized
  coordinates is half that of the chart coordinates
  (`TauCeti.MorseChart.isNormalizedEuclidean_iff_euclideanForm`).
* So the negative gradient of `f` is twice the linear field `z ↦ (-wᵢ zᵢ)ᵢ` of the chart
  (`TauCeti.MorseChart.IsNormalizedEuclidean.neg_mgradient_eq_two_smul_field`); in normalized
  coordinates it is `(2 v⁻, -2 v⁺)`
  (`TauCeti.MorseChart.IsNormalizedEuclidean.normalizedCoord_mfderiv_neg_mgradient`), and its flow
  is the linear flow `(v⁻, v⁺) ↦ (e^{2t} v⁻, e^{-2t} v⁺)`
  (`TauCeti.normalizedLinearFlow`), with rates `±2`.
* Consequently the negative gradient is not itself an adapted pseudo-gradient, whose rates are
  `±1`, but half of it is (`TauCeti.isAdaptedPseudoGradient_inv_two_smul_neg_mgradient`), being
  the linear field of the chart
  (`TauCeti.MorseChart.IsNormalizedEuclidean.coord_mfderiv_inv_two_smul_neg_mgradient`). Its
  integral curves are the orbits of the flow of this adapted pseudo-gradient run at double speed
  (`TauCeti.IsAdaptedPseudoGradient.flow_mul_eq_of_isMIntegralCurve`): a time `t` of the negative
  gradient flow is the time `T = 2t` of the half-quadratic convention, and `e^{-T} = e^{-2t}`
  (`TauCeti.MorseChart.normalizedCoord_coord_symm_linearFlow`). Near a critical point, in normalized
  coordinates, every integral curve of the negative gradient runs along the linear flow
  (`TauCeti.MorseChart.IsNormalizedEuclidean.normalizedChart_eq_normalizedLinearFlow`).
* Such metrics exist: a smooth function whose critical points in a compact set are nondegenerate
  has Morse charts at them, with sources of pairwise disjoint closures, and a smooth metric which
  is the Euclidean metric of the normalized coordinates on each whole source, in particular on
  every closed ball of normalized coordinates inside it
  (`IsCompact.exists_contMDiffRiemannianMetric_isNormalizedEuclidean`). For a Morse function on a
  compact manifold this gives a metric whose halved negative gradient is an adapted
  pseudo-gradient (`TauCeti.IsMorse.exists_contMDiffRiemannianMetric_isNormalizedEuclidean`).

## Main declarations

* `TauCeti.normalizedLinearFlow`: the linear flow `(v⁻, v⁺) ↦ (e^{2t} v⁻, e^{-2t} v⁺)`.
* `TauCeti.MorseChart.IsNormalizedEuclidean`: the metric is the Euclidean metric of the normalized
  coordinates of a Morse chart, with `TauCeti.MorseChart.isNormalizedEuclidean_iff_euclideanForm`.
* `TauCeti.MorseChart.IsNormalizedEuclidean.normalizedCoord_mfderiv_neg_mgradient`: the negative
  gradient is `(2 v⁻, -2 v⁺)` in normalized coordinates.
* `TauCeti.isAdaptedPseudoGradient_inv_two_smul_neg_mgradient`: half the negative gradient is an
  adapted pseudo-gradient.
* `TauCeti.MorseChart.normalizedCoord_coord_symm_linearFlow`: the half-quadratic linear flow at
  time `2t` is the normalized linear flow at time `t`.
* `TauCeti.MorseChart.IsNormalizedEuclidean.normalizedChart_eq_normalizedLinearFlow`: integral
  curves of the negative gradient follow the normalized linear flow in a normalized chart.
* `IsCompact.exists_contMDiffRiemannianMetric_isNormalizedEuclidean`: such metrics exist near the
  critical points in a compact set.

## References

* K. Wehrheim, *Smooth structures on Morse trajectory spaces, featuring finite ends and associative
  gluing*, Geom. Topol. Monogr. **18** (2012), [arXiv:1205.0713](https://arxiv.org/abs/1205.0713),
  Definition 1.1 and Theorem 2.6 (Morse–Smale pairs Euclidean in Morse coordinates near the
  critical points, in the half-quadratic convention, and their gluing parameters).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.2.
-/

public section

open Bundle Function Set TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

/-! ### The normalized linear flow -/

section LinearFlow

variable {n : ℕ}

/-- The **normalized linear flow** `(v⁻, v⁺) ↦ (e^{2t} v⁻, e^{-2t} v⁺)` on `ℝⁿ`, where `v⁻` are
the first `k` coordinates. It is the flow of the field `(2 v⁻, -2 v⁺)`
(`TauCeti.hasDerivAt_normalizedLinearFlow`), the negative Euclidean gradient of the model
function `-|v⁻|² + |v⁺|²` of a normalized Morse chart. -/
noncomputable def normalizedLinearFlow (k : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i ↦ Real.exp (if i.val < k then 2 * t else -(2 * t)) * v i

/-- The coordinates of the normalized linear flow. -/
@[simp]
theorem normalizedLinearFlow_apply (k : ℕ) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    normalizedLinearFlow k t v i = Real.exp (if i.val < k then 2 * t else -(2 * t)) * v i :=
  (rfl)

/-- At time zero the normalized linear flow is the identity. -/
@[simp]
theorem normalizedLinearFlow_zero (k : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    normalizedLinearFlow k 0 v = v := by
  ext i
  simp

/-- The flow law of the normalized linear flow. -/
theorem normalizedLinearFlow_add (k : ℕ) (s t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    normalizedLinearFlow k (s + t) v = normalizedLinearFlow k s (normalizedLinearFlow k t v) := by
  ext i
  simp only [normalizedLinearFlow_apply, ← mul_assoc, ← Real.exp_add]
  split_ifs <;> ring_nf

/-- **The normalized linear flow has rates `±2`**: it solves `v' = (2 v⁻, -2 v⁺)`. -/
theorem hasDerivAt_normalizedLinearFlow (k : ℕ) (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun t ↦ normalizedLinearFlow k t v)
      (WithLp.toLp 2 fun i ↦ (if i.val < k then 2 else -2) * normalizedLinearFlow k t v i) t := by
  have hg : HasDerivAt (fun t ↦ fun i : Fin n ↦ Real.exp (if i.val < k then 2 * t else -(2 * t)) *
      v i) (fun i ↦ (if i.val < k then 2 else -2) * normalizedLinearFlow k t v i) t := by
    refine hasDerivAt_pi.2 fun i ↦ ?_
    simp only [normalizedLinearFlow_apply]
    split_ifs
    · convert (((hasDerivAt_id' t).const_mul 2).exp).mul_const (v i) using 1
      ring
    · convert (((hasDerivAt_id' t).const_mul 2).neg.exp).mul_const (v i) using 1
      simp only [Pi.neg_apply]
      ring
  exact (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n ↦ ℝ).symm.hasFDerivAt.comp_hasDerivAt t hg

end LinearFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}

namespace MorseChart

/-! ### The Euclidean metric of the normalized coordinates -/

section NormalizedCoord

variable (φ : MorseChart E f x)

/-- **Half-quadratic time is twice normalized time.** In normalized coordinates, the linear flow
`z ↦ (e^{-wᵢ s} zᵢ)ᵢ` of a Morse chart at time `s = 2t` is the normalized linear flow
`(v⁻, v⁺) ↦ (e^{2t} v⁻, e^{-2t} v⁺)` at time `t`. -/
theorem normalizedCoord_coord_symm_linearFlow (t : ℝ) (v : E) :
    φ.normalizedCoord (φ.coord.symm (φ.linearFlow (2 * t) (φ.coord v))) =
      normalizedLinearFlow (manifoldMorseIndex 𝓘(ℝ, E) f x) t (φ.normalizedCoord v) := by
  ext i
  rw [normalizedCoord_apply, LinearEquiv.apply_symm_apply, linearFlow_apply, φ.weight_sort_apply,
    normalizedLinearFlow_apply, normalizedCoord_apply]
  split_ifs <;> ring_nf

variable [RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y)]

/-- The metric is **Euclidean in the normalized coordinates** of the Morse chart `φ` when, on the
source of the chart, it is the Euclidean inner product of the normalized coordinates of tangent
vectors, read through the differential of the chart. -/
def IsNormalizedEuclidean : Prop :=
  ∀ y ∈ φ.toChart.source, ∀ v w : TangentSpace 𝓘(ℝ, E) y,
    inner ℝ v w = inner ℝ (φ.normalizedCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y v))
      (φ.normalizedCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y w))

/-- The defining property of a Morse chart in whose normalized coordinates the metric is
Euclidean. -/
theorem isNormalizedEuclidean_iff : φ.IsNormalizedEuclidean ↔
    ∀ y ∈ φ.toChart.source, ∀ v w : TangentSpace 𝓘(ℝ, E) y,
      inner ℝ v w = inner ℝ (φ.normalizedCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y v))
        (φ.normalizedCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y w)) :=
  Iff.rfl

/-- **The normalized Euclidean metric is half the Euclidean metric of the chart**: a metric is
Euclidean in the normalized coordinates of a Morse chart exactly when it is half the Euclidean
metric `TauCeti.MorseChart.euclideanForm` of the chart on its source. -/
theorem isNormalizedEuclidean_iff_euclideanForm : φ.IsNormalizedEuclidean ↔
    ∀ y ∈ φ.toChart.source, ∀ v w : TangentSpace 𝓘(ℝ, E) y,
      inner ℝ v w = 2⁻¹ * φ.euclideanForm y v w := by
  refine forall₂_congr fun y _ ↦ forall₂_congr fun v w ↦ ?_
  rw [φ.inner_normalizedCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y v)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y w), euclideanForm_apply]

variable {φ}

/-- In a Morse chart in whose normalized coordinates the metric is Euclidean, the metric is the
inner product of the normalized coordinates. -/
theorem IsNormalizedEuclidean.inner_eq (hφ : φ.IsNormalizedEuclidean) {y : M}
    (hy : y ∈ φ.toChart.source) (v w : TangentSpace 𝓘(ℝ, E) y) :
    inner ℝ v w = inner ℝ (φ.normalizedCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y v))
      (φ.normalizedCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y w)) :=
  hφ y hy v w

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **In normalized Euclidean coordinates the negative gradient is twice the linear field** of the
Morse chart, `z ↦ (-2 wᵢ zᵢ)ᵢ` in the chart coordinates. -/
theorem IsNormalizedEuclidean.neg_mgradient_eq_two_smul_field (hφ : φ.IsNormalizedEuclidean)
    {y : M} (hy : y ∈ φ.toChart.source) : -mgradient 𝓘(ℝ, E) f y = (2 : ℝ) • φ.field y := by
  have h : -((2 : ℝ) • φ.field y) = mgradient 𝓘(ℝ, E) f y := eq_mgradient_iff.2 fun v ↦ by
    rw [φ.isNormalizedEuclidean_iff_euclideanForm.1 hφ y hy, map_neg, map_smul,
      neg_apply, smul_apply,
      φ.euclideanForm_apply_left_eq_neg_mvfderiv (fun _ hz ↦ φ.coord_mfderiv_field hz) hy,
      smul_eq_mul]
    ring
  rw [← h, neg_neg]

/-- **In normalized Euclidean coordinates half the negative gradient is the linear field** of the
Morse chart: its chart coordinates are `z ↦ (-wᵢ zᵢ)ᵢ`. -/
theorem IsNormalizedEuclidean.coord_mfderiv_inv_two_smul_neg_mgradient
    (hφ : φ.IsNormalizedEuclidean) {y : M} (hy : y ∈ φ.toChart.source) :
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y ((2⁻¹ : ℝ) • -mgradient 𝓘(ℝ, E) f y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i) := by
  rw [hφ.neg_mgradient_eq_two_smul_field hy, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul,
    φ.coord_mfderiv_field hy]

/-- **The negative gradient in normalized coordinates is `(2 v⁻, -2 v⁺)`**, where `v = ψ y` are
the normalized coordinates of the point and `v⁻` its first `λ` coordinates, `λ` the Morse
index. -/
theorem IsNormalizedEuclidean.normalizedCoord_mfderiv_neg_mgradient
    (hφ : φ.IsNormalizedEuclidean) {y : M} (hy : y ∈ φ.toChart.source)
    (i : Fin (Module.finrank ℝ E)) :
    φ.normalizedCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (-mgradient 𝓘(ℝ, E) f y)) i =
      (if i.val < manifoldMorseIndex 𝓘(ℝ, E) f x then 2 else -2) * φ.normalizedChart y i := by
  -- The computation in `E`, for a vector `a` with the chart coordinates of the linear field.
  have key (a : E) (ha : φ.coord a = fun j ↦ -(φ.weight j * φ.coord (φ.toChart y) j)) :
      φ.normalizedCoord ((2 : ℝ) • a) i =
        (if i.val < manifoldMorseIndex 𝓘(ℝ, E) f x then 2 else -2) * φ.normalizedChart y i := by
    rw [map_smul, PiLp.smul_apply, normalizedCoord_apply, ha, normalizedChart_apply,
      normalizedCoord_apply, smul_eq_mul]
    beta_reduce
    rw [φ.weight_sort_apply]
    split_ifs <;> ring
  -- `dψ` acts on tangent spaces and the normalized coordinates on `E`, so the scalar is moved
  -- through `dψ` before the computation in `E`.
  rw [hφ.neg_mgradient_eq_two_smul_field hy]
  exact (congrArg (fun b ↦ φ.normalizedCoord b i) (map_smul _ _ _)).trans
    (key _ (φ.coord_mfderiv_field hy))

end NormalizedCoord

end MorseChart

/-! ### Half the negative gradient is an adapted pseudo-gradient -/

section Adapted

variable [RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y)] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **Half the negative gradient is an adapted pseudo-gradient** for a smooth function `f` and a
smooth metric that is Euclidean in the normalized coordinates of a Morse chart at each critical
point of `f`. The negative gradient itself has rates `±2` near the critical points, while adapted
pseudo-gradients have rates `±1`. -/
theorem isAdaptedPseudoGradient_inv_two_smul_neg_mgradient
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hφ : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
      ∃ φ : MorseChart E f x, φ.IsNormalizedEuclidean) :
    IsAdaptedPseudoGradient f fun y ↦ (2⁻¹ : ℝ) • -mgradient 𝓘(ℝ, E) f y where
  contMDiff := by
    have : IsManifold 𝓘(ℝ, E) (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
    exact ContMDiff.const_smul_section (contMDiff_neg_mgradient (n := ∞) hf)
  mvfderiv_apply_lt_zero y hy := by
    have hg : mgradient 𝓘(ℝ, E) f y ≠ 0 := by
      rwa [ne_eq, mgradient_eq_zero_iff, mvfderiv_eq_zero_iff]
    rw [map_smul, map_neg, mvfderiv_apply_mgradient, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (by norm_num) (neg_lt_zero.2 (real_inner_self_pos.2 hg))
  exists_morseChart x hx := by
    obtain ⟨φ, hφ⟩ := hφ x hx
    exact ⟨φ, fun y hy ↦ hφ.coord_mfderiv_inv_two_smul_neg_mgradient hy⟩

end Adapted

/-! ### The normalized negative gradient flow -/

namespace MorseChart

variable [RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y)] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] {φ : MorseChart E f x}

/-- **The flow in normalized coordinates.** Let the metric be Euclidean in the normalized
coordinates `ψ` of the Morse chart `φ`, and let `X = (1/2) (-grad f)` be adapted. If the
normalized linear flow of `ψ y` stays in the chart between the times `0` and `t`, then the flow of
`X` at time `2t`, which is the negative gradient flow at time `t`, moves `y` to the point with
normalized coordinates `(e^{2t} v⁻, e^{-2t} v⁺)`, where `v = ψ y`. -/
theorem IsNormalizedEuclidean.normalizedChart_flow_two_mul
    (hX : IsAdaptedPseudoGradient f fun y ↦ (2⁻¹ : ℝ) • -mgradient 𝓘(ℝ, E) f y)
    (hφ : φ.IsNormalizedEuclidean) {y : M} (hy : y ∈ φ.toChart.source) {t : ℝ}
    (ht : ∀ s ∈ uIcc 0 t, normalizedLinearFlow (manifoldMorseIndex 𝓘(ℝ, E) f x) s
      (φ.normalizedChart y) ∈ φ.normalizedChart.target) :
    φ.normalizedChart (hX.flow (2 * t) y) =
      normalizedLinearFlow (manifoldMorseIndex 𝓘(ℝ, E) f x) t (φ.normalizedChart y) := by
  set z := φ.coord (φ.toChart y)
  -- The linear orbit of `z` at time `2 s` is the normalized linear orbit of `ψ y` at time `s`.
  have hlin (s : ℝ) : φ.coord.symm (φ.linearFlow (2 * s) z) =
      φ.normalizedCoord.symm (normalizedLinearFlow (manifoldMorseIndex 𝓘(ℝ, E) f x) s
        (φ.normalizedChart y)) := by
    rw [normalizedChart_apply, ← normalizedCoord_coord_symm_linearFlow,
      ContinuousLinearEquiv.symm_apply_apply]
  have hmem {s : ℝ} (hs : s ∈ uIcc 0 t) : φ.coord.symm (φ.linearFlow (2 * s) z) ∈
      φ.toChart.target := by
    rw [hlin]
    simpa only [normalizedChart_target, mem_preimage] using ht s hs
  -- `X` is the linear field of the chart.
  have hXφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y
      ((2⁻¹ : ℝ) • -mgradient 𝓘(ℝ, E) f y)) = fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i) :=
    fun _ hy ↦ hφ.coord_mfderiv_inv_two_smul_neg_mgradient hy
  have hyz : y = φ.toChart.symm (φ.coord.symm z) := by
    rw [LinearEquiv.symm_apply_apply, φ.toChart.left_inv hy]
  have hflow := hX.flow_toChart_symm_of_forall_mem_uIcc φ hXφ (z := z) (t := 2 * t) fun s hs ↦ by
    have hs' : s / 2 ∈ uIcc 0 t := by
      have h := mem_image_of_mem (· / 2) hs
      rwa [image_div_const_uIcc, zero_div, mul_div_cancel_left₀ t two_ne_zero] at h
    simpa only [mul_div_cancel₀ s two_ne_zero] using hmem hs'
  rw [← hyz] at hflow
  rw [hflow, normalizedChart_apply, φ.toChart.right_inv (hmem right_mem_uIcc), hlin,
    ContinuousLinearEquiv.apply_symm_apply]

/-- **Integral curves of the normalized negative gradient follow the normalized linear flow.** Let
the metric be Euclidean in the normalized coordinates `ψ` of the Morse chart `φ`, with
`(1/2) (-grad f)` adapted, and let `γ` be an integral curve of `-grad f` starting in the chart. If
the normalized linear flow of `ψ (γ 0)` stays in the chart between the times `0` and `t`, then
`ψ (γ t) = (e^{2t} v⁻, e^{-2t} v⁺)` for `v = ψ (γ 0)`. -/
theorem IsNormalizedEuclidean.normalizedChart_eq_normalizedLinearFlow
    (hX : IsAdaptedPseudoGradient f fun y ↦ (2⁻¹ : ℝ) • -mgradient 𝓘(ℝ, E) f y)
    (hφ : φ.IsNormalizedEuclidean) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ fun y ↦ -mgradient 𝓘(ℝ, E) f y) (h0 : γ 0 ∈ φ.toChart.source)
    {t : ℝ} (ht : ∀ s ∈ uIcc 0 t, normalizedLinearFlow (manifoldMorseIndex 𝓘(ℝ, E) f x) s
      (φ.normalizedChart (γ 0)) ∈ φ.normalizedChart.target) :
    φ.normalizedChart (γ t) =
      normalizedLinearFlow (manifoldMorseIndex 𝓘(ℝ, E) f x) t (φ.normalizedChart (γ 0)) := by
  have h2 : ((2 : ℝ) • fun y ↦ (2⁻¹ : ℝ) • -mgradient 𝓘(ℝ, E) f y) =
      fun y ↦ -mgradient 𝓘(ℝ, E) f y := by
    funext y
    rw [Pi.smul_apply, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]
  have hγ' : IsMIntegralCurve γ ((2 : ℝ) • fun y ↦ (2⁻¹ : ℝ) • -mgradient 𝓘(ℝ, E) f y) := by
    rwa [h2]
  rw [← hX.flow_mul_eq_of_isMIntegralCurve hγ' t]
  exact hφ.normalizedChart_flow_two_mul hX h0 ht

end MorseChart

/-! ### Existence -/

section Existence

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **A metric which is Euclidean in normalized Morse coordinates.** Let `K` be a compact subset
of a Hausdorff σ-compact manifold and let `f` be smooth. If every critical point of `f` in `K` is
nondegenerate, then there are Morse charts `φ c` at the critical points `c` in `K`, whose sources
have pairwise disjoint closures, and a smooth Riemannian metric which is the Euclidean metric of
the normalized coordinates of `φ c` on the whole source of `φ c`, in particular on every closed
ball of normalized coordinates inside it.

No condition is imposed on the metric away from these charts, nor on the critical points of `f`
outside `K`. -/
theorem _root_.IsCompact.exists_contMDiffRiemannianMetric_isNormalizedEuclidean [T2Space M]
    [SigmaCompactSpace M] {K : Set M} (hK : IsCompact K) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hnd : ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
      IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) :
    ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y),
      ∃ φ : ∀ c : ↥(criticalPoints 𝓘(ℝ, E) f ∩ K), MorseChart E f c,
        (letI : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) := ⟨g.toRiemannianMetric⟩
          ∀ c, (φ c).IsNormalizedEuclidean) ∧
          Pairwise (Disjoint on fun c ↦ closure (φ c).toChart.source) := by
  obtain ⟨g, φ, hφ, hdisj⟩ :=
    hK.exists_contMDiffRiemannianMetric_inner_eq_smul_euclideanForm hf hnd (inv_pos.2 two_pos)
  let : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) := ⟨g.toRiemannianMetric⟩
  refine ⟨g, φ, fun c ↦ (φ c).isNormalizedEuclidean_iff_euclideanForm.2 fun y hy v w ↦ ?_, hdisj⟩
  rw [g.inner_eq, hφ c y hy, smul_apply, smul_apply, smul_eq_mul]

/-- **A Morse function has a metric which is Euclidean in normalized Morse coordinates.** Every
Morse function on a compact manifold has a smooth Riemannian metric which is Euclidean in the
normalized coordinates of a Morse chart at each critical point; half its negative gradient is then
a pseudo-gradient adapted to the function. -/
theorem IsMorse.exists_contMDiffRiemannianMetric_isNormalizedEuclidean
    [CompactSpace M] [T2Space M] (hf : IsMorse 𝓘(ℝ, E) f) :
    ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y),
      letI : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) := ⟨g.toRiemannianMetric⟩
      (∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 → ∃ φ : MorseChart E f x, φ.IsNormalizedEuclidean) ∧
        IsAdaptedPseudoGradient f fun y ↦ (2⁻¹ : ℝ) • -mgradient 𝓘(ℝ, E) f y := by
  obtain ⟨g, φ, hφ, -⟩ := isCompact_univ.exists_contMDiffRiemannianMetric_isNormalizedEuclidean
    hf.contMDiff fun _ _ hx ↦ hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
  let : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) :=
    ⟨⟨g.inner, g.contMDiff, g.inner_eq⟩⟩
  have hcrit (x : M) (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
      ∃ φ : MorseChart E f x, φ.IsNormalizedEuclidean :=
    ⟨φ ⟨x, mem_criticalPoints_iff_mfderiv_eq_zero.2 hx, mem_univ x⟩, hφ _⟩
  exact ⟨g, hcrit, isAdaptedPseudoGradient_inv_two_smul_neg_mgradient hf.contMDiff hcrit⟩

end Existence

end TauCeti
