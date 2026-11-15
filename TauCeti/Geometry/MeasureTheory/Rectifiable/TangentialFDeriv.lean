/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import TauCeti.Geometry.MeasureTheory.Rectifiable.ApproximateTangent
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Analysis.Normed.Ring.Units
import TauCeti.Geometry.Euclidean.Volume.Density
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Constructions.BorelSpace.IsOpenUnits

/-!
# Tangential differentiation on rectifiable sets

Let `E` be a subset of a real inner product space `V` admitting an approximate tangent `k`-plane
`P` at `x`. A map `g : V → W` into a normed space `W` has **tangential derivative**
`L : P →L[ℝ] W` along `E` at `x` (`TauCeti.HasTangentialFDerivAt k g P L E x`) if for every
`ε > 0` the set of points `z ∈ E ∩ closedBall x r` where the tangential first-order error
`‖g z - g x - L (P.orthogonalProjectionOnto (z - x))‖` exceeds `ε * dist z x` has
`k`-dimensional Hausdorff density zero at `x`. When `L` exists uniquely on the canonical
approximate tangent plane `TauCeti.approxTangentPlane k E x`, `TauCeti.tangentialFDeriv k g E x`
selects it (and takes the junk value `0` otherwise).

Along any differentiable parametrization `f : U → V` that is antilipschitz on `s ⊆ U`, at a
Lebesgue density-one point `x₀ ∈ s` with `f '' s ⊆ E`:
* any tangential derivative of `g` along `E` at `f x₀` is **deterministically unique**
  (`HasFDerivWithinAt.hasTangentialFDerivAt_unique`), with operator norm bounded by the Lipschitz
  constant of `g` on `E` (`HasFDerivWithinAt.opNorm_le_of_hasTangentialFDerivAt`);
* if `E \ f '' s` has `(finrank ℝ U)`-dimensional Hausdorff density zero at `f x₀` and `g ∘ f`
  has derivative `B` within `s` at `x₀`, then `g` is tangentially differentiable along `E` at
  `f x₀`, satisfying the chain rule
  `((tangentialFDeriv k g E (f x₀)).comp
  (approxTangentPlane k E (f x₀)).orthogonalProjectionOnto) ∘L A = B` and the Jacobian identity
  `(tangentialFDeriv k g E (f x₀)).normDet * A.normDet = B.normDet`.

Combining Rademacher's theorem on bi-Lipschitz charts with Hausdorff density zero of chart
complements yields **almost-everywhere tangential differentiability** of Lipschitz maps on
null-measurable, countably `k`-rectifiable sets with locally finite `μHE[k]` measure, together with
chart independence, invariance under `μHE[k]`-null modifications of the set or map, and
`AEMeasurable` regularity of both the ambient tangential derivative field and the tangential
Jacobian `normDet`.

## Main definitions

* `TauCeti.HasTangentialFDerivAt k g P L E x`: `P` is an approximate tangent `k`-plane to `E` at
  `x` and `L : P →L[ℝ] W` approximates `g z - g x` along `E` up to `k`-density-zero error.
* `TauCeti.tangentialFDeriv k g E x`: the unique `L : approxTangentPlane k E x →L[ℝ] W`
  satisfying `HasTangentialFDerivAt` if one exists uniquely, and `0` otherwise.

## Main results

* `HasFDerivWithinAt.hasTangentialFDerivAt`: ambient differentiability within `E` implies
  tangential differentiability by restriction to any approximate tangent plane.
* `TauCeti.hasTangentialFDerivAt_congr_ae`,
  `TauCeti.tangentialFDeriv_comp_orthogonalProjectionOnto_congr_ae`,
  `TauCeti.ae_tangentialFDeriv_congr`: invariance under `μHE[k]`-null modifications of `E` and `g`.
* `HasFDerivWithinAt.hasTangentialFDerivAt_unique`,
  `HasFDerivWithinAt.existsUnique_hasTangentialFDerivAt_of_tendsto_diff`,
  `HasFDerivWithinAt.tangentialFDeriv_comp_orthogonalProjectionOnto_comp_eq`,
  `HasFDerivWithinAt.normDet_tangentialFDeriv_mul_eq`: deterministic uniqueness, chart chain rule,
  and Jacobian factorization.
* `TauCeti.CountablyRectifiable.ae_existsUnique_hasTangentialFDerivAt`,
  `TauCeti.CountablyRectifiable.ae_norm_tangentialFDeriv_le`,
  `TauCeti.CountablyRectifiable.aemeasurable_tangentialFDeriv_comp_orthogonalProjectionOnto`,
  `TauCeti.CountablyRectifiable.aemeasurable_normDet_tangentialFDeriv`: Rademacher-type tangential
  differentiability and measurability on countably `k`-rectifiable sets.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11–§12.
* H. Federer, *Geometric Measure Theory*, §3.2.16–3.2.19.
-/

public section

open Filter Function Metric MeasureTheory Module Set
open scoped ENNReal NNReal symmDiff Topology

namespace TauCeti

section Basic

variable {V W W' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W'] [NormedSpace ℝ W']

/-- `HasTangentialFDerivAt k g P L E x` means that `P` is an approximate tangent `k`-plane to `E`
at `x` and `L : P →L[ℝ] W` is an approximate tangential derivative of `g` along `E` at `x`: for
every `ε > 0`, the points of `E ∩ closedBall x r` where the first-order tangential Taylor error
exceeds `ε * dist z x` have `k`-dimensional Hausdorff density zero as `r → 0⁺`. -/
structure HasTangentialFDerivAt (k : ℕ) (g : V → W) (P : Submodule ℝ V)
    [P.HasOrthogonalProjection] (L : P →L[ℝ] W) (E : Set V) (x : V) : Prop where
  /-- `P` is an approximate tangent `k`-plane to `E` at `x`. -/
  isApproxTangentPlane : IsApproxTangentPlane k E P x
  /-- For every `ε > 0`, the points of `E` where the tangential Taylor remainder exceeds
  `ε * dist z x` have `k`-dimensional Hausdorff density zero at `x`. -/
  tendsto_outside_error_div : ∀ ε > (0 : ℝ), Tendsto (fun r =>
    μHE[k] {z ∈ E ∩ closedBall x r |
      ε * dist z x < ‖g z - g x - L (P.orthogonalProjectionOnto (z - x))‖} /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)

/-- Characterization of `HasTangentialFDerivAt` unpacking its two conditions. -/
theorem hasTangentialFDerivAt_iff {k : ℕ} {g : V → W} {P : Submodule ℝ V}
    [P.HasOrthogonalProjection] {L : P →L[ℝ] W} {E : Set V} {x : V} :
    HasTangentialFDerivAt k g P L E x ↔
      IsApproxTangentPlane k E P x ∧
      ∀ ε > (0 : ℝ), Tendsto (fun r =>
        μHE[k] {z ∈ E ∩ closedBall x r |
          ε * dist z x < ‖g z - g x - L (P.orthogonalProjectionOnto (z - x))‖} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- No map has a tangential derivative along the empty set. -/
@[simp]
theorem not_hasTangentialFDerivAt_empty (k : ℕ) (g : V → W) (P : Submodule ℝ V)
    [P.HasOrthogonalProjection] (L : P →L[ℝ] W) (x : V) :
    ¬ HasTangentialFDerivAt k g P L (∅ : Set V) x := fun h =>
  not_isApproxTangentPlane_empty k P x h.isApproxTangentPlane

/-- The canonical tangential derivative of `g : V → W` along `E` at `x` on `approxTangentPlane`:
the unique `L` satisfying `HasTangentialFDerivAt` if one exists uniquely, and `0` otherwise. -/
noncomputable def tangentialFDeriv (k : ℕ) (g : V → W) (E : Set V) (x : V) :
    approxTangentPlane k E x →L[ℝ] W :=
  open Classical in
  if h : ∃! L : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E x) L E x
    then h.choose else 0

/-- When `g` has a unique tangential derivative on `approxTangentPlane k E x`,
`tangentialFDeriv k g E x` satisfies `HasTangentialFDerivAt`. -/
theorem hasTangentialFDerivAt_tangentialFDeriv {k : ℕ} {g : V → W} {E : Set V} {x : V}
    (h : ∃! L : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E x) L E x) :
    HasTangentialFDerivAt k g (approxTangentPlane k E x) (tangentialFDeriv k g E x) E x := by
  simp only [tangentialFDeriv, h, ↓reduceDIte]
  exact h.choose_spec.1

/-- When `g` has a unique tangential derivative on `approxTangentPlane k E x`,
`tangentialFDeriv k g E x` equals any witness `L`. -/
theorem tangentialFDeriv_eq_of_existsUnique {k : ℕ} {g : V → W} {E : Set V} {x : V}
    {L : approxTangentPlane k E x →L[ℝ] W}
    (h : ∃! L' : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E x) L' E x)
    (hL : HasTangentialFDerivAt k g (approxTangentPlane k E x) L E x) :
    tangentialFDeriv k g E x = L :=
  h.unique (hasTangentialFDerivAt_tangentialFDeriv h) hL

/-- Outside the locus of unique existence, `tangentialFDeriv` takes the junk value `0`. -/
theorem tangentialFDeriv_of_not_existsUnique {k : ℕ} {g : V → W} {E : Set V} {x : V}
    (h : ¬ ∃! L : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E x) L E x) :
    tangentialFDeriv k g E x = 0 := by
  simp only [tangentialFDeriv, h, ↓reduceDIte]

/-- Along the empty set, `tangentialFDeriv` is `0`. -/
@[simp]
theorem tangentialFDeriv_empty (k : ℕ) (g : V → W) (x : V) :
    tangentialFDeriv k g (∅ : Set V) x = 0 :=
  tangentialFDeriv_of_not_existsUnique fun ⟨_, hL, _⟩ =>
    not_hasTangentialFDerivAt_empty k g _ _ x hL

/-- For `k = 0`, `approxTangentPlane 0 E x = ⊥`, so `tangentialFDeriv 0 g E x = 0` everywhere. -/
@[simp]
theorem tangentialFDeriv_zero (g : V → W) (E : Set V) (x : V) :
    tangentialFDeriv 0 g E x = 0 := by
  have hbot : approxTangentPlane 0 E x = ⊥ := approxTangentPlane_zero E x
  have : Subsingleton (approxTangentPlane 0 E x) := hbot ▸ inferInstance
  exact Subsingleton.elim _ _

/-- Transporting unique tangential differentiability from any witness plane `P` to
`approxTangentPlane k E x`. -/
theorem existsUnique_hasTangentialFDerivAt_of_unique
    {k : ℕ} {g : V → W} {P : Submodule ℝ V} [inst : P.HasOrthogonalProjection]
    {L : P →L[ℝ] W} {E : Set V} {x : V}
    (hP : ∃! Q : Submodule ℝ V, IsApproxTangentPlane k E Q x)
    (hL : HasTangentialFDerivAt k g P L E x)
    (huniq : ∀ L' : P →L[ℝ] W, HasTangentialFDerivAt k g P L' E x → L' = L) :
    ∃! L' : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E x) L' E x := by
  have heq : P = approxTangentPlane k E x :=
    (approxTangentPlane_eq_of_existsUnique hP hL.isApproxTangentPlane).symm
  subst heq
  have hinst : inst = (inferInstance : (approxTangentPlane k E x).HasOrthogonalProjection) :=
    Subsingleton.elim _ _
  cases hinst
  exact ⟨L, hL, huniq⟩

/-- Identifying the ambient operator `(tangentialFDeriv k g E x).comp orthogonalProjectionOnto`
from a witness `(P, L)` when both `P` and `L` are unique. -/
theorem tangentialFDeriv_comp_orthogonalProjectionOnto_eq_of_unique
    {k : ℕ} {g : V → W} {P : Submodule ℝ V} [inst : P.HasOrthogonalProjection]
    {L : P →L[ℝ] W} {E : Set V} {x : V}
    (hP : ∃! Q : Submodule ℝ V, IsApproxTangentPlane k E Q x)
    (hL : HasTangentialFDerivAt k g P L E x)
    (huniq : ∀ L' : P →L[ℝ] W, HasTangentialFDerivAt k g P L' E x → L' = L) :
    (tangentialFDeriv k g E x).comp (approxTangentPlane k E x).orthogonalProjectionOnto =
      L.comp P.orthogonalProjectionOnto := by
  have heq : P = approxTangentPlane k E x :=
    (approxTangentPlane_eq_of_existsUnique hP hL.isApproxTangentPlane).symm
  subst heq
  have hinst : inst = (inferInstance : (approxTangentPlane k E x).HasOrthogonalProjection) :=
    Subsingleton.elim _ _
  cases hinst
  rw [tangentialFDeriv_eq_of_existsUnique ⟨L, hL, huniq⟩ hL]

/-- Identifying the operator norm of `tangentialFDeriv` from a unique witness `(P, L)`. -/
theorem norm_tangentialFDeriv_eq_of_unique
    {k : ℕ} {g : V → W} {P : Submodule ℝ V} [inst : P.HasOrthogonalProjection]
    {L : P →L[ℝ] W} {E : Set V} {x : V}
    (hP : ∃! Q : Submodule ℝ V, IsApproxTangentPlane k E Q x)
    (hL : HasTangentialFDerivAt k g P L E x)
    (huniq : ∀ L' : P →L[ℝ] W, HasTangentialFDerivAt k g P L' E x → L' = L) :
    ‖tangentialFDeriv k g E x‖ = ‖L‖ := by
  have heq : P = approxTangentPlane k E x :=
    (approxTangentPlane_eq_of_existsUnique hP hL.isApproxTangentPlane).symm
  subst heq
  have hinst : inst = (inferInstance : (approxTangentPlane k E x).HasOrthogonalProjection) :=
    Subsingleton.elim _ _
  cases hinst
  rw [tangentialFDeriv_eq_of_existsUnique ⟨L, hL, huniq⟩ hL]

/-- Identifying the tangential Jacobian `normDet` from a unique witness `(P, L)`. -/
theorem normDet_tangentialFDeriv_eq_of_unique
    {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    {k : ℕ} {g : V → W₀} {P : Submodule ℝ V} [inst : FiniteDimensional ℝ P]
    {L : P →L[ℝ] W₀} {E : Set V} {x : V}
    (hP : ∃! Q : Submodule ℝ V, IsApproxTangentPlane k E Q x)
    (hL : HasTangentialFDerivAt k g P L E x)
    (huniq : ∀ L' : P →L[ℝ] W₀, HasTangentialFDerivAt k g P L' E x → L' = L) :
    (tangentialFDeriv k g E x).normDet = L.normDet := by
  have heq : P = approxTangentPlane k E x :=
    (approxTangentPlane_eq_of_existsUnique hP hL.isApproxTangentPlane).symm
  subst heq
  have hinst : inst = (inferInstance : FiniteDimensional ℝ (approxTangentPlane k E x)) :=
    Subsingleton.elim _ _
  cases hinst
  rw [tangentialFDeriv_eq_of_existsUnique ⟨L, hL, huniq⟩ hL]

/-! ### Comparison with ambient derivatives and algebraic operations -/

/-- **Ambient relative differentiability implies tangential differentiability.** If `g` has
derivative `D` within `E` at `x` and `P` is an approximate tangent `k`-plane to `E` at `x`, then
`g` has tangential derivative `D.comp P.subtypeL` along `E` at `x`. -/
theorem _root_.HasFDerivWithinAt.hasTangentialFDerivAt
    {k : ℕ} {g : V → W} {D : V →L[ℝ] W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {E : Set V} {x : V} (hg : HasFDerivWithinAt g D E x) (hP : IsApproxTangentPlane k E P x) :
    HasTangentialFDerivAt k g P (D.comp P.subtypeL) E x where
  isApproxTangentPlane := hP
  tendsto_outside_error_div ε hε := by
    have hlo : ∀ᶠ z in 𝓝[E] x, ‖g z - g x - D (z - x)‖ ≤ (ε / 2) * ‖z - x‖ :=
      hg.isLittleO.bound (half_pos hε)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hlo
    obtain ⟨δ, hδ, hbound⟩ := hlo
    set M := max ‖D‖ 1
    have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hcone := hP.tendsto_outside_cone_div ((ε / 2) / M) (by positivity)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcone
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
    apply ENNReal.div_le_div_right
    apply measure_mono
    rintro z ⟨⟨hzE, hzr⟩, hzerr⟩
    refine ⟨⟨hzE, hzr⟩, ?_⟩
    have hzδ : dist z x < δ := (mem_closedBall.1 hzr).trans_lt hr
    have h1 : ‖g z - g x - D (z - x)‖ ≤ (ε / 2) * dist z x := by
      simpa only [dist_eq_norm] using hbound hzδ hzE
    have hdecomp : g z - g x - (D.comp P.subtypeL) (P.orthogonalProjectionOnto (z - x)) =
        (g z - g x - D (z - x)) + D (z - x - P.starProjection (z - x)) := by
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        Submodule.coe_orthogonalProjectionOnto_apply, map_sub]
      abel
    have h2 : ‖D (z - x - P.starProjection (z - x))‖ ≤
        M * infDist (z - x) (P : Set V) := by
      calc ‖D (z - x - P.starProjection (z - x))‖
          ≤ ‖D‖ * ‖z - x - P.starProjection (z - x)‖ := D.le_opNorm _
        _ ≤ M * ‖z - x - P.starProjection (z - x)‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ = M * infDist (z - x) (P : Set V) := by
            rw [← dist_eq_norm, P.dist_starProjection_eq_infDist]
    have h3 : ε * dist z x < (ε / 2) * dist z x + M * infDist (z - x) (P : Set V) := by
      calc ε * dist z x
          < ‖g z - g x - (D.comp P.subtypeL) (P.orthogonalProjectionOnto (z - x))‖ := hzerr
        _ ≤ ‖g z - g x - D (z - x)‖ + ‖D (z - x - P.starProjection (z - x))‖ := by
            rw [hdecomp]
            exact norm_add_le _ _
        _ ≤ (ε / 2) * dist z x + M * infDist (z - x) (P : Set V) := add_le_add h1 h2
    rw [div_mul_eq_mul_div, div_lt_iff₀ hM]
    linarith

/-- Ambient Fréchet differentiability at `x` implies tangential differentiability along `E` on any
approximate tangent `k`-plane `P`. -/
theorem _root_.HasFDerivAt.hasTangentialFDerivAt
    {k : ℕ} {g : V → W} {D : V →L[ℝ] W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {E : Set V} {x : V} (hg : HasFDerivAt g D x) (hP : IsApproxTangentPlane k E P x) :
    HasTangentialFDerivAt k g P (D.comp P.subtypeL) E x :=
  hg.hasFDerivWithinAt.hasTangentialFDerivAt hP

namespace HasTangentialFDerivAt

/-- Constant functions have zero tangential derivative on any approximate tangent plane. -/
theorem const {k : ℕ} (c : W) {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {E : Set V} {x : V} (hP : IsApproxTangentPlane k E P x) :
    HasTangentialFDerivAt k (fun _ => c) P 0 E x := by
  simpa using (hasFDerivWithinAt_const c x E).hasTangentialFDerivAt hP

/-- The identity map has tangential derivative `P.subtypeL` on any approximate tangent plane `P`. -/
theorem id {k : ℕ} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {E : Set V} {x : V} (hP : IsApproxTangentPlane k E P x) :
    HasTangentialFDerivAt k (_root_.id : V → V) P P.subtypeL E x := by
  simpa using (hasFDerivWithinAt_id x E).hasTangentialFDerivAt hP

/-- Post-composing a tangentially differentiable map with a continuous linear map composes the
tangential derivative. -/
theorem continuousLinearMap_comp {k : ℕ} {g : V → W} {P : Submodule ℝ V}
    [P.HasOrthogonalProjection] {L : P →L[ℝ] W} {E : Set V} {x : V}
    (C : W →L[ℝ] W') (h : HasTangentialFDerivAt k g P L E x) :
    HasTangentialFDerivAt k (C ∘ g) P (C.comp L) E x where
  isApproxTangentPlane := h.isApproxTangentPlane
  tendsto_outside_error_div ε hε := by
    set M := max ‖C‖ 1
    have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (h.tendsto_outside_error_div (ε / M) (by positivity))
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
    apply ENNReal.div_le_div_right
    apply measure_mono
    rintro z ⟨hzE, hzerr⟩
    refine ⟨hzE, ?_⟩
    have hle : ‖(C ∘ g) z - (C ∘ g) x - (C.comp L) (P.orthogonalProjectionOnto (z - x))‖ ≤
        M * ‖g z - g x - L (P.orthogonalProjectionOnto (z - x))‖ := by
      have heq : (C ∘ g) z - (C ∘ g) x - (C.comp L) (P.orthogonalProjectionOnto (z - x)) =
          C (g z - g x - L (P.orthogonalProjectionOnto (z - x))) := by
        simp [Function.comp_apply, map_sub]
      rw [heq]
      exact (C.le_opNorm _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    rw [div_mul_eq_mul_div, div_lt_iff₀ hM]
    linarith

/-- Scalar multiplication commutes with `HasTangentialFDerivAt`. -/
theorem const_smul {k : ℕ} {g : V → W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {L : P →L[ℝ] W} {E : Set V} {x : V} (c : ℝ) (h : HasTangentialFDerivAt k g P L E x) :
    HasTangentialFDerivAt k (fun z => c • g z) P (c • L) E x := by
  simpa [Function.comp_def] using h.continuousLinearMap_comp (c • ContinuousLinearMap.id ℝ W)

/-- Negation commutes with `HasTangentialFDerivAt`. -/
theorem neg {k : ℕ} {g : V → W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {L : P →L[ℝ] W} {E : Set V} {x : V} (h : HasTangentialFDerivAt k g P L E x) :
    HasTangentialFDerivAt k (fun z => -g z) P (-L) E x := by
  simpa [Function.comp_def] using h.continuousLinearMap_comp (-ContinuousLinearMap.id ℝ W)

/-- Addition of tangentially differentiable maps on the same approximate tangent plane. -/
theorem add {k : ℕ} {g₁ g₂ : V → W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {L₁ L₂ : P →L[ℝ] W} {E : Set V} {x : V}
    (h₁ : HasTangentialFDerivAt k g₁ P L₁ E x)
    (h₂ : HasTangentialFDerivAt k g₂ P L₂ E x) :
    HasTangentialFDerivAt k (fun z => g₁ z + g₂ z) P (L₁ + L₂) E x where
  isApproxTangentPlane := h₁.isApproxTangentPlane
  tendsto_outside_error_div ε hε := by
    have hsum : Tendsto (fun r =>
        μHE[k] {z ∈ E ∩ closedBall x r |
          (ε / 2) * dist z x < ‖g₁ z - g₁ x - L₁ (P.orthogonalProjectionOnto (z - x))‖} /
            volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) +
        μHE[k] {z ∈ E ∩ closedBall x r |
          (ε / 2) * dist z x < ‖g₂ z - g₂ x - L₂ (P.orthogonalProjectionOnto (z - x))‖} /
            volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [add_zero] using
        (h₁.tendsto_outside_error_div (ε / 2) (half_pos hε)).add
          (h₂.tendsto_outside_error_div (ε / 2) (half_pos hε))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
    rw [← ENNReal.add_div]
    refine ENNReal.div_le_div_right ((measure_mono ?_).trans (measure_union_le _ _)) _
    intro z ⟨hzE, hzerr⟩
    by_contra hnot
    rw [mem_union, not_or] at hnot
    have hle₁ :
        ‖g₁ z - g₁ x - L₁ (P.orthogonalProjectionOnto (z - x))‖ ≤ (ε / 2) * dist z x :=
      le_of_not_gt fun h => hnot.1 ⟨hzE, h⟩
    have hle₂ :
        ‖g₂ z - g₂ x - L₂ (P.orthogonalProjectionOnto (z - x))‖ ≤ (ε / 2) * dist z x :=
      le_of_not_gt fun h => hnot.2 ⟨hzE, h⟩
    have htri :
        ‖(g₁ z + g₂ z) - (g₁ x + g₂ x) - (L₁ + L₂) (P.orthogonalProjectionOnto (z - x))‖ ≤
          ‖g₁ z - g₁ x - L₁ (P.orthogonalProjectionOnto (z - x))‖ +
            ‖g₂ z - g₂ x - L₂ (P.orthogonalProjectionOnto (z - x))‖ := by
      have heq :
          (g₁ z + g₂ z) - (g₁ x + g₂ x) - (L₁ + L₂) (P.orthogonalProjectionOnto (z - x)) =
            (g₁ z - g₁ x - L₁ (P.orthogonalProjectionOnto (z - x))) +
              (g₂ z - g₂ x - L₂ (P.orthogonalProjectionOnto (z - x))) := by
        simp only [add_apply]
        abel
      rw [heq]
      exact norm_add_le _ _
    linarith

/-- Subtraction of tangentially differentiable maps on the same approximate tangent plane. -/
theorem sub {k : ℕ} {g₁ g₂ : V → W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {L₁ L₂ : P →L[ℝ] W} {E : Set V} {x : V}
    (h₁ : HasTangentialFDerivAt k g₁ P L₁ E x)
    (h₂ : HasTangentialFDerivAt k g₂ P L₂ E x) :
    HasTangentialFDerivAt k (fun z => g₁ z - g₂ z) P (L₁ - L₂) E x := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-! ### Invariance under density-zero and null modifications -/

/-- `HasTangentialFDerivAt` is preserved when both `E₁ \ E₂` and `E₂ \ E₁` have
`k`-dimensional Hausdorff density zero at `x`. -/
theorem of_tendsto_diff {k : ℕ} {g : V → W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {L : P →L[ℝ] W} {E₁ E₂ : Set V} {x : V}
    (h : HasTangentialFDerivAt k g P L E₁ x)
    (h12 : Tendsto (fun r => μHE[k] ((E₁ \ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0))
    (h21 : Tendsto (fun r => μHE[k] ((E₂ \ E₁) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    HasTangentialFDerivAt k g P L E₂ x where
  isApproxTangentPlane := h.isApproxTangentPlane.of_tendsto_diff h12 h21
  tendsto_outside_error_div ε hε := by
    have hsum : Tendsto (fun r =>
        μHE[k] {z ∈ E₁ ∩ closedBall x r |
          ε * dist z x < ‖g z - g x - L (P.orthogonalProjectionOnto (z - x))‖} /
            volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) +
        μHE[k] ((E₂ \ E₁) ∩ closedBall x r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [add_zero] using (h.tendsto_outside_error_div ε hε).add h21
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
    rw [← ENNReal.add_div]
    refine ENNReal.div_le_div_right ((measure_mono ?_).trans (measure_union_le _ _)) _
    intro z ⟨⟨hzE₂, hzr⟩, hzerr⟩
    by_cases hzE₁ : z ∈ E₁
    · exact Or.inl ⟨⟨hzE₁, hzr⟩, hzerr⟩
    · exact Or.inr ⟨⟨hzE₂, hzE₁⟩, hzr⟩

end HasTangentialFDerivAt

/-- `HasTangentialFDerivAt` depends only on `E` up to symmetric difference of `k`-dimensional
Hausdorff density zero at `x`. -/
theorem hasTangentialFDerivAt_congr_of_tendsto_symmDiff_div
    {k : ℕ} {g : V → W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {L : P →L[ℝ] W} {E₁ E₂ : Set V} {x : V}
    (h : Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    HasTangentialFDerivAt k g P L E₁ x ↔ HasTangentialFDerivAt k g P L E₂ x := by
  have h12 : Tendsto (fun r => μHE[k] ((E₁ \ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
    gcongr
    exact subset_union_left
  have h21 : Tendsto (fun r => μHE[k] ((E₂ \ E₁) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
    gcongr
    exact subset_union_right
  exact ⟨fun h₁ => h₁.of_tendsto_diff h12 h21, fun h₂ => h₂.of_tendsto_diff h21 h12⟩

/-- **Invariance under `μHE[k]`-null set modifications.** If `E₁ =ᵐ[μHE[k]] E₂`, then
`HasTangentialFDerivAt` agrees at **every** point `x : V`. -/
theorem hasTangentialFDerivAt_congr_ae
    {k : ℕ} {g : V → W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {L : P →L[ℝ] W} {E₁ E₂ : Set V} (h : E₁ =ᵐ[μHE[k]] E₂) {x : V} :
    HasTangentialFDerivAt k g P L E₁ x ↔ HasTangentialFDerivAt k g P L E₂ x := by
  refine hasTangentialFDerivAt_congr_of_tendsto_symmDiff_div ?_
  have hnull : μHE[k] (E₁ ∆ E₂) = 0 := by
    rw [symmDiff_def]
    exact measure_union_null (ae_eq_set.1 h).1 (ae_eq_set.1 h).2
  refine tendsto_const_nhds.congr' (Eventually.of_forall fun r => ?_)
  dsimp only
  rw [measure_mono_null inter_subset_left hnull, ENNReal.zero_div]

/-- If `E₁ =ᵐ[μHE[k]] E₂`, the ambient tangential derivative operator
`(tangentialFDeriv k g E x).comp (approxTangentPlane k E x).orthogonalProjectionOnto` agrees at
**every** point `x : V`. -/
theorem tangentialFDeriv_comp_orthogonalProjectionOnto_congr_ae
    {k : ℕ} {g : V → W} {E₁ E₂ : Set V} (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    (tangentialFDeriv k g E₁ x).comp (approxTangentPlane k E₁ x).orthogonalProjectionOnto =
      (tangentialFDeriv k g E₂ x).comp
        (approxTangentPlane k E₂ x).orthogonalProjectionOnto := by
  classical
  let F (P : Submodule ℝ V) [FiniteDimensional ℝ P] (E : Set V) : V →L[ℝ] W :=
    (if hex : ExistsUnique (fun L : P →L[ℝ] W => HasTangentialFDerivAt k g P L E x)
      then hex.choose else 0).comp P.orthogonalProjectionOnto
  have hE (P : Submodule ℝ V) [FiniteDimensional ℝ P] : F P E₁ = F P E₂ :=
    congrArg (fun q : (P →L[ℝ] W) → Prop =>
      (if hex : ExistsUnique q then hex.choose else 0).comp P.orthogonalProjectionOnto)
      (funext fun L => propext (hasTangentialFDerivAt_congr_ae h))
  have hP {P₁ P₂ : Submodule ℝ V} [FiniteDimensional ℝ P₁] [FiniteDimensional ℝ P₂]
      (heq : P₁ = P₂) : F P₁ E₂ = F P₂ E₂ := by
    subst heq
    rfl
  change F (approxTangentPlane k E₁ x) E₁ = F (approxTangentPlane k E₂ x) E₂
  exact (hE _).trans (hP (approxTangentPlane_congr_ae h x))

/-- If `E₁ =ᵐ[μHE[k]] E₂`, the tangential Jacobian `normDet` agrees at **every** point
`x : V`. -/
theorem normDet_tangentialFDeriv_congr_ae
    {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    {k : ℕ} {g : V → W₀} {E₁ E₂ : Set V} (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    (tangentialFDeriv k g E₁ x).normDet = (tangentialFDeriv k g E₂ x).normDet := by
  classical
  let F (P : Submodule ℝ V) [FiniteDimensional ℝ P] (E : Set V) : ℝ :=
    (if hex : ExistsUnique (fun L : P →L[ℝ] W₀ => HasTangentialFDerivAt k g P L E x)
      then hex.choose else 0).normDet
  have hE (P : Submodule ℝ V) [FiniteDimensional ℝ P] : F P E₁ = F P E₂ :=
    congrArg (fun q : (P →L[ℝ] W₀) → Prop =>
      (if hex : ExistsUnique q then hex.choose else 0).normDet)
      (funext fun L => propext (hasTangentialFDerivAt_congr_ae h))
  have hP {P₁ P₂ : Submodule ℝ V} [FiniteDimensional ℝ P₁] [FiniteDimensional ℝ P₂]
      (heq : P₁ = P₂) : F P₁ E₂ = F P₂ E₂ := by
    subst heq
    rfl
  change F (approxTangentPlane k E₁ x) E₁ = F (approxTangentPlane k E₂ x) E₂
  exact (hE _).trans (hP (approxTangentPlane_congr_ae h x))

/-- `HasTangentialFDerivAt` is invariant under modifying `g` away from `x` on a subset of `E` of
`k`-dimensional Hausdorff density zero at `x`. -/
theorem hasTangentialFDerivAt_congr_of_tendsto_ne_div
    {k : ℕ} {g₁ g₂ : V → W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {L : P →L[ℝ] W} {E : Set V} {x : V} (hx : g₁ x = g₂ x)
    (hne : Tendsto (fun r => μHE[k] ({z ∈ E | g₁ z ≠ g₂ z} ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    HasTangentialFDerivAt k g₁ P L E x ↔ HasTangentialFDerivAt k g₂ P L E x := by
  have aux {f₁ f₂ : V → W} (hfx : f₁ x = f₂ x)
      (hfn : Tendsto (fun r => μHE[k] ({z ∈ E | f₁ z ≠ f₂ z} ∩ closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0))
      (h₁ : HasTangentialFDerivAt k f₁ P L E x) : HasTangentialFDerivAt k f₂ P L E x := by
    refine ⟨h₁.isApproxTangentPlane, fun ε hε => ?_⟩
    have hsum : Tendsto (fun r =>
        μHE[k] {z ∈ E ∩ closedBall x r |
          ε * dist z x < ‖f₁ z - f₁ x - L (P.orthogonalProjectionOnto (z - x))‖} /
            volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) +
        μHE[k] ({z ∈ E | f₁ z ≠ f₂ z} ∩ closedBall x r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [add_zero] using (h₁.tendsto_outside_error_div ε hε).add hfn
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
    rw [← ENNReal.add_div]
    refine ENNReal.div_le_div_right ((measure_mono ?_).trans (measure_union_le _ _)) _
    intro z ⟨⟨hzE, hzr⟩, hzerr⟩
    by_cases hfz : f₁ z = f₂ z
    · exact Or.inl ⟨⟨hzE, hzr⟩, by rwa [hfz, hfx]⟩
    · exact Or.inr ⟨⟨hzE, hfz⟩, hzr⟩
  refine ⟨aux hx hne, aux hx.symm ?_⟩
  convert hne using 4 with r
  ext z
  simp [ne_comm]

/-- `tangentialFDeriv` is invariant under modifying `g` away from `x` on a subset of `E` of
`k`-dimensional Hausdorff density zero at `x`. -/
theorem tangentialFDeriv_congr_of_tendsto_ne_div
    {k : ℕ} {g₁ g₂ : V → W} {E : Set V} {x : V} (hx : g₁ x = g₂ x)
    (hne : Tendsto (fun r => μHE[k] ({z ∈ E | g₁ z ≠ g₂ z} ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    tangentialFDeriv k g₁ E x = tangentialFDeriv k g₂ E x := by
  classical
  exact congrArg (fun q : (approxTangentPlane k E x →L[ℝ] W) → Prop =>
    if hex : ExistsUnique q then hex.choose else 0)
    (funext fun L => propext (hasTangentialFDerivAt_congr_of_tendsto_ne_div hx hne))

/-- At any `x ∈ E`, `HasTangentialFDerivAt` depends only on the restriction of `g` to `E`. -/
theorem hasTangentialFDerivAt_congr_of_eqOn
    {k : ℕ} {g₁ g₂ : V → W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {L : P →L[ℝ] W} {E : Set V} {x : V} (hg : EqOn g₁ g₂ E) (hx : x ∈ E) :
    HasTangentialFDerivAt k g₁ P L E x ↔ HasTangentialFDerivAt k g₂ P L E x := by
  refine hasTangentialFDerivAt_congr_of_tendsto_ne_div (hg hx) ?_
  have hempty : {z ∈ E | g₁ z ≠ g₂ z} = ∅ :=
    eq_empty_of_forall_notMem fun z ⟨hzE, hne⟩ => hne (hg hzE)
  simp only [hempty, empty_inter, measure_empty, ENNReal.zero_div, tendsto_const_nhds]

/-- At any `x ∈ E`, `tangentialFDeriv` depends only on the restriction of `g` to `E`. -/
theorem tangentialFDeriv_congr_of_eqOn
    {k : ℕ} {g₁ g₂ : V → W} {E : Set V} {x : V} (hg : EqOn g₁ g₂ E) (hx : x ∈ E) :
    tangentialFDeriv k g₁ E x = tangentialFDeriv k g₂ E x := by
  classical
  exact congrArg (fun q : (approxTangentPlane k E x →L[ℝ] W) → Prop =>
    if hex : ExistsUnique q then hex.choose else 0)
    (funext fun L => propext (hasTangentialFDerivAt_congr_of_eqOn hg hx))

/-- **Invariance under `μHE[k]`-null function modifications on `E`.** If `g₁` and `g₂` agree at
`μHE[k]`-almost every point of `E`, then `tangentialFDeriv k g₁ E x = tangentialFDeriv k g₂ E x`
at `μHE[k]`-almost every `x ∈ E`. -/
theorem ae_tangentialFDeriv_congr
    {k : ℕ} {g₁ g₂ : V → W} {E : Set V}
    (hg : ∀ᵐ z ∂μHE[k], z ∈ E → g₁ z = g₂ z) :
    ∀ᵐ x ∂μHE[k], x ∈ E → tangentialFDeriv k g₁ E x = tangentialFDeriv k g₂ E x := by
  have hnull : μHE[k] {z ∈ E | g₁ z ≠ g₂ z} = 0 := by
    refine measure_mono_null (fun z hz => ?_) (ae_iff.1 hg)
    exact fun h => hz.2 (h hz.1)
  filter_upwards [hg] with x hx hxE
  refine tangentialFDeriv_congr_of_tendsto_ne_div (hx hxE) ?_
  refine tendsto_const_nhds.congr' (Eventually.of_forall fun r => ?_)
  dsimp only
  rw [measure_mono_null inter_subset_left hnull, ENNReal.zero_div]

end Basic

end TauCeti

/-! ### Deterministic uniqueness, chain rule, and Jacobian along parametrizations -/

namespace HasFDerivWithinAt

variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {f : U → V} {g : V → W} {s : Set U} {E : Set V} {x₀ : U}
  {A : U →L[ℝ] V} {B : U →L[ℝ] W} {Lf : ℝ≥0}

/-- **Deterministic uniqueness of tangential derivatives along a parametrization.** At a Lebesgue
density-one point `x₀ ∈ s` of an inverse-Lipschitz differentiable map `f` with `f '' s ⊆ E`,
an arbitrary map `g : V → W` can have at most one tangential derivative along `E` at `f x₀`. -/
theorem hasTangentialFDerivAt_unique
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s)
    (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E) {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {L₁ L₂ : P →L[ℝ] W}
    (h₁ : TauCeti.HasTangentialFDerivAt (finrank ℝ U) g P L₁ E (f x₀))
    (h₂ : TauCeti.HasTangentialFDerivAt (finrank ℝ U) g P L₂ E (f x₀)) :
    L₁ = L₂ := by
  by_contra hne
  obtain ⟨p₀, hp₀⟩ : ∃ p : P, L₁ p ≠ L₂ p :=
    not_forall.1 fun hall => hne (ContinuousLinearMap.ext hall)
  have hPrange : P = LinearMap.range A.toLinearMap :=
    hf.eq_range_of_isApproxTangentPlane hx₀ hi hs hfs h₁.isApproxTangentPlane
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : U, A u₀ = (p₀ : V) := hPrange ▸ p₀.2
  have hAu₀ : A u₀ ≠ 0 := by
    intro h0
    have hp₀_zero : p₀ = 0 := Subtype.ext (hu₀.symm.trans h0)
    exact hp₀ (by simp [hp₀_zero])
  have : 0 < ‖A u₀‖ := norm_pos_iff.2 hAu₀
  set u : U := (2 * ‖A u₀‖)⁻¹ • u₀
  have hAu_norm : ‖A u‖ < 1 := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : (2 * ‖A u₀‖)⁻¹ * ‖A u₀‖ = 1 / 2 := by field_simp
    linarith
  have hproj_Au : P.orthogonalProjectionOnto (A u) = (2 * ‖A u₀‖)⁻¹ • p₀ := by
    apply Subtype.ext
    rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.coe_smul]
    have hmem : A u ∈ P := by
      rw [map_smul, hu₀]
      exact P.smul_mem _ p₀.2
    rw [P.starProjection_eq_self_iff.2 hmem, map_smul, hu₀]
  set c : ℝ := ‖(L₁ - L₂) (P.orthogonalProjectionOnto (A u))‖
  have hc : 0 < c := by
    rw [norm_pos_iff, hproj_Au, map_smul, smul_ne_zero_iff]
    exact ⟨inv_ne_zero (by positivity), sub_ne_zero.2 hp₀⟩
  set M : ℝ := max ‖L₁ - L₂‖ 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set η : ℝ := c / (2 * M)
  have hlow := hf.liminf_euclideanHausdorffMeasure_directional_closedBall_pos hi hs hfs
    hAu_norm (show 0 < η by positivity)
  have hsum : Tendsto (fun r =>
      μHE[finrank ℝ U] {z ∈ E ∩ closedBall (f x₀) r |
        (c / 6) * dist z (f x₀) <
          ‖g z - g (f x₀) - L₁ (P.orthogonalProjectionOnto (z - f x₀))‖} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r) +
      μHE[finrank ℝ U] {z ∈ E ∩ closedBall (f x₀) r |
        (c / 6) * dist z (f x₀) <
          ‖g z - g (f x₀) - L₂ (P.orthogonalProjectionOnto (z - f x₀))‖} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [add_zero] using
      (h₁.tendsto_outside_error_div (c / 6) (by positivity)).add
        (h₂.tendsto_outside_error_div (c / 6) (by positivity))
  refine hlow.ne' (le_antisymm ?_ zero_le)
  rw [← hsum.liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [← ENNReal.add_div]
  refine ENNReal.div_le_div_right ((measure_mono ?_).trans (measure_union_le _ _)) _
  intro z ⟨hzE, hzd⟩
  by_contra hnot
  rw [mem_union, not_or] at hnot
  have hle₁ : ‖g z - g (f x₀) - L₁ (P.orthogonalProjectionOnto (z - f x₀))‖ ≤
      (c / 6) * dist z (f x₀) := le_of_not_gt fun h => hnot.1 ⟨hzE, h⟩
  have hle₂ : ‖g z - g (f x₀) - L₂ (P.orthogonalProjectionOnto (z - f x₀))‖ ≤
      (c / 6) * dist z (f x₀) := le_of_not_gt fun h => hnot.2 ⟨hzE, h⟩
  have hzr : dist z (f x₀) ≤ r := mem_closedBall.1 hzE.2
  have hdiff_upper :
      ‖(L₁ - L₂) (P.orthogonalProjectionOnto (z - f x₀))‖ ≤ (c / 3) * r := by
    have heq : (L₁ - L₂) (P.orthogonalProjectionOnto (z - f x₀)) =
        (g z - g (f x₀) - L₂ (P.orthogonalProjectionOnto (z - f x₀))) -
          (g z - g (f x₀) - L₁ (P.orthogonalProjectionOnto (z - f x₀))) := by
      simp only [sub_apply]
      abel
    calc ‖(L₁ - L₂) (P.orthogonalProjectionOnto (z - f x₀))‖
        ≤ ‖g z - g (f x₀) - L₂ (P.orthogonalProjectionOnto (z - f x₀))‖ +
            ‖g z - g (f x₀) - L₁ (P.orthogonalProjectionOnto (z - f x₀))‖ := by
          rw [heq]
          exact norm_sub_le _ _
      _ ≤ (c / 6) * dist z (f x₀) + (c / 6) * dist z (f x₀) := add_le_add hle₂ hle₁
      _ ≤ (c / 3) * r := by nlinarith
  have hdiff_step :
      ‖(L₁ - L₂) (P.orthogonalProjectionOnto (z - f x₀ - r • A u))‖ ≤
        r * (c / 2) := by
    calc ‖(L₁ - L₂) (P.orthogonalProjectionOnto (z - f x₀ - r • A u))‖
        ≤ ‖L₁ - L₂‖ * ‖P.orthogonalProjectionOnto (z - f x₀ - r • A u)‖ :=
            (L₁ - L₂).le_opNorm _
      _ ≤ M * ‖z - f x₀ - r • A u‖ :=
          mul_le_mul (le_max_left _ _) (P.norm_orthogonalProjectionOnto_apply_le _)
            (norm_nonneg _) hM.le
      _ ≤ M * (r * η) := mul_le_mul_of_nonneg_left hzd hM.le
      _ = r * (c / 2) := by
          simp only [η]
          field_simp
  have hrc : r * c ≤
      ‖(L₁ - L₂) (P.orthogonalProjectionOnto (z - f x₀))‖ + r * (c / 2) := by
    have hnorm_rc : ‖r • (L₁ - L₂) (P.orthogonalProjectionOnto (A u))‖ = r * c := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have heq : r • (L₁ - L₂) (P.orthogonalProjectionOnto (A u)) =
        (L₁ - L₂) (P.orthogonalProjectionOnto (z - f x₀)) -
          (L₁ - L₂) (P.orthogonalProjectionOnto (z - f x₀ - r • A u)) := by
      rw [← map_sub (L₁ - L₂), ← map_sub P.orthogonalProjectionOnto, sub_sub_cancel,
        map_smul P.orthogonalProjectionOnto r (A u), map_smul (L₁ - L₂) r]
    rw [← hnorm_rc, heq]
    exact (norm_sub_le _ _).trans (add_le_add_right hdiff_step _)
  nlinarith

/-- **Operator-norm bound on tangential derivatives.** If `g` is `K`-Lipschitz on `E`, then any
tangential derivative `L` of `g` along `E` at a density-one parametrization point `f x₀` satisfies
`‖L‖ ≤ K`. -/
theorem opNorm_le_of_hasTangentialFDerivAt
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s)
    (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E) {K : ℝ≥0} (hg : LipschitzOnWith K g E)
    {P : Submodule ℝ V} [P.HasOrthogonalProjection] {L : P →L[ℝ] W}
    (hL : TauCeti.HasTangentialFDerivAt (finrank ℝ U) g P L E (f x₀)) :
    ‖L‖ ≤ K := by
  refine L.opNorm_le_bound K.coe_nonneg fun p => ?_
  by_cases hp : p = 0
  · simp [hp]
  have hp_pos : 0 < ‖p‖ := norm_pos_iff.2 hp
  have hPrange : P = LinearMap.range A.toLinearMap :=
    hf.eq_range_of_isApproxTangentPlane hx₀ hi hs hfs hL.isApproxTangentPlane
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : U, A u₀ = (p : V) := hPrange ▸ p.2
  have hAu₀ : ‖A u₀‖ = ‖p‖ := by
    rw [hu₀]
    exact Submodule.norm_coe p
  set u : U := (2 * ‖p‖)⁻¹ • u₀
  have hAu_norm : ‖A u‖ = 1 / 2 := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hAu₀]
    field_simp
  have hproj_Au : P.orthogonalProjectionOnto (A u) = (2 * ‖p‖)⁻¹ • p := by
    apply Subtype.ext
    rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.coe_smul]
    have hmem : A u ∈ P := by
      rw [map_smul, hu₀]
      exact P.smul_mem _ p.2
    rw [P.starProjection_eq_self_iff.2 hmem, map_smul, hu₀]
  have hhalf : ‖L (P.orthogonalProjectionOnto (A u))‖ ≤ (K : ℝ) / 2 := by
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    set M : ℝ := (K : ℝ) + ‖L‖ + 1
    have hM : 0 < M := by positivity
    set η : ℝ := δ / (3 * M)
    have hlow := hf.liminf_euclideanHausdorffMeasure_directional_closedBall_pos hi hs hfs
      (by linarith : ‖A u‖ < 1) (show 0 < η by positivity)
    have herr := (hL.tendsto_outside_error_div (δ / 3) (by positivity)).liminf_eq
    have hex : ∃ r > (0 : ℝ), ∃ z ∈ E ∩ closedBall (f x₀) r,
        ‖z - f x₀ - r • A u‖ ≤ r * η ∧
        ‖g z - g (f x₀) - L (P.orthogonalProjectionOnto (z - f x₀))‖ ≤
          (δ / 3) * dist z (f x₀) := by
      by_contra hall
      refine hlow.ne' (le_antisymm ?_ zero_le)
      rw [← herr]
      refine liminf_le_liminf ?_
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      apply ENNReal.div_le_div_right
      apply measure_mono
      rintro z ⟨hzE, hzd⟩
      exact ⟨hzE, not_le.1 fun hle => hall ⟨r, hr, z, hzE, hzd, hle⟩⟩
    obtain ⟨r, hr, z, ⟨hzE, hzr⟩, hzd, hzerr⟩ := hex
    have hfx₀E : f x₀ ∈ E := hfs (mem_image_of_mem f hx₀)
    have hdist_le : dist z (f x₀) ≤ r * (1 / 2 + η) := by
      have heq : z - f x₀ = (z - f x₀ - r • A u) + r • A u := by abel
      rw [dist_eq_norm, heq]
      calc ‖(z - f x₀ - r • A u) + r • A u‖
          ≤ ‖z - f x₀ - r • A u‖ + ‖r • A u‖ := norm_add_le _ _
        _ ≤ r * η + r * (1 / 2) := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hAu_norm]
            linarith
        _ = r * (1 / 2 + η) := by ring
    have hLip : ‖g z - g (f x₀)‖ ≤ (K : ℝ) * (r * (1 / 2 + η)) := by
      rw [← dist_eq_norm]
      exact (hg.dist_le_mul z hzE (f x₀) hfx₀E).trans
        (mul_le_mul_of_nonneg_left hdist_le K.coe_nonneg)
    have hLstep :
        ‖L (P.orthogonalProjectionOnto (z - f x₀ - r • A u))‖ ≤ ‖L‖ * (r * η) := by
      calc ‖L (P.orthogonalProjectionOnto (z - f x₀ - r • A u))‖
          ≤ ‖L‖ * ‖P.orthogonalProjectionOnto (z - f x₀ - r • A u)‖ := L.le_opNorm _
        _ ≤ ‖L‖ * ‖z - f x₀ - r • A u‖ :=
            mul_le_mul_of_nonneg_left
              (P.norm_orthogonalProjectionOnto_apply_le _) (norm_nonneg L)
        _ ≤ ‖L‖ * (r * η) := mul_le_mul_of_nonneg_left hzd (norm_nonneg L)
    have htri : r * ‖L (P.orthogonalProjectionOnto (A u))‖ ≤
        ‖g z - g (f x₀)‖ +
          ‖g z - g (f x₀) - L (P.orthogonalProjectionOnto (z - f x₀))‖ +
          ‖L (P.orthogonalProjectionOnto (z - f x₀ - r • A u))‖ := by
      have hnorm : ‖r • L (P.orthogonalProjectionOnto (A u))‖ =
          r * ‖L (P.orthogonalProjectionOnto (A u))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      have heq_proj : r • L (P.orthogonalProjectionOnto (A u)) =
          L (P.orthogonalProjectionOnto (z - f x₀)) -
            L (P.orthogonalProjectionOnto (z - f x₀ - r • A u)) := by
        rw [← map_sub L, ← map_sub P.orthogonalProjectionOnto, sub_sub_cancel,
          map_smul P.orthogonalProjectionOnto r (A u), map_smul L r]
      have heq : r • L (P.orthogonalProjectionOnto (A u)) =
          (g z - g (f x₀)) - (g z - g (f x₀) - L (P.orthogonalProjectionOnto (z - f x₀))) -
            L (P.orthogonalProjectionOnto (z - f x₀ - r • A u)) := by
        rw [heq_proj, sub_sub_cancel]
      rw [← hnorm, heq]
      exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    have hzr' : dist z (f x₀) ≤ r := mem_closedBall.1 hzr
    have hKL_η : ((K : ℝ) + ‖L‖) * η < δ / 3 := by
      have hlt : (K : ℝ) + ‖L‖ < M := by simp only [M]; linarith
      calc ((K : ℝ) + ‖L‖) * η < M * η := mul_lt_mul_of_pos_right hlt (by positivity)
        _ = δ / 3 := by simp only [η]; field_simp
    have hr_bound : r * ‖L (P.orthogonalProjectionOnto (A u))‖ < r * ((K : ℝ) / 2 + δ) := by
      have h1 : (δ / 3) * dist z (f x₀) ≤ (δ / 3) * r :=
        mul_le_mul_of_nonneg_left hzr' (by positivity)
      nlinarith
    exact lt_of_mul_lt_mul_left hr_bound hr.le
  rw [hproj_Au, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hhalf
  have : (2 * ‖p‖)⁻¹ * ‖L p‖ * (2 * ‖p‖) ≤ (K : ℝ) / 2 * (2 * ‖p‖) :=
    mul_le_mul_of_nonneg_right hhalf (by positivity)
  have h1 : (2 * ‖p‖)⁻¹ * ‖L p‖ * (2 * ‖p‖) = ‖L p‖ := by field_simp
  have : (K : ℝ) / 2 * (2 * ‖p‖) = (K : ℝ) * ‖p‖ := by ring
  linarith

/-- **Deterministic tangential differentiability along a parametrization.** At a Lebesgue
density-one point `x₀ ∈ s` of an inverse-Lipschitz map `f` with `HasFDerivWithinAt f A s x₀`,
if `g ∘ f` has derivative `B` within `s` at `x₀` and `E \ f '' s` has `(finrank ℝ U)`-dimensional
Hausdorff density zero at `f x₀`, then `g` has tangential derivative `B ∘ (A|_range)⁻¹` along
`E` at `f x₀`. No Lipschitz condition on `g` is needed. -/
theorem hasTangentialFDerivAt_of_tendsto_diff
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s)
    (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hinj : Injective A)
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r =>
      μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s x₀) :
    TauCeti.HasTangentialFDerivAt (finrank ℝ U) g (LinearMap.range A.toLinearMap)
      (B.comp (LinearEquiv.ofInjective A.toLinearMap hinj).symm.toContinuousLinearMap)
      E (f x₀) := by
  set P := LinearMap.range A.toLinearMap
  set L : P →L[ℝ] W :=
    B.comp (LinearEquiv.ofInjective A.toLinearMap hinj).symm.toContinuousLinearMap
  have hLA (u : U) : L ⟨A u, LinearMap.mem_range_self _ u⟩ = B u := by
    simp only [L, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
    have heq : (⟨A u, LinearMap.mem_range_self _ u⟩ : P) =
        LinearEquiv.ofInjective A.toLinearMap hinj u := rfl
    rw [heq]
    exact congrArg B ((LinearEquiv.ofInjective A.toLinearMap hinj).symm_apply_apply u)
  have himg : TauCeti.HasTangentialFDerivAt (finrank ℝ U) g P L (f '' s) (f x₀) := by
    refine ⟨hf.isApproxTangentPlane_image hx₀ hi hs, fun ε hε => ?_⟩
    set M : ℝ := max ‖L‖ 1
    have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    set Lf' : ℝ := max (Lf : ℝ) 1
    have hLf' : 0 < Lf' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hlo₁ : ∀ᶠ y in 𝓝[s] x₀, ‖f y - f x₀ - A (y - x₀)‖ ≤
        (ε / (3 * M * Lf')) * ‖y - x₀‖ :=
      hf.isLittleO.bound (by positivity)
    have hlo₂ : ∀ᶠ y in 𝓝[s] x₀, ‖g (f y) - g (f x₀) - B (y - x₀)‖ ≤
        (ε / (3 * Lf')) * ‖y - x₀‖ :=
      hgf.isLittleO.bound (by positivity)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hlo₁ hlo₂
    obtain ⟨δ₁, hδ₁, hb₁⟩ := hlo₁
    obtain ⟨δ₂, hδ₂, hb₂⟩ := hlo₂
    set δ : ℝ := min δ₁ δ₂ / Lf'
    have hδ : 0 < δ := div_pos (lt_min hδ₁ hδ₂) hLf'
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
    have hempty : {z ∈ f '' s ∩ closedBall (f x₀) r |
        ε * dist z (f x₀) <
          ‖g z - g (f x₀) - L (P.orthogonalProjectionOnto (z - f x₀))‖} = ∅ := by
      apply eq_empty_of_forall_notMem
      rintro _ ⟨⟨⟨y, hys, rfl⟩, hzr⟩, hzerr⟩
      have hdist_f : dist (f y) (f x₀) < δ := (mem_closedBall.1 hzr).trans_lt hr
      have hdist_y_le : dist y x₀ ≤ Lf' * dist (f y) (f x₀) :=
        (hi.le_mul_dist ⟨y, hys⟩ ⟨x₀, hx₀⟩).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
      have hdist_y_lt : dist y x₀ < min δ₁ δ₂ := by
        calc dist y x₀ ≤ Lf' * dist (f y) (f x₀) := hdist_y_le
          _ < Lf' * δ := mul_lt_mul_of_pos_left hdist_f hLf'
          _ = min δ₁ δ₂ := by simp only [δ]; field_simp
      have h1 : ‖f y - f x₀ - A (y - x₀)‖ ≤ (ε / (3 * M)) * dist (f y) (f x₀) := by
        calc ‖f y - f x₀ - A (y - x₀)‖
            ≤ (ε / (3 * M * Lf')) * dist y x₀ := by
              simpa only [dist_eq_norm] using hb₁ (hdist_y_lt.trans_le (min_le_left _ _)) hys
          _ ≤ (ε / (3 * M * Lf')) * (Lf' * dist (f y) (f x₀)) :=
              mul_le_mul_of_nonneg_left hdist_y_le (by positivity)
          _ = (ε / (3 * M)) * dist (f y) (f x₀) := by field_simp
      have h2 : ‖g (f y) - g (f x₀) - B (y - x₀)‖ ≤ (ε / 3) * dist (f y) (f x₀) := by
        calc ‖g (f y) - g (f x₀) - B (y - x₀)‖
            ≤ (ε / (3 * Lf')) * dist y x₀ := by
              simpa only [dist_eq_norm] using hb₂ (hdist_y_lt.trans_le (min_le_right _ _)) hys
          _ ≤ (ε / (3 * Lf')) * (Lf' * dist (f y) (f x₀)) :=
              mul_le_mul_of_nonneg_left hdist_y_le (by positivity)
          _ = (ε / 3) * dist (f y) (f x₀) := by field_simp
      have hproj_A : P.orthogonalProjectionOnto (A (y - x₀)) =
          ⟨A (y - x₀), LinearMap.mem_range_self _ _⟩ := by
        apply Subtype.ext
        rw [Submodule.coe_orthogonalProjectionOnto_apply,
          P.starProjection_eq_self_iff.2 (show A (y - x₀) ∈ P from ⟨y - x₀, rfl⟩)]
      have hdecomp : g (f y) - g (f x₀) - L (P.orthogonalProjectionOnto (f y - f x₀)) =
          (g (f y) - g (f x₀) - B (y - x₀)) -
            L (P.orthogonalProjectionOnto (f y - f x₀ - A (y - x₀))) := by
        have hsub : f y - f x₀ = (f y - f x₀ - A (y - x₀)) + A (y - x₀) := by abel
        rw [← hLA (y - x₀), ← hproj_A]
        conv_lhs => rw [hsub, map_add, map_add]
        abel
      have h3 : ‖L (P.orthogonalProjectionOnto (f y - f x₀ - A (y - x₀)))‖ ≤
          (ε / 3) * dist (f y) (f x₀) := by
        calc ‖L (P.orthogonalProjectionOnto (f y - f x₀ - A (y - x₀)))‖
            ≤ ‖L‖ * ‖P.orthogonalProjectionOnto (f y - f x₀ - A (y - x₀))‖ :=
                L.le_opNorm _
          _ ≤ M * ‖f y - f x₀ - A (y - x₀)‖ :=
              mul_le_mul (le_max_left _ _) (P.norm_orthogonalProjectionOnto_apply_le _)
                (norm_nonneg _) hM.le
          _ ≤ M * ((ε / (3 * M)) * dist (f y) (f x₀)) := mul_le_mul_of_nonneg_left h1 hM.le
          _ = (ε / 3) * dist (f y) (f x₀) := by field_simp
      have htot : ‖g (f y) - g (f x₀) - L (P.orthogonalProjectionOnto (f y - f x₀))‖ ≤
          ε * dist (f y) (f x₀) := by
        have : 0 ≤ dist (f y) (f x₀) := dist_nonneg
        calc ‖g (f y) - g (f x₀) - L (P.orthogonalProjectionOnto (f y - f x₀))‖
            ≤ ‖g (f y) - g (f x₀) - B (y - x₀)‖ +
                ‖L (P.orthogonalProjectionOnto (f y - f x₀ - A (y - x₀)))‖ := by
              rw [hdecomp]
              exact norm_sub_le _ _
          _ ≤ (ε / 3) * dist (f y) (f x₀) + (ε / 3) * dist (f y) (f x₀) := add_le_add h2 h3
          _ ≤ ε * dist (f y) (f x₀) := by nlinarith
      exact (not_lt_of_ge htot) hzerr
    rw [hempty, measure_empty, ENNReal.zero_div]
  exact himg.of_tendsto_diff (by
    rw [sdiff_eq_empty.2 hfs]
    simp only [empty_inter, measure_empty, ENNReal.zero_div, tendsto_const_nhds]) hdiff

/-- Under the hypotheses of `hasTangentialFDerivAt_of_tendsto_diff`, `g` has a **unique**
tangential derivative on `approxTangentPlane (finrank ℝ U) E (f x₀)`. -/
theorem existsUnique_hasTangentialFDerivAt_of_tendsto_diff
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s)
    (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r =>
      μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s x₀) :
    ∃! L : TauCeti.approxTangentPlane (finrank ℝ U) E (f x₀) →L[ℝ] W,
      TauCeti.HasTangentialFDerivAt (finrank ℝ U) g
        (TauCeti.approxTangentPlane (finrank ℝ U) E (f x₀)) L E (f x₀) := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs
  have hL := hf.hasTangentialFDerivAt_of_tendsto_diff hx₀ hi hs hinj hfs hdiff hgf
  exact TauCeti.existsUnique_hasTangentialFDerivAt_of_unique
    (hf.existsUnique_isApproxTangentPlane_of_tendsto_diff hx₀ hi hs hfs hdiff) hL
    fun L' hL' => hf.hasTangentialFDerivAt_unique hx₀ hi hs hfs hL' hL

/-- **Chart chain rule for `tangentialFDeriv`.** Composing the ambient tangential derivative
`(tangentialFDeriv (finrank ℝ U) g E (f x₀)).comp orthogonalProjectionOnto` with the chart
derivative `A` recovers the parameter-space derivative `B` of `g ∘ f`. -/
theorem tangentialFDeriv_comp_orthogonalProjectionOnto_comp_eq
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s)
    (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r =>
      μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s x₀) :
    ((TauCeti.tangentialFDeriv (finrank ℝ U) g E (f x₀)).comp
      (TauCeti.approxTangentPlane (finrank ℝ U) E (f x₀)).orthogonalProjectionOnto).comp A =
        B := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs
  have hL := hf.hasTangentialFDerivAt_of_tendsto_diff hx₀ hi hs hinj hfs hdiff hgf
  rw [TauCeti.tangentialFDeriv_comp_orthogonalProjectionOnto_eq_of_unique
    (hf.existsUnique_isApproxTangentPlane_of_tendsto_diff hx₀ hi hs hfs hdiff) hL
    fun L' hL' => hf.hasTangentialFDerivAt_unique hx₀ hi hs hfs hL' hL]
  ext u
  have hproj : (LinearMap.range A.toLinearMap).orthogonalProjectionOnto (A u) =
      LinearEquiv.ofInjective A.toLinearMap hinj u := by
    apply Subtype.ext
    rw [Submodule.coe_orthogonalProjectionOnto_apply]
    exact (LinearMap.range A.toLinearMap).starProjection_eq_self_iff.2 ⟨u, rfl⟩
  simp only [ContinuousLinearMap.comp_apply, hproj, LinearMap.coe_toContinuousLinearMap']
  exact congrArg B ((LinearEquiv.ofInjective A.toLinearMap hinj).symm_apply_apply u)

/-- **Explicit ambient operator formula for `tangentialFDeriv`** in a complete inner product space:
`(tangentialFDeriv k g E (f x₀)).comp orthogonalProjectionOnto = B ∘L (A† ∘L A)⁻¹ ∘L A†`. -/
theorem tangentialFDeriv_comp_orthogonalProjectionOnto_eq [CompleteSpace V]
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s)
    (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r =>
      μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s x₀) :
    (TauCeti.tangentialFDeriv (finrank ℝ U) g E (f x₀)).comp
      (TauCeti.approxTangentPlane (finrank ℝ U) E (f x₀)).orthogonalProjectionOnto =
      B.comp ((Ring.inverse (A.adjoint.comp A)).comp A.adjoint) := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs
  have hL := hf.hasTangentialFDerivAt_of_tendsto_diff hx₀ hi hs hinj hfs hdiff hgf
  rw [TauCeti.tangentialFDeriv_comp_orthogonalProjectionOnto_eq_of_unique
    (hf.existsUnique_isApproxTangentPlane_of_tendsto_diff hx₀ hi hs hfs hdiff) hL
    fun L' hL' => hf.hasTangentialFDerivAt_unique hx₀ hi hs hfs hL' hL]
  have hinj_gram : Injective (A.adjoint.comp A) := fun u₁ u₂ hu => by
    have h0 : (A.adjoint.comp A) (u₁ - u₂) = 0 := by rw [map_sub, hu, sub_self]
    have hinner : inner ℝ (A (u₁ - u₂)) (A (u₁ - u₂)) = 0 := by
      rw [← A.adjoint_inner_left]
      change inner ℝ ((A.adjoint.comp A) (u₁ - u₂)) (u₁ - u₂) = 0
      rw [h0, inner_zero_left]
    exact sub_eq_zero.1 (hinj (by simpa [inner_self_eq_zero] using hinner))
  have hunit : IsUnit (A.adjoint.comp A) :=
    ContinuousLinearMap.isUnit_iff_bijective.2
      ⟨hinj_gram, LinearMap.injective_iff_surjective.1 hinj_gram⟩
  ext v
  set u : U := Ring.inverse (A.adjoint.comp A) (A.adjoint v)
  have hproj : (LinearMap.range A.toLinearMap).orthogonalProjectionOnto v =
      LinearEquiv.ofInjective A.toLinearMap hinj u := by
    apply Subtype.ext
    rw [Submodule.coe_orthogonalProjectionOnto_apply]
    change (LinearMap.range A.toLinearMap).starProjection v = A u
    refine (LinearMap.range A.toLinearMap).eq_starProjection_of_mem_of_inner_eq_zero
      (show A u ∈ LinearMap.range A.toLinearMap from ⟨u, rfl⟩) ?_
    rintro _ ⟨u', rfl⟩
    change inner ℝ (v - A u) (A u') = 0
    rw [← A.adjoint_inner_left]
    have hcancel : A.adjoint (v - A u) = 0 := by
      rw [map_sub]
      change A.adjoint v - (A.adjoint.comp A) (Ring.inverse (A.adjoint.comp A) (A.adjoint v)) = 0
      rw [ContinuousLinearMap.apply_ringInverse_apply hunit, sub_self]
    rw [hcancel, inner_zero_left]
  simp only [ContinuousLinearMap.comp_apply, hproj, LinearMap.coe_toContinuousLinearMap']
  exact congrArg B ((LinearEquiv.ofInjective A.toLinearMap hinj).symm_apply_apply u)

/-- **Jacobian factorization along a parametrization.** When the target `W₀` is a real inner
product space, `(tangentialFDeriv (finrank ℝ U) g E (f x₀)).normDet * A.normDet = B.normDet`. -/
theorem normDet_tangentialFDeriv_mul_eq
    {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    {g : V → W₀} {B : U →L[ℝ] W₀}
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s)
    (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r =>
      μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s x₀) :
    (TauCeti.tangentialFDeriv (finrank ℝ U) g E (f x₀)).normDet * A.normDet = B.normDet := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs
  set P := LinearMap.range A.toLinearMap
  have hL := hf.hasTangentialFDerivAt_of_tendsto_diff hx₀ hi hs hinj hfs hdiff hgf
  rw [TauCeti.normDet_tangentialFDeriv_eq_of_unique
    (hf.existsUnique_isApproxTangentPlane_of_tendsto_diff hx₀ hi hs hfs hdiff) hL
    fun L' hL' => hf.hasTangentialFDerivAt_unique hx₀ hi hs hfs hL' hL]
  let A' : U →ₗ[ℝ] P := A.toLinearMap.codRestrict P (LinearMap.mem_range_self _)
  have hcomp :
      (B.comp (LinearEquiv.ofInjective A.toLinearMap hinj).symm.toContinuousLinearMap).toLinearMap
        ∘ₗ A' = B.toLinearMap := by
    ext u
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', A']
    have heq : (A.toLinearMap.codRestrict P (LinearMap.mem_range_self _) u : P) =
        LinearEquiv.ofInjective A.toLinearMap hinj u := rfl
    rw [heq]
    exact congrArg B ((LinearEquiv.ofInjective A.toLinearMap hinj).symm_apply_apply u)
  have hfin : finrank ℝ U = finrank ℝ P := (LinearMap.finrank_range_of_inj hinj).symm
  calc (B.comp (LinearEquiv.ofInjective A.toLinearMap hinj).symm.toContinuousLinearMap).normDet *
        A.normDet
      = (B.comp (LinearEquiv.ofInjective A.toLinearMap hinj).symm.toContinuousLinearMap).normDet *
          A'.normDet := by rw [LinearMap.normDet_codRestrict]
    _ = B.normDet := by
        rw [← LinearMap.normDet_comp_of_finrank_eq A' _ hfin, hcomp]

/-- Explicit quotient formula for the tangential Jacobian:
`(tangentialFDeriv (finrank ℝ U) g E (f x₀)).normDet = B.normDet / A.normDet`. -/
theorem normDet_tangentialFDeriv_eq_div
    {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    {g : V → W₀} {B : U →L[ℝ] W₀}
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s)
    (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r =>
      μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s x₀) :
    (TauCeti.tangentialFDeriv (finrank ℝ U) g E (f x₀)).normDet = B.normDet / A.normDet := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs
  have hAne : A.normDet ≠ 0 := fun h0 =>
    (LinearMap.normDet_eq_zero_iff_ker_ne_bot.1 h0) (LinearMap.ker_eq_bot.2 hinj)
  exact eq_div_of_mul_eq hAne
    (hf.normDet_tangentialFDeriv_mul_eq hx₀ hi hs hfs hdiff hgf)

end HasFDerivWithinAt

/-! ### Rademacher tangential differentiability and measurability on rectifiable sets -/

/-- Shared bi-Lipschitz chart differentiation and Hausdorff density helper given a globally
Lipschitz extension `g₀` agreeing with `g` on `E`. -/
private theorem ae_chart_good_of_extend
    {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {f : U → V} {g g₀ : V → W} {s : Set U} {E : Set V} {Kf Lf Kg₀ : ℝ≥0}
    (hf : LipschitzWith Kf f) (hs : MeasurableSet s) (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hfs : f '' s ⊆ E) (hEm : NullMeasurableSet E μHE[finrank ℝ U])
    [IsLocallyFiniteMeasure (μHE[finrank ℝ U].restrict E)]
    (hg₀ : LipschitzWith Kg₀ g₀) (hgg₀ : EqOn g g₀ E) :
    ∀ᵐ y ∂μHE[finrank ℝ U], y ∈ f '' s →
      ∃ x ∈ s, f x = y ∧ DifferentiableAt ℝ f x ∧
        HasFDerivWithinAt (g ∘ f) (fderiv ℝ (g₀ ∘ f) x) s x ∧
        Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r))
          (𝓝[>] 0) (𝓝 1) ∧
        Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x) r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r))
          (𝓝[>] 0) (𝓝 0) := by
  set k := finrank ℝ U
  have hcomp_eq : EqOn (g ∘ f) (g₀ ∘ f) s := fun x hx => hgg₀ (hfs (mem_image_of_mem f hx))
  have hparam : ∀ᵐ x ∂(volume : Measure U), x ∈ s →
      DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ (g₀ ∘ f) x ∧
        Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r))
          (𝓝[>] 0) (𝓝 1) := by
    filter_upwards [hf.ae_differentiableAt, (hg₀.comp hf).ae_differentiableAt,
      (ae_restrict_iff' hs).1 (Besicovitch.ae_tendsto_measure_inter_div volume s)]
      with x hdf hdg hdens hxs
    exact ⟨hdf, hdg, hdens hxs⟩
  set N : Set U := {x ∈ s | ¬ (DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ (g₀ ∘ f) x ∧
    Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 1))}
  have hN_vol : volume N = 0 := by
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hparam)
    exact fun h => hx.2 (h hx.1)
  have hN_img : μHE[k] (f '' N) = 0 := by
    have hN_haus : μHE[k] N = 0 := by
      rwa [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    refine nonpos_iff_eq_zero.1 ?_
    exact (hf.lipschitzOnWith.euclideanHausdorffMeasure_image_le k).trans_eq
      (by rw [hN_haus, mul_zero])
  have hf_meas : MeasurableSet (f '' s) :=
    hs.image_of_continuousOn_injOn hf.continuous.continuousOn (injOn_iff_injective.2 hi.injective)
  have : IsLocallyFiniteMeasure (μHE[k].restrict (E \ f '' s)) := by
    rw [Set.sdiff_eq, inter_comm, ← Measure.restrict_restrict hf_meas.compl]
    infer_instance
  have hdiff_zero :=
    TauCeti.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div_of_isLocallyFiniteMeasure k
      (hEm.diff hf_meas.nullMeasurableSet)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN_img, hdiff_zero] with y hyN hzero hyfs
  obtain ⟨x, hxs, rfl⟩ := hyfs
  have hx_good : DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ (g₀ ∘ f) x ∧
      Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r))
        (𝓝[>] 0) (𝓝 1) := by
    by_contra hx_bad
    exact hyN ⟨x, ⟨hxs, hx_bad⟩, rfl⟩
  exact ⟨x, hxs, rfl, hx_good.1,
    (hx_good.2.1.hasFDerivAt.hasFDerivWithinAt (s := s)).congr hcomp_eq (hcomp_eq hxs),
    hx_good.2.2, hzero fun h => h.2 (mem_image_of_mem f hxs)⟩

/-- **Chart-level tangential differentiability of Lipschitz maps.** Let `f : U → V` be globally
Lipschitz and `Lf`-antilipschitz on a Borel set `s ⊆ U` with `f '' s ⊆ E`, where `E` is
`μHE[finrank ℝ U]`-null-measurable with locally finite restricted measure, and let `g : V → W`
be `Kg`-Lipschitz on `E` into a finite-dimensional real normed space `W`. Then at
`μHE[finrank ℝ U]`-almost every `y ∈ f '' s`, `g` has a unique tangential derivative along `E`
at `y`, with norm at most `Kg` and satisfying the chart chain rule against
`fderivWithin ℝ (g ∘ f) s`. In particular `tangentialFDeriv` is independent of the chosen
bi-Lipschitz chart. -/
theorem LipschitzWith.ae_existsUnique_hasTangentialFDerivAt_image
    {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {f : U → V} {g : V → W} {s : Set U} {E : Set V} {Kf Lf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hs : MeasurableSet s) (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hfs : f '' s ⊆ E) (hEm : NullMeasurableSet E μHE[finrank ℝ U])
    [IsLocallyFiniteMeasure (μHE[finrank ℝ U].restrict E)] (hg : LipschitzOnWith Kg g E) :
    ∀ᵐ y ∂μHE[finrank ℝ U], y ∈ f '' s →
      ∃ x ∈ s, f x = y ∧ DifferentiableAt ℝ f x ∧
        DifferentiableWithinAt ℝ (g ∘ f) s x ∧
        (∃! L : TauCeti.approxTangentPlane (finrank ℝ U) E y →L[ℝ] W,
          TauCeti.HasTangentialFDerivAt (finrank ℝ U) g
            (TauCeti.approxTangentPlane (finrank ℝ U) E y) L E y) ∧
        ‖TauCeti.tangentialFDeriv (finrank ℝ U) g E y‖ ≤ Kg ∧
        ((TauCeti.tangentialFDeriv (finrank ℝ U) g E y).comp
          (TauCeti.approxTangentPlane (finrank ℝ U) E y).orthogonalProjectionOnto).comp
            (fderiv ℝ f x) = fderivWithin ℝ (g ∘ f) s x := by
  obtain ⟨g₀, hg₀, hgg₀⟩ := hg.extend_finite_dimension
  filter_upwards [ae_chart_good_of_extend hf hs hi hfs hEm hg₀ hgg₀] with y hy hyfs
  obtain ⟨x, hxs, rfl, hdf, hfdw_gf, hdens, hz⟩ := hy hyfs
  have hfdw_f := hdf.hasFDerivAt.hasFDerivWithinAt (s := s)
  have huniq_s : UniqueDiffWithinAt ℝ s x :=
    volume.uniqueDiffWithinAt_of_tendsto_inter_closedBall_div hdens
  have hex := hfdw_f.existsUnique_hasTangentialFDerivAt_of_tendsto_diff hxs hi hdens hfs
    hz hfdw_gf
  refine ⟨x, hxs, rfl, hdf, hfdw_gf.differentiableWithinAt, hex,
    hfdw_f.opNorm_le_of_hasTangentialFDerivAt hxs hi hdens hfs hg
      (TauCeti.hasTangentialFDerivAt_tangentialFDeriv hex), ?_⟩
  rw [hfdw_gf.fderivWithin huniq_s]
  exact hfdw_f.tangentialFDeriv_comp_orthogonalProjectionOnto_comp_eq hxs hi hdens hfs hz hfdw_gf

namespace TauCeti

section Rectifiable

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] {k : ℕ} {E : Set V} {g : V → W} {K : ℝ≥0}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
private theorem existsUnique_hasTangentialFDerivAt_congr_dim
    {n₁ n₂ : ℕ} (hn : n₁ = n₂) {y : V} :
    (∃! L : approxTangentPlane n₁ E y →L[ℝ] W,
      HasTangentialFDerivAt n₁ g (approxTangentPlane n₁ E y) L E y) ↔
    (∃! L : approxTangentPlane n₂ E y →L[ℝ] W,
      HasTangentialFDerivAt n₂ g (approxTangentPlane n₂ E y) L E y) := by
  subst hn
  rfl

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
private theorem norm_tangentialFDeriv_congr_dim {n₁ n₂ : ℕ} (hn : n₁ = n₂) {y : V} :
    ‖tangentialFDeriv n₁ g E y‖ = ‖tangentialFDeriv n₂ g E y‖ := by
  subst hn
  rfl

private theorem CountablyRectifiable.ae_existsUnique_and_norm_le
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hg : LipschitzOnWith K g E) :
    ∀ᵐ x ∂μHE[k], x ∈ E →
      (∃! L : approxTangentPlane k E x →L[ℝ] W,
        HasTangentialFDerivAt k g (approxTangentPlane k E x) L E x) ∧
      ‖tangentialFDeriv k g E x‖ ≤ K := by
  obtain ⟨E₀, hE₀E, hE₀m, hE₀ae⟩ := hEm.exists_measurable_subset_ae_eq
  obtain ⟨A, f, hAm, hbi, hcover⟩ := (hE.congr hE₀ae.symm).exists_bilipschitz_cover
  choose Kf Lf hLip hAnti using hbi
  let A' (n : ℕ) : Set (EuclideanSpace ℝ (Fin k)) := A n ∩ f n ⁻¹' E₀
  have hA'm (n : ℕ) : MeasurableSet (A' n) :=
    (hAm n).inter (hE₀m.preimage (hLip n).continuous.measurable)
  have hA'anti (n : ℕ) : AntilipschitzWith (Lf n) ((A' n).domRestrict (f n)) :=
    fun x y => hAnti n ⟨x, x.2.1⟩ ⟨y, y.2.1⟩
  have hA'sub (n : ℕ) : f n '' A' n ⊆ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact hE₀E hx.2
  have hk : finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  have : IsLocallyFiniteMeasure (μHE[finrank ℝ (EuclideanSpace ℝ (Fin k))].restrict E) := by
    simpa only [hk] using ‹IsLocallyFiniteMeasure (μHE[k].restrict E)›
  have hpatch (n : ℕ) : ∀ᵐ y ∂μHE[k], y ∈ f n '' A' n →
      (∃! L : approxTangentPlane k E y →L[ℝ] W,
        HasTangentialFDerivAt k g (approxTangentPlane k E y) L E y) ∧
      ‖tangentialFDeriv k g E y‖ ≤ K := by
    have h := (hLip n).ae_existsUnique_hasTangentialFDerivAt_image (hA'm n) (hA'anti n)
      (hA'sub n) (by simpa only [hk] using hEm) hg
    have h' : ∀ᵐ y ∂μHE[k], y ∈ f n '' A' n →
        (∃! L : approxTangentPlane (finrank ℝ (EuclideanSpace ℝ (Fin k))) E y →L[ℝ] W,
          HasTangentialFDerivAt (finrank ℝ (EuclideanSpace ℝ (Fin k))) g
            (approxTangentPlane (finrank ℝ (EuclideanSpace ℝ (Fin k))) E y) L E y) ∧
        ‖tangentialFDeriv (finrank ℝ (EuclideanSpace ℝ (Fin k))) g E y‖ ≤ K := by
      have hmeas_eq : (μHE[finrank ℝ (EuclideanSpace ℝ (Fin k))] : Measure V) = μHE[k] := by
        rw [hk]
      rw [← hmeas_eq]
      exact h.mono fun y hy hyfs =>
        ⟨(hy hyfs).choose_spec.2.2.2.2.1, (hy hyfs).choose_spec.2.2.2.2.2.1⟩
    exact h'.mono fun y hy hyfs =>
      ⟨(existsUnique_hasTangentialFDerivAt_congr_dim hk).1 (hy hyfs).1,
        (norm_tangentialFDeriv_congr_dim hk).symm.trans_le (hy hyfs).2⟩
  have hcov : μHE[k] (E \ ⋃ n, f n '' A' n) = 0 := by
    have h1 : μHE[k] (E \ E₀) = 0 := (ae_eq_set.1 hE₀ae.symm).1
    refine measure_mono_null (fun y ⟨hyE, hyU⟩ => ?_) (measure_union_null h1 hcover)
    by_cases hyE₀ : y ∈ E₀
    · refine Or.inr ⟨hyE₀, fun hyA => hyU ?_⟩
      obtain ⟨n, x, hx, rfl⟩ := mem_iUnion.1 hyA
      exact mem_iUnion.2 ⟨n, x, ⟨hx, hyE₀⟩, rfl⟩
    · exact Or.inl ⟨hyE, hyE₀⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hcov, ae_all_iff.2 hpatch] with x hcovx hpx hxE
  obtain ⟨n, hxn⟩ := mem_iUnion.1 (not_not.1 fun h => hcovx ⟨hxE, h⟩)
  exact hpx n hxn

/-- **Rademacher's theorem on countably `k`-rectifiable sets.** Let `E` be a null-measurable,
countably `k`-rectifiable subset of `V` with locally finite `μHE[k]` measure, and let `g : V → W`
be `K`-Lipschitz on `E` into a finite-dimensional real normed space `W`. Then at `μHE[k]`-almost
every `x ∈ E`, `g` has a **unique** tangential derivative along `E` on `approxTangentPlane k E x`.
-/
theorem CountablyRectifiable.ae_existsUnique_hasTangentialFDerivAt
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hg : LipschitzOnWith K g E) :
    ∀ᵐ x ∂μHE[k], x ∈ E →
      ∃! L : approxTangentPlane k E x →L[ℝ] W,
        HasTangentialFDerivAt k g (approxTangentPlane k E x) L E x :=
  (hE.ae_existsUnique_and_norm_le hEm hg).mono fun _ hx hxE => (hx hxE).1

/-- At `μHE[k]`-almost every point of a null-measurable, countably `k`-rectifiable set `E` with
locally finite `μHE[k]` measure, `tangentialFDeriv k g E x` satisfies `HasTangentialFDerivAt`. -/
theorem CountablyRectifiable.ae_hasTangentialFDerivAt_tangentialFDeriv
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hg : LipschitzOnWith K g E) :
    ∀ᵐ x ∂μHE[k], x ∈ E →
      HasTangentialFDerivAt k g (approxTangentPlane k E x) (tangentialFDeriv k g E x) E x := by
  filter_upwards [hE.ae_existsUnique_hasTangentialFDerivAt hEm hg] with x hx hxE
  exact hasTangentialFDerivAt_tangentialFDeriv (hx hxE)

/-- The operator norm of `tangentialFDeriv k g E x` is bounded by the Lipschitz constant `K` at
`μHE[k]`-almost every `x ∈ E`. -/
theorem CountablyRectifiable.ae_norm_tangentialFDeriv_le
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hg : LipschitzOnWith K g E) :
    ∀ᵐ x ∂μHE[k], x ∈ E → ‖tangentialFDeriv k g E x‖ ≤ K :=
  (hE.ae_existsUnique_and_norm_le hEm hg).mono fun _ hx hxE => (hx hxE).2

/-- Helper gluing patchwise measurable fields on bi-Lipschitz charts into an `AEMeasurable` field
on `μHE[k].restrict E`. -/
private theorem CountablyRectifiable.aemeasurable_of_bilipschitz_patches
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    (Ψ : V → α)
    (hchart : ∀ {Kf Lf : ℝ≥0} {f : EuclideanSpace ℝ (Fin k) → V}
      {s : Set (EuclideanSpace ℝ (Fin k))},
      LipschitzWith Kf f → MeasurableSet s → AntilipschitzWith Lf (s.domRestrict f) →
      f '' s ⊆ E →
      ∃ Φ : V → α, Measurable Φ ∧ ∀ᵐ y ∂μHE[k], y ∈ f '' s → Ψ y = Φ y) :
    AEMeasurable Ψ (μHE[k].restrict E) := by
  classical
  obtain ⟨E₀, hE₀E, hE₀m, hE₀ae⟩ := hEm.exists_measurable_subset_ae_eq
  obtain ⟨A, f, hAm, hbi, hcover⟩ := (hE.congr hE₀ae.symm).exists_bilipschitz_cover
  choose Kf Lf hLip hAnti using hbi
  let A' (n : ℕ) : Set (EuclideanSpace ℝ (Fin k)) := A n ∩ f n ⁻¹' E₀
  have hA'm (n : ℕ) : MeasurableSet (A' n) :=
    (hAm n).inter (hE₀m.preimage (hLip n).continuous.measurable)
  have hA'anti (n : ℕ) : AntilipschitzWith (Lf n) ((A' n).domRestrict (f n)) :=
    fun x y => hAnti n ⟨x, x.2.1⟩ ⟨y, y.2.1⟩
  have hA'sub (n : ℕ) : f n '' A' n ⊆ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact hE₀E hx.2
  let S (n : ℕ) : Set V := f n '' A' n
  have hSm (n : ℕ) : MeasurableSet (S n) :=
    (hA'm n).image_of_continuousOn_injOn (hLip n).continuous.continuousOn
      (injOn_iff_injective.2 (hA'anti n).injective)
  choose Φ hΦm hΦ using fun n => hchart (hLip n) (hA'm n) (hA'anti n) (hA'sub n)
  let Uset := ⋃ n, S n
  have hindex (x : Uset) : ∃ n, (x : V) ∈ S n := mem_iUnion.1 x.property
  let F : Uset → α := fun x => Φ (Nat.find (hindex x)) x
  have hFm : Measurable F := Measurable.find
    (fun n => (hΦm n).comp measurable_subtype_coe)
    (fun n => (hSm n).preimage measurable_subtype_coe) hindex
  obtain ⟨G, hGm, hG⟩ :=
    (MeasurableEmbedding.subtype_coe (MeasurableSet.iUnion hSm)).exists_measurable_extend
      hFm (fun _ => inferInstance)
  have hcov : μHE[k] (E \ Uset) = 0 := by
    have h1 : μHE[k] (E \ E₀) = 0 := (ae_eq_set.1 hE₀ae.symm).1
    refine measure_mono_null (fun y ⟨hyE, hyU⟩ => ?_) (measure_union_null h1 hcover)
    by_cases hyE₀ : y ∈ E₀
    · refine Or.inr ⟨hyE₀, fun hyA => hyU ?_⟩
      obtain ⟨n, x, hx, rfl⟩ := mem_iUnion.1 hyA
      exact mem_iUnion.2 ⟨n, x, ⟨hx, hyE₀⟩, rfl⟩
    · exact Or.inl ⟨hyE, hyE₀⟩
  refine hGm.aemeasurable.congr ((ae_restrict_iff'₀ hEm).2 ?_)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hcov, ae_all_iff.2 hΦ] with x hcovx hΦx hxE
  have hxU : x ∈ Uset := not_not.1 fun h => hcovx ⟨hxE, h⟩
  let n := Nat.find (hindex ⟨x, hxU⟩)
  have hxn : x ∈ S n := Nat.find_spec (hindex ⟨x, hxU⟩)
  exact (congrFun hG ⟨x, hxU⟩).trans (hΦx n hxn).symm

/-- **Measurability of the ambient tangential derivative field.** For a null-measurable, countably
`k`-rectifiable set `E` with locally finite `μHE[k]` measure and a `K`-Lipschitz map `g : V → W`
into a finite-dimensional normed space `W`, the operator field
`x ↦ (tangentialFDeriv k g E x).comp (approxTangentPlane k E x).orthogonalProjectionOnto` is
`(μHE[k].restrict E)`-almost everywhere measurable. -/
theorem CountablyRectifiable.aemeasurable_tangentialFDeriv_comp_orthogonalProjectionOnto
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hg : LipschitzOnWith K g E) :
    AEMeasurable (fun x =>
      (tangentialFDeriv k g E x).comp (approxTangentPlane k E x).orthogonalProjectionOnto)
      (μHE[k].restrict E) := by
  obtain ⟨g₀, hg₀, hgg₀⟩ := hg.extend_finite_dimension
  have hk : finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  have : IsLocallyFiniteMeasure (μHE[finrank ℝ (EuclideanSpace ℝ (Fin k))].restrict E) := by
    simpa only [hk] using ‹IsLocallyFiniteMeasure (μHE[k].restrict E)›
  refine hE.aemeasurable_of_bilipschitz_patches hEm _ ?_
  intro Kf Lf f s hf hs hi hfs
  have he : MeasurableEmbedding (s.domRestrict f) :=
    hf.continuous.continuousOn.measurableEmbedding hs (injOn_iff_injective.2 hi.injective)
  have hAf_meas : Measurable (fderiv ℝ f) := measurable_fderiv ℝ f
  have hBf_meas : Measurable (fderiv ℝ (g₀ ∘ f)) := measurable_fderiv ℝ (g₀ ∘ f)
  have hAadj_meas : Measurable (fun x => (fderiv ℝ f x).adjoint) := by
    simpa only [Function.comp_def, ContinuousLinearMap.adjointRealCLM_apply] using
      ContinuousLinearMap.adjointRealCLM.continuous.measurable.comp hAf_meas
  have hgram_meas : Measurable (fun x => (fderiv ℝ f x).adjoint.comp (fderiv ℝ f x)) :=
    (continuous_fst.clm_comp continuous_snd).measurable.comp (hAadj_meas.prodMk hAf_meas)
  have hinv_meas : Measurable (fun x =>
      (Ring.inverse ((fderiv ℝ f x).adjoint.comp (fderiv ℝ f x))).comp
        (fderiv ℝ f x).adjoint) :=
    (continuous_fst.clm_comp continuous_snd).measurable.comp
      (hgram_meas.ringInverse.prodMk hAadj_meas)
  have htot_meas : Measurable (fun x =>
      (fderiv ℝ (g₀ ∘ f) x).comp
        ((Ring.inverse ((fderiv ℝ f x).adjoint.comp (fderiv ℝ f x))).comp
          (fderiv ℝ f x).adjoint)) :=
    (continuous_fst.clm_comp continuous_snd).measurable.comp (hBf_meas.prodMk hinv_meas)
  obtain ⟨Φ, hΦm, hΦ⟩ := he.exists_measurable_extend
    (htot_meas.comp measurable_subtype_coe) (fun _ => ⟨0⟩)
  refine ⟨Φ, hΦm, ?_⟩
  have hchart := ae_chart_good_of_extend hf hs hi hfs (by simpa only [hk] using hEm) hg₀ hgg₀
  have hmeas_eq : (μHE[finrank ℝ (EuclideanSpace ℝ (Fin k))] : Measure V) = μHE[k] := by
    rw [hk]
  rw [← hmeas_eq]
  refine hchart.mono fun y hy hyfs => ?_
  obtain ⟨x, hxs, rfl, hdf, hfdw_gf, hdens, hz⟩ := hy hyfs
  have hval :=
    (hdf.hasFDerivAt.hasFDerivWithinAt (s := s)).tangentialFDeriv_comp_orthogonalProjectionOnto_eq
      hxs hi hdens hfs hz hfdw_gf
  have aux {n₁ n₂ : ℕ} (hn : n₁ = n₂) :
      (tangentialFDeriv n₁ g E (f x)).comp
          (approxTangentPlane n₁ E (f x)).orthogonalProjectionOnto =
        (tangentialFDeriv n₂ g E (f x)).comp
          (approxTangentPlane n₂ E (f x)).orthogonalProjectionOnto := by
    subst hn
    rfl
  exact (aux hk).symm.trans (hval.trans (congrFun hΦ ⟨x, hxs⟩).symm)

/-- **Measurability of the tangential Jacobian `normDet`.** For a null-measurable, countably
`k`-rectifiable set `E` with locally finite `μHE[k]` measure and a `K`-Lipschitz map `g : V → W₀`
into a finite-dimensional real inner product space `W₀`, the function
`x ↦ (tangentialFDeriv k g E x).normDet` is `(μHE[k].restrict E)`-almost everywhere measurable. -/
theorem CountablyRectifiable.aemeasurable_normDet_tangentialFDeriv
    {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    [FiniteDimensional ℝ W₀] {g : V → W₀}
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hg : LipschitzOnWith K g E) :
    AEMeasurable (fun x => (tangentialFDeriv k g E x).normDet) (μHE[k].restrict E) := by
  obtain ⟨g₀, hg₀, hgg₀⟩ := hg.extend_finite_dimension
  have hk : finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  have : IsLocallyFiniteMeasure (μHE[finrank ℝ (EuclideanSpace ℝ (Fin k))].restrict E) := by
    simpa only [hk] using ‹IsLocallyFiniteMeasure (μHE[k].restrict E)›
  refine hE.aemeasurable_of_bilipschitz_patches hEm _ ?_
  intro Kf Lf f s hf hs hi hfs
  have he : MeasurableEmbedding (s.domRestrict f) :=
    hf.continuous.continuousOn.measurableEmbedding hs (injOn_iff_injective.2 hi.injective)
  have hjac_meas : Measurable (fun x =>
      (fderiv ℝ (g₀ ∘ f) x).normDet / (fderiv ℝ f x).normDet) :=
    (ContinuousLinearMap.continuous_normDet.measurable.comp
      (measurable_fderiv ℝ (g₀ ∘ f))).div
      (ContinuousLinearMap.continuous_normDet.measurable.comp (measurable_fderiv ℝ f))
  obtain ⟨Φ, hΦm, hΦ⟩ := he.exists_measurable_extend
    (hjac_meas.comp measurable_subtype_coe) (fun _ => ⟨0⟩)
  refine ⟨Φ, hΦm, ?_⟩
  have hchart := ae_chart_good_of_extend hf hs hi hfs (by simpa only [hk] using hEm) hg₀ hgg₀
  have hmeas_eq : (μHE[finrank ℝ (EuclideanSpace ℝ (Fin k))] : Measure V) = μHE[k] := by
    rw [hk]
  rw [← hmeas_eq]
  refine hchart.mono fun y hy hyfs => ?_
  obtain ⟨x, hxs, rfl, hdf, hfdw_gf, hdens, hz⟩ := hy hyfs
  have hval := (hdf.hasFDerivAt.hasFDerivWithinAt (s := s)).normDet_tangentialFDeriv_eq_div
    hxs hi hdens hfs hz hfdw_gf
  have hdim_eq :
      (tangentialFDeriv (finrank ℝ (EuclideanSpace ℝ (Fin k))) g E (f x)).normDet =
      (tangentialFDeriv k g E (f x)).normDet := by
    have aux {n₁ n₂ : ℕ} (hn : n₁ = n₂) :
        (tangentialFDeriv n₁ g E (f x)).normDet = (tangentialFDeriv n₂ g E (f x)).normDet := by
      subst hn
      rfl
    exact aux hk
  exact hdim_eq.symm.trans (hval.trans (congrFun hΦ ⟨x, hxs⟩).symm)

end Rectifiable

end TauCeti
