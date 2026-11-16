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
import TauCeti.Analysis.Calculus.TangentCone.Haar
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.Analysis.Normed.Ring.Units
import TauCeti.Geometry.Euclidean.Volume.Density
import TauCeti.MeasureTheory.Constructions.BorelSpace.IsOpenUnits

/-!
# Tangential differentiation on rectifiable sets

A map `g : V → W` has **tangential derivative** `L : P →L[ℝ] W` along `E ⊆ V` at `x` on an
approximate tangent `k`-plane `P` (`TauCeti.HasTangentialFDerivAt`, `TauCeti.tangentialFDeriv`) if
points of `E ∩ closedBall x r` with Taylor error above `ε * dist z x` have `k`-density zero. Along
antilipschitz charts, tangential derivatives are unique with Lipschitz norm bound, chain rule, and
Jacobian factorization (`HasFDerivWithinAt.hasTangentialFDerivAt_unique`,
`HasFDerivWithinAt.normDet_tangentialFDeriv_mul_eq`), yielding Rademacher differentiability and
measurability (`TauCeti.CountablyRectifiable.ae_existsUnique_hasTangentialFDerivAt`,
`TauCeti.CountablyRectifiable.aemeasurable_normDet_tangentialFDeriv`).

## References
* L. Simon, *Lectures on Geometric Measure Theory*, §11–§12; H. Federer, *GMT*, §3.2.16–3.2.19.
-/

public section

open Filter Function Metric MeasureTheory Module Set
open scoped ENNReal NNReal symmDiff Topology

namespace TauCeti
section Basic

variable {V W W' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']

/-- `HasTangentialFDerivAt k g P L E x` means `P` is an approximate tangent `k`-plane to `E` at `x`
and `L : P →L[ℝ] W` approximates `g z - g x` along `E` up to `k`-density-zero error. -/
structure HasTangentialFDerivAt (k : ℕ) (g : V → W) (P : Submodule ℝ V)
    [P.HasOrthogonalProjection] (L : P →L[ℝ] W) (E : Set V) (x : V) : Prop where
  /-- `P` is an approximate tangent `k`-plane to `E` at `x`. -/
  isApproxTangentPlane : IsApproxTangentPlane k E P x
  /-- Points of `E` with tangential Taylor error above `ε * dist z x` have `k`-density zero. -/
  tendsto_outside_error_div : ∀ ε > (0 : ℝ), Tendsto (fun r =>
    μHE[k] {z ∈ E ∩ closedBall x r |
      ε * dist z x < ‖g z - g x - L (P.orthogonalProjectionOnto (z - x))‖} /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)

/-- Characterization of `HasTangentialFDerivAt` unpacking its two conditions. -/
theorem hasTangentialFDerivAt_iff {k : ℕ} {g : V → W} {P : Submodule ℝ V}
    [P.HasOrthogonalProjection] {L : P →L[ℝ] W} {E : Set V} {x : V} :
    HasTangentialFDerivAt k g P L E x ↔ IsApproxTangentPlane k E P x ∧
      ∀ ε > (0 : ℝ), Tendsto (fun r =>
        μHE[k] {z ∈ E ∩ closedBall x r |
          ε * dist z x < ‖g z - g x - L (P.orthogonalProjectionOnto (z - x))‖} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- No map has a tangential derivative along the empty set. -/
@[simp] theorem not_hasTangentialFDerivAt_empty (k : ℕ) (g : V → W) (P : Submodule ℝ V)
    [P.HasOrthogonalProjection] (L : P →L[ℝ] W) (x : V) :
    ¬ HasTangentialFDerivAt k g P L (∅ : Set V) x := fun h =>
  not_isApproxTangentPlane_empty k P x h.isApproxTangentPlane

/-- The canonical tangential derivative of `g : V → W` along `E` at `x` (`0` if not unique). -/
noncomputable def tangentialFDeriv (k : ℕ) (g : V → W) (E : Set V) (x : V) :
    approxTangentPlane k E x →L[ℝ] W := open Classical in
  if h : ∃! L : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E x) L E x then h.choose else 0

/-- When unique on `approxTangentPlane`, `tangentialFDeriv` satisfies `HasTangentialFDerivAt`. -/
theorem hasTangentialFDerivAt_tangentialFDeriv {k : ℕ} {g : V → W} {E : Set V} {x : V}
    (h : ∃! L : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E x) L E x) :
    HasTangentialFDerivAt k g (approxTangentPlane k E x) (tangentialFDeriv k g E x) E x := by
  simpa only [tangentialFDeriv, h, ↓reduceDIte] using h.choose_spec.1

/-- When unique on `approxTangentPlane k E x`, `tangentialFDeriv k g E x` equals any witness `L`. -/
theorem tangentialFDeriv_eq_of_existsUnique {k : ℕ} {g : V → W} {E : Set V} {x : V}
    {L : approxTangentPlane k E x →L[ℝ] W} (h : ∃! L' : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E x) L' E x)
    (hL : HasTangentialFDerivAt k g (approxTangentPlane k E x) L E x) :
    tangentialFDeriv k g E x = L := h.unique (hasTangentialFDerivAt_tangentialFDeriv h) hL

/-- Outside the locus of unique existence, `tangentialFDeriv` takes the junk value `0`. -/
theorem tangentialFDeriv_of_not_existsUnique {k : ℕ} {g : V → W} {E : Set V} {x : V}
    (h : ¬ ∃! L : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E x) L E x) :
    tangentialFDeriv k g E x = 0 := by simp [tangentialFDeriv, h]

@[simp] theorem tangentialFDeriv_empty (k : ℕ) (g : V → W) (x : V) :
    tangentialFDeriv k g (∅ : Set V) x = 0 :=
  tangentialFDeriv_of_not_existsUnique fun ⟨_, h, _⟩ => not_hasTangentialFDerivAt_empty k g _ _ x h

@[simp] theorem tangentialFDeriv_zero (g : V → W) (E : Set V) (x : V) :
    tangentialFDeriv 0 g E x = 0 := by
  have : Subsingleton (approxTangentPlane 0 E x) := by rw [approxTangentPlane_zero]; infer_instance
  exact Subsingleton.elim _ _

private theorem existsUnique_and_apply_eq_of_unique {α : Type*} {k : ℕ} {g : V → W}
    {P : Submodule ℝ V} [inst : P.HasOrthogonalProjection] {L : P →L[ℝ] W} {E : Set V} {x : V}
    (Φ : ∀ (Q : Submodule ℝ V) [FiniteDimensional ℝ Q] [Q.HasOrthogonalProjection], (Q →L[ℝ] W) → α)
    (hP : ∃! Q : Submodule ℝ V, IsApproxTangentPlane k E Q x)
    (hL : HasTangentialFDerivAt k g P L E x)
    (huniq : ∀ L' : P →L[ℝ] W, HasTangentialFDerivAt k g P L' E x → L' = L) :
    (∃! L' : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E x) L' E x) ∧
    @Φ (approxTangentPlane k E x) inferInstance inferInstance (tangentialFDeriv k g E x) =
      @Φ P hL.isApproxTangentPlane.finiteDimensional inst L := by
  have heq := (approxTangentPlane_eq_of_existsUnique hP hL.isApproxTangentPlane).symm
  subst heq
  cases Subsingleton.elim inst inferInstance
  exact ⟨⟨L, hL, huniq⟩, by rw [tangentialFDeriv_eq_of_existsUnique ⟨L, hL, huniq⟩ hL]⟩

/-- Transporting unique tangential differentiability from `(P, L)` to `approxTangentPlane`. -/
theorem existsUnique_hasTangentialFDerivAt_of_unique {k : ℕ} {g : V → W} {P : Submodule ℝ V}
    [P.HasOrthogonalProjection] {L : P →L[ℝ] W} {E : Set V} {x : V}
    (hP : ∃! Q : Submodule ℝ V, IsApproxTangentPlane k E Q x)
    (hL : HasTangentialFDerivAt k g P L E x)
    (huniq : ∀ L' : P →L[ℝ] W, HasTangentialFDerivAt k g P L' E x → L' = L) :
    ∃! L' : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E x) L' E x :=
  (existsUnique_and_apply_eq_of_unique (fun _ _ _ _ => ()) hP hL huniq).1

/-- Evaluating any `FiniteDimensional`-parametric functional `Φ` on
`(approxTangentPlane k E x, tangentialFDeriv k g E x)` agrees with `Φ P L` for any unique witness
`(P, L)`. -/
theorem tangentialFDeriv_apply_eq_of_unique {α : Type*} {k : ℕ} {g : V → W}
    {P : Submodule ℝ V} [FiniteDimensional ℝ P] {L : P →L[ℝ] W} {E : Set V} {x : V}
    (Φ : ∀ (Q : Submodule ℝ V) [FiniteDimensional ℝ Q], (Q →L[ℝ] W) → α)
    (hP : ∃! Q : Submodule ℝ V, IsApproxTangentPlane k E Q x)
    (hL : HasTangentialFDerivAt k g P L E x)
    (huniq : ∀ L' : P →L[ℝ] W, HasTangentialFDerivAt k g P L' E x → L' = L) :
    Φ (approxTangentPlane k E x) (tangentialFDeriv k g E x) = Φ P L :=
  (existsUnique_and_apply_eq_of_unique (fun Q _ _ M => Φ Q M) hP hL huniq).2

/-- Identifying `(tangentialFDeriv k g E x).comp orthogonalProjectionOnto` from a unique witness. -/
theorem tangentialFDeriv_comp_orthogonalProjectionOnto_eq_of_unique {k : ℕ} {g : V → W}
    {P : Submodule ℝ V} [P.HasOrthogonalProjection] {L : P →L[ℝ] W} {E : Set V} {x : V}
    (hP : ∃! Q : Submodule ℝ V, IsApproxTangentPlane k E Q x)
    (hL : HasTangentialFDerivAt k g P L E x)
    (huniq : ∀ L' : P →L[ℝ] W, HasTangentialFDerivAt k g P L' E x → L' = L) :
    (tangentialFDeriv k g E x).comp (approxTangentPlane k E x).orthogonalProjectionOnto =
      L.comp P.orthogonalProjectionOnto :=
  have := hL.isApproxTangentPlane.finiteDimensional
  tangentialFDeriv_apply_eq_of_unique (fun Q _ M => M.comp Q.orthogonalProjectionOnto) hP hL huniq

/-- Identifying `‖tangentialFDeriv k g E x‖` from a unique witness `(P, L)`. -/
theorem norm_tangentialFDeriv_eq_of_unique {k : ℕ} {g : V → W} {P : Submodule ℝ V}
    [P.HasOrthogonalProjection] {L : P →L[ℝ] W} {E : Set V} {x : V}
    (hP : ∃! Q : Submodule ℝ V, IsApproxTangentPlane k E Q x)
    (hL : HasTangentialFDerivAt k g P L E x)
    (huniq : ∀ L' : P →L[ℝ] W, HasTangentialFDerivAt k g P L' E x → L' = L) :
    ‖tangentialFDeriv k g E x‖ = ‖L‖ :=
  have := hL.isApproxTangentPlane.finiteDimensional
  tangentialFDeriv_apply_eq_of_unique (fun _ _ M => ‖M‖) hP hL huniq

/-- Identifying `(tangentialFDeriv k g E x).normDet` from a unique witness `(P, L)`. -/
theorem normDet_tangentialFDeriv_eq_of_unique {W₀ : Type*} [NormedAddCommGroup W₀]
    [InnerProductSpace ℝ W₀] {k : ℕ} {g : V → W₀} {P : Submodule ℝ V} [FiniteDimensional ℝ P]
    {L : P →L[ℝ] W₀} {E : Set V} {x : V} (hP : ∃! Q : Submodule ℝ V, IsApproxTangentPlane k E Q x)
    (hL : HasTangentialFDerivAt k g P L E x)
    (huniq : ∀ L' : P →L[ℝ] W₀, HasTangentialFDerivAt k g P L' E x → L' = L) :
    (tangentialFDeriv k g E x).normDet = L.normDet :=
  tangentialFDeriv_apply_eq_of_unique (fun _ _ (M : _ →L[ℝ] W₀) => M.normDet) hP hL huniq

/-- **Ambient relative differentiability within `E` implies tangential differentiability.** -/
theorem _root_.HasFDerivWithinAt.hasTangentialFDerivAt
    {k : ℕ} {g : V → W} {D : V →L[ℝ] W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {E : Set V} {x : V} (hg : HasFDerivWithinAt g D E x) (hP : IsApproxTangentPlane k E P x) :
    HasTangentialFDerivAt k g P (D.comp P.subtypeL) E x where
  isApproxTangentPlane := hP
  tendsto_outside_error_div ε hε := by
    obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.1
      (eventually_nhdsWithin_iff.1 (hg.isLittleO.bound (half_pos hε)))
    set M := max ‖D‖ 1
    have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hP.tendsto_outside_cone_div ((ε / 2) / M) (by positivity))
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
    refine ENNReal.div_le_div_right (measure_mono ?_) _; rintro z ⟨⟨hzE, hzr⟩, hzerr⟩
    refine ⟨⟨hzE, hzr⟩, ?_⟩
    have h1 : ‖g z - g x - D (z - x)‖ ≤ (ε / 2) * dist z x := by
      simpa only [dist_eq_norm] using hbound ((mem_closedBall.1 hzr).trans_lt hr) hzE
    have h2 : ‖D (z - x - P.starProjection (z - x))‖ ≤ M * infDist (z - x) (P : Set V) := by
      rw [← P.dist_starProjection_eq_infDist, dist_eq_norm]
      exact (D.le_opNorm _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hdecomp : g z - g x - (D.comp P.subtypeL) (P.orthogonalProjectionOnto (z - x)) =
        (g z - g x - D (z - x)) + D (z - x - P.starProjection (z - x)) := by
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        Submodule.coe_orthogonalProjectionOnto_apply, map_sub]; abel
    rw [hdecomp] at hzerr
    have htri := hzerr.trans_le ((norm_add_le _ _).trans (add_le_add h1 h2))
    rw [div_mul_eq_mul_div, div_lt_iff₀ hM]; linarith

/-- Ambient Fréchet differentiability at `x` implies tangential differentiability along `E`. -/
theorem _root_.HasFDerivAt.hasTangentialFDerivAt
    {k : ℕ} {g : V → W} {D : V →L[ℝ] W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {E : Set V} {x : V} (hg : HasFDerivAt g D x) (hP : IsApproxTangentPlane k E P x) :
    HasTangentialFDerivAt k g P (D.comp P.subtypeL) E x :=
  hg.hasFDerivWithinAt.hasTangentialFDerivAt hP

/-- Constant functions have zero tangential derivative on any approximate tangent plane. -/
theorem hasTangentialFDerivAt_const {k : ℕ} (c : W) {P : Submodule ℝ V}
    [P.HasOrthogonalProjection] {E : Set V} {x : V} (hP : IsApproxTangentPlane k E P x) :
    HasTangentialFDerivAt k (fun _ => c) P 0 E x := by
  simpa using (hasFDerivWithinAt_const c x E).hasTangentialFDerivAt hP

/-- The identity map has tangential derivative `P.subtypeL` on any approximate tangent plane `P`. -/
theorem hasTangentialFDerivAt_id {k : ℕ} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {E : Set V} {x : V} (hP : IsApproxTangentPlane k E P x) :
    HasTangentialFDerivAt k (id : V → V) P P.subtypeL E x := by
  simpa using (hasFDerivWithinAt_id x E).hasTangentialFDerivAt hP

namespace HasTangentialFDerivAt

/-- Post-composing with a continuous linear map composes the tangential derivative. -/
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
    refine ENNReal.div_le_div_right (measure_mono ?_) _; rintro z ⟨hzE, hzerr⟩
    refine ⟨hzE, ?_⟩
    have heq : (C ∘ g) z - (C ∘ g) x - (C.comp L) (P.orthogonalProjectionOnto (z - x)) =
        C (g z - g x - L (P.orthogonalProjectionOnto (z - x))) := by
      simp [Function.comp_apply, map_sub]
    rw [heq] at hzerr
    have hle := hzerr.trans_le
      ((C.le_opNorm _).trans (mul_le_mul_of_nonneg_right (le_max_left ‖C‖ 1) (norm_nonneg _)))
    rw [div_mul_eq_mul_div, div_lt_iff₀ hM]; linarith

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
    (h₁ : HasTangentialFDerivAt k g₁ P L₁ E x) (h₂ : HasTangentialFDerivAt k g₂ P L₂ E x) :
    HasTangentialFDerivAt k (fun z => g₁ z + g₂ z) P (L₁ + L₂) E x where
  isApproxTangentPlane := h₁.isApproxTangentPlane
  tendsto_outside_error_div ε hε := by
    refine tendsto_measure_div_of_subset_union
      (h₁.tendsto_outside_error_div (ε / 2) (half_pos hε))
      (h₂.tendsto_outside_error_div (ε / 2) (half_pos hε)) fun r z ⟨hzE, hzerr⟩ => ?_
    by_contra hnot; rw [mem_union, not_or] at hnot
    have hle₁ := le_of_not_gt fun h => hnot.1 ⟨hzE, h⟩
    have hle₂ := le_of_not_gt fun h => hnot.2 ⟨hzE, h⟩
    have heq : (g₁ z + g₂ z) - (g₁ x + g₂ x) - (L₁ + L₂) (P.orthogonalProjectionOnto (z - x)) =
        (g₁ z - g₁ x - L₁ (P.orthogonalProjectionOnto (z - x))) +
          (g₂ z - g₂ x - L₂ (P.orthogonalProjectionOnto (z - x))) := by
      simp only [add_apply]; abel
    rw [heq] at hzerr
    linarith [hzerr.trans_le ((norm_add_le _ _).trans (add_le_add hle₁ hle₂))]

/-- Subtraction of tangentially differentiable maps on the same approximate tangent plane. -/
theorem sub {k : ℕ} {g₁ g₂ : V → W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {L₁ L₂ : P →L[ℝ] W} {E : Set V} {x : V}
    (h₁ : HasTangentialFDerivAt k g₁ P L₁ E x) (h₂ : HasTangentialFDerivAt k g₂ P L₂ E x) :
    HasTangentialFDerivAt k (fun z => g₁ z - g₂ z) P (L₁ - L₂) E x := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- `HasTangentialFDerivAt` is preserved under `k`-density-zero set differences at `x`. -/
theorem of_tendsto_diff {k : ℕ} {g : V → W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {L : P →L[ℝ] W} {E₁ E₂ : Set V} {x : V} (h : HasTangentialFDerivAt k g P L E₁ x)
    (h12 : Tendsto (fun r => μHE[k] ((E₁ \ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0))
    (h21 : Tendsto (fun r => μHE[k] ((E₂ \ E₁) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    HasTangentialFDerivAt k g P L E₂ x where
  isApproxTangentPlane := h.isApproxTangentPlane.of_tendsto_diff h12 h21
  tendsto_outside_error_div ε hε := by
    classical
    exact tendsto_measure_div_of_subset_union (h.tendsto_outside_error_div ε hε) h21
      fun _ z ⟨⟨hzE₂, hzr⟩, hzerr⟩ =>
        if hzE₁ : z ∈ E₁ then Or.inl ⟨⟨hzE₁, hzr⟩, hzerr⟩ else Or.inr ⟨⟨hzE₂, hzE₁⟩, hzr⟩

end HasTangentialFDerivAt

/-- If `g₁` and `g₂` admit the same tangential derivatives on `approxTangentPlane k E x`,
their canonical `tangentialFDeriv` agrees at `x`. -/
theorem tangentialFDeriv_congr_of_iff {k : ℕ} {g₁ g₂ : V → W} {E : Set V} {x : V}
    (h : ∀ L : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g₁ (approxTangentPlane k E x) L E x ↔
        HasTangentialFDerivAt k g₂ (approxTangentPlane k E x) L E x) :
    tangentialFDeriv k g₁ E x = tangentialFDeriv k g₂ E x := by
  have hex := existsUnique_congr h
  by_cases h₁ : ∃! L, HasTangentialFDerivAt k g₁ (approxTangentPlane k E x) L E x
  · exact (tangentialFDeriv_eq_of_existsUnique (hex.1 h₁)
      ((h _).1 (hasTangentialFDerivAt_tangentialFDeriv h₁))).symm
  · rw [tangentialFDeriv_of_not_existsUnique h₁,
      tangentialFDeriv_of_not_existsUnique (mt hex.2 h₁)]

/-- If `E₁`, `E₂` admit the same approximate tangent `k`-planes at `x` and `g₁`, `g₂` admit the
same tangential derivatives, any functional `Φ` takes the same value on
`(approxTangentPlane, tangentialFDeriv)`. -/
theorem tangentialFDeriv_apply_congr_of_iff {α W₀ : Type*} [NormedAddCommGroup W₀]
    [NormedSpace ℝ W₀] {k : ℕ} {g₁ g₂ : V → W₀} {E₁ E₂ : Set V} {x : V}
    (Φ : ∀ (P : Submodule ℝ V) [FiniteDimensional ℝ P], (P →L[ℝ] W₀) → α)
    (hP : ∀ P, IsApproxTangentPlane k E₁ P x ↔ IsApproxTangentPlane k E₂ P x)
    (hL : ∀ (P : Submodule ℝ V) [P.HasOrthogonalProjection] (L : P →L[ℝ] W₀),
      HasTangentialFDerivAt k g₁ P L E₁ x ↔ HasTangentialFDerivAt k g₂ P L E₂ x) :
    Φ (approxTangentPlane k E₁ x) (tangentialFDeriv k g₁ E₁ x) =
      Φ (approxTangentPlane k E₂ x) (tangentialFDeriv k g₂ E₂ x) := by
  have key {P₁ P₂ : Submodule ℝ V} [inst₁ : FiniteDimensional ℝ P₁]
      [inst₂ : FiniteDimensional ℝ P₂] {L₁ : P₁ →L[ℝ] W₀} {L₂ : P₂ →L[ℝ] W₀}
      (heq : P₁ = P₂)
      (h₁ : (∃! L, HasTangentialFDerivAt k g₁ P₁ L E₁ x) → HasTangentialFDerivAt k g₁ P₁ L₁ E₁ x)
      (h₀₁ : (¬ ∃! L, HasTangentialFDerivAt k g₁ P₁ L E₁ x) → L₁ = 0)
      (h₂ : (∃! L, HasTangentialFDerivAt k g₂ P₂ L E₂ x) → HasTangentialFDerivAt k g₂ P₂ L₂ E₂ x)
      (h₀₂ : (¬ ∃! L, HasTangentialFDerivAt k g₂ P₂ L E₂ x) → L₂ = 0) :
      Φ P₁ L₁ = Φ P₂ L₂ := by
    subst heq
    cases Subsingleton.elim inst₁ inst₂
    have hex := existsUnique_congr (hL P₁)
    by_cases hu : ∃! L, HasTangentialFDerivAt k g₁ P₁ L E₁ x
    · obtain ⟨_, _, huniq⟩ := hex.1 hu
      rw [huniq L₁ ((hL P₁ L₁).1 (h₁ hu)), huniq L₂ (h₂ (hex.1 hu))]
    · rw [h₀₁ hu, h₀₂ (mt hex.2 hu)]
  exact key (approxTangentPlane_congr_of_iff hP) hasTangentialFDerivAt_tangentialFDeriv
    tangentialFDeriv_of_not_existsUnique hasTangentialFDerivAt_tangentialFDeriv
    tangentialFDeriv_of_not_existsUnique

/-- `HasTangentialFDerivAt` depends on `E` only up to `k`-density-zero symmetric differences. -/
theorem hasTangentialFDerivAt_congr_of_tendsto_symmDiff_div
    {k : ℕ} {g : V → W} {P : Submodule ℝ V} [P.HasOrthogonalProjection]
    {L : P →L[ℝ] W} {E₁ E₂ : Set V} {x : V}
    (h : Tendsto (fun r => μHE[k] ((E₁ ∆ E₂) ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    HasTangentialFDerivAt k g P L E₁ x ↔ HasTangentialFDerivAt k g P L E₂ x := by
  have hsub {A B : Set V} (hab : A \ B ⊆ E₁ ∆ E₂) :
      Tendsto (fun r => μHE[k] ((A \ B) ∩ closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_measure_div_of_subset h fun _ => inter_subset_inter_left _ hab
  exact ⟨fun h₁ => h₁.of_tendsto_diff (hsub subset_union_left) (hsub subset_union_right),
    fun h₂ => h₂.of_tendsto_diff (hsub subset_union_right) (hsub subset_union_left)⟩

/-- **Invariance under `μHE[k]`-null set modifications** at **every** point `x : V`. -/
theorem hasTangentialFDerivAt_congr_ae {k : ℕ} {g : V → W} {P : Submodule ℝ V}
    [P.HasOrthogonalProjection] {L : P →L[ℝ] W} {E₁ E₂ : Set V} (h : E₁ =ᵐ[μHE[k]] E₂) {x : V} :
    HasTangentialFDerivAt k g P L E₁ x ↔ HasTangentialFDerivAt k g P L E₂ x := by
  have hnull : μHE[k] (E₁ ∆ E₂) = 0 := measure_union_null (ae_eq_set.1 h).1 (ae_eq_set.1 h).2
  exact hasTangentialFDerivAt_congr_of_tendsto_symmDiff_div
    (tendsto_measure_inter_div_of_measure_eq_zero Subset.rfl hnull _ _ _)

private theorem tangentialFDeriv_apply_congr_ae {α W₀ : Type*} [NormedAddCommGroup W₀]
    [NormedSpace ℝ W₀] {k : ℕ} {g : V → W₀} {E₁ E₂ : Set V}
    (Φ : ∀ (P : Submodule ℝ V) [FiniteDimensional ℝ P], (P →L[ℝ] W₀) → α)
    (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    Φ (approxTangentPlane k E₁ x) (tangentialFDeriv k g E₁ x) =
      Φ (approxTangentPlane k E₂ x) (tangentialFDeriv k g E₂ x) :=
  tangentialFDeriv_apply_congr_of_iff Φ (fun P => isApproxTangentPlane_congr_ae h P x)
    fun _ _ _ => hasTangentialFDerivAt_congr_ae h

/-- If `E₁ =ᵐ[μHE[k]] E₂`, `(tangentialFDeriv k g E x).comp orthogonalProjectionOnto` agrees at `x`.
-/
theorem tangentialFDeriv_comp_orthogonalProjectionOnto_congr_ae {k : ℕ} {g : V → W}
    {E₁ E₂ : Set V} (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    (tangentialFDeriv k g E₁ x).comp (approxTangentPlane k E₁ x).orthogonalProjectionOnto =
      (tangentialFDeriv k g E₂ x).comp (approxTangentPlane k E₂ x).orthogonalProjectionOnto :=
  tangentialFDeriv_apply_congr_ae (fun P _ L => L.comp P.orthogonalProjectionOnto) h x

/-- If `E₁ =ᵐ[μHE[k]] E₂`, `(tangentialFDeriv k g E x).normDet` agrees at **every** point `x`. -/
theorem normDet_tangentialFDeriv_congr_ae {W₀ : Type*} [NormedAddCommGroup W₀]
    [InnerProductSpace ℝ W₀] {k : ℕ} {g : V → W₀} {E₁ E₂ : Set V} (h : E₁ =ᵐ[μHE[k]] E₂) (x : V) :
    (tangentialFDeriv k g E₁ x).normDet = (tangentialFDeriv k g E₂ x).normDet :=
  tangentialFDeriv_apply_congr_ae (fun P _ (L : P →L[ℝ] W₀) => L.toLinearMap.normDet) h x

/-- `HasTangentialFDerivAt` ignores `k`-density-zero modifications of `g` away from `x` on `E`. -/
theorem hasTangentialFDerivAt_congr_of_tendsto_ne_div {k : ℕ} {g₁ g₂ : V → W} {P : Submodule ℝ V}
    [P.HasOrthogonalProjection] {L : P →L[ℝ] W} {E : Set V} {x : V} (hx : g₁ x = g₂ x)
    (hne : Tendsto (fun r => μHE[k] ({z ∈ E | g₁ z ≠ g₂ z} ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    HasTangentialFDerivAt k g₁ P L E x ↔ HasTangentialFDerivAt k g₂ P L E x := by
  classical
  have aux {f₁ f₂ : V → W} (hfx : f₁ x = f₂ x)
      (hfn : Tendsto (fun r => μHE[k] ({z ∈ E | f₁ z ≠ f₂ z} ∩ closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0))
      (h₁ : HasTangentialFDerivAt k f₁ P L E x) : HasTangentialFDerivAt k f₂ P L E x :=
    ⟨h₁.isApproxTangentPlane, fun ε hε =>
      tendsto_measure_div_of_subset_union (h₁.tendsto_outside_error_div ε hε) hfn
        fun _ z ⟨⟨hzE, hzr⟩, hzerr⟩ =>
          if hfz : f₁ z = f₂ z then Or.inl ⟨⟨hzE, hzr⟩, by rwa [hfz, hfx]⟩
          else Or.inr ⟨⟨hzE, hfz⟩, hzr⟩⟩
  refine ⟨aux hx hne, aux hx.symm ?_⟩
  convert hne using 4 with r; ext; simp [ne_comm]

/-- `tangentialFDeriv` ignores `k`-density-zero modifications of `g` away from `x` on `E`. -/
theorem tangentialFDeriv_congr_of_tendsto_ne_div {k : ℕ} {g₁ g₂ : V → W} {E : Set V} {x : V}
    (hx : g₁ x = g₂ x) (hne : Tendsto (fun r => μHE[k] ({z ∈ E | g₁ z ≠ g₂ z} ∩ closedBall x r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)) :
    tangentialFDeriv k g₁ E x = tangentialFDeriv k g₂ E x :=
  tangentialFDeriv_congr_of_iff fun _ => hasTangentialFDerivAt_congr_of_tendsto_ne_div hx hne

/-- At any `x ∈ E`, `HasTangentialFDerivAt` depends only on `g|_E`. -/
theorem hasTangentialFDerivAt_congr_of_eqOn {k : ℕ} {g₁ g₂ : V → W} {P : Submodule ℝ V}
    [P.HasOrthogonalProjection] {L : P →L[ℝ] W} {E : Set V} {x : V} (hg : EqOn g₁ g₂ E)
    (hx : x ∈ E) : HasTangentialFDerivAt k g₁ P L E x ↔ HasTangentialFDerivAt k g₂ P L E x :=
  have hsub : {z ∈ E | g₁ z ≠ g₂ z} ⊆ ∅ := fun _ ⟨hzE, hne⟩ => hne (hg hzE)
  hasTangentialFDerivAt_congr_of_tendsto_ne_div (hg hx)
    (tendsto_measure_inter_div_of_measure_eq_zero hsub measure_empty _ _ _)

/-- At any `x ∈ E`, `tangentialFDeriv` depends only on `g|_E`. -/
theorem tangentialFDeriv_congr_of_eqOn {k : ℕ} {g₁ g₂ : V → W} {E : Set V} {x : V}
    (hg : EqOn g₁ g₂ E) (hx : x ∈ E) : tangentialFDeriv k g₁ E x = tangentialFDeriv k g₂ E x :=
  tangentialFDeriv_congr_of_iff fun _ => hasTangentialFDerivAt_congr_of_eqOn hg hx

/-- **Invariance under `μHE[k]`-null function modifications on `E`** at `μHE[k]`-a.e. `x ∈ E`. -/
theorem ae_tangentialFDeriv_congr {k : ℕ} {g₁ g₂ : V → W} {E : Set V}
    (hg : ∀ᵐ z ∂μHE[k], z ∈ E → g₁ z = g₂ z) :
    ∀ᵐ x ∂μHE[k], x ∈ E → tangentialFDeriv k g₁ E x = tangentialFDeriv k g₂ E x := by
  have hnull : μHE[k] {z ∈ E | g₁ z ≠ g₂ z} = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hg.mono fun _ h hz => hz.2 (h hz.1))
  filter_upwards [hg] with x hx hxE
  exact tangentialFDeriv_congr_of_tendsto_ne_div (hx hxE)
    (tendsto_measure_inter_div_of_measure_eq_zero Subset.rfl hnull _ _ _)

end Basic

end TauCeti

/-! ### Deterministic uniqueness, chain rule, and Jacobian along parametrizations -/

namespace HasFDerivWithinAt

variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {f : U → V} {g : V → W} {s : Set U} {E : Set V} {x₀ : U}
  {A : U →L[ℝ] V} {B : U →L[ℝ] W} {Lf : ℝ≥0}

private theorem norm_apply_orthogonalProjectionOnto_le_of_hasTangentialFDerivAt
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E) {K : ℝ≥0} (hg : LipschitzOnWith K g E)
    {P : Submodule ℝ V} [P.HasOrthogonalProjection] {L : P →L[ℝ] W}
    (hL : TauCeti.HasTangentialFDerivAt (finrank ℝ U) g P L E (f x₀)) {u : U} (hu : ‖A u‖ = 1 / 2) :
    ‖L (P.orthogonalProjectionOnto (A u))‖ ≤ (K : ℝ) / 2 := by
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  set M : ℝ := (K : ℝ) + ‖L‖ + 1
  have hM : 0 < M := by positivity
  set η : ℝ := δ / (3 * M)
  -- Since the directional slice around `r • A u` has positive lower Hausdorff density while
  -- tangential Taylor errors above `δ / 3` have density zero, pick a witness `z` in the former
  -- where the error bound holds.
  have hlow := hf.liminf_euclideanHausdorffMeasure_directional_closedBall_pos hi hs hfs
    (by linarith : ‖A u‖ < 1) (show 0 < η by positivity)
  have herr := (hL.tendsto_outside_error_div (δ / 3) (by positivity)).liminf_eq
  obtain ⟨r, hr, z, ⟨hzE, hzr⟩, hzd, hzerr⟩ : ∃ r > (0 : ℝ), ∃ z ∈ E ∩ closedBall (f x₀) r,
      ‖z - f x₀ - r • A u‖ ≤ r * η ∧
      ‖g z - g (f x₀) - L (P.orthogonalProjectionOnto (z - f x₀))‖ ≤ (δ / 3) * dist z (f x₀) := by
    by_contra hall; refine hlow.ne' (le_antisymm ?_ zero_le)
    rw [← herr]; refine liminf_le_liminf ?_
    filter_upwards [self_mem_nhdsWithin] with r (_ : 0 < r)
    refine ENNReal.div_le_div_right (measure_mono ?_) _; rintro z ⟨hzE, hzd⟩
    exact ⟨hzE, not_le.1 fun hle => hall ⟨r, ‹_›, z, hzE, hzd, hle⟩⟩
  -- Bound the Lipschitz increment of `g`, the Taylor remainder, and the directional offset from
  -- `r • A u`.
  have hdist_le : dist z (f x₀) ≤ r * (1 / 2 + η) := by
    rw [dist_eq_norm, show z - f x₀ = (z - f x₀ - r • A u) + r • A u by abel]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu]; linarith
  have hLip : ‖g z - g (f x₀)‖ ≤ (K : ℝ) * (r * (1 / 2 + η)) := by
    rw [← dist_eq_norm]
    exact (hg.dist_le_mul z hzE (f x₀) (hfs (mem_image_of_mem f hx₀))).trans
      (mul_le_mul_of_nonneg_left hdist_le K.coe_nonneg)
  have hLstep : ‖L (P.orthogonalProjectionOnto (z - f x₀ - r • A u))‖ ≤ ‖L‖ * (r * η) :=
    (L.le_opNorm _).trans <| mul_le_mul_of_nonneg_left
      ((P.norm_orthogonalProjectionOnto_apply_le _).trans hzd) (norm_nonneg L)
  have heq : r • L (P.orthogonalProjectionOnto (A u)) =
      (g z - g (f x₀)) - (g z - g (f x₀) - L (P.orthogonalProjectionOnto (z - f x₀))) -
        L (P.orthogonalProjectionOnto (z - f x₀ - r • A u)) := by
    rw [sub_sub_cancel, ← map_sub L, ← map_sub P.orthogonalProjectionOnto, sub_sub_cancel,
      map_smul P.orthogonalProjectionOnto r (A u), map_smul L r]
  have htri : r * ‖L (P.orthogonalProjectionOnto (A u))‖ ≤ ‖g z - g (f x₀)‖ +
      ‖g z - g (f x₀) - L (P.orthogonalProjectionOnto (z - f x₀))‖ +
      ‖L (P.orthogonalProjectionOnto (z - f x₀ - r • A u))‖ :=
    calc r * ‖L (P.orthogonalProjectionOnto (A u))‖
        = ‖r • L (P.orthogonalProjectionOnto (A u))‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ _ := by rw [heq]; exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
  -- Cancel the positive scale `r` after absorbing the `η` and `δ / 3` error terms into `δ`.
  have hKL_η : ((K : ℝ) + ‖L‖) * η < δ / 3 :=
    (mul_lt_mul_of_pos_right (show (K : ℝ) + ‖L‖ < M by simp [M]) (by positivity)).trans_eq
      (by simp only [η]; field_simp)
  have hzr' : ‖g z - g (f x₀) - L (P.orthogonalProjectionOnto (z - f x₀))‖ ≤ (δ / 3) * r :=
    hzerr.trans (mul_le_mul_of_nonneg_left (mem_closedBall.1 hzr) (by positivity))
  refine lt_of_mul_lt_mul_left ?_ hr.le
  calc r * ‖L (P.orthogonalProjectionOnto (A u))‖
      ≤ (K : ℝ) * (r * (1 / 2 + η)) + (δ / 3) * r + ‖L‖ * (r * η) :=
        htri.trans (add_le_add (add_le_add hLip hzr') hLstep)
    _ = r * ((K : ℝ) / 2 + (((K : ℝ) + ‖L‖) * η + δ / 3)) := by ring
    _ < r * ((K : ℝ) / 2 + (δ / 3 + δ / 3)) := by gcongr
    _ < r * ((K : ℝ) / 2 + δ) := mul_lt_mul_of_pos_left (by linarith) hr

/-- **Operator-norm bound on tangential derivatives** of `K`-Lipschitz maps along a chart. -/
theorem opNorm_le_of_hasTangentialFDerivAt
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E) {K : ℝ≥0} (hg : LipschitzOnWith K g E)
    {P : Submodule ℝ V} [P.HasOrthogonalProjection] {L : P →L[ℝ] W}
    (hL : TauCeti.HasTangentialFDerivAt (finrank ℝ U) g P L E (f x₀)) : ‖L‖ ≤ K := by
  refine L.opNorm_le_bound K.coe_nonneg fun p => ?_
  by_cases hp : p = 0; · simp [hp]
  have : 0 < ‖p‖ := norm_pos_iff.2 hp
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : U, A u₀ = (p : V) := LinearMap.mem_range.1 <| by
    simpa only [hf.eq_range_of_isApproxTangentPlane hx₀ hi hs hfs hL.isApproxTangentPlane] using p.2
  set u : U := (2 * ‖p‖)⁻¹ • u₀
  have hAu_norm : ‖A u‖ = 1 / 2 := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hu₀, Submodule.norm_coe]
    field_simp
  have hproj : P.orthogonalProjectionOnto (A u) = (2 * ‖p‖)⁻¹ • p := Subtype.ext <| by
    rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.coe_smul,
      P.starProjection_eq_self_iff.2 (by rw [map_smul, hu₀]; exact P.smul_mem _ p.2), map_smul, hu₀]
  have hhalf := hf.norm_apply_orthogonalProjectionOnto_le_of_hasTangentialFDerivAt hx₀ hi hs hfs
    hg hL hAu_norm
  rw [hproj, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hhalf
  have hmul := mul_le_mul_of_nonneg_right hhalf (show 0 ≤ 2 * ‖p‖ by positivity)
  have h1 : (2 * ‖p‖)⁻¹ * ‖L p‖ * (2 * ‖p‖) = ‖L p‖ := by field_simp
  linarith

/-- **Deterministic uniqueness of tangential derivatives** along an antilipschitz chart. -/
theorem hasTangentialFDerivAt_unique
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E) {P : Submodule ℝ V} [P.HasOrthogonalProjection] {L₁ L₂ : P →L[ℝ] W}
    (h₁ : TauCeti.HasTangentialFDerivAt (finrank ℝ U) g P L₁ E (f x₀))
    (h₂ : TauCeti.HasTangentialFDerivAt (finrank ℝ U) g P L₂ E (f x₀)) : L₁ = L₂ := by
  have hsub : TauCeti.HasTangentialFDerivAt (finrank ℝ U) (fun _ => (0 : W)) P (L₁ - L₂)
      E (f x₀) := by simpa only [sub_self] using h₁.sub h₂
  have h0 := hf.opNorm_le_of_hasTangentialFDerivAt hx₀ hi hs hfs
    (LipschitzWith.const (0 : W)).lipschitzOnWith hsub
  rw [NNReal.coe_zero] at h0
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

/-- **Deterministic tangential differentiability along a parametrization** (`B ∘ (A|_range)⁻¹`). -/
theorem hasTangentialFDerivAt_of_tendsto_diff
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1))
    (hinj : Injective A) (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s x₀) :
    TauCeti.HasTangentialFDerivAt (finrank ℝ U) g (LinearMap.range A.toLinearMap)
      (B.comp (LinearEquiv.ofInjective A.toLinearMap hinj).symm.toContinuousLinearMap)
      E (f x₀) := by
  set P := LinearMap.range A.toLinearMap
  set L : P →L[ℝ] W :=
    B.comp (LinearEquiv.ofInjective A.toLinearMap hinj).symm.toContinuousLinearMap
  set D : V →L[ℝ] W := L.comp P.orthogonalProjectionOnto
  have hDA (u : U) : D (A u) = B u := by
    have hp := P.orthogonalProjectionOnto_mem_subspace_eq_self ⟨A u, LinearMap.mem_range_self _ u⟩
    simp only [D, L, ContinuousLinearMap.comp_apply, hp, LinearMap.coe_toContinuousLinearMap']
    exact congrArg B ((LinearEquiv.ofInjective A.toLinearMap hinj).symm_apply_apply u)
  have hfdw_img : HasFDerivWithinAt g D (f '' s) (f x₀) :=
    hf.of_comp_antilipschitzWith hx₀ hi hgf hDA
  have hDL : D.comp (LinearMap.range A.toLinearMap).subtypeL = L := by ext p; simp [D]
  have himg : TauCeti.HasTangentialFDerivAt (finrank ℝ U) g P L (f '' s) (f x₀) := by
    dsimp only [P]; rw [← hDL]
    exact hfdw_img.hasTangentialFDerivAt (hf.isApproxTangentPlane_image hx₀ hi hs)
  exact himg.of_tendsto_diff (TauCeti.tendsto_measure_sdiff_inter_div_of_subset hfs _ _ _) hdiff

/-- Unique tangential differentiability on `approxTangentPlane` along a parametrization. -/
theorem existsUnique_hasTangentialFDerivAt_of_tendsto_diff
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s x₀) :
    ∃! L : TauCeti.approxTangentPlane (finrank ℝ U) E (f x₀) →L[ℝ] W,
      TauCeti.HasTangentialFDerivAt (finrank ℝ U) g
        (TauCeti.approxTangentPlane (finrank ℝ U) E (f x₀)) L E (f x₀) := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs
  have hL := hf.hasTangentialFDerivAt_of_tendsto_diff hx₀ hi hs hinj hfs hdiff hgf
  exact TauCeti.existsUnique_hasTangentialFDerivAt_of_unique
    (hf.existsUnique_isApproxTangentPlane_of_tendsto_diff hx₀ hi hs hfs hdiff) hL
    fun _ hL' => hf.hasTangentialFDerivAt_unique hx₀ hi hs hfs hL' hL

/-- **Chart chain rule for `tangentialFDeriv`**: composing with `A` recovers `B`. -/
theorem tangentialFDeriv_comp_orthogonalProjectionOnto_comp_eq
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s x₀) :
    ((TauCeti.tangentialFDeriv (finrank ℝ U) g E (f x₀)).comp
      (TauCeti.approxTangentPlane (finrank ℝ U) E (f x₀)).orthogonalProjectionOnto).comp A = B := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs
  have hL := hf.hasTangentialFDerivAt_of_tendsto_diff hx₀ hi hs hinj hfs hdiff hgf
  rw [TauCeti.tangentialFDeriv_comp_orthogonalProjectionOnto_eq_of_unique
    (hf.existsUnique_isApproxTangentPlane_of_tendsto_diff hx₀ hi hs hfs hdiff) hL
    fun _ hL' => hf.hasTangentialFDerivAt_unique hx₀ hi hs hfs hL' hL]
  ext u
  have hproj := (LinearMap.range A.toLinearMap).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨A u, LinearMap.mem_range_self _ u⟩
  simp only [ContinuousLinearMap.comp_apply, hproj, LinearMap.coe_toContinuousLinearMap']
  exact congrArg B ((LinearEquiv.ofInjective A.toLinearMap hinj).symm_apply_apply u)

/-- **Explicit ambient operator formula**: `B ∘L (A† ∘L A)⁻¹ ∘L A†` in complete `V`. -/
theorem tangentialFDeriv_comp_orthogonalProjectionOnto_eq [CompleteSpace V]
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s x₀) :
    (TauCeti.tangentialFDeriv (finrank ℝ U) g E (f x₀)).comp
      (TauCeti.approxTangentPlane (finrank ℝ U) E (f x₀)).orthogonalProjectionOnto =
      B.comp ((Ring.inverse (A.adjoint.comp A)).comp A.adjoint) := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs
  have hL := hf.hasTangentialFDerivAt_of_tendsto_diff hx₀ hi hs hinj hfs hdiff hgf
  rw [TauCeti.tangentialFDeriv_comp_orthogonalProjectionOnto_eq_of_unique
    (hf.existsUnique_isApproxTangentPlane_of_tendsto_diff hx₀ hi hs hfs hdiff) hL
    fun _ hL' => hf.hasTangentialFDerivAt_unique hx₀ hi hs hfs hL' hL]
  have hunit : IsUnit (A.adjoint.comp A) :=
    (ContinuousLinearMap.isUnit_adjoint_comp_self_iff A).2 hinj
  ext v
  set u : U := Ring.inverse (A.adjoint.comp A) (A.adjoint v)
  have hproj : A.range.orthogonalProjectionOnto v =
      LinearEquiv.ofInjective A.toLinearMap hinj u := Subtype.ext <| by
    rw [Submodule.coe_orthogonalProjectionOnto_apply,
      ContinuousLinearMap.starProjection_range_eq hunit]
    simp [ContinuousLinearMap.comp_apply, u]
  simp only [ContinuousLinearMap.comp_apply, hproj, LinearMap.coe_toContinuousLinearMap']
  exact congrArg B ((LinearEquiv.ofInjective A.toLinearMap hinj).symm_apply_apply u)

/-- **Jacobian factorization**: `(tangentialFDeriv k g E y).normDet * A.normDet = B.normDet`. -/
theorem normDet_tangentialFDeriv_mul_eq
    {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] {g : V → W₀} {B : U →L[ℝ] W₀}
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s x₀) :
    (TauCeti.tangentialFDeriv (finrank ℝ U) g E (f x₀)).normDet * A.normDet = B.normDet := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs
  set P := LinearMap.range A.toLinearMap
  have hL := hf.hasTangentialFDerivAt_of_tendsto_diff hx₀ hi hs hinj hfs hdiff hgf
  rw [TauCeti.normDet_tangentialFDeriv_eq_of_unique
    (hf.existsUnique_isApproxTangentPlane_of_tendsto_diff hx₀ hi hs hfs hdiff) hL
    fun _ hL' => hf.hasTangentialFDerivAt_unique hx₀ hi hs hfs hL' hL]
  let A' : U →ₗ[ℝ] P := A.toLinearMap.codRestrict P (LinearMap.mem_range_self _)
  rw [← A.toLinearMap.normDet_codRestrict (LinearMap.mem_range_self _),
    ← LinearMap.normDet_comp_of_finrank_eq A' _ (LinearMap.finrank_range_of_inj hinj).symm]
  congr 1; ext u; exact congrArg B ((LinearEquiv.ofInjective A.toLinearMap hinj).symm_apply_apply u)

/-- Explicit quotient formula `(tangentialFDeriv k g E (f x₀)).normDet = B.normDet / A.normDet`. -/
theorem normDet_tangentialFDeriv_eq_div
    {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀] {g : V → W₀} {B : U →L[ℝ] W₀}
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hs : Tendsto (fun r => volume (s ∩ closedBall x₀ r) / volume (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1))
    (hfs : f '' s ⊆ E)
    (hdiff : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x₀) r) /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0))
    (hgf : HasFDerivWithinAt (g ∘ f) B s x₀) :
    (TauCeti.tangentialFDeriv (finrank ℝ U) g E (f x₀)).normDet = B.normDet / A.normDet := by
  have hinj : Injective A := hf.injective_of_tendsto_inter_closedBall_div volume hx₀ hi hs
  have hAne : A.normDet ≠ 0 := fun h0 =>
    (LinearMap.normDet_eq_zero_iff_ker_ne_bot.1 h0) (LinearMap.ker_eq_bot.2 hinj)
  exact eq_div_of_mul_eq hAne (hf.normDet_tangentialFDeriv_mul_eq hx₀ hi hs hfs hdiff hgf)

end HasFDerivWithinAt

private theorem ae_chart_good_of_extend {U V W : Type*} [NormedAddCommGroup U]
    [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {f : U → V} {g g₀ : V → W} {s : Set U} {E : Set V} {Kf Lf Kg₀ : ℝ≥0}
    (hf : LipschitzWith Kf f) (hs : MeasurableSet s) (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hfs : f '' s ⊆ E) (hEm : NullMeasurableSet E μHE[finrank ℝ U])
    [IsLocallyFiniteMeasure (μHE[finrank ℝ U].restrict E)]
    (hg₀ : LipschitzWith Kg₀ g₀) (hgg₀ : EqOn g g₀ E) :
    ∀ᵐ y ∂μHE[finrank ℝ U], y ∈ f '' s →
      ∃ x ∈ s, f x = y ∧ DifferentiableAt ℝ f x ∧
        HasFDerivWithinAt (g ∘ f) (fderiv ℝ (g₀ ∘ f) x) s x ∧
        Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 1) ∧
        Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' s) ∩ closedBall (f x) r) /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0) := by
  have hcomp : EqOn (g ∘ f) (g₀ ∘ f) s := fun x hx => hgg₀ (hfs (mem_image_of_mem f hx))
  filter_upwards [hf.ae_image_of_ae_volume hs hi hEm
    ((hg₀.comp hf).ae_differentiableAt.mono fun _ h _ => h)] with y hy hyfs
  obtain ⟨x, hxs, rfl, hdg, hdf, hdens, hz⟩ := hy hyfs
  exact ⟨x, hxs, rfl, hdf, (hdg.hasFDerivAt.hasFDerivWithinAt (s := s)).congr hcomp (hcomp hxs),
    hdens, hz⟩

/-- **Chart-level tangential differentiability of Lipschitz maps** along bi-Lipschitz patches. -/
theorem LipschitzWith.ae_existsUnique_hasTangentialFDerivAt_image {U V W : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [MeasurableSpace U]
    [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {f : U → V} {g : V → W} {s : Set U} {E : Set V} {Kf Lf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hs : MeasurableSet s) (hi : AntilipschitzWith Lf (s.domRestrict f))
    (hfs : f '' s ⊆ E) (hEm : NullMeasurableSet E μHE[finrank ℝ U])
    [IsLocallyFiniteMeasure (μHE[finrank ℝ U].restrict E)] (hg : LipschitzOnWith Kg g E) :
    ∀ᵐ y ∂μHE[finrank ℝ U], y ∈ f '' s →
      ∃ x ∈ s, f x = y ∧ DifferentiableAt ℝ f x ∧ DifferentiableWithinAt ℝ (g ∘ f) s x ∧
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
  have hex := hfdw_f.existsUnique_hasTangentialFDerivAt_of_tendsto_diff hxs hi hdens hfs hz hfdw_gf
  refine ⟨x, hxs, rfl, hdf, hfdw_gf.differentiableWithinAt, hex,
    hfdw_f.opNorm_le_of_hasTangentialFDerivAt hxs hi hdens hfs hg
      (TauCeti.hasTangentialFDerivAt_tangentialFDeriv hex), ?_⟩
  rw [hfdw_gf.fderivWithin (volume.uniqueDiffWithinAt_of_tendsto_inter_closedBall_div hdens)]
  exact hfdw_f.tangentialFDeriv_comp_orthogonalProjectionOnto_comp_eq hxs hi hdens hfs hz hfdw_gf

namespace TauCeti

section Rectifiable

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] {k : ℕ} {E : Set V} {g : V → W} {K : ℝ≥0}

private theorem CountablyRectifiable.ae_existsUnique_and_norm_le
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hg : LipschitzOnWith K g E) :
    ∀ᵐ x ∂μHE[k], x ∈ E → (∃! L : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E x) L E x) ∧
      ‖tangentialFDeriv k g E x‖ ≤ K := by
  obtain ⟨A, f, hAm, hAsub, hbi, hcov⟩ := hE.exists_bilipschitz_subset_cover hEm
  choose Kf Lf hLip hAnti using hbi
  have hk : finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  have : IsLocallyFiniteMeasure (μHE[finrank ℝ (EuclideanSpace ℝ (Fin k))].restrict E) := by
    simpa only [hk] using ‹IsLocallyFiniteMeasure (μHE[k].restrict E)›
  have hpatch (n : ℕ) : ∀ᵐ y ∂μHE[k], y ∈ f n '' A n → (∃! L : approxTangentPlane k E y →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E y) L E y) ∧
      ‖tangentialFDeriv k g E y‖ ≤ K := by
    have hae := (hLip n).ae_existsUnique_hasTangentialFDerivAt_image (hAm n) (hAnti n) (hAsub n)
      (by simpa only [hk] using hEm) hg
    rw [hk] at hae
    refine hae.mono fun _ hy hyfs => ?_
    obtain ⟨_, _, _, _, _, hex, hnorm, -⟩ := hy hyfs
    exact ⟨hex, hnorm⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hcov, ae_all_iff.2 hpatch] with x hcovx hpx hxE
  obtain ⟨n, hxn⟩ := mem_iUnion.1 (not_not.1 fun h => hcovx ⟨hxE, h⟩)
  exact hpx n hxn

/-- **Rademacher's theorem on countably `k`-rectifiable sets**: a `K`-Lipschitz map has a unique
tangential derivative on `approxTangentPlane k E x` at `μHE[k]`-almost every `x ∈ E`. -/
theorem CountablyRectifiable.ae_existsUnique_hasTangentialFDerivAt
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hg : LipschitzOnWith K g E) :
    ∀ᵐ x ∂μHE[k], x ∈ E → ∃! L : approxTangentPlane k E x →L[ℝ] W,
      HasTangentialFDerivAt k g (approxTangentPlane k E x) L E x :=
  (hE.ae_existsUnique_and_norm_le hEm hg).mono fun _ hx hxE => (hx hxE).1

/-- At `μHE[k]`-a.e. `x ∈ E`, `tangentialFDeriv k g E x` satisfies `HasTangentialFDerivAt`. -/
theorem CountablyRectifiable.ae_hasTangentialFDerivAt_tangentialFDeriv
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hg : LipschitzOnWith K g E) :
    ∀ᵐ x ∂μHE[k], x ∈ E →
      HasTangentialFDerivAt k g (approxTangentPlane k E x) (tangentialFDeriv k g E x) E x :=
  (hE.ae_existsUnique_hasTangentialFDerivAt hEm hg).mono fun _ hx hxE =>
    hasTangentialFDerivAt_tangentialFDeriv (hx hxE)

/-- `‖tangentialFDeriv k g E x‖ ≤ K` at `μHE[k]`-almost every `x ∈ E`. -/
theorem CountablyRectifiable.ae_norm_tangentialFDeriv_le
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hg : LipschitzOnWith K g E) :
    ∀ᵐ x ∂μHE[k], x ∈ E → ‖tangentialFDeriv k g E x‖ ≤ K :=
  (hE.ae_existsUnique_and_norm_le hEm hg).mono fun _ hx hxE => (hx hxE).2

private theorem CountablyRectifiable.aemeasurable_of_chart_formula {W₀ α : Type*}
    [NormedAddCommGroup W₀] [NormedSpace ℝ W₀] [FiniteDimensional ℝ W₀] [MeasurableSpace α]
    [Nonempty α] {g : V → W₀} (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hg : LipschitzOnWith K g E) (Ψ : ℕ → V → α)
    (F : (EuclideanSpace ℝ (Fin k) → V) → (V → W₀) → EuclideanSpace ℝ (Fin k) → α)
    (hFm : ∀ f g₀, Measurable (F f g₀))
    (hFeq : ∀ {Lf : ℝ≥0} {f : EuclideanSpace ℝ (Fin k) → V} {s : Set (EuclideanSpace ℝ (Fin k))}
      {g₀ : V → W₀} {x : EuclideanSpace ℝ (Fin k)},
      x ∈ s → AntilipschitzWith Lf (s.domRestrict f) → f '' s ⊆ E → DifferentiableAt ℝ f x →
      HasFDerivWithinAt (g ∘ f) (fderiv ℝ (g₀ ∘ f) x) s x →
      Tendsto (fun r => volume (s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 1) →
      Tendsto (fun r => μHE[finrank ℝ (EuclideanSpace ℝ (Fin k))]
        ((E \ f '' s) ∩ closedBall (f x) r) / volume (closedBall
          (0 : EuclideanSpace ℝ (Fin (finrank ℝ (EuclideanSpace ℝ (Fin k))))) r)) (𝓝[>] 0) (𝓝 0) →
      Ψ (finrank ℝ (EuclideanSpace ℝ (Fin k))) (f x) = F f g₀ x) :
    AEMeasurable (Ψ k) (μHE[k].restrict E) := by
  classical
  obtain ⟨g₀, hg₀, hgg₀⟩ := hg.extend_finite_dimension
  obtain ⟨A, f, hAm, hAsub, hbi, hcov⟩ := hE.exists_bilipschitz_subset_cover hEm
  choose Kf Lf hLip hAnti using hbi
  have hk : finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  have : IsLocallyFiniteMeasure (μHE[finrank ℝ (EuclideanSpace ℝ (Fin k))].restrict E) := by
    simpa only [hk] using ‹IsLocallyFiniteMeasure (μHE[k].restrict E)›
  let S (n : ℕ) : Set V := f n '' A n
  have hSm (n : ℕ) : MeasurableSet (S n) :=
    (hAm n).image_of_continuousOn_injOn (hLip n).continuous.continuousOn
      (injOn_iff_injective.2 (hAnti n).injective)
  -- Push the measurable chart formula forward along each bi-Lipschitz Borel patch `S n`.
  have hpatch (n : ℕ) : ∃ Φ : V → α, Measurable Φ ∧ ∀ᵐ y ∂μHE[k], y ∈ S n → Ψ k y = Φ y := by
    have he := (hLip n).continuous.continuousOn.measurableEmbedding (hAm n)
      (injOn_iff_injective.2 (hAnti n).injective)
    obtain ⟨Φ, hΦm, hΦ⟩ := he.exists_measurable_extend
      ((hFm (f n) g₀).comp measurable_subtype_coe) (fun _ => inferInstance)
    refine ⟨Φ, hΦm, ?_⟩
    rw [← (by rw [hk] : (μHE[finrank ℝ (EuclideanSpace ℝ (Fin k))] : Measure V) = μHE[k])]
    refine (ae_chart_good_of_extend (hLip n) (hAm n) (hAnti n) (hAsub n)
      (by simpa only [hk] using hEm) hg₀ hgg₀).mono fun _ hy hyfs => ?_
    obtain ⟨x, hxs, rfl, hdf, hfdw_gf, hdens, hz⟩ := hy hyfs
    exact (congrArg (Ψ · (f n x)) hk).symm.trans
      ((hFeq hxs (hAnti n) (hAsub n) hdf hfdw_gf hdens hz).trans (congrFun hΦ ⟨x, hxs⟩).symm)
  choose Φ hΦm hΦ using hpatch
  -- Glue the Borel representatives across `⋃ n, S n` via `Measurable.find`.
  let Uset := ⋃ n, S n
  have hindex (x : Uset) : ∃ n, (x : V) ∈ S n := mem_iUnion.1 x.property
  obtain ⟨G, hGm, hG⟩ :=
    (MeasurableEmbedding.subtype_coe (MeasurableSet.iUnion hSm)).exists_measurable_extend
      (Measurable.find (fun n => (hΦm n).comp measurable_subtype_coe)
        (fun n => (hSm n).preimage measurable_subtype_coe) hindex) (fun _ => inferInstance)
  refine hGm.aemeasurable.congr ((ae_restrict_iff'₀ hEm).2 ?_)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hcov, ae_all_iff.2 hΦ] with x hcovx hΦx hxE
  have hxU : x ∈ Uset := not_not.1 fun h => hcovx ⟨hxE, h⟩
  exact (congrFun hG ⟨x, hxU⟩).trans (hΦx _ (Nat.find_spec (hindex ⟨x, hxU⟩))).symm

/-- **Measurability of the ambient tangential derivative field** on `μHE[k].restrict E`. -/
theorem CountablyRectifiable.aemeasurable_tangentialFDeriv_comp_orthogonalProjectionOnto
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hg : LipschitzOnWith K g E) :
    AEMeasurable (fun x =>
      (tangentialFDeriv k g E x).comp (approxTangentPlane k E x).orthogonalProjectionOnto)
      (μHE[k].restrict E) :=
  hE.aemeasurable_of_chart_formula hEm hg
    (fun m x => (tangentialFDeriv m g E x).comp (approxTangentPlane m E x).orthogonalProjectionOnto)
    (fun f g₀ x => (fderiv ℝ (g₀ ∘ f) x).comp
      ((Ring.inverse ((fderiv ℝ f x).adjoint.comp (fderiv ℝ f x))).comp (fderiv ℝ f x).adjoint))
    (fun f g₀ => by
      have hAf := measurable_fderiv ℝ f
      have hAadj : Measurable (fun x => (fderiv ℝ f x).adjoint) := by
        simpa only [Function.comp_def, ContinuousLinearMap.adjointRealCLM_apply] using
          ContinuousLinearMap.adjointRealCLM.continuous.measurable.comp hAf
      have hgram := (continuous_fst.clm_comp continuous_snd).measurable.comp (hAadj.prodMk hAf)
      exact (continuous_fst.clm_comp continuous_snd).measurable.comp
        ((measurable_fderiv ℝ (g₀ ∘ f)).prodMk
          ((continuous_fst.clm_comp continuous_snd).measurable.comp
            (hgram.ringInverse.prodMk hAadj))))
    fun hxs hi hfs hdf hfdw_gf hdens hz =>
      hdf.hasFDerivAt.hasFDerivWithinAt.tangentialFDeriv_comp_orthogonalProjectionOnto_eq
        hxs hi hdens hfs hz hfdw_gf

/-- **Measurability of the tangential Jacobian `normDet`** on `μHE[k].restrict E`. -/
theorem CountablyRectifiable.aemeasurable_normDet_tangentialFDeriv
    {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℝ W₀]
    [FiniteDimensional ℝ W₀] {g : V → W₀}
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hg : LipschitzOnWith K g E) :
    AEMeasurable (fun x => (tangentialFDeriv k g E x).normDet) (μHE[k].restrict E) :=
  hE.aemeasurable_of_chart_formula hEm hg (fun m x => (tangentialFDeriv m g E x).normDet)
    (fun f g₀ x => (fderiv ℝ (g₀ ∘ f) x).normDet / (fderiv ℝ f x).normDet)
    (fun f g₀ => (ContinuousLinearMap.continuous_normDet.measurable.comp
      (measurable_fderiv ℝ (g₀ ∘ f))).div
      (ContinuousLinearMap.continuous_normDet.measurable.comp (measurable_fderiv ℝ f)))
    fun hxs hi hfs hdf hfdw_gf hdens hz =>
      hdf.hasFDerivAt.hasFDerivWithinAt.normDet_tangentialFDeriv_eq_div hxs hi hdens hfs hz hfdw_gf

end Rectifiable

end TauCeti
