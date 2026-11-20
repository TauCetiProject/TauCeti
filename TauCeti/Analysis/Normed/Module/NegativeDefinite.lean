/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Negative definite subspaces through a dense map

Let `Q` be a continuous bilinear form on a normed space `X`, and `ι : Y → X` a linear map with
dense range. If `Q` is negative definite on a finite-dimensional subspace `W` of `X`, then `Y` has
a subspace of the same dimension on whose image `Q` is negative definite
(`exists_finrank_eq_forall_apply_lt_zero_of_denseRange`): negative definiteness on the span of a
basis is an open condition on the basis, by compactness of the unit sphere of the coefficients, so
it survives approximating the basis vectors in the range of `ι`.

This is how an index computed on a completion is attained on a dense space of smooth sections.
-/

public section

open Filter Module Set Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- **Negative definite subspaces through a dense map.** If the continuous bilinear form `Q` on `X`
is negative definite on a finite-dimensional subspace `W`, and `ι : Y → X` is linear with dense
range, then some subspace of `Y` of dimension `finrank W` is mapped by `ι` to vectors on which `Q`
is negative, except for `0`. -/
theorem exists_finrank_eq_forall_apply_lt_zero_of_denseRange (Q : X →L[ℝ] X →L[ℝ] ℝ)
    {ι : Y →ₗ[ℝ] X} (hι : DenseRange ι) (W : Submodule ℝ X) [FiniteDimensional ℝ W]
    (hW : ∀ w ∈ W, w ≠ 0 → Q w w < 0) :
    ∃ W' : Submodule ℝ Y, finrank ℝ W' = finrank ℝ W ∧ ∀ y ∈ W', y ≠ 0 → Q (ι y) (ι y) < 0 := by
  classical
  set n := finrank ℝ W
  set v : Fin n → X := fun i ↦ (Module.finBasis ℝ W i : X)
  have hv : LinearIndependent ℝ v :=
    (Module.finBasis ℝ W).linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  set G : (Fin n → X) × (Fin n → ℝ) → ℝ := fun p ↦ Q (∑ i, p.2 i • p.1 i) (∑ i, p.2 i • p.1 i)
  have hGc : Continuous G := by
    have hs : Continuous fun p : (Fin n → X) × (Fin n → ℝ) ↦ ∑ i, p.2 i • p.1 i :=
      continuous_finsetSum _ fun i _ ↦
        ((continuous_apply i).comp continuous_snd).smul ((continuous_apply i).comp continuous_fst)
    exact Q.continuous₂.comp (hs.prodMk hs)
  have hGsmul (d : Fin n → X) (a : Fin n → ℝ) (t : ℝ) :
      G (d, t • a) = t ^ 2 * G (d, a) := by
    simp only [G, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul, smul_apply]
    ring
  set S := Metric.sphere (0 : Fin n → ℝ) 1
  have hS : IsCompact S := isCompact_sphere 0 1
  have hvS : ∀ a ∈ S, G (v, a) < 0 := fun a ha ↦ by
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp [S] at ha
    refine hW _ (Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Module.finBasis ℝ W i).2)
      fun h ↦ ha0 (funext fun i ↦ ?_)
    exact Fintype.linearIndependent_iff.1 hv a h i
  have hev : ∀ᶠ d in 𝓝 v, ∀ a ∈ S, G (d, a) < 0 := by
    refine hS.eventually_forall_of_forall_eventually fun a ha ↦ ?_
    exact (hGc.tendsto (v, a)).eventually (gt_mem_nhds (hvS a ha))
  obtain ⟨O, hOsub, hO, hvO⟩ := mem_nhds_iff.1 hev
  have hdense : DenseRange fun y : Fin n → Y ↦ fun i ↦ ι (y i) :=
    DenseRange.piMap fun _ ↦ hι
  obtain ⟨y, hy⟩ := hdense.exists_mem_open hO ⟨v, hvO⟩
  have hyS : ∀ a ∈ S, G ((fun i ↦ ι (y i)), a) < 0 := hOsub hy
  have hneg (a : Fin n → ℝ) (ha : a ≠ 0) : Q (ι (∑ i, a i • y i)) (ι (∑ i, a i • y i)) < 0 := by
    have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
    have h := hyS (‖a‖⁻¹ • a) (by
      simp [S, norm_smul, inv_mul_cancel₀ hna.ne'])
    rw [hGsmul] at h
    have h' : G ((fun i ↦ ι (y i)), a) < 0 := by
      by_contra h''
      exact h.not_ge (mul_nonneg (by positivity) (not_lt.1 h''))
    simpa only [G, map_sum, map_smul] using h'
  have hyli : LinearIndependent ℝ y := Fintype.linearIndependent_iff.2 fun a ha i ↦ by
    by_contra hai
    have := hneg a fun h ↦ hai (by simp [h])
    simp [ha] at this
  refine ⟨Submodule.span ℝ (Set.range y), ?_, fun z hz hz0 ↦ ?_⟩
  · rw [finrank_span_eq_card hyli, Fintype.card_fin]
  · obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hz
    exact hneg a fun h ↦ hz0 (by simp [h])
