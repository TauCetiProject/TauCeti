/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.DenseEmbedding
import TauCeti.Analysis.CStarAlgebra.Basic

/-!
# Sequential implementation of approximate unitary equivalence

For a separable source, approximate unitary equivalence with target unitaries is
implemented by a single sequence of unitaries converging pointwise after conjugation.
This replaces finite-set tests by sequences when constructing approximate intertwining
maps. The converse and closure under point-norm limits work for any net along a
nontrivial filter, without separability.

The diagonal argument follows Kirchberg–Phillips, *Embedding of exact C*-algebras in
the Cuntz algebra O₂*, Definition 0.5 and the paragraph immediately following it.
Contractivity of star homomorphisms and Mathlib's equicontinuous convergence theorem
extend convergence from a countable dense sequence to the whole source.
-/

public section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti.ApproximatelyUnitarilyEquivalent

variable {A B : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]
  {φ ψ : A →⋆ₙₐ[ℂ] B}

/-- A net of implementing target unitaries gives approximate unitary equivalence.
The filter must be nontrivial, but no separability assumption is needed. -/
theorem of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] (u : ι → unitary B)
    (h : ∀ a, Tendsto (fun i ↦ (u i : B) * φ a * star (u i : B)) l (𝓝 (ψ a))) :
    ApproximatelyUnitarilyEquivalent φ ψ := by
  rw [approximatelyUnitarilyEquivalent_def]
  intro F ε hε
  have he (a : A) : ∀ᶠ i in l, ‖(u i : B) * φ a * star (u i : B) - ψ a‖ < ε :=
    (Metric.tendsto_nhds.mp (h a) ε hε).mono fun _ hi ↦ by
      simpa only [dist_eq_norm] using hi
  obtain ⟨i, hi⟩ := (F.eventually_all.mpr fun a _ ↦ he a).exists
  exact ⟨u i, hi⟩

/-- Approximate unitary equivalence is jointly closed in both arguments under point-norm
convergence along any nontrivial filter, without separability assumptions. -/
theorem of_tendsto_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {Φ Ψ : ι → A →⋆ₙₐ[ℂ] B}
    (h : ∀ᶠ i in l, ApproximatelyUnitarilyEquivalent (Φ i) (Ψ i))
    (hφ : ∀ a, Tendsto (fun i ↦ Φ i a) l (𝓝 (φ a)))
    (hψ : ∀ a, Tendsto (fun i ↦ Ψ i a) l (𝓝 (ψ a))) :
    ApproximatelyUnitarilyEquivalent φ ψ := by
  rw [approximatelyUnitarilyEquivalent_def]
  intro F ε hε
  have hε₃ : 0 < ε / 3 := by positivity
  have heΦ (a : A) : ∀ᶠ i in l, ‖Φ i a - φ a‖ < ε / 3 :=
    (Metric.tendsto_nhds.mp (hφ a) (ε / 3) hε₃).mono fun _ hi ↦ by
      simpa only [dist_eq_norm] using hi
  have heΨ (a : A) : ∀ᶠ i in l, ‖Ψ i a - ψ a‖ < ε / 3 :=
    (Metric.tendsto_nhds.mp (hψ a) (ε / 3) hε₃).mono fun _ hi ↦ by
      simpa only [dist_eq_norm] using hi
  obtain ⟨i, ⟨hi, hΦi⟩, hΨi⟩ :=
    ((h.and (F.eventually_all.mpr fun a _ ↦ heΦ a)).and
      (F.eventually_all.mpr fun a _ ↦ heΨ a)).exists
  obtain ⟨u, hu⟩ := (approximatelyUnitarilyEquivalent_def _ _).mp hi F (ε / 3) hε₃
  refine ⟨u, fun a ha ↦ ?_⟩
  calc
    ‖(u : B) * φ a * star (u : B) - ψ a‖
      ≤ (‖(u : B) * φ a * star (u : B) - (u : B) * Φ i a * star (u : B)‖ +
          ‖(u : B) * Φ i a * star (u : B) - Ψ i a‖) + ‖Ψ i a - ψ a‖ :=
        (norm_sub_le_norm_sub_add_norm_sub _ (Ψ i a) _).trans
          (add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ ((u : B) * Φ i a * star (u : B)) _)
            _)
    _ = ‖Φ i a - φ a‖ + ‖(u : B) * Φ i a * star (u : B) - Ψ i a‖ + ‖Ψ i a - ψ a‖ := by
        rw [CStarRing.norm_unitary_conj_sub, norm_sub_rev (φ a)]
    _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add (hΦi a ha) (hu a ha)) (hΨi a ha)
    _ = ε := by ring

/-- Approximate unitary equivalence is closed in the left argument under point-norm convergence
along any nontrivial filter, without separability assumptions. -/
theorem of_tendsto_left {ι : Type*} {l : Filter ι} [l.NeBot] {Φ : ι → A →⋆ₙₐ[ℂ] B}
    (h : ∀ᶠ i in l, ApproximatelyUnitarilyEquivalent (Φ i) ψ)
    (hlim : ∀ a, Tendsto (fun i ↦ Φ i a) l (𝓝 (φ a))) :
    ApproximatelyUnitarilyEquivalent φ ψ :=
  of_tendsto_of_tendsto h hlim fun _ ↦ tendsto_const_nhds

/-- Approximate unitary equivalence is closed in the right argument under point-norm convergence
along any nontrivial filter, without separability assumptions. -/
theorem of_tendsto_right {ι : Type*} {l : Filter ι} [l.NeBot] {Ψ : ι → A →⋆ₙₐ[ℂ] B}
    (h : ∀ᶠ i in l, ApproximatelyUnitarilyEquivalent φ (Ψ i))
    (hlim : ∀ a, Tendsto (fun i ↦ Ψ i a) l (𝓝 (ψ a))) :
    ApproximatelyUnitarilyEquivalent φ ψ :=
  of_tendsto_of_tendsto h (fun _ ↦ tendsto_const_nhds) hlim

/-- For a separable source, approximate unitary equivalence is equivalent to pointwise
convergence of conjugates along a sequence of target unitaries. -/
theorem iff_exists_unitary_seq [TopologicalSpace.SeparableSpace A] :
    ApproximatelyUnitarilyEquivalent φ ψ ↔
      ∃ u : ℕ → unitary B, ∀ a,
        Tendsto (fun n ↦ (u n : B) * φ a * star (u n : B)) atTop (𝓝 (ψ a)) := by
  classical
  constructor
  · intro h
    rw [approximatelyUnitarilyEquivalent_def] at h
    let d := TopologicalSpace.denseSeq A
    have hchoose (n : ℕ) := h ((Finset.range n).image d) (1 / ((n : ℝ) + 1)) (by positivity)
    choose u hu using hchoose
    let e (n : ℕ) := Unitary.conjStarAlgAut ℂ B (u n)
    have hd (k : ℕ) : Tendsto (fun n ↦ e n (φ (d k))) atTop (𝓝 (ψ (d k))) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have hεn : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
      filter_upwards [hεn, eventually_gt_atTop k] with n hn hkn
      simpa only [e, Unitary.conjStarAlgAut_apply, dist_eq_norm] using
        (hu n (d k) (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hkn, rfl⟩)).trans hn
    -- All conjugated maps are contractions, uniformly in the implementing unitary.
    have he : Equicontinuous (fun n a ↦ e n (φ a)) := by
      apply Metric.equicontinuous_of_continuity_modulus id tendsto_id
      intro a b n
      simpa only [id_eq, dist_eq_norm, ← map_sub, StarAlgEquiv.norm_map] using
        NonUnitalStarAlgHom.norm_apply_le φ (a - b)
    refine ⟨u, ?_⟩
    exact isClosed_property (TopologicalSpace.denseRange_denseSeq A)
      (he.isClosed_setOfPred_tendsto (map_continuous ψ)) hd
  · rintro ⟨u, hu⟩
    exact of_tendsto u hu

end TauCeti.ApproximatelyUnitarilyEquivalent
