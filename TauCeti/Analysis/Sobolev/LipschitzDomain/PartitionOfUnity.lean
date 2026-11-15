/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Partitions of unity adapted to Lipschitz boundary charts

Sobolev trace and extension operators on a bounded Lipschitz domain `Ω` are assembled from
their flat models by a partition of unity: one smooth cutoff supported inside `Ω`, and one
cutoff for each boundary chart of a finite cover. This file constructs such a partition.

Each boundary cutoff is supported, in the coordinates of its chart, in the shortened cylinder
`normalCylinder (a - 2 * L * b) b`, where `a` and `b` are the normal and tangential radii of the
chart and `L` is the Lipschitz constant of its graph. On this cylinder the reflection
`t ↦ 2 * φ y - t` across the graph of `φ` stays inside the chart cylinder, so the reflected
values of a cutoff product never reach parts of `Ω` outside the chart. This is the support
hypothesis of the extension through one chart in Evans–Gariepy §4.4.

The charts come from
`Set.IsLipschitzDomainWith.exists_finset_isLipschitzChartWith_two_mul_lt_cover`, and the cutoffs
from Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`. Every cylinder is bounded, so each
cutoff has compact support; its value and gradient are then bounded, as the localization
operator `TauCeti.W1p.localizeL` requires, by `ContDiff.exists_abs_le_and_norm_gradient_le`.

## Main declarations

* `Set.IsLipschitzDomainWith.exists_contDiff_partitionOfUnity`: a smooth partition of unity on
  the closure of a bounded Lipschitz domain, subordinate to the domain itself and to the
  shortened cylinders of finitely many boundary charts.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  §4.4.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.4.
-/

public section

noncomputable section

namespace Set

open Metric Topology TauCeti
open scoped NNReal ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0}

/-- **Partition of unity for a bounded Lipschitz domain.** For a bounded Lipschitz domain `Omega`
with constant `L`, there are finitely many frontier points `x ∈ t` carrying Lipschitz boundary
charts `e x`, `φ x` with radii `a x`, `b x` satisfying `2 * L * b x < a x`, together with
smooth cutoffs `ψ₀` and `ψ x` with values in `[0, 1]` and compact support, such that `ψ₀` is
supported in `Omega`, each `ψ x` is supported in the preimage of the shortened chart cylinder
`normalCylinder (a x - 2 * L * b x) (b x)`, and `ψ₀ + ∑ x ∈ t, ψ x = 1` on the closure of
`Omega`. -/
theorem IsLipschitzDomainWith.exists_contDiff_partitionOfUnity [FiniteDimensional ℝ E]
    (h : Omega.IsLipschitzDomainWith L) (hb : Bornology.IsBounded Omega) :
    ∃ (t : Finset (WithLp 2 (ℝ × E))) (e : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ]
        WithLp 2 (ℝ × E)) (φ : WithLp 2 (ℝ × E) → E → ℝ) (a b : WithLp 2 (ℝ × E) → ℝ)
        (ψ₀ : WithLp 2 (ℝ × E) → ℝ) (ψ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) → ℝ),
      (∀ x ∈ t, x ∈ frontier Omega ∧ e x x = 0 ∧
        Omega.IsLipschitzChartWith L (e x) (φ x) (a x) (b x) ∧ 2 * L * b x < a x) ∧
      (ContDiff ℝ ∞ ψ₀ ∧ range ψ₀ ⊆ Icc 0 1 ∧ HasCompactSupport ψ₀ ∧ tsupport ψ₀ ⊆ Omega) ∧
      (∀ x ∈ t, ContDiff ℝ ∞ (ψ x) ∧ range (ψ x) ⊆ Icc 0 1 ∧ HasCompactSupport (ψ x) ∧
        tsupport (ψ x) ⊆ e x ⁻¹' normalCylinder (a x - 2 * L * b x) (b x)) ∧
      ∀ y ∈ closure Omega, ψ₀ y + ∑ x ∈ t, ψ x y = 1 := by
  classical
  obtain ⟨t, e, φ, a, b, hchart, hcover⟩ :=
    h.exists_finset_isLipschitzChartWith_two_mul_lt_cover hb
  have hOmega : IsOpen Omega := ((isLipschitzDomainWith_iff ..).1 h).1
  -- The open cover of `closure Omega` by `Omega` and the shortened chart cylinders; each member
  -- is bounded, so the subordinate cutoffs have compact support.
  let U : Option t → Set (WithLp 2 (ℝ × E)) := fun i ↦
    i.elim Omega fun x ↦ e x ⁻¹' normalCylinder (a x - 2 * L * b x) (b x)
  have hUo : ∀ i, IsOpen (U i) := by
    rintro (_ | x)
    · exact hOmega
    · exact (isOpen_normalCylinder _ _).preimage (e x).continuous
  have hUb : ∀ i, Bornology.IsBounded (U i) := by
    rintro (_ | x)
    · exact hb
    · exact (e x).antilipschitzWith.isBounded_preimage (isBounded_normalCylinder _ _)
  have hUc : closure Omega ⊆ ⋃ i, U i := by
    intro y hy
    by_cases hyΩ : y ∈ Omega
    · exact mem_iUnion.2 ⟨none, hyΩ⟩
    · obtain ⟨x, hxt, hyx⟩ :=
        mem_iUnion₂.1 (hcover ⟨hy, by rwa [hOmega.interior_eq]⟩)
      exact mem_iUnion.2 ⟨some ⟨x, hxt⟩, hyx⟩
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, WithLp 2 (ℝ × E)) isClosed_closure U hUo hUc
  have hρ_cont : ∀ i, ContDiff ℝ ∞ (ρ i) := fun i ↦ (ρ i).contMDiff.contDiff
  have hρ_range : ∀ i, range (ρ i) ⊆ Icc 0 1 := by
    rintro i _ ⟨y, rfl⟩
    exact ⟨ρ.nonneg i y, ρ.le_one i y⟩
  have hρ_cpt : ∀ i, HasCompactSupport (ρ i) := fun i ↦
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) ((hUb i).subset (hρ i))
  -- Reindex the chart cutoffs by the chart centres, extending by zero off `t`.
  let ψ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) → ℝ := fun x y ↦
    if hx : x ∈ t then ρ (some ⟨x, hx⟩) y else 0
  have hψ : ∀ x (hx : x ∈ t), ψ x = ρ (some ⟨x, hx⟩) := fun x hx ↦ funext fun y ↦ by simp [ψ, hx]
  refine ⟨t, e, φ, a, b, ρ none, ψ, hchart, ⟨hρ_cont none, hρ_range none, hρ_cpt none,
    hρ none⟩, fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · rw [hψ x hx]
    exact ⟨hρ_cont _, hρ_range _, hρ_cpt _, hρ (some ⟨x, hx⟩)⟩
  · rw [← ρ.sum_eq_one hy, finsum_eq_sum_of_fintype, Fintype.sum_option, ← Finset.sum_coe_sort t]
    congr 1
    exact Finset.sum_congr rfl fun x _ ↦ by rw [hψ x x.2]

end Set
