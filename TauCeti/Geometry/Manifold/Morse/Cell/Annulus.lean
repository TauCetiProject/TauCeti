/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Map
public import TauCeti.Geometry.Manifold.Morse.Deformation
public import TauCeti.Topology.Homotopy.RetractionTrack

/-!
# Annulus deformations of Morse characteristic discs

For a normalized Morse chart with characteristic disc of radius `√ε`, parametrize its
negative-coordinate annulus between radii `d * √ε` and `√ε`, where `d ∈ [0,1]`. The radial
parameter `s ∈ [0,1]` corresponds to radius `(d + (1-d)*s) * √ε`. The annulus lies in
`{f ≤ c - ε*d²}`, its inner circle has value `c - ε*d²`, and its outer circle is the
existing attaching map at level `c - ε`.

If the compact band between these two levels has no critical points, deform the annulus
to the retraction track of its inner circle. The homotopy fixes the inner seam and keeps
the outer seam in `{f ≤ c - ε}`. Consequently the inner disc can subsequently move, together
with its entire track, without losing the attaching-boundary condition. No overlap of whole
characteristic discs of different charts is required.

The construction uses `TauCeti.exists_sublevelDeformation` and the characteristic map
`OpenPartialHomeomorph.morseCellMap`. See J. Milnor, *Morse Theory*, Princeton University
Press, 1963, §3, Remark 3.3, for the comparison of characteristic discs.
-/

public section

noncomputable section

universe u

open Set Metric Topology unitInterval
open scoped ContDiff Manifold

namespace OpenPartialHomeomorph

variable {M : Type u} [TopologicalSpace M] {n k : ℕ} {f : M → ℝ} {c ε : ℝ}

/-- The negative-coordinate annulus of a Morse characteristic disc, with normalized inner
radius `d`. Its radial coordinate runs from `d` to `1`. -/
def morseAnnulusMap (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
    (hε : 0 ≤ ε) (hball : closedBall 0 √ε ⊆ ψ.target)
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    (d : I) : C(I × TopCat.diskBoundary.{u} k, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2}) where
  toFun p := ⟨ψ.morseCellMap hk ε
    ((unitInterval.symm (unitInterval.symm d * unitInterval.symm p.1) : ℝ) •
      (p.2.down : EuclideanSpace ℝ (Fin k))), by
        have hn : ‖(p.2.down : EuclideanSpace ℝ (Fin k))‖ = 1 :=
          mem_sphere_zero_iff_norm.mp p.2.down.property
        have hnorm : ‖(unitInterval.symm (unitInterval.symm d *
            unitInterval.symm p.1) : ℝ) • (p.2.down : EuclideanSpace ℝ (Fin k))‖ =
            (unitInterval.symm (unitInterval.symm d * unitInterval.symm p.1) : ℝ) := by
          rw [norm_smul, Real.norm_of_nonneg (unitInterval.symm _).property.1, hn, mul_one]
        simp only [mem_ofPred_eq]
        rw [ψ.apply_morseCellMap_eq_sub_mul_norm_sq hball hf hk hε
          (by rw [hnorm]; exact (unitInterval.symm _).property.2), hnorm]
        have hds : (d : ℝ) ≤
            (unitInterval.symm (unitInterval.symm d * unitInterval.symm p.1) : ℝ) := by
          simpa only [unitInterval.symm_symm] using Subtype.coe_le_coe.mpr
            (unitInterval.symm_le_symm.mpr
              (unitInterval.mul_le_left (x := unitInterval.symm d) (y := unitInterval.symm p.1)))
        have hd := d.property.1
        have hr := (unitInterval.symm (unitInterval.symm d *
          unitInterval.symm p.1)).property.1
        exact sub_le_sub_left (mul_le_mul_of_nonneg_left (by nlinarith) hε) c⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (ψ.continuousOn_morseCellMap hball hk).comp_continuous (by fun_prop)
    intro p
    rw [mem_closedBall_zero_iff, norm_smul,
      Real.norm_of_nonneg (unitInterval.symm _).property.1,
      mem_sphere_zero_iff_norm.mp p.2.down.property, mul_one]
    exact (unitInterval.symm _).property.2

/-- Coordinates of the parametrized annulus, read through the existing Morse cell map. -/
theorem coe_morseAnnulusMap_apply
    (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
    (hε : 0 ≤ ε) (hball : closedBall 0 √ε ⊆ ψ.target)
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    (d s : I) (θ : TopCat.diskBoundary.{u} k) :
    (ψ.morseAnnulusMap hk hε hball hf d (s, θ) : M) =
      ψ.morseCellMap hk ε
        ((unitInterval.symm (unitInterval.symm d * unitInterval.symm s) : ℝ) •
          (θ.down : EuclideanSpace ℝ (Fin k))) :=
  (rfl)

/-- The inner seam is the small negative-coordinate circle. -/
@[simp]
theorem coe_morseAnnulusMap_zero
    (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
    (hε : 0 ≤ ε) (hball : closedBall 0 √ε ⊆ ψ.target)
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    (d : I) (θ : TopCat.diskBoundary.{u} k) :
    (ψ.morseAnnulusMap hk hε hball hf d (0, θ) : M) =
      ψ.morseCellMap hk ε ((d : ℝ) • (θ.down : EuclideanSpace ℝ (Fin k))) := by
  simp [coe_morseAnnulusMap_apply]

/-- The outer seam is the actual attaching map of the original characteristic disc. -/
@[simp]
theorem coe_morseAnnulusMap_one
    (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
    (hε : 0 ≤ ε) (hball : closedBall 0 √ε ⊆ ψ.target)
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    (d : I) (θ : TopCat.diskBoundary.{u} k) :
    (ψ.morseAnnulusMap hk hε hball hf d (1, θ) : M) =
      (ψ.morseAttachingMap hk hε hball hf θ : M) := by
  simpa only [coe_morseAnnulusMap_apply, unitInterval.symm_one, mul_zero,
    unitInterval.symm_zero, Set.Icc.coe_one, one_smul] using
    (coe_morseAttachingMap_apply hball hf hk hε θ).symm

/-- The function decreases quadratically with the actual radial coordinate of the annulus. -/
theorem apply_morseAnnulusMap
    (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
    (hε : 0 ≤ ε) (hball : closedBall 0 √ε ⊆ ψ.target)
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    (d s : I) (θ : TopCat.diskBoundary.{u} k) :
    f (ψ.morseAnnulusMap hk hε hball hf d (s, θ)) =
      c - ε * ((d : ℝ) + (1 - d) * s) ^ 2 := by
  have hn : ‖(θ.down : EuclideanSpace ℝ (Fin k))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp θ.down.property
  have hnorm : ‖(unitInterval.symm (unitInterval.symm d * unitInterval.symm s) : ℝ) •
      (θ.down : EuclideanSpace ℝ (Fin k))‖ =
      (unitInterval.symm (unitInterval.symm d * unitInterval.symm s) : ℝ) := by
    rw [norm_smul, Real.norm_of_nonneg (unitInterval.symm _).property.1, hn, mul_one]
  rw [coe_morseAnnulusMap_apply,
    ψ.apply_morseCellMap_eq_sub_mul_norm_sq hball hf hk hε
      (by rw [hnorm]; exact (unitInterval.symm _).property.2), hnorm]
  simp only [unitInterval.coe_symm_eq, Set.Icc.coe_mul]
  ring

/-- The value of the function on the inner seam is the level of the smaller circle. -/
theorem apply_morseAnnulusMap_zero
    (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
    (hε : 0 ≤ ε) (hball : closedBall 0 √ε ⊆ ψ.target)
    (hf : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    (d : I) (θ : TopCat.diskBoundary.{u} k) :
    f (ψ.morseAnnulusMap hk hε hball hf d (0, θ)) = c - ε * (d : ℝ) ^ 2 := by
  simpa only [Set.Icc.coe_zero, mul_zero, add_zero] using
    ψ.apply_morseAnnulusMap hk hε hball hf d 0 θ

end OpenPartialHomeomorph

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {Iₘ : ModelWithCorners ℝ E H} [Iₘ.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold Iₘ ∞ M] [T2Space M]
  {f : M → ℝ} {c ε : ℝ} {n k : ℕ}

/-- In a compact critical-free band below a critical level, the actual annulus of a Morse
chart is homotopic to the retraction track of its small inner circle. The homotopy fixes the
inner seam and carries the outer seam into the original lower sublevel at every time. -/
theorem exists_morseAnnulus_deformation (hf : ContMDiff Iₘ 𝓘(ℝ) ∞ f)
    (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
    (hε : 0 ≤ ε) (hball : closedBall 0 √ε ⊆ ψ.target)
    (hchart : ∀ y ∈ ψ.source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ y j ^ 2)
    (d : unitInterval)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c - ε * (d : ℝ) ^ 2)))
    (hreg : ∀ x, c - ε ≤ f x → f x ≤ c - ε * (d : ℝ) ^ 2 →
      mfderiv Iₘ 𝓘(ℝ) f x ≠ 0)
    (β : C(unitInterval, unitInterval)) (hβ₀ : β 0 = 0) (hβ₁ : β 1 = 1) :
    let γ := ψ.morseAnnulusMap hk hε hball hchart d
    ∃ r : C({x : M | f x ≤ c - ε * (d : ℝ) ^ 2}, {x : M | f x ≤ c - ε * (d : ℝ) ^ 2}),
      ∃ R : (ContinuousMap.id _).HomotopyRel r {x | f x.val ≤ c - ε},
        (∀ x, f (r x).val ≤ c - ε) ∧
        Nonempty (γ.HomotopyWith
          (R.toHomotopy.retractionTrack β ⟨fun θ ↦ γ (0, θ), by fun_prop⟩)
          (fun g ↦ (∀ θ, g (0, θ) = γ (0, θ)) ∧ ∀ θ, f (g (1, θ)).val ≤ c - ε)) := by
  have hab : c - ε ≤ c - ε * (d : ℝ) ^ 2 := by
    have hd := pow_le_one₀ d.property.1 d.property.2 (n := 2)
    nlinarith
  obtain ⟨r, -, ⟨R⟩⟩ := exists_sublevelDeformation hf hab hcompact hreg
  let r' := (sublevelInclusion f _ _ hab).comp r
  have hr : ∀ x, f (r' x).val ≤ c - ε := by
    intro x
    simpa only [r', ContinuousMap.comp_apply, coe_sublevelInclusion_apply, mem_ofPred_eq] using
      (r x).property
  refine ⟨r', R.symm, hr, ⟨?_⟩⟩
  apply R.symm.annulusToTrack hr _ _ β hβ₀ hβ₁
  intro θ
  simp only [mem_ofPred_eq]
  rw [ψ.coe_morseAnnulusMap_one]
  exact (ψ.morseAttachingMap hk hε hball hchart θ).property

end TauCeti
