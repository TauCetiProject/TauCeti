/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.TrajectorySpace
import TauCeti.Data.Fin.Basic

/-!
# Changing the levels on which broken trajectories are recorded

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X`. The compactified space of trajectories from `p` to `r` is realized as the
records of broken trajectories on a family of levels `c`
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords`): the families of their points on
these levels. This file shows that the realization does not depend on the levels, as long as they
are dense between `f r` and `f p` and avoid the critical values.

A record `w` on the levels `c` determines the point of its broken trajectory on every level `a`
(`TauCeti.IsAdaptedPseudoGradient.morseLevelPoint`), continuously in `w` and `a`. Reading these
points on the levels of another family `c'` gives a record on `c'` of the same broken trajectory
(`IsAdaptedPseudoGradient.morseLevelPoint_comp_mem_morseBrokenTrajectoryRecords`), which is
unbroken when `w` is (`IsAdaptedPseudoGradient.morseLevelPoint_comp_mem_morseTrajectoryRecords`)
and has the same points on every level
(`TauCeti.IsAdaptedPseudoGradient.morseLevelPoint_morseLevelPoint_comp`). Reading back on `c`
recovers `w`, so this is a homeomorphism between the two spaces of records
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecordsHomeomorph`). It preserves the
points on all levels, hence the Moore paths of the broken trajectories
(`IsAdaptedPseudoGradient.morseLevelPath_morseBrokenTrajectoryRecordsHomeomorph`), and the unbroken
trajectories.

On the trajectory spaces between critical points
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`), the change of levels
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceHomeomorph`) preserves the boundary
(`morseBrokenTrajectorySpaceHomeomorph_mem_morseBrokenTrajectorySpaceBoundary_iff`) and commutes
with the composition maps (`morseBrokenTrajectorySpaceHomeomorph_morseBrokenTrajectorySpaceComp`,
both in the namespace `TauCeti.IsAdaptedPseudoGradient`):
the change of levels is an isomorphism of the families of compactified trajectory spaces with
their faces, and twisting chain systems are carried along it.

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecordsHomeomorph`: the records of broken
  trajectories on two families of levels are homeomorphic.
* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceHomeomorph`: so are the trajectory
  spaces between two critical points.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseLevelPoint_morseBrokenTrajectoryRecordsHomeomorph`,
  `morseLevelPath_morseBrokenTrajectoryRecordsHomeomorph`: the change of levels keeps the points of
  a broken trajectory on all levels, and its Moore path.
* `morseBrokenTrajectoryRecordsHomeomorph_mem_morseTrajectoryRecords_iff`: it keeps the unbroken
  trajectories.
* `morseBrokenTrajectorySpaceHomeomorph_mem_morseBrokenTrajectorySpaceBoundary_iff`: on the
  trajectory spaces it keeps the boundary.
* `morseBrokenTrajectorySpaceHomeomorph_morseBrokenTrajectorySpaceComp`: it commutes with the
  composition maps.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 5 and 6.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι ι' : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-! ### Reading a record on other levels -/

section Records

variable {hX} {p r : M} {c : ι → ℝ} {c' : ι' → ℝ} {w : ι → M}

/-- On levels strictly between `f r` and `f p` that avoid the critical values, the points of a
recorded broken trajectory lie on its components. -/
private theorem morseLevelPoint_comp_chain (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) (hc' : ∀ i', c' i' ∈ Ioo (f r) (f p))
    (hreg' : ∀ i' (q : criticalPoints 𝓘(ℝ, E) f), c' i' ≠ f q) {k : ℕ} {x : Fin (k + 1) → M}
    {z : Fin k → M} (hx0 : x 0 = p) (hxk : x (Fin.last k) = r)
    (hxc : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0) (hxne : ∀ j : Fin k, x j.castSucc ≠ x j.succ)
    (hz : ∀ j : Fin k, z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ))
    (hw : ∀ i, f (w i) = c i ∧ ∃ j t, hX.flow t (z j) = w i) (i' : ι') :
    f (hX.morseLevelPoint p r c w (c' i')) = c' i' ∧
      ∃ j t, hX.flow t (z j) = hX.morseLevelPoint p r c w (c' i') := by
  -- The level `c' i'` lies strictly between the values of two consecutive critical points of the
  -- chain, so the component joining them crosses it.
  obtain ⟨j, hlo, hhi⟩ := Fin.exists_succ_lt_lt_castSucc (g := fun j ↦ f (x j))
    (fun j h ↦ hreg' i' ⟨x j, mem_criticalPoints_iff_mfderiv_eq_zero.2 (hxc j)⟩ h.symm)
    (by rw [hx0]; exact (hc' i').2) (by rw [hxk]; exact (hc' i').1)
  obtain ⟨t, ht⟩ :=
    (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet (hxne j) (hz j) hlo hhi).exists
  have h := hX.morseLevelPoint_eq hf hdense hx0 hxk hxc hxne hz hw (Or.inr ⟨j, t, rfl⟩)
  rw [ht] at h
  exact ⟨by rw [h, ht], j, t, h.symm⟩

/-- **Reading a recorded broken trajectory on other levels.** If `w` records a broken trajectory
from `p` to `r` on levels dense between `f r` and `f p`, its points on levels `c'` strictly between
`f r` and `f p` that avoid the critical values record the same broken trajectory on `c'`. -/
theorem morseLevelPoint_comp_mem_morseBrokenTrajectoryRecords (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) (hw : w ∈ hX.morseBrokenTrajectoryRecords p r c)
    (hc' : ∀ i', c' i' ∈ Ioo (f r) (f p))
    (hreg' : ∀ i' (q : criticalPoints 𝓘(ℝ, E) f), c' i' ≠ f q) :
    hX.morseLevelPoint p r c w ∘ c' ∈ hX.morseBrokenTrajectoryRecords p r c' := by
  obtain ⟨k, x, z, hx0, hxk, hxc, hxne, hz, hrec⟩ := hX.mem_morseBrokenTrajectoryRecords.1 hw
  exact hX.mem_morseBrokenTrajectoryRecords.2 ⟨k, x, z, hx0, hxk, hxc, hxne, hz,
    morseLevelPoint_comp_chain hf hdense hc' hreg' hx0 hxk hxc hxne hz hrec⟩

/-- **Reading a recorded unbroken trajectory on other levels** gives a record of the same unbroken
trajectory. -/
theorem morseLevelPoint_comp_mem_morseTrajectoryRecords (hf : IsMorse 𝓘(ℝ, E) f)
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0) (hpr : p ≠ r)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) (hw : w ∈ hX.morseTrajectoryRecords p r c)
    (hc' : ∀ i', c' i' ∈ Ioo (f r) (f p))
    (hreg' : ∀ i' (q : criticalPoints 𝓘(ℝ, E) f), c' i' ≠ f q) :
    hX.morseLevelPoint p r c w ∘ c' ∈ hX.morseTrajectoryRecords p r c' := by
  obtain ⟨y, hy, hrec⟩ := hX.mem_morseTrajectoryRecords.1 hw
  -- An unbroken trajectory is a broken one with the single component `y`.
  have hchain := morseLevelPoint_comp_chain (k := 1) (x := ![p, r]) (z := ![y]) hf hdense hc'
    hreg' rfl rfl (fun j ↦ by fin_cases j <;> assumption) (fun j ↦ by fin_cases j; exact hpr)
    (fun j ↦ by fin_cases j; exact hy) fun i ↦ ⟨(hrec i).1, 0, (hrec i).2⟩
  refine hX.mem_morseTrajectoryRecords.2 ⟨y, hy, fun i' ↦ ?_⟩
  obtain ⟨h, j, t, ht⟩ := hchain i'
  exact ⟨h, t, by simpa using ht⟩

/-- **Reading a record on other levels keeps the points on all levels.** For records on levels
dense between `f r` and `f p`, the record on `c'` of the broken trajectory recorded by `w` has the
same point as `w` on every level. -/
theorem morseLevelPoint_morseLevelPoint_comp (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) (hdense' : Ioo (f r) (f p) ⊆ closure (range c'))
    (hw : w ∈ hX.morseBrokenTrajectoryRecords p r c) (hc' : ∀ i', c' i' ∈ Ioo (f r) (f p))
    (hreg' : ∀ i' (q : criticalPoints 𝓘(ℝ, E) f), c' i' ≠ f q) :
    hX.morseLevelPoint p r c' (hX.morseLevelPoint p r c w ∘ c') = hX.morseLevelPoint p r c w := by
  have hw' := morseLevelPoint_comp_mem_morseBrokenTrajectoryRecords hf hdense hw hc' hreg'
  funext a
  rcases le_or_gt (f p) a with hpa | hpa
  · rw [hX.morseLevelPoint_of_apply_le hpa, hX.morseLevelPoint_of_apply_le hpa]
  rcases le_or_gt a (f r) with har | har
  · rw [hX.morseLevelPoint_of_le_apply hw' har, hX.morseLevelPoint_of_le_apply hw har]
  -- Strictly between the ends, both records have the same points on the dense levels of `c'`.
  refine hX.morseLevelPoint_eqOn_Icc hf hdense' hdense hw' hw (har.trans hpa) hdense' ?_
    ⟨har.le, hpa.le⟩
  rintro _ ⟨i', rfl⟩
  exact hX.morseLevelPoint_apply_level hf hdense' hw' i'

variable (hX) in
/-- **Changing the levels of the records of broken trajectories.** For two families of levels `c`
and `c'` strictly between `f r` and `f p`, both dense there and avoiding the critical values,
reading the points of a broken trajectory on the levels of `c'` is a homeomorphism from its records
on `c` to its records on `c'`. Its inverse reads the points on the levels of `c`. -/
noncomputable def morseBrokenTrajectoryRecordsHomeomorph (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c)) (hdense' : Ioo (f r) (f p) ⊆ closure (range c'))
    (hc : ∀ i, c i ∈ Ioo (f r) (f p)) (hreg : ∀ i (q : criticalPoints 𝓘(ℝ, E) f), c i ≠ f q)
    (hc' : ∀ i', c' i' ∈ Ioo (f r) (f p))
    (hreg' : ∀ i' (q : criticalPoints 𝓘(ℝ, E) f), c' i' ≠ f q) :
    hX.morseBrokenTrajectoryRecords p r c ≃ₜ hX.morseBrokenTrajectoryRecords p r c' where
  toFun w := ⟨hX.morseLevelPoint p r c w ∘ c',
    morseLevelPoint_comp_mem_morseBrokenTrajectoryRecords hf hdense w.property hc' hreg'⟩
  invFun w := ⟨hX.morseLevelPoint p r c' w ∘ c,
    morseLevelPoint_comp_mem_morseBrokenTrajectoryRecords hf hdense' w.property hc hreg⟩
  left_inv w := Subtype.ext <| by
    simp only [morseLevelPoint_morseLevelPoint_comp hf hdense hdense' w.property hc' hreg']
    exact funext (hX.morseLevelPoint_apply_level hf hdense w.property)
  right_inv w := Subtype.ext <| by
    simp only [morseLevelPoint_morseLevelPoint_comp hf hdense' hdense w.property hc hreg]
    exact funext (hX.morseLevelPoint_apply_level hf hdense' w.property)
  continuous_toFun := (continuous_pi fun _ ↦
    (hX.continuousOn_morseLevelPoint hf hdense).comp_continuous
      (continuous_subtypeVal.prodMk continuous_const) fun w ↦ ⟨w.property, mem_univ _⟩).subtype_mk _
  continuous_invFun := (continuous_pi fun _ ↦
    (hX.continuousOn_morseLevelPoint hf hdense').comp_continuous
      (continuous_subtypeVal.prodMk continuous_const) fun w ↦ ⟨w.property, mem_univ _⟩).subtype_mk _

variable (hf : IsMorse 𝓘(ℝ, E) f) (hdense : Ioo (f r) (f p) ⊆ closure (range c))
  (hdense' : Ioo (f r) (f p) ⊆ closure (range c')) (hc : ∀ i, c i ∈ Ioo (f r) (f p))
  (hreg : ∀ i (q : criticalPoints 𝓘(ℝ, E) f), c i ≠ f q) (hc' : ∀ i', c' i' ∈ Ioo (f r) (f p))
  (hreg' : ∀ i' (q : criticalPoints 𝓘(ℝ, E) f), c' i' ≠ f q)

/-- The record on the new levels is the family of the points of the broken trajectory on them. -/
@[simp]
theorem coe_morseBrokenTrajectoryRecordsHomeomorph_apply
    (w : hX.morseBrokenTrajectoryRecords p r c) :
    (hX.morseBrokenTrajectoryRecordsHomeomorph hf hdense hdense' hc hreg hc' hreg' w : ι' → M) =
      hX.morseLevelPoint p r c w ∘ c' :=
  (rfl)

/-- The inverse of a change of levels is the change of levels back. -/
@[simp]
theorem morseBrokenTrajectoryRecordsHomeomorph_symm :
    (hX.morseBrokenTrajectoryRecordsHomeomorph hf hdense hdense' hc hreg hc' hreg').symm =
      hX.morseBrokenTrajectoryRecordsHomeomorph hf hdense' hdense hc' hreg' hc hreg :=
  (rfl)

/-- **A change of levels keeps the points of a broken trajectory on all levels.** -/
theorem morseLevelPoint_morseBrokenTrajectoryRecordsHomeomorph
    (w : hX.morseBrokenTrajectoryRecords p r c) :
    hX.morseLevelPoint p r c'
        (hX.morseBrokenTrajectoryRecordsHomeomorph hf hdense hdense' hc hreg hc' hreg' w) =
      hX.morseLevelPoint p r c w :=
  morseLevelPoint_morseLevelPoint_comp hf hdense hdense' w.property hc' hreg'

/-- **A change of levels keeps the Moore path of a broken trajectory.** -/
@[simp]
theorem morseLevelPath_morseBrokenTrajectoryRecordsHomeomorph
    (w : hX.morseBrokenTrajectoryRecords p r c) :
    hX.morseLevelPath hf hdense'
        (hX.morseBrokenTrajectoryRecordsHomeomorph hf hdense hdense' hc hreg hc' hreg' w) =
      hX.morseLevelPath hf hdense w :=
  MoorePath.ext (by rw [length_morseLevelPath, length_morseLevelPath]) fun t ↦ by
    rw [morseLevelPath_apply, morseLevelPath_apply,
      morseLevelPoint_morseBrokenTrajectoryRecordsHomeomorph]

/-- **A change of levels keeps the unbroken trajectories**, between distinct critical points. -/
theorem morseBrokenTrajectoryRecordsHomeomorph_mem_morseTrajectoryRecords_iff
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0) (hpr : p ≠ r)
    (w : hX.morseBrokenTrajectoryRecords p r c) :
    (hX.morseBrokenTrajectoryRecordsHomeomorph hf hdense hdense' hc hreg hc' hreg' w : ι' → M) ∈
        hX.morseTrajectoryRecords p r c' ↔ (w : ι → M) ∈ hX.morseTrajectoryRecords p r c := by
  refine ⟨fun h ↦ ?_, fun h ↦
    morseLevelPoint_comp_mem_morseTrajectoryRecords hf hp hr hpr hdense h hc' hreg'⟩
  rw [← congrArg Subtype.val
    ((hX.morseBrokenTrajectoryRecordsHomeomorph hf hdense hdense' hc hreg hc'
      hreg').symm_apply_apply w)]
  exact morseLevelPoint_comp_mem_morseTrajectoryRecords hf hp hr hpr hdense' h hc hreg

end Records

/-! ### Changing the levels of the trajectory spaces -/

section TrajectorySpace

variable {c : ι → ℝ} {c' : ι' → ℝ} (hf : IsMorse 𝓘(ℝ, E) f)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
  (hdense' : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c'))
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
  (hc' : ∀ i' (x : criticalPoints 𝓘(ℝ, E) f), c' i' ≠ f x)

/-- The change of levels of the records of broken trajectories between two critical points, on the
levels of `c` and of `c'` between their values. -/
private noncomputable abbrev recordsHomeomorph (x y : criticalPoints 𝓘(ℝ, E) f) :
    hX.morseBrokenTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) ≃ₜ
      hX.morseBrokenTrajectoryRecords x y ((c' ⁻¹' Ioo (f y) (f x)).domRestrict c') :=
  hX.morseBrokenTrajectoryRecordsHomeomorph hf
    (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y))
    (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense' x y)) (fun i ↦ i.property)
    (fun i ↦ hc i) (fun i ↦ i.property) fun i ↦ hc' i

/-- The change of levels back is the inverse of the change of levels of the records. -/
private theorem recordsHomeomorph_symm (x y : criticalPoints 𝓘(ℝ, E) f) :
    (hX.recordsHomeomorph hf hdense hdense' hc hc' x y).symm =
      hX.recordsHomeomorph hf hdense' hdense hc' hc x y :=
  (rfl)

/-- **Changing the levels of the trajectory spaces.** For two families of levels `c` and `c'`,
dense between any two critical values and avoiding the critical values, reading the points of a
broken trajectory on the levels of `c'` is a homeomorphism from the trajectory space from `x` to
`y` on the levels of `c` to the one on the levels of `c'`. -/
noncomputable def morseBrokenTrajectorySpaceHomeomorph (x y : criticalPoints 𝓘(ℝ, E) f) :
    hX.morseBrokenTrajectorySpace c x y ≃ₜ hX.morseBrokenTrajectorySpace c' x y where
  toFun w := ⟨hX.recordsHomeomorph hf hdense hdense' hc hc' x y
      (inclusion (morseBrokenTrajectorySpace_subset _ _) w),
    mem_morseBrokenTrajectorySpace.2 ⟨(mem_morseBrokenTrajectorySpace.1 w.property).1,
      Subtype.property _⟩⟩
  invFun w := ⟨hX.recordsHomeomorph hf hdense' hdense hc' hc x y
      (inclusion (morseBrokenTrajectorySpace_subset _ _) w),
    mem_morseBrokenTrajectorySpace.2 ⟨(mem_morseBrokenTrajectorySpace.1 w.property).1,
      Subtype.property _⟩⟩
  left_inv w := Subtype.ext <| by
    -- The records underlying both sides agree, as the change of levels back is the inverse.
    simp only [Subtype.coe_eta, ← recordsHomeomorph_symm hX hf hdense hdense' hc hc' x y,
      Homeomorph.symm_apply_apply, coe_inclusion]
  right_inv w := Subtype.ext <| by
    simp only [Subtype.coe_eta, ← recordsHomeomorph_symm hX hf hdense hdense' hc hc' x y,
      Homeomorph.apply_symm_apply, coe_inclusion]
  continuous_toFun := (continuous_subtypeVal.comp <|
    (hX.recordsHomeomorph hf hdense hdense' hc hc' x y).continuous.comp
      (continuous_inclusion _)).subtype_mk _
  continuous_invFun := (continuous_subtypeVal.comp <|
    (hX.recordsHomeomorph hf hdense' hdense hc' hc x y).continuous.comp
      (continuous_inclusion _)).subtype_mk _

variable {x y : criticalPoints 𝓘(ℝ, E) f}

/-- The record underlying the change of levels of a point of a trajectory space is the change of
levels of its record. -/
private theorem inclusion_morseBrokenTrajectorySpaceHomeomorph
    (w : hX.morseBrokenTrajectorySpace c x y) :
    inclusion (morseBrokenTrajectorySpace_subset _ _)
        (hX.morseBrokenTrajectorySpaceHomeomorph hf hdense hdense' hc hc' x y w) =
      hX.recordsHomeomorph hf hdense hdense' hc hc' x y
        (inclusion (morseBrokenTrajectorySpace_subset _ _) w) :=
  (rfl)

/-- The record on the new levels is the family of the points of the broken trajectory on them. -/
@[simp]
theorem coe_morseBrokenTrajectorySpaceHomeomorph_apply (w : hX.morseBrokenTrajectorySpace c x y) :
    (hX.morseBrokenTrajectorySpaceHomeomorph hf hdense hdense' hc hc' x y w :
        c' ⁻¹' Ioo (f y) (f x) → M) =
      hX.morseLevelPoint x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) w ∘
        (c' ⁻¹' Ioo (f y) (f x)).domRestrict c' :=
  (rfl)

/-- **The change of levels of the trajectory spaces keeps the Moore paths** of the broken
trajectories. -/
@[simp]
theorem morseLevelPath_morseBrokenTrajectorySpaceHomeomorph
    (w : hX.morseBrokenTrajectorySpace c x y) :
    hX.morseLevelPath hf (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense' x y))
        (inclusion (morseBrokenTrajectorySpace_subset _ _)
          (hX.morseBrokenTrajectorySpaceHomeomorph hf hdense hdense' hc hc' x y w)) =
      hX.morseLevelPath hf (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y))
        (inclusion (morseBrokenTrajectorySpace_subset _ _) w) := by
  rw [inclusion_morseBrokenTrajectorySpaceHomeomorph]
  exact hX.morseLevelPath_morseBrokenTrajectoryRecordsHomeomorph ..

/-- The inverse of a change of levels of the trajectory spaces is the change of levels back. -/
@[simp]
theorem morseBrokenTrajectorySpaceHomeomorph_symm :
    (hX.morseBrokenTrajectorySpaceHomeomorph hf hdense hdense' hc hc' x y).symm =
      hX.morseBrokenTrajectorySpaceHomeomorph hf hdense' hdense hc' hc x y :=
  (rfl)

/-- **The change of levels keeps the boundary of the trajectory spaces**: a broken trajectory is
unbroken on the new levels exactly when it is on the old ones. -/
theorem morseBrokenTrajectorySpaceHomeomorph_mem_morseBrokenTrajectorySpaceBoundary_iff
    (w : hX.morseBrokenTrajectorySpace c x y) :
    hX.morseBrokenTrajectorySpaceHomeomorph hf hdense hdense' hc hc' x y w ∈
        hX.morseBrokenTrajectorySpaceBoundary c' x y ↔
      w ∈ hX.morseBrokenTrajectorySpaceBoundary c x y := by
  rw [mem_morseBrokenTrajectorySpaceBoundary, mem_morseBrokenTrajectorySpaceBoundary, not_iff_not,
    ← coe_inclusion (morseBrokenTrajectorySpace_subset _ _),
    inclusion_morseBrokenTrajectorySpaceHomeomorph]
  exact hX.morseBrokenTrajectoryRecordsHomeomorph_mem_morseTrajectoryRecords_iff hf
    (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y))
    (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense' x y)) (fun i ↦ i.property)
    (fun i ↦ hc i) (fun i ↦ i.property) (fun i ↦ hc' i)
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property)
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property)
    (mem_morseBrokenTrajectorySpace.1 w.property).1
    (inclusion (morseBrokenTrajectorySpace_subset _ _) w)

/-- **The change of levels commutes with the composition maps of the trajectory spaces**: the
record on the new levels of a concatenation of broken trajectories is the concatenation of their
records on the new levels. -/
theorem morseBrokenTrajectorySpaceHomeomorph_morseBrokenTrajectorySpaceComp
    (x z y : criticalPoints 𝓘(ℝ, E) f) (u : hX.morseBrokenTrajectorySpace c x z)
    (v : hX.morseBrokenTrajectorySpace c z y) :
    hX.morseBrokenTrajectorySpaceHomeomorph hf hdense hdense' hc hc' x y
        (hX.morseBrokenTrajectorySpaceComp hc x z y (u, v)) =
      hX.morseBrokenTrajectorySpaceComp hc' x z y
        (hX.morseBrokenTrajectorySpaceHomeomorph hf hdense hdense' hc hc' x z u,
          hX.morseBrokenTrajectorySpaceHomeomorph hf hdense hdense' hc hc' z y v) := by
  refine Subtype.ext (funext fun i ↦ ?_)
  rw [coe_morseBrokenTrajectorySpaceHomeomorph_apply, coe_morseBrokenTrajectorySpaceComp_apply,
    coe_morseBrokenTrajectorySpaceComp_apply, Function.comp_apply]
  have hd := subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y)
  -- Above the level of `z` both sides are the points of `u`, below it those of `v`.
  rcases lt_or_gt_of_ne (hc' i z).symm with h | h
  · rw [concatLevelRecords_of_lt _ _ _ h, coe_morseBrokenTrajectorySpaceHomeomorph_apply]
    exact hX.morseLevelPoint_concatLevelRecords_of_le _
      (morseBrokenTrajectorySpace_subset _ _ u.property)
      (morseBrokenTrajectorySpace_subset _ _ v.property) hf hd
      (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x z)) h.le
  · rw [concatLevelRecords_of_gt _ _ _ h, coe_morseBrokenTrajectorySpaceHomeomorph_apply]
    exact hX.morseLevelPoint_concatLevelRecords_of_ge _
      (morseBrokenTrajectorySpace_subset _ _ u.property)
      (morseBrokenTrajectorySpace_subset _ _ v.property) hf hd
      (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense z y)) h.le

end TrajectorySpace

end IsAdaptedPseudoGradient

end TauCeti
