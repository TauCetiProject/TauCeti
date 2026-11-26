/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.TrajectorySpace
import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Face

/-!
# Changing the levels on which broken trajectories are recorded

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X`. The compactified space `L_c(x, y)` of trajectories between critical points
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`) records each broken trajectory from
`x` to `y` by its points on the levels of a family `c`. This file shows that the choice of the
levels does not matter, as long as they are dense between any two critical values and avoid the
critical values.

Let `c` and `c'` be two such families. A broken trajectory recorded on the levels of `c` has a
point on every level (`TauCeti.IsAdaptedPseudoGradient.morseLevelPoint`), and its points on the
levels of `c'` record the same broken trajectory
(`TauCeti.IsAdaptedPseudoGradient.mem_morseBrokenTrajectoryRecords_morseLevelPoint`,
`TauCeti.IsAdaptedPseudoGradient.morseLevelPoint_morseLevelPoint`). This re-recording is a
homeomorphism `L_c(x, y) ≃ₜ L_{c'}(x, y)`
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceLevelHomeomorph`), whose inverse
re-records on the levels of `c`. It is compatible with all the structure of the trajectory
spaces:

* it commutes with the composition maps, the concatenation of broken trajectories at a critical
  point (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceLevelHomeomorph_comp`);
* it carries the boundary, the broken trajectories that are not unbroken, onto the boundary
  (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceLevelHomeomorph_mem_boundary_iff`),
  since the boundary is the union of the images of the composition maps;
* it does not change the Moore path of a broken trajectory, parametrized by the values of `f`
  (`TauCeti.IsAdaptedPseudoGradient.morseLevelPath_morseBrokenTrajectorySpaceLevelHomeomorph`).

So twisting chain systems on the trajectory spaces for `c` are carried to twisting chain systems
for `c'`, and their evaluations into Moore paths agree. This is the independence of the
Barraud–Cornea cocycle from the levels.

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceLevelHomeomorph`: the homeomorphism
  `L_c(x, y) ≃ₜ L_{c'}(x, y)` recording each broken trajectory on the levels of `c'`.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceLevelHomeomorph_comp`: it commutes
  with the composition maps.
* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceLevelHomeomorph_mem_boundary_iff`: it
  preserves the boundary.
* `TauCeti.IsAdaptedPseudoGradient.morseLevelPath_morseBrokenTrajectorySpaceLevelHomeomorph`: it
  preserves the Moore paths of broken trajectories.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3 and 5.
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

variable (hX : IsAdaptedPseudoGradient f X) {c : ι → ℝ} {c' : ι' → ℝ}
  (hf : IsMorse 𝓘(ℝ, E) f)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
  (hdense' : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c'))
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
  (hc' : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c' i ≠ f x)

/-! ### Recording on other levels -/

section LevelMap

include hf hdense hc'

/-- The points on the levels of `c'` of a broken trajectory of the trajectory space for the levels
of `c` lie in the trajectory space for the levels of `c'`. -/
private theorem morseLevelPoint_mem_morseBrokenTrajectorySpace (x y : criticalPoints 𝓘(ℝ, E) f)
    (w : hX.morseBrokenTrajectorySpace c x y) :
    (fun i : c' ⁻¹' Ioo (f y) (f x) ↦
      hX.morseLevelPoint x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) w (c' i)) ∈
      hX.morseBrokenTrajectorySpace c' x y :=
  mem_morseBrokenTrajectorySpace.2 ⟨(mem_morseBrokenTrajectorySpace.1 w.property).1,
    hX.mem_morseBrokenTrajectoryRecords_morseLevelPoint hf
      (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y))
      (morseBrokenTrajectorySpace_subset _ _ w.property) (fun i ↦ Ioo_subset_Icc_self i.property)
      fun i m hm ↦ hc' i ⟨m, mem_criticalPoints_iff_mfderiv_eq_zero.2 hm⟩⟩

/-- Recording the broken trajectories of the trajectory space for the levels of `c` on the levels
of `c'`, as a continuous map between the trajectory spaces. -/
private noncomputable def morseBrokenTrajectorySpaceLevelMap (x y : criticalPoints 𝓘(ℝ, E) f) :
    C(hX.morseBrokenTrajectorySpace c x y, hX.morseBrokenTrajectorySpace c' x y) where
  toFun w := ⟨_, hX.morseLevelPoint_mem_morseBrokenTrajectorySpace hf hdense hc' x y w⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
    exact (hX.continuousOn_morseLevelPoint hf
      (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y))).comp_continuous
      (continuous_subtypeVal.prodMk continuous_const)
      fun w ↦ ⟨morseBrokenTrajectorySpace_subset _ _ w.property, mem_univ _⟩

end LevelMap

/-- Re-recording on the levels of `c` a broken trajectory first re-recorded on the levels of `c'`
gives back the original record. -/
private theorem morseBrokenTrajectorySpaceLevelMap_morseBrokenTrajectorySpaceLevelMap
    (x y : criticalPoints 𝓘(ℝ, E) f) (w : hX.morseBrokenTrajectorySpace c x y) :
    hX.morseBrokenTrajectorySpaceLevelMap hf hdense' hc x y
      (hX.morseBrokenTrajectorySpaceLevelMap hf hdense hc' x y w) = w := by
  have hd := subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y)
  have hd' := subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense' x y)
  have hw := morseBrokenTrajectorySpace_subset _ _ w.property
  refine Subtype.ext (funext fun i ↦ ?_)
  exact (hX.morseLevelPoint_morseLevelPoint hf hd hd' hw (fun i ↦ Ioo_subset_Icc_self i.property)
      (fun i m hm ↦ hc' i ⟨m, mem_criticalPoints_iff_mfderiv_eq_zero.2 hm⟩) (c i)).trans
    (hX.morseLevelPoint_apply_level hf hd hw i)

/-! ### The homeomorphism of trajectory spaces -/

/-- **Changing the levels of the trajectory spaces.** For two families of levels `c` and `c'`,
each dense between any two critical values and avoiding the critical values, recording each
broken trajectory from `x` to `y` on the levels of `c'` instead of those of `c` is a
homeomorphism between the trajectory spaces. Its inverse records on the levels of `c`
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceLevelHomeomorph_symm`). -/
noncomputable def morseBrokenTrajectorySpaceLevelHomeomorph (x y : criticalPoints 𝓘(ℝ, E) f) :
    hX.morseBrokenTrajectorySpace c x y ≃ₜ hX.morseBrokenTrajectorySpace c' x y where
  toFun := hX.morseBrokenTrajectorySpaceLevelMap hf hdense hc' x y
  invFun := hX.morseBrokenTrajectorySpaceLevelMap hf hdense' hc x y
  left_inv := hX.morseBrokenTrajectorySpaceLevelMap_morseBrokenTrajectorySpaceLevelMap hf hdense
    hdense' hc hc' x y
  right_inv := hX.morseBrokenTrajectorySpaceLevelMap_morseBrokenTrajectorySpaceLevelMap hf hdense'
    hdense hc' hc x y
  continuous_toFun := (hX.morseBrokenTrajectorySpaceLevelMap hf hdense hc' x y).continuous
  continuous_invFun := (hX.morseBrokenTrajectorySpaceLevelMap hf hdense' hc x y).continuous

/-- The record on the level `c' i` of a broken trajectory recorded on the levels of `c` is its
point on that level. -/
@[simp]
theorem coe_morseBrokenTrajectorySpaceLevelHomeomorph_apply (x y : criticalPoints 𝓘(ℝ, E) f)
    (w : hX.morseBrokenTrajectorySpace c x y) (i : c' ⁻¹' Ioo (f y) (f x)) :
    (hX.morseBrokenTrajectorySpaceLevelHomeomorph hf hdense hdense' hc hc' x y w :
      c' ⁻¹' Ioo (f y) (f x) → M) i =
      hX.morseLevelPoint x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) w (c' i) :=
  (rfl)

/-- The inverse of the change of levels from `c` to `c'` is the change of levels from `c'` to
`c`. -/
@[simp]
theorem morseBrokenTrajectorySpaceLevelHomeomorph_symm (x y : criticalPoints 𝓘(ℝ, E) f) :
    (hX.morseBrokenTrajectorySpaceLevelHomeomorph hf hdense hdense' hc hc' x y).symm =
      hX.morseBrokenTrajectorySpaceLevelHomeomorph hf hdense' hdense hc' hc x y :=
  (rfl)

/-- **The change of levels preserves the Moore paths** of broken trajectories, parametrized by the
values of `f`. -/
theorem morseLevelPath_morseBrokenTrajectorySpaceLevelHomeomorph (x y : criticalPoints 𝓘(ℝ, E) f)
    (w : hX.morseBrokenTrajectorySpace c x y) :
    hX.morseLevelPath hf (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense' x y))
        (inclusion (morseBrokenTrajectorySpace_subset _ _)
          (hX.morseBrokenTrajectorySpaceLevelHomeomorph hf hdense hdense' hc hc' x y w)) =
      hX.morseLevelPath hf (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y))
        (inclusion (morseBrokenTrajectorySpace_subset _ _) w) := by
  refine MoorePath.ext (by simp only [length_morseLevelPath]) fun t ↦ ?_
  simp only [morseLevelPath_apply]
  exact hX.morseLevelPoint_morseLevelPoint hf
    (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y))
    (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense' x y))
    (morseBrokenTrajectorySpace_subset _ _ w.property) (fun i ↦ Ioo_subset_Icc_self i.property)
    (fun i m hm ↦ hc' i ⟨m, mem_criticalPoints_iff_mfderiv_eq_zero.2 hm⟩) _

/-- **The change of levels commutes with the composition maps**: re-recording the concatenation of
two broken trajectories at a critical point is concatenating their re-recordings. -/
theorem morseBrokenTrajectorySpaceLevelHomeomorph_comp (x z y : criticalPoints 𝓘(ℝ, E) f)
    (w : hX.morseBrokenTrajectorySpace c x z × hX.morseBrokenTrajectorySpace c z y) :
    hX.morseBrokenTrajectorySpaceLevelHomeomorph hf hdense hdense' hc hc' x y
        (hX.morseBrokenTrajectorySpaceComp hc x z y w) =
      hX.morseBrokenTrajectorySpaceComp hc' x z y
        (hX.morseBrokenTrajectorySpaceLevelHomeomorph hf hdense hdense' hc hc' x z w.1,
          hX.morseBrokenTrajectorySpaceLevelHomeomorph hf hdense hdense' hc hc' z y w.2) := by
  have hd (p q : criticalPoints 𝓘(ℝ, E) f) :=
    subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense p q)
  have hw₁ := morseBrokenTrajectorySpace_subset _ _ w.1.property
  have hw₂ := morseBrokenTrajectorySpace_subset _ _ w.2.property
  refine Subtype.ext (funext fun i ↦ ?_)
  rw [coe_morseBrokenTrajectorySpaceLevelHomeomorph_apply,
    coe_morseBrokenTrajectorySpaceComp_apply, coe_morseBrokenTrajectorySpaceComp_apply]
  -- Above the level of `z` both sides are points of the first broken trajectory, below it points
  -- of the second.
  by_cases h : f z < c' i
  · rw [concatLevelRecords_of_lt _ _ _ h, coe_morseBrokenTrajectorySpaceLevelHomeomorph_apply]
    exact hX.morseLevelPoint_concatLevelRecords_of_le (fun j ↦ hc j z) hw₁ hw₂ hf (hd x y) (hd x z)
      h.le
  · rw [concatLevelRecords_of_gt _ _ _ (lt_of_le_of_ne (not_lt.1 h) (hc' i z)),
      coe_morseBrokenTrajectorySpaceLevelHomeomorph_apply]
    exact hX.morseLevelPoint_concatLevelRecords_of_ge (fun j ↦ hc j z) hw₁ hw₂ hf (hd x y) (hd z y)
      (not_lt.1 h)

/-- The change of levels carries the boundary into the boundary: a boundary point is a
concatenation at a critical point, and the change of levels commutes with concatenation. -/
private theorem morseBrokenTrajectorySpaceLevelHomeomorph_mem_boundary
    {x y : criticalPoints 𝓘(ℝ, E) f} {w : hX.morseBrokenTrajectorySpace c x y}
    (hw : w ∈ hX.morseBrokenTrajectorySpaceBoundary c x y) :
    hX.morseBrokenTrajectorySpaceLevelHomeomorph hf hdense hdense' hc hc' x y w ∈
      hX.morseBrokenTrajectorySpaceBoundary c' x y := by
  obtain ⟨z, a, b, -, rfl⟩ :=
    hX.exists_morseBrokenTrajectorySpaceComp_eq_of_mem_morseBrokenTrajectorySpaceBoundary hc hw
  rw [morseBrokenTrajectorySpaceLevelHomeomorph_comp]
  exact hX.morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary hc' hdense' _ _ _ _

/-- **The change of levels preserves the boundary**: a broken trajectory is not unbroken exactly
when its re-recording is not. -/
theorem morseBrokenTrajectorySpaceLevelHomeomorph_mem_boundary_iff
    {x y : criticalPoints 𝓘(ℝ, E) f} {w : hX.morseBrokenTrajectorySpace c x y} :
    hX.morseBrokenTrajectorySpaceLevelHomeomorph hf hdense hdense' hc hc' x y w ∈
        hX.morseBrokenTrajectorySpaceBoundary c' x y ↔
      w ∈ hX.morseBrokenTrajectorySpaceBoundary c x y := by
  refine ⟨fun hw ↦ ?_, hX.morseBrokenTrajectorySpaceLevelHomeomorph_mem_boundary hf hdense hdense'
    hc hc'⟩
  have h := hX.morseBrokenTrajectorySpaceLevelHomeomorph_mem_boundary hf hdense' hdense hc' hc hw
  rwa [← morseBrokenTrajectorySpaceLevelHomeomorph_symm, Homeomorph.symm_apply_apply] at h

end IsAdaptedPseudoGradient

end TauCeti
