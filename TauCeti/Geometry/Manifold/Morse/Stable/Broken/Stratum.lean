/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Boundary
import TauCeti.Data.Fin.Basic
import TauCeti.Topology.PiCurry

/-!
# Closures of the strata of broken Morse trajectories

A stratum of the trajectory records through a prescribed chain of critical points allows an
unbroken trajectory at each step. Its closure allows a compactified trajectory at each step.
Restriction to the levels between successive points gives the homeomorphism with the ordered
product of the compactified trajectory spaces. Thus the factors of a closed stratum are the
spaces in which further breaking can occur independently.

The coordinate comparison uses
`TauCeti.IsAdaptedPseudoGradient.exists_homeomorph_morseBrokenTrajectoryStratum` on unbroken
factors and `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectorySpace_eq_closure`
to pass to compactified factors.

The inverse homeomorphism assembles the step records into a closed embedding in the full
compactification. Its image is the closure of the prescribed stratum there.

## References

* K. Wehrheim, *Smooth structures on Morse trajectory spaces, featuring finite ends and
  associative gluing*, Proceedings of the Freedman Fest, Geom. Topol. Monogr. 18 (2012),
  369–450, Theorem 2.3.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti.IsAdaptedPseudoGradient

section LevelPartition

variable {M : Type*} [TopologicalSpace M] {f : M → ℝ} {ι : Type*} {k : ℕ}
  {x : Fin (k + 1) → M} {c : ι → ℝ}
  (hanti : StrictAnti (f ∘ x))
  (hc : ∀ i, c i ∈ Ioo (f (x (Fin.last k))) (f (x 0)))
  (hcx : ∀ i j, c i ≠ f (x j))

/-- Restricting to the levels at every step of a descending chain reindexes the space of all
records. -/
private noncomputable def restrictLevelRecords :
    (ι → M) ≃ₜ ((j : Fin k) → (c ⁻¹' Ioo (f (x j.succ)) (f (x j.castSucc))) → M) :=
  (piSigmaConstHomeomorph M <| Equiv.ofBijective
    (fun i : Σ j : Fin k, c ⁻¹' Ioo (f (x j.succ)) (f (x j.castSucc)) ↦ i.2.val) <| by
      constructor
      · rintro ⟨j, i⟩ ⟨j', i'⟩ heq
        have hlevel : i.val = i'.val := heq
        obtain rfl : j = j' :=
          hanti.antitone.eq_of_mem_Ioo_of_mem_Icc_fin i.property (by
            rw [hlevel]
            exact Ioo_subset_Icc_self i'.property)
        exact congrArg (Sigma.mk j) (Subtype.ext heq)
      · intro i
        obtain ⟨j, hi⟩ := Fin.exists_succ_lt_lt_castSucc (g := f ∘ x)
          (fun j ↦ (hcx i j).symm) (hc i).2 (hc i).1
        exact ⟨⟨j, ⟨i, hi⟩⟩, rfl⟩).symm

@[simp]
private theorem restrictLevelRecords_apply (w : ι → M) (j : Fin k) :
    restrictLevelRecords hanti hc hcx w j = fun i : c ⁻¹' Ioo (f (x j.succ))
        (f (x j.castSucc)) ↦ w i.val := by
  funext i
  simp only [restrictLevelRecords, piSigmaConstHomeomorph_symm_apply]
  rfl

end LevelPartition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (m : M) → TangentSpace 𝓘(ℝ, E) m} {ι : Type*}
  {hX : IsAdaptedPseudoGradient f X}
  {k : ℕ} {x : Fin (k + 1) → M} {c : ι → ℝ}

namespace IsMorseSmale

variable (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  [Countable ι]
  (hanti : StrictAnti (f ∘ x))
  (hc : ∀ i, c i ∈ Ioo (f (x (Fin.last k))) (f (x 0)))
  (hreg : ∀ i (y : criticalPoints 𝓘(ℝ, E) f), c i ≠ f y)
  (hx : ∀ j, x j ∈ criticalPoints 𝓘(ℝ, E) f)

include h hf hanti hc hreg hx
/-- A record lies in the closure of the prescribed stratum if and only if each restriction to
the levels of a step is a compactified trajectory record for that step. -/
theorem mem_closure_morseBrokenTrajectoryStratum_iff {w : ι → M} :
    w ∈ closure (hX.morseBrokenTrajectoryStratum x c) ↔
      ∀ j : Fin k, (fun i : c ⁻¹' Ioo (f (x j.succ)) (f (x j.castSucc)) ↦ w i) ∈
        hX.morseBrokenTrajectorySpace c (x j.castSucc) (x j.succ) := by
  have hcx (i : ι) (j : Fin (k + 1)) : c i ≠ f (x j) := hreg i ⟨x j, hx j⟩
  let e := restrictLevelRecords hanti hc hcx
  obtain ⟨Φ, hΦ⟩ := hX.exists_homeomorph_morseBrokenTrajectoryStratum hc hcx
  have hcoords (u : hX.morseBrokenTrajectoryStratum x c) (j : Fin k) :
      e u.val j = (Φ u j).val := by
    funext i
    rw [hΦ, restrictLevelRecords_apply]
  have he : hX.morseBrokenTrajectoryStratum x c = e ⁻¹' (univ.pi fun j : Fin k ↦
      hX.morseTrajectoryRecords (x j.castSucc) (x j.succ)
        ((c ⁻¹' Ioo (f (x j.succ)) (f (x j.castSucc))).domRestrict c)) := by
    ext v
    simp only [mem_preimage, mem_univ_pi]
    constructor
    · intro hv j
      rw [hcoords ⟨v, hv⟩ j]
      exact (Φ ⟨v, hv⟩ j).property
    · intro hv
      obtain ⟨u, hu⟩ := Φ.surjective (fun j ↦ ⟨e v j, hv j⟩)
      have huv : e u.val = e v := by
        funext j
        rw [hcoords, hu]
      exact e.injective huv ▸ u.property
  rw [he, ← e.preimage_closure, mem_preimage, closure_pi_set, mem_univ_pi]
  refine forall_congr' fun j ↦ ?_
  have hne : x j.castSucc ≠ x j.succ :=
    (hanti (Fin.castSucc_lt_succ (i := j))).ne' ∘ congrArg f
  rw [h.morseBrokenTrajectorySpace_eq_closure hf hreg hne]
  simp only [e, restrictLevelRecords_apply]

/-- The closure of a stratum is homeomorphic to the ordered product of the compactified
trajectory spaces of its successive steps. The forward map reads each factor on the levels
between its two endpoints. -/
noncomputable def closureMorseBrokenTrajectoryStratumHomeomorph :
    closure (hX.morseBrokenTrajectoryStratum x c) ≃ₜ
      ((j : Fin k) → hX.morseBrokenTrajectorySpace c (x j.castSucc) (x j.succ)) := by
  have hcx (i : ι) (j : Fin (k + 1)) : c i ≠ f (x j) := hreg i ⟨x j, hx j⟩
  let e := restrictLevelRecords hanti hc hcx
  have he (v : ι → M) : v ∈ closure (hX.morseBrokenTrajectoryStratum x c) ↔
      ∀ j : Fin k, e v j ∈ hX.morseBrokenTrajectorySpace c (x j.castSucc) (x j.succ) := by
    simpa only [e, restrictLevelRecords_apply] using
      h.mem_closure_morseBrokenTrajectoryStratum_iff hf hanti hc hreg hx (w := v)
  refine
    { toFun := fun v j ↦ ⟨e v.val j, (he v.val).1 v.property j⟩
      invFun := fun u ↦ ⟨e.symm (fun j ↦ (u j).val), (he _).2 fun j ↦ ?_⟩
      left_inv := fun v ↦ Subtype.ext (e.symm_apply_apply v.val)
      right_inv := fun u ↦ funext fun j ↦ Subtype.ext (congrFun (e.apply_symm_apply _) j)
      continuous_toFun := continuous_pi fun j ↦
        ((continuous_apply j).comp (e.continuous.comp continuous_subtypeVal)).subtype_mk _
      continuous_invFun := (e.symm.continuous.comp
        (continuous_pi fun j ↦ continuous_subtypeVal.comp (continuous_apply j))).subtype_mk _ }
  rw [e.apply_symm_apply]
  exact (u j).property

/-- The homeomorphism restricts the record to the levels of the given step. -/
@[simp]
theorem closureMorseBrokenTrajectoryStratumHomeomorph_apply
    (w : closure (hX.morseBrokenTrajectoryStratum x c)) (j : Fin k)
    (i : c ⁻¹' Ioo (f (x j.succ)) (f (x j.castSucc))) :
    ((closureMorseBrokenTrajectoryStratumHomeomorph h hf hanti hc hreg hx) w j).val i = w.val i :=
  congrFun (restrictLevelRecords_apply ..) i

/-- The prescribed stratum closes inside the compactification of the trajectories joining
the first and last points of the chain, provided these endpoints are distinct. -/
theorem closure_morseBrokenTrajectoryStratum_subset (hend : x 0 ≠ x (Fin.last k)) :
    closure (hX.morseBrokenTrajectoryStratum x c) ⊆
      hX.morseBrokenTrajectoryRecords (x 0) (x (Fin.last k)) c := by
  have hregular (i : ι) (y : M) (hy : f y = c i) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y ≠ 0 := fun hzero ↦
    hreg i ⟨y, mem_criticalPoints_iff_mfderiv_eq_zero.2 hzero⟩ hy.symm
  have hclosed : IsClosed (hX.morseBrokenTrajectoryRecords (x 0) (x (Fin.last k)) c) := by
    rw [← h.closure_morseTrajectoryRecords hf hend hregular hc]
    exact isClosed_closure
  refine closure_minimal (fun w hw ↦ ?_) hclosed
  obtain ⟨z, hz, hw⟩ := hX.mem_morseBrokenTrajectoryStratum.1 hw
  exact hX.mem_morseBrokenTrajectoryRecords.2
    ⟨k, x, z, rfl, rfl, fun j ↦ mem_criticalPoints_iff_mfderiv_eq_zero.1 (hx j),
      fun j ↦ (hanti (Fin.castSucc_lt_succ (i := j))).ne' ∘ congrArg f, hz, hw⟩

/-- Concatenating the compactified step records of a chain gives a record in the full
compactification with the same first and last endpoints. -/
noncomputable def morseBrokenTrajectoryStratumConcat (hend : x 0 ≠ x (Fin.last k)) :
    C(((j : Fin k) → hX.morseBrokenTrajectorySpace c (x j.castSucc) (x j.succ)),
      hX.morseBrokenTrajectoryRecords (x 0) (x (Fin.last k)) c) :=
  (ContinuousMap.inclusion (h.closure_morseBrokenTrajectoryStratum_subset hf hanti hc hreg hx
    hend)).comp (closureMorseBrokenTrajectoryStratumHomeomorph h hf hanti hc hreg hx).symm

/-- Restriction of a concatenated record to the levels of a step recovers that factor. -/
@[simp]
theorem morseBrokenTrajectoryStratumConcat_apply (hend : x 0 ≠ x (Fin.last k))
    (v : (j : Fin k) → hX.morseBrokenTrajectorySpace c (x j.castSucc) (x j.succ))
    (j : Fin k) (i : c ⁻¹' Ioo (f (x j.succ)) (f (x j.castSucc))) :
    (morseBrokenTrajectoryStratumConcat h hf hanti hc hreg hx hend v).val i = (v j).val i := by
  let e := closureMorseBrokenTrajectoryStratumHomeomorph h hf hanti hc hreg hx
  have he := closureMorseBrokenTrajectoryStratumHomeomorph_apply h hf hanti hc hreg hx
    (e.symm v) j i
  rw [e.apply_symm_apply v] at he
  exact he.symm

/-- The range of concatenation in the full compactification is the closure of the
prescribed stratum. -/
theorem range_morseBrokenTrajectoryStratumConcat (hend : x 0 ≠ x (Fin.last k)) :
    range (morseBrokenTrajectoryStratumConcat h hf hanti hc hreg hx hend) =
      closure (Subtype.val ⁻¹' hX.morseBrokenTrajectoryStratum x c) := by
  let e := closureMorseBrokenTrajectoryStratumHomeomorph h hf hanti hc hreg hx
  have hsubset := h.closure_morseBrokenTrajectoryStratum_subset hf hanti hc hreg hx hend
  have hstratum := subset_closure.trans hsubset
  ext w
  rw [closure_subtype, Set.image_preimage_eq_inter_range, Subtype.range_coe,
    Set.inter_eq_left.mpr hstratum]
  constructor
  · rintro ⟨v, rfl⟩
    exact (e.symm v).property
  · intro hw
    let u : closure (hX.morseBrokenTrajectoryStratum x c) := ⟨w.val, hw⟩
    refine ⟨e u, Subtype.ext ?_⟩
    exact congrArg (fun a : closure (hX.morseBrokenTrajectoryStratum x c) ↦ a.val)
      (e.symm_apply_apply u)

/-- Concatenating the compactified steps embeds their product as a closed stratum. -/
theorem isClosedEmbedding_morseBrokenTrajectoryStratumConcat (hend : x 0 ≠ x (Fin.last k)) :
    IsClosedEmbedding (morseBrokenTrajectoryStratumConcat h hf hanti hc hreg hx hend) := by
  let e := closureMorseBrokenTrajectoryStratumHomeomorph h hf hanti hc hreg hx
  have hincl := IsEmbedding.inclusion
    (h.closure_morseBrokenTrajectoryStratum_subset hf hanti hc hreg hx hend)
  refine ⟨hincl.comp e.symm.isEmbedding, ?_⟩
  rw [range_morseBrokenTrajectoryStratumConcat]
  exact isClosed_closure

end IsMorseSmale

end TauCeti.IsAdaptedPseudoGradient
