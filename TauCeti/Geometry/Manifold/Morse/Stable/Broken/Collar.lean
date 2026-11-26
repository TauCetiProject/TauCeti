/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Global
public import TauCeti.Geometry.Manifold.Morse.Boundary.Gluing
public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.TrajectorySpace
import TauCeti.Geometry.Manifold.Morse.Gluing.Compactification
import TauCeti.Geometry.Manifold.Morse.Stable.Stratum
import TauCeti.Topology.Order.OrderClosed

/-!
# The collar of the boundary of the index-two trajectory spaces

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient adapted
to `f` satisfying the Morse–Smale condition, and `p`, `r` critical points with
`ind p = ind r + 2`. Record the broken trajectories from `p` to `r` on countably many levels `c i`
that avoid the critical values and are dense between `f r` and `f p`, and let `L(p, r)` be the
space of these records (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`), with its
boundary `∂L(p, r)` of records that are not unbroken
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary`).

This file proves that the boundary is collared
(`IsAdaptedPseudoGradient.IsMorseSmale.isCollared_morseBrokenTrajectorySpaceBoundary`): there is an
open embedding `∂L(p, r) × [0, 1) → L(p, r)` which is the inclusion at depth `0`. This is the
collar hypothesis of the existence theorem for representing chain systems of fundamental classes
(`TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units`) in the lowest index
difference for which that theorem asks for one.

The proof identifies `L(p, r)` with the compactified space of index-two trajectories of
`TauCeti.Geometry.Manifold.Morse.Boundary.Compactification`, which records a trajectory by its
points on two levels only. A boundary point of `L(p, r)` breaks once, at a critical point `q` with
`ind p = ind q + 1 = ind r + 2`
(`IsAdaptedPseudoGradient.IsMorseSmale.exists_of_mem_morseBrokenTrajectoryRecords_of_notMem`).
Choose levels `c j₁` and `c j₂` of the family separating every critical value strictly between
`f r` and `f p` from `f r` and `f p`. Then a record is determined by its points on these two
levels: an unbroken one by its point on one level, and a broken one by its points on its two
components (`TauCeti.IsAdaptedPseudoGradient.eq_of_apply_eq_of_apply_eq`). Reading these two
levels is therefore a continuous injection of the compact space `L(p, r)`, onto the closure of the
pairs of points of trajectories from `p` to `r` on the two levels, and so a homeomorphism
(`IsAdaptedPseudoGradient.IsMorseSmale.exists_homeomorph_closure_morseTrajectoryPairs`). It carries
the boundary of `L(p, r)` onto the broken pairs, whose collar in that closure is
`IsAdaptedPseudoGradient.IsMorseSmale.isCollared_closure_diff_morseTrajectoryPairs`: the closure is
a compact space modelled on the half-line, by the gluing of broken trajectories in a Morse box.

In higher index differences the boundary has corners, and its collar needs the gluing of
trajectories broken several times; this is not treated here.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `exists_of_mem_morseBrokenTrajectoryRecords_of_notMem`: in index difference two, a broken
  trajectory that is not unbroken breaks once, at a critical point of the intermediate index.
* `exists_homeomorph_closure_morseTrajectoryPairs`: in index difference two, reading two separating
  levels is a homeomorphism from the trajectory space onto the compactified space of trajectory
  pairs, carrying the boundary onto the broken pairs.
* `isCollared_morseBrokenTrajectorySpaceBoundary`: in index difference two, the boundary of the
  trajectory space is collared.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (the compactified spaces of trajectories of index difference two are compact
  one-manifolds whose boundary is the set of once-broken trajectories).
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, Appendix A.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

namespace IsAdaptedPseudoGradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X}

/-! ### Once-broken trajectories -/

/-- **In index difference two, a broken trajectory that is not unbroken breaks once.** Under the
Morse–Smale condition, if `ind p = ind r + 2`, a record of a broken trajectory from `p` to `r` that
is not the record of an unbroken one runs through a single intermediate critical point `q`, with
`ind p = ind q + 1 = ind r + 2` and `f r < f q < f p`: its points on the levels between `f q` and
`f p` lie on a trajectory from `p` to `q`, and those on the levels between `f r` and `f q` on a
trajectory from `q` to `r`. -/
theorem exists_of_mem_morseBrokenTrajectoryRecords_of_notMem (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) {p r : M} {c : ι → ℝ} {w : ι → M}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2)
    (hw : w ∈ hX.morseBrokenTrajectoryRecords p r c)
    (hw' : w ∉ hX.morseTrajectoryRecords p r c) :
    ∃ q ∈ criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
      f q ∈ Ioo (f r) (f p) ∧
      (∀ i, c i ∈ Ioo (f q) (f p) → w i ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) ∧
      ∀ i, c i ∈ Ioo (f r) (f q) → w i ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r := by
  obtain ⟨k, x, z, hx0, hxk, hxc, hxne, hz, hrec⟩ := hX.mem_morseBrokenTrajectoryRecords.1 hw
  have hk := h.add_manifoldMorseIndex_le_of_chain hf hx0 hxk hxne hz
  -- A chain with no step would join `p` to itself, and one with a single step is unbroken.
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain rfl : p = r := hx0.symm.trans ((congrArg x Fin.last_zero.symm).trans hxk)
    omega
  have hk1 : k ≠ 1 := by
    rintro rfl
    refine hw' (hX.mem_morseTrajectoryRecords.2 ⟨z 0, ?_, fun i ↦ ⟨(hrec i).1, ?_⟩⟩)
    · rw [← hx0, ← hxk]
      exact hz 0
    · obtain ⟨-, j, t, ht⟩ := hrec i
      obtain rfl := Subsingleton.elim j 0
      exact ⟨t, ht⟩
  -- By the index count the chain has exactly two steps, through `q = x 1`.
  obtain rfl : k = 2 := by omega
  subst hx0 hxk
  have hind₁ : manifoldMorseIndex 𝓘(ℝ, E) f (x 1) < manifoldMorseIndex 𝓘(ℝ, E) f (x 0) :=
    h.strictAnti_manifoldMorseIndex_of_chain hf hxne hz (by decide)
  have hind₂ : manifoldMorseIndex 𝓘(ℝ, E) f (x (Fin.last 2)) <
      manifoldMorseIndex 𝓘(ℝ, E) f (x 1) :=
    h.strictAnti_manifoldMorseIndex_of_chain hf hxne hz (by decide)
  have hval₁ : f (x 1) < f (x 0) := hX.strictAnti_apply_of_chain hxne hz (by decide)
  have hval₂ : f (x (Fin.last 2)) < f (x 1) := hX.strictAnti_apply_of_chain hxne hz (by decide)
  have hstrat : w ∈ hX.morseBrokenTrajectoryStratum x c :=
    hX.mem_morseBrokenTrajectoryStratum.2 ⟨z, hz, hrec⟩
  exact ⟨x 1, mem_criticalPoints.2 (mvfderiv_eq_zero_iff.2 (hxc 1)), by omega, by omega,
    ⟨hval₂, hval₁⟩,
    fun i hi ↦ hX.mem_unstableSet_inter_stableSet_of_mem_morseBrokenTrajectoryStratum hstrat
      (j := 0) hi,
    fun i hi ↦ hX.mem_unstableSet_inter_stableSet_of_mem_morseBrokenTrajectoryStratum hstrat
      (j := 1) hi⟩

/-! ### Reading the index-two trajectory space on two levels -/

variable {c : ι → ℝ} {p r : criticalPoints 𝓘(ℝ, E) f} {j₁ j₂ : c ⁻¹' Ioo (f r) (f p)}

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- Critical points whose Morse indices differ by two are distinct. -/
private theorem ne_of_manifoldMorseIndex_eq_add_two
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) :
    (p : M) ≠ r := fun hpr ↦ by
  have := congrArg (manifoldMorseIndex 𝓘(ℝ, E) f) hpr
  omega

/-- In index difference two, the trajectory space is the closure of the records of unbroken
trajectories. -/
private theorem morseBrokenTrajectorySpace_eq_closure_of_add_two [Countable ι]
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) :
    hX.morseBrokenTrajectorySpace c p r =
      closure (hX.morseTrajectoryRecords p r ((c ⁻¹' Ioo (f r) (f p)).domRestrict c)) := by
  have hpr := ne_of_manifoldMorseIndex_eq_add_two hind
  rw [h.closure_morseTrajectoryRecords hf hpr (c := (c ⁻¹' Ioo (f r) (f p)).domRestrict c)
    (fun i y hy hy' ↦ hc i ⟨y, mem_criticalPoints.2 (mvfderiv_eq_zero_iff.2 hy')⟩ hy.symm)
    fun i ↦ i.property]
  ext w
  exact ⟨fun hw ↦ (mem_morseBrokenTrajectorySpace.1 hw).2,
    fun hw ↦ mem_morseBrokenTrajectorySpace.2 ⟨hpr, hw⟩⟩

/-- The reading of a record on two levels is a pair of points of a trajectory from `p` to `r`
exactly when the record is unbroken. -/
private theorem readings_mem_morseTrajectoryPairs_iff (w : hX.morseBrokenTrajectorySpace c p r) :
    ((w : c ⁻¹' Ioo (f r) (f p) → M) j₁, (w : _ → M) j₂) ∈
        hX.morseTrajectoryPairs p r (c j₁) (c j₂) ↔
      w ∉ hX.morseBrokenTrajectorySpaceBoundary c p r := by
  rw [mem_morseBrokenTrajectorySpaceBoundary, not_not, mem_morseTrajectoryPairs]
  refine ⟨fun hw ↦ hX.mem_morseTrajectoryRecords_of_apply_mem
    (mem_morseBrokenTrajectorySpace.1 w.property).2 hw.1, fun hw ↦ ?_⟩
  obtain ⟨y, hy, hwy⟩ := hX.mem_morseTrajectoryRecords.1 hw
  obtain ⟨hw₁, t₁, ht₁⟩ := hwy j₁
  obtain ⟨hw₂, t₂, ht₂⟩ := hwy j₂
  exact ⟨ht₁ ▸ hX.flow.isInvariant_unstableSet_inter_stableSet _ _ t₁ hy, hw₁, hw₂, t₂ - t₁,
    by rw [← ht₁, ← Flow.map_add, sub_add_cancel, ht₂]⟩

/-- In index difference two, reading the records on two levels separating the critical values
between `f r` and `f p` from `f r` and `f p` is injective: an unbroken record is determined by one
of its points, and a broken one by its points on the two levels, one on each of its components. -/
private theorem injective_readings (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo (c j₂) (c j₁)) :
    Injective fun w : hX.morseBrokenTrajectorySpace c p r ↦
      ((w : c ⁻¹' Ioo (f r) (f p) → M) j₁, (w : _ → M) j₂) := by
  intro w w' hww'
  obtain ⟨e₁, e₂⟩ := Prod.mk.inj hww'
  have hwL := (mem_morseBrokenTrajectorySpace.1 w.property).2
  have hwL' := (mem_morseBrokenTrajectorySpace.1 w'.property).2
  by_cases hw : (w : c ⁻¹' Ioo (f r) (f p) → M) ∈
      hX.morseTrajectoryRecords p r ((c ⁻¹' Ioo (f r) (f p)).domRestrict c)
  · have hw₁ := (hX.mem_morseTrajectoryPairs.1
      ((readings_mem_morseTrajectoryPairs_iff (j₁ := j₁) (j₂ := j₂) w).2
        (mem_morseBrokenTrajectorySpaceBoundary.not.2 (not_not.2 hw)))).1
    exact Subtype.ext (funext fun i ↦
      hX.apply_eq_apply_of_apply_eq_of_mem hwL hwL' e₁ hw₁ i.property)
  obtain ⟨q, hq, -, -, hqv, h₁, h₂⟩ :=
    h.exists_of_mem_morseBrokenTrajectoryRecords_of_notMem hf hind hwL hw
  have hq' := hgap q hq hqv
  exact Subtype.ext (hX.eq_of_apply_eq_of_apply_eq (c := (c ⁻¹' Ioo (f r) (f p)).domRestrict c)
    (fun i ↦ hc i ⟨q, hq⟩) hwL hwL' e₁ e₂ (h₁ j₁ ⟨hq'.2, j₁.property.2⟩)
    (h₂ j₂ ⟨j₂.property.1, hq'.1⟩))

/-- Every pair of points on two levels of a trajectory from `p` to `r` is the reading of the record
of that trajectory. -/
private theorem morseTrajectoryPairs_subset_range_readings
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) :
    hX.morseTrajectoryPairs p r (c j₁) (c j₂) ⊆
      range fun w : hX.morseBrokenTrajectorySpace c p r ↦
        ((w : c ⁻¹' Ioo (f r) (f p) → M) j₁, (w : _ → M) j₂) := by
  have hpr := ne_of_manifoldMorseIndex_eq_add_two hind
  intro y hy
  obtain ⟨hy₁, hf₁, hf₂, t, ht⟩ := hX.mem_morseTrajectoryPairs.1 hy
  -- The record of the trajectory through `y.1`.
  obtain ⟨Φ, hΦ⟩ := hX.exists_homeomorph_morseTrajectoryRecords hpr
    (c := (c ⁻¹' Ioo (f r) (f p)).domRestrict c) (fun i ↦ i.property) j₁
  set w := Φ.symm ⟨y.1, hy₁, hf₁⟩
  have hw₁ : (w : c ⁻¹' Ioo (f r) (f p) → M) j₁ = y.1 := by
    rw [← hΦ, Homeomorph.apply_symm_apply]
  have hwB := hX.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords
    (mvfderiv_eq_zero_iff.1 (mem_criticalPoints.1 p.property))
    (mvfderiv_eq_zero_iff.1 (mem_criticalPoints.1 r.property)) hpr _ w.property
  refine ⟨⟨w, mem_morseBrokenTrajectorySpace.2 ⟨hpr, hwB⟩⟩, Prod.ext hw₁ ?_⟩
  -- Its point on the level `c j₂` lies on the orbit of `y.1`, as `y.2` does.
  obtain ⟨t', ht'⟩ := hX.exists_flow_eq_of_apply_mem_unstableSet_inter_stableSet hwB
    (hw₁ ▸ hy₁) j₂.property
  obtain rfl : t' = t :=
    (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpr hy₁ j₂.property.1
      j₂.property.2).unique
      (by rw [← hw₁, ht']; exact hX.value_apply_eq_of_mem_morseBrokenTrajectoryRecords hwB j₂)
      (by rw [ht, hf₂])
  exact ht'.symm.trans (by rw [hw₁]; exact ht)

/-- **The index-two trajectory space is the compactified space of trajectory pairs.** Let `X`
satisfy the Morse–Smale condition, record the broken trajectories on countably many levels `c i`
that avoid the critical values, and let `ind p = ind r + 2`. If the levels `c j₁` and `c j₂`
separate the critical values strictly between `f r` and `f p` from `f r` and `f p`, reading a
record on these two levels is a homeomorphism from the trajectory space `L(p, r)` onto the closure
of the pairs of points of the trajectories from `p` to `r` on these levels
(`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryPairs`), which carries the boundary of `L(p, r)`
onto the points of the closure that are not unbroken pairs. -/
theorem exists_homeomorph_closure_morseTrajectoryPairs [Countable ι] (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo (c j₂) (c j₁)) :
    ∃ Ψ : hX.morseBrokenTrajectorySpace c p r ≃ₜ
        closure (hX.morseTrajectoryPairs p r (c j₁) (c j₂)),
      (∀ w, (Ψ w : M × M) = ((w : c ⁻¹' Ioo (f r) (f p) → M) j₁, (w : _ → M) j₂)) ∧
      ∀ w, w ∈ hX.morseBrokenTrajectorySpaceBoundary c p r ↔
        (Ψ w : M × M) ∉ hX.morseTrajectoryPairs p r (c j₁) (c j₂) := by
  have hL := morseBrokenTrajectorySpace_eq_closure_of_add_two h hf hc hind
  have : CompactSpace (hX.morseBrokenTrajectorySpace c p r) := by
    rw [← isCompact_iff_compactSpace, hL]
    exact isClosed_closure.isCompact
  -- The reading of the levels `c j₁` and `c j₂`, on all families of points.
  set π : (c ⁻¹' Ioo (f r) (f p) → M) → M × M := fun v ↦ (v j₁, v j₂)
  have hπc : Continuous π := ((continuous_apply j₁).prodMk (continuous_apply j₂))
  -- It carries the trajectory space into the closure of the trajectory pairs.
  have hmem (w : hX.morseBrokenTrajectorySpace c p r) :
      π w ∈ closure (hX.morseTrajectoryPairs p r (c j₁) (c j₂)) := by
    have hw := (Set.ext_iff.1 hL _).1 w.property
    refine closure_mono ?_ (image_closure_subset_closure_image hπc ⟨w, hw, rfl⟩)
    rintro _ ⟨v, hv, rfl⟩
    exact (readings_mem_morseTrajectoryPairs_iff ⟨v, hL ▸ subset_closure hv⟩).2
      (mem_morseBrokenTrajectorySpaceBoundary.not.2 (not_not.2 hv))
  let Ψ₀ : hX.morseBrokenTrajectorySpace c p r →
      closure (hX.morseTrajectoryPairs p r (c j₁) (c j₂)) := fun w ↦ ⟨π w, hmem w⟩
  have hΨ₀ : IsClosedEmbedding Ψ₀ :=
    ((hπc.comp continuous_subtypeVal).subtype_mk hmem).isClosedEmbedding fun w w' hww' ↦
      injective_readings h hf hc hind hgap (congrArg Subtype.val hww')
  -- It is onto, since its range is closed and contains the trajectory pairs.
  have hsurj : Surjective Ψ₀ := by
    rintro ⟨y, hy⟩
    have hrange : closure (hX.morseTrajectoryPairs p r (c j₁) (c j₂)) ⊆ range (π ∘ Subtype.val) :=
      closure_minimal (morseTrajectoryPairs_subset_range_readings hind)
        (isCompact_range (hπc.comp continuous_subtypeVal)).isClosed
    obtain ⟨w, hw⟩ := hrange hy
    exact ⟨w, Subtype.ext hw⟩
  refine ⟨hΨ₀.isEmbedding.toHomeomorphOfSurjective hsurj, fun w ↦ rfl, fun w ↦ ?_⟩
  rw [IsEmbedding.toHomeomorphOfSurjective_apply]
  have hiff := readings_mem_morseTrajectoryPairs_iff (j₁ := j₁) (j₂ := j₂) w
  exact ⟨fun hw hP ↦ hiff.1 hP hw, fun hP ↦ not_not.1 fun hw ↦ hP (hiff.2 hw)⟩

/-! ### The collar -/

/-- **The boundary of an index-two trajectory space is collared.** Let `X` satisfy the Morse–Smale
condition, and record the broken trajectories on countably many levels `c i` that avoid the
critical values and are dense between `f r` and `f p`. If `ind p = ind r + 2`, the boundary of the
trajectory space `L(p, r)`, its once-broken trajectories, has a collar: an open embedding
`∂L(p, r) × [0, 1) → L(p, r)` which is the inclusion at depth `0`. This is the collar hypothesis
of `TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units` for the pairs of
critical points of index difference two. -/
theorem isCollared_morseBrokenTrajectorySpaceBoundary [Countable ι] (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
    (hdense : Ioo (f r) (f p) ⊆ closure (range c))
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) :
    IsCollared (Subtype.val : hX.morseBrokenTrajectorySpaceBoundary c p r →
      hX.morseBrokenTrajectorySpace c p r) := by
  rcases le_or_gt (f p) (f r) with hrp | hrp
  · -- Without a trajectory from `p` to `r`, the trajectory space is empty.
    have : IsEmpty (hX.morseBrokenTrajectorySpaceBoundary c p r) :=
      ⟨fun w ↦ (hX.value_lt_of_mem_morseBrokenTrajectorySpace w.val.property).not_ge hrp⟩
    exact isCollared_iff.2 ⟨fun x ↦ isEmptyElim x.1, IsOpenEmbedding.of_isEmpty _,
      fun x ↦ isEmptyElim x⟩
  -- Two levels of the family separating the critical values between `f r` and `f p`.
  obtain ⟨c₁, c₂, hr₂, h₂₁, h₁p, hgap⟩ := hf.exists_lt_lt_forall_mem_Ioo hrp
  obtain ⟨i₁, hi₁⟩ := exists_mem_Ioo_of_Ioo_subset_closure_range h₁p
    ((Ioo_subset_Ioo_left (hr₂.trans h₂₁).le).trans hdense)
  obtain ⟨i₂, hi₂⟩ := exists_mem_Ioo_of_Ioo_subset_closure_range hr₂
    ((Ioo_subset_Ioo_right (h₂₁.trans h₁p).le).trans hdense)
  set j₁ : c ⁻¹' Ioo (f r) (f p) := ⟨i₁, (hr₂.trans h₂₁).trans hi₁.1, hi₁.2⟩
  set j₂ : c ⁻¹' Ioo (f r) (f p) := ⟨i₂, hi₂.1, hi₂.2.trans (h₂₁.trans h₁p)⟩
  have hgap' (x) (hx : x ∈ criticalPoints 𝓘(ℝ, E) f) (hxv : f x ∈ Ioo (f r) (f p)) :
      f x ∈ Ioo (c j₂) (c j₁) :=
    ⟨hi₂.2.trans (hgap x hx hxv).1, (hgap x hx hxv).2.trans hi₁.1⟩
  -- Transport the collar of the broken pairs along the reading of these two levels.
  obtain ⟨Ψ, -, hΨB⟩ := h.exists_homeomorph_closure_morseTrajectoryPairs hf hc hind hgap'
  have hcol := h.isCollared_closure_diff_morseTrajectoryPairs hf hind hi₂.1
    (hi₂.2.trans (h₂₁.trans hi₁.1)) hi₁.2 hgap'
  convert (hcol.comp_homeomorph (Ψ.subtype hΨB)).isOpenEmbedding_comp Ψ.symm.isOpenEmbedding
    using 1
  funext w
  simp

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
