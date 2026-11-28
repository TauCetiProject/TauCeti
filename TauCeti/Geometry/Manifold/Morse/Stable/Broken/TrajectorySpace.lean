/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Stable.LevelPath
import TauCeti.Geometry.Manifold.Morse.Stable.Stratum
import TauCeti.Topology.Homeomorph.SetCongr
import TauCeti.Topology.Order.OrderClosed

/-!
# Spaces of broken trajectories with boundary

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X`, and record the broken trajectories from `x` to `y` by their points on the
levels of a family `c` between `f y` and `f x`
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords`). Under the Morse–Smale condition
these records form the compactified space `L(x, y)` of trajectories from `x` to `y`.

Two representing chain systems are joined by a homotopy
(`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`) when the composition maps are
associative and land in the boundary of the target space, and the maps
`H_{ind x - ind y - 1}(M x y) → H_{ind x - ind y - 1}(M x y, A x y)` are injective whenever
`ind y < ind x` (its hypothesis `hinj`). The space `L(x, x)` of records from a
critical point to itself is the single empty record, and concatenation with it is the identity of
`L(x, y)`, which does not land in the boundary. The **space of broken trajectories**
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`) is therefore `L(x, y)` for `x ≠ y`
and empty for `x = y`, as for the moduli spaces of Morse theory. Its **boundary**
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary`) is made of the broken
trajectories that are not unbroken. Concatenation at a critical point
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceConcat`, the restriction of
`morseRecordsConcat`) is associative
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceConcat_assoc`) and lands in the
boundary when some level lies between the ends of the first factor, by
`IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceConcat_mem_morseBrokenTrajectorySpaceBoundary`.
Indexed by the critical points (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceComp`),
these are the hypotheses `hι` and `hA` of
`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`. A twisting chain system on these
spaces is carried to the Barraud–Cornea cocycle
(`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`). Under the Morse–Smale condition the
Morse index drops strictly along a broken trajectory, so the trajectory space from `x` to `y` is
empty unless `y` has smaller index than `x`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectorySpace_eq_empty_of_le`).

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`,
  `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary`: the trajectory spaces and
  their boundaries.
* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceConcat`,
  `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceComp`: concatenation of broken
  trajectories on the trajectory spaces, and the composition maps indexed by the critical points.

## Main results

* `IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectorySpace_eq_morseTrajectoryRecords`,
  `IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectorySpaceBoundary_eq_empty`,
  `IsAdaptedPseudoGradient.IsMorseSmale.natCard_morseBrokenTrajectorySpace`,
  `IsAdaptedPseudoGradient.IsMorseSmale.finite_morseBrokenTrajectorySpace`: between distinct
  critical points of consecutive index, a trajectory space is made of the records of unbroken
  trajectories, has empty boundary, is finite, and, when some level of `c` lies strictly between
  the values at its ends, has as many points as there are unparametrized trajectories.
* `IsAdaptedPseudoGradient.morseBrokenTrajectorySpace_eq_morseTrajectoryRecords_of_forall_notMem`,
  `IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary_eq_empty_of_forall_notMem`,
  `IsAdaptedPseudoGradient.exists_homeomorph_morseBrokenTrajectorySpace_of_forall_notMem`: when no
  critical value lies strictly between the values at its ends, a trajectory space is made of the
  records of unbroken trajectories, has empty boundary, and is a copy of the level slice
  `W^u(x) ∩ W^s(y) ∩ {f = c}` on any of its levels `c`.
* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceComp_assoc`,
  `IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary`:
  the composition maps of the trajectory spaces are associative and land in the boundary.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectorySpace_eq_empty_of_le`: under
  the Morse–Smale condition, the trajectory space from `x` to `y` is empty when the index of `x` is
  at most that of `y`.

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
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

/-! ### The trajectory spaces with boundary -/

section Spaces

variable (hX : IsAdaptedPseudoGradient f X) (c : ι → ℝ)

/-- **The space of broken trajectories from `x` to `y`**: empty if `x = y`, and otherwise the
records of the broken trajectories from `x` to `y` on the levels of `c` strictly between `f y` and
`f x`. -/
def morseBrokenTrajectorySpace (x y : M) : Set (c ⁻¹' Ioo (f y) (f x) → M) :=
  {w | x ≠ y ∧ w ∈ hX.morseBrokenTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c)}

/-- **The boundary of the trajectory space from `x` to `y`**: its broken trajectories that are not
unbroken. -/
def morseBrokenTrajectorySpaceBoundary (x y : M) : Set (hX.morseBrokenTrajectorySpace c x y) :=
  {w | (w : c ⁻¹' Ioo (f y) (f x) → M) ∉
    hX.morseTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c)}

variable {hX c}

/-- Membership in a trajectory space. -/
@[simp]
theorem mem_morseBrokenTrajectorySpace {x y : M} {w : c ⁻¹' Ioo (f y) (f x) → M} :
    w ∈ hX.morseBrokenTrajectorySpace c x y ↔
      x ≠ y ∧ w ∈ hX.morseBrokenTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) :=
  Iff.rfl

/-- Membership in the boundary of a trajectory space. -/
@[simp]
theorem mem_morseBrokenTrajectorySpaceBoundary {x y : M} {w : hX.morseBrokenTrajectorySpace c x y} :
    w ∈ hX.morseBrokenTrajectorySpaceBoundary c x y ↔ (w : c ⁻¹' Ioo (f y) (f x) → M) ∉
      hX.morseTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) :=
  Iff.rfl

/-- A point of a trajectory space lies outside the boundary exactly when it records an unbroken
trajectory. -/
theorem notMem_morseBrokenTrajectorySpaceBoundary {x y : M}
    {w : hX.morseBrokenTrajectorySpace c x y} :
    w ∉ hX.morseBrokenTrajectorySpaceBoundary c x y ↔ (w : c ⁻¹' Ioo (f y) (f x) → M) ∈
      hX.morseTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) :=
  not_not

/-- The trajectory space from a point to itself is empty. -/
@[simp]
theorem morseBrokenTrajectorySpace_self (x : M) : hX.morseBrokenTrajectorySpace c x x = ∅ :=
  eq_empty_of_forall_notMem fun _ hw ↦ hw.1 rfl

/-- The trajectory space from `x` to `y` is contained in the records of broken trajectories from `x`
to `y`. -/
theorem morseBrokenTrajectorySpace_subset (x y : M) :
    hX.morseBrokenTrajectorySpace c x y ⊆
      hX.morseBrokenTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) :=
  fun _ hw ↦ hw.2

/-- Along a trajectory space, `f` decreases strictly from the source to the target. -/
theorem value_lt_of_mem_morseBrokenTrajectorySpace {x y : M} {w : c ⁻¹' Ioo (f y) (f x) → M}
    (hw : w ∈ hX.morseBrokenTrajectorySpace c x y) : f y < f x :=
  hX.value_lt_of_mem_morseBrokenTrajectoryRecords hw.1 hw.2

/-- **The index drops along a trajectory space.** Under the Morse–Smale condition, the trajectory
space from `x` to `y` is empty when the Morse index of `x` is at most that of `y`: a broken
trajectory from `x` to `y ≠ x` has at least one component, and each component lowers the index. -/
theorem IsMorseSmale.morseBrokenTrajectorySpace_eq_empty_of_le (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) {x y : M}
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y) :
    hX.morseBrokenTrajectorySpace c x y = ∅ := by
  refine eq_empty_of_forall_notMem fun w ⟨hne, hw⟩ ↦ ?_
  obtain ⟨k, x', z, h0, hk, -, hxne, hz, -⟩ := hX.mem_morseBrokenTrajectoryRecords.1 hw
  have hle := h.add_manifoldMorseIndex_le_of_chain hf h0 hk hxne hz
  rcases k with _ | k
  · exact hne (h0.symm.trans hk)
  · omega

/-- **Between consecutive indices a trajectory space is made of unbroken trajectories.** Under the
Morse–Smale condition, for critical points `x ≠ y` with `ind x ≤ ind y + 1` the trajectory space
from `x` to `y` is the set of records of the unbroken trajectories from `x` to `y`, since every
broken trajectory between them is unbroken
(`IsMorseSmale.morseBrokenTrajectoryRecords_eq_morseTrajectoryRecords`). -/
theorem IsMorseSmale.morseBrokenTrajectorySpace_eq_morseTrajectoryRecords (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) {x y : M} (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
    (hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0) (hxy : x ≠ y)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 1) :
    hX.morseBrokenTrajectorySpace c x y =
      hX.morseTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) := by
  ext w
  rw [mem_morseBrokenTrajectorySpace,
    h.morseBrokenTrajectoryRecords_eq_morseTrajectoryRecords hf hx hy hxy hind, and_iff_right hxy]

/-- **Between consecutive indices a trajectory space has empty boundary.** Under the Morse–Smale
condition, for critical points `x` and `y` with `ind x ≤ ind y + 1` every broken trajectory from
`x` to `y` is unbroken (`IsMorseSmale.morseBrokenTrajectorySpace_eq_morseTrajectoryRecords`). -/
theorem IsMorseSmale.morseBrokenTrajectorySpaceBoundary_eq_empty (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) {x y : M} (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
    (hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 1) :
    hX.morseBrokenTrajectorySpaceBoundary c x y = ∅ :=
  eq_empty_of_forall_notMem fun w hw ↦ hw <|
    (h.morseBrokenTrajectorySpace_eq_morseTrajectoryRecords hf hx hy w.property.1 hind).subset
      w.property

/-- **Between consecutive indices a trajectory space counts the unparametrized trajectories.**
Under the Morse–Smale condition, let `x ≠ y` be critical points with `ind x ≤ ind y + 1`, and let
some level of `c` lie strictly between `f y` and `f x`. Then the trajectory space from `x` to `y`
has as many points as there are unparametrized trajectories from `x` to `y`: its points are the
records of unbroken trajectories, and the point on one level determines the trajectory
(`TauCeti.IsAdaptedPseudoGradient.exists_homeomorph_morseTrajectoryRecords_orbitQuotient`). -/
theorem IsMorseSmale.natCard_morseBrokenTrajectorySpace (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) {x y : M} (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
    (hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0) (hxy : x ≠ y)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 1)
    (hc : ∃ i, c i ∈ Ioo (f y) (f x)) :
    Nat.card (hX.morseBrokenTrajectorySpace c x y) =
      Nat.card (Quotient (Flow.connectingOrbitSetoid hX.flow x y)) := by
  obtain ⟨i, hi⟩ := hc
  have : Nonempty (c ⁻¹' Ioo (f y) (f x)) := ⟨⟨i, hi⟩⟩
  obtain ⟨Φ⟩ := hX.exists_homeomorph_morseTrajectoryRecords_orbitQuotient hxy
    (c := (c ⁻¹' Ioo (f y) (f x)).domRestrict c) fun i ↦ i.property
  rw [h.morseBrokenTrajectorySpace_eq_morseTrajectoryRecords hf hx hy hxy hind]
  exact Nat.card_congr Φ.toEquiv

/-- **Between consecutive indices a trajectory space is finite.** Under the Morse–Smale condition,
for critical points `x` and `y` with `ind x = ind y + 1` the trajectory space from `x` to `y` is
finite: its points are records of unbroken trajectories, determined by their points on one level,
and only finitely many trajectories from `x` to `y` cross a level. -/
theorem IsMorseSmale.finite_morseBrokenTrajectorySpace (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) {x y : M} (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0)
    (hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1) :
    (hX.morseBrokenTrajectorySpace c x y).Finite := by
  have hxy : x ≠ y := fun hxy ↦ by rw [hxy] at hind; omega
  rcases isEmpty_or_nonempty (c ⁻¹' Ioo (f y) (f x)) with hι | ⟨⟨i₀⟩⟩
  · -- Without a level there is at most one record, the empty family.
    exact Set.subsingleton_of_subsingleton.finite
  · rw [h.morseBrokenTrajectorySpace_eq_morseTrajectoryRecords hf hx hy hxy hind.le]
    obtain ⟨Φ, -⟩ := hX.exists_homeomorph_morseTrajectoryRecords hxy
      (c := (c ⁻¹' Ioo (f y) (f x)).domRestrict c) (fun i ↦ i.property) i₀
    have : Finite (hX.morseTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c)) :=
      have := (h.finite_unstableSet_inter_stableSet_inter_level hf hind
        ((c ⁻¹' Ioo (f y) (f x)).domRestrict c i₀)).to_subtype
      .of_equiv _ Φ.toEquiv.symm
    exact Set.toFinite _

/-- **Without an intermediate critical value a trajectory space is made of unbroken trajectories.**
If no critical point of `f` takes a value strictly between `f y` and `f x`, the trajectory space
from `x` to `y` is the set of records of the unbroken trajectories from `x` to `y`
(`IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords_eq_morseTrajectoryRecords_of_forall_notMem`).
-/
theorem morseBrokenTrajectorySpace_eq_morseTrajectoryRecords_of_forall_notMem {x y : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0) (hxy : x ≠ y)
    (hcrit : ∀ z, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 → f z ∉ Ioo (f y) (f x)) :
    hX.morseBrokenTrajectorySpace c x y =
      hX.morseTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c) := by
  ext w
  rw [mem_morseBrokenTrajectorySpace,
    hX.morseBrokenTrajectoryRecords_eq_morseTrajectoryRecords_of_forall_notMem hx hy hxy hcrit,
    and_iff_right hxy]

/-- **Without an intermediate critical value a trajectory space has empty boundary.** If no
critical point of `f` takes a value strictly between `f y` and `f x`, every broken trajectory from
`x` to `y` is unbroken. -/
theorem morseBrokenTrajectorySpaceBoundary_eq_empty_of_forall_notMem {x y : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0)
    (hcrit : ∀ z, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 → f z ∉ Ioo (f y) (f x)) :
    hX.morseBrokenTrajectorySpaceBoundary c x y = ∅ :=
  eq_empty_of_forall_notMem fun w hw ↦ hw <|
    (morseBrokenTrajectorySpace_eq_morseTrajectoryRecords_of_forall_notMem hx hy w.property.1
      hcrit).subset w.property

/-- **Without an intermediate critical value a trajectory space is a level slice.** If no critical
point of `f` takes a value strictly between `f y` and `f x`, reading off the point on a level
`c i₀` of the family identifies the trajectory space from `x` to `y` with the level slice
`W^u(x) ∩ W^s(y) ∩ {f = c i₀}`. -/
theorem exists_homeomorph_morseBrokenTrajectorySpace_of_forall_notMem {x y : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0) (hxy : x ≠ y)
    (hcrit : ∀ z, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z = 0 → f z ∉ Ioo (f y) (f x))
    (i₀ : c ⁻¹' Ioo (f y) (f x)) :
    ∃ Φ : hX.morseBrokenTrajectorySpace c x y ≃ₜ
        ↥(hX.flow.unstableSet x ∩ hX.flow.stableSet y ∩ {z | f z = c i₀}),
      ∀ w, (Φ w : M) = (w : c ⁻¹' Ioo (f y) (f x) → M) i₀ := by
  obtain ⟨Φ, hΦ⟩ := hX.exists_homeomorph_morseTrajectoryRecords hxy
    (c := (c ⁻¹' Ioo (f y) (f x)).domRestrict c) (fun i ↦ i.property) i₀
  have hrec := hX.morseBrokenTrajectorySpace_eq_morseTrajectoryRecords_of_forall_notMem (c := c)
    hx hy hxy hcrit
  exact ⟨(Homeomorph.setCongr hrec).trans Φ, fun w ↦
    (hΦ (Homeomorph.setCongr hrec w)).trans (by rw [Homeomorph.setCongr_apply])⟩

variable {x z y : M}

/-- **Concatenation of broken trajectories at `z`** on the trajectory spaces: the restriction of
`TauCeti.IsAdaptedPseudoGradient.morseRecordsConcat`. It requires that no level of `c` is the level
`f z`, which holds when `z` is a critical point and the levels are regular values. -/
noncomputable def morseBrokenTrajectorySpaceConcat (hz : ∀ i, c i ≠ f z) :
    C(hX.morseBrokenTrajectorySpace c x z × hX.morseBrokenTrajectorySpace c z y,
      hX.morseBrokenTrajectorySpace c x y) where
  toFun w := ⟨hX.morseRecordsConcat hz (inclusion (morseBrokenTrajectorySpace_subset x z) w.1,
      inclusion (morseBrokenTrajectorySpace_subset z y) w.2),
    mem_morseBrokenTrajectorySpace.2
      ⟨fun h ↦ ((value_lt_of_mem_morseBrokenTrajectorySpace w.2.property).trans
        (value_lt_of_mem_morseBrokenTrajectorySpace w.1.property)).ne' (congrArg f h),
      Subtype.property _⟩⟩
  continuous_toFun := (continuous_subtypeVal.comp <| (hX.morseRecordsConcat hz).continuous.comp
    ((continuous_inclusion _).prodMap (continuous_inclusion _))).subtype_mk _

/-- The record underlying a concatenation is the concatenation of the records. -/
@[simp]
theorem coe_morseBrokenTrajectorySpaceConcat_apply (hz : ∀ i, c i ≠ f z)
    (w : hX.morseBrokenTrajectorySpace c x z × hX.morseBrokenTrajectorySpace c z y) :
    (hX.morseBrokenTrajectorySpaceConcat hz w : c ⁻¹' Ioo (f y) (f x) → M) =
      concatLevelRecords c hz w.1.val w.2.val :=
  hX.coe_morseRecordsConcat hz _

/-- As records of broken trajectories, a concatenation on the trajectory spaces is the
concatenation `TauCeti.IsAdaptedPseudoGradient.morseRecordsConcat` of the records. -/
@[simp]
theorem inclusion_morseBrokenTrajectorySpaceConcat (hz : ∀ i, c i ≠ f z)
    (w : hX.morseBrokenTrajectorySpace c x z × hX.morseBrokenTrajectorySpace c z y) :
    inclusion (morseBrokenTrajectorySpace_subset x y) (hX.morseBrokenTrajectorySpaceConcat hz w) =
      hX.morseRecordsConcat hz (inclusion (morseBrokenTrajectorySpace_subset x z) w.1,
        inclusion (morseBrokenTrajectorySpace_subset z y) w.2) :=
  Subtype.ext <| by simp

/-- **Concatenation of broken trajectories is associative.** -/
theorem morseBrokenTrajectorySpaceConcat_assoc {s : M} (hz : ∀ i, c i ≠ f z) (hs : ∀ i, c i ≠ f s)
    (a : hX.morseBrokenTrajectorySpace c x z) (b : hX.morseBrokenTrajectorySpace c z s)
    (d : hX.morseBrokenTrajectorySpace c s y) :
    hX.morseBrokenTrajectorySpaceConcat hs (hX.morseBrokenTrajectorySpaceConcat hz (a, b), d) =
      hX.morseBrokenTrajectorySpaceConcat hz (a, hX.morseBrokenTrajectorySpaceConcat hs (b, d)) :=
  Subtype.ext <| by
    simpa only [coe_morseBrokenTrajectorySpaceConcat_apply] using
      concatLevelRecords_assoc hz hs (value_lt_of_mem_morseBrokenTrajectorySpace b.property).le
        _ _ _

/-- **Concatenations lie in the boundary.** If some level of `c` lies strictly between `f z` and
`f x`, no concatenation of broken trajectories from `x` to `z` and from `z` to `y` is unbroken. -/
theorem morseBrokenTrajectorySpaceConcat_mem_morseBrokenTrajectorySpaceBoundary
    (hz : ∀ i, c i ≠ f z)
    (hlevel : ∃ i, c i ∈ Ioo (f z) (f x))
    (w : hX.morseBrokenTrajectorySpace c x z × hX.morseBrokenTrajectorySpace c z y) :
    hX.morseBrokenTrajectorySpaceConcat hz w ∈ hX.morseBrokenTrajectorySpaceBoundary c x y := by
  obtain ⟨_, hi₀⟩ := hlevel
  rw [mem_morseBrokenTrajectorySpaceBoundary, coe_morseBrokenTrajectorySpaceConcat_apply]
  exact hX.concatLevelRecords_notMem_morseTrajectoryRecords hz
    w.1.property.2 w.2.property.2 w.2.property.1 hi₀

end Spaces

/-! ### The composition maps of the trajectory spaces -/

section Comp

variable (hX : IsAdaptedPseudoGradient f X) {c : ι → ℝ}
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)

/-- **The composition maps of the trajectory spaces**, indexed by the critical points of `f`:
concatenation at the middle critical point. -/
noncomputable def morseBrokenTrajectorySpaceComp (x y z : criticalPoints 𝓘(ℝ, E) f) :
    C(hX.morseBrokenTrajectorySpace c x y × hX.morseBrokenTrajectorySpace c y z,
      hX.morseBrokenTrajectorySpace c x z) :=
  hX.morseBrokenTrajectorySpaceConcat fun i ↦ hc i y

/-- The record underlying a composite is the concatenation of the records. -/
@[simp]
theorem coe_morseBrokenTrajectorySpaceComp_apply (x y z : criticalPoints 𝓘(ℝ, E) f)
    (w : hX.morseBrokenTrajectorySpace c x y × hX.morseBrokenTrajectorySpace c y z) :
    (hX.morseBrokenTrajectorySpaceComp hc x y z w : c ⁻¹' Ioo (f z) (f x) → M) =
      concatLevelRecords c (fun i ↦ hc i y) w.1.val w.2.val :=
  hX.coe_morseBrokenTrajectorySpaceConcat_apply _ w

/-- As records of broken trajectories, a composite is the concatenation
`TauCeti.IsAdaptedPseudoGradient.morseRecordsConcat` of the records. -/
@[simp]
theorem inclusion_morseBrokenTrajectorySpaceComp (x y z : criticalPoints 𝓘(ℝ, E) f)
    (w : hX.morseBrokenTrajectorySpace c x y × hX.morseBrokenTrajectorySpace c y z) :
    inclusion (morseBrokenTrajectorySpace_subset _ _)
        (hX.morseBrokenTrajectorySpaceComp hc x y z w) =
      hX.morseRecordsConcat (fun i ↦ hc i y) (inclusion (morseBrokenTrajectorySpace_subset _ _) w.1,
        inclusion (morseBrokenTrajectorySpace_subset _ _) w.2) :=
  hX.inclusion_morseBrokenTrajectorySpaceConcat _ w

/-- The composition maps are associative, in the form of the hypothesis `hι` of
`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`. -/
theorem morseBrokenTrajectorySpaceComp_assoc (x w z y : criticalPoints 𝓘(ℝ, E) f)
    (a : hX.morseBrokenTrajectorySpace c x w) (b : hX.morseBrokenTrajectorySpace c w z)
    (d : hX.morseBrokenTrajectorySpace c z y) :
    hX.morseBrokenTrajectorySpaceComp hc x z y
        (hX.morseBrokenTrajectorySpaceComp hc x w z (a, b), d) =
      hX.morseBrokenTrajectorySpaceComp hc x w y
        (a, hX.morseBrokenTrajectorySpaceComp hc w z y (b, d)) :=
  hX.morseBrokenTrajectorySpaceConcat_assoc _ _ a b d

/-- The composition maps take values in the boundary, in the form of the hypothesis `hA` of
`TauCeti.TwistingChainSystem.IsRepresenting.nonempty_homotopy`. -/
theorem morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (x z y : criticalPoints 𝓘(ℝ, E) f)
    (w : hX.morseBrokenTrajectorySpace c x z × hX.morseBrokenTrajectorySpace c z y) :
    hX.morseBrokenTrajectorySpaceComp hc x z y w ∈ hX.morseBrokenTrajectorySpaceBoundary c x y :=
  hX.morseBrokenTrajectorySpaceConcat_mem_morseBrokenTrajectorySpaceBoundary _
    (exists_mem_Ioo_of_Ioo_subset_closure_range
      (value_lt_of_mem_morseBrokenTrajectorySpace w.1.property) (hdense x z)) w

end Comp

end IsAdaptedPseudoGradient

end TauCeti
