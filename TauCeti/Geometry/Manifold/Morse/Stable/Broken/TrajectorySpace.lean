/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Stable.LevelPath
import TauCeti.Geometry.Manifold.Morse.Stable.Stratum
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
(`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`).

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`,
  `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary`: the trajectory spaces and
  their boundaries.
* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceConcat`,
  `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceComp`: concatenation of broken
  trajectories on the trajectory spaces, and the composition maps indexed by the critical points.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceComp_assoc`,
  `IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary`:
  the composition maps of the trajectory spaces are associative and land in the boundary.

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
