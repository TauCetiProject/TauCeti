/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Gluing.Compactification
public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.TrajectorySpace
import TauCeti.Geometry.Manifold.Morse.Stable.TrajectorySpace
import TauCeti.Topology.Order.OrderClosed

/-!
# The boundary and the interior of the spaces of broken trajectories

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X`, and record broken trajectories by their points on the levels of a family
`c : ι → ℝ` none of which is a critical value. For critical points `x ≠ y` the space
`L(x, y)` of broken trajectories from `x` to `y`
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`) has as boundary
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary`) the broken trajectories that
are not unbroken, and the composition maps
`L(x, z) × L(z, y) → L(x, y)` (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceComp`)
concatenate at a critical point `z`. This file proves the point-set facts about these spaces that
the existence of representing chain systems of fundamental chains asks of a family of compactified
moduli spaces (`TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units`).

* **The boundary is the union of the faces.** Every broken trajectory from `x` to `y` that is not
  unbroken is a concatenation at its first breaking point
  (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary_subset_iUnion_range`), and
  conversely every concatenation lies in the boundary when the levels are dense between the
  critical values. So
  `∂L(x, y) = ⋃_z L(x, z) × L(z, y)`
  (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary_eq_iUnion_range`).
* **The faces meet only along their boundaries.** A concatenation at `z` is its first factor above
  the level of `z` and its second factor below it, so concatenation and the composition maps are
  injective (`TauCeti.IsAdaptedPseudoGradient.injective_morseBrokenTrajectorySpaceConcat`,
  `TauCeti.IsAdaptedPseudoGradient.injective_morseBrokenTrajectorySpaceComp`) and carry the
  boundary of `L(x, z) × L(z, y)` off the image of its interior. For `z' ≠ z` the face of `z'`
  misses the image of the interior of `L(x, z) × L(z, y)`
  (`TauCeti.IsAdaptedPseudoGradient.disjoint_range_morseBrokenTrajectorySpaceComp_image`): on a
  suitable level its points lie on a broken trajectory ending at `z'` and on an unbroken trajectory
  ending at `z` or at `y`, which never meet.
* **The spaces are compact.** Under the Morse–Smale condition and for countably many levels,
  `L(x, y)` is the closure of the records of unbroken trajectories
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectorySpace_eq_closure`, from
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.closure_morseTrajectoryRecords`), hence closed in
  the compact space of all records
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.isClosed_morseBrokenTrajectorySpace`) and compact
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.compactSpace_morseBrokenTrajectorySpace`).
* **The boundary is closed.** A Morse function on a compact manifold has finitely many critical
  points, so the boundary is a finite union of images of compact spaces
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.isClosed_morseBrokenTrajectorySpaceBoundary`).
* **The interior is the space of unparametrized trajectories.** The space of unparametrized
  trajectories from `x` to `y`, the quotient of `W^u(x) ∩ W^s(y)` by the flow, embeds onto the
  complement of the boundary, which is open
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_isOpenEmbedding_orbitQuotient`). Under
  the Morse–Smale condition this quotient is a manifold of dimension `ind x - ind y - 1`
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_isManifold_orbitQuotient`).

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseBrokenTrajectorySpaceBoundary_eq_iUnion_range`: the boundary is the union of the images
  of the composition maps.
* `injective_morseBrokenTrajectorySpaceConcat`, `injective_morseBrokenTrajectorySpaceComp`:
  concatenation and the composition maps are injective.
* `disjoint_range_morseBrokenTrajectorySpaceComp_image`: distinct faces meet only along their
  boundaries.
* `IsMorseSmale.morseBrokenTrajectorySpace_eq_closure`: a space of broken trajectories is the
  closure of the unbroken ones.
* `IsMorseSmale.compactSpace_morseBrokenTrajectorySpace`: the spaces of broken trajectories are
  compact.
* `IsMorseSmale.isClosed_morseBrokenTrajectorySpaceBoundary`: their boundaries are closed.
* `IsMorseSmale.exists_isOpenEmbedding_orbitQuotient`: the unparametrized trajectories form an open
  subspace, the complement of the boundary.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, §2 and Appendix A.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 5.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (spaces of broken trajectories).
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

/-! ### The boundary is the union of the faces -/

section Faces

variable (hX : IsAdaptedPseudoGradient f X) {c : ι → ℝ}
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)

/-- **Splitting a broken trajectory at its first breaking point.** A record of a broken trajectory
through a chain `x 0, x 1, …, x (k + 2)` of critical points, with at least two components, is the
concatenation at `x 1` of the record of its first component, an unbroken trajectory from `x 0` to
`x 1`, and the record of the broken trajectory formed by the other components. -/
private theorem exists_concatLevelRecords_eq_of_chain {k : ℕ} {x : Fin (k + 2 + 1) → M}
    {z : Fin (k + 2) → M} {p r : M} {w : c ⁻¹' Ioo (f r) (f p) → M} (hx0 : x 0 = p)
    (hxk : x (Fin.last (k + 2)) = r) (hxc : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0)
    (hne : ∀ j : Fin (k + 2), x j.castSucc ≠ x j.succ)
    (hz : ∀ j : Fin (k + 2),
      z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ))
    (hw : ∀ i, f (w i) = c i ∧ ∃ j t, hX.flow t (z j) = w i) :
    ∃ w₁ ∈ hX.morseTrajectoryRecords p (x 1) ((c ⁻¹' Ioo (f (x 1)) (f p)).domRestrict c),
    ∃ w₂ ∈ hX.morseBrokenTrajectoryRecords (x 1) r ((c ⁻¹' Ioo (f r) (f (x 1))).domRestrict c),
      concatLevelRecords c (fun i ↦ hc i ⟨x 1, mem_criticalPoints_iff_mfderiv_eq_zero.2 (hxc 1)⟩)
        w₁ w₂ = w := by
  have hanti := hX.strictAnti_apply_of_chain hne hz
  have h₁ : f (x 1) < f p := hx0 ▸ hanti Fin.zero_lt_one
  have h₂ : f r < f (x 1) := hxk ▸ hanti Fin.one_lt_last
  refine ⟨fun i ↦ w ⟨i, h₂.trans i.property.1, i.property.2⟩,
    hX.mem_morseTrajectoryRecords_of_chain hx0 rfl hz (fun _ ↦ hw _) fun i ↦ i.property,
    fun i ↦ w ⟨i, i.property.1, i.property.2.trans h₁⟩,
    hX.mem_morseBrokenTrajectoryRecords_of_chain rfl hxk hxc hne hz (fun _ ↦ hw _)
      fun i ↦ i.property.2,
    funext fun i ↦ ?_⟩
  -- The two parts concatenate to the record, since no level is `f (x 1)`.
  · rcases (hc i ⟨x 1, mem_criticalPoints_iff_mfderiv_eq_zero.2 (hxc 1)⟩).lt_or_gt with h | h
    · exact concatLevelRecords_of_gt _ _ _ h
    · exact concatLevelRecords_of_lt _ _ _ h

/-- **The boundary consists of concatenations.** A broken trajectory from `x` to `y` that is not
unbroken is the concatenation, at its first breaking point `z`, of a trajectory from `x` to `z` and
a broken trajectory from `z` to `y`. -/
theorem morseBrokenTrajectorySpaceBoundary_subset_iUnion_range (x y : criticalPoints 𝓘(ℝ, E) f) :
    hX.morseBrokenTrajectorySpaceBoundary c x y ⊆
      ⋃ z, range (hX.morseBrokenTrajectorySpaceComp hc x z y) := by
  intro w hw
  rw [mem_morseBrokenTrajectorySpaceBoundary] at hw
  obtain ⟨hxy, hw₀⟩ := mem_morseBrokenTrajectorySpace.1 w.property
  obtain ⟨k, xs, zs, hx0, hxk, hxc, hne, hz, hrec⟩ := hX.mem_morseBrokenTrajectoryRecords.1 hw₀
  -- A broken trajectory from `x` to `y ≠ x` has at least one component, and exactly one only if it
  -- is unbroken.
  obtain _ | _ | k := k
  · exact absurd (hx0.symm.trans hxk) hxy
  · exact absurd (hX.mem_morseTrajectoryRecords_of_chain hx0 hxk hz hrec fun i ↦ i.property) hw
  obtain ⟨w₁, h₁, w₂, h₂, hw'⟩ :=
    hX.exists_concatLevelRecords_eq_of_chain hc hx0 hxk hxc hne hz hrec
  have hanti := hX.strictAnti_apply_of_chain hne hz
  have hx1 : (x : M) ≠ xs 1 := hx0 ▸ hne 0
  have hy1 : xs 1 ≠ y := by
    rw [← hxk]
    exact fun h ↦ (hanti Fin.one_lt_last).ne' (congrArg f h)
  refine mem_iUnion.2 ⟨⟨xs 1, mem_criticalPoints_iff_mfderiv_eq_zero.2 (hxc 1)⟩,
    ⟨⟨w₁, mem_morseBrokenTrajectorySpace.2 ⟨hx1,
      hX.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property) (hxc 1) hx1 _ h₁⟩⟩,
      ⟨w₂, mem_morseBrokenTrajectorySpace.2 ⟨hy1, h₂⟩⟩⟩, Subtype.ext ?_⟩
  rw [coe_morseBrokenTrajectorySpaceComp_apply]
  exact hw'

/-- **The boundary of a space of broken trajectories is the union of its faces**, the images of
the composition maps `L(x, z) × L(z, y) → L(x, y)`, when the levels are dense between the critical
values. -/
theorem morseBrokenTrajectorySpaceBoundary_eq_iUnion_range
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    hX.morseBrokenTrajectorySpaceBoundary c x y =
      ⋃ z, range (hX.morseBrokenTrajectorySpaceComp hc x z y) :=
  (hX.morseBrokenTrajectorySpaceBoundary_subset_iUnion_range hc x y).antisymm <|
    iUnion_subset fun z ↦ range_subset_iff.2 fun w ↦
      hX.morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary hc hdense x z y w

/-- **Concatenation is injective.** A concatenation at `z` is its first factor on the levels above
`f z` and its second factor on the levels below. -/
theorem injective_morseBrokenTrajectorySpaceConcat {x z y : M} (hz : ∀ i, c i ≠ f z) :
    Function.Injective (hX.morseBrokenTrajectorySpaceConcat (x := x) (y := y) hz) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  have hzy := value_lt_of_mem_morseBrokenTrajectorySpace b.property
  have hxz := value_lt_of_mem_morseBrokenTrajectorySpace a.property
  have happ (i : c ⁻¹' Ioo (f y) (f x)) :
      concatLevelRecords c hz a.val b.val i = concatLevelRecords c hz a'.val b'.val i := by
    simpa only [coe_morseBrokenTrajectorySpaceConcat_apply] using
      congrFun (congrArg Subtype.val hab) i
  refine Prod.ext (Subtype.ext (funext fun ⟨i, hi₁, hi₂⟩ ↦ ?_))
    (Subtype.ext (funext fun ⟨i, hi₁, hi₂⟩ ↦ ?_))
  · have h := happ ⟨i, hzy.trans hi₁, hi₂⟩
    rw [concatLevelRecords_of_lt (i := ⟨i, hzy.trans hi₁, hi₂⟩) _ _ _ hi₁,
      concatLevelRecords_of_lt (i := ⟨i, hzy.trans hi₁, hi₂⟩) _ _ _ hi₁] at h
    exact h
  · have h := happ ⟨i, hi₁, hi₂.trans hxz⟩
    rw [concatLevelRecords_of_gt (i := ⟨i, hi₁, hi₂.trans hxz⟩) _ _ _ hi₂,
      concatLevelRecords_of_gt (i := ⟨i, hi₁, hi₂.trans hxz⟩) _ _ _ hi₂] at h
    exact h

/-- **The composition maps are injective.** A concatenation at `z` is its first factor on the
levels above `f z` and its second factor on the levels below. So the composition map carries the
boundary `∂L(x, z) × L(z, y) ∪ L(x, z) × ∂L(z, y)` of the product off the image of its interior. -/
theorem injective_morseBrokenTrajectorySpaceComp (x z y : criticalPoints 𝓘(ℝ, E) f) :
    Function.Injective (hX.morseBrokenTrajectorySpaceComp hc x z y) := by
  -- The composition map at `z` has the records of concatenation at `z`.
  have h : ⇑(hX.morseBrokenTrajectorySpaceComp hc x z y) =
      hX.morseBrokenTrajectorySpaceConcat fun i ↦ hc i z := funext fun w ↦ Subtype.ext <| by
    rw [coe_morseBrokenTrajectorySpaceComp_apply, coe_morseBrokenTrajectorySpaceConcat_apply]
  rw [h]
  exact hX.injective_morseBrokenTrajectorySpaceConcat _

/-- **Distinct open faces are disjoint.** For critical points `z' ≠ z`, and levels dense between
the critical values, no concatenation at `z'` is a concatenation at `z` of two unbroken
trajectories: the face of `z'` misses the interior of the face of `z`. -/
theorem disjoint_range_morseBrokenTrajectorySpaceComp_image
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    {x z' z y : criticalPoints 𝓘(ℝ, E) f} (hz : z' ≠ z) :
    Disjoint (range (hX.morseBrokenTrajectorySpaceComp hc x z' y))
      (hX.morseBrokenTrajectorySpaceComp hc x z y ''
        ((hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ ×ˢ
          (hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ)) := by
  refine disjoint_left.2 ?_
  rintro w ⟨⟨a, b⟩, rfl⟩ ⟨⟨a₀, b₀⟩, ⟨ha₀, hb₀⟩, hw⟩
  rw [mem_compl_iff, mem_morseBrokenTrajectorySpaceBoundary, not_not] at ha₀ hb₀
  have hxz' := value_lt_of_mem_morseBrokenTrajectorySpace a.property
  have hz'y := value_lt_of_mem_morseBrokenTrajectorySpace b.property
  have hxz := value_lt_of_mem_morseBrokenTrajectorySpace a₀.property
  have ha := (mem_morseBrokenTrajectorySpace.1 a.property).2
  -- On a level `c i` above `f z'` the record is the point of `a`, a broken trajectory to `z'`.
  have hw' (i : ι) (hi : c i ∈ Ioo (f y) (f x)) (hi' : f z' < c i) :
      (hX.morseBrokenTrajectorySpaceComp hc x z y (a₀, b₀) : c ⁻¹' Ioo (f y) (f x) → M) ⟨i, hi⟩ =
        (a : c ⁻¹' Ioo (f z') (f x) → M) ⟨i, hi', hi.2⟩ := by
    rw [hw, coe_morseBrokenTrajectorySpaceComp_apply, concatLevelRecords_of_lt _ _ _ hi']
  rcases le_or_gt (f z) (f z') with hle | hlt
  · -- If `f z ≤ f z'`, a level between `f z'` and `f x` meets `a` and the unbroken `a₀` at the same
    -- point.
    obtain ⟨i, hi⟩ := exists_mem_Ioo_of_Ioo_subset_closure_range hxz' (hdense x z')
    have h₀ := hw' i ⟨hz'y.trans hi.1, hi.2⟩ hi.1
    rw [coe_morseBrokenTrajectorySpaceComp_apply,
      concatLevelRecords_of_lt _ _ _ (hle.trans_lt hi.1)] at h₀
    exact hX.apply_ne_of_mem_morseBrokenTrajectoryRecords_of_mem_morseTrajectoryRecords_of_le ha
      ha₀ hle (Subtype.coe_injective.ne hz) _ _ h₀.symm
  · -- If `f z' < f z`, a level between `f z'` and `f z` meets `a` and the unbroken `b₀` at the same
    -- point.
    obtain ⟨i, hi⟩ := exists_mem_Ioo_of_Ioo_subset_closure_range hlt (hdense z z')
    have h₀ := hw' i ⟨hz'y.trans hi.1, hi.2.trans hxz⟩ hi.1
    rw [coe_morseBrokenTrajectorySpaceComp_apply, concatLevelRecords_of_gt _ _ _ hi.2] at h₀
    exact hX.apply_ne_of_mem_morseBrokenTrajectoryRecords_of_mem_morseTrajectoryRecords ha hb₀
      hz'y _ _ h₀.symm

end Faces

/-! ### Compactness, the closed boundary and the open interior -/

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  {c : ι → ℝ} (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
include h hf hc

/-- **A space of broken trajectories is the closure of the unbroken ones.** For distinct points
`x` and `y`, and countably many levels none of which is a critical value, `L(x, y)` is the closure
of the records of the trajectories from `x` to `y`. -/
theorem morseBrokenTrajectorySpace_eq_closure [Countable ι] {x y : M} (hxy : x ≠ y) :
    hX.morseBrokenTrajectorySpace c x y =
      closure (hX.morseTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c)) := by
  have hreg : ∀ (i : c ⁻¹' Ioo (f y) (f x)) z,
      f z = (c ⁻¹' Ioo (f y) (f x)).domRestrict c i → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z ≠ 0 :=
    fun i z hz h0 ↦ hc i ⟨z, mem_criticalPoints_iff_mfderiv_eq_zero.2 h0⟩ hz.symm
  ext w
  rw [mem_morseBrokenTrajectorySpace, h.closure_morseTrajectoryRecords hf hxy hreg fun i ↦
    i.property, and_iff_right hxy]

/-- **The spaces of broken trajectories are closed** in the space of all records on their levels,
for countably many levels none of which is a critical value. -/
theorem isClosed_morseBrokenTrajectorySpace [Countable ι] (x y : M) :
    IsClosed (hX.morseBrokenTrajectorySpace c x y) := by
  rcases eq_or_ne x y with rfl | hxy
  · rw [morseBrokenTrajectorySpace_self]
    exact isClosed_empty
  rw [h.morseBrokenTrajectorySpace_eq_closure hf hc hxy]
  exact isClosed_closure

/-- **The spaces of broken trajectories are compact**, for countably many levels none of which is a
critical value. -/
theorem isCompact_morseBrokenTrajectorySpace [Countable ι] (x y : M) :
    IsCompact (hX.morseBrokenTrajectorySpace c x y) :=
  (h.isClosed_morseBrokenTrajectorySpace hf hc x y).isCompact

/-- **The spaces of broken trajectories are compact spaces**, for countably many levels none of
which is a critical value. -/
theorem compactSpace_morseBrokenTrajectorySpace [Countable ι] (x y : M) :
    CompactSpace (hX.morseBrokenTrajectorySpace c x y) :=
  isCompact_iff_compactSpace.1 (h.isCompact_morseBrokenTrajectorySpace hf hc x y)

variable (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
include hdense

/-- **The boundary of a space of broken trajectories is closed**, for countably many levels, dense
between the critical values, none of which is a critical value. It is the union of the images of
the composition maps, finitely many since a Morse function on a compact manifold has finitely many
critical points, each the image of a compact space. -/
theorem isClosed_morseBrokenTrajectorySpaceBoundary [Countable ι]
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    IsClosed (hX.morseBrokenTrajectorySpaceBoundary c x y) := by
  have : Finite (criticalPoints 𝓘(ℝ, E) f) := hf.finite_criticalPoints.to_subtype
  rw [hX.morseBrokenTrajectorySpaceBoundary_eq_iUnion_range hc hdense x y]
  refine isClosed_iUnion_of_finite fun z ↦ ?_
  have := h.compactSpace_morseBrokenTrajectorySpace hf hc x z
  have := h.compactSpace_morseBrokenTrajectorySpace hf hc z y
  exact (isCompact_range (hX.morseBrokenTrajectorySpaceComp hc x z y).continuous).isClosed

/-- **The unparametrized trajectories form the interior of the space of broken trajectories.** For
distinct critical points `x` and `y`, and countably many levels, dense between the critical values,
none of which is a critical value, the space of unparametrized trajectories from `x` to `y`, the
quotient of `W^u(x) ∩ W^s(y)` by the orbits of the flow, embeds as an open subspace of `L(x, y)`
onto the complement of the boundary. -/
theorem exists_isOpenEmbedding_orbitQuotient [Countable ι] {x y : criticalPoints 𝓘(ℝ, E) f}
    (hxy : x ≠ y) :
    ∃ j : Quotient (Flow.connectingOrbitSetoid hX.flow x y) →
        hX.morseBrokenTrajectorySpace c x y,
      IsOpenEmbedding j ∧ range j = (hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ := by
  have hxy' : (x : M) ≠ y := Subtype.coe_injective.ne hxy
  rcases (hX.flow.unstableSet (x : M) ∩ hX.flow.stableSet (y : M)).eq_empty_or_nonempty
    with hC | ⟨u, hu⟩
  · -- Without trajectories from `x` to `y`, the quotient is empty and every broken trajectory lies
    -- in the boundary.
    have : IsEmpty (Quotient (Flow.connectingOrbitSetoid hX.flow x y)) :=
      ⟨fun q ↦ Quotient.inductionOn q fun v ↦ (hC ▸ v.property : (v : M) ∈ (∅ : Set M))⟩
    refine ⟨isEmptyElim, .of_isEmpty _, ?_⟩
    rw [range_eq_empty, eq_comm, compl_empty_iff, eq_univ_iff_forall]
    intro w
    rw [mem_morseBrokenTrajectorySpaceBoundary, mem_morseTrajectoryRecords]
    rintro ⟨v, hv, -⟩
    exact (hC ▸ hv : v ∈ (∅ : Set M))
  -- Some level lies between `f y` and `f x`, so the records of unbroken trajectories are the
  -- unparametrized trajectories.
  have hlt := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hxy' hu
  obtain ⟨i, hi⟩ := exists_mem_Ioo_of_Ioo_subset_closure_range (hlt.1.trans hlt.2) (hdense x y)
  have : Nonempty (c ⁻¹' Ioo (f y) (f x)) := ⟨⟨i, hi⟩⟩
  obtain ⟨Φ⟩ := hX.exists_homeomorph_morseTrajectoryRecords_orbitQuotient hxy'
    (c := (c ⁻¹' Ioo (f y) (f x)).domRestrict c) fun i ↦ i.property
  have hx := mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property
  have hy := mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property
  let j : Quotient (Flow.connectingOrbitSetoid hX.flow x y) →
      hX.morseBrokenTrajectorySpace c x y := fun q ↦
    ⟨Φ.symm q, mem_morseBrokenTrajectorySpace.2 ⟨hxy',
      hX.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords hx hy hxy' _
        (Φ.symm q).property⟩⟩
  have hrange : range j = (hX.morseBrokenTrajectorySpaceBoundary c x y)ᶜ := by
    ext w
    rw [mem_compl_iff, mem_morseBrokenTrajectorySpaceBoundary, not_not]
    refine ⟨?_, fun hw ↦ ⟨Φ ⟨w, hw⟩, Subtype.ext ?_⟩⟩
    · rintro ⟨q, rfl⟩
      exact (Φ.symm q).property
    · simp only [j, Homeomorph.symm_apply_apply]
  -- Read in the space of all records, `j` is the inverse of `Φ` followed by the inclusion of the
  -- records of unbroken trajectories: `j q` is `Φ.symm q` with its membership in `L(x, y)`.
  have hj : Subtype.val ∘ j = Subtype.val ∘ Φ.symm := rfl
  have hemb : IsEmbedding j := by
    rw [← IsEmbedding.of_comp_iff IsEmbedding.subtypeVal, hj]
    exact IsEmbedding.subtypeVal.comp Φ.symm.isEmbedding
  refine ⟨j, ⟨hemb, ?_⟩, hrange⟩
  rw [hrange, isOpen_compl_iff]
  exact h.isClosed_morseBrokenTrajectorySpaceBoundary hf hc hdense x y

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
