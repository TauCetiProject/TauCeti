/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import TauCeti.CategoryTheory.Category.QuiverTotal
public import TauCeti.Topology.IsLocalHomeomorph

/-!
# Cutoff functions for étale groupoids

Let `C` be a quiver, such as a groupoid, whose objects and total arrows `Quiver.Total C` carry
topologies. A cutoff function (`TauCeti.Quiver.IsCutoff`) is a nonnegative function `c` on the
objects such that

* for every object `x`, the values of `c` at the targets of the arrows with source `x` sum to one,
  `∑ᶠ a ∈ Quiver.Total.left ⁻¹' {x}, c a.right = 1`;
* for every compact set `K` of objects, the arrows with source in `K` and target in the support of
  `c` form a compact set.

The second condition makes the source map proper on the support of `c` composed with the target
(`TauCeti.Quiver.IsCutoff.isProperMap_left`). When the source is a local homeomorphism it also makes
each of the sums above finite (`TauCeti.Quiver.IsCutoff.finite_preimage_left_singleton_inter`).
Every arrow is counted, so isotropy arrows acting trivially near their object, and with them the
ineffective isotropy of an orbifold presentation, are retained.

For a groupoid, dividing a nonnegative function `β` by its sums `x ↦ ∑ᶠ a, β a.right` over the
arrows with source `x` gives a cutoff function, as soon as every orbit meets the locus where `β` is
nonzero and `β` satisfies the compactness condition (`TauCeti.Quiver.isCutoff_div_finsum`). The
sums are constant along orbits, by `Quiver.Total.finsum_mem_preimage_left_singleton_eq_of_iso`.

Cutoff functions turn sums over the arrows of a proper groupoid into locally finite sums, as needed
to average data along its orbits. Smooth cutoff functions of proper étale manifold groupoids are
constructed in `TauCeti.Geometry.Manifold.Groupoid.Cutoff`. For the action groupoid of a
discrete group, `TauCeti.MulAction.IsCutoff` is the corresponding notion.

## References

* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2, for cutoff functions on proper
  groupoids.
-/

public section

open Set Topology

namespace TauCeti.Quiver

variable {C : Type*} [Quiver C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]

/-- A cutoff function for a topological quiver, such as a topological groupoid: a nonnegative
function on objects whose values at the targets of the arrows with each given source sum to one,
and such that the arrows with source in a compact set and target in its support form a compact
set. -/
structure IsCutoff (c : C → ℝ) : Prop where
  /-- A cutoff function is nonnegative. -/
  nonneg (x : C) : 0 ≤ c x
  /-- The values of a cutoff function at the targets of the arrows with source `x` sum to one. -/
  finsum_eq_one (x : C) : ∑ᶠ a ∈ Quiver.Total.left ⁻¹' {x}, c a.right = 1
  /-- The arrows with source in a compact set and target in the support of a cutoff function
  form a compact set. -/
  isCompact_preimage_inter ⦃K : Set C⦄ (hK : IsCompact K) :
    IsCompact (Quiver.Total.left ⁻¹' K ∩ Quiver.Total.right ⁻¹' tsupport c)

section Finite

variable {R : Type*} [Zero R] {f : C → R}

/-- If the source map is a local homeomorphism and the arrows with source in a compact set and
target in the support of `f` form a compact set, then only finitely many arrows with a given source
have their target in the support of `f`. -/
theorem finite_preimage_left_singleton_inter
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (hf : ∀ ⦃K : Set C⦄, IsCompact K →
      IsCompact (Quiver.Total.left ⁻¹' K ∩ Quiver.Total.right ⁻¹' tsupport f))
    (x : C) : (Quiver.Total.left ⁻¹' {x} ∩ Quiver.Total.right ⁻¹' tsupport f).Finite := by
  simpa only [inter_assoc] using hs.isLocallyInjective.finite_preimage_singleton_inter
    (by simpa only [inter_assoc] using hf isCompact_singleton)

/-- If the arrows with source in a compact set `K` and target in the support of `f` form a compact
set, then so do the arrows with source in `K` lying in the support of `f` composed with the
target. -/
theorem isCompact_preimage_left_inter_tsupport_comp
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C)) {K : Set C}
    (hf : IsCompact (Quiver.Total.left ⁻¹' K ∩ Quiver.Total.right ⁻¹' tsupport f)) :
    IsCompact (Quiver.Total.left ⁻¹' K ∩ tsupport (f ∘ Quiver.Total.right)) := by
  have hsub := tsupport_comp_subset_preimage f ht
  simpa only [inter_assoc, inter_eq_right.2 hsub] using
    hf.inter_right (isClosed_tsupport (f ∘ Quiver.Total.right))

end Finite

/-- If the source map is a local homeomorphism, `f` is nonnegative and nonzero at the target of
some arrow with source `x`, and the arrows with source in a compact set and target in the support
of `f` form a compact set, then the sum of `f` over the targets of the arrows with source `x` is
positive. -/
theorem finsum_mem_preimage_left_singleton_pos
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {f : C → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ ⦃K : Set C⦄, IsCompact K →
      IsCompact (Quiver.Total.left ⁻¹' K ∩ Quiver.Total.right ⁻¹' tsupport f))
    {x : C} (hx : ∃ a ∈ Quiver.Total.left ⁻¹' {x}, f a.right ≠ 0) :
    0 < ∑ᶠ a ∈ Quiver.Total.left ⁻¹' {x}, f a.right := by
  obtain ⟨a, ha, hfa⟩ := hx
  refine finsum_cond_pos (fun _ _ ↦ hf0 _) ⟨a, ha, (hf0 _).lt_of_ne' hfa⟩ ?_
  refine (finite_preimage_left_singleton_inter hs hf x).subset fun b ⟨hb, hbx⟩ ↦ ⟨hbx, ?_⟩
  exact subset_tsupport f hb

namespace IsCutoff

variable {c : C → ℝ}

/-- If the source map is a local homeomorphism, only finitely many arrows with a given source have
their target in the support of a cutoff function. -/
theorem finite_preimage_left_singleton_inter (hc : IsCutoff c)
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) (x : C) :
    (Quiver.Total.left ⁻¹' {x} ∩ Quiver.Total.right ⁻¹' tsupport c).Finite :=
  TauCeti.Quiver.finite_preimage_left_singleton_inter hs hc.isCompact_preimage_inter x

/-- The arrows with source in a compact set and lying in the support of a cutoff function
composed with the target form a compact set. -/
theorem isCompact_preimage_left_inter_tsupport_comp (hc : IsCutoff c)
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C)) {K : Set C} (hK : IsCompact K) :
    IsCompact (Quiver.Total.left ⁻¹' K ∩ tsupport (c ∘ Quiver.Total.right)) :=
  TauCeti.Quiver.isCompact_preimage_left_inter_tsupport_comp ht (hc.isCompact_preimage_inter hK)

/-- The source map is proper on the support of a cutoff function composed with the target map. -/
theorem isProperMap_left [T2Space C] [CompactlyCoherentSpace C] (hc : IsCutoff c)
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C)) :
    IsProperMap fun a : tsupport (c ∘ Quiver.Total.right) ↦ (a : Quiver.Total C).left := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hs.comp continuous_subtype_val, fun K hK ↦ ?_⟩
  have hpre : (fun a : tsupport (c ∘ Quiver.Total.right) ↦ (a : Quiver.Total C).left) ⁻¹' K =
      Subtype.val ⁻¹' (Quiver.Total.left ⁻¹' K ∩ Quiver.Total.right ⁻¹' tsupport c) := by
    ext ⟨a, ha⟩
    exact ⟨fun h ↦ ⟨h, tsupport_comp_subset_preimage c ht ha⟩, fun h ↦ h.1⟩
  rw [hpre]
  exact (isClosed_tsupport _).isClosedEmbedding_subtypeVal.isCompact_preimage
    (hc.isCompact_preimage_inter hK)

end IsCutoff

end TauCeti.Quiver

namespace TauCeti.Quiver

open CategoryTheory

variable {C : Type*} [CategoryTheory.Groupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)]

/-- In a groupoid whose source map is a local homeomorphism, dividing a nonnegative function `β`
by its sums over the targets of the arrows with each given source gives a cutoff function. This
needs every orbit to meet the locus where `β` is nonzero, and the arrows with source in a compact
set and target in the support of `β` to form a compact set. -/
theorem isCutoff_div_finsum (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    {β : C → ℝ} (hβ : ∀ x, 0 ≤ β x)
    (hfin : ∀ ⦃K : Set C⦄, IsCompact K →
      IsCompact (Quiver.Total.left ⁻¹' K ∩ Quiver.Total.right ⁻¹' tsupport β))
    (hpos : ∀ x, ∃ a ∈ Quiver.Total.left ⁻¹' {x}, β a.right ≠ 0) :
    IsCutoff fun x ↦ β x / ∑ᶠ a ∈ Quiver.Total.left ⁻¹' {x}, β a.right := by
  have hsum (x : C) : 0 < ∑ᶠ a ∈ Quiver.Total.left ⁻¹' {x}, β a.right :=
    finsum_mem_preimage_left_singleton_pos hs hβ hfin (hpos x)
  -- The sums are constant along each arrow.
  have hinv (a : Quiver.Total C) :
      ∑ᶠ b ∈ Quiver.Total.left ⁻¹' {a.right}, β b.right =
        ∑ᶠ b ∈ Quiver.Total.left ⁻¹' {a.left}, β b.right :=
    (Quiver.Total.finsum_mem_preimage_left_singleton_eq_of_iso β (asIso a.hom)).symm
  -- Dividing by the positive sums does not change the support.
  have hsupp : Function.support (fun x ↦ β x / ∑ᶠ a ∈ Quiver.Total.left ⁻¹' {x}, β a.right) =
      Function.support β := by
    rw [Function.support_div, inter_eq_left]
    exact fun x _ ↦ (hsum x).ne'
  refine ⟨fun x ↦ div_nonneg (hβ x) (hsum x).le, fun x ↦ ?_, fun K hK ↦ ?_⟩
  · rw [finsum_mem_congr rfl fun a (ha : a.left = x) ↦ by rw [hinv, ha, div_eq_mul_inv],
      ← finsum_mem_mul, mul_inv_cancel₀ (hsum x).ne']
  · rw [tsupport, hsupp]
    exact hfin hK

end TauCeti.Quiver
