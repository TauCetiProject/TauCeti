/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.Groupoid.Effective
public import TauCeti.Topology.Covering.Degree

/-!
# The covering of ineffective arrows

When the ineffective arrows of a proper étale groupoid form a closed set, their source map
is a proper covering. Its fibre over an object is the full ineffective kernel, not a quotient
of that kernel. This identifies the ineffective-kernel order with a covering degree.

`coarseCardIneffectiveKernel` descends this order to the actual quotient by isomorphism classes.
Closedness of ineffective arrows is a separate hypothesis here: it need not hold for arbitrary
topological étale groupoids.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public noncomputable section

open CategoryTheory Set Topology

namespace TauCeti

section Quiver

variable {C : Type*} [Quiver C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)]

/-- If ineffective arrows are closed, their source map is proper: on this closed subspace,
the proper source-target map factors through the diagonal of the object space. -/
theorem isProperMap_source_ineffectiveArrows
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hclosed : IsClosed (ineffectiveArrows C)) :
    IsProperMap fun a : ineffectiveArrows C ↦ (a : Quiver.Total C).left := by
  apply isProperMap_of_comp_of_inj
    (hs.comp continuous_subtype_val)
    (continuous_id.prodMk continuous_id) ?_
    (fun _ _ h ↦ congrArg Prod.fst h)
  convert hp.comp hclosed.isClosedEmbedding_subtypeVal.isProperMap using 1
  funext a
  exact Prod.ext rfl (left_eq_right_of_mem_ineffectiveArrows a.property)

/-- The ineffective arrows of a proper étale quiver, when closed, form a finite-fibre
covering of the objects under source. The number of sheets may vary between components. -/
theorem isCoveringMap_source_ineffectiveArrows [T2Space (Quiver.Total C)]
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hclosed : IsClosed (ineffectiveArrows C)) :
    IsCoveringMap fun a : ineffectiveArrows C ↦ (a : Quiver.Total C).left := by
  have hloc := hs.comp isOpen_ineffectiveArrows.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hproper := isProperMap_source_ineffectiveArrows hs.continuous hp hclosed
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply hproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn _ hloc.isLocalHomeomorphOn
  intro x _
  exact (hproper.isCompact_preimage isCompact_singleton).finite
    (hloc.isLocallyInjective.isDiscrete_preimage_singleton x)

end Quiver

variable {C : Type*} [Groupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] [IsTopologicalGroupoid C]
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))

/-- The ineffective kernel at an object is the fibre of the source map on ineffective arrows.
Every automorphism is retained as a separate point of this fibre. -/
def ineffectiveKernelEquivFiber (x : C) :
    ineffectiveKernel hs x ≃
      (fun a : ineffectiveArrows C ↦ (a : Quiver.Total C).left) ⁻¹' {x} :=
  Equiv.ofBijective
    (fun g ↦ ⟨⟨⟨x, x, g.val.asIso.hom⟩, (mem_ineffectiveKernel hs).mp g.property⟩, rfl⟩) <| by
    constructor
    · intro g h heq
      apply Subtype.ext
      apply Aut.ext
      apply Iso.ext
      exact eq_of_heq (Quiver.Total.mk.inj
        (congrArg (fun a ↦ a.val.val) heq)).2.2
    · rintro ⟨⟨⟨a, b, f⟩, hf⟩, ha⟩
      simp only [mem_preimage, mem_singleton_iff] at ha
      subst a
      have hb := left_eq_right_of_mem_ineffectiveArrows hf
      dsimp only at hb
      subst b
      exact ⟨⟨Aut.of (asIso f), (mem_ineffectiveKernel hs).mpr hf⟩, rfl⟩

/-- The fibre equivalence sends an ineffective automorphism to its actual total arrow. -/
@[simp]
theorem ineffectiveKernelEquivFiber_apply_val (x : C) (g : ineffectiveKernel hs x) :
    (ineffectiveKernelEquivFiber hs x g).val.val = ⟨x, x, g.val.asIso.hom⟩ := (rfl)

/-- The order of the ineffective kernel on the coarse quotient. As usual, `Nat.card` is zero
for infinite groups; proper étale groupoids have finite ineffective kernels. -/
def coarseCardIneffectiveKernel : _root_.Quotient (isIsomorphicSetoid C) → ℕ :=
  _root_.Quotient.lift (fun x ↦ Nat.card (ineffectiveKernel hs x)) fun _ _ ⟨e⟩ ↦
    card_ineffectiveKernel_eq_of_iso hs e

/-- At the class of an object, the coarse kernel order is the order of its ineffective kernel. -/
@[simp]
theorem coarseCardIneffectiveKernel_mk (x : C) :
    coarseCardIneffectiveKernel hs (_root_.Quotient.mk' (s := isIsomorphicSetoid C) x) =
      Nat.card (ineffectiveKernel hs x) := (rfl)

end TauCeti
