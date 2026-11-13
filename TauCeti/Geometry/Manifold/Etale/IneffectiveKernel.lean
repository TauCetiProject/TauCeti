/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.Basic
public import TauCeti.Geometry.Manifold.GroupAction.GermKernel
public import TauCeti.Topology.CategoryTheory.ActionGroupoid.Effective

/-!
# The order of the ineffective kernel of a proper étale groupoid is locally constant

Let `C` be a Hausdorff proper étale groupoid whose source and target are `C¹` local
diffeomorphisms, with objects a manifold without boundary over `ℝ` or `ℂ`. The ineffective kernel
`TauCeti.ineffectiveKernel hs x` at an object `x` consists of the isotropy arrows inducing the
identity germ at `x`. This file proves that its order is a locally constant function of `x`
(`TauCeti.isLocallyConstant_card_ineffectiveKernel`). Since that order only depends on the
isomorphism class of `x`, it is also a locally constant function on the coarse space
(`TauCeti.isLocallyConstant_isomorphismClassesCardIneffectiveKernel`). Hence it is constant on
every connected component of the coarse space, for instance by
`IsLocallyConstant.apply_eq_of_isPreconnected`.

Near `x`, the groupoid is the action groupoid of the finite group `Aut x` acting by `C¹` maps on
an open neighbourhood `U` (`TauCeti.exists_contMDiff_isotropy_action_of_proper_source_target`),
and the ineffective kernel of `C` at a point `y` of `U` has the order of the germ kernel of this
action at `y` (`TauCeti.card_ineffectiveKernel_eq_card_germKernel`). The identity principle for
finite-order `C¹` maps makes the germ kernel locally constant on `U`
(`TauCeti.isLocallyConstant_card_germKernel`).

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Chapter 1, for the ineffective kernel of an
  orbifold.
-/

public section

open CategoryTheory Filter Topology TauCeti.MulAction
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {n : ℕ∞ω} {C : Type*} [Groupoid C] [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsTopologicalGroupoid C] [T2Space (Quiver.Total C)]

/-- **The order of the ineffective kernel is locally constant.** In a Hausdorff proper étale
groupoid whose source and target are `C¹` local diffeomorphisms, over a manifold without
boundary, the order of the ineffective kernel is a locally constant function of the object. -/
theorem isLocallyConstant_card_ineffectiveKernel
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) (hn : 1 ≤ n) :
    IsLocallyConstant fun x : C ↦ Nat.card (ineffectiveKernel hs.isLocalHomeomorph x) := by
  have : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x ↦ ?_
  obtain ⟨U, hxU, _, F, hsmooth, -, hobj, _, _, hσ, -, -⟩ :=
    exists_contMDiff_isotropy_action_of_proper_source_target hp hs ht
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp x
  have := finite_aut_of_proper_source_target hp hs.isLocalHomeomorph x
  -- On the chart `U`, the order of the ineffective kernel is the order of the germ kernel of the
  -- smooth finite isotropy action, which is locally constant by the identity principle.
  have hloc : IsLocallyConstant fun y : U ↦ Nat.card (germKernel (Aut x) y) :=
    isLocallyConstant_card_germKernel (I := I)
      (fun g ↦ (hsmooth.contMDiff_const_smul g).of_le hn) fun _ ↦ isMulTorsion_of_finite
  have hcard (y : U) : Nat.card (ineffectiveKernel hs.isLocalHomeomorph (y : C)) =
      Nat.card (germKernel (Aut x) y) :=
    card_ineffectiveKernel_eq_card_germKernel hs.isLocalHomeomorph Subtype.val_injective hobj hσ y
  rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x, hxU⟩, eventually_map]
  filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp hloc ⟨x, hxU⟩] with y hy
  rw [hcard, hy, ← hcard]

/-- **The kernel order on the coarse space.** In a Hausdorff proper étale groupoid whose source
and target are `C¹` local diffeomorphisms, over a manifold without boundary, the order of the
ineffective kernel is a locally constant function on the coarse space. So it is constant on each
connected component of the coarse space. -/
theorem isLocallyConstant_isomorphismClassesCardIneffectiveKernel
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C)) (hn : 1 ≤ n) :
    IsLocallyConstant (isomorphismClassesCardIneffectiveKernel C hs.isLocalHomeomorph) := by
  refine IsLocallyConstant.iff_isOpen_fiber.mpr fun k ↦ ?_
  have h : isomorphismClassesCardIneffectiveKernel C hs.isLocalHomeomorph ∘
      _root_.Quotient.mk (isIsomorphicSetoid C) =
        fun x : C ↦ Nat.card (ineffectiveKernel hs.isLocalHomeomorph x) :=
    funext (isomorphismClassesCardIneffectiveKernel_mk hs.isLocalHomeomorph)
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage, ← Set.preimage_comp]
  -- The quotient-map API uses `Quotient.mk'`, which is `Quotient.mk` by definition.
  change IsOpen ((isomorphismClassesCardIneffectiveKernel C hs.isLocalHomeomorph ∘
    _root_.Quotient.mk (isIsomorphicSetoid C)) ⁻¹' {k})
  rw [h]
  exact (isLocallyConstant_card_ineffectiveKernel hp hs ht hn).isOpen_fiber k

end TauCeti
