/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
public import TauCeti.CategoryTheory.Preadditive.NSMul

/-!
# Recognising colimits and limits of shape `SingleObj G`

A functor `J : SingleObj G ⥤ C` is an object of `C` with an action of the monoid `G`, and its
colimit, when it exists, is the object of coinvariants of that action, and its limit the object of
invariants. This file gives two criteria for a given cocone to be that colimit, and, in the
preadditive setting, the dual criterion for a given cone to be that limit.

In types, for a group `G`, Mathlib computes the colimit as the quotient by the action
(`CategoryTheory.Limits.SingleObj.Types.colimitEquivQuotient`). Correspondingly, a cocone over
`J : SingleObj G ⥤ Type u` is a colimit exactly when its leg is surjective and its fibres are the
orbits of the action (`CategoryTheory.Limits.SingleObj.Types.nonempty_isColimit_iff`).

In a preadditive category, for a finite monoid `G`, suppose a cocone `π : J.obj * ⟶ c.pt` has a
*transfer*: a morphism `t : c.pt ⟶ J.obj *` back, with `t ≫ π = |G| • 𝟙` and
`π ≫ t = ∑_{g ∈ G} J.map g`. If multiplication by `|G|` is invertible on both objects, then `c` is
a colimit (`CategoryTheory.Limits.SingleObj.isColimitOfTransfer`): the averaged transfer
`|G|⁻¹ • t` is a section of `π` whose composite with `π` is the averaging idempotent. The
hypotheses are equations between morphisms, so every additive functor preserves them and hence
preserves this colimit (`CategoryTheory.Limits.SingleObj.isColimitMapCoconeOfTransfer`). This is
the formal reason why, for a finite covering with deck group `G` and coefficients in which `|G|`
is invertible, the homology of the base is the coinvariants of the homology of the total space.

Dually, a cone over the action whose leg `t : c.pt ⟶ J.obj *` has a morphism `p : J.obj * ⟶ c.pt`
back, with `t ≫ p = |G| • 𝟙` and `p ≫ t = ∑_{g ∈ G} J.map g`, is a limit cone when `|G|` is
invertible on both objects (`CategoryTheory.Limits.SingleObj.isLimitOfTransfer`), and every
additive functor preserves this limit (`CategoryTheory.Limits.SingleObj.isLimitMapConeOfTransfer`).
This is why the transfer identifies the homology of the base with the invariants of the homology of
the total space.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.G, Proposition 3G.1, for the averaging argument with the transfer.
-/

public section

universe u v

namespace CategoryTheory.Limits.SingleObj

namespace Types

variable {G : Type v} [Group G] {J : SingleObj G ⥤ Type u} (c : Cocone J)

/-- A cocone over `J : SingleObj G ⥤ Type u` is a colimit if and only if its leg is surjective
and identifies two elements exactly when they lie in the same orbit of the action of `G`. -/
theorem nonempty_isColimit_iff :
    Nonempty (IsColimit c) ↔ Function.Surjective (c.ι.app (SingleObj.star G)) ∧
      ∀ x y, c.ι.app (SingleObj.star G) x = c.ι.app (SingleObj.star G) y ↔
        x ∈ MulAction.orbit G y := by
  have hle : MulAction.orbitRel G (J.obj (SingleObj.star G)) ≤
      Setoid.ker (c.ι.app (SingleObj.star G)) := by
    rintro x y ⟨g, rfl⟩
    exact c.w_apply (j := SingleObj.star G) (j' := SingleObj.star G) g y
  -- Through Mathlib's identification of the colimit type with the orbit quotient, the canonical
  -- map out of the colimit type becomes the map induced by the leg on the orbit quotient.
  have hdesc : J.descColimitType (J.coconeTypesEquiv.symm c) ∘
      (colimitTypeRelEquivOrbitRelQuotient J).symm =
        Quotient.lift (c.ι.app (SingleObj.star G)) hle := by
    ext q
    induction q using Quotient.inductionOn
    rfl
  have hbij : (J.coconeTypesEquiv.symm c).IsColimit ↔
      Function.Bijective (J.descColimitType (J.coconeTypesEquiv.symm c)) :=
    ⟨fun h ↦ h.bijective, fun h ↦ ⟨h⟩⟩
  rw [Types.isColimit_iff_coconeTypesIsColimit, hbij,
    ← Equiv.bijective_comp (colimitTypeRelEquivOrbitRelQuotient J).symm, hdesc]
  refine ((Setoid.lift_injective_iff_ker_eq_of_le hle).and (Quot.surjective_lift _)).trans ?_
  rw [and_comm, Setoid.ext_iff]
  simp only [Setoid.ker_def, MulAction.orbitRel_apply]
  -- The two sides now differ only in how the codomain of the leg is written, as
  -- `(J.coconeTypesEquiv.symm c).pt` or as `((Functor.const _).obj c.pt).obj _`; both are `c.pt`.
  rfl

/-- A cocone over `J : SingleObj G ⥤ Type u` whose leg is surjective, and identifies two elements
only when they lie in the same orbit of the action of `G`, is a colimit. -/
noncomputable def isColimitOf (hsurj : Function.Surjective (c.ι.app (SingleObj.star G)))
    (hfib : ∀ x y, c.ι.app (SingleObj.star G) x = c.ι.app (SingleObj.star G) y →
      x ∈ MulAction.orbit G y) :
    IsColimit c :=
  ((nonempty_isColimit_iff c).2 ⟨hsurj, fun x y ↦ ⟨hfib x y, fun ⟨g, hg⟩ ↦
    hg ▸ c.w_apply (j := SingleObj.star G) (j' := SingleObj.star G) g y⟩⟩).some

end Types

section Preadditive

variable {C : Type*} [Category C] [Preadditive C] {G : Type*} [Monoid G] [Fintype G]
  {J : SingleObj G ⥤ C} (c : Cocone J) (t : c.pt ⟶ J.obj (SingleObj.star G))

/-- Let `G` be a finite monoid acting on an object of a preadditive category, and let `c` be a
cocone over the action whose leg `π` has a *transfer* `t`: `t ≫ π = |G| • 𝟙` and
`π ≫ t = ∑_{g ∈ G} J.map g`. If multiplication by `|G|` is invertible on the acted-on object and on
the cocone point, then `c` is a colimit cocone: the cocone point is the object of coinvariants. -/
noncomputable def isColimitOfTransfer
    (ht : t ≫ c.ι.app (SingleObj.star G) = Fintype.card G • 𝟙 c.pt)
    (ht' : c.ι.app (SingleObj.star G) ≫ t = ∑ g : G, J.map g)
    [IsIso (Fintype.card G • 𝟙 (J.obj (SingleObj.star G)))] [IsIso (Fintype.card G • 𝟙 c.pt)] :
    IsColimit c where
  desc s := t ≫ inv (Fintype.card G • 𝟙 _) ≫ s.ι.app (SingleObj.star G)
  fac s j := by
    obtain rfl : j = SingleObj.star G := rfl
    rw [← Category.assoc, ht', reassoc_of% Preadditive.comp_inv_nsmul_id, IsIso.inv_comp_eq]
    simp [Preadditive.sum_comp, Preadditive.nsmul_comp, s.w]
  uniq s m hm := by
    have key : inv (Fintype.card G • 𝟙 _) ≫ c.ι.app (SingleObj.star G) =
        c.ι.app (SingleObj.star G) ≫ inv (Fintype.card G • 𝟙 c.pt) :=
      (Preadditive.comp_inv_nsmul_id (Y := c.pt) _ _).symm
    conv_rhs => rw [← hm (SingleObj.star G), reassoc_of% key, reassoc_of% ht,
      IsIso.hom_inv_id_assoc]

/-- The colimit of `CategoryTheory.Limits.SingleObj.isColimitOfTransfer` is preserved by every
additive functor: under the same hypotheses, every additive functor sends `c` to a colimit
cocone. -/
noncomputable def isColimitMapCoconeOfTransfer {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    (ht : t ≫ c.ι.app (SingleObj.star G) = Fintype.card G • 𝟙 c.pt)
    (ht' : c.ι.app (SingleObj.star G) ≫ t = ∑ g : G, J.map g)
    [IsIso (Fintype.card G • 𝟙 (J.obj (SingleObj.star G)))] [IsIso (Fintype.card G • 𝟙 c.pt)] :
    IsColimit (F.mapCocone c) :=
  have : IsIso (Fintype.card G • 𝟙 ((J ⋙ F).obj (SingleObj.star G))) :=
    F.isIso_nsmul_id_obj _ (J.obj _)
  have : IsIso (Fintype.card G • 𝟙 (F.mapCocone c).pt) := F.isIso_nsmul_id_obj _ c.pt
  isColimitOfTransfer (F.mapCocone c) (F.map t)
    (by simp only [Functor.mapCocone_pt, Functor.mapCocone_ι_app, ← F.map_comp, ht,
      F.map_nsmul, F.map_id])
    (by simp only [Functor.mapCocone_ι_app, ← F.map_comp, ht', F.map_sum, Functor.comp_map])

end Preadditive

section PreadditiveLimit

variable {C : Type*} [Category C] [Preadditive C] {G : Type*} [Monoid G] [Fintype G]
  {J : SingleObj G ⥤ C} (c : Cone J) (p : J.obj (SingleObj.star G) ⟶ c.pt)

/-- Let `G` be a finite monoid acting on an object of a preadditive category, and let `c` be a
cone over the action whose leg `t` has a *projection* `p` back with `t ≫ p = |G| • 𝟙` and
`p ≫ t = ∑_{g ∈ G} J.map g`. If multiplication by `|G|` is invertible on the acted-on object and on
the cone point, then `c` is a limit cone: the cone point is the object of invariants. -/
noncomputable def isLimitOfTransfer
    (hp : c.π.app (SingleObj.star G) ≫ p = Fintype.card G • 𝟙 c.pt)
    (hp' : p ≫ c.π.app (SingleObj.star G) = ∑ g : G, J.map g)
    [IsIso (Fintype.card G • 𝟙 (J.obj (SingleObj.star G)))] [IsIso (Fintype.card G • 𝟙 c.pt)] :
    IsLimit c where
  lift s := s.π.app (SingleObj.star G) ≫ p ≫ inv (Fintype.card G • 𝟙 c.pt)
  fac s j := by
    obtain rfl : j = SingleObj.star G := rfl
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_inv_nsmul_id, reassoc_of% hp',
      ← Category.assoc, IsIso.comp_inv_eq]
    simp [Preadditive.comp_sum, Preadditive.comp_nsmul, s.w]
  uniq s m hm := by
    rw [← hm (SingleObj.star G), Category.assoc, reassoc_of% hp, IsIso.hom_inv_id]
    exact (Category.comp_id m).symm

/-- The limit of `CategoryTheory.Limits.SingleObj.isLimitOfTransfer` is preserved by every
additive functor: if `c` and `p` satisfy its transfer identities, then every additive functor `F`
for which multiplication by `|G|` is invertible on the images of the acted-on object and of the
cone point sends `c` to a limit cone. -/
noncomputable def isLimitMapConeOfTransfer {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    (hp : c.π.app (SingleObj.star G) ≫ p = Fintype.card G • 𝟙 c.pt)
    (hp' : p ≫ c.π.app (SingleObj.star G) = ∑ g : G, J.map g)
    [IsIso (Fintype.card G • 𝟙 ((J ⋙ F).obj (SingleObj.star G)))]
    [IsIso (Fintype.card G • 𝟙 (F.mapCone c).pt)] :
    IsLimit (F.mapCone c) :=
  isLimitOfTransfer (F.mapCone c) (F.map p)
    (by simp only [Functor.mapCone_pt, Functor.mapCone_π_app, ← F.map_comp, hp,
      F.map_nsmul, F.map_id])
    (by simp only [Functor.mapCone_π_app, ← F.map_comp, hp', F.map_sum, Functor.comp_map])

end PreadditiveLimit

end CategoryTheory.Limits.SingleObj
