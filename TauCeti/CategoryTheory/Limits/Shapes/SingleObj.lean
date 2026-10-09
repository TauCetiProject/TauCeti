/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Recognising colimits of shape `SingleObj G`

A functor `J : SingleObj G ⥤ C` is an object of `C` with an action of the group `G`, and its
colimit, when it exists, is the object of coinvariants of that action. This file gives two
criteria for a given cocone to be that colimit.

In types, Mathlib computes the colimit as the quotient by the action
(`CategoryTheory.Limits.SingleObj.Types.colimitEquivQuotient`). Correspondingly, a cocone over
`J : SingleObj G ⥤ Type u` is a colimit exactly when its leg is surjective and its fibres are the
orbits of the action (`CategoryTheory.Limits.SingleObj.Types.nonempty_isColimit_iff`).

In a preadditive category, for a finite group `G`, suppose a cocone `π : J.obj * ⟶ c.pt` has a
*transfer*: a morphism `t : c.pt ⟶ J.obj *` back, with `t ≫ π = |G| • 𝟙` and
`π ≫ t = ∑_{g ∈ G} J.map g`. If multiplication by `|G|` is invertible on both objects, then `c` is
a colimit (`CategoryTheory.Limits.SingleObj.isColimitOfTransfer`): the averaged transfer
`|G|⁻¹ • t` is a section of `π` whose composite with `π` is the averaging idempotent. The
hypotheses are equations between morphisms, so every additive functor preserves them and hence
preserves this colimit (`CategoryTheory.Limits.SingleObj.isColimitMapCoconeOfTransfer`). This is
the formal reason why, for a finite covering with deck group `G` and coefficients in which `|G|`
is invertible, the homology of the base is the coinvariants of the homology of the total space.

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
  let π := c.ι.app (SingleObj.star G)
  have hle : MulAction.orbitRel G (J.obj (SingleObj.star G)) ≤ Setoid.ker π := by
    rintro x y ⟨g, rfl⟩
    exact c.w_apply (j := SingleObj.star G) (j' := SingleObj.star G) g y
  -- Through Mathlib's identification of the colimit type with the orbit quotient, the canonical
  -- map out of the colimit type becomes the map induced by `π` on the orbit quotient.
  have hdesc : J.descColimitType (J.coconeTypesEquiv.symm c) ∘
      (colimitTypeRelEquivOrbitRelQuotient J).symm = Quotient.lift π hle := by
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
  exact Iff.rfl

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

variable {C : Type*} [Category C] [Preadditive C] {G : Type*} [Group G] [Fintype G]
  {J : SingleObj G ⥤ C} (c : Cocone J) (t : c.pt ⟶ J.obj (SingleObj.star G))

omit [Fintype G] in
/-- The inverse of multiplication by a natural number commutes with every morphism. -/
private lemma comp_inv_nsmul_id {X Y : C} (f : X ⟶ Y) (d : ℕ) [IsIso (d • 𝟙 X)]
    [IsIso (d • 𝟙 Y)] :
    f ≫ inv (d • 𝟙 Y) = inv (d • 𝟙 X) ≫ f := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq, Preadditive.nsmul_comp,
    Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

/-- Let `G` be a finite group acting on an object of a preadditive category, and let `c` be a
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
    rw [← Category.assoc, ht', reassoc_of% comp_inv_nsmul_id, IsIso.inv_comp_eq,
      Preadditive.sum_comp, Preadditive.nsmul_comp, Category.id_comp]
    simp only [s.w, Finset.sum_const, Finset.card_univ]
  uniq s m hm := by
    have key : inv (Fintype.card G • 𝟙 _) ≫ c.ι.app (SingleObj.star G) =
        c.ι.app (SingleObj.star G) ≫ inv (Fintype.card G • 𝟙 c.pt) :=
      (comp_inv_nsmul_id (Y := c.pt) _ _).symm
    conv_rhs => rw [← hm (SingleObj.star G), reassoc_of% key, reassoc_of% ht,
      IsIso.hom_inv_id_assoc]

/-- The colimit of `CategoryTheory.Limits.SingleObj.isColimitOfTransfer` is absolute: under the
same hypotheses, every additive functor sends `c` to a colimit cocone. -/
noncomputable def isColimitMapCoconeOfTransfer {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    (ht : t ≫ c.ι.app (SingleObj.star G) = Fintype.card G • 𝟙 c.pt)
    (ht' : c.ι.app (SingleObj.star G) ≫ t = ∑ g : G, J.map g)
    [IsIso (Fintype.card G • 𝟙 (J.obj (SingleObj.star G)))] [IsIso (Fintype.card G • 𝟙 c.pt)] :
    IsColimit (F.mapCocone c) :=
  have hF (X : C) [IsIso (Fintype.card G • 𝟙 X)] : IsIso (Fintype.card G • 𝟙 (F.obj X)) := by
    rw [← F.map_id, ← F.map_nsmul]
    infer_instance
  have : IsIso (Fintype.card G • 𝟙 ((J ⋙ F).obj (SingleObj.star G))) := hF (J.obj _)
  have : IsIso (Fintype.card G • 𝟙 (F.mapCocone c).pt) := hF c.pt
  isColimitOfTransfer (F.mapCocone c) (F.map t)
    (by simp only [Functor.mapCocone_pt, Functor.mapCocone_ι_app, ← F.map_comp, ht,
      F.map_nsmul, F.map_id])
    (by simp only [Functor.mapCocone_ι_app, ← F.map_comp, ht', F.map_sum, Functor.comp_map])

end Preadditive

end CategoryTheory.Limits.SingleObj
