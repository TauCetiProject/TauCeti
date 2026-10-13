/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import TauCeti.RepresentationTheory.Induction.Projection

/-!
# Coinvariants of induced representations

Taking coinvariants after induction along a group homomorphism is naturally isomorphic to
taking coinvariants before induction. This is the comparison of left adjoints to the
trivial-action functor: restriction of a trivial representation is trivial. Its forward map
sends `⟦⟦h ⊗ₜ a⟧⟧` to `⟦a⟧`.

The comparison identifies the image of the projection formula under coinvariants with
Mathlib's `Rep.coinvariantsTensorIndIso`. This makes the representation-level tensor identity
and the coinvariants tensor identity agree as isomorphisms.

The tensor comparison uses a common universe for `k`, `G`, and `H`, as required by
Mathlib's `Rep.coinvariantsTensorIndIso`.

## References

C. W. Curtis and I. Reiner, *Methods of Representation Theory, Vol. I*, §10.
The construction uses Mathlib's induction and coinvariants adjunctions and
`CategoryTheory.Adjunction.leftAdjointUniq`.
-/

public section

open CategoryTheory MonoidalCategory Representation TensorProduct

universe u v w t

namespace MonoidHom

variable {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Group G] [Group H]

/-- Coinvariants commute with induction, naturally in the representation being induced. -/
noncomputable def indCoinvariantsNatIso (φ : G →* H) :
    Rep.indFunctor.{max u v w t} k φ ⋙ Rep.coinvariantsFunctor k H ≅
      Rep.coinvariantsFunctor k G :=
  ((Rep.indResAdjunction.{max u v w t} k φ).comp
    (Rep.coinvariantsAdjunction k H)).leftAdjointUniq
      -- Restriction fixes the trivial actions and their underlying maps, so the right adjoints
      -- are definitionally equal.
      ((Rep.coinvariantsAdjunction k G).ofNatIsoRight (eqToIso (by rfl)))

private theorem indCoinvariantsNatIso_hom_app_mk_one (φ : G →* H)
    (A : Rep.{max u v w t} k G) (a : A) :
    ((indCoinvariantsNatIso.{u, v, w, t} φ).hom.app A).hom
        (Coinvariants.mk (Rep.ind φ A).ρ (IndV.mk φ A.ρ 1 a)) =
      Coinvariants.mk A.ρ a := by
  have key := Adjunction.unit_leftAdjointUniq_hom_app
    ((Rep.indResAdjunction.{max u v w t} k φ).comp
      (Rep.coinvariantsAdjunction k H))
    ((Rep.coinvariantsAdjunction k G).ofNatIsoRight (eqToIso (by rfl))) A
  -- The induction unit inserts the coordinate `1`; the coinvariants unit is the quotient map.
  -- Reading the abstract unit identity on vectors therefore gives the displayed generator law.
  exact congrArg (fun f => f.hom a) key

/-- On generators, the induction–coinvariants comparison forgets the group coordinate. -/
@[simp↓]
theorem indCoinvariantsNatIso_hom_app_mk (φ : G →* H)
    (A : Rep.{max u v w t} k G) (h : H) (a : A) :
    ((indCoinvariantsNatIso.{u, v, w, t} φ).hom.app A).hom
        (Coinvariants.mk (Rep.ind φ A).ρ (IndV.mk φ A.ρ h a)) =
      Coinvariants.mk A.ρ a := by
  have hh : Coinvariants.mk (Rep.ind φ A).ρ (IndV.mk φ A.ρ h a) =
      Coinvariants.mk (Rep.ind φ A).ρ (IndV.mk φ A.ρ 1 a) := by
    simpa using Coinvariants.mk_self_apply (Rep.ind φ A).ρ h⁻¹ (IndV.mk φ A.ρ 1 a)
  rw [hh]
  exact indCoinvariantsNatIso_hom_app_mk_one.{u, v, w, t} φ A a

/-- The inverse inserts the identity group coordinate before passing to coinvariants. -/
@[simp↓]
theorem indCoinvariantsNatIso_inv_app_mk (φ : G →* H)
    (A : Rep.{max u v w t} k G) (a : A) :
    ((indCoinvariantsNatIso.{u, v, w, t} φ).inv.app A).hom (Coinvariants.mk A.ρ a) =
      Coinvariants.mk (Rep.ind φ A).ρ (IndV.mk φ A.ρ 1 a) := by
  have key := congrArg ((indCoinvariantsNatIso.{u, v, w, t} φ).inv.app A).hom
    (indCoinvariantsNatIso_hom_app_mk.{u, v, w, t} φ A 1 a)
  simpa only [← ModuleCat.comp_apply, Iso.hom_inv_id_app, ModuleCat.id_apply] using key.symm

section Projection

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- The projection formula followed by Mathlib's coinvariants tensor identity is the
canonical induction–coinvariants comparison. This equality identifies the entire
isomorphisms, rather than only their values on generators. -/
theorem indCoinvariantsNatIso_app_tensor (φ : G →* H) (X : Rep k G) (Y : Rep k H) :
    (indCoinvariantsNatIso.{u, u, u, u} φ).app (X ⊗ Rep.res φ Y) =
      (Rep.coinvariantsFunctor k H).mapIso (TauCeti.indProjection φ X Y) ≪≫
        Rep.coinvariantsTensorIndIso φ X Y := by
  apply Iso.ext
  apply Rep.coinvariantsFunctor_hom_ext
  apply ModuleCat.hom_ext
  apply IndV.hom_ext
  intro h
  apply TensorProduct.ext
  ext x y
  simpa only [Iso.app_hom, Iso.trans_hom, Functor.mapIso_hom, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
    Rep.coinvariantsMk_app_hom, Rep.indFunctor_obj, Rep.of_ρ,
    Rep.tensor_V, Rep.tensor_ρ, Rep.res_obj_ρ,
    Rep.coinvariantsTensorIndIso_hom] using
    (indCoinvariantsNatIso_hom_app_mk.{u, u, u, u} φ (X ⊗ Rep.res φ Y) h
      (x ⊗ₜ[k] y)).trans (TauCeti.coinvariantsTensorIndHom_map_indProjection_mk φ X Y h x y).symm

end Projection

end MonoidHom
