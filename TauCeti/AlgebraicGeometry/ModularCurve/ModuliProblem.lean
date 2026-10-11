/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.Ell

/-!
# Moduli problems on `Ell/B` and rigidity

A **moduli problem** on the category `Ell/B` of elliptic curves over `B`-schemes is a
contravariant functor `P` from `Ell/B` to types (`ModuliProblem B`). An element of `P(E/S)` is a
`P`-structure on `E/S`, such as a level structure, and since every arrow of `Ell/B` is a base change
(`EllObj.isStronglyCartesian`), the functoriality of `P` is the pullback of `P`-structures along
base change. A moduli problem `P` is **representable** when it is representable as a presheaf on
`Ell/B` (Mathlib's `Functor.IsRepresentable`): there is an elliptic curve `E_univ` over a
`B`-scheme `M(P)` with a `P`-structure `α_univ` such that every elliptic curve with a
`P`-structure is the base change of `(E_univ, α_univ)` along a unique morphism to `M(P)`.

A moduli problem is **rigid** (`ModuliProblem.IsRigid`) when an automorphism of an elliptic curve
`E/S` over `S` that fixes a `P`-structure on `E/S` is the identity. Rigidity is necessary for
representability (`ModuliProblem.isRigid_of_isRepresentable`): the universal property makes such an
automorphism a factorisation of the classifying arrow through itself over the identity of the
base, and cartesian factorisations in `Ell/B` are unique. Rigidity passes from the target to the
source of a morphism of moduli problems (`ModuliProblem.IsRigid.of_hom`), for instance from `P` to
a simultaneous problem `(P, Q)` mapping to `P`.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem B`: the moduli problems on `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.IsRigid P`: no nontrivial automorphism of an elliptic
  curve fixes a `P`-structure.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.isRigid_of_isRepresentable`: a representable moduli
  problem is rigid.
* `TauCeti.AlgebraicGeometry.ModuliProblem.IsRigid.of_hom`: a moduli problem mapping to a rigid one
  is rigid.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Chapter 4 and A.4.1.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe v u

namespace TauCeti.AlgebraicGeometry

/-- A **moduli problem** on `Ell/B`: a contravariant functor from the category `Ell/B` of elliptic
curves over `B`-schemes to types. Its value on `E/S` is the set of `P`-structures on `E/S`, and its
action on an arrow of `Ell/B` is the pullback of structures along the base change that the arrow
exhibits. -/
abbrev ModuliProblem (B : Scheme.{u}) : Type _ :=
  (EllObj B)ᵒᵖ ⥤ Type v

namespace ModuliProblem

variable {B : Scheme.{u}}

/-- A moduli problem `P` on `Ell/B` is **rigid** if an automorphism of an elliptic curve `E/S`
over `S`, that is, an arrow `σ : (S, E) ⟶ (S, E)` of `Ell/B` lying over the identity of `S`, which
fixes some `P`-structure on `E/S` is the identity. Such an arrow is automatically an automorphism
(`EllObj.isIso_iff_isIso_base`). -/
def IsRigid (P : ModuliProblem.{v} B) : Prop :=
  ∀ ⦃X : EllObj B⦄ (σ : X ⟶ X), σ.base = 𝟙 X.base →
    ∀ α : P.obj (op X), P.map σ.op α = α → σ = 𝟙 X

/-- **A representable moduli problem is rigid.** If `P` is represented by `(M, E_univ)`, an
automorphism `σ` of `E/S` over `S` fixing the structure classified by `a : (S, E) ⟶ (M, E_univ)`
satisfies `σ ≫ a = a`, and `σ` and the identity are then two factorisations of `a` through `a`
over the identity of `S`, which agree since `a` is cartesian. -/
theorem isRigid_of_isRepresentable (P : ModuliProblem.{v} B) [P.IsRepresentable] : P.IsRigid := by
  intro X σ hσ α hα
  let e := P.representableBy
  obtain ⟨a, rfl⟩ := e.homEquiv.surjective α
  have ha : σ ≫ a = a := e.homEquiv.injective (by rw [e.homEquiv_comp, hα])
  rw [EllObj.Hom.eq_lift a a (𝟙 X.base) (Category.id_comp _) σ ha hσ,
    EllObj.Hom.eq_lift a a (𝟙 X.base) (Category.id_comp _) (𝟙 X) (Category.id_comp _)
      (EllObj.id_base X)]

/-- **Rigidity pulls back along morphisms of moduli problems.** If `η : P ⟶ Q` is a morphism of
moduli problems and `Q` is rigid, then `P` is rigid: an automorphism fixing a `P`-structure `α`
fixes the `Q`-structure `η α`. -/
theorem IsRigid.of_hom {P Q : ModuliProblem.{v} B} (η : P ⟶ Q) (hQ : Q.IsRigid) : P.IsRigid :=
  fun X σ hσ α hα ↦ hQ σ hσ (η.app (op X) α) (by rw [← NatTrans.naturality_apply, hα])

end ModuliProblem

end TauCeti.AlgebraicGeometry
