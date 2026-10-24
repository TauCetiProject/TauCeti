/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.RationalMap
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

/-!
# Morphisms into proper schemes from maps of function fields

Let `k` be a commutative ring, `X` an integral `k`-scheme all of whose local rings are valuation
rings (for instance a regular integral scheme of dimension one, a normal curve), and `Y` an
integral `k`-scheme proper over `k`. Every `k`-algebra map `ψ : k(Y) → k(X)` of function fields is
the pullback of rational functions along a unique dominant `k`-morphism `X ⟶ Y`
(`AlgebraicGeometry.Scheme.homOfFunctionFieldAlgHom`): `Spec ψ` moves the generic point of `X`
into `Y`, and this morphism `Spec k(X) ⟶ Y` extends to all of `X`
(`AlgebraicGeometry.Scheme.homOfFunctionField`).

The construction is functorial, so when `X` and `Y` both have valuation rings as local rings and
are both proper over `k`, a `k`-isomorphism of their function fields gives an isomorphism of
`k`-schemes (`AlgebraicGeometry.Scheme.isoOfFunctionFieldAlgEquiv`). For curves over a field this
says that a regular proper curve is determined by its function field: proper normal curves which
are birational are isomorphic.

## Main definitions

* `AlgebraicGeometry.Scheme.homOfFunctionFieldAlgHom`: the dominant `k`-morphism `X ⟶ Y` whose
  pullback of rational functions is a given `k`-algebra map `k(Y) → k(X)`.
* `AlgebraicGeometry.Scheme.isoOfFunctionFieldAlgEquiv`: the isomorphism `X ≅ Y` induced by a
  `k`-isomorphism `k(Y) ≃ k(X)`.

## Main results

* `AlgebraicGeometry.Scheme.functionFieldMap_homOfFunctionFieldAlgHom`: the pullback of rational
  functions along `homOfFunctionFieldAlgHom hX ψ` is `ψ`.
* `AlgebraicGeometry.Scheme.eq_homOfFunctionFieldAlgHom_iff`: a dominant `k`-morphism is
  `homOfFunctionFieldAlgHom hX ψ` exactly when its pullback of rational functions is `ψ`.
* `AlgebraicGeometry.Scheme.functionFieldAlgHom_homOfFunctionFieldAlgHom` and
  `AlgebraicGeometry.Scheme.homOfFunctionFieldAlgHom_functionFieldAlgHom`: the construction is
  inverse to the pullback of rational functions `AlgebraicGeometry.Scheme.Hom.functionFieldAlgHom`.
* `AlgebraicGeometry.Scheme.homOfFunctionFieldAlgHom_id` and
  `AlgebraicGeometry.Scheme.homOfFunctionFieldAlgHom_comp`: functoriality.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition I.6.8 and
  Corollary I.6.12.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [CommRing k] {X Y Z : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

variable [IsProper (Y ↘ Spec (.of k))] (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))

/-- **The morphism induced by a map of function fields**: for an integral `k`-scheme `X` whose
local rings are valuation rings and an integral `k`-scheme `Y` proper over `k`, the unique
dominant `k`-morphism `X ⟶ Y` whose pullback of rational functions is the `k`-algebra map
`ψ : k(Y) → k(X)` (`functionFieldMap_homOfFunctionFieldAlgHom`,
`eq_homOfFunctionFieldAlgHom_iff`). -/
noncomputable def homOfFunctionFieldAlgHom (ψ : Y.functionField →ₐ[k] X.functionField) : X ⟶ Y :=
  homOfFunctionField hX _
    (specMap_comp_fromSpecStalk_genericPoint_comp_over k (CommRingCat.ofHom ψ.toRingHom)
      ψ.commutes)

variable (ψ : Y.functionField →ₐ[k] X.functionField)

/-- On the generic point, `homOfFunctionFieldAlgHom hX ψ` is `Spec ψ`. -/
@[reassoc]
theorem fromSpecStalk_homOfFunctionFieldAlgHom :
    X.fromSpecStalk (genericPoint X) ≫ homOfFunctionFieldAlgHom hX ψ =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y) :=
  fromSpecStalk_homOfFunctionField ..

/-- `homOfFunctionFieldAlgHom hX ψ` is a morphism over `k`. -/
instance : (homOfFunctionFieldAlgHom hX ψ).IsOver (Spec (.of k)) := by
  rw [homOfFunctionFieldAlgHom]
  -- Instance search does not unify the unfolded morphism with the instance's conclusion, so the
  -- instance is applied by name.
  exact isOver_homOfFunctionField ..

/-- `homOfFunctionFieldAlgHom hX ψ` is dominant: it sends the generic point to the generic
point. -/
instance : IsDominant (homOfFunctionFieldAlgHom hX ψ) :=
  Hom.isDominant_of_SpecMap_fromSpecStalk _ _ (fromSpecStalk_homOfFunctionFieldAlgHom hX ψ).symm

/-- **The pullback of rational functions along `homOfFunctionFieldAlgHom hX ψ` is `ψ`.** -/
@[simp]
theorem functionFieldMap_homOfFunctionFieldAlgHom :
    (homOfFunctionFieldAlgHom hX ψ).functionFieldMap = CommRingCat.ofHom ψ.toRingHom :=
  ((Hom.eq_functionFieldMap_iff _ _).mpr (fromSpecStalk_homOfFunctionFieldAlgHom hX ψ).symm).symm

/-- **A dominant morphism into a proper scheme is determined by its pullback of rational
functions**: a dominant `k`-morphism `f : X ⟶ Y` is `homOfFunctionFieldAlgHom hX ψ` exactly when
its pullback of rational functions is `ψ`. -/
theorem eq_homOfFunctionFieldAlgHom_iff (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsDominant f] :
    f = homOfFunctionFieldAlgHom hX ψ ↔ ∀ a, f.functionFieldMap a = ψ a := by
  refine ⟨fun h a ↦ ?_, fun h ↦ Hom.ext_of_functionFieldMap_eq (Spec (.of k)) ?_⟩
  · subst h
    simp
  rw [functionFieldMap_homOfFunctionFieldAlgHom]
  ext a
  exact h a

/-- **The pullback of rational functions along `homOfFunctionFieldAlgHom hX ψ` is `ψ`**, as a
`k`-algebra map. -/
@[simp]
theorem functionFieldAlgHom_homOfFunctionFieldAlgHom :
    (homOfFunctionFieldAlgHom hX ψ).functionFieldAlgHom k = ψ := by
  ext a
  simp

/-- **A dominant morphism into a proper scheme is induced by its pullback of rational
functions**: a dominant `k`-morphism `f : X ⟶ Y` is `homOfFunctionFieldAlgHom` of
`f^* : k(Y) → k(X)`. -/
@[simp]
theorem homOfFunctionFieldAlgHom_functionFieldAlgHom (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsDominant f] : homOfFunctionFieldAlgHom hX (f.functionFieldAlgHom k) = f :=
  ((eq_homOfFunctionFieldAlgHom_iff hX _ f).mpr fun a ↦ by simp).symm

/-! ### Functoriality -/

/-- The identity of `k(X)` induces the identity of `X`. -/
@[simp]
theorem homOfFunctionFieldAlgHom_id [IsProper (X ↘ Spec (.of k))] :
    homOfFunctionFieldAlgHom hX (AlgHom.id k X.functionField) = 𝟙 X :=
  ((eq_homOfFunctionFieldAlgHom_iff hX _ (𝟙 X)).mpr fun a ↦ by simp).symm

/-- `k`-algebra maps `k(Z) → k(Y) → k(X)` induce the composite `X ⟶ Y ⟶ Z`. -/
@[reassoc]
theorem homOfFunctionFieldAlgHom_comp [IsProper (Z ↘ Spec (.of k))]
    (hY : ∀ y : Y, ValuationRing (Y.presheaf.stalk y))
    (ψ' : Z.functionField →ₐ[k] Y.functionField) :
    homOfFunctionFieldAlgHom hX ψ ≫ homOfFunctionFieldAlgHom hY ψ' =
      homOfFunctionFieldAlgHom hX (ψ.comp ψ') := by
  refine (eq_homOfFunctionFieldAlgHom_iff hX _ _).mpr fun a ↦ ?_
  simp

/-- **Proper schemes with valuation rings as local rings are determined by their function
fields**: for integral `k`-schemes `X` and `Y`, both proper over `k` and with valuation rings as
local rings, the isomorphism `X ≅ Y` of `k`-schemes induced by a `k`-isomorphism
`e : k(Y) ≃ k(X)` of function fields. -/
noncomputable def isoOfFunctionFieldAlgEquiv [IsProper (X ↘ Spec (.of k))]
    (hY : ∀ y : Y, ValuationRing (Y.presheaf.stalk y))
    (e : Y.functionField ≃ₐ[k] X.functionField) : X ≅ Y where
  hom := homOfFunctionFieldAlgHom hX e.toAlgHom
  inv := homOfFunctionFieldAlgHom hY e.symm.toAlgHom
  hom_inv_id := by
    rw [homOfFunctionFieldAlgHom_comp, ← homOfFunctionFieldAlgHom_id (k := k) hX]
    congr 1
    ext a
    simp
  inv_hom_id := by
    rw [homOfFunctionFieldAlgHom_comp, ← homOfFunctionFieldAlgHom_id (k := k) hY]
    congr 1
    ext a
    simp

variable [IsProper (X ↘ Spec (.of k))] (hY : ∀ y : Y, ValuationRing (Y.presheaf.stalk y))
  (e : Y.functionField ≃ₐ[k] X.functionField)

/-- The forward morphism of `isoOfFunctionFieldAlgEquiv hX hY e` is the morphism induced by
`e`. -/
@[simp]
theorem isoOfFunctionFieldAlgEquiv_hom :
    (isoOfFunctionFieldAlgEquiv hX hY e).hom = homOfFunctionFieldAlgHom hX e.toAlgHom :=
  (rfl)

/-- The inverse morphism of `isoOfFunctionFieldAlgEquiv hX hY e` is the morphism induced by
`e.symm`. -/
@[simp]
theorem isoOfFunctionFieldAlgEquiv_inv :
    (isoOfFunctionFieldAlgEquiv hX hY e).inv = homOfFunctionFieldAlgHom hY e.symm.toAlgHom :=
  (rfl)

/-- `isoOfFunctionFieldAlgEquiv hX hY e` is a morphism over `k`. -/
instance : (isoOfFunctionFieldAlgEquiv hX hY e).hom.IsOver (Spec (.of k)) := by
  rw [isoOfFunctionFieldAlgEquiv_hom]
  infer_instance

/-- The inverse of `isoOfFunctionFieldAlgEquiv hX hY e` is a morphism over `k`. -/
instance : (isoOfFunctionFieldAlgEquiv hX hY e).inv.IsOver (Spec (.of k)) := by
  rw [isoOfFunctionFieldAlgEquiv_inv]
  infer_instance

end AlgebraicGeometry.Scheme
