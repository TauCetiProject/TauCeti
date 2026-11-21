/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.Rep.DirectSum.Basic

/-!
# Morphisms into finite direct sums in `FDRep`

Combining `FDRep.forget₂HomLinearEquiv`, `Rep.homLinearEquiv`, and
`Representation.IntertwiningMap.directSumLinearEquiv`, an unbundled equivalence
`e : Representation.Equiv Y.ρ (Representation.directSum fun i ↦ (Z i).ρ)` identifies the space of
morphisms `X ⟶ Y` in `FDRep R G` `R`-linearly with the product `∀ i, X ⟶ Z i`
(`FDRep.homLinearEquivOfEquivDirectSum`). Over a field, taking `Module.finrank` decomposes the
dimension of `X ⟶ Y` into the finite sum `∑ i, Module.finrank k (X ⟶ Z i)`
(`FDRep.finrank_hom_of_equiv_directSum`) without bundling the direct sum in `FDRep` or restricting
the universe of the index type `ι`.

## Main definitions

* `FDRep.homLinearEquivOfEquivDirectSum`: `R`-linear equivalence `(X ⟶ Y) ≃ₗ[R] ∀ i, X ⟶ Z i`
  induced by `e : Representation.Equiv Y.ρ (Representation.directSum fun i ↦ (Z i).ρ)` for finite
  `ι`.

## Main results

* `FDRep.homLinearEquivOfEquivDirectSum_apply_hom_hom_hom`,
  `FDRep.e_homLinearEquivOfEquivDirectSum_symm_apply`: componentwise evaluation of
  `FDRep.homLinearEquivOfEquivDirectSum` and its inverse.
* `FDRep.finrank_hom_of_equiv_directSum`:
  `Module.finrank k (X ⟶ Y) = ∑ i, Module.finrank k (X ⟶ Z i)` over a field `k` for `[Fintype ι]`.
-/

public section

open CategoryTheory

universe u v w

namespace FDRep

section CommRing

variable {R : Type u} {G : Type v} {ι : Type w} [CommRing R] [Monoid G] [Finite ι]

/-- An unbundled equivalence `Representation.Equiv Y.ρ (Representation.directSum fun i ↦ (Z i).ρ)`
decomposes morphisms `X ⟶ Y` in `FDRep R G` `R`-linearly into families of component morphisms
`∀ i, X ⟶ Z i`. The index type `ι` may lie in any universe. -/
noncomputable def homLinearEquivOfEquivDirectSum (X Y : FDRep R G) (Z : ι → FDRep R G)
    (e : Representation.Equiv Y.ρ (Representation.directSum fun i ↦ (Z i).ρ)) :
    (X ⟶ Y) ≃ₗ[R] ∀ i, X ⟶ Z i :=
  ((forget₂HomLinearEquiv X Y).symm.trans (Rep.homLinearEquiv _ _)).trans <|
    (Representation.Equiv.intertwiningMapCongr (.refl X.ρ) e).trans <|
    (Representation.IntertwiningMap.directSumLinearEquiv X.ρ (fun i ↦ (Z i).ρ)).trans <|
    LinearEquiv.piCongrRight fun i ↦
      ((forget₂HomLinearEquiv X (Z i)).symm.trans (Rep.homLinearEquiv _ _)).symm

/-- Evaluating the `i`-th component of `homLinearEquivOfEquivDirectSum` applies `e` and reads off
summand `i`. -/
@[simp]
theorem homLinearEquivOfEquivDirectSum_apply_hom_hom_hom (X Y : FDRep R G) (Z : ι → FDRep R G)
    (e : Representation.Equiv Y.ρ (Representation.directSum fun i ↦ (Z i).ρ))
    (φ : X ⟶ Y) (i : ι) (x : X) :
    (homLinearEquivOfEquivDirectSum X Y Z e φ i).hom.hom.hom x = e (φ.hom.hom.hom x) i :=
  (Representation.IntertwiningMap.directSumLinearEquiv_apply _ _ _ i x).trans <|
    congrArg (fun y : DirectSum ι fun j ↦ ↥(Z j) ↦ y i)
      (Representation.Equiv.intertwiningMapCongr_apply _ _ _ x)

/-- Applying `e` to the inverse of `homLinearEquivOfEquivDirectSum` recovers each supplied
component morphism. -/
@[simp]
theorem e_homLinearEquivOfEquivDirectSum_symm_apply (X Y : FDRep R G) (Z : ι → FDRep R G)
    (e : Representation.Equiv Y.ρ (Representation.directSum fun i ↦ (Z i).ρ))
    (φ : ∀ i, X ⟶ Z i) (x : X) (i : ι) :
    e (((homLinearEquivOfEquivDirectSum X Y Z e).symm φ).hom.hom.hom x) i =
      (φ i).hom.hom.hom x := by
  rw [← homLinearEquivOfEquivDirectSum_apply_hom_hom_hom, LinearEquiv.apply_symm_apply]

end CommRing

section Field

variable {k : Type u} {G : Type v} {ι : Type w} [Field k] [Monoid G] [Fintype ι]

/-- **Direct-sum decomposition of Hom-space dimensions in `FDRep k G`**: an unbundled equivalence
`Representation.Equiv Y.ρ (Representation.directSum fun i ↦ (Z i).ρ)` decomposes the dimension of
`X ⟶ Y` as the sum of the dimensions of `X ⟶ Z i`. -/
theorem finrank_hom_of_equiv_directSum (X Y : FDRep k G) (Z : ι → FDRep k G)
    (e : Representation.Equiv Y.ρ (Representation.directSum fun i ↦ (Z i).ρ)) :
    Module.finrank k (X ⟶ Y) = ∑ i, Module.finrank k (X ⟶ Z i) := by
  rw [(homLinearEquivOfEquivDirectSum X Y Z e).finrank_eq, Module.finrank_pi_fintype]

end Field

end FDRep
