/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Pinning.Basic

/-!
# Transport of pinnings across isomorphisms

An isomorphism `e : H ≅ L` of coordinate Hopf algebras identifies the affine group schemes
`Spec L` and `Spec H`. This file transports a pinning of `L` to a pinning of `H`: the split
maximal torus and the Borel subgroup are pulled back along `e`, and each simple root space
trivialization is followed by the differential of `e`.

The simple roots of a pinning are not chosen data but are read off from the torus and the Borel
subgroup. The substance of the transport is therefore that the pulled-back torus and Borel subgroup
have the same positive and simple roots. This rests on two compatibilities of the differential of
`e`: it carries each adjoint weight space onto the weight space of the same character for the
pulled-back torus (`Derivation.map_dualCotangentMap_adjointWeightSpace`), and it carries the
tangent Lie algebra of the Borel subgroup onto that of its pullback
(`TauCeti.HopfIdeal.derivationComp_mem_lieSubalgebra_comapOfSurjective_iff`).

This lets a pinning constructed for one presentation of a group scheme be used for every
isomorphic presentation, for instance for an explicitly constructed Chevalley group identified
with a classical group.

## Main declarations

* `TauCeti.SplitMaximalTorus.isPositiveRoot_comapOfIso_iff` and
  `TauCeti.SplitMaximalTorus.isSimpleRoot_comapOfIso_iff`: positive and simple roots are invariant
  under transport across an isomorphism.
* `TauCeti.Pinning.comapOfIso`: the transported pinning, with the same simple roots
  (`TauCeti.Pinning.isSimpleRoot_comapOfIso_iff`).
* `TauCeti.Pinning.comapOfIso_rootVector`: its root vectors are the images of the original root
  vectors under the differential of the isomorphism.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21.1.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {R : Type u} [CommRing R] {H L : CommHopfAlgCat.{u} R}
  [Algebra.FiniteType R H] [Algebra.FiniteType R L] {r : ℕ}

namespace SplitMaximalTorus

variable [Module.Projective R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R L)]

/-- Positive roots are invariant under pulling the torus and the subgroup back across an
isomorphism of coordinate Hopf algebras. -/
@[simp]
theorem isPositiveRoot_comapOfIso_iff (T : SplitMaximalTorus R L r) (B : HopfIdeal R L)
    (e : H ≅ L) (α : ULift.{u} (Fin r) →₀ ℤ) :
    (T.comapOfIso e).IsPositiveRoot
        (B.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2) α ↔
      T.IsPositiveRoot B α := by
  rw [isPositiveRoot_iff, isPositiveRoot_iff, hom_comapOfIso_coordinateMap,
    Derivation.nontrivialAdjointWeights_comp_bialgEquiv]
  refine and_congr_right fun _ ↦ ?_
  rw [← Derivation.map_dualCotangentMap_adjointWeightSpace (CommHopfAlgCat.ofIso e)
    T.coordinateMap.hom (Multiplicative.ofAdd α)]
  refine ⟨fun h y hy ↦ ?_, ?_⟩
  · have hmem := h _ (Submodule.mem_map_of_mem hy)
    rw [Derivation.cotangentLinearEquiv_dualCotangentMap] at hmem
    exact (HopfIdeal.derivationComp_mem_lieSubalgebra_comapOfSurjective_iff _ _ _ _).mp hmem
  · rintro h x ⟨y, hy, rfl⟩
    rw [Derivation.cotangentLinearEquiv_dualCotangentMap]
    exact (HopfIdeal.derivationComp_mem_lieSubalgebra_comapOfSurjective_iff _ _ _ _).mpr (h y hy)

/-- Simple roots are invariant under pulling the torus and the subgroup back across an
isomorphism of coordinate Hopf algebras. -/
@[simp]
theorem isSimpleRoot_comapOfIso_iff (T : SplitMaximalTorus R L r) (B : HopfIdeal R L)
    (e : H ≅ L) (α : ULift.{u} (Fin r) →₀ ℤ) :
    (T.comapOfIso e).IsSimpleRoot
        (B.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2) α ↔
      T.IsSimpleRoot B α := by
  simp only [isSimpleRoot_iff, isPositiveRoot_comapOfIso_iff]

end SplitMaximalTorus

namespace Pinning

variable [Algebra.Smooth R H] [Algebra.Smooth R L] [ConnectedSpace (PrimeSpectrum R)]

/-- **Transport of a pinning across an isomorphism** `e : H ≅ L` of coordinate Hopf algebras.
The torus and the Borel subgroup of `L` are pulled back along `e`, and each simple root space
trivialization is followed by the differential of `e`. -/
noncomputable def comapOfIso (P : Pinning R L r) (e : H ≅ L) : Pinning R H r where
  reductive := (reductiveCommHopfAlgPropertyOver R).prop_of_iso
    (ObjectProperty.isoMk _ e).symm P.reductive
  torus := P.torus.comapOfIso e
  borel := P.borel.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2
  isBorel := P.isBorel.comapOfIso e
  borel_le_torus := by
    rw [SplitMaximalTorus.definingIdeal_comapOfIso]
    exact HopfIdeal.comapOfSurjective_mono _ _ P.borel_le_torus
  rootSpaceEquiv α :=
    (P.rootSpaceEquiv ⟨α.val,
      (SplitMaximalTorus.isSimpleRoot_comapOfIso_iff _ _ e _).mp α.property⟩).trans
      ((Derivation.adjointWeightSpaceEquiv (CommHopfAlgCat.ofIso e) _ _).trans
        (LinearEquiv.ofEq _ _ (by
          rw [SplitMaximalTorus.hom_comapOfIso_coordinateMap])))

@[simp]
theorem comapOfIso_torus (P : Pinning R L r) (e : H ≅ L) :
    (P.comapOfIso e).torus = P.torus.comapOfIso e :=
  (rfl)

@[simp]
theorem comapOfIso_borel (P : Pinning R L r) (e : H ≅ L) :
    (P.comapOfIso e).borel =
      P.borel.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2 :=
  (rfl)

/-- The simple roots of a transported pinning are those of the original pinning. -/
theorem isSimpleRoot_comapOfIso_iff (P : Pinning R L r) (e : H ≅ L)
    (α : ULift.{u} (Fin r) →₀ ℤ) :
    (P.comapOfIso e).torus.IsSimpleRoot (P.comapOfIso e).borel α ↔
      P.torus.IsSimpleRoot P.borel α := by
  rw [comapOfIso_torus, comapOfIso_borel, SplitMaximalTorus.isSimpleRoot_comapOfIso_iff]

/-- The trivializations of a transported pinning are those of the original pinning, at the same
simple root, followed by the differential of the isomorphism. -/
@[simp]
theorem coe_comapOfIso_rootSpaceEquiv_apply (P : Pinning R L r) (e : H ≅ L)
    (α : {α // (P.comapOfIso e).torus.IsSimpleRoot (P.comapOfIso e).borel α}) (c : R) :
    ((P.comapOfIso e).rootSpaceEquiv α c : Module.Dual R (Bialgebra.CotangentSpace R H)) =
      Derivation.dualCotangentMap e.hom.hom
        (P.rootSpaceEquiv ⟨α.val,
          (P.isSimpleRoot_comapOfIso_iff e _).mp α.property⟩ c) := by
  rw [← CommHopfAlgCat.coe_ofIso]
  -- The transported trivialization is the original one followed by the weight-space equivalence
  -- of `CommHopfAlgCat.ofIso e` and a `LinearEquiv.ofEq` retyping. `LinearEquiv.trans_apply`
  -- cannot be rewritten here: the field's codomain is stated for `(P.comapOfIso e).torus`, which
  -- is not reducibly `P.torus.comapOfIso e`, so `exact` unfolds the chain instead.
  exact Derivation.coe_adjointWeightSpaceEquiv_apply _ _ _ _

/-- **The root vectors of a transported pinning** are the images of the root vectors of the
original pinning, at the same simple roots, under the differential of the isomorphism. -/
theorem comapOfIso_rootVector (P : Pinning R L r) (e : H ≅ L)
    (α : {α // (P.comapOfIso e).torus.IsSimpleRoot (P.comapOfIso e).borel α}) :
    (P.comapOfIso e).rootVector α =
      Derivation.dualCotangentMap e.hom.hom
        (P.rootVector ⟨α.val, (P.isSimpleRoot_comapOfIso_iff e _).mp α.property⟩) := by
  rw [rootVector_def, rootVector_def, coe_comapOfIso_rootSpaceEquiv_apply]

end Pinning

end TauCeti
