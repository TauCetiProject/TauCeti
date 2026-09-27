/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import TauCeti.RepresentationTheory.Rep.ChangeOfGroup

/-!
# Functoriality of group homology

Mathlib shows that the functor `groupHomology.chainsFunctor k G` sending a representation to its
complex of inhomogeneous chains preserves zero morphisms. This file shows that it is additive,
matching Mathlib's instance for its cohomological counterpart `groupCohomology.cochainsFunctor`.

It also records how the map on first homology induced by a group homomorphism `f : H →* G` reads
through Mathlib's identification `H₁(G, A) ≃ Gᵃᵇ ⊗ A` for trivial coefficients: it is
`Abelianization.map f` tensored with the coefficients.

## Main results

* `TauCeti.groupHomology.chainsFunctorAdditive`: the chains functor is additive.
* `TauCeti.groupHomology.map_mkH1OfIsTrivial`: with trivial coefficients, the map on `H₁` induced
  by `f : H →* G` and `φ : A ⟶ Res(f)(B)` sends the class of `x ⊗ a` to that of `f x ⊗ φ a`.
* `TauCeti.groupHomology.H1AddEquivOfIsTrivial_map`: with trivial coefficients, the map
  `H₁(H, A) ⟶ H₁(G, A)` induced by `f : H →* G` is `Abelianization.map f ⊗ A`.
-/

public noncomputable section

universe u

open CategoryTheory

namespace TauCeti.groupHomology

variable {R G : Type u} [CommRing R] [Group G]

/-- The functor from representations to inhomogeneous group-homology chains is additive. -/
noncomputable instance chainsFunctorAdditive :
    (_root_.groupHomology.chainsFunctor R G).Additive where
  map_add := by
    intro X Y f g
    -- `chainsFunctor.map` is `chainsMap (MonoidHom.id G)` by definition (`chainsFunctor_map`).
    -- Rewriting with that lemma is not enough: the sum in the goal would still carry the
    -- preadditive instance from the statement of `Functor.Additive`, which
    -- `HomologicalComplex.add_f_apply` does not match syntactically. Restating the goal
    -- elaborates both sums with the `HomologicalComplex` addition.
    change _root_.groupHomology.chainsMap (MonoidHom.id G) (f + g) =
      _root_.groupHomology.chainsMap (MonoidHom.id G) f +
        _root_.groupHomology.chainsMap (MonoidHom.id G) g
    refine HomologicalComplex.hom_ext _ _ fun i => ModuleCat.hom_ext ?_
    simp only [HomologicalComplex.add_f_apply, ModuleCat.hom_add,
      _root_.groupHomology.chainsMap_id_f_hom_eq_mapRange]
    refine Finsupp.lhom_ext fun x a => ?_
    simp only [Rep.add_hom, Representation.IntertwiningMap.add_toLinearMap,
      LinearMap.add_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      Finsupp.single_add]

section IsTrivial

open _root_.groupHomology

variable {H : Type u} [Group H] (f : H →* G)

/-- With trivial coefficients, the map on first homology induced by `f : H →* G` and
`φ : A ⟶ Res(f)(B)` sends the class of `x ⊗ a` to the class of `f x ⊗ φ a`. -/
@[simp]
theorem map_mkH1OfIsTrivial {A : Rep R H} {B : Rep R G} [A.IsTrivial] [B.IsTrivial]
    (φ : A ⟶ Rep.res f B) (x : Additive (Abelianization H)) (a : A) :
    map f φ 1 (mkH1OfIsTrivial A x a) =
      mkH1OfIsTrivial B ((Abelianization.map f).toAdditive x) (φ.hom a) := by
  obtain ⟨h, rfl⟩ : ∃ h : H, Additive.ofMul (Abelianization.of h) = x :=
    QuotientGroup.mk'_surjective _ x.toMul
  rw [mkH1OfIsTrivial_apply, H1π_comp_map_apply, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
    Abelianization.map_of, mkH1OfIsTrivial_apply]
  congr 1
  apply Subtype.ext
  rw [coe_mapCycles₁, cycles₁IsoOfIsTrivial_inv_apply, cycles₁IsoOfIsTrivial_inv_apply]
  simp

/-- With trivial coefficients, the map on first homology induced by `f : H →* G` is
`Abelianization.map f ⊗ A`, read through the identifications `H₁(H, A) ≃ Hᵃᵇ ⊗ A` and
`H₁(G, A) ≃ Gᵃᵇ ⊗ A`. -/
@[simp]
theorem H1AddEquivOfIsTrivial_map (A : Rep R G) [A.IsTrivial] (y : H1 (Rep.res f A)) :
    H1AddEquivOfIsTrivial A (map f (𝟙 (Rep.res f A)) 1 y) =
      LinearMap.rTensor A (AddMonoidHom.toIntLinearMap (Abelianization.map f).toAdditive)
        (H1AddEquivOfIsTrivial (Rep.res f A) y) := by
  obtain ⟨t, rfl⟩ := (H1AddEquivOfIsTrivial (Rep.res f A)).symm.surjective y
  rw [AddEquiv.apply_symm_apply]
  induction t using TensorProduct.inductionOn with
  | tmul x a =>
    obtain ⟨h, rfl⟩ : ∃ h : H, Additive.ofMul (Abelianization.of h) = x :=
      QuotientGroup.mk'_surjective _ x.toMul
    rw [H1AddEquivOfIsTrivial_symm_tmul, ← mkH1OfIsTrivial_apply, map_mkH1OfIsTrivial]
    simpa using H1AddEquivOfIsTrivial_single A (f h) a
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', map_add]

end IsTrivial

end TauCeti.groupHomology
