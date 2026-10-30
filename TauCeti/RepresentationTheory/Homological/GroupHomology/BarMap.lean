/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.Resolution

/-!
# Change of groups on bar coinvariants

For `f : G →* H` and a compatible coefficient map `φ : A ⟶ Rep.res f B`, the map on bar
coinvariants sends `⟦a ⊗ c⟧` to `⟦φ(a) ⊗ f_*(c)⟧`. This file constructs it by transporting
Mathlib's inhomogeneous chain map across Amelia Livingston's `inhomogeneousChainsIso`, then
proves this tensor formula. Thus the construction works for arbitrary homomorphisms, including
ones for which restriction does not preserve projective representations.

The chain square and its induced homology square identify the algebraic change-of-group map
in comparisons with equivariant chains of a contractible free group action. Coefficients may
have nontrivial action. The bar map uses the existing
`TauCeti.Rep.barComplex.resChainMap`, which applies the homomorphism to all group labels.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapters I.5 and III.8.
-/

public section

noncomputable section

open CategoryTheory Rep Representation Finsupp
open groupHomology

universe u

namespace MonoidHom

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  [DecidableEq G] [DecidableEq H] {A : Rep k G} {B : Rep k H}

/-- Change of groups on bar coinvariants. On tensor classes this applies the compatible
coefficient map in the first factor and relabels the bar chain in the second factor. -/
def barCoinvariantsMap (f : G →* H) (φ : A ⟶ res f B) :
    (barComplex k G).coinvariantsTensorObj A ⟶
      (barComplex k H).coinvariantsTensorObj B :=
  (inhomogeneousChainsIso A).inv ≫ chainsMap f φ ≫ (inhomogeneousChainsIso B).hom

/-- The inhomogeneous-to-bar chain identification commutes with change of groups and
compatible coefficient maps. -/
@[reassoc]
theorem inhomogeneousChainsIso_hom_barCoinvariantsMap (f : G →* H) (φ : A ⟶ res f B) :
    (inhomogeneousChainsIso A).hom ≫ f.barCoinvariantsMap φ =
      chainsMap f φ ≫ (inhomogeneousChainsIso B).hom := by
  simp [barCoinvariantsMap]

/-- The inverse chain identification also commutes with change of groups. -/
@[reassoc]
theorem barCoinvariantsMap_inhomogeneousChainsIso_inv (f : G →* H) (φ : A ⟶ res f B) :
    f.barCoinvariantsMap φ ≫ (inhomogeneousChainsIso B).inv =
      (inhomogeneousChainsIso A).inv ≫ chainsMap f φ := by
  simp [barCoinvariantsMap]

/-- On the class of a tensor with one bar basis vector, change of groups applies `φ` to the
coefficient and `f` to both the tuple and the group-ring label. -/
private theorem barCoinvariantsMap_f_mk_tmul_single (f : G →* H) (φ : A ⟶ res f B) (n : ℕ)
    (a : A) (x : Fin n → G) (g : G) (r : k) :
    (f.barCoinvariantsMap φ).f n
        (Coinvariants.mk _ (a ⊗ₜ[k] single x (MonoidAlgebra.single g r))) =
      Coinvariants.mk _ (φ.hom a ⊗ₜ[k]
        single (f ∘ x) (MonoidAlgebra.single (f g) r)) := by
  apply (coinvariantsTensorFreeLEquiv B (Fin n → H)).injective
  simp only [barCoinvariantsMap, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply,
    inhomogeneousChainsIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    HomologicalComplex.Hom.isoOfComponents_inv_f, Iso.symm_hom, Iso.symm_inv,
    LinearEquiv.toModuleIso_hom, LinearEquiv.toModuleIso_inv, ModuleCat.hom_ofHom,
    LinearEquiv.coe_coe]
  rw [LinearEquiv.apply_symm_apply]
  -- Mathlib's equivalence is an abbreviation assembled with `LinearEquiv.ofLinearMap`.
  -- Present its forward map explicitly before applying the tensor-basis computation.
  change (chainsMap f φ).f n
      (coinvariantsTensorFreeToFinsupp A _ (Coinvariants.mk _
        (a ⊗ₜ[k] single x (MonoidAlgebra.single g r)))) =
    coinvariantsTensorFreeToFinsupp B _ (Coinvariants.mk _
      (φ.hom a ⊗ₜ[k] single (f ∘ x) (MonoidAlgebra.single (f g) r)))
  simp only [tensor_ρ]
  rw [coinvariantsTensorFreeToFinsupp_mk_tmul_single, chainsMap_f_single,
    coinvariantsTensorFreeToFinsupp_mk_tmul_single]
  congr 1
  rw [map_smul, Rep.hom_comm_apply]
  simp only [res_obj_ρ, MonoidHom.comp_apply, map_inv]

/-- On any tensor class the bar map is the tensor of the coefficient map and the existing
bar-resolution map, followed by passage to the target coinvariants. -/
-- State tensor classes in simp normal form, with the tensor representation explicit.
@[simp]
theorem barCoinvariantsMap_f_mk_tmul (f : G →* H) (φ : A ⟶ res f B)
    (n : ℕ) (a : A) (c : (Fin n → G) →₀ MonoidAlgebra k G) :
    (dsimp% only [Functor.mapHomologicalComplex_obj_X, Functor.postcompose₂_obj_obj_obj_obj,
      MonoidalCategory.curriedTensor_obj_obj, coinvariantsFunctor_obj_carrier, tensor_V, tensor_ρ]
      ((f.barCoinvariantsMap φ).f n
      (Coinvariants.mk (A.ρ.tprod (Representation.free k G (Fin n → G))) (a ⊗ₜ[k] c)))) =
      Coinvariants.mk (B.ρ.tprod (Representation.free k H (Fin n → H)))
        (φ.hom a ⊗ₜ[k] (((TauCeti.Rep.barComplex.resChainMap f).f n).hom c)) := by
  -- Compare linear maps before evaluating at `c`: each bar term is a free representation
  -- on tuples, so its two nested free-module universal properties reduce to basis vectors.
  have h : ∀ c : (Fin n → G) →₀ MonoidAlgebra k G,
      (f.barCoinvariantsMap φ).f n (Coinvariants.mk _ (a ⊗ₜ[k] c)) =
        Coinvariants.mk _ (φ.hom a ⊗ₜ[k]
          (TauCeti.Rep.barComplex.resHom f n).hom c) := by
    apply LinearMap.congr_fun (show
      ((f.barCoinvariantsMap φ).f n).hom ∘ₗ Coinvariants.mk _ ∘ₗ
          TensorProduct.mk k _ _ a =
        Coinvariants.mk _ ∘ₗ TensorProduct.mk k _ _ (φ.hom a) ∘ₗ
          (TauCeti.Rep.barComplex.resHom f n).hom.toLinearMap from ?_)
    refine lhom_ext' fun x ↦ MonoidAlgebra.lhom_ext' fun g ↦ LinearMap.ext fun r ↦ ?_
    -- The extensionality lemmas insert linear `single` maps and the curried tensor map.
    -- State their applications on the underlying free modules to use the basis formula.
    change (f.barCoinvariantsMap φ).f n
        (Coinvariants.mk _ (a ⊗ₜ[k] single x (MonoidAlgebra.single g r))) =
      Coinvariants.mk _ (φ.hom a ⊗ₜ[k]
        (TauCeti.Rep.barComplex.resHom f n).hom (single x (MonoidAlgebra.single g r)))
    rw [barCoinvariantsMap_f_mk_tmul_single, TauCeti.Rep.barComplex.resHom_single]
  simpa only [MonoidalCategory.curriedTensor_obj_obj, tensor_ρ,
    TauCeti.Rep.barComplex.resChainMap_f] using h c

/-- The identity homomorphism and identity coefficient map induce the identity on bar
coinvariants. -/
@[simp]
theorem barCoinvariantsMap_id :
    (MonoidHom.id G).barCoinvariantsMap (𝟙 A) =
      𝟙 ((barComplex k G).coinvariantsTensorObj A) := by
  simp [barCoinvariantsMap]

/-- Change of groups on bar coinvariants respects composition of both the homomorphisms and
the compatible coefficient maps. -/
theorem barCoinvariantsMap_comp {K : Type u} [Group K] [DecidableEq K] {C : Rep k K}
    (f : G →* H) (g : H →* K) (φ : A ⟶ res f B) (ψ : B ⟶ res g C) :
    (g.comp f).barCoinvariantsMap (φ ≫ (resFunctor f).map ψ) =
      f.barCoinvariantsMap φ ≫ g.barCoinvariantsMap ψ := by
  unfold barCoinvariantsMap
  rw [chainsMap_comp]
  simp [Category.assoc]

/-- The induced map on the homology of bar coinvariants is Mathlib's change-of-group map
on group homology under the existing chain identifications. -/
@[reassoc]
theorem inhomogeneousChainsIso_homologyMap_barCoinvariantsMap (f : G →* H)
    (φ : A ⟶ res f B) (n : ℕ) :
    HomologicalComplex.homologyMap (inhomogeneousChainsIso A).hom n ≫
        HomologicalComplex.homologyMap (f.barCoinvariantsMap φ) n =
      groupHomology.map f φ n ≫
        HomologicalComplex.homologyMap (inhomogeneousChainsIso B).hom n := by
  dsimp only [groupHomology.map]
  rw [← HomologicalComplex.homologyMap_comp, inhomogeneousChainsIso_hom_barCoinvariantsMap,
    HomologicalComplex.homologyMap_comp]
  rfl

end MonoidHom
