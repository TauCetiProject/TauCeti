/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Resolution
public import TauCeti.RepresentationTheory.Homological.GroupHomology.ChangeOfGroups

/-!
# Equivariant maps on coinvariant singular chains

A continuous map equivariant along a group homomorphism induces a map on the coinvariants
of singular chains. No injectivity or surjectivity of the homomorphism is required. These
are the maps on the geometric resolutions used to compare the homology of quotient covers
with group homology.

The map sends the class of `a ⊗ c` to the class of `a ⊗ f_* c`. It respects identities and
composition, and is defined for arbitrary continuous actions, without freeness or
contractibility assumptions. The descent uses Mathlib's `Representation.Coinvariants.lift`.

Before passing to coinvariants, pushing chains forward along `f` is a chain map
`TauCeti.singularChainsRepResMap` from the equivariant singular chains of `E` to the restriction
along `φ` of those of `F`, and it preserves the augmentations
(`TauCeti.singularChainsRepResMap_f_zero_comp_augmentation`). The map on coinvariants is the
change-of-groups map `MonoidHom.coinvariantsTensorChainMap` induced by it
(`TauCeti.singularChainsCoinvariantsMap_eq_coinvariantsTensorChainMap`), which is how the
group-homology naturality of `MonoidHom.groupHomologyIso_hom_naturality` applies to singular
chains.

## Main definitions

* `TauCeti.singularChainsRepResMap`: the equivariant pushforward of singular chains, as a chain
  map into the restricted complex.
* `TauCeti.singularChainsCoinvariantsMap`: the induced chain map on coinvariants.

## References

* K. S. Brown, *Cohomology of Groups*, Springer GTM 87, Chapters II.4 and III.1.
-/

public section

noncomputable section

open CategoryTheory Representation

universe u

namespace TauCeti

variable (k : Type u) [CommRing k]

section Equivariance

variable {G H : Type u} [Monoid G] [Monoid H]
  {E F : TopCat.{u}} [MulAction G E] [MulAction H F]
  [ContinuousConstSMul G E] [ContinuousConstSMul H F]
  {φ : G →* H} (f : E ⟶ F) (hf : ∀ g x, f (g • x) = φ g • f x)

include hf in
/-- Pushing singular chains forward along an equivariant map intertwines the actions,
including when the acting monoids differ. -/
theorem singularChains_map_f_representation (n : ℕ) (g : G)
    (c : ((singularChains k).obj E).X n) :
    ((singularChains k).map f).f n (singularChainsRepresentation k E G n g c) =
      singularChainsRepresentation k F H n (φ g) (((singularChains k).map f).f n c) := by
  have h : TopCat.ofHom ⟨(g • · : E → E), continuous_const_smul g⟩ ≫ f =
      f ≫ TopCat.ofHom ⟨(φ g • · : F → F), continuous_const_smul (φ g)⟩ :=
    ConcreteCategory.hom_ext _ _ (hf g)
  simp only [singularChainsRepresentation_apply]
  simpa only [Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.comp_apply] using
    ConcreteCategory.congr_hom
    (congrArg (fun q ↦ q.f n) (congrArg (singularChains k).map h)) c

/-- The pushforward of singular `n`-chains along an equivariant map, as a morphism of
representations of `G` into the restriction along `φ`. -/
private def singularChainsRepResHom (n : ℕ) :
    (singularChainsRep k E G).X n ⟶ Rep.res φ ((singularChainsRep k F H).X n) :=
  Rep.ofHom
    { toLinearMap := (((singularChains k).map f).f n).hom
      isIntertwining' g := LinearMap.ext fun c ↦ singularChains_map_f_representation k f hf n g c }

/-- **Pushing singular chains forward along an equivariant map** is a chain map from the
equivariant singular chains of `E` to the restriction along `φ` of the equivariant singular chains
of `F`. -/
def singularChainsRepResMap :
    singularChainsRep k E G ⟶
      ((Rep.resFunctor φ).mapHomologicalComplex _).obj (singularChainsRep k F H) where
  f n := singularChainsRepResHom k f hf n
  comm' i j hij := by
    subst i
    rw [Functor.mapHomologicalComplex_obj_d, singularChainsRep_d, singularChainsRep_d]
    ext c
    -- Both composites push `c` forward along `f` and take the singular boundary, in either order.
    exact (singularChainsRepDifferential_hom_apply k F H j _).trans
      ((ConcreteCategory.congr_hom (((singularChains k).map f).comm (j + 1) j) c).trans
        (congrArg (((singularChains k).map f).f j)
          (singularChainsRepDifferential_hom_apply k E G j c).symm))

/-- The equivariant chain map pushes chains forward along `f`. -/
-- Match before simplification changes the presentation of the restricted target carrier.
@[simp↓]
theorem singularChainsRepResMap_f_hom_apply (n : ℕ) (c : ((singularChains k).obj E).X n) :
    ((singularChainsRepResMap k f hf).f n).hom c = ((singularChains k).map f).f n c :=
  (rfl)

/-- The equivariant pushforward of singular chains preserves the augmentations. -/
theorem singularChainsRepResMap_f_zero_comp_augmentation :
    (singularChainsRepResMap k f hf).f 0 ≫
        (Rep.resFunctor φ).map ((singularChainsRepAugmentation k F H).f 0) =
      (singularChainsRepAugmentation k E G).f 0 := by
  ext c
  rw [singularChainsRepAugmentation_f_zero, singularChainsRepAugmentation_f_zero]
  -- Both sides are the augmentation, after pushing `c` forward along `f` on the left.
  exact (LinearMap.congr_fun (singularAugmentRep_hom_toLinearMap k F H) _).trans
    ((singularAugment_map f c).trans
      (LinearMap.congr_fun (singularAugmentRep_hom_toLinearMap k E G) c).symm)

end Equivariance

variable {G H K : Type u} [Group G] [Group H] [Group K]
  {E F D : TopCat.{u}} [MulAction G E] [MulAction H F] [MulAction K D]
  [ContinuousConstSMul G E] [ContinuousConstSMul H F] [ContinuousConstSMul K D]
  {φ : G →* H} (f : E ⟶ F) (hf : ∀ g x, f (g • x) = φ g • f x)

private def singularChainsCoinvariantsMapApp (n : ℕ) :
    ((Rep.coinvariantsTensor k G).obj (Rep.trivial k G k)).obj
        (Rep.of (singularChainsRepresentation k E G n)) ⟶
      ((Rep.coinvariantsTensor k H).obj (Rep.trivial k H k)).obj
        (Rep.of (singularChainsRepresentation k F H n)) :=
  ModuleCat.ofHom <| Coinvariants.lift _
    ((Coinvariants.mk _).comp
      (TensorProduct.map LinearMap.id (((singularChains k).map f).f n).hom)) fun g ↦ by
        refine TensorProduct.ext (LinearMap.ext₂ fun (a : k)
          (c : ((singularChains k).obj E).X n) ↦ ?_)
        -- The tensor representation acts trivially on the scalar factor. Unfold its action
        -- before applying equivariance, since the coinvariant carrier contains that factor.
        change Coinvariants.mk ((Representation.trivial k H k).tprod
            (singularChainsRepresentation k F H n)) (a ⊗ₜ[k]
            (((singularChains k).map f).f n (singularChainsRepresentation k E G n g c))) =
          Coinvariants.mk ((Representation.trivial k H k).tprod
            (singularChainsRepresentation k F H n))
            (a ⊗ₜ[k] (((singularChains k).map f).f n c))
        rw [singularChains_map_f_representation k f hf]
        exact Coinvariants.mk_self_apply _ (φ g) (a ⊗ₜ[k] _)

private lemma singularChainsCoinvariantsMapApp_mk (n : ℕ) (a : k)
    (c : ((singularChains k).obj E).X n) :
    singularChainsCoinvariantsMapApp k f hf n (Rep.coinvariantsTensorMk _ _ a c) =
      Rep.coinvariantsTensorMk _ _ a (((singularChains k).map f).f n c) :=
  (rfl)

/-- The chain map on coinvariants induced by a continuous map equivariant along `φ`.
The coefficient representation is the trivial representation on `k`. -/
def singularChainsCoinvariantsMap :
    (singularChainsRep k E G).coinvariantsTensorObj (Rep.trivial k G k) ⟶
      (singularChainsRep k F H).coinvariantsTensorObj (Rep.trivial k H k) where
  f := singularChainsCoinvariantsMapApp k f hf
  comm' i j hij := by
    subst i
    rw [Functor.mapHomologicalComplex_obj_d, singularChainsRep_d,
      Functor.mapHomologicalComplex_obj_d, singularChainsRep_d]
    refine Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun (a : k)
      (c : ((singularChains k).obj E).X (j + 1)) ↦ ?_)
    -- Both differentials are induced on the tensor coinvariants by the singular boundary.
    -- Expose these induced maps so that evaluation on a pure tensor is available.
    change (((Rep.coinvariantsTensor k H).obj (Rep.trivial k H k)).map
        (singularChainsRepDifferential k F H j)).hom
        (singularChainsCoinvariantsMapApp k f hf (j + 1)
          (Rep.coinvariantsTensorMk (Rep.trivial k G k)
            (Rep.of (singularChainsRepresentation k E G (j + 1))) a c)) =
      singularChainsCoinvariantsMapApp k f hf j
        (Rep.coinvariantsTensorMk (Rep.trivial k G k)
          (Rep.of (singularChainsRepresentation k E G j)) a
          ((singularChainsRepDifferential k E G j).hom c))
    rw [singularChainsCoinvariantsMapApp_mk, singularChainsCoinvariantsMapApp_mk]
    -- Functoriality on tensor coinvariants evaluates on representatives by definition.
    change Rep.coinvariantsTensorMk (Rep.trivial k H k)
        (Rep.of (singularChainsRepresentation k F H j)) a
        ((singularChainsRepDifferential k F H j).hom
          (((singularChains k).map f).f (j + 1) c)) = _
    rw [singularChainsRepDifferential_hom_apply, singularChainsRepDifferential_hom_apply]
    apply congrArg (Rep.coinvariantsTensorMk (Rep.trivial k H k)
      (Rep.of (singularChainsRepresentation k F H j)) a)
    exact ConcreteCategory.congr_hom (((singularChains k).map f).comm (j + 1) j) c

/-- The map on coinvariants pushes forward the chain in a pure tensor. -/
-- Match before simplification changes the presentation of the dependent tensor carrier.
@[simp↓]
theorem singularChainsCoinvariantsMap_f_mk (n : ℕ) (a : k)
    (c : ((singularChains k).obj E).X n) :
    (singularChainsCoinvariantsMap k f hf).f n
        (Rep.coinvariantsTensorMk (Rep.trivial k G k)
          (Rep.of (singularChainsRepresentation k E G n)) a c) =
      Rep.coinvariantsTensorMk (Rep.trivial k H k)
        (Rep.of (singularChainsRepresentation k F H n)) a
        (((singularChains k).map f).f n c) :=
  singularChainsCoinvariantsMapApp_mk k f hf n a c

/-- The identity of a space induces the identity on coinvariant singular chains. -/
@[simp]
theorem singularChainsCoinvariantsMap_id :
    singularChainsCoinvariantsMap k (𝟙 E) (φ := MonoidHom.id G) (fun _ _ ↦ rfl) =
      𝟙 ((singularChainsRep k E G).coinvariantsTensorObj (Rep.trivial k G k)) := by
  apply HomologicalComplex.hom_ext
  intro n
  refine Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun (a : k)
    (c : ((singularChains k).obj E).X n) ↦ ?_)
  -- Evaluate on tensor classes, removing the complex and bilinear-map wrappers.
  change (singularChainsCoinvariantsMap k (𝟙 E) (φ := MonoidHom.id G)
      (fun _ _ ↦ rfl)).f n
      (Rep.coinvariantsTensorMk (Rep.trivial k G k)
        (Rep.of (singularChainsRepresentation k E G n)) a c) =
    Rep.coinvariantsTensorMk (Rep.trivial k G k)
      (Rep.of (singularChainsRepresentation k E G n)) a c
  refine (singularChainsCoinvariantsMap_f_mk k (𝟙 E)
    (φ := MonoidHom.id G) (fun _ _ ↦ rfl) n a c).trans ?_
  exact congrArg (fun q : (singularChains k).obj E ⟶ (singularChains k).obj E ↦
    Rep.coinvariantsTensorMk (Rep.trivial k G k)
      (Rep.of (singularChainsRepresentation k E G n)) a (q.f n c))
    ((singularChains k).map_id E)

/-- Equivariant continuous maps induce maps on coinvariant chains respecting composition. -/
@[simp]
theorem singularChainsCoinvariantsMap_comp {ψ : H →* K} (q : F ⟶ D)
    (hq : ∀ h x, q (h • x) = ψ h • q x) :
    singularChainsCoinvariantsMap k (f ≫ q) (φ := ψ.comp φ)
        (fun g x ↦ by rw [TopCat.comp_app, hf, hq]; rfl) =
      singularChainsCoinvariantsMap k f hf ≫ singularChainsCoinvariantsMap k q hq := by
  apply HomologicalComplex.hom_ext
  intro n
  refine Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun (a : k)
    (c : ((singularChains k).obj E).X n) ↦ ?_)
  -- Evaluate the composite components on tensor classes before using their formulas.
  change (singularChainsCoinvariantsMap k (f ≫ q) (φ := ψ.comp φ)
      (fun g x ↦ by rw [TopCat.comp_app, hf, hq]; rfl)).f n
      (Rep.coinvariantsTensorMk (Rep.trivial k G k)
        (Rep.of (singularChainsRepresentation k E G n)) a c) =
    (singularChainsCoinvariantsMap k q hq).f n
      ((singularChainsCoinvariantsMap k f hf).f n
        (Rep.coinvariantsTensorMk (Rep.trivial k G k)
          (Rep.of (singularChainsRepresentation k E G n)) a c))
  rw [singularChainsCoinvariantsMap_f_mk, singularChainsCoinvariantsMap_f_mk,
    singularChainsCoinvariantsMap_f_mk]
  simp only [Functor.map_comp, HomologicalComplex.comp_f]
  rfl

/-- The map on coinvariant singular chains is the change-of-groups map on tensor coinvariants
induced by the equivariant pushforward of chains, with the identity on the trivial coefficients
`k`. -/
theorem singularChainsCoinvariantsMap_eq_coinvariantsTensorChainMap :
    singularChainsCoinvariantsMap k f hf =
      φ.coinvariantsTensorChainMap (B := Rep.trivial k H k) (𝟙 (Rep.trivial k G k))
        (singularChainsRepResMap k f hf) :=
  -- Both sides evaluate on a tensor class `⟦a ⊗ c⟧` to `⟦a ⊗ f_* c⟧`.
  HomologicalComplex.hom_ext _ _ fun n ↦
    Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a c ↦
      (singularChainsCoinvariantsMap_f_mk k f hf n a c).trans
        (φ.coinvariantsTensorChainMap_f_mk (B := Rep.trivial k H k) (𝟙 (Rep.trivial k G k))
          (singularChainsRepResMap k f hf) n a c).symm)

end TauCeti
