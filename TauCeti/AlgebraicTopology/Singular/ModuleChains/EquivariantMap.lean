/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Resolution
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

/-!
# Equivariant maps on coinvariant singular chains

A continuous map equivariant along a group homomorphism induces a map on the coinvariants
of singular chains. No injectivity or surjectivity of the homomorphism is required. These
are the maps on the geometric resolutions used to compare the homology of quotient covers
with group homology.

The map sends the class of `a ⊗ c` to the class of `a ⊗ f_* c`. It respects identities and
composition, and is defined for arbitrary continuous actions, without freeness or
contractibility assumptions. The descent uses Mathlib's `Representation.Coinvariants.lift`.

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

end TauCeti
