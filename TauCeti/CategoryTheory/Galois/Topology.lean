/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Galois.Topology

/-!
# Continuity of whiskering and conjugation on automorphism groups of fibre functors

For a functor `F : C ⥤ FintypeCat`, Mathlib topologizes `Aut F` as a subspace of
`∀ X, Aut (F.obj X)`, each factor being discrete (`CategoryTheory.PreGaloisCategory.autEmbedding`).
When `F` is a fibre functor, `Aut F` is the fundamental group of the Galois category at `F`.
Mathlib shows that post-composition with a functor `FintypeCat ⥤ FintypeCat` induces a continuous
map on these groups (`CategoryTheory.PreGaloisCategory.continuous_mapAut_whiskeringRight`).
This file records the two other operations that change the fibre functor:

* precomposition with a functor `P : D ⥤ C`, inducing `Aut F →* Aut (P ⋙ F)`, which is how a
  morphism of Galois categories compatible with fibre functors acts on fundamental groups;
* conjugation `Iso.conjAut` along a natural isomorphism `e : F ≅ G`, which is how a path
  between base points changes the base point of a fundamental group.

Both are continuous, because the component at each object only depends on one component of the
argument: the component at `X` after precomposition is the component at `P.obj X`, and the
component of `e.conjAut σ` at `X` is the conjugate of the component of `σ` at `X` by `e.app X`.
Conjugation is therefore an isomorphism of topological groups `Aut F ≃ₜ* Aut G`
(`CategoryTheory.Iso.continuousConjAut`).

## Main results

* `CategoryTheory.PreGaloisCategory.continuous_mapAut_whiskeringLeft`: precomposition with a
  functor induces a continuous homomorphism `Aut F →* Aut (P ⋙ F)`.
* `CategoryTheory.Iso.continuous_conjAut`: conjugation along `e : F ≅ G` is continuous.
* `CategoryTheory.Iso.continuousConjAut`: conjugation along `e : F ≅ G` as an isomorphism of
  topological groups.
-/

public section

universe u₁ u₂ u₃ u₄ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{u₂} C] {D : Type u₃} [Category.{u₄} D]

namespace PreGaloisCategory

/-- If `P : D ⥤ C` is a functor, the induced map `Aut F → Aut (P ⋙ F)` is continuous. -/
lemma continuous_mapAut_whiskeringLeft (P : D ⥤ C) (F : C ⥤ FintypeCat.{w}) :
    Continuous (((Functor.whiskeringLeft _ _ _).obj P).mapAut F) := by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing,
    continuous_pi_iff]
  refine fun X ↦ ((continuous_apply (P.obj X)).comp
    (autEmbedding_isClosedEmbedding F).continuous).congr fun σ ↦ ?_
  simp only [Function.comp_apply, autEmbedding_apply, Functor.mapAut_apply_asIso]
  exact congrArg Aut.of (Iso.ext (by simp))

end PreGaloisCategory

namespace Iso

open PreGaloisCategory

variable {F G : C ⥤ FintypeCat.{w}}

/-- Conjugation along a natural isomorphism `e : F ≅ G` of functors to finite sets is
continuous on automorphism groups. -/
lemma continuous_conjAut (e : F ≅ G) : Continuous e.conjAut := by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing,
    continuous_pi_iff]
  refine fun X ↦ (continuous_of_discreteTopology.comp ((continuous_apply X).comp
    (autEmbedding_isClosedEmbedding F).continuous) :
      Continuous fun σ ↦ (e.app X).conjAut (autEmbedding F σ X)).congr fun σ ↦ ?_
  ext
  simp [autEmbedding_apply, conjAut_apply]

/-- Conjugation along a natural isomorphism `e : F ≅ G` of functors to finite sets, as an
isomorphism of topological groups `Aut F ≃ₜ* Aut G`. -/
noncomputable def continuousConjAut (e : F ≅ G) : Aut F ≃ₜ* Aut G where
  __ := e.conjAut
  continuous_toFun := e.continuous_conjAut
  continuous_invFun := e.symm.continuous_conjAut

@[simp]
lemma continuousConjAut_apply (e : F ≅ G) (σ : Aut F) : e.continuousConjAut σ = e.conjAut σ :=
  (rfl)

@[simp]
lemma continuousConjAut_symm_apply (e : F ≅ G) (σ : Aut G) :
    e.continuousConjAut.symm σ = e.symm.conjAut σ :=
  (rfl)

end Iso

end CategoryTheory
