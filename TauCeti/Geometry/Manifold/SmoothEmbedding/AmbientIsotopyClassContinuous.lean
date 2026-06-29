/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.AmbientIsotopyProd
public import TauCeti.Topology.Homotopy.AmbientIsotopyClassProd

/-!
# Forgetting smooth ambient-isotopy classes to continuous classes

The geometric-topology roadmap treats a geometric knot presentation as a smooth embedding, but
also insists that isotopy and ambient isotopy be defined first for arbitrary continuous maps. This
file connects the two layers: a bundled smooth embedding has an underlying continuous map, and
ambient isotopy of smooth embeddings was defined by ambient isotopy of those underlying maps, so
there is a canonical map from smooth-embedding ambient-isotopy classes to continuous
ambient-isotopy classes.

The map is deliberately only forgetful: it does not assert that every continuous class contains a
smooth representative. The product compatibility theorem records that forgetting commutes with the
already-defined product of smooth embedding classes.

## Main definitions

* `TauCeti.SmoothEmbedding.AmbientIsotopyClass.toContinuousClass`: forget a smooth-embedding
  ambient-isotopy class to the ambient-isotopy class of its underlying continuous map.
* `TauCeti.SmoothEmbedding.AmbientIsotopyClass.toContinuousClass_prodMap`: forgetting commutes
  with product classes.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff

namespace SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {H₁ : Type*} [TopologicalSpace H₁] {H₂ : Type*} [TopologicalSpace H₂]
  {G₁ : Type*} [TopologicalSpace G₁] {G₂ : Type*} [TopologicalSpace G₂]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {J₁ : ModelWithCorners 𝕜 F₁ G₁} {J₂ : ModelWithCorners 𝕜 F₂ G₂}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  {N₁ : Type*} [TopologicalSpace N₁] [ChartedSpace G₁ N₁]
  {N₂ : Type*} [TopologicalSpace N₂] [ChartedSpace G₂ N₂]
  {n : ℕ∞ω}

namespace AmbientIsotopyClass

/-- Forget a smooth-embedding ambient-isotopy class to the ambient-isotopy class of its underlying
continuous map. -/
def toContinuousClass :
    AmbientIsotopyClass I₁ J₁ n M₁ N₁ → TauCeti.AmbientIsotopyClass M₁ N₁ :=
  lift (fun f => TauCeti.AmbientIsotopyClass.mk f.toContinuousMap) fun {_ _} hfg =>
    TauCeti.AmbientIsotopyClass.mk_eq_mk
      (TauCeti.ambientIsotopic_def.2 (SmoothEmbedding.ambientIsotopic_def.1 hfg))

/-- Computation rule for `AmbientIsotopyClass.toContinuousClass` on representatives. -/
@[simp]
theorem toContinuousClass_mk (f : SmoothEmbedding I₁ J₁ n M₁ N₁) :
    toContinuousClass (mk f) = TauCeti.AmbientIsotopyClass.mk f.toContinuousMap :=
  lift_mk (fun f => TauCeti.AmbientIsotopyClass.mk f.toContinuousMap)
    (fun {_ _} hfg => TauCeti.AmbientIsotopyClass.mk_eq_mk
      (TauCeti.ambientIsotopic_def.2 (SmoothEmbedding.ambientIsotopic_def.1 hfg))) f

/-- The forgetful map to continuous ambient-isotopy classes is the unique map with the expected
value on representatives. -/
theorem toContinuousClass_unique
    (F : AmbientIsotopyClass I₁ J₁ n M₁ N₁ → TauCeti.AmbientIsotopyClass M₁ N₁)
    (hF : ∀ f : SmoothEmbedding I₁ J₁ n M₁ N₁,
      F (mk f) = TauCeti.AmbientIsotopyClass.mk f.toContinuousMap) :
    F = toContinuousClass :=
  lift_unique (fun f => TauCeti.AmbientIsotopyClass.mk f.toContinuousMap)
    (fun {_ _} hfg => TauCeti.AmbientIsotopyClass.mk_eq_mk
      (TauCeti.ambientIsotopic_def.2 (SmoothEmbedding.ambientIsotopic_def.1 hfg))) F hF

/-- Forgetting smooth ambient-isotopy classes to continuous classes commutes with products. -/
@[simp]
theorem toContinuousClass_prodMap [IsManifold I₁ n M₁] [IsManifold I₂ n M₂]
    [IsManifold J₁ n N₁] [IsManifold J₂ n N₂]
    (x : AmbientIsotopyClass I₁ J₁ n M₁ N₁)
    (y : AmbientIsotopyClass I₂ J₂ n M₂ N₂) :
    toContinuousClass (prodMap x y) =
      TauCeti.AmbientIsotopyClass.prodMap (toContinuousClass x) (toContinuousClass y) := by
  refine induction_on x ?_
  intro f
  refine induction_on y ?_
  intro g
  rw [SmoothEmbedding.AmbientIsotopyClass.prodMap_mk_mk, toContinuousClass_mk,
    toContinuousClass_mk, toContinuousClass_mk, TauCeti.AmbientIsotopyClass.prodMap_mk_mk]
  apply TauCeti.AmbientIsotopyClass.mk_eq_mk
  rw [SmoothEmbedding.toContinuousMap_prodMap]

end AmbientIsotopyClass

end SmoothEmbedding

end TauCeti
