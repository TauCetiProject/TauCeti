/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.AmbientIsotopyProd

/-!
# Ambient-isotopy classes of smooth embeddings

The geometric-topology roadmap asks for equivalence in each knot presentation, with the
geometric presentation given by smooth embeddings and equivalence given by ambient isotopy. The
previous files define ambient isotopy of bundled smooth embeddings and package it as a `Setoid`;
this file adds the quotient type and its first functorial operation.

This remains at the general manifold level. A geometric knot type such as smooth embeddings
`S¹ ↪ S³` is a later specialization of `SmoothEmbedding`, and its ambient-isotopy classes are
instances of the quotient defined here.

## Main definitions

* `TauCeti.SmoothEmbedding.AmbientIsotopyClass`: bundled smooth embeddings modulo ambient
  isotopy.
* `TauCeti.SmoothEmbedding.AmbientIsotopyClass.lift`: descend a relation-invariant function
  from embeddings to ambient-isotopy classes.
* `TauCeti.SmoothEmbedding.AmbientIsotopyClass.map`: descend a relation-preserving operation
  between smooth-embedding types to their quotients.
* `TauCeti.SmoothEmbedding.AmbientIsotopyClass.prodMap`: products of embeddings descend to
  products of ambient-isotopy classes.

The relation being quotiented follows Burde--Zieschang, *Knots*, Chapter 1, Definitions 1.1 and
1.2, via `TauCeti.Topology.Homotopy.AmbientIsotopic`.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff

namespace SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {I' : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace G M']
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

/-- Ambient-isotopy classes of bundled smooth embeddings.

This is the quotient of `SmoothEmbedding I J n M N` by the continuous ambient-isotopy relation on
the underlying maps. It is the general ambient-isotopy-class type whose special cases include
geometric knot presentations modulo ambient isotopy. -/
abbrev AmbientIsotopyClass (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H')
    (n : ℕ∞ω) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (N : Type*) [TopologicalSpace N] [ChartedSpace H' N] : Type _ :=
  Quotient (AmbientIsotopic.setoid I J n M N)

namespace AmbientIsotopyClass

variable {f g : SmoothEmbedding I J n M N}

/-- The ambient-isotopy class of a bundled smooth embedding. -/
def mk (f : SmoothEmbedding I J n M N) : AmbientIsotopyClass I J n M N :=
  Quotient.mk (AmbientIsotopic.setoid I J n M N) f

@[simp]
theorem mk_eq_mk_iff :
    mk f = mk g ↔ SmoothEmbedding.AmbientIsotopic f g := by
  change Quotient.mk (AmbientIsotopic.setoid I J n M N) f =
      Quotient.mk (AmbientIsotopic.setoid I J n M N) g ↔
    SmoothEmbedding.AmbientIsotopic f g
  rw [Quotient.eq]
  exact AmbientIsotopic.setoid_r_iff

/-- Ambient-isotopic bundled smooth embeddings determine the same ambient-isotopy class. -/
theorem mk_eq_mk (hfg : SmoothEmbedding.AmbientIsotopic f g) : mk f = mk g :=
  mk_eq_mk_iff.2 hfg

/-- Equality of ambient-isotopy classes of representatives recovers ambient isotopy. -/
theorem ambientIsotopic_of_mk_eq (hfg : mk f = mk g) :
    SmoothEmbedding.AmbientIsotopic f g :=
  mk_eq_mk_iff.1 hfg

/-- Descend a function on bundled smooth embeddings to ambient-isotopy classes.

The hypothesis says exactly that the function is invariant under ambient isotopy. -/
def lift {β : Sort*} (F : SmoothEmbedding I J n M N → β)
    (hF : ∀ ⦃f g : SmoothEmbedding I J n M N⦄,
      SmoothEmbedding.AmbientIsotopic f g → F f = F g) :
    AmbientIsotopyClass I J n M N → β :=
  Quotient.lift F fun f g hfg =>
    hF (f := f) (g := g) (AmbientIsotopic.setoid_r_iff.1 hfg)

@[simp]
theorem lift_mk {β : Sort*} (F : SmoothEmbedding I J n M N → β)
    (hF : ∀ ⦃f g : SmoothEmbedding I J n M N⦄,
      SmoothEmbedding.AmbientIsotopic f g → F f = F g) (f : SmoothEmbedding I J n M N) :
    lift F hF (mk f) = F f :=
  Quotient.lift_mk F (fun f g hfg =>
    hF (f := f) (g := g) (AmbientIsotopic.setoid_r_iff.1 hfg)) f

/-- Descend an ambient-isotopy-preserving map between bundled smooth-embedding types to their
ambient-isotopy quotients. -/
def map (F : SmoothEmbedding I J n M N → SmoothEmbedding I' J' n M' N')
    (hF : ∀ ⦃f g : SmoothEmbedding I J n M N⦄,
      SmoothEmbedding.AmbientIsotopic f g → SmoothEmbedding.AmbientIsotopic (F f) (F g)) :
    AmbientIsotopyClass I J n M N → AmbientIsotopyClass I' J' n M' N' :=
  Quotient.map F fun {f g} hfg =>
    AmbientIsotopic.setoid_r_iff.2
      (hF (f := f) (g := g) (AmbientIsotopic.setoid_r_iff.1 hfg))

@[simp]
theorem map_mk (F : SmoothEmbedding I J n M N → SmoothEmbedding I' J' n M' N')
    (hF : ∀ ⦃f g : SmoothEmbedding I J n M N⦄,
      SmoothEmbedding.AmbientIsotopic f g → SmoothEmbedding.AmbientIsotopic (F f) (F g))
    (f : SmoothEmbedding I J n M N) :
    map F hF (mk f) = mk (F f) :=
  Quotient.map_mk F (fun {f g} hfg =>
    AmbientIsotopic.setoid_r_iff.2
      (hF (f := f) (g := g) (AmbientIsotopic.setoid_r_iff.1 hfg))) f

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
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

/-- The product of ambient-isotopy classes of bundled smooth embeddings.

This is the quotient-level operation induced by `SmoothEmbedding.prodMap`, using product closure
of ambient isotopy of bundled smooth embeddings. -/
def prodMap [IsManifold I₁ n M₁] [IsManifold I₂ n M₂]
    [IsManifold J₁ n N₁] [IsManifold J₂ n N₂] :
    AmbientIsotopyClass I₁ J₁ n M₁ N₁ →
      AmbientIsotopyClass I₂ J₂ n M₂ N₂ →
        AmbientIsotopyClass (I₁.prod I₂) (J₁.prod J₂) n (M₁ × M₂) (N₁ × N₂) :=
  Quotient.map₂ (fun f g => f.prodMap g) fun {f f'} hff' {g g'} hgg' =>
    AmbientIsotopic.prodMap_setoid (f := f) (f' := f') (g := g) (g' := g') hff' hgg'

@[simp]
theorem prodMap_mk_mk [IsManifold I₁ n M₁] [IsManifold I₂ n M₂]
    [IsManifold J₁ n N₁] [IsManifold J₂ n N₂]
    (f : SmoothEmbedding I₁ J₁ n M₁ N₁) (g : SmoothEmbedding I₂ J₂ n M₂ N₂) :
    prodMap (mk f) (mk g) = mk (f.prodMap g) := by
  change
    Quotient.map₂
        (fun (f : SmoothEmbedding I₁ J₁ n M₁ N₁) (g : SmoothEmbedding I₂ J₂ n M₂ N₂) =>
          f.prodMap g)
        (fun {f f'} hff' {g g'} hgg' =>
          AmbientIsotopic.prodMap_setoid (f := f) (f' := f') (g := g) (g' := g') hff' hgg')
        (Quotient.mk (AmbientIsotopic.setoid I₁ J₁ n M₁ N₁) f)
        (Quotient.mk (AmbientIsotopic.setoid I₂ J₂ n M₂ N₂) g) =
      Quotient.mk
        (AmbientIsotopic.setoid (I₁.prod I₂) (J₁.prod J₂) n (M₁ × M₂) (N₁ × N₂))
        (f.prodMap g)
  exact Quotient.map₂_mk
    (fun (f : SmoothEmbedding I₁ J₁ n M₁ N₁) (g : SmoothEmbedding I₂ J₂ n M₂ N₂) =>
      f.prodMap g)
    (fun {f f'} hff' {g g'} hgg' =>
      AmbientIsotopic.prodMap_setoid (f := f) (f' := f') (g := g) (g' := g') hff' hgg') f g

end AmbientIsotopyClass

end SmoothEmbedding

end TauCeti
