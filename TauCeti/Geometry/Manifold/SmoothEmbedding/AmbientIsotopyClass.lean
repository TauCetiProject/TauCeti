/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.AmbientIsotopy

/-!
# Ambient-isotopy classes of smooth embeddings

The geometric-topology roadmap asks for equivalence in each knot presentation, with the
geometric presentation given by smooth embeddings and equivalence given by ambient isotopy. The
previous files define ambient isotopy of bundled smooth embeddings and package it as a `Setoid`;
this file adds the quotient type and its core functorial operations.

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
  {n n' : ℕ∞ω}

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
abbrev mk (f : SmoothEmbedding I J n M N) : AmbientIsotopyClass I J n M N :=
  Quotient.mk (AmbientIsotopic.setoid I J n M N) f

/-- Equality of two quotient representatives is equivalent to ambient isotopy of the bundled
smooth embeddings. -/
@[simp]
theorem mk_eq_mk_iff :
    mk f = mk g ↔ SmoothEmbedding.AmbientIsotopic f g := by
  rw [mk, mk, Quotient.eq]
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

/-- Computation rule for `AmbientIsotopyClass.lift` on representatives. -/
@[simp]
theorem lift_mk {β : Sort*} (F : SmoothEmbedding I J n M N → β)
    (hF : ∀ ⦃f g : SmoothEmbedding I J n M N⦄,
      SmoothEmbedding.AmbientIsotopic f g → F f = F g) (f : SmoothEmbedding I J n M N) :
    lift F hF (mk f) = F f :=
  Quotient.lift_mk F (fun f g hfg =>
    hF (f := f) (g := g) (AmbientIsotopic.setoid_r_iff.1 hfg)) f

/-- Descend an ambient-isotopy-preserving map between bundled smooth-embedding types to their
ambient-isotopy quotients. -/
def map (F : SmoothEmbedding I J n M N → SmoothEmbedding I' J' n' M' N')
    (hF : ∀ ⦃f g : SmoothEmbedding I J n M N⦄,
      SmoothEmbedding.AmbientIsotopic f g → SmoothEmbedding.AmbientIsotopic (F f) (F g)) :
    AmbientIsotopyClass I J n M N → AmbientIsotopyClass I' J' n' M' N' :=
  Quotient.map F fun {f g} hfg =>
    AmbientIsotopic.setoid_r_iff.2
      (hF (f := f) (g := g) (AmbientIsotopic.setoid_r_iff.1 hfg))

/-- Computation rule for `AmbientIsotopyClass.map` on representatives. -/
@[simp]
theorem map_mk (F : SmoothEmbedding I J n M N → SmoothEmbedding I' J' n' M' N')
    (hF : ∀ ⦃f g : SmoothEmbedding I J n M N⦄,
      SmoothEmbedding.AmbientIsotopic f g → SmoothEmbedding.AmbientIsotopic (F f) (F g))
    (f : SmoothEmbedding I J n M N) :
    map F hF (mk f) = mk (F f) :=
  Quotient.map_mk F (fun {f g} hfg =>
    AmbientIsotopic.setoid_r_iff.2
      (hF (f := f) (g := g) (AmbientIsotopic.setoid_r_iff.1 hfg))) f

end AmbientIsotopyClass

end SmoothEmbedding

end TauCeti
