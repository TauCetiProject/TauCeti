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
* `TauCeti.SmoothEmbedding.AmbientIsotopyClass.induction_on`: prove facts about classes by
  checking representatives.
* `TauCeti.SmoothEmbedding.AmbientIsotopyClass.lift`: descend a relation-invariant function
  from embeddings to ambient-isotopy classes.
* `TauCeti.SmoothEmbedding.AmbientIsotopyClass.map`: descend a relation-preserving operation
  between smooth-embedding types to their quotients.
* `TauCeti.SmoothEmbedding.AmbientIsotopyClass.lift₂` and
  `TauCeti.SmoothEmbedding.AmbientIsotopyClass.map₂`: descend binary invariant or
  relation-preserving operations.

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
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {H'' : Type*} [TopologicalSpace H'']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {G'' : Type*} [TopologicalSpace G'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {I'' : ModelWithCorners 𝕜 E'' H''} {J'' : ModelWithCorners 𝕜 F'' G''}
  {I' : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {N'' : Type*} [TopologicalSpace N''] [ChartedSpace G'' N'']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace G M']
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n n' n'' : ℕ∞ω}

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

/-- Prove a proposition about ambient-isotopy classes by checking representatives. -/
@[elab_as_elim]
theorem induction_on {motive : AmbientIsotopyClass I J n M N → Prop}
    (x : AmbientIsotopyClass I J n M N)
    (h : ∀ f : SmoothEmbedding I J n M N, motive (mk f)) : motive x :=
  Quotient.inductionOn x h

/-- Two functions out of ambient-isotopy classes are equal if they agree on representatives. -/
theorem funext {β : Sort*} {F G : AmbientIsotopyClass I J n M N → β}
    (h : ∀ f : SmoothEmbedding I J n M N, F (mk f) = G (mk f)) : F = G :=
  _root_.funext fun x => induction_on x h

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

/-- A function on ambient-isotopy classes agreeing with a descended function on representatives is
equal to that descended function. -/
theorem lift_unique {β : Sort*} (F : SmoothEmbedding I J n M N → β)
    (hF : ∀ ⦃f g : SmoothEmbedding I J n M N⦄,
      SmoothEmbedding.AmbientIsotopic f g → F f = F g)
    (G : AmbientIsotopyClass I J n M N → β)
    (hG : ∀ f : SmoothEmbedding I J n M N, G (mk f) = F f) :
    G = lift F hF :=
  funext fun f => by simp [hG f]

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

/-- Descend a binary function on bundled smooth embeddings to ambient-isotopy classes.

The hypothesis says that the function is invariant under ambient isotopy in both variables. -/
def lift₂ {β : Sort*}
    (F : SmoothEmbedding I J n M N → SmoothEmbedding I' J' n' M' N' → β)
    (hF : ∀ ⦃f f' : SmoothEmbedding I J n M N⦄,
      SmoothEmbedding.AmbientIsotopic f f' →
        ∀ ⦃g g' : SmoothEmbedding I' J' n' M' N'⦄,
          SmoothEmbedding.AmbientIsotopic g g' → F f g = F f' g') :
    AmbientIsotopyClass I J n M N → AmbientIsotopyClass I' J' n' M' N' → β :=
  Quotient.lift₂ F fun f g f' g' hff' hgg' =>
    hF (f := f) (f' := f') (AmbientIsotopic.setoid_r_iff.1 hff')
      (g := g) (g' := g') (AmbientIsotopic.setoid_r_iff.1 hgg')

/-- Computation rule for `AmbientIsotopyClass.lift₂` on representatives. -/
@[simp]
theorem lift₂_mk_mk {β : Sort*}
    (F : SmoothEmbedding I J n M N → SmoothEmbedding I' J' n' M' N' → β)
    (hF : ∀ ⦃f f' : SmoothEmbedding I J n M N⦄,
      SmoothEmbedding.AmbientIsotopic f f' →
        ∀ ⦃g g' : SmoothEmbedding I' J' n' M' N'⦄,
          SmoothEmbedding.AmbientIsotopic g g' → F f g = F f' g')
    (f : SmoothEmbedding I J n M N) (g : SmoothEmbedding I' J' n' M' N') :
    lift₂ F hF (mk f) (mk g) = F f g :=
  Quotient.lift₂_mk F (fun f g f' g' hff' hgg' =>
    hF (f := f) (f' := f') (AmbientIsotopic.setoid_r_iff.1 hff')
      (g := g) (g' := g') (AmbientIsotopic.setoid_r_iff.1 hgg')) f g

/-- Descend a binary ambient-isotopy-preserving operation between bundled smooth-embedding types to
their ambient-isotopy quotients. -/
def map₂
    (F : SmoothEmbedding I J n M N → SmoothEmbedding I' J' n' M' N' →
      SmoothEmbedding I'' J'' n'' M'' N'')
    (hF : ∀ ⦃f f' : SmoothEmbedding I J n M N⦄,
      SmoothEmbedding.AmbientIsotopic f f' →
        ∀ ⦃g g' : SmoothEmbedding I' J' n' M' N'⦄,
          SmoothEmbedding.AmbientIsotopic g g' →
            SmoothEmbedding.AmbientIsotopic (F f g) (F f' g')) :
    AmbientIsotopyClass I J n M N → AmbientIsotopyClass I' J' n' M' N' →
      AmbientIsotopyClass I'' J'' n'' M'' N'' :=
  Quotient.map₂ F fun {f f'} hff' {g g'} hgg' =>
    AmbientIsotopic.setoid_r_iff.2
      (hF (f := f) (f' := f') (AmbientIsotopic.setoid_r_iff.1 hff')
        (g := g) (g' := g') (AmbientIsotopic.setoid_r_iff.1 hgg'))

/-- Computation rule for `AmbientIsotopyClass.map₂` on representatives. -/
@[simp]
theorem map₂_mk_mk
    (F : SmoothEmbedding I J n M N → SmoothEmbedding I' J' n' M' N' →
      SmoothEmbedding I'' J'' n'' M'' N'')
    (hF : ∀ ⦃f f' : SmoothEmbedding I J n M N⦄,
      SmoothEmbedding.AmbientIsotopic f f' →
        ∀ ⦃g g' : SmoothEmbedding I' J' n' M' N'⦄,
          SmoothEmbedding.AmbientIsotopic g g' →
            SmoothEmbedding.AmbientIsotopic (F f g) (F f' g'))
    (f : SmoothEmbedding I J n M N) (g : SmoothEmbedding I' J' n' M' N') :
    map₂ F hF (mk f) (mk g) = mk (F f g) :=
  Quotient.map₂_mk F (fun {f f'} hff' {g g'} hgg' =>
    AmbientIsotopic.setoid_r_iff.2
      (hF (f := f) (f' := f') (AmbientIsotopic.setoid_r_iff.1 hff')
        (g := g) (g' := g') (AmbientIsotopic.setoid_r_iff.1 hgg'))) f g

end AmbientIsotopyClass

end SmoothEmbedding

end TauCeti
