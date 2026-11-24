/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Basic
public import TauCeti.AlgebraicGeometry.AlgebraicSpace.EtaleEquivRel

/-!
# The étale equivalence relation of an étale atlas

Let `a : h_U ⟶ F` be an étale atlas of a presheaf `F` on schemes. Since `a` is representable by
schemes, its kernel pair `h_U ×_F h_U` is represented by a scheme `R = U ×_F U`, with projections
`t = ha.relativelyRepresentable.fst' a` and `s = ha.relativelyRepresentable.snd a` to `U`. This
file shows that `(s, t)` is an étale equivalence relation on `U` in the sense of Stacks, Spaces,
Definition 65.9.2 (02WS), following parts (1) and (2) of Stacks, Spaces, Lemma 65.9.1 (0262).

`R` is not the kernel pair of a morphism of schemes, since `F` need not be a scheme, so the
kernel pair criterion `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.of_isKernelPair` does not
apply directly. Instead, `(t, s)` is an equivalence relation because `a` is relatively
representable (`CategoryTheory.Functor.relativelyRepresentable.isEquivalenceRelation`). The
projection `s` is a base change of `a`, hence étale whenever `a` is representable by étale
morphisms (surjectivity of the atlas is not needed), and `t` is `s` composed with the automorphism
of `R` exchanging the factors.

## Main results

* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.of_etale`: the kernel pair of a morphism
  representable by étale morphisms of schemes is an étale equivalence relation.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.of_etaleAtlas`: the kernel pair of an étale
  atlas is an étale equivalence relation.

## References

* [Stacks Project, Lemma 65.9.1](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Definition 65.9.2](https://stacks.math.columbia.edu/tag/02WS)
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

variable {F : SchemePresheaf.{u}} {U : Scheme.{u}} {a : yoneda.obj U ⟶ F}

/-- **The kernel pair of a morphism representable by étale morphisms is an étale equivalence
relation** (Stacks, Spaces, Lemma 65.9.1 (0262), parts (1) and (2)). If `a : h_U ⟶ F` is
representable by étale morphisms of schemes, then the scheme `U ×_F U` representing the kernel
pair of `a`, with its two projections to `U`, is an étale equivalence relation on `U`. -/
theorem EtaleEquivRel.of_etale (ha : MorphismProperty.presheaf @Etale a) :
    EtaleEquivRel (ha.rep.snd a) (ha.rep.fst' a) := by
  set hr := ha.rep
  have := ha.property_snd a
  refine ⟨hr.isEquivalenceRelation, this, ?_⟩
  rw [← hr.symmetry_snd hr]
  infer_instance

/-- **The kernel pair of an étale atlas is an étale equivalence relation** (Stacks, Spaces,
Lemma 65.9.1 (0262), parts (1) and (2)). For an étale atlas `a : h_U ⟶ F`, the scheme `U ×_F U`
representing the kernel pair of `a`, with its two projections to `U`, is an étale equivalence
relation on `U`. This is `EtaleEquivRel.of_etale` applied to the étale half of the atlas. -/
theorem EtaleEquivRel.of_etaleAtlas (ha : EtaleAtlas a) :
    EtaleEquivRel (ha.relativelyRepresentable.snd a) (ha.relativelyRepresentable.fst' a) :=
  of_etale ha.etale

end TauCeti.AlgebraicGeometry.Spaces
