/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.CategoryTheory.EquivalenceRelation

/-!
# Étale equivalence relations on schemes

A pair of morphisms of schemes `s t : R ⟶ U` is an *étale equivalence relation* on `U` if
`j = (t, s) : R ⟶ U × U` is an equivalence relation, that is, `t` and `s` are jointly monic and
for every scheme `T` the image of `R(T)` in `U(T) × U(T)` is an equivalence relation, and `s` and
`t` are étale (Stacks, Definition 39.3.1 (022P) and Spaces, Definition 65.9.2 (02WS)). The
equivalence relation is Mathlib's internal `CategoryTheory.IsEquivalenceRelation t s`, which
`TauCeti.CategoryTheory.isEquivalenceRelation_iff` describes through points.

## Main definitions

* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel s t`: `s, t : R ⟶ U` is an étale equivalence
  relation.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.refl`, `.symm`, `.trans`: the diagonal
  `e : U ⟶ R`, the inverse `i : R ⟶ R` and the composition `c : R ×_U R ⟶ R`.

## Main results

* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.id`: the diagonal of `U` is an étale
  equivalence relation.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.ofKernelPair`: the kernel pair of an étale
  morphism is an étale equivalence relation.

## References

* [Stacks Project, Definition 39.3.1](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Definition 65.9.2](https://stacks.math.columbia.edu/tag/02WS)
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

/-- A pair of morphisms of schemes `s t : R ⟶ U` is an *étale equivalence relation* on `U` if
`(t, s) : R ⟶ U × U` is an equivalence relation and `s` and `t` are étale (Stacks, Definition
65.9.2 (02WS)). A point `r` of `R` relates `t r` to `s r`. -/
structure EtaleEquivRel {R U : Scheme.{u}} (s t : R ⟶ U) : Prop where
  /-- `(t, s) : R ⟶ U × U` is an equivalence relation. -/
  isEquivalenceRelation : IsEquivalenceRelation t s
  /-- The source morphism of an étale equivalence relation is étale. -/
  etale_s : Etale s
  /-- The target morphism of an étale equivalence relation is étale. -/
  etale_t : Etale t

namespace EtaleEquivRel

variable {R U : Scheme.{u}} {s t : R ⟶ U}

/-- A chosen internal equivalence relation structure on an étale equivalence relation. -/
noncomputable def equivalenceRelation (h : EtaleEquivRel s t) : EquivalenceRelation t s :=
  h.isEquivalenceRelation.nonempty_equivalenceRelation.some

/-- The reflexivity morphism `e : U ⟶ R` of an étale equivalence relation, a section of both `s`
and `t`. -/
noncomputable def refl (h : EtaleEquivRel s t) : U ⟶ R :=
  h.equivalenceRelation.r

@[reassoc (attr := simp)]
theorem refl_t (h : EtaleEquivRel s t) : h.refl ≫ t = 𝟙 U :=
  h.equivalenceRelation.reflexivity₁

@[reassoc (attr := simp)]
theorem refl_s (h : EtaleEquivRel s t) : h.refl ≫ s = 𝟙 U :=
  h.equivalenceRelation.reflexivity₂

/-- The symmetry morphism `i : R ⟶ R` of an étale equivalence relation, exchanging `s` and `t`. -/
noncomputable def symm (h : EtaleEquivRel s t) : R ⟶ R :=
  h.equivalenceRelation.s

@[reassoc (attr := simp)]
theorem symm_t (h : EtaleEquivRel s t) : h.symm ≫ t = s :=
  h.equivalenceRelation.symmetry₁

@[reassoc (attr := simp)]
theorem symm_s (h : EtaleEquivRel s t) : h.symm ≫ s = t :=
  h.equivalenceRelation.symmetry₂

/-- The transitivity morphism `c : R ×_U R ⟶ R` of an étale equivalence relation, where the fibre
product is formed over `s` on the first factor and `t` on the second: it relates `t` of the first
point to `s` of the second. -/
noncomputable def trans (h : EtaleEquivRel s t) : pullback s t ⟶ R :=
  (h.equivalenceRelation.isLimit.conePointUniqueUpToIso (pullbackIsPullback s t)).inv ≫
    h.equivalenceRelation.t

@[reassoc (attr := simp)]
theorem trans_t (h : EtaleEquivRel s t) : h.trans ≫ t = pullback.fst s t ≫ t := by
  simp [trans, h.equivalenceRelation.transitivity₁]

@[reassoc (attr := simp)]
theorem trans_s (h : EtaleEquivRel s t) : h.trans ≫ s = pullback.snd s t ≫ s := by
  simp [trans, h.equivalenceRelation.transitivity₂]

/-- The morphisms `t` and `s` of an étale equivalence relation are jointly monic. -/
theorem jointlyMono₂ (h : EtaleEquivRel s t) : JointlyMono₂ t s :=
  h.equivalenceRelation.toJointlyMono₂

/-- The diagonal `U ⟶ U × U` is an étale equivalence relation on `U`. -/
theorem id (U : Scheme.{u}) : EtaleEquivRel (𝟙 U) (𝟙 U) where
  isEquivalenceRelation :=
    (IsKernelPair.id_of_mono (𝟙 U)).equivalenceRelation (𝟙 U) _ _ (pullbackIsPullback _ _)
      |>.isEquivalenceRelation
  etale_s := inferInstance
  etale_t := inferInstance

/-- The kernel pair `U ×_X U ⇉ U` of an étale morphism `f : U ⟶ X` is an étale equivalence
relation on `U`. -/
theorem ofKernelPair {X : Scheme.{u}} (f : U ⟶ X) [Etale f] :
    EtaleEquivRel (pullback.snd f f) (pullback.fst f f) where
  isEquivalenceRelation := (IsKernelPair.equivalenceRelation f _ _ (pullbackIsPullback _ _)
    (IsKernelPair.of_hasPullback f)).isEquivalenceRelation
  etale_s := inferInstance
  etale_t := inferInstance

end EtaleEquivRel

end TauCeti.AlgebraicGeometry.Spaces
