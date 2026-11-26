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
* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.of_isKernelPair`: the kernel pair of an étale
  morphism is an étale equivalence relation.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleEquivRel.restrict`: the restriction
  `R ×_{U × U} (U' × U')` of an étale equivalence relation on `U` along an étale morphism
  `U' ⟶ U` is an étale equivalence relation on `U'`.

## References

* [Stacks Project, Definition 39.3.1](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Lemma 39.3.2](https://stacks.math.columbia.edu/tag/02V8)
* [Stacks Project, Definition 39.3.3](https://stacks.math.columbia.edu/tag/02V9)
* [Stacks Project, Definition 65.9.2](https://stacks.math.columbia.edu/tag/02WS)
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry TauCeti.CategoryTheory

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

/-- The reflexivity morphism `e : U ⟶ R` of an étale equivalence relation, a section of both `s`
and `t`. -/
noncomputable def refl (h : EtaleEquivRel s t) : U ⟶ R :=
  h.isEquivalenceRelation.refl

@[reassoc (attr := simp)]
theorem refl_t (h : EtaleEquivRel s t) : h.refl ≫ t = 𝟙 U :=
  h.isEquivalenceRelation.reflexivity₁

@[reassoc (attr := simp)]
theorem refl_s (h : EtaleEquivRel s t) : h.refl ≫ s = 𝟙 U :=
  h.isEquivalenceRelation.reflexivity₂

/-- The symmetry morphism `i : R ⟶ R` of an étale equivalence relation, exchanging `s` and `t`. -/
noncomputable def symm (h : EtaleEquivRel s t) : R ⟶ R :=
  h.isEquivalenceRelation.symm

@[reassoc (attr := simp)]
theorem symm_t (h : EtaleEquivRel s t) : h.symm ≫ t = s :=
  h.isEquivalenceRelation.symmetry₁

@[reassoc (attr := simp)]
theorem symm_s (h : EtaleEquivRel s t) : h.symm ≫ s = t :=
  h.isEquivalenceRelation.symmetry₂

/-- The transitivity morphism `c : R ×_U R ⟶ R` of an étale equivalence relation, where the fibre
product is formed over `s` on the first factor and `t` on the second: it relates `t` of the first
point to `s` of the second. -/
noncomputable def trans (h : EtaleEquivRel s t) : pullback s t ⟶ R :=
  h.isEquivalenceRelation.trans

@[reassoc (attr := simp)]
theorem trans_t (h : EtaleEquivRel s t) : h.trans ≫ t = pullback.fst s t ≫ t :=
  h.isEquivalenceRelation.transitivity₁

@[reassoc (attr := simp)]
theorem trans_s (h : EtaleEquivRel s t) : h.trans ≫ s = pullback.snd s t ≫ s :=
  h.isEquivalenceRelation.transitivity₂

/-- The morphisms `t` and `s` of an étale equivalence relation are jointly monic. -/
theorem jointlyMono₂ (h : EtaleEquivRel s t) : JointlyMono₂ t s :=
  have := h.isEquivalenceRelation
  inferInstance

/-- Morphisms into the total space of an étale equivalence relation agree when their composites
with `t` and with `s` agree. -/
theorem hom_ext (h : EtaleEquivRel s t) {T : Scheme.{u}} {f g : T ⟶ R} (ht : f ≫ t = g ≫ t)
    (hs : f ≫ s = g ≫ s) : f = g :=
  h.isEquivalenceRelation.hom_ext ht hs

/-- Exchanging `s` and `t` in an étale equivalence relation gives an étale equivalence relation. -/
theorem swap (h : EtaleEquivRel s t) : EtaleEquivRel t s :=
  ⟨h.isEquivalenceRelation.swap, h.etale_t, h.etale_s⟩

@[reassoc (attr := simp)]
theorem symm_symm (h : EtaleEquivRel s t) : h.symm ≫ h.symm = 𝟙 R :=
  h.isEquivalenceRelation.symm_symm

@[reassoc (attr := simp)]
theorem refl_symm (h : EtaleEquivRel s t) : h.refl ≫ h.symm = h.refl :=
  h.isEquivalenceRelation.refl_symm

/-- The symmetry morphism of an étale equivalence relation is an isomorphism. -/
instance isIso_symm (h : EtaleEquivRel s t) : IsIso h.symm :=
  h.isEquivalenceRelation.isIso_symm

@[simp]
theorem inv_symm (h : EtaleEquivRel s t) : inv h.symm = h.symm :=
  h.isEquivalenceRelation.inv_symm

/-- Composing a point with the reflexivity at its `s` is the point itself. -/
@[reassoc (attr := simp)]
theorem lift_id_refl_trans (h : EtaleEquivRel s t) :
    pullback.lift (𝟙 R) (s ≫ h.refl) (by simp) ≫ h.trans = 𝟙 R :=
  h.isEquivalenceRelation.lift_id_refl_trans

/-- Composing the reflexivity at the `t` of a point with the point is the point itself. -/
@[reassoc (attr := simp)]
theorem lift_refl_id_trans (h : EtaleEquivRel s t) :
    pullback.lift (t ≫ h.refl) (𝟙 R) (by simp) ≫ h.trans = 𝟙 R :=
  h.isEquivalenceRelation.lift_refl_id_trans

/-- Composing a point with its inverse gives the reflexivity at its `t`. -/
@[reassoc (attr := simp)]
theorem lift_id_symm_trans (h : EtaleEquivRel s t) :
    pullback.lift (𝟙 R) h.symm (by simp) ≫ h.trans = t ≫ h.refl :=
  h.isEquivalenceRelation.lift_id_symm_trans

/-- Composing the inverse of a point with the point gives the reflexivity at its `s`. -/
@[reassoc (attr := simp)]
theorem lift_symm_id_trans (h : EtaleEquivRel s t) :
    pullback.lift h.symm (𝟙 R) (by simp) ≫ h.trans = s ≫ h.refl :=
  h.isEquivalenceRelation.lift_symm_id_trans

/-- The reflexivity morphism of an étale equivalence relation is étale. -/
instance etale_refl (h : EtaleEquivRel s t) : Etale h.refl :=
  have := h.etale_s
  have : Etale (h.refl ≫ s) := by rw [refl_s]; infer_instance
  Etale.of_comp h.refl s

/-- The transitivity morphism of an étale equivalence relation is étale. -/
instance etale_trans (h : EtaleEquivRel s t) : Etale h.trans :=
  have := h.etale_s
  have : Etale (h.trans ≫ s) := by rw [trans_s]; infer_instance
  Etale.of_comp h.trans s

/-- The kernel pair `t, s : R ⇉ U` of an étale morphism `f : U ⟶ X` is an étale equivalence
relation on `U`. -/
theorem of_isKernelPair {X : Scheme.{u}} {f : U ⟶ X} [Etale f] (hk : IsKernelPair f t s) :
    EtaleEquivRel s t where
  isEquivalenceRelation := hk.isEquivalenceRelation
  etale_s := MorphismProperty.of_isPullback hk ‹_›
  etale_t := MorphismProperty.of_isPullback hk.flip ‹_›

/-- On the kernel pair `t, s` of `f`, the reflexivity morphism is the diagonal `U ⟶ U ×_X U`. -/
theorem refl_eq_lift (h : EtaleEquivRel s t) {X : Scheme.{u}} {f : U ⟶ X}
    (hk : IsKernelPair f t s) : h.refl = hk.lift (𝟙 U) (𝟙 U) rfl :=
  h.isEquivalenceRelation.refl_eq_lift hk

/-- On the kernel pair `t, s` of `f`, the symmetry morphism exchanges the two factors. -/
theorem symm_eq_lift (h : EtaleEquivRel s t) {X : Scheme.{u}} {f : U ⟶ X}
    (hk : IsKernelPair f t s) : h.symm = hk.lift s t hk.w.symm :=
  h.isEquivalenceRelation.symm_eq_lift hk

/-- The diagonal `U ⟶ U × U` is an étale equivalence relation on `U`. -/
theorem id (U : Scheme.{u}) : EtaleEquivRel (𝟙 U) (𝟙 U) :=
  of_isKernelPair (IsKernelPair.id_of_mono (𝟙 U))

@[simp]
theorem id_refl (h : EtaleEquivRel (𝟙 U) (𝟙 U)) : h.refl = 𝟙 U :=
  h.isEquivalenceRelation.id_refl

@[simp]
theorem id_symm (h : EtaleEquivRel (𝟙 U) (𝟙 U)) : h.symm = 𝟙 U :=
  h.isEquivalenceRelation.id_symm

/-- The restriction of an étale equivalence relation `s, t : R ⟶ U` along an étale morphism
`g : U' ⟶ U`, the relation `R' = R ×_{U × U} (U' × U')` on `U'` with projections
`TauCeti.CategoryTheory.restrictRel.fst g t s` and `TauCeti.CategoryTheory.restrictRel.snd g t s`,
is an étale equivalence relation on `U'` (Stacks, Definition 39.3.3 (02V9) and Lemma 39.3.2
(02V8)). Étaleness of `g` is used only for the étaleness of the
projections: the restriction along any morphism is an equivalence relation
(`CategoryTheory.IsEquivalenceRelation.restrictRel`). -/
theorem restrict (h : EtaleEquivRel s t) {U' : Scheme.{u}} (g : U' ⟶ U) [Etale g] :
    EtaleEquivRel (restrictRel.snd g t s) (restrictRel.fst g t s) := by
  have := h.isEquivalenceRelation
  have := h.etale_s
  have := h.etale_t
  -- `snd` is the base change along `g` of `pullback.snd g t ≫ s` (a base change of `g` followed
  -- by `s`), and `fst` is a base change of `g` followed by one of `t`.
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [restrictRel.snd_def]
    infer_instance
  · rw [restrictRel.fst_def]
    infer_instance

end EtaleEquivRel

/-- The restriction of a pair `s, t : R ⟶ U` of morphisms of schemes with empty source `R`, along
any `g : U' ⟶ U`, has an empty total space. -/
instance isEmpty_restrictRel {R U U' : Scheme.{u}} [IsEmpty R] (g : U' ⟶ U) (s t : R ⟶ U) :
    IsEmpty ↥(restrictRel g t s) :=
  ⟨fun x ↦ isEmptyElim (restrictRel.proj g t s x)⟩

end TauCeti.AlgebraicGeometry.Spaces
