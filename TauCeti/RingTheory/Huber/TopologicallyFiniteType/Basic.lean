/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Ideal
public import TauCeti.RingTheory.Huber.StronglyNoetherian
public import TauCeti.RingTheory.Huber.WeightedEval.Basic
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion

import TauCeti.Data.Set.Finite
import TauCeti.RingTheory.Huber.OpenMapping
import TauCeti.RingTheory.Huber.WeightedEval.Completion
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.FirstCountable
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.OfDefinition
import TauCeti.Topology.Algebra.GroupCompletion

/-!
# Homomorphisms topologically of finite type

Wedhorn's §6.6. A ring homomorphism `φ : A → B` is *topologically of finite type* when `B` is
presented as an `A`-algebra by an open quotient map out of the completion of a weighted restricted
power-series ring `A⟨X₁, …, Xₖ⟩_T` on finitely many variables, each weight `Tᵢ` finite. It is
*strictly* topologically of finite type when the trivial weight family `Tᵢ = {1}` suffices, so
that the presenting algebra is `TauCeti.Huber.restrictedMvPowerSeriesCompletion`, the object this
library writes `A⟨X₁, …, Xₖ⟩`.

The notion is what three results the adic-spaces roadmap needs are stated in terms of: the second
half of Proposition and Definition 6.36 (a Tate ring is strongly noetherian exactly when every
Tate ring topologically of finite type over it is noetherian), Remark 6.37(1), and Example 6.38,
which Proposition 8.30 cites by name.

## What is and is not assumed

Wedhorn states 6.28 and 6.29 for an `f`-adic `A` and a *complete* `f`-adic `B`. **Those standing
hypotheses are deliberately not imposed here**: the definitions ask only that `A` be a
nonarchimedean topological commutative ring — the least that lets `A⟨X⟩_T` be formed at all — and
that `B` be a topological commutative ring. The predicates are therefore defined on a wider class
than Wedhorn's, and agree with his on the class he considers. A consumer that needs completeness
of `B` should assume it alongside, not read it out of these definitions.

## Notation, and one thing it is easy to get backwards

`A⟨X₁, …, Xₖ⟩_T` names the **uncompleted** weighted ring `TauCeti.Huber.weightedRestrictedSubring`
of Wedhorn's Remark and Definition 5.48, as it does in the roadmap (`AdicSpaces/README.md`, §0.4).
Wedhorn's presenting algebra in 6.28/6.29 is its **completion**, which he writes `Â⟨…⟩`; at the
trivial weight family that completion is `restrictedMvPowerSeriesCompletion`, which this library
writes `A⟨X₁, …, Xₖ⟩` without a subscript. So the domain of `π` below is a completion throughout,
never the subring itself.

## The weighted algebra, and why not the Tate-only one

The presenting algebra is the **weighted** one. That is Wedhorn's own 6.29(i), and it is what the
roadmap asks for (`AdicSpaces/README.md`, §5.2): the Tate-only algebra is too narrow downstream,
since `A_inf` is Huber and not Tate. Definition 6.28, the strict variant, is the Tate-only case;
the implication between them is `IsStrictlyTopologicallyFiniteType.isTopologicallyFiniteType`, and
over a Tate ring the converse `IsTopologicallyFiniteType.isStrictlyTopologicallyFiniteType` holds
as well.

Two conditions on the weight family are in play and they are not the same. Wedhorn's standing
hypothesis on `T` — needed even to *form* `A⟨X⟩_T` — is `TauCeti.Huber.IsWeightFamily`, that
`Tᵢ^m · U` is a neighbourhood of zero for every `m` and every neighbourhood `U` of zero. The
phrasing in 6.29(i), that each `Tᵢ · A` is open, is the `U = ⊤` case, and is recovered from it by
`TauCeti.Huber.IsWeightFamily.isOpen_weightMul_top`; the converse is not available here (see that
lemma's docstring). Finiteness of each `Tᵢ` is a separate requirement of 6.29(i) — it is what makes
the notion one of *finite* type — and is carried explicitly, since `IsWeightFamily` does not imply
it.

## Main definitions

* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType`: Wedhorn Definition 6.28.
* `TauCeti.Huber.IsTopologicallyFiniteType`: Wedhorn Proposition and Definition 6.29(i).

## Main results

* `TauCeti.Huber.isStrictlyTopologicallyFiniteType_algebraMap`: the structure map
  `A → A⟨X₁, …, Xₖ⟩` is strictly topologically of finite type — the presentation by the identity.
* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.isTopologicallyFiniteType`: strictly
  topologically of finite type implies topologically of finite type, by the trivial weight family.
* `TauCeti.Huber.IsTopologicallyFiniteType.continuous`: such a `φ` is continuous, since it factors
  through the presenting algebra's structure map.
* `TauCeti.Huber.IsTopologicallyFiniteType.isOpen_map`: out of a Huber ring, such a `φ` carries
  open ideals to ideals generating open ideals.
* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.comp_isOpenQuotientMap` and
  `TauCeti.Huber.IsTopologicallyFiniteType.comp_isOpenQuotientMap`: both notions are stable under
  composing with a further open quotient map.
* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.quotientMk` and
  `TauCeti.Huber.IsTopologicallyFiniteType.quotientMk`: in particular, stable under passing to a
  quotient by an ideal.
* `TauCeti.Huber.IsTopologicallyFiniteType.comp_ringEquiv`: topological finite type is stable
  under precomposing with an isomorphism of topological rings of the base.
* `TauCeti.Huber.isStrictlyTopologicallyFiniteType_quotientMk_algebraMap`: every quotient of
  `A⟨X₁, …, Xₖ⟩` is strictly topologically of finite type over `A` — the shape of every Laurent
  and rational presentation.
* `TauCeti.Huber.isStrictlyTopologicallyFiniteType_id`: the identity of a complete Hausdorff
  nonarchimedean ring is strictly topologically of finite type, presented with no variables.
* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.isStronglyNoetherian`: over a strongly
  noetherian Huber ring, an algebra strictly topologically of finite type is again strongly
  noetherian.
* `TauCeti.Huber.isStrictlyTopologicallyFiniteType_of_surjective`: **over a Tate ring, a
  surjection out of `A⟨X₁, …, Xₖ⟩` that is continuous at zero is already a strict
  presentation** — openness is supplied by the open mapping theorem rather than assumed.
* `TauCeti.Huber.exists_isOpenQuotientMap_completion_weightedRestrictedSubring_append`: over a
  Huber ring the completion of `A⟨X₁, …, Xₖ⟩_T` is an open quotient of the completion of
  `A⟨X'₁, …, X'ₖ, Y₁, …, Yₘ⟩_{V, 1}`, for any weights `V` making each `Vᵢ Xᵢ` power-bounded, with
  `X'ᵢ` going to `Xᵢ` and each unweighted `Yⱼ` to a weighted variable `t Xᵢ`.
* `TauCeti.Huber.exists_isOpenQuotientMap_restrictedMvPowerSeriesCompletion`: over a Tate ring the
  completion of `A⟨X₁, …, Xₖ⟩_T` is an open quotient of an unweighted `A⟨Y₁, …, Yₘ⟩`, each `Yⱼ`
  going to a weighted variable `t Xᵢ` and every weighted variable being hit.
* `TauCeti.Huber.isStrictlyTopologicallyFiniteType_algebraMap_completion_weightedRestrictedSubring`:
  over a Tate ring the completion of `A⟨X₁, …, Xₖ⟩_T` is strictly topologically of finite type,
  presented by one variable for each element of each `Tᵢ`.
* `TauCeti.Huber.IsTopologicallyFiniteType.isStrictlyTopologicallyFiniteType` and
  `TauCeti.Huber.isStrictlyTopologicallyFiniteType_iff_isTopologicallyFiniteType`: over a Tate
  ring the two notions agree, Wedhorn Proposition 6.34.
* `TauCeti.Huber.IsTopologicallyFiniteType.isStronglyNoetherian`: over a strongly noetherian Tate
  ring, an algebra topologically of finite type is strongly noetherian.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §6.6, Definition 6.28 and
  Proposition and Definition 6.29, and Proposition 6.34.
-/

public section

namespace TauCeti.Huber

open UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {B : Type*} [CommRing B] [TopologicalSpace B]

/-- **Wedhorn Proposition and Definition 6.29(i)**: `φ : A → B` is *topologically of finite type*
when `B` is presented, as an `A`-algebra, by an open quotient map out of the completion of a
weighted restricted power-series ring on finitely many variables with each weight `Tᵢ` finite. -/
def IsTopologicallyFiniteType (φ : A →+* B) : Prop :=
  ∃ (k : ℕ) (T : Fin k → Set A) (_ : ∀ i, (T i).Finite) (hT : IsWeightFamily T)
    (π : Completion (weightedRestrictedSubring T hT) →+* B),
    IsOpenQuotientMap π ∧ π.comp (algebraMap A (Completion (weightedRestrictedSubring T hT))) = φ

/-- Unfolding lemma for the sealed definition `TauCeti.Huber.IsTopologicallyFiniteType`. -/
theorem isTopologicallyFiniteType_iff {φ : A →+* B} :
    IsTopologicallyFiniteType φ ↔
      ∃ (k : ℕ) (T : Fin k → Set A) (_ : ∀ i, (T i).Finite) (hT : IsWeightFamily T)
        (π : Completion (weightedRestrictedSubring T hT) →+* B),
        IsOpenQuotientMap π ∧
          π.comp (algebraMap A (Completion (weightedRestrictedSubring T hT))) = φ :=
  (Iff.rfl)

/-- **Wedhorn Definition 6.28**: `φ : A → B` is *strictly* topologically of finite type when the
presenting algebra can be taken to be `A⟨X₁, …, Xₖ⟩`, the trivial weight family. -/
def IsStrictlyTopologicallyFiniteType (φ : A →+* B) : Prop :=
  ∃ (k : ℕ) (π : restrictedMvPowerSeriesCompletion k A →+* B),
    IsOpenQuotientMap π ∧
      π.comp (algebraMap A (restrictedMvPowerSeriesCompletion k A)) = φ

/-- Unfolding lemma for the sealed definition
`TauCeti.Huber.IsStrictlyTopologicallyFiniteType`. -/
theorem isStrictlyTopologicallyFiniteType_iff {φ : A →+* B} :
    IsStrictlyTopologicallyFiniteType φ ↔
      ∃ (k : ℕ) (π : restrictedMvPowerSeriesCompletion k A →+* B),
        IsOpenQuotientMap π ∧
          π.comp (algebraMap A (restrictedMvPowerSeriesCompletion k A)) = φ :=
  (Iff.rfl)

/-- **The presentation by the identity**: the structure map `A → A⟨X₁, …, Xₖ⟩` is strictly
topologically of finite type. This is the witness that the conditions are simultaneously
satisfiable, and the `k = 0` case says the completion map `A → Â` is one too. -/
theorem isStrictlyTopologicallyFiniteType_algebraMap (k : ℕ) :
    IsStrictlyTopologicallyFiniteType (algebraMap A (restrictedMvPowerSeriesCompletion k A)) :=
  ⟨k, RingHom.id _, IsOpenQuotientMap.id, RingHom.id_comp _⟩

/-- The trivial weight family is finite and satisfies the standing hypothesis, so a strict
presentation is a presentation. -/
theorem IsStrictlyTopologicallyFiniteType.isTopologicallyFiniteType {φ : A →+* B}
    (h : IsStrictlyTopologicallyFiniteType φ) : IsTopologicallyFiniteType φ := by
  obtain ⟨k, π, hπ, hcomm⟩ := isStrictlyTopologicallyFiniteType_iff.mp h
  exact isTopologicallyFiniteType_iff.mpr
    ⟨k, _, fun _ ↦ Set.finite_singleton 1, isWeightFamily_one_weight, π, hπ, hcomm⟩

/-- A homomorphism topologically of finite type is continuous: it factors as an open quotient map
after the presenting algebra's structure map, and both are continuous. -/
theorem IsTopologicallyFiniteType.continuous {φ : A →+* B} (h : IsTopologicallyFiniteType φ) :
    Continuous φ := by
  obtain ⟨k, T, _, hT, π, hπ, hcomm⟩ := isTopologicallyFiniteType_iff.mp h
  rw [← hcomm]
  exact hπ.continuous.comp (continuous_algebraMap_completion_weightedRestrictedSubring k A hT)

/-! ### Stability under a further open quotient

Wedhorn presents an algebra topologically of finite type as an open quotient of a restricted
power-series ring, so composing that presentation with another open quotient map is again a
presentation of the same shape. This is what lets a *quotient* of `A⟨X₁, …, Xₖ⟩` — the form every
rational localisation and Laurent presentation takes — inherit finite type without exhibiting a
fresh presentation by hand.
-/

section OpenQuotient

variable {C : Type*} [CommRing C] [TopologicalSpace C]

/-- **A strict presentation pushes along an open quotient map.** If `φ : A → B` is strictly
topologically of finite type and `ψ : B → C` is an open quotient map, then so is `ψ ∘ φ`: compose
the presenting `A⟨X₁, …, Xₖ⟩ ↠ B` with `ψ`, and use that open quotient maps compose. -/
theorem IsStrictlyTopologicallyFiniteType.comp_isOpenQuotientMap {φ : A →+* B} {ψ : B →+* C}
    (h : IsStrictlyTopologicallyFiniteType φ) (hψ : IsOpenQuotientMap ψ) :
    IsStrictlyTopologicallyFiniteType (ψ.comp φ) := by
  obtain ⟨k, π, hπ, hcomm⟩ := isStrictlyTopologicallyFiniteType_iff.mp h
  exact isStrictlyTopologicallyFiniteType_iff.mpr
    ⟨k, ψ.comp π, hψ.comp hπ, by rw [RingHom.comp_assoc, hcomm]⟩

/-- **A presentation pushes along an open quotient map**, the weighted form of
`TauCeti.Huber.IsStrictlyTopologicallyFiniteType.comp_isOpenQuotientMap`. The weight family is
carried across unchanged; only the presenting map moves. -/
theorem IsTopologicallyFiniteType.comp_isOpenQuotientMap {φ : A →+* B} {ψ : B →+* C}
    (h : IsTopologicallyFiniteType φ) (hψ : IsOpenQuotientMap ψ) :
    IsTopologicallyFiniteType (ψ.comp φ) := by
  obtain ⟨k, T, hTfin, hT, π, hπ, hcomm⟩ := isTopologicallyFiniteType_iff.mp h
  exact isTopologicallyFiniteType_iff.mpr
    ⟨k, T, hTfin, hT, ψ.comp π, hψ.comp hπ, by rw [RingHom.comp_assoc, hcomm]⟩

variable [IsTopologicalRing B]

/-- **Strict finite type passes to a quotient by an ideal.** The quotient map of a topological
ring is an open quotient map, so this is the previous lemma at `ψ = Ideal.Quotient.mk I`. -/
theorem IsStrictlyTopologicallyFiniteType.quotientMk {φ : A →+* B}
    (h : IsStrictlyTopologicallyFiniteType φ) (I : Ideal B) :
    IsStrictlyTopologicallyFiniteType ((Ideal.Quotient.mk I).comp φ) :=
  h.comp_isOpenQuotientMap (QuotientRing.isOpenQuotientMap_mk I)

/-- **Finite type passes to a quotient by an ideal.** -/
theorem IsTopologicallyFiniteType.quotientMk {φ : A →+* B} (h : IsTopologicallyFiniteType φ)
    (I : Ideal B) : IsTopologicallyFiniteType ((Ideal.Quotient.mk I).comp φ) :=
  h.comp_isOpenQuotientMap (QuotientRing.isOpenQuotientMap_mk I)

/-- **Every quotient of `A⟨X₁, …, Xₖ⟩` is strictly topologically of finite type over `A`.** This is
the form every Laurent and rational presentation takes — Wedhorn's Examples 6.38 and 6.39 exhibit
their rings this way — so it is the statement those examples reduce to once the presenting ideal
is named. -/
theorem isStrictlyTopologicallyFiniteType_quotientMk_algebraMap (k : ℕ)
    (I : Ideal (restrictedMvPowerSeriesCompletion k A)) :
    IsStrictlyTopologicallyFiniteType
      ((Ideal.Quotient.mk I).comp (algebraMap A (restrictedMvPowerSeriesCompletion k A))) :=
  (isStrictlyTopologicallyFiniteType_algebraMap k).quotientMk I

end OpenQuotient

/-! ### Change of base along an isomorphism -/

section RingEquiv

variable {A' : Type*} [CommRing A'] [TopologicalSpace A'] [NonarchimedeanRing A']

/-- **Topological finite type is stable under precomposition with an isomorphism of topological
rings.** If `φ : A → B` is topologically of finite type and `e : A' ≃+* A` is a ring isomorphism
continuous in both directions, then `φ ∘ e : A' → B` is topologically of finite type. Compare
`TauCeti.Huber.IsTopologicallyFiniteType.comp_isOpenQuotientMap`, which changes the target rather
than the base. -/
theorem IsTopologicallyFiniteType.comp_ringEquiv {φ : A →+* B} (h : IsTopologicallyFiniteType φ)
    (e : A' ≃+* A) (he : Continuous e) (he' : Continuous e.symm) :
    IsTopologicallyFiniteType (φ.comp (e : A' →+* A)) := by
  obtain ⟨k, T, hTfin, hT, π, hπ, rfl⟩ := isTopologicallyFiniteType_iff.mp h
  -- the weights `Tᵢ` pull back to `e⁻¹(Tᵢ)`
  have hT' : IsWeightFamily fun i ↦ e.symm '' T i :=
    hT.image (φ := (e.symm : A →+* A')) he' (.of_inverse he e.symm_apply_apply e.apply_symm_apply)
  have hTS i : (e : A' →+* A) '' (e.symm '' T i) ⊆ T i := (e.image_symm_image _).le
  have hST i : (e.symm : A →+* A') '' T i ⊆ e.symm '' T i := subset_rfl
  -- the presenting algebras are identified by the isomorphism `ψ` induced by `e`
  let ψ := weightedMapCompletionEquiv e he he' hT' hT hTS hST
  have hψ : IsOpenQuotientMap ψ := Homeomorph.isOpenQuotientMap ⟨ψ.toEquiv,
    continuous_weightedMapCompletionEquiv .., continuous_weightedMapCompletionEquiv_symm ..⟩
  refine isTopologicallyFiniteType_iff.mpr ⟨k, _, fun i ↦ (hTfin i).image _, hT', π.comp ψ,
    hπ.comp hψ, RingHom.ext fun a ↦ ?_⟩
  -- `ψ` passes `he : Continuous e` for continuity of `(e : A' →+* A)`, so the lemmas about the
  -- induced maps only match once instantiated at that `he`
  simp [ψ, weightedMapCompletion_coe (φ := (e : A' →+* A)) he,
    weightedMap_weightedC (φ := (e : A' →+* A)) he]

end RingEquiv

/-! ### The identity of a complete ring -/

section Identity

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [NonarchimedeanRing R]
  [CompleteSpace R] [T0Space R]

/-- **The identity of a complete Hausdorff nonarchimedean ring is strictly topologically of finite
type**, presented in no variables. Compare the `k = 0` case of
`TauCeti.Huber.isStrictlyTopologicallyFiniteType_algebraMap`, which presents the completion map
`R → R⟨⟩` of an arbitrary `R` rather than the identity. -/
theorem isStrictlyTopologicallyFiniteType_id : IsStrictlyTopologicallyFiniteType (RingHom.id R) :=
  -- The presenting map `π : R⟨⟩ → R` is the continuous extension of the identity of `R`.
  let π := weightedEvalHomCompletion (φ := .id R) isWeightFamily_one_weight continuousAt_id
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ ![]).mpr isEmptyElim)
  -- The structure map `R → R⟨⟩` is a section of `π`.
  have hπ : Function.LeftInverse π (algebraMap R _) := fun a ↦ by simp [π]
  -- A continuous map with a continuous section is a quotient map, and a quotient map of
  -- topological groups is open.
  ⟨0, π, AddMonoidHom.isOpenQuotientMap_of_isQuotientMap <| .of_inverse
    (continuous_algebraMap_restrictedMvPowerSeriesCompletion 0 R)
    (continuous_weightedEvalHomCompletion ..) hπ, RingHom.ext hπ⟩

end Identity

/-! ### Strong noetherianness

Strong noetherianness passes from `A` to any algebra strictly topologically of finite type over
it. This is the standing hypothesis of Wedhorn's §8.2 in the form the flatness results consume:
rational localisations of a strongly noetherian ring are again strongly noetherian, once they are
known to be strictly topologically of finite type.
-/

section StronglyNoetherian

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [IsStronglyNoetherian A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B]
  [T0Space B]

/-- **Strong noetherianness passes to an algebra strictly topologically of finite type.** Over a
strongly noetherian Huber ring `A`, a complete Hausdorff nonarchimedean ring `B` admitting a map
`φ : A →+* B` strictly topologically of finite type is again strongly noetherian.

The intended use is Wedhorn's §8.2, where
`TauCeti.Huber.PairOfDefinition.flat_restrictionRingHomOfSubset_of_forall_isStronglyNoetherian`
asks that every rational localisation in a cover be strongly noetherian. Combined with a strict
finite type presentation of such a localisation over its base — the shape
`TauCeti.Huber.isStrictlyTopologicallyFiniteType_quotientMk_algebraMap` produces, and the one
Wedhorn's Examples 6.38 and 6.39 exhibit — this theorem reduces that hypothesis to strong
noetherianness of the base alone. -/
theorem IsStrictlyTopologicallyFiniteType.isStronglyNoetherian {φ : A →+* B}
    (hφ : IsStrictlyTopologicallyFiniteType φ) : IsStronglyNoetherian B := by
  obtain ⟨k, π, hπ, -⟩ := isStrictlyTopologicallyFiniteType_iff.mp hφ
  exact hπ.isStronglyNoetherian

end StronglyNoetherian

/-! ### Open ideals -/

section OpenIdeal

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B]

/-- **A homomorphism topologically of finite type out of a Huber ring carries open ideals to
ideals generating open ideals**, part of the adicity in Wedhorn's Proposition and Definition 6.29.
-/
theorem IsTopologicallyFiniteType.isOpen_map {φ : A →+* B} (h : IsTopologicallyFiniteType φ)
    {J : Ideal A} (hJ : IsOpen (J : Set A)) : IsOpen (J.map φ : Set B) := by
  obtain ⟨k, T, _, hT, π, hπ, rfl⟩ := isTopologicallyFiniteType_iff.mp h
  -- each of the three factors of the presentation carries open ideals to ideals generating open
  -- ideals: the constant series, the completion map, and the open surjection onto `B`
  have hcomp : algebraMap A (Completion (weightedRestrictedSubring T hT)) =
      Completion.coeRingHom.comp (algebraMap A (weightedRestrictedSubring T hT)) :=
    RingHom.ext fun a ↦ Completion.algebraMap_def _ _ a
  rw [← Ideal.map_map, hcomp, ← Ideal.map_map, Ideal.map_eq_image_of_surjective _ hπ.surjective]
  exact hπ.isOpenMap _ (isOpen_map_coeRingHom (isOpen_map_algebraMap_weightedRestrictedSubring hJ))

end OpenIdeal

/-! ### Presentations supplied by the open mapping theorem

Over a Tate ring a strict presentation need not be exhibited as an *open* map: **openness is
automatic**. A surjection out of `A⟨X₁, …, Xₖ⟩` onto a complete Hausdorff first countable algebra
that is continuous at zero is open, so continuity and surjectivity together already make it a
strict presentation.
-/

section OpenMappingPresentation

open Filter
open scoped Uniformity

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [IsTateRing A]
  {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [CompleteSpace B]
  [(𝓤 B).IsCountablyGenerated] [T0Space B] [Algebra A B] [ContinuousConstSMul A B]

/-- **Over a Tate ring, a surjection out of `A⟨X₁, …, Xₖ⟩` that is continuous at zero is a strict
presentation.** Openness is not a third obligation: with continuity at zero and surjectivity in
hand, Wedhorn Definition 6.28 asks for nothing more.

The hypotheses on the target are the standing hypotheses of Wedhorn's §8.2: complete, Hausdorff,
and first countable in the form of a countably generated uniformity. The source needs nothing
beyond what `A⟨X₁, …, Xₖ⟩` already carries.

The target is an arbitrary ring receiving a surjection, not the literal quotient type
`A⟨X₁, …, Xₖ⟩ ⧸ I` that
`TauCeti.Huber.isStrictlyTopologicallyFiniteType_quotientMk_algebraMap` covers. That is what a
consumer holds: a completed rational localisation is not a quotient type.

**This constructs no surjection.** Exhibiting one onto a given `B` is the work; this theorem
removes openness from the list of things that then have to be checked. -/
theorem isStrictlyTopologicallyFiniteType_of_surjective {k : ℕ}
    (π : restrictedMvPowerSeriesCompletion k A →ₐ[A] B)
    (hπ : ContinuousAt (π : restrictedMvPowerSeriesCompletion k A → B) 0)
    (hs : Function.Surjective π) :
    IsStrictlyTopologicallyFiniteType (algebraMap A B) := by
  let _ : (𝓤 (restrictedMvPowerSeriesCompletion k A)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  exact isStrictlyTopologicallyFiniteType_iff.mpr
    ⟨k, π.toRingHom, ⟨hs, continuous_of_continuousAt_zero π.toLinearMap hπ,
      IsTateRing.isOpenMap π.toLinearMap hs hπ⟩, π.comp_algebraMap⟩

end OpenMappingPresentation

/-! ### Trading weights for variables

Over a Huber ring the substitution `Y_{(i, t)} ↦ t Xᵢ`, with one unweighted variable for each
`t ∈ Tᵢ`, maps `A⟨Yⱼ⟩` openly into the completed weighted algebra `A⟨X₁, …, Xₖ⟩_T`, onto an open
subring. Adjoining the variables `Xᵢ` themselves, with any weights `Vᵢ` making `Vᵢ Xᵢ`
power-bounded, gives an open quotient map onto `A⟨X₁, …, Xₖ⟩_T`.

Over a Tate ring the weights can be removed altogether: the open subring already contains each
`Xᵢ`, since the pseudouniformiser is a unit, so `A⟨X₁, …, Xₖ⟩_T` is an open quotient of the
unweighted `A⟨Yⱼ⟩`. Consequently the two finite-type notions of Wedhorn's §6.6 coincide over a
Tate ring (Wedhorn Proposition 6.34), and strong noetherianness passes to every algebra
topologically of finite type over a strongly noetherian Tate ring, which is the input to
Corollary 8.35.
-/

section Lift

open scoped Pointwise

variable {A : Type*} [CommRing A] {k m : ℕ} {T : Fin k → Set A} {idx : Fin m → Fin k}
  {t : Fin m → A}

/-- Every weighted monomial `w Xᵛ` with `w ∈ Tᵛ` is the image of a monomial `Yᵘ` under
`Yⱼ ↦ tⱼ X_{idx j}`, once every element of every `Tᵢ` is some `tⱼ` with `idx j = i`. -/
private theorem exists_aeval_monomial_one_eq (ht : ∀ i, ∀ a ∈ T i, ∃ j, idx j = i ∧ t j = a)
    {ν : Fin k →₀ ℕ} {w : A} (hw : w ∈ weightPow T ν) :
    ∃ μ : Fin m →₀ ℕ, MvPolynomial.aeval (fun j ↦ MvPolynomial.C (t j) * MvPolynomial.X (idx j))
      (MvPolynomial.monomial μ (1 : A)) = MvPolynomial.monomial ν w := by
  classical
  set g : Fin m → MvPolynomial (Fin k) A :=
    fun j ↦ MvPolynomial.C (t j) * MvPolynomial.X (idx j) with hg
  -- the realised pairs `(ν, w)` are closed under multiplication
  have hmul : ∀ {ν₁ ν₂ : Fin k →₀ ℕ} {w₁ w₂ : A},
      (∃ μ, MvPolynomial.aeval g (MvPolynomial.monomial μ (1 : A)) =
        MvPolynomial.monomial ν₁ w₁) →
      (∃ μ, MvPolynomial.aeval g (MvPolynomial.monomial μ (1 : A)) =
        MvPolynomial.monomial ν₂ w₂) →
      ∃ μ, MvPolynomial.aeval g (MvPolynomial.monomial μ (1 : A)) =
        MvPolynomial.monomial (ν₁ + ν₂) (w₁ * w₂) := by
    rintro ν₁ ν₂ w₁ w₂ ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩
    refine ⟨μ₁ + μ₂, ?_⟩
    rw [← mul_one (1 : A), ← MvPolynomial.monomial_mul_monomial, map_mul, h₁, h₂,
      MvPolynomial.monomial_mul_monomial]
  -- a power `Tᵢⁿ` is realised by induction on `n`, one factor `tⱼ Xᵢ` at a time
  have hpow : ∀ (i : Fin k) (n : ℕ) (w : A), w ∈ T i ^ n →
      ∃ μ, MvPolynomial.aeval g (MvPolynomial.monomial μ (1 : A)) =
        MvPolynomial.monomial (Finsupp.single i n) w := by
    intro i n
    induction n with
    | zero =>
      intro w hw
      rw [pow_zero, Set.mem_one] at hw
      exact ⟨0, by simp [hw]⟩
    | succ n ihn =>
      intro w hw
      rw [pow_succ] at hw
      obtain ⟨a, ha, b, hb, rfl⟩ := hw
      obtain ⟨j, rfl, rfl⟩ := ht _ b hb
      rw [Finsupp.single_add]
      refine hmul (ihn a ha) ⟨Finsupp.single j 1, ?_⟩
      simp [hg, MvPolynomial.aeval_monomial, MvPolynomial.C_mul_X_eq_monomial]
  induction ν using Finsupp.induction generalizing w with
  | zero =>
    rw [weightPow_zero, Set.mem_one] at hw
    exact ⟨0, by simp [hw]⟩
  | single_add i n ν' _ _ ih =>
    rw [weightPow_add, weightPow_single] at hw
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hw
    exact hmul (hpow i n w₁ hw₁) (ih hw₂)

/-- **A polynomial with coefficients bounded by the weights lifts to one with coefficients in
`U`.** If every coefficient of `p` at `ν` lies in `Tᵛ · U`, then `p` is the image under
`Yⱼ ↦ tⱼ X_{idx j}` of a polynomial all of whose coefficients lie in `U`. -/
private theorem exists_aeval_eq_of_forall_coeff_mem
    (ht : ∀ i, ∀ a ∈ T i, ∃ j, idx j = i ∧ t j = a) {U : AddSubgroup A}
    (p : MvPolynomial (Fin k) A) (hp : ∀ ν, p.coeff ν ∈ weightMul T ν U) :
    ∃ q : MvPolynomial (Fin m) A, (∀ μ, q.coeff μ ∈ U) ∧
      MvPolynomial.aeval (fun j ↦ MvPolynomial.C (t j) * MvPolynomial.X (idx j)) q = p := by
  classical
  -- the polynomials with every coefficient in `U`
  let S : AddSubgroup (MvPolynomial (Fin m) A) :=
    { carrier := {q | ∀ μ, q.coeff μ ∈ U}
      add_mem' := fun ha hb μ ↦ by simpa using U.add_mem (ha μ) (hb μ)
      zero_mem' := fun _ ↦ by simp
      neg_mem' := fun ha μ ↦ by simpa using U.neg_mem (ha μ) }
  let Q := S.map (MvPolynomial.aeval
    (fun j ↦ MvPolynomial.C (t j) * MvPolynomial.X (idx j))).toAddMonoidHom
  suffices hQ : p ∈ Q by
    obtain ⟨q, hq, hqp⟩ := hQ
    exact ⟨q, hq, hqp⟩
  rw [p.as_sum]
  refine sum_mem fun ν _ ↦ ?_
  -- each weight bound `Tᵛ · U` is generated by products `w u`, and those lift monomially
  suffices hle : weightMul T ν U ≤
      Q.comap (MvPolynomial.monomial ν : A →ₗ[A] MvPolynomial (Fin k) A).toAddMonoidHom from
    hle (hp ν)
  rw [weightMul_def, AddSubgroup.closure_le]
  rintro _ ⟨w, hw, u, hu, rfl⟩
  obtain ⟨μ, hμ⟩ := exists_aeval_monomial_one_eq ht hw
  refine ⟨MvPolynomial.monomial μ u, fun μ' ↦ ?_, ?_⟩
  · rw [MvPolynomial.coeff_monomial]
    split_ifs
    exacts [hu, U.zero_mem]
  · have hu' : MvPolynomial.monomial μ u = u • MvPolynomial.monomial μ (1 : A) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
      RingHom.coe_coe, LinearMap.toAddMonoidHom_coe]
    rw [hu', map_smul, hμ, MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]

end Lift

section Substitution

open Filter Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {k m : ℕ} {T : Fin k → Set A} (hT : IsWeightFamily T) {idx : Fin m → Fin k} {t : Fin m → A}
  (htT : ∀ j, t j ∈ T (idx j))

/-- The substitution `A⟨Y₁, …, Yₘ⟩ → A⟨X₁, …, Xₖ⟩_T` (completed) sending `Yⱼ` to the
power-bounded element `tⱼ X_{idx j}`, by the universal property of `A⟨Y₁, …, Yₘ⟩`. -/
private noncomputable def weightSubst :
    restrictedMvPowerSeriesCompletion m A →+* Completion (weightedRestrictedSubring T hT) :=
  weightedEvalHomCompletion isWeightFamily_one_weight
    (continuous_algebraMap_completion_weightedRestrictedSubring k A hT).continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun j ↦
      isPowerBounded_completion_coe_of_isPowerBounded
        (isPowerBounded_weightedC_mul_weightedX hT (htT j)))

private theorem continuous_weightSubst : Continuous (weightSubst hT htT) :=
  continuous_weightedEvalHomCompletion ..

private theorem weightSubst_algebraMap (a : A) :
    weightSubst hT htT (algebraMap A (restrictedMvPowerSeriesCompletion m A) a) =
      algebraMap A (Completion (weightedRestrictedSubring T hT)) a := by
  rw [algebraMap_completion_weightedRestrictedSubring_apply, weightSubst,
    weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

/-- On polynomials, `weightSubst` is the substitution `Yⱼ ↦ tⱼ X_{idx j}` of polynomials
followed by the inclusions. -/
private theorem weightSubst_coe_weightedPolynomialHom (q : MvPolynomial (Fin m) A) :
    weightSubst hT htT (weightedPolynomialHom _ isWeightFamily_one_weight q :
        restrictedMvPowerSeriesCompletion m A) =
      (weightedPolynomialHom T hT (MvPolynomial.aeval
        (fun j ↦ MvPolynomial.C (t j) * MvPolynomial.X (idx j)) q) :
        Completion (weightedRestrictedSubring T hT)) := by
  refine congrArg (fun f : MvPolynomial (Fin m) A →+* _ ↦ f q)
    (MvPolynomial.ringHom_ext
      (f := (weightSubst hT htT).comp
        (Completion.coeRingHom.comp (weightedPolynomialHom _ isWeightFamily_one_weight)))
      (g := (Completion.coeRingHom.comp (weightedPolynomialHom T hT)).comp
        (MvPolynomial.aeval fun j ↦ MvPolynomial.C (t j) * MvPolynomial.X (idx j)).toRingHom)
      (fun a ↦ ?_) fun j ↦ ?_)
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Completion.coe_coeRingHom]
    rw [weightedPolynomialHom_C, weightedPolynomialHom_C,
      ← algebraMap_completion_weightedRestrictedSubring_apply,
      ← algebraMap_completion_weightedRestrictedSubring_apply, weightSubst_algebraMap]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_X, Completion.coe_coeRingHom, map_mul]
    rw [weightedPolynomialHom_X, weightedPolynomialHom_C, weightedPolynomialHom_X, weightSubst,
      weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]
    exact Completion.coe_mul _ _

variable {hT}

/-- A series of `A⟨X⟩_T` with coefficients bounded by `U` is a limit of images of series of
`A⟨Y⟩` with coefficients in `U`: truncate it to a polynomial and lift coefficientwise. -/
private theorem coe_mem_closure_image_weightSubst
    (ht : ∀ i, ∀ a ∈ T i, ∃ j, idx j = i ∧ t j = a) (U : OpenAddSubgroup A)
    {h : weightedRestrictedSubring T hT} (hh : h ∈ weightedNhd T hT U.toAddSubgroup) :
    (h : Completion (weightedRestrictedSubring T hT)) ∈ closure (weightSubst hT htT ''
      (((↑) : weightedRestrictedSubring (fun _ : Fin m ↦ ({1} : Set A)) isWeightFamily_one_weight →
        restrictedMvPowerSeriesCompletion m A) ''
          SetLike.coe (weightedNhd _ isWeightFamily_one_weight U.toAddSubgroup))) := by
  rw [mem_closure_iff_nhds]
  intro N hN
  have hc : Continuous fun x : weightedRestrictedSubring T hT ↦
      ((h - x : weightedRestrictedSubring T hT) : Completion (weightedRestrictedSubring T hT)) :=
    (Completion.continuous_coe _).comp (continuous_const.sub continuous_id)
  obtain ⟨V, -, hV⟩ := (hasBasis_nhds_zero_weightedTopology hT).mem_iff.mp
    (hc.continuousAt.preimage_mem_nhds (by simpa using hN))
  obtain ⟨p, hp⟩ := exists_mvPolynomial_forall_coeff_sub_mem
    (mem_weightedRestrictedSubring.mp h.2) (V ⊓ U)
  have hx : h - weightedPolynomialHom T hT p ∈ weightedNhd T hT (V ⊓ U).toAddSubgroup :=
    mem_weightedNhd.mpr fun ν ↦ by simpa using hp ν
  have hpU : ∀ ν, p.coeff ν ∈ weightMul T ν U.toAddSubgroup := fun ν ↦ by
    simpa using mem_weightedNhd.mp ((weightedNhd T hT U.toAddSubgroup).sub_mem hh
      (weightedNhd_mono (inf_le_right : V ⊓ U ≤ U) hx)) ν
  obtain ⟨q, hq, hqp⟩ := exists_aeval_eq_of_forall_coeff_mem ht p hpU
  refine ⟨(weightedPolynomialHom T hT p : Completion (weightedRestrictedSubring T hT)), ?_,
    _, ⟨weightedPolynomialHom _ isWeightFamily_one_weight q,
      mem_weightedNhd.mpr fun μ ↦ by simpa using hq μ, rfl⟩,
    by rw [weightSubst_coe_weightedPolynomialHom, hqp]⟩
  have hpN : ((h - (h - weightedPolynomialHom T hT p) : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)) ∈ N :=
    hV (weightedNhd_mono (inf_le_left : V ⊓ U ≤ V) hx)
  rwa [sub_sub_cancel] at hpN

/-- The closure of the image under `weightSubst` of a neighbourhood of zero is a neighbourhood
of zero. -/
private theorem closure_image_weightSubst_mem_nhds
    (ht : ∀ i, ∀ a ∈ T i, ∃ j, idx j = i ∧ t j = a)
    {V : Set (restrictedMvPowerSeriesCompletion m A)}
    (hV : V ∈ 𝓝 0) :
    closure (weightSubst hT htT '' V) ∈ 𝓝 (0 : Completion (weightedRestrictedSubring T hT)) := by
  obtain ⟨U, -, hU⟩ := (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).mem_iff.mp
    ((Completion.continuous_coe _).continuousAt.preimage_mem_nhds (by simpa using hV))
  have hW := Completion.isDenseInducing_coe.closure_image_mem_nhds
    ((isOpen_weightedNhd hT U.isOpen).mem_nhds (weightedNhd T hT U.toAddSubgroup).zero_mem)
  rw [Completion.coe_zero] at hW
  refine Filter.mem_of_superset hW (closure_minimal ?_ isClosed_closure)
  rintro _ ⟨h, hh, rfl⟩
  exact closure_mono (Set.image_mono (by rintro _ ⟨x, hx, rfl⟩; exact hU hx))
    (coe_mem_closure_image_weightSubst htT ht U hh)

/-- Henkel's approximation removes the closure, so `weightSubst` is an open map. -/
private theorem isOpenMap_weightSubst (ht : ∀ i, ∀ a ∈ T i, ∃ j, idx j = i ∧ t j = a) :
    IsOpenMap (weightSubst hT htT) :=
  TauCeti.isOpenMap_of_closure_image_mem_nhds (weightSubst hT htT)
    (continuous_weightSubst hT htT).continuousAt fun _ hV ↦
      closure_image_weightSubst_mem_nhds htT ht hV

end Substitution

section Huber

open Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {k m : ℕ} {T : Fin k → Set A} {hT : IsWeightFamily T} {idx : Fin m → Fin k} {t : Fin m → A}
  {V : Fin k → Set A}

/-- The values of the substitution `X'ᵢ ↦ Xᵢ`, `Yⱼ ↦ tⱼ X_{idx j}` satisfy the hypothesis of the
universal property of `A⟨X', Y⟩_{V, 1}`. -/
private theorem isWeightBounded_append (htT : ∀ j, t j ∈ T (idx j)) (hVX : IsWeightedVarPowerBounded
    (algebraMap A (Completion (weightedRestrictedSubring T hT))) V
    fun i ↦ ((weightedX T hT i : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT))) :
    IsWeightBounded (algebraMap A (Completion (weightedRestrictedSubring T hT)))
      (Fin.append V fun _ : Fin m ↦ ({1} : Set A))
      (Fin.append (fun i ↦ ((weightedX T hT i : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT)))
        fun j ↦ ((weightedC T hT (t j) * weightedX T hT (idx j) :
          weightedRestrictedSubring T hT) : Completion (weightedRestrictedSubring T hT))) := by
  refine isWeightBounded_of_isWeightedVarPowerBounded ((isWeightedVarPowerBounded_iff _ _ _).mpr
    (Fin.addCases (fun i ↦ ?_) fun j ↦ ?_))
  · simpa using (isWeightedVarPowerBounded_iff _ _ _).mp hVX i
  · refine (isPowerBounded_iff.mp (isPowerBounded_completion_coe_of_isPowerBounded
      (isPowerBounded_weightedC_mul_weightedX hT (htT j)))).subset ?_
    simp [Set.singleton_pow, Completion.coe_one]

/-- The substitution `A⟨X'₁, …, X'ₖ, Y₁, …, Yₘ⟩_{V, 1} → A⟨X₁, …, Xₖ⟩_T` (completed) sending `X'ᵢ`
to `Xᵢ` and `Yⱼ` to `tⱼ X_{idx j}`. -/
private noncomputable def appendSubst (htT : ∀ j, t j ∈ T (idx j)) (hV : IsWeightFamily V)
    (hVX : IsWeightedVarPowerBounded
    (algebraMap A (Completion (weightedRestrictedSubring T hT))) V
    fun i ↦ ((weightedX T hT i : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT))) :
    Completion (weightedRestrictedSubring (Fin.append V fun _ : Fin m ↦ ({1} : Set A))
        (hV.append isWeightFamily_one_weight)) →+*
      Completion (weightedRestrictedSubring T hT) :=
  weightedEvalHomCompletion _
    (continuous_algebraMap_completion_weightedRestrictedSubring k A hT).continuousAt
    (isWeightBounded_append htT hVX)

/-- The inclusion `A⟨Y₁, …, Yₘ⟩ → A⟨X'₁, …, X'ₖ, Y₁, …, Yₘ⟩_{V, 1}` of the unweighted block. -/
private noncomputable def appendIncl (hV : IsWeightFamily V) :
    restrictedMvPowerSeriesCompletion m A →+*
      Completion (weightedRestrictedSubring (Fin.append V fun _ : Fin m ↦ ({1} : Set A))
        (hV.append isWeightFamily_one_weight)) :=
  weightedEvalHomCompletion isWeightFamily_one_weight
    (continuous_algebraMap_completion_weightedRestrictedSubring (k + m) A _).continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun j ↦
      isPowerBounded_completion_coe_of_isPowerBounded
        (isPowerBounded_weightedX (hV.append isWeightFamily_one_weight) (i := Fin.natAdd k j)
          (by simp)))

variable {htT : ∀ j, t j ∈ T (idx j)} {hV : IsWeightFamily V} {hVX : IsWeightedVarPowerBounded
    (algebraMap A (Completion (weightedRestrictedSubring T hT))) V
    fun i ↦ ((weightedX T hT i : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT))}

private theorem appendSubst_algebraMap (a : A) :
    appendSubst htT hV hVX (algebraMap A _ a) =
      algebraMap A (Completion (weightedRestrictedSubring T hT)) a := by
  rw [algebraMap_completion_weightedRestrictedSubring_apply, appendSubst,
    weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

private theorem appendSubst_weightedX_castAdd (i : Fin k) :
    appendSubst htT hV hVX (weightedX _ (hV.append isWeightFamily_one_weight) (Fin.castAdd m i) :
        weightedRestrictedSubring _ _) =
      ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) := by
  rw [appendSubst, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX, Fin.append_left]

private theorem appendSubst_weightedX_natAdd (j : Fin m) :
    appendSubst htT hV hVX (weightedX _ (hV.append isWeightFamily_one_weight) (Fin.natAdd k j) :
        weightedRestrictedSubring _ _) =
      ((weightedC T hT (t j) * weightedX T hT (idx j) : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) := by
  rw [appendSubst, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX, Fin.append_right]

private theorem appendIncl_algebraMap (a : A) :
    appendIncl hV (algebraMap A (restrictedMvPowerSeriesCompletion m A) a) =
      algebraMap A _ a := by
  rw [algebraMap_completion_weightedRestrictedSubring_apply, appendIncl,
    weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

private theorem appendIncl_weightedX (j : Fin m) :
    appendIncl hV (weightedX _ (isWeightFamily_one_weight (A := A)) j :
        weightedRestrictedSubring _ _) =
      Completion.coe' (weightedX _ (hV.append isWeightFamily_one_weight) (Fin.natAdd k j) :
        weightedRestrictedSubring _ _) := by
  rw [appendIncl, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

private theorem weightSubst_weightedX (j : Fin m) :
    weightSubst hT htT (weightedX _ (isWeightFamily_one_weight (A := A)) j :
        weightedRestrictedSubring _ _) =
      ((weightedC T hT (t j) * weightedX T hT (idx j) : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) := by
  rw [weightSubst, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

/-- On the unweighted block the substitution is `weightSubst`. -/
private theorem appendSubst_appendIncl (x : restrictedMvPowerSeriesCompletion m A) :
    appendSubst htT hV hVX (appendIncl hV x) = weightSubst hT htT x := by
  refine DFunLike.congr_fun (completion_weightedRestrictedSubring_ringHom_ext_of_continuous
    (f := (appendSubst htT hV hVX).comp (appendIncl hV)) (g := weightSubst hT htT)
    isWeightFamily_one_weight
    ((continuous_weightedEvalHomCompletion ..).comp (continuous_weightedEvalHomCompletion ..))
    (continuous_weightSubst hT htT) (fun a ↦ ?_) fun j ↦ ?_) x
  · simp only [RingHom.comp_apply, ← algebraMap_completion_weightedRestrictedSubring_apply,
      appendIncl_algebraMap, appendSubst_algebraMap, weightSubst_algebraMap]
  · simp only [RingHom.comp_apply, appendIncl_weightedX, appendSubst_weightedX_natAdd,
      weightSubst_weightedX]

/-- The substitution is open: the image of a neighbourhood of zero contains the image under
`weightSubst` of its preimage in the unweighted block, whose closure is a neighbourhood of zero. -/
private theorem isOpenMap_appendSubst (ht : ∀ i, ∀ a ∈ T i, ∃ j, idx j = i ∧ t j = a) :
    IsOpenMap (appendSubst htT hV hVX) := by
  refine TauCeti.isOpenMap_of_closure_image_mem_nhds (appendSubst htT hV hVX)
    (continuous_weightedEvalHomCompletion ..).continuousAt fun N hN ↦ ?_
  have hN' : (appendIncl hV) ⁻¹' N ∈ 𝓝 (0 : restrictedMvPowerSeriesCompletion m A) :=
    (continuous_weightedEvalHomCompletion ..).continuousAt.preimage_mem_nhds
      (by rwa [map_zero])
  refine Filter.mem_of_superset (closure_image_weightSubst_mem_nhds htT ht hN')
    (closure_mono ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨appendIncl hV x, hx, appendSubst_appendIncl x⟩

/-- The substitution is surjective: its range is an open subring containing the constants and
every `Xᵢ`. -/
private theorem surjective_appendSubst (ht : ∀ i, ∀ a ∈ T i, ∃ j, idx j = i ∧ t j = a) :
    Function.Surjective (appendSubst htT hV hVX) :=
  mem_of_mem_nhds_of_forall_weightedX_mem hT
    ((isOpenMap_appendSubst ht).isOpen_range.mem_nhds ⟨0, map_zero _⟩)
    (fun a ↦ RingHom.mem_range.mpr ⟨_, appendSubst_algebraMap a⟩)
    fun i ↦ RingHom.mem_range.mpr ⟨_, appendSubst_weightedX_castAdd i⟩

variable (hT) in
/-- **Over a Huber ring the completed weighted algebra is an open quotient of a partly unweighted
one.** Let `T` be a finite weight family and `V` a weight family such that each weighted variable
`Vᵢ Xᵢ` is power-bounded in the completion of `A⟨X₁, …, Xₖ⟩_T`. For an enumeration
`j ↦ (idx j, t j)` of the pairs `(i, t)` with `t ∈ Tᵢ`, there is an open quotient map over `A`
from the completion of `A⟨X'₁, …, X'ₖ, Y₁, …, Yₘ⟩_{V, 1}` onto that of `A⟨X₁, …, Xₖ⟩_T`, sending
`X'ᵢ` to `Xᵢ` and `Yⱼ` to `tⱼ X_{idx j}`.

Each unweighted `Yⱼ` stands for the weighted variable `tⱼ X_{idx j}`, so the weights `T` reappear
as variables. The variables `X'ᵢ` are needed because over a general Huber ring the `tⱼ X_{idx j}`
need not generate `Xᵢ`: over `ℤ_[p]` with `T = {p}`, the series in `p X` do not contain `X`. They
may carry any weights `V` for which `Vᵢ Xᵢ` is power-bounded. Over a Tate ring the `X'ᵢ` can be
dropped:
`TauCeti.Huber.exists_isOpenQuotientMap_restrictedMvPowerSeriesCompletion`. -/
theorem exists_isOpenQuotientMap_completion_weightedRestrictedSubring_append
    (hTfin : ∀ i, (T i).Finite) (hV : IsWeightFamily V) (hVX : IsWeightedVarPowerBounded
      (algebraMap A (Completion (weightedRestrictedSubring T hT))) V
      fun i ↦ ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT))) :
    ∃ (m : ℕ) (idx : Fin m → Fin k) (t : Fin m → A), (∀ j, t j ∈ T (idx j)) ∧
      (∀ i, ∀ a ∈ T i, ∃ j, idx j = i ∧ t j = a) ∧
      ∃ θ : Completion (weightedRestrictedSubring (Fin.append V fun _ : Fin m ↦ ({1} : Set A))
          (hV.append isWeightFamily_one_weight)) →+* Completion (weightedRestrictedSubring T hT),
        IsOpenQuotientMap θ ∧
          θ.comp (algebraMap A _) = algebraMap A (Completion (weightedRestrictedSubring T hT)) ∧
          (∀ i, θ (weightedX _ (hV.append isWeightFamily_one_weight) (Fin.castAdd m i) :
              weightedRestrictedSubring _ _) =
            ((weightedX T hT i : weightedRestrictedSubring T hT) :
              Completion (weightedRestrictedSubring T hT))) ∧
          ∀ j, θ (weightedX _ (hV.append isWeightFamily_one_weight) (Fin.natAdd k j) :
              weightedRestrictedSubring _ _) =
            ((weightedC T hT (t j) * weightedX T hT (idx j) : weightedRestrictedSubring T hT) :
              Completion (weightedRestrictedSubring T hT)) := by
  obtain ⟨m, idx, t, htT, ht⟩ := Set.exists_enumeration_finite_family T hTfin
  exact ⟨m, idx, t, htT, ht, appendSubst htT hV hVX,
    ⟨surjective_appendSubst ht, continuous_weightedEvalHomCompletion .., isOpenMap_appendSubst ht⟩,
    RingHom.ext appendSubst_algebraMap, appendSubst_weightedX_castAdd,
    appendSubst_weightedX_natAdd⟩

end Huber

section Tate

open Filter Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  {k m : ℕ} {T : Fin k → Set A} {hT : IsWeightFamily T} {idx : Fin m → Fin k} {t : Fin m → A}
  (htT : ∀ j, t j ∈ T (idx j))

/-- `weightSubst` is surjective once every element of every `Tᵢ` is some `tⱼ` with
`idx j = i`. -/
private theorem surjective_weightSubst (ht : ∀ i, ∀ a ∈ T i, ∃ j, idx j = i ∧ t j = a) :
    Function.Surjective (weightSubst hT htT) := by
  -- the range `R` is an open subring; it contains every `Xᵢ`, because some `ϖⁿ Xᵢ` is small and
  -- the pseudouniformiser `ϖ` is a unit
  set R := (weightSubst hT htT).range
  have hR : (R : Set (Completion (weightedRestrictedSubring T hT))) ∈ 𝓝 0 :=
    (isOpenMap_weightSubst htT ht).isOpen_range.mem_nhds ⟨0, map_zero _⟩
  refine mem_of_mem_nhds_of_forall_weightedX_mem hT hR
    (fun a ↦ ⟨_, weightSubst_algebraMap hT htT a⟩)
    fun i ↦ ?_
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  obtain ⟨u, rfl⟩ := hϖ.isUnit
  have hc : Continuous fun a : A ↦ ((weightedC T hT a * weightedX T hT i :
      weightedRestrictedSubring T hT) : Completion (weightedRestrictedSubring T hT)) :=
    (Completion.continuous_coe _).comp ((continuous_weightedC hT).mul continuous_const)
  have hlim := (hc.tendsto 0).comp hϖ.isTopologicallyNilpotent
  rw [map_zero, zero_mul, Completion.coe_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually_mem hR).exists
  have hXi : ((weightedX T hT i : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)) =
        algebraMap A (Completion (weightedRestrictedSubring T hT)) ((↑u⁻¹ : A) ^ n) *
          ((weightedC T hT ((u : A) ^ n) * weightedX T hT i : weightedRestrictedSubring T hT) :
            Completion (weightedRestrictedSubring T hT)) := by
    rw [algebraMap_completion_weightedRestrictedSubring_apply, ← Completion.coe_mul,
      ← mul_assoc, ← map_mul, ← mul_pow, Units.inv_mul, one_pow, map_one, one_mul]
  rw [hXi]
  exact R.mul_mem ⟨_, weightSubst_algebraMap hT htT _⟩ hn

variable (hT) in
/-- **Over a Tate ring the completed weighted algebra is an open quotient of an unweighted one.**
For a finite weight family `T` there is an enumeration `j ↦ (idx j, t j)` of the pairs `(i, t)`
with `t ∈ Tᵢ`, and an open quotient map `θ : A⟨Y₁, …, Yₘ⟩ → A⟨X₁, …, Xₖ⟩_T` (completed) over `A`
sending `Yⱼ` to `tⱼ X_{idx j}`. -/
theorem exists_isOpenQuotientMap_restrictedMvPowerSeriesCompletion
    (hTfin : ∀ i, (T i).Finite) :
    ∃ (m : ℕ) (idx : Fin m → Fin k) (t : Fin m → A), (∀ j, t j ∈ T (idx j)) ∧
      (∀ i, ∀ a ∈ T i, ∃ j, idx j = i ∧ t j = a) ∧
      ∃ θ : restrictedMvPowerSeriesCompletion m A →+* Completion (weightedRestrictedSubring T hT),
        IsOpenQuotientMap θ ∧
          θ.comp (algebraMap A (restrictedMvPowerSeriesCompletion m A)) =
            algebraMap A (Completion (weightedRestrictedSubring T hT)) ∧
          ∀ j, θ (weightedX (fun _ : Fin m ↦ ({1} : Set A)) isWeightFamily_one_weight j :
              weightedRestrictedSubring _ _) =
            ((weightedC T hT (t j) * weightedX T hT (idx j) : weightedRestrictedSubring T hT) :
              Completion (weightedRestrictedSubring T hT)) := by
  obtain ⟨m, idx, t, htT, ht⟩ := Set.exists_enumeration_finite_family T hTfin
  let θ : restrictedMvPowerSeriesCompletion m A →ₐ[A] Completion (weightedRestrictedSubring T hT) :=
    { weightSubst hT htT with commutes' := weightSubst_algebraMap hT htT }
  refine ⟨m, idx, t, htT, ht, θ.toRingHom,
    ⟨surjective_weightSubst htT ht, continuous_weightSubst hT htT, isOpenMap_weightSubst htT ht⟩,
    RingHom.ext (weightSubst_algebraMap hT htT), fun j ↦ ?_⟩
  simp only [θ]
  rw [weightSubst, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

variable (hT) in
/-- **Over a Tate ring the completed weighted algebra is strictly topologically of finite type.**
For a finite weight family `T`, the completion of `A⟨X₁, …, Xₖ⟩_T` is an open quotient of an
unweighted `A⟨Y₁, …, Yₘ⟩` with one variable for each pair `(i, t)` with `t ∈ Tᵢ`, mapped to
`t Xᵢ`. -/
theorem isStrictlyTopologicallyFiniteType_algebraMap_completion_weightedRestrictedSubring
    (hTfin : ∀ i, (T i).Finite) :
    IsStrictlyTopologicallyFiniteType
      (algebraMap A (Completion (weightedRestrictedSubring T hT))) := by
  obtain ⟨m, -, -, -, -, θ, hθ, hθA, -⟩ :=
    exists_isOpenQuotientMap_restrictedMvPowerSeriesCompletion hT hTfin
  exact isStrictlyTopologicallyFiniteType_iff.mpr ⟨m, θ, hθ, hθA⟩

/-- **Over a Tate ring, topologically of finite type is strictly topologically of finite type**:
a presentation by a weighted restricted power-series algebra can be replaced by one by
`A⟨Y₁, …, Yₘ⟩`. The converse is
`TauCeti.Huber.IsStrictlyTopologicallyFiniteType.isTopologicallyFiniteType`, for any base. -/
theorem IsTopologicallyFiniteType.isStrictlyTopologicallyFiniteType {B : Type*} [CommRing B]
    [TopologicalSpace B] {φ : A →+* B} (hφ : IsTopologicallyFiniteType φ) :
    IsStrictlyTopologicallyFiniteType φ := by
  obtain ⟨k, T, hTfin, hT, π, hπ, rfl⟩ := isTopologicallyFiniteType_iff.mp hφ
  exact (isStrictlyTopologicallyFiniteType_algebraMap_completion_weightedRestrictedSubring hT
    hTfin).comp_isOpenQuotientMap hπ

/-- **Wedhorn Proposition 6.34**: over a Tate ring the two finite-type notions of Wedhorn's §6.6
agree. Wedhorn assumes `B` complete `f`-adic; no hypothesis on `B` is needed here. -/
theorem isStrictlyTopologicallyFiniteType_iff_isTopologicallyFiniteType {B : Type*} [CommRing B]
    [TopologicalSpace B] {φ : A →+* B} :
    IsStrictlyTopologicallyFiniteType φ ↔ IsTopologicallyFiniteType φ :=
  ⟨IsStrictlyTopologicallyFiniteType.isTopologicallyFiniteType,
    IsTopologicallyFiniteType.isStrictlyTopologicallyFiniteType⟩

/-- **Strong noetherianness passes to an algebra topologically of finite type over a Tate
ring.** Over a strongly noetherian Tate ring `A`, a complete Hausdorff nonarchimedean ring `B`
admitting a map `φ : A →+* B` topologically of finite type is again strongly noetherian. -/
theorem IsTopologicallyFiniteType.isStronglyNoetherian [IsStronglyNoetherian A] {B : Type*}
    [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B]
    [T0Space B] {φ : A →+* B} (hφ : IsTopologicallyFiniteType φ) : IsStronglyNoetherian B :=
  hφ.isStrictlyTopologicallyFiniteType.isStronglyNoetherian

end Tate

end TauCeti.Huber
