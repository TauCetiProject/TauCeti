/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Comparing `A⟨X₁,…,X_{k+m}⟩_U` with `A⟨X₁,…,Xₖ⟩_T⟨Y₁,…,Y_m⟩_W`

Let `A` be a Huber ring and `U` a weight family on `k + m` variables. Write `T` for its restriction
to the first `k` variables, `B` for the completion of `A⟨X₁,…,Xₖ⟩_T`, and `W` for the image in `B`
of its restriction to the last `m` variables, so that

```text
U (Fin.castAdd m i) = T i,        algebraMap A B '' U (Fin.natAdd k j) = W j.
```

Splitting the variables into these two blocks presents the completion of `A⟨X₁,…,X_{k+m}⟩_U` as
the completion of `B⟨Y₁,…,Y_m⟩_W`, an algebra in `m` variables over the algebra in `k`. This file
constructs the two comparison maps

```text
A⟨X₁,…,X_{k+m}⟩_U ⟶ A⟨X₁,…,Xₖ⟩_T⟨Y₁,…,Y_m⟩_W    and    A⟨X₁,…,Xₖ⟩_T⟨Y₁,…,Y_m⟩_W ⟶ A⟨X₁,…,X_{k+m}⟩_U
```

(all rings completed) and proves them mutually inverse, so that `A⟨X⟩_T⟨Y⟩_W ≅ A⟨X,Y⟩_U`. At the
trivial weight families this is `A⟨X⟩⟨Y⟩ ≅ A⟨X,Y⟩` for the completed algebras
`TauCeti.Huber.restrictedMvPowerSeriesCompletion`. With nontrivial weights it lets presentations by
weighted restricted series be composed over a Huber ring that is not Tate, where the weights cannot
be removed.

The first map carries `Xᵢ` to the `i`-th variable of the inner algebra read as a constant series of
the outer one when `i < k`, and to the corresponding variable of the outer algebra when `i ≥ k`.
The second carries the `j`-th variable of the outer algebra to `X_{k+j}`, and is a map over
`A⟨X₁,…,Xₖ⟩_T` through the inclusion of the first block of variables. Both come from the universal
property of completed weighted restricted series (Wedhorn, Proposition 5.50), whose hypothesis on
the variables holds because the variables of every completed `A⟨X⟩_T` satisfy it
(`TauCeti.Huber.isWeightBounded_completion_weightedX`).

## Main definitions

* `TauCeti.Huber.iterateVar`: the generators of `A⟨X₁,…,Xₖ⟩_T⟨Y₁,…,Y_m⟩_W`, indexed by
  `Fin (k + m)` as those of `A⟨X₁,…,X_{k+m}⟩_U` are.
* `TauCeti.Huber.iterateStructureHom`: the structure map `A → A⟨X₁,…,Xₖ⟩_T⟨Y₁,…,Y_m⟩_W`, the
  composite of the two the iterated algebra is built from.
* `TauCeti.Huber.iterateSplitHom`: the comparison map that splits the variables.
* `TauCeti.Huber.iterateFirstBlockHom`: the inclusion `A⟨X₁,…,Xₖ⟩_T → A⟨X₁,…,X_{k+m}⟩_U` of the
  first block, which the map below is taken over.
* `TauCeti.Huber.iterateJoinHom`: the comparison map that joins them.
* `TauCeti.Huber.iterateRingEquiv`: the isomorphism the two assemble into, with
  `TauCeti.Huber.iterateAlgEquiv` its `A`-algebra form.

## Main results

* `TauCeti.Huber.isWeightBounded_iterateVar`: the generators of the iterated algebra satisfy the
  hypothesis of Proposition 5.50 relative to the weights `U`.
* `TauCeti.Huber.continuous_iterateSplitHom` and `TauCeti.Huber.continuous_iterateJoinHom`, with
  `TauCeti.Huber.continuous_iterateFirstBlockHom`: all three are morphisms of *topological* rings.
* `TauCeti.Huber.iterateSplitHom_coe_weightedC`, `…_coe_weightedX` and their `iterateJoinHom` and
  `iterateFirstBlockHom` counterparts, with `TauCeti.Huber.iterateVar_castAdd` and
  `TauCeti.Huber.iterateVar_natAdd` for the two blocks of generators: the values on the
  generators. The bodies of the definitions are not exported, so these are how a consumer computes
  with the maps.
* `TauCeti.Huber.iterateJoinHom_comp_iterateSplitHom` and
  `TauCeti.Huber.iterateSplitHom_comp_iterateJoinHom`: the two maps are mutually inverse, with
  `TauCeti.Huber.iterateSplitHom_comp_iterateFirstBlockHom` identifying the composite of the
  splitting with the inclusion of the first block as the structure map of the iterate.
* `TauCeti.Huber.continuous_iterateRingEquiv` and its `symm`, with the `_coe` and `_apply` `@[simp]`
  lemmas: the isomorphism is one of *topological* rings, and it is `iterateSplitHom` with inverse
  `iterateJoinHom`.
* `TauCeti.Huber.iterateSplitHom_comp_algebraMap`: the comparison carries the structure map of
  `A⟨X₁,…,X_{k+m}⟩_U` to that of the iterate, which is what makes it a map of `A`-algebras. The
  iterate carries no `Algebra A` instance — `Algebra` does not compose transitively — so
  `iterateAlgEquiv` supplies the one its structure map induces, and
  `TauCeti.Huber.iterateAlgEquiv_toRingEquiv` with its two `_apply` forms says that this changes
  nothing but the bundling.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark and Definition 5.48 and
  Proposition 5.50, whose completed form all three maps apply.
-/
public section

namespace TauCeti.Huber

open UniformSpace

/-! ### Splitting the variables -/

section Iterate

variable {k m : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] {T : Fin k → Set A} (hT : IsWeightFamily T)
  {W : Fin m → Set (Completion (weightedRestrictedSubring T hT))} (hW : IsWeightFamily W)
  {U : Fin (k + m) → Set A} (hU : IsWeightFamily U)
  (hTU : ∀ i, U (Fin.castAdd m i) = T i)
  (hUW : ∀ j, algebraMap A (Completion (weightedRestrictedSubring T hT)) '' U (Fin.natAdd k j) =
    W j)

/-- The generators of `A⟨X₁,…,Xₖ⟩_T⟨Y₁,…,Y_m⟩_W`, indexed as those of `A⟨X₁,…,X_{k+m}⟩_U`. -/
noncomputable def iterateVar (i : Fin (k + m)) : Completion (weightedRestrictedSubring W hW) :=
  Fin.addCases
    (fun i ↦ ((weightedC W hW ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) : weightedRestrictedSubring W hW) :
      Completion (weightedRestrictedSubring W hW)))
    (fun j ↦ ((weightedX W hW j : weightedRestrictedSubring W hW) :
      Completion (weightedRestrictedSubring W hW)))
    i

/-- On the first block the generator is the `i`-th variable of the inner algebra, read as a
constant series of the outer one. -/
@[simp]
theorem iterateVar_castAdd (i : Fin k) :
    iterateVar hT hW (Fin.castAdd m i)
      = ((weightedC W hW ((weightedX T hT i : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT)) : weightedRestrictedSubring W hW) :
        Completion (weightedRestrictedSubring W hW)) := by
  rw [iterateVar, Fin.addCases_left]

/-- On the second block the generator is the `j`-th variable of the outer algebra. -/
@[simp]
theorem iterateVar_natAdd (j : Fin m) :
    iterateVar hT hW (Fin.natAdd k j)
      = ((weightedX W hW j : weightedRestrictedSubring W hW) :
        Completion (weightedRestrictedSubring W hW)) := by
  rw [iterateVar, Fin.addCases_right]

/-- The structure map `A → A⟨X₁,…,Xₖ⟩_T⟨Y₁,…,Y_m⟩_W`, the composite of the two structure maps the
iterated algebra is built from. -/
noncomputable def iterateStructureHom : A →+* Completion (weightedRestrictedSubring W hW) :=
  (algebraMap (Completion (weightedRestrictedSubring T hT))
    (Completion (weightedRestrictedSubring W hW))).comp
    (algebraMap A (Completion (weightedRestrictedSubring T hT)))

/-- The structure map of the iterated algebra is continuous. -/
theorem continuous_iterateStructureHom : Continuous (iterateStructureHom hT hW) :=
  (continuous_algebraMap_completion_weightedRestrictedSubring _ _ hW).comp
    (continuous_algebraMap_completion_weightedRestrictedSubring _ _ hT)

/-- The structure map of the iterated algebra is the constant series of a constant series. -/
@[simp]
theorem iterateStructureHom_apply (a : A) :
    iterateStructureHom hT hW a
      = ((weightedC W hW ((weightedC T hT a : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT)) : weightedRestrictedSubring W hW) :
        Completion (weightedRestrictedSubring W hW)) := by
  rw [iterateStructureHom, RingHom.comp_apply,
    algebraMap_completion_weightedRestrictedSubring_apply _ _ hT,
    algebraMap_completion_weightedRestrictedSubring_apply _ _ hW]

include hTU hUW in
/-- **The generators of the iterated algebra satisfy the hypothesis of Wedhorn's universal
property** relative to the weights `U`, which is what Proposition 5.50 asks of the tuple. On the
first block the weighted variables are the images of those of the inner algebra, and on the second
block they are those of the outer algebra, whose weights `W` are the images of the last weights
of `U`. -/
theorem isWeightBounded_iterateVar :
    IsWeightBounded (iterateStructureHom hT hW) U (iterateVar hT hW) := by
  refine isWeightBounded_of_isWeightedVarPowerBounded
    ((isWeightedVarPowerBounded_iff _ _ _).mpr fun l ↦ Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) l)
  · -- the weighted variable is the image of `T i · Xᵢ` under the structure map of the outer algebra
    have hset : weightedVar (iterateStructureHom hT hW) U (iterateVar hT hW) (Fin.castAdd m i) =
        algebraMap (Completion (weightedRestrictedSubring T hT))
            (Completion (weightedRestrictedSubring W hW)) ''
          weightedVar (algebraMap A (Completion (weightedRestrictedSubring T hT))) T
            (fun i ↦ ((weightedX T hT i : weightedRestrictedSubring T hT) :
              Completion (weightedRestrictedSubring T hT))) i := by
      rw [weightedVar_def, weightedVar_def, Set.image_mul, Set.image_singleton, hTU,
        iterateVar_castAdd, iterateStructureHom, RingHom.coe_comp, Set.image_comp,
        algebraMap_completion_weightedRestrictedSubring_apply _ _ hW]
    simp_rw [hset, ← Set.image_pow, ← Set.image_iUnion]
    exact IsBounded.image_algebraMap_completion_weightedRestrictedSubring hW
      ((isWeightedVarPowerBounded_iff _ _ _).mp
        (isWeightBounded_completion_weightedX hT).isWeightedVarPowerBounded i)
  · -- the weighted variable is `W j · Yⱼ`, a weighted variable of the outer algebra
    have hset : weightedVar (iterateStructureHom hT hW) U (iterateVar hT hW) (Fin.natAdd k j) =
        weightedVar (algebraMap (Completion (weightedRestrictedSubring T hT))
            (Completion (weightedRestrictedSubring W hW))) W
          (fun j ↦ ((weightedX W hW j : weightedRestrictedSubring W hW) :
            Completion (weightedRestrictedSubring W hW))) j := by
      rw [weightedVar_def, weightedVar_def, iterateVar_natAdd, iterateStructureHom,
        RingHom.coe_comp, Set.image_comp, hUW]
    rw [hset]
    exact (isWeightedVarPowerBounded_iff _ _ _).mp
      (isWeightBounded_completion_weightedX hW).isWeightedVarPowerBounded j

/-- **The comparison map `A⟨X₁,…,X_{k+m}⟩_U → A⟨X₁,…,Xₖ⟩_T⟨Y₁,…,Y_m⟩_W`.** -/
noncomputable def iterateSplitHom :
    Completion (weightedRestrictedSubring U hU) →+* Completion (weightedRestrictedSubring W hW) :=
  weightedEvalHomCompletion hU (continuous_iterateStructureHom hT hW).continuousAt
    (isWeightBounded_iterateVar hT hW hTU hUW)

/-- The comparison map is continuous. -/
theorem continuous_iterateSplitHom : Continuous (iterateSplitHom hT hW hU hTU hUW) :=
  continuous_weightedEvalHomCompletion _ _ _

/-- The comparison map sends a constant to the corresponding constant. -/
@[simp]
theorem iterateSplitHom_coe_weightedC (a : A) :
    iterateSplitHom hT hW hU hTU hUW
        ((weightedC U hU a : weightedRestrictedSubring U hU) :
          Completion (weightedRestrictedSubring U hU))
      = iterateStructureHom hT hW a := by
  rw [iterateSplitHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

/-- The comparison map sends `Xᵢ` to the `i`-th generator of the iterated algebra: for `i < k`
the `i`-th variable of the inner algebra, read as a constant of the outer one, and for `i ≥ k`
the variable of the outer algebra. -/
@[simp]
theorem iterateSplitHom_coe_weightedX (i : Fin (k + m)) :
    iterateSplitHom hT hW hU hTU hUW
        ((weightedX U hU i : weightedRestrictedSubring U hU) :
          Completion (weightedRestrictedSubring U hU))
      = iterateVar hT hW i := by
  rw [iterateSplitHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

/-! ### Joining the variables -/

include hTU in
/-- The variables of the first block satisfy the hypothesis of Wedhorn's universal property
relative to the weights `T`. -/
private theorem isWeightBounded_firstBlock :
    IsWeightBounded (algebraMap A (Completion (weightedRestrictedSubring U hU))) T
      fun i ↦ ((weightedX U hU (Fin.castAdd m i) : weightedRestrictedSubring U hU) :
        Completion (weightedRestrictedSubring U hU)) := by
  refine isWeightBounded_of_isWeightedVarPowerBounded
    ((isWeightedVarPowerBounded_iff _ _ _).mpr fun i ↦ ?_)
  simpa only [weightedVar_def, hTU] using
    (isWeightedVarPowerBounded_iff _ _ _).mp
      (isWeightBounded_completion_weightedX hU).isWeightedVarPowerBounded (Fin.castAdd m i)

/-- **The inclusion of the first block of variables**, `A⟨X₁,…,Xₖ⟩_T → A⟨X₁,…,X_{k+m}⟩_U`: the
unique continuous homomorphism over `A` carrying `Xᵢ` to `Xᵢ`. -/
noncomputable def iterateFirstBlockHom :
    Completion (weightedRestrictedSubring T hT) →+* Completion (weightedRestrictedSubring U hU) :=
  weightedEvalHomCompletion hT
    (continuous_algebraMap_completion_weightedRestrictedSubring _ _ hU).continuousAt
    (isWeightBounded_firstBlock hU hTU)

/-- The inclusion of the first block of variables is continuous. -/
theorem continuous_iterateFirstBlockHom : Continuous (iterateFirstBlockHom hT hU hTU) :=
  continuous_weightedEvalHomCompletion _ _ _

/-- The inclusion of the first block sends `Xᵢ` to `Xᵢ`. -/
@[simp]
theorem iterateFirstBlockHom_coe_weightedX (i : Fin k) :
    iterateFirstBlockHom hT hU hTU
        ((weightedX T hT i : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT))
      = ((weightedX U hU (Fin.castAdd m i) : weightedRestrictedSubring U hU) :
        Completion (weightedRestrictedSubring U hU)) := by
  rw [iterateFirstBlockHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

/-- The inclusion of the first block is a map of `A`-algebras. -/
@[simp]
theorem iterateFirstBlockHom_coe_weightedC (a : A) :
    iterateFirstBlockHom hT hU hTU
        ((weightedC T hT a : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT))
      = algebraMap A (Completion (weightedRestrictedSubring U hU)) a := by
  rw [iterateFirstBlockHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

include hUW in
/-- The variables of the second block satisfy the hypothesis of Wedhorn's universal property over
the first block, relative to the weights `W`. -/
private theorem isWeightBounded_secondBlock :
    IsWeightBounded (iterateFirstBlockHom hT hU hTU) W
      fun j ↦ ((weightedX U hU (Fin.natAdd k j) : weightedRestrictedSubring U hU) :
        Completion (weightedRestrictedSubring U hU)) := by
  -- through the inclusion of the first block, the weights `W j` are the weights `U (k + j)`
  have hcomp : (iterateFirstBlockHom hT hU hTU : _ → _) ∘
      algebraMap A (Completion (weightedRestrictedSubring T hT)) =
        algebraMap A (Completion (weightedRestrictedSubring U hU)) :=
    funext fun a ↦ by
      rw [Function.comp_apply, algebraMap_completion_weightedRestrictedSubring_apply _ _ hT,
        iterateFirstBlockHom_coe_weightedC]
  refine isWeightBounded_of_isWeightedVarPowerBounded
    ((isWeightedVarPowerBounded_iff _ _ _).mpr fun j ↦ ?_)
  simpa only [weightedVar_def, ← hUW, ← Set.image_comp, hcomp] using
    (isWeightedVarPowerBounded_iff _ _ _).mp
      (isWeightBounded_completion_weightedX hU).isWeightedVarPowerBounded (Fin.natAdd k j)

/-- **The comparison map `A⟨X₁,…,Xₖ⟩_T⟨Y₁,…,Y_m⟩_W → A⟨X₁,…,X_{k+m}⟩_U`**: the unique continuous
homomorphism over `A⟨X₁,…,Xₖ⟩_T` — through the inclusion of the first block — carrying `Y_j` to
`X_{k+j}`. -/
noncomputable def iterateJoinHom :
    Completion (weightedRestrictedSubring W hW) →+* Completion (weightedRestrictedSubring U hU) :=
  weightedEvalHomCompletion hW (continuous_iterateFirstBlockHom hT hU hTU).continuousAt
    (isWeightBounded_secondBlock hT hU hTU hUW)

/-- The join map is continuous. -/
theorem continuous_iterateJoinHom : Continuous (iterateJoinHom hT hW hU hTU hUW) :=
  continuous_weightedEvalHomCompletion _ _ _

/-- The join map sends a constant series of the outer algebra to the image of its value under the
inclusion of the first block. -/
@[simp]
theorem iterateJoinHom_coe_weightedC (c : Completion (weightedRestrictedSubring T hT)) :
    iterateJoinHom hT hW hU hTU hUW
        ((weightedC W hW c : weightedRestrictedSubring W hW) :
          Completion (weightedRestrictedSubring W hW))
      = iterateFirstBlockHom hT hU hTU c := by
  rw [iterateJoinHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

/-- The join map sends the `j`-th variable of the outer algebra to `X_{k+j}`. -/
@[simp]
theorem iterateJoinHom_coe_weightedX (j : Fin m) :
    iterateJoinHom hT hW hU hTU hUW
        ((weightedX W hW j : weightedRestrictedSubring W hW) :
          Completion (weightedRestrictedSubring W hW))
      = ((weightedX U hU (Fin.natAdd k j) : weightedRestrictedSubring U hU) :
        Completion (weightedRestrictedSubring U hU)) := by
  rw [iterateJoinHom, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

/-! ### The two maps are mutually inverse -/

/-- **Joining after splitting is the identity on `A⟨X₁,…,X_{k+m}⟩_U`.** -/
@[simp]
theorem iterateJoinHom_comp_iterateSplitHom :
    (iterateJoinHom hT hW hU hTU hUW).comp (iterateSplitHom hT hW hU hTU hUW)
      = RingHom.id (Completion (weightedRestrictedSubring U hU)) := by
  refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous hU
    ((continuous_iterateJoinHom hT hW hU hTU hUW).comp
      (continuous_iterateSplitHom hT hW hU hTU hUW)) continuous_id (fun a ↦ ?_) fun i ↦ ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      iterateSplitHom_coe_weightedC, iterateStructureHom_apply, iterateJoinHom_coe_weightedC,
      iterateFirstBlockHom_coe_weightedC,
      algebraMap_completion_weightedRestrictedSubring_apply _ _ hU]
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      iterateSplitHom_coe_weightedX]
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i
    · rw [iterateVar_castAdd, iterateJoinHom_coe_weightedC, iterateFirstBlockHom_coe_weightedX]
    · rw [iterateVar_natAdd, iterateJoinHom_coe_weightedX]

/-- Splitting after including the first block is the structure map of the iterated algebra over
`A⟨X₁,…,Xₖ⟩_T`: the two agree on the constants and on the variables of `A⟨X₁,…,Xₖ⟩_T`. -/
@[simp]
theorem iterateSplitHom_comp_iterateFirstBlockHom :
    (iterateSplitHom hT hW hU hTU hUW).comp (iterateFirstBlockHom hT hU hTU)
      = algebraMap (Completion (weightedRestrictedSubring T hT))
        (Completion (weightedRestrictedSubring W hW)) := by
  refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous hT
    ((continuous_iterateSplitHom hT hW hU hTU hUW).comp
      (continuous_iterateFirstBlockHom hT hU hTU))
    (continuous_algebraMap_completion_weightedRestrictedSubring _ _ hW) (fun a ↦ ?_) fun i ↦ ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, iterateFirstBlockHom_coe_weightedC,
      algebraMap_completion_weightedRestrictedSubring_apply _ _ hU,
      algebraMap_completion_weightedRestrictedSubring_apply _ _ hW,
      iterateSplitHom_coe_weightedC, iterateStructureHom_apply]
  · simp only [RingHom.coe_comp, Function.comp_apply, iterateFirstBlockHom_coe_weightedX,
      iterateSplitHom_coe_weightedX, iterateVar_castAdd,
      algebraMap_completion_weightedRestrictedSubring_apply _ _ hW]

/-- **Splitting after joining is the identity on `A⟨X₁,…,Xₖ⟩_T⟨Y₁,…,Y_m⟩_W`.** -/
@[simp]
theorem iterateSplitHom_comp_iterateJoinHom :
    (iterateSplitHom hT hW hU hTU hUW).comp (iterateJoinHom hT hW hU hTU hUW)
      = RingHom.id (Completion (weightedRestrictedSubring W hW)) := by
  refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous hW
    ((continuous_iterateSplitHom hT hW hU hTU hUW).comp
      (continuous_iterateJoinHom hT hW hU hTU hUW)) continuous_id (fun c ↦ ?_) fun j ↦ ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      iterateJoinHom_coe_weightedC]
    rw [← RingHom.comp_apply, iterateSplitHom_comp_iterateFirstBlockHom,
      algebraMap_completion_weightedRestrictedSubring_apply _ _ hW]
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      iterateJoinHom_coe_weightedX, iterateSplitHom_coe_weightedX, iterateVar_natAdd]

/-- **The iteration isomorphism**
`A⟨X₁,…,X_{k+m}⟩_U ≃+* A⟨X₁,…,Xₖ⟩_T⟨Y₁,…,Y_m⟩_W`. -/
noncomputable def iterateRingEquiv :
    Completion (weightedRestrictedSubring U hU) ≃+* Completion (weightedRestrictedSubring W hW) :=
  RingEquiv.ofRingHom (iterateSplitHom hT hW hU hTU hUW) (iterateJoinHom hT hW hU hTU hUW)
    (iterateSplitHom_comp_iterateJoinHom hT hW hU hTU hUW)
    (iterateJoinHom_comp_iterateSplitHom hT hW hU hTU hUW)

/-- The iteration isomorphism is `TauCeti.Huber.iterateSplitHom`. -/
@[simp]
theorem iterateRingEquiv_coe :
    ((iterateRingEquiv hT hW hU hTU hUW : Completion (weightedRestrictedSubring U hU) ≃+*
        Completion (weightedRestrictedSubring W hW)) :
      Completion (weightedRestrictedSubring U hU) →+* Completion (weightedRestrictedSubring W hW))
      = iterateSplitHom hT hW hU hTU hUW := by
  simp only [iterateRingEquiv, RingEquiv.toRingHom_ofRingHom]

/-- The pointwise form of `TauCeti.Huber.iterateRingEquiv_coe`. -/
@[simp]
theorem iterateRingEquiv_apply (x : Completion (weightedRestrictedSubring U hU)) :
    iterateRingEquiv hT hW hU hTU hUW x = iterateSplitHom hT hW hU hTU hUW x :=
  DFunLike.congr_fun (iterateRingEquiv_coe hT hW hU hTU hUW) x

/-- The inverse of the iteration isomorphism is `TauCeti.Huber.iterateJoinHom`. -/
@[simp]
theorem iterateRingEquiv_symm_coe :
    (((iterateRingEquiv hT hW hU hTU hUW).symm : Completion (weightedRestrictedSubring W hW) ≃+*
          Completion (weightedRestrictedSubring U hU)) :
      Completion (weightedRestrictedSubring W hW) →+* Completion (weightedRestrictedSubring U hU))
      = iterateJoinHom hT hW hU hTU hUW := by
  simp only [iterateRingEquiv, RingEquiv.ofRingHom_symm, RingEquiv.toRingHom_ofRingHom]

/-- The pointwise form of `TauCeti.Huber.iterateRingEquiv_symm_coe`. -/
@[simp]
theorem iterateRingEquiv_symm_apply (x : Completion (weightedRestrictedSubring W hW)) :
    (iterateRingEquiv hT hW hU hTU hUW).symm x = iterateJoinHom hT hW hU hTU hUW x :=
  DFunLike.congr_fun (iterateRingEquiv_symm_coe hT hW hU hTU hUW) x

/-- The iteration isomorphism is an isomorphism of *topological* rings. -/
theorem continuous_iterateRingEquiv : Continuous (iterateRingEquiv hT hW hU hTU hUW) :=
  (continuous_iterateSplitHom hT hW hU hTU hUW).congr fun x ↦
    (iterateRingEquiv_apply hT hW hU hTU hUW x).symm

/-- Its inverse is continuous too. -/
theorem continuous_iterateRingEquiv_symm :
    Continuous (iterateRingEquiv hT hW hU hTU hUW).symm :=
  (continuous_iterateJoinHom hT hW hU hTU hUW).congr fun x ↦
    (iterateRingEquiv_symm_apply hT hW hU hTU hUW x).symm

/-! ### As a map of `A`-algebras -/

/-- **The comparison map carries the structure map of `A⟨X₁,…,X_{k+m}⟩_U` to the structure map of
the iterated algebra**, so it is a map of `A`-algebras. -/
@[simp]
theorem iterateSplitHom_comp_algebraMap :
    (iterateSplitHom hT hW hU hTU hUW).comp
        (algebraMap A (Completion (weightedRestrictedSubring U hU)))
      = iterateStructureHom hT hW := by
  ext a
  rw [RingHom.comp_apply, algebraMap_completion_weightedRestrictedSubring_apply _ _ hU,
    iterateSplitHom_coe_weightedC]

/-- **The iteration isomorphism as an equivalence of `A`-algebras.**

The algebra structure on the iterate is the one its structure map induces: `Algebra` does not
compose transitively, so `A⟨X₁,…,Xₖ⟩_T⟨Y₁,…,Y_m⟩_W` carries no `Algebra A` instance of its own and
the statement supplies it. -/
noncomputable def iterateAlgEquiv :
    letI := (iterateStructureHom hT hW).toAlgebra
    Completion (weightedRestrictedSubring U hU) ≃ₐ[A] Completion (weightedRestrictedSubring W hW) :=
  letI := (iterateStructureHom hT hW).toAlgebra
  AlgEquiv.ofRingEquiv (f := iterateRingEquiv hT hW hU hTU hUW) fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra, iterateRingEquiv_apply, ← RingHom.comp_apply,
      iterateSplitHom_comp_algebraMap]

/-- The algebra equivalence is the ring equivalence. -/
@[simp]
theorem iterateAlgEquiv_toRingEquiv :
    letI := (iterateStructureHom hT hW).toAlgebra
    (iterateAlgEquiv hT hW hU hTU hUW).toRingEquiv = iterateRingEquiv hT hW hU hTU hUW :=
  (rfl)

/-- The pointwise form of `TauCeti.Huber.iterateAlgEquiv_toRingEquiv`. -/
@[simp]
theorem iterateAlgEquiv_apply (x : Completion (weightedRestrictedSubring U hU)) :
    letI := (iterateStructureHom hT hW).toAlgebra
    iterateAlgEquiv hT hW hU hTU hUW x = iterateRingEquiv hT hW hU hTU hUW x :=
  (rfl)

/-- The inverse of the algebra equivalence is the inverse of the ring equivalence. -/
@[simp]
theorem iterateAlgEquiv_symm_apply (x : Completion (weightedRestrictedSubring W hW)) :
    letI := (iterateStructureHom hT hW).toAlgebra
    (iterateAlgEquiv hT hW hU hTU hUW).symm x = (iterateRingEquiv hT hW hU hTU hUW).symm x :=
  (rfl)

end Iterate

end TauCeti.Huber

end
