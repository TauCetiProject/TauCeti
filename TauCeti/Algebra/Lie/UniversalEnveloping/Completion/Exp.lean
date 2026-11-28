/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Completion.Primitive
public import TauCeti.RingTheory.FilteredAlgebra.Exp.Basic

import TauCeti.RingTheory.FilteredAlgebra.Exp.Map
import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Exp

/-!
# Completed exponential and logarithm on graded enveloping algebras

Over a commutative `ℚ`-algebra, `completedExp` and `completedLog` exchange completed primitive
elements in the first completion ideal with completed grouplike elements congruent to `1`. For a
positively graded Lie algebra over `R`, this identifies `d.completedLie ℒ` with the
completed grouplike elements of `completedEnveloping` (`completedLieExpEquiv`).
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

section Nonneg

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ)
  [DecidableEq Γ] [GradedLieAlgebra ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝓕" => degreeFiltration ℒ d

/-- `completedCoproduct` commutes with `completedExp` on the first completion ideal. -/
@[simp]
theorem completedCoproduct_completedExp (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (x : (𝓕 hneg).completionIdeal 1) :
    completedCoproduct ℒ d hneg ((𝓕 hneg).completedExp x) =
      ((𝓕 hneg).tensorProduct R (𝓕 hneg)).completedExp
        ⟨completedCoproduct ℒ d hneg x,
          completedCoproduct_mem_completionIdeal ℒ d hneg x.property⟩ := by
  simpa only [completedCoproduct_eq_mapCompletionₐ] using
    (𝓕 hneg).mapCompletionₐ_completedExp _ (Bialgebra.comulAlgHom R U) id monotone_id
      (fun k => degreeFiltration_le_comap_comulAlgHom ℒ d hneg (k + 1))
      (degreeFiltration_le_comap_comulAlgHom ℒ d hneg 1) x

/-- Over a commutative `ℚ`-algebra, the completed exponential of an element of the first
completion ideal is completed grouplike if and only if that element is completed primitive. -/
@[simp]
theorem isCompletedGroupLike_completedExp_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (x : (𝓕 hneg).completionIdeal 1) :
    IsCompletedGroupLike ℒ d hneg ((𝓕 hneg).completedExp x) ↔
      IsCompletedPrimitive ℒ d hneg (x : completedEnveloping ℒ d hneg) := by
  let 𝒯 := (𝓕 hneg).tensorProduct R (𝓕 hneg)
  let a : 𝒯.completionIdeal 1 :=
    ⟨completedCoproduct ℒ d hneg x, completedCoproduct_mem_completionIdeal ℒ d hneg x.property⟩
  let bL : 𝒯.completionIdeal 1 := ⟨(𝓕 hneg).includeLeftCompletion R (𝓕 hneg) x,
    (𝓕 hneg).includeLeftCompletion_mem_completionIdeal R (𝓕 hneg) x.property⟩
  let bR : 𝒯.completionIdeal 1 := ⟨(𝓕 hneg).includeRightCompletion R (𝓕 hneg) x,
    (𝓕 hneg).includeRightCompletion_mem_completionIdeal R (𝓕 hneg) x.property⟩
  have hcounit : completedCounit ℒ d hneg ((𝓕 hneg).completedExp x) = 1 := by
    have h0 := completedCounit_eq_zero_of_mem_completionIdeal_one ℒ d hneg
      ((𝓕 hneg).completedExp_sub_one_mem x)
    rwa [map_sub, map_one, sub_eq_zero] at h0
  rw [isCompletedGroupLike_iff,
    isCompletedPrimitive_iff_includeLeftCompletion_add_includeRightCompletion, hcounit,
    completedCoproduct_completedExp, (𝓕 hneg).completedTensor_completedExp R (𝓕 hneg) x x]
  refine ⟨fun h => ?_, fun h => ⟨rfl, congrArg 𝒯.completedExp (Subtype.ext h)⟩⟩
  have hinj : a = bL + bR := 𝒯.completedExpEquiv.injective
    (Subtype.ext (by simpa only [AlgFiltration.coe_completedExpEquiv] using h.2))
  simpa only [a, bL, bR, AddMemClass.coe_add] using congrArg Subtype.val hinj

/-- Over a commutative `ℚ`-algebra, the completed logarithm of an element congruent to `1` modulo
the first completion ideal is completed primitive if and only if that element is completed
grouplike. -/
@[simp]
theorem isCompletedPrimitive_completedLog_iff (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    (u : {u : completedEnveloping ℒ d hneg // u - 1 ∈ (𝓕 hneg).completionIdeal 1}) :
    IsCompletedPrimitive ℒ d hneg ((𝓕 hneg).completedLog u) ↔
      IsCompletedGroupLike ℒ d hneg (u : completedEnveloping ℒ d hneg) := by
  simpa only [AlgFiltration.completedExp_completedLog, Subtype.coe_mk] using
    (isCompletedGroupLike_completedExp_iff ℒ d hneg
      ⟨(𝓕 hneg).completedLog u, (𝓕 hneg).completedLog_mem u⟩).symm

/-- For a strictly positive Lie grading over a commutative `ℚ`-algebra, `completedExp` and
`completedLog` identify the completed primitive elements with the completed grouplike elements of
`completedEnveloping`. -/
noncomputable def completedPrimitiveExpEquiv (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    completedPrimitiveLieSubalgebra ℒ d (fun n hn => hpos n hn.le) ≃
      {u : completedEnveloping ℒ d (fun n hn => hpos n hn.le) //
        IsCompletedGroupLike ℒ d (fun n hn => hpos n hn.le) u} :=
  let hneg := fun n (hn : d n < 0) => hpos n hn.le
  let e₁ : completedPrimitiveLieSubalgebra ℒ d hneg ≃
      {x : (𝓕 hneg).completionIdeal 1 //
        IsCompletedPrimitive ℒ d hneg (x : completedEnveloping ℒ d hneg)} :=
    (Equiv.subtypeEquivRight fun _ => mem_completedPrimitiveLieSubalgebra_iff ℒ d hneg).trans
      (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ (𝓕 hneg).completionIdeal 1))
        (q := IsCompletedPrimitive ℒ d hneg) fun hx => hx.mem_completionIdeal_one hpos).symm
  let e₂ : {x : (𝓕 hneg).completionIdeal 1 //
        IsCompletedPrimitive ℒ d hneg (x : completedEnveloping ℒ d hneg)} ≃
      {u : {u : completedEnveloping ℒ d hneg // u - 1 ∈ (𝓕 hneg).completionIdeal 1} //
        IsCompletedGroupLike ℒ d hneg (u : completedEnveloping ℒ d hneg)} :=
    (𝓕 hneg).completedExpEquiv.subtypeEquiv fun x => by
      simpa only [AlgFiltration.coe_completedExpEquiv] using
        (isCompletedGroupLike_completedExp_iff ℒ d hneg x).symm
  let e₃ : {u : {u : completedEnveloping ℒ d hneg // u - 1 ∈ (𝓕 hneg).completionIdeal 1} //
        IsCompletedGroupLike ℒ d hneg (u : completedEnveloping ℒ d hneg)} ≃
      {u : completedEnveloping ℒ d hneg // IsCompletedGroupLike ℒ d hneg u} :=
    Equiv.subtypeSubtypeEquivSubtype fun {u} hu => hu.sub_one_mem_completionIdeal_one hpos
  (e₁.trans e₂).trans e₃

@[simp]
theorem coe_completedPrimitiveExpEquiv (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    (x : completedPrimitiveLieSubalgebra ℒ d (fun n hn => hpos n hn.le)) :
    (completedPrimitiveExpEquiv ℒ d hpos x :
      completedEnveloping ℒ d (fun n hn => hpos n hn.le)) =
      (𝓕 (fun n hn => hpos n hn.le)).completedExp ⟨x.val,
        ((mem_completedPrimitiveLieSubalgebra_iff _ _ _).mp x.property).mem_completionIdeal_one
          hpos⟩ := by
  simp only [completedPrimitiveExpEquiv, Equiv.trans_apply,
    Equiv.subtypeSubtypeEquivSubtype_apply_coe, Equiv.subtypeEquiv_apply,
    AlgFiltration.coe_completedExpEquiv, Equiv.subtypeEquivRight_apply]
  exact congrArg _ (Subtype.ext rfl)

@[simp]
theorem coe_completedPrimitiveExpEquiv_symm (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)
    (u : {u : completedEnveloping ℒ d (fun n hn => hpos n hn.le) //
      IsCompletedGroupLike ℒ d (fun n hn => hpos n hn.le) u}) :
    ((completedPrimitiveExpEquiv ℒ d hpos).symm u :
      completedEnveloping ℒ d (fun n hn => hpos n hn.le)) =
      (𝓕 (fun n hn => hpos n hn.le)).completedLog
        ⟨u.val, u.property.sub_one_mem_completionIdeal_one hpos⟩ := by
  simp only [completedPrimitiveExpEquiv, Equiv.symm_trans_apply,
    Equiv.subtypeEquivRight_symm_apply, Equiv.symm_symm,
    Equiv.subtypeSubtypeEquivSubtype_apply_coe, Equiv.subtypeEquiv_symm,
    Equiv.subtypeEquiv_apply, AlgFiltration.coe_completedExpEquiv_symm]
  exact congrArg _ (Subtype.ext rfl)

end Nonneg

section Positive

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "Û" => completedEnveloping ℒ d.degree (d.eq_bot_of_degree_neg ℒ)
local notation "𝓕" => degreeFiltration ℒ d.degree (d.eq_bot_of_degree_neg ℒ)

/-- Over a commutative `ℚ`-algebra `R`, `completedExp ∘ completedLieToU` identifies
`d.completedLie ℒ` with the completed grouplike elements of `completedEnveloping`. -/
noncomputable def completedLieExpEquiv :
    d.completedLie ℒ ≃ {u : Û // IsCompletedGroupLike ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u} :=
  (completedPrimitiveLieEquiv d ℒ).toLinearEquiv.toEquiv.trans
    (completedPrimitiveExpEquiv ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ))

@[simp]
theorem coe_completedLieExpEquiv_apply (x : d.completedLie ℒ) :
    (completedLieExpEquiv d ℒ x : Û) =
      (𝓕).completedExp ⟨completedLieToU d ℒ x, completedLieToU_mem_completionIdeal_one d ℒ x⟩ :=
  (coe_completedPrimitiveExpEquiv ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ) _).trans <|
    congrArg ((𝓕).completedExp) (Subtype.ext (coe_completedPrimitiveLieEquiv_apply d ℒ x))

@[simp]
theorem completedLieToU_completedLieExpEquiv_symm
    (u : {u : Û // IsCompletedGroupLike ℒ d.degree (d.eq_bot_of_degree_neg ℒ) u}) :
    completedLieToU d ℒ ((completedLieExpEquiv d ℒ).symm u) =
      (𝓕).completedLog
        ⟨u.val, u.property.sub_one_mem_completionIdeal_one (d.eq_bot_of_degree_nonpos ℒ)⟩ :=
  (completedLieToU_completedPrimitiveLieEquiv_symm d ℒ _).trans
    (coe_completedPrimitiveExpEquiv_symm ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ) u)

end Positive

end TauCeti.UniversalEnvelopingAlgebra
