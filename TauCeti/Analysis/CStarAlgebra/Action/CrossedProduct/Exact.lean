/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Quotient
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Ideal
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Surjective
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Universal

/-!
# The invariant-ideal short exact sequence of full crossed products

Let `α` be a point-norm continuous action of a locally compact group `G` on a (possibly nonunital)
C⋆-algebra `A` with left Haar measure `μ`, and let `I` be a closed `α`-invariant two-sided ideal of
`A`. Dana Williams's Proposition 3.19 states that the induced full crossed-product homomorphisms

`0 → I ⋊_α G → A ⋊_α G → (A ⧸ I) ⋊_α G → 0`

form a short exact sequence of C⋆-algebras, so `(A ⋊_α G) ⧸ (I ⋊_α G) ≃⋆ₐ[ℂ] (A ⧸ I) ⋊_α G`.

Isometric injectivity on the left (`IsInvariant.isometry_fullCrossedProductMap_subtypeHom`) and
surjectivity on the right (`CStarAction.Hom.surjective_fullCrossedProductMap`) were established
separately. Here we complete the short exact sequence by proving exactness in the middle and
constructing the resulting canonical `⋆`-isomorphisms of quotient crossed products, both for an
arbitrary surjective equivariant `q : CStarAction.Hom α β` with kernel `I` and for the concrete
quotient `α.quotient I hI`.

Exactness in the middle and the two-sided ideal kernel identifications hold without any
`T2Space G`, separability, σ-finiteness, or unitality assumption; `T2Space G` enters only where
surjectivity of `q.fullCrossedProductMap μ` is invoked. All resulting `StarAlgEquiv`s between
C⋆-algebras are automatically isometric via `StarAlgEquiv.isometry`.

## Main declarations

* `IsInvariant.crossedProductIdeal` and `IsInvariant.idealCrossedProductIdeal`: the closed two-sided
  ideal of `FullCrossedProduct α μ` formed by the embedded crossed product of a closed `α`-invariant
  ideal (bundled as `NonUnitalStarSubalgebra ℂ A` or `TwoSidedIdeal A`), together with isometric
  closed-embedding lemmas for `IsInvariant.idealSubtypeHom`.
* `TauCeti.CStarAction.fullCrossedProductMap_eq_zero_iff_mem_range_subtypeHom`,
  `TauCeti.CStarAction.Hom.ker_fullCrossedProductMap`, and
  `TauCeti.CStarAction.ker_fullCrossedProductMap_quotientMkHom`: exactness in the middle and
  two-sided ideal kernel identifications (requiring no `T2Space G` hypothesis).
* `TauCeti.CStarAction.fullCrossedProductMap_exact`,
  `TauCeti.CStarAction.fullCrossedProductMap_idealSubtypeHom_exact`, and
  `TauCeti.CStarAction.fullCrossedProductMap_quotientMkHom_exact`: the full short exact sequence of
  full crossed products (Williams, Proposition 3.19).
* `TauCeti.CStarAction.quotientFullCrossedProductEquiv`,
  `TauCeti.CStarAction.Hom.quotientIdealCrossedProductEquiv`, and
  `IsInvariant.quotientCrossedProductEquiv`: canonical `⋆`-isomorphisms identifying
  `(A ⋊_α G) ⧸ (I ⋊_α G)` with `(A ⧸ I) ⋊_α G` and `B ⋊_β G`.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 3.19.
* Iain Raeburn, *On crossed products and Takai duality*, Proc. Edinburgh Math. Soc. 31 (1988),
  321–330.
-/

public section

noncomputable section

open MeasureTheory Topology TauCeti
open scoped CStarAlgebra MultiplierAlgebra

universe u v w

/-! ### Extended integration of descended covariant pairs -/

namespace TauCeti.CStarAction

section DescendIntegration

variable {G : Type u} {A B : Type v} {C : Type w} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} {β : CStarAction G B} (μ : Measure G) [μ.IsHaarMeasure]

namespace CovariantRepresentation

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : CovariantRepresentation α H)

/-- Integrating `P.descend q hq hker` on the full crossed product factors `P.integratedFull μ`
through `q.fullCrossedProductMap μ`. -/
@[simp]
theorem integratedFull_descend_comp_fullCrossedProductMap (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 → P.coefficient a = 0) :
    ((P.descend q hq hker).integratedFull μ).comp (q.fullCrossedProductMap μ) =
      P.integratedFull μ :=
  FullCrossedProduct.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun _ => by simp

@[simp]
theorem integratedFull_descend_fullCrossedProductMap_apply (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 → P.coefficient a = 0)
    (x : FullCrossedProduct α μ) :
    (P.descend q hq hker).integratedFull μ (q.fullCrossedProductMap μ x) =
      P.integratedFull μ x :=
  DFunLike.congr_fun (P.integratedFull_descend_comp_fullCrossedProductMap μ q hq hker) x

@[simp]
theorem integratedFull_quotientLift_comp_fullCrossedProductMap (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) :
    ((P.quotientLift I hI hP).integratedFull μ).comp
        ((α.quotientMkHom I hI).fullCrossedProductMap μ) =
      P.integratedFull μ :=
  FullCrossedProduct.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun f => by
    simpa only [NonUnitalStarAlgHom.comp_apply, Hom.fullCrossedProductMap_of, integratedFull_of,
      integratedStarAlgHom_apply] using
      ((P.quotientLift I hI hP).integratedOperator_comap (α.quotientMkHom I hI) μ f).symm.trans
        (congrArg (fun Q => Q.integratedOperator μ f.ofConv)
          (P.comap_quotientLift_quotientMkHom I hI hP))

@[simp]
theorem integratedFull_quotientLift_fullCrossedProductMap_apply (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hP : ∀ a ∈ I, P.coefficient a = 0) (x : FullCrossedProduct α μ) :
    (P.quotientLift I hI hP).integratedFull μ
        ((α.quotientMkHom I hI).fullCrossedProductMap μ x) =
      P.integratedFull μ x :=
  DFunLike.congr_fun (P.integratedFull_quotientLift_comp_fullCrossedProductMap μ I hI hP) x

end CovariantRepresentation

namespace CovariantMultiplierHom

/-- `M.integratedFull μ` vanishes after `φ.fullCrossedProductMap μ` precisely when `M.coefficient`
vanishes on the range of `φ`. -/
theorem integratedFull_comp_fullCrossedProductMap_eq_zero_iff
    (M : CovariantMultiplierHom β C) (φ : Hom α β) :
    (M.integratedFull μ).comp (φ.fullCrossedProductMap μ) = 0 ↔
      ∀ a, M.coefficient (φ a) = 0 := by
  rw [M.integratedFull_comp_fullCrossedProductMap μ φ, integratedFull_eq_zero_iff,
    NonUnitalStarAlgHom.ext_iff]
  simp only [comap_coefficient, NonUnitalStarAlgHom.comp_apply, Hom.coe_toNonUnitalStarAlgHom,
    NonUnitalStarAlgHom.zero_apply]

/-- `M.integratedFull μ` vanishes on `(φ.fullCrossedProductMap μ).range` precisely when
`M.coefficient` vanishes on the range of `φ`. -/
theorem forall_mem_range_fullCrossedProductMap_integratedFull_eq_zero_iff
    (M : CovariantMultiplierHom β C) (φ : Hom α β) :
    (∀ y ∈ (φ.fullCrossedProductMap μ).range, M.integratedFull μ y = 0) ↔
      ∀ a, M.coefficient (φ a) = 0 := by
  rw [← M.integratedFull_comp_fullCrossedProductMap_eq_zero_iff μ φ, NonUnitalStarAlgHom.ext_iff]
  simp only [NonUnitalStarAlgHom.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.zero_apply]

/-- Integrating `M.descend q hq hker` on the full crossed product factors `M.integratedFull μ`
through `q.fullCrossedProductMap μ`. -/
theorem integratedFull_descend_comp_fullCrossedProductMap
    (M : CovariantMultiplierHom α C) (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → M.coefficient a = 0) :
    ((M.descend q hq hker).integratedFull μ).comp (q.fullCrossedProductMap μ) =
      M.integratedFull μ := by
  rw [integratedFull_comp_fullCrossedProductMap, M.comap_descend]

theorem integratedFull_descend_fullCrossedProductMap_apply
    (M : CovariantMultiplierHom α C) (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → M.coefficient a = 0) (x : FullCrossedProduct α μ) :
    (M.descend q hq hker).integratedFull μ (q.fullCrossedProductMap μ x) =
      M.integratedFull μ x :=
  DFunLike.congr_fun (M.integratedFull_descend_comp_fullCrossedProductMap μ q hq hker) x

theorem integratedFull_quotientLift_comp_fullCrossedProductMap
    (M : CovariantMultiplierHom α C) (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hM : ∀ a ∈ I, M.coefficient a = 0) :
    ((M.quotientLift I hI hM).integratedFull μ).comp
        ((α.quotientMkHom I hI).fullCrossedProductMap μ) =
      M.integratedFull μ := by
  rw [integratedFull_comp_fullCrossedProductMap, M.comap_quotientLift_quotientMkHom]

theorem integratedFull_quotientLift_fullCrossedProductMap_apply
    (M : CovariantMultiplierHom α C) (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (hM : ∀ a ∈ I, M.coefficient a = 0) (x : FullCrossedProduct α μ) :
    (M.quotientLift I hI hM).integratedFull μ
        ((α.quotientMkHom I hI).fullCrossedProductMap μ x) =
      M.integratedFull μ x :=
  DFunLike.congr_fun (M.integratedFull_quotientLift_comp_fullCrossedProductMap μ I hI hM) x

end CovariantMultiplierHom

end DescendIntegration

end TauCeti.CStarAction

/-! ### Closed two-sided ideals in `FullCrossedProduct` from invariant ideals -/

namespace IsInvariant

open CStarAction CStarAction.FullCrossedProduct

/-- Viewing a closed `α`-invariant two-sided ideal as a nonunital `⋆`-subalgebra preserves
invariance. -/
theorem toNonUnitalStarSubalgebra {G : Type u} {A : Type v} [Group G] [TopologicalSpace G]
    [NonUnitalCStarAlgebra A] {α : CStarAction G A} {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    _root_.IsInvariant (fun g a => α g a) (I.toNonUnitalStarSubalgebra : Set A) :=
  fun g _ ha => I.mem_toNonUnitalStarSubalgebra.mpr (hI g (I.mem_toNonUnitalStarSubalgebra.mp ha))

section StarSubalgebra

variable {G : Type u} {A B : Type v} {C : Type w} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} {β : CStarAction G B}
  {I : NonUnitalStarSubalgebra ℂ A} [IsClosed (I : Set A)]
  (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
  (μ : Measure G) [μ.IsHaarMeasure]

/-- `M.integratedFull μ` vanishes on `(hI.subtypeHom.fullCrossedProductMap μ).range` precisely when
`M.coefficient` vanishes on `I`. -/
theorem forall_mem_range_fullCrossedProductMap_subtypeHom_multiplierIntegratedFull_eq_zero_iff
    (M : CovariantMultiplierHom α C) :
    (∀ y ∈ (hI.subtypeHom.fullCrossedProductMap μ).range, M.integratedFull μ y = 0) ↔
      ∀ x ∈ I, M.coefficient x = 0 := by
  rw [M.forall_mem_range_fullCrossedProductMap_integratedFull_eq_zero_iff μ hI.subtypeHom]
  simp only [subtypeHom_apply, Subtype.forall]

/-- When `q : Hom α β` vanishes on `I`, the composite of the induced full crossed-product maps is
zero. -/
theorem fullCrossedProductMap_comp_subtypeHom_eq_zero (q : Hom α β) (hqI : ∀ a ∈ I, q a = 0) :
    (q.fullCrossedProductMap μ).comp (hI.subtypeHom.fullCrossedProductMap μ) = 0 := by
  refine FullCrossedProduct.starAlgHom_ext <| NonUnitalStarAlgHom.ext fun f => ?_
  have hconv : q.convolutionMap μ (hI.subtypeHom.convolutionMap μ f) = 0 := by
    ext s
    simpa using hqI (f.ofConv s) (f.ofConv s).2
  simp [hconv]

/-- If `q : Hom α β` vanishes on `I`, then `q.fullCrossedProductMap μ` vanishes on every element
embedded from `FullCrossedProduct hI.restrict μ`. -/
theorem fullCrossedProductMap_subtypeHom_apply_eq_zero (q : Hom α β) (hqI : ∀ a ∈ I, q a = 0)
    (x : FullCrossedProduct hI.restrict μ) :
    q.fullCrossedProductMap μ (hI.subtypeHom.fullCrossedProductMap μ x) = 0 :=
  DFunLike.congr_fun (hI.fullCrossedProductMap_comp_subtypeHom_eq_zero μ q hqI) x

/-- The closed two-sided ideal of `FullCrossedProduct α μ` formed by the embedded full crossed
product of a closed `α`-invariant two-sided star ideal `I`. -/
def crossedProductIdeal (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    TwoSidedIdeal (FullCrossedProduct α μ) :=
  TwoSidedIdeal.mk' ((hI.subtypeHom.fullCrossedProductMap μ).range : Set (FullCrossedProduct α μ))
    (hI.subtypeHom.fullCrossedProductMap μ).range.zero_mem
    (fun hx hy => (hI.subtypeHom.fullCrossedProductMap μ).range.add_mem hx hy)
    (fun hx => (hI.subtypeHom.fullCrossedProductMap μ).range.neg_mem hx)
    (fun hy => hI.mul_mem_range_fullCrossedProductMap_subtypeHom_left μ hmul _ hy)
    (fun hx => hI.mul_mem_range_fullCrossedProductMap_subtypeHom_right μ hmul hx _)

@[simp]
theorem coe_crossedProductIdeal (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (hI.crossedProductIdeal μ hmul : Set (FullCrossedProduct α μ)) =
      Set.range (hI.subtypeHom.fullCrossedProductMap μ) := by
  simp [crossedProductIdeal]

@[simp]
theorem mem_crossedProductIdeal (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I)
    {x : FullCrossedProduct α μ} :
    x ∈ hI.crossedProductIdeal μ hmul ↔
      x ∈ Set.range (hI.subtypeHom.fullCrossedProductMap μ) := by
  rw [← SetLike.mem_coe, coe_crossedProductIdeal]

/-- The embedded ideal crossed product `hI.crossedProductIdeal μ hmul` is topologically closed in
`FullCrossedProduct α μ`. -/
instance isClosed_crossedProductIdeal (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    IsClosed (hI.crossedProductIdeal μ hmul : Set (FullCrossedProduct α μ)) := by
  rw [coe_crossedProductIdeal, ← NonUnitalStarAlgHom.coe_range]
  exact hI.isClosed_range_fullCrossedProductMap_subtypeHom μ hmul

@[simp]
theorem toNonUnitalStarSubalgebra_crossedProductIdeal (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (hI.crossedProductIdeal μ hmul).toNonUnitalStarSubalgebra =
      (hI.subtypeHom.fullCrossedProductMap μ).range := by
  ext x
  simp

end StarSubalgebra

section TwoSidedIdeal

private def idealToSubalgebraHom {G : Type u} {A : Type v} [Group G] [TopologicalSpace G]
    [NonUnitalCStarAlgebra A] {α : CStarAction G A} {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    Hom hI.restrictIdeal hI.toNonUnitalStarSubalgebra.restrict where
  toNonUnitalStarAlgHom := I.toNonUnitalStarSubalgebraEquiv.toNonUnitalStarAlgHom
  map_action' g x := Subtype.ext <| by simp

private def subalgebraToIdealHom {G : Type u} {A : Type v} [Group G] [TopologicalSpace G]
    [NonUnitalCStarAlgebra A] {α : CStarAction G A} {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    Hom hI.toNonUnitalStarSubalgebra.restrict hI.restrictIdeal where
  toNonUnitalStarAlgHom := I.toNonUnitalStarSubalgebraEquiv.symm.toNonUnitalStarAlgHom
  map_action' g x := Subtype.ext <| by simp

private theorem subalgebraToIdealHom_comp_idealToSubalgebraHom {G : Type u} {A : Type v}
    [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A] {α : CStarAction G A}
    {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    (subalgebraToIdealHom hI).comp (idealToSubalgebraHom hI) = Hom.id hI.restrictIdeal := by
  ext x
  simp [subalgebraToIdealHom, idealToSubalgebraHom]

private theorem idealToSubalgebraHom_comp_subalgebraToIdealHom {G : Type u} {A : Type v}
    [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A] {α : CStarAction G A}
    {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    (idealToSubalgebraHom hI).comp (subalgebraToIdealHom hI) =
      Hom.id hI.toNonUnitalStarSubalgebra.restrict := by
  ext x
  simp [subalgebraToIdealHom, idealToSubalgebraHom]

private theorem subtypeHom_comp_idealToSubalgebraHom {G : Type u} {A : Type v}
    [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A] {α : CStarAction G A}
    {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    hI.toNonUnitalStarSubalgebra.subtypeHom.comp (idealToSubalgebraHom hI) =
      hI.idealSubtypeHom := by
  ext x
  simp [idealToSubalgebraHom]

variable {G : Type u} {A : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A}
  {I : TwoSidedIdeal A} [IsClosed (I : Set A)]
  (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
  (μ : Measure G) [μ.IsHaarMeasure]

/-- `hI.idealSubtypeHom.fullCrossedProductMap μ` preserves norms identically. -/
theorem norm_fullCrossedProductMap_idealSubtypeHom (x : FullCrossedProduct hI.restrictIdeal μ) :
    ‖hI.idealSubtypeHom.fullCrossedProductMap μ x‖ = ‖x‖ := by
  have hinj : Function.Injective ((idealToSubalgebraHom hI).fullCrossedProductMap μ) :=
    Function.LeftInverse.injective fun y => by
      have h := DFunLike.congr_fun
        (congrArg (Hom.fullCrossedProductMap μ)
          (subalgebraToIdealHom_comp_idealToSubalgebraHom hI)) y
      simpa using h
  have hfac : hI.idealSubtypeHom.fullCrossedProductMap μ =
      (hI.toNonUnitalStarSubalgebra.subtypeHom.fullCrossedProductMap μ).comp
        ((idealToSubalgebraHom hI).fullCrossedProductMap μ) := by
    rw [← subtypeHom_comp_idealToSubalgebraHom hI, Hom.fullCrossedProductMap_comp]
  rw [hfac, NonUnitalStarAlgHom.comp_apply,
    hI.toNonUnitalStarSubalgebra.norm_fullCrossedProductMap_subtypeHom μ
      (fun a _ hx => I.mem_toNonUnitalStarSubalgebra.2
        (I.mul_mem_left a _ (I.mem_toNonUnitalStarSubalgebra.1 hx)))]
  exact (NonUnitalStarAlgHom.isometry _ hinj).norm_map_of_map_zero (map_zero _) x

/-- `hI.idealSubtypeHom.fullCrossedProductMap μ` is an isometry. -/
theorem isometry_fullCrossedProductMap_idealSubtypeHom :
    Isometry (hI.idealSubtypeHom.fullCrossedProductMap μ) :=
  AddMonoidHomClass.isometry_of_norm _ (hI.norm_fullCrossedProductMap_idealSubtypeHom μ)

/-- `hI.idealSubtypeHom.fullCrossedProductMap μ` is a closed topological embedding. -/
theorem isClosedEmbedding_fullCrossedProductMap_idealSubtypeHom :
    IsClosedEmbedding (hI.idealSubtypeHom.fullCrossedProductMap μ) :=
  (hI.isometry_fullCrossedProductMap_idealSubtypeHom μ).isClosedEmbedding

/-- `hI.idealSubtypeHom.fullCrossedProductMap μ` is injective. -/
theorem fullCrossedProductMap_idealSubtypeHom_injective :
    Function.Injective (hI.idealSubtypeHom.fullCrossedProductMap μ) :=
  (hI.isometry_fullCrossedProductMap_idealSubtypeHom μ).injective

/-- The `⋆`-subalgebra range of `hI.idealSubtypeHom.fullCrossedProductMap μ` agrees with that of
`I.toNonUnitalStarSubalgebra`. -/
theorem range_fullCrossedProductMap_idealSubtypeHom :
    (hI.idealSubtypeHom.fullCrossedProductMap μ).range =
      (hI.toNonUnitalStarSubalgebra.subtypeHom.fullCrossedProductMap μ).range := by
  have hsurj : Function.Surjective ((idealToSubalgebraHom hI).fullCrossedProductMap μ) :=
    Function.RightInverse.surjective fun y => by
      have h := DFunLike.congr_fun
        (congrArg (Hom.fullCrossedProductMap μ)
          (idealToSubalgebraHom_comp_subalgebraToIdealHom hI)) y
      simpa using h
  apply SetLike.coe_injective
  rw [NonUnitalStarAlgHom.coe_range, NonUnitalStarAlgHom.coe_range,
    ← subtypeHom_comp_idealToSubalgebraHom hI, Hom.fullCrossedProductMap_comp,
    NonUnitalStarAlgHom.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]

/-- The closed two-sided ideal of `FullCrossedProduct α μ` formed by the embedded full crossed
product of a closed `α`-invariant `I : TwoSidedIdeal A`. -/
def idealCrossedProductIdeal : TwoSidedIdeal (FullCrossedProduct α μ) :=
  hI.toNonUnitalStarSubalgebra.crossedProductIdeal μ fun a _ hx =>
    I.mem_toNonUnitalStarSubalgebra.2 (I.mul_mem_left a _ (I.mem_toNonUnitalStarSubalgebra.1 hx))

@[simp]
theorem coe_idealCrossedProductIdeal :
    (hI.idealCrossedProductIdeal μ : Set (FullCrossedProduct α μ)) =
      Set.range (hI.idealSubtypeHom.fullCrossedProductMap μ) := by
  rw [idealCrossedProductIdeal, coe_crossedProductIdeal, ← NonUnitalStarAlgHom.coe_range,
    ← hI.range_fullCrossedProductMap_idealSubtypeHom μ, NonUnitalStarAlgHom.coe_range]

@[simp]
theorem mem_idealCrossedProductIdeal {x : FullCrossedProduct α μ} :
    x ∈ hI.idealCrossedProductIdeal μ ↔
      x ∈ Set.range (hI.idealSubtypeHom.fullCrossedProductMap μ) := by
  rw [← SetLike.mem_coe, coe_idealCrossedProductIdeal]

/-- The embedded ideal crossed product `hI.idealCrossedProductIdeal μ` is topologically closed in
`FullCrossedProduct α μ`. -/
instance isClosed_idealCrossedProductIdeal :
    IsClosed (hI.idealCrossedProductIdeal μ : Set (FullCrossedProduct α μ)) := by
  dsimp [idealCrossedProductIdeal]
  infer_instance

@[simp]
theorem toNonUnitalStarSubalgebra_idealCrossedProductIdeal :
    (hI.idealCrossedProductIdeal μ).toNonUnitalStarSubalgebra =
      (hI.idealSubtypeHom.fullCrossedProductMap μ).range := by
  ext x
  simp

end TwoSidedIdeal

end IsInvariant

/-! ### Exactness in the middle and kernel identifications -/

namespace TauCeti.CStarAction

private theorem mul_mem_of_ker {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {α : CStarAction G A} {β : CStarAction G B} {I : NonUnitalStarSubalgebra ℂ A}
    (q : Hom α β) (hker : ∀ a, q a = 0 ↔ a ∈ I) (a : A) {x : A} (hx : x ∈ I) : a * x ∈ I :=
  (hker (a * x)).1 <| by rw [map_mul, (hker x).2 hx, mul_zero]

section MiddleExact

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B} (μ : Measure G) [μ.IsHaarMeasure]

/-- Any dense-range `⋆`-homomorphism `ψ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] C` annihilating an
equivariantly embedded crossed product vanishes on `ker (q.fullCrossedProductMap μ)`. -/
private theorem map_eq_zero_of_fullCrossedProductMap_eq_zero {D : Type v} {C : Type w}
    [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra C] {γ : CStarAction G D}
    (φ : Hom γ α) (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 → a ∈ Set.range φ)
    (ψ : FullCrossedProduct α μ →⋆ₙₐ[ℂ] C) (hψ : DenseRange ψ)
    (hψφ : ∀ z, ψ (φ.fullCrossedProductMap μ z) = 0)
    {x : FullCrossedProduct α μ} (hx : q.fullCrossedProductMap μ x = 0) :
    ψ x = 0 := by
  have hΦ : ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).IsMultiplierNondegenerate := by
    rw [NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense]
    simp only [NonUnitalStarAlgHom.comp_apply]
    exact (NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense_span_comp
      (φ := DoubleCentralizer.coeHom (𝕜 := ℂ)) hψ).1
      NonUnitalStarAlgHom.isMultiplierNondegenerate_coeHom
  have hM : ∀ a, q a = 0 →
      (((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).toCovariantMultiplierHom hΦ).coefficient a =
        0 := by
    intro a ha
    obtain ⟨d, rfl⟩ := hker a ha
    refine (((((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).toCovariantMultiplierHom hΦ
      ).forall_mem_range_fullCrossedProductMap_integratedFull_eq_zero_iff μ φ).1 ?_) d
    intro y hy
    obtain ⟨z, rfl⟩ := (φ.fullCrossedProductMap μ).mem_range.1 hy
    rw [NonUnitalStarAlgHom.integratedFull_toCovariantMultiplierHom]
    simp [hψφ z]
  have hN :=
    (((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ).toCovariantMultiplierHom hΦ
      ).integratedFull_descend_fullCrossedProductMap_apply μ q hq hM x
  rw [hx, map_zero, NonUnitalStarAlgHom.integratedFull_toCovariantMultiplierHom] at hN
  exact DoubleCentralizer.coe_injective (𝕜 := ℂ) (by simpa using hN.symm)

/-- Exactness in the middle for full crossed products: if `q : Hom α β` is surjective with kernel
`I`, then `q.fullCrossedProductMap μ` vanishes at `x` precisely when `x` lies in the range of
`hI.subtypeHom.fullCrossedProductMap μ`. Requires no `T2Space G` assumption. -/
theorem fullCrossedProductMap_eq_zero_iff_mem_range_subtypeHom
    (I : NonUnitalStarSubalgebra ℂ A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I)
    (x : FullCrossedProduct α μ) :
    q.fullCrossedProductMap μ x = 0 ↔
      x ∈ Set.range (hI.subtypeHom.fullCrossedProductMap μ) := by
  refine ⟨fun hx => ?_, fun ⟨y, hy⟩ =>
    hy ▸ hI.fullCrossedProductMap_subtypeHom_apply_eq_zero μ q (fun a ha => (hker a).2 ha) y⟩
  have hmul : ∀ a : A, ∀ y ∈ I, a * y ∈ I := fun a _ hy => mul_mem_of_ker q hker a hy
  have hmk : TwoSidedIdeal.Quotient.mkStarAlgHom (hI.crossedProductIdeal μ hmul) x = 0 :=
    map_eq_zero_of_fullCrossedProductMap_eq_zero μ hI.subtypeHom q hq
      (fun a ha => ⟨⟨a, (hker a).1 ha⟩, hI.subtypeHom_apply ⟨a, (hker a).1 ha⟩⟩)
      (TwoSidedIdeal.Quotient.mkStarAlgHom (hI.crossedProductIdeal μ hmul))
      (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective _).denseRange
      (fun z => (TwoSidedIdeal.Quotient.mkStarAlgHom_apply _ _).trans <|
        TwoSidedIdeal.Quotient.eq_zero_iff_mem.2
          ((hI.mem_crossedProductIdeal μ hmul).2 ⟨z, rfl⟩))
      hx
  exact (hI.mem_crossedProductIdeal μ hmul).1 <|
    TwoSidedIdeal.Quotient.eq_zero_iff_mem.1 <|
      (TwoSidedIdeal.Quotient.mkStarAlgHom_apply _ x).symm.trans hmk

/-- For a surjective equivariant `q : Hom α β` with kernel `I : NonUnitalStarSubalgebra ℂ A`, the
two-sided ideal kernel of `q.fullCrossedProductMap μ` is `hI.crossedProductIdeal μ hmul`. -/
theorem ker_fullCrossedProductMap_eq_crossedProductIdeal
    (I : NonUnitalStarSubalgebra ℂ A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I)
    (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    TwoSidedIdeal.ker (q.fullCrossedProductMap μ) = hI.crossedProductIdeal μ hmul := by
  ext x
  rw [TwoSidedIdeal.mem_ker, hI.mem_crossedProductIdeal μ hmul]
  exact fullCrossedProductMap_eq_zero_iff_mem_range_subtypeHom μ I hI q hq hker x

/-- Exactness in the middle for `I : TwoSidedIdeal A` and a surjective `q : Hom α β` with kernel
`I`. -/
theorem fullCrossedProductMap_eq_zero_iff_mem_range_idealSubtypeHom
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I)
    (x : FullCrossedProduct α μ) :
    q.fullCrossedProductMap μ x = 0 ↔
      x ∈ Set.range (hI.idealSubtypeHom.fullCrossedProductMap μ) := by
  rw [← NonUnitalStarAlgHom.coe_range, hI.range_fullCrossedProductMap_idealSubtypeHom μ,
    NonUnitalStarAlgHom.coe_range]
  exact fullCrossedProductMap_eq_zero_iff_mem_range_subtypeHom μ
    I.toNonUnitalStarSubalgebra hI.toNonUnitalStarSubalgebra q hq
    (fun a => (hker a).trans I.mem_toNonUnitalStarSubalgebra.symm) x

/-- For a surjective `q : Hom α β` with kernel `I : TwoSidedIdeal A`, the two-sided ideal kernel of
`q.fullCrossedProductMap μ` is `hI.idealCrossedProductIdeal μ`. -/
theorem ker_fullCrossedProductMap_eq_idealCrossedProductIdeal
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    TwoSidedIdeal.ker (q.fullCrossedProductMap μ) = hI.idealCrossedProductIdeal μ := by
  ext x
  rw [TwoSidedIdeal.mem_ker, hI.mem_idealCrossedProductIdeal μ]
  exact fullCrossedProductMap_eq_zero_iff_mem_range_idealSubtypeHom μ I hI q hq hker x

namespace Hom

/-- For any surjective equivariant homomorphism `q : Hom α β`, the kernel of
`q.fullCrossedProductMap μ` is the embedded crossed product of `ker q`. -/
theorem ker_fullCrossedProductMap (q : Hom α β) (hq : Function.Surjective q) :
    TwoSidedIdeal.ker (q.fullCrossedProductMap μ) =
      (IsInvariant.ker q).idealCrossedProductIdeal μ :=
  ker_fullCrossedProductMap_eq_idealCrossedProductIdeal μ
    (TwoSidedIdeal.ker q.toNonUnitalStarAlgHom) (IsInvariant.ker q) q hq fun _ =>
      (TwoSidedIdeal.mem_ker q.toNonUnitalStarAlgHom).symm

/-- Pointwise kernel characterization of `q.fullCrossedProductMap μ` for surjective `q : Hom α β`.
-/
theorem fullCrossedProductMap_eq_zero_iff (q : Hom α β) (hq : Function.Surjective q)
    (x : FullCrossedProduct α μ) :
    q.fullCrossedProductMap μ x = 0 ↔
      x ∈ Set.range ((IsInvariant.ker q).idealSubtypeHom.fullCrossedProductMap μ) := by
  rw [← TwoSidedIdeal.mem_ker, q.ker_fullCrossedProductMap μ hq,
    IsInvariant.mem_idealCrossedProductIdeal]

end Hom

/-- The kernel of `(α.quotientMkHom I hI).fullCrossedProductMap μ` is
`hI.idealCrossedProductIdeal μ`. -/
@[simp]
theorem ker_fullCrossedProductMap_quotientMkHom (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    TwoSidedIdeal.ker ((α.quotientMkHom I hI).fullCrossedProductMap μ) =
      hI.idealCrossedProductIdeal μ :=
  ker_fullCrossedProductMap_eq_idealCrossedProductIdeal μ I hI (α.quotientMkHom I hI)
    (α.quotientMkHom_surjective I hI) fun a =>
      (α.quotientMkHom_apply I hI a ▸ TwoSidedIdeal.Quotient.eq_zero_iff_mem)

/-- `(α.quotientMkHom I hI).fullCrossedProductMap μ x = 0` precisely when `x` lies in the range of
`hI.idealSubtypeHom.fullCrossedProductMap μ`. -/
theorem fullCrossedProductMap_quotientMkHom_eq_zero_iff (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (x : FullCrossedProduct α μ) :
    (α.quotientMkHom I hI).fullCrossedProductMap μ x = 0 ↔
      x ∈ Set.range (hI.idealSubtypeHom.fullCrossedProductMap μ) := by
  rw [← TwoSidedIdeal.mem_ker, α.ker_fullCrossedProductMap_quotientMkHom μ I hI,
    hI.mem_idealCrossedProductIdeal μ]

end MiddleExact

/-! ### Full short exact sequence and quotient `⋆`-isomorphisms -/

section ExactSequence

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B} (μ : Measure G) [μ.IsHaarMeasure]

/-- The invariant-ideal short exact sequence of full crossed products (Williams, Proposition 3.19):
if `q : Hom α β` is surjective with kernel the closed `α`-invariant ideal `I`, then the induced
homomorphisms `I ⋊ G → A ⋊ G → B ⋊ G` are injective on the left, surjective on the right, and
exact in the middle. -/
theorem fullCrossedProductMap_exact
    (I : NonUnitalStarSubalgebra ℂ A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    Function.Injective (hI.subtypeHom.fullCrossedProductMap μ) ∧
      Function.Surjective (q.fullCrossedProductMap μ) ∧
      ∀ x, q.fullCrossedProductMap μ x = 0 ↔
        x ∈ Set.range (hI.subtypeHom.fullCrossedProductMap μ) :=
  ⟨hI.fullCrossedProductMap_subtypeHom_injective μ (fun a _ hx => mul_mem_of_ker q hker a hx),
    q.surjective_fullCrossedProductMap μ hq.denseRange,
    fullCrossedProductMap_eq_zero_iff_mem_range_subtypeHom μ I hI q hq hker⟩

/-- Short exact sequence of full crossed products for a closed `α`-invariant `I : TwoSidedIdeal A`
and any surjective `q : Hom α β` with kernel `I`. -/
theorem fullCrossedProductMap_idealSubtypeHom_exact
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
    (q : Hom α β) (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I) :
    Function.Injective (hI.idealSubtypeHom.fullCrossedProductMap μ) ∧
      Function.Surjective (q.fullCrossedProductMap μ) ∧
      ∀ x, q.fullCrossedProductMap μ x = 0 ↔
        x ∈ Set.range (hI.idealSubtypeHom.fullCrossedProductMap μ) :=
  ⟨hI.fullCrossedProductMap_idealSubtypeHom_injective μ,
    q.surjective_fullCrossedProductMap μ hq.denseRange,
    fullCrossedProductMap_eq_zero_iff_mem_range_idealSubtypeHom μ I hI q hq hker⟩

/-- Short exact sequence `0 → I ⋊ G → A ⋊ G → (A ⧸ I) ⋊ G → 0` for a closed `α`-invariant
`I : TwoSidedIdeal A` and the concrete descended quotient action `α.quotient I hI`. -/
theorem fullCrossedProductMap_quotientMkHom_exact (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    Function.Injective (hI.idealSubtypeHom.fullCrossedProductMap μ) ∧
      Function.Surjective ((α.quotientMkHom I hI).fullCrossedProductMap μ) ∧
      ∀ x, (α.quotientMkHom I hI).fullCrossedProductMap μ x = 0 ↔
        x ∈ Set.range (hI.idealSubtypeHom.fullCrossedProductMap μ) :=
  ⟨hI.fullCrossedProductMap_idealSubtypeHom_injective μ,
    α.surjective_fullCrossedProductMap_quotientMkHom μ I hI,
    α.fullCrossedProductMap_quotientMkHom_eq_zero_iff μ I hI⟩

namespace Hom

/-- Canonical `⋆`-isomorphism `(A ⋊_α G) ⧸ (ker q ⋊_α G) ≃⋆ₐ[ℂ] B ⋊_β G` induced by a surjective
equivariant homomorphism `q : Hom α β`. -/
def quotientIdealCrossedProductEquiv (q : Hom α β) (hq : Function.Surjective q) :
    (FullCrossedProduct α μ) ⧸ (IsInvariant.ker q).idealCrossedProductIdeal μ ≃⋆ₐ[ℂ]
      FullCrossedProduct β μ :=
  (TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq (q.ker_fullCrossedProductMap μ hq).symm).trans
    (NonUnitalStarAlgHom.quotientKerEquivOfSurjective
      (q.surjective_fullCrossedProductMap μ hq.denseRange))

@[simp]
theorem quotientIdealCrossedProductEquiv_mk (q : Hom α β) (hq : Function.Surjective q)
    (x : FullCrossedProduct α μ) :
    q.quotientIdealCrossedProductEquiv μ hq
        (TwoSidedIdeal.Quotient.mk ((IsInvariant.ker q).idealCrossedProductIdeal μ) x) =
      q.fullCrossedProductMap μ x := by
  simp [quotientIdealCrossedProductEquiv]

@[simp]
theorem quotientIdealCrossedProductEquiv_symm_fullCrossedProductMap
    (q : Hom α β) (hq : Function.Surjective q) (x : FullCrossedProduct α μ) :
    (q.quotientIdealCrossedProductEquiv μ hq).symm (q.fullCrossedProductMap μ x) =
      TwoSidedIdeal.Quotient.mk ((IsInvariant.ker q).idealCrossedProductIdeal μ) x :=
  (q.quotientIdealCrossedProductEquiv μ hq).symm_apply_eq.2
    (q.quotientIdealCrossedProductEquiv_mk μ hq x).symm

end Hom

/-- Canonical `⋆`-isomorphism `(A ⋊_α G) ⧸ (I ⋊_α G) ≃⋆ₐ[ℂ] (A ⧸ I) ⋊_α G` for a closed
`α`-invariant two-sided ideal `I : TwoSidedIdeal A`. -/
def quotientFullCrossedProductEquiv (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) :
    (FullCrossedProduct α μ) ⧸ hI.idealCrossedProductIdeal μ ≃⋆ₐ[ℂ]
      FullCrossedProduct (α.quotient I hI) μ :=
  (TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq
      (α.ker_fullCrossedProductMap_quotientMkHom μ I hI).symm).trans
    (NonUnitalStarAlgHom.quotientKerEquivOfSurjective
      (α.surjective_fullCrossedProductMap_quotientMkHom μ I hI))

@[simp]
theorem quotientFullCrossedProductEquiv_mk (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (x : FullCrossedProduct α μ) :
    α.quotientFullCrossedProductEquiv μ I hI
        (TwoSidedIdeal.Quotient.mk (hI.idealCrossedProductIdeal μ) x) =
      (α.quotientMkHom I hI).fullCrossedProductMap μ x := by
  simp [quotientFullCrossedProductEquiv]

@[simp]
theorem quotientFullCrossedProductEquiv_symm_fullCrossedProductMap (α : CStarAction G A)
    (I : TwoSidedIdeal A) [IsClosed (I : Set A)]
    (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A)) (x : FullCrossedProduct α μ) :
    (α.quotientFullCrossedProductEquiv μ I hI).symm
        ((α.quotientMkHom I hI).fullCrossedProductMap μ x) =
      TwoSidedIdeal.Quotient.mk (hI.idealCrossedProductIdeal μ) x :=
  (α.quotientFullCrossedProductEquiv μ I hI).symm_apply_eq.2
    (α.quotientFullCrossedProductEquiv_mk μ I hI x).symm

end ExactSequence

end TauCeti.CStarAction

namespace IsInvariant

open CStarAction

variable {G : Type u} {A B : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B}
  {I : NonUnitalStarSubalgebra ℂ A} [IsClosed (I : Set A)]
  (hI : _root_.IsInvariant (fun g a => α g a) (I : Set A))
  (μ : Measure G) [μ.IsHaarMeasure]

/-- Canonical `⋆`-isomorphism `(A ⋊_α G) ⧸ (I ⋊_α G) ≃⋆ₐ[ℂ] B ⋊_β G` associated to a surjective
equivariant homomorphism `q : Hom α β` with kernel `I : NonUnitalStarSubalgebra ℂ A`. -/
def quotientCrossedProductEquiv (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 ↔ a ∈ I) (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (FullCrossedProduct α μ) ⧸ hI.crossedProductIdeal μ hmul ≃⋆ₐ[ℂ] FullCrossedProduct β μ :=
  (TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq
      (ker_fullCrossedProductMap_eq_crossedProductIdeal μ I hI q hq hker hmul).symm).trans
    (NonUnitalStarAlgHom.quotientKerEquivOfSurjective
      (q.surjective_fullCrossedProductMap μ hq.denseRange))

@[simp]
theorem quotientCrossedProductEquiv_mk (q : Hom α β) (hq : Function.Surjective q)
    (hker : ∀ a, q a = 0 ↔ a ∈ I)
    (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (x : FullCrossedProduct α μ) :
    hI.quotientCrossedProductEquiv μ q hq hker hmul
        (TwoSidedIdeal.Quotient.mk (hI.crossedProductIdeal μ hmul) x) =
      q.fullCrossedProductMap μ x := by
  simp [quotientCrossedProductEquiv]

@[simp]
theorem quotientCrossedProductEquiv_symm_fullCrossedProductMap (q : Hom α β)
    (hq : Function.Surjective q) (hker : ∀ a, q a = 0 ↔ a ∈ I)
    (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (x : FullCrossedProduct α μ) :
    (hI.quotientCrossedProductEquiv μ q hq hker hmul).symm (q.fullCrossedProductMap μ x) =
      TwoSidedIdeal.Quotient.mk (hI.crossedProductIdeal μ hmul) x :=
  (hI.quotientCrossedProductEquiv μ q hq hker hmul).symm_apply_eq.2
    (hI.quotientCrossedProductEquiv_mk μ q hq hker hmul x).symm

end IsInvariant
