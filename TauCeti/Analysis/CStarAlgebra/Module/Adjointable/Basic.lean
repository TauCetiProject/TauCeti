/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import TauCeti.Analysis.CStarAlgebra.Module.Action
public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair

/-!
# Adjointable operators on Hilbert C⋆-modules

Between C⋆-modules `E` and `F` over `A`, a map `T : E → F` is *adjointable*
(`CStarModule.IsAdjointable`) when there exists a function `S : F → E` satisfying
`⟪T x, y⟫_A = ⟪x, S y⟫_A` for all `x` and `y`. Unlike on Hilbert spaces over `ℂ`, a bounded
module-linear operator between complete Hilbert C⋆-modules need not be adjointable. When an
adjoint exists, it is unique (`LinearMap.IsAdjointPair.unique_right_cstarModule`), both maps are
complex-linear and commute with the `A`-action, and between complete modules both are bounded
(`LinearMap.IsAdjointPair.toContinuousLinearMapCStarModule`).

`CStarModule.Adjointable A E F` bundles a bounded complex-linear operator `E →L[ℂ] F` together
with its bounded adjoint `F →L[ℂ] E` and the adjoint identity. Because the inner product separates
points, the underlying map `E →L[ℂ] F` uniquely determines its adjoint, so `Adjointable A E F` is
extensional on pointwise evaluation (`CStarModule.Adjointable.ext`). Right Hilbert `B`-modules are
represented throughout by taking `A = Bᵐᵒᵖ`; no unit on `A` and no nonzero-module assumption on
`E` or `F` is required.

Equipping `Adjointable A E F` with the operator norm pulled back along the forgetful map
`toContinuousLinearMap` makes the forgetful embedding `toContinuousLinearMapₗᵢ` a linear isometry,
makes `adjointₗᵢ : Adjointable A E F ≃ₗᵢ⋆[ℂ] Adjointable A F E` a conjugate-linear isometric
equivalence, and makes `Adjointable A E F` a Banach space whenever `E` and `F` are complete. On a
single complete Hilbert C⋆-module `E`, `Adjointable A E E` is a unital C⋆-algebra under
composition and adjoint (`CStarModule.Adjointable.instCStarAlgebra`), acting naturally and
boundedly on `E` and commuting with the coefficient action.

## Main declarations

* `CStarModule.IsAdjointable`: predicate that a plain function `E → F` admits an everywhere-defined
  C⋆-module adjoint.
* `CStarModule.Adjointable`: the bundled space of bounded adjointable operators between normed
  C⋆-modules, with `FunLike` and `ContinuousLinearMapClass` instances.
* `CStarModule.Adjointable.ofAdjointPair`, `CStarModule.Adjointable.ofIsAdjointable`: construct a
  bundled adjointable operator from plain functions between complete Hilbert C⋆-modules.
* `CStarModule.Adjointable.adjoint`: the adjoint operator `Adjointable A F E`, bundled as a
  conjugate-linear isometric equivalence `CStarModule.Adjointable.adjointₗᵢ`.
* `CStarModule.Adjointable.toContinuousLinearMapₗᵢ`,
  `CStarModule.Adjointable.toContinuousLinearMapAlgHom`: the isometric forgetful map to continuous
  complex-linear operators, respecting identity and composition on endomorphisms.
* `CStarModule.Adjointable.instCompleteSpace`, `CStarModule.Adjointable.instCStarAlgebra`:
  completeness of `Adjointable A E F` and the unital C⋆-algebra structure on `Adjointable A E E`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Section 2.2.
* William L. Paschke, *Inner product modules over B⋆-algebras*, Trans. Amer. Math. Soc. 182
  (1973), 443–468.
* The conjugate-linear isometric adjoint `CStarModule.Adjointable.adjointₗᵢ` parallels Mathlib's
  `ContinuousLinearMap.adjoint` (`Mathlib.Analysis.InnerProductSpace.Adjoint`).
-/

public section

open MulOpposite ContinuousLinearMap

namespace CStarModule

/-! ### The unbundled adjointability predicate -/

section IsAdjointable

variable {A E F G : Type*}

section Algebraic

variable [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]
  [AddCommGroup G] [Module ℂ G] [SMul A G] [Norm G] [CStarModule A G]

/-- A function `T : E → F` between C⋆-modules over `A` is *adjointable* if it admits an
everywhere-defined function `S : F → E` satisfying `⟪T x, y⟫_A = ⟪x, S y⟫_A` for all `x` and `y`.
Neither linearity nor continuity of `T` or `S` is assumed in the definition. -/
def IsAdjointable (A : Type*) [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
    [PartialOrder A] [Norm A] {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
    [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]
    (T : E → F) : Prop :=
  ∃ S : F → E,
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip (innerₛₗ (A := A) (E := F)).flip T S

/-- Unfold `IsAdjointable` directly in terms of the inner-product identity. -/
theorem isAdjointable_iff {T : E → F} :
    IsAdjointable A T ↔ ∃ S : F → E, ∀ x y, inner A (T x) y = inner A x (S y) :=
  exists_congr fun _ ↦ isAdjointPair_inner_iff

/-- Right-module form of `isAdjointable_iff` for `CStarModule Bᵐᵒᵖ`. -/
theorem isAdjointable_mulOpposite_iff {B E F : Type*}
    [NonUnitalSeminormedRing B] [StarRing B] [Module ℂ B] [StarModule ℂ B] [PartialOrder B]
    [AddCommGroup E] [Module ℂ E] [SMul Bᵐᵒᵖ E] [Norm E] [CStarModule Bᵐᵒᵖ E]
    [AddCommGroup F] [Module ℂ F] [SMul Bᵐᵒᵖ F] [Norm F] [CStarModule Bᵐᵒᵖ F]
    {T : E → F} :
    IsAdjointable Bᵐᵒᵖ T ↔
      ∃ S : F → E, ∀ x y, unop (inner Bᵐᵒᵖ (T x) y) = unop (inner Bᵐᵒᵖ x (S y)) := by
  rw [isAdjointable_iff]
  exact exists_congr fun S ↦ forall₂_congr fun x y ↦ unop_injective.eq_iff.symm

namespace IsAdjointable

theorem id : IsAdjointable A (id : E → E) :=
  isAdjointable_iff.mpr ⟨_root_.id, fun _ _ ↦ rfl⟩

theorem zero : IsAdjointable A (0 : E → F) :=
  isAdjointable_iff.mpr ⟨0, fun _ _ ↦ by simp⟩

theorem add {T₁ T₂ : E → F} (h₁ : IsAdjointable A T₁) (h₂ : IsAdjointable A T₂) :
    IsAdjointable A (T₁ + T₂) := by
  rcases isAdjointable_iff.mp h₁ with ⟨S₁, hS₁⟩
  rcases isAdjointable_iff.mp h₂ with ⟨S₂, hS₂⟩
  exact isAdjointable_iff.mpr ⟨S₁ + S₂, fun x y ↦ by simp [hS₁, hS₂]⟩

theorem neg {T : E → F} (h : IsAdjointable A T) : IsAdjointable A (-T) := by
  rcases isAdjointable_iff.mp h with ⟨S, hS⟩
  exact isAdjointable_iff.mpr ⟨-S, fun x y ↦ by simp [hS]⟩

theorem sub {T₁ T₂ : E → F} (h₁ : IsAdjointable A T₁) (h₂ : IsAdjointable A T₂) :
    IsAdjointable A (T₁ - T₂) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

theorem smul {T : E → F} (c : ℂ) (h : IsAdjointable A T) : IsAdjointable A (c • T) := by
  rcases isAdjointable_iff.mp h with ⟨S, hS⟩
  exact isAdjointable_iff.mpr ⟨star c • S, fun x y ↦ by simp [hS]⟩

theorem comp {S : F → G} {T : E → F} (hS : IsAdjointable A S) (hT : IsAdjointable A T) :
    IsAdjointable A (S ∘ T) := by
  rcases isAdjointable_iff.mp hS with ⟨S', hS'⟩
  rcases isAdjointable_iff.mp hT with ⟨T', hT'⟩
  exact isAdjointable_iff.mpr ⟨T' ∘ S', fun x y ↦ by simp [Function.comp_apply, hS', hT']⟩

theorem map_add {T : E → F} (h : IsAdjointable A T) (x y : E) : T (x + y) = T x + T y := by
  obtain ⟨_, hS⟩ := h
  exact hS.map_add_cstarModule x y

theorem map_smul {T : E → F} (h : IsAdjointable A T) (c : ℂ) (x : E) : T (c • x) = c • T x := by
  obtain ⟨_, hS⟩ := h
  exact hS.map_smul_cstarModule c x

theorem map_smul_coeff {T : E → F} (h : IsAdjointable A T) (a : A) (x : E) :
    T (a • x) = a • T x := by
  obtain ⟨_, hS⟩ := h
  exact hS.map_smul_coeff_cstarModule a x

end IsAdjointable

end Algebraic

/-- An adjointable function between complete Hilbert C⋆-modules is automatically continuous. -/
theorem IsAdjointable.continuous [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [SMul A E] [CStarModule A E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [SMul A F] [CStarModule A F]
    {T : E → F} (h : IsAdjointable A T) : Continuous T := by
  obtain ⟨_, hS⟩ := h
  exact hS.continuous_cstarModule

end IsAdjointable

/-! ### Bundled adjointable operators -/

/-- The space of bounded adjointable operators between normed C⋆-modules `E` and `F` over `A`.
Although the adjoint `adjointMap` is stored as a field so algebraic operations avoid choice, it is
uniquely determined by `toContinuousLinearMap`, making `Adjointable A E F` extensional on
vectors. -/
structure Adjointable (A E F : Type*)
    [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F] where
  /-- The underlying continuous complex-linear map. -/
  toContinuousLinearMap : E →L[ℂ] F
  /-- The continuous complex-linear adjoint map; prefer `Adjointable.adjoint` in user code. -/
  protected adjointMap : F →L[ℂ] E
  /-- The defining adjoint-pair relation for `toContinuousLinearMap` and `adjointMap`. -/
  protected isAdjointPair' :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip (innerₛₗ (A := A) (E := F)).flip
      toContinuousLinearMap adjointMap

namespace Adjointable

section Algebraic

variable {A E F G : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

instance instFunLike : FunLike (Adjointable A E F) E F where
  coe T := T.toContinuousLinearMap
  coe_injective T₁ T₂ h := by
    cases T₁ with | mk f₁ g₁ h₁ =>
    cases T₂ with | mk f₂ g₂ h₂ =>
    have hf : f₁ = f₂ := DFunLike.coe_injective h
    subst hf
    have hg : g₁ = g₂ := DFunLike.coe_injective (h₁.unique_right_cstarModule h₂)
    subst hg
    rfl

instance instContinuousLinearMapClass : ContinuousLinearMapClass (Adjointable A E F) ℂ E F where
  map_add T := T.toContinuousLinearMap.map_add
  map_smulₛₗ T := T.toContinuousLinearMap.map_smul
  map_continuous T := T.toContinuousLinearMap.continuous

@[simp]
theorem coe_toContinuousLinearMap (T : Adjointable A E F) :
    ⇑T.toContinuousLinearMap = ⇑T := (rfl)

@[simp]
theorem toContinuousLinearMap_apply (T : Adjointable A E F) (x : E) :
    T.toContinuousLinearMap x = T x := (rfl)

@[ext]
theorem ext {T₁ T₂ : Adjointable A E F} (h : ∀ x, T₁ x = T₂ x) : T₁ = T₂ :=
  DFunLike.ext T₁ T₂ h

theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : Adjointable A E F → E →L[ℂ] F) :=
  fun _ _ h ↦ ext fun x ↦ congrArg (· x) h

@[simp]
theorem toContinuousLinearMap_inj {T₁ T₂ : Adjointable A E F} :
    T₁.toContinuousLinearMap = T₂.toContinuousLinearMap ↔ T₁ = T₂ :=
  toContinuousLinearMap_injective.eq_iff

/-- Construct an `Adjointable` operator from two continuous complex-linear maps satisfying
`⟪T x, y⟫_A = ⟪x, S y⟫_A`. -/
def mkOfInner (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) : Adjointable A E F where
  toContinuousLinearMap := T
  adjointMap := S
  isAdjointPair' := isAdjointPair_inner_iff.mpr h

@[simp]
theorem mkOfInner_apply (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) (x : E) :
    mkOfInner T S h x = T x := (rfl)

@[simp]
theorem toContinuousLinearMap_mkOfInner (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) :
    (mkOfInner T S h).toContinuousLinearMap = T := (rfl)

/-- The adjoint of a bundled adjointable operator, as an adjointable operator `F → E`. -/
def adjoint (T : Adjointable A E F) : Adjointable A F E where
  toContinuousLinearMap := T.adjointMap
  adjointMap := T.toContinuousLinearMap
  isAdjointPair' := T.isAdjointPair'.symm_cstarModule

@[simp]
theorem toContinuousLinearMap_adjoint_mkOfInner (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) :
    (mkOfInner T S h).adjoint.toContinuousLinearMap = S := (rfl)

@[simp]
theorem adjoint_mkOfInner_apply (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) (y : F) :
    (mkOfInner T S h).adjoint y = S y := (rfl)

/-- Defining relation of the adjoint in the second slot: `⟪x, T* y⟫_A = ⟪T x, y⟫_A`. -/
theorem adjoint_inner_right (T : Adjointable A E F) (x : E) (y : F) :
    inner A x (T.adjoint y) = inner A (T x) y :=
  (T.isAdjointPair'.inner_eq_cstarModule x y).symm

/-- Defining relation of the adjoint in the first slot: `⟪T* y, x⟫_A = ⟪y, T x⟫_A`. -/
theorem adjoint_inner_left (T : Adjointable A E F) (x : E) (y : F) :
    inner A (T.adjoint y) x = inner A y (T x) :=
  T.adjoint.isAdjointPair'.inner_eq_cstarModule y x

/-- Right-module form of `adjoint_inner_right` for `CStarModule Bᵐᵒᵖ`. -/
theorem unop_adjoint_inner_right {B E F : Type*}
    [NonUnitalSeminormedRing B] [StarRing B] [Module ℂ B] [StarModule ℂ B] [PartialOrder B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
    (T : Adjointable Bᵐᵒᵖ E F) (x : E) (y : F) :
    unop (inner Bᵐᵒᵖ x (T.adjoint y)) = unop (inner Bᵐᵒᵖ (T x) y) :=
  congrArg unop (T.adjoint_inner_right x y)

/-- Right-module form of `adjoint_inner_left` for `CStarModule Bᵐᵒᵖ`. -/
theorem unop_adjoint_inner_left {B E F : Type*}
    [NonUnitalSeminormedRing B] [StarRing B] [Module ℂ B] [StarModule ℂ B] [PartialOrder B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
    (T : Adjointable Bᵐᵒᵖ E F) (x : E) (y : F) :
    unop (inner Bᵐᵒᵖ (T.adjoint y) x) = unop (inner Bᵐᵒᵖ y (T x)) :=
  congrArg unop (T.adjoint_inner_left x y)

/-- Every bundled adjointable operator satisfies `IsAdjointable`. -/
theorem isAdjointable (T : Adjointable A E F) : IsAdjointable A (T : E → F) :=
  ⟨T.adjoint, T.isAdjointPair'⟩

/-- Every adjointable operator commutes with the coefficient action. -/
@[simp]
theorem map_smul_coeff (T : Adjointable A E F) (a : A) (x : E) : T (a • x) = a • T x :=
  T.isAdjointPair'.map_smul_coeff_cstarModule a x

/-- Right-module form of `map_smul_coeff`: `T (x b) = (T x) b`. -/
theorem map_op_smul {B E F : Type*}
    [NonUnitalSeminormedRing B] [StarRing B] [Module ℂ B] [StarModule ℂ B] [PartialOrder B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
    (T : Adjointable Bᵐᵒᵖ E F) (b : B) (x : E) :
    T (op b • x) = op b • T x :=
  T.map_smul_coeff (op b) x

/-- Taking the adjoint twice recovers the original operator. -/
@[simp]
theorem adjoint_adjoint (T : Adjointable A E F) : T.adjoint.adjoint = T :=
  toContinuousLinearMap_injective rfl

theorem adjoint_injective :
    Function.Injective (adjoint : Adjointable A E F → Adjointable A F E) :=
  Function.RightInverse.injective adjoint_adjoint

@[simp]
theorem adjoint_inj {T₁ T₂ : Adjointable A E F} : T₁.adjoint = T₂.adjoint ↔ T₁ = T₂ :=
  adjoint_injective.eq_iff

/-- Uniqueness characterization of the adjoint. -/
theorem eq_adjoint_iff {S : Adjointable A F E} {T : Adjointable A E F} :
    S = T.adjoint ↔ ∀ x y, inner A (T x) y = inner A x (S y) := by
  refine ⟨fun h x y ↦ h ▸ (T.adjoint_inner_right x y).symm, fun h ↦ ext fun y ↦ ?_⟩
  exact CStarModule.ext_inner_left fun x ↦ (h x y).symm.trans (T.adjoint_inner_right x y).symm

/-! #### Additive and complex-linear structure -/

instance instZero : Zero (Adjointable A E F) :=
  ⟨mkOfInner 0 0 fun _ _ ↦ by simp⟩

instance instAdd : Add (Adjointable A E F) :=
  ⟨fun T₁ T₂ ↦ mkOfInner (T₁.toContinuousLinearMap + T₂.toContinuousLinearMap)
    (T₁.adjoint.toContinuousLinearMap + T₂.adjoint.toContinuousLinearMap) fun x y ↦ by
      simp [← adjoint_inner_right]⟩

instance instNeg : Neg (Adjointable A E F) :=
  ⟨fun T ↦ mkOfInner (-T.toContinuousLinearMap) (-T.adjoint.toContinuousLinearMap) fun x y ↦ by
    simp [← adjoint_inner_right]⟩

instance instSub : Sub (Adjointable A E F) :=
  ⟨fun T₁ T₂ ↦ mkOfInner (T₁.toContinuousLinearMap - T₂.toContinuousLinearMap)
    (T₁.adjoint.toContinuousLinearMap - T₂.adjoint.toContinuousLinearMap) fun x y ↦ by
      simp [inner_sub_left, inner_sub_right, ← adjoint_inner_right]⟩

instance instSMulNat : SMul ℕ (Adjointable A E F) :=
  ⟨fun n T ↦ mkOfInner (n • T.toContinuousLinearMap) (n • T.adjoint.toContinuousLinearMap)
    fun x y ↦ by simp [← Nat.cast_smul_eq_nsmul ℂ, ← adjoint_inner_right]⟩

instance instSMulInt : SMul ℤ (Adjointable A E F) :=
  ⟨fun z T ↦ mkOfInner (z • T.toContinuousLinearMap) (z • T.adjoint.toContinuousLinearMap)
    fun x y ↦ by simp [← Int.cast_smul_eq_zsmul ℂ, ← adjoint_inner_right]⟩

instance instSMulComplex : SMul ℂ (Adjointable A E F) :=
  ⟨fun c T ↦ mkOfInner (c • T.toContinuousLinearMap) (star c • T.adjoint.toContinuousLinearMap)
    fun x y ↦ by simp [← adjoint_inner_right]⟩

@[simp] theorem zero_apply (x : E) : (0 : Adjointable A E F) x = 0 := (rfl)
@[simp] theorem add_apply (T₁ T₂ : Adjointable A E F) (x : E) : (T₁ + T₂) x = T₁ x + T₂ x := (rfl)
@[simp] theorem neg_apply (T : Adjointable A E F) (x : E) : (-T) x = -T x := (rfl)
@[simp] theorem sub_apply (T₁ T₂ : Adjointable A E F) (x : E) : (T₁ - T₂) x = T₁ x - T₂ x := (rfl)
@[simp] theorem smul_apply (c : ℂ) (T : Adjointable A E F) (x : E) : (c • T) x = c • T x := (rfl)

@[simp]
theorem toContinuousLinearMap_zero : (0 : Adjointable A E F).toContinuousLinearMap = 0 := (rfl)

@[simp]
theorem toContinuousLinearMap_add (T₁ T₂ : Adjointable A E F) :
    (T₁ + T₂).toContinuousLinearMap = T₁.toContinuousLinearMap + T₂.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_neg (T : Adjointable A E F) :
    (-T).toContinuousLinearMap = -T.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_sub (T₁ T₂ : Adjointable A E F) :
    (T₁ - T₂).toContinuousLinearMap = T₁.toContinuousLinearMap - T₂.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_nsmul (n : ℕ) (T : Adjointable A E F) :
    (n • T).toContinuousLinearMap = n • T.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_zsmul (z : ℤ) (T : Adjointable A E F) :
    (z • T).toContinuousLinearMap = z • T.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_smul (c : ℂ) (T : Adjointable A E F) :
    (c • T).toContinuousLinearMap = c • T.toContinuousLinearMap := (rfl)

instance instAddCommGroup : AddCommGroup (Adjointable A E F) :=
  toContinuousLinearMap_injective.addCommGroup _ toContinuousLinearMap_zero
    toContinuousLinearMap_add toContinuousLinearMap_neg toContinuousLinearMap_sub
    (fun T n ↦ toContinuousLinearMap_nsmul n T) (fun T z ↦ toContinuousLinearMap_zsmul z T)

/-- The forgetful map as an additive monoid homomorphism. -/
def toContinuousLinearMapAddMonoidHom : Adjointable A E F →+ (E →L[ℂ] F) where
  toFun := toContinuousLinearMap
  map_zero' := toContinuousLinearMap_zero
  map_add' := toContinuousLinearMap_add

instance instModuleComplex : Module ℂ (Adjointable A E F) :=
  Function.Injective.module ℂ toContinuousLinearMapAddMonoidHom
    (by exact toContinuousLinearMap_injective) (by intro _ _; rfl)

/-- The forgetful map as a complex-linear map. -/
def toContinuousLinearMapₗ : Adjointable A E F →ₗ[ℂ] (E →L[ℂ] F) where
  toFun := toContinuousLinearMap
  map_add' := toContinuousLinearMap_add
  map_smul' := toContinuousLinearMap_smul

@[simp]
theorem adjoint_zero : (0 : Adjointable A E F).adjoint = 0 :=
  toContinuousLinearMap_injective rfl

@[simp]
theorem adjoint_add (T₁ T₂ : Adjointable A E F) :
    (T₁ + T₂).adjoint = T₁.adjoint + T₂.adjoint :=
  toContinuousLinearMap_injective rfl

@[simp]
theorem adjoint_neg (T : Adjointable A E F) : (-T).adjoint = -T.adjoint :=
  toContinuousLinearMap_injective rfl

@[simp]
theorem adjoint_sub (T₁ T₂ : Adjointable A E F) :
    (T₁ - T₂).adjoint = T₁.adjoint - T₂.adjoint :=
  toContinuousLinearMap_injective rfl

@[simp]
theorem adjoint_smul (c : ℂ) (T : Adjointable A E F) : (c • T).adjoint = star c • T.adjoint :=
  toContinuousLinearMap_injective rfl

@[simp]
theorem adjoint_eq_zero {T : Adjointable A E F} : T.adjoint = 0 ↔ T = 0 := by
  rw [← adjoint_zero (A := A) (E := E) (F := F), adjoint_inj]

/-! #### Identity, composition, and star-algebra structure on endomorphisms -/

variable (A E) in
/-- The identity operator as a bundled adjointable operator. -/
protected def id : Adjointable A E E :=
  mkOfInner (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ E) fun _ _ ↦ rfl

@[simp]
theorem id_apply (x : E) : Adjointable.id A E x = x := (rfl)

@[simp]
theorem toContinuousLinearMap_id :
    (Adjointable.id A E).toContinuousLinearMap = ContinuousLinearMap.id ℂ E := (rfl)

@[simp]
theorem adjoint_id : (Adjointable.id A E).adjoint = Adjointable.id A E :=
  toContinuousLinearMap_injective rfl

/-- Composition of bundled adjointable operators. -/
def comp (S : Adjointable A F G) (T : Adjointable A E F) : Adjointable A E G :=
  mkOfInner (S.toContinuousLinearMap.comp T.toContinuousLinearMap)
    (T.adjoint.toContinuousLinearMap.comp S.adjoint.toContinuousLinearMap) fun x z ↦ by
      simp [ContinuousLinearMap.comp_apply, ← adjoint_inner_right]

@[simp]
theorem comp_apply (S : Adjointable A F G) (T : Adjointable A E F) (x : E) :
    S.comp T x = S (T x) := (rfl)

@[simp]
theorem coe_comp (S : Adjointable A F G) (T : Adjointable A E F) :
    ⇑(S.comp T) = ⇑S ∘ ⇑T := (rfl)

@[simp]
theorem toContinuousLinearMap_comp (S : Adjointable A F G) (T : Adjointable A E F) :
    (S.comp T).toContinuousLinearMap = S.toContinuousLinearMap.comp T.toContinuousLinearMap := (rfl)

@[simp]
theorem adjoint_comp (S : Adjointable A F G) (T : Adjointable A E F) :
    (S.comp T).adjoint = T.adjoint.comp S.adjoint :=
  toContinuousLinearMap_injective rfl

theorem comp_assoc {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul A H] [CStarModule A H]
    (R : Adjointable A G H) (S : Adjointable A F G) (T : Adjointable A E F) :
    (R.comp S).comp T = R.comp (S.comp T) := by
  ext
  rfl

@[simp]
theorem id_comp (T : Adjointable A E F) : (Adjointable.id A F).comp T = T := by
  ext
  rfl

@[simp]
theorem comp_id (T : Adjointable A E F) : T.comp (Adjointable.id A E) = T := by
  ext
  rfl

@[simp]
theorem zero_comp (T : Adjointable A E F) : (0 : Adjointable A F G).comp T = 0 := by
  ext
  simp

@[simp]
theorem comp_zero (S : Adjointable A F G) : S.comp (0 : Adjointable A E F) = 0 := by
  ext
  simp

theorem add_comp (S₁ S₂ : Adjointable A F G) (T : Adjointable A E F) :
    (S₁ + S₂).comp T = S₁.comp T + S₂.comp T := by
  ext
  simp

theorem comp_add (S : Adjointable A F G) (T₁ T₂ : Adjointable A E F) :
    S.comp (T₁ + T₂) = S.comp T₁ + S.comp T₂ := by
  ext
  simp

theorem smul_comp (c : ℂ) (S : Adjointable A F G) (T : Adjointable A E F) :
    (c • S).comp T = c • (S.comp T) := by
  ext
  simp

theorem comp_smul (c : ℂ) (S : Adjointable A F G) (T : Adjointable A E F) :
    S.comp (c • T) = c • (S.comp T) := by
  ext
  simp

instance instOne : One (Adjointable A E E) := ⟨Adjointable.id A E⟩
instance instMul : Mul (Adjointable A E E) := ⟨comp⟩

instance instNatCast : NatCast (Adjointable A E E) :=
  ⟨fun n ↦ mkOfInner (n : E →L[ℂ] E) (n : E →L[ℂ] E) fun x y ↦ by
    rw [← Nat.smul_one_eq_cast]
    simp only [_root_.smul_apply, one_apply_eq_self,
      ← Nat.cast_smul_eq_nsmul ℂ, inner_smul_left_complex, inner_smul_right_complex, star_natCast]⟩

instance instIntCast : IntCast (Adjointable A E E) :=
  ⟨fun z ↦ mkOfInner (z : E →L[ℂ] E) (z : E →L[ℂ] E) fun x y ↦ by
    rw [← Int.smul_one_eq_cast]
    simp only [_root_.smul_apply, one_apply_eq_self,
      ← Int.cast_smul_eq_zsmul ℂ, inner_smul_left_complex, inner_smul_right_complex, star_intCast]⟩

instance instPow : Pow (Adjointable A E E) ℕ :=
  ⟨fun T n ↦ mkOfInner (T.toContinuousLinearMap ^ n) (T.adjoint.toContinuousLinearMap ^ n)
    fun x y ↦ by
      induction n generalizing x y with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ, pow_succ']
        simp only [ContinuousLinearMap.mul_def,
          ContinuousLinearMap.comp_apply, ih, toContinuousLinearMap_apply, ← adjoint_inner_right]⟩

theorem one_def : (1 : Adjointable A E E) = Adjointable.id A E := (rfl)
theorem mul_def (S T : Adjointable A E E) : S * T = S.comp T := (rfl)

@[simp] theorem one_apply (x : E) : (1 : Adjointable A E E) x = x := (rfl)
@[simp] theorem mul_apply (S T : Adjointable A E E) (x : E) : (S * T) x = S (T x) := (rfl)

@[simp]
theorem toContinuousLinearMap_one : (1 : Adjointable A E E).toContinuousLinearMap = 1 := (rfl)

@[simp]
theorem toContinuousLinearMap_mul (S T : Adjointable A E E) :
    (S * T).toContinuousLinearMap = S.toContinuousLinearMap * T.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_pow (T : Adjointable A E E) (n : ℕ) :
    (T ^ n).toContinuousLinearMap = T.toContinuousLinearMap ^ n := (rfl)

@[simp]
theorem toContinuousLinearMap_natCast (n : ℕ) :
    (n : Adjointable A E E).toContinuousLinearMap = n := (rfl)

@[simp]
theorem toContinuousLinearMap_intCast (z : ℤ) :
    (z : Adjointable A E E).toContinuousLinearMap = z := (rfl)

instance instRing : Ring (Adjointable A E E) :=
  toContinuousLinearMap_injective.ring _ toContinuousLinearMap_zero toContinuousLinearMap_one
    toContinuousLinearMap_add toContinuousLinearMap_mul toContinuousLinearMap_neg
    toContinuousLinearMap_sub (by intro _ _; rfl) (by intro _ _; rfl) (by intro _ _; rfl)
    toContinuousLinearMap_natCast toContinuousLinearMap_intCast

instance instAlgebraComplex : Algebra ℂ (Adjointable A E E) :=
  Algebra.ofModule
    (fun c S T ↦ by rw [mul_def, mul_def, smul_comp])
    (fun c S T ↦ by rw [mul_def, mul_def, comp_smul])

@[simp]
theorem algebraMap_apply (c : ℂ) :
    algebraMap ℂ (Adjointable A E E) c = c • 1 :=
  Algebra.algebraMap_eq_smul_one c

/-- The forgetful map from adjointable endomorphisms to continuous complex-linear endomorphisms
respects the identity, composition, and complex-algebra structure. -/
def toContinuousLinearMapAlgHom : Adjointable A E E →ₐ[ℂ] (E →L[ℂ] E) where
  toFun := toContinuousLinearMap
  map_one' := toContinuousLinearMap_one
  map_mul' := toContinuousLinearMap_mul
  map_zero' := toContinuousLinearMap_zero
  map_add' := toContinuousLinearMap_add
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]

@[simp]
theorem coe_toContinuousLinearMapAlgHom :
    ⇑(toContinuousLinearMapAlgHom (A := A) (E := E)) = toContinuousLinearMap := (rfl)

instance instStar : Star (Adjointable A E E) := ⟨adjoint⟩

theorem star_def (T : Adjointable A E E) : star T = T.adjoint := (rfl)

@[simp]
theorem star_apply (T : Adjointable A E E) (x : E) : (star T) x = T.adjoint x := (rfl)

@[simp]
theorem adjoint_one : (1 : Adjointable A E E).adjoint = 1 := adjoint_id

instance instStarRing : StarRing (Adjointable A E E) where
  star_involutive T := by exact adjoint_adjoint T
  star_mul S T := by exact adjoint_comp S T
  star_add S T := by exact adjoint_add S T

instance instStarModuleComplex : StarModule ℂ (Adjointable A E E) where
  star_smul c T := by exact adjoint_smul c T

/-- An adjointable endomorphism is self-adjoint if and only if it equals its adjoint. -/
theorem isSelfAdjoint_iff' {T : Adjointable A E E} : IsSelfAdjoint T ↔ T.adjoint = T := by
  rfl

/-! #### Natural left action of `Adjointable A E E` on `E` -/

instance instSMulModule : SMul (Adjointable A E E) E := ⟨fun T x ↦ T x⟩

@[simp]
theorem smul_def (T : Adjointable A E E) (x : E) : T • x = T x := (rfl)

instance instModuleEnd : Module (Adjointable A E E) E where
  one_smul _ := by rfl
  mul_smul _ _ _ := by rfl
  smul_zero T := map_zero T
  smul_add T := map_add T
  add_smul _ _ _ := by rfl
  zero_smul _ := by rfl

instance instSMulCommClassCoeff : SMulCommClass A (Adjointable A E E) E where
  smul_comm a T x := by exact (T.map_smul_coeff a x).symm

instance instSMulCommClassCoeffSymm : SMulCommClass (Adjointable A E E) A E :=
  SMulCommClass.symm A (Adjointable A E E) E

instance instIsScalarTowerComplex : IsScalarTower ℂ (Adjointable A E E) E where
  smul_assoc _ _ _ := by rfl

instance instSMulCommClassComplex : SMulCommClass ℂ (Adjointable A E E) E where
  smul_comm c T x := by exact (map_smul T c x).symm

/-! #### Operator norm pulled back from continuous linear maps -/

/-- The operator norm on `Adjointable A E F` is induced by the forgetful map to `E →L[ℂ] F`. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (Adjointable A E F) :=
  NormedAddCommGroup.induced (Adjointable A E F) (E →L[ℂ] F)
    toContinuousLinearMapAddMonoidHom (by exact toContinuousLinearMap_injective)

noncomputable instance instNormedSpaceComplex : NormedSpace ℂ (Adjointable A E F) where
  norm_smul_le c T := by exact norm_smul_le c T.toContinuousLinearMap

theorem norm_def (T : Adjointable A E F) : ‖T‖ = ‖T.toContinuousLinearMap‖ := (rfl)

@[simp]
theorem norm_toContinuousLinearMap (T : Adjointable A E F) :
    ‖T.toContinuousLinearMap‖ = ‖T‖ := (rfl)

@[simp]
theorem dist_toContinuousLinearMap (T₁ T₂ : Adjointable A E F) :
    dist T₁.toContinuousLinearMap T₂.toContinuousLinearMap = dist T₁ T₂ := (rfl)

/-- The forgetful map to continuous complex-linear operators is a linear isometry. -/
noncomputable def toContinuousLinearMapₗᵢ : Adjointable A E F →ₗᵢ[ℂ] (E →L[ℂ] F) where
  toLinearMap := toContinuousLinearMapₗ
  norm_map' _ := by rfl

@[simp]
theorem coe_toContinuousLinearMapₗᵢ :
    ⇑(toContinuousLinearMapₗᵢ (A := A) (E := E) (F := F)) = toContinuousLinearMap := (rfl)

theorem isometry_toContinuousLinearMap :
    Isometry (toContinuousLinearMap : Adjointable A E F → E →L[ℂ] F) :=
  toContinuousLinearMapₗᵢ.isometry

theorem le_opNorm (T : Adjointable A E F) (x : E) : ‖T x‖ ≤ ‖T‖ * ‖x‖ :=
  T.toContinuousLinearMap.le_opNorm x

theorem opNorm_le_bound (T : Adjointable A E F) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x, ‖T x‖ ≤ M * ‖x‖) : ‖T‖ ≤ M :=
  T.toContinuousLinearMap.opNorm_le_bound hM h

theorem opNorm_comp_le (S : Adjointable A F G) (T : Adjointable A E F) :
    ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ :=
  S.toContinuousLinearMap.opNorm_comp_le T.toContinuousLinearMap

noncomputable instance instNormedRing : NormedRing (Adjointable A E E) :=
  { instRing, instNormedAddCommGroup with
    dist_eq S T := by exact dist_eq_norm_neg_add S T
    norm_mul_le S T := by exact opNorm_comp_le S T }

noncomputable instance instNormedAlgebraComplex : NormedAlgebra ℂ (Adjointable A E E) where
  norm_smul_le := norm_smul_le

instance instIsBoundedSMulModule : IsBoundedSMul (Adjointable A E E) E :=
  IsBoundedSMul.of_norm_smul_le fun T x ↦ by exact le_opNorm T x

instance instContinuousSMulModule : ContinuousSMul (Adjointable A E E) E :=
  inferInstance

private theorem range_toProd :
    Set.range (fun T : Adjointable A E F ↦
      (T.toContinuousLinearMap, T.adjoint.toContinuousLinearMap)) =
      {p : (E →L[ℂ] F) × (F →L[ℂ] E) | ∀ x y, inner A (p.1 x) y = inner A x (p.2 y)} := by
  ext p
  refine ⟨?_, fun hp ↦ ⟨mkOfInner p.1 p.2 hp, rfl⟩⟩
  rintro ⟨T, rfl⟩ x y
  exact (T.adjoint_inner_right x y).symm

end Algebraic

/-! ### Adjoint isometry, completeness, and C⋆-algebra structure -/

section Analytic

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- An adjointable operator and its adjoint have the same operator norm. -/
@[simp]
theorem norm_adjoint (T : Adjointable A E F) : ‖T.adjoint‖ = ‖T‖ :=
  T.isAdjointPair'.norm_eq_cstarModule

/-- Taking the adjoint is a conjugate-linear isometric equivalence `Adjointable A E F ≃ₗᵢ⋆[ℂ]`
`Adjointable A F E`. -/
noncomputable def adjointₗᵢ : Adjointable A E F ≃ₗᵢ⋆[ℂ] Adjointable A F E where
  toFun := adjoint
  invFun := adjoint
  left_inv := adjoint_adjoint
  right_inv := adjoint_adjoint
  map_add' := adjoint_add
  map_smul' := adjoint_smul
  norm_map' := norm_adjoint

@[simp]
theorem adjointₗᵢ_apply (T : Adjointable A E F) : adjointₗᵢ T = T.adjoint := (rfl)

@[simp]
theorem adjointₗᵢ_symm :
    (adjointₗᵢ (A := A) (E := E) (F := F)).symm = adjointₗᵢ (A := A) (E := F) (F := E) :=
  LinearIsometryEquiv.ext fun _ ↦ rfl

/-- The C⋆-identity for adjointable operators: `‖T* ∘ T‖ = ‖T‖ ^ 2`. -/
theorem norm_adjoint_comp_self (T : Adjointable A E F) : ‖T.adjoint.comp T‖ = ‖T‖ ^ 2 :=
  T.isAdjointPair'.norm_adjoint_comp_self_cstarModule

/-- Dual C⋆-identity: `‖T ∘ T*‖ = ‖T‖ ^ 2`. -/
theorem norm_self_comp_adjoint (T : Adjointable A E F) : ‖T.comp T.adjoint‖ = ‖T‖ ^ 2 := by
  simpa only [adjoint_adjoint, norm_adjoint] using norm_adjoint_comp_self T.adjoint

@[simp]
theorem adjoint_comp_self_eq_zero {T : Adjointable A E F} : T.adjoint.comp T = 0 ↔ T = 0 := by
  rw [← norm_eq_zero, norm_adjoint_comp_self, sq_eq_zero_iff, norm_eq_zero]

@[simp]
theorem self_comp_adjoint_eq_zero {T : Adjointable A E F} : T.comp T.adjoint = 0 ↔ T = 0 := by
  rw [← norm_eq_zero, norm_self_comp_adjoint, sq_eq_zero_iff, norm_eq_zero]

instance instCStarRing : CStarRing (Adjointable A E E) where
  norm_mul_self_le T := by
    rw [star_def, mul_def, norm_adjoint_comp_self, sq]

/-! #### Completeness and automatic boundedness on complete Hilbert C⋆-modules -/

section Complete

/-- Embedding `T ↦ (T, T*)` into `(E →L[ℂ] F) × (F →L[ℂ] E)` is isometric because `‖T*‖ = ‖T‖`. -/
private theorem isometry_toProd :
    Isometry (fun T : Adjointable A E F ↦
      (T.toContinuousLinearMap, T.adjoint.toContinuousLinearMap)) :=
  Isometry.of_dist_eq fun T₁ T₂ ↦ by
    simp [dist_eq_norm, ← toContinuousLinearMap_sub, ← adjoint_sub]

/-- When `E` and `F` are complete Hilbert C⋆-modules, `Adjointable A E F` is a Banach space. -/
instance instCompleteSpace [CompleteSpace E] [CompleteSpace F] :
    CompleteSpace (Adjointable A E F) := by
  rw [completeSpace_iff_isComplete_range isometry_toProd.isUniformInducing, range_toProd]
  apply IsClosed.isComplete
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_eq
    ((CStarModule.continuous_inner (A := A) (E := F)).comp
      (((ContinuousLinearMap.apply ℂ F x).continuous.comp continuous_fst).prodMk continuous_const))
    ((CStarModule.continuous_inner (A := A) (E := E)).comp
      (continuous_const.prodMk ((ContinuousLinearMap.apply ℂ E y).continuous.comp continuous_snd)))

/-- The endomorphisms `Adjointable A E E` of a complete Hilbert C⋆-module `E` form a unital
C⋆-algebra. No nontriviality hypothesis on `E` is needed: the zero module yields the zero
C⋆-algebra. -/
noncomputable instance instCStarAlgebra [CompleteSpace E] : CStarAlgebra (Adjointable A E E) where

variable [CompleteSpace E] [CompleteSpace F]

/-- Between complete Hilbert C⋆-modules, any pair of plain functions satisfying
`⟪T x, y⟫_A = ⟪x, S y⟫_A` defines a bundled adjointable operator. -/
noncomputable def ofAdjointPair {T : E → F} {S : F → E}
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) : Adjointable A E F :=
  let h' := (isAdjointPair_inner_iff (A := A)).mpr h
  mkOfInner h'.toContinuousLinearMapCStarModule
    h'.symm_cstarModule.toContinuousLinearMapCStarModule fun x y ↦ by
      simp [h x y]

@[simp]
theorem ofAdjointPair_apply {T : E → F} {S : F → E}
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) (x : E) :
    ofAdjointPair h x = T x :=
  (isAdjointPair_inner_iff.mpr h).toContinuousLinearMapCStarModule_apply x

@[simp]
theorem adjoint_ofAdjointPair_apply {T : E → F} {S : F → E}
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) (y : F) :
    (ofAdjointPair h).adjoint y = S y :=
  (isAdjointPair_inner_iff.mpr h).symm_cstarModule.toContinuousLinearMapCStarModule_apply y

/-- Bundle any function `T : E → F` satisfying `IsAdjointable A T` between complete Hilbert
C⋆-modules as an `Adjointable` operator. -/
noncomputable def ofIsAdjointable {T : E → F} (h : IsAdjointable A T) : Adjointable A E F :=
  ofAdjointPair (Classical.choose_spec (isAdjointable_iff.mp h))

@[simp]
theorem ofIsAdjointable_apply {T : E → F} (h : IsAdjointable A T) (x : E) :
    ofIsAdjointable h x = T x :=
  ofAdjointPair_apply _ x

@[simp]
theorem coe_ofIsAdjointable {T : E → F} (h : IsAdjointable A T) :
    ⇑(ofIsAdjointable h) = T :=
  funext (ofIsAdjointable_apply h)

/-- Between complete Hilbert C⋆-modules, a plain function `T : E → F` comes from a bundled
`Adjointable A E F` operator if and only if `IsAdjointable A T` holds. -/
theorem exists_coe_eq_iff {T : E → F} :
    (∃ T' : Adjointable A E F, ⇑T' = T) ↔ IsAdjointable A T :=
  ⟨by rintro ⟨T', rfl⟩; exact T'.isAdjointable, fun h ↦ ⟨ofIsAdjointable h, coe_ofIsAdjointable h⟩⟩

/-- Between complete Hilbert C⋆-modules, a continuous complex-linear map `T : E →L[ℂ] F` is the
underlying map of an `Adjointable A E F` operator if and only if there exists a plain function
`S : F → E` satisfying `⟪T x, y⟫_A = ⟪x, S y⟫_A` for all `x` and `y`. -/
theorem exists_toContinuousLinearMap_eq_iff {T : E →L[ℂ] F} :
    (∃ T' : Adjointable A E F, T'.toContinuousLinearMap = T) ↔
      ∃ S : F → E, ∀ x y, inner A (T x) y = inner A x (S y) := by
  rw [← isAdjointable_iff (T := (T : E → F)), ← exists_coe_eq_iff]
  exact exists_congr fun T' ↦ DFunLike.coe_injective.eq_iff.symm

end Complete

end Analytic

end Adjointable

end CStarModule
