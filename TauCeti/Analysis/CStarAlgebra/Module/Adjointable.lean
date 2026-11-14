/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import TauCeti.Analysis.CStarAlgebra.Compression

/-!
# Adjointable operators on Hilbert C⋆-modules

Unlike bounded linear maps between Hilbert spaces, a bounded `A`-linear operator between Hilbert
C⋆-modules need not admit an adjoint for the `A`-valued inner product. When an adjoint exists it is
unique, bounded, complex-linear, and compatible with the coefficient action
(`LinearMap.IsAdjointPair.exists_continuousLinearMaps_cstarModule`). This file bundles such
operators into the Banach space `TauCeti.AdjointableMap A E F` and equips the endomorphism algebra
`TauCeti.AdjointableMap A E E` of a complete module with its unital C⋆-algebra structure, spectral
order, continuous functional calculus, and orthogonal projections. Adjointable isometries and module
unitaries are developed in `TauCeti.Analysis.CStarAlgebra.Module.Unitary`.

Following `Mathlib.Analysis.CStarAlgebra.Module.Defs`, the coefficient action on `CStarModule A E`
is written on the left (`a • x`); right Hilbert `B`-modules are obtained by taking `A = Bᵐᵒᵖ`, with
right action `x b = MulOpposite.op b • x` and `B`-valued inner product
`⟨x, y⟩_B = MulOpposite.unop (inner Bᵐᵒᵖ x y)`. Neither a unit in `A`, fullness, countable
generation, nor nontriviality of the modules is assumed; in particular the zero module is allowed.

## Main definitions

* `TauCeti.AdjointableMap A E F`: bundled bounded complex-linear maps `T : E →L[ℂ] F` equipped with
  a bounded adjoint `T.adjoint : AdjointableMap A F E` satisfying `⟪T x, y⟫_A = ⟪x, T.adjoint y⟫_A`.
  Because the inner product is nondegenerate, `T` determines `T.adjoint`, so equality of adjointable
  maps is extensional on vectors in `E`.
* `TauCeti.AdjointableMap.ofAdjointPair`: constructs an `AdjointableMap A E F` between complete
  modules from plain functions `T : E → F` and `S : F → E` satisfying `⟪T x, y⟫_A = ⟪x, S y⟫_A`.
* `TauCeti.AdjointableMap.toContinuousLinearMapₗᵢ` and
  `TauCeti.AdjointableMap.toContinuousLinearMapAlgHom`: the isometric forgetful linear map into
  `E →L[ℂ] F` and unital `ℂ`-algebra homomorphism into `E →L[ℂ] E`.
* `TauCeti.AdjointableMap.adjointₗᵢ`: the adjoint as a conjugate-linear isometric equivalence
  `AdjointableMap A E F ≃ₗᵢ⋆[ℂ] AdjointableMap A F E`.

## Main results

* `TauCeti.AdjointableMap.instCompleteSpace` and `TauCeti.AdjointableMap.instCStarAlgebra`:
  `AdjointableMap A E F` is complete when `E` and `F` are complete, and `AdjointableMap A E E` is a
  unital C⋆-algebra with its spectral `PartialOrder`, `StarOrderedRing`, and continuous functional
  calculus.
* `TauCeti.AdjointableMap.nonneg_iff_forall_inner_nonneg` and
  `TauCeti.AdjointableMap.le_iff_forall_inner_le`: an operator `T : AdjointableMap A E E` is
  positive in the C⋆-algebra `AdjointableMap A E E` if and only if `0 ≤ ⟪x, T x⟫_A` for every
  `x : E`, with no prior self-adjointness hypothesis.
* `TauCeti.AdjointableMap.inner_map_map_le_norm_sq_smul`: Paschke's inequality
  `⟪T x, T x⟫_A ≤ ‖T‖ ^ 2 • ⟪x, x⟫_A` for any `T : AdjointableMap A E F` when `E` is complete.
* `TauCeti.AdjointableMap.isClosed_range_of_isIdempotentElem` and
  `TauCeti.AdjointableMap.inner_eq_add_inner_one_sub_of_isStarProjection`: closed range for
  adjointable idempotents and orthogonal inner-product decomposition for adjointable star
  projections.

## References

* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2 (Definitions 2.17–2.18, Proposition 2.19, Corollary 2.22, Proposition 2.28).
* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1, 3,
  and 4 (Proposition 1.2, Lemma 4.1).
* Bruce Blackadar, *Operator Algebras*, II.7.1–II.7.2.
-/

public section

open CStarModule MulOpposite

namespace TauCeti

/-! ### Bundled adjointable operators -/

/-- A bounded adjointable operator between Hilbert C⋆-modules `E` and `F` over `A`: a continuous
`ℂ`-linear map `E →L[ℂ] F` equipped with a continuous `ℂ`-linear adjoint `F →L[ℂ] E` satisfying
`⟪T x, y⟫_A = ⟪x, T* y⟫_A`. Because the `A`-valued inner product separates points, the adjoint is
uniquely determined by the underlying map (`TauCeti.AdjointableMap.ext`). For right Hilbert
`B`-modules, take `A = Bᵐᵒᵖ`. -/
structure AdjointableMap (A E F : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
    extends E →L[ℂ] F where
  /-- The bounded adjoint map `F →L[ℂ] E`. -/
  adjoint' : F →L[ℂ] E
  /-- The defining adjoint identity `⟪T x, y⟫_A = ⟪x, T* y⟫_A`. -/
  inner_map_eq' (x : E) (y : F) : inner A (toContinuousLinearMap x) y = inner A x (adjoint' y)

namespace AdjointableMap

section Basic

variable {A E F G : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

instance instFunLike : FunLike (AdjointableMap A E F) E F where
  coe T := T.toContinuousLinearMap
  coe_injective T S h := by
    cases T with | mk T₁ T₂ hT =>
    cases S with | mk S₁ S₂ hS =>
    have h₁ : T₁ = S₁ := DFunLike.coe_injective h
    subst h₁
    have h₂ : ⇑T₂ = ⇑S₂ :=
      (CStarModule.isAdjointPair_inner_iff.mpr hT).unique_right_cstarModule
        (CStarModule.isAdjointPair_inner_iff.mpr hS)
    congr
    exact DFunLike.coe_injective h₂

instance instContinuousLinearMapClass : ContinuousLinearMapClass (AdjointableMap A E F) ℂ E F where
  map_add T := map_add T.toContinuousLinearMap
  map_smulₛₗ T := map_smulₛₗ T.toContinuousLinearMap
  map_continuous T := T.toContinuousLinearMap.continuous

@[simp]
theorem toContinuousLinearMap_apply (T : AdjointableMap A E F) (x : E) :
    T.toContinuousLinearMap x = T x := (rfl)

@[simp]
theorem coe_toContinuousLinearMap (T : AdjointableMap A E F) :
    ⇑T.toContinuousLinearMap = ⇑T := (rfl)

@[simp]
theorem coe_mk (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) :
    ⇑(⟨T, S, h⟩ : AdjointableMap A E F) = ⇑T := (rfl)

theorem mk_apply (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) (x : E) :
    (⟨T, S, h⟩ : AdjointableMap A E F) x = T x := (rfl)

/-- Adjointable maps are determined by their action on vectors. -/
@[ext]
theorem ext {T S : AdjointableMap A E F} (h : ∀ x, T x = S x) : T = S :=
  DFunLike.ext T S h

/-- The forgetful map to `E →L[ℂ] F` is injective. -/
theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : AdjointableMap A E F → E →L[ℂ] F) :=
  fun _ _ h ↦ ext fun x ↦ DFunLike.congr_fun h x

@[simp]
theorem toContinuousLinearMap_inj {T S : AdjointableMap A E F} :
    T.toContinuousLinearMap = S.toContinuousLinearMap ↔ T = S :=
  toContinuousLinearMap_injective.eq_iff

/-- Copy of an `AdjointableMap` with a new `toFun` equal to the old one. -/
protected def copy (T : AdjointableMap A E F) (f : E → F) (hf : f = ⇑T) :
    AdjointableMap A E F where
  toContinuousLinearMap := T.toContinuousLinearMap.copy f hf
  adjoint' := T.adjoint'
  inner_map_eq' x y := by simpa [hf] using T.inner_map_eq' x y

@[simp]
theorem coe_copy (T : AdjointableMap A E F) (f : E → F) (hf : f = ⇑T) :
    ⇑(T.copy f hf) = f := (rfl)

theorem copy_eq (T : AdjointableMap A E F) (f : E → F) (hf : f = ⇑T) :
    T.copy f hf = T :=
  DFunLike.ext' hf

/-- The adjoint of an adjointable operator `T : E → F`, as an adjointable operator `F → E`. -/
def adjoint (T : AdjointableMap A E F) : AdjointableMap A F E where
  toContinuousLinearMap := T.adjoint'
  adjoint' := T.toContinuousLinearMap
  inner_map_eq' y x :=
    (CStarModule.isAdjointPair_inner_iff.mpr T.inner_map_eq').symm_cstarModule.inner_eq_cstarModule
      y x

@[simp]
theorem adjoint'_eq (T : AdjointableMap A E F) :
    T.adjoint' = T.adjoint.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_adjoint_mk (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) :
    (⟨T, S, h⟩ : AdjointableMap A E F).adjoint.toContinuousLinearMap = S := (rfl)

@[simp]
theorem adjoint_mk_apply (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) (y : F) :
    (⟨T, S, h⟩ : AdjointableMap A E F).adjoint y = S y := (rfl)

/-- The adjoint operation is involutive. -/
@[simp]
theorem adjoint_adjoint (T : AdjointableMap A E F) : T.adjoint.adjoint = T := (rfl)

theorem adjoint_injective :
    Function.Injective (adjoint : AdjointableMap A E F → AdjointableMap A F E) :=
  Function.LeftInverse.injective adjoint_adjoint

@[simp]
theorem adjoint_inj {T S : AdjointableMap A E F} : T.adjoint = S.adjoint ↔ T = S :=
  adjoint_injective.eq_iff

/-- Defining identity `⟪x, T.adjoint y⟫_A = ⟪T x, y⟫_A` of the adjoint. -/
theorem adjoint_inner_right (T : AdjointableMap A E F) (x : E) (y : F) :
    inner A x (T.adjoint y) = inner A (T x) y :=
  (T.inner_map_eq' x y).symm

/-- Symmetric form `⟪T.adjoint y, x⟫_A = ⟪y, T x⟫_A` of the adjoint identity. -/
theorem adjoint_inner_left (T : AdjointableMap A E F) (x : E) (y : F) :
    inner A (T.adjoint y) x = inner A y (T x) :=
  T.adjoint.inner_map_eq' y x

/-- Every `AdjointableMap` forms a `LinearMap.IsAdjointPair` with its adjoint. -/
theorem isAdjointPair (T : AdjointableMap A E F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T T.adjoint :=
  CStarModule.isAdjointPair_inner_iff.mpr fun x y ↦ (T.adjoint_inner_right x y).symm

/-- Uniqueness characterization of the adjoint: `S = T.adjoint` iff `⟪T x, y⟫_A = ⟪x, S y⟫_A`
for all `x` and `y`. -/
theorem eq_adjoint_iff {S : AdjointableMap A F E} {T : AdjointableMap A E F} :
    S = T.adjoint ↔ ∀ x y, inner A (T x) y = inner A x (S y) :=
  ⟨fun h x y ↦ h ▸ (T.adjoint_inner_right x y).symm, fun h ↦
    ext fun y ↦ congrFun
      ((CStarModule.isAdjointPair_inner_iff.mpr h).unique_right_cstarModule T.isAdjointPair) y⟩

/-- Every adjointable operator automatically commutes with the `A`-action; for right Hilbert
`B`-modules (`A = Bᵐᵒᵖ`) this states right `B`-linearity `T (x b) = (T x) b`. -/
@[simp]
theorem map_smul_coeff (T : AdjointableMap A E F) (a : A) (x : E) :
    T (a • x) = a • T x :=
  T.isAdjointPair.map_smul_coeff_cstarModule a x

/-! #### Linear structure and composition -/

instance instZero : Zero (AdjointableMap A E F) where
  zero :=
    { toContinuousLinearMap := 0
      adjoint' := 0
      inner_map_eq' := fun _ _ ↦ by simp }

instance instIsZeroApply : IsZeroApply (AdjointableMap A E F) where

instance instInhabited : Inhabited (AdjointableMap A E F) := ⟨0⟩

instance instSubsingleton [Subsingleton F] : Subsingleton (AdjointableMap A E F) :=
  toContinuousLinearMap_injective.subsingleton

instance instUnique [Subsingleton F] : Unique (AdjointableMap A E F) :=
  uniqueOfSubsingleton 0

instance instSubsingletonLeft [Subsingleton E] : Subsingleton (AdjointableMap A E F) where
  allEq T S := ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero]

instance instUniqueLeft [Subsingleton E] : Unique (AdjointableMap A E F) :=
  uniqueOfSubsingleton 0

instance instAdd : Add (AdjointableMap A E F) where
  add T S :=
    { toContinuousLinearMap := T.toContinuousLinearMap + S.toContinuousLinearMap
      adjoint' := T.adjoint' + S.adjoint'
      inner_map_eq' := fun x y ↦ by simp [T.adjoint_inner_right, S.adjoint_inner_right] }

instance instIsAddApply : IsAddApply (AdjointableMap A E F) where

instance instNeg : Neg (AdjointableMap A E F) where
  neg T :=
    { toContinuousLinearMap := -T.toContinuousLinearMap
      adjoint' := -T.adjoint'
      inner_map_eq' := fun x y ↦ by simp [T.adjoint_inner_right] }

instance instIsNegApply : IsNegApply (AdjointableMap A E F) where

instance instSub : Sub (AdjointableMap A E F) where
  sub T S :=
    { toContinuousLinearMap := T.toContinuousLinearMap - S.toContinuousLinearMap
      adjoint' := T.adjoint' - S.adjoint'
      inner_map_eq' := fun x y ↦ by simp [T.adjoint_inner_right, S.adjoint_inner_right] }

instance instIsSubApply : IsSubApply (AdjointableMap A E F) where

instance instSMulComplex : SMul ℂ (AdjointableMap A E F) where
  smul c T :=
    { toContinuousLinearMap := c • T.toContinuousLinearMap
      adjoint' := star c • T.adjoint'
      inner_map_eq' := fun x y ↦ by simp [T.adjoint_inner_right] }

instance instIsSMulApplyComplex : IsSMulApply ℂ (AdjointableMap A E F) where

@[simp] theorem toContinuousLinearMap_zero :
    (0 : AdjointableMap A E F).toContinuousLinearMap = 0 := (rfl)
@[simp] theorem toContinuousLinearMap_add (T S : AdjointableMap A E F) :
    (T + S).toContinuousLinearMap = T.toContinuousLinearMap + S.toContinuousLinearMap := (rfl)
@[simp] theorem toContinuousLinearMap_neg (T : AdjointableMap A E F) :
    (-T).toContinuousLinearMap = -T.toContinuousLinearMap := (rfl)
@[simp] theorem toContinuousLinearMap_sub (T S : AdjointableMap A E F) :
    (T - S).toContinuousLinearMap = T.toContinuousLinearMap - S.toContinuousLinearMap := (rfl)
@[simp] theorem toContinuousLinearMap_smul (c : ℂ) (T : AdjointableMap A E F) :
    (c • T).toContinuousLinearMap = c • T.toContinuousLinearMap := (rfl)

@[simp] theorem adjoint_zero : (0 : AdjointableMap A E F).adjoint = 0 := (rfl)
@[simp] theorem adjoint_add (T S : AdjointableMap A E F) :
    (T + S).adjoint = T.adjoint + S.adjoint := (rfl)
@[simp] theorem adjoint_neg (T : AdjointableMap A E F) : (-T).adjoint = -T.adjoint := (rfl)
@[simp] theorem adjoint_sub (T S : AdjointableMap A E F) :
    (T - S).adjoint = T.adjoint - S.adjoint := (rfl)

@[simp]
theorem adjoint_smul (c : ℂ) (T : AdjointableMap A E F) :
    (c • T).adjoint = star c • T.adjoint :=
  toContinuousLinearMap_injective rfl

instance instSMulNat : SMul ℕ (AdjointableMap A E F) where
  smul n T :=
    { toContinuousLinearMap := n • T.toContinuousLinearMap
      adjoint' := n • T.adjoint'
      inner_map_eq' := fun x y ↦ by
        simpa [Nat.cast_smul_eq_nsmul ℂ] using ((n : ℂ) • T).inner_map_eq' x y }

instance instIsSMulApplyNat : IsSMulApply ℕ (AdjointableMap A E F) where

instance instSMulInt : SMul ℤ (AdjointableMap A E F) where
  smul n T :=
    { toContinuousLinearMap := n • T.toContinuousLinearMap
      adjoint' := n • T.adjoint'
      inner_map_eq' := fun x y ↦ by
        simpa [Int.cast_smul_eq_zsmul ℂ] using ((n : ℂ) • T).inner_map_eq' x y }

instance instIsSMulApplyInt : IsSMulApply ℤ (AdjointableMap A E F) where

instance instAddCommGroup : AddCommGroup (AdjointableMap A E F) :=
  toContinuousLinearMap_injective.addCommGroup _
    toContinuousLinearMap_zero toContinuousLinearMap_add toContinuousLinearMap_neg
    toContinuousLinearMap_sub (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance instModuleComplex : Module ℂ (AdjointableMap A E F) :=
  Function.Injective.module ℂ
    { toFun := toContinuousLinearMap, map_zero' := rfl, map_add' := toContinuousLinearMap_add }
    toContinuousLinearMap_injective toContinuousLinearMap_smul

instance instIsSMulApplyReal : IsSMulApply ℝ (AdjointableMap A E F) where

/-- The forgetful `ℂ`-linear map from `AdjointableMap A E F` to `E →L[ℂ] F`. -/
def toContinuousLinearMapLinear : AdjointableMap A E F →ₗ[ℂ] E →L[ℂ] F where
  toFun := toContinuousLinearMap
  map_add' := toContinuousLinearMap_add
  map_smul' := toContinuousLinearMap_smul

@[simp] theorem toContinuousLinearMapLinear_apply (T : AdjointableMap A E F) :
    toContinuousLinearMapLinear T = T.toContinuousLinearMap := (rfl)

/-- The adjoint bundled as a conjugate-linear equivalence
`AdjointableMap A E F ≃ₗ⋆[ℂ] AdjointableMap A F E`. -/
def adjointEquiv : AdjointableMap A E F ≃ₗ⋆[ℂ] AdjointableMap A F E where
  toFun := adjoint
  invFun := adjoint
  left_inv := adjoint_adjoint
  right_inv := adjoint_adjoint
  map_add' := adjoint_add
  map_smul' := adjoint_smul

@[simp] theorem adjointEquiv_apply (T : AdjointableMap A E F) : adjointEquiv T = T.adjoint := (rfl)
@[simp] theorem adjointEquiv_symm :
    (adjointEquiv : AdjointableMap A E F ≃ₗ⋆[ℂ] AdjointableMap A F E).symm = adjointEquiv := (rfl)

/-- The identity operator on a Hilbert C⋆-module as an adjointable map. -/
protected def id (A E : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] :
    AdjointableMap A E E where
  toContinuousLinearMap := ContinuousLinearMap.id ℂ E
  adjoint' := ContinuousLinearMap.id ℂ E
  inner_map_eq' _ _ := rfl

@[simp] theorem toContinuousLinearMap_id :
    (AdjointableMap.id A E).toContinuousLinearMap = ContinuousLinearMap.id ℂ E := (rfl)
@[simp] theorem id_apply (x : E) : AdjointableMap.id A E x = x := (rfl)
@[simp] theorem adjoint_id : (AdjointableMap.id A E).adjoint = AdjointableMap.id A E := (rfl)

instance instNontrivial [Nontrivial E] : Nontrivial (AdjointableMap A E E) :=
  ⟨⟨.id A E, 0, fun h ↦
    let ⟨x, hx⟩ := exists_ne (0 : E)
    hx (by simpa using DFunLike.congr_fun h x)⟩⟩

/-- Composition of adjointable operators, with `(S.comp T).adjoint = T.adjoint.comp S.adjoint`. -/
def comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    AdjointableMap A E G where
  toContinuousLinearMap := S.toContinuousLinearMap.comp T.toContinuousLinearMap
  adjoint' := T.adjoint'.comp S.adjoint'
  inner_map_eq' x z := (S.inner_map_eq' (T x) z).trans (T.inner_map_eq' x (S.adjoint z))

@[simp] theorem toContinuousLinearMap_comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (S.comp T).toContinuousLinearMap = S.toContinuousLinearMap.comp T.toContinuousLinearMap := (rfl)
@[simp] theorem comp_apply (S : AdjointableMap A F G) (T : AdjointableMap A E F) (x : E) :
    S.comp T x = S (T x) := (rfl)

/-- The adjoint reverses composition: `(S ∘ T)* = T* ∘ S*`. -/
@[simp] theorem adjoint_comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (S.comp T).adjoint = T.adjoint.comp S.adjoint := (rfl)

theorem comp_assoc {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul A H]
    [CStarModule A H] (R : AdjointableMap A G H) (S : AdjointableMap A F G)
    (T : AdjointableMap A E F) :
    (R.comp S).comp T = R.comp (S.comp T) := (rfl)

@[simp] theorem id_comp (T : AdjointableMap A E F) : (AdjointableMap.id A F).comp T = T :=
  ext fun _ ↦ rfl
@[simp] theorem comp_id (T : AdjointableMap A E F) : T.comp (AdjointableMap.id A E) = T :=
  ext fun _ ↦ rfl
@[simp] theorem zero_comp (T : AdjointableMap A E F) : (0 : AdjointableMap A F G).comp T = 0 :=
  ext fun _ ↦ rfl
@[simp] theorem comp_zero (S : AdjointableMap A F G) : S.comp (0 : AdjointableMap A E F) = 0 :=
  ext fun _ ↦ map_zero S

theorem add_comp (S₁ S₂ : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (S₁ + S₂).comp T = S₁.comp T + S₂.comp T :=
  ext fun _ ↦ rfl

theorem comp_add (S : AdjointableMap A F G) (T₁ T₂ : AdjointableMap A E F) :
    S.comp (T₁ + T₂) = S.comp T₁ + S.comp T₂ :=
  ext fun _ ↦ map_add S _ _

theorem smul_comp (c : ℂ) (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (c • S).comp T = c • (S.comp T) :=
  ext fun _ ↦ rfl

theorem comp_smul (c : ℂ) (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    S.comp (c • T) = c • (S.comp T) :=
  ext fun _ ↦ map_smul S c _

/-! #### Endomorphism algebra, star structure, and natural action on the module -/

instance instOne : One (AdjointableMap A E E) := ⟨AdjointableMap.id A E⟩
instance instMul : Mul (AdjointableMap A E E) := ⟨comp⟩

theorem one_def : (1 : AdjointableMap A E E) = AdjointableMap.id A E := (rfl)
theorem mul_def (S T : AdjointableMap A E E) : S * T = S.comp T := (rfl)

instance instIsOneApplyEqSelf : IsOneApplyEqSelf (AdjointableMap A E E) where
instance instIsMulApplyEqComp : IsMulApplyEqComp (AdjointableMap A E E) where

@[simp] theorem toContinuousLinearMap_one :
    (1 : AdjointableMap A E E).toContinuousLinearMap = 1 := (rfl)
@[simp] theorem toContinuousLinearMap_mul (S T : AdjointableMap A E E) :
    (S * T).toContinuousLinearMap = S.toContinuousLinearMap * T.toContinuousLinearMap := (rfl)

instance instPowNat : Pow (AdjointableMap A E E) ℕ where
  pow T n :=
    { toContinuousLinearMap := T.toContinuousLinearMap ^ n
      adjoint' := T.adjoint' ^ n
      inner_map_eq' := fun x y ↦ by
        induction n generalizing x y with
        | zero =>
          simp only [pow_zero, one_apply_eq_self]
        | succ k hk =>
          rw [pow_succ', pow_succ, mul_apply_eq_comp, mul_apply_eq_comp]
          exact (T.inner_map_eq' _ y).trans (hk x (T.adjoint' y)) }

@[simp] theorem toContinuousLinearMap_pow (T : AdjointableMap A E E) (n : ℕ) :
    (T ^ n).toContinuousLinearMap = T.toContinuousLinearMap ^ n := (rfl)

instance instNatCast : NatCast (AdjointableMap A E E) := ⟨fun n ↦ n • 1⟩
instance instIntCast : IntCast (AdjointableMap A E E) := ⟨fun n ↦ n • 1⟩

instance instIsNatCastApplyEqSMul : IsNatCastApplyEqSMul (AdjointableMap A E E) where
instance instIsIntCastApplyEqSMul : IsIntCastApplyEqSMul (AdjointableMap A E E) where

instance instRing : Ring (AdjointableMap A E E) :=
  toContinuousLinearMap_injective.ring _
    toContinuousLinearMap_zero toContinuousLinearMap_one toContinuousLinearMap_add
    toContinuousLinearMap_mul toContinuousLinearMap_neg toContinuousLinearMap_sub
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (by intro n; exact nsmul_one n) (by intro n; exact zsmul_one n)

instance instAlgebraComplex : Algebra ℂ (AdjointableMap A E E) :=
  Algebra.ofModule (by intro c S T; exact smul_comp c S T) (by intro c S T; exact comp_smul c S T)

/-- The forgetful `ℂ`-algebra homomorphism from `AdjointableMap A E E` to `E →L[ℂ] E`. -/
def toContinuousLinearMapAlgHom : AdjointableMap A E E →ₐ[ℂ] E →L[ℂ] E where
  toFun := toContinuousLinearMap
  map_one' := toContinuousLinearMap_one
  map_mul' := toContinuousLinearMap_mul
  map_zero' := toContinuousLinearMap_zero
  map_add' := toContinuousLinearMap_add
  commutes' _ := by ext; rfl

@[simp] theorem toContinuousLinearMapAlgHom_apply (T : AdjointableMap A E E) :
    toContinuousLinearMapAlgHom T = T.toContinuousLinearMap := (rfl)

instance instStar : Star (AdjointableMap A E E) := ⟨adjoint⟩

theorem star_eq_adjoint (T : AdjointableMap A E E) : star T = T.adjoint := (rfl)

instance instStarRing : StarRing (AdjointableMap A E E) where
  star_involutive T := by exact adjoint_adjoint T
  star_mul S T := by exact adjoint_comp S T
  star_add S T := by exact adjoint_add S T

instance instStarModuleComplex : StarModule ℂ (AdjointableMap A E E) where
  star_smul c T := by exact adjoint_smul c T

/-- The natural left action of `AdjointableMap A E E` on the module `E` by evaluation. -/
instance instSMulApply : SMul (AdjointableMap A E E) E := ⟨fun T x ↦ T x⟩

@[simp] protected theorem smul_def (T : AdjointableMap A E E) (x : E) : T • x = T x := (rfl)

instance applyModule : Module (AdjointableMap A E E) E where
  one_smul x := by exact one_apply_eq_self x
  mul_smul S T x := by exact mul_apply_eq_comp S T x
  smul_zero T := map_zero T
  smul_add T := map_add T
  add_smul S T x := by exact add_apply S T x
  zero_smul x := by exact zero_apply x

instance applyFaithfulSMul : FaithfulSMul (AdjointableMap A E E) E :=
  ⟨fun {_ _} h ↦ ext h⟩

instance applySMulCommClassComplexLeft : SMulCommClass ℂ (AdjointableMap A E E) E where
  smul_comm c T x := (map_smul T c x).symm

instance applySMulCommClassComplexRight : SMulCommClass (AdjointableMap A E E) ℂ E where
  smul_comm T c x := map_smul T c x

/-- The natural left action of `AdjointableMap A E E` on `E` commutes with the coefficient action
of `A` (in particular, with the right `B`-action when `A = Bᵐᵒᵖ`). -/
instance applySMulCommClassCoeffLeft : SMulCommClass A (AdjointableMap A E E) E where
  smul_comm a T x := (T.map_smul_coeff a x).symm

instance applySMulCommClassCoeffRight : SMulCommClass (AdjointableMap A E E) A E where
  smul_comm T a x := T.map_smul_coeff a x

instance applyIsScalarTowerComplex : IsScalarTower ℂ (AdjointableMap A E E) E where
  smul_assoc _ _ _ := rfl

@[simp]
theorem algebraMap_apply {R : Type*} [CommSemiring R] [SMul R E]
    [Algebra R (AdjointableMap A E E)] [IsScalarTower R (AdjointableMap A E E) E]
    (r : R) (x : E) :
    algebraMap R (AdjointableMap A E E) r x = r • x := by
  rw [Algebra.algebraMap_eq_smul_one, ← AdjointableMap.smul_def,
    smul_one_smul (AdjointableMap A E E)]

end Basic

/-! ### Right-module inner-product convenience lemmas -/

section Right

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- Right-module form `⟨x, T.adjoint y⟩_B = ⟨T x, y⟩_B` of the adjoint identity. -/
theorem unop_adjoint_inner_right (T : AdjointableMap Bᵐᵒᵖ E F) (x : E) (y : F) :
    unop (inner Bᵐᵒᵖ x (T.adjoint y)) = unop (inner Bᵐᵒᵖ (T x) y) :=
  congrArg unop (T.adjoint_inner_right x y)

/-- Symmetric right-module form `⟨T.adjoint y, x⟩_B = ⟨y, T x⟩_B` of the adjoint identity. -/
theorem unop_adjoint_inner_left (T : AdjointableMap Bᵐᵒᵖ E F) (x : E) (y : F) :
    unop (inner Bᵐᵒᵖ (T.adjoint y) x) = unop (inner Bᵐᵒᵖ y (T x)) :=
  congrArg unop (T.adjoint_inner_left x y)

end Right

/-! ### Operator norm, isometric forgetful map, completeness, and C⋆-algebra structure -/

section Norm

variable {A E F G : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (AdjointableMap A E F) :=
  NormedAddCommGroup.induced (AdjointableMap A E F) (E →L[ℂ] F)
    ({ toFun := toContinuousLinearMap
       map_zero' := rfl
       map_add' := toContinuousLinearMap_add } : AdjointableMap A E F →+ E →L[ℂ] F)
    toContinuousLinearMap_injective

theorem norm_def (T : AdjointableMap A E F) : ‖T‖ = ‖T.toContinuousLinearMap‖ := (rfl)

@[simp]
theorem norm_toContinuousLinearMap (T : AdjointableMap A E F) :
    ‖T.toContinuousLinearMap‖ = ‖T‖ := (rfl)

noncomputable instance instNormedSpaceComplex : NormedSpace ℂ (AdjointableMap A E F) where
  norm_smul_le c T := T.toContinuousLinearMap.opNorm_smul_le c

/-- The forgetful map from `AdjointableMap A E F` to `E →L[ℂ] F` as a `ℂ`-linear isometry. -/
noncomputable def toContinuousLinearMapₗᵢ : AdjointableMap A E F →ₗᵢ[ℂ] E →L[ℂ] F where
  toLinearMap := toContinuousLinearMapLinear
  norm_map' _ := rfl

@[simp]
theorem toContinuousLinearMapₗᵢ_apply (T : AdjointableMap A E F) :
    toContinuousLinearMapₗᵢ T = T.toContinuousLinearMap := (rfl)

theorem isometry_toContinuousLinearMap :
    Isometry (toContinuousLinearMap : AdjointableMap A E F → E →L[ℂ] F) :=
  (toContinuousLinearMapₗᵢ (A := A) (E := E) (F := F)).isometry

theorem le_opNorm (T : AdjointableMap A E F) (x : E) : ‖T x‖ ≤ ‖T‖ * ‖x‖ :=
  T.toContinuousLinearMap.le_opNorm x

theorem opNorm_le_bound (T : AdjointableMap A E F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖T x‖ ≤ M * ‖x‖) : ‖T‖ ≤ M :=
  T.toContinuousLinearMap.opNorm_le_bound hMp hM

theorem opNorm_comp_le (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ :=
  S.toContinuousLinearMap.opNorm_comp_le T.toContinuousLinearMap

/-- Composition of adjointable operators is jointly continuous for the operator norm. -/
theorem continuous_comp :
    Continuous (fun p : AdjointableMap A F G × AdjointableMap A E F ↦ p.1.comp p.2) :=
  (isometry_toContinuousLinearMap (A := A) (E := E) (F := G)).comp_continuous_iff.mp <|
    (isometry_toContinuousLinearMap.continuous.comp continuous_fst).clm_comp
      (isometry_toContinuousLinearMap.continuous.comp continuous_snd)

noncomputable instance instNormedRing : NormedRing (AdjointableMap A E E) where
  dist_eq := instNormedAddCommGroup.dist_eq
  norm_mul_le S T := by rw [mul_def]; exact opNorm_comp_le S T

@[simp]
theorem norm_id [Nontrivial E] : ‖AdjointableMap.id A E‖ = 1 := by
  rw [← norm_toContinuousLinearMap, toContinuousLinearMap_id]
  exact ContinuousLinearMap.norm_id

instance instNormOneClass [Nontrivial E] : NormOneClass (AdjointableMap A E E) :=
  ⟨by rw [one_def]; exact norm_id⟩

noncomputable instance instNormedAlgebraComplex :
    NormedAlgebra ℂ (AdjointableMap A E E) where
  norm_smul_le := instNormedSpaceComplex.norm_smul_le

instance instIsBoundedSMulApply : IsBoundedSMul (AdjointableMap A E E) E where
  dist_smul_pair' T x y := by simpa [dist_eq_norm, sub_zero, map_sub] using T.le_opNorm (x - y)
  dist_pair_smul' T S x := by simpa [dist_eq_norm] using (T - S).le_opNorm x

section StarOrdered

variable [StarOrderedRing A]

/-- An adjointable operator and its adjoint have the same operator norm. -/
@[simp]
theorem norm_adjoint (T : AdjointableMap A E F) : ‖T.adjoint‖ = ‖T‖ :=
  T.isAdjointPair.norm_eq_cstarModule

/-- The adjoint bundled as a conjugate-linear isometric equivalence
`AdjointableMap A E F ≃ₗᵢ⋆[ℂ] AdjointableMap A F E`. -/
noncomputable def adjointₗᵢ : AdjointableMap A E F ≃ₗᵢ⋆[ℂ] AdjointableMap A F E where
  toLinearEquiv := adjointEquiv
  norm_map' T := norm_adjoint T

@[simp]
theorem adjointₗᵢ_apply (T : AdjointableMap A E F) : adjointₗᵢ T = T.adjoint := (rfl)

@[simp]
theorem adjointₗᵢ_symm :
    (adjointₗᵢ : AdjointableMap A E F ≃ₗᵢ⋆[ℂ] AdjointableMap A F E).symm = adjointₗᵢ :=
  LinearIsometryEquiv.ext fun _ ↦ rfl

theorem continuous_adjoint :
    Continuous (adjoint : AdjointableMap A E F → AdjointableMap A F E) :=
  adjointₗᵢ.continuous

/-- The C⋆-identity `‖T* ∘ T‖ = ‖T‖ ^ 2` for rectangular adjointable operators. -/
@[simp]
theorem norm_adjoint_comp_self (T : AdjointableMap A E F) :
    ‖T.adjoint.comp T‖ = ‖T‖ ^ 2 :=
  T.isAdjointPair.norm_adjoint_comp_self_cstarModule

/-- Dual C⋆-identity `‖T ∘ T*‖ = ‖T‖ ^ 2` for rectangular adjointable operators. -/
@[simp]
theorem norm_self_comp_adjoint (T : AdjointableMap A E F) :
    ‖T.comp T.adjoint‖ = ‖T‖ ^ 2 := by
  simpa only [adjoint_adjoint, norm_adjoint] using norm_adjoint_comp_self T.adjoint

@[simp]
theorem adjoint_comp_self_eq_zero_iff {T : AdjointableMap A E F} :
    T.adjoint.comp T = 0 ↔ T = 0 := by
  rw [← norm_eq_zero, norm_adjoint_comp_self, sq_eq_zero_iff, norm_eq_zero]

@[simp]
theorem self_comp_adjoint_eq_zero_iff {T : AdjointableMap A E F} :
    T.comp T.adjoint = 0 ↔ T = 0 := by
  rw [← norm_eq_zero, norm_self_comp_adjoint, sq_eq_zero_iff, norm_eq_zero]

instance instNormedStarGroup : NormedStarGroup (AdjointableMap A E E) where
  norm_star_le T := (norm_adjoint T).le

instance instCStarRing : CStarRing (AdjointableMap A E E) where
  norm_mul_self_le T := by
    rw [star_eq_adjoint, mul_def, norm_adjoint_comp_self, sq]

/-- Product map `T ↦ (T, T.adjoint)` into `(E →L[ℂ] F) × (F →L[ℂ] E)`. -/
private def toProd (T : AdjointableMap A E F) : (E →L[ℂ] F) × (F →L[ℂ] E) :=
  (T.toContinuousLinearMap, T.adjoint.toContinuousLinearMap)

omit [StarOrderedRing A] in
private theorem range_toProd_eq :
    Set.range (toProd (A := A) (E := E) (F := F)) =
      ⋂ (x : E) (y : F),
        {p : (E →L[ℂ] F) × (F →L[ℂ] E) | inner A (p.1 x) y = inner A x (p.2 y)} := by
  ext p
  simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
  exact ⟨by rintro ⟨T, rfl⟩ x y; exact (T.adjoint_inner_right x y).symm,
    fun hp ↦ ⟨⟨p.1, p.2, hp⟩, rfl⟩⟩

private theorem isClosed_range_toProd :
    IsClosed (Set.range (toProd (A := A) (E := E) (F := F))) := by
  rw [range_toProd_eq]
  refine isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_eq ?_ ?_
  · exact CStarModule.continuous_inner.comp
      (((ContinuousLinearMap.apply ℂ F x).continuous.comp continuous_fst).prodMk continuous_const)
  · exact CStarModule.continuous_inner.comp
      (continuous_const.prodMk ((ContinuousLinearMap.apply ℂ E y).continuous.comp continuous_snd))

private theorem isometry_toProd : Isometry (toProd (A := A) (E := E) (F := F)) :=
  Isometry.of_dist_eq fun T S ↦ by
    have h₁ : dist T.toContinuousLinearMap S.toContinuousLinearMap = dist T S := by
      rw [dist_eq_norm, dist_eq_norm, ← toContinuousLinearMap_sub, norm_toContinuousLinearMap]
    have h₂ : dist T.adjoint.toContinuousLinearMap S.adjoint.toContinuousLinearMap = dist T S := by
      rw [dist_eq_norm, dist_eq_norm, ← toContinuousLinearMap_sub, ← adjoint_sub,
        norm_toContinuousLinearMap, norm_adjoint]
    simp only [Prod.dist_eq, toProd, h₁, h₂, max_self]

instance instCompleteSpace [CompleteSpace E] [CompleteSpace F] :
    CompleteSpace (AdjointableMap A E F) :=
  isometry_toProd.isUniformInducing.completeSpace isClosed_range_toProd.isComplete

/-- Between complete Hilbert C⋆-modules, the adjointable operators form a norm-closed subset of
`E →L[ℂ] F`. -/
theorem isClosed_range_toContinuousLinearMap [CompleteSpace E] [CompleteSpace F] :
    IsClosed (Set.range (toContinuousLinearMap : AdjointableMap A E F → E →L[ℂ] F)) :=
  isometry_toContinuousLinearMap.isClosedEmbedding.isClosed_range

section Complete

variable [CompleteSpace E] [CompleteSpace F]

/-- Construct an `AdjointableMap A E F` between complete Hilbert C⋆-modules from plain functions
`T : E → F` and `S : F → E` satisfying `⟪T x, y⟫_A = ⟪x, S y⟫_A`, with no linearity or continuity
hypotheses on `T` or `S`. -/
noncomputable def ofAdjointPair (T : E → F) (S : F → E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) : AdjointableMap A E F where
  toContinuousLinearMap :=
    (CStarModule.isAdjointPair_inner_iff.mpr h).toContinuousLinearMapCStarModule
  adjoint' :=
    (CStarModule.isAdjointPair_inner_iff.mpr h).symm_cstarModule.toContinuousLinearMapCStarModule
  inner_map_eq' x y := by simpa using h x y

@[simp]
theorem ofAdjointPair_apply (T : E → F) (S : F → E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) (x : E) :
    ofAdjointPair T S h x = T x :=
  (CStarModule.isAdjointPair_inner_iff.mpr h).toContinuousLinearMapCStarModule_apply x

@[simp]
theorem coe_ofAdjointPair (T : E → F) (S : F → E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) :
    ⇑(ofAdjointPair T S h) = T :=
  funext (ofAdjointPair_apply T S h)

@[simp]
theorem adjoint_ofAdjointPair_apply (T : E → F) (S : F → E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) (y : F) :
    (ofAdjointPair T S h).adjoint y = S y :=
  (CStarModule.isAdjointPair_inner_iff.mpr h).symm_cstarModule
    |>.toContinuousLinearMapCStarModule_apply y

@[simp]
theorem coe_adjoint_ofAdjointPair (T : E → F) (S : F → E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) :
    ⇑(ofAdjointPair T S h).adjoint = S :=
  funext (adjoint_ofAdjointPair_apply T S h)

theorem adjoint_ofAdjointPair (T : E → F) (S : F → E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) :
    (ofAdjointPair T S h).adjoint = ofAdjointPair S T
      ((CStarModule.isAdjointPair_inner_iff.mpr h).symm_cstarModule.inner_eq_cstarModule) :=
  ext fun y ↦ by simp

/-- Between complete Hilbert C⋆-modules, a bounded complex-linear map `T : E →L[ℂ] F` is
adjointable if and only if it admits a plain function `S : F → E` satisfying
`⟪T x, y⟫_A = ⟪x, S y⟫_A`. -/
theorem mem_range_toContinuousLinearMap_iff {T : E →L[ℂ] F} :
    T ∈ Set.range (toContinuousLinearMap : AdjointableMap A E F → E →L[ℂ] F) ↔
      ∃ S : F → E, ∀ x y, inner A (T x) y = inner A x (S y) :=
  ⟨by rintro ⟨T', rfl⟩; exact ⟨T'.adjoint, fun x y ↦ (T'.adjoint_inner_right x y).symm⟩,
    by rintro ⟨S, hS⟩; exact ⟨ofAdjointPair T S hS, by ext x; simp⟩⟩

end Complete

/-- The unital C⋆-algebra structure on bounded adjointable endomorphisms `AdjointableMap A E E` of
a complete Hilbert C⋆-module `E` (including the zero module). -/
noncomputable instance instCStarAlgebra [CompleteSpace E] :
    CStarAlgebra (AdjointableMap A E E) where

/-- The spectral partial order on `AdjointableMap A E E` for a complete Hilbert C⋆-module `E`. -/
noncomputable instance instPartialOrder [CompleteSpace E] :
    PartialOrder (AdjointableMap A E E) :=
  CStarAlgebra.spectralOrder _

/-- `AdjointableMap A E E` is a `StarOrderedRing` for its spectral order. -/
instance instStarOrderedRing [CompleteSpace E] :
    StarOrderedRing (AdjointableMap A E E) :=
  CStarAlgebra.spectralOrderedRing _

end StarOrdered

end Norm

/-! ### Self-adjointness, positivity, square roots, and Paschke's inequality -/

section Order

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- An endomorphism `T : AdjointableMap A E E` is self-adjoint if and only if
`⟪T x, y⟫_A = ⟪x, T y⟫_A` for all `x, y : E`. -/
theorem isSelfAdjoint_iff_forall_inner_eq (T : AdjointableMap A E E) :
    IsSelfAdjoint T ↔ ∀ x y : E, inner A (T x) y = inner A x (T y) := by
  rw [IsSelfAdjoint, star_eq_adjoint, eq_comm, eq_adjoint_iff]

/-- An endomorphism `T : AdjointableMap A E E` is self-adjoint if and only if every diagonal inner
product `⟪x, T x⟫_A` is self-adjoint in `A`. -/
theorem isSelfAdjoint_iff_forall_isSelfAdjoint_inner (T : AdjointableMap A E E) :
    IsSelfAdjoint T ↔ ∀ x : E, IsSelfAdjoint (inner A x (T x)) := by
  refine ⟨fun hT x ↦ ?_, fun h ↦ ?_⟩
  · rw [IsSelfAdjoint, star_inner, ← T.adjoint_inner_right, ← star_eq_adjoint, hT.star_eq]
  · rw [IsSelfAdjoint, star_eq_adjoint]
    refine CStarModule.eq_of_forall_inner_map_self (A := A) fun x ↦ ?_
    rw [T.adjoint_inner_right, ← star_inner, (h x).star_eq]

section SpectralOrder

variable [StarOrderedRing A] [CompleteSpace E]

/-- An operator `T : AdjointableMap A E E` on a complete Hilbert C⋆-module is positive in the
C⋆-algebra `AdjointableMap A E E` if and only if `0 ≤ ⟪x, T x⟫_A` in `A` for every `x : E`, with no
prior self-adjointness hypothesis on `T` (Lance, Lemma 4.1; Raeburn–Williams,
Proposition 2.28). -/
theorem nonneg_iff_forall_inner_nonneg {T : AdjointableMap A E E} :
    0 ≤ T ↔ ∀ x : E, 0 ≤ inner A x (T x) := by
  refine ⟨fun hT x ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
    rw [mul_apply_eq_comp, star_eq_adjoint, R.adjoint_inner_right]
    exact inner_self_nonneg
  · -- Positivity of all `⟪x, T x⟫_A` first forces `T` to be self-adjoint by polarization.
    have hsa : IsSelfAdjoint T :=
      (isSelfAdjoint_iff_forall_isSelfAdjoint_inner T).mpr fun x ↦ .of_nonneg (h x)
    refine TauCeti.nonneg_of_isSelfAdjoint_of_star_mul_mul_eq_neg hsa fun R N hRN ↦ ?_
    refine ext fun x ↦ (inner_self (A := A)).mp (le_antisymm ?_ inner_self_nonneg)
    have hpair : inner A (N x) (T (N x)) = -inner A (R x) (R x) := by
      calc inner A (N x) (T (N x))
          = inner A x ((star N * T * N) x) := by
            simp [mul_apply_eq_comp, star_eq_adjoint, N.adjoint_inner_right]
        _ = -inner A (R x) (R x) := by
            rw [hRN]
            simp [mul_apply_eq_comp, star_eq_adjoint, R.adjoint_inner_right]
    exact Left.nonneg_neg_iff.mp (hpair ▸ h (N x))

/-- Spectral order characterization on `AdjointableMap A E E`: `S ≤ T` if and only if
`⟪x, S x⟫_A ≤ ⟪x, T x⟫_A` for every `x : E`. -/
theorem le_iff_forall_inner_le {S T : AdjointableMap A E E} :
    S ≤ T ↔ ∀ x : E, inner A x (S x) ≤ inner A x (T x) := by
  rw [← sub_nonneg, nonneg_iff_forall_inner_nonneg]
  simp_rw [sub_apply, inner_sub_right, sub_nonneg]

/-- The positive square root `CFC.sqrt T` of a positive operator `T : AdjointableMap A E E`
satisfies `⟪CFC.sqrt T x, CFC.sqrt T y⟫_A = ⟪x, T y⟫_A`. -/
theorem inner_sqrt_apply_sqrt_apply {T : AdjointableMap A E E} (hT : 0 ≤ T) (x y : E) :
    inner A (CFC.sqrt T x) (CFC.sqrt T y) = inner A x (T y) := by
  rw [← (CFC.sqrt T).adjoint_inner_right, ← star_eq_adjoint,
    (CFC.sqrt_nonneg T).isSelfAdjoint.star_eq, ← mul_apply_eq_comp, CFC.sqrt_mul_sqrt_self T hT]

/-- For any rectangular adjointable map `S : AdjointableMap A E F`, `S* ∘ S` is positive in
`AdjointableMap A E E` (completeness of `F` is not needed). -/
theorem adjoint_comp_self_nonneg (S : AdjointableMap A E F) :
    0 ≤ S.adjoint.comp S :=
  nonneg_iff_forall_inner_nonneg.mpr fun x ↦ by
    rw [comp_apply, S.adjoint_inner_right]
    exact inner_self_nonneg

/-- Congruence of positivity along a rectangular adjointable map `S : AdjointableMap A E F`: if
`0 ≤ T` on `F`, then `0 ≤ S* ∘ T ∘ S` on `E`. -/
theorem adjoint_conj_nonneg [CompleteSpace F] (S : AdjointableMap A E F)
    {T : AdjointableMap A F F} (hT : 0 ≤ T) :
    0 ≤ S.adjoint.comp (T.comp S) :=
  nonneg_iff_forall_inner_nonneg.mpr fun x ↦ by
    rw [comp_apply, comp_apply, S.adjoint_inner_right]
    exact nonneg_iff_forall_inner_nonneg.mp hT (S x)

/-- Paschke's inequality for adjointable operators: `⟪T x, T x⟫_A ≤ ‖T‖ ^ 2 • ⟪x, x⟫_A` in `A`
for every `T : AdjointableMap A E F` when `E` is complete (completeness of `F` is not needed). -/
theorem inner_map_map_le_norm_sq_smul (T : AdjointableMap A E F) (x : E) :
    inner A (T x) (T x) ≤ ‖T‖ ^ 2 • inner A x x := by
  have hle : T.adjoint.comp T ≤
      algebraMap ℝ (AdjointableMap A E E) ‖T.adjoint.comp T‖ :=
    (adjoint_comp_self_nonneg T).isSelfAdjoint.le_algebraMap_norm_self
  have hx := le_iff_forall_inner_le.mp hle x
  rwa [comp_apply, T.adjoint_inner_right, algebraMap_apply, inner_smul_right_real,
    norm_adjoint_comp_self] at hx

end SpectralOrder

section RightOrder

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {E₁ F₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [SMul Bᵐᵒᵖ E₁]
  [CStarModule Bᵐᵒᵖ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [SMul Bᵐᵒᵖ F₁] [CStarModule Bᵐᵒᵖ F₁]

/-- Right-module form of `nonneg_iff_forall_inner_nonneg`: `0 ≤ T` in `AdjointableMap Bᵐᵒᵖ E₁ E₁`
if and only if `0 ≤ ⟨x, T x⟩_B` in `B` for every `x : E₁`. -/
theorem nonneg_iff_forall_unop_inner_nonneg {T : AdjointableMap Bᵐᵒᵖ E₁ E₁} :
    0 ≤ T ↔ ∀ x : E₁, 0 ≤ unop (inner Bᵐᵒᵖ x (T x)) := by
  simp_rw [nonneg_iff_forall_inner_nonneg, ← unop_nonneg]

/-- Right-module form of `le_iff_forall_inner_le`: `S ≤ T` in `AdjointableMap Bᵐᵒᵖ E₁ E₁`
if and only if `⟨x, S x⟩_B ≤ ⟨x, T x⟩_B` in `B` for every `x : E₁`. -/
theorem le_iff_forall_unop_inner_le {S T : AdjointableMap Bᵐᵒᵖ E₁ E₁} :
    S ≤ T ↔ ∀ x : E₁, unop (inner Bᵐᵒᵖ x (S x)) ≤ unop (inner Bᵐᵒᵖ x (T x)) := by
  simp_rw [le_iff_forall_inner_le, ← unop_le_unop]

/-- Right-module form of Paschke's inequality: `⟨T x, T x⟩_B ≤ ‖T‖ ^ 2 • ⟨x, x⟩_B`. -/
theorem unop_inner_map_map_le_norm_sq_smul (T : AdjointableMap Bᵐᵒᵖ E₁ F₁) (x : E₁) :
    unop (inner Bᵐᵒᵖ (T x) (T x)) ≤ ‖T‖ ^ 2 • unop (inner Bᵐᵒᵖ x x) := by
  simpa only [unop_smul] using unop_le_unop.mpr (inner_map_map_le_norm_sq_smul T x)

end RightOrder

end Order

/-! ### Idempotents and orthogonal projections -/

section Projections

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

/-- For an adjointable star projection `P`, `⟪P x, P y⟫_A = ⟪x, P y⟫_A`. -/
theorem inner_map_map_of_isStarProjection {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x y : E) :
    inner A (P x) (P y) = inner A x (P y) := by
  rw [← P.adjoint_inner_right, ← star_eq_adjoint, hP.isSelfAdjoint.star_eq, ← mul_apply_eq_comp,
    hP.isIdempotentElem.eq]

/-- Orthogonal inner-product decomposition along an adjointable star projection `P`:
`⟪x, y⟫_A = ⟪P x, P y⟫_A + ⟪(1 - P) x, (1 - P) y⟫_A`. -/
theorem inner_eq_add_inner_one_sub_of_isStarProjection {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x y : E) :
    inner A x y = inner A (P x) (P y) + inner A ((1 - P) x) ((1 - P) y) := by
  rw [inner_map_map_of_isStarProjection hP, inner_map_map_of_isStarProjection hP.one_sub,
    ← inner_add_right, ← add_apply, add_sub_cancel, one_apply_eq_self]

/-- The range of an adjointable idempotent `P` is its fixed-point locus `{x | P x = x}`. -/
theorem range_eq_of_isIdempotentElem {P : AdjointableMap A E E} (hP : IsIdempotentElem P) :
    Set.range P = {x : E | P x = x} :=
  Set.ext fun _ ↦
    LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap (hP.map toContinuousLinearMapAlgHom))

/-- The range of an adjointable idempotent is norm-closed (without completeness of `E`). -/
theorem isClosed_range_of_isIdempotentElem {P : AdjointableMap A E E} (hP : IsIdempotentElem P) :
    IsClosed (Set.range P) := by
  rw [← coe_toContinuousLinearMap]
  exact ContinuousLinearMap.IsIdempotentElem.isClosed_range (hP.map toContinuousLinearMapAlgHom)

/-- Vectors in the range and kernel of an adjointable star projection are orthogonal for the
`A`-valued inner product. -/
theorem inner_eq_zero_of_isStarProjection {P : AdjointableMap A E E} (hP : IsStarProjection P)
    {x y : E} (hx : x ∈ Set.range P) (hy : P y = 0) :
    inner A x y = 0 := by
  rw [← (range_eq_of_isIdempotentElem hP.isIdempotentElem).subset hx, ← P.adjoint_inner_right,
    ← star_eq_adjoint, hP.isSelfAdjoint.star_eq, hy, inner_zero_right]

/-- An adjointable star projection decreases diagonal inner products: `⟪P x, P x⟫_A ≤ ⟪x, x⟫_A`. -/
theorem inner_map_map_le_of_isStarProjection [StarOrderedRing A] {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x : E) :
    inner A (P x) (P x) ≤ inner A x x := by
  rw [inner_eq_add_inner_one_sub_of_isStarProjection hP x x]
  exact le_add_of_nonneg_right inner_self_nonneg

/-- Every adjointable star projection is contractive on vectors: `‖P x‖ ≤ ‖x‖`. -/
theorem norm_apply_le_of_isStarProjection [StarOrderedRing A] {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x : E) :
    ‖P x‖ ≤ ‖x‖ :=
  CStarModule.norm_le_of_inner_self_le (inner_map_map_le_of_isStarProjection hP x)

end Projections

end AdjointableMap

end TauCeti
