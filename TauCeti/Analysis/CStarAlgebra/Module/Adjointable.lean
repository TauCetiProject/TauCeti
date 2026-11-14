/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

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
* `TauCeti.AdjointableMap.ofAdjointPair` and `LinearMap.IsAdjointPair.toAdjointableMap`: construct
  an `AdjointableMap A E F` between complete modules from plain functions `T : E → F` and
  `S : F → E` satisfying `⟪T x, y⟫_A = ⟪x, S y⟫_A`.
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
* `TauCeti.AdjointableMap.inner_map_self_le_norm_sq_smul`: Paschke's inequality
  `⟪T x, T x⟫_A ≤ ‖T‖ ^ 2 • ⟪x, x⟫_A` for any `T : AdjointableMap A E F` when `E` is complete.
* `TauCeti.AdjointableMap.isClosed_range_of_isStarProjection` and
  `TauCeti.AdjointableMap.inner_eq_add_inner_one_sub_of_isStarProjection`: closed range and
  orthogonal inner-product decomposition for adjointable star projections.

## References

* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2 (Definitions 2.17–2.18, Proposition 2.19, Corollary 2.22, Proposition 2.28).
* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1, 3,
  and 4 (Proposition 1.2, Theorem 4.1).
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
@[expose] def adjoint (T : AdjointableMap A E F) : AdjointableMap A F E where
  toContinuousLinearMap := T.adjoint'
  adjoint' := T.toContinuousLinearMap
  inner_map_eq' y x :=
    (CStarModule.isAdjointPair_inner_iff.mpr T.inner_map_eq').symm_cstarModule.inner_eq_cstarModule
      y x

@[simp]
theorem adjoint'_eq (T : AdjointableMap A E F) :
    T.adjoint' = T.adjoint.toContinuousLinearMap := (rfl)

/-- The adjoint operation is involutive. -/
@[simp]
theorem adjoint_adjoint (T : AdjointableMap A E F) : T.adjoint.adjoint = T := (rfl)

theorem adjoint_injective :
    Function.Injective (adjoint : AdjointableMap A E F → AdjointableMap A F E) :=
  Function.LeftInverse.injective adjoint_adjoint

@[simp]
theorem adjoint_inj {T S : AdjointableMap A E F} : T.adjoint = S.adjoint ↔ T = S :=
  adjoint_injective.eq_iff

/-- Defining identity `⟪T x, y⟫_A = ⟪x, T.adjoint y⟫_A` of the adjoint. -/
theorem inner_map_left (T : AdjointableMap A E F) (x : E) (y : F) :
    inner A (T x) y = inner A x (T.adjoint y) :=
  T.inner_map_eq' x y

/-- Symmetric form `⟪x, T y⟫_A = ⟪T.adjoint x, y⟫_A` of the adjoint identity. -/
theorem inner_map_right (T : AdjointableMap A E F) (x : F) (y : E) :
    inner A x (T y) = inner A (T.adjoint x) y :=
  (T.adjoint.inner_map_left x y).symm

/-- Every `AdjointableMap` forms a `LinearMap.IsAdjointPair` with its adjoint. -/
theorem isAdjointPair (T : AdjointableMap A E F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T T.adjoint :=
  CStarModule.isAdjointPair_inner_iff.mpr T.inner_map_left

/-- Uniqueness characterization of the adjoint: `S = T.adjoint` iff `⟪T x, y⟫_A = ⟪x, S y⟫_A`
for all `x` and `y`. -/
theorem eq_adjoint_iff {S : AdjointableMap A F E} {T : AdjointableMap A E F} :
    S = T.adjoint ↔ ∀ x y, inner A (T x) y = inner A x (S y) :=
  ⟨fun h x y ↦ h ▸ T.inner_map_left x y, fun h ↦
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
      inner_map_eq' := fun x y ↦ by simp [T.inner_map_left, S.inner_map_left] }

instance instNeg : Neg (AdjointableMap A E F) where
  neg T :=
    { toContinuousLinearMap := -T.toContinuousLinearMap
      adjoint' := -T.adjoint'
      inner_map_eq' := fun x y ↦ by simp [T.inner_map_left] }

instance instSub : Sub (AdjointableMap A E F) where
  sub T S :=
    { toContinuousLinearMap := T.toContinuousLinearMap - S.toContinuousLinearMap
      adjoint' := T.adjoint' - S.adjoint'
      inner_map_eq' := fun x y ↦ by simp [T.inner_map_left, S.inner_map_left] }

instance instSMulComplex : SMul ℂ (AdjointableMap A E F) where
  smul c T :=
    { toContinuousLinearMap := c • T.toContinuousLinearMap
      adjoint' := star c • T.adjoint'
      inner_map_eq' := fun x y ↦ by simp [T.inner_map_left] }

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

@[simp] theorem zero_apply (x : E) : (0 : AdjointableMap A E F) x = 0 := (rfl)
@[simp] theorem add_apply (T S : AdjointableMap A E F) (x : E) : (T + S) x = T x + S x := (rfl)
@[simp] theorem neg_apply (T : AdjointableMap A E F) (x : E) : (-T) x = -T x := (rfl)
@[simp] theorem sub_apply (T S : AdjointableMap A E F) (x : E) : (T - S) x = T x - S x := (rfl)
@[simp] theorem smul_apply (c : ℂ) (T : AdjointableMap A E F) (x : E) : (c • T) x = c • T x := (rfl)

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
        simpa [Nat.cast_smul_eq_nsmul ℂ] using ((n : ℂ) • T).inner_map_left x y }

instance instSMulInt : SMul ℤ (AdjointableMap A E F) where
  smul n T :=
    { toContinuousLinearMap := n • T.toContinuousLinearMap
      adjoint' := n • T.adjoint'
      inner_map_eq' := fun x y ↦ by
        simpa [Int.cast_smul_eq_zsmul ℂ] using ((n : ℂ) • T).inner_map_left x y }

instance instAddCommGroup : AddCommGroup (AdjointableMap A E F) :=
  toContinuousLinearMap_injective.addCommGroup _
    toContinuousLinearMap_zero toContinuousLinearMap_add toContinuousLinearMap_neg
    toContinuousLinearMap_sub (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance instModuleComplex : Module ℂ (AdjointableMap A E F) :=
  Function.Injective.module ℂ
    { toFun := toContinuousLinearMap, map_zero' := rfl, map_add' := toContinuousLinearMap_add }
    toContinuousLinearMap_injective toContinuousLinearMap_smul

/-- The forgetful `ℂ`-linear map from `AdjointableMap A E F` to `E →L[ℂ] F`. -/
def toContinuousLinearMapLinear : AdjointableMap A E F →ₗ[ℂ] E →L[ℂ] F where
  toFun := toContinuousLinearMap
  map_add' := toContinuousLinearMap_add
  map_smul' := toContinuousLinearMap_smul

@[simp] theorem toContinuousLinearMapLinear_apply (T : AdjointableMap A E F) :
    toContinuousLinearMapLinear T = T.toContinuousLinearMap := (rfl)

@[simp]
theorem sum_apply {ι : Type*} (s : Finset ι) (T : ι → AdjointableMap A E F) (x : E) :
    (∑ i ∈ s, T i) x = ∑ i ∈ s, T i x := by
  induction s using Finset.cons_induction <;> simp [*]

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
@[expose] protected def id (A E : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] :
    AdjointableMap A E E where
  toContinuousLinearMap := ContinuousLinearMap.id ℂ E
  adjoint' := ContinuousLinearMap.id ℂ E
  inner_map_eq' _ _ := rfl

@[simp] theorem toContinuousLinearMap_id :
    (AdjointableMap.id A E).toContinuousLinearMap = ContinuousLinearMap.id ℂ E := (rfl)
@[simp] theorem id_apply (x : E) : AdjointableMap.id A E x = x := (rfl)
@[simp] theorem adjoint_id : (AdjointableMap.id A E).adjoint = AdjointableMap.id A E := (rfl)

/-- Composition of adjointable operators, with `(S.comp T).adjoint = T.adjoint.comp S.adjoint`. -/
@[expose] def comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    AdjointableMap A E G where
  toContinuousLinearMap := S.toContinuousLinearMap.comp T.toContinuousLinearMap
  adjoint' := T.adjoint'.comp S.adjoint'
  inner_map_eq' x z := (S.inner_map_left (T x) z).trans (T.inner_map_left x (S.adjoint z))

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

@[simp] theorem toContinuousLinearMap_one :
    (1 : AdjointableMap A E E).toContinuousLinearMap = 1 := (rfl)
@[simp] theorem toContinuousLinearMap_mul (S T : AdjointableMap A E E) :
    (S * T).toContinuousLinearMap = S.toContinuousLinearMap * T.toContinuousLinearMap := (rfl)
@[simp] theorem one_apply (x : E) : (1 : AdjointableMap A E E) x = x := (rfl)
@[simp] theorem mul_apply (S T : AdjointableMap A E E) (x : E) : (S * T) x = S (T x) := (rfl)

instance instPowNat : Pow (AdjointableMap A E E) ℕ where
  pow T n :=
    { toContinuousLinearMap := T.toContinuousLinearMap ^ n
      adjoint' := T.adjoint' ^ n
      inner_map_eq' := fun x y ↦ by
        induction n generalizing x y with
        | zero => rfl
        | succ k hk =>
          rw [pow_succ', pow_succ]
          exact (T.inner_map_eq' _ y).trans (hk x (T.adjoint' y)) }

@[simp] theorem toContinuousLinearMap_pow (T : AdjointableMap A E E) (n : ℕ) :
    (T ^ n).toContinuousLinearMap = T.toContinuousLinearMap ^ n := (rfl)

instance instNatCast : NatCast (AdjointableMap A E E) := ⟨fun n ↦ n • 1⟩
instance instIntCast : IntCast (AdjointableMap A E E) := ⟨fun n ↦ n • 1⟩

instance instRing : Ring (AdjointableMap A E E) :=
  toContinuousLinearMap_injective.ring _
    toContinuousLinearMap_zero toContinuousLinearMap_one toContinuousLinearMap_add
    toContinuousLinearMap_mul toContinuousLinearMap_neg toContinuousLinearMap_sub
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun n ↦ nsmul_one n) (fun n ↦ zsmul_one n)

instance instAlgebraComplex : Algebra ℂ (AdjointableMap A E E) :=
  Algebra.ofModule smul_comp comp_smul

/-- The forgetful `ℂ`-algebra homomorphism from `AdjointableMap A E E` to `E →L[ℂ] E`. -/
def toContinuousLinearMapAlgHom : AdjointableMap A E E →ₐ[ℂ] E →L[ℂ] E where
  toFun := toContinuousLinearMap
  map_one' := rfl
  map_mul' := toContinuousLinearMap_mul
  map_zero' := rfl
  map_add' := toContinuousLinearMap_add
  commutes' _ := by ext; rfl

@[simp] theorem toContinuousLinearMapAlgHom_apply (T : AdjointableMap A E E) :
    toContinuousLinearMapAlgHom T = T.toContinuousLinearMap := (rfl)
@[simp] theorem algebraMap_apply (r : ℝ) (x : E) :
    algebraMap ℝ (AdjointableMap A E E) r x = r • x := (rfl)
@[simp] theorem algebraMap_complex_apply (c : ℂ) (x : E) :
    algebraMap ℂ (AdjointableMap A E E) c x = c • x := (rfl)

instance instStar : Star (AdjointableMap A E E) := ⟨adjoint⟩

@[simp] theorem star_eq_adjoint (T : AdjointableMap A E E) : star T = T.adjoint := (rfl)

instance instStarRing : StarRing (AdjointableMap A E E) where
  star_involutive := adjoint_adjoint
  star_mul := adjoint_comp
  star_add := adjoint_add

instance instStarModuleComplex : StarModule ℂ (AdjointableMap A E E) where
  star_smul := adjoint_smul

/-- The natural left action of `AdjointableMap A E E` on the module `E` by evaluation. -/
instance instSMulApply : SMul (AdjointableMap A E E) E := ⟨fun T x ↦ T x⟩

@[simp] protected theorem smul_def (T : AdjointableMap A E E) (x : E) : T • x = T x := (rfl)

instance applyModule : Module (AdjointableMap A E E) E where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero T := map_zero T
  smul_add T := map_add T
  add_smul _ _ _ := rfl
  zero_smul _ := rfl

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

end Basic

/-! ### Right-module inner-product convenience lemmas -/

section Right

variable {B E F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- Right-module form `⟨T x, y⟩_B = ⟨x, T.adjoint y⟩_B` of the adjoint identity. -/
theorem unop_inner_map_left (T : AdjointableMap Bᵐᵒᵖ E F) (x : E) (y : F) :
    unop (inner Bᵐᵒᵖ (T x) y) = unop (inner Bᵐᵒᵖ x (T.adjoint y)) :=
  congrArg unop (T.inner_map_left x y)

/-- Symmetric right-module form `⟨x, T y⟩_B = ⟨T.adjoint x, y⟩_B` of the adjoint identity. -/
theorem unop_inner_map_right (T : AdjointableMap Bᵐᵒᵖ E F) (x : F) (y : E) :
    unop (inner Bᵐᵒᵖ x (T y)) = unop (inner Bᵐᵒᵖ (T.adjoint x) y) :=
  congrArg unop (T.inner_map_right x y)

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
  norm_mul_le := opNorm_comp_le

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
theorem norm_comp_adjoint_self (T : AdjointableMap A E F) :
    ‖T.comp T.adjoint‖ = ‖T‖ ^ 2 := by
  simpa only [adjoint_adjoint, norm_adjoint] using norm_adjoint_comp_self T.adjoint

instance instNormedStarGroup : NormedStarGroup (AdjointableMap A E E) where
  norm_star_le T := (norm_adjoint T).le

instance instCStarRing : CStarRing (AdjointableMap A E E) where
  norm_mul_self_le T := by
    rw [← sq, ← norm_adjoint_comp_self T]
    exact le_rfl

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
  exact ⟨by rintro ⟨T, rfl⟩ x y; exact T.inner_map_left x y,
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
  ⟨by rintro ⟨T', rfl⟩; exact ⟨T'.adjoint, T'.inner_map_left⟩,
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
  · rw [IsSelfAdjoint, star_inner, T.inner_map_left, ← star_eq_adjoint, hT.star_eq]
  · rw [IsSelfAdjoint, star_eq_adjoint]
    refine CStarModule.eq_of_forall_inner_map_self (A := A) fun x ↦ ?_
    rw [← T.inner_map_left, ← star_inner, (h x).star_eq]

section SpectralOrder

variable [StarOrderedRing A] [CompleteSpace E]

/-- An operator `T : AdjointableMap A E E` on a complete Hilbert C⋆-module is positive in the
C⋆-algebra `AdjointableMap A E E` if and only if `0 ≤ ⟪x, T x⟫_A` in `A` for every `x : E`, with no
prior self-adjointness hypothesis on `T` (Lance, Theorem 4.1; Raeburn–Williams,
Proposition 2.28). -/
theorem nonneg_iff_forall_inner_nonneg {T : AdjointableMap A E E} :
    0 ≤ T ↔ ∀ x : E, 0 ≤ inner A x (T x) := by
  refine ⟨fun hT x ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
    rw [mul_apply, star_eq_adjoint, ← R.inner_map_left]
    exact inner_self_nonneg
  · -- Positivity of all `⟪x, T x⟫_A` first forces `T` to be self-adjoint by polarization.
    have hsa : IsSelfAdjoint T :=
      (isSelfAdjoint_iff_forall_isSelfAdjoint_inner T).mpr fun x ↦ .of_nonneg (h x)
    refine CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero.mpr ⟨hsa, ?_⟩
    set N := T⁻
    have hN : 0 ≤ N := CFC.negPart_nonneg T
    obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hN
    have hTN : T * N = -(star R * R * N) := by
      conv_lhs => rw [← CFC.posPart_sub_negPart T hsa]
      rw [sub_mul, CFC.posPart_mul_negPart, zero_sub, ← hR]
    -- Pairing at `N x` forces `R (N x) = 0` for all `x`, hence `R * N = 0` and `N = 0`.
    have hRN : R * N = 0 := by
      refine ext fun x ↦ (inner_self (A := A)).mp (le_antisymm ?_ inner_self_nonneg)
      have hx := h (N x)
      rw [← mul_apply, hTN, neg_apply, inner_neg_right, mul_apply, mul_apply, star_eq_adjoint,
        ← R.inner_map_left, Left.nonneg_neg_iff] at hx
      exact hx
    rw [← star_mul_self_eq_zero, hN.isSelfAdjoint.star_eq]
    calc N * N = star R * (R * N) := by rw [← mul_assoc, ← hR]
      _ = 0 := by rw [hRN, mul_zero]

/-- Spectral order characterization on `AdjointableMap A E E`: `S ≤ T` if and only if
`⟪x, S x⟫_A ≤ ⟪x, T x⟫_A` for every `x : E`. -/
theorem le_iff_forall_inner_le {S T : AdjointableMap A E E} :
    S ≤ T ↔ ∀ x : E, inner A x (S x) ≤ inner A x (T x) := by
  rw [← sub_nonneg, nonneg_iff_forall_inner_nonneg]
  simp_rw [sub_apply, inner_sub_right, sub_nonneg]

/-- The positive square root `CFC.sqrt T` of a positive operator `T : AdjointableMap A E E`
satisfies `⟪CFC.sqrt T x, CFC.sqrt T y⟫_A = ⟪x, T y⟫_A`. -/
theorem inner_sqrt_self {T : AdjointableMap A E E} (hT : 0 ≤ T) (x y : E) :
    inner A (CFC.sqrt T x) (CFC.sqrt T y) = inner A x (T y) := by
  rw [(CFC.sqrt T).inner_map_left, ← star_eq_adjoint, (CFC.sqrt_nonneg T).isSelfAdjoint.star_eq,
    ← mul_apply, CFC.sqrt_mul_sqrt_self T hT]

/-- For any rectangular adjointable map `S : AdjointableMap A E F`, `S* ∘ S` is positive in
`AdjointableMap A E E` (completeness of `F` is not needed). -/
theorem adjoint_comp_self_nonneg (S : AdjointableMap A E F) :
    0 ≤ S.adjoint.comp S :=
  nonneg_iff_forall_inner_nonneg.mpr fun x ↦ by
    rw [comp_apply, ← S.inner_map_left]
    exact inner_self_nonneg

/-- Congruence of positivity along a rectangular adjointable map `S : AdjointableMap A E F`: if
`0 ≤ T` on `F`, then `0 ≤ S* ∘ T ∘ S` on `E`. -/
theorem adjoint_comp_nonneg [CompleteSpace F] (S : AdjointableMap A E F)
    {T : AdjointableMap A F F} (hT : 0 ≤ T) :
    0 ≤ S.adjoint.comp (T.comp S) :=
  nonneg_iff_forall_inner_nonneg.mpr fun x ↦ by
    rw [comp_apply, comp_apply, ← S.inner_map_left]
    exact nonneg_iff_forall_inner_nonneg.mp hT (S x)

/-- Paschke's inequality for adjointable operators: `⟪T x, T x⟫_A ≤ ‖T‖ ^ 2 • ⟪x, x⟫_A` in `A`
for every `T : AdjointableMap A E F` when `E` is complete (completeness of `F` is not needed). -/
theorem inner_map_self_le_norm_sq_smul (T : AdjointableMap A E F) (x : E) :
    inner A (T x) (T x) ≤ ‖T‖ ^ 2 • inner A x x := by
  have hle : T.adjoint.comp T ≤
      algebraMap ℝ (AdjointableMap A E E) ‖T.adjoint.comp T‖ :=
    (adjoint_comp_self_nonneg T).isSelfAdjoint.le_algebraMap_norm_self
  have hx := le_iff_forall_inner_le.mp hle x
  rw [comp_apply, ← T.inner_map_left, norm_adjoint_comp_self, algebraMap_apply,
    ← smul_one_smul ℂ (‖T‖ ^ 2) x, inner_smul_right_complex, smul_one_smul] at hx
  exact hx

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

/-- Right-module form of Paschke's inequality: `⟨T x, T x⟩_B ≤ ‖T‖ ^ 2 • ⟨x, x⟩_B`. -/
theorem unop_inner_map_self_le_norm_sq_smul (T : AdjointableMap Bᵐᵒᵖ E₁ F₁) (x : E₁) :
    unop (inner Bᵐᵒᵖ (T x) (T x)) ≤ ‖T‖ ^ 2 • unop (inner Bᵐᵒᵖ x x) := by
  simpa only [unop_smul] using unop_le_unop.mpr (inner_map_self_le_norm_sq_smul T x)

end RightOrder

end Order

/-! ### Orthogonal projections -/

section Projections

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

/-- For an adjointable star projection `P`, `⟪P x, P y⟫_A = ⟪x, P y⟫_A`. -/
theorem inner_map_self_of_isStarProjection {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x y : E) :
    inner A (P x) (P y) = inner A x (P y) := by
  rw [P.inner_map_left, ← star_eq_adjoint, hP.isSelfAdjoint.star_eq, ← mul_apply,
    hP.isIdempotentElem.eq]

/-- Orthogonal inner-product decomposition along an adjointable star projection `P`:
`⟪x, y⟫_A = ⟪P x, P y⟫_A + ⟪(1 - P) x, (1 - P) y⟫_A`. -/
theorem inner_eq_add_inner_one_sub_of_isStarProjection {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x y : E) :
    inner A x y = inner A (P x) (P y) + inner A ((1 - P) x) ((1 - P) y) := by
  rw [inner_map_self_of_isStarProjection hP, inner_map_self_of_isStarProjection hP.one_sub,
    ← inner_add_right, ← add_apply, add_sub_cancel, one_apply]

/-- The range of an adjointable star projection `P` is its fixed-point locus `{x | P x = x}`. -/
theorem range_eq_of_isStarProjection {P : AdjointableMap A E E} (hP : IsStarProjection P) :
    Set.range P = {x : E | P x = x} :=
  Set.ext fun x ↦
    ⟨by rintro ⟨y, rfl⟩; exact DFunLike.congr_fun hP.isIdempotentElem.eq y, fun hx ↦ ⟨x, hx⟩⟩

/-- The range of an adjointable star projection is norm-closed (without completeness of `E`). -/
theorem isClosed_range_of_isStarProjection {P : AdjointableMap A E E} (hP : IsStarProjection P) :
    IsClosed (Set.range P) := by
  rw [range_eq_of_isStarProjection hP]
  exact isClosed_eq P.toContinuousLinearMap.continuous continuous_id

/-- Vectors in the range and kernel of an adjointable star projection are orthogonal for the
`A`-valued inner product. -/
theorem inner_eq_zero_of_isStarProjection {P : AdjointableMap A E E} (hP : IsStarProjection P)
    {x y : E} (hx : x ∈ Set.range P) (hy : P y = 0) :
    inner A x y = 0 := by
  rw [← (range_eq_of_isStarProjection hP).subset hx, P.inner_map_left, ← star_eq_adjoint,
    hP.isSelfAdjoint.star_eq, hy, inner_zero_right]

/-- An adjointable star projection decreases diagonal inner products: `⟪P x, P x⟫_A ≤ ⟪x, x⟫_A`. -/
theorem inner_self_le_of_isStarProjection [StarOrderedRing A] {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x : E) :
    inner A (P x) (P x) ≤ inner A x x := by
  rw [inner_eq_add_inner_one_sub_of_isStarProjection hP x x]
  exact le_add_of_nonneg_right inner_self_nonneg

/-- Every adjointable star projection is contractive on vectors: `‖P x‖ ≤ ‖x‖`. -/
theorem norm_apply_le_of_isStarProjection [StarOrderedRing A] {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x : E) :
    ‖P x‖ ≤ ‖x‖ := by
  rw [norm_eq_sqrt_norm_inner_self (A := A), norm_eq_sqrt_norm_inner_self (A := A) (x := x)]
  exact Real.sqrt_le_sqrt
    (CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (inner_self_le_of_isStarProjection hP x) inner_self_nonneg)

end Projections

end AdjointableMap

end TauCeti

namespace LinearMap.IsAdjointPair

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F] [CompleteSpace F]
  {T : E → F} {S : F → E}

/-- Bundle a `LinearMap.IsAdjointPair` of plain functions between complete Hilbert C⋆-modules as a
`TauCeti.AdjointableMap A E F`. -/
noncomputable def toAdjointableMap
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) : TauCeti.AdjointableMap A E F :=
  TauCeti.AdjointableMap.ofAdjointPair T S h.inner_eq_cstarModule

@[simp]
theorem toAdjointableMap_apply
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (x : E) :
    h.toAdjointableMap x = T x :=
  TauCeti.AdjointableMap.ofAdjointPair_apply T S h.inner_eq_cstarModule x

@[simp]
theorem adjoint_toAdjointableMap_apply
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) (y : F) :
    h.toAdjointableMap.adjoint y = S y :=
  TauCeti.AdjointableMap.adjoint_ofAdjointPair_apply T S h.inner_eq_cstarModule y

theorem adjoint_toAdjointableMap
    (h : IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) :
    h.toAdjointableMap.adjoint = h.symm_cstarModule.toAdjointableMap :=
  TauCeti.AdjointableMap.adjoint_ofAdjointPair T S h.inner_eq_cstarModule

end LinearMap.IsAdjointPair
