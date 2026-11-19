/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair

/-!
# Adjointable maps between C⋆-modules

For C⋆-modules `E` and `F` over `A`, an adjointable map `T : E → F` is a bounded complex-linear
map admitting an adjoint `T† : F → E` with `⟪T x, y⟫_A = ⟪x, T† y⟫_A`. Unlike for Hilbert spaces,
not every bounded module map is adjointable, so the adjoint is part of the data; it is uniquely
determined by `T`, so two adjointable maps with the same underlying map are equal. This file
builds the space `AdjointableMap A E F` of such maps (usually written `L_A(E, F)`) with its
addition, complex scalar multiplication, composition, adjoint and operator norm, and proves that
`AdjointableMap A E E` is a unital C⋆-algebra when `E` is complete, with the adjoint as star.
The C⋆-identity comes from `LinearMap.IsAdjointPair.norm_adjoint_comp_self_cstarModule`.

The norm of `T` is the operator norm of the underlying map, and the adjoint is isometric. Since
`T ↦ (T, T†)` is then an isometry onto the closed set of pairs satisfying the adjoint identity,
`AdjointableMap A E F` is complete when `E` and `F` are. The ring structure on
`AdjointableMap A E E` is assembled with `FunLike.compRing`, as for `ContinuousLinearMap`.
Storing a map together with a partner map, and the completeness argument (the range of
`T ↦ (T, T†)` is an intersection of closed equations), follow Mathlib's `DoubleCentralizer`
(`Mathlib/Analysis/CStarAlgebra/Multiplier.lean`).

For right Hilbert `A`-modules, instantiate the coefficient type with `Aᵐᵒᵖ`. No unit,
fullness, countable generation or nonzero-module hypothesis is needed: for the zero module,
`AdjointableMap A E E` is the zero C⋆-algebra. Positivity on `L_A(E)` is the spectral order of
its C⋆-algebra structure (`CStarAlgebra.spectralOrder`), so square roots, the continuous
functional calculus, projections, isometries and unitaries of `L_A(E)` are those of Mathlib's
C⋆-algebra API.

## Main declarations

* `TauCeti.AdjointableMap A E F`: adjointable maps from `E` to `F`, with coercion to functions.
* `TauCeti.AdjointableMap.adjoint`: the adjoint `L_A(E, F) → L_A(F, E)`, characterised by
  `TauCeti.AdjointableMap.eq_adjoint_iff`; it is an involution reversing composition, and it is
  isometric (`TauCeti.AdjointableMap.norm_adjoint`).
* `TauCeti.AdjointableMap.ofIsAdjointPair`: two plain functions between complete modules
  satisfying the adjoint identity form an adjointable map.
* `TauCeti.AdjointableMap.comp`, `TauCeti.AdjointableMap.id`: composition and identity.
* `TauCeti.AdjointableMap.norm_adjoint_comp_self`: the C⋆-identity `‖T† ∘ T‖ = ‖T‖ ^ 2`.
* `TauCeti.AdjointableMap.instCompleteSpace`: `L_A(E, F)` is complete for complete `E` and `F`.
* `TauCeti.AdjointableMap.instCStarAlgebra`: `L_A(E)` is a unital C⋆-algebra.
* `TauCeti.AdjointableMap.toContinuousLinearMapAlgHom`: the forgetful map
  `L_A(E) → (E →L[ℂ] E)`, a unital algebra homomorphism which is isometric
  (`TauCeti.AdjointableMap.norm_toContinuousLinearMap`).

## Implementation notes

The adjoint is stored as the field `adjointMap`, but the normal form is
`TauCeti.AdjointableMap.adjoint` (`TauCeti.AdjointableMap.adjointMap_eq`). Definitions are
exposed so that the algebraic and normed instances built here agree definitionally downstream.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 2.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Section 2.2.
-/

@[expose] public section

open CStarModule

namespace TauCeti

section Defs

variable (A E F : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- An adjointable map between C⋆-modules over `A`: a bounded complex-linear map
`T : E →L[ℂ] F` together with a bounded complex-linear map `T† : F →L[ℂ] E` satisfying
`⟪T x, y⟫_A = ⟪x, T† y⟫_A`. The adjoint is uniquely determined by `T`
(`TauCeti.AdjointableMap.ext`). -/
structure AdjointableMap where
  /-- The underlying bounded complex-linear map. -/
  toContinuousLinearMap : E →L[ℂ] F
  /-- The adjoint of the map, as a bounded complex-linear map; use
  `TauCeti.AdjointableMap.adjoint` for the adjoint as an adjointable map. -/
  adjointMap : F →L[ℂ] E
  /-- The adjoint identity `⟪T x, y⟫_A = ⟪x, T† y⟫_A`. -/
  inner_map_left : ∀ x y, inner A (toContinuousLinearMap x) y = inner A x (adjointMap y)

end Defs

namespace AdjointableMap

variable {A E F G : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

/-! ### Coercions, extensionality and the adjoint -/

instance instFunLike : FunLike (AdjointableMap A E F) E F where
  coe T := T.toContinuousLinearMap
  coe_injective S T h := by
    obtain ⟨S, S', hS⟩ := S
    obtain ⟨T, T', hT⟩ := T
    obtain rfl : S = T := ContinuousLinearMap.coe_injective (DFunLike.coe_injective h)
    obtain rfl : S' = T' := DFunLike.coe_injective
      ((isAdjointPair_inner_iff.mpr hS).unique_right_cstarModule (isAdjointPair_inner_iff.mpr hT))
    rfl

instance instContinuousSemilinearMapClass :
    ContinuousSemilinearMapClass (AdjointableMap A E F) (RingHom.id ℂ) E F where
  map_add T := T.toContinuousLinearMap.map_add
  map_smulₛₗ T := T.toContinuousLinearMap.map_smul
  map_continuous T := T.toContinuousLinearMap.continuous

@[simp]
theorem coe_toContinuousLinearMap (T : AdjointableMap A E F) :
    ⇑T.toContinuousLinearMap = T := (rfl)

/-- Adjointable maps are determined by their values; the adjoint is then determined too. -/
@[ext]
theorem ext {S T : AdjointableMap A E F} (h : ∀ x, S x = T x) : S = T :=
  DFunLike.ext _ _ h

theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : AdjointableMap A E F → E →L[ℂ] F) :=
  fun _ _ h => ext fun x => DFunLike.congr_fun h x

/-- The adjoint of an adjointable map, as an adjointable map. -/
def adjoint (T : AdjointableMap A E F) : AdjointableMap A F E where
  toContinuousLinearMap := T.adjointMap
  adjointMap := T.toContinuousLinearMap
  inner_map_left y x := by
    rw [← star_inner x, ← T.inner_map_left, star_inner]

/-- The field `adjointMap` is the underlying map of the adjoint; the latter is the normal form. -/
@[simp]
theorem adjointMap_eq (T : AdjointableMap A E F) :
    T.adjointMap = T.adjoint.toContinuousLinearMap := (rfl)

/-- The fundamental property of the adjoint: `⟪x, T† y⟫_A = ⟪T x, y⟫_A`. -/
theorem adjoint_inner_right (T : AdjointableMap A E F) (x : E) (y : F) :
    inner A x (T.adjoint y) = inner A (T x) y :=
  (T.inner_map_left x y).symm

/-- The fundamental property of the adjoint: `⟪T† y, x⟫_A = ⟪y, T x⟫_A`. -/
theorem adjoint_inner_left (T : AdjointableMap A E F) (y : F) (x : E) :
    inner A (T.adjoint y) x = inner A y (T x) :=
  T.adjoint.inner_map_left y x

@[simp]
theorem adjoint_adjoint (T : AdjointableMap A E F) : T.adjoint.adjoint = T := (rfl)

/-- The adjoint is unique: `S` is the adjoint of `T` if and only if
`⟪S x, y⟫_A = ⟪x, T y⟫_A` for all `x` and `y`. -/
theorem eq_adjoint_iff (S : AdjointableMap A E F) (T : AdjointableMap A F E) :
    S = T.adjoint ↔ ∀ x y, inner A (S x) y = inner A x (T y) := by
  refine ⟨fun h x y => h ▸ T.adjoint_inner_left x y, fun h => ext fun x => ?_⟩
  exact congrFun ((isAdjointPair_inner_iff.mpr h).unique_left_cstarModule
    (isAdjointPair_inner_iff.mpr T.adjoint.inner_map_left)) x

/-- An adjointable map and its adjoint form an adjoint pair in the sense of
`LinearMap.IsAdjointPair` for the flipped module inner products. -/
theorem isAdjointPair (T : AdjointableMap A E F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T T.adjoint :=
  isAdjointPair_inner_iff.mpr T.inner_map_left

/-- An adjointable map commutes with the coefficient action. -/
theorem map_smul_coeff (T : AdjointableMap A E F) (a : A) (x : E) : T (a • x) = a • T x :=
  T.isAdjointPair.map_smul_coeff_cstarModule a x

/-- Two plain functions between complete C⋆-modules satisfying the adjoint identity
`⟪T x, y⟫_A = ⟪x, S y⟫_A` form an adjointable map: linearity and boundedness are automatic. -/
noncomputable def ofIsAdjointPair [StarOrderedRing A] [CompleteSpace E] [CompleteSpace F]
    {T : E → F} {S : F → E}
    (h : LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) : AdjointableMap A E F where
  toContinuousLinearMap := h.toContinuousLinearMapCStarModule
  adjointMap := h.symm_cstarModule.toContinuousLinearMapCStarModule
  inner_map_left x y := by simpa using h.inner_eq_cstarModule x y

@[simp]
theorem coe_ofIsAdjointPair [StarOrderedRing A] [CompleteSpace E] [CompleteSpace F]
    {T : E → F} {S : F → E}
    (h : LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) : ⇑(ofIsAdjointPair h) = T :=
  funext h.toContinuousLinearMapCStarModule_apply

@[simp]
theorem adjoint_ofIsAdjointPair [StarOrderedRing A] [CompleteSpace E] [CompleteSpace F]
    {T : E → F} {S : F → E}
    (h : LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) : ⇑(ofIsAdjointPair h).adjoint = S :=
  funext h.symm_cstarModule.toContinuousLinearMapCStarModule_apply

/-! ### Composition and identity -/

/-- The composition of adjointable maps, with adjoint `(S ∘ T)† = T† ∘ S†`. -/
def comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) : AdjointableMap A E G where
  toContinuousLinearMap := S.toContinuousLinearMap.comp T.toContinuousLinearMap
  adjointMap := T.adjointMap.comp S.adjointMap
  inner_map_left x z := by
    simp [← adjoint_inner_right]

@[simp]
theorem coe_comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    ⇑(S.comp T) = S ∘ T := (rfl)

theorem comp_apply (S : AdjointableMap A F G) (T : AdjointableMap A E F) (x : E) :
    S.comp T x = S (T x) := (rfl)

@[simp]
theorem adjoint_comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (S.comp T).adjoint = T.adjoint.comp S.adjoint := (rfl)

@[simp]
theorem toContinuousLinearMap_comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (S.comp T).toContinuousLinearMap = S.toContinuousLinearMap.comp T.toContinuousLinearMap :=
  (rfl)

theorem comp_assoc {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul A H]
    [CStarModule A H] (R : AdjointableMap A G H) (S : AdjointableMap A F G)
    (T : AdjointableMap A E F) : (R.comp S).comp T = R.comp (S.comp T) := (rfl)

variable (A E) in
/-- The identity map, which is its own adjoint. -/
def id : AdjointableMap A E E where
  toContinuousLinearMap := ContinuousLinearMap.id ℂ E
  adjointMap := ContinuousLinearMap.id ℂ E
  inner_map_left _ _ := rfl

@[simp]
theorem coe_id : ⇑(id A E) = _root_.id := (rfl)

@[simp]
theorem adjoint_id : (id A E).adjoint = id A E := (rfl)

@[simp]
theorem toContinuousLinearMap_id : (id A E).toContinuousLinearMap = ContinuousLinearMap.id ℂ E :=
  (rfl)

@[simp]
theorem id_comp (T : AdjointableMap A E F) : (id A F).comp T = T := (rfl)

@[simp]
theorem comp_id (T : AdjointableMap A E F) : T.comp (id A E) = T := (rfl)

/-! ### The additive group and complex vector space structure -/

instance instZero : Zero (AdjointableMap A E F) where
  zero := ⟨0, 0, fun _ _ => by simp⟩

instance instAdd : Add (AdjointableMap A E F) where
  add S T := ⟨S.toContinuousLinearMap + T.toContinuousLinearMap, S.adjointMap + T.adjointMap,
    fun x y => by simp [adjoint_inner_right]⟩

instance instNeg : Neg (AdjointableMap A E F) where
  neg T := ⟨-T.toContinuousLinearMap, -T.adjointMap, fun x y => by simp [adjoint_inner_right]⟩

instance instSub : Sub (AdjointableMap A E F) where
  sub S T := ⟨S.toContinuousLinearMap - T.toContinuousLinearMap, S.adjointMap - T.adjointMap,
    fun x y => by simp [adjoint_inner_right]⟩

/-- Complex scalar multiplication; the adjoint of `c • T` is `star c • T†`. -/
instance instSMul : SMul ℂ (AdjointableMap A E F) where
  smul c T := ⟨c • T.toContinuousLinearMap, star c • T.adjointMap,
    fun x y => by simp [adjoint_inner_right]⟩

instance instSMulNat : SMul ℕ (AdjointableMap A E F) where
  smul n T := (n : ℂ) • T

instance instSMulInt : SMul ℤ (AdjointableMap A E F) where
  smul n T := (n : ℂ) • T

instance instIsZeroApply : IsZeroApply (AdjointableMap A E F) where

instance instIsAddApply : IsAddApply (AdjointableMap A E F) where

instance instIsNegApply : IsNegApply (AdjointableMap A E F) where

instance instIsSubApply : IsSubApply (AdjointableMap A E F) where

instance instIsSMulApply : IsSMulApply ℂ (AdjointableMap A E F) where

instance instIsSMulApplyNat : IsSMulApply ℕ (AdjointableMap A E F) where
  smul_apply T n x := Nat.cast_smul_eq_nsmul ℂ n (T x)

instance instIsSMulApplyInt : IsSMulApply ℤ (AdjointableMap A E F) where
  smul_apply T n x := Int.cast_smul_eq_zsmul ℂ n (T x)

instance instAddCommGroup : AddCommGroup (AdjointableMap A E F) :=
  fast_instance% FunLike.addCommGroup

instance instModule : Module ℂ (AdjointableMap A E F) :=
  fast_instance% FunLike.module

@[simp]
theorem toContinuousLinearMap_zero : (0 : AdjointableMap A E F).toContinuousLinearMap = 0 :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_add (S T : AdjointableMap A E F) :
    (S + T).toContinuousLinearMap = S.toContinuousLinearMap + T.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_neg (T : AdjointableMap A E F) :
    (-T).toContinuousLinearMap = -T.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_sub (S T : AdjointableMap A E F) :
    (S - T).toContinuousLinearMap = S.toContinuousLinearMap - T.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_smul (c : ℂ) (T : AdjointableMap A E F) :
    (c • T).toContinuousLinearMap = c • T.toContinuousLinearMap := (rfl)

@[simp]
theorem adjoint_zero : (0 : AdjointableMap A E F).adjoint = 0 := (rfl)

@[simp]
theorem adjoint_add (S T : AdjointableMap A E F) : (S + T).adjoint = S.adjoint + T.adjoint :=
  (rfl)

@[simp]
theorem adjoint_neg (T : AdjointableMap A E F) : (-T).adjoint = -T.adjoint := (rfl)

@[simp]
theorem adjoint_sub (S T : AdjointableMap A E F) : (S - T).adjoint = S.adjoint - T.adjoint :=
  (rfl)

@[simp]
theorem adjoint_smul (c : ℂ) (T : AdjointableMap A E F) :
    (c • T).adjoint = star c • T.adjoint :=
  ext fun _ => rfl

variable (A E F) in
/-- The forgetful map to bounded complex-linear maps, as a linear map. -/
def toContinuousLinearMapₗ : AdjointableMap A E F →ₗ[ℂ] E →L[ℂ] F where
  toFun := toContinuousLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem toContinuousLinearMapₗ_apply (T : AdjointableMap A E F) :
    toContinuousLinearMapₗ A E F T = T.toContinuousLinearMap := (rfl)

variable (A E F) in
/-- The adjoint as a conjugate-linear equivalence `L_A(E, F) ≃ L_A(F, E)`. -/
def adjointₗ : AdjointableMap A E F ≃ₗ⋆[ℂ] AdjointableMap A F E where
  toFun := adjoint
  invFun := adjoint
  left_inv := adjoint_adjoint
  right_inv := adjoint_adjoint
  map_add' := adjoint_add
  map_smul' := adjoint_smul

@[simp]
theorem adjointₗ_apply (T : AdjointableMap A E F) : adjointₗ A E F T = T.adjoint := (rfl)

@[simp]
theorem adjointₗ_symm : (adjointₗ A E F).symm = adjointₗ A F E := (rfl)

/-! ### The operator norm -/

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (AdjointableMap A E F) :=
  NormedAddCommGroup.induced _ _ (toContinuousLinearMapₗ A E F).toAddMonoidHom
    toContinuousLinearMap_injective

noncomputable instance instNormedSpace : NormedSpace ℂ (AdjointableMap A E F) where
  norm_smul_le c T := norm_smul_le c T.toContinuousLinearMap

/-- The norm of an adjointable map is its operator norm: the forgetful map to bounded
complex-linear maps is an isometry. -/
@[simp]
theorem norm_toContinuousLinearMap (T : AdjointableMap A E F) :
    ‖T.toContinuousLinearMap‖ = ‖T‖ := (rfl)

theorem isometry_toContinuousLinearMap :
    Isometry (toContinuousLinearMap : AdjointableMap A E F → E →L[ℂ] F) :=
  AddMonoidHomClass.isometry_of_norm (toContinuousLinearMapₗ A E F) fun _ => rfl

theorem le_opNorm (T : AdjointableMap A E F) (x : E) : ‖T x‖ ≤ ‖T‖ * ‖x‖ :=
  T.toContinuousLinearMap.le_opNorm x

theorem opNorm_comp_le (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ :=
  S.toContinuousLinearMap.opNorm_comp_le T.toContinuousLinearMap

section Norm

variable [StarOrderedRing A]

/-- The adjoint is isometric: `‖T†‖ = ‖T‖`. -/
@[simp]
theorem norm_adjoint (T : AdjointableMap A E F) : ‖T.adjoint‖ = ‖T‖ := by
  rw [← norm_toContinuousLinearMap, ← norm_toContinuousLinearMap, ← adjointMap_eq]
  exact T.isAdjointPair.norm_eq_cstarModule

/-- The C⋆-identity for adjointable maps: `‖T† ∘ T‖ = ‖T‖ ^ 2`. -/
theorem norm_adjoint_comp_self (T : AdjointableMap A E F) :
    ‖T.adjoint.comp T‖ = ‖T‖ ^ 2 := by
  rw [← norm_toContinuousLinearMap, ← norm_toContinuousLinearMap, toContinuousLinearMap_comp,
    ← adjointMap_eq]
  exact T.isAdjointPair.norm_adjoint_comp_self_cstarModule

/-- The map `T ↦ (T, T†)` into pairs of bounded maps is an isometry for the supremum norm. -/
private theorem isometry_prodMk_adjointMap :
    Isometry fun T : AdjointableMap A E F => (T.toContinuousLinearMap, T.adjointMap) :=
  AddMonoidHomClass.isometry_of_norm
    ((toContinuousLinearMapₗ A E F).toAddMonoidHom.prod
      ((toContinuousLinearMapₗ A F E).toAddMonoidHom.comp (adjointₗ A E F).toAddMonoidHom))
    fun T => by simp [Prod.norm_def]

/-- The pairs `(T, S)` of bounded maps satisfying the adjoint identity form a closed set. -/
private theorem isClosed_range_prodMk_adjointMap :
    IsClosed
      (Set.range fun T : AdjointableMap A E F => (T.toContinuousLinearMap, T.adjointMap)) := by
  have : Set.range (fun T : AdjointableMap A E F => (T.toContinuousLinearMap, T.adjointMap)) =
      ⋂ (x : E) (y : F),
        {p : (E →L[ℂ] F) × (F →L[ℂ] E) | inner A (p.1 x) y = inner A x (p.2 y)} := by
    ext p
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun ⟨T, hT⟩ => hT ▸ T.inner_map_left, fun h => ⟨⟨p.1, p.2, h⟩, rfl⟩⟩
  rw [this]
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ ?_
  · exact continuous_inner.comp
      (((ContinuousLinearMap.apply ℂ F x).continuous.comp continuous_fst).prodMk continuous_const)
  · exact continuous_inner.comp
      (continuous_const.prodMk ((ContinuousLinearMap.apply ℂ E y).continuous.comp continuous_snd))

instance instCompleteSpace [CompleteSpace E] [CompleteSpace F] :
    CompleteSpace (AdjointableMap A E F) :=
  (completeSpace_iff_isComplete_range isometry_prodMk_adjointMap.isUniformInducing).mpr
    isClosed_range_prodMk_adjointMap.isComplete

end Norm

/-! ### The C⋆-algebra `L_A(E)` -/

instance instOne : One (AdjointableMap A E E) where
  one := id A E

instance instMul : Mul (AdjointableMap A E E) where
  mul := comp

instance instNatCast : NatCast (AdjointableMap A E E) where
  natCast n := ⟨n, n, fun x y => by
    simp only [ContinuousLinearMap.natCast_apply, ← Nat.cast_smul_eq_nsmul ℂ,
      inner_smul_left_complex, inner_smul_right_complex, star_natCast]⟩

instance instIntCast : IntCast (AdjointableMap A E E) where
  intCast n := ⟨n, n, fun x y => by
    simp only [intCast_apply_eq_smul, ← Int.cast_smul_eq_zsmul ℂ,
      inner_smul_left_complex, inner_smul_right_complex, star_intCast]⟩

instance instNPow : NPow (AdjointableMap A E E) where
  npow n T := ⟨T.toContinuousLinearMap ^ n, T.adjointMap ^ n, by
    induction n with
    | zero => exact fun _ _ => rfl
    | succ n ih =>
      intro x y
      rw [pow_succ, pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, ih, T.inner_map_left]⟩

instance instIsOneApplyEqSelf : IsOneApplyEqSelf (AdjointableMap A E E) where

instance instIsMulApplyEqComp : IsMulApplyEqComp (AdjointableMap A E E) where

instance instIsNPowApplyEqIterate : IsNPowApplyEqIterate (AdjointableMap A E E) where
  pow_apply_eq_iterate T n x := pow_apply_eq_iterate T.toContinuousLinearMap n x

instance instIsNatCastApplyEqSMul : IsNatCastApplyEqSMul (AdjointableMap A E E) where

instance instIsIntCastApplyEqSMul : IsIntCastApplyEqSMul (AdjointableMap A E E) where
  intCast_apply_eq_smul n x := intCast_apply_eq_smul (F := E →L[ℂ] E) n x

theorem one_def : (1 : AdjointableMap A E E) = id A E := (rfl)

theorem mul_def (S T : AdjointableMap A E E) : S * T = S.comp T := (rfl)

@[simp]
theorem toContinuousLinearMap_one :
    (1 : AdjointableMap A E E).toContinuousLinearMap = 1 := (rfl)

@[simp]
theorem toContinuousLinearMap_mul (S T : AdjointableMap A E E) :
    (S * T).toContinuousLinearMap = S.toContinuousLinearMap * T.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_natCast (n : ℕ) :
    (n : AdjointableMap A E E).toContinuousLinearMap = n := (rfl)

@[simp]
theorem toContinuousLinearMap_intCast (n : ℤ) :
    (n : AdjointableMap A E E).toContinuousLinearMap = n := (rfl)

@[simp]
theorem toContinuousLinearMap_pow (T : AdjointableMap A E E) (n : ℕ) :
    (T ^ n).toContinuousLinearMap = T.toContinuousLinearMap ^ n := (rfl)

instance instRing : Ring (AdjointableMap A E E) :=
  fast_instance% FunLike.compRing

instance instAlgebra : Algebra ℂ (AdjointableMap A E E) :=
  Algebra.ofModule (fun _ _ _ => ext fun _ => by simp)
    fun _ _ _ => ext fun _ => by simp

variable (A E) in
/-- The forgetful map `L_A(E) → (E →L[ℂ] E)`, a unital algebra homomorphism. -/
def toContinuousLinearMapAlgHom : AdjointableMap A E E →ₐ[ℂ] E →L[ℂ] E :=
  AlgHom.ofLinearMap (toContinuousLinearMapₗ A E E) (rfl) fun _ _ => rfl

@[simp]
theorem toContinuousLinearMapAlgHom_apply (T : AdjointableMap A E E) :
    toContinuousLinearMapAlgHom A E T = T.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_algebraMap (c : ℂ) :
    (algebraMap ℂ (AdjointableMap A E E) c).toContinuousLinearMap =
      algebraMap ℂ (E →L[ℂ] E) c :=
  (toContinuousLinearMapAlgHom A E).commutes c

noncomputable instance instNormedRing : NormedRing (AdjointableMap A E E) where
  __ := instNormedAddCommGroup
  __ := instRing
  norm_mul_le := opNorm_comp_le

noncomputable instance instNormedAlgebra : NormedAlgebra ℂ (AdjointableMap A E E) where
  norm_smul_le := norm_smul_le

instance instStar : Star (AdjointableMap A E E) where
  star := adjoint

theorem star_eq_adjoint (T : AdjointableMap A E E) : star T = T.adjoint := (rfl)

@[simp]
theorem coe_star (T : AdjointableMap A E E) : ⇑(star T) = T.adjoint := (rfl)

@[simp]
theorem toContinuousLinearMap_star (T : AdjointableMap A E E) :
    (star T).toContinuousLinearMap = T.adjoint.toContinuousLinearMap := (rfl)

instance instStarRing : StarRing (AdjointableMap A E E) where
  star_involutive := adjoint_adjoint
  star_mul S T := adjoint_comp S T
  star_add := adjoint_add

instance instStarModule : StarModule ℂ (AdjointableMap A E E) where
  star_smul := adjoint_smul

instance instCStarRing [StarOrderedRing A] : CStarRing (AdjointableMap A E E) where
  norm_mul_self_le T := by
    rw [← sq, star_eq_adjoint, mul_def, norm_adjoint_comp_self]

/-- For a complete C⋆-module `E`, the adjointable maps `L_A(E)` form a unital C⋆-algebra, with
the adjoint as star and the operator norm. -/
noncomputable instance instCStarAlgebra [StarOrderedRing A] [CompleteSpace E] :
    CStarAlgebra (AdjointableMap A E E) where

/-- The positive cone of `L_A(E)` is that of its C⋆-algebra structure: `0 ≤ T` when `T` is
self-adjoint with nonnegative spectrum. This gives `L_A(E)` its positive square roots and
continuous functional calculus. -/
noncomputable instance instPartialOrder [StarOrderedRing A] [CompleteSpace E] :
    PartialOrder (AdjointableMap A E E) :=
  CStarAlgebra.spectralOrder _

instance instStarOrderedRing [StarOrderedRing A] [CompleteSpace E] :
    StarOrderedRing (AdjointableMap A E E) :=
  CStarAlgebra.spectralOrderedRing _

end AdjointableMap

end TauCeti
