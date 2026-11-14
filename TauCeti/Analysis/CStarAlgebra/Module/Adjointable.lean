/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.UnitInterval
import TauCeti.Analysis.CStarAlgebra.Module.Self

/-!
# Adjointable operators and module unitaries on Hilbert C⋆-modules

For Hilbert C⋆-modules `E` and `F` over `A`, a continuous complex-linear map `T : E →L[ℂ] F` is
*adjointable* if there exists `T* : F →L[ℂ] E` satisfying `⟪T x, y⟫_A = ⟪x, T* y⟫_A` for all
`x ∈ E` and `y ∈ F`. Unlike on Hilbert spaces, a bounded `A`-linear map between complete Hilbert
C⋆-modules need not admit an adjoint: the isometric inclusion of the maximal ideal
`{f ∈ C([0, 1], ℂ) | f 0 = 0}` into `C([0, 1], ℂ)` is a concrete counterexample. Conversely, on
complete modules, the adjoint identity for plain functions already forces complex linearity,
compatibility with the `A`-action, and continuity
(`LinearMap.IsAdjointPair.continuous_cstarModule`).

This file bundles adjointable operators as `TauCeti.AdjointableMap A E F` (`L_A(E, F)`), equips
them with the operator norm and completeness when `E` and `F` are complete, and equips the
endomorphism algebra `TauCeti.AdjointableMap A E E` (`L_A(E)`) with its unital C⋆-algebra
structure, spectral order, continuous functional calculus, positive square roots, natural action
on `E`, orthogonal projections, and adjointable isometries. Right Hilbert `B`-modules are covered
throughout by instantiating the coefficient algebra with `Bᵐᵒᵖ`.

In `L_A(E)`, positivity is characterized purely by `A`-valued inner products without assuming
self-adjointness beforehand (`TauCeti.AdjointableMap.nonneg_iff`):
`0 ≤ T ↔ ∀ x : E, 0 ≤ ⟪x, T x⟫_A`, from which Paschke's operator inequality
`⟪T x, T x⟫_A ≤ ‖T‖ ^ 2 • ⟪x, x⟫_A` and the modulus `|T| = √(T* T)` follow.

We also define bundled Hilbert C⋆-module unitaries `TauCeti.CStarModuleEquiv A E F` and prove
Lance's characterization (Theorem 3.5): a map `U : E → F` is an invertible adjointable operator
whose inverse is its adjoint if and only if it is surjective and preserves the `A`-valued inner
product (`TauCeti.AdjointableMap.adjoint_comp_self_and_self_comp_adjoint_iff` and
`TauCeti.CStarModuleEquiv.ofSurjectiveInner`). Finally, when `A = ℂ`, `L_ℂ(H, F)` and `L_ℂ(H)`
identify isometrically with `H →L[ℂ] F` and the C⋆-algebra `H →L[ℂ] H`.

## Main declarations

* `TauCeti.AdjointableMap`: the space `L_A(E, F)` of adjointable operators between Hilbert
  C⋆-modules, with operator norm, isometric forgetful map `toContinuousLinearMapLI`,
  conjugate-linear isometric adjoint `adjointLI`, and completeness when `E` and `F` are complete.
* `TauCeti.AdjointableMap.instCStarAlgebra`: `L_A(E)` is a unital C⋆-algebra when `E` is complete
  (allowing the zero module), ordered by `CStarAlgebra.spectralOrder`.
* `TauCeti.AdjointableMap.nonneg_iff`: `0 ≤ T ↔ ∀ x, 0 ≤ ⟪x, T x⟫_A` in `L_A(E)`.
* `TauCeti.AdjointableMap.inner_map_self_le`: `⟪T x, T x⟫_A ≤ ‖T‖ ^ 2 • ⟪x, x⟫_A`.
* `TauCeti.AdjointableMap.abs`: the modulus `|T| = CFC.sqrt (T.adjoint.comp T)` in `L_A(E)` for
  `T : L_A(E, F)`, satisfying `⟪|T| x, |T| y⟫_A = ⟪T x, T y⟫_A` and `‖|T| x‖ = ‖T x‖`.
* `TauCeti.CStarModuleEquiv`: unitary equivalences between Hilbert C⋆-modules, constructed either
  from surjective inner-product-preserving maps (`ofSurjectiveInner`) or from adjoint-unitary
  operators (`ofAdjointable`), with `toUnitary : CStarModuleEquiv A E E ≃* unitary L_A(E)`.
* `TauCeti.AdjointableMap.starAlgEquivContinuousLinearMapComplex`: the isometric `⋆`-isomorphism
  `L_ℂ(H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)` for a complex Hilbert space `H`.
* `TauCeti.AdjointableMap.exists_continuousLinearMap_smul_not_adjointable`: a bounded module map
  between complete right Hilbert `C([0, 1], ℂ)`-modules that is not adjointable.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1, 3,
  and 4 (Theorems 3.5 and 4.1).
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2 (Definition 2.17, Proposition 2.21, Corollary 2.22).
* Bruce Blackadar, *Operator Algebras*, Section II.7.2.
-/

public section

open MulOpposite Complex

namespace TauCeti

/-! ### Bundled adjointable operators, algebraic structure, and operator norm -/

/-- An *adjointable operator* between Hilbert C⋆-modules `E` and `F` over `A` is a continuous
`ℂ`-linear map `T : E →L[ℂ] F` equipped with an adjoint `F →L[ℂ] E` satisfying
`⟪T x, y⟫_A = ⟪x, T* y⟫_A`. By nondegeneracy of the `A`-valued inner product, the adjoint is
uniquely determined by `T` (`AdjointableMap.ext`), and `T` automatically commutes with the action
of `A` (`AdjointableMap.map_smul_coeff`). For right Hilbert `B`-modules, take `A = Bᵐᵒᵖ`. -/
structure AdjointableMap (A E F : Type*) [NonUnitalRing A] [StarRing A] [Module ℂ A]
    [StarModule ℂ A] [PartialOrder A] [Norm A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
    extends E →L[ℂ] F where
  /-- The underlying continuous linear map of the adjoint. Prefer `AdjointableMap.adjoint`, which
  bundles the adjoint as an element of `AdjointableMap A F E`. -/
  adjointContinuousLinearMap : F →L[ℂ] E
  /-- The defining adjoint identity `⟪T x, y⟫_A = ⟪x, T* y⟫_A`. -/
  inner_map_eq' :
    ∀ x y, inner A (toContinuousLinearMap x) y = inner A x (adjointContinuousLinearMap y)

namespace AdjointableMap

section General

variable {A E F G : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : AdjointableMap A E F → E →L[ℂ] F) := by
  rintro ⟨T₁, S₁, h₁⟩ ⟨T₂, S₂, h₂⟩ (hT : T₁ = T₂)
  subst hT
  have hS : S₁ = S₂ := ContinuousLinearMap.ext fun y =>
    CStarModule.ext_inner_left (A := A) fun x => (h₁ x y).symm.trans (h₂ x y)
  subst hS
  rfl

instance instFunLike : FunLike (AdjointableMap A E F) E F where
  coe T := T.toContinuousLinearMap
  coe_injective _ _ h := toContinuousLinearMap_injective (DFunLike.coe_injective h)

instance instContinuousSemilinearMapClass :
    ContinuousSemilinearMapClass (AdjointableMap A E F) (RingHom.id ℂ) E F where
  map_add T := T.toContinuousLinearMap.map_add
  map_smulₛₗ T := T.toContinuousLinearMap.map_smul
  map_continuous T := T.toContinuousLinearMap.continuous

@[simp]
theorem coe_toContinuousLinearMap (T : AdjointableMap A E F) :
    ⇑T.toContinuousLinearMap = ⇑T := (rfl)

@[simp]
theorem toContinuousLinearMap_apply (T : AdjointableMap A E F) (x : E) :
    T.toContinuousLinearMap x = T x := (rfl)

@[simp]
theorem mk_apply (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y, inner A (T x) y = inner A x (S y)) (x : E) :
    (⟨T, S, h⟩ : AdjointableMap A E F) x = T x := (rfl)

/-- Adjointable operators are determined by their action on vectors: the adjoint is uniquely
determined by nondegeneracy of the `A`-valued inner product. -/
@[ext]
theorem ext {T S : AdjointableMap A E F} (h : ∀ x, T x = S x) : T = S :=
  DFunLike.ext T S h

@[simp]
theorem toContinuousLinearMap_inj {T S : AdjointableMap A E F} :
    T.toContinuousLinearMap = S.toContinuousLinearMap ↔ T = S :=
  toContinuousLinearMap_injective.eq_iff

/-- The adjoint of an adjointable operator `T : E → F`, bundled as an adjointable operator
`F → E`. -/
def adjoint (T : AdjointableMap A E F) : AdjointableMap A F E where
  toContinuousLinearMap := T.adjointContinuousLinearMap
  adjointContinuousLinearMap := T.toContinuousLinearMap
  inner_map_eq' y x := by
    simpa only [CStarModule.star_inner] using congrArg star (T.inner_map_eq' x y).symm

@[simp]
theorem toContinuousLinearMap_adjoint (T : AdjointableMap A E F) :
    T.adjoint.toContinuousLinearMap = T.adjointContinuousLinearMap := (rfl)

@[simp]
theorem adjointContinuousLinearMap_apply (T : AdjointableMap A E F) (y : F) :
    T.adjointContinuousLinearMap y = T.adjoint y := (rfl)

/-- The defining adjoint identity `⟪T x, y⟫_A = ⟪x, T* y⟫_A`. -/
theorem inner_map_left (T : AdjointableMap A E F) (x : E) (y : F) :
    inner A (T x) y = inner A x (T.adjoint y) :=
  T.inner_map_eq' x y

/-- The symmetric adjoint identity `⟪x, T y⟫_A = ⟪T* x, y⟫_A`. -/
theorem inner_map_right (T : AdjointableMap A E F) (x : F) (y : E) :
    inner A x (T y) = inner A (T.adjoint x) y :=
  (T.adjoint.inner_map_left x y).symm

/-- Every `AdjointableMap` forms a C⋆-module `LinearMap.IsAdjointPair` with its adjoint. -/
theorem isAdjointPair (T : AdjointableMap A E F) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := E)).flip
      (CStarModule.innerₛₗ (A := A) (E := F)).flip T T.adjoint :=
  CStarModule.isAdjointPair_inner_iff.mpr T.inner_map_left

/-- Every adjointable operator commutes with the coefficient `A`-action. For right Hilbert
`B`-modules (`A = Bᵐᵒᵖ`), this states `T (op b • x) = op b • T x`. -/
@[simp]
theorem map_smul_coeff (T : AdjointableMap A E F) (a : A) (x : E) :
    T (a • x) = a • T x :=
  T.isAdjointPair.map_smul_coeff_cstarModule a x

@[simp]
theorem adjoint_adjoint (T : AdjointableMap A E F) : T.adjoint.adjoint = T := (rfl)

theorem adjoint_involutive :
    Function.Involutive (adjoint : AdjointableMap A E E → AdjointableMap A E E) :=
  adjoint_adjoint

theorem adjoint_injective :
    Function.Injective (adjoint : AdjointableMap A E F → AdjointableMap A F E) :=
  Function.LeftInverse.injective adjoint_adjoint

theorem adjoint_surjective :
    Function.Surjective (adjoint : AdjointableMap A E F → AdjointableMap A F E) :=
  Function.RightInverse.surjective adjoint_adjoint

theorem adjoint_bijective :
    Function.Bijective (adjoint : AdjointableMap A E F → AdjointableMap A F E) :=
  ⟨adjoint_injective, adjoint_surjective⟩

@[simp]
theorem adjoint_inj {T S : AdjointableMap A E F} : T.adjoint = S.adjoint ↔ T = S :=
  adjoint_injective.eq_iff

theorem adjoint_eq_iff {T : AdjointableMap A E F} {S : AdjointableMap A F E} :
    T.adjoint = S ↔ ∀ x y, inner A (T x) y = inner A x (S y) := by
  refine ⟨fun h x y => h ▸ T.inner_map_left x y, fun h => ext fun y => ?_⟩
  exact CStarModule.ext_inner_left (A := A) fun x => (T.inner_map_left x y).symm.trans (h x y)

/-- The identity operator on a Hilbert C⋆-module is adjointable, with itself as adjoint. -/
def id (A E : Type*) [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
    [PartialOrder A] [Norm A] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul A E] [CStarModule A E] : AdjointableMap A E E where
  toContinuousLinearMap := ContinuousLinearMap.id ℂ E
  adjointContinuousLinearMap := ContinuousLinearMap.id ℂ E
  inner_map_eq' _ _ := rfl

@[simp] theorem id_apply (x : E) : AdjointableMap.id A E x = x := (rfl)
@[simp] theorem adjoint_id : (AdjointableMap.id A E).adjoint = AdjointableMap.id A E := (rfl)

@[simp]
theorem toContinuousLinearMap_id :
    (AdjointableMap.id A E).toContinuousLinearMap = ContinuousLinearMap.id ℂ E := (rfl)

/-- Composition of adjointable operators, with `(T ∘ S)* = S* ∘ T*`. -/
def comp (T : AdjointableMap A F G) (S : AdjointableMap A E F) : AdjointableMap A E G where
  toContinuousLinearMap := T.toContinuousLinearMap.comp S.toContinuousLinearMap
  adjointContinuousLinearMap := S.adjointContinuousLinearMap.comp T.adjointContinuousLinearMap
  inner_map_eq' x z := by
    simp only [ContinuousLinearMap.comp_apply, toContinuousLinearMap_apply,
      adjointContinuousLinearMap_apply]
    rw [T.inner_map_left, S.inner_map_left]

@[simp]
theorem comp_apply (T : AdjointableMap A F G) (S : AdjointableMap A E F) (x : E) :
    T.comp S x = T (S x) := (rfl)

@[simp]
theorem toContinuousLinearMap_comp (T : AdjointableMap A F G) (S : AdjointableMap A E F) :
    (T.comp S).toContinuousLinearMap = T.toContinuousLinearMap.comp S.toContinuousLinearMap := (rfl)

@[simp]
theorem adjoint_comp (T : AdjointableMap A F G) (S : AdjointableMap A E F) :
    (T.comp S).adjoint = S.adjoint.comp T.adjoint := (rfl)

theorem comp_assoc {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [SMul A H] [CStarModule A H]
    (R : AdjointableMap A G H) (T : AdjointableMap A F G) (S : AdjointableMap A E F) :
    (R.comp T).comp S = R.comp (T.comp S) := (rfl)

@[simp]
theorem id_comp (T : AdjointableMap A E F) : (AdjointableMap.id A F).comp T = T :=
  ext fun _ => rfl

@[simp]
theorem comp_id (T : AdjointableMap A E F) : T.comp (AdjointableMap.id A E) = T :=
  ext fun _ => rfl

/-! ### Linear, normed-space, and star-algebra structures -/

instance instZero : Zero (AdjointableMap A E F) where
  zero := ⟨0, 0, fun _ _ => by simp [CStarModule.inner_zero_left, CStarModule.inner_zero_right]⟩

instance instAdd : Add (AdjointableMap A E F) where
  add T S := ⟨T.toContinuousLinearMap + S.toContinuousLinearMap,
    T.adjointContinuousLinearMap + S.adjointContinuousLinearMap,
    fun x y => by
      simp only [add_apply, toContinuousLinearMap_apply, adjointContinuousLinearMap_apply,
        CStarModule.inner_add_left, CStarModule.inner_add_right,
        T.inner_map_left, S.inner_map_left]⟩

instance instNeg : Neg (AdjointableMap A E F) where
  neg T := ⟨-T.toContinuousLinearMap, -T.adjointContinuousLinearMap,
    fun x y => by
      simp only [neg_apply, toContinuousLinearMap_apply, adjointContinuousLinearMap_apply,
        CStarModule.inner_neg_left, CStarModule.inner_neg_right, T.inner_map_left]⟩

instance instSub : Sub (AdjointableMap A E F) where
  sub T S := ⟨T.toContinuousLinearMap - S.toContinuousLinearMap,
    T.adjointContinuousLinearMap - S.adjointContinuousLinearMap,
    fun x y => by
      simp only [sub_apply, toContinuousLinearMap_apply, adjointContinuousLinearMap_apply,
        CStarModule.inner_sub_left, CStarModule.inner_sub_right,
        T.inner_map_left, S.inner_map_left]⟩

instance instSMulNat : SMul ℕ (AdjointableMap A E F) where
  smul n T := ⟨n • T.toContinuousLinearMap, n • T.adjointContinuousLinearMap,
    fun x y => by
      simp only [smul_apply, toContinuousLinearMap_apply, adjointContinuousLinearMap_apply,
        ← Nat.cast_smul_eq_nsmul ℂ, CStarModule.inner_smul_left_complex,
        CStarModule.inner_smul_right_complex, star_natCast, T.inner_map_left]⟩

instance instSMulInt : SMul ℤ (AdjointableMap A E F) where
  smul n T := ⟨n • T.toContinuousLinearMap, n • T.adjointContinuousLinearMap,
    fun x y => by
      simp only [smul_apply, toContinuousLinearMap_apply, adjointContinuousLinearMap_apply,
        ← Int.cast_smul_eq_zsmul ℂ, CStarModule.inner_smul_left_complex,
        CStarModule.inner_smul_right_complex, star_intCast, T.inner_map_left]⟩

instance instSMulComplex : SMul ℂ (AdjointableMap A E F) where
  smul c T := ⟨c • T.toContinuousLinearMap, star c • T.adjointContinuousLinearMap,
    fun x y => by
      simp only [smul_apply, toContinuousLinearMap_apply, adjointContinuousLinearMap_apply,
        CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex,
        T.inner_map_left]⟩

@[simp] theorem zero_apply (x : E) : (0 : AdjointableMap A E F) x = 0 := (rfl)
@[simp] theorem add_apply (T S : AdjointableMap A E F) (x : E) : (T + S) x = T x + S x := (rfl)
@[simp] theorem neg_apply (T : AdjointableMap A E F) (x : E) : (-T) x = -T x := (rfl)
@[simp] theorem sub_apply (T S : AdjointableMap A E F) (x : E) : (T - S) x = T x - S x := (rfl)
@[simp] theorem smul_apply (c : ℂ) (T : AdjointableMap A E F) (x : E) : (c • T) x = c • T x := (rfl)

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

instance instAddCommGroup : AddCommGroup (AdjointableMap A E F) :=
  toContinuousLinearMap_injective.addCommGroup toContinuousLinearMap
    toContinuousLinearMap_zero toContinuousLinearMap_add toContinuousLinearMap_neg
    toContinuousLinearMap_sub (fun _ _ => rfl) (fun _ _ => rfl)

instance instModuleComplex : Module ℂ (AdjointableMap A E F) :=
  toContinuousLinearMap_injective.module ℂ
    { toFun := toContinuousLinearMap
      map_zero' := toContinuousLinearMap_zero
      map_add' := toContinuousLinearMap_add }
    toContinuousLinearMap_smul

/-- The forgetful `ℂ`-linear map from `AdjointableMap A E F` to `E →L[ℂ] F`. -/
def toContinuousLinearMapLinear : AdjointableMap A E F →ₗ[ℂ] (E →L[ℂ] F) where
  toFun := toContinuousLinearMap
  map_add' := toContinuousLinearMap_add
  map_smul' := toContinuousLinearMap_smul

@[simp] theorem toContinuousLinearMapLinear_apply (T : AdjointableMap A E F) :
    toContinuousLinearMapLinear T = T.toContinuousLinearMap := (rfl)

@[simp]
theorem sum_apply {ι : Type*} (s : Finset ι) (T : ι → AdjointableMap A E F) (x : E) :
    (∑ i ∈ s, T i) x = ∑ i ∈ s, T i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ hnotmem ih => simp [Finset.sum_insert hnotmem, ih]

@[simp] theorem adjoint_zero : (0 : AdjointableMap A E F).adjoint = 0 := ext fun _ => rfl
@[simp] theorem adjoint_add (T S : AdjointableMap A E F) :
    (T + S).adjoint = T.adjoint + S.adjoint := ext fun _ => rfl
@[simp] theorem adjoint_neg (T : AdjointableMap A E F) : (-T).adjoint = -T.adjoint :=
  ext fun _ => rfl
@[simp] theorem adjoint_sub (T S : AdjointableMap A E F) :
    (T - S).adjoint = T.adjoint - S.adjoint := ext fun _ => rfl
@[simp] theorem adjoint_smul (c : ℂ) (T : AdjointableMap A E F) :
    (c • T).adjoint = star c • T.adjoint := ext fun _ => rfl

/-- The adjoint bundled as a conjugate-linear equivalence `L_A(E, F) ≃ₗ⋆[ℂ] L_A(F, E)`. -/
def adjointLinearEquiv : AdjointableMap A E F ≃ₗ⋆[ℂ] AdjointableMap A F E where
  toFun := adjoint
  invFun := adjoint
  left_inv := adjoint_adjoint
  right_inv := adjoint_adjoint
  map_add' := adjoint_add
  map_smul' := adjoint_smul

@[simp] theorem adjointLinearEquiv_apply (T : AdjointableMap A E F) :
    adjointLinearEquiv T = T.adjoint := (rfl)
@[simp] theorem adjointLinearEquiv_symm :
    (adjointLinearEquiv : AdjointableMap A E F ≃ₗ⋆[ℂ] AdjointableMap A F E).symm =
      adjointLinearEquiv := (rfl)

@[simp] theorem comp_zero (T : AdjointableMap A F G) : T.comp (0 : AdjointableMap A E F) = 0 :=
  ext fun _ => map_zero T
@[simp] theorem zero_comp (S : AdjointableMap A E F) : (0 : AdjointableMap A F G).comp S = 0 :=
  ext fun _ => rfl

theorem comp_add (T : AdjointableMap A F G) (S₁ S₂ : AdjointableMap A E F) :
    T.comp (S₁ + S₂) = T.comp S₁ + T.comp S₂ :=
  ext fun x => map_add T (S₁ x) (S₂ x)

theorem add_comp (T₁ T₂ : AdjointableMap A F G) (S : AdjointableMap A E F) :
    (T₁ + T₂).comp S = T₁.comp S + T₂.comp S :=
  ext fun _ => rfl

theorem comp_smul (T : AdjointableMap A F G) (c : ℂ) (S : AdjointableMap A E F) :
    T.comp (c • S) = c • T.comp S :=
  ext fun x => map_smul T c (S x)

theorem smul_comp (c : ℂ) (T : AdjointableMap A F G) (S : AdjointableMap A E F) :
    (c • T).comp S = c • T.comp S :=
  ext fun _ => rfl

theorem toContinuousLinearMapLinear_injective :
    Function.Injective (toContinuousLinearMapLinear : AdjointableMap A E F →ₗ[ℂ] (E →L[ℂ] F)) := by
  intro T S h
  rwa [toContinuousLinearMapLinear_apply, toContinuousLinearMapLinear_apply,
    toContinuousLinearMap_inj] at h

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (AdjointableMap A E F) :=
  NormedAddCommGroup.induced (AdjointableMap A E F) (E →L[ℂ] F)
    toContinuousLinearMapLinear toContinuousLinearMapLinear_injective

noncomputable instance instNormedSpaceComplex : NormedSpace ℂ (AdjointableMap A E F) :=
  NormedSpace.induced ℂ (AdjointableMap A E F) (E →L[ℂ] F) toContinuousLinearMapLinear

@[simp]
theorem norm_toContinuousLinearMap (T : AdjointableMap A E F) :
    ‖T.toContinuousLinearMap‖ = ‖T‖ := (rfl)

theorem norm_def (T : AdjointableMap A E F) : ‖T‖ = ‖T.toContinuousLinearMap‖ := (rfl)

/-- The forgetful map `L_A(E, F) →ₗᵢ[ℂ] (E →L[ℂ] F)` is a `ℂ`-linear isometry. -/
noncomputable def toContinuousLinearMapLI : AdjointableMap A E F →ₗᵢ[ℂ] (E →L[ℂ] F) where
  toLinearMap := toContinuousLinearMapLinear
  norm_map' := norm_toContinuousLinearMap

@[simp]
theorem toContinuousLinearMapLI_apply (T : AdjointableMap A E F) :
    toContinuousLinearMapLI T = T.toContinuousLinearMap := (rfl)

theorem le_opNorm (T : AdjointableMap A E F) (x : E) : ‖T x‖ ≤ ‖T‖ * ‖x‖ :=
  T.toContinuousLinearMap.le_opNorm x

theorem opNorm_le_bound (T : AdjointableMap A E F) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x, ‖T x‖ ≤ M * ‖x‖) : ‖T‖ ≤ M :=
  T.toContinuousLinearMap.opNorm_le_bound hM h

theorem norm_comp_le (T : AdjointableMap A F G) (S : AdjointableMap A E F) :
    ‖T.comp S‖ ≤ ‖T‖ * ‖S‖ :=
  T.toContinuousLinearMap.opNorm_comp_le S.toContinuousLinearMap

/-- Continuous bilinear composition `(T, S) ↦ T ∘ S` of adjointable operators. -/
noncomputable def compL :
    AdjointableMap A F G →L[ℂ] AdjointableMap A E F →L[ℂ] AdjointableMap A E G :=
  LinearMap.mkContinuous₂
    { toFun := fun (T : AdjointableMap A F G) =>
        { toFun := T.comp
          map_add' := T.comp_add
          map_smul' := T.comp_smul }
      map_add' := fun _ _ => LinearMap.ext fun _ => add_comp _ _ _
      map_smul' := fun _ _ => LinearMap.ext fun _ => smul_comp _ _ _ }
    1 fun T S => by simpa only [LinearMap.coe_mk, AddHom.coe_mk, one_mul] using norm_comp_le T S

@[simp]
theorem compL_apply (T : AdjointableMap A F G) (S : AdjointableMap A E F) :
    compL T S = T.comp S := (rfl)

/-! ### Endomorphism algebra `L_A(E)` and natural action on `E` -/

instance instOne : One (AdjointableMap A E E) := ⟨AdjointableMap.id A E⟩
instance instMul : Mul (AdjointableMap A E E) := ⟨comp⟩

theorem one_def : (1 : AdjointableMap A E E) = AdjointableMap.id A E := (rfl)
theorem mul_def (T S : AdjointableMap A E E) : T * S = T.comp S := (rfl)
@[simp] theorem one_apply (x : E) : (1 : AdjointableMap A E E) x = x := (rfl)
@[simp] theorem mul_apply (T S : AdjointableMap A E E) (x : E) : (T * S) x = T (S x) := (rfl)
@[simp] theorem toContinuousLinearMap_one :
    (1 : AdjointableMap A E E).toContinuousLinearMap = 1 := (rfl)
@[simp] theorem toContinuousLinearMap_mul (T S : AdjointableMap A E E) :
    (T * S).toContinuousLinearMap = T.toContinuousLinearMap * S.toContinuousLinearMap := (rfl)

instance instRing : Ring (AdjointableMap A E E) where
  __ := instAddCommGroup
  left_distrib := comp_add
  right_distrib := add_comp
  zero_mul := zero_comp
  mul_zero := comp_zero
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

instance instAlgebraComplex : Algebra ℂ (AdjointableMap A E E) :=
  Algebra.ofModule
    (fun c T S => by rw [mul_def, mul_def, smul_comp])
    (fun c T S => by rw [mul_def, mul_def, comp_smul])

/-- The forgetful `ℂ`-algebra homomorphism from `AdjointableMap A E E` to `E →L[ℂ] E`. -/
def toContinuousLinearMapAlgHom : AdjointableMap A E E →ₐ[ℂ] (E →L[ℂ] E) where
  toRingHom :=
    { toFun := toContinuousLinearMap
      map_one' := toContinuousLinearMap_one
      map_mul' := toContinuousLinearMap_mul
      map_zero' := toContinuousLinearMap_zero
      map_add' := toContinuousLinearMap_add }
  commutes' c := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]

@[simp]
theorem toContinuousLinearMapAlgHom_apply (T : AdjointableMap A E E) :
    toContinuousLinearMapAlgHom T = T.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_pow (T : AdjointableMap A E E) (n : ℕ) :
    (T ^ n).toContinuousLinearMap = T.toContinuousLinearMap ^ n :=
  map_pow toContinuousLinearMapAlgHom T n

@[simp]
theorem pow_apply (T : AdjointableMap A E E) (n : ℕ) (x : E) :
    (T ^ n) x = (T.toContinuousLinearMap ^ n) x := by
  rw [← toContinuousLinearMap_pow, toContinuousLinearMap_apply]

@[simp]
theorem algebraMap_apply (c : ℂ) (x : E) :
    algebraMap ℂ (AdjointableMap A E E) c x = c • x := by
  rw [Algebra.algebraMap_eq_smul_one, smul_apply, one_apply]

noncomputable instance instNormedRing : NormedRing (AdjointableMap A E E) where
  __ := instNormedAddCommGroup
  __ := instRing
  dist_eq x y := by rw [dist_comm, dist_eq_norm, sub_eq_neg_add]
  norm_mul_le := norm_comp_le

noncomputable instance instNormedAlgebraComplex : NormedAlgebra ℂ (AdjointableMap A E E) :=
  { instAlgebraComplex, instNormedSpaceComplex with }

instance instNontrivial [Nontrivial E] : Nontrivial (AdjointableMap A E E) :=
  ⟨⟨0, 1, fun h => by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact hx (by simpa using (DFunLike.congr_fun h x).symm)⟩⟩

instance instNormOneClass [Nontrivial E] : NormOneClass (AdjointableMap A E E) where
  norm_one := by rw [← norm_toContinuousLinearMap, toContinuousLinearMap_one, norm_one]

instance instStar : Star (AdjointableMap A E E) where
  star := adjoint

theorem star_eq_adjoint (T : AdjointableMap A E E) : star T = T.adjoint := (rfl)

instance instStarAddMonoid : StarAddMonoid (AdjointableMap A E E) where
  star_involutive T := by simp only [star_eq_adjoint, adjoint_adjoint]
  star_add T S := by simp only [star_eq_adjoint, adjoint_add]

instance instStarRing : StarRing (AdjointableMap A E E) where
  __ := instStarAddMonoid
  star_mul T S := by simp only [star_eq_adjoint, mul_def, adjoint_comp]

instance instStarModuleComplex : StarModule ℂ (AdjointableMap A E E) where
  star_smul c T := by simp only [star_eq_adjoint, adjoint_smul]

theorem inner_star_left (T : AdjointableMap A E E) (x y : E) :
    inner A (star T x) y = inner A x (T y) := by
  rw [star_eq_adjoint]
  exact T.adjoint.inner_map_left x y

theorem inner_star_right (T : AdjointableMap A E E) (x y : E) :
    inner A x (star T y) = inner A (T x) y := by
  rw [star_eq_adjoint]
  exact (T.inner_map_left x y).symm

theorem isSelfAdjoint_iff' {T : AdjointableMap A E E} : IsSelfAdjoint T ↔ T.adjoint = T := by
  rw [IsSelfAdjoint, star_eq_adjoint]

theorem isSelfAdjoint_iff {T : AdjointableMap A E E} :
    IsSelfAdjoint T ↔ ∀ x y, inner A (T x) y = inner A x (T y) :=
  isSelfAdjoint_iff'.trans adjoint_eq_iff

/-- Over `ℂ`, an adjointable operator is self-adjoint if and only if all of its diagonal inner
products `⟪x, T x⟫_A` are self-adjoint, by complex polarization. -/
theorem isSelfAdjoint_iff_forall_isSelfAdjoint {T : AdjointableMap A E E} :
    IsSelfAdjoint T ↔ ∀ x, IsSelfAdjoint (inner A x (T x)) := by
  refine ⟨fun hT x => ?_, fun h => isSelfAdjoint_iff.mpr fun x y => ?_⟩
  · rw [IsSelfAdjoint, CStarModule.star_inner, ← inner_star_right, hT.star_eq]
  · have hdiag (z : E) : inner A (T z) z = inner A z (T z) := by
      rw [← CStarModule.star_inner, (h z).star_eq]
    have hpol : inner A (T x) y - inner A x (T y) = (4 : ℂ)⁻¹ • (
        (inner A (T (x + y)) (x + y) - inner A (x + y) (T (x + y))) -
        (inner A (T (x - y)) (x - y) - inner A (x - y) (T (x - y))) -
        I • (inner A (T (x + I • y)) (x + I • y) - inner A (x + I • y) (T (x + I • y))) +
        I • (inner A (T (x - I • y)) (x - I • y) - inner A (x - I • y) (T (x - I • y)))) := by
      simp only [map_add, map_sub, map_smul, CStarModule.inner_add_left,
        CStarModule.inner_add_right, CStarModule.inner_sub_left, CStarModule.inner_sub_right,
        CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex,
        Complex.star_def, conj_I, smul_add, smul_sub, smul_neg, smul_smul, neg_smul, I_mul_I]
      module
    rw [← sub_eq_zero, hpol, hdiag, hdiag, hdiag, hdiag]
    simp

/-- The natural left action of `L_A(E)` on `E` by evaluation. -/
instance instSMulApply : SMul (AdjointableMap A E E) E where
  smul T x := T x

@[simp]
protected theorem smul_def (T : AdjointableMap A E E) (x : E) : T • x = T x := (rfl)

/-- The natural left `L_A(E)`-module structure on `E`, commuting with both complex scalars and the
coefficient `A`-action. -/
instance applyModule : Module (AdjointableMap A E E) E where
  one_smul x := by rw [AdjointableMap.smul_def, one_apply]
  mul_smul T S x := by
    rw [AdjointableMap.smul_def, mul_apply, AdjointableMap.smul_def, AdjointableMap.smul_def]
  smul_zero T := map_zero T
  smul_add T := map_add T
  add_smul T S x := by
    rw [AdjointableMap.smul_def, add_apply, AdjointableMap.smul_def, AdjointableMap.smul_def]
  zero_smul x := by rw [AdjointableMap.smul_def, zero_apply]

instance applyFaithfulSMul : FaithfulSMul (AdjointableMap A E E) E :=
  ⟨fun {_ _} => ext⟩

instance applySMulCommClassComplex : SMulCommClass ℂ (AdjointableMap A E E) E where
  smul_comm c T x := (map_smul T c x).symm

instance applySMulCommClassComplex' : SMulCommClass (AdjointableMap A E E) ℂ E where
  smul_comm T c x := map_smul T c x

instance applyIsScalarTowerComplex : IsScalarTower ℂ (AdjointableMap A E E) E where
  smul_assoc c T x := by rw [AdjointableMap.smul_def, smul_apply, AdjointableMap.smul_def]

instance applySMulCommClassCoeff : SMulCommClass A (AdjointableMap A E E) E where
  smul_comm a T x := (T.map_smul_coeff a x).symm

instance applySMulCommClassCoeff' : SMulCommClass (AdjointableMap A E E) A E where
  smul_comm := map_smul_coeff

instance continuousConstSMul_apply : ContinuousConstSMul (AdjointableMap A E E) E :=
  ⟨fun T => T.toContinuousLinearMap.continuous⟩

instance isBoundedSMul_apply : IsBoundedSMul (AdjointableMap A E E) E :=
  IsBoundedSMul.of_norm_smul_le fun T x => by
    rw [AdjointableMap.smul_def]
    exact le_opNorm T x

/-! ### Adjointable isometries -/

/-- An adjointable operator `V : E → F` satisfies `V* ∘ V = id_E` if and only if it preserves the
`A`-valued inner product on all pairs of vectors. -/
theorem adjoint_comp_self_eq_id_iff {V : AdjointableMap A E F} :
    V.adjoint.comp V = AdjointableMap.id A E ↔ ∀ x y : E, inner A (V x) (V y) = inner A x y := by
  refine ⟨fun h x y => ?_, fun h => ext fun y => CStarModule.ext_inner_left (A := A) fun x => ?_⟩
  · rw [V.inner_map_left, ← comp_apply, h, id_apply]
  · rw [comp_apply, ← V.inner_map_left, id_apply, h]

/-- By polarization, `V* ∘ V = id_E` holds if and only if `V` preserves diagonal inner products
`⟪x, x⟫_A`. -/
theorem adjoint_comp_self_eq_id_iff_self {V : AdjointableMap A E F} :
    V.adjoint.comp V = AdjointableMap.id A E ↔ ∀ x : E, inner A (V x) (V x) = inner A x x := by
  rw [adjoint_comp_self_eq_id_iff]
  refine ⟨fun h x => h x x, fun h x y => ?_⟩
  rw [CStarModule.inner_polarization (V x) (V y), CStarModule.inner_polarization x y]
  simp only [← map_add, ← map_sub, ← map_smul, h]

theorem norm_map_of_adjoint_comp_self_eq_id {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = AdjointableMap.id A E) (x : E) : ‖V x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A),
    CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (x := x),
    adjoint_comp_self_eq_id_iff.mp hV x x]

theorem isometry_of_adjoint_comp_self_eq_id {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = AdjointableMap.id A E) : Isometry V :=
  AddMonoidHomClass.isometry_of_norm V (norm_map_of_adjoint_comp_self_eq_id hV)

/-- If `V : E → F` is an adjointable isometry (`V* ∘ V = id_E`), its range projection `V ∘ V*` is
a star projection in `L_A(F)`. -/
theorem isStarProjection_comp_adjoint {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = AdjointableMap.id A E) :
    IsStarProjection (V.comp V.adjoint) where
  isIdempotentElem := by
    rw [IsIdempotentElem, mul_def, comp_assoc, ← comp_assoc V.adjoint V V.adjoint, hV, id_comp]
  isSelfAdjoint := by
    rw [IsSelfAdjoint, star_eq_adjoint, adjoint_comp, adjoint_adjoint]

end General

section RightAlgebraic

variable {A E F : Type*} [NonUnitalSeminormedRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]

/-- The adjoint identity for right Hilbert `A`-modules in `A`-valued inner-product form:
`⟨T x, y⟩_A = ⟨x, T* y⟩_A`. -/
theorem unop_inner_map_left (T : AdjointableMap Aᵐᵒᵖ E F) (x : E) (y : F) :
    unop (inner Aᵐᵒᵖ (T x) y) = unop (inner Aᵐᵒᵖ x (T.adjoint y)) :=
  congrArg unop (T.inner_map_left x y)

/-- The symmetric adjoint identity for right Hilbert `A`-modules:
`⟨x, T y⟩_A = ⟨T* x, y⟩_A`. -/
theorem unop_inner_map_right (T : AdjointableMap Aᵐᵒᵖ E F) (x : F) (y : E) :
    unop (inner Aᵐᵒᵖ x (T y)) = unop (inner Aᵐᵒᵖ (T.adjoint x) y) :=
  congrArg unop (T.inner_map_right x y)

end RightAlgebraic

/-! ### Completeness, C⋆-algebra structure, spectral order, and modulus -/

section CStar

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- The adjoint has the same operator norm as the operator: `‖T*‖ = ‖T‖`. -/
@[simp]
theorem norm_adjoint (T : AdjointableMap A E F) : ‖T.adjoint‖ = ‖T‖ :=
  T.isAdjointPair.norm_eq_cstarModule

/-- The adjoint bundled as a conjugate-linear isometric equivalence
`L_A(E, F) ≃ₗᵢ⋆[ℂ] L_A(F, E)`. -/
noncomputable def adjointLI : AdjointableMap A E F ≃ₗᵢ⋆[ℂ] AdjointableMap A F E :=
  { adjointLinearEquiv with norm_map' := norm_adjoint }

@[simp]
theorem adjointLI_apply (T : AdjointableMap A E F) : adjointLI T = T.adjoint := (rfl)

@[simp]
theorem adjointLI_symm :
    (adjointLI : AdjointableMap A E F ≃ₗᵢ⋆[ℂ] AdjointableMap A F E).symm = adjointLI := (rfl)

/-- The C⋆-identity for rectangular adjointable operators: `‖T* ∘ T‖ = ‖T‖ ^ 2`. -/
@[simp]
theorem norm_adjoint_comp_self (T : AdjointableMap A E F) :
    ‖T.adjoint.comp T‖ = ‖T‖ ^ 2 := by
  simpa only [← norm_toContinuousLinearMap, toContinuousLinearMap_comp] using
    T.isAdjointPair.norm_adjoint_comp_self_cstarModule

/-- The dual C⋆-identity for rectangular adjointable operators: `‖T ∘ T*‖ = ‖T‖ ^ 2`. -/
@[simp]
theorem norm_self_comp_adjoint (T : AdjointableMap A E F) :
    ‖T.comp T.adjoint‖ = ‖T‖ ^ 2 := by
  simpa only [adjoint_adjoint, norm_adjoint] using norm_adjoint_comp_self T.adjoint

/-- Constructing an `AdjointableMap` on complete C⋆-modules from plain functions satisfying the
adjoint identity; continuity and linearity are supplied automatically by the closed graph
theorem. -/
noncomputable def ofAdjointPair [CompleteSpace E] [CompleteSpace F]
    (T : E → F) (S : F → E) (h : ∀ x y, inner A (T x) y = inner A x (S y)) :
    AdjointableMap A E F :=
  let hpair := (CStarModule.isAdjointPair_inner_iff (A := A)).mpr h
  { toContinuousLinearMap := hpair.toContinuousLinearMapCStarModule
    adjointContinuousLinearMap := hpair.symm_cstarModule.toContinuousLinearMapCStarModule
    inner_map_eq' := fun x y => by simp [h x y] }

@[simp]
theorem ofAdjointPair_apply [CompleteSpace E] [CompleteSpace F]
    (T : E → F) (S : F → E) (h : ∀ x y, inner A (T x) y = inner A x (S y)) (x : E) :
    ofAdjointPair T S h x = T x :=
  (CStarModule.isAdjointPair_inner_iff.mpr h).toContinuousLinearMapCStarModule_apply x

@[simp]
theorem adjoint_ofAdjointPair_apply [CompleteSpace E] [CompleteSpace F]
    (T : E → F) (S : F → E) (h : ∀ x y, inner A (T x) y = inner A x (S y)) (y : F) :
    (ofAdjointPair T S h).adjoint y = S y :=
  LinearMap.IsAdjointPair.toContinuousLinearMapCStarModule_apply
    (CStarModule.isAdjointPair_inner_iff.mpr h).symm_cstarModule y

/-- Constructing an `AdjointableMap` on complete C⋆-modules from a function admitting some plain
adjoint function. -/
noncomputable def ofExistsAdjoint [CompleteSpace E] [CompleteSpace F]
    (T : E → F) (h : ∃ S : F → E, ∀ x y, inner A (T x) y = inner A x (S y)) :
    AdjointableMap A E F :=
  ofAdjointPair T h.choose h.choose_spec

@[simp]
theorem ofExistsAdjoint_apply [CompleteSpace E] [CompleteSpace F]
    (T : E → F) (h : ∃ S : F → E, ∀ x y, inner A (T x) y = inner A x (S y)) (x : E) :
    ofExistsAdjoint T h x = T x :=
  ofAdjointPair_apply T h.choose h.choose_spec x

/-- Between complete Hilbert C⋆-modules, a plain function (and in particular a bounded module map)
arises from an `AdjointableMap` if and only if there exists a function satisfying the adjoint
identity. -/
theorem exists_coe_eq_iff [CompleteSpace E] [CompleteSpace F] {T : E → F} :
    (∃ T' : AdjointableMap A E F, ⇑T' = T) ↔
      ∃ S : F → E, ∀ x y, inner A (T x) y = inner A x (S y) := by
  refine ⟨?_, fun h => ⟨ofExistsAdjoint T h, funext (ofExistsAdjoint_apply T h)⟩⟩
  rintro ⟨T', rfl⟩
  exact ⟨T'.adjoint, T'.inner_map_left⟩

/-- When `E` and `F` are complete, `L_A(E, F)` is complete: the map `T ↦ (T, T*)` is an isometry
onto a closed subspace of `(E →L[ℂ] F) × (F →L[ℂ] E)`. -/
instance instCompleteSpace [CompleteSpace E] [CompleteSpace F] :
    CompleteSpace (AdjointableMap A E F) := by
  let emb : AdjointableMap A E F → (E →L[ℂ] F) × (F →L[ℂ] E) :=
    fun T => (T.toContinuousLinearMap, T.adjoint.toContinuousLinearMap)
  have hiso : Isometry emb := Isometry.of_dist_eq fun T S => by
    simp only [emb, dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub,
      ← toContinuousLinearMap_sub, ← adjoint_sub, norm_toContinuousLinearMap, norm_adjoint,
      max_self]
  rw [completeSpace_iff_isComplete_range hiso.isUniformInducing]
  have hrange : Set.range emb =
      ⋂ (x : E) (y : F), {p | inner A (p.1 x) y = inner A x (p.2 y)} := by
    ext ⟨u, v⟩
    simp only [emb, Set.mem_range, Prod.mk.injEq, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨?_, fun h => ⟨⟨u, v, h⟩, rfl, rfl⟩⟩
    rintro ⟨T, rfl, rfl⟩ x y
    exact T.inner_map_left x y
  rw [hrange]
  refine IsClosed.isComplete (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ ?_)
  · exact CStarModule.continuous_inner.comp
      (((ContinuousLinearMap.apply ℂ F x).continuous.comp continuous_fst).prodMk continuous_const)
  · exact CStarModule.continuous_inner.comp
      (continuous_const.prodMk ((ContinuousLinearMap.apply ℂ E y).continuous.comp continuous_snd))

instance instNormedStarGroup : NormedStarGroup (AdjointableMap A E E) where
  norm_star_le T := by rw [star_eq_adjoint, norm_adjoint]

instance instCStarRing : CStarRing (AdjointableMap A E E) where
  norm_mul_self_le T := by
    rw [← sq, ← norm_adjoint_comp_self T, star_eq_adjoint, mul_def]

/-- For a complete Hilbert C⋆-module `E` over `A` (including the zero module), the algebra
`L_A(E)` of adjointable endomorphisms is a unital complex C⋆-algebra. -/
noncomputable instance instCStarAlgebra [CompleteSpace E] :
    CStarAlgebra (AdjointableMap A E E) where

noncomputable instance instPartialOrder [CompleteSpace E] :
    PartialOrder (AdjointableMap A E E) :=
  CStarAlgebra.spectralOrder _

instance instStarOrderedRing [CompleteSpace E] :
    StarOrderedRing (AdjointableMap A E E) :=
  CStarAlgebra.spectralOrderedRing _

/-- Lance's positivity theorem (Theorem 4.1): in the C⋆-algebra `L_A(E)` of a complete Hilbert
C⋆-module `E`, an operator `T` is positive (`0 ≤ T` in the spectral order) if and only if
`0 ≤ ⟪x, T x⟫_A` in `A` for every `x ∈ E`. Self-adjointness of `T` is not assumed separately; it
follows automatically by complex polarization. -/
theorem nonneg_iff [CompleteSpace E] {T : AdjointableMap A E E} :
    0 ≤ T ↔ ∀ x : E, 0 ≤ inner A x (T x) := by
  refine ⟨fun hT x => ?_, fun h => ?_⟩
  · obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
    rw [mul_apply, ← inner_star_left]
    exact CStarModule.inner_self_nonneg
  · have hsa : IsSelfAdjoint T :=
      isSelfAdjoint_iff_forall_isSelfAdjoint.mpr fun x => .of_nonneg (h x)
    refine CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero.mpr ⟨hsa, ?_⟩
    set N := T⁻
    have hN : 0 ≤ N := CFC.negPart_nonneg T
    obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hN
    have hTN : T * N = -(star R * R * N) := by
      conv_lhs => rw [← CFC.posPart_sub_negPart T hsa]
      rw [sub_mul, CFC.posPart_mul_negPart, zero_sub, ← hR]
    have hRN : R * N = 0 := by
      ext x
      have hx := h (N x)
      have heq : inner A (N x) (T (N x)) = -inner A ((R * N) x) ((R * N) x) := by
        rw [← mul_apply, hTN, neg_apply, CStarModule.inner_neg_right, mul_assoc, mul_apply,
          ← inner_star_left, star_star, ← mul_apply]
      rw [heq, Left.nonneg_neg_iff] at hx
      exact CStarModule.inner_self.mp (le_antisymm hx CStarModule.inner_self_nonneg)
    rw [← star_mul_self_eq_zero, hN.isSelfAdjoint.star_eq]
    calc N * N = star R * (R * N) := by rw [← mul_assoc, ← hR]
      _ = 0 := by rw [hRN, mul_zero]

/-- The spectral order on `L_A(E)` is characterized by `S ≤ T ↔ ∀ x, ⟪x, S x⟫_A ≤ ⟪x, T x⟫_A`. -/
theorem le_iff [CompleteSpace E] {S T : AdjointableMap A E E} :
    S ≤ T ↔ ∀ x : E, inner A x (S x) ≤ inner A x (T x) := by
  rw [← sub_nonneg, nonneg_iff]
  simp_rw [sub_apply, CStarModule.inner_sub_right, sub_nonneg]

/-- For any rectangular adjointable operator `T : E → F` with `E` complete, `T* ∘ T` is positive
in `L_A(E)`. -/
@[simp]
theorem adjoint_comp_self_nonneg [CompleteSpace E] (T : AdjointableMap A E F) :
    0 ≤ T.adjoint.comp T :=
  nonneg_iff.mpr fun x => by
    rw [comp_apply, ← T.inner_map_left]
    exact CStarModule.inner_self_nonneg

/-- For any rectangular adjointable operator `T : E → F` with `F` complete, `T ∘ T*` is positive
in `L_A(F)`. -/
@[simp]
theorem self_comp_adjoint_nonneg [CompleteSpace F] (T : AdjointableMap A E F) :
    0 ≤ T.comp T.adjoint := by
  simpa only [adjoint_adjoint] using adjoint_comp_self_nonneg T.adjoint

/-- Conjugating a positive operator in `L_A(F)` by `T : L_A(E, F)` gives a positive operator in
`L_A(E)`. -/
theorem adjoint_comp_nonneg_comp [CompleteSpace E] [CompleteSpace F]
    {S : AdjointableMap A F F} (hS : 0 ≤ S) (T : AdjointableMap A E F) :
    0 ≤ (T.adjoint.comp S).comp T :=
  nonneg_iff.mpr fun x => by
    rw [comp_apply, comp_apply, ← T.inner_map_left]
    exact nonneg_iff.mp hS (T x)

/-- Paschke's operator inequality for adjointable maps: `⟪T x, T x⟫_A ≤ ‖T‖ ^ 2 • ⟪x, x⟫_A` in
`A`. -/
theorem inner_map_self_le [CompleteSpace E] (T : AdjointableMap A E F) (x : E) :
    inner A (T x) (T x) ≤ ‖T‖ ^ 2 • inner A x x := by
  have hbound : T.adjoint.comp T ≤ algebraMap ℝ (AdjointableMap A E E) ‖T.adjoint.comp T‖ :=
    (adjoint_comp_self_nonneg T).isSelfAdjoint.le_algebraMap_norm_self
  have hx := le_iff.mp hbound x
  rwa [comp_apply, ← T.inner_map_left, norm_adjoint_comp_self, Algebra.algebraMap_eq_smul_one,
    ← Complex.coe_smul, smul_apply, one_apply, CStarModule.inner_smul_right_complex,
    Complex.coe_smul] at hx

/-- The modulus `|T| = √(T* ∘ T) ∈ L_A(E)` of an adjointable operator `T : E → F`, defined via
the continuous functional calculus on `L_A(E)`. -/
noncomputable def abs [CompleteSpace E] (T : AdjointableMap A E F) : AdjointableMap A E E :=
  CFC.sqrt (T.adjoint.comp T)

@[simp]
theorem abs_nonneg [CompleteSpace E] (T : AdjointableMap A E F) : 0 ≤ T.abs :=
  CFC.sqrt_nonneg _

theorem isSelfAdjoint_abs [CompleteSpace E] (T : AdjointableMap A E F) : IsSelfAdjoint T.abs :=
  (abs_nonneg T).isSelfAdjoint

@[simp]
theorem abs_mul_abs [CompleteSpace E] (T : AdjointableMap A E F) :
    T.abs * T.abs = T.adjoint.comp T :=
  CFC.sqrt_mul_sqrt_self _ (adjoint_comp_self_nonneg T)

/-- `|T|` preserves all `A`-valued inner products relative to `T`:
`⟪|T| x, |T| y⟫_A = ⟪T x, T y⟫_A`. This is the algebraic starting point for polar decomposition in
Hilbert C⋆-modules. -/
theorem inner_abs_abs [CompleteSpace E] (T : AdjointableMap A E F) (x y : E) :
    inner A (T.abs x) (T.abs y) = inner A (T x) (T y) := by
  rw [T.abs.inner_map_left, isSelfAdjoint_iff'.mp (isSelfAdjoint_abs T), ← mul_apply,
    abs_mul_abs, comp_apply, ← T.inner_map_left]

@[simp]
theorem norm_abs_apply [CompleteSpace E] (T : AdjointableMap A E F) (x : E) :
    ‖T.abs x‖ = ‖T x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A),
    CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (x := T x), inner_abs_abs]

@[simp]
theorem norm_abs [CompleteSpace E] (T : AdjointableMap A E F) : ‖T.abs‖ = ‖T‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self,
    (isSelfAdjoint_abs T).star_eq, abs_mul_abs, norm_adjoint_comp_self]

theorem ker_abs [CompleteSpace E] (T : AdjointableMap A E F) :
    LinearMap.ker (T.abs.toContinuousLinearMap : E →ₗ[ℂ] E) =
      LinearMap.ker (T.toContinuousLinearMap : E →ₗ[ℂ] F) := by
  ext x
  simp [← norm_eq_zero]

end CStar

section RightOrder

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]

/-- Positivity in `L_A(E)` for a right Hilbert `A`-module, in `A`-valued inner-product form. -/
theorem unop_nonneg_iff {T : AdjointableMap Aᵐᵒᵖ E E} :
    0 ≤ T ↔ ∀ x : E, 0 ≤ unop (inner Aᵐᵒᵖ x (T x)) := by
  simp_rw [nonneg_iff, unop_nonneg]

/-- Paschke's operator inequality for right Hilbert `A`-modules:
`⟨T x, T x⟩_A ≤ ‖T‖ ^ 2 • ⟨x, x⟩_A`. -/
theorem unop_inner_map_self_le (T : AdjointableMap Aᵐᵒᵖ E F) (x : E) :
    unop (inner Aᵐᵒᵖ (T x) (T x)) ≤ ‖T‖ ^ 2 • unop (inner Aᵐᵒᵖ x x) :=
  unop_le_unop.mpr (T.inner_map_self_le x)

end RightOrder

end AdjointableMap

end TauCeti

/-! ### Orthogonal projections in `L_A(E)` -/

namespace IsStarProjection

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  {P : TauCeti.AdjointableMap A E E}

theorem inner_map_self_adjointable (hP : IsStarProjection P) (x : E) :
    inner A (P x) (P x) = inner A x (P x) := by
  rw [P.inner_map_left, ← P.star_eq_adjoint, hP.isSelfAdjoint.star_eq,
    ← TauCeti.AdjointableMap.mul_apply, hP.isIdempotentElem.eq]

theorem inner_map_sub_self_adjointable (hP : IsStarProjection P) (x y : E) :
    inner A (P x) (y - P y) = 0 := by
  rw [P.inner_map_left, ← P.star_eq_adjoint, hP.isSelfAdjoint.star_eq, map_sub,
    ← TauCeti.AdjointableMap.mul_apply, hP.isIdempotentElem.eq, sub_self,
    CStarModule.inner_zero_right]

/-- Pythagorean identity for an adjointable orthogonal projection `P ∈ L_A(E)`:
`⟪x, x⟫_A = ⟪P x, P x⟫_A + ⟪x - P x, x - P x⟫_A`. -/
theorem inner_self_eq_add_adjointable (hP : IsStarProjection P) (x : E) :
    inner A x x = inner A (P x) (P x) + inner A (x - P x) (x - P x) := by
  have hdecomp : x = P x + (x - P x) := (add_sub_cancel (P x) x).symm
  conv_lhs => rw [hdecomp]
  have h1 := hP.inner_map_sub_self_adjointable x x
  have h2 : inner A (x - P x) (P x) = 0 := by
    rw [← CStarModule.star_inner, h1, star_zero]
  rw [CStarModule.inner_add_left, CStarModule.inner_add_right, CStarModule.inner_add_right,
    h1, h2, add_zero, zero_add]

theorem isClosed_range_adjointable (hP : IsStarProjection P) :
    IsClosed (Set.range P) :=
  ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (hP.isIdempotentElem.map TauCeti.AdjointableMap.toContinuousLinearMapAlgHom)

end IsStarProjection

namespace TauCeti

/-! ### Module unitaries (`CStarModuleEquiv`) and Lance's characterization -/

/-- A *unitary equivalence* between Hilbert C⋆-modules `E` and `F` over `A` is a `ℂ`-linear
isometric equivalence preserving the `A`-valued inner product. Compatibility with the `A`-action
and existence of an adjoint inverse in `AdjointableMap A F E` follow automatically from
inner-product preservation and surjectivity (`map_smul_coeff`, `toAdjointableMap`). -/
structure CStarModuleEquiv (A E F : Type*) [NonUnitalRing A] [StarRing A] [Module ℂ A]
    [StarModule ℂ A] [PartialOrder A] [Norm A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
    extends E ≃ₗᵢ[ℂ] F where
  /-- A module unitary preserves the `A`-valued inner product. -/
  inner_map (x y : E) : inner A (toLinearIsometryEquiv x) (toLinearIsometryEquiv y) = inner A x y

namespace CStarModuleEquiv

variable {A E F G : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

theorem toLinearIsometryEquiv_injective :
    Function.Injective (toLinearIsometryEquiv : CStarModuleEquiv A E F → E ≃ₗᵢ[ℂ] F) := by
  rintro ⟨e₁, _⟩ ⟨e₂, _⟩ rfl
  rfl

instance instEquivLike : EquivLike (CStarModuleEquiv A E F) E F where
  coe U := U.toLinearIsometryEquiv
  inv U := U.toLinearIsometryEquiv.symm
  left_inv U := U.toLinearIsometryEquiv.left_inv
  right_inv U := U.toLinearIsometryEquiv.right_inv
  coe_injective' _ _ h _ := toLinearIsometryEquiv_injective (DFunLike.coe_injective h)

instance instLinearIsometryEquivClass :
    LinearIsometryEquivClass (CStarModuleEquiv A E F) ℂ E F where
  map_add U := U.toLinearIsometryEquiv.map_add
  map_smulₛₗ U := U.toLinearIsometryEquiv.map_smul
  norm_map U := U.toLinearIsometryEquiv.norm_map

@[simp]
theorem coe_toLinearIsometryEquiv (U : CStarModuleEquiv A E F) :
    ⇑U.toLinearIsometryEquiv = ⇑U := (rfl)

@[simp]
theorem toLinearIsometryEquiv_apply (U : CStarModuleEquiv A E F) (x : E) :
    U.toLinearIsometryEquiv x = U x := (rfl)

@[simp]
theorem mk_apply (e : E ≃ₗᵢ[ℂ] F)
    (h : ∀ x y, inner A (e x) (e y) = inner A x y) (x : E) :
    (⟨e, h⟩ : CStarModuleEquiv A E F) x = e x := (rfl)

@[ext]
theorem ext {U V : CStarModuleEquiv A E F} (h : ∀ x, U x = V x) : U = V :=
  DFunLike.ext U V h

@[simp]
theorem inner_apply (U : CStarModuleEquiv A E F) (x y : E) :
    inner A (U x) (U y) = inner A x y :=
  U.inner_map x y

/-- The identity module unitary on `E`. -/
def refl (A E : Type*) [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
    [PartialOrder A] [Norm A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] :
    CStarModuleEquiv A E E where
  toLinearIsometryEquiv := LinearIsometryEquiv.refl ℂ E
  inner_map _ _ := rfl

@[simp]
theorem refl_apply (x : E) : refl A E x = x := (rfl)

/-- The inverse of a module unitary is a module unitary. -/
def symm (U : CStarModuleEquiv A E F) : CStarModuleEquiv A F E where
  toLinearIsometryEquiv := U.toLinearIsometryEquiv.symm
  inner_map x y := by
    simpa only [toLinearIsometryEquiv_apply, U.toLinearIsometryEquiv.apply_symm_apply] using
      (U.inner_map (U.toLinearIsometryEquiv.symm x) (U.toLinearIsometryEquiv.symm y)).symm

@[simp]
theorem symm_symm (U : CStarModuleEquiv A E F) : U.symm.symm = U := (rfl)

@[simp]
theorem apply_symm_apply (U : CStarModuleEquiv A E F) (y : F) : U (U.symm y) = y :=
  U.toLinearIsometryEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (U : CStarModuleEquiv A E F) (x : E) : U.symm (U x) = x :=
  U.toLinearIsometryEquiv.symm_apply_apply x

/-- Composition of module unitaries. -/
def trans (U : CStarModuleEquiv A E F) (V : CStarModuleEquiv A F G) :
    CStarModuleEquiv A E G where
  toLinearIsometryEquiv := U.toLinearIsometryEquiv.trans V.toLinearIsometryEquiv
  inner_map x y := (V.inner_apply (U x) (U y)).trans (U.inner_apply x y)

@[simp]
theorem trans_apply (U : CStarModuleEquiv A E F) (V : CStarModuleEquiv A F G) (x : E) :
    U.trans V x = V (U x) := (rfl)

@[simp]
theorem symm_trans (U : CStarModuleEquiv A E F) (V : CStarModuleEquiv A F G) :
    (U.trans V).symm = V.symm.trans U.symm := (rfl)

/-- Every module unitary is an adjointable operator whose adjoint is its inverse `U.symm`. -/
def toAdjointableMap (U : CStarModuleEquiv A E F) : AdjointableMap A E F where
  toContinuousLinearMap := U.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
  adjointContinuousLinearMap := U.symm.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
  inner_map_eq' x y := by
    simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      toLinearIsometryEquiv_apply]
    conv_lhs => rw [← U.apply_symm_apply y]
    exact U.inner_apply x (U.symm y)

@[simp]
theorem toAdjointableMap_apply (U : CStarModuleEquiv A E F) (x : E) :
    U.toAdjointableMap x = U x := (rfl)

@[simp]
theorem adjoint_toAdjointableMap (U : CStarModuleEquiv A E F) :
    U.toAdjointableMap.adjoint = U.symm.toAdjointableMap := (rfl)

@[simp]
theorem symm_comp_toAdjointableMap (U : CStarModuleEquiv A E F) :
    U.symm.toAdjointableMap.comp U.toAdjointableMap = AdjointableMap.id A E :=
  AdjointableMap.ext U.symm_apply_apply

@[simp]
theorem toAdjointableMap_comp_symm (U : CStarModuleEquiv A E F) :
    U.toAdjointableMap.comp U.symm.toAdjointableMap = AdjointableMap.id A F :=
  AdjointableMap.ext U.apply_symm_apply

theorem adjoint_toAdjointableMap_comp_self (U : CStarModuleEquiv A E F) :
    U.toAdjointableMap.adjoint.comp U.toAdjointableMap = AdjointableMap.id A E := by
  rw [U.adjoint_toAdjointableMap]
  exact U.symm_comp_toAdjointableMap

theorem toAdjointableMap_comp_adjoint (U : CStarModuleEquiv A E F) :
    U.toAdjointableMap.comp U.toAdjointableMap.adjoint = AdjointableMap.id A F := by
  rw [U.adjoint_toAdjointableMap]
  exact U.toAdjointableMap_comp_symm

/-- Every module unitary automatically commutes with the coefficient `A`-action. -/
@[simp]
theorem map_smul_coeff (U : CStarModuleEquiv A E F) (a : A) (x : E) :
    U (a • x) = a • U x :=
  U.toAdjointableMap.map_smul_coeff a x

/-- Construct a `CStarModuleEquiv` from any plain surjective function preserving the `A`-valued
inner product (Lance, Theorem 3.5). Injectivity, complex linearity, compatibility with the
`A`-action, and isometric continuity all follow automatically, without completeness assumptions. -/
noncomputable def ofSurjectiveInner (f : E → F) (hsurj : Function.Surjective f)
    (hinner : ∀ x y : E, inner A (f x) (f y) = inner A x y) : CStarModuleEquiv A E F := by
  have hinj : Function.Injective f := fun x₁ x₂ hx =>
    CStarModule.ext_inner_right (A := A) fun z => by rw [← hinner x₁ z, hx, hinner x₂ z]
  let e : E ≃ F := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have he (x : E) : e x = f x := rfl
  have hpair : LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := E)).flip
      (CStarModule.innerₛₗ (A := A) (E := F)).flip e e.symm :=
    CStarModule.isAdjointPair_inner_iff.mpr fun x y => by
      conv_lhs => rw [← e.apply_symm_apply y]
      exact hinner x (e.symm y)
  have hnorm (x : E) : ‖hpair.toLinearMapCStarModule x‖ = ‖x‖ := by
    rw [hpair.toLinearMapCStarModule_apply, CStarModule.norm_eq_sqrt_norm_inner_self (A := A),
      CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (x := x), he, hinner x x]
  exact
    { toLinearIsometryEquiv :=
        LinearIsometryEquiv.ofLinearIsometry
          { toLinearMap := hpair.toLinearMapCStarModule
            norm_map' := hnorm }
          hpair.symm_cstarModule.toLinearMapCStarModule
          (LinearMap.ext fun y => by simp [e.apply_symm_apply y])
          (LinearMap.ext fun x => by simp [e.symm_apply_apply x])
      inner_map := fun x y => by simp [he, hinner x y] }

@[simp]
theorem ofSurjectiveInner_apply (f : E → F) (hsurj : Function.Surjective f)
    (hinner : ∀ x y : E, inner A (f x) (f y) = inner A x y) (x : E) :
    ofSurjectiveInner f hsurj hinner x = f x := by
  simp [ofSurjectiveInner]
  rfl

/-- Construct a `CStarModuleEquiv` from an invertible adjointable operator whose inverse is its
adjoint (`T* ∘ T = id_E` and `T ∘ T* = id_F`). -/
def ofAdjointable (T : AdjointableMap A E F)
    (h₁ : T.adjoint.comp T = AdjointableMap.id A E)
    (h₂ : T.comp T.adjoint = AdjointableMap.id A F) : CStarModuleEquiv A E F where
  toLinearIsometryEquiv :=
    LinearIsometryEquiv.ofLinearIsometry
      { toLinearMap := T.toContinuousLinearMap.toLinearMap
        norm_map' := AdjointableMap.norm_map_of_adjoint_comp_self_eq_id h₁ }
      T.adjoint.toContinuousLinearMap.toLinearMap
      (LinearMap.ext fun y => DFunLike.congr_fun h₂ y)
      (LinearMap.ext fun x => DFunLike.congr_fun h₁ x)
  inner_map x y := AdjointableMap.adjoint_comp_self_eq_id_iff.mp h₁ x y

@[simp]
theorem ofAdjointable_apply (T : AdjointableMap A E F)
    (h₁ : T.adjoint.comp T = AdjointableMap.id A E)
    (h₂ : T.comp T.adjoint = AdjointableMap.id A F) (x : E) :
    ofAdjointable T h₁ h₂ x = T x := (rfl)

@[simp]
theorem toAdjointableMap_ofAdjointable (T : AdjointableMap A E F)
    (h₁ : T.adjoint.comp T = AdjointableMap.id A E)
    (h₂ : T.comp T.adjoint = AdjointableMap.id A F) :
    (ofAdjointable T h₁ h₂).toAdjointableMap = T :=
  AdjointableMap.ext fun _ => rfl

@[simp]
theorem ofAdjointable_toAdjointableMap (U : CStarModuleEquiv A E F) :
    ofAdjointable U.toAdjointableMap U.adjoint_toAdjointableMap_comp_self
      U.toAdjointableMap_comp_adjoint = U :=
  ext fun _ => rfl

instance instMul : Mul (CStarModuleEquiv A E E) := ⟨fun U V => V.trans U⟩
instance instOne : One (CStarModuleEquiv A E E) := ⟨refl A E⟩
instance instInv : Inv (CStarModuleEquiv A E E) := ⟨symm⟩

@[simp] theorem mul_apply (U V : CStarModuleEquiv A E E) (x : E) : (U * V) x = U (V x) := (rfl)
@[simp] theorem one_apply (x : E) : (1 : CStarModuleEquiv A E E) x = x := (rfl)
@[simp] theorem inv_apply (U : CStarModuleEquiv A E E) (x : E) : U⁻¹ x = U.symm x := (rfl)

instance instGroup : Group (CStarModuleEquiv A E E) where
  mul_assoc _ _ _ := ext fun x => by simp
  one_mul _ := ext fun x => by simp
  mul_one _ := ext fun x => by simp
  inv_mul_cancel _ := ext fun x => by simp

/-- Endomorphism module unitaries `CStarModuleEquiv A E E` are canonically isomorphic as a group
to `unitary (AdjointableMap A E E)`. -/
def toUnitary : CStarModuleEquiv A E E ≃* unitary (AdjointableMap A E E) where
  toFun U := ⟨U.toAdjointableMap, Unitary.mem_iff.mpr
    ⟨by rw [AdjointableMap.star_eq_adjoint, AdjointableMap.mul_def, AdjointableMap.one_def]
        exact U.adjoint_toAdjointableMap_comp_self,
     by rw [AdjointableMap.star_eq_adjoint, AdjointableMap.mul_def, AdjointableMap.one_def]
        exact U.toAdjointableMap_comp_adjoint⟩⟩
  invFun u := ofAdjointable u.1
    (by simpa only [Unitary.coe_star, AdjointableMap.star_eq_adjoint, AdjointableMap.mul_def,
          AdjointableMap.one_def] using Unitary.coe_star_mul_self u)
    (by simpa only [Unitary.coe_star, AdjointableMap.star_eq_adjoint, AdjointableMap.mul_def,
          AdjointableMap.one_def] using Unitary.coe_mul_star_self u)
  left_inv _ := ext fun _ => rfl
  right_inv _ := Subtype.ext (AdjointableMap.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (AdjointableMap.ext fun _ => rfl)

@[simp]
theorem coe_toUnitary (U : CStarModuleEquiv A E E) :
    (U.toUnitary : AdjointableMap A E E) = U.toAdjointableMap := (rfl)

@[simp]
theorem toUnitary_symm_apply (u : unitary (AdjointableMap A E E)) (x : E) :
    toUnitary.symm u x = (u : AdjointableMap A E E) x := (rfl)

end CStarModuleEquiv

namespace AdjointableMap

section UnitaryCharacterization

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- Lance's unitary characterization (Theorem 3.5) for adjointable operators: `T : L_A(E, F)` is
invertible with inverse `T*` if and only if `T` is surjective and preserves the `A`-valued inner
product. -/
theorem adjoint_comp_self_and_self_comp_adjoint_iff {T : AdjointableMap A E F} :
    T.adjoint.comp T = AdjointableMap.id A E ∧ T.comp T.adjoint = AdjointableMap.id A F ↔
      Function.Surjective T ∧ ∀ x y : E, inner A (T x) (T y) = inner A x y := by
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨fun y => ⟨T.adjoint y, DFunLike.congr_fun h₂ y⟩,
    adjoint_comp_self_eq_id_iff.mp h₁⟩, fun ⟨hsurj, hinner⟩ => ?_⟩
  let U := CStarModuleEquiv.ofSurjectiveInner T hsurj hinner
  have hTU : T = U.toAdjointableMap := ext fun x => by simp [U]
  rw [hTU]
  exact ⟨U.adjoint_toAdjointableMap_comp_self, U.toAdjointableMap_comp_adjoint⟩

/-- Lance's unitary characterization (Theorem 3.5) starting from a plain function `f : E → F`:
`f` is the underlying map of an invertible adjointable operator whose inverse is its adjoint if
and only if `f` is surjective and preserves the `A`-valued inner product. -/
theorem exists_adjoint_comp_eq_id_iff {f : E → F} :
    (∃ T : AdjointableMap A E F,
      ⇑T = f ∧ T.adjoint.comp T = AdjointableMap.id A E ∧
        T.comp T.adjoint = AdjointableMap.id A F) ↔
      Function.Surjective f ∧ ∀ x y : E, inner A (f x) (f y) = inner A x y := by
  refine ⟨?_, fun ⟨hsurj, hinner⟩ => ?_⟩
  · rintro ⟨T, rfl, h₁, h₂⟩
    exact adjoint_comp_self_and_self_comp_adjoint_iff.mp ⟨h₁, h₂⟩
  · let U := CStarModuleEquiv.ofSurjectiveInner f hsurj hinner
    exact ⟨U.toAdjointableMap, funext fun x => by simp [U],
      U.adjoint_toAdjointableMap_comp_self, U.toAdjointableMap_comp_adjoint⟩

/-- In `L_A(E)`, an operator belongs to `unitary L_A(E)` if and only if it is surjective and
preserves the `A`-valued inner product. -/
theorem mem_unitary_iff {T : AdjointableMap A E E} :
    T ∈ unitary (AdjointableMap A E E) ↔
      Function.Surjective T ∧ ∀ x y : E, inner A (T x) (T y) = inner A x y := by
  rw [Unitary.mem_iff, star_eq_adjoint, mul_def, mul_def, one_def]
  exact adjoint_comp_self_and_self_comp_adjoint_iff (A := A)

end UnitaryCharacterization

/-! ### Scalar Hilbert-space comparison (`A = ℂ`) -/

section ComplexHilbertSpace

open ComplexOrder

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- On complex Hilbert spaces (viewed as `CStarModule ℂ` via
`WithCStarModule.instCStarModuleComplex`), every continuous linear map is adjointable, giving an
isometric `ℂ`-linear equivalence `L_ℂ(H, F) ≃ₗᵢ[ℂ] (H →L[ℂ] F)`. -/
noncomputable def equivContinuousLinearMapComplex :
    AdjointableMap ℂ H F ≃ₗᵢ[ℂ] (H →L[ℂ] F) :=
  LinearIsometryEquiv.ofLinearIsometry
    toContinuousLinearMapLI
    { toFun := fun f =>
        ⟨f, ContinuousLinearMap.adjoint f,
          fun x y => (ContinuousLinearMap.adjoint_inner_right f x y).symm⟩
      map_add' := fun _ _ => ext fun _ => rfl
      map_smul' := fun _ _ => ext fun _ => rfl }
    (LinearMap.ext fun _ => rfl)
    (LinearMap.ext fun _ => ext fun _ => rfl)

@[simp]
theorem equivContinuousLinearMapComplex_apply (T : AdjointableMap ℂ H F) :
    equivContinuousLinearMapComplex T = T.toContinuousLinearMap := (rfl)

@[simp]
theorem equivContinuousLinearMapComplex_symm_apply (f : H →L[ℂ] F) (x : H) :
    equivContinuousLinearMapComplex.symm f x = f x := (rfl)

@[simp]
theorem adjoint_equivContinuousLinearMapComplex_symm (f : H →L[ℂ] F) :
    (equivContinuousLinearMapComplex.symm f).adjoint =
      equivContinuousLinearMapComplex.symm (ContinuousLinearMap.adjoint f) :=
  ext fun _ => rfl

/-- For a complex Hilbert space `H`, `L_ℂ(H)` is isometrically `⋆`-isomorphic to `H →L[ℂ] H`.
Being a `⋆`-isomorphism between C⋆-algebras, this automatically preserves positivity and the
continuous functional calculus. -/
noncomputable def starAlgEquivContinuousLinearMapComplex :
    AdjointableMap ℂ H H ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
  StarAlgEquiv.ofAlgEquiv
    (AlgEquiv.ofLinearEquiv equivContinuousLinearMapComplex.toLinearEquiv
      (toContinuousLinearMap_one (A := ℂ)) (toContinuousLinearMap_mul (A := ℂ)))
    fun T => ContinuousLinearMap.ext fun y => CStarModule.ext_inner_left (A := ℂ) fun x => by
      simp only [star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint]
      exact (T.inner_map_left x y).symm.trans
        (ContinuousLinearMap.adjoint_inner_right T.toContinuousLinearMap x y).symm

@[simp]
theorem starAlgEquivContinuousLinearMapComplex_apply (T : AdjointableMap ℂ H H) :
    starAlgEquivContinuousLinearMapComplex T = T.toContinuousLinearMap := (rfl)

@[simp]
theorem starAlgEquivContinuousLinearMapComplex_symm_apply (f : H →L[ℂ] H) (x : H) :
    starAlgEquivContinuousLinearMapComplex.symm f x = f x := (rfl)

end ComplexHilbertSpace

/-! ### Counterexample: a bounded module map need not be adjointable -/

section Counterexample

open unitInterval

private noncomputable instance : PartialOrder C(I, ℂ) :=
  CStarAlgebra.spectralOrder C(I, ℂ)

private instance : StarOrderedRing C(I, ℂ) :=
  CStarAlgebra.spectralOrderedRing C(I, ℂ)

private noncomputable abbrev zeroAtZeroSubmodule : Submodule ℂ C(I, ℂ) :=
  LinearMap.ker (ContinuousMap.evalCLM ℂ (0 : I)).toLinearMap

private instance : CompleteSpace zeroAtZeroSubmodule :=
  (ContinuousMap.evalCLM ℂ (0 : I)).isClosed_ker.completeSpace_coe

private noncomputable instance : SMul C(I, ℂ)ᵐᵒᵖ zeroAtZeroSubmodule where
  smul a f := ⟨op (unop a) • f.1, by
    have hf : f.1 0 = 0 := f.2
    simp [LinearMap.mem_ker, MulOpposite.smul_eq_mul_unop, hf]⟩

private noncomputable instance : CStarModule C(I, ℂ)ᵐᵒᵖ zeroAtZeroSubmodule where
  inner f g := inner C(I, ℂ)ᵐᵒᵖ f.1 g.1
  inner_add_right {x _ _} := CStarModule.inner_add_right (A := C(I, ℂ)ᵐᵒᵖ) (x := x.1)
  inner_self_nonneg {x} := CStarModule.inner_self_nonneg (A := C(I, ℂ)ᵐᵒᵖ) (x := x.1)
  inner_self {x} :=
    (CStarModule.inner_self (A := C(I, ℂ)ᵐᵒᵖ) (x := x.1)).trans Submodule.coe_eq_zero
  inner_op_smul_right {a x y} :=
    CStarModule.inner_op_smul_right (A := C(I, ℂ)ᵐᵒᵖ) (a := a) (x := x.1) (y := y.1)
  inner_smul_right_complex {z x y} :=
    CStarModule.inner_smul_right_complex (A := C(I, ℂ)ᵐᵒᵖ) (z := z) (x := x.1) (y := y.1)
  star_inner x y := CStarModule.star_inner (A := C(I, ℂ)ᵐᵒᵖ) x.1 y.1
  norm_eq_sqrt_norm_inner_self {x} :=
    CStarModule.norm_eq_sqrt_norm_inner_self (A := C(I, ℂ)ᵐᵒᵖ) x.1

private lemma zeroAtZeroSubmodule_inner (f g : zeroAtZeroSubmodule) :
    inner C(I, ℂ)ᵐᵒᵖ f g = inner C(I, ℂ)ᵐᵒᵖ f.1 g.1 := rfl

private lemma zero_mem_closure_pos_unitInterval :
    (0 : I) ∈ closure {t : I | (0 : ℝ) < (t : ℝ)} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hpos : 0 < min (ε / 2) 1 := lt_min (half_pos hε) one_pos
  have hz : ((0 : I) : ℝ) = 0 := rfl
  refine ⟨⟨min (ε / 2) 1, Set.mem_Icc.mpr ⟨hpos.le, min_le_right _ _⟩⟩, hpos, ?_⟩
  simp only [Subtype.dist_eq, hz, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hpos]
  exact (min_le_left _ _).trans_lt (half_lt_self hε)

/-- In `A = C([0, 1], ℂ)` viewed as a right Hilbert `A`-module over itself, the closed right ideal
`J = {f ∈ A | f 0 = 0}` is a complete right Hilbert `A`-module whose isometric `A`-linear inclusion
`J →L[ℂ] A` has no adjoint: any adjoint `S : A → J` would satisfy `t · (S 1 t) = t` for all
`t ∈ [0, 1]`, forcing `S 1 = 1` by continuity and contradicting `(S 1) 0 = 0`. -/
theorem exists_continuousLinearMap_smul_not_adjointable :
    ∃ (A E F : Type) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
      (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E) (_ : CompleteSpace E)
      (_ : SMul Aᵐᵒᵖ E) (_ : CStarModule Aᵐᵒᵖ E)
      (_ : NormedAddCommGroup F) (_ : NormedSpace ℂ F) (_ : CompleteSpace F)
      (_ : SMul Aᵐᵒᵖ F) (_ : CStarModule Aᵐᵒᵖ F)
      (T : E →L[ℂ] F),
      (∀ (a : A) (x : E), T (op a • x) = op a • T x) ∧
      ¬∃ T' : AdjointableMap Aᵐᵒᵖ E F, ⇑T' = ⇑T := by
  refine ⟨C(I, ℂ), zeroAtZeroSubmodule, C(I, ℂ), inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    zeroAtZeroSubmodule.subtypeL, fun _ _ => rfl, ?_⟩
  rintro ⟨T', hT'⟩
  let coord : zeroAtZeroSubmodule :=
    ⟨⟨fun t : I => ((t : ℝ) : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩,
      by simp [LinearMap.mem_ker]⟩
  let s1 : zeroAtZeroSubmodule := T'.adjoint 1
  have hid : unop (inner C(I, ℂ)ᵐᵒᵖ (T' coord) (1 : C(I, ℂ))) =
      unop (inner C(I, ℂ)ᵐᵒᵖ coord s1) :=
    T'.unop_inner_map_left coord 1
  rw [congrFun hT' coord] at hid
  have hs1_pos : ∀ t : I, (0 : ℝ) < (t : ℝ) → s1.1 t = 1 := fun t ht => by
    have hval := DFunLike.congr_fun hid t
    simp only [zeroAtZeroSubmodule_inner, CStarModule.unop_inner_mulOpposite,
      Submodule.coe_subtypeL, Submodule.subtype_apply, ContinuousMap.mul_apply,
      ContinuousMap.star_apply, ContinuousMap.one_apply, ContinuousMap.coe_mk, coord] at hval
    have hne : star (((t : ℝ) : ℂ)) ≠ 0 := star_ne_zero.mpr (Complex.ofReal_ne_zero.mpr ht.ne')
    exact (mul_right_inj' hne).mp hval.symm
  have hclosed : IsClosed {t : I | s1.1 t = 1} := isClosed_eq s1.1.continuous continuous_const
  have hs1_zero_one : s1.1 0 = 1 :=
    hclosed.closure_subset_iff.mpr (fun t ht => hs1_pos t ht) zero_mem_closure_pos_unitInterval
  have hs1_zero : s1.1 0 = 0 := s1.2
  exact one_ne_zero (hs1_zero_one.symm.trans hs1_zero)

end Counterexample

end AdjointableMap

end TauCeti
