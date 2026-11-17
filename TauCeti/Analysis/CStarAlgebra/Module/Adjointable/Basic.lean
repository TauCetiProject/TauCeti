/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
# Adjointable operators on Hilbert C⋆-modules

For Hilbert C⋆-modules `E` and `F` over `A`, a continuous complex-linear map `T : E →L[ℂ] F` is
*adjointable* if there exists `T* : F →L[ℂ] E` satisfying `⟪T x, y⟫_A = ⟪x, T* y⟫_A` for all
`x ∈ E` and `y ∈ F`. On complete modules, the adjoint identity for plain functions already forces
complex linearity, compatibility with the `A`-action, and continuity
(`LinearMap.IsAdjointPair.continuous_cstarModule`).

This file bundles adjointable operators as `TauCeti.AdjointableMap A E F` (`L_A(E, F)`), equips
them with the operator norm and completeness when `E` and `F` are complete, and equips the
endomorphism algebra `TauCeti.AdjointableMap A E E` (`L_A(E)`) with its unital C⋆-algebra
structure, spectral order, natural left action on `E`, adjointable isometries, and orthogonal
projections. Right Hilbert `B`-modules are covered throughout by instantiating the coefficient
algebra with `Bᵐᵒᵖ`.

## Main declarations

* `TauCeti.AdjointableMap`: the space `L_A(E, F)` of adjointable operators between Hilbert
  C⋆-modules, with operator norm, isometric forgetful map `toContinuousLinearMapLI`,
  conjugate-linear isometric adjoint `adjointLI`, and completeness when `E` and `F` are complete.
* `TauCeti.AdjointableMap.ofAdjointPair`, `TauCeti.AdjointableMap.ofExistsAdjoint`: constructors
  on complete modules from plain functions satisfying the adjoint identity.
* `TauCeti.AdjointableMap.instCStarAlgebra`: `L_A(E)` is a unital C⋆-algebra when `E` is complete
  (allowing the zero module), ordered by `CStarAlgebra.spectralOrder`.
* `TauCeti.AdjointableMap.applyModule`: the natural left `L_A(E)`-module action on `E`, commuting
  with complex scalars and the coefficient `A`-action.
* `TauCeti.AdjointableMap.adjoint_comp_self_eq_id_iff`,
  `TauCeti.AdjointableMap.isStarProjection_comp_adjoint`,
  `IsStarProjection.inner_self_eq_add_adjointable`, `IsStarProjection.isClosed_range_adjointable`:
  adjointable isometries and orthogonal projections.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1 and 3.
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
theorem toContinuousLinearMap_sum {ι : Type*} (s : Finset ι) (T : ι → AdjointableMap A E F) :
    (∑ i ∈ s, T i).toContinuousLinearMap = ∑ i ∈ s, (T i).toContinuousLinearMap :=
  map_sum toContinuousLinearMapLinear T s

@[simp]
theorem sum_apply {ι : Type*} (s : Finset ι) (T : ι → AdjointableMap A E F) (x : E) :
    (∑ i ∈ s, T i) x = ∑ i ∈ s, T i x :=
  map_sum (AddMonoidHom.mk' (fun S : AdjointableMap A E F => S x) fun _ _ => rfl) T s

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

@[simp]
theorem adjoint_sum {ι : Type*} (s : Finset ι) (T : ι → AdjointableMap A E F) :
    (∑ i ∈ s, T i).adjoint = ∑ i ∈ s, (T i).adjoint :=
  map_sum adjointLinearEquiv T s

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

/-- Over `ℂ`, an adjointable endomorphism vanishes if and only if all of its diagonal inner
products `⟪x, T x⟫_A` vanish. -/
theorem inner_map_self_eq_zero {T : AdjointableMap A E E} :
    (∀ x, inner A x (T x) = 0) ↔ T = 0 := by
  refine ⟨fun h => ext fun y => CStarModule.ext_inner_left (A := A) fun x => ?_, ?_⟩
  · have hpol : inner A x (T y) = (4 : ℂ)⁻¹ • (
        inner A (x + y) (T (x + y)) - inner A (x - y) (T (x - y)) -
        I • inner A (x + I • y) (T (x + I • y)) +
        I • inner A (x - I • y) (T (x - I • y))) := by
      simp only [map_add, map_sub, map_smul, CStarModule.inner_add_left,
        CStarModule.inner_add_right, CStarModule.inner_sub_left, CStarModule.inner_sub_right,
        CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex,
        Complex.star_def, conj_I, smul_add, smul_sub, smul_neg, smul_smul, neg_smul, I_mul_I]
      module
    rw [hpol, h, h, h, h]
    simp
  · rintro rfl x
    simp

/-- Over `ℂ`, an adjointable operator is self-adjoint if and only if all of its diagonal inner
products `⟪x, T x⟫_A` are self-adjoint. -/
theorem isSelfAdjoint_iff_forall_isSelfAdjoint {T : AdjointableMap A E E} :
    IsSelfAdjoint T ↔ ∀ x, IsSelfAdjoint (inner A x (T x)) := by
  rw [IsSelfAdjoint, ← sub_eq_zero, ← inner_map_self_eq_zero]
  refine forall_congr' fun x => ?_
  rw [sub_apply, CStarModule.inner_sub_right, sub_eq_zero, inner_star_right,
    ← CStarModule.star_inner, IsSelfAdjoint]

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

/-- An adjointable operator `V : E → F` satisfies `V* ∘ V = id_E` if and only if it preserves
diagonal inner products `⟪x, x⟫_A`. -/
theorem adjoint_comp_self_eq_id_iff_self {V : AdjointableMap A E F} :
    V.adjoint.comp V = AdjointableMap.id A E ↔ ∀ x : E, inner A (V x) (V x) = inner A x x := by
  rw [adjoint_comp_self_eq_id_iff]
  refine ⟨fun h x => h x x, fun h x y => ?_⟩
  rw [CStarModule.inner_polarization (V x) (V y), CStarModule.inner_polarization x y]
  simp only [← map_add, ← map_sub, ← map_smul, h]

/-- An adjointable isometry preserves norms. -/
theorem norm_map_of_adjoint_comp_self_eq_id {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = AdjointableMap.id A E) (x : E) : ‖V x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A),
    CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (x := x),
    adjoint_comp_self_eq_id_iff.mp hV x x]

/-- An adjointable operator satisfying `V* ∘ V = id_E` is an `Isometry`. -/
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

/-! ### Completeness and C⋆-algebra structure -/

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
adjoint identity; continuity and linearity are supplied automatically. -/
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

/-- The space `L_A(E, F)` of adjointable operators between complete Hilbert C⋆-modules is
complete. -/
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

end CStar

end AdjointableMap

end TauCeti

/-! ### Orthogonal projections in `L_A(E)` -/

namespace IsStarProjection

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  {P : TauCeti.AdjointableMap A E E}

/-- For an adjointable orthogonal projection `P`, `⟪P x, P x⟫_A = ⟪x, P x⟫_A`. -/
theorem inner_map_self_adjointable (hP : IsStarProjection P) (x : E) :
    inner A (P x) (P x) = inner A x (P x) := by
  rw [P.inner_map_left, ← P.star_eq_adjoint, hP.isSelfAdjoint.star_eq,
    ← TauCeti.AdjointableMap.mul_apply, hP.isIdempotentElem.eq]

/-- The range and complementary subspace `(1 - P) E` of an adjointable orthogonal projection are
orthogonal in the `A`-valued inner product. -/
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

/-- The range of an adjointable orthogonal projection is closed. -/
theorem isClosed_range_adjointable (hP : IsStarProjection P) :
    IsClosed (Set.range P) :=
  ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (hP.isIdempotentElem.map TauCeti.AdjointableMap.toContinuousLinearMapAlgHom)

end IsStarProjection
