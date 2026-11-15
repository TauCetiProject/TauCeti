/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Projection
public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair

/-!
# Adjointable operators on Hilbert C⋆-modules

For Hilbert C⋆-modules `E` and `F` over a C⋆-algebra `A` (with right Hilbert `B`-modules
represented as `CStarModule Bᵐᵒᵖ E` and `CStarModule Bᵐᵒᵖ F`), a bounded `ℂ`-linear map
`T : E →L[ℂ] F` is *adjointable* if there exists `T* : F →L[ℂ] E` such that
`⟪T x, y⟫_A = ⟪x, T* y⟫_A` for all `x : E` and `y : F`. Unlike on Hilbert spaces, bounded
`A`-linear maps between Hilbert C⋆-modules need not admit an adjoint; on the other hand, between
complete modules any plain function `T : E → F` admitting a plain function `S : F → E` satisfying
`⟪T x, y⟫_A = ⟪x, S y⟫_A` is automatically `ℂ`-linear, `A`-linear, and bounded
(`AdjointableMap.ofAdjointPair`).

This file bundles adjointable operators as `TauCeti.AdjointableMap A E F` and develops their
algebraic, norm, order, and spectral interface:

* Because `CStarModule` inner products separate points, the adjoint is uniquely determined by the
  forward map, so `AdjointableMap A E F` is extensional on vector evaluation (`AdjointableMap.ext`).
* The forgetful map `AdjointableMap A E F →ₗᵢ[ℂ] (E →L[ℂ] F)` is a linear isometry, and on
  endomorphisms `AdjointableMap A E E →ₐ[ℂ] (E →L[ℂ] E)` is an isometric unital algebra
  homomorphism.
* Taking adjoints defines a conjugate-linear isometric equivalence
  `AdjointableMap.adjointₗᵢ : AdjointableMap A E F ≃ₗᵢ⋆[ℂ] AdjointableMap A F E` satisfying
  `(S.comp T).adjoint = T.adjoint.comp S.adjoint`, `‖T.adjoint‖ = ‖T‖`, and the C⋆-identity
  `‖T.adjoint.comp T‖ = ‖T‖ ^ 2`.
* When `E` and `F` are complete, `AdjointableMap A E F` is a Banach space, and
  `AdjointableMap A E E` is a unital C⋆-algebra (with the zero module allowed), equipped with its
  canonical spectral order `PartialOrder` and `StarOrderedRing` instances, continuous functional
  calculus, positive square roots, and tautological left module action on `E` commuting with `A`.
* Positivity in the C⋆-algebra `AdjointableMap A E E` is characterized by the module inner product:
  `0 ≤ T ↔ ∀ x, 0 ≤ ⟪x, T x⟫_A` (`AdjointableMap.nonneg_iff`). Every `T : AdjointableMap A E F` has
  a positive modulus `T.abs = CFC.sqrt (T.adjoint.comp T)` satisfying
  `⟪T.abs x, T.abs y⟫_A = ⟪T x, T y⟫_A`, `‖T.abs x‖ = ‖T x‖`, and `‖T.abs‖ = ‖T‖`.
* Adjointable orthogonal projections (`IsStarProjection P`) are characterized by
  `⟪P x, y⟫_A = ⟪P x, P y⟫_A`, decompose inner products orthogonally as
  `⟪P x, P x⟫_A + ⟪(1 - P) x, (1 - P) x⟫_A = ⟪x, x⟫_A`, are uniquely determined by their range, and
  have their spectral order characterized by range inclusion.
* Adjointable isometries (`T.adjoint.comp T = .id`) are characterized by preserving module inner
  products (`⟪T x, T y⟫_A = ⟪x, y⟫_A`), equivalently diagonal inner products
  `⟪T x, T x⟫_A = ⟪x, x⟫_A`.

## Main declarations

* `CStarModule.IsAdjointable`: predicate that a function `T : E → F` admits an adjoint function for
  the `A`-valued inner product.
* `TauCeti.AdjointableMap`: the space `L_A(E, F)` of adjointable operators between Hilbert
  C⋆-modules, and the unital C⋆-algebra `L_A(E) = AdjointableMap A E E`.
* `TauCeti.AdjointableMap.ofAdjointPair`, `TauCeti.AdjointableMap.exists_coe_eq_iff`: construction
  of an adjointable operator from plain functions on complete modules, and equivalence with
  `CStarModule.IsAdjointable`.
* `TauCeti.AdjointableMap.nonneg_iff`, `TauCeti.AdjointableMap.isSelfAdjoint_iff`: module
  inner-product characterizations of positivity and self-adjointness in `AdjointableMap A E E`.
* `TauCeti.AdjointableMap.abs`: the modulus `|T| = √(T* T) ∈ AdjointableMap A E E` of a rectangular
  adjointable operator `T : AdjointableMap A E F`.
* `TauCeti.AdjointableMap.isStarProjection_iff_forall_inner`,
  `TauCeti.AdjointableMap.eq_of_isStarProjection_of_range_eq`: characterization and range
  uniqueness of adjointable orthogonal projections.
* `TauCeti.AdjointableMap.adjoint_comp_self_eq_id_iff`: characterization of adjointable isometries.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1, 3, 4.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2 (Definitions 2.16–2.17, Lemma 2.18, Proposition 2.21).
* Bruce Blackadar, *Operator Algebras*, Section II.7.1.
* The bundled C⋆-algebra and completeness setup parallels `DoubleCentralizer` in
  `Mathlib.Analysis.CStarAlgebra.Multiplier`, using the closed-graph and norm estimates from
  `TauCeti.Analysis.CStarAlgebra.Module.AdjointPair`.
-/

public section

open CStarModule MulOpposite Complex

/-! ### The adjointability predicate on functions -/

namespace CStarModule

/-- A plain function `T : E → F` between `A`-inner-product spaces is *adjointable* if there exists a
plain function `S : F → E` satisfying `⟪T x, y⟫_A = ⟪x, S y⟫_A` for all `x` and `y`. On complete
Hilbert C⋆-modules, this forces both `T` and `S` to be bounded `ℂ`-linear `A`-module maps. -/
def IsAdjointable (A : Type*) {E F : Type*} [Inner A E] [Inner A F] (T : E → F) : Prop :=
  ∃ S : F → E, ∀ x y, inner A (T x) y = inner A x (S y)

section Inner

variable {A E F G : Type*}

theorem isAdjointable_def [Inner A E] [Inner A F] {T : E → F} :
    IsAdjointable A T ↔ ∃ S : F → E, ∀ x y, inner A (T x) y = inner A x (S y) :=
  Iff.rfl

@[simp]
theorem isAdjointable_id [Inner A E] : IsAdjointable A (id : E → E) :=
  ⟨id, fun _ _ => rfl⟩

theorem IsAdjointable.comp [Inner A E] [Inner A F] [Inner A G] {S : F → G} {T : E → F}
    (hS : IsAdjointable A S) (hT : IsAdjointable A T) :
    IsAdjointable A (S ∘ T) := by
  rcases hS with ⟨S', hS'⟩
  rcases hT with ⟨T', hT'⟩
  exact ⟨T' ∘ S', fun x z => (hS' (T x) z).trans (hT' x (S' z))⟩

end Inner

section Basic

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]

@[simp]
theorem isAdjointable_zero : IsAdjointable A (0 : E → F) := by
  refine ⟨0, fun x y => ?_⟩
  have h₁ : inner A (0 : F) y = 0 := by
    simpa using CStarModule.inner_add_left (A := A) (x := (0 : F)) (y := 0) (z := y)
  have h₂ : inner A x (0 : E) = 0 := by
    simpa using CStarModule.inner_add_right (A := A) (x := x) (y := (0 : E)) (z := 0)
  simpa only [Pi.zero_apply] using h₁.trans h₂.symm

theorem IsAdjointable.add {T₁ T₂ : E → F} (h₁ : IsAdjointable A T₁) (h₂ : IsAdjointable A T₂) :
    IsAdjointable A (T₁ + T₂) := by
  rcases h₁ with ⟨S₁, h₁⟩
  rcases h₂ with ⟨S₂, h₂⟩
  exact ⟨S₁ + S₂, fun x y => by simp [h₁ x y, h₂ x y]⟩

theorem IsAdjointable.neg {T : E → F} (h : IsAdjointable A T) : IsAdjointable A (-T) := by
  rcases h with ⟨S, h⟩
  refine ⟨-S, fun x y => add_right_cancel (b := inner A (T x) y) ?_⟩
  have h₁ := CStarModule.inner_add_left (A := A) (x := -T x) (y := T x) (z := y)
  have h₂ := CStarModule.inner_add_right (A := A) (x := x) (y := -S y) (z := S y)
  have h₀ : inner A (0 : F) y = inner A x (0 : E) := by
    obtain ⟨h₀₁, h₀₂⟩ : inner A (0 : F) y = 0 ∧ inner A x (0 : E) = 0 :=
      ⟨by simpa using CStarModule.inner_add_left (A := A) (x := (0 : F)) (y := 0) (z := y),
       by simpa using CStarModule.inner_add_right (A := A) (x := x) (y := (0 : E)) (z := 0)⟩
    exact h₀₁.trans h₀₂.symm
  simp only [neg_add_cancel] at h₁ h₂
  simpa only [Pi.neg_apply, ← h x y] using h₁.symm.trans (h₀.trans h₂)

theorem IsAdjointable.sub {T₁ T₂ : E → F} (h₁ : IsAdjointable A T₁) (h₂ : IsAdjointable A T₂) :
    IsAdjointable A (T₁ - T₂) := by
  rw [sub_eq_add_neg]
  exact h₁.add h₂.neg

theorem IsAdjointable.map_add {T : E → F} (h : IsAdjointable A T) (x y : E) :
    T (x + y) = T x + T y := by
  rcases h with ⟨S, h⟩
  have hsub (z : F) : inner A (T (x + y) - (T x + T y)) z = 0 := by
    have hadd := CStarModule.inner_add_left (A := A)
      (x := T (x + y) - (T x + T y)) (y := T x + T y) (z := z)
    rw [sub_add_cancel, h (x + y) z, CStarModule.inner_add_left, ← h x z, ← h y z,
      ← CStarModule.inner_add_left] at hadd
    exact add_right_cancel (hadd.symm.trans (zero_add _).symm)
  exact sub_eq_zero.mp ((CStarModule.inner_self (A := A)).mp (hsub _))

theorem IsAdjointable.map_smul {T : E → F} (h : IsAdjointable A T) (c : ℂ) (x : E) :
    T (c • x) = c • T x := by
  rcases h with ⟨S, h⟩
  have hsub (z : F) : inner A z (T (c • x) - c • T x) = 0 := by
    have hadd := CStarModule.inner_add_right (A := A)
      (x := z) (y := T (c • x) - c • T x) (z := c • T x)
    have heq : inner A z (T (c • x)) = inner A z (c • T x) := by
      rw [← CStarModule.star_inner, h (c • x) z, CStarModule.star_inner,
        CStarModule.inner_smul_right_complex, ← CStarModule.star_inner x (S z), ← h x z,
        CStarModule.star_inner, ← CStarModule.inner_smul_right_complex]
    rw [sub_add_cancel, heq] at hadd
    exact add_right_cancel (hadd.symm.trans (zero_add _).symm)
  exact sub_eq_zero.mp ((CStarModule.inner_self (A := A)).mp (hsub _))

theorem IsAdjointable.map_smul_coeff {T : E → F} (h : IsAdjointable A T) (a : A) (x : E) :
    T (a • x) = a • T x := by
  rcases h with ⟨S, h⟩
  have hsub (z : F) : inner A (T (a • x) - a • T x) z = 0 := by
    have hadd := CStarModule.inner_add_left (A := A)
      (x := T (a • x) - a • T x) (y := a • T x) (z := z)
    rw [sub_add_cancel, h (a • x) z, CStarModule.inner_op_smul_left,
      CStarModule.inner_op_smul_left, ← h x z] at hadd
    exact add_right_cancel (hadd.symm.trans (zero_add _).symm)
  exact sub_eq_zero.mp ((CStarModule.inner_self (A := A)).mp (hsub _))

end Basic

section StarModule

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]

theorem isAdjointable_iff_exists_isAdjointPair {T : E → F} :
    IsAdjointable A T ↔
      ∃ S : F → E, LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
        (innerₛₗ (A := A) (E := F)).flip T S := by
  simp_rw [isAdjointPair_inner_iff, IsAdjointable]

theorem IsAdjointable.smul {T : E → F} (c : ℂ) (h : IsAdjointable A T) :
    IsAdjointable A (c • T) := by
  rcases h with ⟨S, h⟩
  exact ⟨star c • S, fun x y => by simp [h x y]⟩

end StarModule

end CStarModule

namespace TauCeti

/-! ### Bundled adjointable operators -/

/-- The space `L_A(E, F)` of adjointable operators between Hilbert C⋆-modules `E` and `F` over `A`.
For right Hilbert `B`-modules, take `A = Bᵐᵒᵖ`.

An adjointable operator is a bounded `ℂ`-linear map `E →L[ℂ] F` equipped with its bounded adjoint
`F →L[ℂ] E` satisfying `⟪T x, y⟫_A = ⟪x, T* y⟫_A`. Compatibility with the `A`-action is automatic,
and nondegeneracy of the module inner product makes the adjoint unique, so two adjointable maps are
equal whenever they agree on vectors (`AdjointableMap.ext`). -/
structure AdjointableMap (A E F : Type*)
    [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
    extends E →L[ℂ] F where
  /-- The adjoint bounded `ℂ`-linear map `F →L[ℂ] E`. -/
  adjointContinuousLinearMap : F →L[ℂ] E
  /-- The defining adjoint identity `⟪T x, y⟫_A = ⟪x, T* y⟫_A`. -/
  inner_map_eq' (x : E) (y : F) :
    inner A (toContinuousLinearMap x) y = inner A x (adjointContinuousLinearMap y)

namespace AdjointableMap

section Basic

variable {A E F : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- The adjoint field is uniquely determined by the underlying continuous linear map. -/
private theorem adjointContinuousLinearMap_eq_of_toContinuousLinearMap_eq
    {T S : AdjointableMap A E F} (h : T.toContinuousLinearMap = S.toContinuousLinearMap) :
    T.adjointContinuousLinearMap = S.adjointContinuousLinearMap := by
  ext y
  have hsub (x : E) :
      inner A x (T.adjointContinuousLinearMap y - S.adjointContinuousLinearMap y) = 0 := by
    have hadd := CStarModule.inner_add_right (A := A) (x := x)
      (y := T.adjointContinuousLinearMap y - S.adjointContinuousLinearMap y)
      (z := S.adjointContinuousLinearMap y)
    rw [sub_add_cancel, ← T.inner_map_eq', ← S.inner_map_eq', h] at hadd
    exact add_right_cancel (hadd.symm.trans (zero_add _).symm)
  exact sub_eq_zero.mp ((CStarModule.inner_self (A := A)).mp (hsub _))

/-- The forgetful map to `E →L[ℂ] F` is injective: the adjoint is uniquely determined by the
forward operator. -/
theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : AdjointableMap A E F → E →L[ℂ] F) := by
  intro T S h
  cases T
  cases S
  congr
  exact adjointContinuousLinearMap_eq_of_toContinuousLinearMap_eq h

instance instFunLike : FunLike (AdjointableMap A E F) E F where
  coe T := T.toContinuousLinearMap
  coe_injective _ _ h := toContinuousLinearMap_injective (DFunLike.coe_injective h)

instance instContinuousLinearMapClass : ContinuousLinearMapClass (AdjointableMap A E F) ℂ E F where
  map_add T := T.toContinuousLinearMap.map_add
  map_smulₛₗ T := T.toContinuousLinearMap.map_smul
  map_continuous T := T.toContinuousLinearMap.continuous

@[simp]
theorem toContinuousLinearMap_apply (T : AdjointableMap A E F) (x : E) :
    T.toContinuousLinearMap x = T x := (rfl)

@[simp]
theorem coe_toContinuousLinearMap (T : AdjointableMap A E F) :
    ⇑T.toContinuousLinearMap = ⇑T := (rfl)

@[ext]
theorem ext {T S : AdjointableMap A E F} (h : ∀ x, T x = S x) : T = S :=
  DFunLike.ext T S h

/-- Two adjointable operators are equal if their inner products against all vectors on the left
agree. -/
theorem ext_inner_left {T S : AdjointableMap A E F}
    (h : ∀ y x, inner A y (T x) = inner A y (S x)) : T = S := by
  ext x
  apply sub_eq_zero.mp
  apply (CStarModule.inner_self (A := A)).mp
  have hadd := CStarModule.inner_add_right (A := A) (x := T x - S x) (y := T x - S x) (z := S x)
  rw [sub_add_cancel, h (T x - S x) x] at hadd
  exact add_right_cancel (hadd.symm.trans (zero_add _).symm)

/-- Two adjointable operators are equal if their inner products against all vectors on the right
agree. -/
theorem ext_inner_right {T S : AdjointableMap A E F}
    (h : ∀ x y, inner A (T x) y = inner A (S x) y) : T = S :=
  ext_inner_left fun y x => by
    rw [← CStarModule.star_inner, h x y, CStarModule.star_inner]

@[simp]
theorem coe_mk (f : E →L[ℂ] F) (g : F →L[ℂ] E) (h) :
    ⇑(mk f g h : AdjointableMap A E F) = ⇑f := (rfl)

@[simp]
theorem toContinuousLinearMap_mk (f : E →L[ℂ] F) (g : F →L[ℂ] E) (h) :
    (mk f g h : AdjointableMap A E F).toContinuousLinearMap = f := (rfl)

@[simp]
theorem adjointContinuousLinearMap_mk (f : E →L[ℂ] F) (g : F →L[ℂ] E) (h) :
    (mk f g h : AdjointableMap A E F).adjointContinuousLinearMap = g := (rfl)

/-- Every adjointable map satisfies `CStarModule.IsAdjointable`. -/
theorem isAdjointable (T : AdjointableMap A E F) : CStarModule.IsAdjointable A T :=
  ⟨T.adjointContinuousLinearMap, T.inner_map_eq'⟩

/-- The adjoint of an adjointable operator `T : AdjointableMap A E F`, as an adjointable operator
`AdjointableMap A F E`. -/
def adjoint (T : AdjointableMap A E F) : AdjointableMap A F E where
  toContinuousLinearMap := T.adjointContinuousLinearMap
  adjointContinuousLinearMap := T.toContinuousLinearMap
  inner_map_eq' y x := by
    rw [← CStarModule.star_inner, ← T.inner_map_eq', CStarModule.star_inner]

@[simp]
theorem toContinuousLinearMap_adjoint (T : AdjointableMap A E F) :
    T.adjoint.toContinuousLinearMap = T.adjointContinuousLinearMap := (rfl)

@[simp]
theorem adjointContinuousLinearMap_adjoint (T : AdjointableMap A E F) :
    T.adjoint.adjointContinuousLinearMap = T.toContinuousLinearMap := (rfl)

@[simp]
theorem adjointContinuousLinearMap_apply (T : AdjointableMap A E F) (y : F) :
    T.adjointContinuousLinearMap y = T.adjoint y := (rfl)

/-- The defining adjoint identity `⟪T x, y⟫_A = ⟪x, T* y⟫_A`. -/
theorem inner_map_left (T : AdjointableMap A E F) (x : E) (y : F) :
    inner A (T x) y = inner A x (T.adjoint y) :=
  T.inner_map_eq' x y

/-- The symmetric adjoint identity `⟪y, T x⟫_A = ⟪T* y, x⟫_A`. -/
theorem inner_map_right (T : AdjointableMap A E F) (y : F) (x : E) :
    inner A y (T x) = inner A (T.adjoint y) x :=
  (T.adjoint.inner_map_left y x).symm

@[simp]
theorem adjoint_adjoint (T : AdjointableMap A E F) : T.adjoint.adjoint = T :=
  ext fun _ => rfl

theorem adjoint_injective :
    Function.Injective (adjoint : AdjointableMap A E F → AdjointableMap A F E) :=
  Function.LeftInverse.injective adjoint_adjoint

theorem adjoint_bijective :
    Function.Bijective (adjoint : AdjointableMap A E F → AdjointableMap A F E) :=
  ⟨adjoint_injective, fun S => ⟨S.adjoint, adjoint_adjoint S⟩⟩

/-- Every adjointable map commutes with the coefficient action of `A`. For a right Hilbert
`B`-module (`A = Bᵐᵒᵖ`), this states `T (op b • x) = op b • T x`. -/
@[simp]
theorem map_smul_coeff (T : AdjointableMap A E F) (a : A) (x : E) :
    T (a • x) = a • T x := by
  have hsub (y : F) : inner A (T (a • x) - a • T x) y = 0 := by
    have hadd := CStarModule.inner_add_left (A := A)
      (x := T (a • x) - a • T x) (y := a • T x) (z := y)
    rw [sub_add_cancel, T.inner_map_left, CStarModule.inner_op_smul_left,
      CStarModule.inner_op_smul_left, ← T.inner_map_left] at hadd
    exact add_right_cancel (hadd.symm.trans (zero_add _).symm)
  exact sub_eq_zero.mp ((CStarModule.inner_self (A := A)).mp (hsub _))

/-- The pair embedding `(T, T*)` into `(E →L[ℂ] F) × (F →L[ℂ] E)`. -/
def toProdContinuousLinearMap (T : AdjointableMap A E F) : (E →L[ℂ] F) × (F →L[ℂ] E) :=
  (T.toContinuousLinearMap, T.adjointContinuousLinearMap)

theorem range_toProdContinuousLinearMap :
    Set.range (toProdContinuousLinearMap : AdjointableMap A E F → (E →L[ℂ] F) × (F →L[ℂ] E)) =
      { p | ∀ x y, inner A (p.1 x) y = inner A x (p.2 y) } := by
  ext p
  exact ⟨by rintro ⟨T, rfl⟩; exact T.inner_map_eq', fun hp => ⟨⟨p.1, p.2, hp⟩, rfl⟩⟩

/-! #### Additive group structure -/

instance instZero : Zero (AdjointableMap A E F) where
  zero :=
    { toContinuousLinearMap := 0
      adjointContinuousLinearMap := 0
      inner_map_eq' x y := by
        have h₁ : inner A (0 : F) y = 0 := by
          simpa using CStarModule.inner_add_left (A := A) (x := (0 : F)) (y := 0) (z := y)
        have h₂ : inner A x (0 : E) = 0 := by
          simpa using CStarModule.inner_add_right (A := A) (x := x) (y := (0 : E)) (z := 0)
        simpa only [zero_apply] using h₁.trans h₂.symm }

instance instInhabited : Inhabited (AdjointableMap A E F) := ⟨0⟩

instance instSubsingletonLeft [Subsingleton E] : Subsingleton (AdjointableMap A E F) :=
  toContinuousLinearMap_injective.subsingleton

instance instSubsingletonRight [Subsingleton F] : Subsingleton (AdjointableMap A E F) :=
  toContinuousLinearMap_injective.subsingleton

instance instAdd : Add (AdjointableMap A E F) where
  add T S :=
    { toContinuousLinearMap := T.toContinuousLinearMap + S.toContinuousLinearMap
      adjointContinuousLinearMap := T.adjointContinuousLinearMap + S.adjointContinuousLinearMap
      inner_map_eq' x y := by
        simp [CStarModule.inner_add_left, CStarModule.inner_add_right, T.inner_map_left,
          S.inner_map_left] }

instance instNeg : Neg (AdjointableMap A E F) where
  neg T :=
    { toContinuousLinearMap := -T.toContinuousLinearMap
      adjointContinuousLinearMap := -T.adjointContinuousLinearMap
      inner_map_eq' x y := by
        apply add_right_cancel (b := inner A (T x) y)
        have h₁ := CStarModule.inner_add_left (A := A) (x := -T x) (y := T x) (z := y)
        have h₂ := CStarModule.inner_add_right (A := A) (x := x) (y := -T.adjoint y)
          (z := T.adjoint y)
        simp only [neg_add_cancel] at h₁ h₂
        calc inner A ((-T.toContinuousLinearMap) x) y + inner A (T x) y
            = inner A (0 : F) y := h₁.symm
          _ = inner A x (0 : E) := (0 : AdjointableMap A E F).inner_map_eq' x y
          _ = inner A x ((-T.adjointContinuousLinearMap) y) + inner A x (T.adjoint y) := h₂
          _ = inner A x ((-T.adjointContinuousLinearMap) y) + inner A (T x) y := by
              rw [T.inner_map_left] }

instance instSub : Sub (AdjointableMap A E F) where
  sub T S := T + -S

instance instSMulNat : SMul ℕ (AdjointableMap A E F) where
  smul n T :=
    { toContinuousLinearMap := n • T.toContinuousLinearMap
      adjointContinuousLinearMap := n • T.adjointContinuousLinearMap
      inner_map_eq' x y := by
        induction n with
        | zero =>
          rw [zero_smul, zero_smul]
          exact (0 : AdjointableMap A E F).inner_map_eq' x y
        | succ k hk =>
          rw [succ_nsmul, succ_nsmul, add_apply, add_apply, CStarModule.inner_add_left,
            CStarModule.inner_add_right, hk, T.inner_map_eq'] }

instance instSMulInt : SMul ℤ (AdjointableMap A E F) where
  smul n T :=
    { toContinuousLinearMap := n • T.toContinuousLinearMap
      adjointContinuousLinearMap := n • T.adjointContinuousLinearMap
      inner_map_eq' x y := by
        cases n with
        | ofNat k =>
          rw [Int.ofNat_eq_natCast, natCast_zsmul, natCast_zsmul]
          exact (k • T).inner_map_eq' x y
        | negSucc k =>
          rw [negSucc_zsmul, negSucc_zsmul]
          exact (-((k + 1 : ℕ) • T)).inner_map_eq' x y }

@[simp]
theorem toContinuousLinearMap_zero :
    (0 : AdjointableMap A E F).toContinuousLinearMap = 0 := (rfl)

@[simp]
theorem zero_apply (x : E) : (0 : AdjointableMap A E F) x = 0 := (rfl)

@[simp]
theorem toContinuousLinearMap_add (T S : AdjointableMap A E F) :
    (T + S).toContinuousLinearMap = T.toContinuousLinearMap + S.toContinuousLinearMap := (rfl)

@[simp]
theorem add_apply (T S : AdjointableMap A E F) (x : E) :
    (T + S) x = T x + S x := (rfl)

@[simp]
theorem toContinuousLinearMap_neg (T : AdjointableMap A E F) :
    (-T).toContinuousLinearMap = -T.toContinuousLinearMap := (rfl)

@[simp]
theorem neg_apply (T : AdjointableMap A E F) (x : E) : (-T) x = -T x := (rfl)

@[simp]
theorem toContinuousLinearMap_sub (T S : AdjointableMap A E F) :
    (T - S).toContinuousLinearMap = T.toContinuousLinearMap - S.toContinuousLinearMap :=
  (sub_eq_add_neg T.toContinuousLinearMap S.toContinuousLinearMap).symm

@[simp]
theorem sub_apply (T S : AdjointableMap A E F) (x : E) : (T - S) x = T x - S x :=
  (sub_eq_add_neg (T x) (S x)).symm

@[simp]
theorem toContinuousLinearMap_nsmul (n : ℕ) (T : AdjointableMap A E F) :
    (n • T).toContinuousLinearMap = n • T.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_zsmul (n : ℤ) (T : AdjointableMap A E F) :
    (n • T).toContinuousLinearMap = n • T.toContinuousLinearMap := (rfl)

instance instAddCommGroup : AddCommGroup (AdjointableMap A E F) :=
  fast_instance% toContinuousLinearMap_injective.addCommGroup _
    toContinuousLinearMap_zero toContinuousLinearMap_add toContinuousLinearMap_neg
    toContinuousLinearMap_sub (fun _ _ => rfl) (fun _ _ => rfl)

/-- The forgetful additive homomorphism `AdjointableMap A E F →+ (E →L[ℂ] F)`. -/
def toContinuousLinearMapAddMonoidHom : AdjointableMap A E F →+ (E →L[ℂ] F) where
  toFun := toContinuousLinearMap
  map_zero' := toContinuousLinearMap_zero
  map_add' := toContinuousLinearMap_add

@[simp]
theorem toContinuousLinearMapAddMonoidHom_apply (T : AdjointableMap A E F) :
    toContinuousLinearMapAddMonoidHom T = T.toContinuousLinearMap := (rfl)

@[simp]
theorem adjoint_zero : (0 : AdjointableMap A E F).adjoint = 0 :=
  ext fun _ => rfl

@[simp]
theorem adjoint_add (T S : AdjointableMap A E F) :
    (T + S).adjoint = T.adjoint + S.adjoint :=
  ext fun _ => rfl

@[simp]
theorem adjoint_neg (T : AdjointableMap A E F) :
    (-T).adjoint = -T.adjoint :=
  ext fun _ => rfl

@[simp]
theorem adjoint_sub (T S : AdjointableMap A E F) :
    (T - S).adjoint = T.adjoint - S.adjoint := by
  simp [sub_eq_add_neg]

end Basic

/-! #### Right-module inner product formulas -/

section Right

variable {B E F : Type*}
  [NonUnitalSeminormedRing B] [StarRing B] [Module ℂ B] [PartialOrder B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- The right-module adjoint identity `⟨T x, y⟩_B = ⟨x, T* y⟩_B`. -/
theorem unop_inner_map_left (T : AdjointableMap Bᵐᵒᵖ E F) (x : E) (y : F) :
    unop (inner Bᵐᵒᵖ (T x) y) = unop (inner Bᵐᵒᵖ x (T.adjoint y)) :=
  congrArg unop (T.inner_map_left x y)

/-- The symmetric right-module adjoint identity `⟨y, T x⟩_B = ⟨T* y, x⟩_B`. -/
theorem unop_inner_map_right (T : AdjointableMap Bᵐᵒᵖ E F) (y : F) (x : E) :
    unop (inner Bᵐᵒᵖ y (T x)) = unop (inner Bᵐᵒᵖ (T.adjoint y) x) :=
  congrArg unop (T.inner_map_right y x)

end Right

/-! #### Identity and composition -/

section IdComp

variable {A E F G H : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul A H] [CStarModule A H]

/-- The identity operator on a Hilbert C⋆-module `E`, as an adjointable map. -/
protected def id : AdjointableMap A E E where
  toContinuousLinearMap := ContinuousLinearMap.id ℂ E
  adjointContinuousLinearMap := ContinuousLinearMap.id ℂ E
  inner_map_eq' _ _ := rfl

@[simp]
theorem toContinuousLinearMap_id :
    (AdjointableMap.id : AdjointableMap A E E).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ E := (rfl)

@[simp]
theorem id_apply (x : E) : (AdjointableMap.id : AdjointableMap A E E) x = x := (rfl)

@[simp]
theorem adjoint_id :
    (AdjointableMap.id : AdjointableMap A E E).adjoint = AdjointableMap.id :=
  ext fun _ => rfl

/-- Composition of adjointable operators, with `(S ∘ T)* = T* ∘ S*`. -/
def comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) : AdjointableMap A E G where
  toContinuousLinearMap := S.toContinuousLinearMap.comp T.toContinuousLinearMap
  adjointContinuousLinearMap := T.adjointContinuousLinearMap.comp S.adjointContinuousLinearMap
  inner_map_eq' x z := (S.inner_map_eq' (T x) z).trans (T.inner_map_eq' x (S.adjoint z))

@[simp]
theorem toContinuousLinearMap_comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (S.comp T).toContinuousLinearMap =
      S.toContinuousLinearMap.comp T.toContinuousLinearMap := (rfl)

@[simp]
theorem comp_apply (S : AdjointableMap A F G) (T : AdjointableMap A E F) (x : E) :
    (S.comp T) x = S (T x) := (rfl)

@[simp]
theorem coe_comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    ⇑(S.comp T) = S ∘ T := (rfl)

/-- The adjoint reverses composition: `(S ∘ T)* = T* ∘ S*`. -/
@[simp]
theorem adjoint_comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (S.comp T).adjoint = T.adjoint.comp S.adjoint :=
  ext fun _ => rfl

@[simp]
theorem id_comp (T : AdjointableMap A E F) : AdjointableMap.id.comp T = T :=
  ext fun _ => rfl

@[simp]
theorem comp_id (T : AdjointableMap A E F) : T.comp AdjointableMap.id = T :=
  ext fun _ => rfl

@[simp]
theorem zero_comp (T : AdjointableMap A E F) : (0 : AdjointableMap A F G).comp T = 0 :=
  ext fun _ => rfl

@[simp]
theorem comp_zero (S : AdjointableMap A F G) : S.comp (0 : AdjointableMap A E F) = 0 :=
  ext fun _ => map_zero S

theorem add_comp (S₁ S₂ : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (S₁ + S₂).comp T = S₁.comp T + S₂.comp T :=
  ext fun _ => rfl

theorem comp_add (S : AdjointableMap A F G) (T₁ T₂ : AdjointableMap A E F) :
    S.comp (T₁ + T₂) = S.comp T₁ + S.comp T₂ :=
  ext fun x => map_add S (T₁ x) (T₂ x)

theorem neg_comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (-S).comp T = -(S.comp T) :=
  ext fun _ => rfl

theorem comp_neg (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    S.comp (-T) = -(S.comp T) :=
  ext fun x => map_neg S (T x)

theorem sub_comp (S₁ S₂ : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (S₁ - S₂).comp T = S₁.comp T - S₂.comp T :=
  ext fun _ => rfl

theorem comp_sub (S : AdjointableMap A F G) (T₁ T₂ : AdjointableMap A E F) :
    S.comp (T₁ - T₂) = S.comp T₁ - S.comp T₂ := by
  ext x; simp

theorem comp_assoc (R : AdjointableMap A G H) (S : AdjointableMap A F G)
    (T : AdjointableMap A E F) :
    (R.comp S).comp T = R.comp (S.comp T) :=
  ext fun _ => rfl

end IdComp

/-! #### Complex scalar structure and `⋆`-ring structure on endomorphisms -/

section StarModule

variable {A E F G : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

/-- Every adjointable map forms a `LinearMap.IsAdjointPair` with its adjoint for the flipped
module inner-product forms. -/
theorem isAdjointPair (T : AdjointableMap A E F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T T.adjoint :=
  CStarModule.isAdjointPair_inner_iff.mpr T.inner_map_left

instance instSMulComplex : SMul ℂ (AdjointableMap A E F) where
  smul c T :=
    { toContinuousLinearMap := c • T.toContinuousLinearMap
      adjointContinuousLinearMap := star c • T.adjointContinuousLinearMap
      inner_map_eq' x y := by
        simp [CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex,
          T.inner_map_left] }

@[simp]
theorem toContinuousLinearMap_smul (c : ℂ) (T : AdjointableMap A E F) :
    (c • T).toContinuousLinearMap = c • T.toContinuousLinearMap := (rfl)

@[simp]
theorem smul_apply (c : ℂ) (T : AdjointableMap A E F) (x : E) :
    (c • T) x = c • T x := (rfl)

@[simp]
theorem adjoint_smul (c : ℂ) (T : AdjointableMap A E F) :
    (c • T).adjoint = star c • T.adjoint :=
  ext fun _ => rfl

instance instModuleComplex : Module ℂ (AdjointableMap A E F) where
  one_smul T := ext fun x => one_smul ℂ (T x)
  mul_smul c₁ c₂ T := ext fun x => mul_smul c₁ c₂ (T x)
  smul_zero c := ext fun _ => smul_zero c
  smul_add c T S := ext fun x => smul_add c (T x) (S x)
  add_smul c₁ c₂ T := ext fun x => add_smul c₁ c₂ (T x)
  zero_smul T := ext fun x => zero_smul ℂ (T x)

/-- The forgetful `ℂ`-linear map `AdjointableMap A E F →ₗ[ℂ] (E →L[ℂ] F)`. -/
def toContinuousLinearMapLinearMap : AdjointableMap A E F →ₗ[ℂ] (E →L[ℂ] F) where
  toFun := toContinuousLinearMap
  map_add' := toContinuousLinearMap_add
  map_smul' := toContinuousLinearMap_smul

@[simp]
theorem toContinuousLinearMapLinearMap_apply (T : AdjointableMap A E F) :
    toContinuousLinearMapLinearMap T = T.toContinuousLinearMap := (rfl)

/-- Taking the adjoint as a conjugate-linear equivalence `AdjointableMap A E F ≃ₗ⋆[ℂ]
AdjointableMap A F E`. -/
def adjointLinearEquiv : AdjointableMap A E F ≃ₗ⋆[ℂ] AdjointableMap A F E where
  toFun := adjoint
  invFun := adjoint
  left_inv := adjoint_adjoint
  right_inv := adjoint_adjoint
  map_add' := adjoint_add
  map_smul' := adjoint_smul

@[simp]
theorem adjointLinearEquiv_apply (T : AdjointableMap A E F) :
    adjointLinearEquiv T = T.adjoint := (rfl)

@[simp]
theorem adjointLinearEquiv_symm_apply (S : AdjointableMap A F E) :
    adjointLinearEquiv.symm S = S.adjoint := (rfl)

@[simp]
theorem smul_comp (c : ℂ) (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (c • S).comp T = c • S.comp T :=
  ext fun _ => rfl

@[simp]
theorem comp_smul (S : AdjointableMap A F G) (c : ℂ) (T : AdjointableMap A E F) :
    S.comp (c • T) = c • S.comp T :=
  ext fun x => map_smul S c (T x)

end StarModule

section EndRing

variable {A E : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

instance instOne : One (AdjointableMap A E E) := ⟨AdjointableMap.id⟩

instance instMul : Mul (AdjointableMap A E E) := ⟨comp⟩

theorem one_def : (1 : AdjointableMap A E E) = AdjointableMap.id := (rfl)

theorem mul_def (T S : AdjointableMap A E E) : T * S = T.comp S := (rfl)

@[simp]
theorem toContinuousLinearMap_one :
    (1 : AdjointableMap A E E).toContinuousLinearMap = 1 := (rfl)

@[simp]
theorem one_apply (x : E) : (1 : AdjointableMap A E E) x = x := (rfl)

@[simp]
theorem toContinuousLinearMap_mul (T S : AdjointableMap A E E) :
    (T * S).toContinuousLinearMap = T.toContinuousLinearMap * S.toContinuousLinearMap := (rfl)

@[simp]
theorem mul_apply (T S : AdjointableMap A E E) (x : E) : (T * S) x = T (S x) := (rfl)

instance instPowNat : Pow (AdjointableMap A E E) ℕ where
  pow T n :=
    { toContinuousLinearMap := T.toContinuousLinearMap ^ n
      adjointContinuousLinearMap := T.adjointContinuousLinearMap ^ n
      inner_map_eq' x y := by
        induction n generalizing x y with
        | zero => rfl
        | succ k hk =>
          rw [pow_succ', mul_apply_eq_comp, T.inner_map_eq', hk, pow_succ, mul_apply_eq_comp] }

instance instNatCast : NatCast (AdjointableMap A E E) where
  natCast n := n • (1 : AdjointableMap A E E)

instance instIntCast : IntCast (AdjointableMap A E E) where
  intCast n := n • (1 : AdjointableMap A E E)

theorem natCast_def (n : ℕ) : (n : AdjointableMap A E E) = n • 1 := (rfl)

theorem intCast_def (n : ℤ) : (n : AdjointableMap A E E) = n • 1 := (rfl)

@[simp]
theorem toContinuousLinearMap_pow (T : AdjointableMap A E E) (n : ℕ) :
    (T ^ n).toContinuousLinearMap = T.toContinuousLinearMap ^ n := (rfl)

@[simp]
theorem toContinuousLinearMap_natCast (n : ℕ) :
    (n : AdjointableMap A E E).toContinuousLinearMap = n := by
  rw [natCast_def, toContinuousLinearMap_nsmul, toContinuousLinearMap_one, nsmul_one]

@[simp]
theorem toContinuousLinearMap_intCast (n : ℤ) :
    (n : AdjointableMap A E E).toContinuousLinearMap = n := by
  rw [intCast_def, toContinuousLinearMap_zsmul, toContinuousLinearMap_one, zsmul_one]

instance instRing : Ring (AdjointableMap A E E) :=
  fast_instance% toContinuousLinearMap_injective.ring _
    toContinuousLinearMap_zero toContinuousLinearMap_one
    toContinuousLinearMap_add toContinuousLinearMap_mul
    toContinuousLinearMap_neg toContinuousLinearMap_sub
    (fun _ _ => rfl) (fun _ _ => rfl)
    toContinuousLinearMap_pow toContinuousLinearMap_natCast toContinuousLinearMap_intCast

/-- The forgetful ring homomorphism `AdjointableMap A E E →+* (E →L[ℂ] E)`. -/
def toContinuousLinearMapRingHom : AdjointableMap A E E →+* (E →L[ℂ] E) where
  toFun := toContinuousLinearMap
  map_one' := toContinuousLinearMap_one
  map_mul' := toContinuousLinearMap_mul
  map_zero' := toContinuousLinearMap_zero
  map_add' := toContinuousLinearMap_add

@[simp]
theorem toContinuousLinearMapRingHom_apply (T : AdjointableMap A E E) :
    toContinuousLinearMapRingHom T = T.toContinuousLinearMap := (rfl)

instance instStar : Star (AdjointableMap A E E) := ⟨adjoint⟩

theorem star_def (T : AdjointableMap A E E) : star T = T.adjoint := (rfl)

@[simp]
theorem star_apply (T : AdjointableMap A E E) (x : E) : (star T) x = T.adjoint x := (rfl)

@[simp]
theorem adjoint_one : (1 : AdjointableMap A E E).adjoint = 1 := adjoint_id

@[simp]
theorem adjoint_mul (T S : AdjointableMap A E E) : (T * S).adjoint = S.adjoint * T.adjoint :=
  adjoint_comp T S

instance instStarRing : StarRing (AdjointableMap A E E) where
  star := star
  star_involutive := adjoint_adjoint
  star_mul := adjoint_comp
  star_add := adjoint_add

/-! #### Tautological action of `AdjointableMap A E E` on `E` -/

/-- The natural left action of `L_A(E)` on `E` by evaluation. -/
instance applyModule : Module (AdjointableMap A E E) E where
  smul T x := T x
  one_smul := one_apply
  mul_smul := mul_apply
  smul_zero T := map_zero T
  smul_add T := map_add T
  add_smul := add_apply
  zero_smul := zero_apply

@[simp]
protected theorem smul_def (T : AdjointableMap A E E) (x : E) : T • x = T x := (rfl)

instance applyFaithfulSMul : FaithfulSMul (AdjointableMap A E E) E :=
  ⟨fun h => ext h⟩

instance applySMulCommClassComplex : SMulCommClass ℂ (AdjointableMap A E E) E where
  smul_comm c T x := (map_smul T c x).symm

instance applySMulCommClassComplex' : SMulCommClass (AdjointableMap A E E) ℂ E where
  smul_comm T c x := map_smul T c x

instance applySMulCommClassCoeff : SMulCommClass A (AdjointableMap A E E) E where
  smul_comm a T x := (T.map_smul_coeff a x).symm

instance applySMulCommClassCoeff' : SMulCommClass (AdjointableMap A E E) A E where
  smul_comm := map_smul_coeff

instance continuousConstSMul_apply : ContinuousConstSMul (AdjointableMap A E E) E :=
  ⟨fun T => T.toContinuousLinearMap.continuous⟩

end EndRing

section EndAlgebra

variable {A E : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

instance instAlgebraComplex : Algebra ℂ (AdjointableMap A E E) where
  algebraMap :=
    { toFun c := c • (1 : AdjointableMap A E E)
      map_one' := one_smul ℂ (1 : AdjointableMap A E E)
      map_mul' c₁ c₂ := by ext x; simp [← mul_smul, mul_comm]
      map_zero' := zero_smul ℂ (1 : AdjointableMap A E E)
      map_add' c₁ c₂ := add_smul c₁ c₂ (1 : AdjointableMap A E E) }
  commutes' c T := by ext x; simp
  smul_def' c T := by ext x; simp

@[simp]
theorem toContinuousLinearMap_algebraMap (c : ℂ) :
    (algebraMap ℂ (AdjointableMap A E E) c).toContinuousLinearMap =
      algebraMap ℂ (E →L[ℂ] E) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    toContinuousLinearMap_smul, toContinuousLinearMap_one]

/-- The forgetful `ℂ`-algebra homomorphism `AdjointableMap A E E →ₐ[ℂ] (E →L[ℂ] E)`. -/
def toContinuousLinearMapAlgHom : AdjointableMap A E E →ₐ[ℂ] (E →L[ℂ] E) where
  toRingHom := toContinuousLinearMapRingHom
  commutes' := toContinuousLinearMap_algebraMap

@[simp]
theorem toContinuousLinearMapAlgHom_apply (T : AdjointableMap A E E) :
    toContinuousLinearMapAlgHom T = T.toContinuousLinearMap := (rfl)

@[simp]
theorem algebraMap_apply (c : ℂ) (x : E) :
    algebraMap ℂ (AdjointableMap A E E) c x = c • x := by
  simp [Algebra.algebraMap_eq_smul_one]

instance instStarModuleComplex : StarModule ℂ (AdjointableMap A E E) where
  star_smul := adjoint_smul

instance applyIsScalarTowerComplex : IsScalarTower ℂ (AdjointableMap A E E) E where
  smul_assoc c T x := by simp [AdjointableMap.smul_def]

/-- Polarization identity for an adjointable endomorphism over `ℂ`: `⟪x, T y⟫_A` is determined by
the diagonal inner products `⟪z, T z⟫_A`. -/
theorem inner_map_polarization (T : AdjointableMap A E E) (x y : E) :
    inner A x (T y) = (4 : ℂ)⁻¹ •
      (inner A (x + y) (T (x + y)) - inner A (x - y) (T (x - y)) -
        I • inner A (x + I • y) (T (x + I • y)) +
        I • inner A (x - I • y) (T (x - I • y))) := by
  simp only [map_add, map_sub, map_smul, CStarModule.inner_add_left,
    CStarModule.inner_add_right, CStarModule.inner_sub_left, CStarModule.inner_sub_right,
    CStarModule.inner_smul_left_complex, CStarModule.inner_smul_right_complex,
    Complex.star_def, conj_I, smul_add, smul_sub, smul_neg, smul_smul, neg_smul, I_mul_I]
  module

/-- Over `ℂ`, an adjointable endomorphism vanishes if and only if all of its diagonal module inner
products `⟪x, T x⟫_A` vanish. -/
theorem eq_zero_iff_forall_inner_self (T : AdjointableMap A E E) :
    T = 0 ↔ ∀ x : E, inner A x (T x) = 0 := by
  refine ⟨fun hT x => by simp [hT], fun h => ext_inner_left fun x y => ?_⟩
  rw [inner_map_polarization]
  simp only [h, sub_zero, add_zero, smul_zero, zero_apply, CStarModule.inner_zero_right]

/-- Over `ℂ`, two adjointable endomorphisms are equal if and only if they have equal diagonal
module inner products `⟪x, T x⟫_A = ⟪x, S x⟫_A` for all `x`. -/
theorem eq_iff_forall_inner_self {T S : AdjointableMap A E E} :
    T = S ↔ ∀ x : E, inner A x (T x) = inner A x (S x) := by
  rw [← sub_eq_zero, eq_zero_iff_forall_inner_self]
  simp only [sub_apply, CStarModule.inner_sub_right, sub_eq_zero]

/-- Over `ℂ`, an adjointable operator `T` is self-adjoint if and only if every diagonal inner
product `⟪x, T x⟫_A` is self-adjoint in `A`. -/
theorem isSelfAdjoint_iff (T : AdjointableMap A E E) :
    IsSelfAdjoint T ↔ ∀ x : E, IsSelfAdjoint (inner A x (T x)) := by
  rw [IsSelfAdjoint, star_def, eq_iff_forall_inner_self]
  refine forall_congr' fun x => ?_
  rw [← T.inner_map_left, ← CStarModule.star_inner, IsSelfAdjoint]

end EndAlgebra

/-! ### Operator norm, isometric forgetful map, and C⋆-identity -/

section NormInduced

variable {A E F G : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

/-- The operator norm on `AdjointableMap A E F` is induced by the forgetful embedding into
`E →L[ℂ] F`. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (AdjointableMap A E F) :=
  fast_instance% NormedAddCommGroup.induced (AdjointableMap A E F) (E →L[ℂ] F)
    ({ toFun := toContinuousLinearMap
       map_zero' := toContinuousLinearMap_zero
       map_add' := toContinuousLinearMap_add } : AdjointableMap A E F →+ (E →L[ℂ] F))
    toContinuousLinearMap_injective

@[simp]
theorem norm_toContinuousLinearMap (T : AdjointableMap A E F) :
    ‖T.toContinuousLinearMap‖ = ‖T‖ := (rfl)

@[simp]
theorem nnNorm_toContinuousLinearMap (T : AdjointableMap A E F) :
    ‖T.toContinuousLinearMap‖₊ = ‖T‖₊ := (rfl)

theorem isometry_toContinuousLinearMap :
    Isometry (toContinuousLinearMap : AdjointableMap A E F → E →L[ℂ] F) :=
  fun _ _ => rfl

theorem le_opNorm (T : AdjointableMap A E F) (x : E) : ‖T x‖ ≤ ‖T‖ * ‖x‖ :=
  T.toContinuousLinearMap.le_opNorm x

theorem opNorm_le_bound (T : AdjointableMap A E F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖T x‖ ≤ M * ‖x‖) : ‖T‖ ≤ M :=
  T.toContinuousLinearMap.opNorm_le_bound hMp hM

theorem opNorm_comp_le (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ :=
  S.toContinuousLinearMap.opNorm_comp_le T.toContinuousLinearMap

noncomputable instance instNormedRing : NormedRing (AdjointableMap A E E) where
  dist_eq := NormedAddCommGroup.dist_eq
  norm_mul_le := opNorm_comp_le

instance applyIsBoundedSMul : IsBoundedSMul (AdjointableMap A E E) E :=
  IsBoundedSMul.of_norm_smul_le le_opNorm

end NormInduced

section NormedSpace

variable {A E F G : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

noncomputable instance instNormedSpaceComplex : NormedSpace ℂ (AdjointableMap A E F) where
  norm_smul_le c T := norm_smul_le c T.toContinuousLinearMap

/-- The forgetful linear isometry `AdjointableMap A E F →ₗᵢ[ℂ] (E →L[ℂ] F)`. -/
noncomputable def toContinuousLinearMapₗᵢ : AdjointableMap A E F →ₗᵢ[ℂ] (E →L[ℂ] F) where
  toLinearMap := toContinuousLinearMapLinearMap
  norm_map' _ := rfl

@[simp]
theorem toContinuousLinearMapₗᵢ_apply (T : AdjointableMap A E F) :
    toContinuousLinearMapₗᵢ T = T.toContinuousLinearMap := (rfl)

/-- Composition of adjointable operators as a bounded bilinear map. -/
noncomputable def compL :
    AdjointableMap A F G →L[ℂ] AdjointableMap A E F →L[ℂ] AdjointableMap A E G :=
  LinearMap.mkContinuous₂
    { toFun S :=
        { toFun := S.comp
          map_add' := S.comp_add
          map_smul' := S.comp_smul }
      map_add' := fun S₁ S₂ => LinearMap.ext (add_comp S₁ S₂)
      map_smul' := fun c S => LinearMap.ext (smul_comp c S) }
    1 fun S T => by
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, one_mul] using opNorm_comp_le S T

@[simp]
theorem compL_apply (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    compL S T = S.comp T := (rfl)

noncomputable instance instNormedAlgebraComplex : NormedAlgebra ℂ (AdjointableMap A E E) where
  norm_smul_le c T := norm_smul_le c T.toContinuousLinearMap

end NormedSpace

section CStarNorm

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- An adjointable operator and its adjoint have equal operator norms: `‖T*‖ = ‖T‖`. -/
@[simp]
theorem norm_adjoint (T : AdjointableMap A E F) : ‖T.adjoint‖ = ‖T‖ :=
  T.isAdjointPair.norm_eq_cstarModule

@[simp]
theorem nnNorm_adjoint (T : AdjointableMap A E F) : ‖T.adjoint‖₊ = ‖T‖₊ :=
  Subtype.ext (norm_adjoint T)

/-- Taking the adjoint is a conjugate-linear isometric equivalence
`AdjointableMap A E F ≃ₗᵢ⋆[ℂ] AdjointableMap A F E`. -/
noncomputable def adjointₗᵢ : AdjointableMap A E F ≃ₗᵢ⋆[ℂ] AdjointableMap A F E :=
  { adjointLinearEquiv with
    norm_map' := norm_adjoint }

@[simp]
theorem adjointₗᵢ_apply (T : AdjointableMap A E F) : adjointₗᵢ T = T.adjoint := (rfl)

@[simp]
theorem adjointₗᵢ_symm_apply (S : AdjointableMap A F E) :
    adjointₗᵢ.symm S = S.adjoint := (rfl)

/-- The C⋆-identity for rectangular adjointable operators: `‖T* ∘ T‖ = ‖T‖ ^ 2`. -/
@[simp]
theorem norm_adjoint_comp_self (T : AdjointableMap A E F) :
    ‖T.adjoint.comp T‖ = ‖T‖ ^ 2 :=
  T.isAdjointPair.norm_adjoint_comp_self_cstarModule

/-- The dual C⋆-identity for rectangular adjointable operators: `‖T ∘ T*‖ = ‖T‖ ^ 2`. -/
@[simp]
theorem norm_comp_adjoint_self (T : AdjointableMap A E F) :
    ‖T.comp T.adjoint‖ = ‖T‖ ^ 2 := by
  simpa only [adjoint_adjoint, norm_adjoint] using norm_adjoint_comp_self T.adjoint

theorem isometry_toProdContinuousLinearMap :
    Isometry (toProdContinuousLinearMap : AdjointableMap A E F → (E →L[ℂ] F) × (F →L[ℂ] E)) := by
  refine Isometry.of_dist_eq fun T S => ?_
  rw [dist_eq_norm, dist_eq_norm, Prod.norm_def]
  simp only [toProdContinuousLinearMap, Prod.fst_sub, Prod.snd_sub, ← toContinuousLinearMap_sub,
    ← toContinuousLinearMap_adjoint, ← adjoint_sub, norm_toContinuousLinearMap, norm_adjoint,
    max_self]

instance instCompleteSpace [CompleteSpace E] [CompleteSpace F] :
    CompleteSpace (AdjointableMap A E F) := by
  rw [completeSpace_iff_isComplete_range
    isometry_toProdContinuousLinearMap.isUniformInducing]
  apply IsClosed.isComplete
  rw [range_toProdContinuousLinearMap]
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ ?_
  · exact CStarModule.continuous_inner.comp
      (((ContinuousLinearMap.apply ℂ F x).continuous.comp continuous_fst).prodMk continuous_const)
  · exact CStarModule.continuous_inner.comp
      (continuous_const.prodMk ((ContinuousLinearMap.apply ℂ E y).continuous.comp continuous_snd))

/-- Construct an adjointable operator from a pair of plain functions `T : E → F` and `S : F → E`
between complete Hilbert C⋆-modules satisfying `⟪T x, y⟫_A = ⟪x, S y⟫_A`. Neither linearity nor
continuity is assumed of `T` or `S`. -/
noncomputable def ofAdjointPair [CompleteSpace E] [CompleteSpace F]
    (T : E → F) (S : F → E) (h : ∀ x y, inner A (T x) y = inner A x (S y)) :
    AdjointableMap A E F where
  toContinuousLinearMap :=
    (CStarModule.isAdjointPair_inner_iff.mpr h).toContinuousLinearMapCStarModule
  adjointContinuousLinearMap :=
    (CStarModule.isAdjointPair_inner_iff.mpr h).symm_cstarModule.toContinuousLinearMapCStarModule
  inner_map_eq' x y := by
    simp [h x y]

@[simp]
theorem ofAdjointPair_apply [CompleteSpace E] [CompleteSpace F]
    (T : E → F) (S : F → E) (h : ∀ x y, inner A (T x) y = inner A x (S y)) (x : E) :
    ofAdjointPair T S h x = T x :=
  (CStarModule.isAdjointPair_inner_iff.mpr h).toContinuousLinearMapCStarModule_apply x

theorem adjoint_ofAdjointPair_apply [CompleteSpace E] [CompleteSpace F]
    (T : E → F) (S : F → E) (h : ∀ x y, inner A (T x) y = inner A x (S y)) (y : F) :
    (ofAdjointPair T S h).adjoint y = S y := by
  have hS := (CStarModule.isAdjointPair_inner_iff.mpr h).symm_cstarModule
  exact hS.toContinuousLinearMapCStarModule_apply y

@[simp]
theorem adjoint_ofAdjointPair [CompleteSpace E] [CompleteSpace F]
    (T : E → F) (S : F → E) (h : ∀ x y, inner A (T x) y = inner A x (S y)) :
    (ofAdjointPair T S h).adjoint =
      ofAdjointPair S T (fun y x => by
        rw [← CStarModule.star_inner, ← h x y, CStarModule.star_inner]) := by
  ext y
  rw [adjoint_ofAdjointPair_apply, ofAdjointPair_apply]

/-- Construct an adjointable operator from a witness of `CStarModule.IsAdjointable` between
complete Hilbert C⋆-modules. -/
noncomputable def ofIsAdjointable [CompleteSpace E] [CompleteSpace F]
    {T : E → F} (h : CStarModule.IsAdjointable A T) : AdjointableMap A E F :=
  ofAdjointPair T h.choose h.choose_spec

@[simp]
theorem ofIsAdjointable_apply [CompleteSpace E] [CompleteSpace F]
    {T : E → F} (h : CStarModule.IsAdjointable A T) (x : E) :
    ofIsAdjointable h x = T x :=
  ofAdjointPair_apply T h.choose h.choose_spec x

@[simp]
theorem coe_ofIsAdjointable [CompleteSpace E] [CompleteSpace F]
    {T : E → F} (h : CStarModule.IsAdjointable A T) :
    ⇑(ofIsAdjointable h) = T :=
  funext (ofIsAdjointable_apply h)

/-- Between complete Hilbert C⋆-modules, a function (in particular, a bounded module map) comes
from an element of `AdjointableMap A E F` if and only if it admits a plain adjoint function. -/
theorem exists_coe_eq_iff [CompleteSpace E] [CompleteSpace F] {T : E → F} :
    (∃ T' : AdjointableMap A E F, ⇑T' = T) ↔ CStarModule.IsAdjointable A T :=
  ⟨by rintro ⟨T', rfl⟩; exact T'.isAdjointable, fun h => ⟨ofIsAdjointable h, coe_ofIsAdjointable h⟩⟩

end CStarNorm

/-! ### The unital C⋆-algebra `L_A(E)`, positivity, and modulus -/

section CStarAlgebra

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

instance instCStarRing : CStarRing (AdjointableMap A E E) where
  norm_mul_self_le T := by
    rw [star_def, mul_def, norm_adjoint_comp_self, sq]

/-- For a complete Hilbert C⋆-module `E`, `AdjointableMap A E E` is a unital C⋆-algebra (with the
zero algebra when `E` is the zero module). -/
noncomputable instance instCStarAlgebra [CompleteSpace E] :
    CStarAlgebra (AdjointableMap A E E) where

noncomputable instance instPartialOrder [CompleteSpace E] :
    PartialOrder (AdjointableMap A E E) :=
  CStarAlgebra.spectralOrder _

instance instStarOrderedRing [CompleteSpace E] :
    StarOrderedRing (AdjointableMap A E E) :=
  CStarAlgebra.spectralOrderedRing _

/-- Positivity in the C⋆-algebra `AdjointableMap A E E` is characterized by positivity of the
module inner products `⟪x, T x⟫_A` in `A` (Lance, Lemma 4.1; Raeburn–Williams, Proposition 2.21).
Self-adjointness is not assumed on the right-hand side: over `ℂ` it follows automatically from
`0 ≤ ⟪x, T x⟫_A`. -/
theorem nonneg_iff [CompleteSpace E] {T : AdjointableMap A E E} :
    0 ≤ T ↔ ∀ x : E, 0 ≤ inner A x (T x) := by
  refine ⟨fun hT x => ?_, fun h => ?_⟩
  · obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
    rw [mul_apply, star_apply, ← R.inner_map_left]
    exact CStarModule.inner_self_nonneg
  · have hsa : IsSelfAdjoint T :=
      (isSelfAdjoint_iff T).mpr fun x => IsSelfAdjoint.of_nonneg (h x)
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
      rw [← mul_apply, hTN, neg_apply, CStarModule.inner_neg_right, mul_assoc, mul_apply,
        star_apply, ← R.inner_map_left, Left.nonneg_neg_iff] at hx
      exact (CStarModule.inner_self (A := A)).mp
        (le_antisymm hx CStarModule.inner_self_nonneg)
    rw [← star_mul_self_eq_zero, hN.isSelfAdjoint.star_eq]
    calc N * N = star R * (R * N) := by rw [← mul_assoc, ← hR]
      _ = 0 := by rw [hRN, mul_zero]

/-- For a complete Hilbert C⋆-module `E` and any `S : AdjointableMap A E F`, `S* ∘ S` is positive
in `AdjointableMap A E E`, even when `F` is not assumed complete. -/
theorem adjoint_comp_self_nonneg [CompleteSpace E] (S : AdjointableMap A E F) :
    0 ≤ S.adjoint.comp S :=
  nonneg_iff.mpr fun x => by
    rw [comp_apply, ← S.inner_map_left]
    exact CStarModule.inner_self_nonneg

/-- For a complete Hilbert C⋆-module `F` and any `S : AdjointableMap A E F`, `S ∘ S*` is positive
in `AdjointableMap A F F`. -/
theorem comp_adjoint_self_nonneg [CompleteSpace F] (S : AdjointableMap A E F) :
    0 ≤ S.comp S.adjoint := by
  simpa only [adjoint_adjoint] using adjoint_comp_self_nonneg S.adjoint

/-- Rectangular congruence preserves positivity: if `0 ≤ T` in `AdjointableMap A F F` and
`S : AdjointableMap A E F`, then `0 ≤ S* ∘ T ∘ S` in `AdjointableMap A E E`. -/
theorem adjoint_comp_comp_nonneg [CompleteSpace E] [CompleteSpace F]
    {T : AdjointableMap A F F} (hT : 0 ≤ T) (S : AdjointableMap A E F) :
    0 ≤ (S.adjoint.comp T).comp S :=
  nonneg_iff.mpr fun x => by
    rw [comp_apply, comp_apply, ← S.inner_map_left]
    exact nonneg_iff.mp hT (S x)

/-- For a self-adjoint adjointable operator `T`, `⟪x, T x⟫_A ≤ ‖T‖ • ⟪x, x⟫_A`. -/
theorem inner_map_self_le_norm [CompleteSpace E] {T : AdjointableMap A E E}
    (hT : IsSelfAdjoint T) (x : E) :
    inner A x (T x) ≤ ‖T‖ • inner A x x := by
  have hsub : 0 ≤ inner A x ((algebraMap ℝ (AdjointableMap A E E) ‖T‖ - T) x) :=
    nonneg_iff.mp (sub_nonneg.mpr hT.le_algebraMap_norm_self) x
  have halg : algebraMap ℝ (AdjointableMap A E E) ‖T‖ x = (‖T‖ : ℂ) • x := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, smul_apply, one_apply]
  rwa [sub_apply, halg, CStarModule.inner_sub_right, CStarModule.inner_smul_right_complex,
    Complex.coe_smul, sub_nonneg] at hsub

/-- The positive modulus `|T| = √(T* ∘ T) ∈ AdjointableMap A E E` of a rectangular adjointable
operator `T : AdjointableMap A E F` on a complete Hilbert C⋆-module `E`. -/
noncomputable def abs [CompleteSpace E] (T : AdjointableMap A E F) : AdjointableMap A E E :=
  CFC.sqrt (T.adjoint.comp T)

theorem abs_def [CompleteSpace E] (T : AdjointableMap A E F) :
    T.abs = CFC.sqrt (T.adjoint.comp T) := (rfl)

@[simp]
theorem abs_nonneg [CompleteSpace E] (T : AdjointableMap A E F) : 0 ≤ T.abs :=
  CFC.sqrt_nonneg (T.adjoint.comp T)

@[simp]
theorem isSelfAdjoint_abs [CompleteSpace E] (T : AdjointableMap A E F) : IsSelfAdjoint T.abs :=
  T.abs_nonneg.isSelfAdjoint

@[simp]
theorem abs_mul_abs [CompleteSpace E] (T : AdjointableMap A E F) :
    T.abs * T.abs = T.adjoint.comp T :=
  CFC.sqrt_mul_sqrt_self _ (adjoint_comp_self_nonneg T)

/-- The modulus preserves module inner products: `⟪|T| x, |T| y⟫_A = ⟪T x, T y⟫_A`. -/
@[simp]
theorem inner_abs_abs [CompleteSpace E] (T : AdjointableMap A E F) (x y : E) :
    inner A (T.abs x) (T.abs y) = inner A (T x) (T y) := by
  rw [T.abs.inner_map_left, ← star_def, T.isSelfAdjoint_abs.star_eq, ← mul_apply, abs_mul_abs,
    comp_apply, ← T.inner_map_left]

@[simp]
theorem norm_abs_apply [CompleteSpace E] (T : AdjointableMap A E F) (x : E) :
    ‖T.abs x‖ = ‖T x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (T.abs x),
    CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (T x), inner_abs_abs]

@[simp]
theorem norm_abs [CompleteSpace E] (T : AdjointableMap A E F) : ‖T.abs‖ = ‖T‖ := by
  rw [abs_def, CFC.norm_sqrt _ (adjoint_comp_self_nonneg T), norm_adjoint_comp_self,
    Real.sqrt_sq (norm_nonneg T)]

end CStarAlgebra

section RightPositivity

variable {B E : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- Right-module form of `AdjointableMap.nonneg_iff`: `0 ≤ T` in `L_B(E)` iff `0 ≤ ⟨x, T x⟩_B` for
all `x : E`. -/
theorem nonneg_iff_unop {T : AdjointableMap Bᵐᵒᵖ E E} :
    0 ≤ T ↔ ∀ x : E, 0 ≤ unop (inner Bᵐᵒᵖ x (T x)) := by
  simp_rw [nonneg_iff, MulOpposite.unop_nonneg]

end RightPositivity

/-! ### Orthogonal projections and adjointable isometries -/

section Projections

variable {A E : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

/-- An adjointable endomorphism `P` is an orthogonal projection (`IsStarProjection P`, i.e.
`P * P = P` and `P* = P`) if and only if `⟪P x, y⟫_A = ⟪P x, P y⟫_A` for all `x, y : E`. -/
theorem isStarProjection_iff_forall_inner {P : AdjointableMap A E E} :
    IsStarProjection P ↔ ∀ x y : E, inner A (P x) y = inner A (P x) (P y) := by
  refine ⟨fun hP x y => ?_, fun h => ?_⟩
  · calc inner A (P x) y = inner A ((P * P) x) y := by rw [hP.isIdempotentElem.eq]
      _ = inner A (P x) (P.adjoint y) := P.inner_map_left (P x) y
      _ = inner A (P x) (P y) := by rw [← star_def, hP.isSelfAdjoint.star_eq]
  · have hsa : IsSelfAdjoint P := by
      rw [IsSelfAdjoint, star_def]
      exact ext_inner_left fun x y => by
        rw [← P.inner_map_left, h x y, ← CStarModule.star_inner, ← h y x, CStarModule.star_inner]
    refine ⟨?_, hsa⟩
    rw [IsIdempotentElem]
    exact ext_inner_right fun x y => by
      rw [mul_apply, P.inner_map_left, ← star_def, hsa.star_eq, ← h x y]

theorem inner_map_self_eq_of_isStarProjection {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x : E) :
    inner A (P x) (P x) = inner A x (P x) := by
  calc inner A (P x) (P x) = inner A (P x) x := (isStarProjection_iff_forall_inner.mp hP x x).symm
    _ = inner A x (P.adjoint x) := P.inner_map_left x x
    _ = inner A x (P x) := by rw [← star_def, hP.isSelfAdjoint.star_eq]

theorem inner_map_one_sub_eq_zero_of_isStarProjection {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x y : E) :
    inner A (P x) ((1 - P) y) = 0 := by
  have hzero : inner A x (0 : E) = 0 := by
    simpa using CStarModule.inner_add_right (A := A) (x := x) (y := (0 : E)) (z := 0)
  calc inner A (P x) ((1 - P) y)
      = inner A x ((P.adjoint * (1 - P)) y) := P.inner_map_left x ((1 - P) y)
    _ = inner A x ((P * (1 - P)) y) := by rw [← star_def, hP.isSelfAdjoint.star_eq]
    _ = inner A x ((0 : AdjointableMap A E E) y) := by rw [hP.mul_one_sub_self]
    _ = 0 := by rw [zero_apply, hzero]

/-- Orthogonal decomposition of the module inner product under an adjointable projection `P`:
`⟪P x, P x⟫_A + ⟪(1 - P) x, (1 - P) x⟫_A = ⟪x, x⟫_A`. -/
theorem inner_self_eq_add_of_isStarProjection {P : AdjointableMap A E E}
    (hP : IsStarProjection P) (x : E) :
    inner A (P x) (P x) + inner A ((1 - P) x) ((1 - P) x) = inner A x x := by
  rw [inner_map_self_eq_of_isStarProjection hP x,
    inner_map_self_eq_of_isStarProjection hP.one_sub x, ← CStarModule.inner_add_right,
    ← add_apply, add_sub_cancel, one_apply]

theorem mul_eq_right_iff_range_subset_of_isIdempotentElem {P Q : AdjointableMap A E E}
    (hQ : IsIdempotentElem Q) :
    Q * P = P ↔ Set.range P ⊆ Set.range Q := by
  refine ⟨fun h => ?_, fun h => ext fun x => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨P x, by rw [← mul_apply, h]⟩
  · obtain ⟨z, hz⟩ := h ⟨x, rfl⟩
    rw [mul_apply, ← hz, ← mul_apply, hQ.eq]

/-- Two adjointable orthogonal projections with the same range are equal. -/
theorem eq_of_isStarProjection_of_range_eq {P Q : AdjointableMap A E E}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : Set.range P = Set.range Q) :
    P = Q := by
  have hQP : Q * P = P :=
    (mul_eq_right_iff_range_subset_of_isIdempotentElem hQ.isIdempotentElem).mpr h.le
  have hPQ : P * Q = Q :=
    (mul_eq_right_iff_range_subset_of_isIdempotentElem hP.isIdempotentElem).mpr h.ge
  calc P = star P := hP.isSelfAdjoint.star_eq.symm
    _ = star (Q * P) := by rw [hQP]
    _ = star P * star Q := star_mul Q P
    _ = P * Q := by rw [hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq]
    _ = Q := hPQ

theorem isStarProjection_eq_iff_range_eq {P Q : AdjointableMap A E E}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    P = Q ↔ Set.range P = Set.range Q :=
  ⟨fun h => h ▸ rfl, eq_of_isStarProjection_of_range_eq hP hQ⟩

end Projections

section ProjectionOrder

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [CompleteSpace E]

/-- On a complete Hilbert C⋆-module, the spectral order on adjointable orthogonal projections agrees
with range inclusion. -/
theorem isStarProjection_le_iff_range_subset {P Q : AdjointableMap A E E}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    P ≤ Q ↔ Set.range P ⊆ Set.range Q :=
  (hP.le_iff_mul_eq_right hQ).trans
    (mul_eq_right_iff_range_subset_of_isIdempotentElem hQ.isIdempotentElem)

end ProjectionOrder

section Isometries

variable {A E F : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- An adjointable operator `T` satisfies `T* ∘ T = id` if and only if it preserves the module inner
product: `⟪T x, T y⟫_A = ⟪x, y⟫_A` for all `x, y : E`. -/
theorem adjoint_comp_self_eq_id_iff {T : AdjointableMap A E F} :
    T.adjoint.comp T = .id ↔ ∀ x y : E, inner A (T x) (T y) = inner A x y := by
  refine ⟨fun h x y => ?_, fun h => ext_inner_left fun x y => ?_⟩
  · rw [T.inner_map_left, ← comp_apply, h, id_apply]
  · rw [comp_apply, ← T.inner_map_left, h, id_apply]

theorem norm_map_of_adjoint_comp_self_eq_id {T : AdjointableMap A E F}
    (hT : T.adjoint.comp T = .id) (x : E) : ‖T x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (T x),
    CStarModule.norm_eq_sqrt_norm_inner_self (A := A) x,
    adjoint_comp_self_eq_id_iff.mp hT x x]

/-- Convert an adjointable isometry `T` (`T* ∘ T = id`) to a `ℂ`-linear isometry `E →ₗᵢ[ℂ] F`. -/
def toLinearIsometryOfAdjointCompSelfEqId {T : AdjointableMap A E F}
    (hT : T.adjoint.comp T = .id) : E →ₗᵢ[ℂ] F where
  toLinearMap := T.toContinuousLinearMap.toLinearMap
  norm_map' := norm_map_of_adjoint_comp_self_eq_id hT

@[simp]
theorem toLinearIsometryOfAdjointCompSelfEqId_apply {T : AdjointableMap A E F}
    (hT : T.adjoint.comp T = .id) (x : E) :
    toLinearIsometryOfAdjointCompSelfEqId hT x = T x := (rfl)

theorem isometry_of_adjoint_comp_self_eq_id {T : AdjointableMap A E F}
    (hT : T.adjoint.comp T = .id) : Isometry T :=
  (toLinearIsometryOfAdjointCompSelfEqId hT).isometry

/-- For an adjointable isometry `T` (`T* ∘ T = id`), the range projection `T ∘ T*` is an orthogonal
projection in `AdjointableMap A F F`. -/
theorem isStarProjection_comp_adjoint_self {T : AdjointableMap A E F}
    (hT : T.adjoint.comp T = .id) : IsStarProjection (T.comp T.adjoint) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, mul_def, comp_assoc, ← comp_assoc T.adjoint T T.adjoint, hT, id_comp]
  · rw [IsSelfAdjoint, star_def, adjoint_comp, adjoint_adjoint]

end Isometries

section IsometriesPolarization

variable {A E F : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- Over `ℂ`, an adjointable operator `T` satisfies `T* ∘ T = id` if and only if it preserves
diagonal module inner products `⟪T x, T x⟫_A = ⟪x, x⟫_A` for all `x : E`. -/
theorem adjoint_comp_self_eq_id_iff_diag {T : AdjointableMap A E F} :
    T.adjoint.comp T = .id ↔ ∀ x : E, inner A (T x) (T x) = inner A x x := by
  rw [eq_iff_forall_inner_self]
  refine forall_congr' fun x => ?_
  rw [comp_apply, ← T.inner_map_left, id_apply]

end IsometriesPolarization

end AdjointableMap

end TauCeti
