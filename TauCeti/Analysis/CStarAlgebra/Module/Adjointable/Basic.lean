/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair

/-!
# Algebraic theory of adjointable operators on Hilbert C⋆-modules

For Hilbert C⋆-modules `E` and `F` over a C⋆-algebra `A` (with right Hilbert `B`-modules
represented as `CStarModule Bᵐᵒᵖ E` and `CStarModule Bᵐᵒᵖ F`), a bounded `ℂ`-linear map
`T : E →L[ℂ] F` is *adjointable* if there exists `T* : F →L[ℂ] E` such that
`⟪T x, y⟫_A = ⟪x, T* y⟫_A` for all `x : E` and `y : F`.

This file defines the plain-function predicate `CStarModule.IsAdjointable` and the bundled space
`TauCeti.AdjointableMap A E F`, and develops its algebraic structure:

* Nondegeneracy of the module inner product makes the adjoint unique, giving vector extensionality
  (`AdjointableMap.ext`, `AdjointableMap.ext_inner_left`, `AdjointableMap.ext_inner_right`) and
  automatic `A`-linearity (`AdjointableMap.map_smul_coeff`).
* `AdjointableMap A E F` carries additive group and `ℂ`-module structures, composition
  `AdjointableMap.comp` with `(S.comp T).adjoint = T.adjoint.comp S.adjoint`, and a conjugate-linear
  involution `AdjointableMap.adjointLinearEquiv`.
* Endomorphisms `AdjointableMap A E E` form a unital `⋆`-ring and `ℂ`-algebra acting faithfully on
  `E` commuting with both `ℂ` and `A`, with diagonal polarization
  (`AdjointableMap.isSelfAdjoint_iff`).

The operator norm, completeness, C⋆-algebra structure, positivity, modulus, projections, and
isometries are developed in `TauCeti.Analysis.CStarAlgebra.Module.Adjointable`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2 (Definitions 2.16–2.17).
* Bruce Blackadar, *Operator Algebras*, Section II.7.1.
* The paired-continuous-linear-map design of `AdjointableMap`, the ring pullback via
  `Function.Injective.ring`, and `AdjointableMap.instPowNat` adapt `DoubleCentralizer` in
  `Mathlib.Analysis.CStarAlgebra.Multiplier`.
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
theorem isAdjointable_zero : IsAdjointable A (0 : E → F) :=
  ⟨0, fun _ _ => by simp⟩

theorem IsAdjointable.add {T₁ T₂ : E → F} (h₁ : IsAdjointable A T₁) (h₂ : IsAdjointable A T₂) :
    IsAdjointable A (T₁ + T₂) :=
  let ⟨S₁, h₁⟩ := h₁; let ⟨S₂, h₂⟩ := h₂
  ⟨S₁ + S₂, fun x y => by simp [h₁ x y, h₂ x y]⟩

theorem IsAdjointable.neg {T : E → F} (h : IsAdjointable A T) : IsAdjointable A (-T) :=
  let ⟨S, h⟩ := h
  ⟨-S, fun x y => by simp only [Pi.neg_apply, inner_neg_left', inner_neg_right', h x y]⟩

theorem IsAdjointable.sub {T₁ T₂ : E → F} (h₁ : IsAdjointable A T₁) (h₂ : IsAdjointable A T₂) :
    IsAdjointable A (T₁ - T₂) :=
  sub_eq_add_neg T₁ T₂ ▸ h₁.add h₂.neg

theorem IsAdjointable.map_add {T : E → F} (h : IsAdjointable A T) (x y : E) :
    T (x + y) = T x + T y :=
  let ⟨_, h⟩ := h
  CStarModule.ext_inner_right (A := A) fun z => by
    rw [h (x + y) z, CStarModule.inner_add_left, ← h x z, ← h y z, ← CStarModule.inner_add_left]

theorem IsAdjointable.map_smul {T : E → F} (h : IsAdjointable A T) (c : ℂ) (x : E) :
    T (c • x) = c • T x :=
  let ⟨S, h⟩ := h
  CStarModule.ext_inner_left (A := A) fun z => by
    rw [← CStarModule.star_inner, h (c • x) z, CStarModule.star_inner,
      CStarModule.inner_smul_right_complex, ← CStarModule.star_inner x (S z), ← h x z,
      CStarModule.star_inner, ← CStarModule.inner_smul_right_complex]

theorem IsAdjointable.map_smul_coeff {T : E → F} (h : IsAdjointable A T) (a : A) (x : E) :
    T (a • x) = a • T x :=
  let ⟨_, h⟩ := h
  CStarModule.ext_inner_right (A := A) fun z => by
    rw [h (a • x) z, CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_left, ← h x z]

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
    IsAdjointable A (c • T) :=
  let ⟨S, h⟩ := h
  ⟨star c • S, fun x y => by simp [h x y]⟩

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
    T.adjointContinuousLinearMap = S.adjointContinuousLinearMap :=
  ContinuousLinearMap.ext fun y => CStarModule.ext_inner_left (A := A) fun x => by
    rw [← T.inner_map_eq', ← S.inner_map_eq', h]

/-- The forgetful map to `E →L[ℂ] F` is injective: the adjoint is uniquely determined by the
forward operator. -/
theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : AdjointableMap A E F → E →L[ℂ] F) := by
  rintro ⟨f₁, g₁, h₁⟩ ⟨f₂, g₂, h₂⟩ (rfl : f₁ = f₂)
  congr
  exact adjointContinuousLinearMap_eq_of_toContinuousLinearMap_eq (T := ⟨f₁, g₁, h₁⟩)
    (S := ⟨f₁, g₂, h₂⟩) rfl

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
    (h : ∀ y x, inner A y (T x) = inner A y (S x)) : T = S :=
  ext fun x => CStarModule.ext_inner_left (A := A) fun y => h y x

/-- Two adjointable operators are equal if their inner products against all vectors on the right
agree. -/
theorem ext_inner_right {T S : AdjointableMap A E F}
    (h : ∀ x y, inner A (T x) y = inner A (S x) y) : T = S :=
  ext_inner_left fun y x => by rw [← CStarModule.star_inner, h x y, CStarModule.star_inner]

@[simp]
theorem coe_mk (f : E →L[ℂ] F) (g : F →L[ℂ] E) (h) :
    ⇑(mk f g h : AdjointableMap A E F) = ⇑f := (rfl)

@[simp]
theorem toContinuousLinearMap_mk (f : E →L[ℂ] F) (g : F →L[ℂ] E) (h) :
    (mk f g h : AdjointableMap A E F).toContinuousLinearMap = f := (rfl)

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

theorem toContinuousLinearMap_adjoint (T : AdjointableMap A E F) :
    T.adjoint.toContinuousLinearMap = T.adjointContinuousLinearMap := (rfl)

@[simp]
theorem adjointContinuousLinearMap_eq_toContinuousLinearMap_adjoint (T : AdjointableMap A E F) :
    T.adjointContinuousLinearMap = T.adjoint.toContinuousLinearMap := (rfl)

@[simp]
theorem toContinuousLinearMap_adjoint_mk (f : E →L[ℂ] F) (g : F →L[ℂ] E) (h) :
    (mk f g h : AdjointableMap A E F).adjoint.toContinuousLinearMap = g := (rfl)

@[simp]
theorem coe_adjoint_mk (f : E →L[ℂ] F) (g : F →L[ℂ] E) (h) :
    ⇑(mk f g h : AdjointableMap A E F).adjoint = ⇑g := (rfl)

theorem adjointContinuousLinearMap_adjoint (T : AdjointableMap A E F) :
    T.adjoint.adjointContinuousLinearMap = T.toContinuousLinearMap := (rfl)

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
theorem adjoint_adjoint (T : AdjointableMap A E F) : T.adjoint.adjoint = T := ext fun _ => rfl

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
    T (a • x) = a • T x :=
  T.isAdjointable.map_smul_coeff a x

/-! #### Additive group structure -/

instance instZero : Zero (AdjointableMap A E F) where
  zero :=
    { toContinuousLinearMap := 0
      adjointContinuousLinearMap := 0
      inner_map_eq' _ _ := by simp }

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
        rw [neg_apply, neg_apply, CStarModule.inner_neg_left', CStarModule.inner_neg_right',
          T.inner_map_eq'] }

instance instSub : Sub (AdjointableMap A E F) where
  sub T S := T + -S

instance instSMulNat : SMul ℕ (AdjointableMap A E F) where
  smul n T :=
    { toContinuousLinearMap := n • T.toContinuousLinearMap
      adjointContinuousLinearMap := n • T.adjointContinuousLinearMap
      inner_map_eq' x y := by
        induction n with
        | zero => simp
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
theorem add_apply (T S : AdjointableMap A E F) (x : E) : (T + S) x = T x + S x := (rfl)

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
theorem adjoint_zero : (0 : AdjointableMap A E F).adjoint = 0 := ext fun _ => rfl

@[simp]
theorem adjoint_add (T S : AdjointableMap A E F) :
    (T + S).adjoint = T.adjoint + S.adjoint := ext fun _ => rfl

@[simp]
theorem adjoint_neg (T : AdjointableMap A E F) : (-T).adjoint = -T.adjoint := ext fun _ => rfl

@[simp]
theorem adjoint_sub (T S : AdjointableMap A E F) :
    (T - S).adjoint = T.adjoint - S.adjoint := by simp [sub_eq_add_neg]

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
    (AdjointableMap.id : AdjointableMap A E E).adjoint = AdjointableMap.id := ext fun _ => rfl

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
    (S.comp T).adjoint = T.adjoint.comp S.adjoint := ext fun _ => rfl

@[simp]
theorem id_comp (T : AdjointableMap A E F) : AdjointableMap.id.comp T = T := ext fun _ => rfl

@[simp]
theorem comp_id (T : AdjointableMap A E F) : T.comp AdjointableMap.id = T := ext fun _ => rfl

@[simp]
theorem zero_comp (T : AdjointableMap A E F) :
    (0 : AdjointableMap A F G).comp T = 0 := ext fun _ => rfl

@[simp]
theorem comp_zero (S : AdjointableMap A F G) :
    S.comp (0 : AdjointableMap A E F) = 0 := ext fun _ => map_zero S

theorem add_comp (S₁ S₂ : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (S₁ + S₂).comp T = S₁.comp T + S₂.comp T := ext fun _ => rfl

theorem comp_add (S : AdjointableMap A F G) (T₁ T₂ : AdjointableMap A E F) :
    S.comp (T₁ + T₂) = S.comp T₁ + S.comp T₂ := ext fun x => map_add S (T₁ x) (T₂ x)

@[simp]
theorem neg_comp (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (-S).comp T = -(S.comp T) := ext fun _ => rfl

@[simp]
theorem comp_neg (S : AdjointableMap A F G) (T : AdjointableMap A E F) :
    S.comp (-T) = -(S.comp T) := ext fun x => map_neg S (T x)

theorem sub_comp (S₁ S₂ : AdjointableMap A F G) (T : AdjointableMap A E F) :
    (S₁ - S₂).comp T = S₁.comp T - S₂.comp T := ext fun _ => rfl

theorem comp_sub (S : AdjointableMap A F G) (T₁ T₂ : AdjointableMap A E F) :
    S.comp (T₁ - T₂) = S.comp T₁ - S.comp T₂ := by ext x; simp

theorem comp_assoc (R : AdjointableMap A G H) (S : AdjointableMap A F G)
    (T : AdjointableMap A E F) :
    (R.comp S).comp T = R.comp (S.comp T) := ext fun _ => rfl

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

/-- The underlying continuous linear maps of an adjointable operator and its adjoint form a
`LinearMap.IsAdjointPair`. -/
theorem isAdjointPair_toContinuousLinearMap (T : AdjointableMap A E F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T.toContinuousLinearMap
      T.adjoint.toContinuousLinearMap :=
  CStarModule.isAdjointPair_inner_iff.mpr fun x y => by
    rw [toContinuousLinearMap_apply, toContinuousLinearMap_apply, T.inner_map_left]

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
theorem smul_apply (c : ℂ) (T : AdjointableMap A E F) (x : E) : (c • T) x = c • T x := (rfl)

@[simp]
theorem adjoint_smul (c : ℂ) (T : AdjointableMap A E F) :
    (c • T).adjoint = star c • T.adjoint := ext fun _ => rfl

instance instModuleComplex : Module ℂ (AdjointableMap A E F) :=
  fast_instance% Function.Injective.module ℂ toContinuousLinearMapAddMonoidHom
    (fun _ _ h => toContinuousLinearMap_injective <| by
      simpa only [toContinuousLinearMapAddMonoidHom_apply] using h)
    (fun c T => by
      simp only [toContinuousLinearMapAddMonoidHom_apply, toContinuousLinearMap_smul])

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
    (c • S).comp T = c • S.comp T := ext fun _ => rfl

@[simp]
theorem comp_smul (S : AdjointableMap A F G) (c : ℂ) (T : AdjointableMap A E F) :
    S.comp (c • T) = c • S.comp T := ext fun x => map_smul S c (T x)

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
instance applyModule : Module (AdjointableMap A E E) E :=
  Module.compHom E toContinuousLinearMapRingHom

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

instance instAlgebraComplex : Algebra ℂ (AdjointableMap A E E) :=
  Algebra.ofModule (fun c S T => by rw [mul_def, mul_def, smul_comp])
    (fun c S T => by rw [mul_def, mul_def, comp_smul])

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
        I • inner A (x - I • y) (T (x - I • y))) :=
  CStarModule.inner_map_polarization T x y

/-- Over `ℂ`, two adjointable endomorphisms are equal if and only if they have equal diagonal
module inner products `⟪x, T x⟫_A = ⟪x, S x⟫_A` for all `x`. -/
theorem eq_iff_forall_inner_self {T S : AdjointableMap A E E} :
    T = S ↔ ∀ x : E, inner A x (T x) = inner A x (S x) :=
  CStarModule.eq_iff_forall_inner_self

/-- Over `ℂ`, an adjointable endomorphism vanishes if and only if all of its diagonal module inner
products `⟪x, T x⟫_A` vanish. -/
theorem eq_zero_iff_forall_inner_self (T : AdjointableMap A E E) :
    T = 0 ↔ ∀ x : E, inner A x (T x) = 0 := by
  simpa [CStarModule.inner_zero_right] using
    CStarModule.eq_iff_forall_inner_self (A := A) (T := T) (S := (0 : AdjointableMap A E E))

/-- Over `ℂ`, an adjointable operator `T` is self-adjoint if and only if every diagonal inner
product `⟪x, T x⟫_A` is self-adjoint in `A`. -/
theorem isSelfAdjoint_iff (T : AdjointableMap A E E) :
    IsSelfAdjoint T ↔ ∀ x : E, IsSelfAdjoint (inner A x (T x)) := by
  rw [IsSelfAdjoint, star_def, eq_iff_forall_inner_self]
  refine forall_congr' fun x => ?_
  rw [← T.inner_map_left, ← CStarModule.star_inner, IsSelfAdjoint]

end EndAlgebra

end AdjointableMap

end TauCeti
