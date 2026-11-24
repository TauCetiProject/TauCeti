/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Compact
public import TauCeti.Analysis.CStarAlgebra.Module.Self
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Basic

/-!
# Adjointable and module-compact operators on the right self-module

A C⋆-algebra `A` is a right Hilbert module over itself (`CStarModule.instMulOpposite`), with right
action `x b = x * b` and inner product `⟨x, y⟩_A = star x * y`. This file identifies its
module-compact operators `K_A(A)` with `A` and its adjointable operators `L_A(A)` with the
multiplier algebra `𝓜(ℂ, A)`.

Left multiplication `L_a : x ↦ a * x` is adjointable with adjoint `L_{star a}`, and `a ↦ L_a` is an
isometric `⋆`-homomorphism `A →⋆ₙₐ[ℂ] L_A(A)`. The rank-one operator `θ_{a,b} : x ↦ a ⟨b, x⟩_A` is
`L_{a * star b}`. Since `a * e → a` along an approximate unit `e` of `A`, every `L_a` is a limit
of rank-one operators, and conversely the range of the isometry `a ↦ L_a` is closed and contains
every rank-one operator. Hence `K_A(A)` is exactly the range of `a ↦ L_a`, which gives the
`⋆`-isomorphism `A ≃⋆ₐ[ℂ] K_A(A)`.

The adjoint of an adjointable operator `T` satisfies `star (T* x) * y = star x * T y`. Thus
`(T, star ∘ T* ∘ star)` is a double centralizer of `A`; conversely the left centralizer `L` of a
double centralizer `(L, R)` is adjointable, with adjoint the left centralizer `star ∘ R ∘ star` of
its star. This gives the isometric `⋆`-isomorphism
`L_A(A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A)`, which sends `L_a` to the canonical image of `a` in `𝓜(ℂ, A)`.
Under it, `K_A(A)` corresponds to the image of `A` in its multiplier algebra.

No unit in `A` is assumed. For unital `A`, `L_1` is the identity, which is therefore
module-compact.

## Main declarations

* `TauCeti.AdjointableMap.mulLeft A a`: left multiplication by `a` as an adjointable operator on
  the right self-module, with adjoint `mulLeft A (star a)` (`adjoint_mulLeft`) and norm `‖a‖`
  (`norm_mulLeft`).
* `TauCeti.AdjointableMap.mulLeftStarHom A`: the isometric `⋆`-homomorphism `a ↦ L_a`.
* `TauCeti.AdjointableMap.rankOne_eq_mulLeft`: `θ_{a,b} = L_{a * star b}`.
* `TauCeti.AdjointableMap.mem_compactOperator_mulOpposite_iff`: an adjointable operator on the
  right self-module is module-compact iff it is a left multiplication.
* `TauCeti.AdjointableMap.compactOperatorMulOppositeStarAlgEquiv A`: the `⋆`-isomorphism
  `A ≃⋆ₐ[ℂ] K_A(A)`, `a ↦ L_a`.
* `TauCeti.AdjointableMap.multiplierMulOppositeStarAlgEquiv A`: the `⋆`-isomorphism
  `L_A(A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A)`, `T ↦ (T, star ∘ T* ∘ star)`, isometric by
  `norm_multiplierMulOppositeStarAlgEquiv`.
* `TauCeti.AdjointableMap.multiplierMulOppositeStarAlgEquiv_mulLeft`: it sends `L_a` to
  `(a : 𝓜(ℂ, A))`.

## References

* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Section 2.2 and Corollary 2.54.
* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 2.
-/

public section

open MulOpposite Filter Topology
open scoped MultiplierAlgebra

namespace TauCeti

namespace AdjointableMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ### Left multiplications -/

section MulLeft

variable (A) in
/-- Left multiplication `x ↦ a * x` as an adjointable operator on the right self-module of `A`,
with adjoint `x ↦ star a * x`. -/
noncomputable def mulLeft (a : A) : AdjointableMap Aᵐᵒᵖ A A where
  toContinuousLinearMap := ContinuousLinearMap.mul ℂ A a
  adjoint' := ContinuousLinearMap.mul ℂ A (star a)
  inner_map_eq' x y := by simp [CStarModule.inner_mulOpposite, mul_assoc]

@[simp]
theorem mulLeft_apply (a x : A) : mulLeft A a x = a * x :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_mulLeft (a : A) :
    (mulLeft A a).toContinuousLinearMap = ContinuousLinearMap.mul ℂ A a :=
  (rfl)

/-- The adjoint of left multiplication by `a` is left multiplication by `star a`. -/
@[simp]
theorem adjoint_mulLeft (a : A) : (mulLeft A a).adjoint = mulLeft A (star a) :=
  -- The adjoint field of `mulLeft A a` is by construction the map underlying `mulLeft A (star a)`.
  ext fun x ↦ adjoint_mk_apply _ _ _ x

/-- Left multiplication by `a` on the right self-module has operator norm `‖a‖`. -/
@[simp]
theorem norm_mulLeft (a : A) : ‖mulLeft A a‖ = ‖a‖ :=
  ContinuousLinearMap.opNorm_mul_apply ℂ A a

variable (A) in
/-- The `⋆`-homomorphism `a ↦ L_a` from `A` into the adjointable operators on its right
self-module. It is isometric (`isometry_mulLeftStarHom`). -/
noncomputable def mulLeftStarHom : A →⋆ₙₐ[ℂ] AdjointableMap Aᵐᵒᵖ A A where
  toFun := mulLeft A
  map_smul' c a := ext fun x ↦ smul_mul_assoc c a x
  map_zero' := ext fun x ↦ zero_mul x
  map_add' a b := ext fun x ↦ add_mul a b x
  map_mul' a b := ext fun x ↦ by simp [mul_def, mul_assoc]
  map_star' a := (adjoint_mulLeft a).symm

@[simp]
theorem mulLeftStarHom_apply (a : A) : mulLeftStarHom A a = mulLeft A a :=
  (rfl)

theorem coe_mulLeftStarHom : ⇑(mulLeftStarHom A) = mulLeft A :=
  (rfl)

@[simp]
theorem mulLeft_zero : mulLeft A 0 = 0 := by
  simpa only [mulLeftStarHom_apply] using map_zero (mulLeftStarHom A)

@[simp]
theorem mulLeft_add (a b : A) : mulLeft A (a + b) = mulLeft A a + mulLeft A b := by
  simpa only [mulLeftStarHom_apply] using map_add (mulLeftStarHom A) a b

@[simp]
theorem mulLeft_smul (c : ℂ) (a : A) : mulLeft A (c • a) = c • mulLeft A a := by
  simpa only [mulLeftStarHom_apply] using map_smul (mulLeftStarHom A) c a

@[simp]
theorem mulLeft_mul (a b : A) : mulLeft A (a * b) = mulLeft A a * mulLeft A b := by
  simpa only [mulLeftStarHom_apply] using map_mul (mulLeftStarHom A) a b

@[simp]
theorem star_mulLeft (a : A) : star (mulLeft A a) = mulLeft A (star a) := by
  simpa only [mulLeftStarHom_apply] using (map_star (mulLeftStarHom A) a).symm

theorem isometry_mulLeftStarHom : Isometry (mulLeftStarHom A) :=
  AddMonoidHomClass.isometry_of_norm _ norm_mulLeft

theorem mulLeft_injective : Function.Injective (mulLeft A) :=
  (isometry_mulLeftStarHom (A := A)).injective

@[simp]
theorem mulLeft_inj {a b : A} : mulLeft A a = mulLeft A b ↔ a = b :=
  mulLeft_injective.eq_iff

theorem continuous_mulLeft : Continuous (mulLeft A) :=
  (isometry_mulLeftStarHom (A := A)).continuous

/-- The range of `a ↦ L_a` is norm-closed in `L_A(A)`. -/
theorem isClosed_range_mulLeft : IsClosed (Set.range (mulLeft A)) :=
  (isometry_mulLeftStarHom (A := A)).isClosedEmbedding.isClosed_range

/-- For unital `A`, left multiplication by `1` is the identity operator. -/
@[simp]
theorem mulLeft_one {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    mulLeft A 1 = 1 :=
  ext fun x ↦ by simp [one_def]

end MulLeft

/-! ### Module-compact operators on the right self-module -/

section Compact

/-- On the right self-module, the rank-one operator `θ_{a,b} : x ↦ a ⟨b, x⟩_A` is left
multiplication by `a * star b`. -/
theorem rankOne_eq_mulLeft (a b : A) : rankOne Aᵐᵒᵖ a b = mulLeft A (a * star b) :=
  ext fun x ↦ by simp [MulOpposite.smul_eq_mul_unop]

/-- Every left multiplication on the right self-module is module-compact: it is the limit of the
rank-one operators `θ_{a,e} = L_{a * e}` along an increasing approximate unit `e` of `A`. -/
theorem mulLeft_mem_compactOperator (a : A) : mulLeft A a ∈ compactOperator Aᵐᵒᵖ A A := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  refine isClosed_compactOperator.mem_of_tendsto
    (continuous_mulLeft.continuousAt.tendsto.comp (hl.tendsto_mul_left a)) ?_
  filter_upwards [hl.eventually_star_eq] with e he
  have h := rankOne_mem_compactOperator (A := Aᵐᵒᵖ) a e
  rwa [rankOne_eq_mulLeft, he] at h

/-- An adjointable operator on the right self-module of `A` is module-compact if and only if it is
left multiplication by an element of `A`. -/
theorem mem_compactOperator_mulOpposite_iff {T : AdjointableMap Aᵐᵒᵖ A A} :
    T ∈ compactOperator Aᵐᵒᵖ A A ↔ ∃ a : A, mulLeft A a = T := by
  refine ⟨fun hT ↦ ?_, fun ⟨a, ha⟩ ↦ ha ▸ mulLeft_mem_compactOperator a⟩
  -- The range of `a ↦ L_a` is a closed subspace containing every rank-one operator.
  have hle := (compactOperator_le_iff (p := LinearMap.range (LinearMap.ofClass (mulLeftStarHom A)))
    (by rw [LinearMap.coe_range, LinearMap.coe_ofClass, coe_mulLeftStarHom]
        exact isClosed_range_mulLeft)).mpr
      fun a b ↦ ⟨a * star b, by simp [rankOne_eq_mulLeft]⟩
  obtain ⟨a, rfl⟩ := hle hT
  exact ⟨a, by simp⟩

/-- The module-compact operators on the right self-module of `A` are exactly the left
multiplications. -/
theorem coe_compactOperator_mulOpposite :
    (compactOperator Aᵐᵒᵖ A A : Set (AdjointableMap Aᵐᵒᵖ A A)) = Set.range (mulLeft A) :=
  Set.ext fun _ ↦ mem_compactOperator_mulOpposite_iff

variable (A) in
/-- The `⋆`-isomorphism `A ≃⋆ₐ[ℂ] K_A(A)`, `a ↦ L_a`, between a C⋆-algebra and the module-compact
operators on its right self-module. -/
noncomputable def compactOperatorMulOppositeStarAlgEquiv :
    A ≃⋆ₐ[ℂ] compactOperatorIdeal Aᵐᵒᵖ A :=
  (StarAlgEquiv.ofBijective
    ((mulLeftStarHom A).codRestrict (compactOperatorIdeal Aᵐᵒᵖ A).toNonUnitalStarSubalgebra
      fun a ↦ (TwoSidedIdeal.mem_toNonUnitalStarSubalgebra _).mpr <|
        mem_compactOperatorIdeal.mpr (mulLeft_mem_compactOperator a))
    ⟨fun _ _ h ↦ mulLeft_injective (congrArg Subtype.val h), fun T ↦ by
      obtain ⟨a, ha⟩ := mem_compactOperator_mulOpposite_iff.mp <| mem_compactOperatorIdeal.mp <|
        (TwoSidedIdeal.mem_toNonUnitalStarSubalgebra _).mp T.property
      exact ⟨a, Subtype.ext ha⟩⟩).trans
    (compactOperatorIdeal Aᵐᵒᵖ A).toNonUnitalStarSubalgebraEquiv.symm

@[simp]
theorem coe_compactOperatorMulOppositeStarAlgEquiv_apply (a : A) :
    (compactOperatorMulOppositeStarAlgEquiv A a : AdjointableMap Aᵐᵒᵖ A A) = mulLeft A a :=
  TwoSidedIdeal.coe_toNonUnitalStarSubalgebraEquiv_symm_apply _ _

/-- The inverse of `compactOperatorMulOppositeStarAlgEquiv` sends `θ_{a,b}` to `a * star b`. -/
@[simp]
theorem compactOperatorMulOppositeStarAlgEquiv_symm_rankOne (a b : A) :
    (compactOperatorMulOppositeStarAlgEquiv A).symm
        ⟨rankOne Aᵐᵒᵖ a b, mem_compactOperatorIdeal.mpr (rankOne_mem_compactOperator a b)⟩ =
      a * star b :=
  (StarAlgEquiv.symm_apply_eq _).mpr <| Subtype.ext <|
    (rankOne_eq_mulLeft a b).trans (coe_compactOperatorMulOppositeStarAlgEquiv_apply _).symm

/-- Left multiplication by the preimage of a module-compact operator `T` under
`compactOperatorMulOppositeStarAlgEquiv` is `T`. -/
@[simp]
theorem mulLeft_compactOperatorMulOppositeStarAlgEquiv_symm (T : compactOperatorIdeal Aᵐᵒᵖ A) :
    mulLeft A ((compactOperatorMulOppositeStarAlgEquiv A).symm T) = T := by
  rw [← coe_compactOperatorMulOppositeStarAlgEquiv_apply, StarAlgEquiv.apply_symm_apply]

/-- The `⋆`-isomorphism `A ≃⋆ₐ[ℂ] K_A(A)` is isometric. -/
theorem norm_compactOperatorMulOppositeStarAlgEquiv (a : A) :
    ‖compactOperatorMulOppositeStarAlgEquiv A a‖ = ‖a‖ :=
  (congrArg norm (coe_compactOperatorMulOppositeStarAlgEquiv_apply a)).trans (norm_mulLeft a)

end Compact

/-! ### Adjointable operators on the right self-module and multipliers -/

section Multiplier

/-- The adjoint identity on the right self-module: `star (T* x) * y = star x * T y`. -/
theorem star_adjoint_apply_mul (T : AdjointableMap Aᵐᵒᵖ A A) (x y : A) :
    star (T.adjoint x) * y = star x * T y := by
  simpa using congrArg unop (T.adjoint_inner_left y x)

variable (A) in
/-- The `⋆`-isomorphism `L_A(A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A)` between the adjointable operators on the right
self-module of `A` and its multiplier algebra. It sends `T` to the double centralizer
`(T, star ∘ T* ∘ star)`; the inverse sends `(L, R)` to `L`, whose adjoint is `star ∘ R ∘ star`.
It is isometric (`norm_multiplierMulOppositeStarAlgEquiv`). -/
noncomputable def multiplierMulOppositeStarAlgEquiv :
    AdjointableMap Aᵐᵒᵖ A A ≃⋆ₐ[ℂ] 𝓜(ℂ, A) where
  toFun T := .ofAdjoint T.toContinuousLinearMap T.adjoint.toContinuousLinearMap
    T.star_adjoint_apply_mul
  invFun m :=
    { toContinuousLinearMap := m.fst
      adjoint' := (star m).fst
      inner_map_eq' x y := by
        have h := congrArg star (m.central (star y) x)
        simp only [star_mul, star_star] at h
        simp [CStarModule.inner_mulOpposite, h] }
  left_inv T := ext fun _ ↦ by simp
  right_inv m := DoubleCentralizer.ext_fst fun _ ↦ by simp
  map_mul' S T := DoubleCentralizer.ext_fst fun _ ↦ by simp
  map_add' S T := DoubleCentralizer.ext_fst fun _ ↦ by simp
  map_smul' c T := DoubleCentralizer.ext_fst fun _ ↦ by simp
  map_star' T := DoubleCentralizer.ext_fst fun _ ↦ by simp [star_eq_adjoint]

@[simp]
theorem multiplierMulOppositeStarAlgEquiv_fst (T : AdjointableMap Aᵐᵒᵖ A A) :
    (multiplierMulOppositeStarAlgEquiv A T).fst = T.toContinuousLinearMap :=
  DoubleCentralizer.ofAdjoint_fst

@[simp]
theorem multiplierMulOppositeStarAlgEquiv_snd_apply (T : AdjointableMap Aᵐᵒᵖ A A) (x : A) :
    (multiplierMulOppositeStarAlgEquiv A T).snd x = star (T.adjoint (star x)) :=
  DoubleCentralizer.ofAdjoint_snd_apply x

@[simp]
theorem multiplierMulOppositeStarAlgEquiv_symm_apply (m : 𝓜(ℂ, A)) (x : A) :
    (multiplierMulOppositeStarAlgEquiv A).symm m x = m.fst x :=
  (rfl)

/-- The adjoint of the adjointable operator corresponding to a double centralizer `(L, R)` is
`star ∘ R ∘ star`. -/
@[simp]
theorem adjoint_multiplierMulOppositeStarAlgEquiv_symm_apply (m : 𝓜(ℂ, A)) (x : A) :
    ((multiplierMulOppositeStarAlgEquiv A).symm m).adjoint x = star (m.snd (star x)) :=
  -- The adjoint field of the inverse is by construction `(star m).fst`.
  adjoint_mk_apply _ _ _ x

/-- The `⋆`-isomorphism `L_A(A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A)` is isometric. -/
@[simp]
theorem norm_multiplierMulOppositeStarAlgEquiv (T : AdjointableMap Aᵐᵒᵖ A A) :
    ‖multiplierMulOppositeStarAlgEquiv A T‖ = ‖T‖ := by
  rw [← DoubleCentralizer.norm_fst, multiplierMulOppositeStarAlgEquiv_fst,
    norm_toContinuousLinearMap]

/-- `L_A(A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A)` sends left multiplication by `a` to the canonical image of `a`. -/
@[simp]
theorem multiplierMulOppositeStarAlgEquiv_mulLeft (a : A) :
    multiplierMulOppositeStarAlgEquiv A (mulLeft A a) = (a : 𝓜(ℂ, A)) :=
  DoubleCentralizer.ext_fst fun _ ↦ by simp

/-- Under `L_A(A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A)`, the module-compact operators `K_A(A)` correspond to the image
of `A` in its multiplier algebra. -/
theorem mem_compactOperator_mulOpposite_iff_multiplierMulOppositeStarAlgEquiv
    {T : AdjointableMap Aᵐᵒᵖ A A} :
    T ∈ compactOperator Aᵐᵒᵖ A A ↔
      ∃ a : A, (a : 𝓜(ℂ, A)) = multiplierMulOppositeStarAlgEquiv A T := by
  simp_rw [mem_compactOperator_mulOpposite_iff, ← multiplierMulOppositeStarAlgEquiv_mulLeft,
    EmbeddingLike.apply_eq_iff_eq]

end Multiplier

end AdjointableMap

end TauCeti
