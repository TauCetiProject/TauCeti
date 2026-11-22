/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Action
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable

/-!
# Adjointable isometries and unitaries on Hilbert C⋆-modules

This file develops adjointable isometries (`V* ∘ V = id_E`) and unitary equivalences between
Hilbert C⋆-modules. For the algebraic adjointable-isometry API (`TauCeti.AdjointableMap`), the
bundled unitaries `TauCeti.CStarModuleUnitary`, and the constructors
`LinearMap.isometryOfInnerCStarModule` / `LinearEquiv.isometryOfInnerCStarModule`, the coefficient
ring `A` only needs to be a non-unital star ring with a compatible complex module structure, partial
order, and norm. By contrast, Lance's isometry-to-inner-product theorems require a C⋆-algebra `A`:
possibly non-unital for complex-linear isometries commuting with the `A`-action, and unital for
bundled `A`-linear or `Aᵐᵒᵖ`-linear isometries.

An adjointable operator `V : TauCeti.AdjointableMap A E F` satisfies `V* ∘ V = id_E` if and only if
it preserves all `A`-valued inner products (`adjoint_comp_self_eq_id_iff_inner_map_map`),
equivalently all diagonal inner products (`adjoint_comp_self_eq_id_iff_inner_map_map_self`); its
range is norm-closed because `V ∘ V*` is an adjointable star projection with range `Set.range V`.

For invertible equivalences, `TauCeti.CStarModuleUnitary.ofSurjective` shows that any plain
surjective function `f : E → F` preserving the `A`-valued inner product is automatically
complex-linear, `A`-linear, norm-preserving, and adjointable with inverse equal to its adjoint,
with no continuity or completeness hypotheses. Together with
`TauCeti.AdjointableMap.adjoint_comp_self_and_self_comp_adjoint_iff`, this gives Lance's unitary
characterization (Theorem 3.5): a plain function is an invertible adjointable operator whose inverse
is its adjoint if and only if it is surjective and preserves the `A`-valued inner product
(`TauCeti.AdjointableMap.exists_adjoint_comp_eq_id_iff`).

## Main definitions

* `TauCeti.CStarModuleUnitary A E F`: bundled Hilbert C⋆-module unitaries between `E` and `F`, i.e.
  complex-linear isometric equivalences `E ≃ₗᵢ[ℂ] F` preserving the `A`-valued inner product.
* `TauCeti.CStarModuleUnitary.toAdjointableMap`: views a module unitary `U` as an adjointable
  operator with `U.toAdjointableMap.adjoint = U.symm.toAdjointableMap`.
* `TauCeti.CStarModuleUnitary.conjStarAlgEquiv`: conjugation `T ↦ U ∘ T ∘ U*` as a unital
  `⋆`-algebra isomorphism `AdjointableMap A E E ≃⋆ₐ[ℂ] AdjointableMap A F F`.
* `TauCeti.CStarModuleUnitary.ofSurjective`: upgrades any plain surjective inner-product-preserving
  function `E → F` to a `CStarModuleUnitary A E F`.
* `TauCeti.CStarModuleUnitary.ofAdjointableMap` and
  `TauCeti.CStarModuleUnitary.equivSubtypeAdjointableMap`: equivalence between
  `CStarModuleUnitary A E F` and `{T : AdjointableMap A E F // T* ∘ T = id_E ∧ T ∘ T* = id_F}`.
* `TauCeti.CStarModuleUnitary.mulEquivUnitary`: group isomorphism between endomorphism module
  unitaries `CStarModuleUnitary A E E` and `unitary (AdjointableMap A E E)`.

## Main results

* `TauCeti.AdjointableMap.adjoint_comp_self_eq_id_iff_inner_map_map` and
  `TauCeti.AdjointableMap.isClosed_range_of_adjoint_comp_self_eq_id`: inner-product
  characterizations and closed-range property of adjointable isometries.
* `TauCeti.AdjointableMap.adjoint_comp_self_and_self_comp_adjoint_iff` and
  `TauCeti.AdjointableMap.exists_adjoint_comp_eq_id_iff`: Lance's unitary characterization
  (Theorem 3.5) for adjointable operators and for plain functions.
* `TauCeti.AdjointableMap.mem_unitary_iff`: `U ∈ unitary (AdjointableMap A E E)` iff `U` is
  surjective and preserves the `A`-valued inner product.
* `LinearMap.isometryOfInnerCStarModule`, `LinearEquiv.isometryOfInnerCStarModule`: construct
  linear isometries and isometric equivalences from inner-product preservation.
* `LinearIsometry.inner_map_map_of_map_smul_cstarModule`,
  `LinearIsometryEquiv.inner_map_map_of_map_smul_cstarModule`: over a (possibly non-unital)
  C⋆-algebra `A`, every complex-linear isometry (not necessarily surjective) commuting with the
  `A`-action preserves `⟪·, ·⟫_A`.
* `LinearIsometry.inner_map_map_cstarModule`, `LinearIsometryEquiv.inner_map_map_cstarModule`,
  `LinearIsometryEquiv.unop_inner_map_map_cstarModule`: over a unital C⋆-algebra `A`, every
  bundled `A`-linear or `Aᵐᵒᵖ`-linear isometry preserves the `A`-valued inner product.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 3
  (Theorem 3.5).
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
-/

public section

open CStarModule MulOpposite

namespace TauCeti

namespace AdjointableMap

/-! ### Adjointable isometries and unitary operators -/

section Isometries

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- An adjointable map `V : AdjointableMap A E F` satisfies `V* ∘ V = id_E` if and only if it
preserves all `A`-valued inner products. -/
theorem adjoint_comp_self_eq_id_iff_inner_map_map (V : AdjointableMap A E F) :
    V.adjoint.comp V = .id A E ↔ ∀ x y : E, inner A (V x) (V y) = inner A x y := by
  refine ⟨fun h x y ↦ ?_, fun h ↦ ext fun y ↦ CStarModule.ext_inner_left (A := A) fun x ↦ ?_⟩
  · rw [← V.adjoint_inner_right, ← comp_apply, h, id_apply]
  · rw [comp_apply, V.adjoint_inner_right, id_apply, h]

/-- An adjointable map `V : AdjointableMap A E F` satisfies `V* ∘ V = id_E` if and only if it
preserves all diagonal inner products `⟪x, x⟫_A`. -/
theorem adjoint_comp_self_eq_id_iff_inner_map_map_self (V : AdjointableMap A E F) :
    V.adjoint.comp V = .id A E ↔ ∀ x : E, inner A (V x) (V x) = inner A x x := by
  rw [adjoint_comp_self_eq_id_iff_inner_map_map,
    CStarModule.inner_map_map_iff_forall_inner_map_map_self]

theorem norm_map_of_adjoint_comp_self_eq_id {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = .id A E) (x : E) :
    ‖V x‖ = ‖x‖ :=
  CStarModule.norm_eq_of_inner_self_eq
    ((adjoint_comp_self_eq_id_iff_inner_map_map V).mp hV x x)

/-- Every adjointable isometry (`V* ∘ V = id_E`) is a metric isometry. -/
theorem isometry_of_adjoint_comp_self_eq_id {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = .id A E) :
    Isometry V :=
  AddMonoidHomClass.isometry_of_norm V (norm_map_of_adjoint_comp_self_eq_id hV)

/-- An adjointable isometry `V` (`V* ∘ V = id_E`) bundled as a complex-linear isometry
`E →ₗᵢ[ℂ] F`. -/
def toLinearIsometryOfAdjointCompSelfEqId {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = .id A E) : E →ₗᵢ[ℂ] F where
  toLinearMap := V.toContinuousLinearMap.toLinearMap
  norm_map' := norm_map_of_adjoint_comp_self_eq_id hV

@[simp] theorem toLinearIsometryOfAdjointCompSelfEqId_apply {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = .id A E) (x : E) :
    toLinearIsometryOfAdjointCompSelfEqId hV x = V x := (rfl)

/-- If `V* ∘ V = id_E`, then `V ∘ V*` is an adjointable star projection on `F` (whose range is
`Set.range V`; see `range_self_comp_adjoint_of_adjoint_comp_self_eq_id`). -/
theorem isStarProjection_self_comp_adjoint_of_adjoint_comp_self_eq_id {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = .id A E) :
    IsStarProjection (V.comp V.adjoint) :=
  ⟨by rw [IsIdempotentElem, mul_def, comp_assoc, ← comp_assoc V.adjoint V, hV, id_comp],
    by rw [IsSelfAdjoint, star_eq_adjoint, adjoint_comp, adjoint_adjoint]⟩

/-- For an adjointable isometry `V`, the range of the range projection `V ∘ V*` equals
`Set.range V`. -/
theorem range_self_comp_adjoint_of_adjoint_comp_self_eq_id {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = .id A E) :
    Set.range (V.comp V.adjoint) = Set.range V :=
  Set.Subset.antisymm (by rintro _ ⟨y, rfl⟩; exact ⟨V.adjoint y, by simp⟩)
    (by rintro _ ⟨x, rfl⟩; exact ⟨V x, by rw [comp_apply, ← comp_apply V.adjoint, hV, id_apply]⟩)

/-- Every adjointable isometry `V : AdjointableMap A E F` has norm-closed range in `F` (even
without completeness of `E` or `F`). -/
theorem isClosed_range_of_adjoint_comp_self_eq_id {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = .id A E) :
    IsClosed (Set.range V) := by
  rw [← range_self_comp_adjoint_of_adjoint_comp_self_eq_id hV]
  exact isClosed_range_of_isIdempotentElem
    (isStarProjection_self_comp_adjoint_of_adjoint_comp_self_eq_id hV).isIdempotentElem

/-- For a rectangular adjointable isometry `V : AdjointableMap A E F` (`V* ∘ V = id_E`),
`V ∘ V* = id_F` holds if and only if `V` is surjective. -/
theorem self_comp_adjoint_eq_id_iff_surjective_of_adjoint_comp_self_eq_id
    {V : AdjointableMap A E F} (hV : V.adjoint.comp V = .id A E) :
    V.comp V.adjoint = .id A F ↔ Function.Surjective V := by
  refine ⟨fun h y ↦ ⟨V.adjoint y, by simpa using DFunLike.congr_fun h y⟩,
    fun hsurj ↦ ext fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hsurj y
  calc (V.comp V.adjoint) (V x) = V ((V.adjoint.comp V) x) := by simp
    _ = AdjointableMap.id A F (V x) := by rw [hV, id_apply, id_apply]

/-- Lance's unitary characterization (Theorem 3.5) for adjointable operators: `T` is invertible
with inverse `T*` if and only if `T` is surjective and preserves the `A`-valued inner product. -/
theorem adjoint_comp_self_and_self_comp_adjoint_iff {T : AdjointableMap A E F} :
    T.adjoint.comp T = .id A E ∧ T.comp T.adjoint = .id A F ↔
      Function.Surjective T ∧ ∀ x y : E, inner A (T x) (T y) = inner A x y := by
  rw [and_comm (a := Function.Surjective T), ← adjoint_comp_self_eq_id_iff_inner_map_map]
  exact and_congr_right self_comp_adjoint_eq_id_iff_surjective_of_adjoint_comp_self_eq_id

/-- An operator `U : AdjointableMap A E E` belongs to `unitary (AdjointableMap A E E)` if and only
if `U* ∘ U = id_E` and `U ∘ U* = id_E`. -/
theorem mem_unitary_iff_adjoint_comp {U : AdjointableMap A E E} :
    U ∈ unitary (AdjointableMap A E E) ↔
      U.adjoint.comp U = .id A E ∧ U.comp U.adjoint = .id A E := by
  rw [Unitary.mem_iff, star_eq_adjoint, mul_def, mul_def, one_def]

/-- An operator `U : AdjointableMap A E E` belongs to `unitary (AdjointableMap A E E)` if and only
if `U` is surjective and preserves the `A`-valued inner product. -/
theorem mem_unitary_iff {U : AdjointableMap A E E} :
    U ∈ unitary (AdjointableMap A E E) ↔
      Function.Surjective U ∧ ∀ x y : E, inner A (U x) (U y) = inner A x y := by
  rw [mem_unitary_iff_adjoint_comp]
  exact adjoint_comp_self_and_self_comp_adjoint_iff

end Isometries

end AdjointableMap

/-! ### Module unitaries -/

/-- A unitary equivalence between Hilbert C⋆-modules `E` and `F` over `A`: a complex-linear
isometric equivalence `E ≃ₗᵢ[ℂ] F` preserving the `A`-valued inner product
`⟪U x, U y⟫_A = ⟪x, y⟫_A`.

Compatibility with the coefficient `A`-action (`U (a • x) = a • U x`) and adjointability with
inverse equal to the adjoint (`CStarModuleUnitary.equivSubtypeAdjointableMap`) follow automatically;
moreover `CStarModuleUnitary.ofSurjective` upgrades any plain surjective inner-product-preserving
function `E → F` to a `CStarModuleUnitary A E F` with no linearity, continuity, or completeness
assumptions. -/
structure CStarModuleUnitary (A E F : Type*) [NonUnitalRing A] [StarRing A] [Module ℂ A]
    [StarModule ℂ A] [PartialOrder A] [Norm A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
    extends E ≃ₗᵢ[ℂ] F where
  /-- A module unitary preserves the `A`-valued inner product. -/
  inner_map_map' (x y : E) :
    inner A (toLinearIsometryEquiv x) (toLinearIsometryEquiv y) = inner A x y

namespace CStarModuleUnitary

variable {A E F G : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

instance instEquivLike : EquivLike (CStarModuleUnitary A E F) E F where
  coe U := U.toLinearIsometryEquiv
  inv U := U.toLinearIsometryEquiv.symm
  left_inv U := U.toLinearIsometryEquiv.left_inv
  right_inv U := U.toLinearIsometryEquiv.right_inv
  coe_injective' U V h _ := by
    cases U
    cases V
    congr
    exact DFunLike.coe_injective h

instance instLinearIsometryEquivClass :
    LinearIsometryEquivClass (CStarModuleUnitary A E F) ℂ E F where
  map_add U := map_add U.toLinearIsometryEquiv
  map_smulₛₗ U := map_smulₛₗ U.toLinearIsometryEquiv
  norm_map U := U.toLinearIsometryEquiv.norm_map

@[simp]
theorem toLinearIsometryEquiv_apply (U : CStarModuleUnitary A E F) (x : E) :
    U.toLinearIsometryEquiv x = U x := (rfl)

@[simp]
theorem coe_mk (e : E ≃ₗᵢ[ℂ] F) (h : ∀ x y : E, inner A (e x) (e y) = inner A x y) :
    ⇑(⟨e, h⟩ : CStarModuleUnitary A E F) = ⇑e := (rfl)

theorem mk_apply (e : E ≃ₗᵢ[ℂ] F) (h : ∀ x y : E, inner A (e x) (e y) = inner A x y) (x : E) :
    (⟨e, h⟩ : CStarModuleUnitary A E F) x = e x := (rfl)

@[simp]
theorem coe_toLinearIsometryEquiv (U : CStarModuleUnitary A E F) :
    ⇑U.toLinearIsometryEquiv = ⇑U := (rfl)

@[ext]
theorem ext {U V : CStarModuleUnitary A E F} (h : ∀ x, U x = V x) : U = V :=
  DFunLike.ext U V h

theorem toLinearIsometryEquiv_injective :
    Function.Injective (toLinearIsometryEquiv : CStarModuleUnitary A E F → E ≃ₗᵢ[ℂ] F) :=
  fun _ _ h ↦ ext fun x ↦ DFunLike.congr_fun h x

@[simp]
theorem toLinearIsometryEquiv_inj {U V : CStarModuleUnitary A E F} :
    U.toLinearIsometryEquiv = V.toLinearIsometryEquiv ↔ U = V :=
  toLinearIsometryEquiv_injective.eq_iff

@[simp]
theorem inner_map_map (U : CStarModuleUnitary A E F) (x y : E) :
    inner A (U x) (U y) = inner A x y :=
  U.inner_map_map' x y

/-- The identity unitary on a Hilbert C⋆-module. -/
protected def refl (A E : Type*) [NonUnitalRing A] [StarRing A] [Module ℂ A]
    [StarModule ℂ A] [PartialOrder A] [Norm A] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul A E] [CStarModule A E] : CStarModuleUnitary A E E where
  toLinearIsometryEquiv := LinearIsometryEquiv.refl ℂ E
  inner_map_map' _ _ := rfl

instance instInhabited : Inhabited (CStarModuleUnitary A E E) := ⟨.refl A E⟩

@[simp]
theorem toLinearIsometryEquiv_refl :
    (CStarModuleUnitary.refl A E).toLinearIsometryEquiv = .refl ℂ E := (rfl)

@[simp]
theorem refl_apply (x : E) : CStarModuleUnitary.refl A E x = x := (rfl)

/-- The inverse of a Hilbert C⋆-module unitary. -/
def symm (U : CStarModuleUnitary A E F) : CStarModuleUnitary A F E where
  toLinearIsometryEquiv := U.toLinearIsometryEquiv.symm
  inner_map_map' x y := by
    calc inner A (U.toLinearIsometryEquiv.symm x) (U.toLinearIsometryEquiv.symm y)
        = inner A (U (U.toLinearIsometryEquiv.symm x)) (U (U.toLinearIsometryEquiv.symm y)) :=
          (U.inner_map_map _ _).symm
      _ = inner A x y := by
          rw [← toLinearIsometryEquiv_apply, ← toLinearIsometryEquiv_apply,
            U.toLinearIsometryEquiv.apply_symm_apply, U.toLinearIsometryEquiv.apply_symm_apply]

@[simp]
theorem toLinearIsometryEquiv_symm (U : CStarModuleUnitary A E F) :
    U.symm.toLinearIsometryEquiv = U.toLinearIsometryEquiv.symm := (rfl)

@[simp]
theorem coe_symm_toLinearIsometryEquiv (U : CStarModuleUnitary A E F) :
    ⇑U.toLinearIsometryEquiv.symm = ⇑U.symm := (rfl)

@[simp]
theorem equivLike_inv_eq_symm (U : CStarModuleUnitary A E F) :
    EquivLike.inv U = ⇑U.symm := (rfl)

@[simp]
theorem symm_symm (U : CStarModuleUnitary A E F) : U.symm.symm = U := (rfl)

theorem symm_injective :
    Function.Injective (symm : CStarModuleUnitary A E F → CStarModuleUnitary A F E) :=
  Function.LeftInverse.injective symm_symm

@[simp]
theorem symm_inj {U V : CStarModuleUnitary A E F} : U.symm = V.symm ↔ U = V :=
  symm_injective.eq_iff

@[simp]
theorem apply_symm_apply (U : CStarModuleUnitary A E F) (y : F) : U (U.symm y) = y :=
  U.toLinearIsometryEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (U : CStarModuleUnitary A E F) (x : E) : U.symm (U x) = x :=
  U.toLinearIsometryEquiv.symm_apply_apply x

theorem symm_apply_eq (U : CStarModuleUnitary A E F) {x : E} {y : F} :
    U.symm y = x ↔ y = U x := by
  simpa only [coe_symm_toLinearIsometryEquiv, toLinearIsometryEquiv_apply] using
    U.toLinearIsometryEquiv.symm_apply_eq (x := y) (y := x)

theorem eq_symm_apply (U : CStarModuleUnitary A E F) {x : E} {y : F} :
    x = U.symm y ↔ U x = y := by
  simpa only [coe_symm_toLinearIsometryEquiv, toLinearIsometryEquiv_apply] using
    U.toLinearIsometryEquiv.eq_symm_apply (x := y) (y := x)

/-- Moving a module unitary across the `A`-valued inner product from left to right:
`⟪x, U.symm y⟫_A = ⟪U x, y⟫_A`. -/
theorem inner_symm_right (U : CStarModuleUnitary A E F) (x : E) (y : F) :
    inner A x (U.symm y) = inner A (U x) y := by
  simpa using (U.inner_map_map x (U.symm y)).symm

/-- Moving a module unitary across the `A`-valued inner product from right to left:
`⟪U.symm y, x⟫_A = ⟪y, U x⟫_A`. -/
theorem inner_symm_left (U : CStarModuleUnitary A E F) (x : E) (y : F) :
    inner A (U.symm y) x = inner A y (U x) := by
  simpa using (U.inner_map_map (U.symm y) x).symm

@[simp]
theorem symm_refl : (CStarModuleUnitary.refl A E).symm = .refl A E := (rfl)

/-- Composition of Hilbert C⋆-module unitaries (`(U.trans V) x = V (U x)`). -/
def trans (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) :
    CStarModuleUnitary A E G where
  toLinearIsometryEquiv := U.toLinearIsometryEquiv.trans V.toLinearIsometryEquiv
  inner_map_map' x y := (V.inner_map_map (U x) (U y)).trans (U.inner_map_map x y)

@[simp]
theorem toLinearIsometryEquiv_trans (U : CStarModuleUnitary A E F)
    (V : CStarModuleUnitary A F G) :
    (U.trans V).toLinearIsometryEquiv =
      U.toLinearIsometryEquiv.trans V.toLinearIsometryEquiv := (rfl)

@[simp]
theorem trans_apply (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) (x : E) :
    U.trans V x = V (U x) := (rfl)

@[simp]
theorem symm_trans (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) :
    (U.trans V).symm = V.symm.trans U.symm := (rfl)

@[simp]
theorem refl_trans (U : CStarModuleUnitary A E F) :
    (CStarModuleUnitary.refl A E).trans U = U :=
  ext fun _ ↦ rfl

@[simp]
theorem trans_refl (U : CStarModuleUnitary A E F) :
    U.trans (.refl A F) = U :=
  ext fun _ ↦ rfl

@[simp]
theorem self_trans_symm (U : CStarModuleUnitary A E F) :
    U.trans U.symm = .refl A E :=
  ext U.symm_apply_apply

@[simp]
theorem symm_trans_self (U : CStarModuleUnitary A E F) :
    U.symm.trans U = .refl A F :=
  ext U.apply_symm_apply

theorem trans_assoc {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul A H]
    [CStarModule A H] (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G)
    (W : CStarModuleUnitary A G H) :
    (U.trans V).trans W = U.trans (V.trans W) := (rfl)

/-- View a Hilbert C⋆-module unitary `U : CStarModuleUnitary A E F` as an adjointable operator
whose adjoint is `U.symm`. -/
def toAdjointableMap (U : CStarModuleUnitary A E F) : AdjointableMap A E F where
  toContinuousLinearMap := U.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
  adjoint' := U.symm.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
  inner_map_eq' x y := by
    simp only [LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, toLinearIsometryEquiv_apply]
    exact (U.inner_symm_right x y).symm

@[simp]
theorem toAdjointableMap_apply (U : CStarModuleUnitary A E F) (x : E) :
    U.toAdjointableMap x = U x := (rfl)

@[simp]
theorem coe_toAdjointableMap (U : CStarModuleUnitary A E F) :
    ⇑U.toAdjointableMap = ⇑U := (rfl)

theorem toAdjointableMap_injective :
    Function.Injective (toAdjointableMap : CStarModuleUnitary A E F → AdjointableMap A E F) :=
  fun _ _ h ↦ ext fun x ↦ DFunLike.congr_fun h x

@[simp]
theorem toAdjointableMap_inj {U V : CStarModuleUnitary A E F} :
    U.toAdjointableMap = V.toAdjointableMap ↔ U = V :=
  toAdjointableMap_injective.eq_iff

@[simp]
theorem adjoint_toAdjointableMap (U : CStarModuleUnitary A E F) :
    U.toAdjointableMap.adjoint = U.symm.toAdjointableMap :=
  AdjointableMap.ext fun _ ↦ by simp [toAdjointableMap]

@[simp]
theorem star_toAdjointableMap (U : CStarModuleUnitary A E E) :
    star U.toAdjointableMap = U.symm.toAdjointableMap :=
  U.adjoint_toAdjointableMap

@[simp]
theorem toAdjointableMap_refl :
    (CStarModuleUnitary.refl A E).toAdjointableMap = .id A E :=
  AdjointableMap.ext fun _ ↦ by simp

@[simp]
theorem toAdjointableMap_trans (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) :
    (U.trans V).toAdjointableMap = V.toAdjointableMap.comp U.toAdjointableMap :=
  AdjointableMap.ext fun _ ↦ by simp

@[simp]
theorem symm_toAdjointableMap_comp_toAdjointableMap (U : CStarModuleUnitary A E F) :
    U.symm.toAdjointableMap.comp U.toAdjointableMap = .id A E :=
  AdjointableMap.ext fun _ ↦ by simp

@[simp]
theorem toAdjointableMap_comp_symm_toAdjointableMap (U : CStarModuleUnitary A E F) :
    U.toAdjointableMap.comp U.symm.toAdjointableMap = .id A F :=
  AdjointableMap.ext fun _ ↦ by simp

theorem adjoint_toAdjointableMap_comp_self (U : CStarModuleUnitary A E F) :
    U.toAdjointableMap.adjoint.comp U.toAdjointableMap = .id A E := by
  simp

theorem toAdjointableMap_comp_adjoint (U : CStarModuleUnitary A E F) :
    U.toAdjointableMap.comp U.toAdjointableMap.adjoint = .id A F := by
  simp

/-- Every Hilbert C⋆-module unitary automatically commutes with the coefficient `A`-action. -/
@[simp]
theorem map_smul_coeff (U : CStarModuleUnitary A E F) (a : A) (x : E) :
    U (a • x) = a • U x :=
  U.toAdjointableMap.map_smul_coeff a x

/-- Conjugation by a Hilbert C⋆-module unitary `U : CStarModuleUnitary A E F` as a unital
`⋆`-algebra isomorphism `AdjointableMap A E E ≃⋆ₐ[ℂ] AdjointableMap A F F` sending `T` to
`U ∘ T ∘ U*`. -/
def conjStarAlgEquiv (U : CStarModuleUnitary A E F) :
    AdjointableMap A E E ≃⋆ₐ[ℂ] AdjointableMap A F F where
  toFun T := (U.toAdjointableMap.comp T).comp U.symm.toAdjointableMap
  invFun S := (U.symm.toAdjointableMap.comp S).comp U.toAdjointableMap
  left_inv T := AdjointableMap.ext fun x ↦ by simp
  right_inv S := AdjointableMap.ext fun y ↦ by simp
  map_mul' T₁ T₂ := AdjointableMap.ext fun y ↦ by simp
  map_add' T₁ T₂ := AdjointableMap.ext fun y ↦ by simp
  map_smul' c T := AdjointableMap.ext fun y ↦ by simp
  map_star' T := AdjointableMap.ext fun y ↦ by simp [AdjointableMap.star_eq_adjoint]

theorem conjStarAlgEquiv_apply (U : CStarModuleUnitary A E F) (T : AdjointableMap A E E) :
    U.conjStarAlgEquiv T = (U.toAdjointableMap.comp T).comp U.symm.toAdjointableMap := (rfl)

@[simp]
theorem conjStarAlgEquiv_apply_apply (U : CStarModuleUnitary A E F)
    (T : AdjointableMap A E E) (y : F) :
    U.conjStarAlgEquiv T y = U (T (U.symm y)) := by
  simp [conjStarAlgEquiv_apply]

@[simp]
theorem conjStarAlgEquiv_symm (U : CStarModuleUnitary A E F) :
    U.conjStarAlgEquiv.symm = U.symm.conjStarAlgEquiv := (rfl)

@[simp]
theorem conjStarAlgEquiv_refl :
    (CStarModuleUnitary.refl A E).conjStarAlgEquiv = .refl ℂ (AdjointableMap A E E) :=
  StarAlgEquiv.ext fun _ ↦ AdjointableMap.ext fun _ ↦ by simp

theorem conjStarAlgEquiv_trans (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) :
    (U.trans V).conjStarAlgEquiv = U.conjStarAlgEquiv.trans V.conjStarAlgEquiv :=
  StarAlgEquiv.ext fun _ ↦ AdjointableMap.ext fun _ ↦ by simp

/-- Construct a Hilbert C⋆-module unitary from a plain surjective inner-product-preserving function
`f : E → F`, with no complex-linearity, `A`-linearity, continuity, or completeness hypotheses. -/
noncomputable def ofSurjective (f : E → F) (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    CStarModuleUnitary A E F :=
  -- Nondegeneracy gives injectivity, and `(f, f⁻¹)` is then an adjoint pair.
  let e : E ≃ F := Equiv.ofBijective f ⟨CStarModule.injective_of_inner_map_map hf_inner, hf_surj⟩
  have hpair : LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip e e.symm :=
    CStarModule.isAdjointPair_inner_iff.mpr fun x y ↦ by
      conv_lhs => rw [← e.apply_symm_apply y]
      exact hf_inner x (e.symm y)
  { toLinearIsometryEquiv :=
      { toFun := f
        invFun := e.symm
        left_inv := e.left_inv
        right_inv := e.right_inv
        map_add' := hpair.map_add_cstarModule
        map_smul' := hpair.map_smul_cstarModule
        norm_map' := fun x ↦ CStarModule.norm_eq_of_inner_self_eq (hf_inner x x) }
    inner_map_map' := hf_inner }

@[simp]
theorem ofSurjective_apply (f : E → F) (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) (x : E) :
    ofSurjective f hf_surj hf_inner x = f x := (rfl)

@[simp]
theorem coe_ofSurjective (f : E → F) (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    ⇑(ofSurjective f hf_surj hf_inner) = f :=
  funext (ofSurjective_apply f hf_surj hf_inner)

@[simp]
theorem ofSurjective_symm_apply_apply (f : E → F) (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) (x : E) :
    (ofSurjective f hf_surj hf_inner).symm (f x) = x :=
  (ofSurjective f hf_surj hf_inner).symm_apply_apply x

theorem ofSurjective_apply_symm_apply (f : E → F) (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) (y : F) :
    f ((ofSurjective f hf_surj hf_inner).symm y) = y := by
  rw [← ofSurjective_apply f hf_surj hf_inner]
  exact (ofSurjective f hf_surj hf_inner).apply_symm_apply y

/-- Construct a Hilbert C⋆-module unitary from an invertible adjointable map `T` whose inverse is
its adjoint (`T* ∘ T = id_E` and `T ∘ T* = id_F`). -/
def ofAdjointableMap (T : AdjointableMap A E F)
    (h₁ : T.adjoint.comp T = .id A E) (h₂ : T.comp T.adjoint = .id A F) :
    CStarModuleUnitary A E F where
  toLinearIsometryEquiv :=
    { toFun := T
      invFun := T.adjoint
      left_inv := fun x ↦ by simpa using DFunLike.congr_fun h₁ x
      right_inv := fun y ↦ by simpa using DFunLike.congr_fun h₂ y
      map_add' := map_add T
      map_smul' := map_smul T
      norm_map' := AdjointableMap.norm_map_of_adjoint_comp_self_eq_id h₁ }
  inner_map_map' := (AdjointableMap.adjoint_comp_self_eq_id_iff_inner_map_map T).mp h₁

@[simp]
theorem ofAdjointableMap_apply (T : AdjointableMap A E F)
    (h₁ : T.adjoint.comp T = .id A E) (h₂ : T.comp T.adjoint = .id A F) (x : E) :
    ofAdjointableMap T h₁ h₂ x = T x := (rfl)

@[simp]
theorem coe_ofAdjointableMap (T : AdjointableMap A E F)
    (h₁ : T.adjoint.comp T = .id A E) (h₂ : T.comp T.adjoint = .id A F) :
    ⇑(ofAdjointableMap T h₁ h₂) = ⇑T := (rfl)

@[simp]
theorem symm_ofAdjointableMap (T : AdjointableMap A E F)
    (h₁ : T.adjoint.comp T = .id A E) (h₂ : T.comp T.adjoint = .id A F) :
    (ofAdjointableMap T h₁ h₂).symm =
      ofAdjointableMap T.adjoint (by simpa using h₂) (by simpa using h₁) :=
  ext fun _ ↦ rfl

@[simp]
theorem toAdjointableMap_ofAdjointableMap (T : AdjointableMap A E F)
    (h₁ : T.adjoint.comp T = .id A E) (h₂ : T.comp T.adjoint = .id A F) :
    (ofAdjointableMap T h₁ h₂).toAdjointableMap = T :=
  AdjointableMap.ext fun _ ↦ rfl

@[simp]
theorem ofAdjointableMap_toAdjointableMap (U : CStarModuleUnitary A E F) :
    ofAdjointableMap U.toAdjointableMap U.adjoint_toAdjointableMap_comp_self
      U.toAdjointableMap_comp_adjoint = U :=
  ext fun _ ↦ rfl

/-- Equivalence between Hilbert C⋆-module unitaries `CStarModuleUnitary A E F` and adjointable
operators `T : AdjointableMap A E F` whose inverse is their adjoint
(`T* ∘ T = id_E` and `T ∘ T* = id_F`). -/
def equivSubtypeAdjointableMap :
    CStarModuleUnitary A E F ≃
      {T : AdjointableMap A E F // T.adjoint.comp T = .id A E ∧ T.comp T.adjoint = .id A F} where
  toFun U := ⟨U.toAdjointableMap, by simp⟩
  invFun T := ofAdjointableMap T.val T.property.1 T.property.2
  left_inv _ := ext fun _ ↦ rfl
  right_inv _ := Subtype.ext (AdjointableMap.ext fun _ ↦ rfl)

@[simp]
theorem coe_equivSubtypeAdjointableMap (U : CStarModuleUnitary A E F) :
    (equivSubtypeAdjointableMap U : AdjointableMap A E F) = U.toAdjointableMap := (rfl)

@[simp]
theorem equivSubtypeAdjointableMap_symm_apply
    (T : {T : AdjointableMap A E F // T.adjoint.comp T = .id A E ∧ T.comp T.adjoint = .id A F}) :
    equivSubtypeAdjointableMap.symm T = ofAdjointableMap T.val T.property.1 T.property.2 := (rfl)

/-! #### Group structure on endomorphism unitaries and comparison with `unitary` -/
section End

instance instOne : One (CStarModuleUnitary A E E) := ⟨.refl A E⟩

instance instMul : Mul (CStarModuleUnitary A E E) := ⟨fun U V ↦ V.trans U⟩

instance instInv : Inv (CStarModuleUnitary A E E) := ⟨symm⟩

instance instIsOneApplyEqSelf : IsOneApplyEqSelf (CStarModuleUnitary A E E) where

instance instIsMulApplyEqComp : IsMulApplyEqComp (CStarModuleUnitary A E E) where

theorem one_def : (1 : CStarModuleUnitary A E E) = .refl A E := (rfl)

theorem mul_def (U V : CStarModuleUnitary A E E) : U * V = V.trans U := (rfl)

theorem inv_def (U : CStarModuleUnitary A E E) : U⁻¹ = U.symm := (rfl)

@[simp]
theorem coe_inv (U : CStarModuleUnitary A E E) : ⇑U⁻¹ = ⇑U.symm := (rfl)

theorem inv_apply (U : CStarModuleUnitary A E E) (x : E) : U⁻¹ x = U.symm x := (rfl)

instance instGroup : Group (CStarModuleUnitary A E E) where
  mul_assoc U V W := (W.trans_assoc V U).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm

@[simp]
theorem toLinearIsometryEquiv_one :
    (1 : CStarModuleUnitary A E E).toLinearIsometryEquiv = 1 := (rfl)

@[simp]
theorem toLinearIsometryEquiv_mul (U V : CStarModuleUnitary A E E) :
    (U * V).toLinearIsometryEquiv =
      U.toLinearIsometryEquiv * V.toLinearIsometryEquiv := (rfl)

@[simp]
theorem toLinearIsometryEquiv_inv (U : CStarModuleUnitary A E E) :
    U⁻¹.toLinearIsometryEquiv = U.toLinearIsometryEquiv⁻¹ := (rfl)

@[simp]
theorem toAdjointableMap_one :
    (1 : CStarModuleUnitary A E E).toAdjointableMap = 1 :=
  AdjointableMap.ext fun _ ↦ by simp

@[simp]
theorem toAdjointableMap_mul (U V : CStarModuleUnitary A E E) :
    (U * V).toAdjointableMap = U.toAdjointableMap * V.toAdjointableMap :=
  AdjointableMap.ext fun _ ↦ by simp [mul_apply_eq_comp]

@[simp]
theorem toAdjointableMap_inv (U : CStarModuleUnitary A E E) :
    U⁻¹.toAdjointableMap = U.symm.toAdjointableMap :=
  AdjointableMap.ext fun _ ↦ by simp

@[simp]
theorem symm_toAdjointableMap_mul_toAdjointableMap (U : CStarModuleUnitary A E E) :
    U.symm.toAdjointableMap * U.toAdjointableMap = 1 := by
  rw [AdjointableMap.mul_def, AdjointableMap.one_def]
  exact U.symm_toAdjointableMap_comp_toAdjointableMap

@[simp]
theorem toAdjointableMap_mul_symm_toAdjointableMap (U : CStarModuleUnitary A E E) :
    U.toAdjointableMap * U.symm.toAdjointableMap = 1 := by
  rw [AdjointableMap.mul_def, AdjointableMap.one_def]
  exact U.toAdjointableMap_comp_symm_toAdjointableMap

@[simp]
theorem toAdjointableMap_mem_unitary (U : CStarModuleUnitary A E E) :
    U.toAdjointableMap ∈ unitary (AdjointableMap A E E) :=
  Unitary.mem_iff.mpr ⟨by simp, by simp⟩

/-- Endomorphism module unitaries `CStarModuleUnitary A E E` are canonically isomorphic as a group
to `unitary (AdjointableMap A E E)`. -/
def mulEquivUnitary : CStarModuleUnitary A E E ≃* unitary (AdjointableMap A E E) :=
  { equivSubtypeAdjointableMap.trans
      (Equiv.subtypeEquivRight fun _ ↦ AdjointableMap.mem_unitary_iff_adjoint_comp.symm) with
    map_mul' _ _ := Subtype.ext <| AdjointableMap.ext fun _ ↦ by
      simp [equivSubtypeAdjointableMap, mul_apply_eq_comp] }

@[simp]
theorem coe_mulEquivUnitary (U : CStarModuleUnitary A E E) :
    (mulEquivUnitary U : AdjointableMap A E E) = U.toAdjointableMap := (rfl)

@[simp]
theorem mulEquivUnitary_symm_apply (U : unitary (AdjointableMap A E E)) (x : E) :
    mulEquivUnitary.symm U x = (U : AdjointableMap A E E) x := (rfl)

@[simp]
theorem toAdjointableMap_mulEquivUnitary_symm (U : unitary (AdjointableMap A E E)) :
    (mulEquivUnitary.symm U).toAdjointableMap = (U : AdjointableMap A E E) :=
  AdjointableMap.ext fun _ ↦ rfl

end End

end CStarModuleUnitary

namespace AdjointableMap

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- Lance's unitary characterization (Theorem 3.5) starting from a plain function `f : E → F`:
`f` is the underlying map of an invertible adjointable operator whose inverse is its adjoint if
and only if `f` is surjective and preserves the `A`-valued inner product. No linearity, continuity,
or completeness hypotheses are needed. -/
theorem exists_adjoint_comp_eq_id_iff {f : E → F} :
    (∃ T : AdjointableMap A E F,
      ⇑T = f ∧ T.adjoint.comp T = .id A E ∧ T.comp T.adjoint = .id A F) ↔
      Function.Surjective f ∧ ∀ x y : E, inner A (f x) (f y) = inner A x y := by
  refine ⟨?_, fun ⟨hsurj, hinner⟩ ↦ ?_⟩
  · rintro ⟨T, rfl, h⟩
    exact adjoint_comp_self_and_self_comp_adjoint_iff.mp h
  · let U := CStarModuleUnitary.ofSurjective f hsurj hinner
    exact ⟨U.toAdjointableMap, by simp [U], U.adjoint_toAdjointableMap_comp_self,
      U.toAdjointableMap_comp_adjoint⟩

end AdjointableMap

end TauCeti

namespace LinearMap

variable {R A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [Semiring R] [SeminormedAddCommGroup E] [Module ℂ E] [SMul A E] [Module R E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [SMul A F] [Module R F] [CStarModule A F]
  (f : E →ₗ[R] F) (hf : ∀ x : E, inner A (f x) (f x) = inner A x x)

/-- An `R`-linear map between Hilbert C⋆-modules preserving self-inner products is an `R`-linear
isometry. -/
def isometryOfInnerCStarModule : E →ₗᵢ[R] F where
  toLinearMap := f
  norm_map' x := CStarModule.norm_eq_of_inner_self_eq (hf x)

@[simp] theorem coe_isometryOfInnerCStarModule : ⇑(f.isometryOfInnerCStarModule hf) = f := (rfl)

@[simp] theorem isometryOfInnerCStarModule_toLinearMap :
    (f.isometryOfInnerCStarModule hf).toLinearMap = f := (rfl)

end LinearMap

namespace LinearEquiv

variable {R A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [Semiring R] [SeminormedAddCommGroup E] [Module ℂ E] [SMul A E] [Module R E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [SMul A F] [Module R F] [CStarModule A F]
  (f : E ≃ₗ[R] F) (hf : ∀ x : E, inner A (f x) (f x) = inner A x x)

/-- An `R`-linear equivalence between Hilbert C⋆-modules preserving self-inner products is a linear
isometric equivalence. -/
def isometryOfInnerCStarModule : E ≃ₗᵢ[R] F where
  toLinearEquiv := f
  norm_map' := (f.toLinearMap.isometryOfInnerCStarModule hf).norm_map

@[simp] theorem coe_isometryOfInnerCStarModule : ⇑(f.isometryOfInnerCStarModule hf) = f := (rfl)

@[simp] theorem isometryOfInnerCStarModule_toLinearEquiv :
    (f.isometryOfInnerCStarModule hf).toLinearEquiv = f := (rfl)

@[simp] theorem coe_symm_isometryOfInnerCStarModule :
    ⇑(f.isometryOfInnerCStarModule hf).symm = f.symm := (rfl)

end LinearEquiv

namespace LinearIsometry

section NonUnital

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [SMul A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [SMul A F] [CStarModule A F]

/-- **Lance's theorem** (isometry case) over a (possibly non-unital) C⋆-algebra `A`: every
`f : E →ₗᵢ[ℂ] F` commuting with the `A`-action preserves `⟪·, ·⟫_A`. -/
theorem inner_map_map_of_map_smul_cstarModule (f : E →ₗᵢ[ℂ] F)
    (hf : ∀ (a : A) (x : E), f (a • x) = a • f x) (x y : E) :
    inner A (f x) (f y) = inner A x y :=
  (CStarModule.inner_map_map_iff_forall_inner_map_map_self f).mpr (fun z ↦ le_antisymm
    (by
      simpa using TauCeti.CStarModule.inner_self_le_of_norm_smul_le (A := A) (C := 1) z (f z)
        fun a ↦ by rw [← hf, f.norm_map, one_mul])
    (by
      simpa using TauCeti.CStarModule.inner_self_le_of_norm_smul_le (A := A) (C := 1) (f z) z
        fun a ↦ by rw [← hf, f.norm_map, one_mul])) x y

end NonUnital

section Left

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [Module A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module A F] [CStarModule A F]

/-- Every `A`-linear isometry `f : E →ₗᵢ[A] F` over a unital C⋆-algebra preserves `⟪·, ·⟫_A`. -/
@[simp] theorem inner_map_map_cstarModule (f : E →ₗᵢ[A] F) (x y : E) :
    inner A (f x) (f y) = inner A x y := by
  have : IsScalarTower ℂ A E := CStarModule.isScalarTower A E
  have : IsScalarTower ℂ A F := CStarModule.isScalarTower A F
  exact LinearIsometry.inner_map_map_of_map_smul_cstarModule
    ⟨f.toLinearMap.restrictScalars ℂ, f.norm_map⟩ f.map_smul x y

/-- Every `A`-linear isometry `f : E →ₗᵢ[A] F` preserves diagonal inner products `⟪x, x⟫_A`. -/
theorem inner_map_map_self_cstarModule (f : E →ₗᵢ[A] F) (x : E) :
    inner A (f x) (f x) = inner A x x := f.inner_map_map_cstarModule x x

end Left

section Right

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]

/-- Every right `A`-linear isometry `f : E →ₗᵢ[Aᵐᵒᵖ] F` preserves `⟨x, y⟩_A`. -/
theorem unop_inner_map_map_cstarModule (f : E →ₗᵢ[Aᵐᵒᵖ] F) (x y : E) :
    unop (inner Aᵐᵒᵖ (f x) (f y)) = unop (inner Aᵐᵒᵖ x y) :=
  congrArg unop (f.inner_map_map_cstarModule x y)

end Right

end LinearIsometry

namespace LinearIsometryEquiv

section NonUnital

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [SMul A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [SMul A F] [CStarModule A F]

/-- **Lance's theorem** (Lance, Theorem 3.5) over a (possibly non-unital) C⋆-algebra `A`: every
`f : E ≃ₗᵢ[ℂ] F` commuting with the `A`-action preserves `⟪·, ·⟫_A`. -/
theorem inner_map_map_of_map_smul_cstarModule (f : E ≃ₗᵢ[ℂ] F)
    (hf : ∀ (a : A) (x : E), f (a • x) = a • f x) (x y : E) :
    inner A (f x) (f y) = inner A x y :=
  f.toLinearIsometry.inner_map_map_of_map_smul_cstarModule hf x y

end NonUnital

section Left

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [Module A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module A F] [CStarModule A F]

/-- **Lance's theorem** (Lance, Theorem 3.5): every surjective `A`-linear isometry `f : E ≃ₗᵢ[A] F`
over a unital C⋆-algebra preserves `⟪·, ·⟫_A`. -/
@[simp] theorem inner_map_map_cstarModule (f : E ≃ₗᵢ[A] F) (x y : E) :
    inner A (f x) (f y) = inner A x y :=
  f.toLinearIsometry.inner_map_map_cstarModule x y

/-- A surjective `A`-linear isometry `f : E ≃ₗᵢ[A] F` preserves diagonal inner products
`⟪x, x⟫_A`. -/
theorem inner_map_map_self_cstarModule (f : E ≃ₗᵢ[A] F) (x : E) :
    inner A (f x) (f x) = inner A x x := f.inner_map_map_cstarModule x x

/-- Moving a surjective `A`-linear isometry `f : E ≃ₗᵢ[A] F` across the `A`-valued inner
product: `⟪f x, y⟫_A = ⟪x, f.symm y⟫_A`. -/
theorem inner_map_eq_flip_cstarModule (f : E ≃ₗᵢ[A] F) (x : E) (y : F) :
    inner A (f x) y = inner A x (f.symm y) := by
  conv_lhs => rw [← f.apply_symm_apply y, f.inner_map_map_cstarModule]

end Left

section Right

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]

/-- A surjective right `A`-linear isometry `f : E ≃ₗᵢ[Aᵐᵒᵖ] F` preserves `⟨x, y⟩_A`. -/
theorem unop_inner_map_map_cstarModule (f : E ≃ₗᵢ[Aᵐᵒᵖ] F) (x y : E) :
    unop (inner Aᵐᵒᵖ (f x) (f y)) = unop (inner Aᵐᵒᵖ x y) :=
  congrArg unop (f.inner_map_map_cstarModule x y)

/-- Moving a surjective right `A`-linear isometry `f : E ≃ₗᵢ[Aᵐᵒᵖ] F` across the `A`-valued
inner product: `⟨f x, y⟩_A = ⟨x, f.symm y⟩_A`. -/
theorem unop_inner_map_eq_flip_cstarModule (f : E ≃ₗᵢ[Aᵐᵒᵖ] F) (x : E) (y : F) :
    unop (inner Aᵐᵒᵖ (f x) y) = unop (inner Aᵐᵒᵖ x (f.symm y)) :=
  congrArg unop (f.inner_map_eq_flip_cstarModule x y)

end Right

end LinearIsometryEquiv
