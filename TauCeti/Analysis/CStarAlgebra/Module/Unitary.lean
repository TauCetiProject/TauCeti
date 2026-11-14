/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable

/-!
# Adjointable isometries and unitaries on Hilbert C⋆-modules

This file develops adjointable isometries (`V* ∘ V = id_E`) and unitary equivalences between
Hilbert C⋆-modules over a (possibly non-unital) C⋆-algebra `A`.

An adjointable operator `V : TauCeti.AdjointableMap A E F` satisfies `V* ∘ V = id_E` if and only if
it preserves all `A`-valued inner products (`adjoint_comp_self_eq_id_iff`), equivalently all
diagonal inner products (`adjoint_comp_self_eq_id_iff_self`); its range is norm-closed because
`V ∘ V*` is an adjointable star projection onto `Set.range V`.

For invertible equivalences, Lance's unitary theorem (`TauCeti.CStarModuleUnitary.ofSurjective`)
shows that any plain surjective function `f : E → F` preserving the `A`-valued inner product is
automatically complex-linear, `A`-linear, norm-preserving, and adjointable with inverse equal to
its adjoint, with no continuity or completeness hypotheses.

## Main definitions

* `TauCeti.CStarModuleUnitary A E F`: bundled Hilbert C⋆-module unitaries between `E` and `F`, i.e.
  complex-linear isometric equivalences `E ≃ₗᵢ[ℂ] F` preserving the `A`-valued inner product.
* `TauCeti.CStarModuleUnitary.toAdjointableMap`: views a module unitary `U` as an adjointable
  operator with `U.toAdjointableMap.adjoint = U.symm.toAdjointableMap`.
* `TauCeti.CStarModuleUnitary.conjStarAlgEquiv`: conjugation `T ↦ U ∘ T ∘ U*` as a unital
  `⋆`-algebra isomorphism `AdjointableMap A E E ≃⋆ₐ[ℂ] AdjointableMap A F F`.
* `TauCeti.CStarModuleUnitary.ofSurjective`: upgrades any plain surjective inner-product-preserving
  function `E → F` to a `CStarModuleUnitary A E F` (Lance, Theorem 3.5).
* `TauCeti.CStarModuleUnitary.ofAdjointableMap` and
  `TauCeti.CStarModuleUnitary.equivSubtypeAdjointableMap`: equivalence between
  `CStarModuleUnitary A E F` and `{T : AdjointableMap A E F // T* ∘ T = id_E ∧ T ∘ T* = id_F}`.
* `TauCeti.CStarModuleUnitary.mulEquivUnitary`: group isomorphism between endomorphism module
  unitaries `CStarModuleUnitary A E E` and `unitary (AdjointableMap A E E)`.

## Main results

* `TauCeti.AdjointableMap.adjoint_comp_self_eq_id_iff` and
  `TauCeti.AdjointableMap.isClosed_range_of_adjoint_comp_self_eq_id`: inner-product
  characterizations and closed-range property of adjointable isometries.
* `TauCeti.AdjointableMap.mem_unitary_iff`: `U ∈ unitary (AdjointableMap A E E)` iff `U` is
  surjective and preserves the `A`-valued inner product.

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

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- An adjointable map `V : AdjointableMap A E F` satisfies `V* ∘ V = id_E` if and only if it
preserves all `A`-valued inner products. -/
theorem adjoint_comp_self_eq_id_iff (V : AdjointableMap A E F) :
    V.adjoint.comp V = .id A E ↔ ∀ x y : E, inner A (V x) (V y) = inner A x y := by
  refine ⟨fun h x y ↦ ?_, fun h ↦ ext fun y ↦ CStarModule.ext_inner_left (A := A) fun x ↦ ?_⟩
  · rw [V.inner_map_left, ← comp_apply, h, id_apply]
  · rw [comp_apply, ← V.inner_map_left, id_apply, h]

/-- An adjointable map `V : AdjointableMap A E F` satisfies `V* ∘ V = id_E` if and only if it
preserves all diagonal inner products `⟪x, x⟫_A`. -/
theorem adjoint_comp_self_eq_id_iff_self (V : AdjointableMap A E F) :
    V.adjoint.comp V = .id A E ↔ ∀ x : E, inner A (V x) (V x) = inner A x x := by
  rw [adjoint_comp_self_eq_id_iff, CStarModule.inner_map_eq_iff_forall_self]

theorem norm_map_of_adjoint_comp_self_eq_id {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = .id A E) (x : E) :
    ‖V x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_norm_inner_self (A := A), norm_eq_sqrt_norm_inner_self (A := A) (x := x),
    (adjoint_comp_self_eq_id_iff V).mp hV]

/-- Every adjointable isometry (`V* ∘ V = id_E`) is a metric isometry. -/
theorem isometry_of_adjoint_comp_self_eq_id {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = .id A E) :
    Isometry V :=
  AddMonoidHomClass.isometry_of_norm V (norm_map_of_adjoint_comp_self_eq_id hV)

/-- If `V* ∘ V = id_E`, then `V ∘ V*` is an adjointable star projection on `F` onto
`Set.range V`. -/
theorem isStarProjection_comp_adjoint {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = .id A E) :
    IsStarProjection (V.comp V.adjoint) :=
  ⟨by rw [IsIdempotentElem, mul_def, comp_assoc, ← comp_assoc V.adjoint V, hV, id_comp],
    by rw [IsSelfAdjoint, star_eq_adjoint, adjoint_comp, adjoint_adjoint]⟩

/-- For an adjointable isometry `V`, the range of the range projection `V ∘ V*` equals
`Set.range V`. -/
theorem range_comp_adjoint {V : AdjointableMap A E F} (hV : V.adjoint.comp V = .id A E) :
    Set.range (V.comp V.adjoint) = Set.range V :=
  Set.Subset.antisymm (by rintro _ ⟨y, rfl⟩; exact ⟨V.adjoint y, rfl⟩)
    (by rintro _ ⟨x, rfl⟩; exact ⟨V x, by rw [comp_apply, ← comp_apply V.adjoint, hV, id_apply]⟩)

/-- Every adjointable isometry `V : AdjointableMap A E F` has norm-closed range in `F` (even
without completeness of `E` or `F`). -/
theorem isClosed_range_of_adjoint_comp_self_eq_id {V : AdjointableMap A E F}
    (hV : V.adjoint.comp V = .id A E) :
    IsClosed (Set.range V) := by
  rw [← range_comp_adjoint hV]
  exact isClosed_range_of_isStarProjection (isStarProjection_comp_adjoint hV)

/-- An operator `U : AdjointableMap A E E` belongs to `unitary (AdjointableMap A E E)` if and only
if `U` is surjective and preserves the `A`-valued inner product. -/
theorem mem_unitary_iff {U : AdjointableMap A E E} :
    U ∈ unitary (AdjointableMap A E E) ↔
      Function.Surjective U ∧ ∀ x y : E, inner A (U x) (U y) = inner A x y := by
  rw [Unitary.mem_iff, star_eq_adjoint, mul_def, mul_def, one_def]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨fun y ↦ ⟨U.adjoint y, DFunLike.congr_fun h₂ y⟩,
      (adjoint_comp_self_eq_id_iff U).mp h₁⟩, fun ⟨hsurj, hinner⟩ ↦ ?_⟩
  have h₁ : U.adjoint.comp U = .id A E := (adjoint_comp_self_eq_id_iff U).mpr hinner
  refine ⟨h₁, ext fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hsurj y
  calc (U.comp U.adjoint) (U x) = U ((U.adjoint.comp U) x) := rfl
    _ = AdjointableMap.id A E (U x) := by rw [h₁, id_apply, id_apply]

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
structure CStarModuleUnitary (A E F : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
    extends E ≃ₗᵢ[ℂ] F where
  /-- A module unitary preserves the `A`-valued inner product. -/
  inner_map (x y : E) : inner A (toLinearIsometryEquiv x) (toLinearIsometryEquiv y) = inner A x y

namespace CStarModuleUnitary

variable {A E F G : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
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
theorem inner_apply (U : CStarModuleUnitary A E F) (x y : E) :
    inner A (U x) (U y) = inner A x y :=
  U.inner_map x y

/-- Right-module form `⟨U x, U y⟩_B = ⟨x, y⟩_B` of inner-product preservation. -/
theorem unop_inner_apply {B E₁ F₁ : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [SMul Bᵐᵒᵖ E₁] [CStarModule Bᵐᵒᵖ E₁]
    [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [SMul Bᵐᵒᵖ F₁] [CStarModule Bᵐᵒᵖ F₁]
    (U : CStarModuleUnitary Bᵐᵒᵖ E₁ F₁) (x y : E₁) :
    unop (inner Bᵐᵒᵖ (U x) (U y)) = unop (inner Bᵐᵒᵖ x y) :=
  congrArg unop (U.inner_apply x y)

/-- The identity unitary on a Hilbert C⋆-module. -/
@[expose] protected def refl (A E : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] :
    CStarModuleUnitary A E E where
  toLinearIsometryEquiv := LinearIsometryEquiv.refl ℂ E
  inner_map _ _ := rfl

instance instInhabited : Inhabited (CStarModuleUnitary A E E) := ⟨.refl A E⟩

@[simp]
theorem refl_apply (x : E) : CStarModuleUnitary.refl A E x = x := (rfl)

/-- The inverse of a Hilbert C⋆-module unitary. -/
@[expose] def symm (U : CStarModuleUnitary A E F) : CStarModuleUnitary A F E where
  toLinearIsometryEquiv := U.toLinearIsometryEquiv.symm
  inner_map x y := by
    calc inner A (U.toLinearIsometryEquiv.symm x) (U.toLinearIsometryEquiv.symm y)
        = inner A (U (U.toLinearIsometryEquiv.symm x)) (U (U.toLinearIsometryEquiv.symm y)) :=
          (U.inner_apply _ _).symm
      _ = inner A x y := by
          rw [← toLinearIsometryEquiv_apply, ← toLinearIsometryEquiv_apply,
            U.toLinearIsometryEquiv.apply_symm_apply, U.toLinearIsometryEquiv.apply_symm_apply]

@[simp]
theorem toLinearIsometryEquiv_symm (U : CStarModuleUnitary A E F) :
    U.symm.toLinearIsometryEquiv = U.toLinearIsometryEquiv.symm := (rfl)

@[simp]
theorem symm_symm (U : CStarModuleUnitary A E F) : U.symm.symm = U := (rfl)

@[simp]
theorem apply_symm_apply (U : CStarModuleUnitary A E F) (y : F) : U (U.symm y) = y :=
  U.toLinearIsometryEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (U : CStarModuleUnitary A E F) (x : E) : U.symm (U x) = x :=
  U.toLinearIsometryEquiv.symm_apply_apply x

@[simp]
theorem symm_refl : (CStarModuleUnitary.refl A E).symm = .refl A E := (rfl)

/-- Composition of Hilbert C⋆-module unitaries (`(U.trans V) x = V (U x)`). -/
@[expose] def trans (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) :
    CStarModuleUnitary A E G where
  toLinearIsometryEquiv := U.toLinearIsometryEquiv.trans V.toLinearIsometryEquiv
  inner_map x y := (V.inner_apply (U x) (U y)).trans (U.inner_apply x y)

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
    conv_lhs => rw [← U.apply_symm_apply y]
    exact U.inner_apply x (U.symm y)

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
theorem adjoint_toAdjointableMap (U : CStarModuleUnitary A E F) :
    U.toAdjointableMap.adjoint = U.symm.toAdjointableMap := (rfl)

@[simp]
theorem toAdjointableMap_refl :
    (CStarModuleUnitary.refl A E).toAdjointableMap = .id A E := (rfl)

@[simp]
theorem toAdjointableMap_trans (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) :
    (U.trans V).toAdjointableMap = V.toAdjointableMap.comp U.toAdjointableMap := (rfl)

@[simp]
theorem symm_toAdjointableMap_comp_toAdjointableMap (U : CStarModuleUnitary A E F) :
    U.symm.toAdjointableMap.comp U.toAdjointableMap = .id A E :=
  AdjointableMap.ext U.symm_apply_apply

@[simp]
theorem toAdjointableMap_comp_symm_toAdjointableMap (U : CStarModuleUnitary A E F) :
    U.toAdjointableMap.comp U.symm.toAdjointableMap = .id A F :=
  AdjointableMap.ext U.apply_symm_apply

theorem adjoint_comp_toAdjointableMap (U : CStarModuleUnitary A E F) :
    U.toAdjointableMap.adjoint.comp U.toAdjointableMap = .id A E :=
  U.symm_toAdjointableMap_comp_toAdjointableMap

theorem toAdjointableMap_comp_adjoint (U : CStarModuleUnitary A E F) :
    U.toAdjointableMap.comp U.toAdjointableMap.adjoint = .id A F :=
  U.toAdjointableMap_comp_symm_toAdjointableMap

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
  map_star' T := AdjointableMap.ext fun y ↦ by simp

@[simp]
theorem conjStarAlgEquiv_apply (U : CStarModuleUnitary A E F) (T : AdjointableMap A E E) :
    U.conjStarAlgEquiv T = (U.toAdjointableMap.comp T).comp U.symm.toAdjointableMap := (rfl)

@[simp]
theorem conjStarAlgEquiv_symm (U : CStarModuleUnitary A E F) :
    U.conjStarAlgEquiv.symm = U.symm.conjStarAlgEquiv := (rfl)

/-- Construct a Hilbert C⋆-module unitary from a plain surjective inner-product-preserving function
`f : E → F`, with no complex-linearity, `A`-linearity, continuity, or completeness hypotheses
(Lance, Theorem 3.5). -/
noncomputable def ofSurjective (f : E → F) (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    CStarModuleUnitary A E F :=
  -- Nondegeneracy gives injectivity, and `(f, f⁻¹)` is then an adjoint pair.
  have hf_inj : Function.Injective f := fun x y hxy ↦
    CStarModule.ext_inner_left (A := A) fun z ↦ by
      rw [← hf_inner z x, ← hf_inner z y, hxy]
  let e : E ≃ F := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hpair : LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip e e.symm :=
    CStarModule.isAdjointPair_inner_iff.mpr fun x y ↦ by
      conv_lhs => rw [← e.apply_symm_apply y]
      exact hf_inner x (e.symm y)
  have hf_norm (x : E) : ‖f x‖ = ‖x‖ := by
    rw [norm_eq_sqrt_norm_inner_self (A := A), norm_eq_sqrt_norm_inner_self (A := A) (x := x),
      hf_inner]
  { toLinearIsometryEquiv :=
      { toFun := f
        invFun := e.symm
        left_inv := e.left_inv
        right_inv := e.right_inv
        map_add' := hpair.map_add_cstarModule
        map_smul' := hpair.map_smul_cstarModule
        norm_map' := hf_norm }
    inner_map := hf_inner }

@[simp]
theorem ofSurjective_apply (f : E → F) (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) (x : E) :
    ofSurjective f hf_surj hf_inner x = f x := (rfl)

@[simp]
theorem coe_ofSurjective (f : E → F) (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    ⇑(ofSurjective f hf_surj hf_inner) = f :=
  funext (ofSurjective_apply f hf_surj hf_inner)

/-- Construct a Hilbert C⋆-module unitary from an invertible adjointable map `T` whose inverse is
its adjoint (`T* ∘ T = id_E` and `T ∘ T* = id_F`). -/
def ofAdjointableMap (T : AdjointableMap A E F)
    (h₁ : T.adjoint.comp T = .id A E) (h₂ : T.comp T.adjoint = .id A F) :
    CStarModuleUnitary A E F where
  toLinearIsometryEquiv :=
    { toFun := T
      invFun := T.adjoint
      left_inv := fun x ↦ DFunLike.congr_fun h₁ x
      right_inv := fun y ↦ DFunLike.congr_fun h₂ y
      map_add' := map_add T
      map_smul' := map_smul T
      norm_map' := AdjointableMap.norm_map_of_adjoint_comp_self_eq_id h₁ }
  inner_map := (AdjointableMap.adjoint_comp_self_eq_id_iff T).mp h₁

@[simp]
theorem ofAdjointableMap_apply (T : AdjointableMap A E F)
    (h₁ : T.adjoint.comp T = .id A E) (h₂ : T.comp T.adjoint = .id A F) (x : E) :
    ofAdjointableMap T h₁ h₂ x = T x := (rfl)

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

/-- Equivalence between Hilbert C⋆-module unitaries `CStarModuleUnitary A E F` and adjointable
operators `T : AdjointableMap A E F` whose inverse is their adjoint
(`T* ∘ T = id_E` and `T ∘ T* = id_F`). -/
def equivSubtypeAdjointableMap :
    CStarModuleUnitary A E F ≃
      {T : AdjointableMap A E F // T.adjoint.comp T = .id A E ∧ T.comp T.adjoint = .id A F} where
  toFun U := ⟨U.toAdjointableMap, U.adjoint_comp_toAdjointableMap, U.toAdjointableMap_comp_adjoint⟩
  invFun T := ofAdjointableMap T.1 T.2.1 T.2.2
  left_inv _ := ext fun _ ↦ rfl
  right_inv _ := Subtype.ext (AdjointableMap.ext fun _ ↦ rfl)

@[simp]
theorem coe_equivSubtypeAdjointableMap (U : CStarModuleUnitary A E F) :
    (equivSubtypeAdjointableMap U : AdjointableMap A E F) = U.toAdjointableMap := (rfl)

@[simp]
theorem equivSubtypeAdjointableMap_symm_apply
    (T : {T : AdjointableMap A E F // T.adjoint.comp T = .id A E ∧ T.comp T.adjoint = .id A F}) :
    equivSubtypeAdjointableMap.symm T = ofAdjointableMap T.1 T.2.1 T.2.2 := (rfl)

/-! #### Group structure on endomorphism unitaries and comparison with `unitary` -/

instance instOne : One (CStarModuleUnitary A E E) := ⟨.refl A E⟩

instance instMul : Mul (CStarModuleUnitary A E E) := ⟨fun U V ↦ V.trans U⟩

instance instInv : Inv (CStarModuleUnitary A E E) := ⟨symm⟩

@[simp] theorem one_apply (x : E) : (1 : CStarModuleUnitary A E E) x = x := (rfl)
@[simp] theorem mul_apply (U V : CStarModuleUnitary A E E) (x : E) : (U * V) x = U (V x) := (rfl)
@[simp] theorem inv_apply (U : CStarModuleUnitary A E E) : U⁻¹ = U.symm := (rfl)

instance instGroup : Group (CStarModuleUnitary A E E) where
  mul_assoc _ _ _ := ext fun x ↦ by simp
  one_mul _ := ext fun x ↦ by simp
  mul_one _ := ext fun x ↦ by simp
  inv_mul_cancel _ := ext fun x ↦ by simp

/-- Endomorphism module unitaries `CStarModuleUnitary A E E` are canonically isomorphic as a group
to `unitary (AdjointableMap A E E)`. -/
def mulEquivUnitary : CStarModuleUnitary A E E ≃* unitary (AdjointableMap A E E) where
  toFun U := ⟨U.toAdjointableMap, by
    rw [Unitary.mem_iff, AdjointableMap.star_eq_adjoint, AdjointableMap.mul_def,
      AdjointableMap.mul_def, AdjointableMap.one_def]
    exact ⟨U.adjoint_comp_toAdjointableMap, U.toAdjointableMap_comp_adjoint⟩⟩
  invFun U :=
    have hU : (U : AdjointableMap A E E).adjoint.comp U = .id A E ∧
        (U : AdjointableMap A E E).comp (U : AdjointableMap A E E).adjoint = .id A E := by
      simpa only [Unitary.mem_iff, AdjointableMap.star_eq_adjoint, AdjointableMap.mul_def,
        AdjointableMap.one_def] using U.2
    ofAdjointableMap (U : AdjointableMap A E E) hU.1 hU.2
  left_inv _ := ext fun _ ↦ rfl
  right_inv _ := Subtype.ext (AdjointableMap.ext fun _ ↦ rfl)
  map_mul' _ _ := Subtype.ext (AdjointableMap.ext fun _ ↦ rfl)

@[simp]
theorem coe_mulEquivUnitary (U : CStarModuleUnitary A E E) :
    (mulEquivUnitary U : AdjointableMap A E E) = U.toAdjointableMap := (rfl)

@[simp]
theorem mulEquivUnitary_symm_apply (U : unitary (AdjointableMap A E E)) (x : E) :
    mulEquivUnitary.symm U x = (U : AdjointableMap A E E) x := (rfl)

end CStarModuleUnitary

end TauCeti
