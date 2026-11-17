/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Basic

/-!
# Unitary equivalences of Hilbert C⋆-modules

This file defines bundled unitary equivalences `TauCeti.CStarModuleEquiv A E F` between Hilbert
C⋆-modules over `A` and establishes Lance's characterization (Theorem 3.5): a plain function
`f : E → F` is an invertible adjointable operator whose inverse is its adjoint if and only if `f`
is surjective and preserves the `A`-valued inner product (`CStarModuleEquiv.ofSurjectiveInner`,
`AdjointableMap.adjoint_comp_self_and_self_comp_adjoint_iff`,
`AdjointableMap.exists_adjoint_comp_eq_id_iff`, and `AdjointableMap.mem_unitary_iff`). Neither
linearity, continuity, compatibility with the `A`-action, nor completeness of `E` or `F` is assumed
in this characterization.

For endomorphisms, `CStarModuleEquiv.toUnitary` identifies the group `CStarModuleEquiv A E E`
canonically with `unitary (AdjointableMap A E E)`.

## Main declarations

* `TauCeti.CStarModuleEquiv`: unitary equivalences between Hilbert C⋆-modules over `A`.
* `TauCeti.CStarModuleEquiv.ofSurjectiveInner`: Lance's Theorem 3.5, constructing a module unitary
  from any surjective inner-product-preserving function.
* `TauCeti.CStarModuleEquiv.ofAdjointable`, `TauCeti.CStarModuleEquiv.toAdjointableMap`:
  bijection between module unitaries and adjoint-unitary operators in `L_A(E, F)`.
* `TauCeti.CStarModuleEquiv.toUnitary`: the group isomorphism
  `CStarModuleEquiv A E E ≃* unitary (AdjointableMap A E E)`.
* `TauCeti.AdjointableMap.mem_unitary_iff`: `T ∈ unitary L_A(E)` if and only if `T` is surjective
  and preserves the `A`-valued inner product.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 3
  (Theorem 3.5).
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
-/

public section

namespace TauCeti

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

variable {A E F G H : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul A H] [CStarModule A H]

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

@[simp]
theorem toLinearIsometryEquiv_refl :
    (refl A E).toLinearIsometryEquiv = LinearIsometryEquiv.refl ℂ E := (rfl)

/-- The inverse of a module unitary is a module unitary. -/
def symm (U : CStarModuleEquiv A E F) : CStarModuleEquiv A F E where
  toLinearIsometryEquiv := U.toLinearIsometryEquiv.symm
  inner_map x y := by
    simpa only [toLinearIsometryEquiv_apply, U.toLinearIsometryEquiv.apply_symm_apply] using
      (U.inner_map (U.toLinearIsometryEquiv.symm x) (U.toLinearIsometryEquiv.symm y)).symm

@[simp]
theorem toLinearIsometryEquiv_symm (U : CStarModuleEquiv A E F) :
    U.symm.toLinearIsometryEquiv = U.toLinearIsometryEquiv.symm := (rfl)

@[simp]
theorem symm_symm (U : CStarModuleEquiv A E F) : U.symm.symm = U := (rfl)

@[simp]
theorem refl_symm : (refl A E).symm = refl A E := (rfl)

@[simp]
theorem apply_symm_apply (U : CStarModuleEquiv A E F) (y : F) : U (U.symm y) = y :=
  U.toLinearIsometryEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (U : CStarModuleEquiv A E F) (x : E) : U.symm (U x) = x :=
  U.toLinearIsometryEquiv.symm_apply_apply x

theorem symm_apply_eq (U : CStarModuleEquiv A E F) {x : E} {y : F} :
    U.symm y = x ↔ y = U x :=
  U.toLinearIsometryEquiv.symm_apply_eq

theorem eq_symm_apply (U : CStarModuleEquiv A E F) {x : E} {y : F} :
    x = U.symm y ↔ U x = y :=
  U.toLinearIsometryEquiv.eq_symm_apply

/-- Composition of module unitaries. -/
def trans (U : CStarModuleEquiv A E F) (V : CStarModuleEquiv A F G) :
    CStarModuleEquiv A E G where
  toLinearIsometryEquiv := U.toLinearIsometryEquiv.trans V.toLinearIsometryEquiv
  inner_map x y := (V.inner_apply (U x) (U y)).trans (U.inner_apply x y)

@[simp]
theorem trans_apply (U : CStarModuleEquiv A E F) (V : CStarModuleEquiv A F G) (x : E) :
    U.trans V x = V (U x) := (rfl)

@[simp]
theorem toLinearIsometryEquiv_trans (U : CStarModuleEquiv A E F) (V : CStarModuleEquiv A F G) :
    (U.trans V).toLinearIsometryEquiv =
      U.toLinearIsometryEquiv.trans V.toLinearIsometryEquiv := (rfl)

@[simp]
theorem symm_trans (U : CStarModuleEquiv A E F) (V : CStarModuleEquiv A F G) :
    (U.trans V).symm = V.symm.trans U.symm := (rfl)

@[simp]
theorem refl_trans (U : CStarModuleEquiv A E F) : (refl A E).trans U = U :=
  ext fun _ => rfl

@[simp]
theorem trans_refl (U : CStarModuleEquiv A E F) : U.trans (refl A F) = U :=
  ext fun _ => rfl

theorem trans_assoc (U : CStarModuleEquiv A E F) (V : CStarModuleEquiv A F G)
    (W : CStarModuleEquiv A G H) :
    (U.trans V).trans W = U.trans (V.trans W) := (rfl)

@[simp]
theorem symm_trans_self (U : CStarModuleEquiv A E F) : U.symm.trans U = refl A F :=
  ext U.apply_symm_apply

@[simp]
theorem self_trans_symm (U : CStarModuleEquiv A E F) : U.trans U.symm = refl A E :=
  ext U.symm_apply_apply

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

theorem toAdjointableMap_injective :
    Function.Injective (toAdjointableMap : CStarModuleEquiv A E F → AdjointableMap A E F) :=
  fun _ _ h => ext fun x => DFunLike.congr_fun h x

@[simp]
theorem toAdjointableMap_refl :
    (refl A E).toAdjointableMap = AdjointableMap.id A E :=
  AdjointableMap.ext fun _ => by simp

@[simp]
theorem toAdjointableMap_trans (U : CStarModuleEquiv A E F) (V : CStarModuleEquiv A F G) :
    (U.trans V).toAdjointableMap = V.toAdjointableMap.comp U.toAdjointableMap :=
  AdjointableMap.ext fun _ => by simp

@[simp]
theorem adjoint_toAdjointableMap (U : CStarModuleEquiv A E F) :
    U.toAdjointableMap.adjoint = U.symm.toAdjointableMap :=
  AdjointableMap.ext fun _ => by
    rw [← AdjointableMap.adjointContinuousLinearMap_apply]
    rfl

@[simp]
theorem symm_comp_toAdjointableMap (U : CStarModuleEquiv A E F) :
    U.symm.toAdjointableMap.comp U.toAdjointableMap = AdjointableMap.id A E :=
  AdjointableMap.ext fun _ => by simp

@[simp]
theorem toAdjointableMap_comp_symm (U : CStarModuleEquiv A E F) :
    U.toAdjointableMap.comp U.symm.toAdjointableMap = AdjointableMap.id A F :=
  AdjointableMap.ext fun _ => by simp

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
      (LinearMap.ext fun y => by
        simpa [AdjointableMap.comp_apply, AdjointableMap.id_apply] using DFunLike.congr_fun h₂ y)
      (LinearMap.ext fun x => by
        simpa [AdjointableMap.comp_apply, AdjointableMap.id_apply] using DFunLike.congr_fun h₁ x)
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

theorem mul_def (U V : CStarModuleEquiv A E E) : U * V = V.trans U := (rfl)
theorem one_def : (1 : CStarModuleEquiv A E E) = refl A E := (rfl)
theorem inv_def (U : CStarModuleEquiv A E E) : U⁻¹ = U.symm := (rfl)

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
  map_mul' _ _ := Subtype.ext (AdjointableMap.ext fun _ => by simp)

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
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨fun y => ⟨T.adjoint y, by
      simpa [comp_apply, id_apply] using DFunLike.congr_fun h₂ y⟩,
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

end AdjointableMap

end TauCeti
