/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable

/-!
# Hilbert C⋆-module unitaries

A *unitary* between Hilbert C⋆-modules `E` and `F` over `A` (with right Hilbert `B`-modules
represented as `CStarModule Bᵐᵒᵖ E` and `CStarModule Bᵐᵒᵖ F`) is a surjective map `U : E → F`
preserving the `A`-valued inner product (`⟪U x, U y⟫_A = ⟪x, y⟫_A`). Nondegeneracy of the module
inner product forces any such map to be injective, `ℂ`-linear, `A`-linear, and norm-preserving
(`CStarModuleUnitary.ofSurjective`, `CStarModuleUnitary.norm_map`), without completeness or
boundedness assumptions.

On normed Hilbert C⋆-modules, Hilbert-module unitaries correspond canonically to invertible
adjointable operators whose inverse is their adjoint (`T* ∘ T = id` and `T ∘ T* = id`), and on a
single module `E` they form a group canonically isomorphic to `unitary (AdjointableMap A E E)`
(Lance, Chapter 3; Raeburn–Williams, Lemma 2.18). Every Hilbert-module unitary `U : E ≅ F` also
induces a unital `⋆`-algebra isomorphism `AdjointableMap A E E ≃⋆ₐ[ℂ] AdjointableMap A F F` by
conjugation `T ↦ U ∘ T ∘ U*`.

## Main declarations

* `TauCeti.CStarModuleUnitary`: bundled Hilbert-module unitary `E ≅ F` extending `E ≃ₗ[ℂ] F` with
  `⟪U x, U y⟫_A = ⟪x, y⟫_A`.
* `TauCeti.CStarModuleUnitary.ofSurjective`: constructs a `CStarModuleUnitary` from a plain
  surjective inner-product-preserving function `E → F`.
* `TauCeti.CStarModuleUnitary.equivAdjointableMap`: equivalence between `CStarModuleUnitary A E F`
  and `{ T : AdjointableMap A E F // T.adjoint.comp T = .id ∧ T.comp T.adjoint = .id }`.
* `TauCeti.AdjointableMap.adjoint_comp_self_and_self_comp_adjoint_eq_id_iff`,
  `TauCeti.AdjointableMap.exists_coe_eq_and_adjoint_comp_self_and_self_comp_adjoint_eq_id_iff`:
  equivalence between surjective inner-product-preserving maps and invertible adjointable maps
  whose inverse is their adjoint.
* `TauCeti.AdjointableMap.mem_unitary_iff`, `TauCeti.CStarModuleUnitary.mulEquivUnitary`:
  identification of `CStarModuleUnitary A E E` with `unitary (AdjointableMap A E E)`.
* `TauCeti.CStarModuleUnitary.conj`: conjugation `⋆`-algebra equivalence
  `AdjointableMap A E E ≃⋆ₐ[ℂ] AdjointableMap A F F`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 3.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Lemma 2.18.
-/

public section

open CStarModule MulOpposite

namespace TauCeti

/-- A unitary isomorphism between Hilbert C⋆-modules `E` and `F` over `A` (take `A = Bᵐᵒᵖ` for right
Hilbert `B`-modules): a `ℂ`-linear equivalence preserving the `A`-valued inner product.
Compatibility with the `A`-action and norm preservation follow automatically; moreover, any plain
surjective inner-product-preserving function `E → F` upgrades to a `CStarModuleUnitary` via
`CStarModuleUnitary.ofSurjective`. -/
structure CStarModuleUnitary (A E F : Type*)
    [AddCommMonoid E] [Module ℂ E] [Inner A E]
    [AddCommMonoid F] [Module ℂ F] [Inner A F]
    extends E ≃ₗ[ℂ] F where
  /-- A Hilbert-module unitary preserves the `A`-valued inner product. -/
  inner_map_map' (x y : E) : inner A (toLinearEquiv x) (toLinearEquiv y) = inner A x y

namespace CStarModuleUnitary

section Algebraic

variable {A E F : Type*}
  [AddCommMonoid E] [Module ℂ E] [Inner A E]
  [AddCommMonoid F] [Module ℂ F] [Inner A F]

theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : CStarModuleUnitary A E F → (E ≃ₗ[ℂ] F)) := by
  rintro ⟨e₁, _⟩ ⟨e₂, _⟩ rfl; rfl

instance instEquivLike : EquivLike (CStarModuleUnitary A E F) E F where
  coe U := U.toLinearEquiv
  inv U := U.toLinearEquiv.symm
  left_inv U := U.toLinearEquiv.left_inv
  right_inv U := U.toLinearEquiv.right_inv
  coe_injective' _ _ h _ := toLinearEquiv_injective (DFunLike.coe_injective h)

instance instLinearEquivClass : LinearEquivClass (CStarModuleUnitary A E F) ℂ E F where
  map_add U := U.toLinearEquiv.map_add
  map_smulₛₗ U := U.toLinearEquiv.map_smul

@[simp]
theorem coe_toLinearEquiv (U : CStarModuleUnitary A E F) : ⇑U.toLinearEquiv = ⇑U := (rfl)

@[simp]
theorem toLinearEquiv_apply (U : CStarModuleUnitary A E F) (x : E) :
    U.toLinearEquiv x = U x := (rfl)

@[simp]
theorem coe_mk (e : E ≃ₗ[ℂ] F)
    (h : ∀ x y : E, inner A (e x) (e y) = inner A x y) :
    ⇑(mk e h : CStarModuleUnitary A E F) = ⇑e := (rfl)

@[simp]
theorem toLinearEquiv_mk (e : E ≃ₗ[ℂ] F)
    (h : ∀ x y : E, inner A (e x) (e y) = inner A x y) :
    (mk e h : CStarModuleUnitary A E F).toLinearEquiv = e := (rfl)

@[ext]
theorem ext {U V : CStarModuleUnitary A E F} (h : ∀ x, U x = V x) : U = V :=
  DFunLike.ext U V h

@[simp]
theorem inner_map_map (U : CStarModuleUnitary A E F) (x y : E) :
    inner A (U x) (U y) = inner A x y :=
  U.inner_map_map' x y

/-- The inverse Hilbert-module unitary `F ≅ E`. -/
def symm (U : CStarModuleUnitary A E F) : CStarModuleUnitary A F E where
  toLinearEquiv := U.toLinearEquiv.symm
  inner_map_map' x y := by
    rw [← U.inner_map_map (U.toLinearEquiv.symm x) (U.toLinearEquiv.symm y),
      ← toLinearEquiv_apply, ← toLinearEquiv_apply,
      U.toLinearEquiv.apply_symm_apply, U.toLinearEquiv.apply_symm_apply]

@[simp]
theorem toLinearEquiv_symm (U : CStarModuleUnitary A E F) :
    U.symm.toLinearEquiv = U.toLinearEquiv.symm := (rfl)

@[simp]
theorem coe_symm_toLinearEquiv (U : CStarModuleUnitary A E F) :
    ⇑U.toLinearEquiv.symm = ⇑U.symm := (rfl)

@[simp]
theorem toLinearEquiv_symm_apply (U : CStarModuleUnitary A E F) (y : F) :
    U.toLinearEquiv.symm y = U.symm y := (rfl)

@[simp]
theorem symm_symm (U : CStarModuleUnitary A E F) : U.symm.symm = U := ext fun _ => rfl

@[simp]
theorem symm_apply_apply (U : CStarModuleUnitary A E F) (x : E) : U.symm (U x) = x :=
  U.toLinearEquiv.symm_apply_apply x

@[simp]
theorem apply_symm_apply (U : CStarModuleUnitary A E F) (y : F) : U (U.symm y) = y :=
  U.toLinearEquiv.apply_symm_apply y

/-- The inverse of a Hilbert-module unitary is its adjoint for the `A`-valued inner product:
`⟪U x, y⟫_A = ⟪x, U.symm y⟫_A`. -/
theorem inner_map_left (U : CStarModuleUnitary A E F) (x : E) (y : F) :
    inner A (U x) y = inner A x (U.symm y) := by
  conv_lhs => rw [← U.apply_symm_apply y, U.inner_map_map]

theorem inner_map_right (U : CStarModuleUnitary A E F) (y : F) (x : E) :
    inner A y (U x) = inner A (U.symm y) x :=
  (U.symm.inner_map_left y x).symm

end Algebraic

section Right

variable {B E F : Type*}
  [AddCommMonoid E] [Module ℂ E] [Inner Bᵐᵒᵖ E]
  [AddCommMonoid F] [Module ℂ F] [Inner Bᵐᵒᵖ F]

theorem unop_inner_map_map (U : CStarModuleUnitary Bᵐᵒᵖ E F) (x y : E) :
    unop (inner Bᵐᵒᵖ (U x) (U y)) = unop (inner Bᵐᵒᵖ x y) :=
  congrArg unop (U.inner_map_map x y)

end Right

section ReflTrans

variable {A E F G H : Type*}
  [AddCommMonoid E] [Module ℂ E] [Inner A E]
  [AddCommMonoid F] [Module ℂ F] [Inner A F]
  [AddCommMonoid G] [Module ℂ G] [Inner A G]
  [AddCommMonoid H] [Module ℂ H] [Inner A H]

/-- The identity Hilbert-module unitary on `E`. -/
def refl : CStarModuleUnitary A E E where
  toLinearEquiv := LinearEquiv.refl ℂ E
  inner_map_map' _ _ := rfl

@[simp]
theorem toLinearEquiv_refl : (refl : CStarModuleUnitary A E E).toLinearEquiv = .refl ℂ E := (rfl)

@[simp]
theorem refl_apply (x : E) : (refl : CStarModuleUnitary A E E) x = x := (rfl)

/-- Diagrammatic composition of Hilbert-module unitaries (`(U.trans V) x = V (U x)`). -/
def trans (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) :
    CStarModuleUnitary A E G where
  toLinearEquiv := U.toLinearEquiv.trans V.toLinearEquiv
  inner_map_map' x y := (V.inner_map_map (U x) (U y)).trans (U.inner_map_map x y)

@[simp]
theorem toLinearEquiv_trans (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) :
    (U.trans V).toLinearEquiv = U.toLinearEquiv.trans V.toLinearEquiv := (rfl)

@[simp]
theorem trans_apply (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) (x : E) :
    (U.trans V) x = V (U x) := (rfl)

@[simp]
theorem refl_symm : (refl : CStarModuleUnitary A E E).symm = refl := ext fun _ => rfl

@[simp]
theorem trans_refl (U : CStarModuleUnitary A E F) : U.trans refl = U := ext fun _ => rfl

@[simp]
theorem refl_trans (U : CStarModuleUnitary A E F) : refl.trans U = U := ext fun _ => rfl

@[simp]
theorem symm_trans (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) :
    (U.trans V).symm = V.symm.trans U.symm := ext fun _ => rfl

@[simp]
theorem self_trans_symm (U : CStarModuleUnitary A E F) :
    U.trans U.symm = refl := ext U.symm_apply_apply

@[simp]
theorem symm_trans_self (U : CStarModuleUnitary A E F) :
    U.symm.trans U = refl := ext U.apply_symm_apply

theorem trans_assoc (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G)
    (W : CStarModuleUnitary A G H) :
    U.trans (V.trans W) = (U.trans V).trans W := ext fun _ => rfl

instance instGroup : Group (CStarModuleUnitary A E E) where
  mul U V := V.trans U
  one := refl
  inv := symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_assoc _ _ _ := trans_assoc _ _ _
  inv_mul_cancel := self_trans_symm

theorem one_def : (1 : CStarModuleUnitary A E E) = refl := (rfl)

theorem mul_def (U V : CStarModuleUnitary A E E) : U * V = V.trans U := (rfl)

theorem inv_def (U : CStarModuleUnitary A E E) : U⁻¹ = U.symm := (rfl)

@[simp]
theorem one_apply (x : E) : (1 : CStarModuleUnitary A E E) x = x := (rfl)

@[simp]
theorem mul_apply (U V : CStarModuleUnitary A E E) (x : E) : (U * V) x = U (V x) := (rfl)

@[simp]
theorem inv_apply (U : CStarModuleUnitary A E E) (x : E) : U⁻¹ x = U.symm x := (rfl)

end ReflTrans

section CStarModuleNorm

variable {A E F : Type*}
  [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]

/-- Every Hilbert-module unitary preserves the module norm: `‖U x‖ = ‖x‖`. -/
@[simp]
theorem norm_map (U : CStarModuleUnitary A E F) (x : E) : ‖U x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (U x),
    CStarModule.norm_eq_sqrt_norm_inner_self (A := A) x, U.inner_map_map]

end CStarModuleNorm

section CStarModuleRing

variable {A E F : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]

/-- Every Hilbert-module unitary commutes with the `A`-action. -/
@[simp]
theorem map_smul_coeff (U : CStarModuleUnitary A E F) (a : A) (x : E) :
    U (a • x) = a • U x :=
  (CStarModule.isAdjointable_def.mpr ⟨U.symm, U.inner_map_left⟩).map_smul_coeff a x

/-- Construct a `CStarModuleUnitary` from a plain surjective function `f : E → F` preserving the
`A`-valued inner product (Lance, Chapter 3). Injectivity, `ℂ`-linearity, and `A`-linearity follow
automatically from nondegeneracy of the module inner product. -/
noncomputable def ofSurjective {f : E → F} (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    CStarModuleUnitary A E F :=
  have hadj : CStarModule.IsAdjointable A f :=
    CStarModule.isAdjointable_def.mpr ⟨Function.surjInv hf_surj, fun x y => by
      rw [← hf_inner x (Function.surjInv hf_surj y), Function.surjInv_eq hf_surj]⟩
  { toFun := f
    invFun := Function.surjInv hf_surj
    left_inv x := CStarModule.ext_inner_left (A := A) fun z => by
      rw [← hf_inner z (Function.surjInv hf_surj (f x)), Function.surjInv_eq hf_surj, hf_inner]
    right_inv := Function.surjInv_eq hf_surj
    map_add' := hadj.map_add
    map_smul' := hadj.map_smul
    inner_map_map' := hf_inner }

@[simp]
theorem ofSurjective_apply {f : E → F} (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) (x : E) :
    ofSurjective hf_surj hf_inner x = f x := (rfl)

@[simp]
theorem coe_ofSurjective {f : E → F} (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    ⇑(ofSurjective hf_surj hf_inner) = f := (rfl)

end CStarModuleRing

section Seminormed

variable {A E F : Type*}
  [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [SeminormedAddCommGroup E] [Module ℂ E] [SMul A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [SMul A F] [CStarModule A F]

/-- Forget the `A`-inner-product structure to obtain a `ℂ`-linear isometric equivalence
`E ≃ₗᵢ[ℂ] F`. -/
def toLinearIsometryEquiv (U : CStarModuleUnitary A E F) : E ≃ₗᵢ[ℂ] F :=
  { U.toLinearEquiv with norm_map' := U.norm_map }

@[simp]
theorem toLinearIsometryEquiv_apply (U : CStarModuleUnitary A E F) (x : E) :
    U.toLinearIsometryEquiv x = U x := (rfl)

@[simp]
theorem toLinearIsometryEquiv_symm_apply (U : CStarModuleUnitary A E F) (y : F) :
    U.toLinearIsometryEquiv.symm y = U.symm y := (rfl)

end Seminormed

/-! ### Equivalence with unitary adjointable operators -/

section Normed

variable {A E F G : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

/-- View a Hilbert-module unitary `U : CStarModuleUnitary A E F` as an adjointable operator
`AdjointableMap A E F`, with adjoint `U.symm`. -/
def toAdjointableMap (U : CStarModuleUnitary A E F) : AdjointableMap A E F where
  toContinuousLinearMap := U.toLinearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  adjointContinuousLinearMap :=
    U.symm.toLinearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  inner_map_eq' x y := by simpa using U.inner_map_left x y

@[simp]
theorem toAdjointableMap_apply (U : CStarModuleUnitary A E F) (x : E) :
    U.toAdjointableMap x = U x := by
  rw [← AdjointableMap.toContinuousLinearMap_apply]
  simp [toAdjointableMap]

@[simp]
theorem coe_toAdjointableMap (U : CStarModuleUnitary A E F) :
    ⇑U.toAdjointableMap = ⇑U :=
  funext U.toAdjointableMap_apply

@[simp]
theorem adjoint_toAdjointableMap (U : CStarModuleUnitary A E F) :
    U.toAdjointableMap.adjoint = U.symm.toAdjointableMap :=
  AdjointableMap.ext_inner_left fun x y => by
    rw [← U.toAdjointableMap.inner_map_left, toAdjointableMap_apply, toAdjointableMap_apply,
      U.inner_map_left]

theorem adjoint_comp_toAdjointableMap (U : CStarModuleUnitary A E F) :
    U.toAdjointableMap.adjoint.comp U.toAdjointableMap = .id := by ext x; simp

theorem toAdjointableMap_comp_adjoint (U : CStarModuleUnitary A E F) :
    U.toAdjointableMap.comp U.toAdjointableMap.adjoint = .id := by ext y; simp

@[simp]
theorem toAdjointableMap_refl :
    (refl : CStarModuleUnitary A E E).toAdjointableMap = 1 := by ext x; simp

@[simp]
theorem toAdjointableMap_trans (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) :
    (U.trans V).toAdjointableMap = V.toAdjointableMap.comp U.toAdjointableMap := by ext x; simp

@[simp]
theorem toAdjointableMap_one :
    (1 : CStarModuleUnitary A E E).toAdjointableMap = 1 := toAdjointableMap_refl

@[simp]
theorem toAdjointableMap_mul (U V : CStarModuleUnitary A E E) :
    (U * V).toAdjointableMap = U.toAdjointableMap * V.toAdjointableMap := by ext x; simp

@[simp]
theorem toAdjointableMap_inv (U : CStarModuleUnitary A E E) :
    (U⁻¹).toAdjointableMap = U.symm.toAdjointableMap := by
  rw [inv_def]

/-- Construct a `CStarModuleUnitary A E F` from an adjointable operator `T` whose adjoint is its
two-sided inverse (`T* ∘ T = id` and `T ∘ T* = id`). -/
def ofAdjointableMap (T : AdjointableMap A E F)
    (h₁ : T.adjoint.comp T = .id) (h₂ : T.comp T.adjoint = .id) :
    CStarModuleUnitary A E F where
  toFun := T
  invFun := T.adjoint
  left_inv x := by simpa using congrArg (· x) h₁
  right_inv y := by simpa using congrArg (· y) h₂
  map_add' := T.map_add
  map_smul' := T.map_smul
  inner_map_map' := AdjointableMap.adjoint_comp_self_eq_id_iff.mp h₁

@[simp]
theorem ofAdjointableMap_apply (T : AdjointableMap A E F)
    (h₁ : T.adjoint.comp T = .id) (h₂ : T.comp T.adjoint = .id) (x : E) :
    ofAdjointableMap T h₁ h₂ x = T x := (rfl)

@[simp]
theorem symm_ofAdjointableMap_apply (T : AdjointableMap A E F)
    (h₁ : T.adjoint.comp T = .id) (h₂ : T.comp T.adjoint = .id) (y : F) :
    (ofAdjointableMap T h₁ h₂).symm y = T.adjoint y := (rfl)

/-- Canonical equivalence between Hilbert-module unitaries `CStarModuleUnitary A E F` and
invertible adjointable operators whose inverse is their adjoint. -/
def equivAdjointableMap :
    CStarModuleUnitary A E F ≃
      { T : AdjointableMap A E F // T.adjoint.comp T = .id ∧ T.comp T.adjoint = .id } where
  toFun U := ⟨U.toAdjointableMap, U.adjoint_comp_toAdjointableMap, U.toAdjointableMap_comp_adjoint⟩
  invFun T := ofAdjointableMap T.1 T.2.1 T.2.2
  left_inv U := by ext x; simp
  right_inv T := by ext x; simp

@[simp]
theorem coe_equivAdjointableMap (U : CStarModuleUnitary A E F) :
    (equivAdjointableMap U : AdjointableMap A E F) = U.toAdjointableMap := (rfl)

@[simp]
theorem equivAdjointableMap_symm_apply
    (T : { T : AdjointableMap A E F // T.adjoint.comp T = .id ∧ T.comp T.adjoint = .id }) (x : E) :
    equivAdjointableMap.symm T x = T.1 x := (rfl)

/-- Group isomorphism between `CStarModuleUnitary A E E` and the unitary group
`unitary (AdjointableMap A E E)`. -/
def mulEquivUnitary : CStarModuleUnitary A E E ≃* unitary (AdjointableMap A E E) where
  toFun U := ⟨U.toAdjointableMap, by
    rw [Unitary.mem_iff, AdjointableMap.star_def, AdjointableMap.mul_def,
      AdjointableMap.mul_def, AdjointableMap.one_def]
    exact ⟨U.adjoint_comp_toAdjointableMap, U.toAdjointableMap_comp_adjoint⟩⟩
  invFun T :=
    have hT : T.1.adjoint.comp T.1 = .id ∧ T.1.comp T.1.adjoint = .id := by
      simpa only [Unitary.mem_iff, AdjointableMap.star_def, AdjointableMap.mul_def,
        AdjointableMap.one_def] using T.2
    ofAdjointableMap T.1 hT.1 hT.2
  left_inv U := by ext x; simp
  right_inv T := by ext x; simp
  map_mul' U V := by ext x; simp

@[simp]
theorem coe_mulEquivUnitary (U : CStarModuleUnitary A E E) :
    (mulEquivUnitary U : AdjointableMap A E E) = U.toAdjointableMap := (rfl)

@[simp]
theorem mulEquivUnitary_symm_apply (u : unitary (AdjointableMap A E E)) (x : E) :
    mulEquivUnitary.symm u x = (u : AdjointableMap A E E) x := (rfl)

end Normed

section Conj

variable {A E F : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- Conjugation `T ↦ U ∘ T ∘ U*` by a Hilbert-module unitary `U : CStarModuleUnitary A E F` as a
unital `⋆`-algebra isomorphism `AdjointableMap A E E ≃⋆ₐ[ℂ] AdjointableMap A F F`. -/
def conj (U : CStarModuleUnitary A E F) :
    AdjointableMap A E E ≃⋆ₐ[ℂ] AdjointableMap A F F where
  toFun T := (U.toAdjointableMap.comp T).comp U.symm.toAdjointableMap
  invFun S := (U.symm.toAdjointableMap.comp S).comp U.toAdjointableMap
  left_inv T := by ext x; simp
  right_inv S := by ext y; simp
  map_mul' T₁ T₂ := by ext y; simp
  map_add' T₁ T₂ := by ext y; simp
  map_smul' c T := by ext y; simp
  map_star' T := by ext y; simp [AdjointableMap.star_def, AdjointableMap.comp_assoc]

theorem conj_apply (U : CStarModuleUnitary A E F) (T : AdjointableMap A E E) :
    U.conj T = (U.toAdjointableMap.comp T).comp U.symm.toAdjointableMap := (rfl)

@[simp]
theorem conj_apply_apply (U : CStarModuleUnitary A E F) (T : AdjointableMap A E E) (y : F) :
    U.conj T y = U (T (U.symm y)) := by simp [conj_apply]

@[simp]
theorem conj_symm (U : CStarModuleUnitary A E F) : U.conj.symm = U.symm.conj :=
  StarAlgEquiv.ext fun S => U.conj.symm_apply_eq.mpr <| by ext y; simp

end Conj

end CStarModuleUnitary

namespace AdjointableMap

variable {A E F : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- An adjointable operator `T : AdjointableMap A E F` has its adjoint as its two-sided inverse
(`T* ∘ T = id` and `T ∘ T* = id`) if and only if it is surjective and preserves the `A`-valued
inner product (Lance, Chapter 3). -/
theorem adjoint_comp_self_and_self_comp_adjoint_eq_id_iff {T : AdjointableMap A E F} :
    T.adjoint.comp T = .id ∧ T.comp T.adjoint = .id ↔
      Function.Surjective T ∧ ∀ x y : E, inner A (T x) (T y) = inner A x y := by
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun ⟨hsurj, hinner⟩ => ?_⟩
  · exact ⟨fun y => ⟨T.adjoint y, by simpa using congrArg (· y) h₂⟩,
      adjoint_comp_self_eq_id_iff.mp h₁⟩
  · let U := CStarModuleUnitary.ofSurjective hsurj hinner
    have hTU : T = U.toAdjointableMap := by ext x; simp [U]
    rw [hTU]
    exact ⟨U.adjoint_comp_toAdjointableMap, U.toAdjointableMap_comp_adjoint⟩

/-- A plain function `f : E → F` between normed Hilbert C⋆-modules is the underlying map of an
invertible adjointable operator whose inverse is its adjoint if and only if `f` is surjective and
preserves the `A`-valued inner product. -/
theorem exists_coe_eq_and_adjoint_comp_self_and_self_comp_adjoint_eq_id_iff {f : E → F} :
    (∃ T : AdjointableMap A E F, ⇑T = f ∧ T.adjoint.comp T = .id ∧ T.comp T.adjoint = .id) ↔
      Function.Surjective f ∧ ∀ x y : E, inner A (f x) (f y) = inner A x y := by
  refine ⟨?_, fun ⟨hsurj, hinner⟩ => ?_⟩
  · rintro ⟨T, rfl, h₁, h₂⟩
    exact adjoint_comp_self_and_self_comp_adjoint_eq_id_iff.mp ⟨h₁, h₂⟩
  · let U := CStarModuleUnitary.ofSurjective hsurj hinner
    exact ⟨U.toAdjointableMap, by ext x; simp [U], U.adjoint_comp_toAdjointableMap,
      U.toAdjointableMap_comp_adjoint⟩

/-- An adjointable endomorphism `U : AdjointableMap A E E` belongs to
`unitary (AdjointableMap A E E)` if and only if it is surjective and preserves the `A`-valued
inner product. -/
theorem mem_unitary_iff {U : AdjointableMap A E E} :
    U ∈ unitary (AdjointableMap A E E) ↔
      Function.Surjective U ∧ ∀ x y : E, inner A (U x) (U y) = inner A x y := by
  rw [Unitary.mem_iff, star_def, mul_def, mul_def, one_def,
    adjoint_comp_self_and_self_comp_adjoint_eq_id_iff]

end AdjointableMap

end TauCeti
