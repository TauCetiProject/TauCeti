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
(Lance, Theorem 3.5; Raeburn–Williams, Lemma 2.18). Every Hilbert-module unitary `U : E ≅ F` also
induces a unital `⋆`-algebra isomorphism `AdjointableMap A E E ≃⋆ₐ[ℂ] AdjointableMap A F F` by
conjugation `T ↦ U ∘ T ∘ U*`.

## Main declarations

* `TauCeti.CStarModuleUnitary`: bundled Hilbert-module unitary `E ≅ F` extending `E ≃ₗ[ℂ] F` with
  `⟪U x, U y⟫_A = ⟪x, y⟫_A`.
* `TauCeti.CStarModuleUnitary.ofSurjective`: constructs a `CStarModuleUnitary` from a plain
  surjective inner-product-preserving function `E → F`.
* `TauCeti.CStarModuleUnitary.equivAdjointableMap`: equivalence between `CStarModuleUnitary A E F`
  and `{ T : AdjointableMap A E F // T.adjoint.comp T = .id ∧ T.comp T.adjoint = .id }`.
* `TauCeti.AdjointableMap.isUnitary_iff`,
  `TauCeti.AdjointableMap.exists_inverse_eq_adjoint_iff`,
  `TauCeti.AdjointableMap.exists_adjointableMap_unitary_iff`: equivalence between surjective
  inner-product-preserving maps and invertible adjointable maps whose inverse is their adjoint.
* `TauCeti.AdjointableMap.mem_unitary_iff`, `TauCeti.CStarModuleUnitary.mulEquivUnitary`:
  identification of `CStarModuleUnitary A E E` with `unitary (AdjointableMap A E E)`.
* `TauCeti.CStarModuleUnitary.conj`: conjugation `⋆`-algebra equivalence
  `AdjointableMap A E E ≃⋆ₐ[ℂ] AdjointableMap A F F`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Theorem 3.5.
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
    [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
    [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
    [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]
    extends E ≃ₗ[ℂ] F where
  /-- A Hilbert-module unitary preserves the `A`-valued inner product. -/
  inner_map_map' (x y : E) : inner A (toLinearEquiv x) (toLinearEquiv y) = inner A x y

namespace CStarModuleUnitary

section Algebraic

variable {A E F : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]

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

@[ext]
theorem ext {U V : CStarModuleUnitary A E F} (h : ∀ x, U x = V x) : U = V :=
  DFunLike.ext U V h

@[simp]
theorem inner_map_map (U : CStarModuleUnitary A E F) (x y : E) :
    inner A (U x) (U y) = inner A x y :=
  U.inner_map_map' x y

/-- Every Hilbert-module unitary preserves the module norm: `‖U x‖ = ‖x‖`. -/
@[simp]
theorem norm_map (U : CStarModuleUnitary A E F) (x : E) : ‖U x‖ = ‖x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (U x),
    CStarModule.norm_eq_sqrt_norm_inner_self (A := A) x, U.inner_map_map]

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

/-- Every Hilbert-module unitary commutes with the `A`-action. -/
@[simp]
theorem map_smul_coeff (U : CStarModuleUnitary A E F) (a : A) (x : E) :
    U (a • x) = a • U x :=
  (CStarModule.isAdjointable_def.mpr ⟨U.symm, U.inner_map_left⟩).map_smul_coeff a x

/-- Construct a `CStarModuleUnitary` from a plain surjective function `f : E → F` preserving the
`A`-valued inner product (Lance, Theorem 3.5). Injectivity, `ℂ`-linearity, and `A`-linearity follow
automatically from nondegeneracy of the module inner product. -/
noncomputable def ofSurjective {f : E → F} (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    CStarModuleUnitary A E F := by
  have hext : ∀ {u v : F}, (∀ w : E, inner A (f w) u = inner A (f w) v) → u = v := by
    intro u v huv
    obtain ⟨w, hw⟩ := hf_surj (u - v)
    have hadd := CStarModule.inner_add_right (A := A) (x := f w) (y := u - v) (z := v)
    rw [sub_add_cancel, huv w, ← hw] at hadd
    have hfw : f w = 0 :=
      (CStarModule.inner_self (A := A)).mp (add_right_cancel (hadd.symm.trans (zero_add _).symm))
    exact sub_eq_zero.mp (hw.symm.trans hfw)
  have hinj : Function.Injective f := by
    intro x₁ x₂ hx
    apply sub_eq_zero.mp
    apply (CStarModule.inner_self (A := A)).mp
    have hadd := CStarModule.inner_add_right (A := A) (x := x₁ - x₂) (y := x₁ - x₂) (z := x₂)
    rw [sub_add_cancel, ← hf_inner (x₁ - x₂) x₁, hx, hf_inner (x₁ - x₂) x₂] at hadd
    exact add_right_cancel (hadd.symm.trans (zero_add _).symm)
  have hadd : ∀ x₁ x₂ : E, f (x₁ + x₂) = f x₁ + f x₂ := fun x₁ x₂ =>
    hext fun w => by
      rw [hf_inner, CStarModule.inner_add_right, CStarModule.inner_add_right, hf_inner, hf_inner]
  have hsmul : ∀ (c : ℂ) (x : E), f (c • x) = c • f x := fun c x =>
    hext fun w => by
      rw [hf_inner, CStarModule.inner_smul_right_complex, CStarModule.inner_smul_right_complex,
        hf_inner]
  exact
    { toLinearEquiv := LinearEquiv.ofBijective
        { toFun := f, map_add' := hadd, map_smul' := hsmul } ⟨hinj, hf_surj⟩
      inner_map_map' := hf_inner }

@[simp]
theorem ofSurjective_apply {f : E → F} (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) (x : E) :
    ofSurjective hf_surj hf_inner x = f x := (rfl)

@[simp]
theorem coe_ofSurjective {f : E → F} (hf_surj : Function.Surjective f)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) :
    ⇑(ofSurjective hf_surj hf_inner) = f := (rfl)

end Algebraic

section Right

variable {B E F : Type*}
  [NonUnitalSeminormedRing B] [StarRing B] [Module ℂ B] [PartialOrder B]
  [AddCommGroup E] [Module ℂ E] [SMul Bᵐᵒᵖ E] [Norm E] [CStarModule Bᵐᵒᵖ E]
  [AddCommGroup F] [Module ℂ F] [SMul Bᵐᵒᵖ F] [Norm F] [CStarModule Bᵐᵒᵖ F]

theorem unop_inner_map_map (U : CStarModuleUnitary Bᵐᵒᵖ E F) (x y : E) :
    unop (inner Bᵐᵒᵖ (U x) (U y)) = unop (inner Bᵐᵒᵖ x y) :=
  congrArg unop (U.inner_map_map x y)

end Right

section ReflTrans

variable {A E F G H : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]
  [AddCommGroup G] [Module ℂ G] [SMul A G] [Norm G] [CStarModule A G]
  [AddCommGroup H] [Module ℂ H] [SMul A H] [Norm H] [CStarModule A H]

/-- The identity Hilbert-module unitary on `E`. -/
def refl : CStarModuleUnitary A E E where
  toLinearEquiv := LinearEquiv.refl ℂ E
  inner_map_map' _ _ := rfl

@[simp]
theorem refl_toLinearEquiv : (refl : CStarModuleUnitary A E E).toLinearEquiv = .refl ℂ E := (rfl)

@[simp]
theorem refl_apply (x : E) : (refl : CStarModuleUnitary A E E) x = x := (rfl)

/-- Diagrammatic composition of Hilbert-module unitaries (`(U.trans V) x = V (U x)`). -/
def trans (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) :
    CStarModuleUnitary A E G where
  toLinearEquiv := U.toLinearEquiv.trans V.toLinearEquiv
  inner_map_map' x y := (V.inner_map_map (U x) (U y)).trans (U.inner_map_map x y)

@[simp]
theorem trans_toLinearEquiv (U : CStarModuleUnitary A E F) (V : CStarModuleUnitary A F G) :
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

/-! ### Equivalence with unitary adjointable operators -/

section Normed

variable {A E F G : Type*}
  [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

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

/-- View a Hilbert-module unitary `U : CStarModuleUnitary A E F` as an adjointable operator
`AdjointableMap A E F`, with adjoint `U.symm`. -/
def toAdjointableMap (U : CStarModuleUnitary A E F) : AdjointableMap A E F where
  toContinuousLinearMap := U.toLinearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  adjointContinuousLinearMap :=
    U.symm.toLinearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  inner_map_eq' := U.inner_map_left

@[simp]
theorem toAdjointableMap_apply (U : CStarModuleUnitary A E F) (x : E) :
    U.toAdjointableMap x = U x := (rfl)

@[simp]
theorem coe_toAdjointableMap (U : CStarModuleUnitary A E F) :
    ⇑U.toAdjointableMap = ⇑U := (rfl)

@[simp]
theorem adjoint_toAdjointableMap (U : CStarModuleUnitary A E F) :
    U.toAdjointableMap.adjoint = U.symm.toAdjointableMap :=
  AdjointableMap.toContinuousLinearMap_injective <| by
    rw [AdjointableMap.toContinuousLinearMap_adjoint]; rfl

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
  toFun U := ⟨U.toAdjointableMap, Unitary.mem_iff.mpr
    ⟨U.adjoint_comp_toAdjointableMap, U.toAdjointableMap_comp_adjoint⟩⟩
  invFun T := ofAdjointableMap T.1 (Unitary.mem_iff.mp T.2).1 (Unitary.mem_iff.mp T.2).2
  left_inv U := by ext x; simp
  right_inv T := by ext x; simp
  map_mul' U V := by ext x; simp

@[simp]
theorem coe_mulEquivUnitary (U : CStarModuleUnitary A E E) :
    (mulEquivUnitary U : AdjointableMap A E E) = U.toAdjointableMap := (rfl)

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

theorem conj_def (U : CStarModuleUnitary A E F) (T : AdjointableMap A E E) :
    U.conj T = (U.toAdjointableMap.comp T).comp U.symm.toAdjointableMap := (rfl)

@[simp]
theorem conj_apply (U : CStarModuleUnitary A E F) (T : AdjointableMap A E E) (y : F) :
    U.conj T y = U (T (U.symm y)) := by simp [conj_def]

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

/-- An adjointable operator `T : AdjointableMap A E F` is a surjective inner-product-preserving
module map if and only if its adjoint is its two-sided inverse (`T* ∘ T = id` and `T ∘ T* = id`;
Lance, Theorem 3.5). -/
theorem isUnitary_iff {T : AdjointableMap A E F} :
    (Function.Surjective T ∧ ∀ x y : E, inner A (T x) (T y) = inner A x y) ↔
      T.adjoint.comp T = .id ∧ T.comp T.adjoint = .id := by
  refine ⟨fun ⟨hsurj, hinner⟩ => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · let U := CStarModuleUnitary.ofSurjective hsurj hinner
    have hTU : T = U.toAdjointableMap := by ext x; simp [U]
    rw [hTU]
    exact ⟨U.adjoint_comp_toAdjointableMap, U.toAdjointableMap_comp_adjoint⟩
  · exact ⟨fun y => ⟨T.adjoint y, by simpa using congrArg (· y) h₂⟩,
      adjoint_comp_self_eq_id_iff.mp h₁⟩

/-- An adjointable operator `T : AdjointableMap A E F` is a surjective inner-product-preserving
module map if and only if it admits a two-sided inverse in `AdjointableMap` equal to its adjoint. -/
theorem exists_inverse_eq_adjoint_iff {T : AdjointableMap A E F} :
    (Function.Surjective T ∧ ∀ x y : E, inner A (T x) (T y) = inner A x y) ↔
      ∃ S : AdjointableMap A F E, S.comp T = .id ∧ T.comp S = .id ∧ S = T.adjoint := by
  rw [isUnitary_iff]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨T.adjoint, h₁, h₂, rfl⟩,
    by rintro ⟨S, h₁, h₂, rfl⟩; exact ⟨h₁, h₂⟩⟩

/-- A plain function `f : E → F` between normed Hilbert C⋆-modules is surjective and preserves the
`A`-valued inner product if and only if it is the underlying map of an invertible adjointable
operator whose inverse is its adjoint. -/
theorem exists_adjointableMap_unitary_iff {f : E → F} :
    (Function.Surjective f ∧ ∀ x y : E, inner A (f x) (f y) = inner A x y) ↔
      ∃ T : AdjointableMap A E F, ⇑T = f ∧ T.adjoint.comp T = .id ∧ T.comp T.adjoint = .id := by
  refine ⟨fun ⟨hsurj, hinner⟩ => ?_, ?_⟩
  · let U := CStarModuleUnitary.ofSurjective hsurj hinner
    exact ⟨U.toAdjointableMap, by ext x; simp [U], U.adjoint_comp_toAdjointableMap,
      U.toAdjointableMap_comp_adjoint⟩
  · rintro ⟨T, rfl, h₁, h₂⟩
    exact isUnitary_iff.mpr ⟨h₁, h₂⟩

/-- An adjointable endomorphism `U : AdjointableMap A E E` belongs to
`unitary (AdjointableMap A E E)` if and only if it is surjective and preserves the `A`-valued
inner product. -/
theorem mem_unitary_iff {U : AdjointableMap A E E} :
    U ∈ unitary (AdjointableMap A E E) ↔
      Function.Surjective U ∧ ∀ x y : E, inner A (U x) (U y) = inner A x y :=
  Unitary.mem_iff.trans isUnitary_iff.symm

end AdjointableMap

end TauCeti
