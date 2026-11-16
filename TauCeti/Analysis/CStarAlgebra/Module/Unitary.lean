/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import TauCeti.Analysis.CStarAlgebra.Module.Action
public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair

/-!
# Unitary maps between Hilbert C⋆-modules

A unitary map between Hilbert C⋆-modules is a surjective function preserving the C⋆-algebra-valued
inner product. Over any (possibly non-unital) C⋆-algebra `A`, preserving `⟪·, ·⟫_A` forces
injectivity and norm preservation, so a surjective inner-product-preserving `U : E → F` is bijective
with inverse `V` satisfying `⟪U x, y⟫_A = ⟪x, V y⟫_A`; by `LinearMap.IsAdjointPair`, both `U` and
`V` are automatically complex-linear, compatible with the `A`-action, and (between complete modules)
continuous.

Over any C⋆-algebra `A` (possibly non-unital), **Lance's theorem** (Lance, Theorem 3.5) shows that a
surjective complex-linear isometry commuting with the `A`-action preserves `⟪·, ·⟫_A` and has its
inverse as its adjoint, via Paschke's inequality (`LinearMap.inner_map_map_self_le_of_norm_le`)
and polarization. Over unital `A`, `E ≃ₗᵢ[A] F` (and `E ≃ₗᵢ[Aᵐᵒᵖ] F`) is therefore the exact type
of unitary isomorphisms between Hilbert C⋆-modules.

## Main declarations

* `CStarModule.injective_of_inner_map_map`: any plain function preserving `⟪·, ·⟫_A` is injective.
* `Equiv.isAdjointPair_symm_cstarModule_iff`,
  `CStarModule.surjective_and_inner_map_map_iff_exists_inverse_isAdjointPair`: adjoint-inverse
  characterizations of inner-product-preserving bijections.
* `LinearEquiv.norm_map_iff_inner_map_map_of_map_smul_cstarModule`,
  `LinearIsometryEquiv.inner_map_map_of_map_smul_cstarModule`: Lance's theorem over possibly
  non-unital C⋆-algebras.
* `LinearIsometryEquiv.inner_map_map_cstarModule`,
  `LinearIsometryEquiv.isAdjointPair_symm_cstarModule`,
  `LinearEquiv.norm_map_iff_inner_map_map_cstarModule`: unital `E ≃ₗᵢ[A] F` and `E ≃ₗ[A] F` forms.
* `LinearMap.isometryOfInnerCStarModule`, `LinearEquiv.isometryOfInnerCStarModule`,
  `CStarModule.linearIsometryEquivOfSurjectiveInner`: construct linear isometries and unitaries from
  inner-product preservation.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Theorem 3.5.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Proposition 2.20.
-/

public section

open MulOpposite CStarModule

namespace Equiv

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]

/-- A bijection between C⋆-modules forms an adjoint pair with its inverse iff it preserves
`⟪·, ·⟫_A`. -/
theorem isAdjointPair_symm_cstarModule_iff (e : E ≃ F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip e e.symm ↔
      ∀ x y : E, inner A (e x) (e y) = inner A x y := by
  rw [isAdjointPair_inner_iff]
  exact ⟨fun h x y ↦ by simpa using h x (e y),
    fun h x y ↦ by conv_lhs => rw [← e.apply_symm_apply y, h x (e.symm y)]⟩

end Equiv

namespace CStarModule

section Algebraic

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]

/-- Any plain function between C⋆-modules that preserves inner products is injective. -/
theorem injective_of_inner_map_map {U : E → F}
    (hU : ∀ x y : E, inner A (U x) (U y) = inner A x y) : Function.Injective U := fun x y hxy ↦ by
  apply sub_eq_zero.mp <| (inner_self (A := A)).mp ?_
  have hsub : inner A (U x - U y) (U x - U y) = inner A (x - y) (x - y) := by
    simp only [inner_sub_left, inner_sub_right, hU]
  simpa [hxy] using hsub.symm

/-- A plain function between C⋆-modules is surjective and preserves `⟪·, ·⟫_A` iff it has a
two-sided inverse that is its module adjoint. -/
theorem surjective_and_inner_map_map_iff_exists_inverse_isAdjointPair {U : E → F} :
    Function.Surjective U ∧ (∀ x y : E, inner A (U x) (U y) = inner A x y) ↔
      ∃ V : F → E, Function.LeftInverse V U ∧ Function.RightInverse V U ∧
        LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
          (innerₛₗ (A := A) (E := F)).flip U V := by
  refine ⟨fun ⟨hsurj, hinner⟩ ↦ ?_, fun ⟨V, hL, hR, hadj⟩ ↦
    ⟨hR.surjective, ((Equiv.mk U V hL hR).isAdjointPair_symm_cstarModule_iff (A := A)).mp hadj⟩⟩
  let e : E ≃ F := Equiv.ofBijective U ⟨injective_of_inner_map_map hinner, hsurj⟩
  have he : ∀ x, e x = U x := fun _ ↦ rfl
  exact ⟨e.symm, e.left_inv, e.right_inv,
    (e.isAdjointPair_symm_cstarModule_iff (A := A)).mpr fun x y ↦ by simpa [he] using hinner x y⟩

end Algebraic

end CStarModule

namespace LinearMap

variable {R A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [Semiring R] [SeminormedAddCommGroup E] [Module ℂ E] [SMul A E] [Module R E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [SMul A F] [Module R F] [CStarModule A F]
  (f : E →ₗ[R] F) (hf : ∀ x : E, inner A (f x) (f x) = inner A x x)

/-- An `R`-linear map between Hilbert C⋆-modules preserving self-inner products is an `R`-linear
isometry. -/
def isometryOfInnerCStarModule : E →ₗᵢ[R] F where
  toLinearMap := f
  norm_map' x := norm_map_of_inner_map_map_self (hf x)

@[simp] theorem coe_isometryOfInnerCStarModule : ⇑(f.isometryOfInnerCStarModule hf) = f := (rfl)

@[simp] theorem isometryOfInnerCStarModule_toLinearMap :
    (f.isometryOfInnerCStarModule hf).toLinearMap = f := (rfl)

end LinearMap

namespace LinearEquiv

section General

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

end General

section NonUnital

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]

/-- **Lance's theorem** (Lance, Theorem 3.5) over a (possibly non-unital) C⋆-algebra `A`: a
complex-linear equivalence commuting with the `A`-action is norm-preserving iff it preserves
`⟪·, ·⟫_A`. -/
theorem norm_map_iff_inner_map_map_of_map_smul_cstarModule (f : E ≃ₗ[ℂ] F)
    (hf : ∀ (a : A) (x : E), f (a • x) = a • f x) :
    (∀ x : E, ‖f x‖ = ‖x‖) ↔ ∀ x y : E, inner A (f x) (f y) = inner A x y := by
  refine ⟨fun hnorm ↦ ?_, fun h x ↦ norm_map_of_inner_map_map_self (h x x)⟩
  have hfsymm (a : A) (y : F) : f.symm (a • y) = a • f.symm y :=
    f.injective (by rw [f.apply_symm_apply, hf, f.apply_symm_apply])
  have hdiag (x : E) : inner A (f x) (f x) = inner A x x := le_antisymm
    (by
      simpa using f.toLinearMap.inner_map_map_self_le_of_norm_le hf (C := 1)
        (fun y ↦ by rw [LinearEquiv.coe_coe, hnorm y, one_mul]) x)
    (by
      simpa using f.symm.toLinearMap.inner_map_map_self_le_of_norm_le hfsymm (C := 1)
        (fun y ↦ by rw [LinearEquiv.coe_coe, ← hnorm (f.symm y), f.apply_symm_apply, one_mul])
        (f x))
  intro x y
  rw [inner_polarization (f x) (f y), inner_polarization x y]
  simp only [← map_smul, ← map_add, ← map_sub, hdiag]

/-- Over a (possibly non-unital) C⋆-algebra `A`, a complex-linear equivalence commuting with the
`A`-action is norm-preserving iff its inverse is its module adjoint. -/
theorem norm_map_iff_isAdjointPair_symm_of_map_smul_cstarModule (f : E ≃ₗ[ℂ] F)
    (hf : ∀ (a : A) (x : E), f (a • x) = a • f x) :
    (∀ x : E, ‖f x‖ = ‖x‖) ↔
      LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
        (innerₛₗ (A := A) (E := F)).flip f f.symm :=
  (f.norm_map_iff_inner_map_map_of_map_smul_cstarModule hf).trans
    (f.toEquiv.isAdjointPair_symm_cstarModule_iff (A := A)).symm

end NonUnital

section Unital

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [AddCommGroup E] [Module ℂ E] [Module A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [Module A F] [Norm F] [CStarModule A F]

/-- Over a unital C⋆-algebra, `f : E ≃ₗ[A] F` is norm-preserving iff it preserves `⟪·, ·⟫_A`. -/
theorem norm_map_iff_inner_map_map_cstarModule (f : E ≃ₗ[A] F) :
    (∀ x : E, ‖f x‖ = ‖x‖) ↔ ∀ x y : E, inner A (f x) (f y) = inner A x y := by
  have : IsScalarTower ℂ A E := CStarModule.isScalarTower A E
  have : IsScalarTower ℂ A F := CStarModule.isScalarTower A F
  exact (f.restrictScalars ℂ).norm_map_iff_inner_map_map_of_map_smul_cstarModule f.map_smul

/-- Over a unital C⋆-algebra, `f : E ≃ₗ[A] F` is norm-preserving iff its inverse is its adjoint. -/
theorem norm_map_iff_isAdjointPair_symm_cstarModule (f : E ≃ₗ[A] F) :
    (∀ x : E, ‖f x‖ = ‖x‖) ↔
      LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
        (innerₛₗ (A := A) (E := F)).flip f f.symm :=
  f.norm_map_iff_inner_map_map_cstarModule.trans
    (f.toEquiv.isAdjointPair_symm_cstarModule_iff (A := A)).symm

end Unital

end LinearEquiv

namespace LinearIsometryEquiv

section NonUnital

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [SMul A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [SMul A F] [CStarModule A F]

/-- **Lance's theorem** over a (possibly non-unital) C⋆-algebra `A`: every `f : E ≃ₗᵢ[ℂ] F`
commuting with the `A`-action preserves `⟪·, ·⟫_A`. -/
theorem inner_map_map_of_map_smul_cstarModule (f : E ≃ₗᵢ[ℂ] F)
    (hf : ∀ (a : A) (x : E), f (a • x) = a • f x) (x y : E) :
    inner A (f x) (f y) = inner A x y :=
  (f.toLinearEquiv.norm_map_iff_inner_map_map_of_map_smul_cstarModule hf).mp f.norm_map x y

/-- Over a (possibly non-unital) C⋆-algebra `A`, every `f : E ≃ₗᵢ[ℂ] F` commuting with the
`A`-action forms a module adjoint pair with `f.symm`. -/
theorem isAdjointPair_symm_of_map_smul_cstarModule (f : E ≃ₗᵢ[ℂ] F)
    (hf : ∀ (a : A) (x : E), f (a • x) = a • f x) :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip f f.symm :=
  (f.toEquiv.isAdjointPair_symm_cstarModule_iff (A := A)).mpr
    (f.inner_map_map_of_map_smul_cstarModule hf)

end NonUnital

section Left

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [Module A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module A F] [CStarModule A F]

/-- **Lance's theorem** (Lance, Theorem 3.5): every surjective `A`-linear isometry `f : E ≃ₗᵢ[A] F`
over a unital C⋆-algebra preserves `⟪·, ·⟫_A`. -/
@[simp] theorem inner_map_map_cstarModule (f : E ≃ₗᵢ[A] F) (x y : E) :
    inner A (f x) (f y) = inner A x y :=
  f.toLinearEquiv.norm_map_iff_inner_map_map_cstarModule.mp f.norm_map x y

theorem inner_map_map_self_cstarModule (f : E ≃ₗᵢ[A] F) (x : E) :
    inner A (f x) (f x) = inner A x x := f.inner_map_map_cstarModule x x

theorem inner_map_eq_flip_cstarModule (f : E ≃ₗᵢ[A] F) (x : E) (y : F) :
    inner A (f x) y = inner A x (f.symm y) := by
  conv_lhs => rw [← f.apply_symm_apply y, f.inner_map_map_cstarModule]

theorem isAdjointPair_symm_cstarModule (f : E ≃ₗᵢ[A] F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip f f.symm :=
  (f.toEquiv.isAdjointPair_symm_cstarModule_iff (A := A)).mpr f.inner_map_map_cstarModule

end Left

section Right

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]

theorem unop_inner_map_map_cstarModule (f : E ≃ₗᵢ[Aᵐᵒᵖ] F) (x y : E) :
    unop (inner Aᵐᵒᵖ (f x) (f y)) = unop (inner Aᵐᵒᵖ x y) :=
  congrArg unop (f.inner_map_map_cstarModule x y)

theorem unop_inner_map_eq_flip_cstarModule (f : E ≃ₗᵢ[Aᵐᵒᵖ] F) (x : E) (y : F) :
    unop (inner Aᵐᵒᵖ (f x) y) = unop (inner Aᵐᵒᵖ x (f.symm y)) :=
  congrArg unop (f.inner_map_eq_flip_cstarModule x y)

end Right

end LinearIsometryEquiv

namespace CStarModule

variable {A E F : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A]
  [Norm A] [SeminormedAddCommGroup E] [Module ℂ E] [Module A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module A F] [CStarModule A F]
  (U : E → F) (hsurj : Function.Surjective U)
  (hinner : ∀ x y : E, inner A (U x) (U y) = inner A x y)

/-- Upgrade any plain surjective function `U : E → F` preserving `⟪·, ·⟫_A` to a bundled unitary
`E ≃ₗᵢ[A] F`. -/
noncomputable def linearIsometryEquivOfSurjectiveInner : E ≃ₗᵢ[A] F :=
  let e : E ≃ F := Equiv.ofBijective U ⟨injective_of_inner_map_map hinner, hsurj⟩
  have hadj : LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip e e.symm :=
    (e.isAdjointPair_symm_cstarModule_iff (A := A)).mpr hinner
  ({ toEquiv := e, map_add' := hadj.map_add_cstarModule,
     map_smul' := hadj.map_smul_coeff_cstarModule } : E ≃ₗ[A] F).isometryOfInnerCStarModule
    fun x ↦ hinner x x

@[simp] theorem coe_linearIsometryEquivOfSurjectiveInner :
    ⇑(linearIsometryEquivOfSurjectiveInner U hsurj hinner) = U := (rfl)

theorem linearIsometryEquivOfSurjectiveInner_apply (x : E) :
    linearIsometryEquivOfSurjectiveInner U hsurj hinner x = U x := (rfl)

@[simp] theorem linearIsometryEquivOfSurjectiveInner_symm_apply_apply (x : E) :
    (linearIsometryEquivOfSurjectiveInner U hsurj hinner).symm (U x) = x :=
  (linearIsometryEquivOfSurjectiveInner U hsurj hinner).symm_apply_apply x

theorem linearIsometryEquivOfSurjectiveInner_apply_symm_apply (y : F) :
    U ((linearIsometryEquivOfSurjectiveInner U hsurj hinner).symm y) = y :=
  (linearIsometryEquivOfSurjectiveInner U hsurj hinner).apply_symm_apply y

end CStarModule
