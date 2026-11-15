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
inner product. Over a general C⋆-algebra `A` (possibly non-unital, and including right Hilbert
modules via `Aᵐᵒᵖ`), preserving the inner product already forces injectivity and norm preservation,
so a surjective inner-product-preserving function `U : E → F` is bijective and its inverse `V`
satisfies `⟪U x, y⟫_A = ⟪x, V y⟫_A`. By `LinearMap.IsAdjointPair.map_add_cstarModule`,
`LinearMap.IsAdjointPair.map_smul_coeff_cstarModule`, and
`LinearMap.IsAdjointPair.continuous_cstarModule`, both `U` and `V` are then automatically
complex-linear, compatible with the coefficient action, and (between complete modules) continuous.
Conversely, any bijection whose inverse is its adjoint preserves the inner product.

Unlike in Hilbert spaces, a non-surjective `A`-linear isometry between Hilbert `A`-modules need not
preserve the `A`-valued inner product. However, over a unital C⋆-algebra `A`, **Lance's theorem**
(Lance, Theorem 3.5) states that every surjective `A`-linear isometry `f : E ≃ₗᵢ[A] F`
automatically preserves `⟪·, ·⟫_A` and has `f.symm` as its adjoint: Paschke's inequality
(`CStarModule.inner_map_self_le_of_norm_le`) applied to both `f` and `f.symm` gives
`⟪f x, f x⟫_A = ⟪x, x⟫_A`, and polarization recovers the off-diagonal values. Consequently,
Mathlib's bundled type `E ≃ₗᵢ[A] F` (and `E ≃ₗᵢ[Aᵐᵒᵖ] F` for right Hilbert `A`-modules) is the
exact type of unitary isomorphisms between Hilbert C⋆-modules over unital C⋆-algebras.

## Main declarations

* `CStarModule.injective_of_inner_map`: any function preserving self-inner products of differences
  (in particular, preserving `⟪·, ·⟫_A`) is injective.
* `Equiv.isAdjointPair_symm_cstarModule_iff`: for a bijection `e : E ≃ F`, `(e, e.symm)` is an
  adjoint pair if and only if `e` preserves `⟪·, ·⟫_A`.
* `CStarModule.surjective_and_inner_eq_iff_exists_inverse_isAdjointPair`: a function is surjective
  and inner-product-preserving if and only if it admits a two-sided inverse which is its adjoint.
* `LinearIsometryEquiv.inner_map_map_cstarModule`,
  `LinearIsometryEquiv.isAdjointPair_symm_cstarModule`: Lance's theorem that every `f : E ≃ₗᵢ[A] F`
  over a unital C⋆-algebra preserves `⟪·, ·⟫_A` and forms an adjoint pair with `f.symm`.
* `LinearMap.isometryOfInnerCStarModule`, `LinearEquiv.isometryOfInnerCStarModule`: construct
  `E →ₗᵢ[A] F` and `E ≃ₗᵢ[A] F` from preservation of `⟪x, x⟫_A`.
* `LinearEquiv.norm_map_iff_inner_map_map_cstarModule`: an `A`-linear equivalence is isometric if
  and only if it preserves `⟪·, ·⟫_A`.
* `CStarModule.linearIsometryEquivOfSurjectiveInner`: upgrade a plain surjective
  inner-product-preserving function to `E ≃ₗᵢ[A] F`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Theorem 3.5.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Proposition 2.20.
-/

public section

open MulOpposite CStarModule

namespace Equiv

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]

/-- A bijection between C⋆-modules forms an adjoint pair with its inverse if and only if it
preserves the coefficient-valued inner product. -/
theorem isAdjointPair_symm_cstarModule_iff (e : E ≃ F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip e e.symm ↔
      ∀ x y : E, inner A (e x) (e y) = inner A x y := by
  rw [isAdjointPair_inner_iff]
  refine ⟨fun h x y ↦ ?_, fun h x y ↦ ?_⟩
  · simpa using h x (e y)
  · conv_lhs => rw [← e.apply_symm_apply y, h x (e.symm y)]

end Equiv

namespace CStarModule

section Algebraic

variable {A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]
  [AddCommGroup F] [Module ℂ F] [SMul A F] [Norm F] [CStarModule A F]

/-- Any plain function between C⋆-modules that preserves inner products is injective; no linearity
assumption is needed. -/
theorem injective_of_inner_map {U : E → F}
    (hU : ∀ x y : E, inner A (U x) (U y) = inner A x y) : Function.Injective U := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply (inner_self (A := A)).mp
  have hsub : inner A (U x - U y) (U x - U y) = inner A (x - y) (x - y) := by
    simp only [inner_sub_left, inner_sub_right, hU]
  simpa [hxy] using hsub.symm

/-- A plain function between C⋆-modules is surjective and preserves the inner product if and only
if it has a two-sided inverse that is its module adjoint. By `LinearMap.IsAdjointPair`, any such
map is automatically complex-linear and commutes with the coefficient action. -/
theorem surjective_and_inner_eq_iff_exists_inverse_isAdjointPair {U : E → F} :
    Function.Surjective U ∧ (∀ x y : E, inner A (U x) (U y) = inner A x y) ↔
      ∃ V : F → E, Function.LeftInverse V U ∧ Function.RightInverse V U ∧
        LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
          (innerₛₗ (A := A) (E := F)).flip U V := by
  constructor
  · rintro ⟨hsurj, hinner⟩
    let e : E ≃ F := Equiv.ofBijective U ⟨injective_of_inner_map hinner, hsurj⟩
    have he : ∀ x, e x = U x := fun _ ↦ rfl
    refine ⟨e.symm, e.left_inv, e.right_inv, ?_⟩
    exact (e.isAdjointPair_symm_cstarModule_iff (A := A)).mpr fun x y ↦ by
      simpa [he] using hinner x y
  · rintro ⟨V, hL, hR, hadj⟩
    let e : E ≃ F := ⟨U, V, hL, hR⟩
    exact ⟨hR.surjective, (e.isAdjointPair_symm_cstarModule_iff (A := A)).mp hadj⟩

omit [StarModule ℂ A] in
/-- Preserving the self-inner product at `x` preserves the Hilbert C⋆-module norm at `x`. -/
theorem norm_map_of_inner_self {U : E → F} {x : E}
    (hx : inner A (U x) (U x) = inner A x x) : ‖U x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_norm_inner_self (A := A) (x := U x),
    norm_eq_sqrt_norm_inner_self (A := A) (x := x), hx]

end Algebraic

end CStarModule

namespace LinearMap

variable {R A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [PartialOrder A] [Norm A] [Semiring R]
  [SeminormedAddCommGroup E] [Module ℂ E] [SMul A E] [Module R E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [SMul A F] [Module R F] [CStarModule A F]

/-- An `R`-linear map between Hilbert C⋆-modules that preserves self-inner products is an
`R`-linear isometry. Take `R = A` (over unital `A`) or `R = Aᵐᵒᵖ` for module-linear isometries. -/
def isometryOfInnerCStarModule (f : E →ₗ[R] F)
    (hf : ∀ x : E, inner A (f x) (f x) = inner A x x) : E →ₗᵢ[R] F where
  toLinearMap := f
  norm_map' x := norm_map_of_inner_self (hf x)

@[simp]
theorem coe_isometryOfInnerCStarModule (f : E →ₗ[R] F)
    (hf : ∀ x : E, inner A (f x) (f x) = inner A x x) :
    ⇑(f.isometryOfInnerCStarModule hf) = f := (rfl)

@[simp]
theorem isometryOfInnerCStarModule_toLinearMap (f : E →ₗ[R] F)
    (hf : ∀ x : E, inner A (f x) (f x) = inner A x x) :
    (f.isometryOfInnerCStarModule hf).toLinearMap = f := (rfl)

end LinearMap

namespace LinearIsometryEquiv

section Left

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [Module A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module A F] [CStarModule A F]

/-- **Lance's theorem** on the diagonal: a surjective `A`-linear isometry between Hilbert C⋆-modules
over a unital C⋆-algebra preserves self-inner products. -/
theorem inner_self_map_cstarModule (f : E ≃ₗᵢ[A] F) (x : E) :
    inner A (f x) (f x) = inner A x x := by
  have : IsScalarTower ℂ A E := CStarModule.isScalarTower A E
  have : IsScalarTower ℂ A F := CStarModule.isScalarTower A F
  have hle₁ : inner A (f x) (f x) ≤ inner A x x := by
    simpa using inner_map_self_le_of_norm_le (f.toLinearMap.restrictScalars ℂ)
      (fun a y ↦ f.map_smul a y) (C := 1) (fun y ↦ by simp) x
  have hle₂ : inner A x x ≤ inner A (f x) (f x) := by
    simpa using inner_map_self_le_of_norm_le (f.symm.toLinearMap.restrictScalars ℂ)
      (fun a y ↦ f.symm.map_smul a y) (C := 1) (fun y ↦ by simp) (f x)
  exact le_antisymm hle₁ hle₂

/-- **Lance's theorem** (Lance, Theorem 3.5): every surjective `A`-linear isometry `f : E ≃ₗᵢ[A] F`
between Hilbert C⋆-modules over a unital C⋆-algebra preserves the `A`-valued inner product. -/
theorem inner_map_map_cstarModule (f : E ≃ₗᵢ[A] F) (x y : E) :
    inner A (f x) (f y) = inner A x y := by
  have : IsScalarTower ℂ A E := CStarModule.isScalarTower A E
  have : IsScalarTower ℂ A F := CStarModule.isScalarTower A F
  have hsmul (c : ℂ) (z : E) : f (c • z) = c • f z :=
    (f.toLinearMap.restrictScalars ℂ).map_smul c z
  rw [inner_polarization (f x) (f y), inner_polarization x y]
  simp only [← hsmul, ← map_add, ← map_sub, f.inner_self_map_cstarModule]

/-- The inverse of a surjective `A`-linear isometry is its module adjoint:
`⟪f x, y⟫_A = ⟪x, f.symm y⟫_A`. -/
theorem inner_map_eq_flip_cstarModule (f : E ≃ₗᵢ[A] F) (x : E) (y : F) :
    inner A (f x) y = inner A x (f.symm y) := by
  conv_lhs => rw [← f.apply_symm_apply y, f.inner_map_map_cstarModule]

/-- Every surjective `A`-linear isometry `f : E ≃ₗᵢ[A] F` over a unital C⋆-algebra forms a module
adjoint pair with `f.symm`. -/
theorem isAdjointPair_symm_cstarModule (f : E ≃ₗᵢ[A] F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip f f.symm :=
  (f.toEquiv.isAdjointPair_symm_cstarModule_iff (A := A)).mpr f.inner_map_map_cstarModule

end Left

section Right

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]

/-- Right-module form of Lance's theorem: every `f : E ≃ₗᵢ[Aᵐᵒᵖ] F` preserves the `A`-valued inner
product `⟨x, y⟩_A = unop (inner Aᵐᵒᵖ x y)`. -/
theorem unop_inner_map_map_cstarModule (f : E ≃ₗᵢ[Aᵐᵒᵖ] F) (x y : E) :
    unop (inner Aᵐᵒᵖ (f x) (f y)) = unop (inner Aᵐᵒᵖ x y) :=
  congrArg unop (f.inner_map_map_cstarModule x y)

/-- Right-module adjoint identity for `f : E ≃ₗᵢ[Aᵐᵒᵖ] F`:
`⟨f x, y⟩_A = ⟨x, f.symm y⟩_A`. -/
theorem unop_inner_map_eq_flip_cstarModule (f : E ≃ₗᵢ[Aᵐᵒᵖ] F) (x : E) (y : F) :
    unop (inner Aᵐᵒᵖ (f x) y) = unop (inner Aᵐᵒᵖ x (f.symm y)) :=
  congrArg unop (f.inner_map_eq_flip_cstarModule x y)

end Right

end LinearIsometryEquiv

namespace LinearEquiv

section General

variable {R A E F : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [PartialOrder A] [Norm A] [Semiring R]
  [SeminormedAddCommGroup E] [Module ℂ E] [SMul A E] [Module R E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [SMul A F] [Module R F] [CStarModule A F]

/-- An `R`-linear equivalence between Hilbert C⋆-modules that preserves self-inner products is a
linear isometric equivalence. -/
def isometryOfInnerCStarModule (f : E ≃ₗ[R] F)
    (hf : ∀ x : E, inner A (f x) (f x) = inner A x x) : E ≃ₗᵢ[R] F where
  toLinearEquiv := f
  norm_map' := (f.toLinearMap.isometryOfInnerCStarModule hf).norm_map

@[simp]
theorem coe_isometryOfInnerCStarModule (f : E ≃ₗ[R] F)
    (hf : ∀ x : E, inner A (f x) (f x) = inner A x x) :
    ⇑(f.isometryOfInnerCStarModule hf) = f := (rfl)

@[simp]
theorem isometryOfInnerCStarModule_toLinearEquiv (f : E ≃ₗ[R] F)
    (hf : ∀ x : E, inner A (f x) (f x) = inner A x x) :
    (f.isometryOfInnerCStarModule hf).toLinearEquiv = f := (rfl)

@[simp]
theorem coe_symm_isometryOfInnerCStarModule (f : E ≃ₗ[R] F)
    (hf : ∀ x : E, inner A (f x) (f x) = inner A x x) :
    ⇑(f.isometryOfInnerCStarModule hf).symm = f.symm := (rfl)

end General

section Unital

variable {A E F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [Module A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module A F] [CStarModule A F]

/-- Over a unital C⋆-algebra, an `A`-linear equivalence between Hilbert C⋆-modules is
norm-preserving if and only if it preserves the `A`-valued inner product. -/
theorem norm_map_iff_inner_map_map_cstarModule (f : E ≃ₗ[A] F) :
    (∀ x : E, ‖f x‖ = ‖x‖) ↔ ∀ x y : E, inner A (f x) (f y) = inner A x y :=
  ⟨fun h ↦ (LinearIsometryEquiv.mk f h).inner_map_map_cstarModule,
    fun h ↦ (f.isometryOfInnerCStarModule fun x ↦ h x x).norm_map⟩

/-- Over a unital C⋆-algebra, an `A`-linear equivalence between Hilbert C⋆-modules is
norm-preserving if and only if its inverse is its module adjoint. -/
theorem norm_map_iff_isAdjointPair_symm_cstarModule (f : E ≃ₗ[A] F) :
    (∀ x : E, ‖f x‖ = ‖x‖) ↔
      LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
        (innerₛₗ (A := A) (E := F)).flip f f.symm :=
  (f.norm_map_iff_inner_map_map_cstarModule).trans
    (f.toEquiv.isAdjointPair_symm_cstarModule_iff (A := A)).symm

end Unital

end LinearEquiv

namespace CStarModule

variable {A E F : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A]
  [Norm A]
  [SeminormedAddCommGroup E] [Module ℂ E] [Module A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module A F] [CStarModule A F]

/-- Upgrade any plain surjective function `U : E → F` preserving the `A`-valued inner product to a
bundled unitary `E ≃ₗᵢ[A] F`; additivity and `A`-linearity are deduced automatically from the
adjoint identity. -/
noncomputable def linearIsometryEquivOfSurjectiveInner (U : E → F)
    (hsurj : Function.Surjective U) (hinner : ∀ x y : E, inner A (U x) (U y) = inner A x y) :
    E ≃ₗᵢ[A] F :=
  let e : E ≃ F := Equiv.ofBijective U ⟨injective_of_inner_map hinner, hsurj⟩
  have hadj :
      LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
        (innerₛₗ (A := A) (E := F)).flip e e.symm :=
    (e.isAdjointPair_symm_cstarModule_iff (A := A)).mpr hinner
  let f : E ≃ₗ[A] F :=
    { toEquiv := e
      map_add' := hadj.map_add_cstarModule
      map_smul' := hadj.map_smul_coeff_cstarModule }
  f.isometryOfInnerCStarModule fun x ↦ hinner x x

@[simp]
theorem linearIsometryEquivOfSurjectiveInner_apply (U : E → F)
    (hsurj : Function.Surjective U) (hinner : ∀ x y : E, inner A (U x) (U y) = inner A x y)
    (x : E) : linearIsometryEquivOfSurjectiveInner U hsurj hinner x = U x := (rfl)

end CStarModule
