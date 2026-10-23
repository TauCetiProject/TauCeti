/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.PosDef
public import TauCeti.RingTheory.TensorProduct.IsBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Bilinear forms and base change

This file extends bilinear forms to abstract base changes through `IsBaseChange.bilinForm`,
using Mathlib's canonical tensor base change and transport along a linear equivalence. It also
records how nondegeneracy behaves under base change.

Nondegeneracy is not preserved by an arbitrary base change: a form can acquire a kernel when its
discriminant becomes a zero divisor. On a finite free module it is exactly the nonvanishing of
that discriminant, so any structure map between integral domains reflects it, and an injective one
also preserves it. The theorems
`LinearMap.BilinForm.nondegenerate_of_nondegenerate_baseChange` and
`LinearMap.BilinForm.nondegenerate_baseChange_iff`, and the computations behind them,
`LinearMap.BilinForm.toMatrix_baseChange` and `LinearMap.BilinForm.det_toMatrix_baseChange`, say
that base change acts entrywise on the Gram matrix of a basis and maps its determinant accordingly.

When the scalar algebra is free over the original semiring, base change preserves left separation
and nondegeneracy without any finiteness or freeness hypothesis on the module carrying the form.
In particular, this applies to arbitrary extensions of fields, even in infinite dimension.
Injective localizations also preserve separation and nondegeneracy without any condition on the
module carrying the form.

Over an ordered field, base change into a linearly ordered commutative ring along an
order-preserving structure map also preserves and reflects positive definiteness of the quadratic
map associated to a bilinear form on a finite-dimensional space; this is how a rational form is
compared with its real extension.

## Main declarations

* `IsBaseChange.bilinForm`: extension to an abstract base change, characterized by its values
  on the original module.
* `IsBaseChange.bilinForm_tmul`: extension commutes with tensor products of bilinear forms.
* `LinearMap.SeparatingLeft.baseChange`: a free scalar extension preserves left separation.
* `LinearMap.BilinForm.Nondegenerate.baseChange`: a free scalar extension preserves
  nondegeneracy, without a finite-dimensionality assumption.
* `LinearMap.BilinForm.Nondegenerate.baseChange_of_isLocalization`: an injective localization
  preserves nondegeneracy, without a freeness or finiteness assumption on the module.
* `LinearMap.BilinForm.liftBaseChange`: lifting a form-preserving map preserves the
  base-changed form, without assuming the map exhibits a base change.
* `IsBaseChange.bilinForm_baseChange`: if a bilinear form restricts along a map to a
  second form, evaluating it through the associated base-change equivalence agrees with the
  canonical base change of the second form.
* `IsBaseChange.bilinFormIsometryEquiv`: in that situation the base-change equivalence is an
  isometric equivalence from the canonical base change of the second form.
* `LinearMap.BilinForm.baseChange_baseChange_baseChange`: base-changed maps preserving a bilinear
  form preserve its base change.
* `LinearMap.BilinForm.toMatrix_baseChange`: the Gram matrix of a base-changed form, in the
  base-changed basis, is the entrywise image of the original Gram matrix.
* `LinearMap.BilinForm.det_toMatrix_baseChange`: the determinant of that Gram matrix is the image of
  the original determinant.
* `LinearMap.BilinForm.nondegenerate_of_nondegenerate_baseChange`: a bilinear form on a finite free
  module over an integral domain is nondegenerate as soon as its base change into a second integral
  domain is, with no hypothesis on the structure map.
* `LinearMap.BilinForm.nondegenerate_baseChange_iff`: along an injective structure map between
  integral domains the implication is an equivalence.
* `LinearMap.BilinForm.IsometryEquiv.baseChange`: an isometric equivalence of bilinear forms
  base-changes to an isometric equivalence of their base changes.
* `TauCeti.bilinFormBaseChangeProdIsometry`: base change commutes with products of
  bilinear forms, via the canonical tensor-product equivalence.
* `LinearMap.BilinForm.posDef_toQuadraticMap_baseChange_iff`: along an order-preserving
  structure map from an ordered field to a linearly ordered commutative ring, base change preserves
  and reflects positive definiteness of the quadratic map of any finite-dimensional bilinear form.
-/

public section

open Module TensorProduct

namespace LinearMap.BilinForm

section Preservation

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M]

/-- Scalar extension commutes with flipping a bilinear form. -/
@[simp]
theorem baseChange_flip (B : LinearMap.BilinForm R M) :
    B.flip.baseChange A = (B.baseChange A).flip := by
  ext x y
  simp

variable (A) in
/-- A free scalar extension preserves left separation of a bilinear form, with no finiteness
assumption on the module carrying the form. -/
theorem _root_.LinearMap.SeparatingLeft.baseChange [Module.Free R A]
    {B : LinearMap.BilinForm R M} (hB : B.SeparatingLeft) :
    (B.baseChange A).SeparatingLeft := by
  classical
  let b := Module.Free.chooseBasis R A
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := M) b
  intro x hx
  apply e.injective
  ext i
  apply hB
  intro w
  -- Evaluating the extended form and then taking a scalar coordinate is the same as evaluating
  -- the original form on the corresponding tensor coordinate.
  have hcoord (z : A ⊗[R] M) : B (e z i) w = b.repr (B.baseChange A z (1 ⊗ₜ[R] w)) i := by
    induction z with
    | tmul a m => simp [e, mul_comm]
    | add z z' hz hz' => simp [hz, hz']
  simpa [hx] using hcoord x

variable (A) in
/-- A free scalar extension preserves right separation of a bilinear form, with no finiteness
assumption on the module carrying the form. -/
theorem _root_.LinearMap.SeparatingRight.baseChange [Module.Free R A]
    {B : LinearMap.BilinForm R M} (hB : B.SeparatingRight) :
    (B.baseChange A).SeparatingRight := by
  have h := LinearMap.SeparatingLeft.baseChange A (B := B.flip) hB
  rw [baseChange_flip] at h
  exact h

variable (A) in
/-- A free scalar extension preserves nondegeneracy of a bilinear form, with no finiteness
assumption on the module carrying the form. In particular, this applies to extensions of fields. -/
theorem Nondegenerate.baseChange [Module.Free R A] {B : LinearMap.BilinForm R M}
    (hB : B.Nondegenerate) : (B.baseChange A).Nondegenerate :=
  ⟨hB.1.baseChange A, hB.2.baseChange A⟩

variable (A) in
/-- An injective localization preserves left separation of a bilinear form, without any freeness
or finiteness assumption on the module carrying the form. -/
theorem _root_.LinearMap.SeparatingLeft.baseChange_of_isLocalization (S : Submonoid R)
    [IsLocalization S A] [FaithfulSMul R A] {B : LinearMap.BilinForm R M}
    (hB : B.SeparatingLeft) : (B.baseChange A).SeparatingLeft := by
  let f : M →ₗ[R] A ⊗[R] M := TensorProduct.mk R A M 1
  have hf : IsLocalizedModule S f := by
    rw [isLocalizedModule_iff_isBaseChange S A]
    exact TensorProduct.isBaseChange R M A
  intro x hx
  obtain ⟨⟨v, s⟩, hs⟩ := hf.surj x
  have hv : v = 0 := hB v fun w ↦ by
    have h : B.baseChange A (s • x) (1 ⊗ₜ[R] w) = 0 := by simp [hx]
    rw [hs] at h
    apply FaithfulSMul.algebraMap_injective R A
    simpa [f, Algebra.algebraMap_eq_smul_one] using h
  rw [hv, map_zero] at hs
  exact (IsLocalizedModule.smul_injective f s) (by simpa using hs)

variable (A) in
/-- An injective localization preserves right separation of a bilinear form, without any freeness
or finiteness assumption on the module carrying the form. -/
theorem _root_.LinearMap.SeparatingRight.baseChange_of_isLocalization (S : Submonoid R)
    [IsLocalization S A] [FaithfulSMul R A] {B : LinearMap.BilinForm R M}
    (hB : B.SeparatingRight) : (B.baseChange A).SeparatingRight := by
  have h := LinearMap.SeparatingLeft.baseChange_of_isLocalization A S (B := B.flip) hB
  rw [baseChange_flip] at h
  exact h

variable (A) in
/-- An injective localization preserves nondegeneracy of a bilinear form, without any freeness
or finiteness assumption on the module carrying the form. -/
theorem Nondegenerate.baseChange_of_isLocalization (S : Submonoid R)
    [IsLocalization S A] [FaithfulSMul R A] {B : LinearMap.BilinForm R M}
    (hB : B.Nondegenerate) : (B.baseChange A).Nondegenerate :=
  ⟨hB.1.baseChange_of_isLocalization A S, hB.2.baseChange_of_isLocalization A S⟩

end Preservation

end LinearMap.BilinForm

namespace IsBaseChange

section BilinForm

variable {R A M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module A N]
  [IsScalarTower R A N] {f : M →ₗ[R] N}

/-- Extend a bilinear form to an abstract base change, transporting Mathlib's tensor-product
base change along the canonical equivalence. -/
noncomputable def bilinForm (h : IsBaseChange A f) (B : LinearMap.BilinForm R M) :
    LinearMap.BilinForm A N :=
  LinearMap.BilinForm.congr h.equiv (B.baseChange A)

theorem bilinForm_def (h : IsBaseChange A f) (B : LinearMap.BilinForm R M) :
    h.bilinForm B = LinearMap.BilinForm.congr h.equiv (B.baseChange A) :=
  (rfl)

/-- The extended form agrees with the original form on the image of the structure map. -/
@[simp]
theorem bilinForm_apply (h : IsBaseChange A f) (B : LinearMap.BilinForm R M) (x y : M) :
    h.bilinForm B (f x) (f y) = algebraMap R A (B x y) := by
  simp [bilinForm_def, h.equiv_symm_apply, Algebra.algebraMap_eq_smul_one]

/-- A bilinear form on a base change is determined by its values on the original module. -/
theorem bilinForm_unique (h : IsBaseChange A f) (B : LinearMap.BilinForm R M)
    (C : LinearMap.BilinForm A N) (hC : ∀ x y, C (f x) (f y) = algebraMap R A (B x y)) :
    C = h.bilinForm B := by
  refine h.algHom_ext _ _ fun x ↦ h.algHom_ext _ _ fun y ↦ ?_
  simp [hC x y]

/-- Scalar extension preserves the zero bilinear form. -/
@[simp]
theorem bilinForm_zero (h : IsBaseChange A f) :
    h.bilinForm (0 : LinearMap.BilinForm R M) = 0 :=
  (h.bilinForm_unique _ _ fun x y ↦ by simp).symm

/-- Scalar extension commutes with addition of bilinear forms. -/
@[simp]
theorem bilinForm_add (h : IsBaseChange A f) (B C : LinearMap.BilinForm R M) :
    h.bilinForm (B + C) = h.bilinForm B + h.bilinForm C :=
  (h.bilinForm_unique _ _ fun x y ↦ by simp).symm

/-- Scalar extension commutes with flipping a bilinear form. -/
@[simp]
theorem bilinForm_flip (h : IsBaseChange A f) (B : LinearMap.BilinForm R M) :
    h.bilinForm B.flip = (h.bilinForm B).flip :=
  (h.bilinForm_unique _ _ fun x y ↦ by simp).symm

/-- Scalar extension commutes with scalar multiples from the original semiring. -/
@[simp]
theorem bilinForm_smul (h : IsBaseChange A f) (r : R) (B : LinearMap.BilinForm R M) :
    h.bilinForm (r • B) = algebraMap R A r • h.bilinForm B :=
  (h.bilinForm_unique _ _ fun x y ↦ by simp [Algebra.smul_def]).symm

/-- A scalar symmetry between a bilinear form and its flip passes to scalar extension. -/
theorem bilinForm_apply_symm (h : IsBaseChange A f) (B : LinearMap.BilinForm R M)
    {r : R} (hB : ∀ x y, B y x = r * B x y) (x y : N) :
    h.bilinForm B y x = algebraMap R A r * h.bilinForm B x y := by
  have hflip : B.flip = r • B := by
    ext u v
    exact hB u v
  have hforms : (h.bilinForm B).flip = algebraMap R A r • h.bilinForm B := by
    rw [← bilinForm_flip, hflip, bilinForm_smul]
  simpa only [LinearMap.BilinForm.flip_apply, LinearMap.smul_apply, smul_eq_mul] using
    congr($(hforms) x y)

/-- Scalar extension commutes with pullback along linear maps, lifted to the base changes.
Supply the target witness `h` when using this as a simp rule, as it is not determined by the
left-hand side. -/
theorem bilinForm_comp {M' N' : Type*} [AddCommMonoid M'] [Module R M']
    [AddCommMonoid N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
    {f' : M' →ₗ[R] N'} (h' : IsBaseChange A f') (h : IsBaseChange A f)
    (B : LinearMap.BilinForm R M) (l r : M' →ₗ[R] M) :
    h'.bilinForm (B.comp l r) =
      (h.bilinForm B).comp (h'.lift (f.comp l)) (h'.lift (f.comp r)) :=
  (h'.bilinForm_unique _ _ fun x y ↦ by simp [IsBaseChange.lift_eq]).symm

/-- Scalar extension of a block-diagonal form is the block-diagonal form of its two extensions. -/
@[simp]
theorem bilinForm_prod {M' N' : Type*} [AddCommMonoid M'] [Module R M']
    [AddCommMonoid N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
    {f' : M' →ₗ[R] N'} (h : IsBaseChange A f) (h' : IsBaseChange A f')
    (B : LinearMap.BilinForm R M) (B' : LinearMap.BilinForm R M') :
    (IsBaseChange.prodMap f f' h h').bilinForm (B.prod B') =
      (h.bilinForm B).prod (h'.bilinForm B') :=
  (bilinForm_unique _ _ _ fun x y ↦ by simp [LinearMap.prodMap_apply]).symm

/-- Scalar extension of a tensor product form is the tensor product of the extended forms. -/
@[simp]
theorem bilinForm_tmul {M' N' : Type*} [AddCommMonoid M'] [Module R M']
    [AddCommMonoid N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
    {f' : M' →ₗ[R] N'} (h : IsBaseChange A f) (h' : IsBaseChange A f')
    (B : LinearMap.BilinForm R M) (B' : LinearMap.BilinForm R M') :
    (h.tensorProduct h').bilinForm (B.tmul B') =
      (h.bilinForm B).tmul (h'.bilinForm B') := by
  refine (bilinForm_unique _ _ _ fun x y ↦ ?_).symm
  induction x with
  | tmul v w =>
    induction y with
    | tmul v' w' =>
      rw [LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
        TensorProduct.map_tmul, TensorProduct.mapOfCompatibleSMul_tmul,
        TensorProduct.mapOfCompatibleSMul_tmul, LinearMap.BilinForm.tensorDistrib_tmul,
        bilinForm_apply, bilinForm_apply, smul_eq_mul, ← map_mul]
      exact congrArg _ (LinearMap.BilinForm.tensorDistrib_tmul R R B B' v w v' w').symm
    | add y y' hy hy' => rw [map_add, map_add, map_add, hy, hy', map_add]
  | add x x' hx hx' =>
    rw [map_add, map_add, LinearMap.add_apply, hx, hx', ← map_add]
    exact congrArg _ (LinearMap.map_add₂ (B.tmul B') x x' y).symm

end BilinForm

end IsBaseChange

namespace TauCeti

section

variable {R : Type*} {A : Type*} {M : Type*} {N : Type*}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A N]
variable {f : M →ₗ[R] N}

/-- If `B` restricts along `f` to `B'`, evaluating `B` on the images of `f.liftBaseChange A`
agrees with the canonical base change of `B'`. The map `f` need not exhibit a base change. -/
theorem _root_.LinearMap.BilinForm.liftBaseChange (B' : LinearMap.BilinForm R M)
    (B : LinearMap.BilinForm A N)
    (hB : ∀ x y : M, B (f x) (f y) = algebraMap R A (B' x y)) (x y : A ⊗[R] M) :
    B (f.liftBaseChange A x) (f.liftBaseChange A y) = B'.baseChange A x y := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
  | tmul a m =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [map_add, hy₁, hy₂]
    | tmul a' m' =>
      simp only [LinearMap.liftBaseChange_tmul, LinearMap.BilinForm.smul_left,
        LinearMap.BilinForm.smul_right, LinearMap.BilinForm.baseChange_tmul,
        hB, Algebra.smul_def]
      ring

/-- If `B` restricts along a base-change map to `B'`, its base-change equivalence preserves
the canonical base change of `B'`. -/
theorem _root_.IsBaseChange.bilinForm_baseChange (h : IsBaseChange A f)
    (B' : LinearMap.BilinForm R M) (B : LinearMap.BilinForm A N)
    (hB : ∀ x y : M, B (f x) (f y) = algebraMap R A (B' x y)) (x y : A ⊗[R] M) :
    B (h.equiv x) (h.equiv y) = B'.baseChange A x y := by
  have hf : f.liftBaseChange A = h.equiv.toLinearMap := by
    ext
    simp [IsBaseChange.equiv_tmul]
  simpa only [hf, LinearEquiv.coe_coe] using B'.liftBaseChange B hB x y

/-- If `B` restricts along a base-change map `f` to `B'`, the base-change equivalence
`A ⊗[R] M ≃ N` is an isometric equivalence from the canonical base change of `B'` to `B`. -/
noncomputable def _root_.IsBaseChange.bilinFormIsometryEquiv (h : IsBaseChange A f)
    (B' : LinearMap.BilinForm R M) (B : LinearMap.BilinForm A N)
    (hB : ∀ x y : M, B (f x) (f y) = algebraMap R A (B' x y)) :
    (B'.baseChange A).IsometryEquiv B where
  toLinearEquiv := h.equiv
  map_app' := h.bilinForm_baseChange B' B hB

/-- The isometric equivalence `IsBaseChange.bilinFormIsometryEquiv` is the base-change
equivalence. -/
@[simp]
theorem _root_.IsBaseChange.bilinFormIsometryEquiv_apply (h : IsBaseChange A f)
    (B' : LinearMap.BilinForm R M) (B : LinearMap.BilinForm A N)
    (hB : ∀ x y : M, B (f x) (f y) = algebraMap R A (B' x y)) (x : A ⊗[R] M) :
    h.bilinFormIsometryEquiv B' B hB x = h.equiv x :=
  (rfl)

/-- **Base-changed maps preserving a bilinear form preserve its base change**: if `g` carries `B`
to `B'`, then `g.baseChange A` carries `B.baseChange A` to `B'.baseChange A`. -/
theorem _root_.LinearMap.BilinForm.baseChange_baseChange_baseChange {M' : Type*}
    [AddCommMonoid M'] [Module R M'] {B : LinearMap.BilinForm R M}
    {B' : LinearMap.BilinForm R M'} {g : M →ₗ[R] M'} (hg : ∀ v w, B' (g v) (g w) = B v w)
    (x y : A ⊗[R] M) :
    B'.baseChange A (g.baseChange A x) (g.baseChange A y) = B.baseChange A x y := by
  have hlift : (TensorProduct.mk R A M' 1 ∘ₗ g).liftBaseChange A = g.baseChange A := by
    ext
    simp
  rw [← hlift]
  exact B.liftBaseChange (B'.baseChange A)
    (fun v w => by simp [hg, Algebra.algebraMap_eq_smul_one]) x y

end

end TauCeti

namespace LinearMap.BilinForm

section Semiring

variable {R A M ι : Type*}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M]

/-- Base change acts entrywise on the Gram matrix of a bilinear form: the matrix of `B.baseChange A`
in the base-changed basis is the image of the matrix of `B` under the structure map. -/
@[simp]
theorem toMatrix_baseChange [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm R M) (b : Basis ι R M) :
    LinearMap.BilinForm.toMatrix (b.baseChange A) (B.baseChange A) =
      (LinearMap.BilinForm.toMatrix b B).map (algebraMap R A) := by
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply, Basis.baseChange_apply,
    Algebra.algebraMap_eq_smul_one]

end Semiring

section Nondegenerate

variable {R A M ι : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M]

/-- The Gram determinant of a base-changed bilinear form is the image of the original Gram
determinant under the structure map. -/
theorem det_toMatrix_baseChange [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm R M) (b : Basis ι R M) :
    (LinearMap.BilinForm.toMatrix (b.baseChange A) (B.baseChange A)).det =
      algebraMap R A (LinearMap.BilinForm.toMatrix b B).det := by
  rw [toMatrix_baseChange, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

variable (A) in
/-- **Nondegeneracy descends along any base change of integral domains.** On a finite free module,
nondegeneracy of a bilinear form is nonvanishing of the determinant of its Gram matrix, and the
structure map sends that determinant to the determinant of the base-changed Gram matrix, so a
nondegenerate base change forces a nondegenerate form. No hypothesis on the structure map is
needed. -/
theorem nondegenerate_of_nondegenerate_baseChange [Finite ι] [IsDomain R] [IsDomain A]
    (B : LinearMap.BilinForm R M) (b : Basis ι R M) (h : (B.baseChange A).Nondegenerate) :
    B.Nondegenerate := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange A),
    det_toMatrix_baseChange] at h
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
  exact fun hdet ↦ h (by rw [hdet, map_zero])

/-- **Nondegeneracy is preserved and reflected by an injective base change of integral domains.**
On a finite free module, nondegeneracy of a bilinear form is nonvanishing of the determinant of its
Gram matrix, and an injective structure map neither creates nor destroys that. -/
theorem nondegenerate_baseChange_iff [Finite ι] [IsDomain A] [FaithfulSMul R A]
    (B : LinearMap.BilinForm R M) (b : Basis ι R M) :
    (B.baseChange A).Nondegenerate ↔ B.Nondegenerate := by
  classical
  have : IsDomain R :=
    Function.Injective.isDomain (algebraMap R A) (FaithfulSMul.algebraMap_injective R A)
  have : Fintype ι := Fintype.ofFinite ι
  refine ⟨nondegenerate_of_nondegenerate_baseChange A B b, fun h ↦ ?_⟩
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange A),
    det_toMatrix_baseChange]
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R A)).mpr
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp h)

end Nondegenerate

end LinearMap.BilinForm

namespace TauCeti

section IsometryEquiv

variable {R A M₁ M₂ : Type*}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
variable {B₁ : LinearMap.BilinForm R M₁} {B₂ : LinearMap.BilinForm R M₂}

variable (A) in
/-- Base change of an isometric equivalence of bilinear forms: the base change of the underlying
linear equivalence is an isometric equivalence of the base-changed forms. -/
def _root_.LinearMap.BilinForm.IsometryEquiv.baseChange (f : B₁.IsometryEquiv B₂) :
    (B₁.baseChange A).IsometryEquiv (B₂.baseChange A) where
  toLinearEquiv := (f : M₁ ≃ₗ[R] M₂).baseChange R A M₁ M₂
  map_app' x y := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | tmul a m =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul b n => simp

/-- On pure tensors, a base-changed isometric equivalence applies the original equivalence to the
vector. -/
@[simp]
theorem _root_.LinearMap.BilinForm.IsometryEquiv.baseChange_tmul (f : B₁.IsometryEquiv B₂)
    (a : A) (m : M₁) : f.baseChange A (a ⊗ₜ m) = a ⊗ₜ f m :=
  LinearEquiv.baseChange_tmul R A M₁ M₂ (e := (f : M₁ ≃ₗ[R] M₂)) a m

variable (A) in
/-- Base change of a product of bilinear forms is isometric to the product of their base changes,
via the canonical distribution of tensor products over products. -/
def bilinFormBaseChangeProdIsometry (B₁ : LinearMap.BilinForm R M₁)
    (B₂ : LinearMap.BilinForm R M₂) :
    ((B₁.prod B₂).baseChange A).IsometryEquiv ((B₁.baseChange A).prod (B₂.baseChange A)) where
  toLinearEquiv := TensorProduct.prodRight R A A M₁ M₂
  map_app' x y := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul b y =>
        simp [LinearMap.BilinForm.prod_apply, Algebra.smul_def, add_mul]

/-- The product base-change isometry distributes a pure tensor over its two coordinates. -/
@[simp]
theorem bilinFormBaseChangeProdIsometry_tmul (B₁ : LinearMap.BilinForm R M₁)
    (B₂ : LinearMap.BilinForm R M₂) (a : A) (x : M₁ × M₂) :
    bilinFormBaseChangeProdIsometry A B₁ B₂ (a ⊗ₜ x) = (a ⊗ₜ x.1, a ⊗ₜ x.2) := by
  rw [← LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv, bilinFormBaseChangeProdIsometry]
  exact TensorProduct.prodRight_tmul R A A M₁ M₂ a x

/-- The inverse product base-change isometry combines pure tensors with a common scalar. -/
@[simp]
theorem bilinFormBaseChangeProdIsometry_symm_tmul (B₁ : LinearMap.BilinForm R M₁)
    (B₂ : LinearMap.BilinForm R M₂) (a : A) (x : M₁) (y : M₂) :
    (bilinFormBaseChangeProdIsometry A B₁ B₂).symm (a ⊗ₜ x, a ⊗ₜ y) = a ⊗ₜ (x, y) := by
  rw [← LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv,
    LinearMap.BilinForm.IsometryEquiv.symm, bilinFormBaseChangeProdIsometry]
  exact TensorProduct.prodRight_symm_tmul R A A M₁ M₂ a x y

end IsometryEquiv

end TauCeti

namespace LinearMap.BilinForm

section PosDef

variable {F K V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] [Algebra F K] [SMulPosStrictMono F K]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- **Positive definiteness is preserved and reflected by an ordered scalar extension.** For a
bilinear form on a finite-dimensional space over an ordered field `F`, and a linearly ordered
commutative ring `K` whose structure map from `F` is strictly monotone, the quadratic map of the
base change of `B` to `K` is positive definite exactly when that of `B` is. No symmetry assumption
is needed. In particular a rational form is positive definite exactly when its real extension is. -/
theorem posDef_toQuadraticMap_baseChange_iff (B : LinearMap.BilinForm F V) :
    (B.baseChange K).toQuadraticMap.PosDef ↔ B.toQuadraticMap.PosDef := by
  wlog hB : B.IsSymm generalizing B
  · -- Symmetrization doubles every diagonal value, before and after base change.
    have hsym : (B + B.flip).IsSymm := by
      constructor
      intro x y
      simp [add_comm]
    have hbase : (B + B.flip).baseChange K = B.baseChange K + (B.baseChange K).flip := by
      ext
      simp [add_smul]
    simpa only [hbase, posDef_toQuadraticMap_add_flip_iff] using this (B + B.flip) hsym
  have hmap {a : F} : 0 < algebraMap F K a ↔ 0 < a := by
    simpa using (algebraMap_strictMono (α := F) K).lt_iff_lt (a := 0) (b := a)
  constructor
  · -- Reflection: evaluate on the nonzero vector `1 ⊗ x`.
    intro h x hx
    have h1 : (1 : K) ⊗ₜ[F] x ≠ 0 :=
      fun h0 ↦ hx ((Module.FaithfullyFlat.one_tmul_eq_zero_iff F V x).mp h0)
    have := h _ h1
    rw [LinearMap.BilinMap.toQuadraticMap_apply, baseChange_tmul, one_mul,
      ← Algebra.algebraMap_eq_smul_one, hmap] at this
    rwa [LinearMap.BilinMap.toQuadraticMap_apply]
  · -- The orthogonal basis `v` base-changes to an orthogonal basis `w` of `B.baseChange K`,
    -- whose diagonal values are the images of the positive diagonal values of `B`.
    intro h z hz
    let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
    obtain ⟨v, hv⟩ := exists_orthogonal_basis (isSymm_iff.mp hB)
    set w := v.baseChange K
    have hw (i j) : B.baseChange K (w i) (w j) = algebraMap F K (B (v i) (v j)) := by
      simp [w, Basis.baseChange_apply, baseChange_tmul, Algebra.algebraMap_eq_smul_one]
    have hpos (i) : 0 < algebraMap F K (B (v i) (v i)) := by
      rw [hmap, ← LinearMap.BilinMap.toQuadraticMap_apply]
      exact h _ (v.ne_zero i)
    -- So in the basis `w`, the form is a sum of squares with positive weights.
    have hz' : B.baseChange K z z =
        ∑ i, w.repr z i * w.repr z i * algebraMap F K (B (v i) (v i)) := by
      conv_lhs => rw [← w.sum_repr z]
      simp only [sum_left, sum_right, smul_left, smul_right, hw]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_eq_single i (fun j _ hji ↦ by rw [hv hji, map_zero, mul_zero]) (by simp)]
      ring
    obtain ⟨i, hi⟩ : ∃ i, w.repr z i ≠ 0 := by
      by_contra! h0
      exact hz (w.repr.injective (by ext i; simp [h0]))
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hz']
    exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (mul_self_nonneg _) (hpos j).le)
      ⟨i, Finset.mem_univ _, mul_pos (mul_self_pos.mpr hi) (hpos i)⟩

end PosDef

end LinearMap.BilinForm
