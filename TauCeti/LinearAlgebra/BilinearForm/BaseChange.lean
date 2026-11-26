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
`IsBaseChange.nondegenerate_bilinForm_iff` transfers the latter to `IsBaseChange.bilinForm`.

When the scalar algebra is free over the original semiring, the left kernel of the base-changed
form is the base change of the left kernel, so base change preserves left separation
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
* `LinearMap.BilinForm.baseChange_rTensor_rTensor`: the canonical base change is natural along
  algebra maps of the scalars.
* `LinearMap.BilinForm.ker_baseChange`: the left kernel of a bilinear form commutes with a free
  scalar extension.
* `LinearMap.SeparatingLeft.baseChange`: a free scalar extension preserves left separation.
* `LinearMap.BilinForm.Nondegenerate.baseChange`: a free scalar extension preserves
  nondegeneracy, without a finite-dimensionality assumption.
* `LinearMap.BilinForm.Nondegenerate.baseChange_of_isLocalization`: an injective localization
  preserves nondegeneracy, without a freeness or finiteness assumption on the module.
* `LinearMap.BilinForm.baseChange_smul`, `LinearMap.BilinForm.baseChange_add`,
  `LinearMap.BilinForm.baseChange_neg`, `LinearMap.BilinForm.baseChange_sub`: scalar extension
  commutes with scalar multiplication, addition, negation and subtraction of forms.
* `LinearMap.BilinForm.baseChange_compl₁₂`: scalar extension commutes with composing a form with
  linear maps on both sides.
* `LinearMap.BilinForm.compl₁₂_baseChange_eq_smul`: a similitude `B.compl₁₂ f f = c • B`
  base-changes to a similitude of `B.baseChange A` with multiplier `algebraMap R A c`.
* `LinearMap.BilinForm.IsAlt.baseChange`: scalar extension preserves alternating forms, using
  `LinearMap.BilinForm.IsAlt.add_flip_eq_zero` (an alternating form is skew-symmetric over a
  semiring).
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
* `IsBaseChange.nondegenerate_bilinForm_iff`: the same equivalence for `IsBaseChange.bilinForm`.
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

/-- **Scalar extension of a bilinear form is natural in the scalars.** Along an `R`-algebra map
`f : A → A'`, the base change of `B` to `A'`, evaluated on the images of `x y : A ⊗[R] M`, is the
image under `f` of its base change to `A`, evaluated on `x` and `y`. -/
@[simp]
theorem baseChange_rTensor_rTensor {A' : Type*} [CommSemiring A'] [Algebra R A'] (f : A →ₐ[R] A')
    (B : LinearMap.BilinForm R M) (x y : A ⊗[R] M) :
    B.baseChange A' (f.toLinearMap.rTensor M x) (f.toLinearMap.rTensor M y) =
      f (B.baseChange A x y) := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
  | tmul a m =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
    | tmul a' m' => simp [map_mul]

variable (A) in
/-- **The kernel of a bilinear form commutes with free scalar extension.** The left kernel of the
base change of `B` to a free `R`-algebra `A` is the base change of the left kernel of `B`, with no
finiteness assumption on the module carrying the form. In particular this holds for every
extension of fields, even in infinite dimension. -/
theorem ker_baseChange [Module.Free R A] (B : LinearMap.BilinForm R M) :
    LinearMap.ker (B.baseChange A) = (LinearMap.ker B).baseChange A := by
  classical
  refine le_antisymm (fun x hx => ?_) (Submodule.baseChange_le_iff_le_comap.2 fun m hm => ?_)
  · let b := Module.Free.chooseBasis R A
    let e := TensorProduct.equivFinsuppOfBasisLeft (N := M) b
    -- Evaluating the extended form and then taking a scalar coordinate is the same as evaluating
    -- the original form on the corresponding tensor coordinate.
    have hcoord (z : A ⊗[R] M) (i) (w : M) :
        B (e z i) w = b.repr (B.baseChange A z (1 ⊗ₜ[R] w)) i := by
      induction z with
      | tmul a m => simp [e, mul_comm]
      | add z z' hz hz' => simp [hz, hz']
    have hmem (i) : e x i ∈ LinearMap.ker B :=
      LinearMap.ext fun w => by simpa [LinearMap.mem_ker.1 hx] using hcoord x i w
    rw [← e.symm_apply_apply x, TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    exact Submodule.finsuppSum_mem _ _ _ _ fun i _ =>
      Submodule.tmul_mem_baseChange_of_mem _ (hmem i)
  · rw [Submodule.mem_comap, Submodule.restrictScalars_mem, LinearMap.mem_ker]
    ext y
    simp [LinearMap.mem_ker.1 hm]

variable (A) in
/-- A free scalar extension preserves left separation of a bilinear form, with no finiteness
assumption on the module carrying the form. -/
theorem _root_.LinearMap.SeparatingLeft.baseChange [Module.Free R A]
    {B : LinearMap.BilinForm R M} (hB : B.SeparatingLeft) :
    (B.baseChange A).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot] at hB ⊢
  rw [ker_baseChange, hB, Submodule.baseChange_bot]

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

section Arithmetic

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M]

/-- Scalar extension commutes with scalar multiplication of bilinear forms. -/
@[simp]
theorem baseChange_smul (r : R) (B : LinearMap.BilinForm R M) :
    (r • B).baseChange A = algebraMap R A r • B.baseChange A := by
  ext a x
  simp [Algebra.smul_def, mul_comm]

/-- Scalar extension commutes with addition of bilinear forms. -/
@[simp]
theorem baseChange_add (B B' : LinearMap.BilinForm R M) :
    (B + B').baseChange A = B.baseChange A + B'.baseChange A := by
  ext a x
  simp [add_smul]

/-- An alternating bilinear form is skew-symmetric, `B + B.flip = 0`, over any commutative
semiring (Mathlib's `LinearMap.IsAlt.neg` needs additive inverses). -/
theorem IsAlt.add_flip_eq_zero {B : LinearMap.BilinForm R M} (hB : B.IsAlt) : B + B.flip = 0 := by
  ext x y
  have := hB (x + y)
  simp only [map_add, LinearMap.add_apply, hB x, hB y, zero_add, add_zero] at this
  simpa [add_comm] using this

/-- Scalar extension of an alternating bilinear form is alternating. -/
theorem IsAlt.baseChange {B : LinearMap.BilinForm R M} (hB : B.IsAlt) :
    (B.baseChange A).IsAlt := by
  have hB' := hB.add_flip_eq_zero
  have hskew : B.baseChange A + (B.baseChange A).flip = 0 := by
    rw [← baseChange_flip, ← baseChange_add, hB', baseChange_zero]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a x => simp [hB x]
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx', zero_add, add_zero]
    simpa using congr($hskew x' x)

/-- Scalar extension commutes with composing a bilinear form with linear maps on both sides. -/
@[simp]
theorem baseChange_compl₁₂ {M' : Type*} [AddCommMonoid M'] [Module R M']
    (B : LinearMap.BilinForm R M) (f g : M' →ₗ[R] M) :
    LinearMap.BilinForm.baseChange A (B.compl₁₂ f g) =
      (B.baseChange A).compl₁₂ (f.baseChange A) (g.baseChange A) := by
  ext a x
  simp

/-- A similitude of `B` with multiplier `c` is a similitude of the scalar extension of `B`, with
multiplier the image of `c`. -/
theorem compl₁₂_baseChange_eq_smul {B : LinearMap.BilinForm R M} {f : M →ₗ[R] M} {c : R}
    (h : B.compl₁₂ f f = c • B) :
    (B.baseChange A).compl₁₂ (f.baseChange A) (f.baseChange A) =
      algebraMap R A c • B.baseChange A := by
  rw [← baseChange_compl₁₂, h, baseChange_smul]

end Arithmetic

section Ring

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid M] [Module R M]

/-- Scalar extension commutes with negation of bilinear forms. -/
@[simp]
theorem baseChange_neg (B : LinearMap.BilinForm R M) : (-B).baseChange A = -B.baseChange A := by
  rw [← neg_one_smul R B, baseChange_smul, map_neg, map_one]
  exact neg_one_smul A (B.baseChange A)

/-- Scalar extension commutes with subtraction of bilinear forms. -/
@[simp]
theorem baseChange_sub (B B' : LinearMap.BilinForm R M) :
    (B - B').baseChange A = B.baseChange A - B'.baseChange A := by
  ext x y
  simp [sub_smul]

end Ring

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

namespace IsBaseChange

section Nondegenerate

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [AddCommMonoid N] [Module R N] [Module A N]
  [IsScalarTower R A N] {f : M →ₗ[R] N}

/-- **Nondegeneracy is preserved and reflected by an injective abstract base change to an integral
domain.** On a finite free module, `IsBaseChange.bilinForm` is a transport of Mathlib's tensor base
change, to which `LinearMap.BilinForm.nondegenerate_baseChange_iff` applies. -/
theorem nondegenerate_bilinForm_iff [Module.Free R M] [Module.Finite R M] [IsDomain A]
    [FaithfulSMul R A] (h : IsBaseChange A f) (B : LinearMap.BilinForm R M) :
    (h.bilinForm B).Nondegenerate ↔ B.Nondegenerate := by
  rw [bilinForm_def, LinearMap.BilinForm.nondegenerate_congr_iff,
    LinearMap.BilinForm.nondegenerate_baseChange_iff B (Module.Free.chooseBasis R M)]

end Nondegenerate

end IsBaseChange

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
  map_app' := LinearMap.BilinForm.baseChange_baseChange_baseChange (g := (f : M₁ →ₗ[R] M₂))
    fun v w => f.map_app w v

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

private theorem posDef_toQuadraticMap_baseChange_of_isSymm {B : LinearMap.BilinForm F V}
    (hB : B.IsSymm) (h : B.toQuadraticMap.PosDef) : (B.baseChange K).toQuadraticMap.PosDef := by
  let _ : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  let _ : Invertible (2 : K) := (Invertible.map (algebraMap F K) 2).copy 2 (map_ofNat _ _).symm
  -- An orthogonal basis `v` base-changes to an orthogonal basis `w` of `B.baseChange K`, whose
  -- diagonal values are the images of the positive diagonal values of `B`.
  obtain ⟨v, hv⟩ := exists_orthogonal_basis (isSymm_iff.mp hB)
  set w := v.baseChange K
  have hassoc : QuadraticMap.associated (R := K) (B.baseChange K).toQuadraticMap = B.baseChange K :=
    QuadraticMap.associated_left_inverse K (IsSymm.baseChange K (isSymm_iff.mp hB)).eq
  have hw (i j) : B.baseChange K (w i) (w j) = algebraMap F K (B (v i) (v j)) := by
    simp [w, Basis.baseChange_apply, baseChange_tmul, Algebra.algebraMap_eq_smul_one]
  have hortho : (QuadraticMap.associated (R := K) (B.baseChange K).toQuadraticMap).IsOrthoᵢ w := by
    intro i j hij
    simp only [Function.onFun, hassoc, hw, hv hij, map_zero]
  have hpos (i) : 0 < (B.baseChange K).toQuadraticMap (w i) := by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hw]
    exact algebraMap_pos K (h _ (v.ne_zero i))
  have hQ : (B.baseChange K).toQuadraticMap =
      ((B.baseChange K).toQuadraticMap.basisRepr w).comp w.equivFun.toLinearMap := by
    ext z
    simp [QuadraticMap.basisRepr]
  rw [hQ, QuadraticMap.basisRepr_eq_of_iIsOrtho _ w hortho]
  exact ((QuadraticMap.posDef_weightedSumSquares_iff _).mpr hpos).comp _ w.equivFun.injective

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
      rw [baseChange_add, baseChange_flip]
    simpa only [hbase, posDef_toQuadraticMap_add_flip_iff] using this (B + B.flip) hsym
  constructor
  · -- Reflection: evaluate on the nonzero vector `1 ⊗ x`.
    intro h x hx
    have h1 : (1 : K) ⊗ₜ[F] x ≠ 0 :=
      fun h0 ↦ hx ((Module.FaithfullyFlat.one_tmul_eq_zero_iff F V x).mp h0)
    have := h _ h1
    rw [LinearMap.BilinMap.toQuadraticMap_apply, baseChange_tmul, one_mul] at this
    rw [LinearMap.BilinMap.toQuadraticMap_apply]
    exact (smul_pos_iff_of_pos_right zero_lt_one).mp this
  · exact posDef_toQuadraticMap_baseChange_of_isSymm hB

end PosDef

end LinearMap.BilinForm
