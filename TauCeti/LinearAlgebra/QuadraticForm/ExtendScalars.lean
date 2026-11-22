/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Pi
public import TauCeti.LinearAlgebra.QuadraticForm.Binary
public import TauCeti.LinearAlgebra.QuadraticForm.MvPolynomial

/-!
# Coordinate scalar extension of quadratic forms

For a quadratic form `Q` on `ι → R`, `ι` finite, and a commutative `R`-algebra `A`,
`QuadraticMap.extendScalars Q A` is the quadratic form on `ι → A` given by the coordinate
polynomial of `Q` with its coefficients mapped into `A`:
`x ↦ ∑ᵢ Q(eᵢ) xᵢ² + ∑_{i ≠ j} polar Q (eᵢ, eⱼ) xᵢ xⱼ`, the second sum over unordered pairs.

Mathlib's `QuadraticForm.baseChange` assumes `2` invertible, since it goes through the symmetric
bilinear form `QuadraticMap.associated`. The coordinate extension needs no such assumption: the
mixed coefficients `polar Q (eᵢ, eⱼ)` are kept as they are, so it extends forms in characteristic
two, where the quadratic form is not determined by its polar form. On `A ⊗[R] (ι → R)` it is the
unique quadratic form with `a ⊗ v ↦ a² Q(v)`, and when `2` is invertible it agrees with
`QuadraticForm.baseChange`.

## Main definitions and results

* `QuadraticMap.extendScalars`: the coordinate scalar extension.
* `QuadraticMap.extendScalars_apply`: it evaluates the polynomial `QuadraticMap.toMvPolynomial`.
* `QuadraticMap.extendScalars_algebraMap`: it agrees with `Q` on vectors with coordinates in `R`,
  and `QuadraticMap.eq_extendScalars_iff` says that this characterizes it.
* `QuadraticMap.toMatrix'_polarBilin_extendScalars`: the Gram matrix of its polar form is the
  image of the Gram matrix of the polar form of `Q`.
* `QuadraticMap.nondegenerate_polarBilin_extendScalars_iff`: extension preserves and reflects
  nonsingularity.
* `QuadraticMap.extendScalars_self`, `QuadraticMap.extendScalars_extendScalars`: the identity
  extension and towers.
* `QuadraticMap.extendScalars_comp`: precomposition with a linear map commutes with extension,
  so that isometries extend (`QuadraticMap.IsometryEquiv.extendScalars`).
* `QuadraticMap.extendScalars_prod_comp_sumArrowLequivProdArrow`: extension commutes with
  orthogonal sums.
* `QuadraticMap.extendScalars_comp_piScalarRight`: agreement with `QuadraticForm.baseChange`.
* `QuadraticMap.extendScalars_comp_basis_eq`: for a quadratic form on a free module, the
  extension along a basis, read on `A ⊗[R] V`, does not depend on the basis.
* `TauCeti.extendScalars_binaryQuadraticForm`: the extension of the binary block `[a, b]` is the
  block with the mapped coefficients; in particular the hyperbolic plane `[0, 0]` extends to the
  hyperbolic plane.

## References

* R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  §7, scalar extension before Lemma 7.15.
-/

public section

noncomputable section

open MvPolynomial TensorProduct

namespace QuadraticMap

variable {R A B ι κ : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- A quadratic form on `ι → A` is determined by its values on the vectors whose coordinates lie
in the image of `R`. -/
theorem ext_algebraMap [Finite ι] {Q₁ Q₂ : QuadraticForm A (ι → A)}
    (h : ∀ v : ι → R, Q₁ (fun i ↦ algebraMap R A (v i)) = Q₂ (fun i ↦ algebraMap R A (v i))) :
    Q₁ = Q₂ := by
  cases nonempty_fintype ι
  classical
  have key : Q₁.comp (piScalarRight R A A ι).toLinearMap =
      Q₂.comp (piScalarRight R A A ι).toLinearMap :=
    _root_.baseChange_ext fun v ↦ by
      simpa [Algebra.algebraMap_eq_smul_one] using h v
  ext x
  simpa using congr($key ((piScalarRight R A A ι).symm x))

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The cross term `polar Q (eᵢ, eⱼ) xᵢ xⱼ` of an unordered pair of coordinates, with its
coefficient mapped into `A`. -/
private def extendScalarsCrossTerm (Q : QuadraticForm R (ι → R)) (A : Type*) [CommRing A]
    [Algebra R A] : Sym2 ι → QuadraticForm A (ι → A) :=
  Sym2.lift ⟨fun i j ↦ algebraMap R A (polar Q (Pi.single i 1) (Pi.single j 1)) • proj i j,
    fun i j ↦ by
      ext x
      simp only [smul_apply, proj_apply, smul_eq_mul]
      rw [polar_comm]
      ring⟩

/-- The scalar extension of a quadratic form on `ι → R` to a commutative `R`-algebra `A`, by its
coordinate polynomial: `x ↦ ∑ᵢ Q(eᵢ) xᵢ² + ∑_{i ≠ j} polar Q (eᵢ, eⱼ) xᵢ xⱼ`, the second sum
over unordered pairs, with coefficients mapped into `A`. Unlike `QuadraticForm.baseChange` it does
not need `2` to be invertible. -/
def extendScalars (Q : QuadraticForm R (ι → R)) (A : Type*) [CommRing A] [Algebra R A] :
    QuadraticForm A (ι → A) :=
  ∑ i : ι, algebraMap R A (Q (Pi.single i 1)) • proj i i +
    ∑ ij ∈ (Finset.univ : Finset ι).sym2 with ¬ ij.IsDiag, extendScalarsCrossTerm Q A ij

/-- The scalar extension of `Q` evaluates the coordinate polynomial of `Q` at points of `A`. -/
theorem extendScalars_apply (Q : QuadraticForm R (ι → R)) (x : ι → A) :
    Q.extendScalars A x = aeval x Q.toMvPolynomial := by
  rw [toMvPolynomial_def, extendScalars, map_add, map_sum, map_sum, add_apply]
  congr 1
  · simp [proj_apply, Algebra.smul_def, _root_.sq]
  · simp only [sum_apply]
    refine Finset.sum_congr rfl fun ij _ ↦ ?_
    induction ij using Sym2.ind with
    | _ i j =>
      simp only [extendScalarsCrossTerm, Sym2.lift_mk, smul_apply, proj_apply, smul_eq_mul,
        map_mul, aeval_C, aeval_X]
      ring

/-- Extending scalars from `R` to `R` does nothing. -/
@[simp]
theorem extendScalars_self (Q : QuadraticForm R (ι → R)) : Q.extendScalars R = Q := by
  ext x
  rw [extendScalars_apply, aeval_eq_eval, eval_toMvPolynomial]

/-- An algebra homomorphism `A →ₐ[R] B` carries values of the extension to `A` to values of the
extension to `B`. -/
theorem map_extendScalars (Q : QuadraticForm R (ι → R)) (f : A →ₐ[R] B) (x : ι → A) :
    f (Q.extendScalars A x) = Q.extendScalars B (fun i ↦ f (x i)) := by
  rw [extendScalars_apply, extendScalars_apply, comp_aeval_apply]

/-- The scalar extension of `Q` agrees with `Q` on vectors with coordinates in `R`. -/
@[simp]
theorem extendScalars_algebraMap (Q : QuadraticForm R (ι → R)) (v : ι → R) :
    Q.extendScalars A (fun i ↦ algebraMap R A (v i)) = algebraMap R A (Q v) := by
  simpa using (map_extendScalars Q (Algebra.ofId R A) v).symm

/-- **Characterization of the scalar extension**: a quadratic form on `ι → A` is the scalar
extension of `Q` exactly when it agrees with `Q` on vectors with coordinates in `R`. -/
theorem eq_extendScalars_iff {Q : QuadraticForm R (ι → R)} {Q' : QuadraticForm A (ι → A)} :
    Q' = Q.extendScalars A ↔
      ∀ v : ι → R, Q' (fun i ↦ algebraMap R A (v i)) = algebraMap R A (Q v) :=
  ⟨fun h v ↦ h ▸ extendScalars_algebraMap Q v,
    fun h ↦ ext_algebraMap fun v ↦ by rw [h, extendScalars_algebraMap]⟩

/-- The zero form extends to the zero form. -/
@[simp]
theorem extendScalars_zero : (0 : QuadraticForm R (ι → R)).extendScalars A = 0 :=
  (eq_extendScalars_iff.mpr fun v ↦ by simp).symm

/-- Scalar extension is additive. -/
@[simp]
theorem extendScalars_add (Q₁ Q₂ : QuadraticForm R (ι → R)) :
    (Q₁ + Q₂).extendScalars A = Q₁.extendScalars A + Q₂.extendScalars A :=
  (eq_extendScalars_iff.mpr fun v ↦ by simp).symm

/-- Scalar extension carries the scaled form `c Q` to the extension of `Q` scaled by the image
of `c`. -/
@[simp]
theorem extendScalars_smul (c : R) (Q : QuadraticForm R (ι → R)) :
    (c • Q).extendScalars A = algebraMap R A c • Q.extendScalars A :=
  (eq_extendScalars_iff.mpr fun v ↦ by simp [Algebra.smul_def]).symm

/-- The scalar extension of `Q` scales by `a²` along `a ⊗ v`: read on `A ⊗[R] (ι → R)`, it sends
`a ⊗ v` to `a² Q(v)`, as `QuadraticForm.baseChange` does when `2` is invertible. -/
theorem extendScalars_piScalarRight_tmul (Q : QuadraticForm R (ι → R)) (a : A) (v : ι → R) :
    Q.extendScalars A (piScalarRight R A A ι (a ⊗ₜ v)) = Q v • (a * a) := by
  have h : piScalarRight R A A ι (a ⊗ₜ v) = a • fun i ↦ algebraMap R A (v i) := by
    ext i
    simp [Algebra.smul_def, mul_comm]
  rw [h, QuadraticMap.map_smul, extendScalars_algebraMap, smul_eq_mul, Algebra.smul_def,
    mul_comm]

/-- When `2` is invertible, the scalar extension of `Q`, read on `A ⊗[R] (ι → R)`, is Mathlib's
`QuadraticForm.baseChange`. -/
theorem extendScalars_comp_piScalarRight [Invertible (2 : R)] (Q : QuadraticForm R (ι → R)) :
    (Q.extendScalars A).comp (piScalarRight R A A ι).toLinearMap = Q.baseChange A :=
  _root_.baseChange_ext fun v ↦ by
    simp only [comp_apply, LinearEquiv.coe_coe, extendScalars_piScalarRight_tmul,
      QuadraticForm.baseChange_tmul]

/-- The polar form of the scalar extension of `Q` agrees with the polar form of `Q` on vectors
with coordinates in `R`. -/
@[simp]
theorem polar_extendScalars_algebraMap (Q : QuadraticForm R (ι → R)) (v w : ι → R) :
    polar (Q.extendScalars A) (fun i ↦ algebraMap R A (v i)) (fun i ↦ algebraMap R A (w i)) =
      algebraMap R A (polar Q v w) := by
  have h : ((fun i ↦ algebraMap R A (v i)) + fun i ↦ algebraMap R A (w i)) =
      fun i ↦ algebraMap R A ((v + w) i) := by
    ext i
    simp
  simp only [polar, h, extendScalars_algebraMap, map_sub]

/-- The Gram matrix of the polar form of the scalar extension of `Q` is the image in `A` of the
Gram matrix of the polar form of `Q`. -/
theorem toMatrix'_polarBilin_extendScalars (Q : QuadraticForm R (ι → R)) :
    LinearMap.BilinForm.toMatrix' (Q.extendScalars A).polarBilin =
      (LinearMap.BilinForm.toMatrix' Q.polarBilin).map (algebraMap R A) := by
  have h (i : ι) :
      (Pi.single i 1 : ι → A) = fun k ↦ algebraMap R A ((Pi.single i (1 : R) : ι → R) k) := by
    ext k
    simp [Pi.single_apply, apply_ite (algebraMap R A) (_ = _)]
  ext i j
  simp only [LinearMap.BilinForm.toMatrix'_apply, polarBilin_apply_apply, Matrix.map_apply]
  rw [h i, h j, polar_extendScalars_algebraMap]

/-- For an injective algebra map `R → A` into an integral domain, for instance a field extension,
scalar extension preserves and reflects nonsingularity: the polar form of the extension is
nondegenerate exactly when the polar form of `Q` is. -/
theorem nondegenerate_polarBilin_extendScalars_iff [IsDomain A] [FaithfulSMul R A]
    {Q : QuadraticForm R (ι → R)} :
    (Q.extendScalars A).polarBilin.Nondegenerate ↔ Q.polarBilin.Nondegenerate := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R A).isDomain _
  refine LinearMap.BilinForm.nondegenerate_toMatrix'_iff.symm.trans
    (Iff.trans ?_ LinearMap.BilinForm.nondegenerate_toMatrix'_iff)
  rw [Matrix.nondegenerate_iff_det_ne_zero, Matrix.nondegenerate_iff_det_ne_zero,
    toMatrix'_polarBilin_extendScalars, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ne_eq,
    ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]

/-- Scalar extension in a tower: extending from `R` to `A` and then from `A` to `B` is extending
from `R` to `B`. -/
@[simp]
theorem extendScalars_extendScalars [Algebra A B] [IsScalarTower R A B]
    (Q : QuadraticForm R (ι → R)) : (Q.extendScalars A).extendScalars B = Q.extendScalars B :=
  (eq_extendScalars_iff.mpr fun w ↦ by
    simpa using (map_extendScalars Q (IsScalarTower.toAlgHom R A B) w).symm).symm

/-- Precomposition with a linear map commutes with scalar extension: the extension of `Q ∘ f` is
the extension of `Q` composed with the base change of `f`, read in coordinates. -/
theorem extendScalars_comp (Q : QuadraticForm R (κ → R)) (f : (ι → R) →ₗ[R] κ → R) :
    (Q.comp f).extendScalars A = (Q.extendScalars A).comp
      ((piScalarRight R A A κ).toLinearMap ∘ₗ f.baseChange A ∘ₗ
        (piScalarRight R A A ι).symm.toLinearMap) := by
  refine (eq_extendScalars_iff.mpr fun v ↦ ?_).symm
  have hv : (piScalarRight R A A ι).symm (fun i ↦ algebraMap R A (v i)) = 1 ⊗ₜ v :=
    piScalarRight_symm_algebraMap R A ι v
  simp only [comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hv,
    LinearMap.baseChange_tmul, extendScalars_piScalarRight_tmul, mul_one, Algebra.smul_def]

/-- Scalar extension commutes with orthogonal sums: the orthogonal sum of coordinate forms on
`ι → R` and `κ → R`, read on `ι ⊕ κ → R`, extends to the orthogonal sum of the extensions. -/
theorem extendScalars_prod_comp_sumArrowLequivProdArrow (Q₁ : QuadraticForm R (ι → R))
    (Q₂ : QuadraticForm R (κ → R)) :
    ((Q₁.prod Q₂).comp (LinearEquiv.sumArrowLequivProdArrow ι κ R R).toLinearMap).extendScalars A =
      ((Q₁.extendScalars A).prod (Q₂.extendScalars A)).comp
        (LinearEquiv.sumArrowLequivProdArrow ι κ A A).toLinearMap := by
  refine (eq_extendScalars_iff.mpr fun v ↦ ?_).symm
  -- Both components of the split vector have coordinates in `R`.
  have h₁ : ((LinearEquiv.sumArrowLequivProdArrow ι κ A A) fun i ↦ algebraMap R A (v i)).1 =
      fun i ↦ algebraMap R A ((LinearEquiv.sumArrowLequivProdArrow ι κ R R v).1 i) := by
    ext
    simp
  have h₂ : ((LinearEquiv.sumArrowLequivProdArrow ι κ A A) fun i ↦ algebraMap R A (v i)).2 =
      fun i ↦ algebraMap R A ((LinearEquiv.sumArrowLequivProdArrow ι κ R R v).2 i) := by
    ext
    simp
  simp only [comp_apply, LinearEquiv.coe_coe, prod_apply, h₁, h₂, extendScalars_algebraMap,
    map_add]

/-- The scalar extension of a diagonal form is the diagonal form with the mapped weights. -/
@[simp]
theorem extendScalars_weightedSumSquares (w : ι → R) :
    (weightedSumSquares R w).extendScalars A =
      weightedSumSquares A (fun i ↦ algebraMap R A (w i)) :=
  (eq_extendScalars_iff.mpr fun v ↦ by simp [weightedSumSquares_apply]).symm

section Basis

variable {V : Type*} [AddCommGroup V] [Module R V]

/-- **Independence of the basis.** For a quadratic form `Q` on a free module `V`, the scalar
extension of `Q` read in a basis `b`, transported to `A ⊗[R] V` along `b`, does not depend on `b`:
it is the unique quadratic form with `a ⊗ v ↦ a² Q(v)`. -/
theorem extendScalars_comp_basis_eq (Q : QuadraticForm R V) (b : Module.Basis ι R V)
    (b' : Module.Basis κ R V) :
    ((Q.comp b.equivFun.symm.toLinearMap).extendScalars A).comp
        ((piScalarRight R A A ι).toLinearMap ∘ₗ b.equivFun.toLinearMap.baseChange A) =
      ((Q.comp b'.equivFun.symm.toLinearMap).extendScalars A).comp
        ((piScalarRight R A A κ).toLinearMap ∘ₗ b'.equivFun.toLinearMap.baseChange A) :=
  _root_.baseChange_ext fun v ↦ by
    simp only [comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
      extendScalars_piScalarRight_tmul, LinearEquiv.symm_apply_apply]

end Basis

end QuadraticMap

namespace QuadraticMap.IsometryEquiv

variable {R A ι κ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Q₁ : QuadraticForm R (ι → R)} {Q₂ : QuadraticForm R (κ → R)}

/-- An isometric equivalence of coordinate quadratic forms extends to an isometric equivalence of
their scalar extensions. The underlying linear equivalence is the base change of `f`, read in
coordinates. -/
def extendScalars (f : Q₁.IsometryEquiv Q₂) (A : Type*) [CommRing A] [Algebra R A] :
    (Q₁.extendScalars A).IsometryEquiv (Q₂.extendScalars A) where
  toLinearEquiv := (piScalarRight R A A ι).symm ≪≫ₗ
    f.toLinearEquiv.baseChange R A _ _ ≪≫ₗ piScalarRight R A A κ
  map_app' x := by
    have h : Q₂.comp f.toLinearEquiv.toLinearMap = Q₁ := QuadraticMap.ext f.map_app
    have key := congr($(extendScalars_comp (A := A) Q₂ f.toLinearEquiv.toLinearMap) x)
    rw [h] at key
    exact key.symm

/-- The linear equivalence underlying the extension of an isometric equivalence is the base change
of the original linear equivalence, read in coordinates. -/
theorem extendScalars_toLinearEquiv (f : Q₁.IsometryEquiv Q₂) :
    (f.extendScalars A).toLinearEquiv = (piScalarRight R A A ι).symm ≪≫ₗ
      f.toLinearEquiv.baseChange R A _ _ ≪≫ₗ piScalarRight R A A κ := (rfl)

/-- The extension of an isometric equivalence agrees with it on vectors with coordinates in `R`. -/
@[simp]
theorem extendScalars_apply_algebraMap (f : Q₁.IsometryEquiv Q₂) (v : ι → R) :
    f.extendScalars A (fun i ↦ algebraMap R A (v i)) = fun i ↦ algebraMap R A (f v i) := by
  have hv : (piScalarRight R A A ι).symm (fun i ↦ algebraMap R A (v i)) = 1 ⊗ₜ v :=
    piScalarRight_symm_algebraMap R A ι v
  rw [← coe_toLinearEquiv, extendScalars_toLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, hv, LinearEquiv.baseChange_tmul]
  ext i
  simp [Algebra.algebraMap_eq_smul_one]

end QuadraticMap.IsometryEquiv

/-- Isometric coordinate quadratic forms have isometric scalar extensions. -/
theorem QuadraticMap.Equivalent.extendScalars {R ι κ : Type*} [CommRing R] [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] {Q₁ : QuadraticForm R (ι → R)}
    {Q₂ : QuadraticForm R (κ → R)} (h : Q₁.Equivalent Q₂) (A : Type*) [CommRing A]
    [Algebra R A] : (Q₁.extendScalars A).Equivalent (Q₂.extendScalars A) :=
  let ⟨f⟩ := h
  ⟨f.extendScalars A⟩

namespace TauCeti

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The scalar extension of the binary block `[a, b] = a x² + x y + b y²` is the binary block with
the mapped coefficients. In particular the hyperbolic plane `[0, 0]` extends to the hyperbolic
plane. -/
@[simp]
theorem extendScalars_binaryQuadraticForm (a b : R) :
    (binaryQuadraticForm R a b).extendScalars A =
      binaryQuadraticForm A (algebraMap R A a) (algebraMap R A b) :=
  (_root_.QuadraticMap.eq_extendScalars_iff.mpr fun v ↦ by simp).symm

end TauCeti
