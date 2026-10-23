/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Star

/-!
# Complex conjugation on a complexified real Clifford algebra

For a real quadratic form `Q`, the complexified Clifford algebra `Cℓ(ℂ ⊗ V, Q_ℂ)` carries two
commuting involutions: Mathlib's complex-linear Clifford conjugation `star = reverse ∘ involute`,
which negates every vector, and complex conjugation `CliffordAlgebra.complexConj` of the
coefficients, which fixes the real vectors `ι (1 ⊗ₜ v)`. Their composite
`CliffordAlgebra.conjStar` is the conjugate-linear anti-automorphism of the complexified
algebra. For the negative-definite form `Q = -g` of a Euclidean space this is the involution
with respect to which a representation on a Hermitian space is a `*`-representation, so that
Clifford multiplication by a real vector is skew-Hermitian.

Under the identification `CliffordAlgebra.equivBaseChange` with the tensor carrier
`ℂ ⊗[ℝ] Cℓ(V, Q)`, `CliffordAlgebra.complexConj` is `conj ⊗ id` and `CliffordAlgebra.conjStar`
is the tensor-product `star`, that is `conj ⊗ star`. The latter uses the real `StarModule`
structure `CliffordAlgebra.starModule_of_trivialStar`, enabled locally.

## Main definitions

* `CliffordAlgebra.complexConj`: coefficientwise complex conjugation, a real algebra
  automorphism of `Cℓ(ℂ ⊗ V, Q_ℂ)`.
* `CliffordAlgebra.conjStar`: the conjugate-linear map `complexConj ∘ star`.

## Main results

* `CliffordAlgebra.complexConj_smul`: `complexConj` is conjugate-linear.
* `CliffordAlgebra.complexConj_unique`: `complexConj` is the unique conjugate-linear ring
  endomorphism fixing the real vectors.
* `CliffordAlgebra.complexConj_complexConj`: `complexConj` is involutive.
* `CliffordAlgebra.conjStar_mul` and `CliffordAlgebra.conjStar_conjStar`: `conjStar` is an
  involutive anti-automorphism.
* `CliffordAlgebra.toBaseChange_conjStar`: on the tensor carrier `conjStar` is the tensor-product
  `star`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, the chapter on Dirac operators.
-/

public section

open scoped TensorProduct ComplexConjugate

namespace CliffordAlgebra

attribute [local instance] starModule_of_trivialStar

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : QuadraticForm ℝ V)

/-! ### Complex conjugation of coefficients -/

/-- Complex conjugation of the coefficients of the complexified Clifford algebra: the ring
automorphism of `Cℓ(ℂ ⊗ V, Q_ℂ)` conjugating scalars and fixing the real vectors
`ι (1 ⊗ₜ v)`. It is `CliffordAlgebra.baseChangeCongr` for `Complex.conjAe`, stated as a ring
equivalence since its conjugate-linearity is recorded by `CliffordAlgebra.complexConj_smul`. -/
noncomputable def complexConj :
    CliffordAlgebra (Q.baseChange ℂ) ≃+* CliffordAlgebra (Q.baseChange ℂ) :=
  (baseChangeCongr Complex.conjAe Q).toRingEquiv

theorem complexConj_apply (x : CliffordAlgebra (Q.baseChange ℂ)) :
    complexConj Q x = baseChangeCongr Complex.conjAe Q x :=
  (rfl)

/-- On the tensor carrier `ℂ ⊗[ℝ] Cℓ(V, Q)`, `CliffordAlgebra.complexConj` is `conj ⊗ id`. -/
@[simp]
theorem toBaseChange_complexConj (x : CliffordAlgebra (Q.baseChange ℂ)) :
    toBaseChange ℂ Q (complexConj Q x) =
      Algebra.TensorProduct.congr Complex.conjAe AlgEquiv.refl (toBaseChange ℂ Q x) := by
  rw [complexConj_apply, toBaseChange_baseChangeCongr]

@[simp]
theorem complexConj_algebraMap (z : ℂ) :
    complexConj Q (algebraMap ℂ _ z) = algebraMap ℂ _ (conj z) := by
  rw [complexConj_apply, baseChangeCongr_algebraMap, Complex.conjAe_coe]

@[simp]
theorem complexConj_ι_tmul (z : ℂ) (v : V) :
    complexConj Q (ι (Q.baseChange ℂ) (z ⊗ₜ v)) = ι (Q.baseChange ℂ) (conj z ⊗ₜ v) := by
  rw [complexConj_apply, baseChangeCongr_ι_tmul, Complex.conjAe_coe]

/-- `CliffordAlgebra.complexConj` fixes the real Clifford algebra. -/
@[simp]
theorem complexConj_ofBaseChangeAux (x : CliffordAlgebra Q) :
    complexConj Q (ofBaseChangeAux ℂ Q x) = ofBaseChangeAux ℂ Q x := by
  rw [complexConj_apply, baseChangeCongr_ofBaseChangeAux]

/-- `CliffordAlgebra.complexConj` is conjugate-linear. -/
@[simp]
theorem complexConj_smul (z : ℂ) (x : CliffordAlgebra (Q.baseChange ℂ)) :
    complexConj Q (z • x) = conj z • complexConj Q x := by
  rw [complexConj_apply, complexConj_apply, baseChangeCongr_smul, Complex.conjAe_coe]

/-- `CliffordAlgebra.complexConj` is the unique conjugate-linear ring endomorphism of the
complexified Clifford algebra fixing the real vectors `ι (1 ⊗ₜ v)`. -/
theorem complexConj_unique
    (f : CliffordAlgebra (Q.baseChange ℂ) →+* CliffordAlgebra (Q.baseChange ℂ))
    (hsmul : ∀ (z : ℂ) x, f (z • x) = conj z • f x)
    (hι : ∀ v : V, f (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) = ι (Q.baseChange ℂ) (1 ⊗ₜ v)) :
    f = (complexConj Q : CliffordAlgebra (Q.baseChange ℂ) →+* CliffordAlgebra (Q.baseChange ℂ)) :=
  baseChange_ringHom_ext Q
    (fun z ↦ by simp [Algebra.algebraMap_eq_smul_one, hsmul])
    (fun v ↦ by simp [hι])

/-- `CliffordAlgebra.complexConj` is involutive. -/
@[simp]
theorem complexConj_complexConj (x : CliffordAlgebra (Q.baseChange ℂ)) :
    complexConj Q (complexConj Q x) = x := by
  have h : Complex.conjAe.trans Complex.conjAe = AlgEquiv.refl := by
    ext z
    simp
  simp [complexConj_apply, ← AlgEquiv.trans_apply, h]

/-- `CliffordAlgebra.complexConj` is its own inverse. -/
@[simp]
theorem complexConj_symm : (complexConj Q).symm = complexConj Q :=
  RingEquiv.ext fun x ↦ (complexConj Q).symm_apply_eq.mpr (complexConj_complexConj Q x).symm

@[simp]
theorem complexConj_involute (x : CliffordAlgebra (Q.baseChange ℂ)) :
    complexConj Q (involute x) = involute (complexConj Q x) := by
  rw [complexConj_apply, complexConj_apply, baseChangeCongr_involute]

@[simp]
theorem complexConj_reverse (x : CliffordAlgebra (Q.baseChange ℂ)) :
    complexConj Q (reverse x) = reverse (complexConj Q x) := by
  rw [complexConj_apply, complexConj_apply, baseChangeCongr_reverse]

@[simp]
theorem complexConj_star (x : CliffordAlgebra (Q.baseChange ℂ)) :
    complexConj Q (star x) = star (complexConj Q x) := by
  rw [complexConj_apply, complexConj_apply, baseChangeCongr_star]

/-! ### The conjugate-linear Clifford involution -/

/-- The conjugate-linear Clifford involution of the complexified Clifford algebra: Clifford
conjugation `star = reverse ∘ involute` followed by complex conjugation of the coefficients. It
is an involutive anti-automorphism (`CliffordAlgebra.conjStar_mul`,
`CliffordAlgebra.conjStar_conjStar`) negating the real vectors. -/
noncomputable def conjStar :
    CliffordAlgebra (Q.baseChange ℂ) →ₗ⋆[ℂ] CliffordAlgebra (Q.baseChange ℂ) where
  toFun x := complexConj Q (star x)
  map_add' x y := by rw [star_add, map_add]
  map_smul' z x := by rw [star_smul, complexConj_smul]

theorem conjStar_apply (x : CliffordAlgebra (Q.baseChange ℂ)) :
    conjStar Q x = complexConj Q (star x) :=
  (rfl)

theorem conjStar_apply' (x : CliffordAlgebra (Q.baseChange ℂ)) :
    conjStar Q x = star (complexConj Q x) :=
  (complexConj_star Q x)

/-- `CliffordAlgebra.conjStar` reverses products. -/
@[simp]
theorem conjStar_mul (x y : CliffordAlgebra (Q.baseChange ℂ)) :
    conjStar Q (x * y) = conjStar Q y * conjStar Q x := by
  simp only [conjStar_apply, star_mul, map_mul]

@[simp]
theorem conjStar_one : conjStar Q 1 = 1 := by
  simp [conjStar_apply]

/-- `CliffordAlgebra.conjStar` is involutive. -/
@[simp]
theorem conjStar_conjStar (x : CliffordAlgebra (Q.baseChange ℂ)) :
    conjStar Q (conjStar Q x) = x := by
  rw [conjStar_apply, conjStar_apply', star_star, complexConj_complexConj]

@[simp]
theorem conjStar_algebraMap (z : ℂ) :
    conjStar Q (algebraMap ℂ _ z) = algebraMap ℂ _ (conj z) := by
  simp [conjStar_apply]

/-- `CliffordAlgebra.conjStar` negates vectors and conjugates their coefficients; in particular
it negates the real vectors `ι (1 ⊗ₜ v)`. -/
@[simp]
theorem conjStar_ι_tmul (z : ℂ) (v : V) :
    conjStar Q (ι (Q.baseChange ℂ) (z ⊗ₜ v)) = -ι (Q.baseChange ℂ) (conj z ⊗ₜ v) := by
  simp [conjStar_apply]

/-- On the real Clifford algebra, `CliffordAlgebra.conjStar` is Clifford conjugation. -/
@[simp]
theorem conjStar_ofBaseChangeAux (x : CliffordAlgebra Q) :
    conjStar Q (ofBaseChangeAux ℂ Q x) = ofBaseChangeAux ℂ Q (star x) := by
  rw [conjStar_apply, ← ofBaseChangeAux_star, complexConj_ofBaseChangeAux]

/-- On the tensor carrier `ℂ ⊗[ℝ] Cℓ(V, Q)`, `CliffordAlgebra.conjStar` is the tensor-product
`star`, acting by `z ⊗ₜ a ↦ conj z ⊗ₜ star a`. -/
theorem toBaseChange_conjStar (x : CliffordAlgebra (Q.baseChange ℂ)) :
    toBaseChange ℂ Q (conjStar Q x) = star (toBaseChange ℂ Q x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap z => simp [Algebra.TensorProduct.algebraMap_apply]
  | ι w =>
      induction w using TensorProduct.inductionOn with
      | tmul z v => simp [TensorProduct.tmul_neg]
      | add w w' hw hw' => simp only [map_add, hw, hw', star_add]
  | add x y hx hy => simp only [map_add, hx, hy, star_add]
  | mul x y hx hy => simp only [conjStar_mul, map_mul, hx, hy, star_mul]

end CliffordAlgebra
