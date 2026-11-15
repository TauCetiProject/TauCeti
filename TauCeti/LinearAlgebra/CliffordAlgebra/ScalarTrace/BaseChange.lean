/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Complexification
public import TauCeti.LinearAlgebra.CliffordAlgebra.ScalarTrace.Basic
-- Private: the finiteness instances and the orthogonal spanning list are used only in proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

/-!
# The scalar part of a base-changed Clifford algebra

For an `R`-algebra `A`, the scalar part `τ = CliffordAlgebra.scalarTrace Q` extends `A`-linearly
to the tensor carrier `A ⊗[R] Cℓ(M, Q)`, as `Module.Dual.baseChange A (scalarTrace Q)`, sending
`a ⊗ₜ x` to `τ x • a`. On the other hand the base-changed Clifford algebra `Cℓ(A ⊗ M, Q_A)` has
its own scalar part `scalarTrace (Q.baseChange A)`. This file shows that the two agree under
Mathlib's identification `CliffordAlgebra.ofBaseChange : A ⊗[R] Cℓ(M, Q) → Cℓ(A ⊗ M, Q_A)`, so
the transported trace on the base-changed algebra is the intrinsic scalar part, and derives the
properties of the extended trace on both carriers.

For a real quadratic form and `A = ℂ` this is the complexified scalar trace: it is normalized,
cyclic, a normalized regular trace, invariant under complex algebra isomorphisms, and it
intertwines complex conjugation of the coefficients with complex conjugation of the value. The
last property, together with the invariance under the grade involution and the reversion, shows
that the scalar part of `CliffordAlgebra.conjStar x` is the complex conjugate of that of `x`.

## Main results

* `CliffordAlgebra.scalarTrace_ofBaseChange`: over a field, the scalar part of the base-changed
  Clifford algebra is the base change of the scalar part; the general form
  `CliffordAlgebra.scalarTrace_ofBaseChange_of_pairwise_isOrtho` only needs `M` to be spanned by
  pairwise orthogonal vectors.
* `CliffordAlgebra.scalarTrace_ofBaseChangeAux`: on the image of `Cℓ(M, Q)`, the scalar part of
  the base-changed algebra is the scalar part of `Cℓ(M, Q)`.
* `CliffordAlgebra.baseChange_scalarTrace_one` and
  `CliffordAlgebra.baseChange_scalarTrace_mul_comm`: the extended trace is normalized and cyclic.
* `CliffordAlgebra.trace_mulLeft_eq_two_pow_mul_baseChange_scalarTrace`: the extended trace is the
  normalized trace of the left regular representation of `A ⊗[K] Cℓ(V, Q)`.
* `CliffordAlgebra.baseChange_scalarTrace_eq_of_algEquiv`: the extended trace is invariant under
  algebra isomorphisms of tensor carriers over a field.
* `CliffordAlgebra.baseChange_scalarTrace_congr_conjAe`,
  `CliffordAlgebra.scalarTrace_complexConj` and `CliffordAlgebra.scalarTrace_conjStar`:
  compatibility with complex conjugation.

## Implementation notes

The comparison uses the uniqueness of the scalar part
(`CliffordAlgebra.eq_smul_scalarTrace`): the base-changed generators `1 ⊗ₜ v` of a pairwise
orthogonal spanning list of `M` are pairwise orthogonal and span `A ⊗ M`, and the extended trace
transported along `CliffordAlgebra.toBaseChange` is normalized, cyclic and invariant under the
grade involution.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I.
-/

public section

open scoped TensorProduct ComplexConjugate

namespace CliffordAlgebra

section CommRing

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
  {Q : QuadraticForm R M} (A : Type*) [CommRing A] [Algebra R A]

/-- The extended scalar part is normalized. -/
@[simp]
theorem baseChange_scalarTrace_one :
    Module.Dual.baseChange A (scalarTrace Q) 1 = 1 := by
  simp [Algebra.TensorProduct.one_def]

/-- **Cyclicity of the extended scalar part** on the tensor carrier `A ⊗[R] Cℓ(M, Q)`. -/
theorem baseChange_scalarTrace_mul_comm (x y : A ⊗[R] CliffordAlgebra Q) :
    Module.Dual.baseChange A (scalarTrace Q) (x * y) =
      Module.Dual.baseChange A (scalarTrace Q) (y * x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [add_mul, mul_add, map_add, map_add, hx, hx']
  | tmul a u =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => rw [add_mul, mul_add, map_add, map_add, hy, hy']
    | tmul b w =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, Module.Dual.baseChange_apply_tmul,
        scalarTrace_mul_comm u w, mul_comm a b]

/-- The extended scalar part is invariant under the grade involution of the right factor. -/
private theorem baseChange_scalarTrace_map_involute (x : A ⊗[R] CliffordAlgebra Q) :
    Module.Dual.baseChange A (scalarTrace Q)
        (TensorProduct.map LinearMap.id involute.toLinearMap x) =
      Module.Dual.baseChange A (scalarTrace Q) x := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, map_add, hx, hx']
  | tmul a u => simp

variable [Invertible (2 : A)]

/-- **The scalar part of a base-changed Clifford algebra is the base change of the scalar part**,
when `M` is spanned by a list of pairwise orthogonal vectors:
`scalarTrace (Q.baseChange A) (ofBaseChange A Q (a ⊗ₜ x)) = scalarTrace Q x • a`. -/
theorem scalarTrace_ofBaseChange_of_pairwise_isOrtho {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (hspan : Submodule.span R {x : M | x ∈ l} = ⊤) (x : A ⊗[R] CliffordAlgebra Q) :
    scalarTrace (Q.baseChange A) (ofBaseChange A Q x) =
      Module.Dual.baseChange A (scalarTrace Q) x := by
  let l' : List (A ⊗[R] M) := l.map (TensorProduct.mk R A M 1)
  have hl' : l'.Pairwise (Q.baseChange A).IsOrtho :=
    List.pairwise_map.mpr <| hl.imp fun {v w} h => by
      rw [QuadraticMap.isOrtho_def] at h ⊢
      simp [← TensorProduct.tmul_add, h, add_smul]
  have hspan' : Submodule.span A {x | x ∈ l'} = ⊤ := by
    have hset : {x | x ∈ l'} = TensorProduct.mk R A M 1 '' {x : M | x ∈ l} := by
      ext; simp [l']
    rw [hset, ← Submodule.baseChange_span, hspan, Submodule.baseChange_top]
  let f : CliffordAlgebra (Q.baseChange A) →ₗ[A] A :=
    Module.Dual.baseChange A (scalarTrace Q) ∘ₗ (toBaseChange A Q).toLinearMap
  have h := eq_smul_scalarTrace hl' hspan' f
    (fun x y => by simp [f, baseChange_scalarTrace_mul_comm])
    (fun x => by simp [f, toBaseChange_involute, baseChange_scalarTrace_map_involute])
  have h1 : f 1 = 1 := by simp [f]
  rw [h1, one_smul] at h
  simpa [f] using (LinearMap.congr_fun h (ofBaseChange A Q x)).symm

end CommRing

section Field

open Module

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [Invertible (2 : K)]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

variable (A : Type*) [CommRing A] [Algebra K A]

/-- **The extended scalar part is the normalized regular trace** of the tensor carrier:
`trace (x * ·) = 2 ^ finrank K V * τ_A x` on `A ⊗[K] Cℓ(V, Q)`. -/
theorem trace_mulLeft_eq_two_pow_mul_baseChange_scalarTrace (x : A ⊗[K] CliffordAlgebra Q) :
    LinearMap.trace A (A ⊗[K] CliffordAlgebra Q) (LinearMap.mulLeft A x) =
      2 ^ finrank K V * Module.Dual.baseChange A (scalarTrace Q) x := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    have h : LinearMap.mulLeft A (x + x') = LinearMap.mulLeft A x + LinearMap.mulLeft A x' := by
      ext
      simp [add_mul]
    rw [h, map_add, hx, hx', map_add, mul_add]
  | tmul a u =>
    have h : LinearMap.mulLeft A (a ⊗ₜ[K] u) = a • (LinearMap.mulLeft K u).baseChange A := by
      ext
      simp [TensorProduct.smul_tmul']
    rw [h, map_smul, LinearMap.trace_baseChange, trace_mulLeft_eq_two_pow_mul_scalarTrace,
      Module.Dual.baseChange_apply_tmul, map_mul, map_pow, map_ofNat, smul_eq_mul,
      Algebra.smul_def]
    ring

variable [Invertible (2 : A)]

/-- **The scalar part of a base-changed Clifford algebra is the base change of the scalar part**:
for a quadratic form on a finite-dimensional space over a field in which `2` is invertible,
`scalarTrace (Q.baseChange A) (ofBaseChange A Q (a ⊗ₜ x)) = scalarTrace Q x • a`. -/
@[simp]
theorem scalarTrace_ofBaseChange (x : A ⊗[K] CliffordAlgebra Q) :
    scalarTrace (Q.baseChange A) (ofBaseChange A Q x) =
      Module.Dual.baseChange A (scalarTrace Q) x := by
  obtain ⟨l, hl, hspan⟩ := QuadraticMap.exists_list_pairwise_isOrtho Q
  exact scalarTrace_ofBaseChange_of_pairwise_isOrtho A hl hspan x

/-- The scalar part of the base-changed Clifford algebra, read on the tensor carrier: it is the
base change of the scalar part. -/
@[simp]
theorem baseChange_scalarTrace_toBaseChange (x : CliffordAlgebra (Q.baseChange A)) :
    Module.Dual.baseChange A (scalarTrace Q) (toBaseChange A Q x) =
      scalarTrace (Q.baseChange A) x := by
  rw [← scalarTrace_ofBaseChange, ofBaseChange_toBaseChange]

/-- **Scalar extension of the scalar part**: on the image of `Cℓ(V, Q)` in the base-changed
Clifford algebra, the scalar part is the scalar part of `Cℓ(V, Q)`. -/
@[simp]
theorem scalarTrace_ofBaseChangeAux (x : CliffordAlgebra Q) :
    scalarTrace (Q.baseChange A) (ofBaseChangeAux A Q x) = algebraMap K A (scalarTrace Q x) := by
  rw [← baseChange_scalarTrace_toBaseChange, toBaseChange_ofBaseChangeAux,
    Module.Dual.baseChange_apply_tmul, Algebra.algebraMap_eq_smul_one]

/-- **The extended scalar part is invariant under algebra isomorphisms** between tensor carriers
`L ⊗[K] Cℓ(V, Q)` and `L ⊗[K] Cℓ(V', Q')` over a field `L`. -/
theorem baseChange_scalarTrace_eq_of_algEquiv (L : Type*) [Field L] [Algebra K L]
    [Invertible (2 : L)] {V' : Type*} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    {Q' : QuadraticForm K V'}
    (e : L ⊗[K] CliffordAlgebra Q ≃ₐ[L] L ⊗[K] CliffordAlgebra Q') (x : L ⊗[K] CliffordAlgebra Q) :
    Module.Dual.baseChange L (scalarTrace Q') (e x) =
      Module.Dual.baseChange L (scalarTrace Q) x := by
  rw [← scalarTrace_ofBaseChange, ← scalarTrace_ofBaseChange,
    ← scalarTrace_eq_of_algEquiv
      (((equivBaseChange L Q).trans e).trans (equivBaseChange L Q').symm) (ofBaseChange L Q x)]
  simp

end Field

/-! ### Complex conjugation -/

section Complex

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}

/-- The complexified scalar part intertwines complex conjugation of the coefficients `conj ⊗ id`
with complex conjugation. -/
theorem baseChange_scalarTrace_congr_conjAe (x : ℂ ⊗[ℝ] CliffordAlgebra Q) :
    Module.Dual.baseChange ℂ (scalarTrace Q)
        (Algebra.TensorProduct.congr Complex.conjAe AlgEquiv.refl x) =
      conj (Module.Dual.baseChange ℂ (scalarTrace Q) x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | tmul z u => simp [Complex.real_smul]

variable [FiniteDimensional ℝ V]

/-- The scalar part of the complexified Clifford algebra intertwines
`CliffordAlgebra.complexConj` with complex conjugation. -/
@[simp]
theorem scalarTrace_complexConj (x : CliffordAlgebra (Q.baseChange ℂ)) :
    scalarTrace (Q.baseChange ℂ) (complexConj Q x) = conj (scalarTrace (Q.baseChange ℂ) x) := by
  rw [← baseChange_scalarTrace_toBaseChange, toBaseChange_complexConj,
    baseChange_scalarTrace_congr_conjAe, baseChange_scalarTrace_toBaseChange]

/-- The scalar part of the conjugate-linear Clifford involution `CliffordAlgebra.conjStar x` is the
complex conjugate of the scalar part of `x`. -/
@[simp]
theorem scalarTrace_conjStar (x : CliffordAlgebra (Q.baseChange ℂ)) :
    scalarTrace (Q.baseChange ℂ) (conjStar Q x) = conj (scalarTrace (Q.baseChange ℂ) x) := by
  rw [conjStar_apply, scalarTrace_complexConj, star_def, scalarTrace_reverse, scalarTrace_involute]

end Complex

end CliffordAlgebra
