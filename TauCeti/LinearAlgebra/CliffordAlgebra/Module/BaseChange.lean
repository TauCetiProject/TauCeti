/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange

/-!
# Scalar extension of Clifford algebra homomorphisms

Let `Q` be a quadratic form on an `R`-module `V` with `2` invertible in `R`, let `A` be a
commutative `R`-algebra, and let `B` be a not-necessarily-commutative `A`-algebra forming a scalar
tower `R → A → B` (for instance `B = Module.End A S` for an `A`-module `S`, with `R = ℝ` and
`A = ℂ`). Composing Mathlib's scalar-extension adjunction `AlgHom.liftEquiv` with the canonical
isomorphism `CliffordAlgebra.equivBaseChange A Q : CliffordAlgebra (Q.baseChange A) ≃ₐ[A]
A ⊗[R] CliffordAlgebra Q` extends every `R`-algebra homomorphism `ρ : CliffordAlgebra Q →ₐ[R] B`
to a unique `A`-algebra homomorphism `ρ.cliffordBaseChange A : CliffordAlgebra (Q.baseChange A)
→ₐ[A] B` restricting to `ρ` along `CliffordAlgebra.ofBaseChangeAux A Q`.

On pure base-changed generators `a ⊗ₜ v ∈ A ⊗[R] V`, the extended homomorphism acts by
`a • ρ (ι Q v)`; in particular `1 ⊗ₜ v` acts by `ρ (ι Q v)`, and this property characterizes the
extension uniquely among `A`-algebra homomorphisms out of `CliffordAlgebra (Q.baseChange A)`.

## Main definitions

* `AlgHom.cliffordBaseChange`: the `A`-linear extension `CliffordAlgebra (Q.baseChange A) →ₐ[A] B`
  of `ρ : CliffordAlgebra Q →ₐ[R] B`.
* `AlgHom.cliffordBaseChangeEquiv`: the equivalence
  `(CliffordAlgebra Q →ₐ[R] B) ≃ (CliffordAlgebra (Q.baseChange A) →ₐ[A] B)` inverse to
  restriction along `CliffordAlgebra.ofBaseChangeAux A Q`.

## Main results

* `AlgHom.cliffordBaseChange_ofBaseChangeAux`, `AlgHom.comp_ofBaseChangeAux_cliffordBaseChange`:
  restricting `ρ.cliffordBaseChange A` along `ofBaseChangeAux A Q` recovers `ρ`.
* `AlgHom.cliffordBaseChange_ι_tmul`, `AlgHom.cliffordBaseChange_ι_one_tmul`: the action of
  `ρ.cliffordBaseChange A` on `ι (Q.baseChange A) (a ⊗ₜ v)` and `ι (Q.baseChange A) (1 ⊗ₜ v)`.
* `AlgHom.eq_cliffordBaseChange_iff`: an `A`-algebra homomorphism out of
  `CliffordAlgebra (Q.baseChange A)` equals `ρ.cliffordBaseChange A` if and only if it sends every
  `ι (Q.baseChange A) (1 ⊗ₜ v)` to `ρ (ι Q v)`.
* `AlgHom.cliffordBaseChange_eq_lift`: `ρ.cliffordBaseChange A` factors as
  `Algebra.TensorProduct.lift` of `Algebra.ofId A B` and `ρ` composed with
  `CliffordAlgebra.equivBaseChange A Q`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open CliffordAlgebra
open scoped TensorProduct

namespace AlgHom

variable {R V : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup V] [Module R V]
  {Q : QuadraticForm R V}

section Lift

variable (A : Type*) [CommRing A] [Algebra R A]
  {B : Type*} [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Extend an `R`-algebra homomorphism `ρ : CliffordAlgebra Q →ₐ[R] B` into an `A`-algebra `B`
along `CliffordAlgebra.toBaseChange A Q` to an `A`-algebra homomorphism out of
`CliffordAlgebra (Q.baseChange A)`. -/
noncomputable def cliffordBaseChange (ρ : CliffordAlgebra Q →ₐ[R] B) :
    CliffordAlgebra (Q.baseChange A) →ₐ[A] B :=
  (ρ.liftEquiv R A (CliffordAlgebra Q) B).comp (CliffordAlgebra.toBaseChange A Q)

variable {A}

/-- Evaluating `ρ.cliffordBaseChange A` after `CliffordAlgebra.ofBaseChange A Q` recovers the
tensor-product scalar extension `AlgHom.liftEquiv`. -/
@[simp]
theorem cliffordBaseChange_ofBaseChange (ρ : CliffordAlgebra Q →ₐ[R] B)
    (x : A ⊗[R] CliffordAlgebra Q) :
    ρ.cliffordBaseChange A (ofBaseChange A Q x) = ρ.liftEquiv R A (CliffordAlgebra Q) B x := by
  simp [cliffordBaseChange]

/-- On a pure tensor `a ⊗ₜ x`, `ρ.cliffordBaseChange A ∘ ofBaseChange A Q` acts by `a • ρ x`. -/
theorem cliffordBaseChange_ofBaseChange_tmul (ρ : CliffordAlgebra Q →ₐ[R] B) (a : A)
    (x : CliffordAlgebra Q) :
    ρ.cliffordBaseChange A (ofBaseChange A Q (a ⊗ₜ x)) = a • ρ x := by
  simp [cliffordBaseChange]

/-- On a pure base-changed vector `a ⊗ₜ v`, `ρ.cliffordBaseChange A` acts by `a • ρ (ι Q v)`. -/
@[simp]
theorem cliffordBaseChange_ι_tmul (ρ : CliffordAlgebra Q →ₐ[R] B) (a : A) (v : V) :
    ρ.cliffordBaseChange A (ι (Q.baseChange A) (a ⊗ₜ v)) = a • ρ (ι Q v) := by
  simp [cliffordBaseChange]

/-- On an embedded vector `1 ⊗ₜ v`, `ρ.cliffordBaseChange A` agrees with `ρ` on `ι Q v`. -/
theorem cliffordBaseChange_ι_one_tmul (ρ : CliffordAlgebra Q →ₐ[R] B) (v : V) :
    ρ.cliffordBaseChange A (ι (Q.baseChange A) (1 ⊗ₜ v)) = ρ (ι Q v) := by
  rw [cliffordBaseChange_ι_tmul, one_smul]

/-- Restricting `ρ.cliffordBaseChange A` to `R` and precomposing with
`CliffordAlgebra.ofBaseChangeAux A Q` recovers `ρ`. -/
@[simp]
theorem comp_ofBaseChangeAux_cliffordBaseChange (ρ : CliffordAlgebra Q →ₐ[R] B) :
    ((ρ.cliffordBaseChange A).restrictScalars R).comp (ofBaseChangeAux A Q) = ρ := by
  apply CliffordAlgebra.hom_ext
  ext v
  simp

/-- Restricting `ρ.cliffordBaseChange A` along `CliffordAlgebra.ofBaseChangeAux A Q` recovers `ρ`
pointwise. -/
@[simp]
theorem cliffordBaseChange_ofBaseChangeAux (ρ : CliffordAlgebra Q →ₐ[R] B)
    (x : CliffordAlgebra Q) :
    ρ.cliffordBaseChange A (ofBaseChangeAux A Q x) = ρ x :=
  congr($(ρ.comp_ofBaseChangeAux_cliffordBaseChange) x)

/-- Two `A`-algebra homomorphisms out of `CliffordAlgebra (Q.baseChange A)` are equal if and only
if they agree on `ι (Q.baseChange A) (1 ⊗ₜ v)` for every `v : V`. -/
theorem cliffordAlgebra_baseChange_ext_iff
    {σ₁ σ₂ : CliffordAlgebra (Q.baseChange A) →ₐ[A] B} :
    σ₁ = σ₂ ↔ ∀ v : V, σ₁ (ι (Q.baseChange A) (1 ⊗ₜ v)) = σ₂ (ι (Q.baseChange A) (1 ⊗ₜ v)) := by
  refine ⟨fun h v ↦ congr($h _), fun h ↦ CliffordAlgebra.hom_ext ?_⟩
  ext v
  simpa using h v

/-- An `A`-algebra homomorphism `σ : CliffordAlgebra (Q.baseChange A) →ₐ[A] B` equals
`ρ.cliffordBaseChange A` if and only if it maps every `ι (Q.baseChange A) (1 ⊗ₜ v)` to
`ρ (ι Q v)`. -/
theorem eq_cliffordBaseChange_iff (ρ : CliffordAlgebra Q →ₐ[R] B)
    {σ : CliffordAlgebra (Q.baseChange A) →ₐ[A] B} :
    σ = ρ.cliffordBaseChange A ↔ ∀ v : V, σ (ι (Q.baseChange A) (1 ⊗ₜ v)) = ρ (ι Q v) := by
  rw [cliffordAlgebra_baseChange_ext_iff]
  simp

/-- `ρ.cliffordBaseChange A` is `Algebra.TensorProduct.lift` of `Algebra.ofId A B` and `ρ`,
precomposed with `CliffordAlgebra.equivBaseChange A Q`. -/
theorem cliffordBaseChange_eq_lift (ρ : CliffordAlgebra Q →ₐ[R] B) :
    ρ.cliffordBaseChange A =
      (Algebra.TensorProduct.lift (Algebra.ofId A B) ρ
        (fun a x ↦ by rw [Algebra.ofId_apply]; exact Algebra.commutes a (ρ x))).comp
        (CliffordAlgebra.equivBaseChange A Q).toAlgHom := by
  symm
  rw [eq_cliffordBaseChange_iff]
  intro v
  simp [equivBaseChange]

end Lift

section Equiv

/-- Scalar extension of Clifford algebra homomorphisms as an equivalence
`(CliffordAlgebra Q →ₐ[R] B) ≃ (CliffordAlgebra (Q.baseChange A) →ₐ[A] B)`, with inverse given by
restriction along `CliffordAlgebra.ofBaseChangeAux A Q`. -/
noncomputable def cliffordBaseChangeEquiv (A : Type*) [CommRing A] [Algebra R A]
    (Q : QuadraticForm R V) (B : Type*) [Semiring B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] :
    (CliffordAlgebra Q →ₐ[R] B) ≃ (CliffordAlgebra (Q.baseChange A) →ₐ[A] B) where
  toFun := cliffordBaseChange A
  invFun σ := (σ.restrictScalars R).comp (ofBaseChangeAux A Q)
  left_inv := comp_ofBaseChangeAux_cliffordBaseChange
  right_inv σ := ((eq_cliffordBaseChange_iff _).2 fun v ↦ by simp).symm

variable {A : Type*} [CommRing A] [Algebra R A]
  {B : Type*} [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Applying `AlgHom.cliffordBaseChangeEquiv` computes `AlgHom.cliffordBaseChange`. -/
@[simp]
theorem cliffordBaseChangeEquiv_apply (ρ : CliffordAlgebra Q →ₐ[R] B) :
    cliffordBaseChangeEquiv A Q B ρ = ρ.cliffordBaseChange A :=
  (rfl)

/-- The inverse of `AlgHom.cliffordBaseChangeEquiv` restricts scalars to `R` and precomposes with
`CliffordAlgebra.ofBaseChangeAux A Q`. -/
@[simp]
theorem cliffordBaseChangeEquiv_symm_apply (σ : CliffordAlgebra (Q.baseChange A) →ₐ[A] B) :
    (cliffordBaseChangeEquiv A Q B).symm σ = (σ.restrictScalars R).comp (ofBaseChangeAux A Q) :=
  (rfl)

/-- Extending the restriction `(σ.restrictScalars R).comp (ofBaseChangeAux A Q)` of an `A`-algebra
map `σ` out of `CliffordAlgebra (Q.baseChange A)` recovers `σ`. -/
@[simp]
theorem cliffordBaseChange_comp_ofBaseChangeAux (σ : CliffordAlgebra (Q.baseChange A) →ₐ[A] B) :
    ((σ.restrictScalars R).comp (ofBaseChangeAux A Q)).cliffordBaseChange A = σ :=
  (cliffordBaseChangeEquiv A Q B).right_inv σ

end Equiv

section Functoriality

variable (A : Type*) [CommRing A] [Algebra R A]
  {B C : Type*} [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Semiring C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]

/-- Scalar extension of Clifford algebra homomorphisms commutes with postcomposition by an
`A`-algebra homomorphism. -/
theorem comp_cliffordBaseChange (ψ : B →ₐ[A] C) (ρ : CliffordAlgebra Q →ₐ[R] B) :
    ψ.comp (ρ.cliffordBaseChange A) = ((ψ.restrictScalars R).comp ρ).cliffordBaseChange A := by
  rw [eq_cliffordBaseChange_iff]
  intro v
  simp

/-- Scalar extension of Clifford algebra homomorphisms commutes with pullback along an isometry of
quadratic forms. -/
theorem cliffordBaseChange_comp_map {V' : Type*} [AddCommGroup V'] [Module R V']
    {Q' : QuadraticForm R V'} (f : Q' →qᵢ Q) (ρ : CliffordAlgebra Q →ₐ[R] B) :
    (ρ.comp (CliffordAlgebra.map f)).cliffordBaseChange A =
      (ρ.cliffordBaseChange A).comp
        (CliffordAlgebra.map (QuadraticMap.Isometry.baseChange f A)) := by
  symm
  rw [eq_cliffordBaseChange_iff]
  intro v
  simp

end Functoriality

end AlgHom
