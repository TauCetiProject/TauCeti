/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.LinearAlgebra.Matrix.Basis
public import TauCeti.Topology.Algebra.Module.Matrix
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.Decay

/-!
# Finite characters on the unit torus

Let `X` be a lattice, that is, a free abelian group with a finite basis `b : Basis d ℤ X`. A
finite character is an element `f = ∑_μ m_μ e^μ` of the group algebra `R[X]`, such as the formal
character of a finite-dimensional representation, whose coefficient `m_μ` is the multiplicity
of the weight `μ`. The basis identifies `X` with `ℤ^d`, and so the weight `μ` with the Fourier
monomial `mFourier (b.repr μ)` on the unit torus `UnitAddTorus d = (ℝ / ℤ)^d`. Sending
`e^μ` to it turns a finite character into the continuous function

`χ_f(θ) = ∑_μ m_μ exp (2πi ⟨b.repr μ, θ⟩)`

on the torus (`Module.Basis.torusEval_coe_apply`). This is `Module.Basis.torusEval`, an
algebra homomorphism: addition and multiplication of finite characters become pointwise
addition and multiplication of functions, and the zero weight becomes the constant function
`1`. Its values are continuous at every point of the torus, being finite sums of continuous
monomials.

By orthonormality of the monomials, the `n`-th Fourier coefficient of `χ_f` is the image in `ℂ`
of the multiplicity of the weight with coordinates `n` (`Module.Basis.mFourierCoeff_torusEval`).
So when `algebraMap R ℂ` is injective, for instance for `R = ℤ`, a finite character is recovered
from its function on the torus (`Module.Basis.torusEval_injective`).
Changing the lattice basis composes this function with the map of tori induced by the transpose
of the change-of-basis matrix (`Module.Basis.torusEval_eq_comp_smulVecHom`); since each basis reads
off the multiplicity of `μ` at the coordinates of `μ`, the Fourier coefficients of a weight do
not depend on the basis.

## Main definitions

* `Module.Basis.torusEval`: the evaluation of finite characters on the unit torus.

## Main results

* `Module.Basis.torusEval_single`: `e^μ` evaluates to the monomial at the coordinates of `μ`.
* `Module.Basis.mFourierCoeff_torusEval`: the Fourier coefficients of `χ_f` are the images in
  `ℂ` of the coefficients of `f`.
* `Module.Basis.torusEval_eq_comp_smulVecHom`: the change of lattice basis.
-/

public section

noncomputable section

open UnitAddTorus Complex Real

namespace Module.Basis

variable {d d' X R : Type*} [Fintype d] [Fintype d'] [AddCommGroup X]
  [CommSemiring R] [Algebra R ℂ]

/-- The Fourier monomials indexed by the coordinates in the basis `b`, as a monoid homomorphism
from `Multiplicative X`. -/
private def torusMonoidHom (b : Basis d ℤ X) : Multiplicative X →* C(UnitAddTorus d, ℂ) where
  toFun μ := mFourier (b.repr μ.toAdd)
  map_one' := by simp [mFourier_zero]
  map_mul' μ ν := by
    ext
    simp [mFourier_add]

/-- The evaluation of finite characters on the unit torus: for a lattice basis
`b : Basis d ℤ X`, the algebra homomorphism `R[X] → C((ℝ / ℤ)^d, ℂ)` sending `e^μ` to the
Fourier monomial `mFourier (b.repr μ)`, so that `∑_μ m_μ e^μ` becomes the function
`θ ↦ ∑_μ m_μ exp (2πi ⟨b.repr μ, θ⟩)`. -/
def torusEval (b : Basis d ℤ X) : AddMonoidAlgebra R X →ₐ[R] C(UnitAddTorus d, ℂ) :=
  AddMonoidAlgebra.lift R C(UnitAddTorus d, ℂ) X b.torusMonoidHom

/-- The weight `μ` with coefficient `r` evaluates to `r` times the Fourier monomial at the
coordinates of `μ`. -/
@[simp]
theorem torusEval_single (b : Basis d ℤ X) (μ : X) (r : R) :
    b.torusEval (AddMonoidAlgebra.single μ r) = r • mFourier (b.repr μ) := by
  simp [torusEval, torusMonoidHom]

/-- The value of the evaluation of `f = ∑_μ m_μ e^μ` at a point `z` of the torus is
`∑_μ m_μ mFourier (b.repr μ) z`. -/
theorem torusEval_apply (b : Basis d ℤ X) (f : AddMonoidAlgebra R X) (z : UnitAddTorus d) :
    b.torusEval f z = f.coeff.sum fun μ r ↦ algebraMap R ℂ r * mFourier (b.repr μ) z := by
  simp [torusEval, torusMonoidHom, AddMonoidAlgebra.lift_apply, Finsupp.sum, Algebra.smul_def]

/-- **The finite character on the torus.** At the image of `x : d → ℝ`, the evaluation of
`f = ∑_μ m_μ e^μ` is `∑_μ m_μ exp (2πi ∑ i, (b.repr μ i) * x i)`. -/
theorem torusEval_coe_apply (b : Basis d ℤ X) (f : AddMonoidAlgebra R X) (x : d → ℝ) :
    b.torusEval f (fun i ↦ (x i : UnitAddCircle)) = f.coeff.sum fun μ r ↦
      algebraMap R ℂ r * cexp (2 * π * I * ∑ i, (b.repr μ i : ℂ) * x i) := by
  simp [torusEval_apply, TauCeti.UnitAddTorus.mFourier_coe_apply]

/-- The Fourier coefficient of the evaluation of `f` at the coordinates of a weight `μ` is the
image in `ℂ` of the multiplicity of `μ` in `f`, whichever lattice basis is used. -/
@[simp↓ high]
theorem mFourierCoeff_torusEval_repr (b : Basis d ℤ X) (f : AddMonoidAlgebra R X) (μ : X) :
    mFourierCoeff (b.torusEval f) (b.repr μ) = algebraMap R ℂ (f.coeff μ) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp [mFourierCoeff]
  | add f g hf hg =>
    simp [mFourierCoeff_add ((b.torusEval f).continuous.integrable_of_hasCompactSupport
      (.of_compactSpace _)) ((b.torusEval g).continuous.integrable_of_hasCompactSupport
      (.of_compactSpace _)), hf, hg]
  | single ν r =>
    rw [torusEval_single, ← algebraMap_smul ℂ r (mFourier _), ContinuousMap.coe_smul,
      mFourierCoeff_smul, TauCeti.UnitAddTorus.mFourierCoeff_mFourier]
    by_cases h : ν = μ
    · subst h
      simp
    · simp [h, b.repr.injective.ne h]

/-- **Fourier coefficients of a finite character.** The `n`-th Fourier coefficient of the
evaluation of `f` on the torus is the image in `ℂ` of the coefficient of `f` at the weight with
coordinates `n`. -/
@[simp↓]
theorem mFourierCoeff_torusEval (b : Basis d ℤ X) (f : AddMonoidAlgebra R X) (n : d → ℤ) :
    mFourierCoeff (b.torusEval f) n = algebraMap R ℂ (f.coeff (b.equivFun.symm n)) := by
  rw [← b.equivFun.apply_symm_apply n, equivFun_apply, mFourierCoeff_torusEval_repr,
    ← equivFun_apply, LinearEquiv.symm_apply_apply]

/-- A finite character is determined by its function on the torus, when the coefficient ring
embeds in `ℂ`. -/
theorem torusEval_injective (b : Basis d ℤ X) (hR : Function.Injective (algebraMap R ℂ)) :
    Function.Injective (b.torusEval (R := R)) := fun f g h ↦ by
  ext μ
  apply hR
  rw [← mFourierCoeff_torusEval_repr b f μ, h, mFourierCoeff_torusEval_repr]

/-- **Change of lattice basis.** Evaluating a finite character with the basis `b'` is evaluating
it with the basis `b` and composing with the map of tori induced by the transpose of the
change-of-basis matrix `b'.toMatrix b`. -/
theorem torusEval_eq_comp_smulVecHom (b : Basis d ℤ X) (b' : Basis d' ℤ X)
    (f : AddMonoidAlgebra R X) :
    b'.torusEval f = (b.torusEval f).comp
      ((b'.toMatrix b).transpose.smulVecHom UnitAddCircle :
        C(UnitAddTorus d', UnitAddTorus d)) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single μ r => simp [toMatrix_mulVec_repr]

end Module.Basis
