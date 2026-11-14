/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.LinearAlgebra.Matrix.Basis
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.Decay
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus

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

By orthonormality of the monomials, the `n`-th Fourier coefficient of `χ_f` is the multiplicity
of the weight with coordinates `n` (`Module.Basis.mFourierCoeff_torusEval`), so a finite
character is recovered from its function on the torus (`Module.Basis.torusEval_injective`).
Changing the lattice basis composes this function with the map of tori dual to the
change-of-basis matrix (`Module.Basis.torusEval_eq_comp_dualTorusMap`); since each basis reads
off the multiplicity of `μ` at the coordinates of `μ`, the Fourier coefficients of a weight do
not depend on the basis.

## Main definitions

* `Matrix.dualTorusMap`: for an integer matrix `M : Matrix d' d ℤ`, the continuous map
  `(ℝ / ℤ)^d' → (ℝ / ℤ)^d` dual to `M *ᵥ · : ℤ^d → ℤ^d'`.
* `Module.Basis.torusEval`: the evaluation of finite characters on the unit torus.

## Main results

* `Matrix.mFourier_comp_dualTorusMap`: `mFourier n ∘ M.dualTorusMap = mFourier (M *ᵥ n)`.
* `Module.Basis.torusEval_single`: `e^μ` evaluates to the monomial at the coordinates of `μ`.
* `Module.Basis.mFourierCoeff_torusEval`: the Fourier coefficients of `χ_f` are the
  coefficients of `f`.
* `Module.Basis.torusEval_eq_comp_dualTorusMap`: the change of lattice basis.
-/

public section

noncomputable section

open UnitAddTorus Complex Real

namespace Matrix

variable {d d' d'' : Type*} [Fintype d']

/-- The continuous map of unit tori `(ℝ / ℤ)^d' → (ℝ / ℤ)^d` dual to the homomorphism
`n ↦ M *ᵥ n` from `ℤ^d` to `ℤ^d'`: it sends `θ` to `i ↦ ∑ j, M j i • θ j`, so that
`mFourier n ∘ M.dualTorusMap = mFourier (M *ᵥ n)` (`Matrix.mFourier_comp_dualTorusMap`). -/
def dualTorusMap (M : Matrix d' d ℤ) : C(UnitAddTorus d', UnitAddTorus d) where
  toFun θ i := ∑ j, M j i • θ j
  continuous_toFun := by fun_prop

/-- The `i`-th coordinate of the dual torus map is `∑ j, M j i • θ j`. -/
@[simp]
theorem dualTorusMap_apply (M : Matrix d' d ℤ) (θ : UnitAddTorus d') (i : d) :
    M.dualTorusMap θ i = ∑ j, M j i • θ j :=
  (rfl)

/-- On the image of `x : d' → ℝ`, the dual torus map is reduction modulo one of
`i ↦ ∑ j, M j i * x j`. -/
theorem dualTorusMap_coe (M : Matrix d' d ℤ) (x : d' → ℝ) :
    M.dualTorusMap (fun j ↦ (x j : UnitAddCircle)) =
      fun i ↦ ((∑ j, (M j i : ℝ) * x j : ℝ) : UnitAddCircle) := by
  ext i
  simp_rw [dualTorusMap_apply, ← zsmul_eq_mul]
  rw [← QuotientAddGroup.mk'_apply, map_sum]
  simp

/-- The identity matrix induces the identity map of the torus. -/
@[simp]
theorem dualTorusMap_one [DecidableEq d'] :
    (1 : Matrix d' d' ℤ).dualTorusMap = ContinuousMap.id _ := by
  ext θ i
  simp [Matrix.one_apply]

/-- The dual torus map reverses products of matrices. -/
theorem dualTorusMap_mul [Fintype d''] (N : Matrix d'' d' ℤ) (M : Matrix d' d ℤ) :
    (N * M).dualTorusMap = M.dualTorusMap.comp N.dualTorusMap := by
  ext θ i
  simp only [dualTorusMap_apply, ContinuousMap.comp_apply, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by rw [mul_comm]

/-- The Fourier monomial `mFourier n` pulled back along the dual torus map of `M` is the
monomial `mFourier (M *ᵥ n)`. -/
theorem mFourier_comp_dualTorusMap [Fintype d] (M : Matrix d' d ℤ) (n : d → ℤ) :
    (mFourier n).comp M.dualTorusMap = mFourier (M *ᵥ n) := by
  ext θ
  obtain ⟨x, rfl⟩ := TauCeti.UnitAddTorus.surjective_coe θ
  simp only [ContinuousMap.comp_apply, dualTorusMap_coe, TauCeti.UnitAddTorus.mFourier_coe_apply]
  congr 2
  simp only [mulVec, dotProduct]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring

end Matrix

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

/-- **Fourier coefficients of a finite character.** The `n`-th Fourier coefficient of the
evaluation of `f` on the torus is the coefficient of `f` at the weight with coordinates `n`. -/
theorem mFourierCoeff_torusEval (b : Basis d ℤ X) (f : AddMonoidAlgebra R X) (n : d → ℤ) :
    mFourierCoeff (b.torusEval f) n = algebraMap R ℂ (f.coeff (b.equivFun.symm n)) := by
  classical
  have hint (μ : X) : MeasureTheory.Integrable fun z : UnitAddTorus d ↦
      mFourier (-n) z • (algebraMap R ℂ (f.coeff μ) * mFourier (b.repr μ) z) :=
    (by fun_prop : Continuous fun z : UnitAddTorus d ↦
      mFourier (-n) z • (algebraMap R ℂ (f.coeff μ) * mFourier (b.repr μ) z))
      |>.integrable_of_hasCompactSupport (.of_compactSpace _)
  have hcoeff (μ : X) : ∫ z, mFourier (-n) z • (algebraMap R ℂ (f.coeff μ) *
      mFourier (b.repr μ) z) =
        algebraMap R ℂ (f.coeff μ) * (Pi.single (⇑(b.repr μ)) 1 : (d → ℤ) → ℂ) n := by
    rw [← TauCeti.UnitAddTorus.mFourierCoeff_mFourier,
      TauCeti.UnitAddTorus.mFourierCoeff_eq_integral_volume, ← smul_eq_mul,
      ← MeasureTheory.integral_smul]
    refine MeasureTheory.integral_congr_ae (.of_forall fun z ↦ ?_)
    simp only [smul_eq_mul]
    ring
  simp_rw [TauCeti.UnitAddTorus.mFourierCoeff_eq_integral_volume, torusEval_apply, Finsupp.sum,
    Finset.smul_sum]
  rw [MeasureTheory.integral_finsetSum _ fun μ _ ↦ hint μ]
  simp_rw [hcoeff]
  rw [Finset.sum_eq_single (b.equivFun.symm n)]
  · rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one]
  · intro μ _ hμ
    rw [Pi.single_eq_of_ne fun h ↦ hμ (by rw [h, ← b.equivFun_apply, LinearEquiv.symm_apply_apply]),
      mul_zero]
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, map_zero, zero_mul]

/-- The Fourier coefficient of the evaluation of `f` at the coordinates of a weight `μ` is the
multiplicity of `μ` in `f`, whichever lattice basis is used. -/
@[simp]
theorem mFourierCoeff_torusEval_repr (b : Basis d ℤ X) (f : AddMonoidAlgebra R X) (μ : X) :
    mFourierCoeff (b.torusEval f) (b.repr μ) = algebraMap R ℂ (f.coeff μ) := by
  rw [mFourierCoeff_torusEval, ← b.equivFun_apply, LinearEquiv.symm_apply_apply]

/-- A finite character is determined by its function on the torus, when the coefficient ring
embeds in `ℂ`. -/
theorem torusEval_injective (b : Basis d ℤ X) (hR : Function.Injective (algebraMap R ℂ)) :
    Function.Injective (b.torusEval (R := R)) := fun f g h ↦ by
  ext μ
  apply hR
  rw [← mFourierCoeff_torusEval_repr b f μ, h, mFourierCoeff_torusEval_repr]

/-- **Change of lattice basis.** Evaluating a finite character with the basis `b'` is evaluating
it with the basis `b` and composing with the dual torus map of the change-of-basis matrix
`b'.toMatrix b`. -/
theorem torusEval_eq_comp_dualTorusMap (b : Basis d ℤ X) (b' : Basis d' ℤ X)
    (f : AddMonoidAlgebra R X) :
    b'.torusEval f = (b.torusEval f).comp (b'.toMatrix b).dualTorusMap := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, ContinuousMap.add_comp]
  | single μ r =>
    ext z
    rw [torusEval_single, torusEval_single, ContinuousMap.comp_apply, ContinuousMap.smul_apply,
      ContinuousMap.smul_apply, ← ContinuousMap.comp_apply (mFourier _),
      Matrix.mFourier_comp_dualTorusMap]
    congr 3
    ext i
    simp [toMatrix_mulVec_repr]

end Module.Basis
