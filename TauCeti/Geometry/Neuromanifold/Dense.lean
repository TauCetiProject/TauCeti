/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import TauCeti.Geometry.Neuromanifold.Composition

/-!
# Dense layers

A dense affine layer with finite input index type `ι` and output index type `ο` has as
parameters a weight matrix `A : Matrix ο ι R` and a bias vector `b : ο → R`, and realizes
`x ↦ A *ᵥ x + b`. Setting the bias to zero recovers the bias-free (linear) layer, which as
a realization map is Mathlib's `Matrix.mulVec` itself.

For presenting these layers with parameters indexed by a single type, `linearParameterEquiv`
identifies `ο × ι → R` with the weight matrices and `denseParameterEquiv` identifies
`ο × ι ⊕ ο → R` with the weight-bias pairs.

As a first application of `compose`, two bias-free dense layers with identity activation
realize `x ↦ (B * A) *ᵥ x`, so their neuromanifold is the image of the matrix products
`B * A` under matrix evaluation. The parameter space is the full product of the two weight
spaces; no claim is made that distinct weight pairs realize distinct functions.

This is the two-layer linear network of Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), Appendix A.
-/

public section

namespace TauCeti.Neuromanifold

open Matrix

variable {R : Type*} {ι κ ο : Type*}

section ParameterEquiv

/-- The parameters of a linear layer, indexed by matrix positions, form its weight matrix. -/
def linearParameterEquiv (R ο ι : Type*) : (ο × ι → R) ≃ Matrix ο ι R :=
  (Equiv.curry ο ι R).trans Matrix.of

/-- The weight matrix read off from linear-layer parameters. -/
@[simp] theorem linearParameterEquiv_apply (p : ο × ι → R) (o : ο) (i : ι) :
    linearParameterEquiv R ο ι p o i = p (o, i) := (rfl)

/-- Linear-layer parameters read off from a weight matrix. -/
@[simp] theorem linearParameterEquiv_symm_apply (A : Matrix ο ι R) (q : ο × ι) :
    (linearParameterEquiv R ο ι).symm A q = A q.1 q.2 := (rfl)

/-- The parameters of a dense affine layer, indexed by matrix positions and then by output
coordinates, form its weight matrix and bias vector. -/
def denseParameterEquiv (R ο ι : Type*) : (ο × ι ⊕ ο → R) ≃ Matrix ο ι R × (ο → R) :=
  (Equiv.sumArrowEquivProdArrow (ο × ι) ο R).trans
    ((linearParameterEquiv R ο ι).prodCongr (Equiv.refl _))

/-- The weight matrix read off from dense-layer parameters. -/
@[simp] theorem denseParameterEquiv_apply_fst (p : ο × ι ⊕ ο → R) (o : ο) (i : ι) :
    (denseParameterEquiv R ο ι p).1 o i = p (Sum.inl (o, i)) := (rfl)

/-- The bias vector read off from dense-layer parameters. -/
@[simp] theorem denseParameterEquiv_apply_snd (p : ο × ι ⊕ ο → R) (o : ο) :
    (denseParameterEquiv R ο ι p).2 o = p (Sum.inr o) := (rfl)

/-- Dense-layer parameters at a matrix position are the corresponding weight. -/
@[simp] theorem denseParameterEquiv_symm_apply_inl (p : Matrix ο ι R × (ο → R)) (q : ο × ι) :
    (denseParameterEquiv R ο ι).symm p (Sum.inl q) = p.1 q.1 q.2 := (rfl)

/-- Dense-layer parameters at an output coordinate are the corresponding bias. -/
@[simp] theorem denseParameterEquiv_symm_apply_inr (p : Matrix ο ι R × (ο → R)) (o : ο) :
    (denseParameterEquiv R ο ι).symm p (Sum.inr o) = p.2 o := (rfl)

end ParameterEquiv

section Dense

variable [NonUnitalNonAssocSemiring R] [Fintype ι]

/-- The dense affine layer: the parameters `(A, b)` realize `x ↦ A *ᵥ x + b`. -/
def dense : Matrix ο ι R × (ο → R) → (ι → R) → ο → R := fun p x => p.1 *ᵥ x + p.2

/-- A dense layer applies its weight matrix and adds its bias. -/
@[simp] theorem dense_apply (p : Matrix ο ι R × (ο → R)) (x : ι → R) :
    dense p x = p.1 *ᵥ x + p.2 := (rfl)

/-- The coordinate formula for a dense layer. -/
theorem dense_apply_apply (A : Matrix ο ι R) (b : ο → R) (x : ι → R) (i : ο) :
    dense (A, b) x i = ∑ j, A i j * x j + b i := by
  simp [mulVec, dotProduct]

/-- A dense layer with zero bias is the linear layer `Matrix.mulVec`. -/
@[simp] theorem dense_mk_zero (A : Matrix ο ι R) : dense (A, 0) = A.mulVec := by
  funext x
  simp

end Dense

section TwoLayer

variable [NonUnitalSemiring R] [Fintype ι] [Fintype κ]

/-- Two bias-free dense layers with identity activation realize the product of their
weight matrices. -/
theorem compose_mulVec_mulVec (A : Matrix κ ι R) (B : Matrix ο κ R) :
    compose Matrix.mulVec Matrix.mulVec (A, B) = (B * A).mulVec := by
  funext x
  simp [mulVec_mulVec]

/-- The neuromanifold of two bias-free dense layers with identity activation is the image
under matrix evaluation of the products `B * A` of their weight matrices. -/
theorem realizedFunctions_compose_mulVec_mulVec :
    realizedFunctions (compose (Matrix.mulVec : Matrix κ ι R → (ι → R) → κ → R)
        (Matrix.mulVec : Matrix ο κ R → (κ → R) → ο → R)) =
      Matrix.mulVec '' Set.range fun p : Matrix κ ι R × Matrix ο κ R => p.2 * p.1 := by
  rw [realizedFunctions_def, ← Set.range_comp]
  congr 1
  funext p
  exact compose_mulVec_mulVec p.1 p.2

end TwoLayer

end TauCeti.Neuromanifold
