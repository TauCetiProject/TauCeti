/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# The Dirac operator of a connection and a Clifford multiplication

Let `V` be a vector bundle over a Riemannian manifold `M`, with a connection `∇` and a
*Clifford multiplication* `c`, a family of linear maps `c x : T_x M → End (V x)`. The
**Dirac operator** of `(∇, c)` sends a section `σ` to the metric contraction of the bilinear map
`(u, w) ↦ c(u) (∇_w σ)`,

`D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ`,

for any orthonormal basis `eᵢ` of the tangent space (`CovariantDerivative.diracOperator_eq_sum`).
The contraction is against the canonical covariant tensor
`InnerProductSpace.canonicalCovariantTensor`, so the definition involves no choice of frame.

When `V` is a Hermitian Clifford module, so that `c(v)² = -‖v‖²` and each `c(v)` is
skew-adjoint, and `∇` is compatible with `c` and the Levi-Civita connection, this is the Dirac
operator of the Clifford module. For the spinor bundle of a `Spinᶜ` structure on a
four-manifold and the spin connection `∇_A` of a unitary connection `A` on its determinant line,
its restriction to the positive spinors is the Dirac operator `D_A` of the Seiberg–Witten
equations. None of these hypotheses is used by the first-order calculus of this file:

* `D` is additive on differentiable sections and commutes with constants
  (`diracOperator_add`, `diracOperator_const_smul`).
* **Leibniz rule.** For a differentiable function `f`,
  `D (f σ) = f D σ + c(grad f) σ` (`diracOperator_smul`). So the commutator of `D` with
  multiplication by `f` is the operator of order zero `c(grad f)`: the principal symbol of `D`
  at a covector `ξ` is Clifford multiplication by its metric dual `ξ♯`, in the geometric
  convention.
* **Naturality.** If `∇' τ = g ∘ ∇ σ` at `x` for an endomorphism `g` commuting with Clifford
  multiplication, then `D' τ = g (D σ)` (`diracOperator_eq_apply_of_eq_comp`); this is the gauge
  covariance of `D`.
* **Change of connection.** Adding to `∇` a one-form `A` with values in the endomorphisms of `V`
  adds the term of order zero `∑ᵢ c(eᵢ) A(eᵢ)` to `D` (`diracOperator_addOneForm`). When
  `A(w) = θ(w) L` for a real one-form `θ` and an endomorphism `L`, this term is `c(θ♯) L`
  (`diracOperator_addOneForm_of_forall_apply_eq`). For the spin connection of `A + a`, with `a`
  an imaginary one-form on the determinant line, `∇_{A + a} = ∇_A + a / 2`, so this is the law
  `D_{A + a} = D_A + c(a) / 2`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, §5 (Dirac operators of Clifford bundles).
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific,
  Definition 12.1.64 and Proposition 12.1.65.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Princeton University Press, 1996, §3.1.
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V]
  (cov : _root_.CovariantDerivative I F V)
  (c : Π x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x)
  {σ τ : Π y : M, V y}

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The **Dirac operator** `D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ` of a connection `∇` and a Clifford
multiplication `c` at `x`: the metric contraction of the bilinear map `(u, w) ↦ c(u) (∇_w σ)`
on the tangent space. In an orthonormal basis it is the sum `∑ᵢ c(eᵢ) ∇_{eᵢ} σ`
(`diracOperator_eq_sum`). -/
def diracOperator (σ : Π y : M, V y) (x : M) : V x :=
  TensorProduct.lift.equiv (.id ℝ) (TangentSpace I x) (TangentSpace I x) (V x)
    (LinearMap.mk₂ ℝ (fun u w ↦ c x u (cov σ x w))
      (fun u u' w ↦ by simp only [map_add, add_apply])
      (fun a u w ↦ by simp only [map_smul, smul_apply])
      (fun u w w' ↦ by simp only [map_add])
      (fun a u w ↦ by simp only [map_smul]))
    (InnerProductSpace.canonicalCovariantTensor (TangentSpace I x))

/-- **The Dirac operator in an orthonormal frame.** For every orthonormal basis `eᵢ` of the
tangent space at `x`, `D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ`. In particular the sum does not depend on the
basis. -/
theorem diracOperator_eq_sum (σ : Π y : M, V y) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.diracOperator c σ x = ∑ i, c x (b i) (cov σ x (b i)) := by
  rw [diracOperator, InnerProductSpace.canonicalCovariantTensor_eq_sum _ b, map_sum]
  simp only [TensorProduct.lift.equiv_apply, LinearMap.mk₂_apply]

/-- The Dirac operator of a section whose covariant derivative vanishes at `x` vanishes at `x`.
In particular `D 0 = 0`. -/
theorem diracOperator_eq_zero_of_eq_zero (x : M) (hσ : cov σ x = 0) :
    cov.diracOperator c σ x = 0 := by
  simp [diracOperator_eq_sum cov c σ x (stdOrthonormalBasis ℝ (TangentSpace I x)), hσ]

/-- The Dirac operator of the zero section is zero. -/
@[simp]
theorem diracOperator_zero [VectorBundle ℝ F V] (x : M) :
    cov.diracOperator c (0 : Π y : M, V y) x = 0 :=
  cov.diracOperator_eq_zero_of_eq_zero c x (by simp)

/-- The Dirac operator is additive on sections differentiable at the point. -/
theorem diracOperator_add {x : M} (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    cov.diracOperator c (σ + τ) x = cov.diracOperator c σ x + cov.diracOperator c τ x := by
  simp only [diracOperator_eq_sum cov c _ x (stdOrthonormalBasis ℝ (TangentSpace I x)),
    cov.isCovariantDerivativeOnUniv.add hσ hτ, add_apply, map_add,
    Finset.sum_add_distrib]

/-- The Dirac operator commutes with multiplication of a differentiable section by a
constant. -/
theorem diracOperator_const_smul {x : M} (a : ℝ) (hσ : MDiffAt (T% σ) x) :
    cov.diracOperator c (a • σ) x = a • cov.diracOperator c σ x := by
  simp only [diracOperator_eq_sum cov c _ x (stdOrthonormalBasis ℝ (TangentSpace I x)),
    cov.isCovariantDerivativeOnUniv.smul_const a hσ, smul_apply, map_smul,
    Finset.smul_sum]

/-- The Dirac operator commutes with negation of a differentiable section. -/
theorem diracOperator_neg {x : M} (hσ : MDiffAt (T% σ) x) :
    cov.diracOperator c (-σ) x = -cov.diracOperator c σ x := by
  rw [← neg_one_smul ℝ σ, cov.diracOperator_const_smul c (-1) hσ, neg_one_smul]

/-- The Dirac operator commutes with differences of differentiable sections. -/
theorem diracOperator_sub [VectorBundle ℝ F V] {x : M} (hσ : MDiffAt (T% σ) x)
    (hτ : MDiffAt (T% τ) x) :
    cov.diracOperator c (σ - τ) x = cov.diracOperator c σ x - cov.diracOperator c τ x := by
  rw [sub_eq_add_neg, cov.diracOperator_add c hσ (mdifferentiableAt_neg_section hτ),
    cov.diracOperator_neg c hτ, sub_eq_add_neg]

/-- **Naturality of the Dirac operator.** Let `g` be an endomorphism of the fibre at `x` which
commutes with Clifford multiplication. If a second connection `∇'` differentiates `τ` at `x` as
`g` applied to the covariant derivative of `σ`, `∇' τ = g ∘ ∇ σ`, then `D' τ = g (D σ)` at `x`.
For a gauge transformation `u` commuting with `c` and the transformed connection
`∇^u = u ∘ ∇ ∘ u⁻¹`, applied to `τ = u σ`, this is the gauge covariance
`D_{∇^u} (u σ) = u (D_∇ σ)`. -/
theorem diracOperator_eq_apply_of_eq_comp (cov' : _root_.CovariantDerivative I F V) {x : M}
    (g : V x →L[ℝ] V x) (hg : ∀ v, g ∘L c x v = c x v ∘L g) (h : cov' τ x = g ∘L cov σ x) :
    cov'.diracOperator c τ x = g (cov.diracOperator c σ x) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [diracOperator_eq_sum cov' c τ x b, diracOperator_eq_sum cov c σ x b, h, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact (DFunLike.congr_fun (hg (b i)) (cov σ x (b i))).symm

variable [IsManifold I 1 M]

/-- **The Leibniz rule for the Dirac operator.** For a function `f` and a section `σ`, both
differentiable at `x`, `D (f σ) = f D σ + c(grad f) σ`. Thus the commutator of `D` with
multiplication by `f` is Clifford multiplication by the gradient of `f`. -/
theorem diracOperator_smul {f : M → ℝ} {x : M} (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) :
    cov.diracOperator c (f • σ) x =
      f x • cov.diracOperator c σ x + c x (TauCeti.Manifold.mgradient I f x) (σ x) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [TauCeti.Manifold.mgradient_def, Riemannian.Tensor.rieszDual_eq_sum _ b,
    diracOperator_eq_sum cov c _ x b, diracOperator_eq_sum cov c _ x b,
    cov.isCovariantDerivativeOnUniv.leibniz hσ hf]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
    map_sum, FunLike.coe_sum, Finset.sum_apply, Finset.sum_add_distrib, Finset.smul_sum]

omit [IsManifold I 1 M] in
/-- **Change of connection.** Adding to `∇` a one-form `A` with values in the endomorphisms of
`V` adds `∑ᵢ c(eᵢ) A(eᵢ) σ` to the Dirac operator, for every orthonormal basis `eᵢ` of the
tangent space at `x`. -/
theorem diracOperator_addOneForm (A : Π y : M, V y →L[ℝ] TangentSpace I y →L[ℝ] V y)
    (σ : Π y : M, V y) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    (cov.addOneForm A).diracOperator c σ x =
      cov.diracOperator c σ x + ∑ i, c x (b i) (A x (σ x) (b i)) := by
  rw [diracOperator_eq_sum _ c σ x b, diracOperator_eq_sum cov c σ x b, addOneForm_apply]
  simp only [add_apply, map_add, Finset.sum_add_distrib]

/-- **Change of connection by a scalar one-form.** If the endomorphism-valued one-form `A` is
`A(w) = θ(w) L` at `x`, for a real covector `θ` and an endomorphism `L` of the fibre, then adding
`A` to `∇` adds `c(θ♯) L σ` to the Dirac operator at `x`, where `θ♯` is the metric dual of `θ`.
For the spin connection of a unitary connection on the determinant line, changing the connection
by an imaginary one-form `a = i θ` changes the spin connection by `a / 2`, that is `L = i / 2`,
and this is the law `D_{A + a} = D_A + c(a) / 2`. -/
theorem diracOperator_addOneForm_of_forall_apply_eq
    (A : Π y : M, V y →L[ℝ] TangentSpace I y →L[ℝ] V y) (σ : Π y : M, V y) {x : M}
    (θ : TangentSpace I x →L[ℝ] ℝ) (L : V x →L[ℝ] V x) (hA : ∀ s w, A x s w = θ w • L s) :
    (cov.addOneForm A).diracOperator c σ x =
      cov.diracOperator c σ x + c x (Riemannian.Tensor.rieszDual x θ) (L (σ x)) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [cov.diracOperator_addOneForm c A σ x b, Riemannian.Tensor.rieszDual_eq_sum θ b]
  simp only [hA, map_smul, map_sum, FunLike.coe_sum, Finset.sum_apply, smul_apply]

end CovariantDerivative
