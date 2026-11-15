/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.RealAction
public import TauCeti.LinearAlgebra.Matrix.Pauli
-- Private: existence of compatible spinor metrics on complex spinor modules is used only inside
-- the spinor-witness proof.
import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Spinor

/-!
# The geometric convention for real Clifford algebra actions on complex Hermitian modules

In Riemannian spin geometry, a complex vector space `S` equipped with an inner product is a
**Hermitian Clifford module** over a real inner product space `V` in the **geometric convention**
when it carries a real algebra homomorphism `ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S` for the
negative-definite metric form `Q v = -‖v‖²` such that Clifford multiplication `c(v) = ρ (ι Q v)` by
every real vector `v : V` is skew-Hermitian:

  `⟪c(v) x, y⟫_ℂ = -⟪x, c(v) y⟫_ℂ`.

Together these two clauses give the polarized Euclidean Clifford relation

  `c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫_ℝ • 1`,

the norm-scaling identity `‖c(v) ψ‖ = ‖v‖ ‖ψ‖` (without assuming `S` finite-dimensional), the
real-part polarization `Re ⟪c(v) ψ, c(w) ψ⟫_ℂ = ⟪v, w⟫_ℝ ‖ψ‖²`, and `Re ⟪c(v) ψ, ψ⟫_ℂ = 0`.

This file records the geometric convention as the predicate `AlgHom.IsGeometricClifford` (supporting
dot notation `ρ.IsGeometricClifford`), develops its unit-plane and graded complex tensor-product
calculus, connects it to the conjugate-linear Clifford involution `CliffordAlgebra.conjStar` and
the chirality operator `liftBaseChange ℂ Q ρ (complexVolume Q o)`, and supplies concrete nontrivial
witnesses in dimensions `1`, `2` (the negative Pauli plane), and arbitrary even dimension, along
with negative controls showing that neither clause of `IsGeometricClifford` is redundant.

## Main definitions

* `AlgHom.IsGeometricClifford`: predicate on `ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S` combining
  `Q v = -‖v‖²` and `⟪c(v) x, y⟫_ℂ = -⟪x, c(v) y⟫_ℂ`.
* `AlgHom.cliffordComplexProd`, `AlgHom.cliffordComplexProdLp`: the graded complex tensor-product
  action `c(v, w) = c₁(v) ⊗ 1 + γ ⊗ c₂(w)` of real Clifford algebras on `E ⊗[ℂ] F`, over
  `M₁ × M₂` and over the `L²` orthogonal sum `WithLp 2 (V₁ × V₂)`.
* `CliffordAlgebra.realLineGeometricClifford`, `CliffordAlgebra.pauliPlaneClifford`: concrete
  models of the geometric convention on `ℝ` (acting on `ℂ` by `i`) and on `EuclideanSpace ℝ (Fin 2)`
  (acting on `EuclideanSpace ℂ (Fin 2)` by `c(e₀) = i σ₃`, `c(e₁) = i σ₂`, with chirality `-σ₁`).

## Main results

* `AlgHom.isGeometricClifford_iff`, `AlgHom.isGeometricClifford_iff_inner`,
  `AlgHom.isGeometricClifford_iff_adjoint`: inner-product and finite-dimensional adjoint
  characterizations of `IsGeometricClifford`.
* `AlgHom.IsGeometricClifford.map_ι_mul_map_ι_add_swap`,
  `AlgHom.IsGeometricClifford.map_ι_apply_map_ι_apply_add_swap`: the polarized Euclidean Clifford
  relation `c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫_ℝ • 1`.
* `AlgHom.IsGeometricClifford.norm_map_ι_apply`,
  `AlgHom.IsGeometricClifford.re_inner_map_ι_apply_map_ι_apply`,
  `AlgHom.IsGeometricClifford.re_inner_map_ι_apply_self`: norm scaling and real inner-product
  identities in arbitrary dimension.
* `CliffordAlgebra.ι_rot_mul_ι_rot_of_orthonormal`,
  `AlgHom.IsGeometricClifford.map_ι_mul_map_ι_sq_of_orthonormal`,
  `AlgHom.IsGeometricClifford.smul_I_map_ι_mul_map_ι_sq_of_orthonormal`,
  `AlgHom.IsGeometricClifford.isSymmetric_smul_I_map_ι_mul_map_ι_of_inner_eq_zero`: unit orthogonal
  2-plane squares, `SO(2)` rotation invariance of `c(e₁) c(e₂)`, and symmetry of `i c(e₁) c(e₂)`.
* `AlgHom.IsGeometricClifford.cliffordComplexProdLp`,
  `CliffordAlgebra.liftBaseChange_cliffordComplexProdLp_eq_complexProdTensor`: the graded complex
  tensor product of geometric Clifford actions preserves `IsGeometricClifford` and complexifies to
  `CliffordAlgebra.complexProdTensor`.
* `CliffordAlgebra.inner_liftBaseChange_eq_conjStar_iff`,
  `CliffordAlgebra.adjoint_liftBaseChange_eq_conjStar_iff`: `liftBaseChange ℂ Q ρ` is compatible
  with `conjStar` if and only if real vectors act skew-Hermitianly.
* `CliffordAlgebra.isSymmetric_liftBaseChange_complexVolume`,
  `CliffordAlgebra.isSelfAdjoint_liftBaseChange_complexVolume`,
  `AlgHom.IsGeometricClifford.isOrtho_eigenspace_liftBaseChange_complexVolume`,
  `AlgHom.IsGeometricClifford.norm_sq_eq_add_norm_sq_projection_complexVolume`: self-adjointness of
  the chirality operator `Γ` and orthogonality and Pythagorean norm splitting of `S = S⁺ ⊕ S⁻`.
* `CliffordAlgebra.isGeometricClifford_realLineGeometricClifford`,
  `CliffordAlgebra.isGeometricClifford_pauliPlaneClifford`,
  `CliffordAlgebra.liftBaseChange_pauliPlaneClifford_complexVolume`,
  `CliffordAlgebra.exists_innerProductCore_isGeometricClifford`: concrete and general spinor
  witnesses.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Chapter 12, §12.1 (Definition 12.1.10).
-/

public section

noncomputable section

open CliffordAlgebra Module
open scoped RealInnerProductSpace TensorProduct ComplexOrder

/-! ### Polar form of minus the squared norm -/

namespace QuadraticMap

/-- For the negative-definite norm-square form `Q v = -‖v‖²` on a real inner product space, the
polar bilinear form is `-2 ⟪v, w⟫_ℝ`. -/
theorem polar_eq_neg_two_mul_inner {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Q : QuadraticForm ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2) (v w : V) :
    polar Q v w = -2 * ⟪v, w⟫ := by
  simp only [polar, hQ, norm_add_sq_real]
  ring

end QuadraticMap

/-! ### The geometric Clifford convention -/

namespace AlgHom

section Seminormed

variable {V S : Type*} [SeminormedAddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]

/-- **The geometric Clifford convention** for a real algebra homomorphism
`ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S`: the quadratic form is minus the squared norm,
`Q v = -‖v‖²`, and Clifford multiplication `c(v) = ρ (ι Q v)` by every real vector `v` is
skew-Hermitian for the complex inner product on `S`. Neither finite-dimensionality of `V` or `S`
nor separation of the seminorms is required to state or use the predicate. -/
structure IsGeometricClifford (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) : Prop where
  /-- The quadratic form is minus the squared norm: `Q v = -‖v‖²`. -/
  map_eq_neg_norm_sq (v : V) : Q v = -‖v‖ ^ 2
  /-- Real vectors act skew-Hermitianly: `⟪c(v) x, y⟫_ℂ = -⟪x, c(v) y⟫_ℂ`. -/
  inner_map_ι_left (v : V) (x y : S) :
    inner ℂ (ρ (ι Q v) x) y = -inner ℂ x (ρ (ι Q v) y)

/-- Unpacking characterization of `AlgHom.IsGeometricClifford`. -/
theorem isGeometricClifford_iff {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} :
    ρ.IsGeometricClifford ↔
      (∀ v : V, Q v = -‖v‖ ^ 2) ∧
        ∀ (v : V) (x y : S), inner ℂ (ρ (ι Q v) x) y = -inner ℂ x (ρ (ι Q v) y) :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

namespace IsGeometricClifford

variable {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
include hρ

/-- Moving `c(v)` from the right slot to the left slot of the complex inner product negates it. -/
theorem inner_map_ι_right (v : V) (x y : S) :
    inner ℂ x (ρ (ι Q v) y) = -inner ℂ (ρ (ι Q v) x) y := by
  rw [hρ.inner_map_ι_left, neg_neg]

/-- Every element `a` of the real Clifford algebra satisfies `⟪ρ a x, y⟫ = ⟪x, ρ (star a) y⟫`,
where `star` is Mathlib's Clifford conjugation `reverse ∘ involute`. -/
theorem inner_map_eq_map_star (a : CliffordAlgebra Q) (x y : S) :
    inner ℂ (ρ a x) y = inner ℂ x (ρ (star a) y) :=
  sesqForm_map_eq_map_star ρ (innerₛₗ ℂ) (fun v x y ↦ hρ.inner_map_ι_left v x y) a x y

/-- On any geometric Hermitian Clifford module, `liftBaseChange ℂ Q ρ` is compatible with
`conjStar`. -/
theorem inner_liftBaseChange_conjStar (a : CliffordAlgebra (Q.baseChange ℂ)) (x y : S) :
    inner ℂ (liftBaseChange ℂ Q ρ a x) y = inner ℂ x (liftBaseChange ℂ Q ρ (conjStar Q a) y) :=
  sesqForm_map_eq_map_conjStar (liftBaseChange ℂ Q ρ) (innerₛₗ ℂ)
    (fun v x y ↦ by simpa using hρ.inner_map_ι_left v x y) a x y

/-- Diagonal Clifford relation in the geometric convention: `c(v)² = -‖v‖² • 1`. -/
theorem map_ι_mul_self (v : V) :
    ρ (ι Q v) * ρ (ι Q v) = ((-‖v‖ ^ 2 : ℝ) : ℂ) • 1 := by
  rw [map_ι_mul_map_ι, hρ.map_eq_neg_norm_sq]

/-- Pointwise diagonal Clifford relation: `c(v) (c(v) ψ) = -‖v‖² • ψ`. -/
theorem map_ι_apply_self (v : V) (ψ : S) :
    ρ (ι Q v) (ρ (ι Q v) ψ) = ((-‖v‖ ^ 2 : ℝ) : ℂ) • ψ := by
  rw [map_ι_apply_map_ι_apply, hρ.map_eq_neg_norm_sq]

/-- **Norm scaling** in the geometric convention (in arbitrary dimension): `‖c(v) ψ‖ = ‖v‖ ‖ψ‖`. -/
theorem norm_map_ι_apply (v : V) (ψ : S) : ‖ρ (ι Q v) ψ‖ = ‖v‖ * ‖ψ‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [← RCLike.ofReal_inj (K := ℂ), RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K,
    hρ.inner_map_ι_left, hρ.map_ι_apply_self, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  push_cast
  ring

/-- Clifford multiplication by a real vector sends every spinor `ψ` to a spinor whose complex inner
product with `ψ` is purely imaginary: `Re ⟪c(v) ψ, ψ⟫_ℂ = 0`. -/
theorem re_inner_map_ι_apply_self (v : V) (ψ : S) :
    (inner ℂ (ρ (ι Q v) ψ) ψ).re = 0 := by
  have h := congrArg (RCLike.re (K := ℂ)) (hρ.inner_map_ι_left v ψ ψ)
  conv_rhs at h => rw [map_neg, inner_re_symm]
  simp only [RCLike.re_to_complex] at h
  linarith

/-- A real unit vector squares to `-1` under a geometric Clifford action. -/
theorem map_ι_mul_self_of_norm_eq_one {u : V} (hu : ‖u‖ = 1) :
    ρ (ι Q u) * ρ (ι Q u) = -1 := by
  simp [hρ.map_ι_mul_self, hu]

/-- Clifford multiplication by a real unit vector preserves norms: `‖c(u) ψ‖ = ‖ψ‖`. -/
theorem norm_map_ι_apply_of_norm_eq_one {u : V} (hu : ‖u‖ = 1) (ψ : S) :
    ‖ρ (ι Q u) ψ‖ = ‖ψ‖ := by
  rw [hρ.norm_map_ι_apply, hu, one_mul]

end IsGeometricClifford

end Seminormed

section RealInner

variable {V S : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]

/-- On a real inner product space, `IsGeometricClifford` is equivalently `Q v = -⟪v, v⟫_ℝ` together
with skew-Hermitianness of `c(v)`. -/
theorem isGeometricClifford_iff_inner {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} :
    ρ.IsGeometricClifford ↔
      (∀ v : V, Q v = -⟪v, v⟫) ∧
        ∀ (v : V) (x y : S), inner ℂ (ρ (ι Q v) x) y = -inner ℂ x (ρ (ι Q v) y) := by
  simp_rw [isGeometricClifford_iff, real_inner_self_eq_norm_sq]

namespace IsGeometricClifford

variable {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
include hρ

/-- **The polarized Euclidean Clifford relation** (Nicolaescu, Definition 12.1.10):
`c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫_ℝ • 1`. -/
theorem map_ι_mul_map_ι_add_swap (v w : V) :
    ρ (ι Q v) * ρ (ι Q w) + ρ (ι Q w) * ρ (ι Q v) = ((-2 * ⟪v, w⟫ : ℝ) : ℂ) • 1 := by
  rw [CliffordAlgebra.map_ι_mul_map_ι_add_swap,
    QuadraticMap.polar_eq_neg_two_mul_inner hρ.map_eq_neg_norm_sq]

/-- Pointwise polarized Euclidean Clifford relation:
`c(v) (c(w) ψ) + c(w) (c(v) ψ) = -2 ⟪v, w⟫_ℝ • ψ`. -/
theorem map_ι_apply_map_ι_apply_add_swap (v w : V) (ψ : S) :
    ρ (ι Q v) (ρ (ι Q w) ψ) + ρ (ι Q w) (ρ (ι Q v) ψ) = ((-2 * ⟪v, w⟫ : ℝ) : ℂ) • ψ := by
  rw [CliffordAlgebra.map_ι_apply_map_ι_apply_add_swap,
    QuadraticMap.polar_eq_neg_two_mul_inner hρ.map_eq_neg_norm_sq]

/-- Orthogonal vectors in `V` anticommute: `⟪v, w⟫_ℝ = 0 → c(v) c(w) = -c(w) c(v)`. -/
theorem map_ι_mul_map_ι_of_inner_eq_zero {v w : V} (h : ⟪v, w⟫ = 0) :
    ρ (ι Q v) * ρ (ι Q w) = -(ρ (ι Q w) * ρ (ι Q v)) := by
  apply eq_neg_of_add_eq_zero_left
  simpa [h] using hρ.map_ι_mul_map_ι_add_swap v w

/-- Pointwise anticommutation of orthogonal vectors: `c(v) (c(w) ψ) = -c(w) (c(v) ψ)`. -/
theorem map_ι_apply_map_ι_apply_of_inner_eq_zero {v w : V} (h : ⟪v, w⟫ = 0) (ψ : S) :
    ρ (ι Q v) (ρ (ι Q w) ψ) = -ρ (ι Q w) (ρ (ι Q v) ψ) := by
  rw [← mul_apply_eq_comp, hρ.map_ι_mul_map_ι_of_inner_eq_zero h, LinearMap.neg_apply,
    mul_apply_eq_comp]

/-- **Polarized inner-product identity**: `Re ⟪c(v) ψ, c(w) ψ⟫_ℂ = ⟪v, w⟫_ℝ ‖ψ‖²`. -/
theorem re_inner_map_ι_apply_map_ι_apply (v w : V) (ψ : S) :
    (inner ℂ (ρ (ι Q v) ψ) (ρ (ι Q w) ψ)).re = ⟪v, w⟫ * ‖ψ‖ ^ 2 := by
  have h := norm_add_sq (𝕜 := ℂ) (ρ (ι Q v) ψ) (ρ (ι Q w) ψ)
  rw [← LinearMap.add_apply, ← map_add ρ, ← map_add (ι Q), hρ.norm_map_ι_apply,
    hρ.norm_map_ι_apply, hρ.norm_map_ι_apply] at h
  have hv : (‖v + w‖ * ‖ψ‖) ^ 2 = (‖v‖ ^ 2 + 2 * ⟪v, w⟫ + ‖w‖ ^ 2) * ‖ψ‖ ^ 2 := by
    rw [mul_pow, norm_add_sq_real]
  simp only [RCLike.re_to_complex] at h
  linarith [hv]

/-- For orthogonal vectors `e₁, e₂`, the bivector operator `c(e₁) c(e₂)` is skew-Hermitian. -/
theorem inner_map_ι_mul_map_ι_left_of_inner_eq_zero {e₁ e₂ : V} (h₁₂ : ⟪e₁, e₂⟫ = 0) (x y : S) :
    inner ℂ ((ρ (ι Q e₁) * ρ (ι Q e₂)) x) y = -inner ℂ x ((ρ (ι Q e₁) * ρ (ι Q e₂)) y) := by
  rw [mul_apply_eq_comp, hρ.inner_map_ι_left, hρ.inner_map_ι_left, neg_neg, ← mul_apply_eq_comp,
    hρ.map_ι_mul_map_ι_of_inner_eq_zero (by rw [real_inner_comm, h₁₂]), LinearMap.neg_apply,
    inner_neg_right]

/-- For orthogonal vectors `e₁, e₂`, multiplying the bivector `c(e₁) c(e₂)` by `i` produces a
symmetric operator `i • (c(e₁) c(e₂))`. -/
theorem isSymmetric_smul_I_map_ι_mul_map_ι_of_inner_eq_zero {e₁ e₂ : V} (h₁₂ : ⟪e₁, e₂⟫ = 0) :
    (Complex.I • (ρ (ι Q e₁) * ρ (ι Q e₂))).IsSymmetric := fun x y ↦ by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
    Complex.conj_I, hρ.inner_map_ι_mul_map_ι_left_of_inner_eq_zero h₁₂, neg_mul_neg]

end IsGeometricClifford

end RealInner

section FiniteDimensional

variable {V S : Type*} [SeminormedAddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]

/-- On a finite-dimensional complex inner product space, `IsGeometricClifford` is equivalent to
`Q v = -‖v‖²` together with `(c(v)).adjoint = -c(v)` for every `v`. -/
theorem isGeometricClifford_iff_adjoint {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} :
    ρ.IsGeometricClifford ↔
      (∀ v : V, Q v = -‖v‖ ^ 2) ∧ ∀ v : V, (ρ (ι Q v)).adjoint = -ρ (ι Q v) := by
  refine isGeometricClifford_iff.trans (and_congr_right' ⟨fun h v ↦ ?_, fun h v x y ↦ ?_⟩)
  · refine ((LinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ ?_).symm
    simp [h v x y]
  · rw [← LinearMap.adjoint_inner_right, h v, LinearMap.neg_apply, inner_neg_right]

namespace IsGeometricClifford

variable {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
include hρ

/-- On a finite-dimensional module, `c(v)` has adjoint `-c(v)`. -/
theorem adjoint_map_ι (v : V) : (ρ (ι Q v)).adjoint = -ρ (ι Q v) :=
  (isGeometricClifford_iff_adjoint.mp hρ).2 v

/-- On a finite-dimensional module, `(ρ a).adjoint = ρ (star a)` for every `a : CliffordAlgebra Q`.
-/
theorem adjoint_map (a : CliffordAlgebra Q) : (ρ a).adjoint = ρ (star a) :=
  adjoint_map_eq_map_star hρ.adjoint_map_ι a

end IsGeometricClifford

end FiniteDimensional

end AlgHom

/-! ### Unit orthogonal two-planes and `SO(2)` rotation invariance -/

namespace CliffordAlgebra

section Plane

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- In `CliffordAlgebra Q` with `Q v = -‖v‖²`, orthogonal vectors anticommute:
`⟪e₁, e₂⟫_ℝ = 0 → ι e₁ * ι e₂ = -(ι e₂ * ι e₁)`. -/
theorem ι_mul_ι_of_inner_eq_zero {e₁ e₂ : V} (h₁₂ : ⟪e₁, e₂⟫ = 0) :
    ι Q e₁ * ι Q e₂ = -(ι Q e₂ * ι Q e₁) := by
  apply eq_neg_of_add_eq_zero_left
  rw [ι_mul_ι_add_swap, QuadraticMap.polar_eq_neg_two_mul_inner hQ, h₁₂, mul_zero, map_zero]

/-- In `CliffordAlgebra Q` with `Q v = -‖v‖²`, the bivector `ι e₁ * ι e₂` of an orthonormal pair
squares to `-1`. -/
theorem ι_mul_ι_sq_of_orthonormal {e₁ e₂ : V} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫ = 0) :
    (ι Q e₁ * ι Q e₂) * (ι Q e₁ * ι Q e₂) = -1 := by
  have h21 : ι Q e₂ * ι Q e₁ = -(ι Q e₁ * ι Q e₂) :=
    ι_mul_ι_of_inner_eq_zero hQ (by rw [real_inner_comm, h₁₂])
  calc
    (ι Q e₁ * ι Q e₂) * (ι Q e₁ * ι Q e₂)
      = (ι Q e₁ * (ι Q e₂ * ι Q e₁)) * ι Q e₂ := by simp [mul_assoc]
    _ = -((ι Q e₁ * ι Q e₁) * (ι Q e₂ * ι Q e₂)) := by
      rw [h21, mul_neg, neg_mul, ← mul_assoc (ι Q e₁), mul_assoc (ι Q e₁ * ι Q e₁)]
    _ = -1 := by simp [ι_sq_scalar, hQ, he₁, he₂]

/-- **`SO(2)` rotation invariance of a unit plane bivector**: for an orthonormal pair `(e₁, e₂)` and
any `(c, s)` on the unit circle `c² + s² = 1`, rotating `(e₁, e₂)` to
`(c • e₁ + s • e₂, -s • e₁ + c • e₂)` leaves the Clifford product `ι e₁ * ι e₂` unchanged. -/
theorem ι_rot_mul_ι_rot_of_orthonormal {e₁ e₂ : V} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫ = 0) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    ι Q (c • e₁ + s • e₂) * ι Q ((-s) • e₁ + c • e₂) = ι Q e₁ * ι Q e₂ := by
  have h1 : ι Q e₁ * ι Q e₁ = -1 := by simp [ι_sq_scalar, hQ, he₁]
  have h2 : ι Q e₂ * ι Q e₂ = -1 := by simp [ι_sq_scalar, hQ, he₂]
  have h21 : ι Q e₂ * ι Q e₁ = -(ι Q e₁ * ι Q e₂) :=
    ι_mul_ι_of_inner_eq_zero hQ (by rw [real_inner_comm, h₁₂])
  simp only [map_add, map_smul, add_mul, mul_add, smul_mul_smul_comm, h1, h2, h21, smul_neg]
  calc
    _ = (c ^ 2 + s ^ 2) • (ι Q e₁ * ι Q e₂) + (c * s - s * c) • (1 : CliffordAlgebra Q) := by
      module
    _ = ι Q e₁ * ι Q e₂ := by rw [hcs, one_smul, mul_comm c s, sub_self, zero_smul, add_zero]

/-- Trigonometric form of `CliffordAlgebra.ι_rot_mul_ι_rot_of_orthonormal`: rotating an orthonormal
pair `(e₁, e₂)` by angle `θ` preserves `ι e₁ * ι e₂`. -/
theorem ι_cos_sin_mul_of_orthonormal {e₁ e₂ : V} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫ = 0) (θ : ℝ) :
    ι Q (Real.cos θ • e₁ + Real.sin θ • e₂) * ι Q ((-Real.sin θ) • e₁ + Real.cos θ • e₂) =
      ι Q e₁ * ι Q e₂ :=
  ι_rot_mul_ι_rot_of_orthonormal hQ he₁ he₂ h₁₂ (Real.cos_sq_add_sin_sq θ)

end Plane

end CliffordAlgebra

namespace AlgHom.IsGeometricClifford

variable {V S : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
include hρ

/-- For an orthonormal pair `(e₁, e₂)`, the unnormalized plane product `c(e₁) c(e₂)` squares to
`-1` (so without the factor `i` it has eigenvalues `±i`, not `±1`). -/
theorem map_ι_mul_map_ι_sq_of_orthonormal {e₁ e₂ : V} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫ = 0) :
    (ρ (ι Q e₁) * ρ (ι Q e₂)) * (ρ (ι Q e₁) * ρ (ι Q e₂)) = -1 := by
  rw [← map_mul ρ, ← map_mul ρ, ι_mul_ι_sq_of_orthonormal hρ.map_eq_neg_norm_sq he₁ he₂ h₁₂,
    map_neg, map_one]

/-- For an orthonormal pair `(e₁, e₂)`, the normalized plane chirality operator `i • (c(e₁) c(e₂))`
squares to `1`. -/
theorem smul_I_map_ι_mul_map_ι_sq_of_orthonormal {e₁ e₂ : V} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫ = 0) :
    (Complex.I • (ρ (ι Q e₁) * ρ (ι Q e₂))) * (Complex.I • (ρ (ι Q e₁) * ρ (ι Q e₂))) = 1 := by
  rw [smul_mul_smul_comm, Complex.I_mul_I, hρ.map_ι_mul_map_ι_sq_of_orthonormal he₁ he₂ h₁₂,
    neg_one_smul, neg_neg]

/-- `SO(2)` rotation invariance of the plane operator `c(e₁) c(e₂)`. -/
theorem map_ι_cos_sin_mul_of_orthonormal {e₁ e₂ : V} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫ = 0) (θ : ℝ) :
    ρ (ι Q (Real.cos θ • e₁ + Real.sin θ • e₂)) *
        ρ (ι Q ((-Real.sin θ) • e₁ + Real.cos θ • e₂)) =
      ρ (ι Q e₁) * ρ (ι Q e₂) := by
  rw [← map_mul ρ, ι_cos_sin_mul_of_orthonormal hρ.map_eq_neg_norm_sq he₁ he₂ h₁₂, map_mul]

end AlgHom.IsGeometricClifford

/-! ### Graded complex tensor product of real Clifford actions -/

namespace AlgHom

section AlgebraicTensor

variable {M₁ M₂ E F : Type*} [AddCommGroup M₁] [Module ℝ M₁] [AddCommGroup M₂] [Module ℝ M₂]
  {Q₁ : QuadraticForm ℝ M₁} {Q₂ : QuadraticForm ℝ M₂}
  [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E) (γ : Module.End ℂ E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F)

include hγρ in
private theorem mul_liftBaseChange_ι_eq_neg (w : ℂ ⊗[ℝ] M₁) :
    γ * liftBaseChange ℂ Q₁ ρ₁ (ι (Q₁.baseChange ℂ) w) =
      -(liftBaseChange ℂ Q₁ ρ₁ (ι (Q₁.baseChange ℂ) w) * γ) := by
  induction w using TensorProduct.inductionOn with
  | tmul z v =>
    rw [liftBaseChange_ι_tmul, mul_smul_comm, hγρ, smul_neg, ← smul_mul_assoc]
  | add x y hx hy =>
    rw [map_add, map_add, mul_add, hx, hy, add_mul, neg_add]

/-- **The graded complex tensor product of real Clifford actions**: given real algebra maps
`ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E` (with a complex-linear grading involution `γ`
anticommuting with `c₁(v)`) and `ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F`, `(v, w)` acts on
`E ⊗[ℂ] F` by `c₁(v) ⊗ 1 + γ ⊗ c₂(w)`. Constructed from `AlgHom.cliffordProdTensor` over `ℂ` via
`CliffordAlgebra.liftBaseChange` and `QuadraticForm.baseChangeProd`. -/
def cliffordComplexProd :
    CliffordAlgebra (Q₁.prod Q₂) →ₐ[ℝ] Module.End ℂ (E ⊗[ℂ] F) :=
  (liftBaseChange ℂ (Q₁.prod Q₂)).symm <|
    (AlgHom.cliffordProdTensor (liftBaseChange ℂ Q₁ ρ₁) γ hγ
        (mul_liftBaseChange_ι_eq_neg ρ₁ γ hγρ) (liftBaseChange ℂ Q₂ ρ₂)).comp
      (equivOfIsometry (QuadraticForm.baseChangeProd Q₁ Q₂)).toAlgHom

/-- Evaluation of `AlgHom.cliffordComplexProd` on a generator `(v, w)`. -/
@[simp]
theorem cliffordComplexProd_ι (x : M₁ × M₂) :
    ρ₁.cliffordComplexProd γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) x) =
      (ρ₁ (ι Q₁ x.1)).rTensor F + TensorProduct.map γ (ρ₂ (ι Q₂ x.2)) := by
  simp [cliffordComplexProd, equivOfIsometry_apply, cliffordProdTensor_ι]

/-- Evaluation of `AlgHom.cliffordComplexProd` on a pure tensor `e ⊗ₜ f`. -/
theorem cliffordComplexProd_ι_tmul (x : M₁ × M₂) (e : E) (f : F) :
    ρ₁.cliffordComplexProd γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) x) (e ⊗ₜ f) =
      ρ₁ (ι Q₁ x.1) e ⊗ₜ f + γ e ⊗ₜ ρ₂ (ι Q₂ x.2) f := by
  simp

end AlgebraicTensor

section LpTensor

section Lift

variable {V₁ V₂ E F : Type*}
  [AddCommGroup V₁] [Module ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂]
  {Q₁ : QuadraticForm ℝ V₁} {Q₂ : QuadraticForm ℝ V₂}
  {Q : QuadraticForm ℝ (WithLp 2 (V₁ × V₂))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F]

/-- **The graded complex tensor product over an `L²` orthogonal direct sum**: acts on `E ⊗[ℂ] F`
for any quadratic form `Q` on `WithLp 2 (V₁ × V₂)` satisfying `Q (v, w) = Q₁ v + Q₂ w`, sending
`WithLp.toLp 2 (v, w)` to `c₁(v) ⊗ 1 + γ ⊗ c₂(w)`. -/
def cliffordComplexProdLp
    (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E) (γ : Module.End ℂ E)
    (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F) :
    CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ (E ⊗[ℂ] F) :=
  (ρ₁.cliffordComplexProd γ hγ hγρ ρ₂).comp
    (CliffordAlgebra.map ⟨(WithLp.linearEquiv 2 ℝ (V₁ × V₂)).toLinearMap, fun x ↦ (hQ x).symm⟩)

/-- On `WithLp.toLp 2 (v, w)`, `cliffordComplexProdLp` acts by `c₁(v) ⊗ 1 + γ ⊗ c₂(w)`. -/
@[simp]
theorem cliffordComplexProdLp_ι_toLp
    (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E) (γ : Module.End ℂ E)
    (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F) (v : V₁) (w : V₂) :
    ρ₁.cliffordComplexProdLp hQ γ hγ hγρ ρ₂ (ι Q (WithLp.toLp 2 (v, w))) =
      (ρ₁ (ι Q₁ v)).rTensor F + TensorProduct.map γ (ρ₂ (ι Q₂ w)) := by
  rw [cliffordComplexProdLp, AlgHom.comp_apply, map_apply_ι]
  exact cliffordComplexProd_ι ρ₁ γ hγ hγρ ρ₂ (v, w)

end Lift

/-- **The graded complex tensor product preserves `IsGeometricClifford`** whenever the grading
involution `γ` on the first factor is symmetric (`⟪γ e₁, e₂⟫ = ⟪e₁, γ e₂⟫`), as holds for the
chirality operator of an oriented even-dimensional Euclidean space. -/
theorem IsGeometricClifford.cliffordComplexProdLp
    {V₁ V₂ E F : Type*}
    [SeminormedAddCommGroup V₁] [Module ℝ V₁]
    [SeminormedAddCommGroup V₂] [Module ℝ V₂]
    {Q₁ : QuadraticForm ℝ V₁} {Q₂ : QuadraticForm ℝ V₂}
    {Q : QuadraticForm ℝ (WithLp 2 (V₁ × V₂))}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E} (hρ₁ : ρ₁.IsGeometricClifford)
    {γ : Module.End ℂ E} (hγ : γ * γ = 1)
    (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ)) (hγsymm : γ.IsSymmetric)
    {ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F} (hρ₂ : ρ₂.IsGeometricClifford) :
    (ρ₁.cliffordComplexProdLp hQ γ hγ hγρ ρ₂).IsGeometricClifford where
  map_eq_neg_norm_sq x := by
    rw [hQ, hρ₁.map_eq_neg_norm_sq, hρ₂.map_eq_neg_norm_sq, WithLp.prod_norm_sq_eq_of_L2]
    change -‖x.fst‖ ^ 2 + -‖x.snd‖ ^ 2 = -(‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2)
    ring
  inner_map_ι_left x t₁ t₂ := by
    have hact := cliffordComplexProdLp_ι_toLp hQ ρ₁ γ hγ hγρ ρ₂ (WithLp.ofLp x).1 (WithLp.ofLp x).2
    refine (congrArg₂ (inner ℂ) (LinearMap.congr_fun hact t₁) rfl).trans <| Eq.trans ?_
      (congrArg Neg.neg (congrArg₂ (inner ℂ) rfl (LinearMap.congr_fun hact t₂).symm))
    induction t₁ using TensorProduct.inductionOn with
    | tmul e₁ f₁ =>
      induction t₂ using TensorProduct.inductionOn with
      | tmul e₂ f₂ =>
        simp only [LinearMap.add_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
          inner_add_left, inner_add_right, TensorProduct.inner_tmul, hρ₁.inner_map_ι_left,
          hρ₂.inner_map_ι_left, hγsymm e₁ e₂]
        ring
      | add u v hu hv =>
        simp only [map_add, inner_add_right] at hu hv ⊢
        linear_combination hu + hv
    | add u v hu hv =>
      simp only [map_add, inner_add_left] at hu hv ⊢
      linear_combination hu + hv

end LpTensor

end AlgHom

namespace CliffordAlgebra

/-- **Compatibility with `CliffordAlgebra.complexProdTensor`**: when the first factor is graded by
its chirality operator `liftBaseChange ℂ Q₁ ρ₁ (complexVolume Q₁ o₁)`, complexifying
`AlgHom.cliffordComplexProdLp` produces `CliffordAlgebra.complexProdTensor`. -/
theorem liftBaseChange_cliffordComplexProdLp_eq_complexProdTensor
    {V₁ V₂ E F : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [FiniteDimensional ℝ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    {Q₁ : QuadraticForm ℝ V₁} {Q₂ : QuadraticForm ℝ V₂}
    {Q : QuadraticForm ℝ (WithLp 2 (V₁ × V₂))}
    (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
    {n : ℕ} [Fact (finrank ℝ V₁ = n)] (o₁ : Orientation ℝ V₁ (Fin n))
    (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E)
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F) :
    liftBaseChange ℂ Q
        (ρ₁.cliffordComplexProdLp hQ (liftBaseChange ℂ Q₁ ρ₁ (complexVolume Q₁ o₁))
          (liftBaseChange_complexVolume_mul_self ρ₁ o₁ hQ₁)
          (liftBaseChange_complexVolume_mul_map_ι_of_even ρ₁ o₁ hn) ρ₂) =
      complexProdTensor hQ o₁ hQ₁ hn (liftBaseChange ℂ Q₁ ρ₁) (liftBaseChange ℂ Q₂ ρ₂) := by
  rw [liftBaseChange_eq_iff]
  intro x
  have hx : x = WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2) := rfl
  rw [hx]
  simp

end CliffordAlgebra

/-! ### `conjStar`-compatibility and self-adjointness of the chirality operator -/

namespace CliffordAlgebra

section ConjStarInner

variable {V S : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

/-- **Criterion for `conjStar`-compatibility of `liftBaseChange`** (in arbitrary dimension): the
complex-linear extension `liftBaseChange ℂ Q ρ` satisfies
`⟪ρ_ℂ a x, y⟫_ℂ = ⟪x, ρ_ℂ (conjStar Q a) y⟫_ℂ` for all `a` if and only if every real vector `v : V`
acts skew-Hermitianly under `ρ`. -/
theorem inner_liftBaseChange_eq_conjStar_iff :
    (∀ (a : CliffordAlgebra (Q.baseChange ℂ)) (x y : S),
        inner ℂ (liftBaseChange ℂ Q ρ a x) y =
          inner ℂ x (liftBaseChange ℂ Q ρ (conjStar Q a) y)) ↔
      ∀ (v : V) (x y : S), inner ℂ (ρ (ι Q v) x) y = -inner ℂ x (ρ (ι Q v) y) := by
  refine ⟨fun h v x y ↦ ?_, fun h a x y ↦ ?_⟩
  · simpa using h (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) x y
  · exact sesqForm_map_eq_map_conjStar (liftBaseChange ℂ Q ρ) (innerₛₗ ℂ)
      (fun v x y ↦ by simpa using h v x y) a x y

end ConjStarInner

section ConjStarAdjoint

variable {V S : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S)

/-- **Adjoint criterion for `liftBaseChange`**: on a finite-dimensional complex inner product space,
`liftBaseChange ℂ Q ρ` is a `*`-representation for `conjStar` if and only if every real vector acts
skew-adjointly. -/
theorem adjoint_liftBaseChange_eq_conjStar_iff :
    (∀ a : CliffordAlgebra (Q.baseChange ℂ),
        (liftBaseChange ℂ Q ρ a).adjoint = liftBaseChange ℂ Q ρ (conjStar Q a)) ↔
      ∀ v : V, (ρ (ι Q v)).adjoint = -ρ (ι Q v) := by
  simpa using adjoint_map_eq_map_conjStar_iff (liftBaseChange ℂ Q ρ)

end ConjStarAdjoint

section ChiralitySymmetry

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))

/-- Whenever real vectors act skew-Hermitianly on `S`, the chirality operator
`liftBaseChange ℂ Q ρ (complexVolume Q o)` is symmetric for the inner product of `S` (for every
quadratic form `Q` and without assuming `S` finite-dimensional). -/
theorem isSymmetric_liftBaseChange_complexVolume
    [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S}
    (hρ : ∀ (v : V) (x y : S), inner ℂ (ρ (ι Q v) x) y = -inner ℂ x (ρ (ι Q v) y)) :
    (liftBaseChange ℂ Q ρ (complexVolume Q o)).IsSymmetric := fun x y ↦ by
  rw [(inner_liftBaseChange_eq_conjStar_iff ρ).mpr hρ, conjStar_complexVolume]

/-- On a finite-dimensional Hermitian module with skew-adjoint real generators, the chirality
operator equals its own adjoint. -/
theorem adjoint_liftBaseChange_complexVolume
    [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S}
    (hρ : ∀ v : V, (ρ (ι Q v)).adjoint = -ρ (ι Q v)) :
    (liftBaseChange ℂ Q ρ (complexVolume Q o)).adjoint =
      liftBaseChange ℂ Q ρ (complexVolume Q o) := by
  rw [(adjoint_liftBaseChange_eq_conjStar_iff ρ).mpr hρ, conjStar_complexVolume]

/-- On a finite-dimensional Hermitian module with skew-adjoint real generators, the chirality
operator is self-adjoint (`IsSelfAdjoint`). -/
theorem isSelfAdjoint_liftBaseChange_complexVolume
    [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S}
    (hρ : ∀ v : V, (ρ (ι Q v)).adjoint = -ρ (ι Q v)) :
    IsSelfAdjoint (liftBaseChange ℂ Q ρ (complexVolume Q o)) :=
  LinearMap.isSelfAdjoint_iff'.mpr (adjoint_liftBaseChange_complexVolume o hρ)

end ChiralitySymmetry

end CliffordAlgebra

namespace AlgHom.IsGeometricClifford

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))

section SeminormedS

variable [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
include hρ

/-- **Symmetry of the chirality operator** on a geometric Hermitian Clifford module. -/
theorem isSymmetric_liftBaseChange_complexVolume :
    (liftBaseChange ℂ Q ρ (complexVolume Q o)).IsSymmetric :=
  CliffordAlgebra.isSymmetric_liftBaseChange_complexVolume o hρ.inner_map_ι_left

/-- **Orthogonality of positive and negative half-spinors**: any `+1`-eigenvector and
`-1`-eigenvector of `liftBaseChange ℂ Q ρ (complexVolume Q o)` are orthogonal. -/
theorem inner_eigenspace_liftBaseChange_complexVolume_eq_zero {ψ₁ ψ₂ : S}
    (h₁ : ψ₁ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace 1)
    (h₂ : ψ₂ ∈ (liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-1)) :
    inner ℂ ψ₁ ψ₂ = 0 := by
  rw [Module.End.mem_eigenspace_iff, one_smul] at h₁
  rw [Module.End.mem_eigenspace_iff, neg_one_smul] at h₂
  have hsymm := hρ.isSymmetric_liftBaseChange_complexVolume o ψ₁ ψ₂
  rw [h₁, h₂, inner_neg_right] at hsymm
  exact (two_ne_zero : (2 : ℂ) ≠ 0).isUnit.smul_eq_zero.mp
    (by rw [two_smul ℂ]; exact eq_neg_iff_add_eq_zero.mp hsymm)

/-- **Pythagorean chirality decomposition**: on a geometric Hermitian Clifford module, the squared
norm of every spinor `ψ` is the sum of the squared norms of its positive and negative chiral
projections. -/
theorem norm_sq_eq_add_norm_sq_projection_complexVolume (ψ : S) :
    ‖ψ‖ ^ 2 =
      ‖Submodule.projection _ _
          (isCompl_eigenspace_liftBaseChange_complexVolume ρ o hρ.map_eq_neg_norm_sq) ψ‖ ^ 2 +
      ‖Submodule.projection _ _
          (isCompl_eigenspace_liftBaseChange_complexVolume ρ o
            hρ.map_eq_neg_norm_sq).symm ψ‖ ^ 2 := by
  set hc := isCompl_eigenspace_liftBaseChange_complexVolume ρ o hρ.map_eq_neg_norm_sq
  have hsum := Submodule.projection_add_projection_eq_self hc ψ
  have horth : inner ℂ (Submodule.projection _ _ hc ψ) (Submodule.projection _ _ hc.symm ψ) = 0 :=
    hρ.inner_eigenspace_liftBaseChange_complexVolume_eq_zero o
      (Submodule.projection_apply_mem hc ψ) (Submodule.projection_apply_mem hc.symm ψ)
  conv_lhs => rw [← hsum]
  rw [norm_add_sq (𝕜 := ℂ), horth, map_zero, mul_zero, add_zero]

end SeminormedS

/-- The `+1`- and `-1`-eigenspaces `S⁺` and `S⁻` of `Γ` are orthogonal submodules (`S⁺ ⟂ S⁻`). -/
theorem isOrtho_eigenspace_liftBaseChange_complexVolume
    [NormedAddCommGroup S] [InnerProductSpace ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford) :
    ((liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace 1).IsOrtho
      ((liftBaseChange ℂ Q ρ (complexVolume Q o)).eigenspace (-1)) :=
  Submodule.isOrtho_iff_inner_eq.mpr fun _ h₁ _ h₂ ↦
    hρ.inner_eigenspace_liftBaseChange_complexVolume_eq_zero o h₁ h₂

/-- **Self-adjointness of `Γ`** on a finite-dimensional geometric Hermitian Clifford module. -/
theorem isSelfAdjoint_liftBaseChange_complexVolume
    [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford) :
    IsSelfAdjoint (liftBaseChange ℂ Q ρ (complexVolume Q o)) :=
  CliffordAlgebra.isSelfAdjoint_liftBaseChange_complexVolume o hρ.adjoint_map_ι

end AlgHom.IsGeometricClifford

/-! ### Concrete nontrivial witnesses and negative controls -/

namespace CliffordAlgebra

section RealLine

private def realLineGen : ℝ →ₗ[ℝ] Module.End ℂ ℂ where
  toFun r := ((r : ℂ) * Complex.I) • 1
  map_add' r s := by push_cast; rw [add_mul, add_smul]
  map_smul' c r := by
    simp only [smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply]
    rw [mul_assoc, ← smul_smul, Complex.coe_smul]

private theorem realLineGen_mul_self (r : ℝ) :
    realLineGen r * realLineGen r =
      algebraMap ℝ (Module.End ℂ ℂ) (-LinearMap.BilinMap.toQuadraticMap (innerₗ ℝ) r) := by
  simp only [realLineGen, LinearMap.coe_mk, AddHom.coe_mk]
  rw [smul_mul_smul_comm, mul_one, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  congr 1
  rw [mul_mul_mul_comm, Complex.I_mul_I, mul_neg_one]
  simp [LinearMap.BilinMap.toQuadraticMap_apply, sq]

/-- **One-dimensional geometric Clifford witness**: `ℝ` with `Q r = -r²` acting on `ℂ` via
`r ↦ (r * i) • 1`. -/
def realLineGeometricClifford :
    CliffordAlgebra (-LinearMap.BilinMap.toQuadraticMap (innerₗ ℝ)) →ₐ[ℝ] Module.End ℂ ℂ :=
  CliffordAlgebra.lift (-LinearMap.BilinMap.toQuadraticMap (innerₗ ℝ))
    ⟨realLineGen, realLineGen_mul_self⟩

/-- The unit generator `1 : ℝ` acts on `ℂ` as multiplication by `i`. -/
@[simp]
theorem realLineGeometricClifford_ι_one :
    realLineGeometricClifford (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ ℝ)) 1) =
      Complex.I • 1 := by
  simp [realLineGeometricClifford, realLineGen]

/-- `CliffordAlgebra.realLineGeometricClifford` satisfies `AlgHom.IsGeometricClifford`. -/
theorem isGeometricClifford_realLineGeometricClifford :
    realLineGeometricClifford.IsGeometricClifford where
  map_eq_neg_norm_sq r := by
    simp [LinearMap.BilinMap.toQuadraticMap_apply, sq]
  inner_map_ι_left r z w := by
    simp only [realLineGeometricClifford, realLineGen, lift_ι_apply, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.smul_apply, one_apply_eq_self, inner_smul_left, inner_smul_right,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring

end RealLine

section PauliPlane

/-- Auxiliary real-linear generator map on `EuclideanSpace ℝ (Fin 2)` sending `v` to
`Matrix.toEuclideanLin (i (v₁ σ₂ + v₀ σ₃))`, so that `e₀ ↦ i σ₃` and `e₁ ↦ i σ₂`. -/
private def pauliPlaneGen :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] Module.End ℂ (EuclideanSpace ℂ (Fin 2)) where
  toFun v := Matrix.toEuclideanLin (Complex.I • TauCeti.pauli ![0, v 1, v 0])
  map_add' v w := by
    have hv : (![0, (v + w) 1, (v + w) 0] : Fin 3 → ℝ) = ![0, v 1, v 0] + ![0, w 1, w 0] := by
      ext i; fin_cases i <;> simp
    rw [hv, map_add, smul_add, map_add]
  map_smul' c v := by
    have hv : (![0, (c • v) 1, (c • v) 0] : Fin 3 → ℝ) = c • ![0, v 1, v 0] := by
      ext i; fin_cases i <;> simp
    simp only [RingHom.id_apply, hv, map_smul, ← Complex.coe_smul]
    rw [smul_comm Complex.I (c : ℂ)]

private theorem pauliPlaneGen_mul_self (v : EuclideanSpace ℝ (Fin 2)) :
    pauliPlaneGen v * pauliPlaneGen v =
      algebraMap ℝ (Module.End ℂ (EuclideanSpace ℂ (Fin 2)))
        ((-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2)))) v) := by
  have hdot : (![0, v 1, v 0] : Fin 3 → ℝ) ⬝ᵥ ![0, v 1, v 0] = v 1 * v 1 + v 0 * v 0 := by
    simp [dotProduct, Fin.sum_univ_three]
  change Matrix.toEuclideanLin _ * Matrix.toEuclideanLin _ = _
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Module.End.mul_eq_comp, ← Matrix.toLin_mul,
    smul_mul_smul_comm, Complex.I_mul_I, TauCeti.pauli_mul_self, neg_one_smul, ← neg_smul,
    map_smul, Matrix.toLin_one, ← Module.End.one_eq_id, Algebra.algebraMap_eq_smul_one,
    ← Complex.ofReal_neg, Complex.coe_smul]
  congr 1
  rw [hdot]
  simp only [LinearMap.BilinMap.toQuadraticMap_apply, neg_apply, innerₗ_apply_apply,
    real_inner_self_eq_norm_sq, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  ring

/-- **Two-dimensional Pauli negative-plane witness**: `EuclideanSpace ℝ (Fin 2)` with `Q v = -‖v‖²`
acting on `EuclideanSpace ℂ (Fin 2)` via `v ↦ i (v₁ σ₂ + v₀ σ₃)` (`e₀ ↦ i σ₃`, `e₁ ↦ i σ₂`). -/
def pauliPlaneClifford :
    CliffordAlgebra (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2)))) →ₐ[ℝ]
      Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  CliffordAlgebra.lift (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
    ⟨pauliPlaneGen, pauliPlaneGen_mul_self⟩

/-- On any vector `v`, `pauliPlaneClifford` acts as `Matrix.toEuclideanLin` of
`i • pauli ![0, v 1, v 0]`. -/
@[simp]
theorem pauliPlaneClifford_ι (v : EuclideanSpace ℝ (Fin 2)) :
    pauliPlaneClifford
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2)))) v) =
      Matrix.toEuclideanLin (Complex.I • TauCeti.pauli ![0, v 1, v 0]) :=
  lift_ι_apply _ _ v

/-- The first standard basis vector `e₀` acts as `i σ₃`. -/
theorem pauliPlaneClifford_single_zero :
    pauliPlaneClifford
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.single 0 1)) =
      Complex.I • Matrix.toEuclideanLin (TauCeti.pauli ![0, 0, 1]) := by
  have hv0 : (![0, (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 1,
      (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 0] : Fin 3 → ℝ) =
      ![0, 0, 1] := by
    ext i; fin_cases i <;> simp
  rw [pauliPlaneClifford_ι, hv0, map_smul]

/-- The second standard basis vector `e₁` acts as `i σ₂`. -/
theorem pauliPlaneClifford_single_one :
    pauliPlaneClifford
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.single 1 1)) =
      Complex.I • Matrix.toEuclideanLin (TauCeti.pauli ![0, 1, 0]) := by
  have hv1 : (![0, (EuclideanSpace.single 1 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 1,
      (EuclideanSpace.single 1 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 0] : Fin 3 → ℝ) =
      ![0, 1, 0] := by
    ext i; fin_cases i <;> simp
  rw [pauliPlaneClifford_ι, hv1, map_smul]

/-- The plane bivector `c(e₀) c(e₁)` acts as `i σ₁`: `(i σ₃) (i σ₂) = -(-i σ₁) = i σ₁`. -/
theorem pauliPlaneClifford_single_zero_mul_single_one :
    pauliPlaneClifford
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.single 0 1)) *
      pauliPlaneClifford
        (ι (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.single 1 1)) =
      Complex.I • Matrix.toEuclideanLin (TauCeti.pauli ![1, 0, 0]) := by
  have hmat : (Complex.I • TauCeti.pauli ![0, 0, 1]) * (Complex.I • TauCeti.pauli ![0, 1, 0]) =
      Complex.I • TauCeti.pauli ![1, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [TauCeti.pauli_apply]
  rw [pauliPlaneClifford_single_zero, pauliPlaneClifford_single_one,
    ← Matrix.toEuclideanLin.map_smul, ← Matrix.toEuclideanLin.map_smul,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, Module.End.mul_eq_comp, ← Matrix.toLin_mul, hmat,
    ← Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toEuclideanLin.map_smul]

/-- **The Pauli negative-plane model satisfies `AlgHom.IsGeometricClifford`.** -/
theorem isGeometricClifford_pauliPlaneClifford : pauliPlaneClifford.IsGeometricClifford := by
  refine AlgHom.isGeometricClifford_iff_adjoint.mpr ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · simp [LinearMap.BilinMap.toQuadraticMap_apply]
  · rw [pauliPlaneClifford_ι, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I,
      (TauCeti.isHermitian_pauli _).eq, neg_smul, map_neg]

local instance : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨by simp⟩

/-- **Chirality of the Pauli negative-plane model**: for the standard orientation of
`EuclideanSpace ℝ (Fin 2)`, the chirality operator `Γ = i c(e₀) c(e₁)` is `-σ₁`. -/
theorem liftBaseChange_pauliPlaneClifford_complexVolume :
    liftBaseChange ℂ (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
        pauliPlaneClifford
        (complexVolume (-LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin 2))))
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation) =
      -Matrix.toEuclideanLin (TauCeti.pauli ![1, 0, 0]) := by
  rw [liftBaseChange_complexVolume_eq_of_neg_norm_sq pauliPlaneClifford _
    isGeometricClifford_pauliPlaneClifford.map_eq_neg_norm_sq (EuclideanSpace.basisFun (Fin 2) ℝ)
    rfl]
  simp only [show (2 + 1) / 2 = 1 from rfl, List.finRange_succ, List.finRange_zero, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one, EuclideanSpace.basisFun_apply,
    Fin.succ_zero_eq_one, pauliPlaneClifford_single_zero_mul_single_one, smul_smul,
    Complex.I_mul_I, neg_one_smul]

end PauliPlane

section SpinorWitness

/-- **Every complex spinor module admits a geometric Hermitian inner product**: for a
finite-dimensional Euclidean space `V` with `Q v = -‖v‖²` and any complex algebra isomorphism
`ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S`, there exists an
`InnerProductSpace.Core ℂ S` making the restricted real action
`(liftBaseChange ℂ Q).symm ρ.toAlgHom` satisfy `AlgHom.IsGeometricClifford`. -/
theorem exists_innerProductCore_isGeometricClifford
    {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Q : QuadraticForm ℝ V} [AddCommGroup S] [Module ℂ S]
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S) :
    ∃ c : InnerProductSpace.Core ℂ S,
      letI : NormedAddCommGroup S := c.toNormedAddCommGroup
      letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore c.toCore
      ((liftBaseChange ℂ Q).symm ρ.toAlgHom).IsGeometricClifford := by
  obtain ⟨H, hpos, hdef, hH⟩ := exists_sesqForm_map_eq_map_conjStar hQ ρ
  let c : InnerProductSpace.Core ℂ S :=
    { inner := fun x y ↦ H x y
      conj_inner_symm := fun x y ↦ hpos.isSymm.eq y x
      re_inner_nonneg := fun x ↦ (RCLike.nonneg_iff.mp (hpos.isNonneg.nonneg x)).1
      add_left := fun x y z ↦ by simp
      smul_left := fun x y r ↦ by simp
      definite := fun x hx ↦ by_contra fun hne ↦ hdef x hne hx }
  refine ⟨c, ?_⟩
  let : NormedAddCommGroup S := c.toNormedAddCommGroup
  let : InnerProductSpace ℂ S := InnerProductSpace.ofCore c.toCore
  refine ⟨hQ, fun v x y ↦ ?_⟩
  have hinner (p q : S) : inner ℂ p q = H p q := rfl
  rw [hinner, hinner]
  simpa using hH (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) x y

end SpinorWitness

section NegativeControls

/-- **Negative control for the metric-form clause**: on any seminormed real module containing a
vector of nonzero norm, no real algebra map out of the exterior algebra `CliffordAlgebra 0`
satisfies `AlgHom.IsGeometricClifford`. -/
theorem not_isGeometricClifford_zero_of_norm_ne_zero
    {V S : Type*} [SeminormedAddCommGroup V] [Module ℝ V]
    [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]
    {v : V} (hv : ‖v‖ ≠ 0) (ρ : CliffordAlgebra (0 : QuadraticForm ℝ V) →ₐ[ℝ] Module.End ℂ S) :
    ¬ ρ.IsGeometricClifford := fun hρ ↦ by
  have h := hρ.map_eq_neg_norm_sq v
  have h0 : ‖v‖ = 0 := by simpa using h.symm
  exact hv h0

/-- **Negative control for the skew-Hermitian clause**: on `ℂ`, the identity operator `1` is not
skew-Hermitian (`⟪1, 1⟫_ℂ = 1 ≠ -1 = -⟪1, 1⟫_ℂ`). -/
theorem not_skewHermitian_one :
    ¬ ∀ x y : ℂ, inner ℂ ((1 : Module.End ℂ ℂ) x) y = -inner ℂ x ((1 : Module.End ℂ ℂ) y) := by
  intro h
  have h1 := h 1 1
  norm_num at h1

end NegativeControls

end CliffordAlgebra
