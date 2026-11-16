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
-- Private: real orthonormal-plane identities and spinor-metric existence are used only in proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Spinor
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

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
dot notation `ρ.IsGeometricClifford`), develops its unit-plane calculus, proves stability under the
graded complex tensor product `AlgHom.cliffordComplexProdLp`, connects it to the chirality operator
`liftBaseChange ℂ Q ρ (complexVolume Q o)`, and proves that any complex spinor algebra isomorphism
over `Q v = -‖v‖²` admits an `InnerProductSpace.Core ℂ S` making its real restriction satisfy
`AlgHom.IsGeometricClifford`. Concrete low-dimensional models and clause-independence
counterexamples are collected in
`TauCeti/Examples/LinearAlgebra/CliffordAlgebra/Hermitian/Geometric.lean`.

## Main definitions

* `AlgHom.IsGeometricClifford`: predicate on `ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S` combining
  `Q v = -‖v‖²` and `⟪c(v) x, y⟫_ℂ = -⟪x, c(v) y⟫_ℂ`.

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
* `AlgHom.IsGeometricClifford.map_ι_mul_map_ι_sq_of_orthonormal`,
  `AlgHom.IsGeometricClifford.I_smul_map_ι_mul_map_ι_sq_of_orthonormal`,
  `AlgHom.IsGeometricClifford.isSymmetric_I_smul_map_ι_mul_map_ι_of_inner_eq_zero`,
  `AlgHom.IsGeometricClifford.map_ι_cos_sin_mul_of_orthonormal`: unit orthogonal 2-plane squares,
  symmetry of `i • (c(e₁) c(e₂))`, and `SO(2)` rotation invariance of `c(e₁) c(e₂)`.
* `AlgHom.IsGeometricClifford.cliffordComplexProdLp`: the graded complex tensor product of geometric
  Clifford actions preserves `IsGeometricClifford`.
* `CliffordAlgebra.isSymmetric_liftBaseChange_complexVolume`,
  `CliffordAlgebra.isSelfAdjoint_liftBaseChange_complexVolume`,
  `AlgHom.IsGeometricClifford.isOrtho_eigenspace_liftBaseChange_complexVolume`,
  `AlgHom.IsGeometricClifford.norm_sq_eq_add_norm_sq_projection_complexVolume`: self-adjointness of
  the chirality operator `Γ` and orthogonality and Pythagorean norm splitting of `S = S⁺ ⊕ S⁻`.
* `CliffordAlgebra.exists_innerProductCore_isGeometricClifford`: every complex spinor algebra
  isomorphism over `Q v = -‖v‖²` admits an `InnerProductSpace.Core ℂ S` making its real restriction
  satisfy `IsGeometricClifford`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Chapter 12, §12.1 (Definition 12.1.10).
-/

public section

noncomputable section

open CliffordAlgebra Module
open scoped RealInnerProductSpace TensorProduct ComplexOrder

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
theorem inner_liftBaseChange_eq_conjStar (a : CliffordAlgebra (Q.baseChange ℂ)) (x y : S) :
    inner ℂ (liftBaseChange ℂ Q ρ a x) y = inner ℂ x (liftBaseChange ℂ Q ρ (conjStar Q a) y) :=
  (inner_liftBaseChange_eq_conjStar_iff ρ).mpr hρ.inner_map_ι_left a x y

/-- Diagonal Clifford relation in the geometric convention: `c(v)² = -‖v‖² • 1`. -/
theorem map_ι_mul_self (v : V) :
    ρ (ι Q v) * ρ (ι Q v) = ((-‖v‖ ^ 2 : ℝ) : ℂ) • 1 := by
  rw [map_ι_mul_map_ι, hρ.map_eq_neg_norm_sq]

/-- Pointwise diagonal Clifford relation: `c(v) (c(v) ψ) = -‖v‖² • ψ`. -/
theorem map_ι_apply_map_ι_apply (v : V) (ψ : S) :
    ρ (ι Q v) (ρ (ι Q v) ψ) = ((-‖v‖ ^ 2 : ℝ) : ℂ) • ψ := by
  rw [CliffordAlgebra.map_ι_apply_map_ι_apply, hρ.map_eq_neg_norm_sq]

/-- **Norm scaling** in the geometric convention (in arbitrary dimension): `‖c(v) ψ‖ = ‖v‖ ‖ψ‖`. -/
theorem norm_map_ι_apply (v : V) (ψ : S) : ‖ρ (ι Q v) ψ‖ = ‖v‖ * ‖ψ‖ :=
  norm_map_ι_apply_of_inner_left_eq_neg hρ.map_eq_neg_norm_sq hρ.inner_map_ι_left v ψ

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
    ρ (ι Q v) * ρ (ι Q w) = -(ρ (ι Q w) * ρ (ι Q v)) :=
  map_ι_mul_map_ι_of_isOrtho ρ
    ((QuadraticMap.isOrtho_iff_inner_eq_zero hρ.map_eq_neg_norm_sq).2 h)

/-- Pointwise anticommutation of orthogonal vectors: `c(v) (c(w) ψ) = -c(w) (c(v) ψ)`. -/
theorem map_ι_apply_map_ι_apply_of_inner_eq_zero {v w : V} (h : ⟪v, w⟫ = 0) (ψ : S) :
    ρ (ι Q v) (ρ (ι Q w) ψ) = -ρ (ι Q w) (ρ (ι Q v) ψ) :=
  map_ι_apply_map_ι_apply_of_isOrtho ρ
    ((QuadraticMap.isOrtho_iff_inner_eq_zero hρ.map_eq_neg_norm_sq).2 h) ψ

/-- **Polarized inner-product identity**: `Re ⟪c(v) ψ, c(w) ψ⟫_ℂ = ⟪v, w⟫_ℝ ‖ψ‖²`. -/
theorem re_inner_map_ι_apply_map_ι_apply (v w : V) (ψ : S) :
    (inner ℂ (ρ (ι Q v) ψ) (ρ (ι Q w) ψ)).re = ⟪v, w⟫ * ‖ψ‖ ^ 2 := by
  rw [re_inner_map_ι_apply_map_ι_apply_of_inner_left_eq_neg hρ.inner_map_ι_left,
    QuadraticMap.polar_eq_neg_two_mul_inner hρ.map_eq_neg_norm_sq]
  ring

/-- For orthogonal vectors `e₁, e₂`, the bivector operator `c(e₁) c(e₂)` is skew-Hermitian. -/
theorem inner_map_ι_mul_map_ι_left_of_inner_eq_zero {e₁ e₂ : V} (h₁₂ : ⟪e₁, e₂⟫ = 0) (x y : S) :
    inner ℂ ((ρ (ι Q e₁) * ρ (ι Q e₂)) x) y = -inner ℂ x ((ρ (ι Q e₁) * ρ (ι Q e₂)) y) := by
  rw [mul_apply_eq_comp, hρ.inner_map_ι_left, hρ.inner_map_ι_left, neg_neg, ← mul_apply_eq_comp,
    hρ.map_ι_mul_map_ι_of_inner_eq_zero (by rw [real_inner_comm, h₁₂]), LinearMap.neg_apply,
    inner_neg_right]

/-- For orthogonal vectors `e₁, e₂`, multiplying the bivector `c(e₁) c(e₂)` by `i` produces a
symmetric operator `i • (c(e₁) c(e₂))`. -/
theorem isSymmetric_I_smul_map_ι_mul_map_ι_of_inner_eq_zero {e₁ e₂ : V} (h₁₂ : ⟪e₁, e₂⟫ = 0) :
    (Complex.I • (ρ (ι Q e₁) * ρ (ι Q e₂))).IsSymmetric := fun x y ↦ by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
    Complex.conj_I, hρ.inner_map_ι_mul_map_ι_left_of_inner_eq_zero h₁₂, neg_mul_neg]

/-- For an orthonormal pair `(e₁, e₂)`, the unnormalized plane product `c(e₁) c(e₂)` squares to
`-1` (so without the factor `i` it has eigenvalues `±i`, not `±1`). -/
theorem map_ι_mul_map_ι_sq_of_orthonormal {e₁ e₂ : V} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫ = 0) :
    (ρ (ι Q e₁) * ρ (ι Q e₂)) ^ 2 = -1 := by
  rw [← map_mul ρ, ← map_pow, ι_mul_ι_sq_of_orthonormal hρ.map_eq_neg_norm_sq he₁ he₂ h₁₂,
    map_neg, map_one]

/-- For an orthonormal pair `(e₁, e₂)`, the normalized plane chirality operator `i • (c(e₁) c(e₂))`
squares to `1`. -/
theorem I_smul_map_ι_mul_map_ι_sq_of_orthonormal {e₁ e₂ : V} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫ = 0) :
    (Complex.I • (ρ (ι Q e₁) * ρ (ι Q e₂))) ^ 2 = 1 := by
  rw [sq, smul_mul_smul_comm, Complex.I_mul_I, ← sq,
    hρ.map_ι_mul_map_ι_sq_of_orthonormal he₁ he₂ h₁₂, neg_one_smul, neg_neg]

/-- `SO(2)` rotation invariance of the plane operator `c(e₁) c(e₂)`. -/
theorem map_ι_cos_sin_mul_of_orthonormal {e₁ e₂ : V} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫ = 0) (θ : ℝ) :
    ρ (ι Q (Real.cos θ • e₁ + Real.sin θ • e₂)) *
        ρ (ι Q ((-Real.sin θ) • e₁ + Real.cos θ • e₂)) =
      ρ (ι Q e₁) * ρ (ι Q e₂) := by
  rw [← map_mul ρ, ι_cos_sin_mul_of_orthonormal hρ.map_eq_neg_norm_sq he₁ he₂ h₁₂, map_mul]

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

/-! ### Graded complex tensor product of geometric Clifford actions -/

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
    rw [hQ, WithLp.ofLp_fst, WithLp.ofLp_snd, hρ₁.map_eq_neg_norm_sq, hρ₂.map_eq_neg_norm_sq,
      WithLp.prod_norm_sq_eq_of_L2]
    ring
  inner_map_ι_left x t₁ t₂ := by
    -- `TensorProduct.instInnerProductSpace` and `TensorProduct` equip `E ⊗[ℂ] F` with `Module`
    -- instances defeq at `default` but not `implicit` transparency, blocking `rw`'s `kabstract`.
    have h := cliffordComplexProdLp_ι hQ ρ₁ γ hγ hγρ ρ₂ x
    suffices inner ℂ (((ρ₁ (ι Q₁ x.fst)).rTensor F + TensorProduct.map γ (ρ₂ (ι Q₂ x.snd))) t₁)
          t₂ =
        -inner ℂ t₁ (((ρ₁ (ι Q₁ x.fst)).rTensor F + TensorProduct.map γ (ρ₂ (ι Q₂ x.snd))) t₂) from
      (congrArg (inner ℂ · t₂) (LinearMap.congr_fun h t₁)).trans
        (this.trans (congrArg (-inner ℂ t₁ ·) (LinearMap.congr_fun h.symm t₂)))
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

end AlgHom

/-! ### Self-adjointness of the chirality operator and orthogonal half-spin splitting -/

namespace CliffordAlgebra

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

/-! ### Existence of geometric Hermitian inner products on complex spinor modules -/

namespace CliffordAlgebra

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
  refine ⟨hpos.toInnerProductCore hdef, ?_⟩
  let : NormedAddCommGroup S := (hpos.toInnerProductCore hdef).toNormedAddCommGroup
  let : InnerProductSpace ℂ S := InnerProductSpace.ofCore (hpos.toInnerProductCore hdef).toCore
  refine ⟨hQ, fun v x y ↦ ?_⟩
  rw [hpos.inner_ofCore_toInnerProductCore hdef, hpos.inner_ofCore_toInnerProductCore hdef]
  simpa using hH (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) x y

end CliffordAlgebra
