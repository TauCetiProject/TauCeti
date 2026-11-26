/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex
public import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Complex
-- Private: spinor-metric existence is used only in proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Spinor

/-!
# The geometric convention for real Clifford actions

Let `V` be a real inner product space (or seminormed real module), `Q` a quadratic form on `V`, and
`S` a complex inner product space with a real algebra map `ρ : Cℓ(V, Q) → End_ℂ(S)`; write
`c(v) = ρ (ι Q v)` for Clifford multiplication by `v`. The **geometric convention** for such an
action, the one used for Clifford modules and Dirac operators on Riemannian manifolds, has two
clauses:

* the quadratic form is minus the squared norm, `Q v = -‖v‖²`, so that `c(v)² = -‖v‖²`;
* every `c(v)` is skew-Hermitian, `⟪c(v) s, t⟫_ℂ = -⟪s, c(v) t⟫_ℂ`.

The skew-Hermitian clause is stated through inner products without assuming separation or
finite-dimensionality of `S` (and `IsGeometricClifford` itself requires only a seminorm on `V`), so
it makes sense on modules of any dimension. The positive convention `c(v)² = +‖v‖²` is excluded by
the first clause: for `V = ℝ` and `S = ℂ`, the operator `c(e) = i` squares to `-1` and is
skew-Hermitian, while `c(e) = 1` squares to `+1` and is Hermitian.

This file records the geometric convention as the predicate `AlgHom.IsGeometricClifford` and
derives:

* the polarized Clifford relation `c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫`, norm scaling
  `‖c(v) ψ‖ = ‖v‖ ‖ψ‖` in arbitrary dimension, and real-part inner-product identities;
* the unit orthogonal 2-plane calculus (`(c(e₁) c(e₂))² = -1`, symmetry and involution property of
  `i c(e₁) c(e₂)`, and `SO(2)` rotation invariance of `c(e₁) c(e₂)`);
* the equivalent adjoint form `c(v)* = -c(v)` on a finite-dimensional module and the
  `*`-representation property of the complex-linear extension `CliffordAlgebra.liftBaseChange`;
* stability of `AlgHom.IsGeometricClifford` under the graded complex tensor product
  `AlgHom.cliffordComplexProdLp`;
* existence of an `InnerProductSpace.Core ℂ S` making the real restriction of any complex spinor
  algebra isomorphism satisfy `AlgHom.IsGeometricClifford`.

Concrete low-dimensional models and clause-independence counterexamples are collected in
`TauCeti/Examples/LinearAlgebra/CliffordAlgebra/Hermitian/Geometric.lean`. Self-adjointness of the
chirality operator `Γ` and orthogonality of the half-spinor eigenspaces `S⁺ ⟂ S⁻` live in
`TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/RealAction.lean`.

## Main definitions

* `AlgHom.IsGeometricClifford ρ`: `Q v = -‖v‖²` and every `c(v)` is skew-Hermitian.

## Main results

* `AlgHom.isGeometricClifford_iff`, `AlgHom.isGeometricClifford_iff_inner`,
  `AlgHom.isGeometricClifford_iff_adjoint`,
  `AlgHom.not_isGeometricClifford_zero_of_norm_ne_zero`: characterizations of `IsGeometricClifford`
  and obstruction for the zero quadratic form on nonzero-norm modules.
* `AlgHom.IsGeometricClifford.map_ι_mul_map_ι_add_swap`,
  `AlgHom.IsGeometricClifford.map_ι_apply_map_ι_apply_add_swap`: the polarized Clifford relation
  `c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫`.
* `AlgHom.IsGeometricClifford.norm_map_ι_apply`,
  `AlgHom.IsGeometricClifford.re_inner_map_ι_apply_map_ι_apply`,
  `AlgHom.IsGeometricClifford.re_inner_map_ι_apply_self`: norm scaling and real inner-product
  identities in arbitrary dimension.
* `AlgHom.IsGeometricClifford.map_ι_mul_map_ι_mul_self_of_orthonormal`,
  `AlgHom.IsGeometricClifford.I_smul_map_ι_mul_map_ι_sq_of_orthonormal`,
  `AlgHom.IsGeometricClifford.isSymmetric_I_smul_map_ι_mul_map_ι_of_inner_eq_zero`,
  `AlgHom.IsGeometricClifford.map_ι_cos_sin_mul_of_orthonormal`: unit orthogonal 2-plane
  computations, symmetry of `i • (c(e₁) c(e₂))`, and `SO(2)` rotation invariance of `c(e₁) c(e₂)`.
* `AlgHom.IsGeometricClifford.inner_liftBaseChange_apply_left`: the complex-linear extension
  `ρ_ℂ = CliffordAlgebra.liftBaseChange ℂ Q ρ` of a geometric action satisfies
  `⟪ρ_ℂ(a) s, t⟫ = ⟪s, ρ_ℂ(conjStar a) t⟫` for `CliffordAlgebra.conjStar`, on a module of any
  dimension.
* `AlgHom.IsGeometricClifford.cliffordComplexProdLp`: the graded complex tensor product of geometric
  Clifford actions preserves `IsGeometricClifford`.
* `CliffordAlgebra.exists_innerProductCore_isGeometricClifford`: every complex spinor algebra
  isomorphism over `Q v = -‖v‖²` admits an `InnerProductSpace.Core ℂ S` making its real restriction
  satisfy `IsGeometricClifford`.

## References

* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Definition 12.1.10, p. 626, and
  Definition 12.1.64, pp. 653–654.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

open CliffordAlgebra Module
open scoped InnerProductSpace TensorProduct

namespace AlgHom

section Seminormed

variable {V S : Type*} [SeminormedAddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]

/-- **The geometric convention for a real Clifford action** `ρ : Cℓ(V, Q) → End_ℂ(S)`: the
quadratic form is minus the squared norm, `Q v = -‖v‖²`, and Clifford multiplication
`c(v) = ρ (ι Q v)` by every vector is skew-Hermitian. Neither finite-dimensionality of `V` or `S`
nor separation of the seminorms is required. Then `c(v)² = -‖v‖²` and
`c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫` (`AlgHom.IsGeometricClifford.map_ι_mul_map_ι_add_swap`). -/
structure IsGeometricClifford (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) : Prop where
  /-- The quadratic form is minus the squared norm. -/
  apply_eq_neg_norm_sq : ∀ v, Q v = -‖v‖ ^ 2
  /-- Clifford multiplication by a vector is skew-Hermitian. -/
  inner_map_ι_apply_left : ∀ (v : V) (s t : S), ⟪ρ (ι Q v) s, t⟫_ℂ = -⟪s, ρ (ι Q v) t⟫_ℂ

/-- Unpacking characterization of `AlgHom.IsGeometricClifford`. -/
theorem isGeometricClifford_iff {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} :
    ρ.IsGeometricClifford ↔
      (∀ v : V, Q v = -‖v‖ ^ 2) ∧
        ∀ (v : V) (s t : S), ⟪ρ (ι Q v) s, t⟫_ℂ = -⟪s, ρ (ι Q v) t⟫_ℂ :=
  ⟨fun h ↦ ⟨h.apply_eq_neg_norm_sq, h.inner_map_ι_apply_left⟩, fun h ↦ ⟨h.1, h.2⟩⟩

namespace IsGeometricClifford

variable {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
include hρ

/-- Moving `c(v)` from the right slot to the left slot of the complex inner product negates it. -/
theorem inner_map_ι_apply_right (v : V) (s t : S) :
    ⟪s, ρ (ι Q v) t⟫_ℂ = -⟪ρ (ι Q v) s, t⟫_ℂ := by
  rw [hρ.inner_map_ι_apply_left, neg_neg]

/-- Every element `a` of the real Clifford algebra satisfies `⟪ρ a s, t⟫ = ⟪s, ρ (star a) t⟫`,
where `star` is Mathlib's Clifford conjugation `reverse ∘ involute`. -/
theorem inner_map_eq_map_star (a : CliffordAlgebra Q) (s t : S) :
    ⟪ρ a s, t⟫_ℂ = ⟪s, ρ (star a) t⟫_ℂ :=
  sesqForm_map_eq_map_star ρ (innerₛₗ ℂ) (fun v x y ↦ hρ.inner_map_ι_apply_left v x y) a s t

/-- **A geometric action is a `*`-representation**: under the geometric convention, the
complex-linear extension `ρ_ℂ` satisfies `⟪ρ_ℂ(a) s, t⟫ = ⟪s, ρ_ℂ(conjStar a) t⟫`, on a module
of any dimension. -/
theorem inner_liftBaseChange_apply_left (a : CliffordAlgebra (Q.baseChange ℂ)) (s t : S) :
    ⟪liftBaseChange ℂ Q ρ a s, t⟫_ℂ = ⟪s, liftBaseChange ℂ Q ρ (conjStar Q a) t⟫_ℂ :=
  (inner_liftBaseChange_eq_conjStar_iff ρ).mpr hρ.inner_map_ι_apply_left a s t

/-- In the geometric convention `c(v)² = -‖v‖²`. -/
theorem map_ι_mul_self (v : V) : ρ (ι Q v) * ρ (ι Q v) = ((-‖v‖ ^ 2 : ℝ) : ℂ) • 1 := by
  rw [map_ι_mul_map_ι, hρ.apply_eq_neg_norm_sq]

/-- Pointwise diagonal Clifford relation: `c(v) (c(v) ψ) = -‖v‖² • ψ`. -/
theorem map_ι_apply_map_ι_apply (v : V) (ψ : S) :
    ρ (ι Q v) (ρ (ι Q v) ψ) = ((-‖v‖ ^ 2 : ℝ) : ℂ) • ψ := by
  rw [CliffordAlgebra.map_ι_apply_map_ι_apply, hρ.apply_eq_neg_norm_sq]

/-- **Norm scaling** in the geometric convention (in arbitrary dimension): `‖c(v) ψ‖ = ‖v‖ ‖ψ‖`. -/
theorem norm_map_ι_apply (v : V) (ψ : S) : ‖ρ (ι Q v) ψ‖ = ‖v‖ * ‖ψ‖ :=
  norm_map_ι_apply_of_inner_left_eq_neg hρ.apply_eq_neg_norm_sq hρ.inner_map_ι_apply_left v ψ

/-- Clifford multiplication by a real vector sends every spinor `ψ` to a spinor whose complex inner
product with `ψ` is purely imaginary: `Re ⟪c(v) ψ, ψ⟫_ℂ = 0`. -/
theorem re_inner_map_ι_apply_self (v : V) (ψ : S) :
    (⟪ρ (ι Q v) ψ, ψ⟫_ℂ).re = 0 := by
  have h := congrArg (RCLike.re (K := ℂ)) (hρ.inner_map_ι_apply_left v ψ ψ)
  conv_rhs at h => rw [map_neg, inner_re_symm]
  simp only [RCLike.re_to_complex] at h
  linarith

/-- Clifford multiplication by a unit vector squares to `-1`. -/
theorem map_ι_mul_self_of_norm_eq_one {v : V} (h : ‖v‖ = 1) : ρ (ι Q v) * ρ (ι Q v) = -1 := by
  simp [hρ.map_ι_mul_self, h]

/-- Clifford multiplication by a real unit vector preserves norms: `‖c(u) ψ‖ = ‖ψ‖`. -/
theorem norm_map_ι_apply_of_norm_eq_one {u : V} (hu : ‖u‖ = 1) (ψ : S) :
    ‖ρ (ι Q u) ψ‖ = ‖ψ‖ := by
  rw [hρ.norm_map_ι_apply, hu, one_mul]

end IsGeometricClifford

/-- **Negative control for the metric-form clause**: on any seminormed real module containing a
vector of nonzero norm, no real algebra map out of the exterior algebra `CliffordAlgebra 0`
satisfies `AlgHom.IsGeometricClifford`. -/
theorem not_isGeometricClifford_zero_of_norm_ne_zero {v : V} (hv : ‖v‖ ≠ 0)
    (ρ : CliffordAlgebra (0 : QuadraticForm ℝ V) →ₐ[ℝ] Module.End ℂ S) :
    ¬ ρ.IsGeometricClifford := fun hρ ↦ by
  have h := hρ.apply_eq_neg_norm_sq v
  have h0 : ‖v‖ = 0 := by simpa using h.symm
  exact hv h0

end Seminormed

section RealInner

variable {V S : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  [SeminormedAddCommGroup S] [InnerProductSpace ℂ S]

/-- On a real inner product space, `IsGeometricClifford` is equivalently `Q v = -⟪v, v⟫_ℝ` together
with skew-Hermitianness of `c(v)`. -/
theorem isGeometricClifford_iff_inner {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} :
    ρ.IsGeometricClifford ↔
      (∀ v : V, Q v = -⟪v, v⟫_ℝ) ∧
        ∀ (v : V) (s t : S), ⟪ρ (ι Q v) s, t⟫_ℂ = -⟪s, ρ (ι Q v) t⟫_ℂ := by
  simp_rw [isGeometricClifford_iff, real_inner_self_eq_norm_sq]

namespace IsGeometricClifford

variable {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
include hρ

/-- **The polarized Clifford relation** of the geometric convention:
`c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫`. -/
theorem map_ι_mul_map_ι_add_swap (v w : V) :
    ρ (ι Q v) * ρ (ι Q w) + ρ (ι Q w) * ρ (ι Q v) = ((-2 * ⟪v, w⟫_ℝ : ℝ) : ℂ) • 1 := by
  rw [CliffordAlgebra.map_ι_mul_map_ι_add_swap,
    QuadraticMap.polar_eq_neg_two_inner hρ.apply_eq_neg_norm_sq]

/-- Pointwise polarized Euclidean Clifford relation:
`c(v) (c(w) ψ) + c(w) (c(v) ψ) = -2 ⟪v, w⟫_ℝ • ψ`. -/
theorem map_ι_apply_map_ι_apply_add_swap (v w : V) (ψ : S) :
    ρ (ι Q v) (ρ (ι Q w) ψ) + ρ (ι Q w) (ρ (ι Q v) ψ) = ((-2 * ⟪v, w⟫_ℝ : ℝ) : ℂ) • ψ := by
  rw [CliffordAlgebra.map_ι_apply_map_ι_apply_add_swap,
    QuadraticMap.polar_eq_neg_two_inner hρ.apply_eq_neg_norm_sq]

/-- Clifford multiplications by orthogonal vectors anticommute. -/
theorem map_ι_mul_map_ι_comm_of_inner_eq_zero {v w : V} (h : ⟪v, w⟫_ℝ = 0) :
    ρ (ι Q v) * ρ (ι Q w) = -(ρ (ι Q w) * ρ (ι Q v)) :=
  map_ι_mul_map_ι_comm_of_isOrtho ρ
    ((QuadraticMap.isOrtho_iff_inner_eq_zero hρ.apply_eq_neg_norm_sq).2 h)

/-- Pointwise anticommutation of orthogonal vectors: `c(v) (c(w) ψ) = -c(w) (c(v) ψ)`. -/
theorem map_ι_apply_map_ι_apply_comm_of_inner_eq_zero {v w : V} (h : ⟪v, w⟫_ℝ = 0) (ψ : S) :
    ρ (ι Q v) (ρ (ι Q w) ψ) = -ρ (ι Q w) (ρ (ι Q v) ψ) :=
  map_ι_apply_map_ι_apply_comm_of_isOrtho ρ
    ((QuadraticMap.isOrtho_iff_inner_eq_zero hρ.apply_eq_neg_norm_sq).2 h) ψ

/-- **Polarized inner-product identity**: `Re ⟪c(v) ψ, c(w) ψ⟫_ℂ = ⟪v, w⟫_ℝ ‖ψ‖²`. -/
theorem re_inner_map_ι_apply_map_ι_apply (v w : V) (ψ : S) :
    (⟪ρ (ι Q v) ψ, ρ (ι Q w) ψ⟫_ℂ).re = ⟪v, w⟫_ℝ * ‖ψ‖ ^ 2 := by
  rw [re_inner_map_ι_apply_map_ι_apply_of_inner_left_eq_neg hρ.inner_map_ι_apply_left,
    QuadraticMap.polar_eq_neg_two_inner hρ.apply_eq_neg_norm_sq]
  ring

/-- For orthogonal vectors `e₁, e₂`, the bivector operator `c(e₁) c(e₂)` is skew-Hermitian. -/
theorem inner_map_ι_mul_map_ι_left_of_inner_eq_zero {e₁ e₂ : V} (h₁₂ : ⟪e₁, e₂⟫_ℝ = 0) (s t : S) :
    ⟪(ρ (ι Q e₁) * ρ (ι Q e₂)) s, t⟫_ℂ = -⟪s, (ρ (ι Q e₁) * ρ (ι Q e₂)) t⟫_ℂ := by
  rw [mul_apply_eq_comp, hρ.inner_map_ι_apply_left, hρ.inner_map_ι_apply_left, neg_neg,
    ← mul_apply_eq_comp, hρ.map_ι_mul_map_ι_comm_of_inner_eq_zero (by rw [real_inner_comm, h₁₂]),
    LinearMap.neg_apply, inner_neg_right]

/-- For orthogonal vectors `e₁, e₂`, multiplying the bivector `c(e₁) c(e₂)` by `i` produces a
symmetric operator `i • (c(e₁) c(e₂))`. -/
theorem isSymmetric_I_smul_map_ι_mul_map_ι_of_inner_eq_zero {e₁ e₂ : V} (h₁₂ : ⟪e₁, e₂⟫_ℝ = 0) :
    (Complex.I • (ρ (ι Q e₁) * ρ (ι Q e₂))).IsSymmetric := fun s t ↦ by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
    Complex.conj_I, hρ.inner_map_ι_mul_map_ι_left_of_inner_eq_zero h₁₂, neg_mul_neg]

/-- **A unit orthogonal pair**: for orthonormal `e₁, e₂`, the product `c(e₁) c(e₂)` squares to
`-1`, so that `i c(e₁) c(e₂)` is an involution. -/
theorem map_ι_mul_map_ι_mul_self_of_orthonormal {e₁ e₂ : V} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h : ⟪e₁, e₂⟫_ℝ = 0) :
    ρ (ι Q e₁) * ρ (ι Q e₂) * (ρ (ι Q e₁) * ρ (ι Q e₂)) = -1 := by
  rw [← map_mul ρ, ← sq, ← map_pow, ι_mul_ι_sq_of_orthonormal hρ.apply_eq_neg_norm_sq h₁ h₂ h,
    map_neg, map_one]

/-- For an orthonormal pair `(e₁, e₂)`, the normalized plane chirality operator `i • (c(e₁) c(e₂))`
squares to `1`. -/
theorem I_smul_map_ι_mul_map_ι_sq_of_orthonormal {e₁ e₂ : V} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫_ℝ = 0) :
    (Complex.I • (ρ (ι Q e₁) * ρ (ι Q e₂))) ^ 2 = 1 := by
  rw [sq, smul_mul_smul_comm, Complex.I_mul_I,
    hρ.map_ι_mul_map_ι_mul_self_of_orthonormal he₁ he₂ h₁₂, neg_one_smul, neg_neg]

/-- `SO(2)` rotation invariance of the plane operator `c(e₁) c(e₂)`. -/
theorem map_ι_cos_sin_mul_of_orthonormal {e₁ e₂ : V} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫_ℝ = 0) (θ : ℝ) :
    ρ (ι Q (Real.cos θ • e₁ + Real.sin θ • e₂)) *
        ρ (ι Q ((-Real.sin θ) • e₁ + Real.cos θ • e₂)) =
      ρ (ι Q e₁) * ρ (ι Q e₂) := by
  rw [← map_mul ρ, ι_cos_sin_mul_of_orthonormal hρ.apply_eq_neg_norm_sq he₁ he₂ h₁₂, map_mul]

end IsGeometricClifford

end RealInner

section FiniteDimensional

variable {V S : Type*} [SeminormedAddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]

/-- **The adjoint form of the geometric convention**: on a finite-dimensional module, the
convention says that `Q v = -‖v‖²` and that `c(v)* = -c(v)` for every vector. -/
theorem isGeometricClifford_iff_adjoint {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} :
    ρ.IsGeometricClifford ↔
      (∀ v, Q v = -‖v‖ ^ 2) ∧ ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v) := by
  refine isGeometricClifford_iff.trans (and_congr_right' ⟨fun h v ↦ ?_, fun h v s t ↦ ?_⟩)
  · refine ((LinearMap.eq_adjoint_iff (-ρ (ι Q v)) (ρ (ι Q v))).2 fun s t ↦ ?_).symm
    rw [LinearMap.neg_apply, inner_neg_left, h v s t, neg_neg]
  · rw [← LinearMap.adjoint_inner_right, h v, LinearMap.neg_apply, inner_neg_right]

namespace IsGeometricClifford

variable {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
include hρ

/-- On a finite-dimensional module, `c(v)` has adjoint `-c(v)`. -/
theorem adjoint_map_ι (v : V) : LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v) :=
  (isGeometricClifford_iff_adjoint.mp hρ).2 v

/-- On a finite-dimensional module, `(ρ a).adjoint = ρ (star a)` for every
`a : CliffordAlgebra Q`. -/
theorem adjoint_map (a : CliffordAlgebra Q) : LinearMap.adjoint (ρ a) = ρ (star a) :=
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
  apply_eq_neg_norm_sq x := by
    rw [hQ, WithLp.ofLp_fst, WithLp.ofLp_snd, hρ₁.apply_eq_neg_norm_sq, hρ₂.apply_eq_neg_norm_sq,
      WithLp.prod_norm_sq_eq_of_L2]
    ring
  inner_map_ι_apply_left x t₁ t₂ := by
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
          inner_add_left, inner_add_right, TensorProduct.inner_tmul, hρ₁.inner_map_ι_apply_left,
          hρ₂.inner_map_ι_apply_left, hγsymm e₁ e₂]
        ring
      | add u v hu hv =>
        simp only [map_add, inner_add_right] at hu hv ⊢
        linear_combination hu + hv
    | add u v hu hv =>
      simp only [map_add, inner_add_left] at hu hv ⊢
      linear_combination hu + hv

end AlgHom

/-! ### Existence of geometric Hermitian inner products on complex spinor modules -/

namespace CliffordAlgebra

open scoped ComplexOrder in
/-- **Every complex spinor module admits a geometric Hermitian inner product**: for a
finite-dimensional Euclidean space `V` with `Q v = -‖v‖²` and any complex algebra isomorphism
`ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S`, there exists an
`InnerProductSpace.Core ℂ S` making the restricted real action
`(liftBaseChangeEquiv ℂ Q).symm ρ.toAlgHom` satisfy `AlgHom.IsGeometricClifford`. -/
theorem exists_innerProductCore_isGeometricClifford
    {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Q : QuadraticForm ℝ V} [AddCommGroup S] [Module ℂ S]
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S) :
    ∃ c : InnerProductSpace.Core ℂ S,
      letI : NormedAddCommGroup S := c.toNormedAddCommGroup
      letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore c.toCore
      ((liftBaseChangeEquiv ℂ Q).symm ρ.toAlgHom).IsGeometricClifford := by
  obtain ⟨H, hpos, hdef, hH⟩ := exists_sesqForm_map_eq_map_conjStar hQ ρ
  have hre : ∀ v, v ≠ 0 → 0 < RCLike.re (H v v) := fun v hv ↦
    (RCLike.pos_iff.mp ((hpos.isNonneg.nonneg v).lt_of_ne' (hdef v hv))).1
  refine ⟨hpos.isSymm.innerProductCore hre, ?_⟩
  let : NormedAddCommGroup S := (hpos.isSymm.innerProductCore hre).toNormedAddCommGroup
  let : InnerProductSpace ℂ S := InnerProductSpace.ofCore (hpos.isSymm.innerProductCore hre).toCore
  refine ⟨hQ, fun v x y ↦ ?_⟩
  rw [hpos.isSymm.inner_ofCore_innerProductCore hre,
    hpos.isSymm.inner_ofCore_innerProductCore hre]
  simpa using hH (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) x y

end CliffordAlgebra
