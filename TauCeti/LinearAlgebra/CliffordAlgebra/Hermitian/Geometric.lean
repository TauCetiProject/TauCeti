/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex
public import TauCeti.LinearAlgebra.CliffordAlgebra.Module.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod
public import TauCeti.LinearAlgebra.CliffordAlgebra.Zero
public import TauCeti.LinearAlgebra.Matrix.Pauli
-- Private: used only inside proofs for orthogonality of orthonormal bases wrt `-‖v‖²` and for the
-- `±1`-eigenspace splitting of an involution over a ring where `2` is a unit.
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.Eigenspace.Separation

/-!
# Geometric Clifford actions on Hermitian modules and their chirality operator

In spin geometry on a Riemannian manifold, a fibre `V` of the tangent bundle acts on a complex
Hermitian vector space `S` through a real algebra homomorphism `ρ : CliffordAlgebra Q →ₐ[ℝ]
Module.End ℂ S` satisfying the **geometric convention**:

* the quadratic form is minus the inner-product square, `Q v = -⟪v, v⟫_ℝ = -‖v‖²`;
* Clifford multiplication `c(v) = ρ (ι Q v)` by every real vector `v` is skew-Hermitian,
  `⟪c(v) x, y⟫_ℂ = -⟪x, c(v) y⟫_ℂ`.

Polarizing `c(v)² = Q v • 1` yields the operator anticommutator
`c(v) c(w) + c(w) c(v) = (-2 * ⟪v, w⟫_ℝ) • 1` together with the Hermitian identity
`⟪c(v) x, c(w) y⟫_ℂ + ⟪c(w) x, c(v) y⟫_ℂ = 2 ⟪v, w⟫_ℝ ⟪x, y⟫_ℂ` and norm scaling
`‖c(v) x‖ = ‖v‖ ‖x‖` without requiring `V` or `S` to be finite-dimensional.

Extending `ρ` complex-linearly via `AlgHom.cliffordBaseChange ℂ` produces a `ℂ`-algebra
homomorphism `ρ.cliffordBaseChange ℂ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S`.
Skew-Hermiticity of the real generators `c(v)` is equivalent to compatibility of
`ρ.cliffordBaseChange ℂ` with the conjugate-linear Clifford involution `CliffordAlgebra.conjStar`
on the entire complexified algebra. When `V` is oriented of dimension `n`, evaluating
`ρ.cliffordBaseChange ℂ` at `CliffordAlgebra.complexVolume Q o` expresses the chirality operator
directly in terms of the real action: in even dimension `n = 2ℓ`,

  `ρ.cliffordBaseChange ℂ (complexVolume Q o) = i ^ ℓ • ρ (volumeElement Q o)
    = i ^ ℓ • c(e₁) ⋯ c(e₂ₗ)`

for every positively oriented orthonormal basis `e` of `V`. On every geometric Clifford module this
chirality operator is a self-adjoint involution whose `+1` and `-1` eigenspaces are orthogonal
complements exchanged by odd Clifford multiplication, and it makes the graded tensor product
`CliffordAlgebra.complexProdTensor` preserve the geometric convention on `WithLp 2 (V × W)`.

Concrete witnesses are given in rank zero, on the real line (`c(1) = i` on `ℂ`), and on the
two-dimensional negative Pauli plane (`c(e₀) = i σ₃`, `c(e₁) = i σ₂`, chirality `-σ₁` on `ℂ²`).

## Main definitions

* `AlgHom.IsGeometricCliffordAction`: predicate on `ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S`
  recording `Q v = -⟪v, v⟫_ℝ` and skew-Hermiticity of `ρ (ι Q v)`.
* `TauCeti.realLineGeometricCliffordAction`: geometric Clifford action of `ℝ` on `ℂ` with
  `c(1) = i`.
* `TauCeti.negativePlanePauliAction`: geometric Clifford action of `EuclideanSpace ℝ (Fin 2)` on
  `EuclideanSpace ℂ (Fin 2)` with Pauli generators `i σ₃`, `i σ₂` and chirality `-σ₁`.

## Main results

* `AlgHom.map_ι_mul_map_ι_add_swap_eq_neg_two_inner`: polarized Clifford anticommutator
  `c(v) c(w) + c(w) c(v) = (-2 * ⟪v, w⟫_ℝ) • 1`.
* `AlgHom.map_ι_rot_mul_map_ι_rot`: rotation invariance of the oriented bivector `c(e₁) c(e₂)` of
  an orthonormal 2-plane.
* `AlgHom.IsGeometricCliffordAction.inner_map_ι_add_swap`,
  `AlgHom.IsGeometricCliffordAction.norm_map_ι_apply`: polarized inner-product identity and
  norm-scaling law without finite-dimensionality assumptions.
* `AlgHom.inner_cliffordBaseChange_eq_conjStar_iff`,
  `AlgHom.adjoint_cliffordBaseChange_eq_conjStar_iff`: `ρ.cliffordBaseChange ℂ` is a `conjStar`
  `*`-representation if and only if every `ρ (ι Q v)` is skew-Hermitian.
* `AlgHom.cliffordBaseChange_complexVolume_even`,
  `AlgHom.cliffordBaseChange_complexVolume_eq_prod_map_ι`: formulas for
  `ρ.cliffordBaseChange ℂ (complexVolume Q o)` in terms of `volumeElement Q o` and positively
  oriented orthonormal frames.
* `AlgHom.isCompl_eigenspace_cliffordBaseChange_complexVolume`,
  `AlgHom.IsGeometricCliffordAction.isSelfAdjoint_cliffordBaseChange_complexVolume`,
  `AlgHom.IsGeometricCliffordAction.inner_eq_zero_of_mem_eigenspace_complexVolume`: self-adjoint
  orthogonal half-spinor decomposition for real Clifford algebra maps.
* `AlgHom.IsGeometricCliffordAction.complexProdTensor`: graded tensor product preservation of the
  geometric convention.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§1 and 5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds* (2nd ed., 2007), §12.1.1,
  Definition 12.1.10.
-/

public section

noncomputable section

open CliffordAlgebra Module
open scoped RealInnerProductSpace TensorProduct ComplexConjugate EuclideanSpace

/-! ### Polarized Clifford relations on real inner product spaces -/

section Polarized

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}

/-- For `Q v = -‖v‖²` on a real inner product space, the polar bilinear form is `-2 ⟪v, w⟫_ℝ`. -/
theorem QuadraticMap.polar_eq_neg_two_inner (hQ : ∀ v, Q v = -‖v‖ ^ 2) (v w : V) :
    QuadraticMap.polar Q v w = -2 * ⟪v, w⟫ := by
  simp only [QuadraticMap.polar, hQ, norm_add_sq_real]
  ring

/-- For `Q v = -‖v‖²`, generators of `CliffordAlgebra Q` satisfy the polarized Clifford relation
`ι Q v * ι Q w + ι Q w * ι Q v = algebraMap ℝ _ (-2 * ⟪v, w⟫_ℝ)`. -/
theorem CliffordAlgebra.ι_mul_ι_add_swap_eq_neg_two_inner (hQ : ∀ v, Q v = -‖v‖ ^ 2) (v w : V) :
    ι Q v * ι Q w + ι Q w * ι Q v = algebraMap ℝ (CliffordAlgebra Q) (-2 * ⟪v, w⟫) := by
  rw [ι_mul_ι_add_swap, QuadraticMap.polar_eq_neg_two_inner hQ]

namespace AlgHom

section GeneralRing

variable {R M B : Type*} [CommRing R] [AddCommGroup M] [Module R M] {Q' : QuadraticForm R M}
  [Semiring B] [Algebra R B] (ρ : CliffordAlgebra Q' →ₐ[R] B)

/-- Polarized Clifford relation under any algebra homomorphism out of `CliffordAlgebra Q'`:
`c(v) c(w) + c(w) c(v) = polar Q' v w • 1`. -/
theorem map_ι_mul_map_ι_add_swap (v w : M) :
    ρ (ι Q' v) * ρ (ι Q' w) + ρ (ι Q' w) * ρ (ι Q' v) = QuadraticMap.polar Q' v w • 1 := by
  rw [← map_mul ρ, ← map_mul ρ, ← map_add ρ, ι_mul_ι_add_swap, commutes,
    Algebra.algebraMap_eq_smul_one]

end GeneralRing

section RealInnerSemiring

variable {B : Type*} [Semiring B] [Algebra ℝ B] (ρ : CliffordAlgebra Q →ₐ[ℝ] B)

/-- **Polarized Clifford relation** for `Q v = -‖v‖²`:
`c(v) c(w) + c(w) c(v) = (-2 * ⟪v, w⟫_ℝ) • 1`. -/
theorem map_ι_mul_map_ι_add_swap_eq_neg_two_inner (hQ : ∀ v, Q v = -‖v‖ ^ 2) (v w : V) :
    ρ (ι Q v) * ρ (ι Q w) + ρ (ι Q w) * ρ (ι Q v) = (-2 * ⟪v, w⟫) • 1 := by
  rw [ρ.map_ι_mul_map_ι_add_swap, QuadraticMap.polar_eq_neg_two_inner hQ]

end RealInnerSemiring

section RealInner

variable {B : Type*} [Ring B] [Algebra ℝ B] (ρ : CliffordAlgebra Q →ₐ[ℝ] B)

/-- Orthogonal vectors anticommute under any algebra map out of `CliffordAlgebra Q` when
`Q v = -‖v‖²`. -/
theorem map_ι_mul_map_ι_of_inner_eq_zero (hQ : ∀ v, Q v = -‖v‖ ^ 2) {v w : V} (hvw : ⟪v, w⟫ = 0) :
    ρ (ι Q v) * ρ (ι Q w) = -(ρ (ι Q w) * ρ (ι Q v)) := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [ρ.map_ι_mul_map_ι_add_swap_eq_neg_two_inner hQ, hvw, mul_zero, zero_smul]

/-- A unit vector acts by a square root of `-1` when `Q v = -‖v‖²`. -/
theorem map_ι_sq_of_norm_eq_one (hQ : ∀ v, Q v = -‖v‖ ^ 2) {e : V} (he : ‖e‖ = 1) :
    ρ (ι Q e) * ρ (ι Q e) = -1 := by
  rw [← map_mul ρ, ι_sq_scalar, hQ, he, one_pow, map_neg, map_one, map_neg, map_one]

/-- For an orthonormal pair `(e₁, e₂)` and `Q v = -‖v‖²`, the bivector `c(e₁) c(e₂)` squares to
`-1`. -/
theorem map_ι_mul_map_ι_sq_of_orthonormal (hQ : ∀ v, Q v = -‖v‖ ^ 2) {e₁ e₂ : V}
    (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) :
    (ρ (ι Q e₁) * ρ (ι Q e₂)) * (ρ (ι Q e₁) * ρ (ι Q e₂)) = -1 := by
  calc
    (ρ (ι Q e₁) * ρ (ι Q e₂)) * (ρ (ι Q e₁) * ρ (ι Q e₂))
      = ρ (ι Q e₁) * (ρ (ι Q e₂) * ρ (ι Q e₁)) * ρ (ι Q e₂) := by simp only [mul_assoc]
    _ = -(ρ (ι Q e₁) * ρ (ι Q e₁) * (ρ (ι Q e₂) * ρ (ι Q e₂))) := by
        rw [ρ.map_ι_mul_map_ι_of_inner_eq_zero hQ (by rw [real_inner_comm, h12])]
        simp only [mul_neg, neg_mul, mul_assoc]
    _ = -1 := by
        rw [ρ.map_ι_sq_of_norm_eq_one hQ he₁, ρ.map_ι_sq_of_norm_eq_one hQ he₂, neg_mul_neg,
          one_mul]

/-- **2-plane rotation invariance**: rotating an orthonormal pair `(e₁, e₂)` by angle `θ` preserves
the oriented Clifford product `c(e₁) c(e₂)` when `Q v = -‖v‖²`. -/
theorem map_ι_rot_mul_map_ι_rot (hQ : ∀ v, Q v = -‖v‖ ^ 2) {e₁ e₂ : V}
    (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫ = 0) (θ : ℝ) :
    ρ (ι Q (Real.cos θ • e₁ + Real.sin θ • e₂)) *
        ρ (ι Q (-Real.sin θ • e₁ + Real.cos θ • e₂)) =
      ρ (ι Q e₁) * ρ (ι Q e₂) := by
  have he₁_sq := ρ.map_ι_sq_of_norm_eq_one hQ he₁
  have he₂_sq := ρ.map_ι_sq_of_norm_eq_one hQ he₂
  have h21 : ρ (ι Q e₂) * ρ (ι Q e₁) = -(ρ (ι Q e₁) * ρ (ι Q e₂)) :=
    ρ.map_ι_mul_map_ι_of_inner_eq_zero hQ (by rw [real_inner_comm, h12])
  simp only [neg_smul, map_add, map_neg, map_smul, add_mul, mul_add, mul_neg,
    smul_mul_assoc, mul_smul_comm, smul_neg, he₁_sq, he₂_sq, h21]
  simp only [smul_add, smul_neg, neg_add_rev, neg_neg, smul_smul]
  calc
    (Real.sin θ * Real.sin θ) • (ρ (ι Q e₁) * ρ (ι Q e₂)) + (Real.sin θ * Real.cos θ) • (1 : B) +
        ((Real.cos θ * Real.cos θ) • (ρ (ι Q e₁) * ρ (ι Q e₂)) +
          -((Real.cos θ * Real.sin θ) • (1 : B)))
      = ((Real.sin θ * Real.cos θ) • (1 : B) - (Real.cos θ * Real.sin θ) • (1 : B)) +
          (Real.cos θ ^ 2 + Real.sin θ ^ 2) • (ρ (ι Q e₁) * ρ (ι Q e₂)) := by
        rw [add_smul, sq, sq, sub_eq_add_neg]
        abel
    _ = ρ (ι Q e₁) * ρ (ι Q e₂) := by
        rw [mul_comm (Real.sin θ) (Real.cos θ), sub_self, zero_add, Real.cos_sq_add_sin_sq,
          one_smul]

end RealInner

/-! ### The geometric convention predicate on real Clifford algebra maps -/

section GeometricConvention

variable {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S]

/-- **The geometric convention** for a real Clifford algebra homomorphism
`ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S` from a real inner product space `V` to a complex
inner product space `S`: the quadratic form satisfies `Q v = -⟪v, v⟫_ℝ`, and Clifford
multiplication `ρ (ι Q v)` by every real vector `v` is skew-Hermitian on `S`. -/
structure IsGeometricCliffordAction (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) : Prop where
  /-- The quadratic form is minus the inner-product square `Q v = -⟪v, v⟫_ℝ`. -/
  apply_eq_neg_inner_self : ∀ v : V, Q v = -⟪v, v⟫
  /-- Clifford multiplication by every real vector is skew-Hermitian on `S`. -/
  inner_map_ι_left : ∀ (v : V) (x y : S), inner ℂ (ρ (ι Q v) x) y = -inner ℂ x (ρ (ι Q v) y)

/-- Alternate constructor for `AlgHom.IsGeometricCliffordAction` from `Q v = -‖v‖²`. -/
theorem IsGeometricCliffordAction.of_norm_sq {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S}
    (hQ : ∀ v : V, Q v = -‖v‖ ^ 2)
    (hskew : ∀ (v : V) (x y : S), inner ℂ (ρ (ι Q v) x) y = -inner ℂ x (ρ (ι Q v) y)) :
    ρ.IsGeometricCliffordAction where
  apply_eq_neg_inner_self v := by rw [hQ, real_inner_self_eq_norm_sq]
  inner_map_ι_left := hskew

/-- Unfolding characterization of `AlgHom.IsGeometricCliffordAction`. -/
theorem isGeometricCliffordAction_iff {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} :
    ρ.IsGeometricCliffordAction ↔
      (∀ v : V, Q v = -⟪v, v⟫) ∧
        ∀ (v : V) (x y : S), inner ℂ (ρ (ι Q v) x) y = -inner ℂ x (ρ (ι Q v) y) :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

namespace IsGeometricCliffordAction

variable {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricCliffordAction)
include hρ

/-- Under the geometric convention, `Q v = -‖v‖²`. -/
theorem apply_eq_neg_norm_sq (v : V) : Q v = -‖v‖ ^ 2 := by
  rw [hρ.apply_eq_neg_inner_self, real_inner_self_eq_norm_sq]

/-- Moving Clifford multiplication to the left in the inner product introduces a minus sign. -/
theorem inner_map_ι_right (v : V) (x y : S) :
    inner ℂ x (ρ (ι Q v) y) = -inner ℂ (ρ (ι Q v) x) y := by
  rw [hρ.inner_map_ι_left, neg_neg]

/-- On a finite-dimensional Hermitian module, `AlgHom.IsGeometricCliffordAction` makes every
generator skew-adjoint for `LinearMap.adjoint`. -/
theorem adjoint_map_ι [FiniteDimensional ℂ S] (v : V) :
    (ρ (ι Q v)).adjoint = -ρ (ι Q v) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  simp [hρ.inner_map_ι_left]

/-- **Polarized Clifford operator relation** under `AlgHom.IsGeometricCliffordAction`:
`c(v) c(w) + c(w) c(v) = (-2 * ⟪v, w⟫_ℝ) • 1`. -/
theorem map_ι_mul_map_ι_add_swap (v w : V) :
    ρ (ι Q v) * ρ (ι Q w) + ρ (ι Q w) * ρ (ι Q v) = (-2 * ⟪v, w⟫) • 1 :=
  ρ.map_ι_mul_map_ι_add_swap_eq_neg_two_inner hρ.apply_eq_neg_norm_sq v w

/-- Pointwise polarized Clifford relation on spinors:
`c(v) (c(w) x) + c(w) (c(v) x) = (-2 * ⟪v, w⟫_ℝ) • x`. -/
theorem map_ι_apply_add_swap (v w : V) (x : S) :
    ρ (ι Q v) (ρ (ι Q w) x) + ρ (ι Q w) (ρ (ι Q v) x) = (-2 * ⟪v, w⟫) • x := by
  have h := LinearMap.congr_fun (hρ.map_ι_mul_map_ι_add_swap v w) x
  simpa only [LinearMap.add_apply, mul_apply_eq_comp, LinearMap.smul_apply,
    one_apply_eq_self] using h

/-- **Polarized Hermitian identity**: combining skew-Hermiticity with the polarized Clifford
relation gives `⟪c(v) x, c(w) y⟫_ℂ + ⟪c(w) x, c(v) y⟫_ℂ = 2 ⟪v, w⟫_ℝ ⟪x, y⟫_ℂ` without assuming
finite-dimensionality of `V` or `S`. -/
theorem inner_map_ι_add_swap (v w : V) (x y : S) :
    inner ℂ (ρ (ι Q v) x) (ρ (ι Q w) y) + inner ℂ (ρ (ι Q w) x) (ρ (ι Q v) y) =
      (2 * ⟪v, w⟫ : ℂ) * inner ℂ x y := by
  rw [hρ.inner_map_ι_right w, hρ.inner_map_ι_right v, ← neg_add, ← inner_add_left,
    add_comm (ρ (ι Q w) (ρ (ι Q v) x)), hρ.map_ι_apply_add_swap, ← Complex.coe_smul,
    inner_smul_left]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

/-- Applying `c(v)` to both arguments multiplies the inner product by `‖v‖²`, without assuming
finite-dimensionality of `S`. -/
theorem inner_map_ι_self (v : V) (x y : S) :
    inner ℂ (ρ (ι Q v) x) (ρ (ι Q v) y) = (‖v‖ ^ 2 : ℂ) * inner ℂ x y := by
  have h := hρ.inner_map_ι_add_swap v v x y
  rw [real_inner_self_eq_norm_sq] at h
  push_cast at h
  linear_combination (1 / 2 : ℂ) * h

/-- Under the geometric convention, Clifford multiplication scales norms by `‖v‖`:
`‖c(v) x‖ = ‖v‖ * ‖x‖`, without assuming finite-dimensionality of `S`. -/
theorem norm_map_ι_apply (v : V) (x : S) :
    ‖ρ (ι Q v) x‖ = ‖v‖ * ‖x‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  have h := congrArg RCLike.re (hρ.inner_map_ι_self v x x)
  simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, RCLike.re_to_complex,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re] at h
  linarith

end IsGeometricCliffordAction

/-- On a finite-dimensional complex inner product space, `AlgHom.IsGeometricCliffordAction` is
equivalent to `Q v = -⟪v, v⟫_ℝ` together with `(ρ (ι Q v)).adjoint = -ρ (ι Q v)`. -/
theorem isGeometricCliffordAction_iff_adjoint [FiniteDimensional ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} :
    ρ.IsGeometricCliffordAction ↔
      (∀ v : V, Q v = -⟪v, v⟫) ∧ ∀ v : V, (ρ (ι Q v)).adjoint = -ρ (ι Q v) := by
  refine ⟨fun h ↦ ⟨h.apply_eq_neg_inner_self, h.adjoint_map_ι⟩, fun ⟨hQ, hadj⟩ ↦ ⟨hQ, ?_⟩⟩
  intro v x y
  rw [← LinearMap.adjoint_inner_right, hadj, LinearMap.neg_apply, inner_neg_right]

end GeometricConvention

/-! ### Complexification and `conjStar` `*-`representations -/

section Complexification

variable {M S : Type*} [AddCommGroup M] [Module ℝ M] {Q' : QuadraticForm ℝ M}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S]

/-- For a real Clifford algebra map `ρ : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ S`, its
complex-linear extension `ρ.cliffordBaseChange ℂ` is compatible with `CliffordAlgebra.conjStar`
for the inner product if and only if every real generator `ρ (ι Q' v)` is skew-Hermitian. -/
theorem inner_cliffordBaseChange_eq_conjStar_iff
    (ρ : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ S) :
    (∀ (a : CliffordAlgebra (Q'.baseChange ℂ)) (x y : S),
        inner ℂ (ρ.cliffordBaseChange ℂ a x) y =
          inner ℂ x (ρ.cliffordBaseChange ℂ (conjStar Q' a) y)) ↔
      ∀ (v : M) (x y : S), inner ℂ (ρ (ι Q' v) x) y = -inner ℂ x (ρ (ι Q' v) y) := by
  refine ⟨fun h v x y ↦ ?_, fun h a x y ↦ ?_⟩
  · have hv := h (ι (Q'.baseChange ℂ) (1 ⊗ₜ v)) x y
    simpa [conjStar_ι_tmul] using hv
  · exact sesqForm_map_eq_map_conjStar (ρ.cliffordBaseChange ℂ) (innerₛₗ ℂ)
      (fun v x y ↦ by simpa [innerₛₗ_apply_apply] using h v x y) a x y

/-- On a finite-dimensional complex inner product space, `ρ.cliffordBaseChange ℂ` is a
`*`-representation for `CliffordAlgebra.conjStar` if and only if every real generator `ρ (ι Q' v)`
is skew-adjoint. -/
theorem adjoint_cliffordBaseChange_eq_conjStar_iff [FiniteDimensional ℂ S]
    (ρ : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ S) :
    (∀ a : CliffordAlgebra (Q'.baseChange ℂ),
        (ρ.cliffordBaseChange ℂ a).adjoint = ρ.cliffordBaseChange ℂ (conjStar Q' a)) ↔
      ∀ v : M, (ρ (ι Q' v)).adjoint = -ρ (ι Q' v) := by
  rw [CliffordAlgebra.adjoint_map_eq_map_conjStar_iff]
  simp

/-- A real Clifford algebra map `ρ` is compatible with Clifford conjugation `star` for the inner
product if and only if every real generator `ρ (ι Q' v)` is skew-Hermitian. -/
theorem inner_map_eq_map_star_iff (ρ : CliffordAlgebra Q' →ₐ[ℝ] Module.End ℂ S) :
    (∀ (a : CliffordAlgebra Q') (x y : S), inner ℂ (ρ a x) y = inner ℂ x (ρ (star a) y)) ↔
      ∀ (v : M) (x y : S), inner ℂ (ρ (ι Q' v) x) y = -inner ℂ x (ρ (ι Q' v) y) := by
  refine ⟨fun h v x y ↦ by simpa [star_ι] using h (ι Q' v) x y, fun h a x y ↦ ?_⟩
  have hc := (ρ.inner_cliffordBaseChange_eq_conjStar_iff.2 h) (ofBaseChangeAux ℂ Q' a) x y
  rw [conjStar_ofBaseChangeAux, ρ.cliffordBaseChange_ofBaseChangeAux,
    ρ.cliffordBaseChange_ofBaseChangeAux] at hc
  exact hc

end Complexification

section GeometricComplexification

variable {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S]

namespace IsGeometricCliffordAction

variable {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricCliffordAction)
include hρ

/-- Under the geometric convention, the complexified action `ρ.cliffordBaseChange ℂ` respects
`CliffordAlgebra.conjStar` in the inner product. -/
theorem inner_cliffordBaseChange_eq_conjStar (a : CliffordAlgebra (Q.baseChange ℂ)) (x y : S) :
    inner ℂ (ρ.cliffordBaseChange ℂ a x) y =
      inner ℂ x (ρ.cliffordBaseChange ℂ (conjStar Q a) y) :=
  (ρ.inner_cliffordBaseChange_eq_conjStar_iff.2 hρ.inner_map_ι_left) a x y

/-- Under the geometric convention, `ρ` respects Clifford conjugation `star` in the inner
product. -/
theorem inner_map_eq_map_star (a : CliffordAlgebra Q) (x y : S) :
    inner ℂ (ρ a x) y = inner ℂ x (ρ (star a) y) :=
  (ρ.inner_map_eq_map_star_iff.2 hρ.inner_map_ι_left) a x y

/-- On a finite-dimensional Hermitian module, the complexification of a geometric Clifford action is
a `*`-representation for `CliffordAlgebra.conjStar`. -/
theorem adjoint_cliffordBaseChange_eq_conjStar [FiniteDimensional ℂ S]
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    (ρ.cliffordBaseChange ℂ a).adjoint = ρ.cliffordBaseChange ℂ (conjStar Q a) :=
  (ρ.adjoint_cliffordBaseChange_eq_conjStar_iff.2 hρ.adjoint_map_ι) a

end IsGeometricCliffordAction

/-- On a finite-dimensional complex inner product space, `AlgHom.IsGeometricCliffordAction` is
equivalent to `Q v = -⟪v, v⟫_ℝ` together with `ρ.cliffordBaseChange ℂ` being a `*`-representation
for `CliffordAlgebra.conjStar`. -/
theorem isGeometricCliffordAction_iff_adjoint_cliffordBaseChange [FiniteDimensional ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} :
    ρ.IsGeometricCliffordAction ↔
      (∀ v : V, Q v = -⟪v, v⟫) ∧
        ∀ a, (ρ.cliffordBaseChange ℂ a).adjoint = ρ.cliffordBaseChange ℂ (conjStar Q a) := by
  rw [isGeometricCliffordAction_iff_adjoint, adjoint_cliffordBaseChange_eq_conjStar_iff]

/-- Restricting a complex Clifford algebra map `σ` along `AlgHom.cliffordBaseChangeEquiv` yields a
geometric Clifford action if and only if `Q v = -⟪v, v⟫_ℝ` and every embedded real generator
`σ (ι (Q.baseChange ℂ) (1 ⊗ₜ v))` is skew-Hermitian. -/
theorem isGeometricCliffordAction_cliffordBaseChangeEquiv_symm_iff
    (σ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S) :
    ((AlgHom.cliffordBaseChangeEquiv ℂ Q (Module.End ℂ S)).symm σ).IsGeometricCliffordAction ↔
      (∀ v : V, Q v = -⟪v, v⟫) ∧
        ∀ (v : V) (x y : S),
          inner ℂ (σ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) x) y =
            -inner ℂ x (σ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) y) := by
  simp [isGeometricCliffordAction_iff]

end GeometricComplexification

/-! ### The chirality operator for real Clifford algebra maps -/

section Chirality

variable [FiniteDimensional ℝ V]

section AnyDim

variable {n : ℕ} [Fact (finrank ℝ V = n)]

/-- Under the complexified action `ρ.cliffordBaseChange ℂ` of a real algebra map `ρ` into a complex
algebra `B`, the normalized complex volume element `complexVolume Q o` acts as
`i ^ ⌊(n + 1) / 2⌋ • ρ (volumeElement Q o)`. -/
theorem cliffordBaseChange_complexVolume {B : Type*} [Semiring B] [Algebra ℝ B] [Algebra ℂ B]
    [IsScalarTower ℝ ℂ B] (ρ : CliffordAlgebra Q →ₐ[ℝ] B) (o : Orientation ℝ V (Fin n)) :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) =
      Complex.I ^ ((n + 1) / 2) • ρ (volumeElement Q o) := by
  rw [complexVolume_def, map_smul, cliffordBaseChange_ofBaseChangeAux]

/-- For every positively oriented orthonormal basis `b` orthogonal for `Q`,
`ρ.cliffordBaseChange ℂ (complexVolume Q o) = i ^ ⌊(n + 1) / 2⌋ • ∏ᵢ ρ (ι Q (b i))`. -/
theorem cliffordBaseChange_complexVolume_eq {B : Type*} [Semiring B] [Algebra ℝ B] [Algebra ℂ B]
    [IsScalarTower ℝ ℂ B] (ρ : CliffordAlgebra Q →ₐ[ℝ] B) (o : Orientation ℝ V (Fin n))
    (b : OrthonormalBasis (Fin n) ℝ V) (hb : b.toBasis.orientation = o)
    (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) =
      Complex.I ^ ((n + 1) / 2) • ((List.finRange n).map fun i ↦ ρ (ι Q (b i))).prod := by
  rw [ρ.cliffordBaseChange_complexVolume o, volumeElement_eq o b hb hQb, map_list_prod,
    List.map_map, List.map_map]
  rfl

/-- For `Q v = -‖v‖²`, `ρ.cliffordBaseChange ℂ (complexVolume Q o)` squares to `1`. -/
@[simp]
theorem cliffordBaseChange_complexVolume_mul_self {B : Type*} [Semiring B] [Algebra ℝ B]
    [Algebra ℂ B] [IsScalarTower ℝ ℂ B] (ρ : CliffordAlgebra Q →ₐ[ℝ] B)
    (o : Orientation ℝ V (Fin n)) (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) *
      ρ.cliffordBaseChange ℂ (complexVolume Q o) = 1 := by
  rw [← map_mul, complexVolume_mul_self o hQ, map_one]

/-- In even dimension, `ρ.cliffordBaseChange ℂ (complexVolume Q o)` anticommutes with every real
generator `ρ (ι Q v)`. -/
theorem cliffordBaseChange_complexVolume_mul_map_ι {B : Type*} [Ring B] [Algebra ℝ B] [Algebra ℂ B]
    [IsScalarTower ℝ ℂ B] (ρ : CliffordAlgebra Q →ₐ[ℝ] B) (o : Orientation ℝ V (Fin n))
    (hn : Even n) (v : V) :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) * ρ (ι Q v) =
      -(ρ (ι Q v) * ρ.cliffordBaseChange ℂ (complexVolume Q o)) := by
  rw [← ρ.cliffordBaseChange_ι_one_tmul (A := ℂ) v, ← map_mul, ← map_mul,
    complexVolume_mul_ι_of_even o hn, map_neg]

/-- In rank zero, `ρ.cliffordBaseChange ℂ (complexVolume Q positiveOrientation) = 1`. -/
theorem cliffordBaseChange_complexVolume_positiveOrientation {B : Type*} [Semiring B] [Algebra ℝ B]
    [Algebra ℂ B] [IsScalarTower ℝ ℂ B] [Fact (finrank ℝ V = 0)] (ρ : CliffordAlgebra Q →ₐ[ℝ] B) :
    ρ.cliffordBaseChange ℂ
        (complexVolume Q (positiveOrientation : Orientation ℝ V (Fin 0))) = 1 := by
  rw [complexVolume_positiveOrientation, map_one]

/-- **Chirality splitting for a real Clifford algebra map**: when `Q v = -‖v‖²`, any complex module
`S` carrying `ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S` splits as the internal direct sum of the
`+1` and `-1` eigenspaces of `ρ.cliffordBaseChange ℂ (complexVolume Q o)`. When `S` is equipped with
`Module.compHom S (ρ.cliffordBaseChange ℂ).toRingHom`, these coincide definitionally with the `±1`
eigenspaces of `Algebra.lsmul ℂ ℂ S (complexVolume Q o)`. -/
theorem isCompl_eigenspace_cliffordBaseChange_complexVolume {S : Type*} [AddCommGroup S]
    [Module ℂ S] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) (o : Orientation ℝ V (Fin n))
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    IsCompl (Module.End.eigenspace (ρ.cliffordBaseChange ℂ (complexVolume Q o)) 1)
      (Module.End.eigenspace (ρ.cliffordBaseChange ℂ (complexVolume Q o)) (-1)) :=
  TauCeti.isCompl_eigenspace_one_neg_one two_ne_zero.isUnit fun s ↦ by
    rw [← mul_apply_eq_comp, ρ.cliffordBaseChange_complexVolume_mul_self o hQ, one_apply_eq_self]

/-- In even dimension, Clifford multiplication by any real vector `v` maps the `μ`-eigenspace of
`ρ.cliffordBaseChange ℂ (complexVolume Q o)` into its `-μ`-eigenspace; in particular it exchanges
`S⁺` (`μ = 1`) and `S⁻` (`μ = -1`). -/
theorem map_ι_mem_eigenspace_cliffordBaseChange_complexVolume_neg {S : Type*} [AddCommGroup S]
    [Module ℂ S] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) (o : Orientation ℝ V (Fin n))
    (hn : Even n) {μ : ℂ} {s : S}
    (hs : s ∈ Module.End.eigenspace (ρ.cliffordBaseChange ℂ (complexVolume Q o)) μ) (v : V) :
    ρ (ι Q v) s ∈ Module.End.eigenspace (ρ.cliffordBaseChange ℂ (complexVolume Q o)) (-μ) := by
  rw [Module.End.mem_eigenspace_iff] at hs ⊢
  have hanti := LinearMap.congr_fun (ρ.cliffordBaseChange_complexVolume_mul_map_ι o hn v) s
  simpa only [mul_apply_eq_comp, LinearMap.neg_apply, hs, map_smul, neg_smul] using hanti

end AnyDim

section EvenDim

variable {ℓ : ℕ} [Fact (finrank ℝ V = 2 * ℓ)]

/-- **Even-dimensional chirality formula**: on an oriented `2ℓ`-dimensional real inner product
space, `ρ.cliffordBaseChange ℂ (complexVolume Q o) = i ^ ℓ • ρ (volumeElement Q o)`. -/
theorem cliffordBaseChange_complexVolume_even {B : Type*} [Semiring B] [Algebra ℝ B] [Algebra ℂ B]
    [IsScalarTower ℝ ℂ B] (ρ : CliffordAlgebra Q →ₐ[ℝ] B) (o : Orientation ℝ V (Fin (2 * ℓ))) :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) = Complex.I ^ ℓ • ρ (volumeElement Q o) := by
  have hℓ : (2 * ℓ + 1) / 2 = ℓ := by omega
  rw [ρ.cliffordBaseChange_complexVolume o, hℓ]

/-- **Frame formula for the chirality operator**: for a `2ℓ`-dimensional real inner product space
with `Q v = -‖v‖²` and any positively oriented orthonormal basis `b`,
`ρ.cliffordBaseChange ℂ (complexVolume Q o) = i ^ ℓ • (c(b₀) ⋯ c(b_{2ℓ - 1}))`. -/
theorem cliffordBaseChange_complexVolume_eq_prod_map_ι {B : Type*} [Semiring B] [Algebra ℝ B]
    [Algebra ℂ B] [IsScalarTower ℝ ℂ B] (ρ : CliffordAlgebra Q →ₐ[ℝ] B)
    (o : Orientation ℝ V (Fin (2 * ℓ))) (b : OrthonormalBasis (Fin (2 * ℓ)) ℝ V)
    (hb : b.toBasis.orientation = o) (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    ρ.cliffordBaseChange ℂ (complexVolume Q o) =
      Complex.I ^ ℓ • ((List.finRange (2 * ℓ)).map fun i ↦ ρ (ι Q (b i))).prod := by
  have hℓ : (2 * ℓ + 1) / 2 = ℓ := by omega
  rw [ρ.cliffordBaseChange_complexVolume_eq o b hb (b.isOrthoᵢ_associated hQ), hℓ]

end EvenDim

section HermitianChirality

variable {n : ℕ} [Fact (finrank ℝ V = n)] {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S]

namespace IsGeometricCliffordAction

variable {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricCliffordAction)
include hρ

/-- **Self-adjointness of `Γ` in the inner product**: on any geometric Clifford module (without
assuming finite-dimensionality of `S`), `ρ.cliffordBaseChange ℂ (complexVolume Q o)` is symmetric
with respect to the complex inner product. -/
theorem inner_cliffordBaseChange_complexVolume_left (o : Orientation ℝ V (Fin n)) (x y : S) :
    inner ℂ (ρ.cliffordBaseChange ℂ (complexVolume Q o) x) y =
      inner ℂ x (ρ.cliffordBaseChange ℂ (complexVolume Q o) y) := by
  rw [hρ.inner_cliffordBaseChange_eq_conjStar, conjStar_complexVolume]

/-- **Self-adjointness of `Γ`**: on any finite-dimensional geometric Clifford module,
`ρ.cliffordBaseChange ℂ (complexVolume Q o)` is self-adjoint (`IsSelfAdjoint`). -/
theorem isSelfAdjoint_cliffordBaseChange_complexVolume [FiniteDimensional ℂ S]
    (o : Orientation ℝ V (Fin n)) :
    IsSelfAdjoint (ρ.cliffordBaseChange ℂ (complexVolume Q o)) := by
  rw [LinearMap.isSelfAdjoint_iff', hρ.adjoint_cliffordBaseChange_eq_conjStar,
    conjStar_complexVolume]

/-- **Orthogonality of the half-spinor eigenspaces**: on any geometric Clifford module, the `+1`
and `-1` eigenspaces of `ρ.cliffordBaseChange ℂ (complexVolume Q o)` are orthogonal. -/
theorem inner_eq_zero_of_mem_eigenspace_complexVolume (o : Orientation ℝ V (Fin n)) {x y : S}
    (hx : x ∈ Module.End.eigenspace (ρ.cliffordBaseChange ℂ (complexVolume Q o)) 1)
    (hy : y ∈ Module.End.eigenspace (ρ.cliffordBaseChange ℂ (complexVolume Q o)) (-1)) :
    inner ℂ x y = 0 := by
  rw [Module.End.mem_eigenspace_iff, one_smul] at hx
  rw [Module.End.mem_eigenspace_iff, neg_one_smul] at hy
  have h := hρ.inner_cliffordBaseChange_complexVolume_left o x y
  rw [hx, hy, inner_neg_right] at h
  linear_combination (1 / 2 : ℂ) * h

end IsGeometricCliffordAction

end HermitianChirality

end Chirality

/-! ### Graded tensor product of geometric Clifford actions -/

section TensorProduct

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₂ : QuadraticForm ℝ W} {Q₁₂ : QuadraticForm ℝ (WithLp 2 (V × W))}

/-- When `Q`, `Q₂`, and `Q₁₂` on `WithLp 2 (V × W)` are each minus the squared norm, `Q₁₂` splits
additively as `Q x.1 + Q₂ x.2`. -/
theorem _root_.QuadraticMap.apply_prod_eq_add_of_neg_norm_sq
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
    (hQ₁₂ : ∀ x, Q₁₂ x = -‖x‖ ^ 2) (x : WithLp 2 (V × W)) :
    Q₁₂ x = Q (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2 := by
  rw [hQ₁₂, hQ, hQ₂, WithLp.prod_norm_sq_eq_of_L2]
  dsimp only [WithLp.fst, WithLp.snd]
  ring

variable [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)]
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Auxiliary inner-product lemma: `TensorProduct.map f g` satisfies
`⟪(f ⊗ g) u, v⟫ = -⟪u, (f ⊗ g) v⟫` when `f` is symmetric and `g` is skew-Hermitian. -/
private theorem inner_tensorMap_of_symm_skew {f : Module.End ℂ E} {g : Module.End ℂ F}
    (hf : ∀ x x', inner ℂ (f x) x' = inner ℂ x (f x'))
    (hg : ∀ y y', inner ℂ (g y) y' = -inner ℂ y (g y'))
    (u v : E ⊗[ℂ] F) :
    inner ℂ (TensorProduct.map f g u) v = -inner ℂ u (TensorProduct.map f g v) := by
  induction u using TensorProduct.inductionOn generalizing v with
  | tmul x y =>
    induction v using TensorProduct.inductionOn with
    | tmul x' y' =>
      simp only [TensorProduct.map_tmul, TensorProduct.inner_tmul, hf, hg, mul_neg]
    | add v₁ v₂ hv₁ hv₂ =>
      simp only [map_add, inner_add_right, hv₁, hv₂, neg_add]
  | add u₁ u₂ hu₁ hu₂ =>
    simp only [map_add, inner_add_left, hu₁, hu₂, neg_add]

/-- **Graded tensor product of geometric Clifford actions**: if `ρ₁` is a geometric Clifford action
of an even-dimensional oriented space `(V, Q)` on `E` and `ρ₂` is a geometric Clifford action of
`(W, Q₂)` on `F`, then restricting `CliffordAlgebra.complexProdTensor` (graded by the chirality of
`V`) along `AlgHom.cliffordBaseChangeEquiv` to `CliffordAlgebra Q₁₂` on `WithLp 2 (V × W)` yields a
geometric Clifford action on `E ⊗[ℂ] F`. -/
theorem IsGeometricCliffordAction.complexProdTensor
    {ρ₁ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ E}
    {ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F}
    (hρ₁ : ρ₁.IsGeometricCliffordAction) (hρ₂ : ρ₂.IsGeometricCliffordAction)
    (o₁ : Orientation ℝ V (Fin n)) (hn : Even n)
    (hQ₁₂ : ∀ x, Q₁₂ x = -‖x‖ ^ 2) :
    ((AlgHom.cliffordBaseChangeEquiv ℂ Q₁₂ (Module.End ℂ (E ⊗[ℂ] F))).symm
      (CliffordAlgebra.complexProdTensor
        (QuadraticMap.apply_prod_eq_add_of_neg_norm_sq
          hρ₁.apply_eq_neg_norm_sq hρ₂.apply_eq_neg_norm_sq hQ₁₂)
        o₁ hρ₁.apply_eq_neg_norm_sq hn (ρ₁.cliffordBaseChange ℂ)
        (ρ₂.cliffordBaseChange ℂ))).IsGeometricCliffordAction := by
  refine (isGeometricCliffordAction_cliffordBaseChangeEquiv_symm_iff (Q := Q₁₂) _).2
    ⟨fun x ↦ by rw [hQ₁₂, real_inner_self_eq_norm_sq], fun x u v ↦ ?_⟩
  have hx : x = WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2) := rfl
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp only [CliffordAlgebra.complexProdTensor_ι_one_tmul_toLp,
    AlgHom.cliffordBaseChange_ι_one_tmul, LinearMap.add_apply, inner_add_left, inner_add_right,
    neg_add]
  congr 1
  · induction u using TensorProduct.inductionOn generalizing v with
    | tmul e f =>
      induction v using TensorProduct.inductionOn with
      | tmul e' f' =>
        simp only [LinearMap.rTensor_tmul, TensorProduct.inner_tmul,
          hρ₁.inner_map_ι_left, neg_mul]
      | add v₁ v₂ hv₁ hv₂ =>
        simp only [map_add, inner_add_right, hv₁, hv₂, neg_add]
    | add u₁ u₂ hu₁ hu₂ =>
      simp only [map_add, inner_add_left, hu₁, hu₂, neg_add]
  · exact inner_tensorMap_of_symm_skew
      (hρ₁.inner_cliffordBaseChange_complexVolume_left o₁)
      (hρ₂.inner_map_ι_left (WithLp.ofLp x).2) u v

end TensorProduct

/-! ### Rank-zero witness -/

section SubsingletonWitness

/-- On a zero-dimensional space `[Subsingleton V]` with `Q = 0` (`Q v = -⟪v, v⟫_ℝ`), the canonical
scalar action `(Algebra.ofId ℝ (Module.End ℂ S)).comp (equivOfSubsingleton Q).toAlgHom` on any
complex inner product space `S` satisfies `AlgHom.IsGeometricCliffordAction`. -/
theorem isGeometricCliffordAction_of_subsingleton [Subsingleton V]
    (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℂ S] :
    ((Algebra.ofId ℝ (Module.End ℂ S)).comp
      (CliffordAlgebra.equivOfSubsingleton Q).toAlgHom).IsGeometricCliffordAction where
  apply_eq_neg_inner_self v := by simp [Subsingleton.elim v 0]
  inner_map_ι_left v x y := by simp [Subsingleton.elim v 0]

/-- In rank zero, the `+1`-eigenspace of `ρ.cliffordBaseChange ℂ` for the positive orientation is
the whole space `⊤`. -/
theorem eigenspace_cliffordBaseChange_complexVolume_positiveOrientation_one
    [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 0)] {S : Type*} [AddCommGroup S] [Module ℂ S]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) :
    Module.End.eigenspace
      (ρ.cliffordBaseChange ℂ
        (complexVolume Q (positiveOrientation : Orientation ℝ V (Fin 0)))) 1 = ⊤ := by
  rw [cliffordBaseChange_complexVolume_positiveOrientation, eq_top_iff]
  intro s _
  simp

/-- In rank zero, the `-1`-eigenspace of `ρ.cliffordBaseChange ℂ` for the positive orientation is
`⊥`. -/
theorem eigenspace_cliffordBaseChange_complexVolume_positiveOrientation_neg_one
    [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 0)] {S : Type*} [AddCommGroup S] [Module ℂ S]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) :
    Module.End.eigenspace
      (ρ.cliffordBaseChange ℂ
        (complexVolume Q (positiveOrientation : Orientation ℝ V (Fin 0)))) (-1) = ⊥ := by
  rw [cliffordBaseChange_complexVolume_positiveOrientation, eq_bot_iff]
  intro s hs
  rw [Module.End.mem_eigenspace_iff, one_apply_eq_self, neg_one_smul] at hs
  rw [Submodule.mem_bot]
  calc
    s = (2⁻¹ : ℂ) • (2 : ℂ) • s := by rw [inv_smul_smul₀ two_ne_zero]
    _ = 0 := by rw [two_smul, add_eq_zero_iff_eq_neg.2 hs, smul_zero]

end SubsingletonWitness

end AlgHom

/-! ### Concrete nontrivial witnesses on the line and the negative Pauli plane -/

namespace TauCeti

/-- **1D geometric Clifford action**: `ℝ` with `Q r = -r²` acting on `ℂ` with generator
`c(1) = i • 1`. -/
def realLineGeometricCliffordAction :
    CliffordAlgebra (-QuadraticMap.sq (R := ℝ)) →ₐ[ℝ] Module.End ℂ ℂ :=
  CliffordAlgebra.lift (-QuadraticMap.sq (R := ℝ))
    ⟨LinearMap.toSpanSingleton ℝ (Module.End ℂ ℂ) (Complex.I • 1), fun r ↦ by
      ext
      simp only [LinearMap.toSpanSingleton_apply, mul_apply_eq_comp, LinearMap.smul_apply,
        one_apply_eq_self, ← Complex.coe_smul, smul_eq_mul, neg_apply,
        QuadraticMap.sq_apply, Module.algebraMap_end_apply]
      push_cast
      linear_combination (r : ℂ) ^ 2 * Complex.I_sq⟩

/-- On the real line, the generator `1 : ℝ` acts on `ℂ` by `i • 1`. -/
@[simp]
theorem realLineGeometricCliffordAction_ι_one :
    realLineGeometricCliffordAction (ι (-QuadraticMap.sq (R := ℝ)) 1) = Complex.I • 1 := by
  simp [realLineGeometricCliffordAction]

/-- `TauCeti.realLineGeometricCliffordAction` satisfies `AlgHom.IsGeometricCliffordAction`. -/
theorem isGeometricCliffordAction_realLineGeometricCliffordAction :
    realLineGeometricCliffordAction.IsGeometricCliffordAction where
  apply_eq_neg_inner_self r := by
    simp [QuadraticMap.sq_apply, sq]
  inner_map_ι_left r x y := by
    have hr : r = r • (1 : ℝ) := by simp
    conv_lhs => rw [hr, map_smul, map_smul, realLineGeometricCliffordAction_ι_one]
    conv_rhs => rw [hr, map_smul, map_smul, realLineGeometricCliffordAction_ι_one]
    simp only [LinearMap.smul_apply, one_apply_eq_self, ← Complex.coe_smul, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal, Complex.conj_I]
    ring

section NegativePauliPlane

variable {Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin 2))}

/-- Auxiliary real-linear map sending `v ∈ EuclideanSpace ℝ (Fin 2)` to the endomorphism
`(i • pauli ![0, v 1, v 0]).toEuclideanLin` on `EuclideanSpace ℂ (Fin 2)`, so that `e₀ ↦ i σ₃` and
`e₁ ↦ i σ₂`. -/
private def negativePlanePauliAux :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] Module.End ℂ (EuclideanSpace ℂ (Fin 2)) where
  toFun v := (Complex.I • pauli ![0, v 1, v 0]).toEuclideanLin
  map_add' v w := by
    have hp : (![0, (v + w) 1, (v + w) 0] : Fin 3 → ℝ) = ![0, v 1, v 0] + ![0, w 1, w 0] := by
      ext i
      fin_cases i <;> simp
    rw [hp, map_add, smul_add, map_add]
  map_smul' r v := by
    have hp : (![0, (r • v) 1, (r • v) 0] : Fin 3 → ℝ) = r • ![0, v 1, v 0] := by
      ext i
      fin_cases i <;> simp
    rw [hp, pauli.map_smul, RingHom.id_apply, ← Complex.coe_smul, smul_comm Complex.I (r : ℂ),
      map_smul, Complex.coe_smul]

private theorem toEuclideanLin_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    A.toEuclideanLin * B.toEuclideanLin = (A * B).toEuclideanLin := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Module.End.mul_eq_comp, ← Matrix.toLin_mul]

/-- **2D negative Pauli plane geometric Clifford action**: for `Q v = -‖v‖²` on
`EuclideanSpace ℝ (Fin 2)`, the Clifford algebra acts on `EuclideanSpace ℂ (Fin 2)` with standard
orthonormal generators `e₀ ↦ i σ₃` and `e₁ ↦ i σ₂`. -/
def negativePlanePauliAction (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  CliffordAlgebra.lift Q ⟨negativePlanePauliAux, fun v ↦ by
    have hnorm : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp [Real.norm_eq_abs, sq_abs]
    have hmat : (Complex.I • pauli ![0, v 1, v 0]) * (Complex.I • pauli ![0, v 1, v 0]) =
        ((-‖v‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pauli_apply, Matrix.mul_apply, Fin.sum_univ_two, hnorm, -Complex.ofReal_pow,
          Complex.ext_iff] <;> ring
    rw [negativePlanePauliAux, LinearMap.coe_mk, AddHom.coe_mk, toEuclideanLin_mul, hmat,
      map_smul, hQ, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
    congr 1
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_one, Module.End.one_eq_id]⟩

/-- Value of `TauCeti.negativePlanePauliAction` on a generator `ι Q v`. -/
@[simp]
theorem negativePlanePauliAction_ι (hQ : ∀ v, Q v = -‖v‖ ^ 2) (v : EuclideanSpace ℝ (Fin 2)) :
    negativePlanePauliAction hQ (ι Q v) = (Complex.I • pauli ![0, v 1, v 0]).toEuclideanLin := by
  simp [negativePlanePauliAction, negativePlanePauliAux]

/-- `TauCeti.negativePlanePauliAction` satisfies `AlgHom.IsGeometricCliffordAction`. -/
theorem isGeometricCliffordAction_negativePlanePauliAction (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    (negativePlanePauliAction hQ).IsGeometricCliffordAction := by
  rw [AlgHom.isGeometricCliffordAction_iff_adjoint]
  refine ⟨fun v ↦ by rw [hQ, real_inner_self_eq_norm_sq], fun v ↦ ?_⟩
  rw [negativePlanePauliAction_ι, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I,
    (isHermitian_pauli ![0, v 1, v 0]).eq, neg_smul, map_neg]

/-- On the negative Pauli plane, the ordered product `c(e₀) c(e₁)` of the standard orthonormal
basis vectors equals `(i • σ₁).toEuclideanLin` (`iX`). -/
theorem negativePlanePauliAction_e0_mul_e1 (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    negativePlanePauliAction hQ (ι Q (EuclideanSpace.single 0 1)) *
        negativePlanePauliAction hQ (ι Q (EuclideanSpace.single 1 1)) =
      (Complex.I • pauli ![1, 0, 0]).toEuclideanLin := by
  rw [negativePlanePauliAction_ι, negativePlanePauliAction_ι, toEuclideanLin_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli_apply, Matrix.mul_apply, Fin.sum_univ_two, EuclideanSpace.single]

/-- **Chirality on the negative Pauli plane**: for the standard orientation of
`EuclideanSpace ℝ (Fin 2)`, the chirality operator of `TauCeti.negativePlanePauliAction` is
`(-σ₁).toEuclideanLin` (`-X`). -/
theorem cliffordBaseChange_complexVolume_negativePlanePauliAction (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    (negativePlanePauliAction hQ).cliffordBaseChange ℂ
        (complexVolume Q (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation) =
      (-pauli ![1, 0, 0]).toEuclideanLin := by
  have hlist : List.finRange 2 = [0, 1] := rfl
  have hdiv : (2 + 1) / 2 = 1 := rfl
  rw [(negativePlanePauliAction hQ).cliffordBaseChange_complexVolume_eq _
    (EuclideanSpace.basisFun (Fin 2) ℝ) rfl
    ((EuclideanSpace.basisFun (Fin 2) ℝ).isOrthoᵢ_associated hQ), hlist, hdiv]
  simp only [pow_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    EuclideanSpace.basisFun_apply, negativePlanePauliAction_e0_mul_e1 hQ, ← map_smul, smul_smul,
    Complex.I_mul_I, neg_one_smul]

end NegativePauliPlane

end TauCeti
