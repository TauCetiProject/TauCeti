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
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Prod
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod
public import TauCeti.LinearAlgebra.Matrix.Pauli
-- Private: used only inside unexposed definitions and proofs for the 1D Clifford-to-`ℂ` map, the
-- tensor-product formal-adjoint identity, real `star` compatibility on generators, polarized real
-- Clifford relations, and the negative-plane coordinate/quaternion Pauli model.
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import TauCeti.Analysis.InnerProductSpace.TensorProduct
import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Orthonormal
import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Pauli

/-!
# Geometric Clifford actions on Hermitian modules and their chirality operator

In spin geometry on a Riemannian manifold, a fibre `V` of the tangent bundle acts on a complex
Hermitian vector space `S` through a real algebra homomorphism `ρ : CliffordAlgebra Q →ₐ[ℝ]
Module.End ℂ S` satisfying the **geometric convention**:

* the quadratic form is minus the inner-product square, `Q v = -⟪v, v⟫_ℝ = -‖v‖²`;
* Clifford multiplication `c(v) = ρ (ι Q v)` by every real vector `v` is skew-Hermitian,
  `⟪c(v) x, y⟫_ℂ = -⟪x, c(v) y⟫_ℂ`.

Combining skew-Hermiticity with the polarized Clifford anticommutator
`c(v) c(w) + c(w) c(v) = (-2 * ⟪v, w⟫_ℝ) • 1`
(`AlgHom.map_cliffordAlgebraι_mul_map_cliffordAlgebraι_add_swap_eq_neg_two_inner`) yields the
Hermitian identity `⟪c(v) x, c(w) y⟫_ℂ + ⟪c(w) x, c(v) y⟫_ℂ = 2 ⟪v, w⟫_ℝ ⟪x, y⟫_ℂ` and norm scaling
`‖c(v) x‖ = ‖v‖ ‖x‖` without requiring `V` or `S` to be finite-dimensional.

Extending `ρ` complex-linearly via `AlgHom.cliffordBaseChange ℂ` produces a `ℂ`-algebra
homomorphism `ρ.cliffordBaseChange ℂ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S`
compatible with the conjugate-linear Clifford involution `CliffordAlgebra.conjStar`
(`AlgHom.inner_cliffordBaseChange_eq_conjStar_iff`), while `ρ` itself respects Clifford conjugation
`star`. When `V` is oriented of dimension `n`, evaluating `ρ.cliffordBaseChange ℂ` at
`CliffordAlgebra.complexVolume Q o` (`AlgHom.cliffordBaseChange_complexVolume_eq_prod_map_ι`) gives
a self-adjoint chirality involution whose `+1` and `-1` eigenspaces
(`AlgHom.isCompl_eigenspace_cliffordBaseChange_complexVolume`) are orthogonal and, in even
dimension, exchanged by Clifford multiplication by real vectors
(`AlgHom.map_ι_mem_eigenspace_cliffordBaseChange_complexVolume_neg`). Moreover, this chirality
grading makes the graded tensor product `CliffordAlgebra.complexProdTensor` preserve the geometric
convention on `WithLp 2 (V × W)`.

Concrete witnesses are given in rank zero, on the real line via `CliffordAlgebraComplex.toComplex`
(`c(1) = i` on `ℂ`), and on the two-dimensional negative Pauli plane via
`OrthonormalBasis.isometryEquivRealCliffordForm`, `TauCeti.realCliffordZeroTwoEquivQuaternion`, and
`Quaternion.toComplexMatrix` (`c(e₀) = i σ₃`, `c(e₁) = i σ₂`, chirality `-σ₁` on `ℂ²`).

## Main definitions

* `AlgHom.IsGeometricCliffordAction`: predicate on `ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S`
  recording `Q v = -⟪v, v⟫_ℝ` and skew-Hermiticity of `ρ (ι Q v)`.
* `TauCeti.realLineGeometricCliffordAction`: geometric Clifford action of `ℝ` on `ℂ` with
  `c(r) = r • (i • 1)`.
* `TauCeti.negativePlanePauliAction`: geometric Clifford action of `EuclideanSpace ℝ (Fin 2)` on
  `EuclideanSpace ℂ (Fin 2)` with Pauli generators `i σ₃`, `i σ₂` and chirality `-σ₁`.

## Main results

* `AlgHom.IsGeometricCliffordAction.inner_map_ι_add_swap`,
  `AlgHom.IsGeometricCliffordAction.norm_map_ι_apply`: polarized inner-product identity and
  norm-scaling law without finite-dimensionality assumptions.
* `AlgHom.IsGeometricCliffordAction.inner_cliffordBaseChange_eq_conjStar`,
  `AlgHom.IsGeometricCliffordAction.adjoint_cliffordBaseChange_eq_conjStar`,
  `AlgHom.IsGeometricCliffordAction.inner_map_eq_map_star`,
  `AlgHom.IsGeometricCliffordAction.adjoint_map_eq_map_star`: compatibility of
  `ρ.cliffordBaseChange ℂ` with `CliffordAlgebra.conjStar` and of `ρ` with `star`.
* `AlgHom.IsGeometricCliffordAction.isSelfAdjoint_cliffordBaseChange_complexVolume`,
  `AlgHom.IsGeometricCliffordAction.inner_eq_zero_of_mem_eigenspace_complexVolume`: self-adjointness
  of the chirality operator and orthogonality of the half-spinor eigenspaces.
* `AlgHom.IsGeometricCliffordAction.complexProdTensor`: graded tensor product preservation of the
  geometric convention.
* `AlgHom.isGeometricCliffordAction_of_subsingleton`,
  `TauCeti.isGeometricCliffordAction_realLineGeometricCliffordAction`,
  `TauCeti.isGeometricCliffordAction_negativePlanePauliAction`,
  `TauCeti.cliffordBaseChange_complexVolume_negativePlanePauliAction`: concrete rank-zero, 1D, and
  2D negative-Pauli-plane witnesses.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§1 and 5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds* (2nd ed., 2007), §12.1.1,
  Definition 12.1.10.
-/

public section

noncomputable section

open CliffordAlgebra Module
open scoped RealInnerProductSpace TensorProduct ComplexConjugate EuclideanSpace

namespace AlgHom

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}

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
  ρ.map_cliffordAlgebraι_mul_map_cliffordAlgebraι_add_swap_eq_neg_two_inner
    hρ.apply_eq_neg_norm_sq v w

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
  (ρ.inner_map_eq_map_star_iff_inner_map_cliffordAlgebraι_left.2 hρ.inner_map_ι_left) a x y

/-- On a finite-dimensional Hermitian module, a geometric Clifford action respects Clifford
conjugation `star` for `LinearMap.adjoint`. -/
theorem adjoint_map_eq_map_star [FiniteDimensional ℂ S] (a : CliffordAlgebra Q) :
    (ρ a).adjoint = ρ (star a) :=
  (ρ.adjoint_map_eq_map_star_iff_adjoint_map_cliffordAlgebraι.2 hρ.adjoint_map_ι) a

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

/-! ### Self-adjointness and orthogonality of the chirality operator -/

section HermitianChirality

variable [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)]
  {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S]

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

/-! ### Graded tensor product of geometric Clifford actions -/

section TensorProduct

variable [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₂ : QuadraticForm ℝ W} {Q₁₂ : QuadraticForm ℝ (WithLp 2 (V × W))}
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

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
    ⟨fun x ↦ by rw [hQ₁₂, real_inner_self_eq_norm_sq], fun x u₁ u₂ ↦ ?_⟩
  obtain ⟨⟨v, w⟩, rfl⟩ := WithLp.toLp_surjective 2 x
  simp only [CliffordAlgebra.complexProdTensor_ι_one_tmul_toLp,
    AlgHom.cliffordBaseChange_ι_one_tmul, LinearMap.add_apply, inner_add_left, inner_add_right,
    neg_add]
  congr 1
  · rw [LinearMap.rTensor_def,
      TensorProduct.inner_map_left (f' := -ρ₁ (ι Q v)) (g' := LinearMap.id)
        (fun a a' ↦ by simp [hρ₁.inner_map_ι_left]) (fun _ _ ↦ rfl),
      ← LinearMap.rTensor_def, LinearMap.rTensor_neg, LinearMap.neg_apply, inner_neg_right,
      LinearMap.rTensor_def]
  · rw [TensorProduct.inner_map_left (f' := ρ₁.cliffordBaseChange ℂ (complexVolume Q o₁))
        (g' := (-1 : ℂ) • ρ₂ (ι Q₂ w)) (hρ₁.inner_cliffordBaseChange_complexVolume_left o₁)
        (fun b b' ↦ by simp [hρ₂.inner_map_ι_left]),
      TensorProduct.map_smul_right, LinearMap.smul_apply, neg_one_smul, inner_neg_right]

end TensorProduct

/-! ### Rank-zero witness -/

section SubsingletonWitness

/-- On a zero-dimensional space `[Subsingleton V]`, every real Clifford algebra homomorphism
`ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S` into a complex inner product space `S` satisfies
`AlgHom.IsGeometricCliffordAction`. -/
theorem isGeometricCliffordAction_of_subsingleton [Subsingleton V]
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℂ S]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) :
    ρ.IsGeometricCliffordAction where
  apply_eq_neg_inner_self v := by simp [Subsingleton.elim v 0]
  inner_map_ι_left v x y := by simp [Subsingleton.elim v 0]

end SubsingletonWitness

end AlgHom

/-! ### Concrete nontrivial witnesses on the line and the negative Pauli plane -/

namespace TauCeti

/-- **1D geometric Clifford action**: `ℝ` with `Q r = -r²` acting on `ℂ` via
`CliffordAlgebraComplex.toComplex`, sending `r` to `r • (i • 1)`. -/
def realLineGeometricCliffordAction :
    CliffordAlgebra (-QuadraticMap.sq (R := ℝ)) →ₐ[ℝ] Module.End ℂ ℂ :=
  ((Algebra.ofId ℂ (Module.End ℂ ℂ)).restrictScalars ℝ).comp CliffordAlgebraComplex.toComplex

/-- On the real line, a vector `r : ℝ` acts on `ℂ` by `r • (i • 1)`. -/
@[simp]
theorem realLineGeometricCliffordAction_ι (r : ℝ) :
    realLineGeometricCliffordAction (ι (-QuadraticMap.sq (R := ℝ)) r) = r • (Complex.I • 1) :=
  (congrArg (Algebra.ofId ℂ (Module.End ℂ ℂ)) (CliffordAlgebraComplex.toComplex_ι r)).trans
    (by rw [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_smul,
      Complex.coe_smul])

/-- On the real line, the generator `1 : ℝ` acts on `ℂ` by `i • 1`. -/
theorem realLineGeometricCliffordAction_ι_one :
    realLineGeometricCliffordAction (ι (-QuadraticMap.sq (R := ℝ)) 1) = Complex.I • 1 := by
  simp

/-- `TauCeti.realLineGeometricCliffordAction` satisfies `AlgHom.IsGeometricCliffordAction`. -/
theorem isGeometricCliffordAction_realLineGeometricCliffordAction :
    realLineGeometricCliffordAction.IsGeometricCliffordAction where
  apply_eq_neg_inner_self r := by
    simp [QuadraticMap.sq_apply, sq]
  inner_map_ι_left r x y := by
    simp only [realLineGeometricCliffordAction_ι, LinearMap.smul_apply, one_apply_eq_self,
      ← Complex.coe_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, Complex.conj_I]
    ring

section NegativePauliPlane

variable {Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin 2))}

/-- **2D negative Pauli plane geometric Clifford action**: for `Q v = -‖v‖²` on
`EuclideanSpace ℝ (Fin 2)`, the Clifford algebra acts on `EuclideanSpace ℂ (Fin 2)` through the
standard coordinate model `OrthonormalBasis.isometryEquivRealCliffordForm` and quaternion Pauli
embedding `Quaternion.toComplexMatrix ∘ realCliffordZeroTwoEquivQuaternion`, sending `e₀ ↦ i σ₃`
and `e₁ ↦ i σ₂`. -/
def negativePlanePauliAction (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (((Matrix.toLpLinAlgEquiv 2).toAlgHom.restrictScalars ℝ).comp
    Quaternion.toComplexMatrix.toAlgHom).comp
    (realCliffordZeroTwoEquivQuaternion.toAlgHom.comp
      (CliffordAlgebra.equivOfIsometry
        ((EuclideanSpace.basisFun (Fin 2) ℝ).isometryEquivRealCliffordForm hQ)).toAlgHom)

/-- Value of `TauCeti.negativePlanePauliAction` on a generator `ι Q v`. -/
@[simp]
theorem negativePlanePauliAction_ι (hQ : ∀ v, Q v = -‖v‖ ^ 2) (v : EuclideanSpace ℝ (Fin 2)) :
    negativePlanePauliAction hQ (ι Q v) = (Complex.I • pauli ![0, v 1, v 0]).toEuclideanLin := by
  have hv : (EuclideanSpace.basisFun (Fin 2) ℝ).isometryEquivRealCliffordForm hQ v =
      fun i ↦ v (Fin.cast (zero_add 2) i) := by
    ext i
    rw [OrthonormalBasis.isometryEquivRealCliffordForm_apply, EuclideanSpace.basisFun_repr]
  simp only [negativePlanePauliAction, AlgHom.comp_apply, AlgHom.coe_restrictScalars',
    AlgEquiv.toAlgHom_apply, StarAlgHom.coe_toAlgHom, equivOfIsometry_apply, map_apply_ι,
    QuadraticMap.IsometryEquiv.toIsometry_apply,
    toComplexMatrix_realCliffordZeroTwoEquivQuaternion_ι, hv]
  rfl

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
theorem negativePlanePauliAction_ι_single_zero_mul_ι_single_one (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    negativePlanePauliAction hQ (ι Q (EuclideanSpace.single 0 1)) *
        negativePlanePauliAction hQ (ι Q (EuclideanSpace.single 1 1)) =
      (Complex.I • pauli ![1, 0, 0]).toEuclideanLin := by
  have h0 : (EuclideanSpace.basisFun (Fin 2) ℝ).isometryEquivRealCliffordForm hQ
      (EuclideanSpace.single 0 1) = Pi.single 0 1 := by
    rw [← EuclideanSpace.basisFun_apply, OrthonormalBasis.isometryEquivRealCliffordForm_apply_self]
    rfl
  have h1 : (EuclideanSpace.basisFun (Fin 2) ℝ).isometryEquivRealCliffordForm hQ
      (EuclideanSpace.single 1 1) = Pi.single 1 1 := by
    rw [← EuclideanSpace.basisFun_apply, OrthonormalBasis.isometryEquivRealCliffordForm_apply_self]
    rfl
  rw [← map_mul]
  simp only [negativePlanePauliAction, AlgHom.comp_apply, AlgHom.coe_restrictScalars',
    AlgEquiv.toAlgHom_apply, StarAlgHom.coe_toAlgHom, equivOfIsometry_apply]
  rw [map_mul (CliffordAlgebra.map _), map_apply_ι, map_apply_ι,
    QuadraticMap.IsometryEquiv.toIsometry_apply, QuadraticMap.IsometryEquiv.toIsometry_apply,
    h0, h1, toComplexMatrix_realCliffordZeroTwoEquivQuaternion_ι_mul_ι]
  rfl

/-- **Chirality on the negative Pauli plane**: for the standard orientation of
`EuclideanSpace ℝ (Fin 2)`, the chirality operator of `TauCeti.negativePlanePauliAction` is
`(-σ₁).toEuclideanLin` (`-X`). -/
theorem cliffordBaseChange_complexVolume_negativePlanePauliAction (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    (negativePlanePauliAction hQ).cliffordBaseChange ℂ
        (complexVolume Q (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation) =
      (-pauli ![1, 0, 0]).toEuclideanLin := by
  have hlist : List.finRange 2 = [0, 1] := rfl
  rw [(negativePlanePauliAction hQ).cliffordBaseChange_complexVolume_eq_prod_map_ι _
    (EuclideanSpace.basisFun (Fin 2) ℝ) rfl hQ (ℓ := 1) rfl, hlist]
  simp only [pow_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    EuclideanSpace.basisFun_apply, negativePlanePauliAction_ι_single_zero_mul_ι_single_one hQ,
    ← map_smul, smul_smul, Complex.I_mul_I, neg_one_smul]

end NegativePauliPlane

end TauCeti
