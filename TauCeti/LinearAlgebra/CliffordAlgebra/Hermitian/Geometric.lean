/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex
public import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
-- Private: `CliffordAlgebra.Equivs` supplies `CliffordAlgebraComplex.toComplex` for the 1D witness.
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs

/-!
# The geometric convention for real Clifford actions

Let `V` be a real inner product space, `Q` a quadratic form on `V` and `S` a complex inner product
space with a real algebra map `ρ : Cℓ(V, Q) → End_ℂ(S)`; write `c(v) = ρ (ι Q v)` for Clifford
multiplication by `v`. The **geometric convention** for such an action, the one used for Clifford
modules and Dirac operators on Riemannian manifolds, has two clauses:

* the quadratic form is minus the squared norm, `Q v = -‖v‖²`, so that `c(v)² = -‖v‖²`;
* every `c(v)` is skew-Hermitian, `⟪c(v) s, t⟫ = -⟪s, c(v) t⟫`.

This file records it as the predicate `AlgHom.IsGeometricClifford` and derives its first
consequences: the polarized Clifford relation `c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫`, the polarized
Hermitian identity `⟪c(v) s, c(w) t⟫ + ⟪c(w) s, c(v) t⟫ = 2 ⟪v, w⟫ ⟪s, t⟫` and diagonal
inner-product scaling `⟪c(v) s, c(v) t⟫ = ‖v‖² ⟪s, t⟫` without assuming finite-dimensionality, the
relations of a unit orthogonal pair `e₁, e₂` (`c(eᵢ)² = -1`, `c(e₁) c(e₂) = -c(e₂) c(e₁)` and
`(c(e₁) c(e₂))² = -1`), the equivalent adjoint forms `c(v)* = -c(v)` and `ρ_ℂ(a)* = ρ_ℂ(conjStar a)`
on a finite-dimensional module, compatibility with Clifford conjugation `star` and `conjStar` on
modules of any dimension, and concrete rank-zero and one-dimensional witnesses
(`AlgHom.isGeometricClifford_of_subsingleton` and `TauCeti.realLineGeometricCliffordAction`).

The skew-Hermitian clause is stated through inner products, so it makes sense on modules of any
dimension. The positive convention `c(v)² = +‖v‖²` is excluded by the first clause: for `V = ℝ`
and `S = ℂ`, the operator `c(e) = i` squares to `-1` and is skew-Hermitian, while `c(e) = 1`
squares to `+1` and is Hermitian.

## Main definitions

* `AlgHom.IsGeometricClifford ρ`: `Q v = -‖v‖²` and every `c(v)` is skew-Hermitian.
* `TauCeti.realLineGeometricCliffordAction`: 1D geometric Clifford action of `ℝ` on `ℂ` with
  `c(r) = r • (i • 1)`.

## Main results

* `AlgHom.isGeometricClifford_iff`, `AlgHom.isGeometricClifford_iff_adjoint`,
  `AlgHom.isGeometricClifford_iff_adjoint_liftBaseChange`,
  `AlgHom.isGeometricClifford_restrictScalars_comp_ofBaseChangeAux_iff`: characterizations of the
  geometric convention in terms of inner products, finite-dimensional adjoints, complexified
  `*`-representations, and restriction along `CliffordAlgebra.ofBaseChangeAux`.
* `AlgHom.IsGeometricClifford.map_ι_mul_map_ι_add_swap`,
  `AlgHom.IsGeometricClifford.map_ι_apply_add_swap`: the polarized Clifford relation
  `c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫` at operator and vector level.
* `AlgHom.IsGeometricClifford.inner_map_ι_map_ι_add_swap`,
  `AlgHom.IsGeometricClifford.inner_map_ι_map_ι`: polarized inner-product identity and diagonal
  inner-product scaling without finite-dimensionality.
* `AlgHom.IsGeometricClifford.map_ι_mul_map_ι_mul_self_of_orthonormal`: for a unit orthogonal
  pair, `(c(e₁) c(e₂))² = -1`.
* `AlgHom.IsGeometricClifford.inner_map_apply_left`,
  `AlgHom.IsGeometricClifford.adjoint_map_eq_map_star`,
  `AlgHom.IsGeometricClifford.inner_liftBaseChange_apply_left`,
  `AlgHom.IsGeometricClifford.adjoint_liftBaseChange`: compatibility of `ρ` with Clifford
  conjugation `star` and of its complex-linear extension
  `ρ_ℂ = CliffordAlgebra.liftBaseChange ℂ Q ρ` with `CliffordAlgebra.conjStar`.
* `AlgHom.isGeometricClifford_of_subsingleton`,
  `TauCeti.isGeometricClifford_realLineGeometricCliffordAction`: rank-zero and 1D witnesses.

## References

* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Definition 12.1.10, p. 626, and
  Definition 12.1.64, pp. 653–654.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open CliffordAlgebra
open scoped InnerProductSpace TensorProduct

namespace AlgHom

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Q : QuadraticForm ℝ V}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S]

/-- **The geometric convention for a real Clifford action** `ρ : Cℓ(V, Q) → End_ℂ(S)`: the
quadratic form is minus the squared norm, `Q v = -‖v‖²`, and Clifford multiplication
`c(v) = ρ (ι Q v)` by every vector is skew-Hermitian. Then `c(v)² = -‖v‖²` and
`c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫` (`AlgHom.IsGeometricClifford.map_ι_mul_map_ι_add_swap`). -/
@[mk_iff]
structure IsGeometricClifford (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) : Prop where
  /-- The quadratic form is minus the squared norm. -/
  apply_eq_neg_norm_sq : ∀ v, Q v = -‖v‖ ^ 2
  /-- Clifford multiplication by a vector is skew-Hermitian. -/
  inner_map_ι_apply_left : ∀ (v : V) (s t : S), ⟪ρ (ι Q v) s, t⟫_ℂ = -⟪s, ρ (ι Q v) t⟫_ℂ

namespace IsGeometricClifford

variable {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} (hρ : ρ.IsGeometricClifford)
include hρ

/-- Under the geometric convention, `Q v = -⟪v, v⟫_ℝ`. -/
theorem apply_eq_neg_inner_self (v : V) : Q v = -⟪v, v⟫_ℝ := by
  rw [hρ.apply_eq_neg_norm_sq, real_inner_self_eq_norm_sq]

/-- Moving Clifford multiplication to the left in the inner product introduces a minus sign. -/
theorem inner_map_ι_apply_right (v : V) (s t : S) :
    ⟪s, ρ (ι Q v) t⟫_ℂ = -⟪ρ (ι Q v) s, t⟫_ℂ := by
  rw [hρ.inner_map_ι_apply_left, neg_neg]

/-- On a finite-dimensional Hermitian module, `AlgHom.IsGeometricClifford` makes every
generator skew-adjoint for `LinearMap.adjoint`. -/
theorem adjoint_map_ι [FiniteDimensional ℂ S] (v : V) :
    LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro s t
  simp [hρ.inner_map_ι_apply_left]

/-- **The polarized Clifford relation** of the geometric convention:
`c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫`. -/
theorem map_ι_mul_map_ι_add_swap (v w : V) :
    ρ (ι Q v) * ρ (ι Q w) + ρ (ι Q w) * ρ (ι Q v) = ((-2 * ⟪v, w⟫_ℝ : ℝ) : ℂ) • 1 := by
  rw [Complex.coe_smul]
  exact ρ.map_cliffordAlgebraι_mul_map_cliffordAlgebraι_add_swap_eq_neg_two_inner
    hρ.apply_eq_neg_norm_sq v w

/-- Pointwise polarized Clifford relation on spinors:
`c(v) (c(w) s) + c(w) (c(v) s) = (-2 * ⟪v, w⟫_ℝ) • s`. -/
theorem map_ι_apply_add_swap (v w : V) (s : S) :
    ρ (ι Q v) (ρ (ι Q w) s) + ρ (ι Q w) (ρ (ι Q v) s) = ((-2 * ⟪v, w⟫_ℝ : ℝ) : ℂ) • s := by
  have h := LinearMap.congr_fun (hρ.map_ι_mul_map_ι_add_swap v w) s
  simpa only [LinearMap.add_apply, mul_apply_eq_comp, LinearMap.smul_apply,
    one_apply_eq_self] using h

/-- In the geometric convention `c(v)² = -‖v‖²`. -/
theorem map_ι_mul_self (v : V) : ρ (ι Q v) * ρ (ι Q v) = ((-‖v‖ ^ 2 : ℝ) : ℂ) • 1 := by
  rw [map_ι_mul_map_ι, hρ.apply_eq_neg_norm_sq]

/-- Clifford multiplications by orthogonal vectors anticommute. -/
theorem map_ι_mul_map_ι_comm_of_inner_eq_zero {v w : V} (h : ⟪v, w⟫_ℝ = 0) :
    ρ (ι Q v) * ρ (ι Q w) = -(ρ (ι Q w) * ρ (ι Q v)) :=
  ρ.map_cliffordAlgebraι_mul_map_cliffordAlgebraι_of_inner_eq_zero hρ.apply_eq_neg_norm_sq h

/-- Clifford multiplication by a unit vector squares to `-1`. -/
theorem map_ι_mul_self_of_norm_eq_one {v : V} (h : ‖v‖ = 1) : ρ (ι Q v) * ρ (ι Q v) = -1 :=
  ρ.map_cliffordAlgebraι_sq_of_norm_eq_one hρ.apply_eq_neg_norm_sq h

/-- **A unit orthogonal pair**: for orthonormal `e₁, e₂`, the product `c(e₁) c(e₂)` squares to
`-1`, so that `i c(e₁) c(e₂)` is an involution. -/
theorem map_ι_mul_map_ι_mul_self_of_orthonormal {e₁ e₂ : V} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h : ⟪e₁, e₂⟫_ℝ = 0) :
    ρ (ι Q e₁) * ρ (ι Q e₂) * (ρ (ι Q e₁) * ρ (ι Q e₂)) = -1 :=
  ρ.map_cliffordAlgebraι_mul_map_cliffordAlgebraι_sq_of_orthonormal
    hρ.apply_eq_neg_norm_sq h₁ h₂ h

/-- **Polarized Hermitian identity**: combining skew-Hermiticity with the polarized Clifford
relation gives `⟪c(v) s, c(w) t⟫_ℂ + ⟪c(w) s, c(v) t⟫_ℂ = 2 ⟪v, w⟫_ℝ ⟪s, t⟫_ℂ` without assuming
finite-dimensionality of `V` or `S`. -/
theorem inner_map_ι_map_ι_add_swap (v w : V) (s t : S) :
    ⟪ρ (ι Q v) s, ρ (ι Q w) t⟫_ℂ + ⟪ρ (ι Q w) s, ρ (ι Q v) t⟫_ℂ =
      (2 * ⟪v, w⟫_ℝ : ℂ) * ⟪s, t⟫_ℂ := by
  rw [hρ.inner_map_ι_apply_right w, hρ.inner_map_ι_apply_right v, ← neg_add, ← inner_add_left,
    add_comm (ρ (ι Q w) (ρ (ι Q v) s)), hρ.map_ι_apply_add_swap, inner_smul_left]
  simp only [Complex.conj_ofReal]
  push_cast
  ring

/-- Applying `c(v)` to both arguments multiplies the inner product by `‖v‖²`, without assuming
finite-dimensionality of `S`. -/
theorem inner_map_ι_map_ι (v : V) (s t : S) :
    ⟪ρ (ι Q v) s, ρ (ι Q v) t⟫_ℂ = (‖v‖ ^ 2 : ℂ) * ⟪s, t⟫_ℂ := by
  have h := hρ.inner_map_ι_map_ι_add_swap v v s t
  rw [real_inner_self_eq_norm_sq] at h
  push_cast at h
  linear_combination (1 / 2 : ℂ) * h

/-- Under the geometric convention, `ρ` respects Clifford conjugation `star` in the inner
product, on a module of any dimension. -/
theorem inner_map_apply_left (a : CliffordAlgebra Q) (s t : S) :
    ⟪ρ a s, t⟫_ℂ = ⟪s, ρ (star a) t⟫_ℂ :=
  (ρ.inner_map_eq_map_star_iff_inner_map_cliffordAlgebraι_left.2 hρ.inner_map_ι_apply_left) a s t

/-- On a finite-dimensional Hermitian module, a geometric Clifford action respects Clifford
conjugation `star` for `LinearMap.adjoint`. -/
theorem adjoint_map_eq_map_star [FiniteDimensional ℂ S] (a : CliffordAlgebra Q) :
    LinearMap.adjoint (ρ a) = ρ (star a) :=
  (ρ.adjoint_map_eq_map_star_iff_adjoint_map_cliffordAlgebraι.2 hρ.adjoint_map_ι) a

/-- **A geometric action is a `*`-representation**: under the geometric convention, the
complex-linear extension `ρ_ℂ` satisfies `⟪ρ_ℂ(a) s, t⟫ = ⟪s, ρ_ℂ(conjStar a) t⟫`, on a module
of any dimension. -/
theorem inner_liftBaseChange_apply_left (a : CliffordAlgebra (Q.baseChange ℂ)) (s t : S) :
    ⟪liftBaseChange ℂ Q ρ a s, t⟫_ℂ = ⟪s, liftBaseChange ℂ Q ρ (conjStar Q a) t⟫_ℂ :=
  (inner_liftBaseChange_eq_liftBaseChange_conjStar_iff.2 hρ.inner_map_ι_apply_left) a s t

/-- On a finite-dimensional Hermitian module, the complexification of a geometric Clifford action is
a `*`-representation for `CliffordAlgebra.conjStar`. -/
theorem adjoint_liftBaseChange [FiniteDimensional ℂ S] (a : CliffordAlgebra (Q.baseChange ℂ)) :
    LinearMap.adjoint (liftBaseChange ℂ Q ρ a) = liftBaseChange ℂ Q ρ (conjStar Q a) :=
  (adjoint_liftBaseChange_eq_liftBaseChange_conjStar_iff.2 hρ.adjoint_map_ι) a

end IsGeometricClifford

/-- **The adjoint form of the geometric convention**: on a finite-dimensional module, the
convention says that `Q v = -‖v‖²` and that `c(v)* = -c(v)` for every vector. -/
theorem isGeometricClifford_iff_adjoint [FiniteDimensional ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} :
    ρ.IsGeometricClifford ↔
      (∀ v, Q v = -‖v‖ ^ 2) ∧ ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v) := by
  refine ⟨fun hρ ↦ ⟨hρ.apply_eq_neg_norm_sq, fun v ↦ ?_⟩, fun ⟨hQ, hρ⟩ ↦ ⟨hQ, fun v s t ↦ ?_⟩⟩
  · exact hρ.adjoint_map_ι v
  · rw [← LinearMap.adjoint_inner_right, hρ, LinearMap.neg_apply, inner_neg_right]

/-- On a finite-dimensional complex inner product space, `AlgHom.IsGeometricClifford` is
equivalent to `Q v = -‖v‖²` together with `CliffordAlgebra.liftBaseChange ℂ Q ρ` being a
`*`-representation for `CliffordAlgebra.conjStar`. -/
theorem isGeometricClifford_iff_adjoint_liftBaseChange [FiniteDimensional ℂ S]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S} :
    ρ.IsGeometricClifford ↔
      (∀ v, Q v = -‖v‖ ^ 2) ∧
        ∀ a, LinearMap.adjoint (liftBaseChange ℂ Q ρ a) = liftBaseChange ℂ Q ρ (conjStar Q a) := by
  rw [isGeometricClifford_iff_adjoint, adjoint_liftBaseChange_eq_liftBaseChange_conjStar_iff]

/-- Restricting a complex Clifford algebra map `σ` along `CliffordAlgebra.ofBaseChangeAux ℂ Q`
yields a geometric Clifford action if and only if `Q v = -‖v‖²` and every embedded real
generator `σ (ι (Q.baseChange ℂ) (1 ⊗ₜ v))` is skew-Hermitian. -/
theorem isGeometricClifford_restrictScalars_comp_ofBaseChangeAux_iff
    (σ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S) :
    ((σ.restrictScalars ℝ).comp (ofBaseChangeAux ℂ Q)).IsGeometricClifford ↔
      (∀ v : V, Q v = -‖v‖ ^ 2) ∧
        ∀ (v : V) (s t : S),
          ⟪σ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) s, t⟫_ℂ =
            -⟪s, σ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) t⟫_ℂ := by
  have happ (v : V) :
      ((σ.restrictScalars ℝ).comp (ofBaseChangeAux ℂ Q)) (ι Q v) =
        σ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) :=
    congrArg σ (ofBaseChangeAux_ι ℂ Q v)
  exact (isGeometricClifford_iff _).trans <|
    and_congr_right' <| forall_congr' fun v ↦ forall₂_congr fun s t ↦
      Eq.to_iff congr(⟪$(happ v) s, t⟫_ℂ = -⟪s, $(happ v) t⟫_ℂ)

/-- On a zero-dimensional space `[Subsingleton V]`, every real Clifford algebra homomorphism
`ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S` into a complex inner product space `S` satisfies
`AlgHom.IsGeometricClifford`. -/
theorem isGeometricClifford_of_subsingleton [Subsingleton V]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ S) :
    ρ.IsGeometricClifford where
  apply_eq_neg_norm_sq v := by simp [Subsingleton.elim v 0]
  inner_map_ι_apply_left v s t := by simp [Subsingleton.elim v 0]

end AlgHom

/-! ### Concrete 1D witness on the real line -/

namespace TauCeti

/-- **1D geometric Clifford action**: `ℝ` with `Q r = -r²` acting on `ℂ` via
`CliffordAlgebraComplex.toComplex`, sending `r` to `r • (i • 1)`. -/
noncomputable def realLineGeometricCliffordAction :
    CliffordAlgebra (-QuadraticMap.sq (R := ℝ)) →ₐ[ℝ] Module.End ℂ ℂ :=
  ((Algebra.ofId ℂ (Module.End ℂ ℂ)).restrictScalars ℝ).comp CliffordAlgebraComplex.toComplex

/-- On the real line, a vector `r : ℝ` acts on `ℂ` by `r • (i • 1)`. -/
@[simp]
theorem realLineGeometricCliffordAction_ι (r : ℝ) :
    realLineGeometricCliffordAction (ι (-QuadraticMap.sq (R := ℝ)) r) = r • (Complex.I • 1) := by
  -- `CliffordAlgebraComplex.Q` is definitionally `-QuadraticMap.sq (R := ℝ)`.
  have hQ : (((Algebra.ofId ℂ (Module.End ℂ ℂ)).restrictScalars ℝ).comp
        CliffordAlgebraComplex.toComplex) (ι CliffordAlgebraComplex.Q r) =
      r • (Complex.I • 1) := by
    rw [AlgHom.comp_apply, AlgHom.coe_restrictScalars', CliffordAlgebraComplex.toComplex_ι,
      Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_smul,
      Complex.coe_smul]
  exact hQ

/-- `TauCeti.realLineGeometricCliffordAction` satisfies `AlgHom.IsGeometricClifford`. -/
theorem isGeometricClifford_realLineGeometricCliffordAction :
    realLineGeometricCliffordAction.IsGeometricClifford where
  apply_eq_neg_norm_sq r := by
    simp [QuadraticMap.sq_apply, sq]
  inner_map_ι_apply_left r x y := by
    simp only [realLineGeometricCliffordAction_ι, LinearMap.smul_apply, one_apply_eq_self,
      ← Complex.coe_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, Complex.conj_I]
    ring

end TauCeti
