/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.Positive.Definite
import TauCeti.LinearAlgebra.CliffordAlgebra.Classification
import TauCeti.LinearAlgebra.CliffordAlgebra.Module.Metric
import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# Skew-adjoint negative Clifford modules on real inner product spaces

Let `W` be a finite-dimensional real module over a Clifford algebra `CliffordAlgebra Q` whose
quadratic space admits a finite orthogonal basis squaring to `-1`. Averaging any positive-definite
symmetric bilinear form on `W` (`TauCeti.exists_posDef_quadraticForm`) over the finite signed
monomial group produces an invariant metric on `W` making every Clifford vector act skew-adjointly
(`AlgHom.exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι`). Any real inner product space `E`
of the same finite dimension is isometric to `(W, B)`
(`TauCeti.exists_linearEquiv_inner_eq_of_posDef`), so conjugating the representation transports the
Clifford module to `E` with skew-adjoint vector actions
(`AlgHom.exists_linearEquiv_inner_conjAlgEquiv_map_cliffordAlgebraι_left`).

Evaluating such a representation on an orthogonal family of vectors squaring to `-1` yields an
`ι`-indexed family of linear operators `A_i : E →ₗ[ℝ] E` satisfying `A_i² = -I`,
`A_i A_j + A_j A_i = 0` for `i ≠ j`, and `⟪A_i x, y⟫_ℝ = -⟪x, A_i y⟫_ℝ`, bundled here as
`TauCeti.SkewAdjointCliffordSystem ι E`. Each `A_i` is a linear isometry equivalence of `E`, sends
every vector `x` into `(ℝ ∙ x)ᗮ`, and maps any unit vector `x` to an orthonormal family `i ↦ A_i x`
in `(ℝ ∙ x)ᗮ` — an orthonormal basis when `dim E = |ι| + 1`
(`TauCeti.SkewAdjointCliffordSystem.orthonormalBasisOrthogonal`). Conversely, given any basis `b`
of `(M, Q)` consisting of pairwise `Q`-orthogonal vectors squaring to `-1`, any
`SkewAdjointCliffordSystem I E` lifts via the universal property to a skew-adjoint
`CliffordAlgebra Q`-module structure on `E`
(`TauCeti.SkewAdjointCliffordSystem.toCliffordAlgHom`).

Finally, combining this metric transport with the classification isomorphisms
`Cliff(0, 1) ≅ M₁(ℂ)`, `Cliff(0, 3) ≅ M₁(ℍ) × M₁(ℍ)` and `Cliff(0, 7) ≅ M₈(ℝ) × M₈(ℝ)` from
`TauCeti.realClifford_classification` produces `SkewAdjointCliffordSystem (Fin n) E` on every real
inner product space `E` of dimension `n + 1` for `n ∈ {0, 1, 3, 7}`
(`TauCeti.nonempty_skewAdjointCliffordSystem_of_finrank_eq_succ`).

## Main definitions

* `TauCeti.SkewAdjointCliffordSystem`: an `ι`-indexed family of pairwise anticommuting skew-adjoint
  complex structures on a real inner product space `E`.
* `TauCeti.SkewAdjointCliffordSystem.isometryEquiv`: each generator as a `LinearIsometryEquiv`.
* `TauCeti.SkewAdjointCliffordSystem.ofSkewAdjointAlgHom`: restriction of a skew-adjoint negative
  Clifford module to an orthogonal family of `-1`-vectors.
* `TauCeti.SkewAdjointCliffordSystem.toCliffordAlgHom`: extension of an `I`-indexed system along a
  `-1`-orthogonal basis `b : Module.Basis I ℝ M` to a skew-adjoint representation of
  `CliffordAlgebra Q`.
* `TauCeti.SkewAdjointCliffordSystem.orthonormalBasisOrthogonal`: the orthonormal basis `i ↦ A_i x`
  of `(ℝ ∙ x)ᗮ` at a unit vector `x ∈ E` when `dim E = |ι| + 1`.

## Main results

* `AlgHom.exists_linearEquiv_inner_conjAlgEquiv_map_cliffordAlgebraι_left`: every
  finite-dimensional real module over a negative-definite Clifford algebra conjugates to a
  skew-adjoint module on any real inner product space of the same dimension.
* `TauCeti.SkewAdjointCliffordSystem.orthonormal_op`: at a unit vector `x`, `i ↦ S.op i x` is
  orthonormal.
* `TauCeti.nonempty_skewAdjointCliffordSystem_of_finrank_eq_succ`: a real inner product space of
  dimension `n + 1` admits a `SkewAdjointCliffordSystem (Fin n) E` when `n ∈ {0, 1, 3, 7}`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§4–5.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
-/

public section

noncomputable section

open CliffordAlgebra Module
open scoped InnerProductSpace Quaternion

namespace AlgHom

/-- Any finite-dimensional real module over a Clifford algebra whose quadratic space has a finite
orthogonal basis squaring to `-1` is conjugate, along a linear equivalence into any real inner
product space `E` of the same finite dimension, to a representation in which every Clifford vector
acts skew-adjointly. -/
theorem exists_linearEquiv_inner_conjAlgEquiv_map_cliffordAlgebraι_left
    {M W E : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ W)
    {I : Type*} [_root_.Finite I] (b : Module.Basis I ℝ M)
    (hb : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) (hQ : ∀ i, Q (b i) = -1)
    (hdim : finrank ℝ W = finrank ℝ E) :
    ∃ φ : W ≃ₗ[ℝ] E, ∀ (v : M) (x y : E),
      ⟪((φ.conjAlgEquiv ℝ).toAlgHom.comp ρ) (ι Q v) x, y⟫_ℝ =
        -⟪x, ((φ.conjAlgEquiv ℝ).toAlgHom.comp ρ) (ι Q v) y⟫_ℝ := by
  obtain ⟨Q₀, hQ₀⟩ := TauCeti.exists_posDef_quadraticForm ℝ W
  obtain ⟨B, hBpos, hBsymm, hskew⟩ :=
    ρ.exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι b hb hQ hQ₀
  obtain ⟨φ, hφ⟩ := TauCeti.exists_linearEquiv_inner_eq_of_posDef hdim hBpos hBsymm
  refine ⟨φ, fun v x y ↦ ?_⟩
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply_apply]
  conv_lhs => rw [← φ.apply_symm_apply y, hφ]
  conv_rhs => rw [← φ.apply_symm_apply x, hφ]
  simpa only [Pi.neg_apply, map_neg] using hskew v (φ.symm x) (φ.symm y)

end AlgHom

namespace TauCeti

/-! ### Skew-adjoint Clifford generator systems on real inner product spaces -/

/-- An `ι`-indexed system of pairwise anticommuting skew-adjoint complex structures on a real inner
product space `E`: linear endomorphisms `op i` satisfying `op i (op i x) = -x`,
`op i (op j x) + op j (op i x) = 0` for `i ≠ j`, and `⟪op i x, y⟫_ℝ = -⟪x, op i y⟫_ℝ`.

These are the generator families of modules over negative-definite real Clifford algebras equipped
with an invariant inner product (`ofSkewAdjointAlgHom`, `toCliffordAlgHom`). -/
@[ext]
structure SkewAdjointCliffordSystem (ι E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  /-- The `i`-th skew-adjoint Clifford generator on `E`. -/
  op : ι → E →ₗ[ℝ] E
  /-- Each generator squares to `-1`. -/
  op_op_self (i : ι) (x : E) : op i (op i x) = -x
  /-- Distinct generators anticommute. -/
  op_op_add_swap {i j : ι} (hij : i ≠ j) (x : E) : op i (op j x) + op j (op i x) = 0
  /-- Each generator is skew-adjoint with respect to the inner product on `E`. -/
  inner_op_left (i : ι) (x y : E) : ⟪op i x, y⟫_ℝ = -⟪x, op i y⟫_ℝ

namespace SkewAdjointCliffordSystem

section General

variable {ι ι' E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] (S : SkewAdjointCliffordSystem ι E)

attribute [simp] op_op_self

/-- As a linear map composition, each generator squares to `-LinearMap.id`. -/
@[simp]
theorem op_comp_op (i : ι) : (S.op i).comp (S.op i) = -LinearMap.id :=
  LinearMap.ext (S.op_op_self i)

/-- In the endomorphism ring `Module.End ℝ E`, each generator squares to `-1`. -/
@[simp]
theorem op_mul_op (i : ι) : S.op i * S.op i = -1 :=
  LinearMap.ext (S.op_op_self i)

/-- Distinct generators anticommute on vectors. -/
theorem op_anticomm {i j : ι} (hij : i ≠ j) (x : E) :
    S.op i (S.op j x) = -S.op j (S.op i x) :=
  eq_neg_of_add_eq_zero_left (S.op_op_add_swap hij x)

/-- Distinct generators anticommute in `Module.End ℝ E`. -/
theorem op_mul_op_add_swap {i j : ι} (hij : i ≠ j) :
    S.op i * S.op j + S.op j * S.op i = 0 :=
  LinearMap.ext (S.op_op_add_swap hij)

/-- Moving a generator to the left slot of the inner product negates it. -/
theorem inner_op_right (i : ι) (x y : E) : ⟪x, S.op i y⟫_ℝ = -⟪S.op i x, y⟫_ℝ := by
  rw [S.inner_op_left, neg_neg]

/-- Each generator preserves the inner product of `E`. -/
@[simp]
theorem inner_op_op (i : ι) (x y : E) : ⟪S.op i x, S.op i y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [S.inner_op_left, S.op_op_self, inner_neg_right, neg_neg]

/-- Each generator preserves norms on `E`. -/
@[simp]
theorem norm_op (i : ι) (x : E) : ‖S.op i x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, S.inner_op_op]

/-- Every vector is orthogonal to its image under a generator. -/
@[simp]
theorem inner_self_op (i : ι) (x : E) : ⟪x, S.op i x⟫_ℝ = 0 := by
  have h := S.inner_op_left i x x
  rw [real_inner_comm] at h
  linarith

/-- Symmetric form of `inner_self_op`: `⟪S.op i x, x⟫_ℝ = 0`. -/
@[simp]
theorem inner_op_self (i : ι) (x : E) : ⟪S.op i x, x⟫_ℝ = 0 := by
  rw [real_inner_comm, S.inner_self_op]

/-- For every `x : E`, `S.op i x` lies in the orthogonal complement `(ℝ ∙ x)ᗮ`. -/
@[simp]
theorem mem_orthogonal_span_singleton (i : ι) (x : E) : S.op i x ∈ (ℝ ∙ x)ᗮ :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (S.inner_self_op i x)

/-- Distinct generators send any vector `x` to pairwise orthogonal vectors. -/
theorem inner_op_eq_zero_of_ne {i j : ι} (hij : i ≠ j) (x : E) : ⟪S.op i x, S.op j x⟫_ℝ = 0 := by
  have h₁ : ⟪S.op i x, S.op j x⟫_ℝ = -⟪x, S.op i (S.op j x)⟫_ℝ := S.inner_op_left i x (S.op j x)
  have h₂ : ⟪S.op i x, S.op j x⟫_ℝ = -⟪x, S.op j (S.op i x)⟫_ℝ := by
    rw [real_inner_comm, S.inner_op_left j x (S.op i x)]
  have hsum : ⟪x, S.op i (S.op j x)⟫_ℝ + ⟪x, S.op j (S.op i x)⟫_ℝ = 0 := by
    rw [← inner_add_right, S.op_op_add_swap hij x, inner_zero_right]
  linarith

/-- Each generator upgraded to a linear isometry equivalence of `E`, with inverse `-S.op i`. -/
def isometryEquiv (i : ι) : E ≃ₗᵢ[ℝ] E where
  toLinearMap := S.op i
  invFun := -S.op i
  left_inv x := by simp
  right_inv x := by simp
  norm_map' := S.norm_op i

/-- Applying `S.isometryEquiv i` agrees with `S.op i`. -/
@[simp]
theorem isometryEquiv_apply (i : ι) (x : E) : S.isometryEquiv i x = S.op i x := by
  rfl

/-- The inverse of `S.isometryEquiv i` acts as `-S.op i`. -/
@[simp]
theorem isometryEquiv_symm_apply (i : ι) (x : E) : (S.isometryEquiv i).symm x = -S.op i x := by
  rfl

/-- Reindexing a `SkewAdjointCliffordSystem` along an equivalence of index types. -/
def reindex (e : ι' ≃ ι) : SkewAdjointCliffordSystem ι' E where
  op i := S.op (e i)
  op_op_self i := S.op_op_self (e i)
  op_op_add_swap hij := S.op_op_add_swap (e.injective.ne hij)
  inner_op_left i := S.inner_op_left (e i)

/-- Generators of `S.reindex e` are obtained by precomposing the index with `e`. -/
@[simp]
theorem reindex_op (e : ι' ≃ ι) (i : ι') : (S.reindex e).op i = S.op (e i) := by
  rfl

/-- Transporting a `SkewAdjointCliffordSystem` along a linear isometry equivalence of ambient
inner product spaces. -/
def map (f : E ≃ₗᵢ[ℝ] E') : SkewAdjointCliffordSystem ι E' where
  op i := f.toLinearEquiv.conj (S.op i)
  op_op_self i x := by simp [LinearEquiv.conj_apply_apply]
  op_op_add_swap hij x := by
    simp [LinearEquiv.conj_apply_apply, ← map_add, S.op_op_add_swap hij]
  inner_op_left i x y := by
    simp only [LinearEquiv.conj_apply_apply, LinearIsometryEquiv.coe_toLinearEquiv]
    conv_lhs => rw [← f.apply_symm_apply y, f.inner_map_map]
    conv_rhs => rw [← f.apply_symm_apply x, f.inner_map_map]
    exact S.inner_op_left i (f.symm x) (f.symm y)

/-- Generators of `S.map f` act by conjugating `S.op i` with `f`. -/
@[simp]
theorem map_op_apply (f : E ≃ₗᵢ[ℝ] E') (i : ι) (x : E') :
    (S.map f).op i x = f (S.op i (f.symm x)) := by
  simp [map]

/-- The empty `SkewAdjointCliffordSystem` on any real inner product space. -/
def empty [IsEmpty ι] : SkewAdjointCliffordSystem ι E where
  op := isEmptyElim
  op_op_self := isEmptyElim
  op_op_add_swap {i} := isEmptyElim i
  inner_op_left := isEmptyElim

instance [IsEmpty ι] : Unique (SkewAdjointCliffordSystem ι E) where
  default := empty
  uniq _ := by ext i; exact isEmptyElim i

/-! ### Orthonormal families and bases on `(ℝ ∙ x)ᗮ` -/

/-- At any unit vector `x ∈ E`, the vectors `S.op i x` form an orthonormal family in `E`. -/
theorem orthonormal_op {x : E} (hx : ‖x‖ = 1) : Orthonormal ℝ fun i ↦ S.op i x :=
  ⟨fun i ↦ by rw [S.norm_op, hx], fun {_ _} hij ↦ S.inner_op_eq_zero_of_ne hij x⟩

/-- The vector `S.op i x` bundled as an element of `(ℝ ∙ x)ᗮ`. -/
def orthogonalVec (i : ι) (x : E) : (ℝ ∙ x)ᗮ :=
  ⟨S.op i x, S.mem_orthogonal_span_singleton i x⟩

/-- Coercing `S.orthogonalVec i x` back to `E` recovers `S.op i x`. -/
@[simp]
theorem coe_orthogonalVec (i : ι) (x : E) : (S.orthogonalVec i x : E) = S.op i x := by
  rfl

/-- Reindexing `S` reindexes `orthogonalVec`. -/
@[simp]
theorem reindex_orthogonalVec (e : ι' ≃ ι) (i : ι') (x : E) :
    (S.reindex e).orthogonalVec i x = S.orthogonalVec (e i) x := by
  ext
  simp

/-- At any unit vector `x ∈ E`, the vectors `S.orthogonalVec i x` form an orthonormal family in
`(ℝ ∙ x)ᗮ`. -/
theorem orthonormal_orthogonalVec {x : E} (hx : ‖x‖ = 1) :
    Orthonormal ℝ fun i ↦ S.orthogonalVec i x := by
  refine ⟨fun i ↦ ?_, fun {_ _} hij ↦ ?_⟩
  · simp only [← Submodule.norm_coe, coe_orthogonalVec, S.norm_op, hx]
  · simp only [Submodule.coe_inner, coe_orthogonalVec]
    exact S.inner_op_eq_zero_of_ne hij x

/-- When `dim E = |ι| + 1`, the vectors `S.op i x` at any unit vector `x ∈ E` form an orthonormal
basis of the hyperplane `(ℝ ∙ x)ᗮ`. -/
def orthonormalBasisOrthogonal [Fintype ι] (hdim : finrank ℝ E = Fintype.card ι + 1)
    {x : E} (hx : ‖x‖ = 1) : OrthonormalBasis ι ℝ (ℝ ∙ x)ᗮ :=
  have : Fact (finrank ℝ E = Fintype.card ι + 1) := ⟨hdim⟩
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ (Fintype.card ι)
  have hon := S.orthonormal_orthogonalVec hx
  have hfin : finrank ℝ (ℝ ∙ x)ᗮ = Fintype.card ι :=
    Submodule.finrank_orthogonal_span_singleton (norm_ne_zero_iff.mp (hx.trans_ne one_ne_zero))
  have hspan : finrank ℝ (Submodule.span ℝ (Set.range fun i ↦ S.orthogonalVec i x)) =
      finrank ℝ (ℝ ∙ x)ᗮ :=
    (finrank_span_eq_card hon.linearIndependent).trans hfin.symm
  OrthonormalBasis.mk hon (Submodule.eq_top_of_finrank_eq hspan).ge

/-- The `i`-th basis vector of `S.orthonormalBasisOrthogonal` is `S.orthogonalVec i x`. -/
@[simp]
theorem orthonormalBasisOrthogonal_apply [Fintype ι] (hdim : finrank ℝ E = Fintype.card ι + 1)
    {x : E} (hx : ‖x‖ = 1) (i : ι) :
    S.orthonormalBasisOrthogonal hdim hx i = S.orthogonalVec i x := by
  rw [orthonormalBasisOrthogonal, OrthonormalBasis.coe_mk]

/-- Coerced to `E`, the `i`-th basis vector of `S.orthonormalBasisOrthogonal` is `S.op i x`. -/
theorem coe_orthonormalBasisOrthogonal_apply [Fintype ι] (hdim : finrank ℝ E = Fintype.card ι + 1)
    {x : E} (hx : ‖x‖ = 1) (i : ι) :
    ((S.orthonormalBasisOrthogonal hdim hx i : (ℝ ∙ x)ᗮ) : E) = S.op i x := by
  rw [orthonormalBasisOrthogonal_apply, coe_orthogonalVec]

/-- The `i`-th coordinate of `w ∈ (ℝ ∙ x)ᗮ` in `S.orthonormalBasisOrthogonal` is the ambient inner
product `⟪S.op i x, w⟫_ℝ`. -/
@[simp]
theorem orthonormalBasisOrthogonal_repr_apply [Fintype ι] (hdim : finrank ℝ E = Fintype.card ι + 1)
    {x : E} (hx : ‖x‖ = 1) (w : (ℝ ∙ x)ᗮ) (i : ι) :
    (S.orthonormalBasisOrthogonal hdim hx).repr w i = ⟪S.op i x, (w : E)⟫_ℝ := by
  rw [OrthonormalBasis.repr_apply_apply, Submodule.coe_inner, coe_orthonormalBasisOrthogonal_apply]

/-- Reconstructing a vector in `(ℝ ∙ x)ᗮ` from its coordinates `c : EuclideanSpace ℝ ι` gives
`∑ i, c.ofLp i • S.op i x` in `E`. -/
@[simp]
theorem coe_orthonormalBasisOrthogonal_repr_symm_apply [Fintype ι]
    (hdim : finrank ℝ E = Fintype.card ι + 1) {x : E} (hx : ‖x‖ = 1)
    (c : EuclideanSpace ℝ ι) :
    (((S.orthonormalBasisOrthogonal hdim hx).repr.symm c : (ℝ ∙ x)ᗮ) : E) =
      ∑ i, c.ofLp i • S.op i x := by
  rw [← OrthonormalBasis.sum_repr_symm, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Submodule.coe_smul, coe_orthonormalBasisOrthogonal_apply]

end General

/-! ### Comparison with negative-definite Clifford modules -/

section CliffordModule

variable {I M E : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Evaluating a skew-adjoint Clifford-algebra representation on a pairwise `Q`-orthogonal family of
vectors squaring to `-1` produces a `SkewAdjointCliffordSystem`. -/
def ofSkewAdjointAlgHom (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) (v : I → M)
    (hortho : ∀ {i j}, i ≠ j → Q.IsOrtho (v i) (v j)) (hQ : ∀ i, Q (v i) = -1)
    (hskew : ∀ i (x y : E), ⟪ρ (ι Q (v i)) x, y⟫_ℝ = -⟪x, ρ (ι Q (v i)) y⟫_ℝ) :
    SkewAdjointCliffordSystem I E where
  op i := ρ (ι Q (v i))
  op_op_self i x := by
    rw [← mul_apply_eq_comp, comp_ι_sq_scalar ρ, hQ i, map_neg, map_one,
      LinearMap.neg_apply, one_apply_eq_self]
  op_op_add_swap hij x := by
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← LinearMap.add_apply, ← map_mul ρ, ← map_mul ρ,
      ← map_add ρ, ι_mul_ι_add_swap_of_isOrtho (hortho hij), map_zero, LinearMap.zero_apply]
  inner_op_left := hskew

/-- The `i`-th generator of `ofSkewAdjointAlgHom` is `ρ (ι Q (v i))`. -/
@[simp]
theorem ofSkewAdjointAlgHom_op (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) (v : I → M)
    (hortho : ∀ {i j}, i ≠ j → Q.IsOrtho (v i) (v j)) (hQ : ∀ i, Q (v i) = -1)
    (hskew : ∀ i (x y : E), ⟪ρ (ι Q (v i)) x, y⟫_ℝ = -⟪x, ρ (ι Q (v i)) y⟫_ℝ) (i : I) :
    (ofSkewAdjointAlgHom ρ v hortho hQ hskew).op i = ρ (ι Q (v i)) := by
  rfl

/-- Extending an `I`-indexed `SkewAdjointCliffordSystem` along a pairwise `Q`-orthogonal basis
`b : Module.Basis I ℝ M` of vectors squaring to `-1` gives a representation of `CliffordAlgebra Q`
on `E`. -/
def toCliffordAlgHom (S : SkewAdjointCliffordSystem I E) (b : Module.Basis I ℝ M)
    (hb : ∀ {i j}, i ≠ j → Q.IsOrtho (b i) (b j)) (hQ : ∀ i, Q (b i) = -1) :
    CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E :=
  CliffordAlgebra.lift Q ⟨b.constr ℝ S.op,
    (CliffordAlgebra.forall_mul_self_eq_iff (isUnit_of_invertible (2 : Module.End ℝ E)) _).mpr <|
      b.ext fun i ↦ b.ext fun j ↦ by
        simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.compl₂_apply,
          LinearMap.mul_apply', LinearMap.flip_apply, Module.Basis.constr_basis,
          LinearMap.compr₂_apply, QuadraticMap.polarBilin_apply_apply,
          Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
        by_cases hij : i = j
        · subst hij
          rw [S.op_mul_op, QuadraticMap.polar_self, hQ, two_nsmul, add_smul, neg_smul, one_smul]
        · rw [S.op_mul_op_add_swap hij, (hb hij).polar_eq_zero, zero_smul]⟩

/-- `S.toCliffordAlgHom b hb hQ` acts on `ι Q v` as `b.constr ℝ S.op v`. -/
@[simp]
theorem toCliffordAlgHom_ι (S : SkewAdjointCliffordSystem I E) (b : Module.Basis I ℝ M)
    (hb : ∀ {i j}, i ≠ j → Q.IsOrtho (b i) (b j)) (hQ : ∀ i, Q (b i) = -1) (v : M) :
    S.toCliffordAlgHom b hb hQ (ι Q v) = b.constr ℝ S.op v :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- On the `i`-th basis vector `b i`, `S.toCliffordAlgHom` recovers `S.op i`. -/
theorem toCliffordAlgHom_ι_basis (S : SkewAdjointCliffordSystem I E) (b : Module.Basis I ℝ M)
    (hb : ∀ {i j}, i ≠ j → Q.IsOrtho (b i) (b j)) (hQ : ∀ i, Q (b i) = -1) (i : I) :
    S.toCliffordAlgHom b hb hQ (ι Q (b i)) = S.op i := by
  simp

/-- Every Clifford vector acts skew-adjointly under `toCliffordAlgHom`. -/
theorem inner_toCliffordAlgHom_ι_left (S : SkewAdjointCliffordSystem I E)
    (b : Module.Basis I ℝ M) (hb : ∀ {i j}, i ≠ j → Q.IsOrtho (b i) (b j))
    (hQ : ∀ i, Q (b i) = -1) (v : M) (x y : E) :
    ⟪S.toCliffordAlgHom b hb hQ (ι Q v) x, y⟫_ℝ =
      -⟪x, S.toCliffordAlgHom b hb hQ (ι Q v) y⟫_ℝ := by
  rw [toCliffordAlgHom_ι, b.constr_apply, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply,
    sum_inner, inner_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right, S.inner_op_left,
    mul_neg]

end CliffordModule

end SkewAdjointCliffordSystem

/-! ### Concrete skew-adjoint Clifford systems in dimensions `1`, `2`, `4`, and `8` -/

/-- Any finite-dimensional real module `W` over `CliffordAlgebra (realCliffordForm 0 q)` yields a
`SkewAdjointCliffordSystem (Fin q) E` on every real inner product space `E` of the same finite
dimension. -/
theorem nonempty_skewAdjointCliffordSystem_of_algHom_realClifford {q : ℕ} {W E : Type*}
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : CliffordAlgebra (realCliffordForm 0 q) →ₐ[ℝ] Module.End ℝ W)
    (hdim : finrank ℝ W = finrank ℝ E) :
    Nonempty (SkewAdjointCliffordSystem (Fin q) E) := by
  let b := Pi.basisFun ℝ (Fin (0 + q))
  have hb : ∀ i j, i ≠ j → (realCliffordForm 0 q).IsOrtho (b i) (b j) := fun i j hij ↦ by
    simpa only [b, Pi.basisFun_apply] using isOrtho_realCliffordForm_single hij 1 1
  have hQ : ∀ i, realCliffordForm 0 q (b i) = -1 := fun i ↦ by
    simp [b]
  obtain ⟨φ, hφ⟩ :=
    ρ.exists_linearEquiv_inner_conjAlgEquiv_map_cliffordAlgebraι_left b hb hQ hdim
  exact ⟨(SkewAdjointCliffordSystem.ofSkewAdjointAlgHom ((φ.conjAlgEquiv ℝ).toAlgHom.comp ρ) b
    (fun hij ↦ hb _ _ hij) hQ fun i ↦ hφ (b i)).reindex (finCongr (Nat.zero_add q).symm)⟩

/-- Every `2`-dimensional real inner product space admits a `1`-generator skew-adjoint Clifford
system. -/
theorem nonempty_skewAdjointCliffordSystem_of_finrank_eq_two {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (hE : finrank ℝ E = 2) :
    Nonempty (SkewAdjointCliffordSystem (Fin 1) E) := by
  have : Fact (finrank ℝ E = 1 + 1) := ⟨hE⟩
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 1
  obtain ⟨e⟩ := realClifford_classification_of_residue_eq_one 0 1
    (by rw [realCliffordResidue_def])
  let ρ : CliffordAlgebra (realCliffordForm 0 1) →ₐ[ℝ] Module.End ℝ ℂ :=
    (Algebra.lmul ℝ ℂ).comp ((Matrix.finOneAlgEquiv ℝ ℂ).symm.toAlgHom.comp e.toAlgHom)
  exact nonempty_skewAdjointCliffordSystem_of_algHom_realClifford ρ
    (Complex.finrank_real_complex.trans hE.symm)

/-- Every `4`-dimensional real inner product space admits a `3`-generator skew-adjoint Clifford
system. -/
theorem nonempty_skewAdjointCliffordSystem_of_finrank_eq_four {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (hE : finrank ℝ E = 4) :
    Nonempty (SkewAdjointCliffordSystem (Fin 3) E) := by
  have : Fact (finrank ℝ E = 3 + 1) := ⟨hE⟩
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 3
  obtain ⟨e⟩ := realClifford_classification_of_residue_eq_three 0 3
    (by rw [realCliffordResidue_def])
  let ρ : CliffordAlgebra (realCliffordForm 0 3) →ₐ[ℝ] Module.End ℝ ℍ[ℝ] :=
    (Algebra.lmul ℝ ℍ[ℝ]).comp
      ((Matrix.finOneAlgEquiv ℝ ℍ[ℝ]).symm.toAlgHom.comp
        ((AlgHom.fst ℝ _ _).comp e.toAlgHom))
  exact nonempty_skewAdjointCliffordSystem_of_algHom_realClifford ρ
    (Quaternion.finrank_eq_four.trans hE.symm)

/-- Every `8`-dimensional real inner product space admits a `7`-generator skew-adjoint Clifford
system. -/
theorem nonempty_skewAdjointCliffordSystem_of_finrank_eq_eight {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (hE : finrank ℝ E = 8) :
    Nonempty (SkewAdjointCliffordSystem (Fin 7) E) := by
  have : Fact (finrank ℝ E = 7 + 1) := ⟨hE⟩
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 7
  obtain ⟨e⟩ := realClifford_classification_of_residue_eq_seven 0 7
    (by rw [realCliffordResidue_def])
  let ρ : CliffordAlgebra (realCliffordForm 0 7) →ₐ[ℝ] Module.End ℝ (Fin 8 → ℝ) :=
    (Matrix.toLinAlgEquiv' (R := ℝ) (n := Fin 8)).toAlgHom.comp
      ((AlgHom.fst ℝ _ _).comp e.toAlgHom)
  have hW : finrank ℝ (Fin 8 → ℝ) = 8 := by simp
  exact nonempty_skewAdjointCliffordSystem_of_algHom_realClifford ρ (hW.trans hE.symm)

/-- Every real inner product space of dimension `n + 1` with `n ∈ {0, 1, 3, 7}` admits an
`n`-generator skew-adjoint Clifford system. -/
theorem nonempty_skewAdjointCliffordSystem_of_finrank_eq_succ {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (hE : finrank ℝ E = n + 1)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    Nonempty (SkewAdjointCliffordSystem (Fin n) E) := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨SkewAdjointCliffordSystem.empty⟩
  · exact nonempty_skewAdjointCliffordSystem_of_finrank_eq_two hE
  · exact nonempty_skewAdjointCliffordSystem_of_finrank_eq_four hE
  · exact nonempty_skewAdjointCliffordSystem_of_finrank_eq_eight hE

end TauCeti
