/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.SesquilinearForm.Star

/-!
# Sesquilinear forms on inner product spaces

A linear map `T : E →ₗ[𝕜] F` defines the sesquilinear form `(x, y) ↦ ⟪x, T y⟫`, and when `F` is
finite-dimensional every sesquilinear form arises from exactly one `T`. This is the linear
equivalence `LinearMap.toSesqForm`, the algebraic counterpart of Mathlib's
`ContinuousLinearMap.toSesqForm`. A sesquilinear form on `E` is Hermitian (`LinearMap.IsSymm`)
exactly when its operator is symmetric (`LinearMap.isSymm_toSesqForm_iff`). In a basis with Gram
matrix `g`, the matrix of the operator `A_a` of a form `a` is `g⁻¹[a]`
(`LinearMap.gram_mul_toMatrix_toSesqForm_symm`).

## Sesquilinear forms with prescribed adjoints

A sesquilinear form on a finite-dimensional inner product space which gives every
endomorphism its usual adjoint is a scalar multiple of the inner product. For a positive
definite real or complex sesquilinear form, the scalar is uniquely determined and positive real.
This is the full-endomorphism-algebra form of the uniqueness of an invariant metric.

The comparison uses Mathlib's rank-one operators: their adjoints exchange the two vectors.
It does not assume that the form being compared is already represented by an operator.

Conversely, a positive definite Hermitian form `h` on a vector space makes it an inner product
space with inner product `h` (`LinearMap.IsSymm.innerProductCore`), and a sesquilinear form which
is real diagonal in some basis is Hermitian (`LinearMap.isSymm_of_basis_diag`).
-/

public section

namespace LinearMap

open InnerProductSpace
open scoped InnerProductSpace

section ToSesqForm

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

variable (𝕜 E F) in
/-- The sesquilinear form `(x, y) ↦ ⟪x, T y⟫` of a linear map `T : E →ₗ[𝕜] F`, as a linear
equivalence onto the sesquilinear forms on `F × E`. The inverse sends a form `a` to the linear
map `y ↦ ∑ i, a (b i) y • b i` for an orthonormal basis `b` of `F`; it is characterized by
`LinearMap.inner_toSesqForm_symm_apply`. -/
noncomputable def toSesqForm : (E →ₗ[𝕜] F) ≃ₗ[𝕜] (F →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) where
  toFun T := (innerₛₗ 𝕜).compl₂ T
  map_add' S T := by ext; simp [inner_add_right]
  map_smul' c T := by ext; simp
  invFun a := ∑ i, (a (stdOrthonormalBasis 𝕜 F i)).smulRight (stdOrthonormalBasis 𝕜 F i)
  left_inv T := by
    ext y
    simpa using (stdOrthonormalBasis 𝕜 F).sum_repr' (T y)
  right_inv a := by
    ext x y
    conv_rhs => rw [← (stdOrthonormalBasis 𝕜 F).sum_repr' x]
    simp [mul_comm]

/-- The value of the sesquilinear form of `T` at `(x, y)` is `⟪x, T y⟫`. -/
@[simp]
theorem toSesqForm_apply_apply (T : E →ₗ[𝕜] F) (x : F) (y : E) :
    toSesqForm 𝕜 E F T x y = ⟪x, T y⟫_𝕜 := by
  simp [toSesqForm]

/-- The linear map of a sesquilinear form `a` represents it through the inner product. -/
@[simp]
theorem inner_toSesqForm_symm_apply (a : F →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (x : F) (y : E) :
    ⟪x, (toSesqForm 𝕜 E F).symm a y⟫_𝕜 = a x y := by
  rw [← toSesqForm_apply_apply, LinearEquiv.apply_symm_apply]

end ToSesqForm

section ToSesqFormEnd

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The identity represents the inner product. -/
@[simp]
theorem toSesqForm_id : toSesqForm 𝕜 E E LinearMap.id = innerₛₗ 𝕜 := by
  ext; simp

/-- The inner product is represented by the identity. -/
@[simp]
theorem toSesqForm_symm_innerₛₗ : (toSesqForm 𝕜 E E).symm (innerₛₗ 𝕜) = LinearMap.id := by
  rw [LinearEquiv.symm_apply_eq, toSesqForm_id]

/-- The sesquilinear form of an operator is Hermitian exactly when the operator is symmetric. -/
theorem isSymm_toSesqForm_iff {T : E →ₗ[𝕜] E} :
    (toSesqForm 𝕜 E E T).IsSymm ↔ T.IsSymmetric := by
  refine ⟨fun h x y ↦ ?_, fun h ↦ ⟨fun x y ↦ ?_⟩⟩
  · simpa [inner_conj_symm] using h.eq y x
  · simp [inner_conj_symm, h y x]

/-- The operator of a Hermitian form is symmetric. -/
theorem IsSymm.isSymmetric_toSesqForm_symm {a : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜} (ha : a.IsSymm) :
    ((toSesqForm 𝕜 E E).symm a).IsSymmetric := by
  rw [← isSymm_toSesqForm_iff, LinearEquiv.apply_symm_apply]
  exact ha

/-- In a basis `b` with Gram matrix `g`, the matrix of the operator `A_a` of a sesquilinear form
`a` satisfies `g·[A_a] = [a]`, so `[A_a] = g⁻¹[a]`. -/
theorem gram_mul_toMatrix_toSesqForm_symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝕜 E) (a : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) :
    Matrix.gram 𝕜 b * LinearMap.toMatrix b b ((toSesqForm 𝕜 E E).symm a) =
      LinearMap.toMatrix₂ b b a := by
  ext i j
  rw [Matrix.mul_apply, LinearMap.toMatrix₂_apply, ← LinearMap.inner_toSesqForm_symm_apply,
    ← b.sum_repr ((toSesqForm 𝕜 E E).symm a (b j)), inner_sum]
  simp [Matrix.gram, LinearMap.toMatrix_apply, inner_smul_right, mul_comm]

end ToSesqFormEnd

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A sesquilinear form with the usual adjoints is determined by its value on any unit vector.
No symmetry or nondegeneracy of the form is required. -/
theorem eq_mul_inner_of_adjoint (H : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜)
    (hH : ∀ (T : Module.End 𝕜 E) x y, H (T x) y = H x (T.adjoint y))
    {u : E} (hu : ‖u‖ = 1) (x y : E) :
    H x y = H u u * inner 𝕜 x y := by
  have h := hH (rankOne 𝕜 x u).toLinearMap u y
  simpa [ContinuousLinearMap.adjoint_toLinearMap, rankOne_apply,
    hu, mul_comm] using h

open scoped ComplexOrder

/-- A positive definite real or complex sesquilinear form giving all endomorphisms their usual
adjoints is a unique positive real multiple of the inner product. Nontriviality is necessary
for uniqueness of the scalar. -/
theorem existsUnique_pos_mul_inner_of_adjoint [Nontrivial E]
    (H : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (hpos : H.IsNonneg)
    (hdef : ∀ x : E, x ≠ 0 → H x x ≠ 0)
    (hH : ∀ (T : Module.End 𝕜 E) x y, H (T x) y = H x (T.adjoint y)) :
    ∃! r : ℝ, 0 < r ∧ ∀ x y, H x y = (r : 𝕜) * inner 𝕜 x y := by
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨u, hu⟩ := exists_norm_eq E zero_le_one
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  obtain ⟨hre, him⟩ := RCLike.nonneg_iff.mp (hpos.nonneg u)
  have hc : H u u = (RCLike.re (H u u) : 𝕜) := by
    apply RCLike.ext <;> simp [him.symm]
  have hr : 0 < RCLike.re (H u u) := lt_of_le_of_ne hre fun h =>
    hdef u hu0 (hc.trans (by simp [h.symm]))
  refine ⟨RCLike.re (H u u), ⟨hr, ?_⟩, ?_⟩
  · intro x y
    exact (eq_mul_inner_of_adjoint H hH hu x y).trans
      (congrArg (· * inner 𝕜 x y) hc)
  · rintro r ⟨_, hr⟩
    have h := hr u u
    rw [inner_self_eq_one_of_norm_eq_one hu, mul_one, hc] at h
    exact (RCLike.ofReal_injective h).symm

section InnerProductCore

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] {h : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜}

/-- The inner product structure on `E` given by a positive definite Hermitian form `h`: the inner
product `⟪u, v⟫` is `h u v`. -/
@[instance_reducible]
def IsSymm.innerProductCore (hh : h.IsSymm) (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (h v v)) :
    InnerProductSpace.Core 𝕜 E where
  inner u v := h u v
  conj_inner_symm u v := hh.eq v u
  re_inner_nonneg v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (hpos v hv).le
  add_left u u' v := by simp
  smul_left u v c := by simp
  definite v hv := by
    by_contra hne
    exact (hpos v hne).ne' (by simpa using congrArg RCLike.re hv)

/-- The inner product of `IsSymm.innerProductCore` is the form. -/
theorem IsSymm.innerProductCore_inner (hh : h.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (h v v)) (u v : E) :
    @inner 𝕜 E (hh.innerProductCore hpos).toInner u v = h u v :=
  (rfl)

/-- The inner product of the inner product space built from `IsSymm.innerProductCore` is the
form. -/
theorem IsSymm.inner_ofCore_innerProductCore (hh : h.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < RCLike.re (h v v)) (u v : E) :
    letI := (hh.innerProductCore hpos).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (hh.innerProductCore hpos).toCore
    inner 𝕜 u v = h u v :=
  (rfl)

/-- **A sesquilinear form which is real diagonal in a basis is Hermitian.** -/
theorem isSymm_of_basis_diag {ι : Type*} [DecidableEq ι] {B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜}
    (bs : Module.Basis ι 𝕜 E) {w : ι → ℝ}
    (hB : ∀ i j, B (bs i) (bs j) = if i = j then (w i : 𝕜) else 0) : B.IsSymm := by
  refine (LinearMap.isSymm_iff_basis bs).2 fun i j ↦ ?_
  rw [hB, hB]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

end InnerProductCore

end LinearMap
