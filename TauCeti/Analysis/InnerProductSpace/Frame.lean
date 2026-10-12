/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# Finite frames: analysis, synthesis, frame and Gram operators

A finite family `v : ι → E` in an inner product space sits between `E` and the coefficient space
`EuclideanSpace 𝕜 ι` through two maps:

* the *analysis map* `x ↦ (⟪vᵢ, x⟫)ᵢ`, from `E` to coefficient space;
* the *synthesis map* `a ↦ ∑ᵢ aᵢ vᵢ`, from coefficient space to `E`.

They are adjoint to each other. Composing them in the two orders gives the *frame operator*
`x ↦ ∑ᵢ ⟪vᵢ, x⟫ vᵢ` on `E` and the *Gram operator* on coefficient space, whose matrix is Mathlib's
Gram matrix `Matrix.gram 𝕜 v`. Both are positive. They record the same quadratic data on opposite
carriers: the frame operator's form is `x ↦ ∑ᵢ ‖⟪vᵢ, x⟫‖²`, and since the two operators are
`A† A` and `A A†` for the analysis map `A`, their sorted eigenvalues agree through the smaller
dimension (`LinearMap.eigenvalues_adjoint_comp_self_eq_eigenvalues_self_comp_adjoint`).

This turns lower frame bounds into Gram-spectrum bounds and back: the inequality
`a ‖x‖² ≤ ∑ᵢ ‖⟪vᵢ, x⟫‖²` for all `x` holds exactly when the sorted Gram eigenvalues below
`finrank 𝕜 E` are at least `a`, provided the family has at least `finrank 𝕜 E` members.

For two finite families `u` and `v`, analysis by `u` after synthesis by `v` is their *overlap
operator*, whose matrix is `(⟪uᵢ, vⱼ⟫)ᵢⱼ`; on the diagonal it is the Gram operator.

The definitions and the algebraic identities need no finiteness of `E`; the comparisons with
adjoints and eigenvalues assume `E` finite-dimensional.

## Main declarations

* `TauCeti.analysisMap`, `TauCeti.synthesisMap`: the analysis and synthesis maps of a family.
* `TauCeti.inner_synthesisMap_left`, `TauCeti.adjoint_analysisMap`: synthesis is the adjoint of
  analysis.
* `TauCeti.frameOperator`, `TauCeti.gramOperator`: the frame and Gram operators.
* `TauCeti.gramOperator_eq_toEuclideanLin_gram`: the Gram operator is the Gram matrix acting on
  coefficient space.
* `TauCeti.overlapOperator`: the overlap operator `a ↦ (⟪uᵢ, ∑ⱼ aⱼ vⱼ⟫)ᵢ` of two families,
  with matrix `(⟪uᵢ, vⱼ⟫)ᵢⱼ` (`TauCeti.overlapOperator_eq_toEuclideanLin`); swapping the families
  gives the adjoint (`TauCeti.adjoint_overlapOperator`), and it is `S_u† S_v`
  (`TauCeti.adjoint_synthesisMap_comp_synthesisMap`).
* `TauCeti.isPositive_frameOperator`, `TauCeti.isPositive_gramOperator`: both are positive.
* `OrthonormalBasis.frameOperator_eq_id`: an orthonormal basis has the identity as frame
  operator.
* `TauCeti.norm_analysisMap_sq`: `‖analysis x‖² = ∑ᵢ ‖⟪vᵢ, x⟫‖²`.
* `TauCeti.eigenvalues_frameOperator_eq_eigenvalues_gramOperator`: the two sorted spectra agree
  through the smaller dimension.
* `TauCeti.le_eigenvalues_gramOperator`: a lower frame bound `a` bounds the Gram eigenvalues
  below `finrank 𝕜 E` from below by `a`.
* `TauCeti.mul_norm_sq_le_sum_norm_inner_sq_of_le_eigenvalues_gramOperator`: conversely, such
  a Gram-spectrum bound gives the lower frame bound when the family has at least `finrank 𝕜 E`
  members.

## References

* O. Christensen, *An Introduction to Frames and Riesz Bases*, second edition, Birkhäuser, 2016,
  Chapter 1 (frames in finite-dimensional inner product spaces, the frame operator and the
  Gram matrix).
-/

public section

open Module (finrank)
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

/-! ### Analysis and synthesis -/

variable (𝕜) in
/-- The analysis map `x ↦ (⟪vᵢ, x⟫)ᵢ` of a finite family `v`, from the ambient space to
coefficient space. -/
noncomputable def analysisMap (v : ι → E) : E →ₗ[𝕜] EuclideanSpace 𝕜 ι where
  toFun x := WithLp.toLp 2 fun i ↦ ⟪v i, x⟫_𝕜
  map_add' x y := by ext i; simp [inner_add_right]
  map_smul' c x := by ext i; simp [inner_smul_right]

variable (𝕜) in
/-- The synthesis map `a ↦ ∑ᵢ aᵢ vᵢ` of a finite family `v`, from coefficient space to the ambient
space. -/
noncomputable def synthesisMap (v : ι → E) : EuclideanSpace 𝕜 ι →ₗ[𝕜] E :=
  Fintype.linearCombination 𝕜 v ∘ₗ (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).toLinearMap

omit [Fintype ι] in
@[simp]
theorem analysisMap_apply (v : ι → E) (x : E) (i : ι) : analysisMap 𝕜 v x i = ⟪v i, x⟫_𝕜 :=
  (rfl)

@[simp]
theorem synthesisMap_apply (v : ι → E) (a : EuclideanSpace 𝕜 ι) :
    synthesisMap 𝕜 v a = ∑ i, a i • v i := by
  simp [synthesisMap, Fintype.linearCombination_apply]

theorem synthesisMap_single [DecidableEq ι] (v : ι → E) (i : ι) (c : 𝕜) :
    synthesisMap 𝕜 v (EuclideanSpace.single i c) = c • v i := by
  simp

/-- The synthesis map is adjoint to the analysis map:
`⟪∑ᵢ aᵢ vᵢ, x⟫ = ⟪a, (⟪vᵢ, x⟫)ᵢ⟫`. -/
theorem inner_synthesisMap_left (v : ι → E) (a : EuclideanSpace 𝕜 ι) (x : E) :
    ⟪synthesisMap 𝕜 v a, x⟫_𝕜 = ⟪a, analysisMap 𝕜 v x⟫_𝕜 := by
  simp [sum_inner, inner_smul_left, PiLp.inner_apply, mul_comm]

/-- `‖analysis x‖² = ∑ᵢ ‖⟪vᵢ, x⟫‖²`. -/
theorem norm_analysisMap_sq (v : ι → E) (x : E) :
    ‖analysisMap 𝕜 v x‖ ^ 2 = ∑ i, ‖⟪v i, x⟫_𝕜‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq]

/-! ### The frame and Gram operators -/

variable (𝕜) in
/-- The frame operator `x ↦ ∑ᵢ ⟪vᵢ, x⟫ vᵢ` of a finite family: synthesis after analysis. -/
noncomputable def frameOperator (v : ι → E) : E →ₗ[𝕜] E :=
  synthesisMap 𝕜 v ∘ₗ analysisMap 𝕜 v

variable (𝕜) in
/-- The Gram operator of a finite family on coefficient space: analysis after synthesis. Its
matrix is the Gram matrix `Matrix.gram 𝕜 v` (`TauCeti.gramOperator_eq_toEuclideanLin_gram`). -/
noncomputable def gramOperator (v : ι → E) : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι :=
  analysisMap 𝕜 v ∘ₗ synthesisMap 𝕜 v

theorem frameOperator_def (v : ι → E) :
    frameOperator 𝕜 v = synthesisMap 𝕜 v ∘ₗ analysisMap 𝕜 v :=
  (rfl)

theorem gramOperator_def (v : ι → E) :
    gramOperator 𝕜 v = analysisMap 𝕜 v ∘ₗ synthesisMap 𝕜 v :=
  (rfl)

@[simp]
theorem frameOperator_apply (v : ι → E) (x : E) :
    frameOperator 𝕜 v x = ∑ i, ⟪v i, x⟫_𝕜 • v i := by
  simp [frameOperator_def]

@[simp]
theorem gramOperator_apply (v : ι → E) (a : EuclideanSpace 𝕜 ι) (i : ι) :
    gramOperator 𝕜 v a i = ∑ j, ⟪v i, v j⟫_𝕜 * a j := by
  simp [gramOperator_def, mul_comm]

/-- The Gram operator is the Gram matrix `Matrix.gram 𝕜 v` acting on coefficient space. -/
theorem gramOperator_eq_toEuclideanLin_gram [DecidableEq ι] (v : ι → E) :
    gramOperator 𝕜 v = Matrix.toEuclideanLin (Matrix.gram 𝕜 v) := by
  ext a i
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.gram_apply]

/-- The sesquilinear form of the frame operator is the inner product of analysis
coefficients. -/
theorem inner_frameOperator_left (v : ι → E) (x y : E) :
    ⟪frameOperator 𝕜 v x, y⟫_𝕜 = ⟪analysisMap 𝕜 v x, analysisMap 𝕜 v y⟫_𝕜 :=
  inner_synthesisMap_left v _ y

/-- The sesquilinear form of the Gram operator is the inner product of the synthesized
vectors. -/
theorem inner_gramOperator_right (v : ι → E) (a b : EuclideanSpace 𝕜 ι) :
    ⟪a, gramOperator 𝕜 v b⟫_𝕜 = ⟪synthesisMap 𝕜 v a, synthesisMap 𝕜 v b⟫_𝕜 :=
  (inner_synthesisMap_left v a _).symm

/-- The quadratic form of the frame operator is `x ↦ ∑ᵢ ‖⟪vᵢ, x⟫‖²`. -/
theorem re_inner_frameOperator_apply_self (v : ι → E) (x : E) :
    RCLike.re ⟪frameOperator 𝕜 v x, x⟫_𝕜 = ∑ i, ‖⟪v i, x⟫_𝕜‖ ^ 2 := by
  rw [inner_frameOperator_left, inner_self_eq_norm_sq, norm_analysisMap_sq]

/-- The frame operator is symmetric. -/
theorem isSymmetric_frameOperator (v : ι → E) : (frameOperator 𝕜 v).IsSymmetric := fun x y ↦ by
  rw [inner_frameOperator_left, ← inner_conj_symm x, inner_frameOperator_left, inner_conj_symm]

/-- The frame operator is positive. -/
theorem isPositive_frameOperator (v : ι → E) : (frameOperator 𝕜 v).IsPositive :=
  ⟨isSymmetric_frameOperator v, fun x ↦ by
    rw [re_inner_frameOperator_apply_self]
    positivity⟩

/-- The Gram operator is positive. -/
theorem isPositive_gramOperator (v : ι → E) : (gramOperator 𝕜 v).IsPositive := by
  classical
  rw [gramOperator_eq_toEuclideanLin_gram, Matrix.isPositive_toEuclideanLin_iff]
  exact Matrix.posSemidef_gram 𝕜 v

/-- The Gram operator is symmetric. -/
theorem isSymmetric_gramOperator (v : ι → E) : (gramOperator 𝕜 v).IsSymmetric :=
  (isPositive_gramOperator v).isSymmetric

/-! ### The overlap operator of two families -/

section Overlap

variable {κ : Type*} [Fintype κ]

variable (𝕜) in
omit [Fintype ι] in
/-- The overlap operator of finite families `u : ι → E` and `v : κ → E`: analysis by `u` after
synthesis by `v`, with matrix `(⟪uᵢ, vⱼ⟫)ᵢⱼ` (`TauCeti.overlapOperator_eq_toEuclideanLin`). On the
diagonal it is the Gram operator (`TauCeti.overlapOperator_self`). -/
noncomputable def overlapOperator (u : ι → E) (v : κ → E) :
    EuclideanSpace 𝕜 κ →ₗ[𝕜] EuclideanSpace 𝕜 ι :=
  analysisMap 𝕜 u ∘ₗ synthesisMap 𝕜 v

omit [Fintype ι] in
theorem overlapOperator_def (u : ι → E) (v : κ → E) :
    overlapOperator 𝕜 u v = analysisMap 𝕜 u ∘ₗ synthesisMap 𝕜 v :=
  (rfl)

omit [Fintype ι] in
/-- The `i`-th coordinate of the overlap operator applied to `a` is `∑ⱼ ⟪uᵢ, vⱼ⟫ aⱼ`, the
matrix `(⟪uᵢ, vⱼ⟫)ᵢⱼ` acting on the coefficients `a`. -/
@[simp]
theorem overlapOperator_apply (u : ι → E) (v : κ → E) (a : EuclideanSpace 𝕜 κ) (i : ι) :
    overlapOperator 𝕜 u v a i = ∑ j, ⟪u i, v j⟫_𝕜 * a j := by
  simp [overlapOperator_def, mul_comm]

omit [Fintype ι] in
/-- The overlap operator sends the `j`-th coordinate vector, scaled by `c`, to `c` times the
coefficients `(⟪uᵢ, vⱼ⟫)ᵢ` of `vⱼ`. -/
@[simp]
theorem overlapOperator_single [DecidableEq κ] (u : ι → E) (v : κ → E) (j : κ) (c : 𝕜) :
    overlapOperator 𝕜 u v (EuclideanSpace.single j c) = c • analysisMap 𝕜 u (v j) := by
  rw [overlapOperator_def, LinearMap.comp_apply, synthesisMap_single, map_smul]

omit [Fintype ι] in
/-- The overlap operator is the matrix `(⟪uᵢ, vⱼ⟫)ᵢⱼ` acting on coefficient space. -/
theorem overlapOperator_eq_toEuclideanLin [DecidableEq κ] (u : ι → E) (v : κ → E) :
    overlapOperator 𝕜 u v = Matrix.toEuclideanLin (Matrix.of fun i j ↦ ⟪u i, v j⟫_𝕜) := by
  ext a i
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-- The overlap operator of a family with itself is its Gram operator. -/
@[simp]
theorem overlapOperator_self (v : ι → E) : overlapOperator 𝕜 v v = gramOperator 𝕜 v := by
  rw [overlapOperator_def, gramOperator_def]

/-- The overlap operators in the two orders are adjoint to each other:
`⟪O_{v,u} b, a⟫ = ⟪b, O_{u,v} a⟫`. -/
theorem inner_overlapOperator_left (u : ι → E) (v : κ → E) (b : EuclideanSpace 𝕜 ι)
    (a : EuclideanSpace 𝕜 κ) :
    ⟪overlapOperator 𝕜 v u b, a⟫_𝕜 = ⟪b, overlapOperator 𝕜 u v a⟫_𝕜 := by
  rw [overlapOperator_def, overlapOperator_def, LinearMap.comp_apply, LinearMap.comp_apply,
    ← inner_synthesisMap_left u b, ← inner_conj_symm (synthesisMap 𝕜 u b),
    inner_synthesisMap_left v a, inner_conj_symm]

/-- Swapping the two families gives the adjoint overlap operator. -/
@[simp]
theorem adjoint_overlapOperator (u : ι → E) (v : κ → E) :
    LinearMap.adjoint (overlapOperator 𝕜 u v) = overlapOperator 𝕜 v u :=
  ((LinearMap.eq_adjoint_iff _ _).mpr (inner_overlapOperator_left u v)).symm

end Overlap

/-! ### Adjoints in finite dimension -/

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- The adjoint of the analysis map is the synthesis map. -/
@[simp]
theorem adjoint_analysisMap (v : ι → E) :
    LinearMap.adjoint (analysisMap 𝕜 v) = synthesisMap 𝕜 v :=
  ((LinearMap.eq_adjoint_iff _ _).mpr (inner_synthesisMap_left v)).symm

/-- The adjoint of the synthesis map is the analysis map. -/
@[simp]
theorem adjoint_synthesisMap (v : ι → E) :
    LinearMap.adjoint (synthesisMap 𝕜 v) = analysisMap 𝕜 v := by
  rw [← adjoint_analysisMap, LinearMap.adjoint_adjoint]

/-- The frame operator is the source Gram operator `A† A` of the analysis map `A`. -/
theorem frameOperator_eq_adjoint_comp_self (v : ι → E) :
    frameOperator 𝕜 v = LinearMap.adjoint (analysisMap 𝕜 v) ∘ₗ analysisMap 𝕜 v := by
  rw [adjoint_analysisMap, frameOperator_def]

/-- The Gram operator is the target Gram operator `A A†` of the analysis map `A`. -/
theorem gramOperator_eq_self_comp_adjoint (v : ι → E) :
    gramOperator 𝕜 v = analysisMap 𝕜 v ∘ₗ LinearMap.adjoint (analysisMap 𝕜 v) := by
  rw [adjoint_analysisMap, gramOperator_def]

/-- In a finite-dimensional space the overlap operator is `S_u† S_v` for the synthesis maps `S_u`
and `S_v`; for orthonormal families these are the coordinate isometries
`Orthonormal.synthesisMapIsometry`. -/
theorem adjoint_synthesisMap_comp_synthesisMap {κ : Type*} [Fintype κ] (u : ι → E) (v : κ → E) :
    LinearMap.adjoint (synthesisMap 𝕜 u) ∘ₗ synthesisMap 𝕜 v = overlapOperator 𝕜 u v := by
  rw [adjoint_synthesisMap, overlapOperator_def]

/-! ### Frame bounds and the Gram spectrum -/

/-- The sorted eigenvalues of the frame operator and of the Gram operator agree at every index
below both `finrank 𝕜 E` and the size of the family. -/
theorem eigenvalues_frameOperator_eq_eigenvalues_gramOperator (v : ι → E) {d m : ℕ}
    (hd : finrank 𝕜 E = d) (hm : finrank 𝕜 (EuclideanSpace 𝕜 ι) = m) {i : ℕ} (hid : i < d)
    (him : i < m) :
    (isSymmetric_frameOperator v).eigenvalues hd ⟨i, hid⟩ =
      (isSymmetric_gramOperator v).eigenvalues hm ⟨i, him⟩ := by
  rw [LinearMap.IsSymmetric.eigenvalues_congr (frameOperator_eq_adjoint_comp_self v) _
      (analysisMap 𝕜 v).isSymmetric_adjoint_comp_self hd,
    LinearMap.IsSymmetric.eigenvalues_congr (gramOperator_eq_self_comp_adjoint v) _
      (analysisMap 𝕜 v).isSymmetric_self_comp_adjoint hm]
  exact (analysisMap 𝕜 v).eigenvalues_adjoint_comp_self_eq_eigenvalues_self_comp_adjoint hd hm
    hid him

/-- **Gram spectrum from a lower frame bound.** If `a ‖x‖² ≤ ∑ᵢ ‖⟪vᵢ, x⟫‖²` for every `x`, then
every sorted eigenvalue of the Gram operator whose index is below `finrank 𝕜 E` is at least
`a`. -/
theorem le_eigenvalues_gramOperator (v : ι → E) {a : ℝ}
    (h : ∀ x, a * ‖x‖ ^ 2 ≤ ∑ i, ‖⟪v i, x⟫_𝕜‖ ^ 2) {m : ℕ}
    (hm : finrank 𝕜 (EuclideanSpace 𝕜 ι) = m) (i : Fin m) (hi : (i : ℕ) < finrank 𝕜 E) :
    a ≤ (isSymmetric_gramOperator v).eigenvalues hm i := by
  have hS := isSymmetric_frameOperator (𝕜 := 𝕜) v
  rw [← eigenvalues_frameOperator_eq_eigenvalues_gramOperator v rfl hm hi i.isLt]
  -- Evaluate the frame form at the unit eigenvector belonging to the `i`-th eigenvalue.
  set e := hS.eigenvectorBasis rfl ⟨i, hi⟩
  have he : RCLike.re ⟪frameOperator 𝕜 v e, e⟫_𝕜 = hS.eigenvalues rfl ⟨i, hi⟩ := by
    rw [hS.apply_eigenvectorBasis, inner_smul_left, RCLike.conj_ofReal,
      inner_self_eq_norm_sq_to_K, (hS.eigenvectorBasis rfl).orthonormal.1]
    simp
  have hfe := h e
  rwa [(hS.eigenvectorBasis rfl).orthonormal.1 ⟨i, hi⟩, one_pow, mul_one,
    ← re_inner_frameOperator_apply_self, he] at hfe

/-- **Lower frame bound from the Gram spectrum.** If the family has at least `finrank 𝕜 E`
members and the sorted Gram eigenvalues below index `finrank 𝕜 E` are at least `a`, then
`a ‖x‖² ≤ ∑ᵢ ‖⟪vᵢ, x⟫‖²` for every `x`. -/
theorem mul_norm_sq_le_sum_norm_inner_sq_of_le_eigenvalues_gramOperator (v : ι → E) {a : ℝ} {m : ℕ}
    (hm : finrank 𝕜 (EuclideanSpace 𝕜 ι) = m) (hdm : finrank 𝕜 E ≤ m)
    (h : ∀ i : Fin m, (i : ℕ) < finrank 𝕜 E → a ≤ (isSymmetric_gramOperator v).eigenvalues hm i)
    (x : E) :
    a * ‖x‖ ^ 2 ≤ ∑ i, ‖⟪v i, x⟫_𝕜‖ ^ 2 := by
  have hS := isSymmetric_frameOperator (𝕜 := 𝕜) v
  rw [← re_inner_frameOperator_apply_self]
  refine hS.le_re_inner_apply_self_of_mem_spanIndices rfl (s := Set.univ) (fun k _ ↦ ?_)
    ((hS.eigenvectorBasis rfl).mem_spanIndices_iff.mpr fun i hi ↦ (hi (Set.mem_univ i)).elim)
  rw [eigenvalues_frameOperator_eq_eigenvalues_gramOperator v rfl hm k.isLt
    (k.isLt.trans_le hdm)]
  exact h ⟨k, k.isLt.trans_le hdm⟩ k.isLt

end FiniteDimensional

end TauCeti

/-! ### Orthonormal bases -/

namespace OrthonormalBasis

open TauCeti

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

/-- The analysis map of an orthonormal basis is its coordinate map `b.repr`. -/
@[simp]
theorem analysisMap_eq_repr (b : OrthonormalBasis ι 𝕜 E) :
    analysisMap 𝕜 b = b.repr.toLinearMap := by
  ext x i
  simp [OrthonormalBasis.repr_apply_apply]

/-- The frame operator of an orthonormal basis is the identity. -/
@[simp]
theorem frameOperator_eq_id (b : OrthonormalBasis ι 𝕜 E) :
    frameOperator 𝕜 b = LinearMap.id := by
  ext x
  simpa using b.sum_repr' x

end OrthonormalBasis
