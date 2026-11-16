/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import TauCeti.Analysis.InnerProductSpace.QuadraticForm.PosDef
import TauCeti.LinearAlgebra.CliffordAlgebra.Module.Metric
import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# Skew-adjoint Clifford actions on real inner product spaces

Let `Q` be a quadratic form on `M` and `ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E` a Clifford
module structure on a real inner product space `E`. Whenever Clifford vectors act skew-adjointly
with respect to the inner product of `E` (`(innerₗ E).IsSkewAdjoint (ρ (ι Q v))`):

* each operator `ρ (ι Q v)` sends every `x : E` into `(ℝ ∙ x)ᗮ`
  (`AlgHom.inner_self_map_cliffordAlgebraι_apply_eq_zero`,
  `AlgHom.map_cliffordAlgebraι_mem_orthogonal_span_singleton`);
* applying `ρ (ι Q v)` to both arguments scales the inner product by `-Q v`
  (`AlgHom.inner_map_cliffordAlgebraι_apply_map_cliffordAlgebraι_apply`, obtained as the
  `B := innerₗ E` specialization of
  `AlgHom.bilinForm_map_cliffordAlgebraι_apply_map_cliffordAlgebraι_apply`);
* `Q`-orthogonal vectors produce orthogonal images at every point `x : E`
  (`AlgHom.inner_map_cliffordAlgebraι_apply_eq_zero_of_isOrtho`);
* a family of pairwise `Q`-orthogonal vectors squaring to `-1` evaluates at each unit vector
  `x : E` to an orthonormal family in `E` and in `(ℝ ∙ x)ᗮ`
  (`AlgHom.orthonormal_map_cliffordAlgebraι_apply`,
  `AlgHom.orthonormal_orthogonal_map_cliffordAlgebraι_apply`).

Conversely, any finite-dimensional real module `W` over `CliffordAlgebra Q` (where `Q` has a
finite orthogonal basis squaring to `-1`) admits an invariant positive-definite symmetric bilinear
form by `AlgHom.exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι`, and transporting along
`LinearMap.BilinForm.exists_linearEquiv_inner_eq` yields a skew-adjoint `CliffordAlgebra Q`-action
on every real inner product space `E` of the same dimension
(`AlgHom.exists_isSkewAdjoint_inner_cliffordAlgebraι`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter I, §§4--5 and §7.
* M. F. Atiyah, R. Bott, and A. Shapiro, *Clifford modules*, Topology 3, Suppl. 1 (1964), 3--38.
-/

public section

open CliffordAlgebra Module

namespace AlgHom

section InnerProduct

variable {M E : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If `v` acts skew-adjointly on `E`, then `ρ (ι Q v) x` is orthogonal to `x`. -/
theorem inner_self_map_cliffordAlgebraι_apply_eq_zero
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) {v : M}
    (hskew : (innerₗ E).IsSkewAdjoint (ρ (ι Q v))) (x : E) :
    inner ℝ x (ρ (ι Q v) x) = 0 := by
  have h1 : inner ℝ (ρ (ι Q v) x) x = -inner ℝ x (ρ (ι Q v) x) := by
    simpa only [innerₗ_apply_apply, Pi.neg_apply, inner_neg_right] using hskew x x
  have h2 : inner ℝ (ρ (ι Q v) x) x = inner ℝ x (ρ (ι Q v) x) :=
    real_inner_comm x (ρ (ι Q v) x)
  linarith

/-- If `v` acts skew-adjointly on `E`, then `ρ (ι Q v) x` lies in `(ℝ ∙ x)ᗮ`. -/
theorem map_cliffordAlgebraι_mem_orthogonal_span_singleton
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) {v : M}
    (hskew : (innerₗ E).IsSkewAdjoint (ρ (ι Q v))) (x : E) :
    ρ (ι Q v) x ∈ (ℝ ∙ x)ᗮ :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    (ρ.inner_self_map_cliffordAlgebraι_apply_eq_zero hskew x)

/-- If `v` acts skew-adjointly on `E`, applying `ρ (ι Q v)` to both arguments scales the inner
product by `-Q v`. -/
theorem inner_map_cliffordAlgebraι_apply_map_cliffordAlgebraι_apply
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) {v : M}
    (hskew : (innerₗ E).IsSkewAdjoint (ρ (ι Q v))) (x y : E) :
    inner ℝ (ρ (ι Q v) x) (ρ (ι Q v) y) = -Q v * inner ℝ x y :=
  ρ.bilinForm_map_cliffordAlgebraι_apply_map_cliffordAlgebraι_apply (innerₗ E) v hskew x y

/-- A skew-adjoint Clifford vector with `Q v = -1` acts isometrically on `E`. -/
theorem norm_map_cliffordAlgebraι_apply_of_eq_neg_one
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) {v : M}
    (hskew : (innerₗ E).IsSkewAdjoint (ρ (ι Q v)))
    (hv : Q v = -1) (x : E) :
    ‖ρ (ι Q v) x‖ = ‖x‖ := by
  have hsq : ‖ρ (ι Q v) x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ρ.inner_map_cliffordAlgebraι_apply_map_cliffordAlgebraι_apply hskew, hv, neg_neg, one_mul]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Two `Q`-orthogonal vectors acting skew-adjointly on `E` send any `x : E` to orthogonal
vectors. -/
theorem inner_map_cliffordAlgebraι_apply_eq_zero_of_isOrtho
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) {u v : M}
    (hu : (innerₗ E).IsSkewAdjoint (ρ (ι Q u)))
    (hv : (innerₗ E).IsSkewAdjoint (ρ (ι Q v)))
    (horth : Q.IsOrtho u v) (x : E) :
    inner ℝ (ρ (ι Q u) x) (ρ (ι Q v) x) = 0 := by
  have h1 : inner ℝ (ρ (ι Q u) x) (ρ (ι Q v) x) = -inner ℝ x (ρ (ι Q u) (ρ (ι Q v) x)) := by
    simpa only [innerₗ_apply_apply, Pi.neg_apply, inner_neg_right] using hu x (ρ (ι Q v) x)
  have h2 : inner ℝ (ρ (ι Q u) x) (ρ (ι Q v) x) = -inner ℝ x (ρ (ι Q v) (ρ (ι Q u) x)) := by
    rw [real_inner_comm]
    simpa only [innerₗ_apply_apply, Pi.neg_apply, inner_neg_right] using hv x (ρ (ι Q u) x)
  have hsum : inner ℝ x (ρ (ι Q u) (ρ (ι Q v) x)) + inner ℝ x (ρ (ι Q v) (ρ (ι Q u) x)) = 0 := by
    rw [← inner_add_right, ρ.map_cliffordAlgebraι_add_swap_apply_of_isOrtho horth,
      inner_zero_right]
  linarith

/-- Evaluating a pairwise `Q`-orthogonal family of Clifford vectors squaring to `-1` with
skew-adjoint actions at a unit vector `x : E` produces an orthonormal family in `E`. -/
theorem orthonormal_map_cliffordAlgebraι_apply
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) {I : Type*} {v : I → M}
    (horth : ∀ i j, i ≠ j → Q.IsOrtho (v i) (v j)) (hQ : ∀ i, Q (v i) = -1)
    (hskew : ∀ i, (innerₗ E).IsSkewAdjoint (ρ (ι Q (v i))))
    {x : E} (hx : ‖x‖ = 1) :
    Orthonormal ℝ fun i ↦ ρ (ι Q (v i)) x := by
  refine ⟨fun i ↦ by rw [ρ.norm_map_cliffordAlgebraι_apply_of_eq_neg_one (hskew i) (hQ i), hx],
    fun {i j} hij ↦
      ρ.inner_map_cliffordAlgebraι_apply_eq_zero_of_isOrtho (hskew i) (hskew j) (horth i j hij) x⟩

/-- Evaluating a pairwise `Q`-orthogonal family of Clifford vectors squaring to `-1` with
skew-adjoint actions at a unit vector `x : E` produces an orthonormal family in `(ℝ ∙ x)ᗮ`. -/
theorem orthonormal_orthogonal_map_cliffordAlgebraι_apply
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) {I : Type*} {v : I → M}
    (horth : ∀ i j, i ≠ j → Q.IsOrtho (v i) (v j)) (hQ : ∀ i, Q (v i) = -1)
    (hskew : ∀ i, (innerₗ E).IsSkewAdjoint (ρ (ι Q (v i))))
    {x : E} (hx : ‖x‖ = 1) :
    Orthonormal ℝ fun i ↦
      (⟨ρ (ι Q (v i)) x,
        ρ.map_cliffordAlgebraι_mem_orthogonal_span_singleton (hskew i) x⟩ : (ℝ ∙ x)ᗮ) := by
  have hon := ρ.orthonormal_map_cliffordAlgebraι_apply horth hQ hskew hx
  exact ⟨fun i ↦ hon.1 i, fun {i j} hij ↦ hon.2 hij⟩

/-- **Skew-adjoint Euclidean realization of a negative-definite Clifford module.** If `W` is a
finite-dimensional real `CliffordAlgebra Q`-module, `Q` has a finite orthogonal basis squaring to
`-1`, and `E` is a finite-dimensional real inner product space of the same dimension as `W`, then
`E` carries a `CliffordAlgebra Q`-module structure in which every vector `ι Q v` acts
skew-adjointly with respect to `innerₗ E`. -/
theorem exists_isSkewAdjoint_inner_cliffordAlgebraι
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [FiniteDimensional ℝ E] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ W)
    {I : Type*} [_root_.Finite I] (b : Module.Basis I ℝ M)
    (hb : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) (hQ : ∀ i, Q (b i) = -1)
    (hdim : finrank ℝ W = finrank ℝ E) :
    ∃ ρ' : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E,
      ∀ v, (innerₗ E).IsSkewAdjoint (ρ' (ι Q v)) := by
  obtain ⟨Q₀, hpos⟩ := QuadraticForm.exists_posDef ℝ W
  obtain ⟨B, hBpos, hBsymm, hBskew⟩ :=
    ρ.exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι b hb hQ hpos
  obtain ⟨e, he⟩ := B.exists_linearEquiv_inner_eq hBpos hBsymm hdim
  refine ⟨(e.conjAlgEquiv ℝ).toAlgHom.comp ρ, fun v x y ↦ ?_⟩
  have hx : e (e.symm x) = x := e.apply_symm_apply x
  have hy : e (e.symm y) = y := e.apply_symm_apply y
  simp only [innerₗ_apply_apply, Pi.neg_apply, inner_neg_right, AlgHom.comp_apply,
    AlgEquiv.toAlgHom_apply, LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  calc
    inner ℝ (e (ρ (ι Q v) (e.symm x))) y
      = inner ℝ (e (ρ (ι Q v) (e.symm x))) (e (e.symm y)) := by rw [hy]
    _ = B (ρ (ι Q v) (e.symm x)) (e.symm y) := he _ _
    _ = -B (e.symm x) (ρ (ι Q v) (e.symm y)) := by
          rw [hBskew v (e.symm x) (e.symm y), Pi.neg_apply, map_neg]
    _ = -inner ℝ (e (e.symm x)) (e (ρ (ι Q v) (e.symm y))) := by rw [he]
    _ = -inner ℝ x (e (ρ (ι Q v) (e.symm y))) := by rw [hx]

end InnerProduct

end AlgHom
