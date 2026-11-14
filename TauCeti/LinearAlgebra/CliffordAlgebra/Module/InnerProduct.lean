/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.QuadraticForm.PosDef
import TauCeti.LinearAlgebra.CliffordAlgebra.Classification
import TauCeti.LinearAlgebra.CliffordAlgebra.Module.Metric
import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# Skew-adjoint Clifford actions on real inner product spaces

Let `Q` be a quadratic form on `M` and `ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E` a Clifford
module structure on a real inner product space `E`. Whenever Clifford vectors act skew-adjointly
with respect to the inner product of `E`:

* each operator `ρ (ι Q v)` sends every `x : E` into `(ℝ ∙ x)ᗮ`
  (`AlgHom.map_cliffordAlgebraι_mem_orthogonal_span_singleton`);
* applying `ρ (ι Q v)` to both arguments scales the inner product by `-Q v`
  (`AlgHom.inner_map_cliffordAlgebraι_apply_map_cliffordAlgebraι_apply`);
* `Q`-orthogonal vectors produce orthogonal images at every point `x : E`
  (`AlgHom.inner_map_cliffordAlgebraι_of_isOrtho`);
* a family of pairwise `Q`-orthogonal vectors squaring to `-1` evaluates at each unit vector
  `x : E` to an orthonormal family in `(ℝ ∙ x)ᗮ` (`AlgHom.orthonormal_map_cliffordAlgebraι_apply`),
  and to an orthonormal basis of `(ℝ ∙ x)ᗮ` when the family has `finrank ℝ E - 1` vectors
  (`AlgHom.orthonormalBasisOrthogonalSpanSingleton`).

Conversely, any finite-dimensional real module `W` over `CliffordAlgebra Q` (where `Q` has a
finite orthogonal basis squaring to `-1`) admits an invariant positive-definite symmetric bilinear
form by `AlgHom.exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι`, and transporting along
`LinearMap.BilinForm.exists_linearEquiv_inner_eq` yields a skew-adjoint `CliffordAlgebra Q`-action
on every real inner product space `E` of the same dimension
(`AlgHom.exists_isSkewAdjoint_inner_cliffordAlgebraι`).

Combining this metric adapter with the real Clifford classification table
(`TauCeti.realClifford_classification`) produces concrete `CliffordAlgebra (realCliffordForm 0 n)`
modules of real dimension `n + 1` for `n ∈ {0, 1, 3, 7}` — namely `ℝ`, `ℂ`, `ℍ[ℝ]`, and `ℝ⁸` —
and hence skew-adjoint `Cliff(0, n)`-actions on every `(n + 1)`-dimensional real inner product
space (`TauCeti.exists_isSkewAdjoint_inner_realCliffordForm_zero`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter I, §§4--5 and §7.
* M. F. Atiyah, R. Bott, and A. Shapiro, *Clifford modules*, Topology 3, Suppl. 1 (1964), 3--38.
-/

public section

open CliffordAlgebra Module
open scoped Quaternion

namespace AlgHom

section CommRing

variable {K M W : Type*} [CommRing K] [AddCommGroup M] [Module K M]
  [AddCommGroup W] [Module K W] {Q : QuadraticForm K M}

/-- Applying the Clifford action of `v` twice scales by `Q v`. -/
@[simp]
theorem map_cliffordAlgebraι_apply_apply (ρ : CliffordAlgebra Q →ₐ[K] Module.End K W)
    (v : M) (x : W) :
    ρ (ι Q v) (ρ (ι Q v) x) = Q v • x := by
  rw [← mul_apply_eq_comp, ← map_mul, ι_sq_scalar, AlgHom.commutes,
    Module.algebraMap_end_apply]

/-- Anticommutator identity for Clifford vector actions: `ρ(u)ρ(v) + ρ(v)ρ(u)` scales by
`QuadraticMap.polar Q u v`. -/
theorem map_cliffordAlgebraι_add_swap_apply (ρ : CliffordAlgebra Q →ₐ[K] Module.End K W)
    (u v : M) (x : W) :
    ρ (ι Q u) (ρ (ι Q v) x) + ρ (ι Q v) (ρ (ι Q u) x) = QuadraticMap.polar Q u v • x := by
  have h := congrArg (fun a ↦ ρ a x) (ι_mul_ι_add_swap (Q := Q) u v)
  simpa only [map_add, map_mul, LinearMap.add_apply, mul_apply_eq_comp, AlgHom.commutes,
    Module.algebraMap_end_apply] using h

/-- Orthogonal Clifford vectors act by anticommuting endomorphisms. -/
theorem map_cliffordAlgebraι_add_swap_apply_of_isOrtho (ρ : CliffordAlgebra Q →ₐ[K] Module.End K W)
    {u v : M} (h : Q.IsOrtho u v) (x : W) :
    ρ (ι Q u) (ρ (ι Q v) x) + ρ (ι Q v) (ρ (ι Q u) x) = 0 := by
  rw [ρ.map_cliffordAlgebraι_add_swap_apply, h.polar_eq_zero, zero_smul]

end CommRing

section InnerProduct

variable {M E : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If `v` acts skew-adjointly on `E`, then `ρ (ι Q v) x` is orthogonal to `x`. -/
theorem inner_self_map_cliffordAlgebraι_apply (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E)
    {v : M} (hskew : ∀ x y, inner ℝ (ρ (ι Q v) x) y = -inner ℝ x (ρ (ι Q v) y)) (x : E) :
    inner ℝ x (ρ (ι Q v) x) = 0 := by
  have h1 := hskew x x
  have h2 : inner ℝ (ρ (ι Q v) x) x = inner ℝ x (ρ (ι Q v) x) :=
    real_inner_comm x (ρ (ι Q v) x)
  linarith

/-- If `v` acts skew-adjointly on `E`, then `ρ (ι Q v) x` lies in `(ℝ ∙ x)ᗮ`. -/
theorem map_cliffordAlgebraι_mem_orthogonal_span_singleton
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) {v : M}
    (hskew : ∀ x y, inner ℝ (ρ (ι Q v) x) y = -inner ℝ x (ρ (ι Q v) y)) (x : E) :
    ρ (ι Q v) x ∈ (ℝ ∙ x)ᗮ :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    (ρ.inner_self_map_cliffordAlgebraι_apply hskew x)

/-- If `v` acts skew-adjointly on `E`, applying `ρ (ι Q v)` to both arguments scales the inner
product by `-Q v`. -/
theorem inner_map_cliffordAlgebraι_apply_map_cliffordAlgebraι_apply
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) {v : M}
    (hskew : ∀ x y, inner ℝ (ρ (ι Q v) x) y = -inner ℝ x (ρ (ι Q v) y)) (x y : E) :
    inner ℝ (ρ (ι Q v) x) (ρ (ι Q v) y) = -Q v * inner ℝ x y := by
  rw [hskew, ρ.map_cliffordAlgebraι_apply_apply, real_inner_smul_right, neg_mul]

/-- A skew-adjoint Clifford vector with `Q v = -1` acts isometrically on `E`. -/
theorem norm_map_cliffordAlgebraι_apply_of_eq_neg_one
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) {v : M}
    (hskew : ∀ x y, inner ℝ (ρ (ι Q v) x) y = -inner ℝ x (ρ (ι Q v) y))
    (hv : Q v = -1) (x : E) :
    ‖ρ (ι Q v) x‖ = ‖x‖ := by
  have hsq : ‖ρ (ι Q v) x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ρ.inner_map_cliffordAlgebraι_apply_map_cliffordAlgebraι_apply hskew, hv, neg_neg, one_mul]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Two `Q`-orthogonal vectors acting skew-adjointly on `E` send any `x : E` to orthogonal
vectors. -/
theorem inner_map_cliffordAlgebraι_of_isOrtho
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) {u v : M}
    (hu : ∀ x y, inner ℝ (ρ (ι Q u) x) y = -inner ℝ x (ρ (ι Q u) y))
    (hv : ∀ x y, inner ℝ (ρ (ι Q v) x) y = -inner ℝ x (ρ (ι Q v) y))
    (horth : Q.IsOrtho u v) (x : E) :
    inner ℝ (ρ (ι Q u) x) (ρ (ι Q v) x) = 0 := by
  have h1 : inner ℝ (ρ (ι Q u) x) (ρ (ι Q v) x) = -inner ℝ x (ρ (ι Q u) (ρ (ι Q v) x)) :=
    hu x (ρ (ι Q v) x)
  have h2 : inner ℝ (ρ (ι Q u) x) (ρ (ι Q v) x) = -inner ℝ x (ρ (ι Q v) (ρ (ι Q u) x)) := by
    rw [real_inner_comm, hv x (ρ (ι Q u) x)]
  have hsum : inner ℝ x (ρ (ι Q u) (ρ (ι Q v) x)) + inner ℝ x (ρ (ι Q v) (ρ (ι Q u) x)) = 0 := by
    rw [← inner_add_right, ρ.map_cliffordAlgebraι_add_swap_apply_of_isOrtho horth,
      inner_zero_right]
  linarith

/-- Evaluating a pairwise `Q`-orthogonal family of Clifford vectors squaring to `-1` with
skew-adjoint actions at a unit vector `x : E` produces an orthonormal family in `E`. -/
theorem orthonormal_map_cliffordAlgebraι_apply
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) {I : Type*} {v : I → M}
    (horth : ∀ i j, i ≠ j → Q.IsOrtho (v i) (v j)) (hQ : ∀ i, Q (v i) = -1)
    (hskew : ∀ i x y, inner ℝ (ρ (ι Q (v i)) x) y = -inner ℝ x (ρ (ι Q (v i)) y))
    {x : E} (hx : ‖x‖ = 1) :
    Orthonormal ℝ fun i ↦ ρ (ι Q (v i)) x := by
  refine ⟨fun i ↦ by rw [ρ.norm_map_cliffordAlgebraι_apply_of_eq_neg_one (hskew i) (hQ i), hx],
    fun {i j} hij ↦ ρ.inner_map_cliffordAlgebraι_of_isOrtho (hskew i) (hskew j) (horth i j hij) x⟩

/-- Evaluating a pairwise `Q`-orthogonal family of Clifford vectors squaring to `-1` with
skew-adjoint actions at a unit vector `x : E` produces an orthonormal family in `(ℝ ∙ x)ᗮ`. -/
theorem orthonormal_orthogonal_map_cliffordAlgebraι_apply
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E) {I : Type*} {v : I → M}
    (horth : ∀ i j, i ≠ j → Q.IsOrtho (v i) (v j)) (hQ : ∀ i, Q (v i) = -1)
    (hskew : ∀ i x y, inner ℝ (ρ (ι Q (v i)) x) y = -inner ℝ x (ρ (ι Q (v i)) y))
    {x : E} (hx : ‖x‖ = 1) :
    Orthonormal ℝ fun i ↦
      (⟨ρ (ι Q (v i)) x,
        ρ.map_cliffordAlgebraι_mem_orthogonal_span_singleton (hskew i) x⟩ : (ℝ ∙ x)ᗮ) := by
  have hon := ρ.orthonormal_map_cliffordAlgebraι_apply horth hQ hskew hx
  exact ⟨fun i ↦ hon.1 i, fun {i j} hij ↦ hon.2 hij⟩

/-- When `Fintype.card I + 1 = finrank ℝ E`, evaluating `I`-many pairwise `Q`-orthogonal Clifford
vectors squaring to `-1` with skew-adjoint actions at a unit vector `x : E` gives an orthonormal
basis of `(ℝ ∙ x)ᗮ`. -/
noncomputable def orthonormalBasisOrthogonalSpanSingleton
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E)
    {I : Type*} [Fintype I] {v : I → M}
    (horth : ∀ i j, i ≠ j → Q.IsOrtho (v i) (v j)) (hQ : ∀ i, Q (v i) = -1)
    (hskew : ∀ i x y, inner ℝ (ρ (ι Q (v i)) x) y = -inner ℝ x (ρ (ι Q (v i)) y))
    (hcard : Fintype.card I + 1 = finrank ℝ E) {x : E} (hx : ‖x‖ = 1) :
    OrthonormalBasis I ℝ (ℝ ∙ x)ᗮ := by
  let : Fact (finrank ℝ E = Fintype.card I + 1) := ⟨hcard.symm⟩
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ (Fintype.card I)
  have hon := ρ.orthonormal_orthogonal_map_cliffordAlgebraι_apply horth hQ hskew hx
  have hfin : finrank ℝ (Submodule.span ℝ (Set.range fun i ↦
      (⟨ρ (ι Q (v i)) x,
        ρ.map_cliffordAlgebraι_mem_orthogonal_span_singleton (hskew i) x⟩ : (ℝ ∙ x)ᗮ))) =
      finrank ℝ (ℝ ∙ x)ᗮ := by
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (hx.symm ▸ one_ne_zero)
    rw [finrank_span_eq_card hon.linearIndependent,
      Submodule.finrank_orthogonal_span_singleton (n := Fintype.card I) hx0]
  exact OrthonormalBasis.mk hon (Submodule.eq_top_of_finrank_eq hfin).ge

@[simp]
theorem coe_orthonormalBasisOrthogonalSpanSingleton_apply
    (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E)
    {I : Type*} [Fintype I] {v : I → M}
    (horth : ∀ i j, i ≠ j → Q.IsOrtho (v i) (v j)) (hQ : ∀ i, Q (v i) = -1)
    (hskew : ∀ i x y, inner ℝ (ρ (ι Q (v i)) x) y = -inner ℝ x (ρ (ι Q (v i)) y))
    (hcard : Fintype.card I + 1 = finrank ℝ E) {x : E} (hx : ‖x‖ = 1) (i : I) :
    (ρ.orthonormalBasisOrthogonalSpanSingleton horth hQ hskew hcard hx i : E) =
      ρ (ι Q (v i)) x := by
  simp [orthonormalBasisOrthogonalSpanSingleton]

/-- **Skew-adjoint Euclidean realization of a negative-definite Clifford module.** If `W` is a
finite-dimensional real `CliffordAlgebra Q`-module, `Q` has a finite orthogonal basis squaring to
`-1`, and `E` is a finite-dimensional real inner product space of the same dimension as `W`, then
`E` carries a `CliffordAlgebra Q`-module structure in which every vector `ι Q v` acts
skew-adjointly with respect to `inner ℝ`. -/
theorem exists_isSkewAdjoint_inner_cliffordAlgebraι
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [FiniteDimensional ℝ E] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ W)
    {I : Type*} [_root_.Finite I] (b : Module.Basis I ℝ M)
    (hb : ∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) (hQ : ∀ i, Q (b i) = -1)
    (hdim : finrank ℝ W = finrank ℝ E) :
    ∃ ρ' : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ E,
      ∀ v x y, inner ℝ (ρ' (ι Q v) x) y = -inner ℝ x (ρ' (ι Q v) y) := by
  obtain ⟨Q₀, hpos⟩ := QuadraticForm.exists_posDef ℝ W
  obtain ⟨B, hBpos, hBsymm, hBskew⟩ :=
    ρ.exists_posDef_isSymm_isSkewAdjoint_map_cliffordAlgebraι b hb hQ hpos
  obtain ⟨e, he⟩ := B.exists_linearEquiv_inner_eq hBpos hBsymm hdim
  refine ⟨(e.conjAlgEquiv ℝ).toAlgHom.comp ρ, fun v x y ↦ ?_⟩
  have hx : e (e.symm x) = x := e.apply_symm_apply x
  have hy : e (e.symm y) = y := e.apply_symm_apply y
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe]
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

namespace TauCeti

/-- For `n ∈ {0, 1, 3, 7}`, the real Clifford classification table supplies a real module `W` of
dimension `n + 1` over `CliffordAlgebra (realCliffordForm 0 n)` (`ℝ`, `ℂ`, `ℍ[ℝ]`, and `ℝ⁸`
respectively). -/
theorem exists_realCliffordForm_zero_module_finrank_eq_succ
    {n : ℕ} (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℝ W) (_ : FiniteDimensional ℝ W),
      finrank ℝ W = n + 1 ∧
        Nonempty (CliffordAlgebra (realCliffordForm 0 n) →ₐ[ℝ] Module.End ℝ W) := by
  rcases hn with rfl | rfl | rfl | rfl
  · obtain ⟨e⟩ := realClifford_classification_of_residue_eq_zero 0 0
      (by rw [realCliffordResidue_def])
    exact ⟨Fin 1 → ℝ, inferInstance, inferInstance, inferInstance, by simp,
      ⟨Matrix.toLinAlgEquiv'.toAlgHom.comp e.toAlgHom⟩⟩
  · obtain ⟨e⟩ := realClifford_classification_of_residue_eq_one 0 1
      (by rw [realCliffordResidue_def])
    refine ⟨ℂ, inferInstance, inferInstance, inferInstance, Complex.finrank_real_complex, ⟨?_⟩⟩
    exact (Algebra.lmul ℝ ℂ).comp ((Matrix.finOneAlgEquiv ℝ ℂ).symm.toAlgHom.comp e.toAlgHom)
  · obtain ⟨e⟩ := realClifford_classification_of_residue_eq_three 0 3
      (by rw [realCliffordResidue_def])
    refine ⟨ℍ[ℝ], inferInstance, inferInstance, inferInstance, Quaternion.finrank_eq_four, ⟨?_⟩⟩
    exact (Algebra.lmul ℝ ℍ[ℝ]).comp
      ((Matrix.finOneAlgEquiv ℝ ℍ[ℝ]).symm.toAlgHom.comp
        ((AlgHom.fst ℝ _ _).comp e.toAlgHom))
  · obtain ⟨e⟩ := realClifford_classification_of_residue_eq_seven 0 7
      (by rw [realCliffordResidue_def])
    exact ⟨Fin 8 → ℝ, inferInstance, inferInstance, inferInstance, by simp,
      ⟨Matrix.toLinAlgEquiv'.toAlgHom.comp ((AlgHom.fst ℝ _ _).comp e.toAlgHom)⟩⟩

/-- **Skew-adjoint `Cliff(0, n)`-actions in Hurwitz dimensions.** For `n ∈ {0, 1, 3, 7}` and any
real inner product space `E` of dimension `n + 1`, there exists an action of
`CliffordAlgebra (realCliffordForm 0 n)` on `E` in which every Clifford vector acts
skew-adjointly. -/
theorem exists_isSkewAdjoint_inner_realCliffordForm_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hdim : finrank ℝ E = n + 1) (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ ρ : CliffordAlgebra (realCliffordForm 0 n) →ₐ[ℝ] Module.End ℝ E,
      ∀ v x y, inner ℝ (ρ (ι (realCliffordForm 0 n) v) x) y =
        -inner ℝ x (ρ (ι (realCliffordForm 0 n) v) y) := by
  let : Fact (finrank ℝ E = n + 1) := ⟨hdim⟩
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨W, _, _, _, hWdim, ⟨ρ₀⟩⟩ := exists_realCliffordForm_zero_module_finrank_eq_succ hn
  let b := Pi.basisFun ℝ (Fin (0 + n))
  have hb : ∀ i j, i ≠ j → (realCliffordForm 0 n).IsOrtho (b i) (b j) := by
    intro i j hij
    simpa only [b, Pi.basisFun_apply] using isOrtho_realCliffordForm_single hij 1 1
  have hQ : ∀ i, realCliffordForm 0 n (b i) = -1 := by
    intro i
    simpa only [b, Pi.basisFun_apply] using realCliffordForm_single_one_of_le (Nat.zero_le _)
  exact ρ₀.exists_isSkewAdjoint_inner_cliffordAlgebraι b hb hQ (hWdim.trans hdim.symm)

end TauCeti
