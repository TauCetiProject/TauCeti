/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import TauCeti.Algebra.Lie.ExteriorPower
public import TauCeti.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.UnitaryGroup
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Basis
import TauCeti.LinearAlgebra.ExteriorPower.Square
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic

/-!
# Norms and linear isometries of exterior powers

The exterior powers `⋀[ℝ]^n E` of a finite-dimensional real inner product space carry Mathlib's
induced inner product, with `⟪v₁ ∧ ⋯ ∧ vₙ, w₁ ∧ ⋯ ∧ wₙ⟫ = det ⟪vⱼ, wᵢ⟫`. This file proves that the
map `⋀ⁿ f` induced by a linear isometry `f` preserves it, so that rotations of an oriented space
act isometrically on its forms, and that infinitesimal rotations, the skew-adjoint endomorphisms,
act skew-adjointly on forms of every degree. It also records that the norm of a wedge
`v₁ ∧ ⋯ ∧ vₙ` is the volume of the parallelepiped spanned by the `vᵢ`, bounded by Hadamard's
inequality. For a real-linear `P : E → ℂ`, it names the two-vector `p₁ ∧ p₂` of the gradients of
`Re P` and `Im P`, which represents the two-form `Im (conj (P u) P w)`. Finally, it packages the
skew endomorphism `u ↦ u ⌟ F` of a two-vector `F`, the operator that represents the two-form
`ω(u, w) = ⟪F, u ∧ w⟫` through the inner product.

## Main definitions

* `ContinuousLinearMap.gradientWedge P`: the wedge `p₁ ∧ p₂` of the vectors representing the
  real and imaginary parts of a complex-valued covector `P`.
* `TauCeti.twoVectorContraction F`: the skew endomorphism `u ↦ u ⌟ F` of a two-vector, with
  `⟪u ⌟ F, w⟫ = ⟪F, u ∧ w⟫`.
* `TauCeti.twoVectorAlternatingSum θ a b c`: the alternating sum
  `θ(a)(b, c) - θ(b)(a, c) + θ(c)(a, b)` of a map with values in two-vectors, which is
  `dω(a, b, c)` for `θ v = ∇_v ω` and a torsion-free connection. It is linear in `θ` and
  alternating in `a`, `b`, `c` (`TauCeti.twoVectorAlternatingSum_swap₁₂`,
  `TauCeti.twoVectorAlternatingSum_swap₂₃`).

## Main results

* `exteriorPower.inner_map_map`: `⟪⋀ⁿ f x, ⋀ⁿ f y⟫ = ⟪x, y⟫` for a linear isometry `f`.
* `exteriorPower.inner_ιMulti_two`: `⟪a ∧ b, u ∧ w⟫ = ⟪a, u⟫ ⟪b, w⟫ - ⟪a, w⟫ ⟪b, u⟫`, and
  `exteriorPower.orthonormal_ιMulti_two_of_orthonormal`: for an orthonormal triple `e, x, y`, the
  wedges `e ∧ x` and `e ∧ y` are orthonormal.
* `exteriorPower.ext_inner_ιMulti`: elements of `⋀ⁿ E` with the same inner products against all
  wedges of vectors are equal, and `exteriorPower.linearMap_ext_inner_ιMulti` is the
  corresponding extensionality principle for linear maps between exterior powers;
  `exteriorPower.ext_inner_ιMulti_two` and `exteriorPower.linearMap_ext_inner_ιMulti_two` test
  only against wedges `u ∧ w` of two vectors.
* `exteriorPower.inner_lieMap_left`: the derivation action `D_A` of a skew-adjoint `A` on
  `⋀ⁿ E` is skew-adjoint, `⟪D_A x, y⟫ = -⟪x, D_A y⟫`.
* `OrthonormalBasis.sum_norm_sq_ιMulti_two`: contraction of squared wedge norms in a basis.
* `OrthonormalBasis.inner_toBasis_exteriorPower`: the induced basis of `⋀ⁿ E` is orthonormal.
* `OrthonormalBasis.ιMulti_two_eq_sum`, `OrthonormalBasis.inner_ιMulti_two_eq_sum`,
  `OrthonormalBasis.eq_sum_inner_smul_ιMulti_two`,
  `OrthonormalBasis.norm_sq_eq_sum_sq_inner_ιMulti_two`: the coordinates of two-vectors in the
  basis `bᵢ ∧ bⱼ` induced by an orthonormal basis `b` of a four-dimensional space.
* `exteriorPower.norm_ιMulti_sq`: `‖v₁ ∧ ⋯ ∧ vₙ‖ ^ 2` is the Gram determinant of `v`.
* `exteriorPower.norm_ιMulti_le_prod_norm`: Hadamard's inequality `‖v₁ ∧ ⋯ ∧ vₙ‖ ≤ ∏ ‖vᵢ‖`, and
  `exteriorPower.norm_ιMulti_two_le`: its case `‖u ∧ w‖ ≤ ‖u‖ ‖w‖` of two vectors.
* `exteriorPower.norm_ιMulti_comp_linearIsometry`, `exteriorPower.norm_ιMulti_comp_perm`,
  `exteriorPower.norm_ιMulti_update_smul`: the volume of a frame is invariant under linear
  isometries and reorderings, and scales by `|c|` when one vector is multiplied by `c`.
* `Orthonormal.norm_ιMulti`: orthonormal frames, the empty frame among them, have volume one.
* `Orthonormal.ιMulti_eq_ιMulti_iff`: two orthonormal frames have the same wedge exactly when they
  differ by a special orthogonal change of frame.
* `exteriorPower.exists_orthonormal_span_eq_and_ιMulti_eq_norm_smul`: every linearly independent
  `n`-frame `v` admits an orthonormal `n`-frame `u` with the same span and
  `v₁ ∧ ⋯ ∧ vₙ = ‖v₁ ∧ ⋯ ∧ vₙ‖ • (u₁ ∧ ⋯ ∧ uₙ)`.
* `ContinuousLinearMap.inner_gradientWedge_ιMulti`: for a real-linear `P : E → ℂ`, the two-form
  `Im (conj (P u) P w)` is represented by `p₁ ∧ p₂`, `⟪p₁ ∧ p₂, u ∧ w⟫ = Im (conj (P u) P w)`,
  and `ContinuousLinearMap.norm_gradientWedge_le`: `‖p₁ ∧ p₂‖ ≤ ‖P‖ ^ 2`.
* `TauCeti.inner_twoVectorContraction_apply`: the contraction `u ⌟ F` of a two-vector
  `F ∈ ⋀² V` by `⟪u, ·⟫` (`TauCeti.twoVectorContraction`) represents the two-form of `F`,
  `⟪u ⌟ F, w⟫ = ⟪F, u ∧ w⟫`: on two-forms, wedging with `u` is adjoint to contracting with
  `⟪u, ·⟫`. So `u ↦ u ⌟ F` is skew-adjoint (`TauCeti.inner_twoVectorContraction_apply_left`).
-/

public section

namespace exteriorPower

open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ}

/-- The map of exterior powers induced by a linear isometry preserves the inner product. -/
theorem inner_map_map (f : E →ₗᵢ[ℝ] F) (x y : ⋀[ℝ]^n E) :
    ⟪map n f.toLinearMap x, map n f.toLinearMap y⟫ = ⟪x, y⟫ := by
  -- On wedge products both sides are the Gram determinants of the same inner products.
  have key (u v : Fin n → E) :
      ⟪map n f.toLinearMap (ιMulti ℝ n u), map n f.toLinearMap (ιMulti ℝ n v)⟫ =
        ⟪ιMulti ℝ n u, ιMulti ℝ n v⟫ := by
    simp [map_apply_ιMulti, inner_ιMulti_ιMulti, Function.comp_def]
  have hx : x ∈ Submodule.span ℝ (Set.range (ιMulti ℝ n)) := by rw [ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    have hy : y ∈ Submodule.span ℝ (Set.range (ιMulti ℝ n)) := by rw [ιMulti_span]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨v, rfl⟩ := hy; exact key u v
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, inner_add_right, hy, hz]
    | smul r y _ hy => simp only [map_smul, real_inner_smul_right, hy]
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, inner_add_left, hx, hz]
  | smul r x _ hx => simp only [map_smul, real_inner_smul_left, hx]

/-- The inner product of two wedges of two vectors is their `2 × 2` Gram determinant. -/
theorem inner_ιMulti_two (a b u w : E) :
    ⟪ιMulti ℝ 2 ![a, b], ιMulti ℝ 2 ![u, w]⟫ = ⟪a, u⟫ * ⟪b, w⟫ - ⟪a, w⟫ * ⟪b, u⟫ := by
  simp [inner_ιMulti_ιMulti, Matrix.det_fin_two]
  ring

/-- For an orthonormal triple `e, x, y`, the wedges `e ∧ x` and `e ∧ y` are orthonormal. -/
theorem orthonormal_ιMulti_two_of_orthonormal {e x y : E} (h : Orthonormal ℝ ![e, x, y]) :
    Orthonormal ℝ ![ιMulti ℝ 2 ![e, x], ιMulti ℝ 2 ![e, y]] := by
  have he : ‖e‖ = 1 := h.left 0
  have hx : ‖x‖ = 1 := h.left 1
  have hy : ‖y‖ = 1 := h.left 2
  have hex : ⟪e, x⟫ = 0 := h.right (by decide : (0 : Fin 3) ≠ 1)
  have hey : ⟪e, y⟫ = 0 := h.right (by decide : (0 : Fin 3) ≠ 2)
  have hxy : ⟪x, y⟫ = 0 := h.right (by decide : (1 : Fin 3) ≠ 2)
  have hyx : ⟪y, x⟫ = 0 := h.right (by decide : (2 : Fin 3) ≠ 1)
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    rw [inner_ιMulti_two] <;>
    simp [he, hx, hy, hex, hey, hxy, hyx]

/-- Elements of `⋀ⁿ E` are determined by their inner products with wedges of vectors, since these
wedges span `⋀ⁿ E`. -/
theorem ext_inner_ιMulti {x y : ⋀[ℝ]^n E} (h : ∀ v, ⟪x, ιMulti ℝ n v⟫ = ⟪y, ιMulti ℝ n v⟫) :
    x = y := by
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
  have : innerₗ (⋀[ℝ]^n E) (x - y) = 0 := by
    refine LinearMap.ext_on (ιMulti_span ℝ n E) ?_
    rintro _ ⟨v, rfl⟩
    simp [h]
  simpa only [innerₗ_apply_apply, LinearMap.zero_apply] using LinearMap.congr_fun this (x - y)

omit [FiniteDimensional ℝ E] in
/-- Linear maps `⋀ⁿ E → ⋀ᵐ F` agree when their values on wedges of vectors have the same inner
products with all wedges of vectors. -/
theorem linearMap_ext_inner_ιMulti {m : ℕ} {f g : ⋀[ℝ]^n E →ₗ[ℝ] ⋀[ℝ]^m F}
    (h : ∀ v w, ⟪f (ιMulti ℝ n v), ιMulti ℝ m w⟫ = ⟪g (ιMulti ℝ n v), ιMulti ℝ m w⟫) :
    f = g :=
  linearMap_ext (AlternatingMap.ext fun v ↦ ext_inner_ιMulti (h v))

/-- Two-vectors are determined by their inner products with the wedges `u ∧ w` of two vectors:
the form of `ext_inner_ιMulti` whose hypothesis matches the lemmas stated for `ιMulti ℝ 2 ![u, w]`,
such as `inner_ιMulti_two`. -/
theorem ext_inner_ιMulti_two {x y : ⋀[ℝ]^2 E}
    (h : ∀ u w, ⟪x, ιMulti ℝ 2 ![u, w]⟫ = ⟪y, ιMulti ℝ 2 ![u, w]⟫) : x = y :=
  ext_inner_ιMulti fun v ↦ by
    rw [← FinVec.etaExpand_eq v]
    exact h (v 0) (v 1)

omit [FiniteDimensional ℝ E] in
/-- Linear maps `⋀² E → ⋀² F` agree when their values on wedges `a ∧ b` have the same inner
products with all wedges `u ∧ w`: the two-vector form of `linearMap_ext_inner_ιMulti`. -/
theorem linearMap_ext_inner_ιMulti_two {f g : ⋀[ℝ]^2 E →ₗ[ℝ] ⋀[ℝ]^2 F}
    (h : ∀ a b u w, ⟪f (ιMulti ℝ 2 ![a, b]), ιMulti ℝ 2 ![u, w]⟫ =
      ⟪g (ιMulti ℝ 2 ![a, b]), ιMulti ℝ 2 ![u, w]⟫) :
    f = g :=
  linearMap_ext (AlternatingMap.ext fun v ↦ ext_inner_ιMulti_two fun u w ↦ by
    rw [← FinVec.etaExpand_eq v]
    exact h (v 0) (v 1) u w)

/-- **Skew-adjoint endomorphisms act skew-adjointly on exterior powers**: if
`⟪A u, w⟫ = -⟪u, A w⟫` for all `u, w`, then the derivation action `D_A` on `⋀ⁿ E`, which applies
`A` to one factor of a wedge at a time, satisfies `⟪D_A x, y⟫ = -⟪x, D_A y⟫`. -/
theorem inner_lieMap_left {A : E →ₗ[ℝ] E}
    (hA : ∀ u w, ⟪A u, w⟫ = -⟪u, A w⟫) (x y : ⋀[ℝ]^n E) :
    ⟪lieMap n A x, y⟫ = -⟪x, lieMap n A y⟫ := by
  -- On wedges, the two sides are sums of Gram determinants with one column, respectively one
  -- row, replaced; by Jacobi's formula both sums are traces against the adjugate.
  have key (v w : Fin n → E) :
      ⟪lieMap n A (ιMulti ℝ n v), ιMulti ℝ n w⟫ =
        -⟪ιMulti ℝ n v, lieMap n A (ιMulti ℝ n w)⟫ := by
    let G : Matrix (Fin n) (Fin n) ℝ := .of fun i j ↦ ⟪v j, w i⟫
    let B : Matrix (Fin n) (Fin n) ℝ := .of fun i j ↦ ⟪v j, A (w i)⟫
    have hcol (j : Fin n) : (Matrix.of fun i c ↦ ⟪Function.update v j (A (v j)) c, w i⟫) =
        G.updateCol j fun i ↦ (-B) i j := by
      ext i c
      rcases eq_or_ne c j with rfl | h
      · simp [G, B, hA]
      · simp [G, B, h]
    have hrow (i : Fin n) : (Matrix.of fun r c ↦ ⟪v c, Function.update w i (A (w i)) r⟫) =
        G.updateRow i (B i) := by
      ext r c
      rcases eq_or_ne r i with rfl | h
      · simp [G, B]
      · simp [G, B, h]
    simp only [lieMap_apply_ιMulti, sum_inner, inner_sum, inner_ιMulti_ιMulti, hcol, hrow,
      Matrix.sum_det_updateCol_eq_trace_adjugate_mul,
      Matrix.sum_det_updateRow_eq_trace_adjugate_mul, Matrix.mul_neg, Matrix.trace_neg]
  have hbil : (innerₗ (⋀[ℝ]^n E)).compl₁₂ (lieMap n A) LinearMap.id =
      -(innerₗ (⋀[ℝ]^n E)).compl₂ (lieMap n A) :=
    linearMap_ext (AlternatingMap.ext fun v ↦ linearMap_ext (AlternatingMap.ext fun w ↦ by
      simpa only [LinearMap.compAlternatingMap_apply, LinearMap.compl₁₂_apply,
        LinearMap.compl₂_apply, LinearMap.neg_apply, LinearMap.id_apply, innerₗ_apply_apply]
        using key v w))
  simpa using LinearMap.congr_fun₂ hbil x y

/-- The squared norm of a wedge of vectors is their Gram determinant. -/
theorem norm_ιMulti_sq (v : Fin n → E) : ‖ιMulti ℝ n v‖ ^ 2 = (Matrix.gram ℝ v).det := by
  rw [← real_inner_self_eq_norm_sq, inner_ιMulti_self]

/-- **Hadamard's inequality** for wedges: `‖v₁ ∧ ⋯ ∧ vₙ‖ ≤ ‖v₁‖ ⋯ ‖vₙ‖`. -/
theorem norm_ιMulti_le_prod_norm (v : Fin n → E) : ‖ιMulti ℝ n v‖ ≤ ∏ i, ‖v i‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [norm_ιMulti_sq, ← Finset.prod_pow]
  simpa using Matrix.re_det_gram_le_prod_norm_sq (𝕜 := ℝ) v

/-- **Hadamard's inequality** for two vectors: `‖u ∧ w‖ ≤ ‖u‖ ‖w‖`. -/
theorem norm_ιMulti_two_le (u w : E) : ‖ιMulti ℝ 2 ![u, w]‖ ≤ ‖u‖ * ‖w‖ := by
  simpa [Fin.prod_univ_two] using norm_ιMulti_le_prod_norm ![u, w]

/-- The volume of a frame is invariant under linear isometries. -/
@[simp]
theorem norm_ιMulti_comp_linearIsometry (f : E →ₗᵢ[ℝ] F) (v : Fin n → E) :
    ‖ιMulti ℝ n (f ∘ v)‖ = ‖ιMulti ℝ n v‖ := by
  rw [← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_ιMulti_sq,
    norm_ιMulti_sq]
  congr 1
  ext i j
  simp [Matrix.gram]

/-- The volume of a frame does not depend on the order of its vectors. -/
@[simp]
theorem norm_ιMulti_comp_perm (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    ‖ιMulti ℝ n (v ∘ σ)‖ = ‖ιMulti ℝ n v‖ := by
  rw [(ιMulti ℝ n).map_perm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- Multiplying one vector of a frame by `c` multiplies its volume by `|c|`. -/
theorem norm_ιMulti_update_smul (v : Fin n → E) (i : Fin n) (c : ℝ) :
    ‖ιMulti ℝ n (Function.update v i (c • v i))‖ = |c| * ‖ιMulti ℝ n v‖ := by
  rw [AlternatingMap.map_update_smul, Function.update_eq_self, norm_smul, Real.norm_eq_abs]

/-- An orthonormal frame spans a parallelepiped of volume one: `‖v₁ ∧ ⋯ ∧ vₙ‖ = 1`. -/
@[simp]
theorem _root_.Orthonormal.norm_ιMulti {v : Fin n → E} (hv : Orthonormal ℝ v) :
    ‖ιMulti ℝ n v‖ = 1 := by
  rw [← pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero, norm_ιMulti_sq,
    Matrix.gram_eq_one_iff_orthonormal.mpr hv, Matrix.det_one, one_pow]

omit [FiniteDimensional ℝ E] in
/-- Two orthonormal frames have the same wedge exactly when one is obtained from the other by a
special orthogonal change of frame, `vⱼ = ∑ i, A j i • eᵢ` with `A ∈ SO(n)`: they span the same
subspace and induce the same orientation on it. -/
theorem _root_.Orthonormal.ιMulti_eq_ιMulti_iff {e v : Fin n → E} (he : Orthonormal ℝ e)
    (hv : Orthonormal ℝ v) :
    ιMulti ℝ n v = ιMulti ℝ n e ↔
      ∃ A ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ, v = fun j ↦ ∑ i, A j i • e i := by
  classical
  refine ⟨fun h ↦ ?_, ?_⟩
  swap
  · rintro ⟨A, hA, rfl⟩
    rw [ιMulti_sum_smul, (Matrix.mem_specialOrthogonalGroup_iff.1 hA).2, one_smul]
  -- Every `vⱼ` lies in the span of `e`, since `vⱼ ∧ e₁ ∧ ⋯ ∧ eₙ = vⱼ ∧ v₁ ∧ ⋯ ∧ vₙ = 0`.
  have hmem (j : Fin n) : v j ∈ Submodule.span ℝ (Set.range e) := by
    rw [TauCeti.exteriorPower.mem_span_range_iff_ι_mul_ιMulti_eq_zero he.linearIndependent, ← h]
    exact (TauCeti.exteriorPower.mem_span_range_iff_ι_mul_ιMulti_eq_zero hv.linearIndependent
      (v j)).1 (Submodule.subset_span ⟨j, rfl⟩)
  choose c hc using fun j ↦ (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hmem j)
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.of c
  have hvA : v = fun j ↦ ∑ i, A j i • e i := funext fun j ↦ (hc j).symm
  have hAO : A ∈ Matrix.orthogonalGroup (Fin n) ℝ :=
    (he.orthonormal_sum_smul_iff_mem_unitaryGroup A).1 (hvA ▸ hv)
  refine ⟨A, Matrix.mem_specialOrthogonalGroup_iff.2 ⟨hAO, ?_⟩, hvA⟩
  refine smul_left_injective ℝ ((ιMulti_ne_zero_iff e).2 he.linearIndependent) ?_
  simp only [← ιMulti_sum_smul, ← hvA, h, one_smul]

/-- Every linearly independent `n`-frame `v` in a finite-dimensional real inner product space
admits an orthonormal `n`-frame `u` with the same span and positive orientation, scaling the
exterior product by the parallelepiped volume: `v₁ ∧ ⋯ ∧ vₙ = ‖v₁ ∧ ⋯ ∧ vₙ‖ • (u₁ ∧ ⋯ ∧ uₙ)`. -/
theorem exists_orthonormal_span_eq_and_ιMulti_eq_norm_smul {v : Fin n → E}
    (hv : LinearIndependent ℝ v) :
    ∃ u : Fin n → E, Orthonormal ℝ u ∧
      Submodule.span ℝ (Set.range u) = Submodule.span ℝ (Set.range v) ∧
      ιMulti ℝ n v = ‖ιMulti ℝ n v‖ • ιMulti ℝ n u := by
  set W := Submodule.span ℝ (Set.range v)
  let w : Fin n → W := fun i ↦ ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hdim : Module.finrank ℝ W = Fintype.card (Fin n) := finrank_span_eq_card hv
  let e : OrthonormalBasis (Fin n) ℝ W := InnerProductSpace.gramSchmidtOrthonormalBasis hdim w
  let u : Fin n → E := W.subtype ∘ e
  have hu_orth : Orthonormal ℝ u := by
    simpa only [u, Submodule.coe_subtypeₗᵢ] using e.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hspan : Submodule.span ℝ (Set.range u) = W := by
    dsimp only [u]
    rw [Set.range_comp, ← e.coe_toBasis, ← Submodule.map_span, e.toBasis.span_eq,
      Submodule.map_top, W.range_subtype]
  have hdet_nonneg : 0 ≤ e.toBasis.det w := by
    rw [InnerProductSpace.gramSchmidtOrthonormalBasis_det_eq_prod_norm]
    exact Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
  have hdet_eq : e.toBasis.det w = ‖ιMulti ℝ n v‖ := by
    have hgram : Matrix.gram ℝ w = Matrix.gram ℝ v := by ext i j; simp [Matrix.gram, w]
    refine (pow_left_inj₀ hdet_nonneg (norm_nonneg _) two_ne_zero).mp ?_
    rw [norm_ιMulti_sq, ← hgram]
    simpa [Real.norm_eq_abs, sq_abs] using (e.det_gram_eq_norm_det_sq w).symm
  refine ⟨u, hu_orth, hspan, ?_⟩
  have h := congr($(AlternatingMap.eq_basis_det_smulRight e.toBasis
    ((ιMulti ℝ n).compLinearMap W.subtype)) w)
  simpa [w, u, hdet_eq, e.coe_toBasis, Function.comp_def] using h

end exteriorPower

namespace ContinuousLinearMap

open exteriorPower
open scoped RealInnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The two-vector `p₁ ∧ p₂` of the gradients of the real and imaginary parts of a
complex-valued covector `P = p₁ + i p₂`. It represents the two-form `Im (conj (P u) P w)`
(`ContinuousLinearMap.inner_gradientWedge_ιMulti`). -/
noncomputable def gradientWedge (P : E →L[ℝ] ℂ) : ⋀[ℝ]^2 E :=
  ιMulti ℝ 2 ![P.reGradient, P.imGradient]

/-- **The two-form `Im (conj (P u) P w)` is represented by the two-vector `p₁ ∧ p₂`** of the
gradients of the real and imaginary parts of `P`. -/
@[simp]
theorem inner_gradientWedge_ιMulti (P : E →L[ℝ] ℂ) (u w : E) :
    ⟪P.gradientWedge, ιMulti ℝ 2 ![u, w]⟫ = (conj (P u) * P w).im := by
  rw [gradientWedge, inner_ιMulti_two, inner_reGradient, inner_reGradient, inner_imGradient,
    inner_imGradient, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The two-vector `p₁ ∧ p₂` of a complex-valued covector `P` has norm at most `‖P‖ ^ 2`. -/
theorem norm_gradientWedge_le (P : E →L[ℝ] ℂ) : ‖P.gradientWedge‖ ≤ ‖P‖ ^ 2 :=
  (norm_ιMulti_two_le _ _).trans <| by
    rw [sq]
    exact mul_le_mul P.norm_reGradient_le P.norm_imGradient_le (norm_nonneg _) (norm_nonneg _)

end ContinuousLinearMap

namespace OrthonormalBasis

open scoped RealInnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

/-- Contracting the squared norms of `eᵢ ∧ u` in an orthonormal basis gives
`(dim E - 1) |u|²`. This includes dimensions zero and one. -/
theorem sum_norm_sq_ιMulti_two (b : OrthonormalBasis ι ℝ E) (u : E) :
    ∑ i, ‖exteriorPower.ιMulti ℝ 2 ![b i, u]‖ ^ 2 =
      ((Fintype.card ι : ℝ) - 1) * ‖u‖ ^ 2 := by
  have hw (i) : ‖exteriorPower.ιMulti ℝ 2 ![b i, u]‖ ^ 2 =
      ‖u‖ ^ 2 - ⟪b i, u⟫ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, exteriorPower.inner_ιMulti_two]
    simp [b.orthonormal.1 i, real_inner_comm, pow_two]
  simp only [hw, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, b.sum_sq_inner_right]
  ring

/-- The basis of `⋀ⁿ E` induced by an orthonormal basis `b` of `E` is orthonormal. -/
theorem inner_toBasis_exteriorPower [LinearOrder ι] (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (u v : Set.powersetCard ι n) :
    ⟪b.toBasis.exteriorPower n u, b.toBasis.exteriorPower n v⟫ = if u = v then 1 else 0 := by
  rw [← OrthonormalBasis.toBasis_exteriorPower, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.inner_eq_ite]

/-! ### Two-vectors in an orthonormal frame of a four-dimensional space -/

section FinFour

open exteriorPower

omit [FiniteDimensional ℝ E] in
/-- A wedge of two vectors in the basis `bᵢ ∧ bⱼ`, `i < j`, of `⋀² E` induced by an orthonormal
basis `b` indexed by `Fin 4`. -/
theorem ιMulti_two_eq_sum (b : OrthonormalBasis (Fin 4) ℝ E) (u w : E) :
    ιMulti ℝ 2 ![u, w] =
      (b.repr u 0 * b.repr w 1 - b.repr u 1 * b.repr w 0) • ιMulti ℝ 2 ![b 0, b 1] +
      (b.repr u 0 * b.repr w 2 - b.repr u 2 * b.repr w 0) • ιMulti ℝ 2 ![b 0, b 2] +
      (b.repr u 0 * b.repr w 3 - b.repr u 3 * b.repr w 0) • ιMulti ℝ 2 ![b 0, b 3] +
      (b.repr u 1 * b.repr w 2 - b.repr u 2 * b.repr w 1) • ιMulti ℝ 2 ![b 1, b 2] +
      (b.repr u 1 * b.repr w 3 - b.repr u 3 * b.repr w 1) • ιMulti ℝ 2 ![b 1, b 3] +
      (b.repr u 2 * b.repr w 3 - b.repr u 3 * b.repr w 2) • ιMulti ℝ 2 ![b 2, b 3] := by
  have := Module.Finite.of_basis b.toBasis
  refine ext_inner_ιMulti_two fun a c ↦ ?_
  simp only [inner_add_left, real_inner_smul_left, inner_ιMulti_two, ← b.repr_apply_apply]
  simp only [b.inner_eq_sum_repr, conj_trivial, Fin.sum_univ_four]
  ring

/-- The pairing of a two-vector with a wedge of two vectors, in the coordinates of an orthonormal
basis `b` indexed by `Fin 4`. -/
theorem inner_ιMulti_two_eq_sum (b : OrthonormalBasis (Fin 4) ℝ E) (x : ⋀[ℝ]^2 E) (u w : E) :
    ⟪x, ιMulti ℝ 2 ![u, w]⟫ =
      (b.repr u 0 * b.repr w 1 - b.repr u 1 * b.repr w 0) * ⟪x, ιMulti ℝ 2 ![b 0, b 1]⟫ +
        (b.repr u 0 * b.repr w 2 - b.repr u 2 * b.repr w 0) * ⟪x, ιMulti ℝ 2 ![b 0, b 2]⟫ +
        (b.repr u 0 * b.repr w 3 - b.repr u 3 * b.repr w 0) * ⟪x, ιMulti ℝ 2 ![b 0, b 3]⟫ +
        (b.repr u 1 * b.repr w 2 - b.repr u 2 * b.repr w 1) * ⟪x, ιMulti ℝ 2 ![b 1, b 2]⟫ +
        (b.repr u 1 * b.repr w 3 - b.repr u 3 * b.repr w 1) * ⟪x, ιMulti ℝ 2 ![b 1, b 3]⟫ +
        (b.repr u 2 * b.repr w 3 - b.repr u 3 * b.repr w 2) * ⟪x, ιMulti ℝ 2 ![b 2, b 3]⟫ := by
  conv_lhs => rw [b.ιMulti_two_eq_sum u w]
  simp only [inner_add_right, real_inner_smul_right]

/-- A two-vector is the sum of its coordinates times the basis vectors `bᵢ ∧ bⱼ`, `i < j`, of
`⋀² E` induced by an orthonormal basis `b` indexed by `Fin 4`. -/
theorem eq_sum_inner_smul_ιMulti_two (b : OrthonormalBasis (Fin 4) ℝ E) (x : ⋀[ℝ]^2 E) :
    x = ⟪x, ιMulti ℝ 2 ![b 0, b 1]⟫ • ιMulti ℝ 2 ![b 0, b 1] +
      ⟪x, ιMulti ℝ 2 ![b 0, b 2]⟫ • ιMulti ℝ 2 ![b 0, b 2] +
      ⟪x, ιMulti ℝ 2 ![b 0, b 3]⟫ • ιMulti ℝ 2 ![b 0, b 3] +
      ⟪x, ιMulti ℝ 2 ![b 1, b 2]⟫ • ιMulti ℝ 2 ![b 1, b 2] +
      ⟪x, ιMulti ℝ 2 ![b 1, b 3]⟫ • ιMulti ℝ 2 ![b 1, b 3] +
      ⟪x, ιMulti ℝ 2 ![b 2, b 3]⟫ • ιMulti ℝ 2 ![b 2, b 3] := by
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [b.inner_ιMulti_two_eq_sum x u w]
  simp only [inner_add_left, real_inner_smul_left, inner_ιMulti_two, ← b.repr_apply_apply]
  ring

/-- The squared norm of a two-vector is the sum of the squares of its coordinates in the
basis `bᵢ ∧ bⱼ`, `i < j`, induced by an orthonormal basis `b` indexed by `Fin 4`. -/
theorem norm_sq_eq_sum_sq_inner_ιMulti_two (b : OrthonormalBasis (Fin 4) ℝ E)
    (x : ⋀[ℝ]^2 E) :
    ‖x‖ ^ 2 = ⟪x, ιMulti ℝ 2 ![b 0, b 1]⟫ ^ 2 +
      ⟪x, ιMulti ℝ 2 ![b 0, b 2]⟫ ^ 2 +
      ⟪x, ιMulti ℝ 2 ![b 0, b 3]⟫ ^ 2 +
      ⟪x, ιMulti ℝ 2 ![b 1, b 2]⟫ ^ 2 +
      ⟪x, ιMulti ℝ 2 ![b 1, b 3]⟫ ^ 2 +
      ⟪x, ιMulti ℝ 2 ![b 2, b 3]⟫ ^ 2 := by
  -- Expand the second factor of `⟪x, x⟫` in the basis `bᵢ ∧ bⱼ`.
  have h := congrArg (fun y ↦ ⟪x, y⟫) (b.eq_sum_inner_smul_ιMulti_two x)
  simp only [inner_add_right, real_inner_smul_right] at h
  rw [← real_inner_self_eq_norm_sq, h]
  ring

end FinFour

end OrthonormalBasis

namespace TauCeti

open _root_.exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section TwoVectorContraction

open CliffordAlgebra

/-- The **skew endomorphism of a two-vector** `F ∈ ⋀² V`: the contraction `u ↦ u ⌟ F` of `F` by
the functional `⟪u, ·⟫`, read as a vector of `V` with `ExteriorAlgebra.ιInv`. It is the operator
`A` with `⟪A u, w⟫ = ω(u, w)` for the two-form `ω(u, w) = ⟪F, u ∧ w⟫` that `F` represents
(`TauCeti.inner_twoVectorContraction_apply`). -/
noncomputable def twoVectorContraction (F : ⋀[ℝ]^2 V) : V →ₗ[ℝ] V where
  toFun u := ExteriorAlgebra.ιInv (contractLeft (innerₗ V u) (F : ExteriorAlgebra ℝ V))
  map_add' u v := by simp
  map_smul' c u := by simp

omit [FiniteDimensional ℝ V] in
theorem twoVectorContraction_apply (F : ⋀[ℝ]^2 V) (u : V) :
    twoVectorContraction F u =
      ExteriorAlgebra.ιInv (contractLeft (innerₗ V u) (F : ExteriorAlgebra ℝ V)) :=
  (rfl)

omit [FiniteDimensional ℝ V] in
@[simp]
theorem twoVectorContraction_zero : twoVectorContraction (0 : ⋀[ℝ]^2 V) = 0 := by
  ext u
  simp [twoVectorContraction_apply]

omit [FiniteDimensional ℝ V] in
@[simp]
theorem twoVectorContraction_add (F G : ⋀[ℝ]^2 V) :
    twoVectorContraction (F + G) = twoVectorContraction F + twoVectorContraction G := by
  ext u
  simp [twoVectorContraction_apply]

omit [FiniteDimensional ℝ V] in
@[simp]
theorem twoVectorContraction_smul (c : ℝ) (F : ⋀[ℝ]^2 V) :
    twoVectorContraction (c • F) = c • twoVectorContraction F := by
  ext u
  simp [twoVectorContraction_apply]

omit [FiniteDimensional ℝ V] in
@[simp]
theorem twoVectorContraction_neg (F : ⋀[ℝ]^2 V) :
    twoVectorContraction (-F) = -twoVectorContraction F := by
  ext u
  simp [twoVectorContraction_apply]

omit [FiniteDimensional ℝ V] in
/-- The contraction `(F, u) ↦ u ⌟ F` as a bilinear map, linear in the two-vector `F` as well as in
`u`. -/
noncomputable def twoVectorContractionₗ : ⋀[ℝ]^2 V →ₗ[ℝ] V →ₗ[ℝ] V where
  toFun := twoVectorContraction
  map_add' := twoVectorContraction_add
  map_smul' := twoVectorContraction_smul

omit [FiniteDimensional ℝ V] in
@[simp]
theorem twoVectorContractionₗ_apply (F : ⋀[ℝ]^2 V) :
    twoVectorContractionₗ F = twoVectorContraction F :=
  (rfl)

omit [FiniteDimensional ℝ V] in
/-- The contraction `u ⌟ F`, read back in the exterior algebra, is the contraction of `F` by the
functional `⟪u, ·⟫`. -/
@[simp]
theorem ι_twoVectorContraction (F : ⋀[ℝ]^2 V) (u : V) :
    ExteriorAlgebra.ι ℝ (twoVectorContraction F u) =
      contractLeft (innerₗ V u) (F : ExteriorAlgebra ℝ V) :=
  ExteriorAlgebra.ι_ιInv_of_mem_exteriorPower_one
    (ExteriorAlgebra.contractLeft_mem_exteriorPower (innerₗ V u) (n := 1) F.property)

omit [FiniteDimensional ℝ V] in
/-- **The contraction of a simple two-vector**: `u ⌟ (a ∧ b) = ⟪u, a⟫ b - ⟪u, b⟫ a`. -/
@[simp]
theorem twoVectorContraction_ιMulti (w : Fin 2 → V) (u : V) :
    twoVectorContraction (ιMulti ℝ 2 w) u = ⟪u, w 0⟫ • w 1 - ⟪u, w 1⟫ • w 0 := by
  apply (ExteriorAlgebra.ι_leftInverse (R := ℝ) (M := V)).injective
  rw [ι_twoVectorContraction, ιMulti_apply_coe, ExteriorAlgebra.contractLeft_ιMulti]
  simp [Fin.sum_univ_two, Fin.removeNth, ExteriorAlgebra.ιMulti_apply, sub_eq_add_neg]

/-- **The contraction represents the two-form of `F`**: `⟪u ⌟ F, w⟫ = ⟪F, u ∧ w⟫`. Equivalently,
on two-forms, wedging with `u` is adjoint to contracting with `⟪u, ·⟫`. -/
@[simp]
theorem inner_twoVectorContraction_apply (F : ⋀[ℝ]^2 V) (u w : V) :
    ⟪twoVectorContraction F u, w⟫ = ⟪F, ιMulti ℝ 2 ![u, w]⟫ := by
  -- Both sides are linear in `F`, so it suffices to compare them on `p ∧ q`.
  have key : innerₗ (⋀[ℝ]^2 V) (ιMulti ℝ 2 ![u, w]) =
      innerₗ V w ∘ₗ LinearMap.applyₗ (R := ℝ) u ∘ₗ twoVectorContractionₗ :=
    exteriorPower.linearMap_ext_ιMulti_two fun p q ↦ by
      simp [inner_ιMulti_ιMulti, Matrix.det_fin_two, inner_sub_right, real_inner_smul_right]
      ring
  rw [real_inner_comm w, real_inner_comm _ F]
  simpa using (LinearMap.congr_fun key F).symm

omit [FiniteDimensional ℝ V] in
/-- The contraction by a two-vector is orthogonal to its argument, `⟪u ⌟ F, u⟫ = 0`. -/
theorem inner_twoVectorContraction_apply_self (F : ⋀[ℝ]^2 V) (u : V) :
    ⟪twoVectorContraction F u, u⟫ = 0 := by
  -- The contraction `u ⌟ F` is a one-form, the image of the vector `u ⌟ F`, and contracting by
  -- `u` twice gives zero.
  have h0 := contractLeft_contractLeft (innerₗ V u) (F : ExteriorAlgebra ℝ V)
  rw [← ι_twoVectorContraction, contractLeft_ι, ExteriorAlgebra.algebraMap_eq_zero_iff] at h0
  rw [real_inner_comm]
  exact h0

omit [FiniteDimensional ℝ V] in
/-- **The contraction by a two-vector is skew-adjoint**: `⟪u ⌟ F, w⟫ = -⟪u, w ⌟ F⟫`. -/
theorem inner_twoVectorContraction_apply_left (F : ⋀[ℝ]^2 V) (u w : V) :
    ⟪twoVectorContraction F u, w⟫ = -⟪u, twoVectorContraction F w⟫ := by
  have h := inner_twoVectorContraction_apply_self F (u + w)
  rw [map_add, inner_add_left, inner_add_right, inner_add_right,
    inner_twoVectorContraction_apply_self, inner_twoVectorContraction_apply_self] at h
  rw [real_inner_comm _ u]
  linarith

end TwoVectorContraction

section TwoVectorAlternatingSum

/-- The **alternating sum** `θ(a)(b, c) - θ(b)(a, c) + θ(c)(a, b)` of a map `θ` from `V` to
two-vectors, each two-vector `η` read as the two-form `(u, w) ↦ ⟪η, u ∧ w⟫`. When `θ v = ∇_v ω`
is the covariant derivative of a two-form `ω` for a torsion-free connection, it is the exterior
derivative `dω(a, b, c)`. -/
noncomputable def twoVectorAlternatingSum (θ : V → ⋀[ℝ]^2 V) (a b c : V) : ℝ :=
  ⟪θ a, ιMulti ℝ 2 ![b, c]⟫ - ⟪θ b, ιMulti ℝ 2 ![a, c]⟫ + ⟪θ c, ιMulti ℝ 2 ![a, b]⟫

theorem twoVectorAlternatingSum_def (θ : V → ⋀[ℝ]^2 V) (a b c : V) :
    twoVectorAlternatingSum θ a b c =
      ⟪θ a, ιMulti ℝ 2 ![b, c]⟫ - ⟪θ b, ιMulti ℝ 2 ![a, c]⟫ + ⟪θ c, ιMulti ℝ 2 ![a, b]⟫ :=
  (rfl)

@[simp]
theorem twoVectorAlternatingSum_zero (a b c : V) :
    twoVectorAlternatingSum (0 : V → ⋀[ℝ]^2 V) a b c = 0 := by
  simp [twoVectorAlternatingSum_def]

@[simp]
theorem twoVectorAlternatingSum_add (θ η : V → ⋀[ℝ]^2 V) (a b c : V) :
    twoVectorAlternatingSum (θ + η) a b c =
      twoVectorAlternatingSum θ a b c + twoVectorAlternatingSum η a b c := by
  simp only [twoVectorAlternatingSum_def, Pi.add_apply, inner_add_left]
  ring

@[simp]
theorem twoVectorAlternatingSum_smul (r : ℝ) (θ : V → ⋀[ℝ]^2 V) (a b c : V) :
    twoVectorAlternatingSum (r • θ) a b c = r * twoVectorAlternatingSum θ a b c := by
  simp only [twoVectorAlternatingSum_def, Pi.smul_apply, real_inner_smul_left]
  ring

@[simp]
theorem twoVectorAlternatingSum_neg (θ : V → ⋀[ℝ]^2 V) (a b c : V) :
    twoVectorAlternatingSum (-θ) a b c = -twoVectorAlternatingSum θ a b c := by
  simp only [twoVectorAlternatingSum_def, Pi.neg_apply, inner_neg_left]
  ring

/-- The alternating sum changes sign when its first two arguments are swapped. -/
theorem twoVectorAlternatingSum_swap₁₂ (θ : V → ⋀[ℝ]^2 V) (a b c : V) :
    twoVectorAlternatingSum θ b a c = -twoVectorAlternatingSum θ a b c := by
  rw [twoVectorAlternatingSum_def, twoVectorAlternatingSum_def, ιMulti_two_swap a b,
    inner_neg_right]
  ring

/-- The alternating sum changes sign when its last two arguments are swapped. -/
theorem twoVectorAlternatingSum_swap₂₃ (θ : V → ⋀[ℝ]^2 V) (a b c : V) :
    twoVectorAlternatingSum θ a c b = -twoVectorAlternatingSum θ a b c := by
  rw [twoVectorAlternatingSum_def, twoVectorAlternatingSum_def, ιMulti_two_swap b c,
    inner_neg_right]
  ring

end TwoVectorAlternatingSum

end TauCeti
