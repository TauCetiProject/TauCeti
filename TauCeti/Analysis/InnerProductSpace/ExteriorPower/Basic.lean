/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import TauCeti.Algebra.Lie.ExteriorPower
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic

/-!
# Norms and linear isometries of exterior powers

The exterior powers `⋀[ℝ]^n E` of a finite-dimensional real inner product space carry Mathlib's
induced inner product, with `⟪v₁ ∧ ⋯ ∧ vₙ, w₁ ∧ ⋯ ∧ wₙ⟫ = det ⟪vⱼ, wᵢ⟫`. This file proves that the
map `⋀ⁿ f` induced by a linear isometry `f` preserves it, so that rotations of an oriented space
act isometrically on its forms, and that infinitesimal rotations, the skew-adjoint endomorphisms,
act skew-adjointly on forms of every degree. It also records that the norm of a wedge
`v₁ ∧ ⋯ ∧ vₙ` is the volume of the parallelepiped spanned by the `vᵢ`, bounded by Hadamard's
inequality. Finally, it packages the skew endomorphism `u ↦ u ⌟ F` of a two-vector `F`, the
operator that represents the two-form `ω(u, w) = ⟪F, u ∧ w⟫` through the inner product.

## Main definitions

* `TauCeti.twoVectorContraction F`: the skew endomorphism `u ↦ u ⌟ F` of a two-vector, with
  `⟪u ⌟ F, w⟫ = ⟪F, u ∧ w⟫`.

## Main results

* `exteriorPower.inner_map_map`: `⟪⋀ⁿ f x, ⋀ⁿ f y⟫ = ⟪x, y⟫` for a linear isometry `f`.
* `exteriorPower.inner_ιMulti_two`: `⟪a ∧ b, u ∧ w⟫ = ⟪a, u⟫ ⟪b, w⟫ - ⟪a, w⟫ ⟪b, u⟫`.
* `exteriorPower.ext_inner_ιMulti`: elements of `⋀ⁿ E` with the same inner products against all
  wedges of vectors are equal, and `exteriorPower.linearMap_ext_inner_ιMulti` is the
  corresponding extensionality principle for linear maps between exterior powers;
  `exteriorPower.ext_inner_ιMulti_two` and `exteriorPower.linearMap_ext_inner_ιMulti_two` test
  only against wedges `u ∧ w` of two vectors.
* `exteriorPower.inner_lieMap_left`: the derivation action `D_A` of a skew-adjoint `A` on
  `⋀ⁿ E` is skew-adjoint, `⟪D_A x, y⟫ = -⟪x, D_A y⟫`.
* `OrthonormalBasis.sum_norm_sq_ιMulti_two`: contraction of squared wedge norms in a basis.
* `OrthonormalBasis.ιMulti_two_eq_sum`, `OrthonormalBasis.inner_ιMulti_two_eq_sum`,
  `OrthonormalBasis.norm_sq_eq_sum_sq_inner_ιMulti_two`: the coordinates of two-vectors in the
  basis `bᵢ ∧ bⱼ` induced by an orthonormal basis `b` of a four-dimensional space.
* `exteriorPower.norm_ιMulti_sq`: `‖v₁ ∧ ⋯ ∧ vₙ‖ ^ 2` is the Gram determinant of `v`.
* `exteriorPower.norm_ιMulti_le_prod_norm`: Hadamard's inequality `‖v₁ ∧ ⋯ ∧ vₙ‖ ≤ ∏ ‖vᵢ‖`.
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

end exteriorPower

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

/-! ### Two-vectors in an orthonormal frame of a four-dimensional space -/

section FinFour

open exteriorPower

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
  have hx : x = ⟪x, ιMulti ℝ 2 ![b 0, b 1]⟫ • ιMulti ℝ 2 ![b 0, b 1] +
      ⟪x, ιMulti ℝ 2 ![b 0, b 2]⟫ • ιMulti ℝ 2 ![b 0, b 2] +
      ⟪x, ιMulti ℝ 2 ![b 0, b 3]⟫ • ιMulti ℝ 2 ![b 0, b 3] +
      ⟪x, ιMulti ℝ 2 ![b 1, b 2]⟫ • ιMulti ℝ 2 ![b 1, b 2] +
      ⟪x, ιMulti ℝ 2 ![b 1, b 3]⟫ • ιMulti ℝ 2 ![b 1, b 3] +
      ⟪x, ιMulti ℝ 2 ![b 2, b 3]⟫ • ιMulti ℝ 2 ![b 2, b 3] := by
    refine ext_inner_ιMulti_two fun u w ↦ ?_
    rw [b.inner_ιMulti_two_eq_sum x u w]
    simp only [inner_add_left, real_inner_smul_left, inner_ιMulti_two,
      ← b.repr_apply_apply]
    ring
  have h := congrArg (fun y ↦ ⟪x, y⟫) hx
  simp only [inner_add_right, real_inner_smul_right] at h
  rw [← real_inner_self_eq_norm_sq, h]
  ring

end FinFour

end OrthonormalBasis

namespace TauCeti

open exteriorPower
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

/-- **The contraction represents the two-form of `F`**: `⟪u ⌟ F, w⟫ = ⟪F, u ∧ w⟫`. Equivalently,
on two-forms, wedging with `u` is adjoint to contracting with `⟪u, ·⟫`. -/
@[simp]
theorem inner_twoVectorContraction_apply (F : ⋀[ℝ]^2 V) (u w : V) :
    ⟪twoVectorContraction F u, w⟫ = ⟪F, ιMulti ℝ 2 ![u, w]⟫ := by
  -- Both sides are linear in `F`, so it suffices to compare them on `p ∧ q`.
  have key : innerₗ (⋀[ℝ]^2 V) (ιMulti ℝ 2 ![u, w]) =
      innerₗ V w ∘ₗ ExteriorAlgebra.ιInv ∘ₗ contractLeft (Q := (0 : QuadraticForm ℝ V))
        (innerₗ V u) ∘ₗ (⋀[ℝ]^2 V).subtype := by
    refine exteriorPower.linearMap_ext ?_
    ext v
    simp [inner_ιMulti_ιMulti, Matrix.det_fin_two, ExteriorAlgebra.ιMulti_apply,
      contractLeft_ι_mul, ← Algebra.commutes, ← Algebra.smul_def, ExteriorAlgebra.ι_leftInverse _,
      inner_sub_right, real_inner_smul_right, Matrix.vecTail]
    ring
  rw [real_inner_comm w, real_inner_comm _ F, twoVectorContraction_apply]
  simpa using (LinearMap.congr_fun key F).symm

/-- The contraction by a two-vector is orthogonal to its argument, `⟪u ⌟ F, u⟫ = 0`. -/
theorem inner_twoVectorContraction_apply_self (F : ⋀[ℝ]^2 V) (u : V) :
    ⟪twoVectorContraction F u, u⟫ = 0 := by
  rw [inner_twoVectorContraction_apply,
    (ιMulti ℝ 2).map_eq_zero_of_eq ![u, u] (i := 0) (j := 1) rfl (by decide), inner_zero_right]

/-- **The contraction by a two-vector is skew-adjoint**: `⟪u ⌟ F, w⟫ = -⟪u, w ⌟ F⟫`. -/
theorem inner_twoVectorContraction_apply_left (F : ⋀[ℝ]^2 V) (u w : V) :
    ⟪twoVectorContraction F u, w⟫ = -⟪u, twoVectorContraction F w⟫ := by
  have h := inner_twoVectorContraction_apply_self F (u + w)
  rw [map_add, inner_add_left, inner_add_right, inner_add_right,
    inner_twoVectorContraction_apply_self, inner_twoVectorContraction_apply_self] at h
  rw [real_inner_comm _ u]
  linarith

end TwoVectorContraction

end TauCeti
