/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Projectivization.Projector

/-!
# A smooth embedding of the real projective plane in four-space

The *normalized trace-free projector* `Projectivization.traceFreeProjector` sends the line `[v]` of
`ℝ³` to the matrix `Q [v] = √(3/2) • (v vᵀ / (vᵀ v) - I / 3)`, read in its entries as a point of
`EuclideanSpace ℝ (Fin 3 × Fin 3)`, so that the Euclidean norm is the Frobenius norm. Its values are
symmetric, have trace zero and have norm one, so `Q` maps `ℝP²` into the unit sphere of the
five-dimensional space `V` of symmetric trace-free matrices; this is the classical Veronese surface
in `S⁴`. Since `Q` differs from the projector embedding `Projectivization.projector` by an affine
isomorphism of the entries, it is a smooth embedding.

The unit vector `TauCeti.traceFreePole = diag(1, 0, -1) / √2` of `V` lies off the image: its inner
product with every `Q [v]` is less than one. The four vectors `TauCeti.traceFreeFrame`,
`diag(1, -2, 1) / √6` and `(E₀₁ + E₁₀) / √2`, `(E₀₂ + E₂₀) / √2`, `(E₁₂ + E₂₁) / √2`, are an
orthonormal basis of the orthogonal complement of the pole in `V`; together with the pole they
span all symmetric trace-free matrices (`TauCeti.eq_inner_traceFreePole_smul_add_sum`). The map
`Projectivization.projectivePlaneEmbedding` is the stereographic projection `stereoToFun` from the
pole, applied to `Q`, read in the coordinates of this frame. The stereographic image is exactly the
corresponding combination of frame vectors (`Projectivization.sum_projectivePlaneEmbedding_smul`),
so the inverse stereographic projection recovers `Q`.

That gives a smooth map from `ℝ⁴` back to the matrix entries which sends the image of a line to its
projector. Since the projector map is an immersion, so is the composite map to `ℝ⁴`
(`ContMDiff.isImmersion_of_isImmersion_comp`), and since projective space is compact it is a closed
smooth embedding `ℝP² → ℝ⁴` (`Projectivization.isSmoothEmbedding_projectivePlaneEmbedding` and
`Projectivization.isClosedEmbedding_projectivePlaneEmbedding`).
Projective space carries its standard atlas of affine charts, modelled on `Fin 2 → ℝ`.

## Main definitions

* `Projectivization.traceFreeProjector`: the normalized trace-free projector `ℝP² → S⁴ ⊆ V`.
* `TauCeti.traceFreePole`, `TauCeti.traceFreeFrame`: the pole and the orthonormal frame of its
  orthogonal complement in `V`.
* `Projectivization.projectivePlaneEmbedding`: the stereographic image of `Q` in frame coordinates.

## Main results

* `Projectivization.norm_traceFreeProjector`, `Projectivization.traceFreeProjector_apply_swap`,
  `Projectivization.sum_traceFreeProjector_apply_self`: the values of `Q` are unit symmetric
  trace-free matrices.
* `Projectivization.isSmoothEmbedding_traceFreeProjector`: `Q` is a smooth embedding.
* `Projectivization.traceFreeProjector_ne_traceFreePole`: the pole is not in the image of `Q`.
* `Projectivization.isSmoothEmbedding_projectivePlaneEmbedding`: the real projective plane is
  smoothly embedded in `EuclideanSpace ℝ (Fin 4)`, as a closed subset
  (`Projectivization.isClosedEmbedding_projectivePlaneEmbedding`).

## References

The projector embedding and its immersion property are from
`TauCeti.Geometry.Manifold.Projectivization.Projector`, and the stereographic projection and its
inverse are Mathlib's, from `Mathlib.Geometry.Manifold.Instances.Sphere`. For the Veronese surface
in `S⁴` see S. S. Chern, M. do Carmo and S. Kobayashi, *Minimal submanifolds of a sphere with
second fundamental form of constant length*, in *Functional Analysis and Related Fields*,
Springer (1970), 59–75.
-/

public section

noncomputable section

open Set Function Topology Manifold Matrix TauCeti
open scoped ContDiff Manifold LinearAlgebra.Projectivization RealInnerProductSpace

namespace Projectivization

/-- The **normalized trace-free projector** `Q [v] = √(3/2) • (v vᵀ / (vᵀ v) - I / 3)` of a line of
`ℝ³`, read in its matrix entries, whose Euclidean norm is the Frobenius norm. Its values are unit
symmetric trace-free matrices, and its image is the Veronese surface in `S⁴`. -/
def traceFreeProjector (p : ℙ ℝ (Fin 3 → ℝ)) : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  WithLp.toLp 2 fun q ↦ √(3 / 2) * (projector p - (3 : ℝ)⁻¹ • 1) q.1 q.2

/-- The entries of the normalized trace-free projector in terms of those of the projector. -/
@[simp]
theorem traceFreeProjector_apply (p : ℙ ℝ (Fin 3 → ℝ)) (i j : Fin 3) :
    traceFreeProjector p (i, j) = √(3 / 2) * (projector p i j - if i = j then 3⁻¹ else 0) := by
  simp [traceFreeProjector, Matrix.one_apply]

/-- The entries of `Q` in terms of a unit vector spanning the line. -/
private theorem exists_traceFreeProjector_apply (p : ℙ ℝ (Fin 3 → ℝ)) :
    ∃ x : Fin 3 → ℝ, x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 ∧ ∀ i j,
      traceFreeProjector p (i, j) = √(3 / 2) * (x i * x j - if i = j then 3⁻¹ else 0) := by
  obtain ⟨x, hx, hp⟩ := exists_projector_eq_vecMulVec p
  refine ⟨x, by simpa [dotProduct, Fin.sum_univ_three, sq] using hx, fun i j ↦ ?_⟩
  rw [traceFreeProjector_apply, hp, vecMulVec_apply]

/-- The normalized trace-free projector takes values in the unit sphere. -/
@[simp]
theorem norm_traceFreeProjector (p : ℙ ℝ (Fin 3 → ℝ)) : ‖traceFreeProjector p‖ = 1 := by
  obtain ⟨x, hx, hQ⟩ := exists_traceFreeProjector_apply p
  have h32 : √(3 / 2) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, EuclideanSpace.real_norm_sq_eq,
    Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three, hQ, mul_pow, h32, Fin.isValue, ↓reduceIte, Fin.reduceEq, sub_zero]
  linear_combination (3 / 2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) + 1 / 2) * hx

/-- The values of the normalized trace-free projector are symmetric matrices. -/
theorem traceFreeProjector_apply_swap (p : ℙ ℝ (Fin 3 → ℝ)) (i j : Fin 3) :
    traceFreeProjector p (j, i) = traceFreeProjector p (i, j) := by
  obtain ⟨x, -, hQ⟩ := exists_traceFreeProjector_apply p
  simp only [hQ, mul_comm (x j) (x i), @eq_comm _ j i]

/-- The values of the normalized trace-free projector have trace zero. -/
theorem sum_traceFreeProjector_apply_self (p : ℙ ℝ (Fin 3 → ℝ)) :
    ∑ i, traceFreeProjector p (i, i) = 0 := by
  obtain ⟨x, hx, hQ⟩ := exists_traceFreeProjector_apply p
  simp only [Fin.sum_univ_three, hQ, ↓reduceIte]
  linear_combination √(3 / 2) * hx

/-- Distinct lines have distinct normalized trace-free projectors. -/
@[simp]
theorem traceFreeProjector_inj {p p' : ℙ ℝ (Fin 3 → ℝ)} :
    traceFreeProjector p = traceFreeProjector p' ↔ p = p' := by
  refine ⟨fun h ↦ projector_injective (Matrix.ext fun i j ↦ ?_), fun h ↦ h ▸ rfl⟩
  have := congr($h (i, j))
  rw [traceFreeProjector_apply, traceFreeProjector_apply] at this
  have h32 : √(3 / 2) ≠ 0 := by positivity
  simpa using mul_left_cancel₀ h32 this

/-- The normalized trace-free projector is injective. -/
theorem traceFreeProjector_injective : Injective traceFreeProjector :=
  fun _ _ ↦ traceFreeProjector_inj.1

end Projectivization

namespace TauCeti

/-- The **pole** `diag(1, 0, -1) / √2`, a symmetric trace-free matrix of Frobenius norm one, read in
its entries. It is not a value of the normalized trace-free projector
(`Projectivization.traceFreeProjector_ne_traceFreePole`). -/
def traceFreePole : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  WithLp.toLp 2 fun q ↦ (√2)⁻¹ * !![1, 0, 0; 0, 0, 0; 0, 0, -1] q.1 q.2

/-- The entry formula for the pole. -/
theorem traceFreePole_def :
    traceFreePole = WithLp.toLp 2 fun q ↦
      (√2)⁻¹ * !![1, 0, 0; 0, 0, 0; 0, 0, -1] q.1 q.2 :=
  (rfl)

/-- The pole is a symmetric matrix. -/
theorem traceFreePole_apply_swap (i j : Fin 3) :
    traceFreePole (j, i) = traceFreePole (i, j) := by
  fin_cases i <;> fin_cases j <;> simp [traceFreePole]

/-- The pole has trace zero. -/
@[simp]
theorem sum_traceFreePole_apply_self : ∑ i, traceFreePole (i, i) = 0 := by
  simp [traceFreePole, Fin.sum_univ_three]

/-- The **frame** `diag(1, -2, 1) / √6`, `(E₀₁ + E₁₀) / √2`, `(E₀₂ + E₂₀) / √2`, `(E₁₂ + E₂₁) / √2`,
read in matrix entries: an orthonormal basis of the symmetric trace-free matrices orthogonal to
`TauCeti.traceFreePole`. -/
def traceFreeFrame : Fin 4 → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  ![WithLp.toLp 2 fun q ↦ (√6)⁻¹ * !![1, 0, 0; 0, -2, 0; 0, 0, 1] q.1 q.2,
    WithLp.toLp 2 fun q ↦ (√2)⁻¹ * !![0, 1, 0; 1, 0, 0; 0, 0, 0] q.1 q.2,
    WithLp.toLp 2 fun q ↦ (√2)⁻¹ * !![0, 0, 1; 0, 0, 0; 1, 0, 0] q.1 q.2,
    WithLp.toLp 2 fun q ↦ (√2)⁻¹ * !![0, 0, 0; 0, 0, 1; 0, 1, 0] q.1 q.2]

/-- The entry formulas for the four frame vectors. -/
theorem traceFreeFrame_def :
    traceFreeFrame =
      ![WithLp.toLp 2 fun q ↦ (√6)⁻¹ * !![1, 0, 0; 0, -2, 0; 0, 0, 1] q.1 q.2,
        WithLp.toLp 2 fun q ↦ (√2)⁻¹ * !![0, 1, 0; 1, 0, 0; 0, 0, 0] q.1 q.2,
        WithLp.toLp 2 fun q ↦ (√2)⁻¹ * !![0, 0, 1; 0, 0, 0; 1, 0, 0] q.1 q.2,
        WithLp.toLp 2 fun q ↦ (√2)⁻¹ * !![0, 0, 0; 0, 0, 1; 0, 1, 0] q.1 q.2] :=
  (rfl)

/-- Each frame vector is a symmetric matrix. -/
theorem traceFreeFrame_apply_swap (k : Fin 4) (i j : Fin 3) :
    traceFreeFrame k (j, i) = traceFreeFrame k (i, j) := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [traceFreeFrame]

/-- Each frame vector has trace zero. -/
@[simp]
theorem sum_traceFreeFrame_apply_self (i : Fin 4) : ∑ j, traceFreeFrame i (j, j) = 0 := by
  fin_cases i <;> simp [traceFreeFrame, Fin.sum_univ_three]; ring

/-- Inner products with the frame give its four explicit matrix coordinates. -/
theorem inner_traceFreeFrame (i : Fin 4) (X : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    ⟪traceFreeFrame i, X⟫ =
      ![(√6)⁻¹ * (X (0, 0) - 2 * X (1, 1) + X (2, 2)),
        (√2)⁻¹ * (X (0, 1) + X (1, 0)),
        (√2)⁻¹ * (X (0, 2) + X (2, 0)),
        (√2)⁻¹ * (X (1, 2) + X (2, 1))] i := by
  fin_cases i <;>
    simp [traceFreeFrame, PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_three] <;> ring

/-- The inner product with the pole reads off the difference of two diagonal entries. -/
theorem inner_traceFreePole (X : EuclideanSpace ℝ (Fin 3 × Fin 3)) :
    ⟪traceFreePole, X⟫ = (√2)⁻¹ * (X (0, 0) - X (2, 2)) := by
  simp [traceFreePole, PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_three]
  ring

/-- The pole is a unit vector. -/
@[simp]
theorem norm_traceFreePole : ‖traceFreePole‖ = 1 := by
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← real_inner_self_eq_norm_sq,
    inner_traceFreePole]
  simp [traceFreePole]
  field_simp
  norm_num

/-- The frame is orthonormal. -/
theorem orthonormal_traceFreeFrame : Orthonormal ℝ traceFreeFrame := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [PiLp.inner_apply]
  fin_cases i <;> fin_cases j <;>
    simp [traceFreeFrame, Fintype.sum_prod_type, Fin.sum_univ_three, inv_pow,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow] <;>
    norm_num

/-- The frame is orthogonal to the pole. -/
@[simp]
theorem inner_traceFreeFrame_traceFreePole (i : Fin 4) :
    ⟪traceFreeFrame i, traceFreePole⟫ = 0 := by
  fin_cases i <;>
    simp [traceFreeFrame, traceFreePole, PiLp.inner_apply, Fintype.sum_prod_type,
      Fin.sum_univ_three]

/-- The pole and the frame span the symmetric trace-free matrices: such a matrix is the sum of its
orthogonal projections onto them. -/
theorem eq_inner_traceFreePole_smul_add_sum {X : EuclideanSpace ℝ (Fin 3 × Fin 3)}
    (hX : ∀ i j, X (j, i) = X (i, j)) (htr : ∑ i, X (i, i) = 0) :
    X = ⟪traceFreePole, X⟫ • traceFreePole + ∑ i, ⟪traceFreeFrame i, X⟫ • traceFreeFrame i := by
  rw [Fin.sum_univ_three] at htr
  have h01 := hX 0 1
  have h02 := hX 0 2
  have h12 := hX 1 2
  have h2 : (√2)⁻¹ * (√2)⁻¹ = (1 / 2 : ℝ) := by norm_num [← mul_inv, ← sq]
  have h6 : (√6)⁻¹ * (√6)⁻¹ = (1 / 6 : ℝ) := by norm_num [← mul_inv, ← sq]
  have h6_two : (√6)⁻¹ * ((√6)⁻¹ * 2) = (1 / 3 : ℝ) := by
    rw [← mul_assoc, h6]
    norm_num
  -- Compare the nine entries; each reduces to a linear identity in the entries of `X`.
  ext ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [traceFreeFrame, traceFreePole, PiLp.inner_apply, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fin.sum_univ_four, add_mul, neg_mul, mul_assoc,
      mul_left_comm _ (2 : ℝ), h2, h6, h6_two] <;> linarith

end TauCeti

namespace Projectivization

/-- The values of the normalized trace-free projector stay away from the pole: their inner product
with it is less than one. -/
theorem inner_traceFreePole_traceFreeProjector_lt_one (p : ℙ ℝ (Fin 3 → ℝ)) :
    ⟪traceFreePole, traceFreeProjector p⟫ < 1 := by
  obtain ⟨x, hx, hQ⟩ := exists_traceFreeProjector_apply p
  rw [inner_traceFreePole, hQ, hQ]
  simp only [↓reduceIte]
  have hc : 0 < (√2)⁻¹ * √(3 / 2) := by positivity
  have hc2 : ((√2)⁻¹ * √(3 / 2)) ^ 2 = 3 / 4 := by
    rw [mul_pow, inv_pow, Real.sq_sqrt zero_le_two, Real.sq_sqrt (by norm_num)]; norm_num
  nlinarith [sq_nonneg (x 1), sq_nonneg (x 2)]

/-- The pole is not a value of the normalized trace-free projector. -/
@[simp]
theorem traceFreeProjector_ne_traceFreePole (p : ℙ ℝ (Fin 3 → ℝ)) :
    traceFreeProjector p ≠ traceFreePole := fun h ↦ by
  have := inner_traceFreePole_traceFreeProjector_lt_one p
  rw [h, real_inner_self_eq_norm_sq, norm_traceFreePole] at this
  norm_num at this

/-- The **embedding of the real projective plane in `ℝ⁴`**: the stereographic projection from
`TauCeti.traceFreePole` of the normalized trace-free projector, read in the coordinates of the
orthonormal frame `TauCeti.traceFreeFrame`
(see `Projectivization.sum_projectivePlaneEmbedding_smul`). It is a closed smooth embedding
(`Projectivization.isSmoothEmbedding_projectivePlaneEmbedding` and
`Projectivization.isClosedEmbedding_projectivePlaneEmbedding`). -/
def projectivePlaneEmbedding (p : ℙ ℝ (Fin 3 → ℝ)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 fun i ↦ ⟪traceFreeFrame i,
    (stereoToFun traceFreePole (traceFreeProjector p) : EuclideanSpace ℝ (Fin 3 × Fin 3))⟫

/-- The coordinates of the embedding: the frame coordinates of `Q` scaled by the stereographic
factor `2 / (1 - ⟪P, Q⟫)`. -/
theorem projectivePlaneEmbedding_apply (p : ℙ ℝ (Fin 3 → ℝ)) (i : Fin 4) :
    projectivePlaneEmbedding p i = 2 / (1 - ⟪traceFreePole, traceFreeProjector p⟫) *
      ⟪traceFreeFrame i, traceFreeProjector p⟫ := by
  simp [projectivePlaneEmbedding, Submodule.orthogonalProjectionOnto_orthogonal,
    Submodule.starProjection_unit_singleton ℝ norm_traceFreePole, inner_smul_right,
    inner_sub_right, inner_traceFreeFrame_traceFreePole]

/-- The embedding lists the frame coordinates of the stereographic projection of `Q`: this
projection lies in the span of the frame. -/
theorem sum_projectivePlaneEmbedding_smul (p : ℙ ℝ (Fin 3 → ℝ)) :
    ∑ i, projectivePlaneEmbedding p i • traceFreeFrame i =
      (stereoToFun traceFreePole (traceFreeProjector p) : EuclideanSpace ℝ (Fin 3 × Fin 3)) := by
  have h := eq_inner_traceFreePole_smul_add_sum (traceFreeProjector_apply_swap p)
    (sum_traceFreeProjector_apply_self p)
  simp only [projectivePlaneEmbedding_apply, mul_smul, ← Finset.smul_sum, stereoToFun_apply,
    Submodule.coe_smul, Submodule.orthogonalProjectionOnto_orthogonal,
    Submodule.starProjection_unit_singleton ℝ norm_traceFreePole, innerSL_apply_apply]
  congr 1
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h.symm)

/-- The affine identification of matrix entries with the trace-free coordinates of `Q`. -/
private def ofProjectorEntries (a : Fin 3 × Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  WithLp.toLp 2 fun q ↦ √(3 / 2) * (a q - if q.1 = q.2 then 3⁻¹ else 0)

/-- The inverse of `ofProjectorEntries`. -/
private def toProjectorEntries (X : EuclideanSpace ℝ (Fin 3 × Fin 3)) : Fin 3 × Fin 3 → ℝ :=
  fun q ↦ (√(3 / 2))⁻¹ * X q + if q.1 = q.2 then 3⁻¹ else 0

private theorem contDiff_ofProjectorEntries {r : ℕ∞ω} : ContDiff ℝ r ofProjectorEntries :=
  contDiff_piLp' 2 fun q ↦ by
    simp only [ofProjectorEntries, PiLp.toLp_apply]
    fun_prop

private theorem contDiff_toProjectorEntries {r : ℕ∞ω} : ContDiff ℝ r toProjectorEntries :=
  contDiff_pi.2 fun q ↦ by
    simp only [toProjectorEntries]
    fun_prop

private theorem ofProjectorEntries_projector (p : ℙ ℝ (Fin 3 → ℝ)) :
    ofProjectorEntries (fun q ↦ projector p q.1 q.2) = traceFreeProjector p := by
  ext ⟨i, j⟩
  simp [ofProjectorEntries, traceFreeProjector_apply]

private theorem toProjectorEntries_traceFreeProjector (p : ℙ ℝ (Fin 3 → ℝ)) :
    toProjectorEntries (traceFreeProjector p) = fun q ↦ projector p q.1 q.2 := by
  ext ⟨i, j⟩
  have h32 : √(3 / 2) ≠ 0 := by positivity
  simp only [toProjectorEntries, traceFreeProjector_apply, inv_mul_cancel_left₀ h32,
    sub_add_cancel]

private theorem toProjectorEntries_comp_traceFreeProjector :
    toProjectorEntries ∘ traceFreeProjector = fun p q ↦ projector p q.1 q.2 :=
  funext toProjectorEntries_traceFreeProjector

/-- The inverse stereographic projection of the frame vector with the coordinates of the embedding
recovers the normalized trace-free projector. -/
theorem stereoInvFunAux_sum_projectivePlaneEmbedding_smul (p : ℙ ℝ (Fin 3 → ℝ)) :
    stereoInvFunAux traceFreePole (∑ i, projectivePlaneEmbedding p i • traceFreeFrame i) =
      traceFreeProjector p := by
  rw [sum_projectivePlaneEmbedding_smul]
  exact congrArg Subtype.val (stereo_left_inv norm_traceFreePole
    (x := ⟨traceFreeProjector p, by simp [norm_traceFreeProjector]⟩)
    (traceFreeProjector_ne_traceFreePole p))

/-- The normalized trace-free projector is `C^r` for every `r`, including the analytic order. -/
theorem contMDiff_traceFreeProjector (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3 × Fin 3)) r traceFreeProjector := by
  rw [← funext ofProjectorEntries_projector]
  exact contDiff_ofProjectorEntries.comp_contMDiff (contMDiff_projector r)

/-- **The Veronese surface.** The normalized trace-free projector is a `C^r` embedding of the
real projective plane in the space of `3 × 3` matrices, for every `r ≥ 1`. -/
theorem isSmoothEmbedding_traceFreeProjector {r : ℕ∞ω} (hr : 1 ≤ r) :
    IsSmoothEmbedding 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3 × Fin 3)) r
      traceFreeProjector := by
  refine ⟨(contMDiff_traceFreeProjector r).isImmersion_of_isImmersion_comp hr
    (g := toProjectorEntries)
    (fun _ ↦ (contDiff_toProjectorEntries (r := 1)).contMDiff.mdifferentiableAt one_ne_zero) ?_,
    ((contMDiff_traceFreeProjector r).continuous.isClosedEmbedding
      traceFreeProjector_injective).isEmbedding⟩
  rw [toProjectorEntries_comp_traceFreeProjector]
  exact isImmersion_projector hr

/-- The embedding of the real projective plane in `ℝ⁴` is injective. -/
theorem projectivePlaneEmbedding_injective : Injective projectivePlaneEmbedding := fun p p' h ↦
  traceFreeProjector_injective (by
    rw [← stereoInvFunAux_sum_projectivePlaneEmbedding_smul p, h,
      stereoInvFunAux_sum_projectivePlaneEmbedding_smul])

/-- The embedding of the real projective plane in `ℝ⁴` is `C^r` for every `r`, including the
analytic order. -/
theorem contMDiff_projectivePlaneEmbedding (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) r projectivePlaneEmbedding := by
  have hΦ : ContDiffOn ℝ r (fun X : EuclideanSpace ℝ (Fin 3 × Fin 3) ↦ WithLp.toLp 2 fun i ↦
      ⟪traceFreeFrame i, (stereoToFun traceFreePole X : EuclideanSpace ℝ (Fin 3 × Fin 3))⟫)
      {X | innerSL ℝ traceFreePole X ≠ 1} :=
    contDiffOn_piLp' 2 fun i ↦
      ((innerSL ℝ (traceFreeFrame i)).contDiff.comp
        (Submodule.subtypeL _).contDiff).comp_contDiffOn contDiffOn_stereoToFun
  exact hΦ.contMDiffOn.comp_contMDiff (contMDiff_traceFreeProjector r) fun p ↦
    (inner_traceFreePole_traceFreeProjector_lt_one p).ne

/-- The embedding of the real projective plane in `ℝ⁴` is a closed embedding. -/
theorem isClosedEmbedding_projectivePlaneEmbedding : IsClosedEmbedding projectivePlaneEmbedding :=
  (contMDiff_projectivePlaneEmbedding 0).continuous.isClosedEmbedding
    projectivePlaneEmbedding_injective

/-- **The real projective plane embeds smoothly in `ℝ⁴`.** The map
`Projectivization.projectivePlaneEmbedding` is a `C^r` embedding of `ℝP²` in
`EuclideanSpace ℝ (Fin 4)` for every `r ≥ 1`, including the analytic order. -/
theorem isSmoothEmbedding_projectivePlaneEmbedding {r : ℕ∞ω} (hr : 1 ≤ r) :
    IsSmoothEmbedding 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) r
      projectivePlaneEmbedding := by
  refine ⟨(contMDiff_projectivePlaneEmbedding r).isImmersion_of_isImmersion_comp hr
    (g := fun y ↦ stereoInvFunAux traceFreePole (∑ i, y i • traceFreeFrame i))
    (fun _ ↦ (contDiff_stereoInvFunAux.comp (by fun_prop)).contMDiff.mdifferentiableAt
      one_ne_zero) ?_,
    isClosedEmbedding_projectivePlaneEmbedding.isEmbedding⟩
  simpa only [Function.comp_def, stereoInvFunAux_sum_projectivePlaneEmbedding_smul] using
    (isSmoothEmbedding_traceFreeProjector hr).1

end Projectivization
