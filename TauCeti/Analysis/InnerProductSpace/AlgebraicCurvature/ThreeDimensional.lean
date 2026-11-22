/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Cone
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic

/-!
# Curvature operators in dimension three

On a three-dimensional real inner product space `V`, bivectors and vectors correspond: an
orthonormal basis `b` of `V` gives the orthonormal basis `b 1 ∧ b 2`, `b 2 ∧ b 0`, `b 0 ∧ b 1` of
`⋀² V`. In these corresponding bases the curvature operator `R = curvatureEndomorphism r` of a
bivector-symmetric four-tensor `r` has the matrix

`⟪R (b (i + 1) ∧ b (i + 2)), b (j + 1) ∧ b (j + 2)⟫ = (Scal / 2) δᵢⱼ - Ric(b i, b j)`,

so `R` is determined by the Ricci contraction. When `b` diagonalizes `Ric` with eigenvalues
`ρ₀, ρ₁, ρ₂`, the operator is diagonal with eigenvalues `(Scal / 2) - ρᵢ`, and each `ρᵢ` is the
sum of the two eigenvalues of `R` other than `(Scal / 2) - ρᵢ`.

The bilinear form of this identity, transported along the resulting isometry `V ≃ ⋀² V`, shows
that for every orthonormal pair of bivectors `ω₁, ω₂` the sum `⟪R ω₁, ω₁⟫ + ⟪R ω₂, ω₂⟫` is the
Ricci curvature `Ric(u, u)` of a unit vector `u`, namely the vector corresponding to the bivector
orthogonal to `ω₁` and `ω₂`; conversely every `Ric(u, u)` of a unit vector arises this way.
Consequently, in dimension three the curvature operator is 2-nonnegative exactly when the Ricci
curvature is nonnegative, and 2-positive exactly when the Ricci curvature is positive. This is the
three-dimensional input to Hamilton's theorem on three-manifolds of positive Ricci curvature,
where the Ricci-nonnegative cone is the 2-nonnegative cone of the curvature operator.

## Main results

* `TauCeti.FourTensor.IsBivectorSymmetric.inner_curvatureEndomorphism_ιMulti_two_add_one_add_two`:
  the matrix of the curvature operator in the bivector basis of an orthonormal basis is
  `(Scal / 2) I - Ric`.
* `TauCeti.FourTensor.IsBivectorSymmetric.exists_ricci_eq_add_of_orthonormal` and
  `TauCeti.FourTensor.IsBivectorSymmetric.exists_orthonormal_add_eq_ricci`: the sums of the
  curvature operator over orthonormal pairs of bivectors are exactly the Ricci curvatures of unit
  vectors.
* `TauCeti.FourTensor.twoNonnegCurvatureOperatorCone_eq_nonnegRicciCone`: in dimension three the
  2-nonnegative cone is the Ricci-nonnegative cone.
* `TauCeti.FourTensor.IsBivectorSymmetric.forall_orthonormal_add_pos_iff_forall_ricci_pos`: in
  dimension three the curvature operator is 2-positive exactly when the Ricci curvature is
  positive.

## References

* R. S. Hamilton, *Three-manifolds with positive Ricci curvature*, J. Differential Geom. 17
  (1982), 255–306.
* P. Topping, *Lectures on the Ricci flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), Chapter 9.
-/

public section

open scoped RealInnerProductSpace
open exteriorPower

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The curvature operator in a bivector basis -/

/-- **The dimension-three identity.** For a bivector-symmetric four-tensor `r` on a space with an
orthonormal basis `b` indexed by `Fin 3`, the matrix of the curvature operator in the bivector basis
`b 1 ∧ b 2, b 2 ∧ b 0, b 0 ∧ b 1` is `(Scal / 2) I - Ric`:
`⟪R (b (i + 1) ∧ b (i + 2)), b (j + 1) ∧ b (j + 2)⟫ = (Scal / 2) ⟪b i, b j⟫ - Ric(b i, b j)`. -/
theorem IsBivectorSymmetric.inner_curvatureEndomorphism_ιMulti_two_add_one_add_two
    {r : FourTensor V} (hr : IsBivectorSymmetric r) (b : OrthonormalBasis (Fin 3) ℝ V)
    (i j : Fin 3) :
    ⟪curvatureEndomorphism r (ιMulti ℝ 2 ![b (i + 1), b (i + 2)]),
        ιMulti ℝ 2 ![b (j + 1), b (j + 2)]⟫ =
      scalar r / 2 * ⟪b i, b j⟫ - ricci r (b i) (b j) := by
  have h₁ (x z w : V) : r ![x, x, z, w] = 0 :=
    CharZero.eq_neg_self_iff.mp (hr.antisymm_first x x z w)
  have h₂ (u v z : V) : r ![u, v, z, z] = 0 :=
    CharZero.eq_neg_self_iff.mp (hr.antisymm_last u v z z)
  rw [hr.inner_curvatureEndomorphism_ιMulti, scalar_apply_orthonormalBasis b,
    ricci_apply_orthonormalBasis b, b.inner_eq_ite]
  -- After expanding the traces, each of the nine entries is a linear identity between the
  -- components `r(b p, b q, b s, b t)`, closed by the pair symmetries listed below: the first six
  -- identify the sectional components `r(b p, b q, b p, b q)` with their transposes, the remaining
  -- ones match the off-diagonal entries with the mixed Ricci components.
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, h₁, h₂] <;>
    linarith [hr.antisymm_first (b 0) (b 1) (b 0) (b 1), hr.antisymm_first (b 0) (b 2) (b 0) (b 2),
      hr.antisymm_first (b 1) (b 2) (b 1) (b 2), hr.antisymm_last (b 1) (b 0) (b 0) (b 1),
      hr.antisymm_last (b 2) (b 0) (b 0) (b 2), hr.antisymm_last (b 2) (b 1) (b 1) (b 2),
      hr.swap_pairs (b 1) (b 2) (b 2) (b 0), hr.antisymm_last (b 2) (b 0) (b 1) (b 2),
      hr.swap_pairs (b 1) (b 2) (b 0) (b 1), hr.antisymm_first (b 0) (b 1) (b 1) (b 2),
      hr.swap_pairs (b 2) (b 1) (b 2) (b 0), hr.antisymm_last (b 2) (b 0) (b 2) (b 1),
      hr.swap_pairs (b 2) (b 0) (b 0) (b 1), hr.antisymm_last (b 0) (b 1) (b 2) (b 0),
      hr.swap_pairs (b 1) (b 2) (b 1) (b 0), hr.antisymm_first (b 1) (b 0) (b 1) (b 2),
      hr.swap_pairs (b 0) (b 2) (b 0) (b 1)]

/-! ### Transport along the isometry of vectors and bivectors -/

/-- The orthonormal basis `b 1 ∧ b 2, b 2 ∧ b 0, b 0 ∧ b 1` of `⋀² V` defined by an orthonormal
basis `b` of `V` indexed by `Fin 3`. -/
private def cyclicWedgeBasis (b : OrthonormalBasis (Fin 3) ℝ V) :
    OrthonormalBasis (Fin 3) ℝ (⋀[ℝ]^2 V) :=
  .mk b.orthonormal_ιMulti_two_add_one_add_two <|
    (b.orthonormal_ιMulti_two_add_one_add_two.linearIndependent.span_eq_top_of_card_eq_finrank' <|
      by simp [Module.finrank_eq_card_basis b.toBasis]).ge

/-- The linear isometry `V ≃ ⋀² V` sending `b 0, b 1, b 2` to `b 1 ∧ b 2, b 2 ∧ b 0, b 0 ∧ b 1`. -/
private def cyclicWedgeEquiv (b : OrthonormalBasis (Fin 3) ℝ V) : V ≃ₗᵢ[ℝ] ⋀[ℝ]^2 V :=
  b.equiv (cyclicWedgeBasis b) (.refl _)

private theorem cyclicWedgeEquiv_apply (b : OrthonormalBasis (Fin 3) ℝ V) (k : Fin 3) :
    cyclicWedgeEquiv b (b k) = ιMulti ℝ 2 ![b (k + 1), b (k + 2)] := by
  simp [cyclicWedgeEquiv, cyclicWedgeBasis]

/-- The dimension-three identity as an identity of bilinear forms on `V`:
`⟪R (Φ x), Φ y⟫ = (Scal / 2) ⟪x, y⟫ - Ric(x, y)` for the isometry `Φ = cyclicWedgeEquiv b`. -/
private theorem IsBivectorSymmetric.inner_curvatureEndomorphism_cyclicWedgeEquiv
    {r : FourTensor V} (hr : IsBivectorSymmetric r) (b : OrthonormalBasis (Fin 3) ℝ V) (x y : V) :
    ⟪curvatureEndomorphism r (cyclicWedgeEquiv b x), cyclicWedgeEquiv b y⟫ =
      scalar r / 2 * ⟪x, y⟫ - ricci r x y := by
  let Φ := (cyclicWedgeEquiv b).toLinearEquiv.toLinearMap
  have h : (innerₗ (⋀[ℝ]^2 V)).compl₁₂ (curvatureEndomorphism r ∘ₗ Φ) Φ =
      (scalar r / 2) • innerₗ V - ricci r :=
    b.toBasis.ext fun i ↦ b.toBasis.ext fun j ↦ by
      simpa [Φ, cyclicWedgeEquiv_apply] using
        hr.inner_curvatureEndomorphism_ιMulti_two_add_one_add_two b i j
  simpa [Φ] using LinearMap.congr_fun₂ h x y

/-- In an orthonormal basis `c` of a three-dimensional space, `Ric(c 2, c 2)` is the sum of the
values of the curvature operator on the bivectors corresponding to `c 0` and `c 1`. -/
private theorem IsBivectorSymmetric.add_inner_curvatureEndomorphism_cyclicWedgeEquiv
    {r : FourTensor V} (hr : IsBivectorSymmetric r) (b c : OrthonormalBasis (Fin 3) ℝ V) :
    ⟪curvatureEndomorphism r (cyclicWedgeEquiv b (c 0)), cyclicWedgeEquiv b (c 0)⟫ +
      ⟪curvatureEndomorphism r (cyclicWedgeEquiv b (c 1)), cyclicWedgeEquiv b (c 1)⟫ =
        ricci r (c 2) (c 2) := by
  have hscal : scalar r = ∑ i, ricci r (c i) (c i) := by
    rw [scalar_apply, bilinFormTrace_eq_sum _ c]
  rw [hr.inner_curvatureEndomorphism_cyclicWedgeEquiv,
    hr.inner_curvatureEndomorphism_cyclicWedgeEquiv, hscal, Fin.sum_univ_three,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, c.orthonormal.1 0, c.orthonormal.1 1]
  ring

/-! ### Sums over orthonormal pairs of bivectors -/

/-- In dimension three, the sum of the values of the curvature operator of a bivector-symmetric
four-tensor on an orthonormal pair of bivectors is the Ricci curvature `Ric(u, u)` of a unit
vector `u`. -/
theorem IsBivectorSymmetric.exists_ricci_eq_add_of_orthonormal {r : FourTensor V}
    (hr : IsBivectorSymmetric r) (hdim : Module.finrank ℝ V = 3) {ω₁ ω₂ : ⋀[ℝ]^2 V}
    (hω : Orthonormal ℝ ![ω₁, ω₂]) :
    ∃ u : V, ‖u‖ = 1 ∧
      ricci r u u = ⟪curvatureEndomorphism r ω₁, ω₁⟫ + ⟪curvatureEndomorphism r ω₂, ω₂⟫ := by
  let b : OrthonormalBasis (Fin 3) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hdim)
  have h₁ : ‖ω₁‖ = 1 := by simpa using hω.1 0
  have h₂ : ‖ω₂‖ = 1 := by simpa using hω.1 1
  have h₁₂ : ⟪ω₁, ω₂⟫ = 0 := by simpa using hω.2 (i := 0) (j := 1) (by decide)
  -- Complete the vectors corresponding to `ω₁` and `ω₂` to an orthonormal basis `c`.
  obtain ⟨c, hc⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (ι := Fin 3) (by simp [hdim])
    (v := ![(cyclicWedgeEquiv b).symm ω₁, (cyclicWedgeEquiv b).symm ω₂, 0]) (s := {0, 1}) <| by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
        simp [LinearIsometryEquiv.inner_map_map, h₁, h₂, h₁₂, real_inner_comm ω₁]
  refine ⟨c 2, c.orthonormal.1 2, ?_⟩
  rw [← hr.add_inner_curvatureEndomorphism_cyclicWedgeEquiv b c, hc 0 (by simp), hc 1 (by simp)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, LinearIsometryEquiv.apply_symm_apply]

/-- In dimension three, the Ricci curvature `Ric(u, u)` of a unit vector `u` is the sum of the
values of the curvature operator of a bivector-symmetric four-tensor on an orthonormal pair of
bivectors. -/
theorem IsBivectorSymmetric.exists_orthonormal_add_eq_ricci {r : FourTensor V}
    (hr : IsBivectorSymmetric r) (hdim : Module.finrank ℝ V = 3) {u : V} (hu : ‖u‖ = 1) :
    ∃ ω₁ ω₂ : ⋀[ℝ]^2 V, Orthonormal ℝ ![ω₁, ω₂] ∧
      ⟪curvatureEndomorphism r ω₁, ω₁⟫ + ⟪curvatureEndomorphism r ω₂, ω₂⟫ = ricci r u u := by
  let b : OrthonormalBasis (Fin 3) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hdim)
  -- Complete `u` to an orthonormal basis `c` with `c 2 = u`.
  obtain ⟨c, hc⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (ι := Fin 3) (by simp [hdim]) (v := fun _ ↦ u) (s := {2}) <| by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Set.mem_singleton_iff] at hi hj
      subst hi hj
      simp [hu]
  refine ⟨cyclicWedgeEquiv b (c 0), cyclicWedgeEquiv b (c 1), ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [LinearIsometryEquiv.inner_map_map, c.inner_eq_ite]
  · rw [hr.add_inner_curvatureEndomorphism_cyclicWedgeEquiv b c, hc 2 rfl]

/-! ### Two-nonnegativity and two-positivity -/

/-- In dimension three, an algebraic curvature tensor has 2-nonnegative curvature operator exactly
when it has nonnegative Ricci curvature. -/
theorem twoNonnegCurvatureOperatorCone_eq_nonnegRicciCone (hdim : Module.finrank ℝ V = 3) :
    twoNonnegCurvatureOperatorCone V = nonnegRicciCone V := by
  refine le_antisymm (twoNonnegCurvatureOperatorCone_le_nonnegRicciCone (by omega)) fun r hr ↦ ?_
  refine mem_twoNonnegCurvatureOperatorCone.mpr fun ω₁ ω₂ hω ↦ ?_
  obtain ⟨u, -, hu⟩ := (mem_algebraicCurvatureSubmodule.mp r.property).isBivectorSymmetric
    |>.exists_ricci_eq_add_of_orthonormal hdim hω
  exact hu ▸ mem_nonnegRicciCone.mp hr u

/-- In dimension three, the curvature operator of a bivector-symmetric four-tensor is 2-positive,
`⟪R ω₁, ω₁⟫ + ⟪R ω₂, ω₂⟫ > 0` for every orthonormal pair of bivectors, exactly when its Ricci
curvature is positive, `Ric(u, u) > 0` for every `u ≠ 0`. -/
theorem IsBivectorSymmetric.forall_orthonormal_add_pos_iff_forall_ricci_pos {r : FourTensor V}
    (hr : IsBivectorSymmetric r) (hdim : Module.finrank ℝ V = 3) :
    (∀ ω₁ ω₂ : ⋀[ℝ]^2 V, Orthonormal ℝ ![ω₁, ω₂] →
      0 < ⟪curvatureEndomorphism r ω₁, ω₁⟫ + ⟪curvatureEndomorphism r ω₂, ω₂⟫) ↔
      ∀ u : V, u ≠ 0 → 0 < ricci r u u := by
  refine ⟨fun h u hu ↦ ?_, fun h ω₁ ω₂ hω ↦ ?_⟩
  · have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    obtain ⟨ω₁, ω₂, hω, hsum⟩ := hr.exists_orthonormal_add_eq_ricci hdim (u := ‖u‖⁻¹ • u) <| by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu']
    have hpos := hsum ▸ h ω₁ ω₂ hω
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc] at hpos
    exact (mul_pos_iff_of_pos_left (mul_self_pos.mpr (inv_ne_zero hu'))).mp hpos
  · obtain ⟨u, hu, hsum⟩ := hr.exists_ricci_eq_add_of_orthonormal hdim hω
    exact hsum ▸ h u (norm_ne_zero_iff.mp (hu ▸ one_ne_zero))

end TauCeti.FourTensor
