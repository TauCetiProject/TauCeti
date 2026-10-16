/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Group
public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Inversion
public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Reflection
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.UpperHalfSpace
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Lifting hyperbolic isometries to `SL₂ℝ~`

Every isometry of the hyperbolic plane lifts to an isometry of the Sasaki model
`SL₂ℝ~`. The proof uses the explicit normal form for upper-half-plane isometries.
Similarities lift through `SL2Tilde.translate`, with `SL2Tilde.reflection` supplying
the nontrivial linear isometry of the boundary line. The product
`SL2Tilde.inversion * SL2Tilde.reflection` lifts inversion in the unit circle.
Conjugating this lift by similarities gives inversions with arbitrary centre and
nonzero radius.

Together with `SL2Tilde.ker_baseIsomHom`, surjectivity identifies the full isometry
group up to the vertical-translation kernel.

References:

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  Section 4, pp. 464–465 (the isometry group of `SL₂ℝ~`).
* J. G. Ratcliffe, *Foundations of Hyperbolic Manifolds*, third edition,
  Section 4.6 (the upper-half-space isometry normal form).
-/

public noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SL2Tilde

local notation "J" => 𝓘(ℝ, ℝ × ℝ × ℝ)
local notation "K" => 𝓘(ℝ, WithLp 2 (ℝ × ℝ))

/-- The lifted reflection induces the reflection `x + iy ↦ -x + iy` of the upper half-plane in
the imaginary axis. -/
@[simp] theorem baseIsomHom_reflection :
    baseIsomHom reflection =
      UpperHalfSpace.similarity 1 one_pos (LinearIsometryEquiv.neg ℝ) 0 := by
  apply (baseIsomHom_eq_iff _ _).mpr
  intro p
  apply UpperHalfSpace.ext_fst_height
  · simp [UpperHalfSpace.coe_similarity_apply]
  · simp

/-- The product of the lifted nonlinear inversion and lifted reflection induces inversion
in the unit circle centred at the origin of the upper-half-plane boundary. -/
@[simp] theorem baseIsomHom_inversion_mul_reflection :
    baseIsomHom (inversion * reflection) =
      UpperHalfSpace.inversion 0 1 one_ne_zero := by
  apply (baseIsomHom_eq_iff _ _).mpr
  intro p
  apply UpperHalfSpace.ext
  rw [UpperHalfSpace.coe_inversion_apply]
  have hd : dist (WithLp.toLp 2 (p.x, Real.exp p.y)) (WithLp.toLp 2 (0, 0)) ^ 2 =
      p.x ^ 2 + Real.exp p.y ^ 2 := by
    rw [Prod.mk_zero_zero, WithLp.toLp_zero, dist_zero_right,
      WithLp.prod_norm_sq_eq_of_L2]
    simp [Real.norm_eq_abs, sq_abs]
  have hpos : 0 < p.x ^ 2 + Real.exp p.y ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (Real.exp_pos _))
  simp only [EuclideanGeometry.inversion, RiemannianIsometry.mul_apply, reflection_apply,
    x_mk, y_mk, x_inversion, y_inversion, coe_projection, vsub_eq_sub, one_div]
  rw [inv_pow, hd, Real.exp_sub]
  simp only [neg_sq, Real.exp_log hpos]
  apply (WithLp.ext_iff 2).2
  ext <;> simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem exists_lift_similarity (c : ℝ) (hc : 0 < c) (A : ℝ ≃ₗᵢ[ℝ] ℝ) (b : ℝ) :
    ∃ Φ : Isom J SL2Tilde, baseIsomHom Φ = UpperHalfSpace.similarity c hc A b := by
  rcases A.eq_refl_or_eq_neg with rfl | rfl
  · refine ⟨translate b (Real.log c) 0, ?_⟩
    simpa only [Real.exp_log hc] using baseIsomHom_translate b (Real.log c) 0
  · refine ⟨translate b (Real.log c) 0 * reflection, ?_⟩
    rw [map_mul, baseIsomHom_reflection]
    have ht : baseIsomHom (translate b (Real.log c) 0) =
        UpperHalfSpace.similarity c hc (.refl ℝ ℝ) b := by
      simpa only [Real.exp_log hc] using baseIsomHom_translate b (Real.log c) 0
    rw [ht, UpperHalfSpace.similarity_mul_similarity]
    congr <;> simp

/-- Every isometry of the hyperbolic plane has a Sasaki isometry lift to `SL₂ℝ~`. -/
theorem baseIsomHom_surjective : Surjective baseIsomHom := by
  intro Ψ
  rcases UpperHalfSpace.exists_eq_similarity_or_exists_eq_inversion_mul_similarity Ψ with
    ⟨c, hc, A, b, rfl⟩ | ⟨a, R, hR, c, hc, A, b, rfl⟩
  · exact exists_lift_similarity c hc A b
  · obtain ⟨Φ₁, hΦ₁⟩ := exists_lift_similarity (R ^ 2) (sq_pos_of_ne_zero hR) (.refl ℝ ℝ) a
    obtain ⟨Φ₂, hΦ₂⟩ := exists_lift_similarity 1 one_pos (.refl ℝ ℝ) (-a)
    obtain ⟨Φ₃, hΦ₃⟩ := exists_lift_similarity c hc A b
    refine ⟨Φ₁ * (inversion * reflection) * Φ₂ * Φ₃, ?_⟩
    rw [map_mul baseIsomHom, map_mul baseIsomHom, map_mul baseIsomHom,
      hΦ₁, hΦ₂, hΦ₃,
      baseIsomHom_inversion_mul_reflection,
      UpperHalfSpace.inversion_eq_similarity_mul_inversion_mul_similarity a R hR]

/-- The first isomorphism theorem for the hyperbolic base action: the isometry group of
`SL₂ℝ~`, modulo the kernel of vertical translations, is the full isometry group of the
hyperbolic plane. The kernel is identified explicitly by `ker_baseIsomHom`. -/
def baseIsomQuotientMulEquiv :
    (Isom J SL2Tilde ⧸ baseIsomHom.ker) ≃* Isom K (UpperHalfSpace ℝ) :=
  QuotientGroup.quotientKerEquivOfSurjective baseIsomHom baseIsomHom_surjective

/-- The quotient classification sends the class of an isometry to its induced hyperbolic
base isometry. -/
@[simp] theorem baseIsomQuotientMulEquiv_apply_mk (Φ : Isom J SL2Tilde) :
    baseIsomQuotientMulEquiv (QuotientGroup.mk Φ) = baseIsomHom Φ :=
  TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk
    baseIsomHom baseIsomHom_surjective Φ

end TauCeti.SL2Tilde
