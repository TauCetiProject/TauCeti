/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic

/-!
# Clifford contractions of algebraic curvature tensors

Let `V` be a finite-dimensional real inner product space and `Q` the quadratic form
`Q v = -‖v‖²`, so that the Clifford relation reads `c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫`. Let `r` be
an algebraic curvature tensor on `V`, `r(u, v, z, w) = ⟪R(u, v) w, z⟫`
(`TauCeti.FourTensor.IsAlgebraicCurvature`), and let `(eᵢ)` be an orthonormal basis. This file
computes the Clifford contractions of `r` that produce the scalar curvature term of the
Lichnerowicz formula for the square of a spin Dirac operator.

* **Contraction of the last three slots.** For every `u`,
  `∑ⱼₖₗ r(u, eⱼ, eₖ, eₗ) c(eⱼ) c(eₖ) c(eₗ) = 2 c(Ric(u)♯)`, where `Ric(u)♯ = ∑ₗ Ric(u, eₗ) eₗ`
  (`TauCeti.FourTensor.sum_sum_sum_smul_ι_mul_ι_mul_ι`). Each rotation of `c(x) c(y) c(z)`
  differs from it by a commutator `⁅c(x) c(y), c(z)⁆`, which is a vector
  (`CliffordAlgebra.ι_mul_ι_lie_ι`), so the sum over the three rotations is `3 c(x) c(y) c(z)` up
  to terms of degree one. The first Bianchi identity kills that sum against `r`; what remains are
  the contractions of `r`.
* **The full contraction.** `∑ᵢⱼₖₗ r(eᵢ, eⱼ, eₖ, eₗ) c(eᵢ) c(eⱼ) c(eₖ) c(eₗ) = -2 Scal`
  (`TauCeti.FourTensor.sum_sum_sum_sum_smul_ι_mul_ι_mul_ι_mul_ι`), because the symmetric Ricci
  form contracts against `c(eᵢ) c(eₗ)` to minus its trace
  (`CliffordAlgebra.sum_sum_smul_ι_mul_ι_of_symm`).
* **The spin curvature term.** The curvature of the spinor bundle is
  `R^S(X, Y) = ¼ ∑ₖₗ ⟪R(X, Y) eₖ, eₗ⟫ c(eₖ) c(eₗ)`, and the curvature term of the Weitzenböck
  formula for the spin Dirac operator is `½ ∑ᵢⱼ c(eᵢ) c(eⱼ) R^S(eᵢ, eⱼ)`. It is the scalar
  `Scal / 4`
  (`TauCeti.FourTensor.sum_sum_inv_two_smul_ι_mul_ι_mul_inv_four_smul_sum_sum_smul_ι_mul_ι`).
  For the constant-curvature tensor, the curvature tensor of the unit sphere `Sⁿ` with
  `n = dim V`, it is `n (n - 1) / 4`
  (`sum_sum_inv_two_smul_ι_mul_ι_mul_inv_four_smul_sum_sum_smul_ι_mul_ι_constantCurvature`).

The statements live in the Clifford algebra itself, so they hold in every Clifford module after
applying the representation. They use only the Clifford relations and the symmetries of `r`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter II, Theorem 8.8.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed. (2007), Theorem 12.2.33.
-/

public section

open CliffordAlgebra
open scoped RealInnerProductSpace

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V} {I : Type*} [Fintype I] {r : FourTensor V}

omit [FiniteDimensional ℝ V] in
/-- By the first Bianchi identity, the sum of `r(u, eⱼ, eₖ, eₗ) c(eⱼ) c(eₖ) c(eₗ)` over the three
rotations of the Clifford factors vanishes. -/
private theorem sum_smul_rotations_eq_zero (hr : r.IsAlgebraicCurvature)
    (b : OrthonormalBasis I ℝ V) (u : V) :
    ∑ j, ∑ k, ∑ l, r ![u, b j, b k, b l] • (ι Q (b j) * ι Q (b k) * ι Q (b l) +
      ι Q (b k) * ι Q (b l) * ι Q (b j) + ι Q (b l) * ι Q (b j) * ι Q (b k)) = 0 := by
  -- Only the vanishing of the cyclic sums `sⱼₖₗ + sₖₗⱼ + sₗⱼₖ` of the coefficients is used.
  suffices h : ∀ s : I → I → I → ℝ, (∀ j k l, s j k l + s k l j + s l j k = 0) →
      ∑ j, ∑ k, ∑ l, s j k l • (ι Q (b j) * ι Q (b k) * ι Q (b l) +
        ι Q (b k) * ι Q (b l) * ι Q (b j) + ι Q (b l) * ι Q (b j) * ι Q (b k)) = 0 from
    h _ fun j k l ↦ hr.cyclic_last_eq_zero u (b j) (b k) (b l)
  intro s hs
  -- Rename the summation indices so that every product reads `c(eⱼ) c(eₖ) c(eₗ)`.
  have h2 : ∑ j, ∑ k, ∑ l, s j k l • (ι Q (b k) * ι Q (b l) * ι Q (b j)) =
      ∑ j, ∑ k, ∑ l, s l j k • (ι Q (b j) * ι Q (b k) * ι Q (b l)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  have h3 : ∑ j, ∑ k, ∑ l, s j k l • (ι Q (b l) * ι Q (b j) * ι Q (b k)) =
      ∑ j, ∑ k, ∑ l, s k l j • (ι Q (b j) * ι Q (b k) * ι Q (b l)) := by
    simp_rw [Finset.sum_comm (γ := I) (s := Finset.univ) (t := Finset.univ)
      (f := fun k l ↦ s _ k l • (ι Q (b l) * ι Q (b _) * ι Q (b k)))]
    exact Finset.sum_comm
  simp_rw [smul_add, Finset.sum_add_distrib]
  rw [h2, h3, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, ← add_smul]
  refine Finset.sum_eq_zero fun j _ ↦ Finset.sum_eq_zero fun k _ ↦
    Finset.sum_eq_zero fun l _ ↦ ?_
  rw [add_assoc, add_comm (s l j k), ← add_assoc, hs, zero_smul]

omit [FiniteDimensional ℝ V] in
/-- Expanding the three rotations of `c(eⱼ) c(eₖ) c(eₗ)` by the Clifford relations, the sum of
`r(u, eⱼ, eₖ, eₗ)` times them is `3 S - 6 T`, where `S = ∑ⱼₖₗ r(u, eⱼ, eₖ, eₗ) c(eⱼ) c(eₖ) c(eₗ)`
and `T = ∑ⱼₖ r(u, eⱼ, eₖ, eⱼ) c(eₖ)`. -/
private theorem sum_smul_rotations_eq (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hr : r.IsAlgebraicCurvature)
    (b : OrthonormalBasis I ℝ V) (u : V) :
    ∑ j, ∑ k, ∑ l, r ![u, b j, b k, b l] • (ι Q (b j) * ι Q (b k) * ι Q (b l) +
      ι Q (b k) * ι Q (b l) * ι Q (b j) + ι Q (b l) * ι Q (b j) * ι Q (b k)) =
      (3 : ℝ) • ∑ j, ∑ k, ∑ l, r ![u, b j, b k, b l] • (ι Q (b j) * ι Q (b k) * ι Q (b l)) -
        (6 : ℝ) • ∑ j, ∑ k, r ![u, b j, b k, b j] • ι Q (b k) := by
  classical
  -- Only the antisymmetry `sⱼₖₗ = -sⱼₗₖ` of the coefficients is used.
  suffices h : ∀ s : I → I → I → ℝ, (∀ j k l, s j k l = -s j l k) →
      ∑ j, ∑ k, ∑ l, s j k l • (ι Q (b j) * ι Q (b k) * ι Q (b l) +
        ι Q (b k) * ι Q (b l) * ι Q (b j) + ι Q (b l) * ι Q (b j) * ι Q (b k)) =
        (3 : ℝ) • ∑ j, ∑ k, ∑ l, s j k l • (ι Q (b j) * ι Q (b k) * ι Q (b l)) -
          (6 : ℝ) • ∑ j, ∑ k, s j k j • ι Q (b k) from
    h _ fun j k l ↦ hr.antisymm_last u (b j) (b k) (b l)
  intro s hs
  -- Each rotation differs from `c(eⱼ) c(eₖ) c(eₗ)` by a commutator `⁅c(x) c(y), c(z)⁆`, which is a
  -- vector.
  have hcyc (j k l : I) :
      ι Q (b j) * ι Q (b k) * ι Q (b l) + ι Q (b k) * ι Q (b l) * ι Q (b j) +
          ι Q (b l) * ι Q (b j) * ι Q (b k) =
        (3 : ℝ) • (ι Q (b j) * ι Q (b k) * ι Q (b l)) + (2 * ⟪b k, b l⟫) • ι Q (b j) -
          (4 * ⟪b j, b l⟫) • ι Q (b k) + (2 * ⟪b j, b k⟫) • ι Q (b l) := by
    have h1 := ι_mul_ι_lie_ι Q (b k) (b l) (b j)
    have h2 := ι_mul_ι_lie_ι Q (b j) (b k) (b l)
    simp only [Ring.lie_def, QuadraticMap.polar_eq_neg_two_inner hQ, map_sub, map_smul,
      ← mul_assoc] at h1 h2
    rw [eq_add_of_sub_eq h1,
      ← sub_sub_cancel (ι Q (b j) * ι Q (b k) * ι Q (b l)) (ι Q (b l) * ι Q (b j) * ι Q (b k)), h2,
      real_inner_comm (b j) (b l), real_inner_comm (b j) (b k)]
    module
  -- The three degree-one terms contract `s` against the metric.
  have hA1 : ∑ j, ∑ k, ∑ l, s j k l • ((2 * ⟪b k, b l⟫) • ι Q (b j)) = 0 := by
    have hzz (j k : I) : s j k k = 0 := by linarith [hs j k k]
    simp [smul_smul, b.inner_eq_ite, hzz]
  have hA2 : ∑ j, ∑ k, ∑ l, (s j k l * (4 * ⟪b j, b l⟫)) • ι Q (b k) =
      (4 : ℝ) • ∑ j, ∑ k, s j k j • ι Q (b k) := by
    simp [Finset.smul_sum, smul_smul, b.inner_eq_ite, mul_comm]
  have hA3 : ∑ j, ∑ k, ∑ l, (s j k l * (2 * ⟪b j, b k⟫)) • ι Q (b l) =
      -((2 : ℝ) • ∑ j, ∑ k, s j k j • ι Q (b k)) := by
    simp only [Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← Finset.sum_smul, smul_smul, ← neg_smul]
    congr 1
    simp [b.inner_eq_ite, hs j j l, mul_comm]
  have h0 : ∑ j, ∑ k, ∑ l, s j k l • ((3 : ℝ) • (ι Q (b j) * ι Q (b k) * ι Q (b l))) =
      (3 : ℝ) • ∑ j, ∑ k, ∑ l, s j k l • (ι Q (b j) * ι Q (b k) * ι Q (b l)) := by
    simp only [Finset.smul_sum, smul_smul, mul_comm]
  simp only [hcyc, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hA1]
  simp only [smul_smul] at h0 hA2 hA3 ⊢
  rw [h0, hA2, hA3]
  module

/-- **The Clifford contraction of the last three slots of a curvature tensor**: for
`Q v = -‖v‖²`, an algebraic curvature tensor `r` and an orthonormal basis `(eᵢ)`,
`∑ⱼₖₗ r(u, eⱼ, eₖ, eₗ) c(eⱼ) c(eₖ) c(eₗ) = 2 c(Ric(u)♯)`, where `Ric(u)♯ = ∑ₗ Ric(u, eₗ) eₗ`. -/
theorem sum_sum_sum_smul_ι_mul_ι_mul_ι (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hr : r.IsAlgebraicCurvature)
    (b : OrthonormalBasis I ℝ V) (u : V) :
    ∑ j, ∑ k, ∑ l, r ![u, b j, b k, b l] • (ι Q (b j) * ι Q (b k) * ι Q (b l)) =
      (2 : ℝ) • ι Q (∑ l, ricci r u (b l) • b l) := by
  -- With `S` the left side and `T = ∑ⱼₖ r(u, eⱼ, eₖ, eⱼ) c(eₖ)`, the rotations give `3 S = 6 T`.
  have h3 := (sum_smul_rotations_eq hQ hr b u).symm.trans (sum_smul_rotations_eq_zero hr b u)
  rw [sub_eq_zero, show (6 : ℝ) = 3 * 2 by norm_num, ← smul_smul] at h3
  rw [smul_right_injective _ (by norm_num : (3 : ℝ) ≠ 0) h3, Finset.sum_comm, map_sum]
  congr 2
  ext k
  rw [map_smul, ← Finset.sum_smul, ricci_apply_orthonormalBasis b]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hr.antisymm_first, hr.antisymm_last, neg_neg]

/-- **The full Clifford contraction of a curvature tensor**: for `Q v = -‖v‖²`, an algebraic
curvature tensor `r` and an orthonormal basis `(eᵢ)`,
`∑ᵢⱼₖₗ r(eᵢ, eⱼ, eₖ, eₗ) c(eᵢ) c(eⱼ) c(eₖ) c(eₗ) = -2 Scal`. -/
theorem sum_sum_sum_sum_smul_ι_mul_ι_mul_ι_mul_ι (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hr : r.IsAlgebraicCurvature) (b : OrthonormalBasis I ℝ V) :
    ∑ i, ∑ j, ∑ k, ∑ l,
        r ![b i, b j, b k, b l] • (ι Q (b i) * ι Q (b j) * ι Q (b k) * ι Q (b l)) =
      algebraMap ℝ (CliffordAlgebra Q) (-2 * scalar r) := by
  have h (i : I) : ∑ j, ∑ k, ∑ l,
      r ![b i, b j, b k, b l] • (ι Q (b i) * ι Q (b j) * ι Q (b k) * ι Q (b l)) =
        ∑ l, (2 * ricci r (b i) (b l)) • (ι Q (b i) * ι Q (b l)) := by
    calc _ = ι Q (b i) * ∑ j, ∑ k, ∑ l,
          r ![b i, b j, b k, b l] • (ι Q (b j) * ι Q (b k) * ι Q (b l)) := by
          simp only [Finset.mul_sum, mul_smul_comm, mul_assoc]
      _ = _ := by
          rw [sum_sum_sum_smul_ι_mul_ι_mul_ι hQ hr b]
          simp only [map_sum, map_smul, Finset.smul_sum, Finset.mul_sum, mul_smul_comm, smul_smul]
  simp_rw [h]
  rw [sum_sum_smul_ι_mul_ι_of_symm hQ b fun i l ↦ by rw [(hr.isSymm_ricci).eq (b i) (b l)]]
  congr 1
  simp_rw [scalar_apply_orthonormalBasis b, ← ricci_apply_orthonormalBasis b, ← Finset.mul_sum]
  ring

/-- **The spin curvature term of the Lichnerowicz formula**: for `Q v = -‖v‖²`, an algebraic
curvature tensor `r(u, v, z, w) = ⟪R(u, v) w, z⟫` and an orthonormal basis `(eᵢ)`, the spin
curvature `R^S(X, Y) = ¼ ∑ₖₗ ⟪R(X, Y) eₖ, eₗ⟫ c(eₖ) c(eₗ)` contracts to
`½ ∑ᵢⱼ c(eᵢ) c(eⱼ) R^S(eᵢ, eⱼ) = Scal / 4`. This is the curvature term of the Weitzenböck formula
`D² = ∇*∇ + Scal / 4` for the square of the spin Dirac operator. -/
theorem sum_sum_inv_two_smul_ι_mul_ι_mul_inv_four_smul_sum_sum_smul_ι_mul_ι
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hr : r.IsAlgebraicCurvature) (b : OrthonormalBasis I ℝ V) :
    ∑ i, ∑ j, (2 : ℝ)⁻¹ • (ι Q (b i) * ι Q (b j) *
        ((4 : ℝ)⁻¹ • ∑ k, ∑ l, r ![b i, b j, b l, b k] • (ι Q (b k) * ι Q (b l)))) =
      algebraMap ℝ (CliffordAlgebra Q) (scalar r / 4) := by
  have h : ∑ i, ∑ j, (2 : ℝ)⁻¹ • (ι Q (b i) * ι Q (b j) *
      ((4 : ℝ)⁻¹ • ∑ k, ∑ l, r ![b i, b j, b l, b k] • (ι Q (b k) * ι Q (b l)))) =
        (-(8 : ℝ)⁻¹) • ∑ i, ∑ j, ∑ k, ∑ l,
          r ![b i, b j, b k, b l] • (ι Q (b i) * ι Q (b j) * ι Q (b k) * ι Q (b l)) := by
    simp only [mul_smul_comm, Finset.mul_sum, Finset.smul_sum, smul_smul, ← mul_assoc]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
    rw [hr.antisymm_last (b i) (b j) (b l) (b k)]
    congr 1
    ring
  rw [h, sum_sum_sum_sum_smul_ι_mul_ι_mul_ι_mul_ι hQ hr b, Algebra.smul_def, ← map_mul]
  congr 1
  ring

/-- **The Lichnerowicz term of the round sphere**: for the constant-curvature tensor, the curvature
tensor of the unit sphere `Sⁿ` with `n = dim V`, the spin curvature term of the Lichnerowicz formula
is `n (n - 1) / 4`. For the unit two-sphere it is `1 / 2`. -/
theorem sum_sum_inv_two_smul_ι_mul_ι_mul_inv_four_smul_sum_sum_smul_ι_mul_ι_constantCurvature
    (hQ : ∀ v, Q v = -‖v‖ ^ 2) (b : OrthonormalBasis I ℝ V) :
    ∑ i, ∑ j, (2 : ℝ)⁻¹ • (ι Q (b i) * ι Q (b j) * ((4 : ℝ)⁻¹ •
        ∑ k, ∑ l, constantCurvature V ![b i, b j, b l, b k] • (ι Q (b k) * ι Q (b l)))) =
      algebraMap ℝ (CliffordAlgebra Q)
        (Module.finrank ℝ V * ((Module.finrank ℝ V : ℝ) - 1) / 4) := by
  rw [sum_sum_inv_two_smul_ι_mul_ι_mul_inv_four_smul_sum_sum_smul_ι_mul_ι hQ
    isAlgebraicCurvature_constantCurvature b, scalar_constantCurvature]

end TauCeti.FourTensor
