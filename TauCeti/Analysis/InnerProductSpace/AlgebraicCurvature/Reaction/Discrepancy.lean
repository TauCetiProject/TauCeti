/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Deformation
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Reaction.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.Analysis.InnerProductSpace.Parseval

/-!
# The reaction on Kulkarni–Nomizu products and the Böhm–Wilking discrepancy

Let `V` be a finite-dimensional real inner product space of dimension `n` with inner product `g`,
let `Q = reactionTensor` be the reaction term of the curvature evolution `R' = Q(R)` under Ricci
flow, and `B = reactionBilinear V` its polarization. Böhm and Wilking deform an algebraic
curvature tensor by `ℓ_(a,b)(r) = r + k ⊙ g`, adding a Kulkarni–Nomizu product with the inner
product (`TauCeti.FourTensor.boehmWilkingDeformation_apply_eq_add_kulkarniNomizu`, with
`k = b Ric₀ + (a Scal / n) g`). This file computes the reaction on such products and derives
their formula for the discrepancy between `Q` and its conjugate by `ℓ_(a,b)`, the identity that
transports `Q`-invariant cones `C` to `Q`-invariant cones `ℓ_(a,b)(C)`.

* **The action of a four-tensor on bilinear forms.** `TauCeti.FourTensor.curvatureAction r h` is
  `r(h)(u, v) = ∑_pq h(eₚ, e_q) r(eₚ, u, e_q, v)` in any orthonormal basis, with `r(g) = Ric(r)`.
  For algebraic `r`, `Ric(Q(r)) = 2 r(Ric(r))` and `Scal(Q(r)) = 2 tr(Ric♯ Ric♯)`.
* **Reaction against `h ⊙ g`.** For an algebraic curvature tensor `r` and a symmetric form `h`,
  `B(r, h ⊙ g) = r(h) ⊙ g + h ⊙ Ric(r)`: the terms of `r` with an argument `h♯ x`, where
  `h♯ = bilinFormToEnd h`, cancel by the first Bianchi identity. Together with
  `(h ⊙ g)(k) = tr(h♯ k♯) g + (tr k) h - ⟪h♯ k♯ ·, ·⟫ - ⟪k♯ h♯ ·, ·⟫` this evaluates `Q(k ⊙ g)`.
* **The discrepancy.** For `X = Q / 2`, `D_(a,b)(r) = ℓ_(a,b)⁻¹ X(ℓ_(a,b) r) - X(r)`
  (`TauCeti.FourTensor.boehmWilkingDiscrepancy`), so that `ℓ_(a,b)⁻¹ Q(ℓ_(a,b) r) = Q(r) + 2 D`.
  For `n ≥ 3`, nonzero eigenfactors and algebraic `r`,
  `D_(a,b)(r) = ((n - 2) b² - 2 (a - b)) Ric₀ ∧ Ric₀ + 2 a Ric ∧ Ric + 2 b² Ric₀² ∧ id + κ I`
  with `κ = tr(Ric₀♯ Ric₀♯) / (n (1 + 2 (n - 1) a)) · (n b² (1 - 2 b) - 2 (a - b) (1 - 2 b + n b²))`
  and `I` the constant-curvature tensor. It is stated for four-tensors, with `A ∧ B` written as
  `(A ⊙ B) / 2` (`TauCeti.FourTensor.boehmWilkingDiscrepancy_eq`), and for bivector operators
  (`TauCeti.FourTensor.curvatureEndomorphism_boehmWilkingDiscrepancy`). The discrepancy depends
  only on the Ricci tensor of `r`, not on its Weyl part.

## Main definitions

* `TauCeti.FourTensor.curvatureAction`: the action of a four-tensor on bilinear forms.
* `TauCeti.FourTensor.boehmWilkingDiscrepancy`: the discrepancy `D_(a,b)`.

## Main results

* `TauCeti.FourTensor.reactionBilinear_kulkarniNomizu_innerₗ_right` and its symmetric
  counterpart: `B(r, h ⊙ g) = r(h) ⊙ g + h ⊙ Ric(r)`.
* `TauCeti.FourTensor.curvatureAction_kulkarniNomizu_innerₗ` and
  `TauCeti.FourTensor.reactionTensor_kulkarniNomizu_innerₗ`: the action and reaction of `k ⊙ g`.
* `TauCeti.FourTensor.IsAlgebraicCurvature.ricci_reactionTensor` and
  `TauCeti.FourTensor.IsAlgebraicCurvature.scalar_reactionTensor`.
* `TauCeti.FourTensor.reactionTensor_boehmWilkingDeformation`,
  `TauCeti.FourTensor.boehmWilkingDeformationEquiv_symm_reactionTensor`,
  `TauCeti.FourTensor.boehmWilkingDiscrepancy_eq`, and
  `TauCeti.FourTensor.curvatureEndomorphism_boehmWilkingDiscrepancy`.

## References

* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. (2) 167 (2008), 1079–1097, Section 2, Theorem 2.
* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 2.
-/

public section

open LinearMap (BilinForm)
open scoped InnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The action of a four-tensor on bilinear forms -/

/-- The bilinear form `(x, y) ↦ r(x, u, y, v)` in the first and third slots of `r`. -/
private def slice13 (r : FourTensor V) (u v : V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y ↦ r ![x, u, y, v])
    (fun _ _ _ ↦ apply_add_first ..) (fun _ _ _ ↦ apply_smul_first ..)
    (fun _ _ _ ↦ apply_add_third ..) (fun _ _ _ ↦ apply_smul_third ..)

private def curvatureActionFun (r : FourTensor V) (h : BilinForm ℝ V) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun u v ↦ ∑ p, ∑ q, h (stdOrthonormalBasis ℝ V p)
      (stdOrthonormalBasis ℝ V q) *
        r ![stdOrthonormalBasis ℝ V p, u, stdOrthonormalBasis ℝ V q, v])
    (fun _ _ _ ↦ by simp only [apply_add_second, mul_add, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by
      simp only [apply_smul_second, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)
    (fun _ _ _ ↦ by simp only [apply_add_fourth, mul_add, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by
      simp only [apply_smul_fourth, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)

/-- The action `h ↦ r(h)` of a four-tensor `r` on bilinear forms, contracting the first and
third slots of `r` against `h`: in an orthonormal basis `(eₚ)`,
`r(h)(u, v) = ∑_pq h(eₚ, e_q) r(eₚ, u, e_q, v)`
(`TauCeti.FourTensor.curvatureAction_apply_orthonormalBasis`). Contracting against the inner
product gives the Ricci contraction, `r(g) = Ric(r)`. -/
def curvatureAction : FourTensor V →ₗ[ℝ] BilinForm ℝ V →ₗ[ℝ] BilinForm ℝ V :=
  LinearMap.mk₂ ℝ curvatureActionFun
    (fun _ _ _ ↦ by
      ext; simp [curvatureActionFun, mul_add, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by
      ext; simp only [curvatureActionFun, LinearMap.mk₂_apply, smul_apply, smul_eq_mul,
        LinearMap.smul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)
    (fun _ _ _ ↦ by
      ext; simp [curvatureActionFun, add_mul, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by
      ext; simp only [curvatureActionFun, LinearMap.mk₂_apply, smul_eq_mul,
        LinearMap.smul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)

/-- **Basis independence** of `curvatureAction`: in every orthonormal basis `b`,
`r(h)(u, v) = ∑_pq h(b p, b q) r(b p, u, b q, v)`. -/
theorem curvatureAction_apply_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (r : FourTensor V) (h : BilinForm ℝ V) (u v : V) :
    curvatureAction r h u v = ∑ p, ∑ q, h (b p) (b q) * r ![b p, u, b q, v] := by
  have hid : ∀ x y : V, ⟪(id : V → V) x, y⟫_ℝ = ⟪x, (id : V → V) y⟫_ℝ := fun _ _ ↦ rfl
  have key := (stdOrthonormalBasis ℝ V).sum_sum_inner_comp_eq_of_inner_eq b hid hid h
    (slice13 r u v)
  simp only [Real.inner_apply, slice13, LinearMap.mk₂_apply, id_eq] at key
  simp only [curvatureAction, curvatureActionFun, LinearMap.mk₂_apply]
  simpa only [mul_comm] using key

/-- Contracting a four-tensor against the inner product gives its Ricci contraction:
`r(g) = Ric(r)`. -/
@[simp]
theorem curvatureAction_innerₗ (r : FourTensor V) :
    curvatureAction r (innerₗ V) = ricci r := by
  classical
  let b := stdOrthonormalBasis ℝ V
  ext u v
  simp only [curvatureAction_apply_orthonormalBasis b, ricci_apply_orthonormalBasis b,
    innerₗ_apply_apply, orthonormal_iff_ite.mp b.orthonormal, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-! ### Contractions against Kulkarni–Nomizu products with the inner product -/

/-- Contracting the last two slots of an algebraic curvature tensor `r` against the
Kulkarni–Nomizu product `h ⊙ g` in an orthonormal basis `b`, where `h♯ = bilinFormToEnd h`:
`∑_pq r(a, c, b p, b q) (h ⊙ g)(x, y, b p, b q) = 2 (r(a, c, h♯ x, y) + r(a, c, x, h♯ y))`. -/
theorem sum_mul_kulkarniNomizu_innerₗ_last {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (h : BilinForm ℝ V) (a c x y : V) :
    (∑ p, ∑ q, r ![a, c, b p, b q] * kulkarniNomizu h (innerₗ V) ![x, y, b p, b q]) =
      2 * (r ![a, c, bilinFormToEnd h x, y] + r ![a, c, x, bilinFormToEnd h y]) := by
  set H := bilinFormToEnd h
  set B := toLinearMap₄ r a c
  have hH (z w : V) : ⟪w, H z⟫_ℝ = h z w := by
    rw [real_inner_comm, LinearMap.BilinForm.inner_bilinFormToEnd_left]
  have hexp : (∑ p, ∑ q, r ![a, c, b p, b q] * kulkarniNomizu h (innerₗ V) ![x, y, b p, b q]) =
      (∑ p, ∑ q, B (b p) (b q) * ⟪b p, H x⟫_ℝ * ⟪b q, y⟫_ℝ) +
        (∑ p, ∑ q, B (b p) (b q) * ⟪b p, x⟫_ℝ * ⟪b q, H y⟫_ℝ) -
        (∑ p, ∑ q, B (b p) (b q) * ⟪b p, y⟫_ℝ * ⟪b q, H x⟫_ℝ) -
        (∑ p, ∑ q, B (b p) (b q) * ⟪b p, H y⟫_ℝ * ⟪b q, x⟫_ℝ) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    simp only [B, toLinearMap₄_apply, kulkarniNomizu_apply, innerₗ_apply_apply, hH,
      real_inner_comm (b p) x, real_inner_comm (b p) y, real_inner_comm (b q) x,
      real_inner_comm (b q) y]
    ring
  simp only [hexp, b.sum_apply_mul_inner_mul_inner b]
  simp only [B, toLinearMap₄_apply]
  rw [hr.antisymm_last a c y, hr.antisymm_last a c (H y) x]
  ring

/-- Contracting the second and fourth slots of an algebraic curvature tensor `r` against the
Kulkarni–Nomizu product `h ⊙ g` of a symmetric form `h` in an orthonormal basis `b`:
`∑_pq r(a, b p, c, b q) (h ⊙ g)(x, b p, y, b q) =
  h(x, y) Ric(a, c) + ⟪x, y⟫ r(h)(a, c) - r(a, y, c, h♯ x) - r(a, h♯ y, c, x)`. -/
theorem sum_mul_kulkarniNomizu_innerₗ_second_fourth {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    {h : BilinForm ℝ V} (hh : h.IsSymm) (a c x y : V) :
    (∑ p, ∑ q, r ![a, b p, c, b q] * kulkarniNomizu h (innerₗ V) ![x, b p, y, b q]) =
      h x y * ricci r a c + ⟪x, y⟫_ℝ * curvatureAction r h a c -
        r ![a, y, c, bilinFormToEnd h x] - r ![a, bilinFormToEnd h y, c, x] := by
  classical
  set H := bilinFormToEnd h
  set B := (toLinearMap₄ r a).flip c
  have hH (z w : V) : ⟪w, H z⟫_ℝ = h z w := by
    rw [real_inner_comm, LinearMap.BilinForm.inner_bilinFormToEnd_left]
  have hB (p q : V) : B p q = r ![a, p, c, q] := by simp [B]
  have hexp : (∑ p, ∑ q, r ![a, b p, c, b q] * kulkarniNomizu h (innerₗ V) ![x, b p, y, b q]) =
      h x y * (∑ p, ∑ q, B (b p) (b q) * ⟪b p, b q⟫_ℝ) +
        ⟪x, y⟫_ℝ * (∑ p, ∑ q, h (b p) (b q) * r ![b p, a, b q, c]) -
        (∑ p, ∑ q, B (b p) (b q) * ⟪b p, y⟫_ℝ * ⟪b q, H x⟫_ℝ) -
        (∑ p, ∑ q, B (b p) (b q) * ⟪b p, H y⟫_ℝ * ⟪b q, x⟫_ℝ) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    simp only [hB, kulkarniNomizu_apply, innerₗ_apply_apply, hH, real_inner_comm (b q) x]
    rw [hr.swap_first_last (b p), hh.eq (b p) y]
    ring
  have hdiag : (∑ p, ∑ q, B (b p) (b q) * ⟪b p, b q⟫_ℝ) = ricci r a c := by
    simp only [orthonormal_iff_ite.mp b.orthonormal, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, hB, ricci_apply_orthonormalBasis b]
    exact Finset.sum_congr rfl fun p _ ↦ hr.swap_first_last _ _ _ _
  rw [hexp, hdiag, ← curvatureAction_apply_orthonormalBasis, b.sum_apply_mul_inner_mul_inner b,
    b.sum_apply_mul_inner_mul_inner b, hB, hB]

/-- **Reaction against a Kulkarni–Nomizu product with the inner product.** For an algebraic
curvature tensor `r` and a symmetric bilinear form `h`, the polarized reaction of `r` with
`h ⊙ g` is `B(r, h ⊙ g) = r(h) ⊙ g + h ⊙ Ric(r)`. -/
theorem reactionBilinear_kulkarniNomizu_innerₗ_right {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {h : BilinForm ℝ V} (hh : h.IsSymm) :
    reactionBilinear V r (kulkarniNomizu h (innerₗ V)) =
      kulkarniNomizu (curvatureAction r h) (innerₗ V) + kulkarniNomizu h (ricci r) := by
  set b := stdOrthonormalBasis ℝ V
  set H := bilinFormToEnd h
  refine ext_vec fun u v z w ↦ ?_
  rw [reactionBilinear_apply_orthonormalBasis b, add_apply, kulkarniNomizu_apply,
    kulkarniNomizu_apply]
  simp only [innerₗ_apply_apply]
  have s1a := sum_mul_kulkarniNomizu_innerₗ_last b hr h u v z w
  have s1b : (∑ p, ∑ q, kulkarniNomizu h (innerₗ V) ![u, v, b p, b q] * r ![z, w, b p, b q]) =
      2 * (r ![z, w, H u, v] + r ![z, w, u, H v]) := by
    simpa only [mul_comm (kulkarniNomizu h (innerₗ V) _)] using
      sum_mul_kulkarniNomizu_innerₗ_last b hr h z w u v
  have s2a := sum_mul_kulkarniNomizu_innerₗ_second_fourth b hr hh u z v w
  have s2b : (∑ p, ∑ q, kulkarniNomizu h (innerₗ V) ![u, b p, z, b q] * r ![v, b p, w, b q]) =
      h u z * ricci r v w + ⟪u, z⟫_ℝ * curvatureAction r h v w - r ![v, z, w, H u] -
        r ![v, H z, w, u] := by
    simpa only [mul_comm (kulkarniNomizu h (innerₗ V) _)] using
      sum_mul_kulkarniNomizu_innerₗ_second_fourth b hr hh v w u z
  have s3a := sum_mul_kulkarniNomizu_innerₗ_second_fourth b hr hh u w v z
  have s3b : (∑ p, ∑ q, kulkarniNomizu h (innerₗ V) ![u, b p, w, b q] * r ![v, b p, z, b q]) =
      h u w * ricci r v z + ⟪u, w⟫_ℝ * curvatureAction r h v z - r ![v, w, z, H u] -
        r ![v, H w, z, u] := by
    simpa only [mul_comm (kulkarniNomizu h (innerₗ V) _)] using
      sum_mul_kulkarniNomizu_innerₗ_second_fourth b hr hh v z u w
  rw [s1a, s1b, s2a, s2b, s3a, s3b]
  -- The terms of `r` with an argument `h♯ x` cancel by the first Bianchi identity, one group
  -- for each of `x = z, w, u, v`.
  linear_combination hr.cyclic_eq_zero u v (H z) w - hr.antisymm_last v (H z) w u +
    hr.swap_first_last u (H z) w v - hr.cyclic_eq_zero u v (H w) z +
    hr.antisymm_last u v z (H w) - hr.swap_first_last u (H w) z v +
    hr.antisymm_last v (H w) z u + hr.cyclic_last_eq_zero (H u) v z w +
    hr.swap_pairs z w (H u) v - hr.reverse v z w (H u) + hr.reverse v w z (H u) -
    hr.antisymm_last (H u) w z v + hr.cyclic_last_eq_zero (H v) u w z + hr.reverse z w u (H v) -
    hr.reverse u w z (H v) + hr.reverse u z w (H v) - hr.antisymm_last (H v) z w u

/-- Symmetric counterpart of `TauCeti.FourTensor.reactionBilinear_kulkarniNomizu_innerₗ_right`:
`B(h ⊙ g, r) = r(h) ⊙ g + h ⊙ Ric(r)`. -/
theorem reactionBilinear_kulkarniNomizu_innerₗ_left {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) {h : BilinForm ℝ V} (hh : h.IsSymm) :
    reactionBilinear V (kulkarniNomizu h (innerₗ V)) r =
      kulkarniNomizu (curvatureAction r h) (innerₗ V) + kulkarniNomizu h (ricci r) := by
  rw [reactionBilinear_comm, reactionBilinear_kulkarniNomizu_innerₗ_right hr hh]

/-- The action of a Kulkarni–Nomizu product with the inner product on a symmetric form: for
symmetric `h` and `k`, with `h♯ = bilinFormToEnd h` and `k♯ = bilinFormToEnd k`,
`(h ⊙ g)(k) = tr(h♯ k♯) g + (tr k) h - ⟪h♯ k♯ ·, ·⟫ - ⟪k♯ h♯ ·, ·⟫`. -/
theorem curvatureAction_kulkarniNomizu_innerₗ {h k : BilinForm ℝ V} (hh : h.IsSymm)
    (hk : k.IsSymm) :
    curvatureAction (kulkarniNomizu h (innerₗ V)) k =
      LinearMap.trace ℝ V (bilinFormToEnd h ∘ₗ bilinFormToEnd k) • innerₗ V +
        bilinFormTrace k • h - (innerₗ V).comp (bilinFormToEnd h ∘ₗ bilinFormToEnd k) -
        (innerₗ V).comp (bilinFormToEnd k ∘ₗ bilinFormToEnd h) := by
  classical
  set b := stdOrthonormalBasis ℝ V
  set H := bilinFormToEnd h
  set K := bilinFormToEnd k
  ext u v
  have hexp : curvatureAction (kulkarniNomizu h (innerₗ V)) k u v =
      ⟪u, v⟫_ℝ * (∑ p, ∑ q, h (b p) (b q) * k (b p) (b q)) +
        h u v * (∑ p, ∑ q, k (b p) (b q) * ⟪b p, b q⟫_ℝ) -
        (∑ p, h (b p) v * ∑ q, k (b p) (b q) * ⟪b q, u⟫_ℝ) -
        (∑ p, ∑ q, h u (b q) * (k (b p) (b q) * ⟪b p, v⟫_ℝ)) := by
    rw [curvatureAction_apply_orthonormalBasis b]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
    simp only [kulkarniNomizu_apply, innerₗ_apply_apply]
    rw [real_inner_comm u (b q)]
    ring
  have h3 : (∑ p, h (b p) v * ∑ q, k (b p) (b q) * ⟪b q, u⟫_ℝ) = ⟪H (K u), v⟫_ℝ := by
    calc (∑ p, h (b p) v * ∑ q, k (b p) (b q) * ⟪b q, u⟫_ℝ)
        = ∑ p, h.flip v (b p) * ⟪b p, K u⟫_ℝ := Finset.sum_congr rfl fun p _ ↦ by
          rw [b.sum_apply_mul_inner, LinearMap.BilinForm.flip_apply, hk.eq (b p) u,
            ← LinearMap.BilinForm.inner_bilinFormToEnd_left k u, real_inner_comm]
      _ = ⟪H (K u), v⟫_ℝ := by
          rw [b.sum_apply_mul_inner, LinearMap.BilinForm.flip_apply,
            LinearMap.BilinForm.inner_bilinFormToEnd_left]
  have h4 : (∑ p, ∑ q, h u (b q) * (k (b p) (b q) * ⟪b p, v⟫_ℝ)) = ⟪K (H u), v⟫_ℝ := by
    have hq (q : Fin (Module.finrank ℝ V)) :
        (∑ p, k (b p) (b q) * ⟪b p, v⟫_ℝ) = ⟪b q, K v⟫_ℝ := by
      calc (∑ p, k (b p) (b q) * ⟪b p, v⟫_ℝ) = ∑ p, k.flip (b q) (b p) * ⟪b p, v⟫_ℝ :=
            Finset.sum_congr rfl fun p _ ↦ by rw [LinearMap.BilinForm.flip_apply]
        _ = ⟪b q, K v⟫_ℝ := by
            rw [b.sum_apply_mul_inner, LinearMap.BilinForm.flip_apply, real_inner_comm,
              LinearMap.BilinForm.inner_bilinFormToEnd_left]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hq, b.sum_apply_mul_inner]
    rw [LinearMap.BilinForm.inner_bilinFormToEnd_left, hk.eq _ v,
      ← LinearMap.BilinForm.inner_bilinFormToEnd_left k v, real_inner_comm,
      LinearMap.BilinForm.inner_bilinFormToEnd_left]
  have h2 : (∑ p, ∑ q, k (b p) (b q) * ⟪b p, b q⟫_ℝ) = bilinFormTrace k := by
    simp only [orthonormal_iff_ite.mp b.orthonormal, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, bilinFormTrace_eq_sum k b]
  rw [hexp, h2, h3, h4, ← LinearMap.BilinForm.trace_bilinFormToEnd_comp_bilinFormToEnd b hh]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    innerₗ_apply_apply, smul_eq_mul, H, K]
  ring

/-- The Ricci contraction of the reaction tensor of an algebraic curvature tensor:
`Ric(Q(r)) = 2 r(Ric(r))`. -/
theorem IsAlgebraicCurvature.ricci_reactionTensor {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    ricci (FourTensor.reactionTensor r) = (2 : ℝ) • curvatureAction r (ricci r) := by
  ext u v
  rw [hr.ricci_reactionTensor_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
    LinearMap.smul_apply, LinearMap.smul_apply,
    curvatureAction_apply_orthonormalBasis (stdOrthonormalBasis ℝ V), smul_eq_mul]

/-- The scalar contraction of the reaction tensor of an algebraic curvature tensor is twice the
squared norm of its Ricci tensor: `Scal(Q(r)) = 2 tr(Ric♯ ∘ Ric♯)`. -/
theorem IsAlgebraicCurvature.scalar_reactionTensor {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    scalar (FourTensor.reactionTensor r) =
      2 * LinearMap.trace ℝ V (ricciEndomorphism r ∘ₗ ricciEndomorphism r) := by
  rw [hr.scalar_reactionTensor_apply_orthonormalBasis (stdOrthonormalBasis ℝ V),
    ricciEndomorphism_apply, LinearMap.BilinForm.trace_bilinFormToEnd_comp_bilinFormToEnd
      (stdOrthonormalBasis ℝ V) hr.isSymm_ricci]
  simp only [sq]

/-- The reaction tensor of a Kulkarni–Nomizu product with the inner product: for a symmetric form
`k` with `k♯ = bilinFormToEnd k` on an `n`-dimensional space,
`Q(k ⊙ g) = (tr(k♯ k♯) g + (tr k) k - 2 ⟪k♯ k♯ ·, ·⟫) ⊙ g + k ⊙ ((n - 2) k + (tr k) g)`. -/
theorem reactionTensor_kulkarniNomizu_innerₗ {k : BilinForm ℝ V} (hk : k.IsSymm) :
    reactionTensor (kulkarniNomizu k (innerₗ V)) =
      kulkarniNomizu (LinearMap.trace ℝ V (bilinFormToEnd k ∘ₗ bilinFormToEnd k) • innerₗ V +
          bilinFormTrace k • k - (2 : ℝ) • (innerₗ V).comp (bilinFormToEnd k ∘ₗ bilinFormToEnd k))
        (innerₗ V) +
      kulkarniNomizu k (((Module.finrank ℝ V : ℝ) - 2) • k + bilinFormTrace k • innerₗ V) := by
  have hg : LinearMap.BilinForm.IsSymm (innerₗ V) :=
    LinearMap.BilinForm.isSymm_iff.mpr isSymm_inner
  rw [← reactionBilinear_self, reactionBilinear_kulkarniNomizu_innerₗ_right
    (isAlgebraicCurvature_kulkarniNomizu hk hg) hk, curvatureAction_kulkarniNomizu_innerₗ hk hk,
    ricci_kulkarniNomizu_innerₗ, two_smul]
  rw [sub_sub (α := LinearMap.BilinForm ℝ V)]

/-! ### The Böhm–Wilking discrepancy -/

/-- The reaction tensor of a Böhm–Wilking deformation `ℓ_(a,b)(r) = r + k ⊙ g`, where
`k = b Ric₀ + (a Scal / n) g`, of an algebraic curvature tensor `r` in dimension `n ≠ 2`:
`Q(ℓ_(a,b) r) = Q(r) + 2 (r(k) ⊙ g + k ⊙ Ric(r)) + Q(k ⊙ g)`. -/
theorem reactionTensor_boehmWilkingDeformation {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (hn : Module.finrank ℝ V ≠ 2) (a b : ℝ) :
    reactionTensor (boehmWilkingDeformation a b r) = reactionTensor r +
      (2 : ℝ) • (kulkarniNomizu (curvatureAction r (b • tracelessRicci r +
          (a * scalar r / Module.finrank ℝ V) • innerₗ V)) (innerₗ V) +
        kulkarniNomizu (b • tracelessRicci r + (a * scalar r / Module.finrank ℝ V) • innerₗ V)
          (ricci r)) +
      reactionTensor (kulkarniNomizu (b • tracelessRicci r +
        (a * scalar r / Module.finrank ℝ V) • innerₗ V) (innerₗ V)) := by
  have hg : LinearMap.BilinForm.IsSymm (innerₗ V) :=
    LinearMap.BilinForm.isSymm_iff.mpr isSymm_inner
  rw [boehmWilkingDeformation_apply_eq_add_kulkarniNomizu hn, reactionTensor_add,
    reactionBilinear_kulkarniNomizu_innerₗ_right hr ((hr.isSymm_tracelessRicci.smul b).add
      (hg.smul _))]

variable (V) in
/-- The **Böhm–Wilking discrepancy** `D_(a,b)(r) = ℓ_(a,b)⁻¹ X(ℓ_(a,b) r) - X(r)` of the vector
field `X = Q / 2`, where `Q = reactionTensor` and `ℓ_(a,b) = boehmWilkingDeformation a b`. It
measures how far the deformation `ℓ_(a,b)` is from intertwining the reaction ODE `R' = Q(R)`
with itself: `ℓ_(a,b)⁻¹ Q(ℓ_(a,b) r) = Q(r) + 2 D_(a,b)(r)`
(`TauCeti.FourTensor.boehmWilkingDeformationEquiv_symm_reactionTensor`). The inverse is written
as `ℓ_(-a / (1 + 2 (n - 1) a), -b / (1 + (n - 2) b))`, which inverts `ℓ_(a,b)` whenever both
eigenfactors `1 + 2 (n - 1) a` and `1 + (n - 2) b` are nonzero. -/
def boehmWilkingDiscrepancy (a b : ℝ) (r : FourTensor V) : FourTensor V :=
  (1 / 2 : ℝ) • (boehmWilkingDeformation (-a / (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a))
      (-b / (1 + ((Module.finrank ℝ V : ℝ) - 2) * b))
      (reactionTensor (boehmWilkingDeformation a b r)) - reactionTensor r)

/-- Definition of `boehmWilkingDiscrepancy V a b r`. -/
theorem boehmWilkingDiscrepancy_def (a b : ℝ) (r : FourTensor V) :
    boehmWilkingDiscrepancy V a b r =
      (1 / 2 : ℝ) • (boehmWilkingDeformation (-a / (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a))
        (-b / (1 + ((Module.finrank ℝ V : ℝ) - 2) * b))
        (reactionTensor (boehmWilkingDeformation a b r)) - reactionTensor r) := (rfl)

/-- For nonzero eigenfactors, the inverse Böhm–Wilking deformation carries the reaction of the
deformed tensor to the reaction plus twice the discrepancy:
`ℓ_(a,b)⁻¹ Q(ℓ_(a,b) r) = Q(r) + 2 D_(a,b)(r)`. -/
theorem boehmWilkingDeformationEquiv_symm_reactionTensor {a b : ℝ}
    (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) (r : FourTensor V) :
    (boehmWilkingDeformationEquiv ha hb).symm (reactionTensor (boehmWilkingDeformation a b r)) =
      reactionTensor r + (2 : ℝ) • boehmWilkingDiscrepancy V a b r := by
  rw [boehmWilkingDiscrepancy_def, smul_smul, boehmWilkingDeformationEquiv_symm_apply]
  norm_num

/-- **The Böhm–Wilking discrepancy formula** (Böhm–Wilking, Theorem 2). For an algebraic curvature
tensor `r` on an `n`-dimensional space, `n ≥ 3`, and nonzero eigenfactors
`1 + 2 (n - 1) a` and `1 + (n - 2) b`,
`D_(a,b)(r) = ((n - 2) b² - 2 (a - b)) / 2 · Ric₀ ⊙ Ric₀ + a · Ric ⊙ Ric + b² · Ric₀² ⊙ g + κ I`,
where `Ric₀² = ⟪Ric₀♯ Ric₀♯ ·, ·⟫`, `I` is the constant-curvature tensor and
`κ = tr(Ric₀♯ Ric₀♯) / (n (1 + 2 (n - 1) a)) · (n b² (1 - 2 b) - 2 (a - b) (1 - 2 b + n b²))`.
In particular `D_(a,b)(r)` depends only on the Ricci tensor of `r`, not on its Weyl part. Since
the bivector operator of `A ⊙ B` is `2 A♯ ∧ B♯`, this is the operator identity of
`TauCeti.FourTensor.curvatureEndomorphism_boehmWilkingDiscrepancy`. -/
theorem boehmWilkingDiscrepancy_eq {r : FourTensor V} (hr : IsAlgebraicCurvature r)
    (hn : 2 < Module.finrank ℝ V) {a b : ℝ}
    (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) :
    boehmWilkingDiscrepancy V a b r =
      ((((Module.finrank ℝ V : ℝ) - 2) * b ^ 2 - 2 * (a - b)) / 2) •
          kulkarniNomizu (tracelessRicci r) (tracelessRicci r) +
        a • kulkarniNomizu (ricci r) (ricci r) +
        b ^ 2 • kulkarniNomizu ((innerₗ V).comp
          (tracelessRicciEndomorphism r ∘ₗ tracelessRicciEndomorphism r)) (innerₗ V) +
        (LinearMap.trace ℝ V (tracelessRicciEndomorphism r ∘ₗ tracelessRicciEndomorphism r) /
            (Module.finrank ℝ V * (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a)) *
          (Module.finrank ℝ V * b ^ 2 * (1 - 2 * b) -
            2 * (a - b) * (1 - 2 * b + Module.finrank ℝ V * b ^ 2))) • constantCurvature V := by
  have hn0 : (Module.finrank ℝ V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by norm_cast; omega)
  have hn2 : (Module.finrank ℝ V : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by norm_cast; omega)
  have hg : LinearMap.BilinForm.IsSymm (innerₗ V) :=
    LinearMap.BilinForm.isSymm_iff.mpr isSymm_inner
  -- Write `ℓ_(a,b) r = r + k ⊙ g` and let `m` be its Ricci form.
  obtain ⟨k, hk_def⟩ : ∃ k : BilinForm ℝ V,
      k = b • tracelessRicci r + (a * scalar r / Module.finrank ℝ V) • innerₗ V := ⟨_, rfl⟩
  have hk : k.IsSymm := hk_def ▸ (hr.isSymm_tracelessRicci.smul b).add (hg.smul _)
  have hA : curvatureAction (boehmWilkingDeformation a b r) =
      curvatureAction r + curvatureAction (kulkarniNomizu k (innerₗ V)) := by
    rw [hk_def, boehmWilkingDeformation_apply_eq_add_kulkarniNomizu hn.ne', map_add]
  obtain ⟨m, hm_def⟩ : ∃ m : BilinForm ℝ V, m = ricci (boehmWilkingDeformation a b r) :=
    ⟨_, rfl⟩
  have hm : m = (1 + ((Module.finrank ℝ V : ℝ) - 2) * b) • tracelessRicci r +
      ((1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a) * scalar r / Module.finrank ℝ V) •
        innerₗ V := hm_def ▸ ricci_boehmWilkingDeformation a b r
  have hmsymm : m.IsSymm := hm_def ▸ (hr.boehmWilkingDeformation a b).isSymm_ricci
  have hρ : ricci r = tracelessRicci r + (scalar r / Module.finrank ℝ V) • innerₗ V := by
    rw [tracelessRicci_apply]; exact (sub_add_cancel (G := BilinForm ℝ V) _ _).symm
  -- Expand the inverse deformation through the Ricci and scalar contractions of `Q(ℓ_(a,b) r)`,
  -- and every reaction and action term through the contraction formulas above.
  rw [boehmWilkingDiscrepancy_def, boehmWilkingDeformation_apply, scalarPart_apply,
    tracelessRicciPart_apply, tracelessRicci_apply,
    (hr.boehmWilkingDeformation a b).ricci_reactionTensor,
    (hr.boehmWilkingDeformation a b).scalar_reactionTensor, ricciEndomorphism_apply, ← hm_def,
    hA, LinearMap.add_apply, curvatureAction_kulkarniNomizu_innerₗ hk hmsymm,
    reactionTensor_boehmWilkingDeformation hr hn.ne', ← hk_def,
    reactionTensor_kulkarniNomizu_innerₗ hk, hm, hk_def, hρ]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    curvatureAction_innerₗ, hρ, bilinFormToEnd_innerₗ, tracelessRicciEndomorphism_apply]
  -- Evaluate on four vectors: what remains is an identity of real polynomials in `a`, `b`, `n`,
  -- the scalar curvature, `tr(Ric₀♯ Ric₀♯)` and the values of the bilinear forms involved.
  refine ext_vec fun u v z w ↦ ?_
  simp only [sub_apply, add_apply, smul_apply, kulkarniNomizu_apply, constantCurvature_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.id_comp, LinearMap.comp_id, map_add, map_smul, LinearMap.trace_id,
    LinearMap.BilinForm.trace_bilinFormToEnd, bilinFormTrace_tracelessRicci, bilinFormTrace_inner,
    innerₗ_apply_apply, LinearMap.BilinForm.inner_bilinFormToEnd_left, smul_eq_mul]
  generalize hα : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a = α at ha ⊢
  generalize hβ : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b = β at hb ⊢
  obtain rfl : a = (α - 1) / (2 * ((Module.finrank ℝ V : ℝ) - 1)) := by
    rw [← hα]; field_simp; ring
  obtain rfl : b = (β - 1) / ((Module.finrank ℝ V : ℝ) - 2) := by
    rw [← hβ]; field_simp; ring
  field_simp
  ring

/-- **The Böhm–Wilking discrepancy formula, operator form** (Böhm–Wilking, Theorem 2). On
bivectors, with `Ric♯` and `Ric₀♯` the Ricci and trace-free Ricci endomorphisms and `A ∧ B`
the operator `exteriorPower.symmMap₂ A B`,
`D_(a,b)(R) = ((n - 2) b² - 2 (a - b)) Ric₀ ∧ Ric₀ + 2 a Ric ∧ Ric + 2 b² Ric₀² ∧ id + κ I`
with `I = id` and `κ` as in `TauCeti.FourTensor.boehmWilkingDiscrepancy_eq`. -/
theorem curvatureEndomorphism_boehmWilkingDiscrepancy {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) (hn : 2 < Module.finrank ℝ V) {a b : ℝ}
    (ha : 1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((Module.finrank ℝ V : ℝ) - 2) * b ≠ 0) :
    curvatureEndomorphism (boehmWilkingDiscrepancy V a b r) =
      (((Module.finrank ℝ V : ℝ) - 2) * b ^ 2 - 2 * (a - b)) •
          exteriorPower.symmMap₂ (tracelessRicciEndomorphism r) (tracelessRicciEndomorphism r) +
        (2 * a) • exteriorPower.symmMap₂ (ricciEndomorphism r) (ricciEndomorphism r) +
        (2 * b ^ 2) • exteriorPower.symmMap₂
          (tracelessRicciEndomorphism r ∘ₗ tracelessRicciEndomorphism r) LinearMap.id +
        (LinearMap.trace ℝ V (tracelessRicciEndomorphism r ∘ₗ tracelessRicciEndomorphism r) /
            (Module.finrank ℝ V * (1 + 2 * ((Module.finrank ℝ V : ℝ) - 1) * a)) *
          (Module.finrank ℝ V * b ^ 2 * (1 - 2 * b) -
            2 * (a - b) * (1 - 2 * b + Module.finrank ℝ V * b ^ 2))) • LinearMap.id := by
  rw [boehmWilkingDiscrepancy_eq hr hn ha hb]
  simp only [map_add, map_smul, curvatureEndomorphism_kulkarniNomizu,
    curvatureEndomorphism_constantCurvature, LinearMap.bilinFormToEnd_innerₗ_comp,
    bilinFormToEnd_innerₗ, ← tracelessRicciEndomorphism_apply, ← ricciEndomorphism_apply,
    smul_smul]
  congr 3 <;> ring_nf

end TauCeti.FourTensor
