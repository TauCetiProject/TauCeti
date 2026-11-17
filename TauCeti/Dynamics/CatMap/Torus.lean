/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.CatMap.Basic
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Topology.Algebra.Module.Matrix
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import TauCeti.Topology.Instances.AddCircle.Torus

/-!
# The periodic points of Arnold's cat map

The integer matrix `P = !![2, 1; 1, 1]` (`TauCeti.catMap`) has determinant one, so it acts on the
torus `T² = Fin 2 → AddCircle p` by a diffeomorphism `φ` (`TauCeti.catMapDiffeomorph`), Arnold's
cat map, whose iterate `φ^[n]` is induced by `Pⁿ` (`TauCeti.iterate_catMapDiffeomorph`). This file
computes the dynamical side of the cat map, its periodic points with their local fixed-point
indices, and compares it with the homological zeta function of `TauCeti.Dynamics.CatMap.Basic`.

* **Counting.** A point is fixed by `φ^[n]` exactly when `Pⁿ - 1` kills it. The integer matrix
  `Pⁿ - 1` has determinant `det (1 - Pⁿ) = 2 - tr (Pⁿ) ≤ 0`, so `φ` has exactly
  `tr (Pⁿ) - 2` points of period `n` (`TauCeti.natCard_ptsOfPeriod_catMapDiffeomorph`), by the
  count `Matrix.natCard_ker_smulVecHom` of the kernel of an integer matrix acting on a torus.
* **Local indices.** At every such point the differential of `φ^[n]` is the matrix `Pⁿ`, read on the
  tangent space `Fin 2 → ℝ`, so `det (1 - dφ^[n]) = det (1 - Pⁿ) < 0`: every periodic point is a
  nondegenerate fixed point of index `-1`
  (`TauCeti.sign_det_id_sub_fixedPointDerivative_iterate_catMapDiffeomorph`), and the cat map is
  nondegenerate up to every period (`TauCeti.isNondegenerateUpToPeriod_catMapDiffeomorph`).
* **Lefschetz numbers.** Summing the indices over the fixed points of `φ^[n]` gives
  `2 - tr (Pⁿ)` (`TauCeti.finsum_sign_det_id_sub_fixedPointDerivative_iterate_catMapDiffeomorph`),
  the Lefschetz number `L (φ^[n])` of the action of `φ^[n]` on the homology of the torus.
* **Zeta function.** Consequently the dynamical zeta function
  `exp (∑ₙ (∑_{φ^[n] x = x} sgn det (1 - dφ^[n]_x)) tⁿ / n)` of the cat map is
  `det (1 - t P) / (1 - t)² = 1 - t - 2 t² - 3 t³ - ⋯`, its homological zeta function
  (`TauCeti.subst_exp_finsum_sign_det_id_sub_fixedPointDerivative_iterate_catMapDiffeomorph`).

These are the orbit-side data of the cat map in the comparison of the weighted count of
pseudoholomorphic tori in `S¹ × Y_φ` with the zeta function of `φ`: every periodic orbit is
positive hyperbolic, with return maps of negative `det (1 - Pⁿ)`.

## References

* V. I. Arnold and A. Avez, *Ergodic Problems of Classical Mechanics*, Benjamin, 1968, Chapter 1.
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
-/

public section

noncomputable section

open Function Matrix
open scoped Manifold ContDiff

namespace TauCeti

variable (p : ℝ) [Fact (0 < p)]

/-- **Arnold's cat map** as a diffeomorphism of the torus `Fin 2 → AddCircle p`: the action of the
matrix `!![2, 1; 1, 1]` of determinant one (`TauCeti.catMap`). -/
def catMapDiffeomorph :
    (Fin 2 → AddCircle p) ≃ₘ⟮ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ),
      ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)⟯ (Fin 2 → AddCircle p) :=
  Diffeomorph.constSmul _ ∞
    (SpecialLinearGroup.toGL (⟨catMap, det_catMap⟩ : SpecialLinearGroup (Fin 2) ℤ))

/-- The cat map sends `x` to `k ↦ ∑ i, P k i • x i`. -/
@[simp]
theorem catMapDiffeomorph_apply (x : Fin 2 → AddCircle p) :
    catMapDiffeomorph p x = Matrix.smulVecHom catMap (AddCircle p) x := by
  simp only [catMapDiffeomorph, Diffeomorph.constSmul_apply]
  -- The matrix underlying `toGL ⟨P, _⟩` is `P`.
  exact AddCircle.generalLinearGroup_smul_eq_smulVecHom p _ x

/-- The `n`-th iterate of the cat map is the map of the torus induced by the matrix `Pⁿ`. -/
theorem iterate_catMapDiffeomorph (n : ℕ) (x : Fin 2 → AddCircle p) :
    (⇑(catMapDiffeomorph p))^[n] x = Matrix.smulVecHom (catMap ^ n) (AddCircle p) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, catMapDiffeomorph_apply, pow_succ', smulVecHom_mul,
      ContinuousAddMonoidHom.coe_comp, Function.comp_apply]

/-- A point is fixed by the `n`-th iterate of the cat map exactly when `Pⁿ - 1` kills it. -/
theorem iterate_catMapDiffeomorph_eq_self_iff (n : ℕ) (x : Fin 2 → AddCircle p) :
    (⇑(catMapDiffeomorph p))^[n] x = x ↔
      Matrix.smulVecHom (catMap ^ n - 1) (AddCircle p) x = 0 := by
  rw [smulVecHom_sub_apply, smulVecHom_one, ContinuousAddMonoidHom.coe_id, id_eq, sub_eq_zero,
    iterate_catMapDiffeomorph]

/-- **The periodic points of the cat map.** The cat map has exactly `tr (Pⁿ) - 2` points of period
`n`. For `n = 0` every point has period `0` and both sides are `0`, `Nat.card` taking its junk
value on the infinite torus. -/
theorem natCard_ptsOfPeriod_catMapDiffeomorph (n : ℕ) :
    (Nat.card (ptsOfPeriod (catMapDiffeomorph p) n) : ℤ) = (catMap ^ n).trace - 2 := by
  have hdet : (1 - catMap ^ n).det = 2 - (catMap ^ n).trace :=
    det_one_sub_eq_two_sub_trace_of_det_eq_one (by rw [det_pow, det_catMap, one_pow])
  have hker : ptsOfPeriod (catMapDiffeomorph p) n =
      (Matrix.smulVecHom (catMap ^ n - 1) (AddCircle p)).toAddMonoidHom.ker :=
    Set.ext fun x ↦ iterate_catMapDiffeomorph_eq_self_iff p n x
  have hneg : (catMap ^ n - 1).det = (1 - catMap ^ n).det := by
    rw [← neg_sub, det_neg, Fintype.card_fin, neg_one_sq, one_mul]
  have hle : (1 - catMap ^ n).det ≤ 0 := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · exact (det_one_sub_catMap_pow_neg hn).le
  rw [hker, SetLike.coe_sort_coe, natCard_ker_smulVecHom p _ (Fact.out : 0 < p).ne', hneg,
    Int.ofNat_natAbs_of_nonpos hle, hdet]
  ring

/-- The differential of the `n`-th iterate of the cat map is, at every point, the matrix `Pⁿ` acting
on the tangent space `Fin 2 → ℝ` of the torus. -/
theorem hasMFDerivAt_iterate_catMapDiffeomorph (n : ℕ) (x : Fin 2 → AddCircle p) :
    HasMFDerivAt (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ))
      (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (⇑(catMapDiffeomorph p))^[n] x
      (LinearMap.toContinuousLinearMap (Matrix.toLin' ((catMap ^ n).map ((↑) : ℤ → ℝ)))) := by
  set g := SpecialLinearGroup.toGL (⟨catMap, det_catMap⟩ : SpecialLinearGroup (Fin 2) ℤ)
  have h : (⇑(catMapDiffeomorph p))^[n] = (g ^ n • ·) := by
    rw [← smul_iterate]
    congr 1
    funext y
    simp only [catMapDiffeomorph, Diffeomorph.constSmul_apply, g]
  have hg : ((g ^ n : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = catMap ^ n := by
    rw [Units.val_pow_eq_pow_val]
    -- The matrix underlying `toGL ⟨P, _⟩` is `P`.
    rfl
  rw [h, ← hg]
  exact AddCircle.hasMFDerivAt_generalLinearGroup_smul p (g ^ n) x

/-- At a fixed point of the `n`-th iterate of the cat map, `det (1 - dφ^[n]) = det (1 - Pⁿ)`. -/
theorem det_id_sub_fixedPointDerivative_iterate_catMapDiffeomorph (n : ℕ)
    (x : {x // (⇑(catMapDiffeomorph p))^[n] x = x}) :
    LinearMap.det (LinearMap.id - fixedPointDerivative
      (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (⇑(catMapDiffeomorph p))^[n] x) =
      ((1 - catMap ^ n).det : ℝ) := by
  rw [(hasMFDerivAt_iterate_catMapDiffeomorph p n x.1).fixedPointDerivative_eq]
  -- The tangent spaces of the torus are its model space `Fin 2 → ℝ`, on which the differential
  -- acts by the matrix `Pⁿ`; `change` forgets the `TangentSpace` wrapper so that `toLin'` applies.
  change LinearMap.det (LinearMap.id (R := ℝ) (M := Fin 2 → ℝ) -
    Matrix.toLin' ((catMap ^ n).map ((↑) : ℤ → ℝ))) = _
  rw [← Matrix.toLin'_one, ← map_sub, LinearMap.det_toLin', Int.cast_det,
    Matrix.map_sub _ Int.cast_sub, Matrix.map_one _ Int.cast_zero Int.cast_one]

/-- **Every periodic point of the cat map has index `-1`.** For `n ≠ 0`, at every fixed point of
`φ^[n]` the sign of `det (1 - dφ^[n])` is `-1`: the point is nondegenerate and positive
hyperbolic. -/
theorem sign_det_id_sub_fixedPointDerivative_iterate_catMapDiffeomorph {n : ℕ} (hn : n ≠ 0)
    (x : {x // (⇑(catMapDiffeomorph p))^[n] x = x}) :
    SignType.sign (LinearMap.det (LinearMap.id - fixedPointDerivative
      (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (⇑(catMapDiffeomorph p))^[n] x)) = -1 := by
  rw [det_id_sub_fixedPointDerivative_iterate_catMapDiffeomorph, sign_neg]
  exact_mod_cast det_one_sub_catMap_pow_neg hn

/-- **The cat map is nondegenerate up to every period**: no return map of a periodic orbit has the
eigenvalue `1`. -/
theorem isNondegenerateUpToPeriod_catMapDiffeomorph (N : ℕ) :
    IsNondegenerateUpToPeriod (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ))
      (catMapDiffeomorph p) N := by
  rw [isNondegenerateUpToPeriod_iff]
  intro k hk _ x hx
  rw [isNondegenerateFixedPt_iff_det_id_sub_ne_zero (x := ⟨x, hx⟩)
    (hasMFDerivAt_iterate_catMapDiffeomorph p k x).mdifferentiableAt,
    det_id_sub_fixedPointDerivative_iterate_catMapDiffeomorph]
  exact_mod_cast (det_one_sub_catMap_pow_neg hk.ne').ne

/-- **The Lefschetz numbers of the cat map.** The indices `sgn det (1 - dφ^[n])` of the fixed points
of `φ^[n]` add up to `2 - tr (Pⁿ)`, the Lefschetz number of the action of `φ^[n]` on the homology of
the torus. For `n = 0` every index is `0`, and so is `2 - tr 1`. -/
theorem finsum_sign_det_id_sub_fixedPointDerivative_iterate_catMapDiffeomorph (n : ℕ) :
    ∑ᶠ x : {x // (⇑(catMapDiffeomorph p))^[n] x = x},
        (SignType.sign (LinearMap.det (LinearMap.id - fixedPointDerivative
          (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (⇑(catMapDiffeomorph p))^[n] x)) : ℤ) =
      2 - (catMap ^ n).trace := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp_rw [det_id_sub_fixedPointDerivative_iterate_catMapDiffeomorph]
    norm_num
  simp_rw [sign_det_id_sub_fixedPointDerivative_iterate_catMapDiffeomorph p hn]
  have hcard : (Nat.card {x // (⇑(catMapDiffeomorph p))^[n] x = x} : ℤ) =
      (catMap ^ n).trace - 2 :=
    (congrArg _ (Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ Iff.rfl))).trans
      (natCard_ptsOfPeriod_catMapDiffeomorph p n)
  have : Finite {x // (⇑(catMapDiffeomorph p))^[n] x = x} := Nat.finite_of_card_ne_zero <| by
    have := det_one_sub_catMap_pow_neg hn
    rw [det_one_sub_eq_two_sub_trace_of_det_eq_one (by rw [det_pow, det_catMap, one_pow])] at this
    lia
  have := Fintype.ofFinite {x // (⇑(catMapDiffeomorph p))^[n] x = x}
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    nsmul_eq_mul, SignType.coe_neg_one, mul_neg_one, hcard, neg_sub]

/-- **The dynamical zeta function of the cat map.** The series
`exp (∑ₙ (∑_{φ^[n] x = x} sgn det (1 - dφ^[n]_x)) tⁿ / n)` of the fixed-point indices of the
iterates of the cat map is `1 - t - 2 t² - 3 t³ - ⋯ = det (1 - t P) / (1 - t)²`
(`TauCeti.coe_charpolyRev_catMap_mul_mk_one_sq`): it agrees with the homological zeta function
`TauCeti.subst_exp_two_sub_trace_catMap_pow`. -/
theorem subst_exp_finsum_sign_det_id_sub_fixedPointDerivative_iterate_catMapDiffeomorph :
    (PowerSeries.exp ℚ).subst (PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ •
        ((∑ᶠ x : {x // (⇑(catMapDiffeomorph p))^[n] x = x},
          (SignType.sign (LinearMap.det (LinearMap.id - fixedPointDerivative
            (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (⇑(catMapDiffeomorph p))^[n] x)) : ℤ) : ℤ) :
          ℚ)) =
      PowerSeries.mk fun n ↦ if n = 0 then 1 else -(n : ℚ) := by
  rw [← subst_exp_two_sub_trace_catMap_pow]
  congr 2
  funext n
  rw [finsum_sign_det_id_sub_fixedPointDerivative_iterate_catMapDiffeomorph p n]
  push_cast
  -- The two sides differ only in how the numeral `2 : ℚ` is elaborated.
  rfl

end TauCeti
