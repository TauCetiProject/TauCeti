/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.Projection.Unitary
public import TauCeti.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Nearby projections, projection homotopies, and unitary conjugacy in `U₀(A)`

In a unital C⋆-algebra `A`, two star projections `p` and `q` at operator-norm distance
`‖p - q‖ < 1` are conjugate by a unitary `u ∈ U₀(A)` satisfying `‖u - 1‖ ≤ √2 * ‖p - q‖`. This is
constructed explicitly via the Kato–Sz.-Nagy intertwiner `z = q * p + (1 - q) * (1 - p)`, for which
`star z * z = z * star z = 1 - (p - q) ^ 2` is strictly positive, by setting
`u = z * (1 - (p - q) ^ 2) ^ (-1 / 2)`.

Partitioning a norm-continuous path of projections on the compact interval `[0, 1]` and conversely
conjugating a base projection along a path in `unitary A` yields the characterization of projection
homotopy in a unital C⋆-algebra: two star projections can be joined by a continuous path of star
projections if and only if they are conjugate by a unitary in the identity path component of
`unitary A`. In particular, conjugating any star projection by a self-adjoint unitary produces a
norm-continuous path of star projections.

## Main results

* `IsStarProjection.exp_smul`: `exp (z • p) = 1 + (exp z - 1) • p` for a star projection `p` and
  `z : ℂ`.
* `IsStarProjection.expUnitary_pi_smul`: `expUnitary (π • p) = 1 - (2 : ℝ) • p`.
* `IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one`: if `‖p - q‖ < 1`, there exists
  `u : unitary A` with `u * p * star u = q` and `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`.
* `IsStarProjection.exists_joined_one_unitary_conj_of_norm_sub_lt_one`: the unitary `u` above lies
  in the path component of `1 : unitary A`.
* `IsStarProjection.exists_path_iff_exists_joined_one_unitary_conj`: `p` and `q` are joined by a
  continuous path of star projections if and only if `q = u * p * star u` for some `u : unitary A`
  with `Joined 1 u`.
* `IsStarProjection.exists_path_of_isSelfAdjoint_unitary`: if `u : unitary A` is self-adjoint, then
  `p` and `u * p * star u` are joined by a continuous path of star projections.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter I, §4.6.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), Proposition 4.6.6.
* M. Rørdam, F. Larsen, N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, LMS Student
  Texts 49, Cambridge University Press (2000), Propositions 2.2.4, 2.2.6, and 2.2.7.
-/

public section

open scoped Real unitInterval

namespace IsStarProjection

section Exponential

variable {A : Type*} [CStarAlgebra A]

/-- The Banach-algebra exponential of a complex multiple of a star projection `p` is
`1 + (exp z - 1) • p`. -/
theorem exp_smul {p : A} (hp : IsStarProjection p) (z : ℂ) :
    NormedSpace.exp (z • p) = 1 + (Complex.exp z - 1) • p := by
  obtain ⟨hspec, hnorm⟩ := isStarProjection_iff_spectrum_subset_and_isStarNormal.mp hp
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← cfc_comp_smul z _ p]
  have hcongr : Set.EqOn (fun w : ℂ ↦ NormedSpace.exp (z • w))
      (fun w : ℂ ↦ 1 + (Complex.exp z - 1) * w) (spectrum ℂ p) := by
    intro w hw
    rcases hspec hw with rfl | rfl <;> simp [← Complex.exp_eq_exp_ℂ]
  rw [cfc_congr hcongr, cfc_const_add .., cfc_const_mul_id .., map_one]

/-- Evaluating `selfAdjoint.expUnitary` at `π • p` for a star projection `p` produces the
self-adjoint unitary reflection `1 - (2 : ℝ) • p`. -/
theorem expUnitary_pi_smul {p : A} (hp : IsStarProjection p) :
    (selfAdjoint.expUnitary ⟨π • p, (IsSelfAdjoint.all π).smul hp.isSelfAdjoint⟩ : A) =
      1 - (2 : ℝ) • p := by
  rw [selfAdjoint.expUnitary_coe]
  dsimp only
  rw [← Complex.coe_smul, smul_smul, mul_comm, hp.exp_smul, Complex.exp_pi_mul_I]
  have htwo : (-1 - 1 : ℂ) = -((2 : ℝ) : ℂ) := by norm_num
  rw [htwo, neg_smul, Complex.coe_smul, ← sub_eq_add_neg]

end Exponential

section KatoUnitary

variable {A : Type*} [CStarAlgebra A]

/-- Purely algebraic ring-and-star identities for the Kato intertwiner
`z = q * p + (1 - q) * (1 - p)` and `a = 1 - (p - q) ^ 2`. -/
private theorem kato_identities {p q : A} (z a : A)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hz : z = q * p + (1 - q) * (1 - p)) (ha : a = 1 - (p - q) ^ 2) :
    star z * z = a ∧ z * star z = a ∧ z * p = q * z ∧ Commute a p ∧ z + star z = a + a := by
  subst hz ha
  have hpp (x : A) : x * p * p = x * p := by rw [mul_assoc, hp.isIdempotentElem.eq]
  have hqq (x : A) : x * q * q = x * q := by rw [mul_assoc, hq.isIdempotentElem.eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [star_add, star_mul, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, sq,
      ← mul_assoc, hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, hqq]
    abel
  · simp only [star_add, star_mul, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, sq,
      ← mul_assoc, hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, hpp]
    abel
  · simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, ← mul_assoc,
      hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, hpp]
    abel
  · rw [commute_iff_eq]
    simp only [sub_mul, mul_sub, one_mul, mul_one, sq, ← mul_assoc,
      hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, hpp]
    abel
  · simp only [star_add, star_mul, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq, sub_mul, mul_sub, one_mul, mul_one, sq,
      hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]
    abel

/-- Spectrum bounds for the Kato operator `a = 1 - (p - q) ^ 2` of two projections at distance
strictly less than `1`: every spectral value `t ∈ spectrum ℝ a` satisfies
`1 - ‖p - q‖ ^ 2 ≤ t` (in particular `0 < t`) and `t ≤ 1`. -/
private theorem kato_spectrum_bounds {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) {t : ℝ} (ht : t ∈ spectrum ℝ (1 - (p - q) ^ 2)) :
    1 - ‖p - q‖ ^ 2 ≤ t ∧ t ≤ 1 ∧ 0 < t := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · exact False.elim (ht (isUnit_of_subsingleton _))
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  set a : A := 1 - (p - q) ^ 2
  have hpq_sa : IsSelfAdjoint (p - q) := hp.isSelfAdjoint.sub hq.isSelfAdjoint
  have ha_sa : IsSelfAdjoint a := IsSelfAdjoint.one A |>.sub (hpq_sa.pow 2)
  have h1a : 1 - a = star (p - q) * (p - q) := by simp [a, sq, hpq_sa.star_eq]
  have hcfc : 1 - a = cfc (fun x : ℝ ↦ 1 - x) a := by
    nth_rw 1 [← cfc_const_one ℝ a]
    nth_rw 2 [← cfc_id' ℝ a]
    rw [← cfc_sub ..]
  have hmem : 1 - t ∈ spectrum ℝ (1 - a) := by
    rw [hcfc, cfc_map_spectrum (fun x : ℝ ↦ 1 - x) a]
    exact ⟨t, ht, rfl⟩
  have hnonneg : 0 ≤ 1 - t :=
    spectrum_nonneg_of_nonneg (h1a ▸ star_mul_self_nonneg (p - q)) hmem
  have hle : 1 - t ≤ ‖p - q‖ ^ 2 := by
    calc 1 - t ≤ ‖1 - t‖ := Real.le_norm_self _
      _ ≤ ‖1 - a‖ := spectrum.norm_le_norm_of_mem hmem
      _ = ‖(p - q) ^ 2‖ := by simp [a]
      _ ≤ ‖p - q‖ ^ 2 := norm_pow_le (p - q) 2
  have hsq_lt : ‖p - q‖ ^ 2 < 1 := sq_lt_one_iff₀ (norm_nonneg _) |>.mpr h
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Quantitative norm bound `‖u - 1‖ ≤ √2 * ‖p - q‖` for the Kato unitary `u = z * b` once
`u + star u = 2 • cfc Real.sqrt a` is established. -/
private theorem kato_norm_bound {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) (u : unitary A)
    (hsum : (u : A) + star (u : A) = cfc Real.sqrt (1 - (p - q) ^ 2) +
      cfc Real.sqrt (1 - (p - q) ^ 2)) :
    ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  set a : A := 1 - (p - q) ^ 2
  have hpq_sa : IsSelfAdjoint (p - q) := hp.isSelfAdjoint.sub hq.isSelfAdjoint
  have ha_sa : IsSelfAdjoint a := IsSelfAdjoint.one A |>.sub (hpq_sa.pow 2)
  have hnorm_sq : star ((u : A) - 1) * ((u : A) - 1) = cfc (fun t : ℝ ↦ 2 * (1 - √t)) a := by
    have h1s : (1 : A) - cfc Real.sqrt a = cfc (fun t : ℝ ↦ 1 - √t) a := by
      rw [← cfc_const_one ℝ a, ← cfc_sub ..]
    calc star ((u : A) - 1) * ((u : A) - 1)
        = (1 - cfc Real.sqrt a) + (1 - cfc Real.sqrt a) := by
            have hadd : star ((u : A) - 1) * ((u : A) - 1) =
                (1 : A) + 1 - ((u : A) + star (u : A)) := by
              simp only [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one,
                Unitary.coe_star_mul_self]
              abel
            rw [hadd, hsum]
            abel
      _ = (2 : ℝ) • cfc (fun t : ℝ ↦ 1 - √t) a := by rw [h1s, two_smul]
      _ = cfc (fun t : ℝ ↦ 2 * (1 - √t)) a := by rw [← cfc_const_mul ..]
  have hsq_le : ‖(u : A) - 1‖ ^ 2 ≤ 2 * ‖p - q‖ ^ 2 := by
    rw [sq, ← CStarRing.norm_star_mul_self, hnorm_sq]
    refine norm_cfc_le (by positivity) fun t ht ↦ ?_
    obtain ⟨ht_low, ht_one, ht_pos⟩ := kato_spectrum_bounds hp hq h ht
    have h1_nonneg : 0 ≤ 1 - √t := sub_nonneg.mpr (Real.sqrt_le_one.mpr ht_one)
    have h1_le : 1 - √t ≤ ‖p - q‖ ^ 2 :=
      calc 1 - √t ≤ (1 - √t) * (1 + √t) :=
              le_mul_of_one_le_right h1_nonneg (by linarith [Real.sqrt_nonneg t])
        _ = 1 - t := by nlinarith [Real.mul_self_sqrt ht_pos.le]
        _ ≤ ‖p - q‖ ^ 2 := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  calc ‖(u : A) - 1‖ = √(‖(u : A) - 1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(2 * ‖p - q‖ ^ 2) := Real.sqrt_le_sqrt hsq_le
    _ = √2 * ‖p - q‖ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- Functional-calculus identities `a * (b * b) = 1` and `a * b = cfc Real.sqrt a` for
`b = cfc (fun t : ℝ ↦ (√t)⁻¹) a` where `a = 1 - (p - q) ^ 2`. -/
private theorem kato_inv_sqrt_identities {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    (1 - (p - q) ^ 2) *
        (cfc (fun t : ℝ ↦ (√t)⁻¹) (1 - (p - q) ^ 2) *
          cfc (fun t : ℝ ↦ (√t)⁻¹) (1 - (p - q) ^ 2)) = 1 ∧
      (1 - (p - q) ^ 2) * cfc (fun t : ℝ ↦ (√t)⁻¹) (1 - (p - q) ^ 2) =
        cfc Real.sqrt (1 - (p - q) ^ 2) := by
  set a : A := 1 - (p - q) ^ 2
  have hpq_sa : IsSelfAdjoint (p - q) := hp.isSelfAdjoint.sub hq.isSelfAdjoint
  have ha_sa : IsSelfAdjoint a := IsSelfAdjoint.one A |>.sub (hpq_sa.pow 2)
  have hcont : ContinuousOn (fun t : ℝ ↦ (√t)⁻¹) (spectrum ℝ a) :=
    Real.continuous_sqrt.continuousOn.inv₀ fun t ht ↦
      (Real.sqrt_pos.mpr (kato_spectrum_bounds hp hq h ht).2.2).ne'
  have hcont2 : ContinuousOn (fun t : ℝ ↦ (√t)⁻¹ * (√t)⁻¹) (spectrum ℝ a) := hcont.mul hcont
  refine ⟨?_, ?_⟩
  · rw [← cfc_mul _ _ a hcont hcont]
    nth_rw 1 [← cfc_id' ℝ a]
    rw [← cfc_mul _ _ a (continuousOn_id' _) hcont2, ← cfc_const_one ℝ a]
    refine cfc_congr fun t ht ↦ ?_
    have ht_pos : 0 < t := (kato_spectrum_bounds hp hq h ht).2.2
    rw [← mul_inv, Real.mul_self_sqrt ht_pos.le, mul_inv_cancel₀ ht_pos.ne']
  · nth_rw 1 [← cfc_id' ℝ a]
    rw [← cfc_mul _ _ a (continuousOn_id' _) hcont]
    refine cfc_congr fun t ht ↦ ?_
    have ht_pos : 0 < t := (kato_spectrum_bounds hp hq h ht).2.2
    nth_rw 1 [← Real.mul_self_sqrt ht_pos.le]
    rw [mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr ht_pos).ne', mul_one]

/-- **Kato–Sz.-Nagy unitary equivalence of nearby projections.** If `p` and `q` are star projections
in a unital C⋆-algebra `A` with `‖p - q‖ < 1`, there exists `u : unitary A` conjugating `p` to `q`
and satisfying the quantitative estimate `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_unitary_conj_of_norm_sub_lt_one {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ∃ u : unitary A, (u : A) * p * star (u : A) = q ∧ ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  let z : A := q * p + (1 - q) * (1 - p)
  let a : A := 1 - (p - q) ^ 2
  obtain ⟨hz_star_mul, hmul_z_star, hzp, hap, hz_add⟩ := kato_identities z a hp hq rfl rfl
  obtain ⟨hab2, hab_sqrt⟩ := kato_inv_sqrt_identities hp hq h
  have haz : Commute a z := by
    rw [commute_iff_eq]
    calc a * z = z * star z * z := by rw [hmul_z_star]
      _ = z * a := by rw [mul_assoc, hz_star_mul]
  let b : A := cfc (fun t : ℝ ↦ (√t)⁻¹) a
  have hb_sa : IsSelfAdjoint b := cfc_predicate _ _
  have hba : Commute b a := (Commute.refl a).cfc_real _
  have hbz : Commute b z := haz.cfc_real _
  have hbp : Commute b p := hap.cfc_real _
  have hu_left : star (z * b) * (z * b) = 1 :=
    calc star (z * b) * (z * b)
        = b * (star z * z) * b := by simp only [star_mul, hb_sa.star_eq, mul_assoc]
      _ = b * a * b := by rw [hz_star_mul]
      _ = a * (b * b) := by rw [hba.eq, mul_assoc]
      _ = 1 := hab2
  have hu_right : z * b * star (z * b) = 1 := by
    simp only [star_mul, hb_sa.star_eq, mul_assoc]
    rw [← mul_assoc b, ← mul_assoc z, (hbz.mul_left hbz).symm.eq, mul_assoc, hmul_z_star,
      (hba.mul_left hba).eq, hab2]
  let u : unitary A := ⟨z * b, Unitary.mem_iff.mpr ⟨hu_left, hu_right⟩⟩
  refine ⟨u, ?_, kato_norm_bound hp hq h u ?_⟩
  · dsimp only [u]
    rw [mul_assoc z b p, hbp.eq, ← mul_assoc z p b, hzp, mul_assoc q z b, mul_assoc, hu_right,
      mul_one]
  · have hbz_star : star z * b = b * star z := by
      simpa only [star_mul, hb_sa.star_eq] using congrArg star hbz.eq
    dsimp only [u]
    rw [star_mul, hb_sa.star_eq, ← hbz_star, ← add_mul, hz_add, add_mul, hab_sqrt]

/-- If two star projections `p` and `q` satisfy `‖p - q‖ < 1`, they are conjugate by a unitary `u`
in the identity path component of `unitary A` with `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_joined_one_unitary_conj_of_norm_sub_lt_one {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = q ∧
      ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  obtain ⟨u, hconj, hnorm⟩ := exists_unitary_conj_of_norm_sub_lt_one hp hq h
  have hlt2 : ‖(u - 1 : A)‖ < 2 := by
    have hsqrt2 : √2 < 2 := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
    calc ‖(u - 1 : A)‖ ≤ √2 * ‖p - q‖ := hnorm
      _ ≤ √2 * 1 := by gcongr
      _ < 2 := by linarith
  exact ⟨u, Unitary.joined 1 u hlt2, hconj, hnorm⟩

end KatoUnitary

section PathEquivalence

variable {A : Type*} [CStarAlgebra A]

/-- Any norm-continuous path of star projections from `p` to `q` in a unital C⋆-algebra is
implemented by conjugation by a unitary in the path component of `1 : unitary A`. -/
theorem exists_joined_one_unitary_conj_of_path {p q : A} (γ : Path p q)
    (hγ : ∀ t, IsStarProjection (γ t)) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = q := by
  have hunif : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  obtain ⟨δ, hδ, hstep⟩ := Metric.uniformContinuous_iff.mp hunif 1 zero_lt_one
  obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
  have hN1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmesh : 1 / ((N : ℝ) + 1) < δ := by
    rw [one_div]
    exact inv_lt_of_inv_lt₀ hδ (by linarith)
  let pt (k : ℕ) (hk : k ≤ N + 1) : I :=
    ⟨(k : ℝ) / ((N : ℝ) + 1), div_nonneg (Nat.cast_nonneg k) hN1_pos.le,
      (div_le_one hN1_pos).mpr (by exact_mod_cast hk)⟩
  have hchain : ∀ k (hk : k ≤ N + 1),
      ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = γ (pt k hk) := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨1, Joined.refl 1, ?_⟩
      have hpt0 : pt 0 hk = 0 := Subtype.ext (by simp [pt])
      simp [hpt0]
    | succ k ih =>
      intro hk
      have hk' : k ≤ N + 1 := Nat.le_of_succ_le hk
      obtain ⟨u, hu_join, hu_conj⟩ := ih hk'
      have hdist_pt : dist (pt k hk') (pt (k + 1) hk) < δ := by
        rw [Subtype.dist_eq, Real.dist_eq]
        have hsub : (k : ℝ) / ((N : ℝ) + 1) - ((k + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) =
            -(1 / ((N : ℝ) + 1)) := by
          push_cast; ring
        rw [hsub, abs_neg, abs_of_pos (by positivity)]
        exact hmesh
      have hnorm : ‖γ (pt k hk') - γ (pt (k + 1) hk)‖ < 1 := by
        rw [← dist_eq_norm]
        exact hstep hdist_pt
      obtain ⟨v, hv_join, hv_conj, -⟩ :=
        exists_joined_one_unitary_conj_of_norm_sub_lt_one (hγ (pt k hk')) (hγ (pt (k + 1) hk)) hnorm
      refine ⟨v * u, by simpa using hv_join.mul hu_join, ?_⟩
      simp only [Submonoid.coe_mul, star_mul, mul_assoc]
      rw [← mul_assoc (u : A), ← mul_assoc ((u : A) * p), hu_conj, ← mul_assoc, hv_conj]
  obtain ⟨u, hu_join, hu_conj⟩ := hchain (N + 1) le_rfl
  have hpt1 : pt (N + 1) le_rfl = 1 := Subtype.ext (by simp [pt, div_self hN1_pos.ne'])
  rw [hpt1, γ.target] at hu_conj
  exact ⟨u, hu_join, hu_conj⟩

/-- Conjugating a star projection `p` along a path from `1` to `u` in `unitary A` gives a
norm-continuous path of star projections from `p` to `u * p * star u`. -/
theorem exists_path_of_joined_one_unitary {p : A} (hp : IsStarProjection p)
    {u : unitary A} (hu : Joined (1 : unitary A) u) :
    ∃ γ : Path p ((u : A) * p * star (u : A)), ∀ t, IsStarProjection (γ t) := by
  obtain ⟨δ⟩ := hu
  refine ⟨{
    toFun := fun t ↦ (δ t : A) * p * star (δ t : A)
    continuous_toFun := by fun_prop
    source' := by simp
    target' := by simp
  }, fun t ↦ hp.star_right_conjugate (δ t)⟩

/-- Two star projections `p` and `q` in a unital C⋆-algebra are joined by a continuous path of star
projections if and only if they are conjugate by a unitary in the identity path component of
`unitary A`. -/
theorem exists_path_iff_exists_joined_one_unitary_conj {p q : A}
    (hp : IsStarProjection p) :
    (∃ γ : Path p q, ∀ t, IsStarProjection (γ t)) ↔
      ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = q := by
  refine ⟨fun ⟨γ, hγ⟩ ↦ exists_joined_one_unitary_conj_of_path γ hγ, ?_⟩
  rintro ⟨u, hu, rfl⟩
  exact exists_path_of_joined_one_unitary hp hu

/-- Conjugating a star projection `p` by a self-adjoint unitary `u` connects `p` to
`u * p * star u` by a norm-continuous path of star projections. -/
theorem exists_path_of_isSelfAdjoint_unitary {p : A} (hp : IsStarProjection p)
    (u : unitary A) (hu : IsSelfAdjoint (u : A)) :
    ∃ γ : Path p ((u : A) * p * star (u : A)), ∀ t, IsStarProjection (γ t) :=
  hp.exists_path_of_joined_one_unitary (Unitary.joined_one_of_isSelfAdjoint u hu)

end PathEquivalence

end IsStarProjection
