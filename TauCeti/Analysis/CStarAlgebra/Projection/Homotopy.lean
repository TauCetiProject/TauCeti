/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import TauCeti.Algebra.Star.Projection.Unitary
public import TauCeti.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# Nearby projections, projection homotopies, and unitary conjugacy in `U₀(A)`

In a unital C⋆-algebra `A`, two star projections `p` and `q` at operator-norm distance
`‖p - q‖ < 1` are conjugate by an explicit unitary `u ∈ U₀(A)` satisfying
`‖u - 1‖ ≤ √2 * ‖p - q‖`. This unitary (`IsStarProjection.conjUnitaryOfNormSubLtOne`) is constructed
from the Kato–Sz.-Nagy intertwiner `z = q * p + (1 - q) * (1 - p)`, for which
`star z * z = z * star z = 1 - (p - q) ^ 2` is strictly positive, by setting
`u = z * (1 - (p - q) ^ 2) ^ (-1 / 2)`.

Chaining local unitary conjugations across the preconnected interval `[0, 1]` and conversely
conjugating a base projection along a path in `unitary A` (`Unitary.conjPath`) yields the
characterization of projection homotopy in a unital C⋆-algebra: two star projections can be joined
by a continuous path of star projections if and only if they are conjugate by a unitary in the
identity path component of `unitary A`.

## Main declarations

* `IsStarProjection.conjUnitaryOfNormSubLtOne`: the explicit Kato–Sz.-Nagy unitary conjugating `p`
  to `q` when `‖p - q‖ < 1`, satisfying `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖` and `Joined 1 u`.
* `IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one`,
  `IsStarProjection.exists_joined_one_unitary_conj_of_norm_sub_lt_one`: existential forms of
  Kato–Sz.-Nagy unitary conjugacy in `U₀(A)`.
* `IsStarProjection.exists_path_iff_exists_joined_one_unitary_conj`: `p` and `q` are joined by a
  continuous path of star projections if and only if `q = u * p * star u` for some `u : unitary A`
  with `Joined 1 u`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter I, §4.6.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), Chapter III, Proposition 4.6.6.
* M. Rørdam, F. Larsen, N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, LMS Student
  Texts 49, Cambridge University Press (2000), Propositions 2.2.4, 2.2.6, and 2.2.7.
-/

public section

open Filter Topology
open scoped Real unitInterval

namespace IsStarProjection

section TopologicalStarMonoid

variable {A : Type*} [Monoid A] [StarMul A] [TopologicalSpace A] [ContinuousMul A]
  [ContinuousStar A]

/-- Conjugating a star projection `p` along `δ : Path (1 : unitary A) u` produces a star projection
at every time `t`. -/
theorem conjPath {p : A} (hp : IsStarProjection p) {u : unitary A} (δ : Path (1 : unitary A) u)
    (t : I) : IsStarProjection (Unitary.conjPath δ p t) := by
  rw [Unitary.conjPath_apply]
  exact hp.star_right_conjugate (δ t)

/-- If `u : unitary A` lies in the path component of `1`, then a star projection `p` and
`(u : A) * p * star (u : A)` are joined by a continuous path of star projections. -/
theorem exists_path_of_joined_one_unitary {p : A} (hp : IsStarProjection p)
    {u : unitary A} (hu : Joined (1 : unitary A) u) :
    ∃ γ : Path p ((u : A) * p * star (u : A)), ∀ t, IsStarProjection (γ t) :=
  let ⟨δ⟩ := hu; ⟨Unitary.conjPath δ p, hp.conjPath δ⟩

end TopologicalStarMonoid

section KatoUnitary

variable {A : Type*} [CStarAlgebra A] {p q : A}

private theorem kato_identities (z a : A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hz : z = q * p + (1 - q) * (1 - p)) (ha : a = 1 - (p - q) ^ 2) :
    star z * z = a ∧ z * star z = a ∧ z * p = q * z ∧ Commute a p ∧ z + star z = a + a := by
  subst hz ha
  have hpp (x : A) : x * p * p = x * p := by rw [mul_assoc, hp.isIdempotentElem.eq]
  have hqq (x : A) : x * q * q = x * q := by rw [mul_assoc, hq.isIdempotentElem.eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [star_add, star_mul, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, sq,
      ← mul_assoc, hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, hqq]; abel
  · simp only [star_add, star_mul, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, sq,
      ← mul_assoc, hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, hpp]; abel
  · simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, ← mul_assoc,
      hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, hpp]; abel
  · rw [commute_iff_eq]
    simp only [sub_mul, mul_sub, one_mul, mul_one, sq, ← mul_assoc,
      hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, hpp]; abel
  · simp only [star_add, star_mul, star_sub, star_one, hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq, sub_mul, mul_sub, one_mul, mul_one, sq,
      hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]; abel

private theorem kato_spectrum_bounds (hp : IsStarProjection p) (hq : IsStarProjection q)
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
    nth_rw 1 [← cfc_const_one ℝ a]; nth_rw 2 [← cfc_id' ℝ a]; rw [← cfc_sub ..]
  have hmem : 1 - t ∈ spectrum ℝ (1 - a) := by
    rw [hcfc, cfc_map_spectrum (fun x : ℝ ↦ 1 - x) a]; exact ⟨t, ht, rfl⟩
  have hnonneg : 0 ≤ 1 - t :=
    spectrum_nonneg_of_nonneg (h1a ▸ star_mul_self_nonneg (p - q)) hmem
  have hle : 1 - t ≤ ‖p - q‖ ^ 2 := by
    calc 1 - t ≤ ‖1 - t‖ := Real.le_norm_self _
      _ ≤ ‖1 - a‖ := spectrum.norm_le_norm_of_mem hmem
      _ = ‖(p - q) ^ 2‖ := by simp [a]
      _ ≤ ‖p - q‖ ^ 2 := norm_pow_le (p - q) 2
  have hsq_lt : ‖p - q‖ ^ 2 < 1 := sq_lt_one_iff₀ (norm_nonneg _) |>.mpr h
  exact ⟨by linarith, by linarith, by linarith⟩

private theorem kato_norm_bound (hp : IsStarProjection p) (hq : IsStarProjection q)
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
                Unitary.coe_star_mul_self]; abel
            rw [hadd, hsum]; abel
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
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; linarith
  calc ‖(u : A) - 1‖ = √(‖(u : A) - 1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(2 * ‖p - q‖ ^ 2) := Real.sqrt_le_sqrt hsq_le
    _ = √2 * ‖p - q‖ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

private theorem kato_inv_sqrt_identities (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
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
  · rw [← cfc_mul _ _ a hcont hcont]; nth_rw 1 [← cfc_id' ℝ a]
    rw [← cfc_mul _ _ a (continuousOn_id' _) hcont2, ← cfc_const_one ℝ a]
    refine cfc_congr fun t ht ↦ ?_
    have ht_pos : 0 < t := (kato_spectrum_bounds hp hq h ht).2.2
    rw [← mul_inv, Real.mul_self_sqrt ht_pos.le, mul_inv_cancel₀ ht_pos.ne']
  · nth_rw 1 [← cfc_id' ℝ a]; rw [← cfc_mul _ _ a (continuousOn_id' _) hcont]
    refine cfc_congr fun t ht ↦ ?_
    have ht_pos : 0 < t := (kato_spectrum_bounds hp hq h ht).2.2
    nth_rw 1 [← Real.mul_self_sqrt ht_pos.le]
    rw [mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr ht_pos).ne', mul_one]

private theorem kato_mem_unitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    (q * p + (1 - q) * (1 - p)) * cfc (fun t : ℝ ↦ (√t)⁻¹) (1 - (p - q) ^ 2) ∈ unitary A := by
  set z : A := q * p + (1 - q) * (1 - p) with hz
  set a : A := 1 - (p - q) ^ 2 with ha
  obtain ⟨hz_star_mul, hmul_z_star, -, -, -⟩ := kato_identities z a hp hq hz ha
  obtain ⟨hab2, -⟩ := kato_inv_sqrt_identities hp hq h
  rw [← ha] at hab2
  have haz : Commute a z := by
    rw [commute_iff_eq]
    calc a * z = z * star z * z := by rw [hmul_z_star]
      _ = z * a := by rw [mul_assoc, hz_star_mul]
  set b : A := cfc (fun t : ℝ ↦ (√t)⁻¹) a
  have hb_sa : IsSelfAdjoint b := cfc_predicate _ _
  have hba : Commute b a := (Commute.refl a).cfc_real _
  have hbz : Commute b z := haz.cfc_real _
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  · calc star (z * b) * (z * b) = b * (star z * z) * b := by
          simp only [star_mul, hb_sa.star_eq, mul_assoc]
      _ = a * (b * b) := by rw [hz_star_mul, hba.eq, mul_assoc]
      _ = 1 := hab2
  · simp only [star_mul, hb_sa.star_eq, mul_assoc]
    rw [← mul_assoc b, ← mul_assoc z, (hbz.mul_left hbz).symm.eq, mul_assoc, hmul_z_star,
      (hba.mul_left hba).eq, hab2]

/-- **Kato–Sz.-Nagy perturbation unitary.** For star projections `p` and `q` in a unital
C⋆-algebra `A` with `‖p - q‖ < 1`, this is the unitary
`(q * p + (1 - q) * (1 - p)) * (1 - (p - q) ^ 2) ^ (-1 / 2)` conjugating `p` to `q` at distance at
most `√2 * ‖p - q‖` from `1`. -/
noncomputable def conjUnitaryOfNormSubLtOne (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : unitary A :=
  ⟨(q * p + (1 - q) * (1 - p)) * cfc (fun t : ℝ ↦ (√t)⁻¹) (1 - (p - q) ^ 2),
    kato_mem_unitary hp hq h⟩

@[simp] theorem coe_conjUnitaryOfNormSubLtOne (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    (hp.conjUnitaryOfNormSubLtOne hq h : A) =
      (q * p + (1 - q) * (1 - p)) * cfc (fun t : ℝ ↦ (√t)⁻¹) (1 - (p - q) ^ 2) := (rfl)

/-- The Kato–Sz.-Nagy unitary `hp.conjUnitaryOfNormSubLtOne hq h` conjugates `p` to `q`. -/
theorem conjUnitaryOfNormSubLtOne_mul_mul_star (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    (hp.conjUnitaryOfNormSubLtOne hq h : A) * p * star (hp.conjUnitaryOfNormSubLtOne hq h : A) =
      q := by
  set z : A := q * p + (1 - q) * (1 - p) with hz
  set a : A := 1 - (p - q) ^ 2 with ha
  obtain ⟨-, -, hzp, hap, -⟩ := kato_identities z a hp hq hz ha
  set b : A := cfc (fun t : ℝ ↦ (√t)⁻¹) a with hb
  have hbp : Commute b p := hap.cfc_real _
  have hu_right : (hp.conjUnitaryOfNormSubLtOne hq h : A) *
      star (hp.conjUnitaryOfNormSubLtOne hq h : A) = 1 := Unitary.coe_mul_star_self _
  rw [coe_conjUnitaryOfNormSubLtOne, ← hz, ← ha, ← hb] at hu_right ⊢
  rw [mul_assoc z b p, hbp.eq, ← mul_assoc z p b, hzp, mul_assoc q z b, mul_assoc, hu_right,
    mul_one]

/-- The Kato–Sz.-Nagy unitary `hp.conjUnitaryOfNormSubLtOne hq h` satisfies the quantitative bound
`‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem norm_conjUnitaryOfNormSubLtOne_sub_one_le (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ‖(hp.conjUnitaryOfNormSubLtOne hq h : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  refine kato_norm_bound hp hq h (hp.conjUnitaryOfNormSubLtOne hq h) ?_
  set z : A := q * p + (1 - q) * (1 - p) with hz
  set a : A := 1 - (p - q) ^ 2 with ha
  obtain ⟨hz_star_mul, hmul_z_star, -, -, hz_add⟩ := kato_identities z a hp hq hz ha
  obtain ⟨-, hab_sqrt⟩ := kato_inv_sqrt_identities hp hq h
  have haz : Commute a z := by
    rw [commute_iff_eq]
    calc a * z = z * star z * z := by rw [hmul_z_star]
      _ = z * a := by rw [mul_assoc, hz_star_mul]
  set b : A := cfc (fun t : ℝ ↦ (√t)⁻¹) a with hb
  have hb_sa : IsSelfAdjoint b := cfc_predicate _ _
  have hbz : Commute b z := haz.cfc_real _
  have hbz_star : star z * b = b * star z := by
    simpa only [star_mul, hb_sa.star_eq] using congrArg star hbz.eq
  rw [coe_conjUnitaryOfNormSubLtOne, ← hz, ← ha, ← hb, star_mul, hb_sa.star_eq, ← hbz_star,
    ← add_mul, hz_add, add_mul, hab_sqrt]

/-- The Kato–Sz.-Nagy unitary `hp.conjUnitaryOfNormSubLtOne hq h` lies in the identity path
component of `unitary A`. -/
@[simp] theorem joined_one_conjUnitaryOfNormSubLtOne (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    Joined (1 : unitary A) (hp.conjUnitaryOfNormSubLtOne hq h) := by
  refine Unitary.joined 1 _ ?_
  have hsqrt2 : √2 < 2 := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  calc ‖(hp.conjUnitaryOfNormSubLtOne hq h - 1 : A)‖
      ≤ √2 * ‖p - q‖ := hp.norm_conjUnitaryOfNormSubLtOne_sub_one_le hq h
    _ ≤ √2 * 1 := by gcongr
    _ < 2 := by linarith

/-- **Kato–Sz.-Nagy unitary equivalence of nearby projections.** If `p` and `q` are star projections
in a unital C⋆-algebra `A` with `‖p - q‖ < 1`, there exists `u : unitary A` conjugating `p` to `q`
and satisfying the quantitative estimate `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_unitary_conj_of_norm_sub_lt_one (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    ∃ u : unitary A, (u : A) * p * star (u : A) = q ∧ ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ :=
  ⟨hp.conjUnitaryOfNormSubLtOne hq h, hp.conjUnitaryOfNormSubLtOne_mul_mul_star hq h,
    hp.norm_conjUnitaryOfNormSubLtOne_sub_one_le hq h⟩

/-- If two star projections `p` and `q` satisfy `‖p - q‖ < 1`, they are conjugate by a unitary `u`
in the identity path component of `unitary A` with `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_joined_one_unitary_conj_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = q ∧
      ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ :=
  ⟨hp.conjUnitaryOfNormSubLtOne hq h, hp.joined_one_conjUnitaryOfNormSubLtOne hq h,
    hp.conjUnitaryOfNormSubLtOne_mul_mul_star hq h,
    hp.norm_conjUnitaryOfNormSubLtOne_sub_one_le hq h⟩

end KatoUnitary

section PathEquivalence

variable {A : Type*} [CStarAlgebra A]

/-- Any norm-continuous path of star projections from `p` to `q` in a unital C⋆-algebra is
implemented by conjugation by a unitary in the path component of `1 : unitary A`. -/
theorem exists_joined_one_unitary_conj_of_path {p q : A} (γ : Path p q)
    (hγ : ∀ t, IsStarProjection (γ t)) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = q := by
  suffices ∀ s t : I, ∃ u : unitary A, Joined 1 u ∧ (u : A) * γ s * star (u : A) = γ t by
    simpa only [γ.source, γ.target] using this 0 1
  refine PreconnectedSpace.induction₂' _ (fun s ↦ ?_) ⟨fun r s t ⟨u, hu, h₁⟩ ⟨v, hv, h₂⟩ ↦ ?_⟩
  · filter_upwards [γ.continuous.continuousAt (Metric.ball_mem_nhds (γ s) zero_lt_one)] with t ht
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at ht
    have ht' : ‖γ s - γ t‖ < 1 := by rwa [norm_sub_rev]
    obtain ⟨u, hu_join, hu_conj, -⟩ :=
      exists_joined_one_unitary_conj_of_norm_sub_lt_one (hγ s) (hγ t) ht'
    obtain ⟨v, hv_join, hv_conj, -⟩ :=
      exists_joined_one_unitary_conj_of_norm_sub_lt_one (hγ t) (hγ s) ht
    exact ⟨⟨u, hu_join, hu_conj⟩, ⟨v, hv_join, hv_conj⟩⟩
  · refine ⟨v * u, by simpa using hv.mul hu, ?_⟩
    simp only [Submonoid.coe_mul, star_mul, mul_assoc]
    rw [← mul_assoc (u : A), ← mul_assoc ((u : A) * γ r), h₁, ← mul_assoc, h₂]

/-- Two star projections `p` and `q` in a unital C⋆-algebra are joined by a continuous path of star
projections if and only if they are conjugate by a unitary in the identity path component of
`unitary A`. -/
theorem exists_path_iff_exists_joined_one_unitary_conj {p q : A} (hp : IsStarProjection p) :
    (∃ γ : Path p q, ∀ t, IsStarProjection (γ t)) ↔
      ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = q :=
  ⟨fun ⟨γ, hγ⟩ ↦ exists_joined_one_unitary_conj_of_path γ hγ,
    fun ⟨_, hu, hq⟩ ↦ hq ▸ exists_path_of_joined_one_unitary hp hu⟩

end PathEquivalence

end IsStarProjection
