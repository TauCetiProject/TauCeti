/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Algebra.Star.Projection.Intertwiner
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Tactic.NoncommRing

/-!
# Perturbation, unitary conjugacy, and paths of star projections

Two star projections `p` and `q` in a unital C⋆-algebra satisfying `‖p - q‖ < 1` are unitarily
conjugate by a unitary close to `1` and hence in the identity path component of the unitary group.
Explicitly, Sz.-Nagy's intertwiner `TauCeti.projectionIntertwiner p q = q * p + (1 - q) * (1 - p)`
(from `TauCeti/Algebra/Star/Projection/Intertwiner.lean`) satisfies `z * p = q * z` and
`star z * z = z * star z = 1 - (p - q) ^ 2`. When `‖p - q‖ < 1`, `z` is a unit whose polar unitary
factor `u = hp.closeUnitary hq h` (`IsStarProjection.closeUnitary_def`) satisfies
`CFC.sqrt (1 - (p - q) * (p - q)) * u = z`, conjugates `p` to `q` (`u * p * star u = q`), and obeys
`‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ < 2` together with `Joined (1 : unitary A) u`.

By connectedness of the unit interval, endpoints of a norm-continuous path of star projections in a
unital C⋆-algebra are conjugate by a unitary joined to `1`
(`Path.exists_joined_one_unitary_conj_of_isStarProjection`). Passing to `Unitization ℂ B` transfers
both the nearby-projection and path-lifting theorems to possibly non-unital C⋆-algebras `B`,
producing a partial isometry in `B` with initial projection `p` and final projection `q`.

We also record `exp (z • p) = 1 + (exp z - 1) • p` and `expUnitary (π • p) = 1 - 2 • p`.

## Main definitions and results

* `IsStarProjection.exp_smul`, `IsStarProjection.coe_expUnitary_pi_smul`: exponential formulas.
* `IsStarProjection.closeUnitary`, `IsStarProjection.closeUnitary_def`,
  `IsStarProjection.coe_closeUnitary`,
  `IsStarProjection.sqrt_one_sub_sub_mul_self_mul_closeUnitary`,
  `IsStarProjection.closeUnitary_mul_sqrt_one_sub_sub_mul_self`: the canonical polar unitary and
  its characterizing formulas.
* `IsStarProjection.closeUnitary_mul_self_mul_star`,
  `IsStarProjection.norm_closeUnitary_sub_one_le`,
  `IsStarProjection.joined_one_closeUnitary`: conjugacy, sharp norm bound, and path connectedness.
* `Path.exists_joined_one_unitary_conj_of_isStarProjection`,
  `IsStarProjection.exists_isPartialIsometry_of_norm_sub_lt_one`,
  `Path.exists_isPartialIsometry_of_isStarProjection`: path lifting and non-unital partial-isometry
  transfer.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), Proposition 4.6.6.
* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, London
  Mathematical Society Student Texts 49, Cambridge University Press (2000), Propositions 2.2.4 and
  2.2.6.
-/

public section

noncomputable section

open NormedSpace Ring TauCeti
open scoped Real unitInterval

namespace IsStarProjection

section Exponential

variable {A : Type*} [CStarAlgebra A]

/-- Exponential of a complex scalar multiple of a star projection:
`exp (z • p) = 1 + (Complex.exp z - 1) • p`. -/
theorem exp_smul {p : A} (hp : IsStarProjection p) (z : ℂ) :
    NormedSpace.exp (z • p) = 1 + (Complex.exp z - 1) • p := by
  obtain ⟨hp_spec, hp_norm⟩ := isStarProjection_iff_spectrum_subset_and_isStarNormal.mp hp
  have hzp_norm : IsStarNormal (z • p) :=
    ⟨by rw [star_smul]; exact (hp_norm.star_comm_self.smul_left (star z)).smul_right z⟩
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ) hzp_norm,
    ← cfc_comp_smul z (NormedSpace.exp : ℂ → ℂ) p]
  have hlin : cfc (fun w : ℂ ↦ 1 + (Complex.exp z - 1) * w) p = 1 + (Complex.exp z - 1) • p := by
    rw [cfc_const_add (1 : ℂ) ((Complex.exp z - 1) * ·) p, map_one,
      cfc_const_mul_id (Complex.exp z - 1) p]
  rw [← hlin]
  refine cfc_congr fun w hw ↦ ?_
  rw [← Complex.exp_eq_exp_ℂ]
  rcases hp_spec hw with hw0 | hw1 <;> simp [Set.mem_singleton_iff.mp ‹_›]

/-- For a star projection `p` and `t : ℝ`, `expUnitary (t • p)` has underlying element
`1 + (Complex.exp (Complex.I * t) - 1) • p`. -/
theorem coe_expUnitary_smul {p : A} (hp : IsStarProjection p) (t : ℝ) :
    (selfAdjoint.expUnitary (t • ⟨p, hp.isSelfAdjoint⟩) : A) =
      1 + (Complex.exp (Complex.I * t) - 1) • p := by
  rw [selfAdjoint.expUnitary_coe, selfAdjoint.val_smul, ← Complex.coe_smul t p, smul_smul,
    hp.exp_smul]

/-- At angle `π`, `expUnitary (π • p)` equals the self-adjoint reflection `1 - 2 • p`. -/
theorem coe_expUnitary_pi_smul {p : A} (hp : IsStarProjection p) :
    (selfAdjoint.expUnitary (π • ⟨p, hp.isSelfAdjoint⟩) : A) = 1 - (2 : ℝ) • p := by
  rw [hp.coe_expUnitary_smul π, mul_comm Complex.I (π : ℂ), Complex.exp_pi_mul_I]
  have hscalar : (-1 - 1 : ℂ) = -((2 : ℝ) : ℂ) := by push_cast; ring
  rw [hscalar, neg_smul, Complex.coe_smul, sub_eq_add_neg]

end Exponential

section Perturbation

variable {A : Type*} [CStarAlgebra A]

private theorem isUnit_one_sub_sub_mul_self {p q : A} (h : ‖p - q‖ < 1) :
    IsUnit (1 - (p - q) * (p - q)) := by
  have hsq : ‖(p - q) * (p - q)‖ < 1 :=
    (norm_mul_le _ _).trans_lt (by simpa using mul_lt_mul'' h h (norm_nonneg _) (norm_nonneg _))
  exact (Units.oneSub ((p - q) * (p - q)) hsq).isUnit

/-- When star projections `p` and `q` satisfy `‖p - q‖ < 1`, Sz.-Nagy's intertwiner
`projectionIntertwiner p q` is a unit in `A`. -/
theorem isUnit_projectionIntertwiner {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    IsUnit (projectionIntertwiner p q) := by
  have hc : Commute (projectionIntertwiner p q) (star (projectionIntertwiner p q)) :=
    (projectionIntertwiner_mul_star_self hp hq).trans
      (star_projectionIntertwiner_mul_self hp hq).symm
  have hz : IsUnit (projectionIntertwiner p q * star (projectionIntertwiner p q)) := by
    rw [projectionIntertwiner_mul_star_self hp hq]
    exact isUnit_one_sub_sub_mul_self h
  exact (hc.isUnit_mul_iff.mp hz).1

/-- The canonical unitary conjugating a star projection `p` to a nearby star projection `q`
(`‖p - q‖ < 1`), defined as the polar unitary factor of `projectionIntertwiner p q`. -/
def closeUnitary {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : unitary A :=
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  (hp.isUnit_projectionIntertwiner hq h).unit.polarUnitary

private theorem exists_star_mul_self_mul_closeUnitary {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ∃ y : A, (star y * y) * (star y * y) = 1 - (p - q) * (p - q) ∧
      (star y * y) * (hp.closeUnitary hq h : A) = projectionIntertwiner p q := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  set z := (hp.isUnit_projectionIntertwiner hq h).unit
  have hz_coe : (z : A) = projectionIntertwiner p q := IsUnit.unit_spec _
  obtain ⟨y, hy⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (CFC.sqrt_nonneg ((z : A) * star (z : A)))
  refine ⟨y, ?_, ?_⟩
  · rw [← hy, CFC.sqrt_mul_sqrt_self _ (mul_star_self_nonneg (z : A)), hz_coe,
      projectionIntertwiner_mul_star_self hp hq]
  · rw [← hy]; exact z.sqrt_mul_star_mul_polarUnitary.trans hz_coe

/-- Left polar-factor identity:
`CFC.sqrt (1 - (p - q) ^ 2) * closeUnitary = projectionIntertwiner`. -/
theorem sqrt_one_sub_sub_mul_self_mul_closeUnitary [PartialOrder A] [StarOrderedRing A]
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    CFC.sqrt (1 - (p - q) * (p - q)) * (hp.closeUnitary hq h : A) =
      projectionIntertwiner p q := by
  obtain ⟨y, hy_sq, hy_mul⟩ := hp.exists_star_mul_self_mul_closeUnitary hq h
  rwa [CFC.sqrt_unique hy_sq (star_mul_self_nonneg y)]

/-- Characterizing formula for `closeUnitary` as `Units.polarUnitary` of the intertwiner unit. -/
theorem closeUnitary_def [PartialOrder A] [StarOrderedRing A]
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    hp.closeUnitary hq h = (hp.isUnit_projectionIntertwiner hq h).unit.polarUnitary :=
  ((hp.isUnit_projectionIntertwiner hq h).unit.polarUnitary_eq_of_mul_eq (CFC.sqrt_nonneg _)
    ((hp.sqrt_one_sub_sub_mul_self_mul_closeUnitary hq h).trans (IsUnit.unit_spec _).symm)).symm

/-- Explicit formula for `(hp.closeUnitary hq h : A)` via `CFC.sqrt` and `projectionIntertwiner`. -/
theorem coe_closeUnitary [PartialOrder A] [StarOrderedRing A]
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    (hp.closeUnitary hq h : A) =
      (CFC.sqrt (1 - (p - q) * (p - q)))⁻¹ʳ * projectionIntertwiner p q := by
  rw [hp.closeUnitary_def hq h, Units.coe_polarUnitary, IsUnit.unit_spec,
    projectionIntertwiner_mul_star_self hp hq]

/-- Right polar-factor identity:
`closeUnitary * CFC.sqrt (1 - (p - q) ^ 2) = projectionIntertwiner`. -/
theorem closeUnitary_mul_sqrt_one_sub_sub_mul_self [PartialOrder A] [StarOrderedRing A]
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    (hp.closeUnitary hq h : A) * CFC.sqrt (1 - (p - q) * (p - q)) =
      projectionIntertwiner p q := by
  have hr := (hp.isUnit_projectionIntertwiner hq h).unit.polarUnitary_mul_sqrt_star_mul
  rwa [← hp.closeUnitary_def hq h, IsUnit.unit_spec,
    star_projectionIntertwiner_mul_self hp hq] at hr

/-- The unitary `hp.closeUnitary hq h` intertwines `p` and `q`: `u * p = q * u`. -/
theorem closeUnitary_mul_self {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    (hp.closeUnitary hq h : A) * p = q * (hp.closeUnitary hq h : A) := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  set z := (hp.isUnit_projectionIntertwiner hq h).unit
  set s := CFC.sqrt (1 - (p - q) * (p - q))
  have hs_eq : (z : A) * star (z : A) = 1 - (p - q) * (p - q) := by
    rw [IsUnit.unit_spec, projectionIntertwiner_mul_star_self hp hq]
  have hs_unit : IsUnit s := by
    dsimp only [s]; rw [← hs_eq]; exact z.isStrictlyPositive_sqrt_mul_star.isUnit
  have hs_mul_u : s * (hp.closeUnitary hq h : A) = projectionIntertwiner p q :=
    hp.sqrt_one_sub_sub_mul_self_mul_closeUnitary hq h
  have hcomm_sq : Commute s q :=
    Commute.cfcₙ_nnreal
      (commute_one_sub_sub_mul_self_right hp.isIdempotentElem hq.isIdempotentElem) NNReal.sqrt
  apply hs_unit.mul_left_cancel
  calc s * ((hp.closeUnitary hq h : A) * p)
      = (s * (hp.closeUnitary hq h : A)) * p := (mul_assoc _ _ _).symm
    _ = q * projectionIntertwiner p q := by
        rw [hs_mul_u, projectionIntertwiner_mul_eq_mul hp.isIdempotentElem hq.isIdempotentElem]
    _ = (q * s) * (hp.closeUnitary hq h : A) := by rw [← hs_mul_u, mul_assoc]
    _ = s * (q * (hp.closeUnitary hq h : A)) := by rw [← hcomm_sq.eq, mul_assoc]

/-- Conjugating `p` by `hp.closeUnitary hq h` yields `q`: `u * p * star u = q`. -/
@[simp]
theorem closeUnitary_mul_self_mul_star {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    (hp.closeUnitary hq h : A) * p * star (hp.closeUnitary hq h : A) = q := by
  rw [hp.closeUnitary_mul_self hq h, mul_assoc,
    Unitary.mul_star_self_of_mem (hp.closeUnitary hq h).property, mul_one]

/-- Sharp Sz.-Nagy norm bound: `‖(hp.closeUnitary hq h : A) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem norm_closeUnitary_sub_one_le {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ‖(hp.closeUnitary hq h : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  set u := hp.closeUnitary hq h
  set z := (hp.isUnit_projectionIntertwiner hq h).unit
  set d := p - q
  have hd_sa : IsSelfAdjoint d := hp.isSelfAdjoint.sub hq.isSelfAdjoint
  have hdd_nonneg : 0 ≤ d * d := by simpa only [hd_sa.star_eq] using star_mul_self_nonneg d
  have hzz : (z : A) * star (z : A) = 1 - d * d := by
    rw [IsUnit.unit_spec, projectionIntertwiner_mul_star_self hp hq]
  set s := CFC.sqrt (1 - d * d)
  have hs_nonneg : 0 ≤ s := CFC.sqrt_nonneg _
  have hs_unit : IsUnit s := by
    dsimp only [s]; rw [← hzz]; exact z.isStrictlyPositive_sqrt_mul_star.isUnit
  have hs_sq : s * s = 1 - d * d := by
    dsimp only [s]; rw [← hzz, CFC.sqrt_mul_sqrt_self _ (mul_star_self_nonneg (z : A)), hzz]
  have hs_le_one : s ≤ 1 := by
    rw [← CFC.sqrt_one (A := A)]; exact CFC.sqrt_le_sqrt _ _ (sub_le_self 1 hdd_nonneg)
  have hus : (u : A) * s = projectionIntertwiner p q :=
    hp.closeUnitary_mul_sqrt_one_sub_sub_mul_self hq h
  have hsu_star : s * star (u : A) = star (projectionIntertwiner p q) := by
    simpa only [star_mul, hs_nonneg.isSelfAdjoint.star_eq] using congrArg star hus
  have hu_add_star : (u : A) + star (u : A) = 2 * s := by
    apply hs_unit.mul_left_cancel
    calc s * ((u : A) + star (u : A))
        = projectionIntertwiner p q + star (projectionIntertwiner p q) := by
          rw [mul_add, hp.sqrt_one_sub_sub_mul_self_mul_closeUnitary hq h, hsu_star]
      _ = 2 * (s * s) := by rw [projectionIntertwiner_add_star hp hq, hs_sq]
      _ = s * (2 * s) := by noncomm_ring
  have hu_sub_sq : star ((u : A) - 1) * ((u : A) - 1) = (2 : ℝ) • (1 - s) := by
    have h1 : star ((u : A) - 1) * ((u : A) - 1) = 1 + 1 - ((u : A) + star (u : A)) := by
      rw [star_sub, star_one, sub_mul, mul_sub, mul_sub,
        Unitary.star_mul_self_of_mem u.property, mul_one, one_mul, one_mul]; abel
    rw [h1, hu_add_star, two_mul, two_smul]; abel
  have h_one_sub_s_nonneg : 0 ≤ 1 - s := sub_nonneg.mpr hs_le_one
  have h_one_sub_s_le : 1 - s ≤ d * d := by
    have hdiff : d * d - (1 - s) = (1 - s) * s := by
      have hss : 1 - s * s = d * d := by rw [hs_sq, sub_sub_cancel]
      rw [← hss]; noncomm_ring
    rw [← sub_nonneg, hdiff]
    exact Commute.mul_nonneg h_one_sub_s_nonneg hs_nonneg ((Commute.one_left s).sub_left rfl)
  have hnorm_sq : ‖(u : A) - 1‖ ^ 2 ≤ (√2 * ‖d‖) ^ 2 := by
    calc ‖(u : A) - 1‖ ^ 2
        = ‖(2 : ℝ) • (1 - s)‖ := by rw [sq, ← CStarRing.norm_star_mul_self, hu_sub_sq]
      _ ≤ ‖(2 : ℝ) • (d * d)‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg
          (smul_le_smul_of_nonneg_left h_one_sub_s_le zero_le_two)
          (smul_nonneg zero_le_two h_one_sub_s_nonneg)
      _ = (√2 * ‖d‖) ^ 2 := by
          rw [norm_smul, Real.norm_ofNat]; nth_rw 1 [← hd_sa.star_eq]
          rw [CStarRing.norm_star_mul_self, ← sq, mul_pow, Real.sq_sqrt zero_le_two]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hnorm_sq

/-- Since `‖p - q‖ < 1` and `√2 < 2`, `hp.closeUnitary hq h` has distance `< 2` from `1`. -/
theorem norm_closeUnitary_sub_one_lt_two {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ‖(hp.closeUnitary hq h : A) - 1‖ < 2 := by
  have hsqrt2 : √2 < 2 := by rw [Real.sqrt_lt' zero_lt_two]; norm_num
  exact (hp.norm_closeUnitary_sub_one_le hq h).trans_lt
    ((mul_lt_mul_of_pos_left h (by positivity)).trans ((mul_one √2).trans_lt hsqrt2))

/-- Nearby star projections (`‖p - q‖ < 1`) are conjugate by `hp.closeUnitary hq h`, which lies in
the path component of `1`. -/
theorem joined_one_closeUnitary {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    Joined (1 : unitary A) (hp.closeUnitary hq h) :=
  Unitary.joined 1 (hp.closeUnitary hq h) (hp.norm_closeUnitary_sub_one_lt_two hq h)

/-- Existential form of Sz.-Nagy's perturbation theorem. -/
theorem exists_unitary_conj_of_norm_sub_lt_one {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ∃ u : unitary A, Joined (1 : unitary A) u ∧
      (u : A) * p * star (u : A) = q ∧ ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ :=
  ⟨hp.closeUnitary hq h, hp.joined_one_closeUnitary hq h,
    hp.closeUnitary_mul_self_mul_star hq h, hp.norm_closeUnitary_sub_one_le hq h⟩

end Perturbation

section NonUnitalPerturbation

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- In a possibly non-unital C⋆-algebra `B`, star projections `p` and `q` with `‖p - q‖ < 1` are
conjugate inside `Unitization ℂ B` by a unitary joined to `1` satisfying
`‖(u : Unitization ℂ B) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_unitization_unitary_conj_of_norm_sub_lt_one {p q : B}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ∃ u : unitary (Unitization ℂ B), Joined (1 : unitary (Unitization ℂ B)) u ∧
      (u : Unitization ℂ B) * (p : Unitization ℂ B) * star (u : Unitization ℂ B) =
        (q : Unitization ℂ B) ∧
      ‖(u : Unitization ℂ B) - 1‖ ≤ √2 * ‖p - q‖ := by
  have hp' : IsStarProjection (p : Unitization ℂ B) :=
    hp.map (Unitization.inrNonUnitalStarAlgHom ℂ B)
  have hq' : IsStarProjection (q : Unitization ℂ B) :=
    hq.map (Unitization.inrNonUnitalStarAlgHom ℂ B)
  have hnorm_eq : ‖(p : Unitization ℂ B) - (q : Unitization ℂ B)‖ = ‖p - q‖ := by
    rw [← Unitization.inr_sub, Unitization.norm_inr]
  obtain ⟨u, hu_join, hu_conj, hu_norm⟩ :=
    hp'.exists_unitary_conj_of_norm_sub_lt_one hq' (hnorm_eq.trans_lt h)
  exact ⟨u, hu_join, hu_conj, hnorm_eq ▸ hu_norm⟩

/-- Nearby star projections (`‖p - q‖ < 1`) in a possibly non-unital C⋆-algebra `B` are linked by
a partial isometry `v : B` with `star v * v = p` and `v * star v = q`. -/
theorem exists_isPartialIsometry_of_norm_sub_lt_one {p q : B}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ∃ v : B, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  obtain ⟨u, -, hu_conj, -⟩ := hp.exists_unitization_unitary_conj_of_norm_sub_lt_one hq h
  exact hp.exists_isPartialIsometry_of_unitization_unitary_conj u hu_conj

end NonUnitalPerturbation

end IsStarProjection

namespace Path

/-- Any norm-continuous path of star projections in a unital C⋆-algebra has endpoints conjugate by
a unitary in the identity path component of `unitary A`. -/
theorem exists_joined_one_unitary_conj_of_isStarProjection {A : Type*} [CStarAlgebra A]
    {p q : A} (γ : Path p q) (hγ : ∀ t : I, IsStarProjection (γ t)) :
    ∃ u : unitary A, Joined (1 : unitary A) u ∧ (u : A) * p * star (u : A) = q := by
  let P : I → I → Prop := fun s t ↦
    ∃ u : unitary A, Joined (1 : unitary A) u ∧ (u : A) * γ s * star (u : A) = γ t
  have hstar_cont : Continuous (star : unitary A → unitary A) :=
    (continuous_star.comp continuous_subtypeVal).subtype_mk _
  have hsymm : Std.Symm P := ⟨fun s t ⟨u, hu_join, hu_conj⟩ ↦
    ⟨star u, by simpa only [star_one] using hu_join.map hstar_cont, by
      rw [Unitary.coe_star, star_star, ← hu_conj, ← mul_assoc, ← mul_assoc,
        Unitary.star_mul_self_of_mem u.property, one_mul, mul_assoc,
        Unitary.star_mul_self_of_mem u.property, mul_one]⟩⟩
  have htrans : IsTrans I P := ⟨fun r s t ⟨u, hu_join, hu_conj⟩ ⟨w, hw_join, hw_conj⟩ ↦
    ⟨w * u, by simpa only [mul_one] using hw_join.mul hu_join, by
      simp only [Submonoid.coe_mul, star_mul, mul_assoc]
      rw [← mul_assoc (u : A), ← mul_assoc ((u : A) * γ r), hu_conj, ← mul_assoc, hw_conj]⟩⟩
  have hloc : ∀ s : I, ∀ᶠ t in nhds s, P s t := fun s ↦ by
    filter_upwards [γ.continuous.continuousAt.eventually (Metric.ball_mem_nhds (γ s) zero_lt_one)]
      with t ht
    have hnorm : ‖γ s - γ t‖ < 1 := by rwa [dist_comm, dist_eq_norm] at ht
    exact ⟨(hγ s).closeUnitary (hγ t) hnorm, (hγ s).joined_one_closeUnitary (hγ t) hnorm,
      (hγ s).closeUnitary_mul_self_mul_star (hγ t) hnorm⟩
  simpa only [P, γ.source, γ.target] using PreconnectedSpace.induction₂ P hloc htrans 0 1

/-- Any norm-continuous path of star projections in a possibly non-unital C⋆-algebra `B` yields a
partial isometry `v : B` with `star v * v = p` and `v * star v = q`. -/
theorem exists_isPartialIsometry_of_isStarProjection {B : Type*} [NonUnitalCStarAlgebra B]
    {p q : B} (γ : Path p q) (hγ : ∀ t : I, IsStarProjection (γ t)) :
    ∃ v : B, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  let γ' : Path (p : Unitization ℂ B) (q : Unitization ℂ B) :=
    γ.map Unitization.isometry_inr.continuous
  have hγ' : ∀ t : I, IsStarProjection (γ' t) := fun t ↦
    (hγ t).map (Unitization.inrNonUnitalStarAlgHom ℂ B)
  obtain ⟨u, -, hu_conj⟩ := γ'.exists_joined_one_unitary_conj_of_isStarProjection hγ'
  exact (γ.source ▸ hγ 0).exists_isPartialIsometry_of_unitization_unitary_conj u hu_conj

end Path
