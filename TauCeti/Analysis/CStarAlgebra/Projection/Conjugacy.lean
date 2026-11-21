/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.Projection.Intertwiner
public import TauCeti.Analysis.CStarAlgebra.Unitary.Polar
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import TauCeti.Analysis.Normed.Ring.Units

/-!
# Unitary conjugacy of nearby projections in a C⋆-algebra

To show that homotopy, Murray–von Neumann, and unitary equivalence coincide on nearby projections
and `K₀` classes are locally constant along inductive limits, Kato's `projectionIntertwiner p q`
polar-normalizes to `u = hp.projectionConjugacyUnitary hq h` for `‖p - q‖ < 1`, with
`(u : A) * p * star (u : A) = q`, `Joined 1 u`, `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`, closed unital
`𝕜'`-`⋆`-subalgebra preservation, and scalar part `1` in `Unitization ℂ A`.

## Main results

* `IsStarProjection.projectionConjugacyUnitary`,
  `IsStarProjection.star_projectionConjugacyUnitary`,
  `IsStarProjection.exists_unitary_conjugate_mem_of_norm_sub_lt_one`,
  `IsStarProjection.exists_unitary_conjugate_of_norm_sub_lt_one`,
  `IsStarProjection.exists_unitization_unitary_conjugate_of_norm_sub_lt_one`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1966), Ch. I, §4.6.
* B. Blackadar, *Operator Algebras*, Springer (2006), §II.3.3; *K-Theory for Operator Algebras*,
  2nd ed., Cambridge Univ. Press (1998), 4.6.6.
-/

public section

open TauCeti
open scoped ContinuousFunctionalCalculus Real

namespace IsStarProjection
section
variable {A : Type*} [CStarAlgebra A] {p q : A}
private theorem spectrum_one_sub_sub_sq_bounds (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) {x : ℝ} (hx : x ∈ spectrum ℝ (1 - (p - q) ^ 2)) :
    0 < x ∧ x ≤ 1 ∧ 1 - x ≤ ‖p - q‖ ^ 2 := by
  rcases subsingleton_or_nontrivial A with _ | _; · exact (hx (isUnit_of_subsingleton _)).elim
  have hd : IsSelfAdjoint (p - q) := hp.isSelfAdjoint.sub hq.isSelfAdjoint
  rw [← show cfc (fun t : ℝ ↦ 1 - t ^ 2) (p - q) = 1 - (p - q) ^ 2 by
      rw [cfc_sub _ _ (p - q), cfc_const_one ℝ _ hd, cfc_pow _ 2 (p - q), cfc_id' ℝ _ hd],
    cfc_map_spectrum (fun t : ℝ ↦ 1 - t ^ 2) (p - q) hd (by fun_prop)] at hx
  rcases hx with ⟨t, ht, rfl⟩
  have htsq : t ^ 2 ≤ ‖p - q‖ ^ 2 := (sq_abs t).symm ▸ pow_le_pow_left₀ (abs_nonneg t)
    (by simpa [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem ht) 2
  exact ⟨by nlinarith [norm_nonneg (p - q)], by nlinarith [sq_nonneg t], by linarith⟩
/-- **Kato–Sz.-Nagy conjugating unitary** for star projections `p, q` with `‖p - q‖ < 1`, defined
as the polar unitary of `projectionIntertwiner p q`. -/
noncomputable def projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : unitary A :=
  let _ := CStarAlgebra.spectralOrder A; let _ := CStarAlgebra.spectralOrderedRing A
  (hp.isIdempotentElem.isUnit_projectionIntertwiner hq.isIdempotentElem h).unit.polarUnitary
/-- Functional-calculus formula for `IsStarProjection.projectionConjugacyUnitary`. -/
theorem coe_projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : (hp.projectionConjugacyUnitary hq h : A) =
      projectionIntertwiner p q * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2) := by
  let _ := CStarAlgebra.spectralOrder A; let _ := CStarAlgebra.spectralOrderedRing A
  rw [projectionConjugacyUnitary, Units.coe_polarUnitary_eq_mul_cfc_inv_sqrt, IsUnit.unit_spec,
    hp.star_projectionIntertwiner_mul_self hq]
/-- The Kato–Sz.-Nagy unitary of a projection `p` with itself is `1`. -/
@[simp] theorem projectionConjugacyUnitary_self (hp : IsStarProjection p) (h : ‖p - p‖ < 1) :
    hp.projectionConjugacyUnitary hp h = 1 := by
  let _ := CStarAlgebra.spectralOrder A; let _ := CStarAlgebra.spectralOrderedRing A
  rw [projectionConjugacyUnitary, show (hp.isIdempotentElem.isUnit_projectionIntertwiner
      hp.isIdempotentElem h).unit = 1 from Units.ext <| by
    simp [hp.isIdempotentElem.projectionIntertwiner_self], Units.polarUnitary_one]
/-- Swapping `p` and `q` takes `IsStarProjection.projectionConjugacyUnitary` to its adjoint. -/
@[simp] theorem star_projectionConjugacyUnitary (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    star (hp.projectionConjugacyUnitary hq h) =
      hq.projectionConjugacyUnitary hp (norm_sub_rev p q ▸ h) := by
  let _ := CStarAlgebra.spectralOrder A; let _ := CStarAlgebra.spectralOrderedRing A
  rw [projectionConjugacyUnitary, projectionConjugacyUnitary, ← Units.polarUnitary_star]
  congr 1; ext; simp [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
/-- `hp.projectionConjugacyUnitary hq h` belongs to every closed unital `𝕜'`-`⋆`-subalgebra
(for any scalar monoid `𝕜'` over `ℝ`) containing `p` and `q`. -/
theorem projectionConjugacyUnitary_mem {𝕜' S : Type*} [Monoid 𝕜'] [MulAction 𝕜' A] [SetLike S A]
    [SubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A] [SMulMemClass S 𝕜' A] [StarMemClass S A]
    {s : S} [IsClosed (s : Set A)] (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) (hp_mem : p ∈ s) (hq_mem : q ∈ s) :
    (hp.projectionConjugacyUnitary hq h : A) ∈ s := by
  let _ := CStarAlgebra.spectralOrder A; let _ := CStarAlgebra.spectralOrderedRing A
  rw [projectionConjugacyUnitary]; exact Units.polarUnitary_mem (𝕜' := 𝕜') _ <| by
    rw [IsUnit.unit_spec]; exact projectionIntertwiner_mem hp_mem hq_mem
/-- Unital `⋆`-ring homomorphisms preserve `IsStarProjection.projectionConjugacyUnitary`. -/
theorem map_projectionConjugacyUnitary {B F : Type*} [CStarAlgebra B] [FunLike F A B]
    [RingHomClass F A B] [StarHomClass F A B] (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) (φ : F) (hφ : ‖φ p - φ q‖ < 1) :
    φ (hp.projectionConjugacyUnitary hq h : A) =
      (((hp.map φ).projectionConjugacyUnitary (hq.map φ) hφ : unitary B) : B) := by
  let _ := CStarAlgebra.spectralOrder A; let _ := CStarAlgebra.spectralOrderedRing A
  let _ := CStarAlgebra.spectralOrder B; let _ := CStarAlgebra.spectralOrderedRing B
  set u := (hp.isIdempotentElem.isUnit_projectionIntertwiner hq.isIdempotentElem h).unit
  have hu' : ((hp.map φ).isIdempotentElem.isUnit_projectionIntertwiner
      (hq.map φ).isIdempotentElem hφ).unit = Units.map (φ : A →* B) u := Units.ext <| by
    simp only [u, Units.coe_map, MonoidHom.coe_ofClass, IsUnit.unit_spec, map_projectionIntertwiner]
  rw [projectionConjugacyUnitary, projectionConjugacyUnitary, hu']; exact u.map_polarUnitary φ
/-- Intertwining identity `q * u = u * p` for `IsStarProjection.projectionConjugacyUnitary`. -/
theorem mul_projectionConjugacyUnitary_eq_projectionConjugacyUnitary_mul
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    q * (hp.projectionConjugacyUnitary hq h : A) =
      (hp.projectionConjugacyUnitary hq h : A) * p := by
  let _ := CStarAlgebra.spectralOrder A; let _ := CStarAlgebra.spectralOrderedRing A
  have hp' := hp.isIdempotentElem; have hq' := hq.isIdempotentElem
  rw [projectionConjugacyUnitary]; refine Units.mul_polarUnitary_eq_polarUnitary_mul _
    (by simpa using hp'.mul_projectionIntertwiner_eq_projectionIntertwiner_mul hq')
    (by simpa [star_projectionIntertwiner, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
          using (hq'.mul_projectionIntertwiner_eq_projectionIntertwiner_mul hp').symm)
/-- Conjugating `p` by `hp.projectionConjugacyUnitary hq h` yields `q`. -/
@[simp] theorem conjugate_projectionConjugacyUnitary (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    (hp.projectionConjugacyUnitary hq h : A) * p * star (hp.projectionConjugacyUnitary hq h : A) =
      q := by
  rw [← hp.mul_projectionConjugacyUnitary_eq_projectionConjugacyUnitary_mul hq h, mul_assoc,
    Unitary.mul_star_self_of_mem (hp.projectionConjugacyUnitary hq h).property, mul_one]
/-- Distance bound `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖` for `u = hp.projectionConjugacyUnitary hq h`. -/
theorem norm_projectionConjugacyUnitary_sub_one_le (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ‖(hp.projectionConjugacyUnitary hq h : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  set u := hp.projectionConjugacyUnitary hq h; set z := projectionIntertwiner p q
  set a := 1 - (p - q) ^ 2; set w := cfc (fun x : ℝ ↦ (√x)⁻¹) a
  have ha : IsSelfAdjoint a :=
    (IsSelfAdjoint.one A).sub ((hp.isSelfAdjoint.sub hq.isSelfAdjoint).pow 2)
  have hw_sa : IsSelfAdjoint w := cfc_predicate _ a
  have hstar_z_comm_w : star z * w = w * star z := by
    simpa only [star_mul, hw_sa.star_eq, z, a, w] using congrArg star
      ((hp.isIdempotentElem.commute_projectionIntertwiner_one_sub_sub_sq
        hq.isIdempotentElem).symm.cfc_real (fun x : ℝ ↦ (√x)⁻¹)).eq
  have haw : a * w = cfc Real.sqrt a := by
    conv_lhs => lhs; rw [← cfc_id' ℝ a ha]
    rw [← cfc_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ (√x)⁻¹) a (continuousOn_id' _)
      (Real.continuous_sqrt.continuousOn.inv₀
        fun _ hx ↦ (Real.sqrt_pos.mpr (hp.spectrum_one_sub_sub_sq_bounds hq h hx).1).ne')]
    refine cfc_congr fun x hx ↦ ?_; have hx_pos := (hp.spectrum_one_sub_sub_sq_bounds hq h hx).1
    field_simp [(Real.sqrt_pos.mpr hx_pos).ne']; exact (Real.sq_sqrt hx_pos.le).symm
  have hu_add : (u : A) + star (u : A) = cfc (fun x : ℝ ↦ 2 * √x) a := by
    rw [hp.coe_projectionConjugacyUnitary hq h, star_mul, hw_sa.star_eq, ← hstar_z_comm_w,
      ← add_mul, hp.projectionIntertwiner_add_star hq, ← Nat.cast_smul_eq_nsmul ℝ 2 a,
      Nat.cast_ofNat, smul_mul_assoc, haw, ← cfc_smul (2 : ℝ) Real.sqrt a]; simp_rw [smul_eq_mul]
  have hstar_sub : star ((u : A) - 1) * ((u : A) - 1) = cfc (fun x : ℝ ↦ 2 * (1 - √x)) a := by
    rw [show star ((u : A) - 1) * ((u : A) - 1) = (2 : A) - ((u : A) + star (u : A)) by
        simp only [star_sub, star_one, sub_mul, mul_sub, mul_one, one_mul,
          Unitary.star_mul_self_of_mem u.property, ← one_add_one_eq_two]; abel,
      ← map_ofNat (algebraMap ℝ A) 2, ← cfc_const (2 : ℝ) a ha, hu_add, ← cfc_sub _ _ a]
    exact cfc_congr fun _ _ ↦ by ring
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [sq, ← CStarRing.norm_star_mul_self, hstar_sub, mul_pow, Real.sq_sqrt (by positivity)]
  refine norm_cfc_le (by positivity) fun x hx ↦ ?_
  obtain ⟨hx_pos, hx_le_one, h1x⟩ := hp.spectrum_one_sub_sub_sq_bounds hq h hx
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity)
    (sub_nonneg.mpr (Real.sqrt_le_one.mpr hx_le_one)))]
  nlinarith [Real.mul_self_sqrt hx_pos.le, Real.sqrt_nonneg x]
/-- `hp.projectionConjugacyUnitary hq h` lies in the path component of `1` in `unitary A`. -/
theorem joined_one_projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : Joined 1 (hp.projectionConjugacyUnitary hq h) :=
  Unitary.joined 1 _ ((hp.norm_projectionConjugacyUnitary_sub_one_le hq h).trans_lt <| by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2])
/-- **Unitary conjugacy in a closed unital `⋆`-subalgebra**: `p, q ∈ s` with `‖p - q‖ < 1` are
conjugate by `u : unitary A` in `s` with `Joined 1 u` and `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_unitary_conjugate_mem_of_norm_sub_lt_one {𝕜' S : Type*} [Monoid 𝕜'] [MulAction 𝕜' A]
    [SetLike S A] [SubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A] [SMulMemClass S 𝕜' A]
    [StarMemClass S A] {s : S} [IsClosed (s : Set A)] (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hp_mem : p ∈ s) (hq_mem : q ∈ s) (h : ‖p - q‖ < 1) :
    ∃ u : unitary A, (u : A) ∈ s ∧ Joined 1 u ∧ (u : A) * p * star (u : A) = q ∧
      ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ :=
  ⟨_, hp.projectionConjugacyUnitary_mem (𝕜' := 𝕜') hq h hp_mem hq_mem,
    hp.joined_one_projectionConjugacyUnitary hq h, hp.conjugate_projectionConjugacyUnitary hq h,
    hp.norm_projectionConjugacyUnitary_sub_one_le hq h⟩
/-- **Unitary conjugacy of nearby projections**: star projections `p, q` with `‖p - q‖ < 1` are
conjugate by `u : unitary A` with `Joined 1 u` and `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_unitary_conjugate_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = q ∧
      ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ :=
  ⟨_, hp.joined_one_projectionConjugacyUnitary hq h, hp.conjugate_projectionConjugacyUnitary hq h,
    hp.norm_projectionConjugacyUnitary_sub_one_le hq h⟩
end
/-- If star projections `p, q : Unitization ℂ A` with `‖p - q‖ < 1` satisfy `p.fst = q.fst`, then
`(hp.projectionConjugacyUnitary hq h : Unitization ℂ A).fst = 1`. -/
theorem fst_projectionConjugacyUnitary_eq_one {A : Type*} [NonUnitalCStarAlgebra A]
    {p q : Unitization ℂ A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) (hfst : p.fst = q.fst) :
    (hp.projectionConjugacyUnitary hq h : Unitization ℂ A).fst = 1 := by
  let _ := CStarAlgebra.spectralOrder (Unitization ℂ A)
  let _ := CStarAlgebra.spectralOrderedRing (Unitization ℂ A)
  rw [projectionConjugacyUnitary]; refine Units.fst_polarUnitary_eq_one ?_
  rw [IsUnit.unit_spec, ← Unitization.fstHom_apply ℂ A, map_projectionIntertwiner,
    Unitization.fstHom_apply, Unitization.fstHom_apply, ← hfst]
  exact (hp.isIdempotentElem.map (Unitization.fstHom ℂ A)).projectionIntertwiner_self
/-- **Unitary conjugacy of nearby projections (non-unital)**: `p, q` (`‖p - q‖ < 1`) are conjugate
in `Unitization ℂ A` by `u` with `fst = 1`, `Joined 1 u`, and `‖(u : _) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_unitization_unitary_conjugate_of_norm_sub_lt_one {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    ∃ u : unitary (Unitization ℂ A), (u : Unitization ℂ A).fst = 1 ∧ Joined 1 u ∧
      (u : Unitization ℂ A) * (p : Unitization ℂ A) * star (u : Unitization ℂ A) =
        (q : Unitization ℂ A) ∧ ‖(u : Unitization ℂ A) - 1‖ ≤ √2 * ‖p - q‖ := by
  let ι := Unitization.inrNonUnitalStarAlgHom ℂ A; have hp' := hp.map ι; have hq' := hq.map ι
  have hnorm : ‖(p : Unitization ℂ A) - (q : Unitization ℂ A)‖ = ‖p - q‖ := by
    rw [← Unitization.inr_sub, Unitization.norm_inr]
  exact ⟨_, hp'.fst_projectionConjugacyUnitary_eq_one hq' (hnorm.symm ▸ h) (by simp [ι]),
    hp'.joined_one_projectionConjugacyUnitary hq' (hnorm.symm ▸ h),
    hp'.conjugate_projectionConjugacyUnitary hq' (hnorm.symm ▸ h),
    (hp'.norm_projectionConjugacyUnitary_sub_one_le hq' (hnorm.symm ▸ h)).trans_eq
      (congrArg _ hnorm)⟩
end IsStarProjection
