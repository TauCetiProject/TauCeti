/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import TauCeti.Algebra.Star.Projection.Intertwiner

/-!
# Unitary conjugacy of nearby projections in a C⋆-algebra

Two star projections `p, q` in a unital C⋆-algebra `A` with `‖p - q‖ < 1` are conjugate by a
unitary `u : unitary A` in the path component of `1` with `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`, lying in
every closed star subalgebra containing `p` and `q`. For non-unital `A`, `Unitization ℂ A` yields a
conjugating unitary with scalar part `1`.

## Main definitions

* `TauCeti.projectionConjugacyElem`, `IsStarProjection.projectionConjugacyUnitary`.

## Main statements

* `IsStarProjection.conjugate_projectionConjugacyUnitary`,
  `IsStarProjection.norm_projectionConjugacyUnitary_sub_one_le`,
  `IsStarProjection.joined_one_projectionConjugacyUnitary`,
  `IsStarProjection.exists_unitization_unitary_conjugate_of_norm_sub_lt_one`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.4.3.2.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge Univ. Press (1998), 4.6.6.
-/

public section

open scoped CStarAlgebra Real

namespace TauCeti

variable {A : Type*} [CStarAlgebra A]

/-- The **Kato–Sz.-Nagy conjugating element**
`projectionIntertwiner p q * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2)`. -/
noncomputable def projectionConjugacyElem (p q : A) : A :=
  projectionIntertwiner p q * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2)

/-- Unfold `TauCeti.projectionConjugacyElem`. -/
theorem projectionConjugacyElem_def (p q : A) :
    projectionConjugacyElem p q =
      projectionIntertwiner p q * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2) := (rfl)

/-- `TauCeti.projectionConjugacyElem p q` lies in every closed star subalgebra containing `p, q`. -/
theorem projectionConjugacyElem_mem {S : Type*} [SetLike S A] [SubringClass S A]
    [SMulMemClass S ℝ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {p q : A}
    (hp : p ∈ s) (hq : q ∈ s) : projectionConjugacyElem p q ∈ s := by
  rw [projectionConjugacyElem_def, projectionIntertwiner_def]
  exact mul_mem
    (add_mem (mul_mem hq hp) (mul_mem (sub_mem (one_mem s) hq) (sub_mem (one_mem s) hp)))
    (cfc_mem (𝕜 := ℝ) (𝕜' := ℝ) _ (sub_mem (one_mem s) (pow_mem (sub_mem hp hq) 2)))

end TauCeti

namespace IsStarProjection

open TauCeti

section Unital

variable {A : Type*} [CStarAlgebra A] {p q : A}

private theorem spectrum_one_sub_sub_sq_bounds (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) {x : ℝ} (hx : x ∈ spectrum ℝ (1 - (p - q) ^ 2)) :
    0 < x ∧ x ≤ 1 ∧ 1 - x ≤ ‖p - q‖ ^ 2 := by
  rcases subsingleton_or_nontrivial A with _ | _
  · exact (hx (isUnit_of_subsingleton _)).elim
  have hd : IsSelfAdjoint (p - q) := hp.isSelfAdjoint.sub hq.isSelfAdjoint
  have hcfc : cfc (fun t : ℝ ↦ 1 - t ^ 2) (p - q) = 1 - (p - q) ^ 2 := by
    rw [cfc_sub _ _ (p - q), cfc_const_one ℝ (p - q) hd, cfc_pow _ 2 (p - q), cfc_id' ℝ (p - q) hd]
  rw [← hcfc, cfc_map_spectrum (fun t : ℝ ↦ 1 - t ^ 2) (p - q) hd
    (continuous_const.sub (continuous_pow 2)).continuousOn] at hx
  rcases hx with ⟨t, ht, rfl⟩
  have ht_le : |t| ≤ ‖p - q‖ := by simpa [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem ht
  have htsq : t ^ 2 ≤ ‖p - q‖ ^ 2 := (sq_abs t).symm ▸ pow_le_pow_left₀ (abs_nonneg t) ht_le 2
  exact ⟨by nlinarith [norm_nonneg (p - q)], by nlinarith [sq_nonneg t], by linarith⟩

private theorem continuousOn_inv_sqrt_one_sub_sub_sq (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ContinuousOn (fun x : ℝ ↦ (√x)⁻¹) (spectrum ℝ (1 - (p - q) ^ 2)) :=
  Real.continuous_sqrt.continuousOn.inv₀ fun _ hx ↦
    (Real.sqrt_pos.mpr (hp.spectrum_one_sub_sub_sq_bounds hq h hx).1).ne'

private theorem mul_cfc_inv_sqrt_one_sub_sub_sq (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : (1 - (p - q) ^ 2) * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2) =
      cfc Real.sqrt (1 - (p - q) ^ 2) := by
  set a := 1 - (p - q) ^ 2
  have ha : IsSelfAdjoint a :=
    (IsSelfAdjoint.one A).sub ((hp.isSelfAdjoint.sub hq.isSelfAdjoint).pow 2)
  conv_lhs => lhs; rw [(cfc_id' ℝ a ha).symm]
  rw [← cfc_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ (√x)⁻¹) a continuousOn_id
    (hp.continuousOn_inv_sqrt_one_sub_sub_sq hq h)]
  refine cfc_congr fun x hx ↦ ?_
  have hx_pos := (hp.spectrum_one_sub_sub_sq_bounds hq h hx).1
  conv_lhs => lhs; rw [← Real.mul_self_sqrt hx_pos.le]
  rw [mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr hx_pos).ne', mul_one]

/-- When `‖p - q‖ < 1`, `TauCeti.projectionConjugacyElem p q` is unitary. -/
theorem projectionConjugacyElem_mem_unitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : projectionConjugacyElem p q ∈ unitary A := by
  set z := projectionIntertwiner p q; set a := 1 - (p - q) ^ 2
  set f : ℝ → ℝ := fun x ↦ (√x)⁻¹; set w := cfc f a
  have ha : IsSelfAdjoint a :=
    (IsSelfAdjoint.one A).sub ((hp.isSelfAdjoint.sub hq.isSelfAdjoint).pow 2)
  have hw_sa : IsSelfAdjoint w := cfc_predicate f a
  have hz_comm_w : Commute z w :=
    ((hp.isIdempotentElem.commute_projectionIntertwiner_one_sub_sub_sq
      hq.isIdempotentElem).symm.cfc_real f).symm
  have hstar_z_comm_w : w * star z = star z * w := by
    simpa [star_mul, hw_sa.star_eq] using congrArg star hz_comm_w.eq
  have haw_w : a * w * w = 1 := by
    rw [hp.mul_cfc_inv_sqrt_one_sub_sub_sq hq h, ← cfc_mul Real.sqrt f a
      Real.continuous_sqrt.continuousOn (hp.continuousOn_inv_sqrt_one_sub_sub_sq hq h),
      ← cfc_const_one ℝ a ha]
    exact cfc_congr fun x hx ↦
      mul_inv_cancel₀ (Real.sqrt_pos.mpr (hp.spectrum_one_sub_sub_sq_bounds hq h hx).1).ne'
  have hwa_w : w * a * w = 1 := by rw [((Commute.refl a).cfc_real f).eq, haw_w]
  have hz1 : star z * z = a := hp.star_projectionIntertwiner_mul_self hq
  have hz2 : z * star z = a := hp.projectionIntertwiner_mul_star_self hq
  rw [Unitary.mem_iff, show projectionConjugacyElem p q = z * w from rfl, star_mul, hw_sa.star_eq]
  refine ⟨by rw [← mul_assoc, mul_assoc w, hz1, hwa_w], ?_⟩
  calc z * w * (w * star z) = w * z * (star z * w) := by rw [hz_comm_w.eq, hstar_z_comm_w]
    _ = w * (z * star z) * w := by simp only [mul_assoc]
    _ = 1 := by rw [hz2, hwa_w]

/-- **Unitary conjugating nearby projections** in a unital C⋆-algebra when `‖p - q‖ < 1`. -/
noncomputable def projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : unitary A :=
  ⟨projectionConjugacyElem p q, hp.projectionConjugacyElem_mem_unitary hq h⟩

/-- Coercion of `IsStarProjection.projectionConjugacyUnitary` to the ambient C⋆-algebra. -/
@[simp] theorem coe_projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    ((hp.projectionConjugacyUnitary hq h : unitary A) : A) = projectionConjugacyElem p q := (rfl)

/-- Intertwining identity `q * u = u * p` for `IsStarProjection.projectionConjugacyUnitary`. -/
theorem mul_projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    q * (hp.projectionConjugacyUnitary hq h : A) =
      (hp.projectionConjugacyUnitary hq h : A) * p := by
  rw [coe_projectionConjugacyUnitary, projectionConjugacyElem_def, ← mul_assoc,
    hp.isIdempotentElem.mul_projectionIntertwiner_eq_projectionIntertwiner_mul hq.isIdempotentElem,
    mul_assoc,
    ((hp.isIdempotentElem.commute_one_sub_sub_sq hq.isIdempotentElem).symm.cfc_real _).symm.eq,
    ← mul_assoc]

/-- Conjugating `p` by `hp.projectionConjugacyUnitary hq h` yields `q`. -/
theorem conjugate_projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    (hp.projectionConjugacyUnitary hq h : A) * p *
        star (hp.projectionConjugacyUnitary hq h : A) = q := by
  rw [← hp.mul_projectionConjugacyUnitary hq h, mul_assoc,
    Unitary.mul_star_self_of_mem (hp.projectionConjugacyUnitary hq h).2, mul_one]

/-- Quantitative distance estimate `‖u - 1‖ ≤ √2 * ‖p - q‖` for `projectionConjugacyUnitary`. -/
theorem norm_projectionConjugacyUnitary_sub_one_le (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ‖(hp.projectionConjugacyUnitary hq h : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  set u := hp.projectionConjugacyUnitary hq h; set z := projectionIntertwiner p q
  set a := 1 - (p - q) ^ 2; set f : ℝ → ℝ := fun x ↦ (√x)⁻¹; set w := cfc f a
  have ha : IsSelfAdjoint a :=
    (IsSelfAdjoint.one A).sub ((hp.isSelfAdjoint.sub hq.isSelfAdjoint).pow 2)
  have hw_sa : IsSelfAdjoint w := cfc_predicate f a
  have hz_comm_w : Commute z w :=
    ((hp.isIdempotentElem.commute_projectionIntertwiner_one_sub_sub_sq
      hq.isIdempotentElem).symm.cfc_real f).symm
  have hstar_z_comm_w : star z * w = w * star z := by
    simpa [star_mul, hw_sa.star_eq] using congrArg star hz_comm_w.eq.symm
  have hu_add : (u : A) + star (u : A) = cfc (fun x : ℝ ↦ 2 * √x) a := by
    rw [show (u : A) = z * w from rfl, star_mul, hw_sa.star_eq, ← hstar_z_comm_w, ← add_mul,
      show z + star z = 2 • a from hp.projectionIntertwiner_add_star hq,
      ← Nat.cast_smul_eq_nsmul ℝ 2 a, Nat.cast_ofNat, smul_mul_assoc,
      show a * w = cfc Real.sqrt a from hp.mul_cfc_inv_sqrt_one_sub_sub_sq hq h,
      ← cfc_smul (2 : ℝ) Real.sqrt a Real.continuous_sqrt.continuousOn]
    rfl
  have hstar_sub : star ((u : A) - 1) * ((u : A) - 1) = cfc (fun x : ℝ ↦ 2 * (1 - √x)) a := by
    have hexpand : star ((u : A) - 1) * ((u : A) - 1) = (2 : A) - ((u : A) + star (u : A)) := by
      simp only [star_sub, star_one, sub_mul, mul_sub, mul_one, one_mul,
        Unitary.star_mul_self_of_mem u.2, ← one_add_one_eq_two]; abel
    have h2 : (2 : A) = cfc (fun _ : ℝ ↦ (2 : ℝ)) a := by
      rw [cfc_const (2 : ℝ) a ha, Algebra.algebraMap_eq_smul_one, two_smul, one_add_one_eq_two]
    rw [hexpand, h2, hu_add, ← cfc_sub (fun _ : ℝ ↦ (2 : ℝ)) (fun x : ℝ ↦ 2 * √x) a
      continuousOn_const (continuous_const.mul Real.continuous_sqrt).continuousOn]
    exact cfc_congr fun _ _ ↦ by ring
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [sq, ← CStarRing.norm_star_mul_self, hstar_sub, mul_pow, Real.sq_sqrt (by positivity)]
  refine norm_cfc_le (by positivity) fun x hx ↦ ?_
  obtain ⟨hx_pos, hx_le_one, h1x⟩ := hp.spectrum_one_sub_sub_sq_bounds hq h hx
  have h1sqrt : 0 ≤ 1 - √x := sub_nonneg.mpr (Real.sqrt_le_one.mpr hx_le_one)
  have h1sqrt_le : 1 - √x ≤ 1 - x :=
    (le_mul_of_one_le_right h1sqrt (show 1 ≤ 1 + √x by linarith [Real.sqrt_nonneg x])).trans_eq <|
      by calc (1 - √x) * (1 + √x) = 1 - √x * √x := by ring
           _ = 1 - x := by rw [Real.mul_self_sqrt hx_pos.le]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  linarith

/-- `hp.projectionConjugacyUnitary hq h` lies in the path component of `1` in `unitary A`. -/
theorem joined_one_projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : Joined 1 (hp.projectionConjugacyUnitary hq h) := by
  refine Unitary.joined 1 (hp.projectionConjugacyUnitary hq h) ?_
  have hsqrt2 : √2 < 2 := by rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2)]; gcongr; norm_num
  exact (hp.norm_projectionConjugacyUnitary_sub_one_le hq h).trans_lt <|
    (mul_lt_mul_of_pos_left h (by positivity)).trans (by linarith)

/-- Existential form of unitary conjugacy of nearby projections in a unital C⋆-algebra. -/
theorem exists_unitary_conjugate_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = q ∧
      ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ :=
  ⟨hp.projectionConjugacyUnitary hq h, hp.joined_one_projectionConjugacyUnitary hq h,
    hp.conjugate_projectionConjugacyUnitary hq h,
    hp.norm_projectionConjugacyUnitary_sub_one_le hq h⟩

end Unital

section NonUnital

/-- **Unitary conjugacy of nearby projections in a non-unital C⋆-algebra**: in `Unitization ℂ A`,
`p` and `q` with `‖p - q‖ < 1` are conjugate by a unitary with scalar part `1`. -/
theorem exists_unitization_unitary_conjugate_of_norm_sub_lt_one {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    ∃ u : unitary (Unitization ℂ A), (u : Unitization ℂ A).fst = 1 ∧ Joined 1 u ∧
      (u : Unitization ℂ A) * (p : Unitization ℂ A) * star (u : Unitization ℂ A) =
        (q : Unitization ℂ A) ∧
      ‖(u : Unitization ℂ A) - 1‖ ≤ √2 * ‖p - q‖ := by
  let ι := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hp' : IsStarProjection (p : Unitization ℂ A) := hp.map ι
  have hq' : IsStarProjection (q : Unitization ℂ A) := hq.map ι
  have hnorm_eq : ‖(p : Unitization ℂ A) - (q : Unitization ℂ A)‖ = ‖p - q‖ := by
    rw [← Unitization.inr_sub, Unitization.norm_inr]
  have h' : ‖(p : Unitization ℂ A) - (q : Unitization ℂ A)‖ < 1 := hnorm_eq.symm ▸ h
  refine ⟨hp'.projectionConjugacyUnitary hq' h', ?_,
    hp'.joined_one_projectionConjugacyUnitary hq' h',
    hp'.conjugate_projectionConjugacyUnitary hq' h',
    hnorm_eq ▸ hp'.norm_projectionConjugacyUnitary_sub_one_le hq' h'⟩
  set a : Unitization ℂ A := 1 - ((p : Unitization ℂ A) - (q : Unitization ℂ A)) ^ 2
  let φ : Unitization ℂ A →⋆ₐ[ℂ] ℂ :=
    { Unitization.fstHom ℂ A with map_star' := Unitization.fst_star }
  have hφa : φ a = 1 := by change a.fst = 1; simp [a, sq]
  have ha : IsSelfAdjoint a :=
    (IsSelfAdjoint.one _).sub ((hp'.isSelfAdjoint.sub hq'.isSelfAdjoint).pow 2)
  have hwfst : (cfc (fun x : ℝ ↦ (√x)⁻¹) a).fst = 1 := by
    change φ (cfc (fun x : ℝ ↦ (√x)⁻¹) a) = 1
    rw [φ.map_cfc _ a (hp'.continuousOn_inv_sqrt_one_sub_sub_sq hq' h')
      Unitization.continuous_fst ha (hφa.symm ▸ IsSelfAdjoint.one ℂ), hφa]
    simp
  rw [coe_projectionConjugacyUnitary, projectionConjugacyElem_def, Unitization.fst_mul, hwfst]
  simp [projectionIntertwiner_def]

end NonUnital

end IsStarProjection
