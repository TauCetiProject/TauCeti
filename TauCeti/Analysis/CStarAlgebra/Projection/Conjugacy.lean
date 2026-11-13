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

Two star projections `p` and `q` in a unital C⋆-algebra `A` satisfying `‖p - q‖ < 1` are conjugate
by a unitary `u : unitary A` in the path component of `1` with quantitative norm bound
`‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`. Concretely, Kato's intertwiner
`z = projectionIntertwiner p q = q * p + (1 - q) * (1 - p)` satisfies
`q * z = z * p` and `star z * z = z * star z = 1 - (p - q) ^ 2`. When `‖p - q‖ < 1`, the spectrum
of `a = 1 - (p - q) ^ 2` lies in `[1 - ‖p - q‖ ^ 2, 1] ⊆ (0, 1]`, and multiplying `z` by
`cfc (fun x : ℝ ↦ (√x)⁻¹) a` produces a unitary `u` inside every closed star subalgebra containing
`p` and `q`, satisfying `(u : A) * p * star (u : A) = q` and
`star ((u : A) - 1) * ((u : A) - 1) = cfc (fun x : ℝ ↦ 2 * (1 - √x)) a`.

For a non-unital C⋆-algebra `A`, passing to `Unitization ℂ A` produces a unitary
`u : unitary (Unitization ℂ A)` with scalar part `u.1.fst = 1`, `Joined 1 u`,
`u.1 * (p : Unitization ℂ A) * star u.1 = (q : Unitization ℂ A)`, and
`‖u.1 - 1‖ ≤ √2 * ‖p - q‖`.

## Main definitions

* `TauCeti.projectionConjugacyElem p q`: the element
  `projectionIntertwiner p q * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2)`.
* `IsStarProjection.projectionConjugacyUnitary hp hq h`: `TauCeti.projectionConjugacyElem p q`
  bundled in `unitary A` when `‖p - q‖ < 1`.

## Main statements

* `IsStarProjection.conjugate_projectionConjugacyUnitary`,
  `IsStarProjection.norm_projectionConjugacyUnitary_sub_one_le`, and
  `IsStarProjection.joined_one_projectionConjugacyUnitary`: unitary conjugacy, quantitative
  `√2 * ‖p - q‖` estimate, and path-connectedness to `1` for nearby projections.
* `IsStarProjection.exists_unitization_unitary_conjugate_of_norm_sub_lt_one`: the non-unital
  version in `Unitization ℂ A` with scalar part `1`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Encyclopaedia of Mathematical Sciences **122**, Springer (2006), Proposition II.4.3.2.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications **5**,
  Cambridge University Press (1998), Proposition 4.6.6.
-/

public section

open scoped CStarAlgebra Real

namespace TauCeti

section Unital

variable {A : Type*} [CStarAlgebra A]

/-- The **Kato–Sz.-Nagy conjugating element**
`projectionIntertwiner p q * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2)`. When `p` and `q` are
star projections with `‖p - q‖ < 1`, this is a unitary conjugating `p` to `q`. -/
noncomputable def projectionConjugacyElem (p q : A) : A :=
  projectionIntertwiner p q * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2)

/-- Unfold `TauCeti.projectionConjugacyElem`. -/
theorem projectionConjugacyElem_def (p q : A) :
    projectionConjugacyElem p q =
      projectionIntertwiner p q * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2) :=
  (rfl)

/-- `TauCeti.projectionConjugacyElem p q` lies in every closed star subalgebra containing `p` and
`q`. -/
theorem projectionConjugacyElem_mem {S : Type*} [SetLike S A] [SubringClass S A]
    [SMulMemClass S ℝ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {p q : A}
    (hp : p ∈ s) (hq : q ∈ s) :
    projectionConjugacyElem p q ∈ s := by
  rw [projectionConjugacyElem_def, projectionIntertwiner_def]
  have hz : q * p + (1 - q) * (1 - p) ∈ s :=
    add_mem (mul_mem hq hp) (mul_mem (sub_mem (one_mem s) hq) (sub_mem (one_mem s) hp))
  have ha : 1 - (p - q) ^ 2 ∈ s := sub_mem (one_mem s) (pow_mem (sub_mem hp hq) 2)
  exact mul_mem hz (cfc_mem (𝕜 := ℝ) (𝕜' := ℝ) _ ha)

end Unital

end TauCeti

namespace IsStarProjection

open TauCeti

section Unital

variable {A : Type*} [CStarAlgebra A] {p q : A}

private theorem spectrum_one_sub_sub_sq_bounds (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) {x : ℝ} (hx : x ∈ spectrum ℝ (1 - (p - q) ^ 2)) :
    0 < x ∧ x ≤ 1 ∧ 1 - x ≤ ‖p - q‖ ^ 2 := by
  rcases subsingleton_or_nontrivial A with _ | _
  · exact False.elim (hx (isUnit_of_subsingleton _))
  have hd : IsSelfAdjoint (p - q) := hp.isSelfAdjoint.sub hq.isSelfAdjoint
  have hcfc : cfc (fun t : ℝ ↦ 1 - t ^ 2) (p - q) = 1 - (p - q) ^ 2 := by
    rw [cfc_sub (fun _ : ℝ ↦ (1 : ℝ)) (fun t : ℝ ↦ t ^ 2) (p - q),
      cfc_const_one ℝ (p - q) hd, cfc_pow (fun t : ℝ ↦ t) 2 (p - q), cfc_id' ℝ (p - q) hd]
  rw [← hcfc, cfc_map_spectrum (fun t : ℝ ↦ 1 - t ^ 2) (p - q) hd
    (continuous_const.sub (continuous_pow 2)).continuousOn] at hx
  rcases hx with ⟨t, ht, rfl⟩
  have ht_le : |t| ≤ ‖p - q‖ := by
    simpa [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem ht
  have htsq_le : t ^ 2 ≤ ‖p - q‖ ^ 2 := by
    calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      _ ≤ ‖p - q‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg t) ht_le 2
  have hnorm_sq_lt : ‖p - q‖ ^ 2 < 1 := by
    nlinarith [norm_nonneg (p - q)]
  refine ⟨by linarith, by nlinarith [sq_nonneg t], by linarith⟩

private theorem continuousOn_inv_sqrt_one_sub_sub_sq (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ContinuousOn (fun x : ℝ ↦ (√x)⁻¹) (spectrum ℝ (1 - (p - q) ^ 2)) := by
  refine Real.continuous_sqrt.continuousOn.inv₀ fun x hx ↦ ?_
  exact (Real.sqrt_pos.mpr (hp.spectrum_one_sub_sub_sq_bounds hq h hx).1).ne'

/-- When `‖p - q‖ < 1`, `TauCeti.projectionConjugacyElem p q` is unitary. -/
theorem projectionConjugacyElem_mem_unitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    projectionConjugacyElem p q ∈ unitary A := by
  set z := projectionIntertwiner p q
  set a := 1 - (p - q) ^ 2
  set f : ℝ → ℝ := fun x ↦ (√x)⁻¹
  set w := cfc f a
  have ha : IsSelfAdjoint a :=
    (IsSelfAdjoint.one A).sub ((hp.isSelfAdjoint.sub hq.isSelfAdjoint).pow 2)
  have hf_cont : ContinuousOn f (spectrum ℝ a) :=
    hp.continuousOn_inv_sqrt_one_sub_sub_sq hq h
  have hw_sa : IsSelfAdjoint w := cfc_predicate f a
  have hz_comm_w : Commute z w :=
    ((hp.isIdempotentElem.commute_projectionIntertwiner_one_sub_sub_sq
      hq.isIdempotentElem).symm.cfc_real f).symm
  have hwa_w : w * a * w = 1 := by
    have ha_id : a = cfc (fun x : ℝ ↦ x) a := (cfc_id' ℝ a ha).symm
    conv_lhs => rw [ha_id]
    rw [← cfc_mul f (fun x : ℝ ↦ x) a hf_cont continuousOn_id,
      ← cfc_mul (fun x : ℝ ↦ f x * x) f a (hf_cont.mul continuousOn_id) hf_cont,
      ← cfc_const_one ℝ a ha]
    refine cfc_congr fun x hx ↦ ?_
    have hx_pos : 0 < x := (hp.spectrum_one_sub_sub_sq_bounds hq h hx).1
    have hsqrt_ne : √x ≠ 0 := (Real.sqrt_pos.mpr hx_pos).ne'
    dsimp [f]
    calc (√x)⁻¹ * x * (√x)⁻¹
        = (√x)⁻¹ * (√x * √x) * (√x)⁻¹ := by rw [Real.mul_self_sqrt hx_pos.le]
      _ = ((√x)⁻¹ * √x) * (√x * (√x)⁻¹) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hsqrt_ne, mul_inv_cancel₀ hsqrt_ne, mul_one]
  rw [Unitary.mem_iff, projectionConjugacyElem_def, star_mul, hw_sa.star_eq]
  refine ⟨?_, ?_⟩
  · calc w * star z * (z * w)
        = w * (star z * z) * w := by simp only [mul_assoc]
      _ = w * a * w := by rw [hp.star_projectionIntertwiner_mul_self hq]
      _ = 1 := hwa_w
  · calc z * w * (w * star z)
        = w * z * (w * star z) := by rw [hz_comm_w.eq]
      _ = w * (z * w) * star z := by simp only [mul_assoc]
      _ = w * (w * z) * star z := by rw [hz_comm_w.eq]
      _ = w * w * (z * star z) := by simp only [mul_assoc]
      _ = w * w * a := by rw [hp.projectionIntertwiner_mul_star_self hq]
      _ = w * a * w := by
          have hw_comm_a : Commute w a := (Commute.refl a).cfc_real f
          conv_lhs => rw [mul_assoc, hw_comm_a.eq, ← mul_assoc]
      _ = 1 := hwa_w

/-- **Unitary conjugating nearby projections** in a unital C⋆-algebra: when `p` and `q` are star
projections with `‖p - q‖ < 1`, `hp.projectionConjugacyUnitary hq h : unitary A` conjugates `p` to
`q` with `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖` and `Joined 1 u`. -/
noncomputable def projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : unitary A :=
  ⟨projectionConjugacyElem p q, hp.projectionConjugacyElem_mem_unitary hq h⟩

/-- Coercion of `IsStarProjection.projectionConjugacyUnitary` to the ambient C⋆-algebra. -/
@[simp]
theorem coe_projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    ((hp.projectionConjugacyUnitary hq h : unitary A) : A) = projectionConjugacyElem p q :=
  (rfl)

/-- Intertwining identity `q * u = u * p` for `IsStarProjection.projectionConjugacyUnitary`. -/
theorem mul_projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    q * (hp.projectionConjugacyUnitary hq h : A) =
      (hp.projectionConjugacyUnitary hq h : A) * p := by
  rw [coe_projectionConjugacyUnitary, projectionConjugacyElem_def]
  have hp_comm : Commute p (cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2)) :=
    ((hp.isIdempotentElem.commute_one_sub_sub_sq hq.isIdempotentElem).symm.cfc_real _).symm
  calc q * (projectionIntertwiner p q * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2))
      = (q * projectionIntertwiner p q) * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2) := by
        rw [mul_assoc]
    _ = (projectionIntertwiner p q * p) * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2) := by
        rw [hp.isIdempotentElem.mul_projectionIntertwiner_eq_projectionIntertwiner_mul
          hq.isIdempotentElem]
    _ = projectionIntertwiner p q * (cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2) * p) := by
        rw [mul_assoc, hp_comm.eq]
    _ = (projectionIntertwiner p q * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2)) * p := by
        rw [← mul_assoc]

/-- Conjugating `p` by `hp.projectionConjugacyUnitary hq h` yields `q`. -/
theorem conjugate_projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    (hp.projectionConjugacyUnitary hq h : A) * p *
        star (hp.projectionConjugacyUnitary hq h : A) = q := by
  rw [← hp.mul_projectionConjugacyUnitary hq h, mul_assoc,
    Unitary.mul_star_self_of_mem (hp.projectionConjugacyUnitary hq h).2, mul_one]

/-- Quantitative distance estimate `‖u - 1‖ ≤ √2 * ‖p - q‖` for
`IsStarProjection.projectionConjugacyUnitary`. -/
theorem norm_projectionConjugacyUnitary_sub_one_le (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ‖(hp.projectionConjugacyUnitary hq h : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  set u := hp.projectionConjugacyUnitary hq h
  set z := projectionIntertwiner p q
  set a := 1 - (p - q) ^ 2
  set f : ℝ → ℝ := fun x ↦ (√x)⁻¹
  set w := cfc f a
  have ha : IsSelfAdjoint a :=
    (IsSelfAdjoint.one A).sub ((hp.isSelfAdjoint.sub hq.isSelfAdjoint).pow 2)
  have hf_cont : ContinuousOn f (spectrum ℝ a) :=
    hp.continuousOn_inv_sqrt_one_sub_sub_sq hq h
  have hw_sa : IsSelfAdjoint w := cfc_predicate f a
  have hz_comm_w : Commute z w :=
    ((hp.isIdempotentElem.commute_projectionIntertwiner_one_sub_sub_sq
      hq.isIdempotentElem).symm.cfc_real f).symm
  have hstar_z_comm_w : star z * w = w * star z := by
    simpa [star_mul, hw_sa.star_eq] using congrArg star hz_comm_w.eq.symm
  have hu_add : (u : A) + star (u : A) = cfc (fun x : ℝ ↦ 2 * √x) a := by
    have hzw : (u : A) + star (u : A) = (2 • a) * w := by
      have hu_eq : (u : A) = z * w := hp.coe_projectionConjugacyUnitary hq h
      calc (u : A) + star (u : A)
          = z * w + w * star z := by rw [hu_eq, star_mul, hw_sa.star_eq]
        _ = (z + star z) * w := by rw [← hstar_z_comm_w, add_mul]
        _ = (2 • a) * w := by rw [hp.projectionIntertwiner_add_star hq]
    have h2a : (2 : ℝ) • a = (2 : ℕ) • a := by norm_cast
    rw [hzw, ← h2a, smul_mul_assoc]
    have haw : a * w = cfc Real.sqrt a := by
      conv_lhs => rw [(cfc_id' ℝ a ha).symm]
      rw [← cfc_mul (fun x : ℝ ↦ x) f a continuousOn_id hf_cont]
      refine cfc_congr fun x hx ↦ ?_
      have hx_pos : 0 < x := (hp.spectrum_one_sub_sub_sq_bounds hq h hx).1
      have hsqrt_ne : √x ≠ 0 := (Real.sqrt_pos.mpr hx_pos).ne'
      dsimp [f]
      calc x * (√x)⁻¹ = (√x * √x) * (√x)⁻¹ := by rw [Real.mul_self_sqrt hx_pos.le]
        _ = √x * (√x * (√x)⁻¹) := by ring
        _ = √x := by rw [mul_inv_cancel₀ hsqrt_ne, mul_one]
    rw [haw, ← cfc_smul (2 : ℝ) Real.sqrt a Real.continuous_sqrt.continuousOn]
    rfl
  have hstar_sub :
      star ((u : A) - 1) * ((u : A) - 1) = cfc (fun x : ℝ ↦ 2 * (1 - √x)) a := by
    have hexpand : star ((u : A) - 1) * ((u : A) - 1) = (2 : A) - ((u : A) + star (u : A)) := by
      calc star ((u : A) - 1) * ((u : A) - 1)
          = star (u : A) * (u : A) + 1 - ((u : A) + star (u : A)) := by
              rw [star_sub, star_one]; noncomm_ring
        _ = (2 : A) - ((u : A) + star (u : A)) := by
              rw [Unitary.star_mul_self_of_mem u.2, one_add_one_eq_two]
    have h2 : (2 : A) = cfc (fun _ : ℝ ↦ (2 : ℝ)) a := by
      rw [cfc_const (2 : ℝ) a ha, Algebra.algebraMap_eq_smul_one, two_smul, one_add_one_eq_two]
    rw [hexpand, h2, hu_add, ← cfc_sub (fun _ : ℝ ↦ (2 : ℝ)) (fun x : ℝ ↦ 2 * √x) a
      continuousOn_const (continuous_const.mul Real.continuous_sqrt).continuousOn]
    exact cfc_congr fun x _ ↦ by ring
  have hnorm_sq : ‖(u : A) - 1‖ ^ 2 ≤ (√2 * ‖p - q‖) ^ 2 := by
    rw [sq, ← CStarRing.norm_star_mul_self, hstar_sub, mul_pow, Real.sq_sqrt (by positivity)]
    refine norm_cfc_le (by positivity) fun x hx ↦ ?_
    obtain ⟨hx_pos, hx_le_one, h1x⟩ := hp.spectrum_one_sub_sub_sq_bounds hq h hx
    have hsqrt_le_one : √x ≤ 1 := Real.sqrt_le_one.mpr hx_le_one
    have h1sqrt_nonneg : 0 ≤ 1 - √x := sub_nonneg.mpr hsqrt_le_one
    have h1sqrt_le : 1 - √x ≤ 1 - x := by
      calc 1 - √x ≤ (1 - √x) * (1 + √x) :=
            le_mul_of_one_le_right h1sqrt_nonneg (by linarith [Real.sqrt_nonneg x])
        _ = 1 - √x * √x := by ring
        _ = 1 - x := by rw [Real.mul_self_sqrt hx_pos.le]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hnorm_sq

/-- `hp.projectionConjugacyUnitary hq h` lies in the path component of `1` in `unitary A`. -/
theorem joined_one_projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    Joined 1 (hp.projectionConjugacyUnitary hq h) := by
  refine Unitary.joined 1 (hp.projectionConjugacyUnitary hq h) ?_
  have hle := hp.norm_projectionConjugacyUnitary_sub_one_le hq h
  have hsqrt2 : √2 < 2 := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  calc ‖((hp.projectionConjugacyUnitary hq h : A) - (1 : unitary A))‖
      = ‖(hp.projectionConjugacyUnitary hq h : A) - 1‖ := rfl
    _ ≤ √2 * ‖p - q‖ := hle
    _ < √2 * 1 := mul_lt_mul_of_pos_left h (by positivity)
    _ < 2 := by linarith

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

/-- **Unitary conjugacy of nearby projections in a non-unital C⋆-algebra**: if `p` and `q` are star
projections in `A` with `‖p - q‖ < 1`, there exists `u : unitary (Unitization ℂ A)` with scalar
part `(u : Unitization ℂ A).fst = 1`, `Joined 1 u`,
`(u : Unitization ℂ A) * (p : Unitization ℂ A) * star (u : Unitization ℂ A) =
  (q : Unitization ℂ A)`, and `‖(u : Unitization ℂ A) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_unitization_unitary_conjugate_of_norm_sub_lt_one {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    ∃ u : unitary (Unitization ℂ A),
      (u : Unitization ℂ A).fst = 1 ∧
      Joined 1 u ∧
      (u : Unitization ℂ A) * (p : Unitization ℂ A) * star (u : Unitization ℂ A) =
        (q : Unitization ℂ A) ∧
      ‖(u : Unitization ℂ A) - 1‖ ≤ √2 * ‖p - q‖ := by
  have hp' : IsStarProjection (p : Unitization ℂ A) :=
    hp.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hq' : IsStarProjection (q : Unitization ℂ A) :=
    hq.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hnorm_eq : ‖(p : Unitization ℂ A) - (q : Unitization ℂ A)‖ = ‖p - q‖ := by
    rw [← Unitization.inr_sub, Unitization.norm_inr]
  have h' : ‖(p : Unitization ℂ A) - (q : Unitization ℂ A)‖ < 1 := hnorm_eq.symm ▸ h
  refine ⟨hp'.projectionConjugacyUnitary hq' h', ?_,
    hp'.joined_one_projectionConjugacyUnitary hq' h',
    hp'.conjugate_projectionConjugacyUnitary hq' h',
    hnorm_eq ▸ hp'.norm_projectionConjugacyUnitary_sub_one_le hq' h'⟩
  -- Show the scalar component of `projectionConjugacyElem (p : A⁺¹) (q : A⁺¹)` is `1`.
  rw [coe_projectionConjugacyUnitary, projectionConjugacyElem_def, Unitization.fst_mul]
  have hzfst : (projectionIntertwiner (p : Unitization ℂ A) (q : Unitization ℂ A)).fst = 1 := by
    simp [projectionIntertwiner_def]
  have hwfst :
      (cfc (fun x : ℝ ↦ (√x)⁻¹)
        (1 - ((p : Unitization ℂ A) - (q : Unitization ℂ A)) ^ 2)).fst = 1 := by
    set d : A := p - q
    have hd : IsSelfAdjoint d := hp.isSelfAdjoint.sub hq.isSelfAdjoint
    have hd_inr : IsSelfAdjoint (d : Unitization ℂ A) :=
      hd.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
    have ha_eq :
        (1 : Unitization ℂ A) - ((p : Unitization ℂ A) - (q : Unitization ℂ A)) ^ 2 =
          cfc (fun t : ℝ ↦ 1 - t ^ 2) (d : Unitization ℂ A) := by
      rw [← Unitization.inr_sub,
        cfc_sub (fun _ : ℝ ↦ (1 : ℝ)) (fun t : ℝ ↦ t ^ 2) (d : Unitization ℂ A),
        cfc_const_one ℝ (d : Unitization ℂ A) hd_inr,
        cfc_pow (fun t : ℝ ↦ t) 2 (d : Unitization ℂ A),
        cfc_id' ℝ (d : Unitization ℂ A) hd_inr]
    have hg_cont :
        ContinuousOn (fun x : ℝ ↦ (√x)⁻¹)
          ((fun t : ℝ ↦ 1 - t ^ 2) '' spectrum ℝ (d : Unitization ℂ A)) := by
      rw [← cfc_map_spectrum (fun t : ℝ ↦ 1 - t ^ 2) (d : Unitization ℂ A) hd_inr
        (continuous_const.sub (continuous_pow 2)).continuousOn, ← ha_eq]
      exact hp'.continuousOn_inv_sqrt_one_sub_sub_sq hq' h'
    rw [ha_eq, ← cfc_comp' (fun x : ℝ ↦ (√x)⁻¹) (fun t : ℝ ↦ 1 - t ^ 2) (d : Unitization ℂ A)
      hg_cont (continuous_const.sub (continuous_pow 2)).continuousOn hd_inr]
    have hsplit :
        cfc (fun t : ℝ ↦ (√(1 - t ^ 2))⁻¹) (d : Unitization ℂ A) =
          1 + cfc (fun t : ℝ ↦ (√(1 - t ^ 2))⁻¹ - 1) (d : Unitization ℂ A) := by
      have hcont_sub :
          ContinuousOn (fun t : ℝ ↦ (√(1 - t ^ 2))⁻¹ - 1)
            (spectrum ℝ (d : Unitization ℂ A)) :=
        (hg_cont.comp (continuous_const.sub (continuous_pow 2)).continuousOn
          (Set.mapsTo_image _ _)).sub continuousOn_const
      rw [show (fun t : ℝ ↦ (√(1 - t ^ 2))⁻¹) =
          (fun t : ℝ ↦ (1 : ℝ) + ((√(1 - t ^ 2))⁻¹ - 1)) by ext; ring,
        cfc_const_add (1 : ℝ) (fun t : ℝ ↦ (√(1 - t ^ 2))⁻¹ - 1) (d : Unitization ℂ A)
          hcont_sub hd_inr, map_one]
    rw [hsplit, ← Unitization.real_cfcₙ_eq_cfc_inr d (fun t : ℝ ↦ (√(1 - t ^ 2))⁻¹ - 1) (by simp)]
    simp
  rw [hzfst, hwfst, mul_one]

end NonUnital

end IsStarProjection
