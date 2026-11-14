/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.Projection.Intertwiner
public import TauCeti.Analysis.CStarAlgebra.Unitary.Polar

/-!
# Unitary conjugacy of nearby projections in a C⋆-algebra

To show that homotopy equivalence, Murray–von Neumann equivalence, and unitary equivalence coincide
on nearby projections—and that `K₀` classes are locally constant along norm-convergent families or
inductive limits—one upgrades Kato's algebraic intertwiner `projectionIntertwiner p q` to an honest
unitary via polar decomposition whenever two star projections satisfy `‖p - q‖ < 1`.

Because `star z * z = 1 - (p - q) ^ 2 = z * star z` for `z = projectionIntertwiner p q`, the bound
`‖p - q‖ < 1` forces `z` to be invertible in any Banach algebra. In a unital C⋆-algebra `A`, its
polar unitary `u = hp.projectionConjugacyUnitary hq h : unitary A` satisfies
`(u : A) * p * star (u : A) = q`, lies in the path component of `1` (`Joined 1 u`), obeys the sharp
chord-arc estimate `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`, and belongs to every closed unital
`𝕜'`-`⋆`-subalgebra (for any scalar action `𝕜'` over `ℝ`, including both real and complex
C⋆-subalgebras) containing `p` and `q`. Passing to `Unitization ℂ A` yields, for any non-unital
C⋆-algebra `A`, a conjugating unitary with scalar part `(u : Unitization ℂ A).fst = 1`.

## Main definitions

* `IsStarProjection.projectionConjugacyUnitary`: the Kato–Sz.-Nagy unitary conjugating `p` to `q`
  when `‖p - q‖ < 1`.

## Main statements

* `IsIdempotentElem.isUnit_projectionIntertwiner`: `projectionIntertwiner p q` is invertible in a
  Banach ring whenever idempotents `p, q` satisfy `‖p - q‖ < 1`.
* `IsStarProjection.projectionConjugacyUnitary_mem`,
  `IsStarProjection.conjugate_projectionConjugacyUnitary`,
  `IsStarProjection.norm_projectionConjugacyUnitary_sub_one_le`,
  `IsStarProjection.joined_one_projectionConjugacyUnitary`.
* `IsStarProjection.exists_unitary_conjugate_mem_of_norm_sub_lt_one`,
  `IsStarProjection.exists_unitary_conjugate_of_norm_sub_lt_one`,
  `IsStarProjection.exists_unitization_unitary_conjugate_of_norm_sub_lt_one`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1966), Chapter I, §4.6.
* B. Blackadar, *Operator Algebras*, Springer (2006), Section II.3.3.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge Univ. Press (1998), 4.6.6.
-/

public section

open TauCeti
open scoped ContinuousFunctionalCalculus Real

namespace IsIdempotentElem

/-- In a complete normed ring, Kato's intertwiner `projectionIntertwiner p q` between two
idempotents `p, q` with `‖p - q‖ < 1` is invertible. -/
theorem isUnit_projectionIntertwiner {R : Type*} [NormedRing R] [CompleteSpace R] {p q : R}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (h : ‖p - q‖ < 1) :
    IsUnit (projectionIntertwiner p q) := by
  have hsq : ‖(p - q) ^ 2‖ < 1 := by
    rw [sq]
    exact (norm_mul_le _ _).trans_lt (by nlinarith [norm_nonneg (p - q)])
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hsq
  have hr : projectionIntertwiner p q * (projectionIntertwiner q p * ↑u⁻¹) = 1 := by
    rw [← mul_assoc, hp.projectionIntertwiner_mul_swap hq, ← hu, Units.mul_inv]
  have hl : (↑u⁻¹ * projectionIntertwiner q p) * projectionIntertwiner p q = 1 := by
    rw [mul_assoc, hp.projectionIntertwiner_swap_mul_self hq, ← hu, Units.inv_mul]
  exact isUnit_iff_exists.mpr ⟨_, hr, left_inv_eq_right_inv hl hr ▸ hl⟩

end IsIdempotentElem

namespace IsStarProjection

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

private theorem mul_cfc_inv_sqrt_one_sub_sub_sq (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : (1 - (p - q) ^ 2) * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2) =
      cfc Real.sqrt (1 - (p - q) ^ 2) := by
  set a := 1 - (p - q) ^ 2
  have ha : IsSelfAdjoint a :=
    (IsSelfAdjoint.one A).sub ((hp.isSelfAdjoint.sub hq.isSelfAdjoint).pow 2)
  have hcont : ContinuousOn (fun x : ℝ ↦ (√x)⁻¹) (spectrum ℝ a) :=
    Real.continuous_sqrt.continuousOn.inv₀ fun _ hx ↦
      (Real.sqrt_pos.mpr (hp.spectrum_one_sub_sub_sq_bounds hq h hx).1).ne'
  conv_lhs => lhs; rw [(cfc_id' ℝ a ha).symm]
  rw [← cfc_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ (√x)⁻¹) a continuousOn_id hcont]
  refine cfc_congr fun x hx ↦ ?_
  have hx_pos := (hp.spectrum_one_sub_sub_sq_bounds hq h hx).1
  conv_lhs => lhs; rw [← Real.mul_self_sqrt hx_pos.le]
  rw [mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr hx_pos).ne', mul_one]

/-- **Kato–Sz.-Nagy conjugating unitary** for two star projections `p, q` in a unital C⋆-algebra
satisfying `‖p - q‖ < 1`, defined as the polar unitary of `projectionIntertwiner p q`. -/
noncomputable def projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : unitary A :=
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  (hp.isIdempotentElem.isUnit_projectionIntertwiner hq.isIdempotentElem h).unit.polarUnitary

/-- Functional-calculus formula for `IsStarProjection.projectionConjugacyUnitary`: its coercion is
`projectionIntertwiner p q * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2)`. -/
theorem coe_projectionConjugacyUnitary (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    (hp.projectionConjugacyUnitary hq h : A) =
      projectionIntertwiner p q * cfc (fun x : ℝ ↦ (√x)⁻¹) (1 - (p - q) ^ 2) := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  rw [projectionConjugacyUnitary, Units.coe_polarUnitary_eq_mul_cfc_inv_sqrt, IsUnit.unit_spec,
    hp.star_projectionIntertwiner_mul_self hq]

/-- The Kato–Sz.-Nagy unitary of a projection `p` with itself is `1`. -/
@[simp] theorem projectionConjugacyUnitary_self (hp : IsStarProjection p) (h : ‖p - p‖ < 1) :
    hp.projectionConjugacyUnitary hp h = 1 := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  rw [projectionConjugacyUnitary]
  have hu : (hp.isIdempotentElem.isUnit_projectionIntertwiner hp.isIdempotentElem h).unit = 1 :=
    Units.ext <| by rw [IsUnit.unit_spec, hp.isIdempotentElem.projectionIntertwiner_self,
      Units.val_one]
  rw [hu, Units.polarUnitary_one]

/-- `hp.projectionConjugacyUnitary hq h` belongs to every closed unital `𝕜'`-`⋆`-subalgebra
(for any scalar action `𝕜'` over `ℝ`, including `ℝ` and `ℂ`) containing `p` and `q`. -/
theorem projectionConjugacyUnitary_mem {𝕜' S : Type*} [Monoid 𝕜'] [MulAction 𝕜' A] [SetLike S A]
    [SubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A] [SMulMemClass S 𝕜' A]
    [StarMemClass S A] {s : S} [IsClosed (s : Set A)] (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) (hp_mem : p ∈ s) (hq_mem : q ∈ s) :
    (hp.projectionConjugacyUnitary hq h : A) ∈ s := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  rw [projectionConjugacyUnitary]
  exact Units.polarUnitary_mem (𝕜' := 𝕜') _ <| by
    rw [IsUnit.unit_spec]
    exact projectionIntertwiner_mem hp_mem hq_mem

/-- Unital `⋆`-ring homomorphisms between C⋆-algebras preserve
`IsStarProjection.projectionConjugacyUnitary`. -/
theorem map_projectionConjugacyUnitary {B F : Type*} [CStarAlgebra B] [FunLike F A B]
    [RingHomClass F A B] [StarHomClass F A B] (φ : F) (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) (hφ : ‖φ p - φ q‖ < 1) :
    (((hp.map φ).projectionConjugacyUnitary (hq.map φ) hφ : unitary B) : B) =
      φ (hp.projectionConjugacyUnitary hq h : A) := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  let _ := CStarAlgebra.spectralOrder B
  let _ := CStarAlgebra.spectralOrderedRing B
  set u := (hp.isIdempotentElem.isUnit_projectionIntertwiner hq.isIdempotentElem h).unit
  set u' := ((hp.map φ).isIdempotentElem.isUnit_projectionIntertwiner
    (hq.map φ).isIdempotentElem hφ).unit
  have hu' : u' = Units.map (φ : A →* B) u := Units.ext <| by
    simp only [u', u, Units.coe_map, MonoidHom.coe_ofClass, IsUnit.unit_spec,
      map_projectionIntertwiner]
  rw [projectionConjugacyUnitary, projectionConjugacyUnitary,
    show ((hp.map φ).isIdempotentElem.isUnit_projectionIntertwiner
      (hq.map φ).isIdempotentElem hφ).unit = Units.map (φ : A →* B) u from hu']
  exact u.map_polarUnitary φ

/-- Intertwining identity `q * u = u * p` for `IsStarProjection.projectionConjugacyUnitary`. -/
theorem mul_projectionConjugacyUnitary_eq_projectionConjugacyUnitary_mul
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    q * (hp.projectionConjugacyUnitary hq h : A) =
      (hp.projectionConjugacyUnitary hq h : A) * p := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  rw [projectionConjugacyUnitary]
  refine Units.mul_polarUnitary_eq_polarUnitary_mul _ ?_ ?_
  · rw [IsUnit.unit_spec]
    exact hp.isIdempotentElem.mul_projectionIntertwiner_eq_projectionIntertwiner_mul
      hq.isIdempotentElem
  · rw [IsUnit.unit_spec, star_projectionIntertwiner, hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq]
    exact (hq.isIdempotentElem.mul_projectionIntertwiner_eq_projectionIntertwiner_mul
      hp.isIdempotentElem).symm

/-- Conjugating `p` by `hp.projectionConjugacyUnitary hq h` yields `q`. -/
@[simp] theorem conjugate_projectionConjugacyUnitary (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    (hp.projectionConjugacyUnitary hq h : A) * p *
        star (hp.projectionConjugacyUnitary hq h : A) = q := by
  rw [← hp.mul_projectionConjugacyUnitary_eq_projectionConjugacyUnitary_mul hq h, mul_assoc,
    Unitary.mul_star_self_of_mem (hp.projectionConjugacyUnitary hq h).2, mul_one]

/-- Quantitative distance estimate `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖` for
`u = hp.projectionConjugacyUnitary hq h`. -/
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
  have hw_sa : IsSelfAdjoint w := cfc_predicate f a
  have hz_comm_w : Commute z w :=
    ((hp.isIdempotentElem.commute_projectionIntertwiner_one_sub_sub_sq
      hq.isIdempotentElem).symm.cfc_real f).symm
  have hstar_z_comm_w : star z * w = w * star z := by
    simpa [star_mul, hw_sa.star_eq] using congrArg star hz_comm_w.eq.symm
  have hu_coe : (u : A) = z * w := hp.coe_projectionConjugacyUnitary hq h
  have hu_add : (u : A) + star (u : A) = cfc (fun x : ℝ ↦ 2 * √x) a := by
    rw [hu_coe, star_mul, hw_sa.star_eq, ← hstar_z_comm_w, ← add_mul,
      hp.projectionIntertwiner_add_star hq, ← Nat.cast_smul_eq_nsmul ℝ 2 a, Nat.cast_ofNat,
      smul_mul_assoc, hp.mul_cfc_inv_sqrt_one_sub_sub_sq hq h,
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

/-- **Unitary conjugacy of nearby projections in a closed unital `⋆`-subalgebra**: if star
projections `p, q` in a closed unital `𝕜'`-`⋆`-subalgebra `s` satisfy `‖p - q‖ < 1`, there exists
`u : unitary A` with `(u : A) ∈ s`, `Joined 1 u`, `(u : A) * p * star (u : A) = q`, and
`‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_unitary_conjugate_mem_of_norm_sub_lt_one {𝕜' S : Type*} [Monoid 𝕜']
    [MulAction 𝕜' A] [SetLike S A] [SubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A]
    [SMulMemClass S 𝕜' A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hp_mem : p ∈ s) (hq_mem : q ∈ s)
    (h : ‖p - q‖ < 1) :
    ∃ u : unitary A, (u : A) ∈ s ∧ Joined 1 u ∧ (u : A) * p * star (u : A) = q ∧
      ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ :=
  ⟨hp.projectionConjugacyUnitary hq h,
    hp.projectionConjugacyUnitary_mem (𝕜' := 𝕜') hq h hp_mem hq_mem,
    hp.joined_one_projectionConjugacyUnitary hq h,
    hp.conjugate_projectionConjugacyUnitary hq h,
    hp.norm_projectionConjugacyUnitary_sub_one_le hq h⟩

/-- **Unitary conjugacy of nearby projections** in a unital C⋆-algebra: if star projections `p, q`
satisfy `‖p - q‖ < 1`, there exists `u : unitary A` with `Joined 1 u`,
`(u : A) * p * star (u : A) = q`, and `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_unitary_conjugate_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = q ∧
      ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  have : IsClosed ((⊤ : StarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨u, -, hjoined, hconj, hnorm⟩ :=
    hp.exists_unitary_conjugate_mem_of_norm_sub_lt_one (s := (⊤ : StarSubalgebra ℂ A)) hq
      trivial trivial h
  exact ⟨u, hjoined, hconj, hnorm⟩

end Unital

section NonUnital

/-- If star projections `p, q : Unitization ℂ A` with `‖p - q‖ < 1` have equal scalar parts
`p.fst = q.fst`, then `(hp.projectionConjugacyUnitary hq h : Unitization ℂ A).fst = 1`. -/
theorem fst_projectionConjugacyUnitary {A : Type*} [NonUnitalCStarAlgebra A]
    {p q : Unitization ℂ A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) (hfst : p.fst = q.fst) :
    (hp.projectionConjugacyUnitary hq h : Unitization ℂ A).fst = 1 := by
  let _ := CStarAlgebra.spectralOrder (Unitization ℂ A)
  let _ := CStarAlgebra.spectralOrderedRing (Unitization ℂ A)
  rw [projectionConjugacyUnitary]
  refine Units.fst_polarUnitary ?_
  rw [IsUnit.unit_spec, ← Unitization.fstHom_apply ℂ A, map_projectionIntertwiner,
    Unitization.fstHom_apply, Unitization.fstHom_apply, ← hfst]
  exact (hp.isIdempotentElem.map (Unitization.fstHom ℂ A)).projectionIntertwiner_self

/-- **Unitary conjugacy of nearby projections in a non-unital C⋆-algebra**: if star projections
`p, q` in a non-unital C⋆-algebra `A` satisfy `‖p - q‖ < 1`, there exists
`u : unitary (Unitization ℂ A)` with `(u : Unitization ℂ A).fst = 1`, `Joined 1 u`,
`(u : Unitization ℂ A) * p * star (u : Unitization ℂ A) = q`, and
`‖(u : Unitization ℂ A) - 1‖ ≤ √2 * ‖p - q‖`. -/
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
  exact ⟨hp'.projectionConjugacyUnitary hq' h',
    hp'.fst_projectionConjugacyUnitary hq' h' (by simp),
    hp'.joined_one_projectionConjugacyUnitary hq' h',
    hp'.conjugate_projectionConjugacyUnitary hq' h',
    hnorm_eq ▸ hp'.norm_projectionConjugacyUnitary_sub_one_le hq' h'⟩

end NonUnital

end IsStarProjection
