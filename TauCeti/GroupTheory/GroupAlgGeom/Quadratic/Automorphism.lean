/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Automorphism
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic

/-!
# Quadratic words under elementary automorphisms

Up to conjugation in `G[X]`, a product of elementary `G`-automorphisms of `G[X]` brings a strictly
quadratic word over a group `G` either to a coefficient or to a standard quadratic word ([IFT],
§2.7, Lemma 1). This file records how the elementary `G`-automorphisms of `G[X]` act on the number
of occurrences of a variable, and hence on quadratic and strictly quadratic systems.

Renaming the variables, inverting a variable and multiplying a variable by coefficients preserve
all occurrence counts, so they preserve quadratic and strictly quadratic systems. A transvection
`x ↦ a x b` preserves the number of occurrences of `x`, and of every variable occurring neither
in `a` nor in `b`, but it may increase the other counts: `x ↦ x y` sends the quadratic word
`x² y²` to `(x y)² y²`, in which `y` occurs four times (`not_isQuadratic_transvection`). The
reduction to standard form therefore uses transvections only in combinations that keep the word
quadratic. For instance the transvection `x ↦ x y⁻¹` followed by the inversion of `y` carries the
Klein bottle word `x y x y⁻¹` to the standard word `x² y²` of the same length
(`exists_standard_kleinBottle`).

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.mem_avoiding_iff_occurrences_eq_zero`: `GX.avoiding x` consists
  of the words with no occurrence of `x`.
* `occurrences_renameEquiv`, `occurrences_invertVar`, `occurrences_transvection`: the occurrence
  counts preserved by the elementary automorphisms.
* `isQuadratic_map_renameEquiv`, `isQuadratic_map_invertVar`, `isQuadratic_map_transvection` and
  their strictly quadratic analogues: renaming, inverting a variable and multiplying a variable by
  coefficients preserve (strictly) quadratic systems.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definition 2 and Lemma 1.
-/

public section

open Monoid.Coprod Function

namespace TauCeti.GroupAlgGeom.Quadratic

variable {G X Y : Type*} [Group G]

/-! ### Words in which a variable does not occur -/

section Avoiding

variable [DecidableEq X] {x : X} {a b : GX G X}

/-- The variable `x` does not occur in a word after the substitution `x ↦ 1`. -/
@[simp]
theorem occurrences_eval_update_one (x : X) (w : GX G X) :
    occurrences x (eval inl (update (fun y => inr (FreeGroup.of y)) x 1) w) = 0 := by
  refine occurrences_map_eq_zero _ x (by simp) (fun y => ?_) w
  by_cases h : y = x
  · subst h; simp
  · simp [h]

/-- The words of `GX.avoiding x` are the words in which `x` does not occur. -/
theorem mem_avoiding_iff_occurrences_eq_zero : a ∈ GX.avoiding x ↔ occurrences x a = 0 := by
  classical
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · rw [← GX.mem_avoiding.1 ha, occurrences_eval_update_one]
  · have h := le_occurrences x
      (fun u => if u ∈ GX.avoiding x then 0 else 1)
      (fun u v => by
        by_cases hu : u ∈ GX.avoiding x
        · by_cases hv : v ∈ GX.avoiding x
          · simp [hu, hv, mul_mem hu hv]
          · simp only [hv, ite_false]; split_ifs <;> omega
        · simp only [hu, ite_false]; split_ifs <;> omega)
      (by simp) (by split_ifs <;> simp) (by split_ifs <;> simp)
      (fun y hy => by simp [hy]) a
    by_contra ha'
    simp [ha, ha'] at h

end Avoiding

/-! ### Occurrences under the elementary automorphisms -/

section Elementary

private theorem occurrences_renameEquiv_le (e : X ≃ Y) (y : Y) (w : GX G X) :
    occurrences y (GX.renameEquiv G e w) ≤ occurrences (e.symm y) w := by
  refine occurrences_map_le _ (e.symm y) y (by simp) (by simp) (fun z hz => ?_) w
  rw [GX.renameEquiv_inr_of, occurrences_inr_of_of_ne]
  rintro rfl
  simp at hz

/-- Renaming the variables renames the occurrence counts. -/
@[simp]
theorem occurrences_renameEquiv (e : X ≃ Y) (y : Y) (w : GX G X) :
    occurrences y (GX.renameEquiv G e w) = occurrences (e.symm y) w := by
  refine (occurrences_renameEquiv_le e y w).antisymm ?_
  simpa [← GX.renameEquiv_symm] using
    occurrences_renameEquiv_le e.symm (e.symm y) (GX.renameEquiv G e w)

variable [DecidableEq X] {x : X} {a b : GX G X}

private theorem occurrences_invertVar_le (x y : X) (w : GX G X) :
    occurrences y (GX.invertVar G x w) ≤ occurrences y w := by
  refine occurrences_map_le _ y y (by simp) ?_ (fun z hz => ?_) w
  · by_cases h : y = x
    · subst h; simp
    · simp [h]
  · by_cases h : z = x
    · subst h; simp [occurrences_inr_of_of_ne hz]
    · simp [h, occurrences_inr_of_of_ne hz]

/-- Inverting a variable preserves all occurrence counts. -/
@[simp]
theorem occurrences_invertVar (x y : X) (w : GX G X) :
    occurrences y (GX.invertVar G x w) = occurrences y w := by
  refine (occurrences_invertVar_le x y w).antisymm ?_
  simpa [← MulAut.mul_apply] using occurrences_invertVar_le x y (GX.invertVar G x w)

private theorem occurrences_transvection_le (ha : a ∈ GX.avoiding x) (hb : b ∈ GX.avoiding x)
    {y : X} (hya : occurrences y a = 0) (hyb : occurrences y b = 0) (w : GX G X) :
    occurrences y (GX.transvection x a b ha hb w) ≤ occurrences y w := by
  have key : ∀ u : GX G X, occurrences y (a * u * b) ≤ occurrences y u := fun u => by
    have h₁ := occurrences_mul_le y (a * u) b
    have h₂ := occurrences_mul_le y a u
    omega
  refine occurrences_map_le _ y y (by simp) ?_ (fun z hz => ?_) w
  · by_cases h : y = x
    · subst h; simpa using key (inr (FreeGroup.of y))
    · simp [h]
  · by_cases h : z = x
    · subst h; simpa [occurrences_inr_of_of_ne hz] using key (inr (FreeGroup.of z))
    · simp [h, occurrences_inr_of_of_ne hz]

/-- The transvection `x ↦ a x b` preserves the number of occurrences of every variable occurring
neither in `a` nor in `b`. -/
@[simp]
theorem occurrences_transvection (ha : a ∈ GX.avoiding x) (hb : b ∈ GX.avoiding x) {y : X}
    (hya : occurrences y a = 0) (hyb : occurrences y b = 0) (w : GX G X) :
    occurrences y (GX.transvection x a b ha hb w) = occurrences y w := by
  refine (occurrences_transvection_le ha hb hya hyb w).antisymm ?_
  have h := occurrences_transvection_le (inv_mem ha) (inv_mem hb) (y := y) (by simpa) (by simpa)
    (GX.transvection x a b ha hb w)
  rwa [← GX.transvection_inv, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h

/-- The transvection `x ↦ a x b` preserves the number of occurrences of `x`. -/
@[simp]
theorem occurrences_transvection_self (ha : a ∈ GX.avoiding x) (hb : b ∈ GX.avoiding x)
    (w : GX G X) : occurrences x (GX.transvection x a b ha hb w) = occurrences x w :=
  occurrences_transvection ha hb (mem_avoiding_iff_occurrences_eq_zero.1 ha)
    (mem_avoiding_iff_occurrences_eq_zero.1 hb) w

end Elementary

/-! ### Quadratic systems under the elementary automorphisms -/

section IsQuadratic

variable {S : Finset (GX G X)}

/-- Renaming the variables preserves quadratic systems. -/
@[simp]
theorem isQuadratic_map_renameEquiv (e : X ≃ Y) :
    IsQuadratic (S.map (GX.renameEquiv G e : GX G X ≃ GX G Y).toEmbedding) ↔ IsQuadratic S :=
  isQuadratic_map_iff _ e fun x w _ => by simp

/-- Renaming the variables preserves strictly quadratic systems. -/
@[simp]
theorem isStrictlyQuadratic_map_renameEquiv (e : X ≃ Y) :
    IsStrictlyQuadratic (S.map (GX.renameEquiv G e : GX G X ≃ GX G Y).toEmbedding) ↔
      IsStrictlyQuadratic S :=
  isStrictlyQuadratic_map_iff _ e fun x w _ => by simp

variable [DecidableEq X] {x : X} {a b : GX G X}

/-- Inverting a variable preserves quadratic systems. -/
@[simp]
theorem isQuadratic_map_invertVar (x : X) :
    IsQuadratic (S.map (GX.invertVar G x : GX G X ≃ GX G X).toEmbedding) ↔ IsQuadratic S :=
  isQuadratic_map_iff _ (.refl X) fun y w _ => occurrences_invertVar x y w

/-- Inverting a variable preserves strictly quadratic systems. -/
@[simp]
theorem isStrictlyQuadratic_map_invertVar (x : X) :
    IsStrictlyQuadratic (S.map (GX.invertVar G x : GX G X ≃ GX G X).toEmbedding) ↔
      IsStrictlyQuadratic S :=
  isStrictlyQuadratic_map_iff _ (.refl X) fun y w _ => occurrences_invertVar x y w

/-- Multiplying a variable on either side by words in which no variable occurs, that is by
coefficients, preserves quadratic systems. -/
@[simp]
theorem isQuadratic_map_transvection (ha : a ∈ GX.avoiding x) (hb : b ∈ GX.avoiding x)
    (ha₀ : ∀ y, occurrences y a = 0) (hb₀ : ∀ y, occurrences y b = 0) :
    IsQuadratic (S.map (GX.transvection x a b ha hb : GX G X ≃ GX G X).toEmbedding) ↔
      IsQuadratic S :=
  isQuadratic_map_iff _ (.refl X) fun y w _ => occurrences_transvection ha hb (ha₀ y) (hb₀ y) w

/-- Multiplying a variable on either side by words in which no variable occurs, that is by
coefficients, preserves strictly quadratic systems. -/
@[simp]
theorem isStrictlyQuadratic_map_transvection (ha : a ∈ GX.avoiding x) (hb : b ∈ GX.avoiding x)
    (ha₀ : ∀ y, occurrences y a = 0) (hb₀ : ∀ y, occurrences y b = 0) :
    IsStrictlyQuadratic (S.map (GX.transvection x a b ha hb : GX G X ≃ GX G X).toEmbedding) ↔
      IsStrictlyQuadratic S :=
  isStrictlyQuadratic_map_iff _ (.refl X) fun y w _ =>
    occurrences_transvection ha hb (ha₀ y) (hb₀ y) w

end IsQuadratic

/-! ### Examples -/

section Examples

/-- The Klein bottle word `x y x y⁻¹` is equivalent to the standard non-orientable word `x² y²`
of genus `2`: the transvection `x ↦ x y⁻¹` followed by the inversion of `y` carries the one to
the other. -/
theorem exists_standard_kleinBottle :
    ∃ S : Standard G (Fin 2), ¬S.IsOrientable ∧ S.genus = 2 ∧
      (GX.invertVar G 1 * GX.transvection 0 1 (inr (.of 1))⁻¹ (one_mem _) (by simp) :
          MulAut (GX G (Fin 2)))
        (inr (.of 0) * inr (.of 1) * inr (.of 0) * (inr (.of 1))⁻¹) = S.toWord :=
  ⟨.nonorientable 2 Nat.two_pos id injective_id, by simp, by simp, by
    simp [Standard.toWord_def, List.ofFn_succ, mul_assoc, pow_two]⟩

/-- Transvections do not preserve quadratic words in general: `x ↦ x y` sends the quadratic word
`x² y²` to `(x y)² y²`, in which `y` occurs four times. -/
theorem not_isQuadratic_transvection :
    ¬IsQuadratic {(GX.transvection (0 : Fin 2) 1 (inr (.of 1)) (one_mem _) (by simp)
      (inr (.of 0) ^ 2 * inr (.of 1) ^ 2) : GX G (Fin 2))} := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [isQuadratic_singleton]
  intro h
  have := (countP_toWord_snd_le_occurrences 1 _).trans (h 1)
  simp only [_root_.map_mul, map_pow, GX.transvection_inr_of_self, one_mul, snd_apply_inr,
    GX.transvection_inr_of_of_ne _ _ h10] at this
  revert this
  decide

end Examples

end TauCeti.GroupAlgGeom.Quadratic
