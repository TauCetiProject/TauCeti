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

A strictly quadratic word over a group `G` is brought to a standard quadratic word by a
`G`-automorphism of `G[X]` composed of elementary ones ([IFT], §2.7, Lemma 1). This file records
how the elementary `G`-automorphisms of `G[X]` act on the number of occurrences of a variable, and
hence on quadratic and strictly quadratic systems.

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

* `TauCeti.GroupAlgGeom.Quadratic.occurrences_map_le`: a homomorphism `G[X] → G[Y]` under which
  `y` occurs at most once in the image of `x` and in no other generator does not increase the
  number of occurrences.
* `TauCeti.GroupAlgGeom.Quadratic.mem_avoiding_iff`: `GX.avoiding x` consists of the words with
  no occurrence of `x`.
* `occurrences_renameEquiv`, `occurrences_invertVar`, `occurrences_transvection`: the occurrence
  counts preserved by the elementary automorphisms.
* `isQuadratic_map_iff`, `isStrictlyQuadratic_map_iff`: an injective map preserving occurrence
  counts, up to a bijection of the variables, preserves quadratic and strictly quadratic systems.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definition 2 and Lemma 1.
-/

public section

open Monoid.Coprod Function

namespace TauCeti.GroupAlgGeom.Quadratic

variable {G X Y : Type*} [Group G]

/-! ### Occurrences under homomorphisms -/

/-- A homomorphism `φ : G[X] → G[Y]` does not increase occurrence counts from `x` to `y` when
`y` does not occur in the images of the coefficients and of the variables other than `x`, and
occurs at most once in the image of `x`. -/
theorem occurrences_map_le {F : Type*} [FunLike F (GX G X) (GX G Y)]
    [MonoidHomClass F (GX G X) (GX G Y)] (φ : F) (x : X) (y : Y)
    (hcoeff : ∀ g, occurrences y (φ (inl g)) = 0)
    (hx : occurrences y (φ (inr (FreeGroup.of x))) ≤ 1)
    (hne : ∀ z, z ≠ x → occurrences y (φ (inr (FreeGroup.of z))) = 0) (w : GX G X) :
    occurrences y (φ w) ≤ occurrences x w :=
  le_occurrences x (fun u => occurrences y (φ u))
    (fun u v => by simpa using occurrences_mul_le y (φ u) (φ v)) hcoeff hx (by simpa using hx)
    (fun z hz => ⟨hne z hz, by simpa using hne z hz⟩) w

/-! ### Words in which a variable does not occur -/

section Avoiding

variable [DecidableEq X] {x : X} {a b : GX G X}

/-- The variable `x` does not occur in a word after the substitution `x ↦ 1`. -/
theorem occurrences_eval_update_one (x : X) (w : GX G X) :
    occurrences x (eval inl (update (fun y => inr (FreeGroup.of y)) x 1) w) = 0 := by
  have hmul : ∀ u v : GX G X, occurrences x u = 0 → occurrences x v = 0 →
      occurrences x (u * v) = 0 := fun u v hu hv =>
    Nat.eq_zero_of_le_zero ((occurrences_mul_le x u v).trans (by omega))
  induction w using Monoid.Coprod.induction_on with
  | inl g => simp
  | inr f =>
    induction f using FreeGroup.induction_on with
    | one => simp
    | of y =>
      by_cases h : y = x
      · subst h; simp
      · simp [h]
    | inv_of y ih => simpa using ih
    | mul f₁ f₂ h₁ h₂ => simpa using hmul _ _ h₁ h₂
  | mul u v hu hv => simpa using hmul _ _ hu hv

/-- The words of `GX.avoiding x` are the words in which `x` does not occur. -/
theorem mem_avoiding_iff : a ∈ GX.avoiding x ↔ occurrences x a = 0 := by
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

private theorem occurrences_renameEquiv_le (e : X ≃ Y) (x : X) (w : GX G X) :
    occurrences (e x) (GX.renameEquiv G e w) ≤ occurrences x w :=
  occurrences_map_le _ x (e x) (by simp) (by simp)
    (fun z hz => by simp [occurrences_inr_of_of_ne (e.injective.ne hz)]) w

/-- Renaming the variables renames the occurrence counts. -/
@[simp]
theorem occurrences_renameEquiv (e : X ≃ Y) (x : X) (w : GX G X) :
    occurrences (e x) (GX.renameEquiv G e w) = occurrences x w := by
  refine (occurrences_renameEquiv_le e x w).antisymm ?_
  simpa [← GX.renameEquiv_symm] using
    occurrences_renameEquiv_le e.symm (e x) (GX.renameEquiv G e w)

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
  occurrences_transvection ha hb (mem_avoiding_iff.1 ha) (mem_avoiding_iff.1 hb) w

/-- Multiplying a variable by coefficients preserves all occurrence counts. -/
@[simp]
theorem occurrences_transvection_inl (x y : X) (g h : G) (w : GX G X) :
    occurrences y (GX.transvection x (inl g) (inl h) (GX.inl_mem_avoiding x g)
      (GX.inl_mem_avoiding x h) w) = occurrences y w :=
  occurrences_transvection _ _ (by simp) (by simp) w

end Elementary

/-! ### Quadratic systems under automorphisms -/

section IsQuadratic

variable {S : Finset (GX G X)}

private theorem sum_occurrences_map (φ : GX G X ↪ GX G Y) (σ : X ≃ Y)
    (h : ∀ x w, occurrences (σ x) (φ w) = occurrences x w) (S : Finset (GX G X)) (y : Y) :
    ∑ w ∈ S.map φ, occurrences y w = ∑ w ∈ S, occurrences (σ.symm y) w := by
  simp [← h]

/-- An injective map `G[X] → G[Y]` preserving the occurrence counts, up to a bijection of the
variables, preserves quadratic systems. -/
theorem isQuadratic_map_iff (φ : GX G X ↪ GX G Y) (σ : X ≃ Y)
    (h : ∀ x w, occurrences (σ x) (φ w) = occurrences x w) :
    IsQuadratic (S.map φ) ↔ IsQuadratic S := by
  simp only [isQuadratic_iff, sum_occurrences_map φ σ h]
  exact σ.symm.forall_congr_right (q := fun x => ∑ w ∈ S, occurrences x w ≤ 2)

/-- An injective map `G[X] → G[Y]` preserving the occurrence counts, up to a bijection of the
variables, preserves strictly quadratic systems. -/
theorem isStrictlyQuadratic_map_iff (φ : GX G X ↪ GX G Y) (σ : X ≃ Y)
    (h : ∀ x w, occurrences (σ x) (φ w) = occurrences x w) :
    IsStrictlyQuadratic (S.map φ) ↔ IsStrictlyQuadratic S := by
  simp only [isStrictlyQuadratic_iff, sum_occurrences_map φ σ h]
  exact σ.symm.forall_congr_right
    (q := fun x => ∑ w ∈ S, occurrences x w = 0 ∨ ∑ w ∈ S, occurrences x w = 2)

/-- Renaming the variables preserves quadratic systems. -/
@[simp]
theorem isQuadratic_map_renameEquiv (e : X ≃ Y) :
    IsQuadratic (S.map (GX.renameEquiv G e : GX G X ≃ GX G Y).toEmbedding) ↔ IsQuadratic S :=
  isQuadratic_map_iff _ e (occurrences_renameEquiv e)

/-- Renaming the variables preserves strictly quadratic systems. -/
@[simp]
theorem isStrictlyQuadratic_map_renameEquiv (e : X ≃ Y) :
    IsStrictlyQuadratic (S.map (GX.renameEquiv G e : GX G X ≃ GX G Y).toEmbedding) ↔
      IsStrictlyQuadratic S :=
  isStrictlyQuadratic_map_iff _ e (occurrences_renameEquiv e)

variable [DecidableEq X]

/-- Inverting a variable preserves quadratic systems. -/
@[simp]
theorem isQuadratic_map_invertVar (x : X) :
    IsQuadratic (S.map (GX.invertVar G x : GX G X ≃ GX G X).toEmbedding) ↔ IsQuadratic S :=
  isQuadratic_map_iff _ (.refl X) (occurrences_invertVar x)

/-- Inverting a variable preserves strictly quadratic systems. -/
@[simp]
theorem isStrictlyQuadratic_map_invertVar (x : X) :
    IsStrictlyQuadratic (S.map (GX.invertVar G x : GX G X ≃ GX G X).toEmbedding) ↔
      IsStrictlyQuadratic S :=
  isStrictlyQuadratic_map_iff _ (.refl X) (occurrences_invertVar x)

/-- Multiplying a variable by coefficients preserves quadratic systems. -/
@[simp]
theorem isQuadratic_map_transvection_inl (x : X) (g h : G) :
    IsQuadratic (S.map (GX.transvection x (inl g) (inl h) (GX.inl_mem_avoiding x g)
      (GX.inl_mem_avoiding x h) : GX G X ≃ GX G X).toEmbedding) ↔ IsQuadratic S :=
  isQuadratic_map_iff _ (.refl X) fun y => occurrences_transvection_inl x y g h

/-- Multiplying a variable by coefficients preserves strictly quadratic systems. -/
@[simp]
theorem isStrictlyQuadratic_map_transvection_inl (x : X) (g h : G) :
    IsStrictlyQuadratic (S.map (GX.transvection x (inl g) (inl h) (GX.inl_mem_avoiding x g)
      (GX.inl_mem_avoiding x h) : GX G X ≃ GX G X).toEmbedding) ↔ IsStrictlyQuadratic S :=
  isStrictlyQuadratic_map_iff _ (.refl X) fun y => occurrences_transvection_inl x y g h

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
