/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.GroupTheory.Coxeter.Length
public import TauCeti.GroupTheory.Coxeter.Geometric.Basic
public import TauCeti.GroupTheory.Coxeter.Parabolic
import TauCeti.GroupTheory.Coxeter.Dihedral
import TauCeti.GroupTheory.Coxeter.Geometric.RankTwo

/-!
# Signs of geometric roots and faithfulness of the geometric representation

Let `cs : CoxeterSystem M W` be a Coxeter system with arbitrary index set `I`, acting on the free
real vector space `I →₀ ℝ` through its standard geometric representation `ρ`. A vector is called
positive when it has nonnegative coefficients and is nonzero, which is exactly Mathlib's strict
order `0 < v` on finitely supported functions; a vector is negative when `v < 0`.

The **geometric sign criterion** says that the sign of the root `ρ(w) αᵢ` records the length
function of `W`:

* `0 < ρ(w) αᵢ` exactly when `i` is not a right descent of `w`, that is, `ℓ(w sᵢ) = ℓ(w) + 1`;
* `ρ(w) αᵢ < 0` exactly when `i` is a right descent of `w`, that is, `ℓ(w sᵢ) + 1 = ℓ(w)`.

**Tits' theorem**, that `ρ` is injective, follows at once: an element `w ≠ 1` has a right descent,
so it makes a simple root negative and cannot act as the identity. Neither statement involves a
finiteness hypothesis or the nondegeneracy of the canonical form: the proof inducts on a finite word
and looks only at one two-generator standard parabolic subgroup at each step.

The file also records the elementary properties of the set of roots, the orbit of the simple roots:
it is stable under `W` and under negation, its vectors are nonzero of norm one for the canonical
form (which need not be positive definite), each of them is positive or negative, and a simple
reflection permutes the positive roots other than its own simple root.

## Main definitions

* `CoxeterSystem.geometricRoots`: the roots, the `W`-orbit of the simple roots.

## Main results

* `CoxeterSystem.geometricRepresentation_single_pos_iff` and
  `CoxeterSystem.geometricRepresentation_single_neg_iff`: the geometric sign criterion.
* `CoxeterSystem.geometricRepresentation_injective`: Tits' theorem.
* `CoxeterSystem.pos_or_neg_of_mem_geometricRoots`: every root is positive or negative.
* `CoxeterSystem.bijOn_geometricReflection_geometricRoots`: a simple reflection permutes the
  positive roots other than its own simple root.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 5.4.
-/

public section

namespace CoxeterSystem

variable {I W : Type*} [Group W] {M : CoxeterMatrix I} (cs : CoxeterSystem M W)

/-! ### The sign criterion -/

/-- **The rank-two case of the sign criterion.** An element `v` of the standard parabolic subgroup
on `{i, j}` without right descent at `i` sends the simple root `αᵢ` to a nonnegative combination of
`αᵢ` and `αⱼ`. -/
theorem exists_nonneg_geometricRepresentation_of_mem_parabolic_pair {i j : I} {v : W}
    (hv : v ∈ cs.parabolic {i, j}) (hvi : ¬cs.IsRightDescent v i) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      cs.geometricRepresentation v (Finsupp.single i 1) =
        a • Finsupp.single i 1 + b • Finsupp.single j 1 := by
  have hlen := cs.not_isRightDescent_iff.mp hvi
  -- a reduced alternating word for `v` ending in `i` would make `i` a right descent
  have hword : cs.wordProd (alternatingWord i j (cs.length v)) = v := by
    refine (cs.wordProd_alternatingWord_eq_of_mem_parabolic_pair hv).elim id fun h ↦ ?_
    rcases hk : cs.length v with - | k
    · simp [cs.length_eq_zero_iff.mp hk, alternatingWord]
    · rw [hk, alternatingWord_succ, wordProd_concat] at h
      have hle := cs.length_wordProd_le (alternatingWord i j k)
      rw [length_alternatingWord] at hle
      rw [← h, cs.simple_mul_simple_cancel_right, h] at hlen
      omega
  -- appending `i` still gives a reduced word, so the alternating word stops before the braid length
  have hred : cs.IsReduced (alternatingWord j i (cs.length v + 1)) := by
    rw [IsReduced, alternatingWord_succ, wordProd_concat, hword, hlen, List.concat_eq_append,
      List.length_append, length_alternatingWord, List.length_singleton]
  have hk : cs.length v < M i j ∨ M i j = 0 := by
    by_contra hcon
    rw [not_or, not_lt] at hcon
    rw [← M.symmetric j i] at hcon
    exact cs.not_isReduced_alternatingWord j i hcon.2 (by omega) hred
  rw [← hword]
  exact cs.rankTwo_nonnegative i j hk

/-- An element without right descent at `i` sends `αᵢ` to a vector with nonnegative coefficients. -/
private theorem geometricRepresentation_single_nonneg {w : W} {i : I}
    (h : ¬cs.IsRightDescent w i) : 0 ≤ cs.geometricRepresentation w (Finsupp.single i 1) := by
  induction hn : cs.length w using Nat.strong_induction_on generalizing w i with
  | _ n ih =>
    rcases eq_or_ne w 1 with rfl | hw
    · simp
    -- a right descent `j` of `w` factors `w = u * v` along the standard parabolic subgroup on
    -- `{i, j}`, where lengths add and `u` is strictly shorter than `w`, which sets up the induction
    obtain ⟨j, hj⟩ := cs.exists_rightDescent_of_ne_one hw
    obtain ⟨⟨u, v⟩, ⟨hu, hv, huv⟩, -⟩ := cs.existsUnique_isMinimalCosetRep_mul {i, j} w
    dsimp only at hu hv huv
    subst huv
    have hu' := cs.isMinimalCosetRep_iff.mp hu
    have hlen := cs.length_mul_of_isMinimalCosetRep hu hv
    have hv₁ : v ≠ 1 := by
      rintro rfl
      exact hu' j (by simp) (by simpa using hj)
    have hvpos : 0 < cs.length v := Nat.pos_of_ne_zero (mt cs.length_eq_zero_iff.mp hv₁)
    have hvi : ¬cs.IsRightDescent v i := fun hd ↦ h <| by
      rw [IsRightDescent] at hd ⊢
      rw [mul_assoc, cs.length_mul_of_isMinimalCosetRep hu
        (mul_mem hv (cs.simple_mem_parabolic (by simp))), hlen]
      omega
    obtain ⟨a, b, ha, hb, hab⟩ :=
      cs.exists_nonneg_geometricRepresentation_of_mem_parabolic_pair hv hvi
    rw [map_mul, mul_apply_eq_comp, hab, map_add, map_smul, map_smul]
    exact add_nonneg (smul_nonneg ha (ih _ (by omega) (hu' i (by simp)) rfl))
      (smul_nonneg hb (ih _ (by omega) (hu' j (by simp)) rfl))

private theorem geometricRepresentation_single_pos {w : W} {i : I}
    (h : ¬cs.IsRightDescent w i) : 0 < cs.geometricRepresentation w (Finsupp.single i 1) :=
  lt_of_le_of_ne (cs.geometricRepresentation_single_nonneg h)
    ((map_ne_zero_iff _ (cs.geometricRepresentation.apply_bijective w).injective).mpr
      (Finsupp.single_ne_zero.mpr one_ne_zero)).symm

private theorem geometricRepresentation_single_neg {w : W} {i : I}
    (h : cs.IsRightDescent w i) : cs.geometricRepresentation w (Finsupp.single i 1) < 0 := by
  have hpos := cs.geometricRepresentation_single_pos
    (cs.isRightDescent_iff_not_isRightDescent_mul.mp h)
  rwa [cs.geometricRepresentation_mul_simple_single, neg_pos] at hpos

/-- **The geometric sign criterion, positive case.** The root `ρ(w) αᵢ` is positive exactly when `i`
is not a right descent of `w`, that is, when `ℓ(w sᵢ) = ℓ(w) + 1`. -/
theorem geometricRepresentation_single_pos_iff (w : W) (i : I) :
    0 < cs.geometricRepresentation w (Finsupp.single i 1) ↔ ¬cs.IsRightDescent w i :=
  ⟨fun hpos hd ↦ lt_asymm hpos (cs.geometricRepresentation_single_neg hd),
    cs.geometricRepresentation_single_pos⟩

/-- **The geometric sign criterion, negative case.** The root `ρ(w) αᵢ` is negative exactly when `i`
is a right descent of `w`, that is, when `ℓ(w sᵢ) + 1 = ℓ(w)`. -/
theorem geometricRepresentation_single_neg_iff (w : W) (i : I) :
    cs.geometricRepresentation w (Finsupp.single i 1) < 0 ↔ cs.IsRightDescent w i :=
  ⟨fun hneg ↦ by_contra fun hd ↦ lt_asymm hneg (cs.geometricRepresentation_single_pos hd),
    cs.geometricRepresentation_single_neg⟩

/-- **Tits' theorem**: the standard geometric representation of a Coxeter system is faithful. -/
theorem geometricRepresentation_injective : Function.Injective cs.geometricRepresentation := by
  refine (injective_iff_map_eq_one _).mpr fun w hw ↦ by_contra fun hw₁ ↦ ?_
  obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hw₁
  have hneg := cs.geometricRepresentation_single_neg hi
  rw [hw, one_apply_eq_self] at hneg
  exact (Finsupp.single_nonneg.mpr zero_le_one).not_gt hneg

/-! ### The roots -/

/-- The **roots** of a Coxeter system: the vectors `ρ(w) αᵢ` of the `W`-orbit of the simple roots in
the geometric representation. The orbit condition is essential, since a positive vector need not be
a root: every root has norm one for the canonical form. -/
def geometricRoots : Set (I →₀ ℝ) :=
  {v | ∃ (w : W) (i : I), cs.geometricRepresentation w (Finsupp.single i 1) = v}

theorem mem_geometricRoots {v : I →₀ ℝ} :
    v ∈ cs.geometricRoots ↔
      ∃ (w : W) (i : I), cs.geometricRepresentation w (Finsupp.single i 1) = v :=
  Iff.rfl

/-- The simple roots are roots. -/
@[simp]
theorem single_mem_geometricRoots (i : I) : Finsupp.single i 1 ∈ cs.geometricRoots :=
  ⟨1, i, by simp⟩

/-- The set of roots is stable under `W`. -/
@[simp]
theorem geometricRepresentation_apply_mem_geometricRoots_iff (w : W) {v : I →₀ ℝ} :
    cs.geometricRepresentation w v ∈ cs.geometricRoots ↔ v ∈ cs.geometricRoots := by
  have key (x : W) {u : I →₀ ℝ} (hu : u ∈ cs.geometricRoots) :
      cs.geometricRepresentation x u ∈ cs.geometricRoots := by
    obtain ⟨y, i, rfl⟩ := hu
    exact ⟨x * y, i, by rw [map_mul, mul_apply_eq_comp]⟩
  exact ⟨fun h ↦ by simpa using key w⁻¹ h, key w⟩

/-- The set of roots is stable under each simple reflection. -/
theorem geometricReflection_apply_mem_geometricRoots_iff (i : I) {v : I →₀ ℝ} :
    M.geometricReflection i v ∈ cs.geometricRoots ↔ v ∈ cs.geometricRoots := by
  rw [← cs.geometricRepresentation_simple, geometricRepresentation_apply_mem_geometricRoots_iff]

/-- The set of roots is stable under negation. -/
@[simp]
theorem neg_mem_geometricRoots_iff {v : I →₀ ℝ} :
    -v ∈ cs.geometricRoots ↔ v ∈ cs.geometricRoots := by
  have key {u : I →₀ ℝ} (hu : u ∈ cs.geometricRoots) : -u ∈ cs.geometricRoots := by
    obtain ⟨w, i, rfl⟩ := hu
    exact ⟨w * cs.simple i, i, cs.geometricRepresentation_mul_simple_single w i⟩
  exact ⟨fun h ↦ by simpa using key h, key⟩

/-- Roots have norm one for the canonical form, which need not be positive definite. -/
theorem geometricForm_self_of_mem_geometricRoots {v : I →₀ ℝ} (hv : v ∈ cs.geometricRoots) :
    M.geometricForm v v = 1 := by
  obtain ⟨w, i, rfl⟩ := hv
  rw [cs.geometricForm_geometricRepresentation, M.geometricForm_single_self]

/-- **Every root is positive or negative.** -/
theorem pos_or_neg_of_mem_geometricRoots {v : I →₀ ℝ} (hv : v ∈ cs.geometricRoots) :
    0 < v ∨ v < 0 := by
  obtain ⟨w, i, rfl⟩ := hv
  by_cases h : cs.IsRightDescent w i
  · exact Or.inr (cs.geometricRepresentation_single_neg h)
  · exact Or.inl (cs.geometricRepresentation_single_pos h)

/-- Roots are nonzero. -/
theorem ne_zero_of_mem_geometricRoots {v : I →₀ ℝ} (hv : v ∈ cs.geometricRoots) : v ≠ 0 :=
  (cs.pos_or_neg_of_mem_geometricRoots hv).elim ne_of_gt ne_of_lt

/-- A root supported at the single index `i` is `αᵢ` or `-αᵢ`, because it has norm one. -/
theorem eq_single_or_eq_neg_single_of_mem_geometricRoots {v : I →₀ ℝ} {i : I}
    (hv : v ∈ cs.geometricRoots) (hsupp : ∀ j, j ≠ i → v j = 0) :
    v = Finsupp.single i 1 ∨ v = -Finsupp.single i 1 := by
  obtain ⟨a, rfl⟩ : ∃ a, v = Finsupp.single i a :=
    ⟨v i, by
      ext j
      by_cases hj : j = i
      · simp [hj]
      · simp [hsupp j hj, Ne.symm hj]⟩
  have hnorm := cs.geometricForm_self_of_mem_geometricRoots hv
  simp only [M.geometricForm_single_single, M.diagonal, Nat.cast_one, div_one, Real.cos_pi,
    neg_neg, mul_one] at hnorm
  rcases mul_self_eq_one_iff.mp hnorm with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Finsupp.single_neg i 1)

/-- A simple reflection keeps every positive root other than its own simple root positive. -/
theorem geometricReflection_pos_of_mem_geometricRoots {v : I →₀ ℝ} {i : I}
    (hv : v ∈ cs.geometricRoots) (hpos : 0 < v) (hne : v ≠ Finsupp.single i 1) :
    0 < M.geometricReflection i v := by
  have hroot : M.geometricReflection i v ∈ cs.geometricRoots :=
    (cs.geometricReflection_apply_mem_geometricRoots_iff i).mpr hv
  refine (cs.pos_or_neg_of_mem_geometricRoots hroot).resolve_right fun hneg ↦ ?_
  -- otherwise every coefficient of `v` away from `i` would be both nonnegative and nonpositive
  have hsupp (j : I) (hj : j ≠ i) : v j = 0 := by
    have h₁ := hneg.le j
    rw [M.geometricReflection_apply_apply_of_ne hj] at h₁
    exact le_antisymm h₁ (hpos.le j)
  rcases cs.eq_single_or_eq_neg_single_of_mem_geometricRoots hv hsupp with h | h
  · exact hne h
  · rw [h, neg_pos] at hpos
    exact (Finsupp.single_nonneg.mpr zero_le_one).not_gt hpos

/-- **A simple reflection permutes the positive roots other than its own simple root.** -/
theorem bijOn_geometricReflection_geometricRoots (i : I) :
    Set.BijOn (M.geometricReflection i)
      {v | v ∈ cs.geometricRoots ∧ 0 < v ∧ v ≠ Finsupp.single i 1}
      {v | v ∈ cs.geometricRoots ∧ 0 < v ∧ v ≠ Finsupp.single i 1} := by
  have hinv (v : I →₀ ℝ) : M.geometricReflection i (M.geometricReflection i v) = v :=
    LinearMap.congr_fun (M.geometricReflection_mul_self i) v
  have hmaps : Set.MapsTo (M.geometricReflection i)
      {v | v ∈ cs.geometricRoots ∧ 0 < v ∧ v ≠ Finsupp.single i 1}
      {v | v ∈ cs.geometricRoots ∧ 0 < v ∧ v ≠ Finsupp.single i 1} := by
    rintro v ⟨hv, hpos, hne⟩
    refine ⟨(cs.geometricReflection_apply_mem_geometricRoots_iff i).mpr hv,
      cs.geometricReflection_pos_of_mem_geometricRoots hv hpos hne, fun h ↦ ?_⟩
    have hv' : v = -Finsupp.single i 1 := by
      rw [← hinv v, h, M.geometricReflection_apply_single_self]
    rw [hv', neg_pos] at hpos
    exact (Finsupp.single_nonneg.mpr zero_le_one).not_gt hpos
  exact Set.InvOn.bijOn ⟨fun v _ ↦ hinv v, fun v _ ↦ hinv v⟩ hmaps hmaps

end CoxeterSystem
