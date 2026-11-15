/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.NthProduct
import TauCeti.Algebra.Vertex.FormalDistribution
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Group.Hom.End

/-!
# Dong's lemma for mutually local fields

If `A`, `B`, `C` are pairwise mutually local fields on an `R`-module `V` of orders `r₁`, `r₂`, `r₃`
respectively, **Dong's lemma** asserts that every `n`-th product `A₍ₙ₎ B` (`n : ℤ`) is again
mutually local with `C`. More precisely:

* for `n ≥ 0`, `nonnegResidueProduct n A B` is local to `C` of order `r₁ + r₂ + r₃`;
* for `n = -1`, `normalOrder A B` is local to `C` of order `r₁ + r₂ + r₃`;
* in general (`n : ℤ`), `nthProduct n A B` is local to `C` of order
  `r₁ + r₂ + r₃ + 2 * (-n - 1).toNat`.

All results hold over an arbitrary commutative ring `R`, with no torsion or characteristic
assumptions. We work directly with three-variable coefficient families `ℤ → ℤ → ℤ → V` and the
commuting difference operators `z - w`, `z - x`, `w - x = -(z - w) + (z - x)`. Writing
`(w - x)^{r₁ + r₂ + r₃} = (-(z - w) + (z - x))^{r₁ + r₂} (w - x)^{r₃}` splits the binomial sum
into terms with exponent at least `r₂` on `z - x` (which annihilate both `A(z)B(w)C(x) -
C(x)A(z)B(w)` and `B(w)A(z)C(x) - C(x)B(w)A(z)`) and terms with exponent at least `r₁ + 1` on
`z - w` (which factor through `(z - w)^{r₁}`, equalizing the two orderings of `A(z)` and `B(w)`
with one spare factor of `z - w`). On nonnegative residue products the difference vanishes
directly; on normal ordering the extra factor of `z - w` telescopes the negative and nonnegative
ray sums to opposite boundary terms `± W₀(0, m, k)`.

## Main results

* `VertexOperator.IsLocalOfOrder.nonnegResidueProduct_left`,
  `VertexOperator.IsLocalOfOrder.nonnegResidueProduct_right`: Dong's lemma for `A₍ₙ₎ B` (`n : ℕ`).
* `VertexOperator.IsLocalOfOrder.normalOrder_left`,
  `VertexOperator.IsLocalOfOrder.normalOrder_right`: Dong's lemma for `:AB:`.
* `VertexOperator.IsLocalOfOrder.nthProduct_left`,
  `VertexOperator.IsLocalOfOrder.nthProduct_right`: Dong's lemma for all `n`-th products (`n : ℤ`).

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., Lemma 3.2.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Proposition 2.2.4.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3.4.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset TauCeti

namespace VertexOperator

section Dist3

variable {V : Type*} [AddCommGroup V]

private theorem end_mul_apply {M : Type*} [AddCommGroup M] (f g : AddMonoid.End M) (x : M) :
    (f * g) x = f (g x) := (rfl)

private theorem end_add_apply {M : Type*} [AddCommGroup M] (f g : AddMonoid.End M) (x : M) :
    (f + g) x = f x + g x := (rfl)

private theorem end_neg_apply {M : Type*} [AddCommGroup M] (f : AddMonoid.End M) (x : M) :
    (-f) x = -f x := (rfl)

private theorem end_nsmul_apply {M : Type*} [AddCommGroup M] (n : ℕ) (f : AddMonoid.End M)
    (x : M) : (n • f) x = n • f x := (rfl)

private theorem end_sum_apply {ι M : Type*} [AddCommGroup M] (s : Finset ι)
    (f : ι → AddMonoid.End M) (x : M) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x :=
  AddMonoidHom.finsetSum_apply f s x

/-- Three-variable formal coefficient families indexed by `z^{-l-1} w^{-m-1} x^{-k-1}`. -/
private abbrev Dist3 (V : Type*) := ℤ → ℤ → ℤ → V

/-- Multiplication of a three-variable family by `z - w`. -/
private def subZW : AddMonoid.End (Dist3 V) where
  toFun Y l m k := Y (l + 1) m k - Y l (m + 1) k
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

/-- Multiplication of a three-variable family by `z - x`. -/
private def subZX : AddMonoid.End (Dist3 V) where
  toFun Y l m k := Y (l + 1) m k - Y l m (k + 1)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

/-- Multiplication of a three-variable family by `w - x`. -/
private def subWX : AddMonoid.End (Dist3 V) where
  toFun Y l m k := Y l (m + 1) k - Y l m (k + 1)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

@[simp]
private theorem subZW_apply (Y : Dist3 V) (l m k : ℤ) :
    subZW Y l m k = Y (l + 1) m k - Y l (m + 1) k := (rfl)

@[simp]
private theorem subZX_apply (Y : Dist3 V) (l m k : ℤ) :
    subZX Y l m k = Y (l + 1) m k - Y l m (k + 1) := (rfl)

@[simp]
private theorem subWX_apply (Y : Dist3 V) (l m k : ℤ) :
    subWX Y l m k = Y l (m + 1) k - Y l m (k + 1) := (rfl)

private theorem subWX_eq : subWX (V := V) = -subZW + subZX := by
  ext Y l m k
  simp only [end_add_apply, end_neg_apply, Pi.add_apply, Pi.neg_apply,
    subWX_apply, subZW_apply, subZX_apply]
  abel

private theorem commute_subZW_subZX : Commute (subZW (V := V)) subZX := by
  ext Y l m k
  simp only [end_mul_apply, subZW_apply, subZX_apply]
  abel

private theorem commute_subZW_subWX : Commute (subZW (V := V)) subWX := by
  rw [subWX_eq]
  exact Commute.add_right (Commute.refl (subZW (V := V))).neg_right commute_subZW_subZX

private theorem commute_subZX_subWX : Commute (subZX (V := V)) subWX := by
  rw [subWX_eq]
  exact Commute.add_right (commute_subZW_subZX (V := V)).symm.neg_right (Commute.refl _)

private theorem subZW_pow_apply (r : ℕ) (Y : Dist3 V) (l m k : ℤ) :
    (subZW ^ r) Y l m k = (FormalDistribution.mulSub ^ r) (fun l' m' ↦ Y l' m' k) l m := by
  induction r generalizing l m with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ', pow_succ', end_mul_apply, end_mul_apply,
      subZW_apply, FormalDistribution.mulSub_apply, ih, ih]

private theorem subZX_pow_apply (r : ℕ) (Y : Dist3 V) (l m k : ℤ) :
    (subZX ^ r) Y l m k = (FormalDistribution.mulSub ^ r) (fun l' k' ↦ Y l' m k') l k := by
  induction r generalizing l k with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ', pow_succ', end_mul_apply, end_mul_apply,
      subZX_apply, FormalDistribution.mulSub_apply, ih, ih]

private theorem subWX_pow_apply (r : ℕ) (Y : Dist3 V) (l m k : ℤ) :
    (subWX ^ r) Y l m k = (FormalDistribution.mulSub ^ r) (fun m' k' ↦ Y l m' k') m k := by
  induction r generalizing m k with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ', pow_succ', end_mul_apply, end_mul_apply,
      subWX_apply, FormalDistribution.mulSub_apply, ih, ih]

private theorem mulSub_pow_comp {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (f : M →+ N) (r : ℕ) (c : FormalDistribution M) (m n : ℤ) :
    (FormalDistribution.mulSub ^ r) (fun m' n' ↦ f (c m' n')) m n =
      f ((FormalDistribution.mulSub ^ r) c m n) := by
  induction r generalizing m n with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ', end_mul_apply, FormalDistribution.mulSub_apply, ih, ih, ← map_sub,
      ← FormalDistribution.mulSub_apply, ← end_mul_apply, ← pow_succ']

/-- The binomial quotient operator factoring `(w - x)^{r₁ + r₂ + r₃}` modulo
`(z - x)^{r₂} (w - x)^{r₃}` through `subZW * · * (-subZW)^{r₁}`. -/
private def dongFactor (r₁ r₂ r₃ : ℕ) : AddMonoid.End (Dist3 V) :=
  -∑ ij ∈ (antidiagonal (r₁ + r₂)).filter (fun ij ↦ ij.2 < r₂),
    (r₁ + r₂).choose ij.1 • ((-subZW) ^ (ij.1 - r₁ - 1) * subZX ^ ij.2 * subWX ^ r₃)

private theorem subWX_pow_eq_subZW_dongFactor {r₁ r₂ r₃ : ℕ} {Z : Dist3 V}
    (hZ : (subZX (V := V) ^ r₂ * subWX (V := V) ^ r₃) Z = 0) :
    (subWX ^ (r₁ + r₂ + r₃)) Z = subZW (dongFactor r₁ r₂ r₃ (((-subZW) ^ r₁) Z)) := by
  have hcomm : Commute (-subZW (V := V)) subZX := (commute_subZW_subZX (V := V)).neg_left
  have hexp₀ : subWX (V := V) ^ (r₁ + r₂) = (-subZW + subZX) ^ (r₁ + r₂) := by rw [subWX_eq]
  rw [pow_add subWX (r₁ + r₂) r₃, hexp₀, hcomm.add_pow' (r₁ + r₂), sum_mul,
    end_sum_apply,
    ← sum_filter_add_sum_filter_not _ (fun ij : ℕ × ℕ ↦ ij.2 < r₂)]
  have hhigh : ∑ ij ∈ (antidiagonal (r₁ + r₂)).filter (fun ij ↦ ¬ ij.2 < r₂),
      (((r₁ + r₂).choose ij.1 • ((-subZW) ^ ij.1 * subZX ^ ij.2) * subWX ^ r₃ :
        AddMonoid.End (Dist3 V))) Z = 0 := by
    refine sum_eq_zero fun ij hij ↦ ?_
    have hij2 : r₂ ≤ ij.2 := not_lt.1 (mem_filter.1 hij).2
    have heq : ij.2 = (ij.2 - r₂) + r₂ := (Nat.sub_add_cancel hij2).symm
    rw [smul_mul_assoc, end_nsmul_apply, heq, pow_add subZX (ij.2 - r₂) r₂,
      ← mul_assoc ((-subZW) ^ ij.1), mul_assoc ((-subZW) ^ ij.1 * subZX ^ (ij.2 - r₂)),
      end_mul_apply, hZ, map_zero, smul_zero]
  rw [hhigh, add_zero, dongFactor, end_neg_apply, end_sum_apply,
    map_neg, map_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun ij hij ↦ ?_
  obtain ⟨hanti, hlt⟩ := mem_filter.1 hij
  have hsum : ij.1 + ij.2 = r₁ + r₂ := mem_antidiagonal.1 hanti
  have hc₁ : Commute (subZX (V := V) ^ ij.2) ((-subZW) ^ r₁) :=
    ((commute_subZW_subZX (V := V)).symm.neg_right).pow_pow ij.2 r₁
  have hc₂ : Commute (subWX (V := V) ^ r₃) ((-subZW) ^ r₁) :=
    ((commute_subZW_subWX (V := V)).symm.neg_right).pow_pow r₃ r₁
  have hc : (subZX (V := V) ^ ij.2 * subWX ^ r₃) * (-subZW) ^ r₁ =
      (-subZW) ^ r₁ * (subZX ^ ij.2 * subWX ^ r₃) := (hc₁.mul_left hc₂).eq
  rw [smul_mul_assoc, end_nsmul_apply, end_nsmul_apply, map_nsmul, ← smul_neg]
  congr 1
  rw [← end_neg_apply, ← end_mul_apply, ← end_mul_apply]
  congr 1
  rw [mul_assoc ((-subZW) ^ (ij.1 - r₁ - 1)) (subZX ^ ij.2) (subWX ^ r₃),
    mul_assoc (-subZW) ((-subZW) ^ (ij.1 - r₁ - 1) * (subZX ^ ij.2 * subWX ^ r₃)) ((-subZW) ^ r₁),
    mul_assoc ((-subZW) ^ (ij.1 - r₁ - 1)) (subZX ^ ij.2 * subWX ^ r₃) ((-subZW) ^ r₁),
    hc, ← mul_assoc ((-subZW) ^ (ij.1 - r₁ - 1)) ((-subZW) ^ r₁),
    ← pow_add (-subZW) (ij.1 - r₁ - 1) r₁,
    ← mul_assoc (-subZW) ((-subZW) ^ (ij.1 - r₁ - 1 + r₁)),
    ← pow_succ' (-subZW) (ij.1 - r₁ - 1 + r₁),
    show ij.1 - r₁ - 1 + r₁ + 1 = ij.1 by omega,
    ← mul_assoc ((-subZW) ^ ij.1) (subZX ^ ij.2) (subWX ^ r₃)]

/-! ### Ray truncation and telescoping -/

/-- Uniform truncation in the second (`w`) index for each fixed third (`x`) index. -/
private def HasBddM (Y : Dist3 V) : Prop :=
  ∀ k : ℤ, ∃ M : ℤ, ∀ l m : ℤ, M ≤ m → Y l m k = 0

/-- Uniform truncation in the first (`z`) index for each fixed third (`x`) index. -/
private def HasBddL (Y : Dist3 V) : Prop :=
  ∀ k : ℤ, ∃ L : ℤ, ∀ l m : ℤ, L ≤ l → Y l m k = 0

private theorem HasBddM.zero : HasBddM (0 : Dist3 V) :=
  fun _ ↦ ⟨0, fun _ _ _ ↦ rfl⟩

private theorem HasBddM.add {Y₁ Y₂ : Dist3 V} (h₁ : HasBddM Y₁) (h₂ : HasBddM Y₂) :
    HasBddM (Y₁ + Y₂) := fun k ↦ by
  obtain ⟨M₁, hM₁⟩ := h₁ k
  obtain ⟨M₂, hM₂⟩ := h₂ k
  exact ⟨max M₁ M₂, fun l m hm ↦ by
    simp [hM₁ l m (le_of_max_le_left hm), hM₂ l m (le_of_max_le_right hm)]⟩

private theorem HasBddM.neg {Y : Dist3 V} (h : HasBddM Y) : HasBddM (-Y) := fun k ↦ by
  obtain ⟨M, hM⟩ := h k
  exact ⟨M, fun l m hm ↦ by simp [hM l m hm]⟩

private theorem HasBddM.nsmul (n : ℕ) {Y : Dist3 V} (h : HasBddM Y) : HasBddM (n • Y) := by
  induction n with
  | zero => simpa using HasBddM.zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

private theorem HasBddM.sum {ι : Type*} (s : Finset ι) (f : ι → Dist3 V)
    (hf : ∀ i ∈ s, HasBddM (f i)) : HasBddM (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasBddM.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (mem_insert_self a s)).add (ih fun b hb ↦ hf b (mem_insert_of_mem hb))

private theorem HasBddM.subZW {Y : Dist3 V} (h : HasBddM Y) : HasBddM (subZW Y) := fun k ↦ by
  obtain ⟨M, hM⟩ := h k
  exact ⟨M, fun l m hm ↦ by simp [hM (l + 1) m hm, hM l (m + 1) (by omega)]⟩

private theorem HasBddM.subZX {Y : Dist3 V} (h : HasBddM Y) : HasBddM (subZX Y) := fun k ↦ by
  obtain ⟨M₁, hM₁⟩ := h k
  obtain ⟨M₂, hM₂⟩ := h (k + 1)
  exact ⟨max M₁ M₂, fun l m hm ↦ by
    simp [hM₁ (l + 1) m (le_of_max_le_left hm), hM₂ l m (le_of_max_le_right hm)]⟩

private theorem HasBddM.subWX {Y : Dist3 V} (h : HasBddM Y) : HasBddM (subWX Y) := by
  rw [subWX_eq, end_add_apply, end_neg_apply]
  exact h.subZW.neg.add h.subZX

private theorem HasBddM.pow_apply {E : AddMonoid.End (Dist3 V)}
    (hE : ∀ {Y : Dist3 V}, HasBddM Y → HasBddM (E Y)) (n : ℕ) {Y : Dist3 V} (hY : HasBddM Y) :
    HasBddM ((E ^ n) Y) := by
  induction n with
  | zero => exact hY
  | succ n ih =>
    rw [pow_succ', end_mul_apply]
    exact hE ih

private theorem HasBddM.dongFactor (r₁ r₂ r₃ : ℕ) {Y : Dist3 V} (hY : HasBddM Y) :
    HasBddM (dongFactor r₁ r₂ r₃ Y) := by
  rw [VertexOperator.dongFactor, end_neg_apply, end_sum_apply]
  refine (HasBddM.sum _ _ fun ij _ ↦ ?_).neg
  rw [end_nsmul_apply, end_mul_apply, end_mul_apply]
  exact HasBddM.nsmul _
    (HasBddM.pow_apply (fun h ↦ h.subZW.neg) _
      (HasBddM.pow_apply HasBddM.subZX _ (HasBddM.pow_apply HasBddM.subWX _ hY)))

private theorem HasBddL.zero : HasBddL (0 : Dist3 V) :=
  fun _ ↦ ⟨0, fun _ _ _ ↦ rfl⟩

private theorem HasBddL.add {Y₁ Y₂ : Dist3 V} (h₁ : HasBddL Y₁) (h₂ : HasBddL Y₂) :
    HasBddL (Y₁ + Y₂) := fun k ↦ by
  obtain ⟨L₁, hL₁⟩ := h₁ k
  obtain ⟨L₂, hL₂⟩ := h₂ k
  exact ⟨max L₁ L₂, fun l m hl ↦ by
    simp [hL₁ l m (le_of_max_le_left hl), hL₂ l m (le_of_max_le_right hl)]⟩

private theorem HasBddL.neg {Y : Dist3 V} (h : HasBddL Y) : HasBddL (-Y) := fun k ↦ by
  obtain ⟨L, hL⟩ := h k
  exact ⟨L, fun l m hl ↦ by simp [hL l m hl]⟩

private theorem HasBddL.nsmul (n : ℕ) {Y : Dist3 V} (h : HasBddL Y) : HasBddL (n • Y) := by
  induction n with
  | zero => simpa using HasBddL.zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

private theorem HasBddL.sum {ι : Type*} (s : Finset ι) (f : ι → Dist3 V)
    (hf : ∀ i ∈ s, HasBddL (f i)) : HasBddL (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasBddL.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (mem_insert_self a s)).add (ih fun b hb ↦ hf b (mem_insert_of_mem hb))

private theorem HasBddL.subZW {Y : Dist3 V} (h : HasBddL Y) : HasBddL (subZW Y) := fun k ↦ by
  obtain ⟨L, hL⟩ := h k
  exact ⟨L, fun l m hl ↦ by simp [hL (l + 1) m (by omega), hL l (m + 1) hl]⟩

private theorem HasBddL.subZX {Y : Dist3 V} (h : HasBddL Y) : HasBddL (subZX Y) := fun k ↦ by
  obtain ⟨L₁, hL₁⟩ := h k
  obtain ⟨L₂, hL₂⟩ := h (k + 1)
  exact ⟨max L₁ L₂, fun l m hl ↦ by
    have h₁ : L₁ ≤ l + 1 := le_trans (le_max_left L₁ L₂) (by omega)
    simp [hL₁ (l + 1) m h₁, hL₂ l m (le_of_max_le_right hl)]⟩

private theorem HasBddL.subWX {Y : Dist3 V} (h : HasBddL Y) : HasBddL (subWX Y) := by
  rw [subWX_eq, end_add_apply, end_neg_apply]
  exact h.subZW.neg.add h.subZX

private theorem HasBddL.pow_apply {E : AddMonoid.End (Dist3 V)}
    (hE : ∀ {Y : Dist3 V}, HasBddL Y → HasBddL (E Y)) (n : ℕ) {Y : Dist3 V} (hY : HasBddL Y) :
    HasBddL ((E ^ n) Y) := by
  induction n with
  | zero => exact hY
  | succ n ih =>
    rw [pow_succ', end_mul_apply]
    exact hE ih

private theorem HasBddL.dongFactor (r₁ r₂ r₃ : ℕ) {Y : Dist3 V} (hY : HasBddL Y) :
    HasBddL (dongFactor r₁ r₂ r₃ Y) := by
  rw [VertexOperator.dongFactor, end_neg_apply, end_sum_apply]
  refine (HasBddL.sum _ _ fun ij _ ↦ ?_).neg
  rw [end_nsmul_apply, end_mul_apply, end_mul_apply]
  exact HasBddL.nsmul _
    (HasBddL.pow_apply (fun h ↦ h.subZW.neg) _
      (HasBddL.pow_apply HasBddL.subZX _ (HasBddL.pow_apply HasBddL.subWX _ hY)))

/-- Negative-ray sum `∑ᶠ i : ℕ, Y (-i - 1) (m + i) k` corresponding to the left half of `:AB:`. -/
private def resNeg (Y : Dist3 V) : FormalDistribution V :=
  fun m k ↦ ∑ᶠ i : ℕ, Y (-(i : ℤ) - 1) (m + i) k

/-- Nonnegative-ray sum `∑ᶠ i : ℕ, Y i (m - i - 1) k` corresponding to the right half of `:AB:`. -/
private def resNonneg (Y : Dist3 V) : FormalDistribution V :=
  fun m k ↦ ∑ᶠ i : ℕ, Y (i : ℤ) (m - i - 1) k

private theorem HasBddM.finite_support_resNeg {Y : Dist3 V} (hY : HasBddM Y) (m k : ℤ) :
    (Function.support fun i : ℕ ↦ Y (-(i : ℤ) - 1) (m + i) k).Finite := by
  obtain ⟨M, hM⟩ := hY k
  refine (finite_toSet (range (M - m).toNat)).subset fun i hi ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! h
  exact hi (hM _ _ (by omega))

private theorem HasBddL.finite_support_resNonneg {Y : Dist3 V} (hY : HasBddL Y) (m k : ℤ) :
    (Function.support fun i : ℕ ↦ Y (i : ℤ) (m - i - 1) k).Finite := by
  obtain ⟨L, hL⟩ := hY k
  refine (finite_toSet (range L.toNat)).subset fun i hi ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! h
  exact hi (hL _ _ (by omega))

private theorem resNeg_subWX {Y : Dist3 V} (hY : HasBddM Y) :
    resNeg (subWX Y) = FormalDistribution.mulSub (resNeg Y) := by
  ext m k : 2
  have heq : (fun i : ℕ ↦ subWX Y (-(i : ℤ) - 1) (m + i) k) =
      fun i : ℕ ↦ Y (-(i : ℤ) - 1) (m + 1 + i) k - Y (-(i : ℤ) - 1) (m + i) (k + 1) := by
    ext i
    simp [subWX_apply, show m + (i : ℤ) + 1 = m + 1 + i by omega]
  rw [resNeg, heq,
    finsum_sub_distrib (hY.finite_support_resNeg (m + 1) k) (hY.finite_support_resNeg m (k + 1)),
    FormalDistribution.mulSub_apply, resNeg, resNeg]

private theorem resNeg_subWX_pow (N : ℕ) {Y : Dist3 V} (hY : HasBddM Y) :
    resNeg ((subWX ^ N) Y) = (FormalDistribution.mulSub ^ N) (resNeg Y) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ', end_mul_apply,
      resNeg_subWX (HasBddM.pow_apply HasBddM.subWX N hY), ih,
      ← end_mul_apply, ← pow_succ']

private theorem resNonneg_subWX {Y : Dist3 V} (hY : HasBddL Y) :
    resNonneg (subWX Y) = FormalDistribution.mulSub (resNonneg Y) := by
  ext m k : 2
  have heq : (fun i : ℕ ↦ subWX Y (i : ℤ) (m - i - 1) k) =
      fun i : ℕ ↦ Y (i : ℤ) (m + 1 - i - 1) k - Y (i : ℤ) (m - i - 1) (k + 1) := by
    ext i
    simp [subWX_apply, show m - (i : ℤ) - 1 + 1 = m + 1 - i - 1 by omega]
  rw [resNonneg, heq, finsum_sub_distrib (hY.finite_support_resNonneg (m + 1) k)
    (hY.finite_support_resNonneg m (k + 1)),
    FormalDistribution.mulSub_apply, resNonneg, resNonneg]

private theorem resNonneg_subWX_pow (N : ℕ) {Y : Dist3 V} (hY : HasBddL Y) :
    resNonneg ((subWX ^ N) Y) = (FormalDistribution.mulSub ^ N) (resNonneg Y) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ', end_mul_apply,
      resNonneg_subWX (HasBddL.pow_apply HasBddL.subWX N hY), ih,
      ← end_mul_apply, ← pow_succ']

private theorem resNeg_subZW {Y : Dist3 V} (hY : HasBddM Y) (m k : ℤ) :
    resNeg (subZW Y) m k = Y 0 m k := by
  obtain ⟨M, hM⟩ := hY k
  let K : ℕ := (M - m).toNat + 1
  have hsub : (Function.support fun i : ℕ ↦ subZW Y (-(i : ℤ) - 1) (m + i) k) ⊆ range K := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! h
    exact hi (by simp [subZW_apply, hM _ _ (by omega : M ≤ m + i),
      hM _ _ (by omega : M ≤ m + i + 1)])
  rw [resNeg, finsum_eq_sum_of_support_subset _ hsub]
  let f : ℕ → V := fun i ↦ Y (-(i : ℤ)) (m + i) k
  have hterm : ∀ i ∈ range K, subZW Y (-(i : ℤ) - 1) (m + i) k = f i - f (i + 1) := by
    intro i _
    simp only [subZW_apply, f, Nat.cast_add, Nat.cast_one,
      show -(i : ℤ) - 1 + 1 = -i by omega, show -((i : ℤ) + 1) = -i - 1 by omega,
      show m + ((i : ℤ) + 1) = m + i + 1 by omega]
  rw [sum_congr rfl hterm, Finset.sum_range_sub' f K]
  simp [f, hM _ _ (by omega : M ≤ m + K)]

private theorem resNonneg_subZW {Y : Dist3 V} (hY : HasBddL Y) (m k : ℤ) :
    resNonneg (subZW Y) m k = -Y 0 m k := by
  obtain ⟨L, hL⟩ := hY k
  let K : ℕ := L.toNat + 1
  have hsub : (Function.support fun i : ℕ ↦ subZW Y (i : ℤ) (m - i - 1) k) ⊆ range K := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! h
    exact hi (by simp [subZW_apply, hL _ _ (by omega : L ≤ (i : ℤ) + 1),
      hL _ _ (by omega : L ≤ (i : ℤ))])
  rw [resNonneg, finsum_eq_sum_of_support_subset _ hsub]
  let g : ℕ → V := fun i ↦ Y (i : ℤ) (m - i) k
  have hterm : ∀ i ∈ range K, subZW Y (i : ℤ) (m - i - 1) k = g (i + 1) - g i := by
    intro i _
    simp only [subZW_apply, g, Nat.cast_add, Nat.cast_one,
      show m - ((i : ℤ) + 1) = m - i - 1 by omega,
      show m - (i : ℤ) - 1 + 1 = m - i by omega]
  rw [sum_congr rfl hterm, Finset.sum_range_sub g K]
  simp [g, hL _ _ (by omega : L ≤ (K : ℤ))]

end Dist3

namespace IsLocalOfOrder

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Common setup for Dong's lemma on a vector `v : V`: the ordered triple-commutator families
`P(z, w, x) = [A(z)B(w), C(x)] v` and `Q(z, w, x) = [B(w)A(z), C(x)] v` are both sent by
`(w - x)^{r₁ + r₂ + r₃}` to `subZW W₀` for a single family `W₀` satisfying both `HasBddM W₀`
and `HasBddL W₀`. -/
private theorem subZX_pow_mul_subWX_pow_jacobi_eq_zero {A B C : VertexOperator R V} {r₂ r₃ : ℕ}
    (hAC : A.IsLocalOfOrder C r₂) (hBC : B.IsLocalOfOrder C r₃) (v : V) :
    (subZX (V := V) ^ r₂ * subWX (V := V) ^ r₃)
      (fun l m k ↦ (A[[l]]) ((B[[m]]) ((C[[k]]) v)) - (C[[k]]) ((A[[l]]) ((B[[m]]) v))) = 0 := by
  have hAC' := (isLocalOfOrder_iff_mulSub_pow_eq_zero A C r₂).1 hAC
  have hBC' := (isLocalOfOrder_iff_mulSub_pow_eq_zero B C r₃).1 hBC
  let P₁ : Dist3 V := fun l m k ↦ (A[[l]]) (((B.commutatorDistribution C m k)) v)
  let P₂ : Dist3 V := fun l m k ↦ ((A.commutatorDistribution C l k)) ((B[[m]]) v)
  have hPsplit :
      (fun l m k ↦ (A[[l]]) ((B[[m]]) ((C[[k]]) v)) - (C[[k]]) ((A[[l]]) ((B[[m]]) v))) =
        P₁ + P₂ := by
    ext l m k
    simp only [P₁, P₂, Pi.add_apply, commutatorDistribution_apply, LinearMap.sub_apply,
      mul_apply_eq_comp, map_sub]
    abel
  have hP₁ : (subWX ^ r₃) P₁ = 0 := by
    ext l m k
    let f : Module.End R V →+ V :=
      (A[[l]]).toAddMonoidHom.comp (LinearMap.evalAddMonoidHom v : Module.End R V →+ V)
    have hf : (fun m' k' ↦ P₁ l m' k') = fun m' k' ↦ f (B.commutatorDistribution C m' k') := by
      ext m' k'
      simp [P₁, f]
    rw [subWX_pow_apply, hf, mulSub_pow_comp, hBC']
    simp [f]
  have hP₂ : (subZX ^ r₂) P₂ = 0 := by
    ext l m k
    let f : Module.End R V →+ V := LinearMap.evalAddMonoidHom ((B[[m]]) v)
    have hf : (fun l' k' ↦ P₂ l' m k') = fun l' k' ↦ f (A.commutatorDistribution C l' k') := by
      ext l' k'
      simp [P₂, f]
    rw [subZX_pow_apply, hf, mulSub_pow_comp, hAC']
    simp [f]
  rw [hPsplit, map_add, end_mul_apply, hP₁, map_zero, zero_add,
    ((commute_subZX_subWX (V := V)).pow_pow r₂ r₃).eq, end_mul_apply, hP₂, map_zero]

private theorem exists_common_dong_witness {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}
    (hAB : A.IsLocalOfOrder B r₁) (hAC : A.IsLocalOfOrder C r₂) (hBC : B.IsLocalOfOrder C r₃)
    (v : V) :
    let P : Dist3 V := fun l m k ↦
      (A[[l]]) ((B[[m]]) ((C[[k]]) v)) - (C[[k]]) ((A[[l]]) ((B[[m]]) v))
    let Q : Dist3 V := fun l m k ↦
      (B[[m]]) ((A[[l]]) ((C[[k]]) v)) - (C[[k]]) ((B[[m]]) ((A[[l]]) v))
    HasBddM P ∧ HasBddL Q ∧
      ∃ W₀ : Dist3 V, HasBddM W₀ ∧ HasBddL W₀ ∧
        (subWX ^ (r₁ + r₂ + r₃)) P = subZW W₀ ∧
        (subWX ^ (r₁ + r₂ + r₃)) Q = subZW W₀ := by
  intro P Q
  have hAB' := (isLocalOfOrder_iff_mulSub_pow_eq_zero A B r₁).1 hAB
  have hP_bdd : HasBddM P := fun k ↦ by
    obtain ⟨M₁, hM₁⟩ := B.exists_forall_ncoeff_apply_eq_zero ((C[[k]]) v)
    obtain ⟨M₂, hM₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
    exact ⟨max (M₁ : ℤ) (M₂ : ℤ), fun _ m hm ↦ by
      simp only [P, hM₁ m (le_of_max_le_left hm), hM₂ m (le_of_max_le_right hm), map_zero,
        sub_self]⟩
  have hQ_bdd : HasBddL Q := fun k ↦ by
    obtain ⟨L₁, hL₁⟩ := A.exists_forall_ncoeff_apply_eq_zero ((C[[k]]) v)
    obtain ⟨L₂, hL₂⟩ := A.exists_forall_ncoeff_apply_eq_zero v
    exact ⟨max (L₁ : ℤ) (L₂ : ℤ), fun l _ hl ↦ by
      simp only [Q, hL₁ l (le_of_max_le_left hl), hL₂ l (le_of_max_le_right hl), map_zero,
        sub_self]⟩
  have hP_ann : (subZX (V := V) ^ r₂ * subWX (V := V) ^ r₃) P = 0 :=
    subZX_pow_mul_subWX_pow_jacobi_eq_zero hAC hBC v
  -- Obtain `hQ_ann` from the swapped fields `(B, A)` by permuting the first two variables.
  have hQ_ann : (subZX (V := V) ^ r₂ * subWX (V := V) ^ r₃) Q = 0 := by
    let Q₁ : Dist3 V := fun l m k ↦ (B[[m]]) (((A.commutatorDistribution C l k)) v)
    let Q₂ : Dist3 V := fun l m k ↦ ((B.commutatorDistribution C m k)) ((A[[l]]) v)
    have hAC' := (isLocalOfOrder_iff_mulSub_pow_eq_zero A C r₂).1 hAC
    have hBC' := (isLocalOfOrder_iff_mulSub_pow_eq_zero B C r₃).1 hBC
    have hQsplit : Q = Q₁ + Q₂ := by
      ext l m k
      simp only [Q, Q₁, Q₂, Pi.add_apply, commutatorDistribution_apply, LinearMap.sub_apply,
        mul_apply_eq_comp, map_sub]
      abel
    have hQ₁ : (subZX ^ r₂) Q₁ = 0 := by
      ext l m k
      let f : Module.End R V →+ V :=
        (B[[m]]).toAddMonoidHom.comp (LinearMap.evalAddMonoidHom v : Module.End R V →+ V)
      have hf : (fun l' k' ↦ Q₁ l' m k') = fun l' k' ↦ f (A.commutatorDistribution C l' k') := by
        ext l' k'
        simp [Q₁, f]
      rw [subZX_pow_apply, hf, mulSub_pow_comp, hAC']
      simp [f]
    have hQ₂ : (subWX ^ r₃) Q₂ = 0 := by
      ext l m k
      let f : Module.End R V →+ V := LinearMap.evalAddMonoidHom ((A[[l]]) v)
      have hf : (fun m' k' ↦ Q₂ l m' k') = fun m' k' ↦ f (B.commutatorDistribution C m' k') := by
        ext m' k'
        simp [Q₂, f]
      rw [subWX_pow_apply, hf, mulSub_pow_comp, hBC']
      simp [f]
    rw [hQsplit, map_add, ((commute_subZX_subWX (V := V)).pow_pow r₂ r₃).eq, end_mul_apply,
      hQ₁, map_zero, zero_add, ← ((commute_subZX_subWX (V := V)).pow_pow r₂ r₃).eq,
      end_mul_apply, hQ₂, map_zero]
  have hPQ : ((-subZW) ^ r₁) P = ((-subZW) ^ r₁) Q := by
    have hsub : (subZW ^ r₁) (P - Q) = 0 := by
      ext l m k
      let f : Module.End R V →+ V :=
        { toFun u := u ((C[[k]]) v) - (C[[k]]) (u v)
          map_zero' := by simp
          map_add' _ _ := by simp; abel }
      have hf : (fun l' m' ↦ (P - Q) l' m' k) =
          fun l' m' ↦ f (A.commutatorDistribution B l' m') := by
        ext l' m'
        simp only [P, Q, Pi.sub_apply, f, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          commutatorDistribution_apply, mul_apply_eq_comp, map_sub]
      rw [subZW_pow_apply, hf, mulSub_pow_comp, hAB']
      simp [f]
    have hneg_pow (n : ℕ) : ((-subZW) ^ n) (P - Q) = (-1 : ℤ) ^ n • ((subZW ^ n) (P - Q)) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', pow_succ', end_mul_apply, end_neg_apply, ih,
          map_zsmul, ← neg_zsmul, pow_succ', end_mul_apply]
        congr 1
        ring
    have h0 : ((-subZW) ^ r₁) (P - Q) = 0 := by rw [hneg_pow, hsub, smul_zero]
    rwa [map_sub, sub_eq_zero] at h0
  refine ⟨hP_bdd, hQ_bdd, dongFactor r₁ r₂ r₃ (((-subZW) ^ r₁) P),
    HasBddM.dongFactor r₁ r₂ r₃ (HasBddM.pow_apply (fun h ↦ h.subZW.neg) r₁ hP_bdd), ?_,
    subWX_pow_eq_subZW_dongFactor hP_ann, ?_⟩
  · rw [hPQ]
    exact HasBddL.dongFactor r₁ r₂ r₃ (HasBddL.pow_apply (fun h ↦ h.subZW.neg) r₁ hQ_bdd)
  · rw [hPQ]
    exact subWX_pow_eq_subZW_dongFactor hQ_ann

/-- **Dong's lemma for nonnegative residue products (left).** If `A, B, C` are pairwise local of
orders `r₁, r₂, r₃`, then `nonnegResidueProduct n A B` is local to `C` of order `r₁ + r₂ + r₃`. -/
theorem nonnegResidueProduct_left {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}
    (hAB : A.IsLocalOfOrder B r₁) (hAC : A.IsLocalOfOrder C r₂) (hBC : B.IsLocalOfOrder C r₃)
    (n : ℕ) :
    (nonnegResidueProduct n A B).IsLocalOfOrder C (r₁ + r₂ + r₃) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  ext m k v : 3
  obtain ⟨_, _, W₀, _, _, hP, hQ⟩ := exists_common_dong_witness hAB hAC hBC v
  let P : Dist3 V := fun l m' k' ↦
    (A[[l]]) ((B[[m']]) ((C[[k']]) v)) - (C[[k']]) ((A[[l]]) ((B[[m']]) v))
  let Q : Dist3 V := fun l m' k' ↦
    (B[[m']]) ((A[[l]]) ((C[[k']]) v)) - (C[[k']]) ((B[[m']]) ((A[[l]]) v))
  have hPQ : (subWX ^ (r₁ + r₂ + r₃)) (P - Q) = 0 := by
    rw [map_sub, hP, hQ, sub_self]
  let ev : Module.End R V →+ V := LinearMap.evalAddMonoidHom v
  have hcomm : (fun m' k' ↦ ev ((nonnegResidueProduct n A B).commutatorDistribution C m' k')) =
      fun m' k' ↦ (subZW ^ n) (P - Q) 0 m' k' := by
    ext m' k'
    rw [subZW_pow_apply, FormalDistribution.mulSub_pow_apply]
    simp only [ev, LinearMap.evalAddMonoidHom_apply, commutatorDistribution_apply,
      ncoeff_nonnegResidueProduct, LinearMap.sub_apply, mul_apply_eq_comp,
      LinearMap.sum_apply, map_sum, ← sum_sub_distrib, zero_add]
    refine sum_congr rfl fun ij _ ↦ ?_
    simp only [LinearMap.smul_apply, map_nsmul, map_zsmul, LinearMap.sub_apply,
      mul_apply_eq_comp, map_sub, P, Q, Pi.sub_apply, smul_sub]
    abel
  have key := (mulSub_pow_comp ev (r₁ + r₂ + r₃)
    ((nonnegResidueProduct n A B).commutatorDistribution C) m k).symm
  rw [hcomm, ← subWX_pow_apply (r₁ + r₂ + r₃) ((subZW ^ n) (P - Q)) 0 m k,
    ← end_mul_apply, ← ((commute_subZW_subWX (V := V)).pow_pow n (r₁ + r₂ + r₃)).eq,
    end_mul_apply, hPQ, map_zero] at key
  simpa [ev] using key

/-- **Dong's lemma for nonnegative residue products (right).** -/
theorem nonnegResidueProduct_right {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}
    (hAB : A.IsLocalOfOrder B r₁) (hCA : C.IsLocalOfOrder A r₂) (hCB : C.IsLocalOfOrder B r₃)
    (n : ℕ) :
    C.IsLocalOfOrder (nonnegResidueProduct n A B) (r₁ + r₂ + r₃) :=
  (hAB.nonnegResidueProduct_left hCA.symm hCB.symm n).symm

private theorem commutatorDistribution_normalOrder_eq (A B C : VertexOperator R V) (v : V) :
    (fun m' k' ↦ ((normalOrder A B).commutatorDistribution C m' k') v) =
      resNeg (fun l m' k' ↦
        (A[[l]]) ((B[[m']]) ((C[[k']]) v)) - (C[[k']]) ((A[[l]]) ((B[[m']]) v))) +
      resNonneg (fun l m' k' ↦
        (B[[m']]) ((A[[l]]) ((C[[k']]) v)) - (C[[k']]) ((B[[m']]) ((A[[l]]) v))) := by
  ext m' k'
  obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero ((C[[k']]) v)
  obtain ⟨P₂, hP₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q₁, hQ₁⟩ := A.exists_forall_ncoeff_apply_eq_zero ((C[[k']]) v)
  obtain ⟨Q₂, hQ₂⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let M : ℕ := max (max P₁ P₂ + m'.natAbs) (max Q₁ Q₂)
  have hBCv (i : ℕ) (hi : M ≤ i) : (B[[m' + i]]) ((C[[k']]) v) = 0 := hP₁ _ (by omega)
  have hBv (i : ℕ) (hi : M ≤ i) : (B[[m' + i]]) v = 0 := hP₂ _ (by omega)
  have hACv (i : ℕ) (hi : M ≤ i) : (A[[(i : ℤ)]]) ((C[[k']]) v) = 0 := hQ₁ _ (by omega)
  have hAv (i : ℕ) (hi : M ≤ i) : (A[[(i : ℤ)]]) v = 0 := hQ₂ _ (by omega)
  have hs₁ : (Function.support fun i : ℕ ↦
      (A[[-(i : ℤ) - 1]]) ((B[[m' + i]]) ((C[[k']]) v)) -
        (C[[k']]) ((A[[-(i : ℤ) - 1]]) ((B[[m' + i]]) v))) ⊆ range M := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! h
    exact hi (by simp [hBCv i h, hBv i h])
  have hs₂ : (Function.support fun i : ℕ ↦
      (B[[m' - i - 1]]) ((A[[(i : ℤ)]]) ((C[[k']]) v)) -
        (C[[k']]) ((B[[m' - i - 1]]) ((A[[(i : ℤ)]]) v))) ⊆ range M := by
    intro i hi
    simp only [mem_coe, mem_range]
    by_contra! h
    exact hi (by simp [hACv i h, hAv i h])
  simp only [commutatorDistribution_apply, LinearMap.sub_apply, mul_apply_eq_comp,
    ncoeff_normalOrder, normalOrderCoeff_eq_sum A B m' ((C[[k']]) v) hBCv hACv,
    normalOrderCoeff_eq_sum A B m' v hBv hAv, map_add, map_sum, Pi.add_apply, resNeg, resNonneg,
    finsum_eq_sum_of_support_subset _ hs₁, finsum_eq_sum_of_support_subset _ hs₂, sum_sub_distrib]
  abel

/-- **Dong's lemma for normal ordering (left).** If `A, B, C` are pairwise local of orders
`r₁, r₂, r₃`, then `normalOrder A B` is local to `C` of order `r₁ + r₂ + r₃`. -/
theorem normalOrder_left {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}
    (hAB : A.IsLocalOfOrder B r₁) (hAC : A.IsLocalOfOrder C r₂) (hBC : B.IsLocalOfOrder C r₃) :
    (normalOrder A B).IsLocalOfOrder C (r₁ + r₂ + r₃) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  ext m k v : 3
  obtain ⟨hP_bdd, hQ_bdd, W₀, hW₀_M, hW₀_L, hP, hQ⟩ :=
    exists_common_dong_witness hAB hAC hBC v
  let ev : Module.End R V →+ V := LinearMap.evalAddMonoidHom v
  have hcomm : (fun m' k' ↦ ev ((normalOrder A B).commutatorDistribution C m' k')) =
      resNeg (fun l m' k' ↦
        (A[[l]]) ((B[[m']]) ((C[[k']]) v)) - (C[[k']]) ((A[[l]]) ((B[[m']]) v))) +
      resNonneg (fun l m' k' ↦
        (B[[m']]) ((A[[l]]) ((C[[k']]) v)) - (C[[k']]) ((B[[m']]) ((A[[l]]) v))) :=
    commutatorDistribution_normalOrder_eq A B C v
  have key := (mulSub_pow_comp ev (r₁ + r₂ + r₃)
    ((normalOrder A B).commutatorDistribution C) m k).symm
  rw [hcomm, map_add, Pi.add_apply, Pi.add_apply, ← resNeg_subWX_pow (r₁ + r₂ + r₃) hP_bdd,
    ← resNonneg_subWX_pow (r₁ + r₂ + r₃) hQ_bdd, hP, hQ, resNeg_subZW hW₀_M,
    resNonneg_subZW hW₀_L, add_neg_cancel] at key
  simpa [ev] using key

/-- **Dong's lemma for normal ordering (right).** -/
theorem normalOrder_right {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}
    (hAB : A.IsLocalOfOrder B r₁) (hCA : C.IsLocalOfOrder A r₂) (hCB : C.IsLocalOfOrder B r₃) :
    C.IsLocalOfOrder (normalOrder A B) (r₁ + r₂ + r₃) :=
  (hAB.normalOrder_left hCA.symm hCB.symm).symm

/-- **Dong's lemma for all `n`-th products (left).** For every `n : ℤ`, if `A, B, C` are pairwise
local of orders `r₁, r₂, r₃`, then `nthProduct n A B` is local to `C` of order
`r₁ + r₂ + r₃ + 2 * (-n - 1).toNat`. -/
theorem nthProduct_left {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}
    (hAB : A.IsLocalOfOrder B r₁) (hAC : A.IsLocalOfOrder C r₂) (hBC : B.IsLocalOfOrder C r₃)
    (n : ℤ) :
    (nthProduct n A B).IsLocalOfOrder C (r₁ + r₂ + r₃ + 2 * (-n - 1).toNat) := by
  rcases lt_or_ge n 0 with hn | hn
  · let k : ℕ := (-n - 1).toNat
    have hn' : n = -(k : ℤ) - 1 := by omega
    rw [hn', nthProduct_neg_succ]
    have hloc := (hAB.hasseDeriv_left k).normalOrder_left (hAC.hasseDeriv_left k) hBC
    exact hloc.mono (by omega)
  · have hk : (-n - 1).toNat = 0 := by omega
    lift n to ℕ using hn
    rw [hk, mul_zero, add_zero, nthProduct_natCast]
    exact hAB.nonnegResidueProduct_left hAC hBC n

/-- **Dong's lemma for all `n`-th products (right).** -/
theorem nthProduct_right {A B C : VertexOperator R V} {r₁ r₂ r₃ : ℕ}
    (hAB : A.IsLocalOfOrder B r₁) (hCA : C.IsLocalOfOrder A r₂) (hCB : C.IsLocalOfOrder B r₃)
    (n : ℤ) :
    C.IsLocalOfOrder (nthProduct n A B) (r₁ + r₂ + r₃ + 2 * (-n - 1).toNat) :=
  (hAB.nthProduct_left hCA.symm hCB.symm n).symm

end IsLocalOfOrder

end VertexOperator
