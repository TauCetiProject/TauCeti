/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Derivative
public import TauCeti.Algebra.Vertex.NormalOrder
public import TauCeti.Algebra.Vertex.ResidueProduct
public import Mathlib.Algebra.Lie.OfAssociative
import TauCeti.Data.Nat.Choose.Sum
import Mathlib.Tactic.Module

/-!
# Dong's lemma and integer `n`-th products of vertex operators

For fields `A` and `B` over an arbitrary commutative ring `R`, we package all integer `n`-th
products (`n : ℤ`) into a single `R`-bilinear operation `VertexOperator.nthProduct n`:

* for `n ≥ 0`, `A₍ₙ₎ B` is the singular residue commutator `Res_z (z - w)ⁿ [A(z), B(w)]`
  (`VertexOperator.nonnegResidueProduct`);
* for `n = -k - 1 < 0`, `A₍₋ₖ₋₁₎ B` is the normal-ordered Hasse derivative `: (D^[k] A) B :`
  (`VertexOperator.normalOrder` composed with `VertexOperator.hasseDeriv k`).

Using Hasse derivatives rather than divided powers of `∂` avoids division by `k!`, so every
`n`-th product is defined over any commutative ring.

The main theorem is **Dong's lemma**: if `(A, B)`, `(A, C)` and `(B, C)` are pairwise mutually
local, then every `n`-th product `A₍ₙ₎ B` (in particular every nonnegative residue product and
the normal-ordered product `:AB:`) is mutually local with `C`, over any commutative ring. We also
prove the formal Leibniz rules for `∂ (A₍ₙ₎ B)`, translation covariance of `A₍ₙ₎ B`, and the
vacuum evaluation formula `(A₍ₙ₎ B)₍₋₁₎ |0⟩ = A₍ₙ₎ (B₍₋₁₎ |0⟩)` for fields regular on `|0⟩`.

## Main definitions

* `VertexOperator.nthProduct`: the `n`-th product `A₍ₙ₎ B` of fields for all `n : ℤ`.

## Main results

* `VertexOperator.IsLocalOfOrder.nonnegResidueProduct_left`,
  `VertexOperator.IsLocalOfOrder.normalOrder_left`,
  `VertexOperator.IsLocalOfOrder.nthProduct_left`: **Dong's lemma** for nonnegative residue
  products, normal ordering, and all integer `n`-th products.
* `VertexOperator.derivative_nonnegResidueProduct`, `VertexOperator.derivative_normalOrder`,
  `VertexOperator.derivative_nthProduct`: Leibniz rules for formal differentiation.
* `VertexOperator.nthProduct_derivative_left`: `(∂A)₍ₙ₎ B = -n • A₍ₙ₋₁₎ B`.
* `VertexOperator.lie_ncoeff_nthProduct`: translation covariance passes to all `n`-th products.
* `VertexOperator.ncoeff_neg_one_nthProduct_apply`: `(A₍ₙ₎ B)₍₋₁₎ v = A₍ₙ₎ (B₍₋₁₎ v)` when
  nonnegative modes of `A` and `B` annihilate `v`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., Lemma 3.2 (Dong's lemma) and §4.4.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Proposition 2.2.4 and Lemma 2.3.5.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., Lemma 2.3.5 and §3.1.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset

namespace VertexOperator

/-! ### Three-variable formal distributions for Dong's lemma -/

section Dist3

variable {M : Type*} [AddCommGroup M]

private abbrev Dist3 (M : Type*) := ℤ → ℤ → ℤ → M

private theorem end_mul_apply {α : Type*} [AddCommMonoid α] (f g : AddMonoid.End α) (x : α) :
    (f * g) x = f (g x) := (rfl)

private theorem end_sub_apply {α : Type*} [AddCommGroup α] (f g : AddMonoid.End α) (x : α) :
    (f - g) x = f x - g x := (rfl)

private theorem end_nsmul_apply {α : Type*} [AddCommMonoid α] (n : ℕ) (f : AddMonoid.End α)
    (x : α) : (n • f) x = n • f x := (rfl)

private theorem end_zsmul_apply {α : Type*} [AddCommGroup α] (z : ℤ) (f : AddMonoid.End α)
    (x : α) : (z • f) x = z • f x := (rfl)

private theorem end_sum_apply {ι α : Type*} [AddCommMonoid α] (s : Finset ι)
    (f : ι → AddMonoid.End α) (x : α) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact congrArg (f a x + ·) ih

private def mulSub₁₂ : AddMonoid.End (Dist3 M) where
  toFun F m₁ m₂ m₃ := F (m₁ + 1) m₂ m₃ - F m₁ (m₂ + 1) m₃
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

private def mulSub₁₃ : AddMonoid.End (Dist3 M) where
  toFun F m₁ m₂ m₃ := F (m₁ + 1) m₂ m₃ - F m₁ m₂ (m₃ + 1)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

private def mulSub₂₃ : AddMonoid.End (Dist3 M) where
  toFun F m₁ m₂ m₃ := F m₁ (m₂ + 1) m₃ - F m₁ m₂ (m₃ + 1)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

@[simp]
private theorem mulSub₁₂_apply (F : Dist3 M) (m₁ m₂ m₃ : ℤ) :
    mulSub₁₂ F m₁ m₂ m₃ = F (m₁ + 1) m₂ m₃ - F m₁ (m₂ + 1) m₃ := (rfl)

@[simp]
private theorem mulSub₁₃_apply (F : Dist3 M) (m₁ m₂ m₃ : ℤ) :
    mulSub₁₃ F m₁ m₂ m₃ = F (m₁ + 1) m₂ m₃ - F m₁ m₂ (m₃ + 1) := (rfl)

@[simp]
private theorem mulSub₂₃_apply (F : Dist3 M) (m₁ m₂ m₃ : ℤ) :
    mulSub₂₃ F m₁ m₂ m₃ = F m₁ (m₂ + 1) m₃ - F m₁ m₂ (m₃ + 1) := (rfl)

private theorem mulSub₂₃_eq_sub :
    (mulSub₂₃ : AddMonoid.End (Dist3 M)) = mulSub₁₃ - mulSub₁₂ := by
  ext F m₁ m₂ m₃
  simp only [mulSub₂₃_apply, end_sub_apply, Pi.sub_apply, mulSub₁₃_apply, mulSub₁₂_apply]
  abel

private theorem commute_mulSub₁₃_mulSub₁₂ :
    Commute (mulSub₁₃ : AddMonoid.End (Dist3 M)) mulSub₁₂ := by
  ext F m₁ m₂ m₃
  simp only [end_mul_apply, mulSub₁₃_apply, mulSub₁₂_apply]
  abel

private theorem commute_mulSub₂₃_mulSub₁₂ :
    Commute (mulSub₂₃ : AddMonoid.End (Dist3 M)) mulSub₁₂ := by
  rw [mulSub₂₃_eq_sub]
  exact commute_mulSub₁₃_mulSub₁₂.sub_left (Commute.refl _)

private theorem commute_mulSub₂₃_mulSub₁₃ :
    Commute (mulSub₂₃ : AddMonoid.End (Dist3 M)) mulSub₁₃ := by
  rw [mulSub₂₃_eq_sub]
  exact (Commute.refl _).sub_left commute_mulSub₁₃_mulSub₁₂.symm

private theorem end_mul_nsmul {α : Type*} [AddCommMonoid α] (f g : AddMonoid.End α) (n : ℕ) :
    f * (n • g) = n • (f * g) := by
  ext x
  simp [end_mul_apply]

private theorem end_mul_zsmul {α : Type*} [AddCommGroup α] (f g : AddMonoid.End α) (z : ℤ) :
    f * (z • g) = z • (f * g) := by
  ext x
  simp [end_mul_apply]

private theorem mulSub₂₃_pow_eq_sum (N : ℕ) :
    (mulSub₂₃ : AddMonoid.End (Dist3 M)) ^ N =
      ∑ pq ∈ antidiagonal N,
        N.choose pq.1 • (-1 : ℤ) ^ pq.2 • (mulSub₁₃ ^ pq.1 * mulSub₁₂ ^ pq.2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', ih, mulSub₂₃_eq_sub, sub_mul, mul_sum, mul_sum,
      sum_antidiagonal_choose_succ_nsmul
        (fun i j ↦ (-1 : ℤ) ^ j • (mulSub₁₃ ^ i * mulSub₁₂ ^ j : AddMonoid.End (Dist3 M))) N]
    have e₁ : ∀ pq ∈ antidiagonal N,
        N.choose pq.1 • (-1 : ℤ) ^ (pq.2 + 1) •
          (mulSub₁₃ ^ pq.1 * mulSub₁₂ ^ (pq.2 + 1) : AddMonoid.End (Dist3 M)) =
        -(mulSub₁₂ * (N.choose pq.1 • (-1 : ℤ) ^ pq.2 • (mulSub₁₃ ^ pq.1 * mulSub₁₂ ^ pq.2))) := by
      intro pq _
      have hp : (-1 : ℤ) ^ (pq.2 + 1) = -((-1 : ℤ) ^ pq.2) := by rw [pow_succ]; ring
      rw [end_mul_nsmul, end_mul_zsmul, ← mul_assoc,
        (commute_mulSub₁₃_mulSub₁₂.pow_left pq.1).symm.eq, mul_assoc, ← pow_succ', hp,
        neg_zsmul, ← natCast_zsmul, zsmul_neg, natCast_zsmul]
    have e₂ : ∀ pq ∈ antidiagonal N,
        N.choose pq.2 • (-1 : ℤ) ^ pq.2 •
          (mulSub₁₃ ^ (pq.1 + 1) * mulSub₁₂ ^ pq.2 : AddMonoid.End (Dist3 M)) =
        mulSub₁₃ * (N.choose pq.1 • (-1 : ℤ) ^ pq.2 • (mulSub₁₃ ^ pq.1 * mulSub₁₂ ^ pq.2)) := by
      intro pq hpq
      rw [Nat.choose_symm_of_eq_add (mem_antidiagonal.mp hpq).symm, end_mul_nsmul, end_mul_zsmul,
        ← mul_assoc, ← pow_succ']
    rw [sum_congr rfl e₁, sum_congr rfl e₂, sum_neg_distrib]
    abel

private theorem mulSub₂₃_pow_eq_zero :
    ∀ (r s : ℕ) (F : Dist3 M),
      (mulSub₁₃ ^ r) F = 0 → (mulSub₁₂ ^ s) F = 0 → (mulSub₂₃ ^ (r + s)) F = 0
  | 0, _, F, h₁₃, _ => by
    have hF : F = 0 := by simpa using h₁₃
    simp [hF]
  | _ + 1, 0, F, _, h₁₂ => by
    have hF : F = 0 := by simpa using h₁₂
    simp [hF]
  | r + 1, s + 1, F, h₁₃, h₁₂ => by
    have hexp : r + 1 + (s + 1) = (r + s + 1) + 1 := by omega
    rw [hexp, pow_succ, end_mul_apply]
    conv_lhs => arg 2; rw [mulSub₂₃_eq_sub]
    rw [end_sub_apply, map_sub]
    have h₁ : (mulSub₂₃ ^ (r + (s + 1))) (mulSub₁₃ F) = 0 :=
      mulSub₂₃_pow_eq_zero r (s + 1) (mulSub₁₃ F) (by simpa [pow_succ] using h₁₃)
        (by rw [← end_mul_apply, (commute_mulSub₁₃_mulSub₁₂.pow_right _).symm.eq,
          end_mul_apply, h₁₂, map_zero])
    have h₂ : (mulSub₂₃ ^ ((r + 1) + s)) (mulSub₁₂ F) = 0 :=
      mulSub₂₃_pow_eq_zero (r + 1) s (mulSub₁₂ F)
        (by rw [← end_mul_apply, (commute_mulSub₁₃_mulSub₁₂.pow_left _).eq,
          end_mul_apply, h₁₃, map_zero])
        (by simpa [pow_succ] using h₁₂)
    have he₁ : r + s + 1 = r + (s + 1) := by omega
    have he₂ : r + s + 1 = (r + 1) + s := by omega
    rw [he₁, h₁, ← he₁, he₂, h₂, sub_zero]

private def Truncated₁ (F : Dist3 M) : Prop :=
  ∀ m₃ : ℤ, ∃ K : ℕ, ∀ m₁ m₂ : ℤ, (K : ℤ) ≤ m₁ → F m₁ m₂ m₃ = 0

private def Truncated₂ (F : Dist3 M) : Prop :=
  ∀ m₃ : ℤ, ∃ K : ℕ, ∀ m₁ m₂ : ℤ, (K : ℤ) ≤ m₂ → F m₁ m₂ m₃ = 0

private theorem truncated₁_mulSub₁₂ {F : Dist3 M} (h : Truncated₁ F) :
    Truncated₁ (mulSub₁₂ F) := fun m₃ ↦ by
  obtain ⟨K, hK⟩ := h m₃
  refine ⟨K, fun m₁ m₂ hm ↦ ?_⟩
  have hm' : (K : ℤ) ≤ m₁ + 1 := by omega
  rw [mulSub₁₂_apply, hK _ _ hm', hK _ _ hm, sub_zero]

private theorem truncated₁_mulSub₁₃ {F : Dist3 M} (h : Truncated₁ F) :
    Truncated₁ (mulSub₁₃ F) := fun m₃ ↦ by
  obtain ⟨K₁, h₁⟩ := h m₃
  obtain ⟨K₂, h₂⟩ := h (m₃ + 1)
  refine ⟨max K₁ K₂, fun m₁ m₂ hm ↦ ?_⟩
  have hm₁ : (K₁ : ℤ) ≤ m₁ + 1 :=
    le_trans (Nat.cast_le.mpr (le_max_left K₁ K₂)) (by omega)
  have hm₂ : (K₂ : ℤ) ≤ m₁ := le_trans (Nat.cast_le.mpr (le_max_right K₁ K₂)) hm
  rw [mulSub₁₃_apply, h₁ _ _ hm₁, h₂ _ _ hm₂, sub_zero]

private theorem truncated₁_mulSub₂₃ {F : Dist3 M} (h : Truncated₁ F) :
    Truncated₁ (mulSub₂₃ F) := fun m₃ ↦ by
  obtain ⟨K₁, h₁⟩ := h m₃
  obtain ⟨K₂, h₂⟩ := h (m₃ + 1)
  refine ⟨max K₁ K₂, fun m₁ m₂ hm ↦ ?_⟩
  have hm₁ : (K₁ : ℤ) ≤ m₁ := le_trans (Nat.cast_le.mpr (le_max_left K₁ K₂)) hm
  have hm₂ : (K₂ : ℤ) ≤ m₁ := le_trans (Nat.cast_le.mpr (le_max_right K₁ K₂)) hm
  rw [mulSub₂₃_apply, h₁ _ _ hm₁, h₂ _ _ hm₂, sub_zero]

private theorem truncated₂_iff_swap (F : Dist3 M) :
    Truncated₂ F ↔ Truncated₁ (fun m₂ m₁ m₃ ↦ F m₁ m₂ m₃) :=
  ⟨fun h m₃ ↦ let ⟨K, hK⟩ := h m₃; ⟨K, fun m₂ m₁ hm ↦ hK m₁ m₂ hm⟩,
   fun h m₃ ↦ let ⟨K, hK⟩ := h m₃; ⟨K, fun m₁ m₂ hm ↦ hK m₂ m₁ hm⟩⟩

private theorem truncated₂_mulSub₁₂ {F : Dist3 M} (h : Truncated₂ F) :
    Truncated₂ (mulSub₁₂ F) := fun m₃ ↦ by
  obtain ⟨K, hK⟩ := h m₃
  refine ⟨K, fun m₁ m₂ hm ↦ ?_⟩
  have hm' : (K : ℤ) ≤ m₂ + 1 := by omega
  rw [mulSub₁₂_apply, hK _ _ hm, hK _ _ hm', sub_zero]

private theorem truncated₂_mulSub₁₃ {F : Dist3 M} (h : Truncated₂ F) :
    Truncated₂ (mulSub₁₃ F) :=
  (truncated₂_iff_swap _).mpr (truncated₁_mulSub₂₃ ((truncated₂_iff_swap F).mp h))

private theorem truncated₂_mulSub₂₃ {F : Dist3 M} (h : Truncated₂ F) :
    Truncated₂ (mulSub₂₃ F) :=
  (truncated₂_iff_swap _).mpr (truncated₁_mulSub₁₃ ((truncated₂_iff_swap F).mp h))

private theorem truncated₁_pow {f : AddMonoid.End (Dist3 M)}
    (hf : ∀ {F}, Truncated₁ F → Truncated₁ (f F)) :
    ∀ (k : ℕ) {F : Dist3 M}, Truncated₁ F → Truncated₁ ((f ^ k) F)
  | 0, _, h => h
  | k + 1, _, h => by
    rw [pow_succ', end_mul_apply]
    exact hf (truncated₁_pow hf k h)

private theorem truncated₂_pow {f : AddMonoid.End (Dist3 M)}
    (hf : ∀ {F}, Truncated₂ F → Truncated₂ (f F)) :
    ∀ (k : ℕ) {F : Dist3 M}, Truncated₂ F → Truncated₂ ((f ^ k) F)
  | 0, _, h => h
  | k + 1, _, h => by
    rw [pow_succ', end_mul_apply]
    exact hf (truncated₂_pow hf k h)

private theorem truncated₁_pow_mulSub (a b c : ℕ) {F : Dist3 M} (h : Truncated₁ F) :
    Truncated₁ (((mulSub₁₃ ^ a * mulSub₁₂ ^ b * mulSub₂₃ ^ c : AddMonoid.End (Dist3 M))) F) := by
  rw [end_mul_apply, end_mul_apply]
  exact truncated₁_pow truncated₁_mulSub₁₃ a
    (truncated₁_pow truncated₁_mulSub₁₂ b (truncated₁_pow truncated₁_mulSub₂₃ c h))

private theorem truncated₂_pow_mulSub (a b c : ℕ) {F : Dist3 M} (h : Truncated₂ F) :
    Truncated₂ (((mulSub₁₃ ^ a * mulSub₁₂ ^ b * mulSub₂₃ ^ c : AddMonoid.End (Dist3 M))) F) := by
  rw [end_mul_apply, end_mul_apply]
  exact truncated₂_pow truncated₂_mulSub₁₃ a
    (truncated₂_pow truncated₂_mulSub₁₂ b (truncated₂_pow truncated₂_mulSub₂₃ c h))

private def iotasumNeg (F : Dist3 M) : TauCeti.FormalDistribution M :=
  fun m₂ m₃ ↦ ∑ᶠ i : ℕ, F (-(i : ℤ) - 1) (m₂ + i) m₃

private def iotasumPos (F : Dist3 M) : TauCeti.FormalDistribution M :=
  fun m₂ m₃ ↦ ∑ᶠ i : ℕ, F i (m₂ - i - 1) m₃

private theorem iotasumNeg_eq_sum {F : Dist3 M} {m₂ m₃ : ℤ} {P : ℕ}
    (hP : ∀ i : ℕ, P ≤ i → F (-(i : ℤ) - 1) (m₂ + i) m₃ = 0) :
    iotasumNeg F m₂ m₃ = ∑ i ∈ range P, F (-(i : ℤ) - 1) (m₂ + i) m₃ := by
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! hle
  exact hi (hP i hle)

private theorem iotasumPos_eq_sum {F : Dist3 M} {m₂ m₃ : ℤ} {Q : ℕ}
    (hQ : ∀ i : ℕ, Q ≤ i → F i (m₂ - i - 1) m₃ = 0) :
    iotasumPos F m₂ m₃ = ∑ i ∈ range Q, F i (m₂ - i - 1) m₃ := by
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  simp only [mem_coe, mem_range]
  by_contra! hle
  exact hi (hQ i hle)

private theorem mulSub_iotasum {F₁ F₂ : Dist3 M} (h₁ : Truncated₂ F₁) (h₂ : Truncated₁ F₂) :
    TauCeti.FormalDistribution.mulSub (iotasumNeg F₁ + iotasumPos F₂) =
      iotasumNeg (mulSub₂₃ F₁) + iotasumPos (mulSub₂₃ F₂) := by
  ext m₂ m₃
  obtain ⟨K₁, hK₁⟩ := h₁ m₃
  obtain ⟨K₁', hK₁'⟩ := h₁ (m₃ + 1)
  obtain ⟨K₂, hK₂⟩ := h₂ m₃
  obtain ⟨K₂', hK₂'⟩ := h₂ (m₃ + 1)
  let M₁ : ℕ := max K₁ K₁'
  let P := M₁ + m₂.natAbs + 1
  let Q := max K₂ K₂'
  have b₁ (m₂' m₃' : ℤ) (hm : m₂ ≤ m₂') (hK : ∀ a b, (M₁ : ℤ) ≤ b → F₁ a b m₃' = 0) :
      ∀ i : ℕ, P ≤ i → F₁ (-(i : ℤ) - 1) (m₂' + i) m₃' = 0 := fun i hi ↦ hK _ _ (by omega)
  have hk₁ (a b : ℤ) (hb : (M₁ : ℤ) ≤ b) : F₁ a b m₃ = 0 :=
    hK₁ a b (le_trans (Nat.cast_le.mpr (le_max_left K₁ K₁')) hb)
  have hk₁' (a b : ℤ) (hb : (M₁ : ℤ) ≤ b) : F₁ a b (m₃ + 1) = 0 :=
    hK₁' a b (le_trans (Nat.cast_le.mpr (le_max_right K₁ K₁')) hb)
  have b₂ (m₂' : ℤ) : ∀ i : ℕ, Q ≤ i → F₂ i (m₂' - i - 1) m₃ = 0 := fun i hi ↦
    hK₂ _ _ (le_trans (Nat.cast_le.mpr (le_max_left K₂ K₂')) (Nat.cast_le.mpr hi))
  have b₂' (m₂' : ℤ) : ∀ i : ℕ, Q ≤ i → F₂ i (m₂' - i - 1) (m₃ + 1) = 0 := fun i hi ↦
    hK₂' _ _ (le_trans (Nat.cast_le.mpr (le_max_right K₂ K₂')) (Nat.cast_le.mpr hi))
  have bN (i : ℕ) (hi : P ≤ i) : mulSub₂₃ F₁ (-(i : ℤ) - 1) (m₂ + i) m₃ = 0 := by
    rw [mulSub₂₃_apply, show m₂ + (i : ℤ) + 1 = m₂ + 1 + i by ring,
      b₁ (m₂ + 1) m₃ (by omega) hk₁ i hi, b₁ m₂ (m₃ + 1) le_rfl hk₁' i hi, sub_zero]
  have bP (i : ℕ) (hi : Q ≤ i) : mulSub₂₃ F₂ i (m₂ - i - 1) m₃ = 0 := by
    rw [mulSub₂₃_apply, show m₂ - (i : ℤ) - 1 + 1 = m₂ + 1 - i - 1 by ring,
      b₂ (m₂ + 1) i hi, b₂' m₂ i hi, sub_zero]
  simp only [TauCeti.FormalDistribution.mulSub_apply, Pi.add_apply,
    iotasumNeg_eq_sum (b₁ (m₂ + 1) m₃ (by omega) hk₁),
    iotasumNeg_eq_sum (b₁ m₂ (m₃ + 1) le_rfl hk₁'),
    iotasumPos_eq_sum (b₂ (m₂ + 1)), iotasumPos_eq_sum (b₂' m₂),
    iotasumNeg_eq_sum bN, iotasumPos_eq_sum bP]
  have e₁ : ∀ i ∈ range P, mulSub₂₃ F₁ (-(i : ℤ) - 1) (m₂ + i) m₃ =
      F₁ (-(i : ℤ) - 1) (m₂ + 1 + i) m₃ - F₁ (-(i : ℤ) - 1) (m₂ + i) (m₃ + 1) := fun i _ ↦ by
    simp only [mulSub₂₃_apply, show m₂ + (i : ℤ) + 1 = m₂ + 1 + i by ring]
  have e₂ : ∀ i ∈ range Q, mulSub₂₃ F₂ i (m₂ - i - 1) m₃ =
      F₂ i (m₂ + 1 - i - 1) m₃ - F₂ i (m₂ - i - 1) (m₃ + 1) := fun i _ ↦ by
    simp only [mulSub₂₃_apply, show m₂ - (i : ℤ) - 1 + 1 = m₂ + 1 - i - 1 by ring]
  rw [sum_congr rfl e₁, sum_congr rfl e₂, sum_sub_distrib, sum_sub_distrib]
  abel

private theorem mulSub_pow_iotasum :
    ∀ (k : ℕ) {F₁ F₂ : Dist3 M}, Truncated₂ F₁ → Truncated₁ F₂ →
      (TauCeti.FormalDistribution.mulSub ^ k) (iotasumNeg F₁ + iotasumPos F₂) =
        iotasumNeg ((mulSub₂₃ ^ k) F₁) + iotasumPos ((mulSub₂₃ ^ k) F₂)
  | 0, _, _, _, _ => by simp
  | k + 1, F₁, F₂, h₁, h₂ => by
    rw [pow_succ', end_mul_apply, mulSub_pow_iotasum k h₁ h₂,
      mulSub_iotasum (truncated₂_pow truncated₂_mulSub₂₃ k h₁)
        (truncated₁_pow truncated₁_mulSub₂₃ k h₂),
      pow_succ', end_mul_apply, end_mul_apply]

private theorem iotasumNeg_mulSub₁₂ {G : Dist3 M} (hG : Truncated₂ G) (m₂ m₃ : ℤ) :
    iotasumNeg (mulSub₁₂ G) m₂ m₃ = G 0 m₂ m₃ := by
  obtain ⟨K, hK⟩ := hG m₃
  let P := K + m₂.natAbs + 1
  have hb (i : ℕ) (hi : P ≤ i) : mulSub₁₂ G (-(i : ℤ) - 1) (m₂ + i) m₃ = 0 := by
    have h₁ : (K : ℤ) ≤ m₂ + i := by omega
    have h₂ : (K : ℤ) ≤ m₂ + i + 1 := by omega
    rw [mulSub₁₂_apply, hK _ _ h₁, hK _ _ h₂, sub_zero]
  rw [iotasumNeg_eq_sum hb]
  have e : ∀ i ∈ range P, mulSub₁₂ G (-(i : ℤ) - 1) (m₂ + i) m₃ =
      G (-(i : ℤ)) (m₂ + i) m₃ - G (-((i + 1 : ℕ) : ℤ)) (m₂ + (i + 1 : ℕ)) m₃ := fun i _ ↦ by
    simp only [mulSub₁₂_apply]
    congr 2 <;> (push_cast; ring)
  rw [sum_congr rfl e, sum_range_sub' (fun i : ℕ ↦ G (-(i : ℤ)) (m₂ + i) m₃) P,
    hK _ _ (by omega : (K : ℤ) ≤ m₂ + P)]
  simp

private theorem iotasumPos_mulSub₁₂ {G : Dist3 M} (hG : Truncated₁ G) (m₂ m₃ : ℤ) :
    iotasumPos (mulSub₁₂ G) m₂ m₃ = -G 0 m₂ m₃ := by
  obtain ⟨K, hK⟩ := hG m₃
  let Q := K + 1
  have hb (i : ℕ) (hi : Q ≤ i) : mulSub₁₂ G i (m₂ - i - 1) m₃ = 0 := by
    have h₁ : (K : ℤ) ≤ i + 1 := by omega
    have h₂ : (K : ℤ) ≤ i := by omega
    rw [mulSub₁₂_apply, hK _ _ h₁, hK _ _ h₂, sub_zero]
  rw [iotasumPos_eq_sum hb]
  have e : ∀ i ∈ range Q, mulSub₁₂ G i (m₂ - i - 1) m₃ =
      G ((i + 1 : ℕ) : ℤ) (m₂ - (i + 1 : ℕ)) m₃ - G (i : ℤ) (m₂ - (i : ℤ)) m₃ := fun i _ ↦ by
    simp only [mulSub₁₂_apply]
    congr 2 <;> (push_cast; ring)
  rw [sum_congr rfl e, sum_range_sub (fun i : ℕ ↦ G (i : ℤ) (m₂ - i) m₃) Q,
    hK _ _ (by omega : (K : ℤ) ≤ Q)]
  simp

private theorem iotasumNeg_sum {ι : Type*} (s : Finset ι) (F : ι → Dist3 M)
    (hF : ∀ x ∈ s, Truncated₂ (F x)) (m₂ m₃ : ℤ) :
    iotasumNeg (∑ x ∈ s, F x) m₂ m₃ = ∑ x ∈ s, iotasumNeg (F x) m₂ m₃ := by
  classical
  choose K hK using fun x : {x // x ∈ s} ↦ hF x.1 x.2 m₃
  let P := (univ.sup K) + m₂.natAbs + 1
  have hb (x : ι) (hx : x ∈ s) (i : ℕ) (hi : P ≤ i) :
      F x (-(i : ℤ) - 1) (m₂ + i) m₃ = 0 := by
    have hle : K (⟨x, hx⟩ : {x // x ∈ s}) ≤ univ.sup K :=
      le_sup (mem_univ (⟨x, hx⟩ : {x // x ∈ s}))
    exact hK ⟨x, hx⟩ _ _ (by omega)
  rw [iotasumNeg_eq_sum (P := P) fun i hi ↦ by
    simp only [Finset.sum_apply]
    exact sum_eq_zero fun x hx ↦ hb x hx i hi]
  simp only [Finset.sum_apply]
  rw [sum_comm]
  exact sum_congr rfl fun x hx ↦ (iotasumNeg_eq_sum (hb x hx)).symm

private theorem iotasumPos_sum {ι : Type*} (s : Finset ι) (F : ι → Dist3 M)
    (hF : ∀ x ∈ s, Truncated₁ (F x)) (m₂ m₃ : ℤ) :
    iotasumPos (∑ x ∈ s, F x) m₂ m₃ = ∑ x ∈ s, iotasumPos (F x) m₂ m₃ := by
  classical
  choose K hK using fun x : {x // x ∈ s} ↦ hF x.1 x.2 m₃
  let Q := (univ.sup K) + 1
  have hb (x : ι) (hx : x ∈ s) (i : ℕ) (hi : Q ≤ i) : F x i (m₂ - i - 1) m₃ = 0 := by
    have hle : K (⟨x, hx⟩ : {x // x ∈ s}) ≤ univ.sup K :=
      le_sup (mem_univ (⟨x, hx⟩ : {x // x ∈ s}))
    exact hK ⟨x, hx⟩ _ _ (by omega)
  rw [iotasumPos_eq_sum (Q := Q) fun i hi ↦ by
    simp only [Finset.sum_apply]
    exact sum_eq_zero fun x hx ↦ hb x hx i hi]
  simp only [Finset.sum_apply]
  rw [sum_comm]
  exact sum_congr rfl fun x hx ↦ (iotasumPos_eq_sum (hb x hx)).symm

private theorem dong_iotasum_term_pos {D₁ D₂ : Dist3 M} {N₁ N₂ N₃ p k : ℕ}
    (hT₁ : Truncated₂ D₁) (hT₂ : Truncated₁ D₂)
    (h₁₂ : (mulSub₁₂ ^ N₁) (D₁ - D₂) = 0) (hk : N₁ ≤ k) (m₂ m₃ : ℤ) :
    iotasumNeg (((N₁ + N₂ + 1).choose p • (-1 : ℤ) ^ (k + 1) •
      (mulSub₁₃ ^ p * mulSub₁₂ ^ (k + 1) : AddMonoid.End (Dist3 M)))
        ((mulSub₂₃ ^ N₃) D₁)) m₂ m₃ +
    iotasumPos (((N₁ + N₂ + 1).choose p • (-1 : ℤ) ^ (k + 1) •
      (mulSub₁₃ ^ p * mulSub₁₂ ^ (k + 1) : AddMonoid.End (Dist3 M)))
        ((mulSub₂₃ ^ N₃) D₂)) m₂ m₃ = 0 := by
  let c := ((N₁ + N₂ + 1).choose p : ℤ) * (-1 : ℤ) ^ (k + 1)
  let G (D : Dist3 M) : Dist3 M :=
    c • ((mulSub₁₃ ^ p * mulSub₁₂ ^ k * mulSub₂₃ ^ N₃ : AddMonoid.End (Dist3 M)) D)
  have hGeq : G D₁ = G D₂ := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hd : (mulSub₁₂ ^ (N₁ + d)) ((mulSub₂₃ ^ N₃) (D₁ - D₂)) = 0 := by
      rw [← end_mul_apply, ((commute_mulSub₂₃_mulSub₁₂.pow_left N₃).pow_right (N₁ + d)).symm,
        add_comm N₁ d, pow_add, end_mul_apply, end_mul_apply, h₁₂, map_zero, map_zero]
    refine sub_eq_zero.mp ?_
    change c • ((mulSub₁₃ ^ p * mulSub₁₂ ^ (N₁ + d) * mulSub₂₃ ^ N₃ :
      AddMonoid.End (Dist3 M)) D₁) -
      c • ((mulSub₁₃ ^ p * mulSub₁₂ ^ (N₁ + d) * mulSub₂₃ ^ N₃ :
        AddMonoid.End (Dist3 M)) D₂) = 0
    rw [← smul_sub, ← map_sub, mul_assoc, end_mul_apply, end_mul_apply, hd, map_zero, smul_zero]
  have rwG (D : Dist3 M) :
      ((N₁ + N₂ + 1).choose p • (-1 : ℤ) ^ (k + 1) •
        (mulSub₁₃ ^ p * mulSub₁₂ ^ (k + 1) : AddMonoid.End (Dist3 M))) ((mulSub₂₃ ^ N₃) D) =
        mulSub₁₂ (G D) := by
    change ((N₁ + N₂ + 1).choose p • (-1 : ℤ) ^ (k + 1) •
      (mulSub₁₃ ^ p * mulSub₁₂ ^ (k + 1) : AddMonoid.End (Dist3 M))) ((mulSub₂₃ ^ N₃) D) =
      mulSub₁₂ ((((N₁ + N₂ + 1).choose p : ℤ) * (-1 : ℤ) ^ (k + 1)) •
        ((mulSub₁₃ ^ p * mulSub₁₂ ^ k * mulSub₂₃ ^ N₃ : AddMonoid.End (Dist3 M)) D))
    rw [end_nsmul_apply, end_zsmul_apply, mul_smul, natCast_zsmul, map_nsmul, map_zsmul]
    congr 2
    rw [pow_succ', ← mul_assoc, (commute_mulSub₁₃_mulSub₁₂.pow_left p).eq,
      mul_assoc, mul_assoc, end_mul_apply, end_mul_apply, end_mul_apply, end_mul_apply]
  have hTG₁ : Truncated₂ (G D₁) := fun m₃' ↦ by
    obtain ⟨K, hK⟩ := truncated₂_pow_mulSub p k N₃ hT₁ m₃'
    exact ⟨K, fun m₁' m₂' hm ↦ (congrArg (c • ·) (hK m₁' m₂' hm)).trans (smul_zero c)⟩
  have hTG₂ : Truncated₁ (G D₂) := fun m₃' ↦ by
    obtain ⟨K, hK⟩ := truncated₁_pow_mulSub p k N₃ hT₂ m₃'
    exact ⟨K, fun m₁' m₂' hm ↦ (congrArg (c • ·) (hK m₁' m₂' hm)).trans (smul_zero c)⟩
  rw [rwG D₁, rwG D₂, iotasumNeg_mulSub₁₂ hTG₁, iotasumPos_mulSub₁₂ hTG₂, ← sub_eq_add_neg]
  exact sub_eq_zero.mpr (congrFun (congrFun (congrFun hGeq 0) m₂) m₃)

private theorem dong_iotasum_term {D₁ D₂ : Dist3 M} {N₁ N₂ N₃ : ℕ}
    (hT₁ : Truncated₂ D₁) (hT₂ : Truncated₁ D₂)
    (h₁₂ : (mulSub₁₂ ^ N₁) (D₁ - D₂) = 0)
    (h₁ : (mulSub₁₃ ^ N₂) ((mulSub₂₃ ^ N₃) D₁) = 0)
    (h₂ : (mulSub₁₃ ^ N₂) ((mulSub₂₃ ^ N₃) D₂) = 0)
    {pq : ℕ × ℕ} (hpq : pq ∈ antidiagonal (N₁ + N₂ + 1)) (m₂ m₃ : ℤ) :
    iotasumNeg (((N₁ + N₂ + 1).choose pq.1 • (-1 : ℤ) ^ pq.2 •
      (mulSub₁₃ ^ pq.1 * mulSub₁₂ ^ pq.2 : AddMonoid.End (Dist3 M)))
        ((mulSub₂₃ ^ N₃) D₁)) m₂ m₃ +
    iotasumPos (((N₁ + N₂ + 1).choose pq.1 • (-1 : ℤ) ^ pq.2 •
      (mulSub₁₃ ^ pq.1 * mulSub₁₂ ^ pq.2 : AddMonoid.End (Dist3 M)))
        ((mulSub₂₃ ^ N₃) D₂)) m₂ m₃ = 0 := by
  by_cases hp : N₂ ≤ pq.1
  · obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hp
    have kill (D : Dist3 M) (hD : (mulSub₁₃ ^ N₂) ((mulSub₂₃ ^ N₃) D) = 0) :
        (mulSub₁₃ ^ (N₂ + r) * mulSub₁₂ ^ pq.2 : AddMonoid.End (Dist3 M))
          ((mulSub₂₃ ^ N₃) D) = 0 := by
      rw [(commute_mulSub₁₃_mulSub₁₂.pow_left _).pow_right _, add_comm N₂ r, pow_add,
        end_mul_apply, end_mul_apply, hD, map_zero, map_zero]
    rw [hr, end_nsmul_apply, end_zsmul_apply, end_nsmul_apply, end_zsmul_apply,
      kill D₁ h₁, kill D₂ h₂]
    simp [iotasumNeg, iotasumPos]
  · obtain ⟨k, hq, hk⟩ : ∃ k, pq.2 = k + 1 ∧ N₁ ≤ k :=
      ⟨pq.2 - 1, by have := mem_antidiagonal.mp hpq; omega,
        by have := mem_antidiagonal.mp hpq; omega⟩
    rw [hq]
    exact dong_iotasum_term_pos hT₁ hT₂ h₁₂ hk m₂ m₃

private theorem dong_iotasum {D₁ D₂ : Dist3 M} {N₁ N₂ N₃ : ℕ}
    (hT₁ : Truncated₂ D₁) (hT₂ : Truncated₁ D₂)
    (h₁₂ : (mulSub₁₂ ^ N₁) (D₁ - D₂) = 0)
    (h₁ : (mulSub₁₃ ^ N₂) ((mulSub₂₃ ^ N₃) D₁) = 0)
    (h₂ : (mulSub₁₃ ^ N₂) ((mulSub₂₃ ^ N₃) D₂) = 0) :
    (TauCeti.FormalDistribution.mulSub ^ (N₁ + N₂ + N₃ + 1))
      (iotasumNeg D₁ + iotasumPos D₂) = 0 := by
  rw [mulSub_pow_iotasum _ hT₁ hT₂]
  have hexp : N₁ + N₂ + N₃ + 1 = (N₁ + N₂ + 1) + N₃ := by omega
  ext m₂ m₃
  rw [Pi.add_apply, Pi.add_apply, hexp, pow_add, end_mul_apply, end_mul_apply,
    mulSub₂₃_pow_eq_sum (N₁ + N₂ + 1), end_sum_apply, end_sum_apply]
  have hS₁ : ∀ pq ∈ antidiagonal (N₁ + N₂ + 1),
      Truncated₂ (((N₁ + N₂ + 1).choose pq.1 • (-1 : ℤ) ^ pq.2 •
        (mulSub₁₃ ^ pq.1 * mulSub₁₂ ^ pq.2 : AddMonoid.End (Dist3 M)))
          ((mulSub₂₃ ^ N₃) D₁)) := fun pq _ m₃' ↦ by
    obtain ⟨K, hK⟩ := truncated₂_pow_mulSub pq.1 pq.2 N₃ hT₁ m₃'
    refine ⟨K, fun m₁' m₂' hm ↦ ?_⟩
    rw [end_nsmul_apply, end_zsmul_apply]
    simp only [Pi.smul_apply, mul_assoc, end_mul_apply] at hK ⊢
    rw [hK m₁' m₂' hm, smul_zero, smul_zero]
  have hS₂ : ∀ pq ∈ antidiagonal (N₁ + N₂ + 1),
      Truncated₁ (((N₁ + N₂ + 1).choose pq.1 • (-1 : ℤ) ^ pq.2 •
        (mulSub₁₃ ^ pq.1 * mulSub₁₂ ^ pq.2 : AddMonoid.End (Dist3 M)))
          ((mulSub₂₃ ^ N₃) D₂)) := fun pq _ m₃' ↦ by
    obtain ⟨K, hK⟩ := truncated₁_pow_mulSub pq.1 pq.2 N₃ hT₂ m₃'
    refine ⟨K, fun m₁' m₂' hm ↦ ?_⟩
    rw [end_nsmul_apply, end_zsmul_apply]
    simp only [Pi.smul_apply, mul_assoc, end_mul_apply] at hK ⊢
    rw [hK m₁' m₂' hm, smul_zero, smul_zero]
  rw [iotasumNeg_sum _ _ hS₁, iotasumPos_sum _ _ hS₂, ← sum_add_distrib, Pi.zero_apply,
    Pi.zero_apply]
  exact sum_eq_zero fun pq hpq ↦ dong_iotasum_term hT₁ hT₂ h₁₂ h₁ h₂ hpq m₂ m₃

end Dist3

/-! ### Dong's lemma on vertex operators -/

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private theorem mulSub₁₂_pow_commutator {N : ℕ} {X Y : VertexOperator R V}
    (h : X.IsLocalOfOrder Y N) (L : ℤ → V →ₗ[R] V) (R' : ℤ → V) :
    (mulSub₁₂ ^ N) (fun m₁ m₂ m₃ ↦ L m₃ ((X.commutatorDistribution Y m₁ m₂) (R' m₃))) = 0 := by
  ext m₁ m₂ m₃
  have key : ∀ k a b,
      (mulSub₁₂ ^ k) (fun p q r ↦ L r ((X.commutatorDistribution Y p q) (R' r))) a b m₃ =
        L m₃ (((TauCeti.FormalDistribution.mulSub ^ k) (X.commutatorDistribution Y) a b)
          (R' m₃)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro a b
      rw [pow_succ', end_mul_apply, mulSub₁₂_apply, ih, ih, pow_succ', end_mul_apply,
        TauCeti.FormalDistribution.mulSub_apply, LinearMap.sub_apply, map_sub]
  rw [key, (isLocalOfOrder_iff_mulSub_pow_eq_zero X Y N).mp h]
  simp

private theorem mulSub₁₃_pow_commutator {N : ℕ} {X Y : VertexOperator R V}
    (h : X.IsLocalOfOrder Y N) (L : ℤ → V →ₗ[R] V) (R' : ℤ → V) :
    (mulSub₁₃ ^ N) (fun m₁ m₂ m₃ ↦ L m₂ ((X.commutatorDistribution Y m₁ m₃) (R' m₂))) = 0 := by
  ext m₁ m₂ m₃
  have key : ∀ k a c,
      (mulSub₁₃ ^ k) (fun p q r ↦ L q ((X.commutatorDistribution Y p r) (R' q))) a m₂ c =
        L m₂ (((TauCeti.FormalDistribution.mulSub ^ k) (X.commutatorDistribution Y) a c)
          (R' m₂)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro a c
      rw [pow_succ', end_mul_apply, mulSub₁₃_apply, ih, ih, pow_succ', end_mul_apply,
        TauCeti.FormalDistribution.mulSub_apply, LinearMap.sub_apply, map_sub]
  rw [key, (isLocalOfOrder_iff_mulSub_pow_eq_zero X Y N).mp h]
  simp

private theorem mulSub₂₃_pow_commutator {N : ℕ} {X Y : VertexOperator R V}
    (h : X.IsLocalOfOrder Y N) (L : ℤ → V →ₗ[R] V) (R' : ℤ → V) :
    (mulSub₂₃ ^ N) (fun m₁ m₂ m₃ ↦ L m₁ ((X.commutatorDistribution Y m₂ m₃) (R' m₁))) = 0 := by
  ext m₁ m₂ m₃
  have key : ∀ k b c,
      (mulSub₂₃ ^ k) (fun p q r ↦ L p ((X.commutatorDistribution Y q r) (R' p))) m₁ b c =
        L m₁ (((TauCeti.FormalDistribution.mulSub ^ k) (X.commutatorDistribution Y) b c)
          (R' m₁)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro b c
      rw [pow_succ', end_mul_apply, mulSub₂₃_apply, ih, ih, pow_succ', end_mul_apply,
        TauCeti.FormalDistribution.mulSub_apply, LinearMap.sub_apply, map_sub]
  rw [key, (isLocalOfOrder_iff_mulSub_pow_eq_zero X Y N).mp h]
  simp

private theorem dong_dist3_relations {A B C : VertexOperator R V} {N₁ N₂ N₃ : ℕ}
    (hAB : A.IsLocalOfOrder B N₁) (hAC : A.IsLocalOfOrder C N₂) (hBC : B.IsLocalOfOrder C N₃)
    (v : V) :
    let D₁ : Dist3 V := fun m₁ m₂ m₃ ↦
      (A[[m₁]]) ((B[[m₂]]) ((C[[m₃]]) v)) - (C[[m₃]]) ((A[[m₁]]) ((B[[m₂]]) v))
    let D₂ : Dist3 V := fun m₁ m₂ m₃ ↦
      (B[[m₂]]) ((A[[m₁]]) ((C[[m₃]]) v)) - (C[[m₃]]) ((B[[m₂]]) ((A[[m₁]]) v))
    Truncated₂ D₁ ∧ Truncated₁ D₂ ∧
      (mulSub₁₂ ^ N₁) (D₁ - D₂) = 0 ∧
      (mulSub₁₃ ^ N₂) ((mulSub₂₃ ^ N₃) D₁) = 0 ∧
      (mulSub₁₃ ^ N₂) ((mulSub₂₃ ^ N₃) D₂) = 0 := by
  intro D₁ D₂
  have hT₁ : Truncated₂ D₁ := fun m₃ ↦ by
    obtain ⟨K₁, hK₁⟩ := B.exists_forall_ncoeff_apply_eq_zero ((C[[m₃]]) v)
    obtain ⟨K₂, hK₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
    exact ⟨max K₁ K₂, fun m₁ m₂ hm ↦ by
      simp [D₁, hK₁ _ (le_trans (Nat.cast_le.mpr (le_max_left _ _)) hm),
        hK₂ _ (le_trans (Nat.cast_le.mpr (le_max_right _ _)) hm)]⟩
  have hT₂ : Truncated₁ D₂ := fun m₃ ↦ by
    obtain ⟨K₁, hK₁⟩ := A.exists_forall_ncoeff_apply_eq_zero ((C[[m₃]]) v)
    obtain ⟨K₂, hK₂⟩ := A.exists_forall_ncoeff_apply_eq_zero v
    exact ⟨max K₁ K₂, fun m₁ m₂ hm ↦ by
      simp [D₂, hK₁ _ (le_trans (Nat.cast_le.mpr (le_max_left _ _)) hm),
        hK₂ _ (le_trans (Nat.cast_le.mpr (le_max_right _ _)) hm)]⟩
  have h₁₂ : (mulSub₁₂ ^ N₁) (D₁ - D₂) = 0 := by
    have e : D₁ - D₂ =
        (fun m₁ m₂ m₃ ↦ LinearMap.id (R := R) ((A.commutatorDistribution B m₁ m₂) ((C[[m₃]]) v))) -
        (fun m₁ m₂ m₃ ↦ (C[[m₃]]) ((A.commutatorDistribution B m₁ m₂) v)) := by
      ext m₁ m₂ m₃
      simp only [Pi.sub_apply, D₁, D₂, LinearMap.id_apply, commutatorDistribution_apply,
        LinearMap.sub_apply, mul_apply_eq_comp, map_sub]
      abel
    rw [e, map_sub, mulSub₁₂_pow_commutator hAB _ _, mulSub₁₂_pow_commutator hAB _ _, sub_zero]
  have hD₁ : (mulSub₁₃ ^ N₂) ((mulSub₂₃ ^ N₃) D₁) = 0 := by
    have e₁ : D₁ =
        (fun m₁ m₂ m₃ ↦ (A[[m₁]]) ((B.commutatorDistribution C m₂ m₃) v)) +
        (fun m₁ m₂ m₃ ↦
          LinearMap.id (R := R) ((A.commutatorDistribution C m₁ m₃) ((B[[m₂]]) v))) := by
      ext m₁ m₂ m₃
      simp only [Pi.add_apply, D₁, LinearMap.id_apply, commutatorDistribution_apply,
        LinearMap.sub_apply, mul_apply_eq_comp, map_sub]
      abel
    rw [e₁, map_add, map_add, mulSub₂₃_pow_commutator hBC _ _, map_zero, zero_add,
      ← end_mul_apply, ((commute_mulSub₂₃_mulSub₁₃.pow_left N₃).pow_right N₂).symm,
      end_mul_apply, mulSub₁₃_pow_commutator hAC _ _, map_zero]
  have hD₂ : (mulSub₁₃ ^ N₂) ((mulSub₂₃ ^ N₃) D₂) = 0 := by
    have e₂ : D₂ =
        (fun m₁ m₂ m₃ ↦ (B[[m₂]]) ((A.commutatorDistribution C m₁ m₃) v)) +
        (fun m₁ m₂ m₃ ↦
          LinearMap.id (R := R) ((B.commutatorDistribution C m₂ m₃) ((A[[m₁]]) v))) := by
      ext m₁ m₂ m₃
      simp only [Pi.add_apply, D₂, LinearMap.id_apply, commutatorDistribution_apply,
        LinearMap.sub_apply, mul_apply_eq_comp, map_sub]
      abel
    rw [e₂, map_add, map_add, mulSub₂₃_pow_commutator hBC _ _, map_zero, add_zero,
      ← end_mul_apply, ((commute_mulSub₂₃_mulSub₁₃.pow_left N₃).pow_right N₂).symm,
      end_mul_apply, mulSub₁₃_pow_commutator hAC _ _, map_zero]
  exact ⟨hT₁, hT₂, h₁₂, hD₁, hD₂⟩

private theorem res0_mulSub₁₂_pow_commutator (A B C : VertexOperator R V) (n : ℕ) (v : V)
    (m₂ m₃ : ℤ) :
    let D₁ : Dist3 V := fun m₁ m₂ m₃ ↦
      (A[[m₁]]) ((B[[m₂]]) ((C[[m₃]]) v)) - (C[[m₃]]) ((A[[m₁]]) ((B[[m₂]]) v))
    let D₂ : Dist3 V := fun m₁ m₂ m₃ ↦
      (B[[m₂]]) ((A[[m₁]]) ((C[[m₃]]) v)) - (C[[m₃]]) ((B[[m₂]]) ((A[[m₁]]) v))
    (mulSub₁₂ ^ n) (D₁ - D₂) 0 m₂ m₃ =
      (((nonnegResidueProduct n A B).commutatorDistribution C m₂ m₃) v) := by
  intro D₁ D₂
  have eqk : ∀ r x y, (mulSub₁₂ ^ r) (D₁ - D₂) x y m₃ =
      (TauCeti.FormalDistribution.mulSub ^ r) (fun p q ↦ (D₁ - D₂) p q m₃) x y := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      intro x y
      rw [pow_succ', end_mul_apply, mulSub₁₂_apply, ih, ih, pow_succ', end_mul_apply,
        TauCeti.FormalDistribution.mulSub_apply]
  rw [eqk, TauCeti.FormalDistribution.mulSub_pow_apply]
  simp only [zero_add, commutatorDistribution_apply, ncoeff_nonnegResidueProduct,
    LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    map_nsmul, map_zsmul, ← sum_sub_distrib]
  refine sum_congr rfl fun ij _ ↦ ?_
  simp only [Pi.sub_apply, D₁, D₂, map_sub, smul_sub]
  abel

namespace IsLocalOfOrder

/-- **Dong's lemma** for nonnegative residue products: if `(A, B)`, `(A, C)` and `(B, C)` are
mutually local of orders `N₁`, `N₂`, `N₃`, then `Res_z (z - w)ⁿ [A(z), B(w)]` is local with `C`
of order `N₁ + N₂ + N₃`, over any commutative ring. -/
theorem nonnegResidueProduct_left {A B C : VertexOperator R V} {N₁ N₂ N₃ : ℕ}
    (hAB : A.IsLocalOfOrder B N₁) (hAC : A.IsLocalOfOrder C N₂) (hBC : B.IsLocalOfOrder C N₃)
    (n : ℕ) :
    (nonnegResidueProduct n A B).IsLocalOfOrder C (N₁ + N₂ + N₃) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  ext m₂ m₃ v
  obtain ⟨_, _, h₁₂, h₁, h₂⟩ := dong_dist3_relations hAB hAC hBC v
  let D₁ : Dist3 V := fun m₁ m₂ m₃ ↦
    (A[[m₁]]) ((B[[m₂]]) ((C[[m₃]]) v)) - (C[[m₃]]) ((A[[m₁]]) ((B[[m₂]]) v))
  let D₂ : Dist3 V := fun m₁ m₂ m₃ ↦
    (B[[m₂]]) ((A[[m₁]]) ((C[[m₃]]) v)) - (C[[m₃]]) ((B[[m₂]]) ((A[[m₁]]) v))
  let G : Dist3 V := (mulSub₁₂ ^ n) (D₁ - D₂)
  have hGdef : G = (mulSub₁₂ ^ n) (D₁ - D₂) := rfl
  have hG₁₂ : (mulSub₁₂ ^ N₁) G = 0 := by
    rw [hGdef, ← end_mul_apply, ← pow_add, add_comm, pow_add, end_mul_apply, h₁₂, map_zero]
  have hG₁₃ : (mulSub₁₃ ^ N₂) ((mulSub₂₃ ^ N₃) G) = 0 := by
    have hcomm :=
      ((((commute_mulSub₁₃_mulSub₁₂ (M := V)).pow_left N₂).mul_left
        ((commute_mulSub₂₃_mulSub₁₂ (M := V)).pow_left N₃)).pow_right n).eq
    rw [hGdef, ← end_mul_apply, ← end_mul_apply, hcomm, end_mul_apply, end_mul_apply,
      map_sub, map_sub, h₁, h₂, sub_zero, map_zero]
  have hkill : (mulSub₂₃ ^ (N₂ + N₁)) ((mulSub₂₃ ^ N₃) G) = 0 :=
    mulSub₂₃_pow_eq_zero N₂ N₁ _ hG₁₃ (by
      rw [← end_mul_apply, ((commute_mulSub₂₃_mulSub₁₂.pow_left N₃).pow_right N₁).symm,
        end_mul_apply, hG₁₂, map_zero])
  have hcomm : ∀ k a b,
      (((TauCeti.FormalDistribution.mulSub ^ k)
        ((nonnegResidueProduct n A B).commutatorDistribution C) a b) v) =
        (mulSub₂₃ ^ k) G 0 a b := by
    intro k
    induction k with
    | zero => intro a b; exact (res0_mulSub₁₂_pow_commutator A B C n v a b).symm
    | succ k ih =>
      intro a b
      rw [pow_succ', end_mul_apply, TauCeti.FormalDistribution.mulSub_apply,
        LinearMap.sub_apply, ih, ih, pow_succ', end_mul_apply, mulSub₂₃_apply]
  have hexp : N₁ + N₂ + N₃ = (N₂ + N₁) + N₃ := by omega
  rw [hcomm, hexp, pow_add, end_mul_apply, hkill]
  rfl

/-- Symmetric form of Dong's lemma for nonnegative residue products. -/
theorem nonnegResidueProduct_right {A B C : VertexOperator R V} {N₁ N₂ N₃ : ℕ}
    (hAB : A.IsLocalOfOrder B N₁) (hAC : A.IsLocalOfOrder C N₂) (hBC : B.IsLocalOfOrder C N₃)
    (n : ℕ) :
    A.IsLocalOfOrder (nonnegResidueProduct n B C) (N₃ + N₁ + N₂) :=
  (nonnegResidueProduct_left hBC hAB.symm hAC.symm n).symm

/-- **Dong's lemma** for normal ordering: if `(A, B)`, `(A, C)` and `(B, C)` are mutually local of
orders `N₁`, `N₂`, `N₃`, then `:AB:` is local with `C` of order `N₁ + N₂ + N₃ + 1`, over any
commutative ring. -/
theorem normalOrder_left {A B C : VertexOperator R V} {N₁ N₂ N₃ : ℕ}
    (hAB : A.IsLocalOfOrder B N₁) (hAC : A.IsLocalOfOrder C N₂) (hBC : B.IsLocalOfOrder C N₃) :
    (normalOrder A B).IsLocalOfOrder C (N₁ + N₂ + N₃ + 1) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  ext m₂ m₃ v
  obtain ⟨hT₁, hT₂, h₁₂, h₁, h₂⟩ := dong_dist3_relations hAB hAC hBC v
  let D₁ : Dist3 V := fun m₁ m₂ m₃ ↦
    (A[[m₁]]) ((B[[m₂]]) ((C[[m₃]]) v)) - (C[[m₃]]) ((A[[m₁]]) ((B[[m₂]]) v))
  let D₂ : Dist3 V := fun m₁ m₂ m₃ ↦
    (B[[m₂]]) ((A[[m₁]]) ((C[[m₃]]) v)) - (C[[m₃]]) ((B[[m₂]]) ((A[[m₁]]) v))
  have hiota (a b : ℤ) :
      (((normalOrder A B).commutatorDistribution C a b) v) =
        (iotasumNeg D₁ + iotasumPos D₂) a b := by
    obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero ((C[[b]]) v)
    obtain ⟨P₂, hP₂⟩ := B.exists_forall_ncoeff_apply_eq_zero v
    obtain ⟨Q₁, hQ₁⟩ := A.exists_forall_ncoeff_apply_eq_zero ((C[[b]]) v)
    obtain ⟨Q₂, hQ₂⟩ := A.exists_forall_ncoeff_apply_eq_zero v
    let P := max P₁ P₂ + a.natAbs
    let Q := max Q₁ Q₂
    have bP₁ (i : ℕ) (hi : P ≤ i) : (B[[a + i]]) ((C[[b]]) v) = 0 :=
      hP₁ _ (by have := le_max_left P₁ P₂; omega)
    have bP₂ (i : ℕ) (hi : P ≤ i) : (B[[a + i]]) v = 0 :=
      hP₂ _ (by have := le_max_right P₁ P₂; omega)
    have bQ₁ (i : ℕ) (hi : Q ≤ i) : (A[[(i : ℤ)]]) ((C[[b]]) v) = 0 :=
      hQ₁ _ (by have := le_max_left Q₁ Q₂; omega)
    have bQ₂ (i : ℕ) (hi : Q ≤ i) : (A[[(i : ℤ)]]) v = 0 :=
      hQ₂ _ (by have := le_max_right Q₁ Q₂; omega)
    simp only [commutatorDistribution_apply, ncoeff_normalOrder, LinearMap.sub_apply,
      mul_apply_eq_comp, normalOrderCoeff_eq_sum A B a ((C[[b]]) v) bP₁ bQ₁,
      normalOrderCoeff_eq_sum A B a v bP₂ bQ₂, map_add, map_sum, Pi.add_apply]
    rw [iotasumNeg_eq_sum (P := P) fun i hi ↦ by simp [D₁, bP₁ i hi, bP₂ i hi],
      iotasumPos_eq_sum (Q := Q) fun i hi ↦ by simp [D₂, bQ₁ i hi, bQ₂ i hi],
      sum_sub_distrib, sum_sub_distrib]
    abel
  have hcomm : ∀ k a b,
      (((TauCeti.FormalDistribution.mulSub ^ k)
        ((normalOrder A B).commutatorDistribution C) a b) v) =
        (TauCeti.FormalDistribution.mulSub ^ k) (iotasumNeg D₁ + iotasumPos D₂) a b := by
    intro k
    induction k with
    | zero => intro a b; simpa using hiota a b
    | succ k ih =>
      intro a b
      rw [pow_succ', end_mul_apply, TauCeti.FormalDistribution.mulSub_apply,
        LinearMap.sub_apply, ih, ih, pow_succ', end_mul_apply,
        TauCeti.FormalDistribution.mulSub_apply]
  rw [hcomm, dong_iotasum hT₁ hT₂ h₁₂ h₁ h₂]
  rfl

/-- Symmetric form of Dong's lemma for normal ordering. -/
theorem normalOrder_right {A B C : VertexOperator R V} {N₁ N₂ N₃ : ℕ}
    (hAB : A.IsLocalOfOrder B N₁) (hAC : A.IsLocalOfOrder C N₂) (hBC : B.IsLocalOfOrder C N₃) :
    A.IsLocalOfOrder (normalOrder B C) (N₃ + N₁ + N₂ + 1) :=
  (normalOrder_left hBC hAB.symm hAC.symm).symm

end IsLocalOfOrder

/-! ### Unified integer `n`-th products -/

/-- The `n`-th product `A₍ₙ₎ B` of two fields (`n : ℤ`), given for `n ≥ 0` by the residue
commutator `Res_z (z - w)ⁿ [A(z), B(w)]` (`VertexOperator.nonnegResidueProduct`) and for
`n = -k - 1 < 0` by the normal-ordered Hasse derivative `: (D^[k] A) B :`. Defined as an
`R`-bilinear map over any commutative ring. -/
def nthProduct (n : ℤ) :
    VertexOperator R V →ₗ[R] VertexOperator R V →ₗ[R] VertexOperator R V :=
  if 0 ≤ n then nonnegResidueProduct n.toNat
  else normalOrderₗ.comp (hasseDeriv (-n - 1).toNat)

/-- For `n ≥ 0`, `nthProduct n` is `nonnegResidueProduct n.toNat`. -/
theorem nthProduct_of_nonneg {n : ℤ} (hn : 0 ≤ n) (A B : VertexOperator R V) :
    nthProduct n A B = nonnegResidueProduct n.toNat A B := by
  simp [nthProduct, hn]

/-- On natural numbers, `nthProduct (n : ℤ)` is `nonnegResidueProduct n`. -/
@[simp]
theorem nthProduct_natCast (n : ℕ) (A B : VertexOperator R V) :
    nthProduct (n : ℤ) A B = nonnegResidueProduct n A B := by
  simp [nthProduct]

/-- For `n < 0`, `nthProduct n A B` is `: (D^[(-n - 1).toNat] A) B :`. -/
theorem nthProduct_of_neg {n : ℤ} (hn : n < 0) (A B : VertexOperator R V) :
    nthProduct n A B = normalOrder (hasseDeriv (-n - 1).toNat A) B := by
  simp [nthProduct, hn.not_ge]

/-- The `(-1)`-product is the normal-ordered product `:AB:`. -/
@[simp]
theorem nthProduct_neg_one (A B : VertexOperator R V) :
    nthProduct (-1) A B = normalOrder A B := by
  simp [nthProduct]

/-- The `(-k - 1)`-product is `: (D^[k] A) B :`. -/
@[simp]
theorem nthProduct_neg_succ (k : ℕ) (A B : VertexOperator R V) :
    nthProduct (-(k : ℤ) - 1) A B = normalOrder (hasseDeriv k A) B := by
  rw [nthProduct_of_neg (by omega), show (-(-(k : ℤ) - 1) - 1).toNat = k by omega]

namespace IsLocalOfOrder

/-- **Dong's lemma** for all integer `n`-th products: pairwise locality of `(A, B)`, `(A, C)` and
`(B, C)` implies locality of `(nthProduct n A B, C)` over any commutative ring. -/
theorem nthProduct_left {A B C : VertexOperator R V} {N₁ N₂ N₃ : ℕ}
    (hAB : A.IsLocalOfOrder B N₁) (hAC : A.IsLocalOfOrder C N₂) (hBC : B.IsLocalOfOrder C N₃)
    (n : ℤ) :
    (nthProduct n A B).IsLocalOfOrder C (N₁ + N₂ + N₃ + 2 * (-n).toNat) := by
  rcases le_or_gt 0 n with hn | hn
  · have hto : (-n).toNat = 0 := by omega
    rw [nthProduct_of_nonneg hn, hto, mul_zero, add_zero]
    exact nonnegResidueProduct_left hAB hAC hBC n.toNat
  · rw [nthProduct_of_neg hn]
    refine (normalOrder_left (hAB.hasseDeriv_left _) (hAC.hasseDeriv_left _) hBC).mono ?_
    omega

/-- Symmetric form of Dong's lemma for all integer `n`-th products. -/
theorem nthProduct_right {A B C : VertexOperator R V} {N₁ N₂ N₃ : ℕ}
    (hAB : A.IsLocalOfOrder B N₁) (hAC : A.IsLocalOfOrder C N₂) (hBC : B.IsLocalOfOrder C N₃)
    (n : ℤ) :
    A.IsLocalOfOrder (nthProduct n B C) (N₃ + N₁ + N₂ + 2 * (-n).toNat) :=
  (nthProduct_left hBC hAB.symm hAC.symm n).symm

end IsLocalOfOrder

/-! ### Formal calculus and Leibniz identities for `nthProduct` -/

/-- `(∂A)₍₀₎ B = 0` for any fields `A` and `B`. -/
@[simp]
theorem nonnegResidueProduct_derivative_left_zero (A B : VertexOperator R V) :
    nonnegResidueProduct 0 (derivative A) B = 0 := by
  apply ext_ncoeff
  intro m
  simp

/-- `(∂A)₍ₙ₊₁₎ B = -(n + 1) • A₍ₙ₎ B` for nonnegative residue products. -/
theorem nonnegResidueProduct_derivative_left_succ (n : ℕ) (A B : VertexOperator R V) :
    nonnegResidueProduct (n + 1) (derivative A) B =
      (-(n + 1 : ℤ)) • nonnegResidueProduct n A B := by
  apply ext_ncoeff
  intro m
  rw [ncoeff_nonnegResidueProduct, map_zsmul, Pi.smul_apply, ncoeff_nonnegResidueProduct]
  have e : ∀ ij ∈ antidiagonal (n + 1),
      (n + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        ((derivative A)[[(ij.1 : ℤ)]] * B[[m + ij.2]] -
          B[[m + ij.2]] * (derivative A)[[(ij.1 : ℤ)]]) =
      -((n + 1).choose ij.1 • ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(ij.1 : ℤ) - 1]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ) - 1]])) := by
    intro ij _
    rw [ncoeff_derivative, smul_mul_assoc, mul_smul_comm, ← smul_sub, neg_zsmul, natCast_zsmul,
      smul_neg, smul_neg, smul_comm ((-1 : ℤ) ^ ij.2) ij.1]
  rw [sum_congr rfl e, sum_neg_distrib]
  let g (i j : ℕ) : Module.End R V :=
    (-1 : ℤ) ^ j • (A[[(i : ℤ) - 1]] * B[[m + j]] - B[[m + j]] * A[[(i : ℤ) - 1]])
  change -(∑ ij ∈ antidiagonal (n + 1), (n + 1).choose ij.1 • ij.1 • g ij.1 ij.2) = _
  rw [sum_antidiagonal_choose_succ_nsmul_nsmul g n]
  have hg : ∀ ij ∈ antidiagonal n,
      n.choose ij.1 • g (ij.1 + 1) ij.2 =
        n.choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (A[[(ij.1 : ℤ)]] * B[[m + ij.2]] - B[[m + ij.2]] * A[[(ij.1 : ℤ)]]) := by
    intro ij _
    simp only [g, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  rw [sum_congr rfl hg, show (-(n + 1 : ℤ)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring,
    neg_zsmul, natCast_zsmul]

/-- `(∂A)₍ₙ₎ B = -n • A₍ₙ₋₁₎ B` for all integers `n : ℤ`. -/
theorem nthProduct_derivative_left (n : ℤ) (A B : VertexOperator R V) :
    nthProduct n (derivative A) B = (-n) • nthProduct (n - 1) A B := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    have h₁ : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    have h₂ : -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [nthProduct_neg_succ, h₁, nthProduct_neg_succ, h₂, natCast_zsmul, hasseDeriv_derivative,
      ← normalOrderₗ_apply, map_nsmul, LinearMap.smul_apply, normalOrderₗ_apply]
  · rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, nthProduct_natCast,
      nonnegResidueProduct_derivative_left_zero, Nat.cast_zero, neg_zero, zero_smul]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
    rw [← Nat.cast_succ, nthProduct_natCast, Nat.cast_succ, add_sub_cancel_right,
      nthProduct_natCast, nonnegResidueProduct_derivative_left_succ]

private def derivSumDist {M : Type*} [AddCommGroup M] :
    AddMonoid.End (TauCeti.FormalDistribution M) where
  toFun c m n := (-m) • c (m - 1) n + (-n) • c m (n - 1)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [smul_add]; abel

@[simp]
private theorem derivSumDist_apply {M : Type*} [AddCommGroup M]
    (c : TauCeti.FormalDistribution M) (m n : ℤ) :
    derivSumDist c m n = (-m) • c (m - 1) n + (-n) • c m (n - 1) := (rfl)

private theorem commute_derivSumDist_mulSub {M : Type*} [AddCommGroup M] :
    Commute (derivSumDist : AddMonoid.End (TauCeti.FormalDistribution M))
      TauCeti.FormalDistribution.mulSub := by
  ext c m n
  simp only [end_mul_apply, derivSumDist_apply, TauCeti.FormalDistribution.mulSub_apply,
    add_sub_cancel_right]
  have hm : m - 1 + 1 = m := by ring
  have hn : n - 1 + 1 = n := by ring
  rw [hm, hn]
  module

/-- **The Leibniz rule** for nonnegative residue products:
`∂ (A₍ₙ₎ B) = (∂A)₍ₙ₎ B + A₍ₙ₎ (∂B)`. -/
theorem derivative_nonnegResidueProduct (n : ℕ) (A B : VertexOperator R V) :
    derivative (nonnegResidueProduct n A B) =
      nonnegResidueProduct n (derivative A) B + nonnegResidueProduct n A (derivative B) := by
  have hres (X Y : VertexOperator R V) (m : ℤ) :
      (nonnegResidueProduct n X Y)[[m]] =
        TauCeti.FormalDistribution.residue
          ((TauCeti.FormalDistribution.mulSub ^ n) (X.commutatorDistribution Y)) m := by
    rw [ncoeff_nonnegResidueProduct, TauCeti.FormalDistribution.residue_apply,
      TauCeti.FormalDistribution.mulSub_pow_apply]
    refine sum_congr rfl fun ij _ ↦ ?_
    simp [commutatorDistribution_apply]
  have hcd : derivSumDist (A.commutatorDistribution B) =
      (derivative A).commutatorDistribution B + A.commutatorDistribution (derivative B) := by
    ext a b : 2
    simp only [derivSumDist_apply, Pi.add_apply, commutatorDistribution_apply, ncoeff_derivative,
      smul_mul_assoc, mul_smul_comm, smul_sub]
  apply ext_ncoeff
  intro m
  rw [ncoeff_derivative, map_add, Pi.add_apply, hres, hres, hres,
    TauCeti.FormalDistribution.residue_apply,
    show (-m) • ((TauCeti.FormalDistribution.mulSub ^ n) (A.commutatorDistribution B) 0 (m - 1)) =
      derivSumDist ((TauCeti.FormalDistribution.mulSub ^ n) (A.commutatorDistribution B)) 0 m by
      simp,
    ← end_mul_apply, (commute_derivSumDist_mulSub.pow_right n).eq,
    end_mul_apply, hcd, map_add]
  simp only [Pi.add_apply, TauCeti.FormalDistribution.residue_apply]

private theorem sum_derivative_normalOrder_left (A B : VertexOperator R V) (m : ℤ) (v : V)
    (P : ℕ) :
    ∑ i ∈ range P, ((derivative A)[[-(i : ℤ) - 1]]) ((B[[m + i]]) v) =
      ∑ i ∈ range (P + 1), (i : ℤ) • (A[[-(i : ℤ) - 1]]) ((B[[m - 1 + i]]) v) := by
  rw [sum_range_succ' (fun i : ℕ ↦ (i : ℤ) • (A[[-(i : ℤ) - 1]]) ((B[[m - 1 + i]]) v)) P]
  simp only [Nat.cast_zero, zero_smul, add_zero]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [ncoeff_derivative, LinearMap.smul_apply,
    show -(-(i : ℤ) - 1) = ((i + 1 : ℕ) : ℤ) by push_cast; ring,
    show -(i : ℤ) - 1 - 1 = -((i + 1 : ℕ) : ℤ) - 1 by push_cast; ring,
    show m + (i : ℤ) = m - 1 + ((i + 1 : ℕ) : ℤ) by push_cast; ring]

private theorem sum_derivative_normalOrder_right (A B : VertexOperator R V) (m : ℤ) (v : V)
    (Q : ℕ) :
    ∑ i ∈ range (Q + 1), (B[[m - i - 1]]) (((derivative A)[[(i : ℤ)]]) v) =
      ∑ i ∈ range Q, (-(i + 1 : ℤ)) • (B[[m - 1 - i - 1]]) ((A[[(i : ℤ)]]) v) := by
  rw [sum_range_succ' (fun i : ℕ ↦ (B[[m - i - 1]]) (((derivative A)[[(i : ℤ)]]) v)) Q]
  simp only [Nat.cast_zero, ncoeff_derivative, neg_zero, zero_smul, LinearMap.zero_apply,
    map_zero, add_zero]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.smul_apply, map_zsmul,
    show -((i + 1 : ℕ) : ℤ) = -((i : ℤ) + 1) by push_cast; ring,
    show ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) by push_cast; ring,
    show m - ((i + 1 : ℕ) : ℤ) - 1 = m - 1 - (i : ℤ) - 1 by push_cast; ring]

/-- **The Leibniz rule** for normal ordering: `∂ (:AB:) = :(∂A)B: + :A(∂B):`. -/
theorem derivative_normalOrder (A B : VertexOperator R V) :
    derivative (normalOrder A B) = normalOrder (derivative A) B + normalOrder A (derivative B) := by
  refine ext_ncoeff fun m ↦ LinearMap.ext fun v ↦ ?_
  obtain ⟨P₀, hP₀⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q₀, hQ₀⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  let P := P₀ + m.natAbs + 1
  let Q := Q₀ + 1
  have bPm1 (i : ℕ) (hi : P + 1 ≤ i) : (B[[m - 1 + i]]) v = 0 := hP₀ _ (by omega)
  have bPm (i : ℕ) (hi : P ≤ i) : (B[[m + i]]) v = 0 := hP₀ _ (by omega)
  have bPdB (i : ℕ) (hi : P + 1 ≤ i) : ((derivative B)[[m + i]]) v = 0 := by
    simp [hP₀ _ (by omega : (P₀ : ℤ) ≤ m + i - 1)]
  have bQA (i : ℕ) (hi : Q ≤ i) : (A[[(i : ℤ)]]) v = 0 := hQ₀ _ (by omega)
  have bQdA (i : ℕ) (hi : Q + 1 ≤ i) : ((derivative A)[[(i : ℤ)]]) v = 0 := by
    simp [hQ₀ _ (by omega : (Q₀ : ℤ) ≤ (i : ℤ) - 1)]
  rw [ncoeff_derivative, map_add, Pi.add_apply, LinearMap.smul_apply, LinearMap.add_apply,
    ncoeff_normalOrder, ncoeff_normalOrder, ncoeff_normalOrder,
    normalOrderCoeff_eq_sum A B (m - 1) v bPm1 bQA,
    normalOrderCoeff_eq_sum (derivative A) B m v bPm bQdA,
    normalOrderCoeff_eq_sum A (derivative B) m v bPdB bQA, smul_add, smul_sum, smul_sum,
    sum_derivative_normalOrder_left A B m v P, sum_derivative_normalOrder_right A B m v Q]
  have hdBL : ∀ i ∈ range (P + 1),
      (A[[-(i : ℤ) - 1]]) (((derivative B)[[m + i]]) v) =
        (-(m + i)) • (A[[-(i : ℤ) - 1]]) ((B[[m - 1 + i]]) v) := fun i _ ↦ by
    rw [ncoeff_derivative, LinearMap.smul_apply, map_zsmul,
      show m + (i : ℤ) - 1 = m - 1 + i by ring]
  have hdBR : ∀ i ∈ range Q,
      ((derivative B)[[m - i - 1]]) ((A[[(i : ℤ)]]) v) =
        (-(m - i - 1)) • (B[[m - 1 - i - 1]]) ((A[[(i : ℤ)]]) v) := fun i _ ↦ by
    rw [ncoeff_derivative, LinearMap.smul_apply, show m - (i : ℤ) - 1 - 1 = m - 1 - i - 1 by ring]
  rw [sum_congr rfl hdBL, sum_congr rfl hdBR,
    add_add_add_comm, ← sum_add_distrib, ← sum_add_distrib]
  congr 1 <;> (refine sum_congr rfl fun i _ ↦ ?_; rw [← add_zsmul]; congr 1; ring)

/-- **The Leibniz rule** for all integer `n`-th products:
`∂ (A₍ₙ₎ B) = (∂A)₍ₙ₎ B + A₍ₙ₎ (∂B)`. -/
theorem derivative_nthProduct (n : ℤ) (A B : VertexOperator R V) :
    derivative (nthProduct n A B) =
      nthProduct n (derivative A) B + nthProduct n A (derivative B) := by
  rcases le_or_gt 0 n with hn | hn
  · rw [nthProduct_of_nonneg hn, nthProduct_of_nonneg hn, nthProduct_of_nonneg hn]
    exact derivative_nonnegResidueProduct n.toNat A B
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    simp only [nthProduct_neg_succ, derivative_normalOrder, derivative_hasseDeriv,
      hasseDeriv_derivative]

/-! ### Translation covariance and vacuum regularity of `nthProduct` -/

private theorem sub_mul_choose_eq (m : ℤ) (k : ℕ) :
    (m - k) * Ring.choose m k = m * Ring.choose (m - 1) k := by
  have h₁ := Ring.choose_smul_choose m (Nat.le_succ k)
  have h₂ := Ring.choose_smul_choose m (Nat.succ_le_succ (Nat.zero_le k))
  have c₁ : (k + 1) - k = 1 := by omega
  have c₂ : (k + 1) - 1 = k := by omega
  rw [Nat.choose_succ_self_right, c₁, Ring.choose_one_right, nsmul_eq_mul] at h₁
  rw [Nat.choose_one_right, c₂, Nat.cast_one, Ring.choose_one_right, nsmul_eq_mul] at h₂
  linarith

attribute [local instance] LieRing.ofAssociativeRing

/-- Translation covariance `[T, A₍ₘ₎] = (∂A)₍ₘ₎` passes to all Hasse derivatives `D^[k] A`. -/
theorem lie_ncoeff_hasseDeriv (T : Module.End R V) {A : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]]) (k : ℕ) (m : ℤ) :
    ⁅T, (hasseDeriv k A)[[m]]⁆ = (derivative (hasseDeriv k A))[[m]] := by
  rw [ncoeff_hasseDeriv, lie_zsmul, lie_zsmul, hA, ncoeff_derivative,
    ncoeff_derivative, ncoeff_hasseDeriv]
  have hidx : m - 1 - (k : ℤ) = m - k - 1 := by ring
  rw [hidx, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  calc (-1 : ℤ) ^ k * Ring.choose m k * -(m - k)
      = -((-1 : ℤ) ^ k * ((m - k) * Ring.choose m k)) := by ring
    _ = -((-1 : ℤ) ^ k * (m * Ring.choose (m - 1) k)) := by rw [sub_mul_choose_eq]
    _ = -m * (-1 : ℤ) ^ k * Ring.choose (m - 1) k := by ring

/-- Translation covariance passes to nonnegative residue products. -/
theorem lie_ncoeff_nonnegResidueProduct (T : Module.End R V) {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (n : ℕ) (m : ℤ) :
    ⁅T, (nonnegResidueProduct n A B)[[m]]⁆ = (derivative (nonnegResidueProduct n A B))[[m]] := by
  rw [derivative_nonnegResidueProduct, map_add, Pi.add_apply, ncoeff_nonnegResidueProduct,
    ncoeff_nonnegResidueProduct, ncoeff_nonnegResidueProduct, ← sum_add_distrib, lie_sum]
  refine sum_congr rfl fun ij _ ↦ ?_
  rw [lie_nsmul, lie_zsmul, ← Ring.lie_def (A[[_]]), leibniz_lie, hA, hB, Ring.lie_def,
    Ring.lie_def, smul_add, smul_add]

private theorem apply_of_lie_eq_derivative {T : Module.End R V} {X : VertexOperator R V}
    (hX : ∀ k, ⁅T, X[[k]]⁆ = (derivative X)[[k]]) (k : ℤ) (w : V) :
    T ((X[[k]]) w) = ((derivative X)[[k]]) w + (X[[k]]) (T w) :=
  sub_eq_iff_eq_add.mp (by simpa [Ring.lie_def] using LinearMap.congr_fun (hX k) w)

/-- Translation covariance passes to normal-ordered products. -/
theorem lie_ncoeff_normalOrder (T : Module.End R V) {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (m : ℤ) :
    ⁅T, (normalOrder A B)[[m]]⁆ = (derivative (normalOrder A B))[[m]] := by
  rw [derivative_normalOrder]
  ext v
  obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨P₂, hP₂⟩ := B.exists_forall_ncoeff_apply_eq_zero (T v)
  obtain ⟨Q₁, hQ₁⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q₂, hQ₂⟩ := A.exists_forall_ncoeff_apply_eq_zero (T v)
  let P := max P₁ P₂ + m.natAbs + 1
  let Q := max Q₁ Q₂ + 1
  have bPv (i : ℕ) (hi : P ≤ i) : (B[[m + i]]) v = 0 :=
    hP₁ _ (by have := le_max_left P₁ P₂; omega)
  have bPTv (i : ℕ) (hi : P ≤ i) : (B[[m + i]]) (T v) = 0 :=
    hP₂ _ (by have := le_max_right P₁ P₂; omega)
  have bPdB (i : ℕ) (hi : P ≤ i) : ((derivative B)[[m + i]]) v = 0 := by
    simp [hP₁ _ (by have := le_max_left P₁ P₂; omega : (P₁ : ℤ) ≤ m + i - 1)]
  have bQv (i : ℕ) (hi : Q ≤ i) : (A[[(i : ℤ)]]) v = 0 :=
    hQ₁ _ (by have := le_max_left Q₁ Q₂; omega)
  have bQTv (i : ℕ) (hi : Q ≤ i) : (A[[(i : ℤ)]]) (T v) = 0 :=
    hQ₂ _ (by have := le_max_right Q₁ Q₂; omega)
  have bQdA (i : ℕ) (hi : Q ≤ i) : ((derivative A)[[(i : ℤ)]]) v = 0 := by
    simp [hQ₁ _ (by have := le_max_left Q₁ Q₂; omega : (Q₁ : ℤ) ≤ (i : ℤ) - 1)]
  rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    map_add, Pi.add_apply, LinearMap.add_apply, ncoeff_normalOrder, ncoeff_normalOrder,
    ncoeff_normalOrder,
    normalOrderCoeff_eq_sum A B m v bPv bQv, normalOrderCoeff_eq_sum A B m (T v) bPTv bQTv,
    normalOrderCoeff_eq_sum (derivative A) B m v bPv bQdA,
    normalOrderCoeff_eq_sum A (derivative B) m v bPdB bQv, map_add, map_sum, map_sum]
  have eL : ∀ i ∈ range P,
      T ((A[[-(i : ℤ) - 1]]) ((B[[m + i]]) v)) - (A[[-(i : ℤ) - 1]]) ((B[[m + i]]) (T v)) =
      ((derivative A)[[-(i : ℤ) - 1]]) ((B[[m + i]]) v) +
        (A[[-(i : ℤ) - 1]]) (((derivative B)[[m + i]]) v) := fun i _ ↦ by
    rw [apply_of_lie_eq_derivative hA, apply_of_lie_eq_derivative hB, map_add]; abel
  have eR : ∀ i ∈ range Q,
      T ((B[[m - i - 1]]) ((A[[(i : ℤ)]]) v)) - (B[[m - i - 1]]) ((A[[(i : ℤ)]]) (T v)) =
      (B[[m - i - 1]]) (((derivative A)[[(i : ℤ)]]) v) +
        ((derivative B)[[m - i - 1]]) ((A[[(i : ℤ)]]) v) := fun i _ ↦ by
    rw [apply_of_lie_eq_derivative hB, apply_of_lie_eq_derivative hA, map_add]; abel
  rw [← sub_add_sub_comm, ← sum_sub_distrib, ← sum_sub_distrib,
    sum_congr rfl eL, sum_congr rfl eR, sum_add_distrib, sum_add_distrib]
  abel

/-- Translation covariance passes to all integer `n`-th products. -/
theorem lie_ncoeff_nthProduct (T : Module.End R V) {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (n m : ℤ) :
    ⁅T, (nthProduct n A B)[[m]]⁆ = (derivative (nthProduct n A B))[[m]] := by
  rcases le_or_gt 0 n with hn | hn
  · rw [nthProduct_of_nonneg hn]
    exact lie_ncoeff_nonnegResidueProduct T hA hB n.toNat m
  · rw [nthProduct_of_neg hn]
    exact lie_ncoeff_normalOrder T (lie_ncoeff_hasseDeriv T hA _) hB m

/-- If `V` is additive-torsion-free, `T vac = 0`, and `B` is translation-covariant with respect to
`T`, then all nonnegative modes of `B` annihilate `vac`: downward induction from Laurent lower
truncation cancels `k + 1` in `0 = T (B₍ₖ₊₁₎ vac) = -(k + 1) • B₍ₖ₎ vac`. -/
theorem ncoeff_apply_eq_zero_of_lie_derivative [IsAddTorsionFree V]
    {T : Module.End R V} {vac : V} (hvac : T vac = 0) {B : VertexOperator R V}
    (hT : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) {m : ℤ} (hm : 0 ≤ m) :
    (B[[m]]) vac = 0 := by
  lift m to ℕ using hm
  obtain ⟨N, hN⟩ := B.exists_forall_ncoeff_apply_eq_zero vac
  suffices ∀ d k : ℕ, N ≤ k + d → (B[[(k : ℤ)]]) vac = 0 from this N m (Nat.le_add_left N m)
  intro d
  induction d with
  | zero => exact fun k hk ↦ hN k (Nat.cast_le.mpr hk)
  | succ d ih =>
    intro k hk
    have hstep : (B[[((k + 1 : ℕ) : ℤ)]]) vac = 0 := ih (k + 1) (by omega)
    have h := apply_of_lie_eq_derivative hT ((k + 1 : ℕ) : ℤ) vac
    rw [hstep, hvac, map_zero, map_zero, add_zero, ncoeff_derivative,
      show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring,
      LinearMap.smul_apply, neg_zsmul, natCast_zsmul, eq_comm, neg_eq_zero] at h
    exact (nsmul_eq_zero_iff_right (Nat.succ_ne_zero k)).mp h

/-- If `T vac = 0` and `B` is translation-covariant with respect to `T`, then
`k! • B₍₋ₖ₋₁₎ vac = Tᵏ (B₍₋₁₎ vac)` for every `k : ℕ`, over any commutative ring. -/
theorem factorial_smul_ncoeff_apply_of_lie_derivative
    {T : Module.End R V} {vac : V} (hvac : T vac = 0) {B : VertexOperator R V}
    (hT : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (k : ℕ) :
    k.factorial • (B[[-(k : ℤ) - 1]]) vac = (T ^ k) ((B[[-1]]) vac) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := apply_of_lie_eq_derivative hT (-(k : ℤ) - 1) vac
    rw [hvac, map_zero, add_zero, ncoeff_derivative, LinearMap.smul_apply,
      show -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
      show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by push_cast; ring, natCast_zsmul] at h
    rw [pow_succ', mul_apply_eq_comp, ← ih, map_nsmul, h, Nat.factorial_succ, mul_nsmul,
      smul_comm]

/-- If nonnegative modes of `A` and `B` annihilate `v`, so do nonnegative modes of every integer
`n`-th product `nthProduct n A B`. -/
theorem ncoeff_nthProduct_apply_eq_zero_of_nonneg (n : ℤ) {A B : VertexOperator R V} {v : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) v = 0) (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) v = 0)
    {m : ℤ} (hm : 0 ≤ m) :
    ((nthProduct n A B)[[m]]) v = 0 := by
  rcases le_or_gt 0 n with hn | hn
  · rw [nthProduct_of_nonneg hn, ncoeff_nonnegResidueProduct, LinearMap.sum_apply]
    refine sum_eq_zero fun ij _ ↦ ?_
    simp [hA _ (Nat.cast_nonneg ij.1), hB _ (by omega : 0 ≤ m + (ij.2 : ℤ))]
  · rw [nthProduct_of_neg hn, ncoeff_normalOrder, normalOrderCoeff_apply]
    have hL : ∀ i : ℕ, ((hasseDeriv (-n - 1).toNat A)[[-(i : ℤ) - 1]]) ((B[[m + i]]) v) = 0 :=
      fun i ↦ by rw [hB _ (by omega), map_zero]
    have hR : ∀ i : ℕ, (B[[m - i - 1]]) (((hasseDeriv (-n - 1).toNat A)[[(i : ℤ)]]) v) = 0 :=
      fun i ↦ by rw [ncoeff_hasseDeriv_apply_eq_zero_of_nonneg _ hA (Nat.cast_nonneg i), map_zero]
    simp_rw [hL, hR]
    simp

/-- If nonnegative modes of `A` and `B` annihilate `v`, then `(A₍ₙ₎ B)₍₋₁₎ v = A₍ₙ₎ (B₍₋₁₎ v)`
for every integer `n : ℤ`. -/
theorem ncoeff_neg_one_nthProduct_apply (n : ℤ) {A B : VertexOperator R V} {v : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) v = 0) (hB : ∀ m : ℤ, 0 ≤ m → (B[[m]]) v = 0) :
    ((nthProduct n A B)[[-1]]) v = (A[[n]]) ((B[[-1]]) v) := by
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn
    rw [nthProduct_natCast, ncoeff_nonnegResidueProduct, LinearMap.sum_apply]
    rw [sum_eq_single (n, 0) (fun ij hij hne ↦ ?_) (by simp)]
    · simp [hA _ (Nat.cast_nonneg n)]
    · have hj : ij.2 ≠ 0 := fun hj ↦
        hne (Prod.ext (by simpa [hj] using mem_antidiagonal.mp hij) hj)
      simp [hA _ (Nat.cast_nonneg ij.1), hB _ (by omega : 0 ≤ -1 + (ij.2 : ℤ))]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_succ, ncoeff_normalOrder,
      normalOrderCoeff_eq_sum _ B (-1) v (P := 1) (Q := 0)
        (fun i hi ↦ hB _ (by omega))
        (fun i _ ↦ ncoeff_hasseDeriv_apply_eq_zero_of_nonneg k hA (Nat.cast_nonneg i))]
    simp only [range_one, sum_singleton, Nat.cast_zero, neg_zero, zero_sub, add_zero, range_zero,
      sum_empty, ncoeff_neg_one_hasseDeriv]

end VertexOperator
