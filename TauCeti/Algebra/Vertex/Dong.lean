/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.NthProduct

/-!
# Dong's lemma for vertex operators

Dong's lemma states that mutual locality of fields is preserved under all integer residue products:
if `A`, `B`, `C : VertexOperator R V` are pairwise mutually local, then `nthProduct n A B` is
mutually local with `C` for every `n : ℤ`.

We prove Dong's lemma over an arbitrary commutative ring `R`, without dividing by factorials:

1. For `n : ℕ`, `nonnegResidueProduct n A B` has locality order `r₀ + r₁ + r₂` with `C` whenever
   `(A, B)`, `(A, C)`, `(B, C)` have locality orders `r₀`, `r₁`, `r₂`. This is proved directly on
   three-variable endomorphism distributions via the Jacobi identity and the commuting difference
   operators `z₁ - z₂`, `z₁ - z₃`, `z₂ - z₃`.
2. For `normalOrder A B`, decomposing `[(:AB:)₍ᵧ₎, C₍₂₎]` via the derivation property of `[·, C₍₂₎]`
   gives one sum killed by `(w - z)^r₂` and a split Cauchy-kernel sum whose `(w - z)` differences
   telescope in `r₁` steps to commutators `[B₍ᵧ₎, (A₍ⱼ₎ C)₍₂₎]`, which are killed by
   `(w - z)^(r₀ + r₁ + r₂)` by step 1. Thus `normalOrder A B` has locality order
   `r₀ + 2 * r₁ + r₂` with `C`.
3. Combining step 2 with `IsLocalOfOrder.hasseDeriv_left` gives locality order
   `r₀ + 2 * r₁ + r₂ + 3 * (-n - 1).toNat` for `nthProduct n A B` at every integer `n : ℤ`.

## Main results

* `VertexOperator.IsLocalOfOrder.nonnegResidueProduct_left`,
  `VertexOperator.IsLocalOfOrder.nonnegResidueProduct_right`: locality of nonnegative residue
  products.
* `VertexOperator.IsLocalOfOrder.normalOrder_left`,
  `VertexOperator.IsLocalOfOrder.normalOrder_right`: locality of normal-ordered products.
* `VertexOperator.IsLocalOfOrder.nthProduct_left`,
  `VertexOperator.IsLocalOfOrder.nthProduct_right`: **Dong's lemma** for all integer products.

## References

* C. Dong, J. Lepowsky, *Generalized Vertex Algebras and Relative Vertex Operators*, Progress in
  Mathematics 112, Birkhäuser, 1993, Chapter 3 (for Dong's lemma).
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., Lemma 3.2.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Proposition 2.2.4.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3.4 and §3.2.1.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset TauCeti

namespace VertexOperator

/-! ### Three-variable formal distributions and difference operators -/

section Dist3

variable {M M' : Type*} [AddCommGroup M] [AddCommGroup M']

private def δ₁₂ : AddMonoid.End (ℤ → ℤ → ℤ → M) where
  toFun f x y z := f (x + 1) y z - f x (y + 1) z
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

private def δ₁₃ : AddMonoid.End (ℤ → ℤ → ℤ → M) where
  toFun f x y z := f (x + 1) y z - f x y (z + 1)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

private def δ₂₃ : AddMonoid.End (ℤ → ℤ → ℤ → M) where
  toFun f x y z := f x (y + 1) z - f x y (z + 1)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp; abel

private theorem end_mul_apply {α : Type*} [AddCommGroup α] (f g : AddMonoid.End α) (x : α) :
    (f * g) x = f (g x) := rfl

private theorem end_add_apply {α : Type*} [AddCommGroup α] (f g : AddMonoid.End α) (x : α) :
    (f + g) x = f x + g x := rfl

private theorem δ₁₃_sub_δ₁₂ : δ₁₃ (M := M) - δ₁₂ = δ₂₃ := by
  ext f x y z
  change (f (x + 1) y z - f x y (z + 1)) - (f (x + 1) y z - f x (y + 1) z) =
    f x (y + 1) z - f x y (z + 1)
  abel

private theorem commute_δ₁₂_δ₁₃ : Commute (δ₁₂ (M := M)) δ₁₃ := by
  ext f x y z
  change (f (x + 1 + 1) y z - f (x + 1) y (z + 1)) - (f (x + 1) (y + 1) z - f x (y + 1) (z + 1)) =
    (f (x + 1 + 1) y z - f (x + 1) (y + 1) z) - (f (x + 1) y (z + 1) - f x (y + 1) (z + 1))
  abel

private theorem commute_δ₁₂_δ₂₃ : Commute (δ₁₂ (M := M)) δ₂₃ := by
  rw [← δ₁₃_sub_δ₁₂]
  exact commute_δ₁₂_δ₁₃.sub_right (Commute.refl _)

private theorem commute_δ₁₃_δ₂₃ : Commute (δ₁₃ (M := M)) δ₂₃ := by
  rw [← δ₁₃_sub_δ₁₂]
  exact (Commute.refl _).sub_right commute_δ₁₂_δ₁₃.symm

private theorem δ₁₂_pow_apply (N : ℕ) (f : ℤ → ℤ → ℤ → M) (x y z : ℤ) :
    ((δ₁₂ ^ N) f) x y z = (FormalDistribution.mulSub ^ N) (fun x' y' ↦ f x' y' z) x y := by
  induction N generalizing x y with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ', pow_succ', end_mul_apply, end_mul_apply, FormalDistribution.mulSub_apply,
      ← ih, ← ih]
    rfl

private theorem δ₁₃_pow_apply (N : ℕ) (f : ℤ → ℤ → ℤ → M) (x y z : ℤ) :
    ((δ₁₃ ^ N) f) x y z = (FormalDistribution.mulSub ^ N) (fun x' z' ↦ f x' y z') x z := by
  induction N generalizing x z with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ', pow_succ', end_mul_apply, end_mul_apply, FormalDistribution.mulSub_apply,
      ← ih, ← ih]
    rfl

private theorem δ₂₃_pow_apply (N : ℕ) (f : ℤ → ℤ → ℤ → M) (x y z : ℤ) :
    ((δ₂₃ ^ N) f) x y z = (FormalDistribution.mulSub ^ N) (f x) y z := by
  induction N generalizing y z with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ', pow_succ', end_mul_apply, end_mul_apply, FormalDistribution.mulSub_apply,
      ← ih, ← ih]
    rfl

private theorem mulSub_pow_comp (φ : M →+ M') (c : FormalDistribution M) (N : ℕ) (m n : ℤ) :
    (FormalDistribution.mulSub ^ N) (fun x y ↦ φ (c x y)) m n =
      φ ((FormalDistribution.mulSub ^ N) c m n) := by
  induction N generalizing m n with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ', pow_succ', end_mul_apply, end_mul_apply, FormalDistribution.mulSub_apply,
      FormalDistribution.mulSub_apply, ih, ih, map_sub]

private theorem add_pow_apply_eq_zero {α : Type*} [AddCommGroup α] {x y : AddMonoid.End α}
    (hxy : Commute x y) :
    ∀ {r₁ r₀ : ℕ} {u : α}, (x ^ r₁) u = 0 → (y ^ r₀) u = 0 → ((x + y) ^ (r₁ + r₀)) u = 0
  | 0, r₀, u, hx, _ => by simp only [pow_zero, AddMonoid.End.one_apply] at hx; simp [hx]
  | r₁ + 1, 0, u, _, hy => by simp only [pow_zero, AddMonoid.End.one_apply] at hy; simp [hy]
  | r₁ + 1, r₀ + 1, u, hx, hy => by
    have hk : r₁ + 1 + (r₀ + 1) = (r₁ + (r₀ + 1)) + 1 := by omega
    rw [hk, pow_succ, end_mul_apply, end_add_apply, map_add]
    have hx₁ : (x ^ r₁) (x u) = 0 := by rwa [← end_mul_apply, ← pow_succ]
    have hy₁ : (y ^ (r₀ + 1)) (x u) = 0 := by
      rw [← end_mul_apply, (hxy.symm.pow_left (r₀ + 1)).eq, end_mul_apply, hy, map_zero]
    have hx₂ : (x ^ (r₁ + 1)) (y u) = 0 := by
      rw [← end_mul_apply, (hxy.pow_left (r₁ + 1)).eq, end_mul_apply, hx, map_zero]
    have hy₂ : (y ^ r₀) (y u) = 0 := by rwa [← end_mul_apply, ← pow_succ]
    rw [add_pow_apply_eq_zero hxy hx₁ hy₁, show r₁ + (r₀ + 1) = (r₁ + 1) + r₀ by omega,
      add_pow_apply_eq_zero hxy hx₂ hy₂, add_zero]
termination_by r₁ r₀ => r₁ + r₀

private theorem sub_pow_apply_eq_zero {α : Type*} [AddCommGroup α] {x y : AddMonoid.End α}
    (hxy : Commute x y) {r₁ r₀ : ℕ} {u : α} (hx : (x ^ r₁) u = 0) (hy : (y ^ r₀) u = 0) :
    ((x - y) ^ (r₁ + r₀)) u = 0 := by
  rw [sub_eq_add_neg]
  refine add_pow_apply_eq_zero hxy.neg_right hx ?_
  rw [neg_pow, end_mul_apply, hy, map_zero]

end Dist3

/-! ### Telescoping split Cauchy-kernel distributions -/

section SplitDist

variable {M : Type*} [AddCommGroup M]

private def SplitTrunc (G₁ G₂ : ℤ → ℤ → ℤ → M) : Prop :=
  ∀ y z : ℤ, (∃ P : ℕ, ∀ i : ℕ, P ≤ i → G₁ (-(i : ℤ) - 1) (y + i) z = 0) ∧
    (∃ Q : ℕ, ∀ i : ℕ, Q ≤ i → G₂ (i : ℤ) (y - 1 - i) z = 0)

private def splitDist (G₁ G₂ : ℤ → ℤ → ℤ → M) : FormalDistribution M :=
  fun y z ↦ (∑ᶠ i : ℕ, G₁ (-(i : ℤ) - 1) (y + i) z) + ∑ᶠ i : ℕ, G₂ (i : ℤ) (y - 1 - i) z

private theorem SplitTrunc.delta13 {G₁ G₂ : ℤ → ℤ → ℤ → M} (h : SplitTrunc G₁ G₂) :
    SplitTrunc (δ₁₃ G₁) (δ₁₃ G₂) := by
  intro y z
  obtain ⟨⟨P₁, hP₁⟩, ⟨Q₁, hQ₁⟩⟩ := h (y + 1) z
  obtain ⟨⟨P₂, hP₂⟩, ⟨Q₂, hQ₂⟩⟩ := h y (z + 1)
  refine ⟨⟨max (P₁ + 1) P₂, fun i hi ↦ ?_⟩, ⟨max Q₁ Q₂, fun i hi ↦ ?_⟩⟩
  · change G₁ (-(i : ℤ) - 1 + 1) (y + i) z - G₁ (-(i : ℤ) - 1) (y + i) (z + 1) = 0
    have h₁ : G₁ (-(i : ℤ) - 1 + 1) (y + i) z = 0 := by
      have hi₁ : P₁ + 1 ≤ i := le_trans (le_max_left _ _) hi
      simpa only [show -(i : ℤ) - 1 + 1 = -((i - 1 : ℕ) : ℤ) - 1 by omega,
        show y + (i : ℤ) = y + 1 + ((i - 1 : ℕ) : ℤ) by omega] using hP₁ (i - 1) (by omega)
    rw [h₁, hP₂ i (le_trans (le_max_right _ _) hi), sub_zero]
  · change G₂ ((i : ℤ) + 1) (y - 1 - i) z - G₂ (i : ℤ) (y - 1 - i) (z + 1) = 0
    have h₁ : G₂ ((i : ℤ) + 1) (y - 1 - i) z = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one,
        show y + 1 - 1 - ((i : ℤ) + 1) = y - 1 - i by omega] using
        hQ₁ (i + 1) (by have := le_trans (le_max_left _ _) hi; omega)
    rw [h₁, hQ₂ i (le_trans (le_max_right _ _) hi), sub_zero]

private theorem finsum_eq_sum_range_of_vanish {f : ℕ → M} {K : ℕ}
    (hf : ∀ i : ℕ, K ≤ i → f i = 0) : (∑ᶠ i : ℕ, f i) = ∑ i ∈ range K, f i := by
  refine finsum_eq_sum_of_support_subset f fun i hi ↦ ?_
  rw [coe_range, Set.mem_Iio]
  by_contra! hle
  exact hi (hf i hle)

private theorem mulSub_splitDist {G₁ G₂ : ℤ → ℤ → ℤ → M} (h : SplitTrunc G₁ G₂) :
    FormalDistribution.mulSub (splitDist G₁ G₂) =
      splitDist (δ₁₃ G₁) (δ₁₃ G₂) - fun y z ↦ G₁ 0 y z - G₂ 0 y z := by
  ext y z
  obtain ⟨⟨P₁, hP₁⟩, ⟨Q₁, hQ₁⟩⟩ := h (y + 1) z
  obtain ⟨⟨P₂, hP₂⟩, ⟨Q₂, hQ₂⟩⟩ := h y (z + 1)
  let K := max (max P₁ P₂) (max Q₁ Q₂) + 1
  have h₁ : (∑ᶠ i : ℕ, G₁ (-(i : ℤ) - 1) (y + 1 + i) z) =
      ∑ i ∈ range K, G₁ (-(i : ℤ) - 1) (y + 1 + i) z :=
    finsum_eq_sum_range_of_vanish fun i hi ↦ hP₁ i (by omega)
  have h₂ : (∑ᶠ i : ℕ, G₁ (-(i : ℤ) - 1) (y + i) (z + 1)) =
      ∑ i ∈ range (K + 1), G₁ (-(i : ℤ) - 1) (y + i) (z + 1) :=
    finsum_eq_sum_range_of_vanish fun i hi ↦ hP₂ i (by omega)
  have h₃ : (∑ᶠ i : ℕ, (δ₁₃ G₁) (-(i : ℤ) - 1) (y + i) z) =
      ∑ i ∈ range (K + 1), (G₁ (-(i : ℤ) - 1 + 1) (y + i) z -
        G₁ (-(i : ℤ) - 1) (y + i) (z + 1)) := by
    refine finsum_eq_sum_range_of_vanish fun i hi ↦ ?_
    change G₁ (-(i : ℤ) - 1 + 1) (y + i) z - G₁ (-(i : ℤ) - 1) (y + i) (z + 1) = 0
    have ha : G₁ (-(i : ℤ) - 1 + 1) (y + i) z = 0 := by
      simpa only [show -(i : ℤ) - 1 + 1 = -((i - 1 : ℕ) : ℤ) - 1 by omega,
        show y + (i : ℤ) = y + 1 + ((i - 1 : ℕ) : ℤ) by omega] using hP₁ (i - 1) (by omega)
    rw [ha, hP₂ i (by omega), sub_zero]
  have h₄ : (∑ᶠ i : ℕ, G₂ (i : ℤ) (y + 1 - 1 - i) z) =
      ∑ i ∈ range (K + 1), G₂ (i : ℤ) (y + 1 - 1 - i) z :=
    finsum_eq_sum_range_of_vanish fun i hi ↦ hQ₁ i (by omega)
  have h₅ : (∑ᶠ i : ℕ, G₂ (i : ℤ) (y - 1 - i) (z + 1)) =
      ∑ i ∈ range K, G₂ (i : ℤ) (y - 1 - i) (z + 1) :=
    finsum_eq_sum_range_of_vanish fun i hi ↦ hQ₂ i (by omega)
  have h₆ : (∑ᶠ i : ℕ, (δ₁₃ G₂) (i : ℤ) (y - 1 - i) z) =
      ∑ i ∈ range K, (G₂ ((i : ℤ) + 1) (y - 1 - i) z - G₂ (i : ℤ) (y - 1 - i) (z + 1)) := by
    refine finsum_eq_sum_range_of_vanish fun i hi ↦ ?_
    change G₂ ((i : ℤ) + 1) (y - 1 - i) z - G₂ (i : ℤ) (y - 1 - i) (z + 1) = 0
    have ha : G₂ ((i : ℤ) + 1) (y - 1 - i) z = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one,
        show y + 1 - 1 - ((i : ℤ) + 1) = y - 1 - i by omega] using hQ₁ (i + 1) (by omega)
    rw [ha, hQ₂ i (by omega), sub_zero]
  simp only [FormalDistribution.mulSub_apply, Pi.sub_apply, splitDist]
  rw [h₁, h₂, h₃, h₄, h₅, h₆, sum_sub_distrib, sum_sub_distrib,
    sum_range_succ' (fun j ↦ G₁ (-(j : ℤ) - 1 + 1) (y + j) z) K,
    sum_range_succ' (fun j ↦ G₂ (j : ℤ) (y + 1 - 1 - j) z) K]
  have e₁ : ∑ i ∈ range K, G₁ (-((i + 1 : ℕ) : ℤ) - 1 + 1) (y + (i + 1 : ℕ)) z =
      ∑ i ∈ range K, G₁ (-(i : ℤ) - 1) (y + 1 + i) z :=
    sum_congr rfl fun i _ ↦ by
      rw [show -((i + 1 : ℕ) : ℤ) - 1 + 1 = -(i : ℤ) - 1 by push_cast; omega,
        show y + ((i + 1 : ℕ) : ℤ) = y + 1 + i by push_cast; omega]
  have e₂ : ∑ i ∈ range K, G₂ ((i + 1 : ℕ) : ℤ) (y + 1 - 1 - (i + 1 : ℕ)) z =
      ∑ i ∈ range K, G₂ ((i : ℤ) + 1) (y - 1 - i) z :=
    sum_congr rfl fun i _ ↦ by
      rw [Nat.cast_add, Nat.cast_one, show y + 1 - 1 - ((i : ℤ) + 1) = y - 1 - i by omega]
  rw [e₁, e₂]
  simp only [Nat.cast_zero, neg_zero, zero_sub, neg_add_cancel, add_zero, sub_zero,
    add_sub_cancel_right]
  abel

private theorem mulSub_pow_splitDist_eq_zero {G₁ G₂ : ℤ → ℤ → ℤ → M} {M₀ r₁ : ℕ}
    (h : SplitTrunc G₁ G₂) (hG₁ : (δ₁₃ ^ r₁) G₁ = 0) (hG₂ : (δ₁₃ ^ r₁) G₂ = 0)
    (hb : ∀ j < r₁, (FormalDistribution.mulSub ^ M₀)
      (fun y z ↦ ((δ₁₃ ^ j) G₁) 0 y z - ((δ₁₃ ^ j) G₂) 0 y z) = 0) :
    (FormalDistribution.mulSub ^ (M₀ + r₁)) (splitDist G₁ G₂) = 0 := by
  induction r₁ generalizing G₁ G₂ with
  | zero =>
    simp only [pow_zero, AddMonoid.End.one_apply] at hG₁ hG₂
    have hs : splitDist G₁ G₂ = 0 := by ext y z; simp [splitDist, hG₁, hG₂]
    simp [hs]
  | succ r₁ ih =>
    rw [← Nat.add_assoc, pow_succ, end_mul_apply, mulSub_splitDist h, map_sub]
    have h₁ : (FormalDistribution.mulSub ^ (M₀ + r₁)) (splitDist (δ₁₃ G₁) (δ₁₃ G₂)) = 0 := by
      refine ih h.delta13 ?_ ?_ fun j hj ↦ ?_
      · rwa [← end_mul_apply, ← pow_succ]
      · rwa [← end_mul_apply, ← pow_succ]
      · simpa only [← end_mul_apply, ← pow_succ] using hb (j + 1) (Nat.succ_lt_succ hj)
    have h₂ : (FormalDistribution.mulSub ^ (M₀ + r₁)) (fun y z ↦ G₁ 0 y z - G₂ 0 y z) = 0 := by
      rw [Nat.add_comm M₀ r₁, pow_add, end_mul_apply]
      simpa only [pow_zero, AddMonoid.End.one_apply, map_zero] using
        congrArg (FormalDistribution.mulSub ^ r₁) (hb 0 (Nat.zero_lt_succ r₁))
    rw [h₁, h₂, sub_zero]

end SplitDist

/-! ### Dong's lemma -/

namespace IsLocalOfOrder

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private theorem δ₂₃_pow_jacobi_eq_zero {A B C : VertexOperator R V} {r₀ r₁ r₂ : ℕ}
    (hAB : A.IsLocalOfOrder B r₀) (hAC : A.IsLocalOfOrder C r₁) (hBC : B.IsLocalOfOrder C r₂) :
    (δ₂₃ ^ (r₀ + r₁ + r₂)) (fun x y z ↦ ⁅⁅A[[x]], B[[y]]⁆, C[[z]]⁆) = 0 := by
  let w : ℤ → ℤ → ℤ → Module.End R V := fun x y z ↦ ⁅⁅A[[x]], B[[y]]⁆, C[[z]]⁆
  let w₁ : ℤ → ℤ → ℤ → Module.End R V := fun x y z ↦ ⁅A[[x]], ⁅B[[y]], C[[z]]⁆⁆
  let w₂ : ℤ → ℤ → ℤ → Module.End R V := fun x y z ↦ ⁅B[[y]], ⁅A[[x]], C[[z]]⁆⁆
  have hw : w = w₁ - w₂ := by
    funext x y z
    simp only [w, w₁, w₂, Pi.sub_apply, Ring.lie_def, mul_sub, sub_mul, mul_assoc]
    abel
  have hAB' := (isLocalOfOrder_iff_mulSub_pow_eq_zero A B r₀).mp hAB
  have hAC' := (isLocalOfOrder_iff_mulSub_pow_eq_zero A C r₁).mp hAC
  have hBC' := (isLocalOfOrder_iff_mulSub_pow_eq_zero B C r₂).mp hBC
  have hw_r₀ : (δ₁₂ ^ r₀) w = 0 := by
    funext x y z
    let ψ : Module.End R V →+ Module.End R V :=
      { toFun := fun X ↦ ⁅X, C[[z]]⁆
        map_zero' := by simp [Ring.lie_def]
        map_add' := fun _ _ ↦ by simp only [Ring.lie_def, add_mul, mul_add]; abel }
    have h := mulSub_pow_comp ψ (A.commutatorDistribution B) r₀ x y
    simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, commutatorDistribution_apply,
      ← Ring.lie_def] at h
    rw [(δ₁₂_pow_apply r₀ w x y z).trans h, hAB']
    simp [Ring.lie_def]
  have hw₁ : (δ₂₃ ^ r₂) w₁ = 0 := by
    funext x y z
    let ψ : Module.End R V →+ Module.End R V :=
      { toFun := fun X ↦ ⁅A[[x]], X⁆
        map_zero' := by simp [Ring.lie_def]
        map_add' := fun _ _ ↦ by simp only [Ring.lie_def, add_mul, mul_add]; abel }
    have h := mulSub_pow_comp ψ (B.commutatorDistribution C) r₂ y z
    simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, commutatorDistribution_apply,
      ← Ring.lie_def] at h
    rw [(δ₂₃_pow_apply r₂ w₁ x y z).trans h, hBC']
    simp [Ring.lie_def]
  have hw₂ : (δ₁₃ ^ r₁) w₂ = 0 := by
    funext x y z
    let ψ : Module.End R V →+ Module.End R V :=
      { toFun := fun X ↦ ⁅B[[y]], X⁆
        map_zero' := by simp [Ring.lie_def]
        map_add' := fun _ _ ↦ by simp only [Ring.lie_def, add_mul, mul_add]; abel }
    have h := mulSub_pow_comp ψ (A.commutatorDistribution C) r₁ x z
    simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, commutatorDistribution_apply,
      ← Ring.lie_def] at h
    rw [(δ₁₃_pow_apply r₁ w₂ x y z).trans h, hAC']
    simp [Ring.lie_def]
  have hu₁ : (δ₁₃ ^ r₁) ((δ₂₃ ^ r₂) w) = 0 := by
    rw [hw, map_sub, hw₁, zero_sub, map_neg, neg_eq_zero, ← end_mul_apply,
      ((commute_δ₁₃_δ₂₃.pow_left r₁).pow_right r₂).eq, end_mul_apply, hw₂, map_zero]
  have hu₀ : (δ₁₂ ^ r₀) ((δ₂₃ ^ r₂) w) = 0 := by
    rw [← end_mul_apply, ((commute_δ₁₂_δ₂₃.pow_left r₀).pow_right r₂).eq, end_mul_apply, hw_r₀,
      map_zero]
  have hsub := sub_pow_apply_eq_zero commute_δ₁₂_δ₁₃.symm hu₁ hu₀
  rwa [δ₁₃_sub_δ₁₂, ← end_mul_apply, ← pow_add, show r₁ + r₀ + r₂ = r₀ + r₁ + r₂ by omega] at hsub

/-- **Dong's lemma for nonnegative residue products.** If `(A, B)`, `(A, C)`, `(B, C)` are mutually
local of orders `r₀`, `r₁`, `r₂`, then `nonnegResidueProduct n A B` is local with `C` of order
`r₀ + r₁ + r₂` for every `n : ℕ`. -/
theorem nonnegResidueProduct_left {A B C : VertexOperator R V} {r₀ r₁ r₂ : ℕ}
    (hAB : A.IsLocalOfOrder B r₀) (hAC : A.IsLocalOfOrder C r₁) (hBC : B.IsLocalOfOrder C r₂)
    (n : ℕ) :
    (nonnegResidueProduct n A B).IsLocalOfOrder C (r₀ + r₁ + r₂) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  let w : ℤ → ℤ → ℤ → Module.End R V := fun x y z ↦ ⁅⁅A[[x]], B[[y]]⁆, C[[z]]⁆
  have hres : (nonnegResidueProduct n A B).commutatorDistribution C = ((δ₁₂ ^ n) w) 0 := by
    funext y z
    let ψ : Module.End R V →+ Module.End R V :=
      { toFun := fun X ↦ ⁅X, C[[z]]⁆
        map_zero' := by simp [Ring.lie_def]
        map_add' := fun _ _ ↦ by simp only [Ring.lie_def, add_mul, mul_add]; abel }
    have h := mulSub_pow_comp ψ (A.commutatorDistribution B) n 0 y
    simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, commutatorDistribution_apply,
      ← Ring.lie_def] at h
    have hsum : (nonnegResidueProduct n A B)[[y]] =
        (FormalDistribution.mulSub ^ n) (A.commutatorDistribution B) 0 y := by
      rw [ncoeff_nonnegResidueProduct, FormalDistribution.mulSub_pow_apply]
      exact sum_congr rfl fun ij _ ↦ by rw [zero_add, commutatorDistribution_apply]
    rw [commutatorDistribution_apply, ← Ring.lie_def, hsum, (δ₁₂_pow_apply n w 0 y z).trans h]
  funext y z
  rw [hres, ← δ₂₃_pow_apply, ← end_mul_apply,
    ((commute_δ₁₂_δ₂₃.pow_left n).pow_right (r₀ + r₁ + r₂)).symm.eq,
    end_mul_apply, δ₂₃_pow_jacobi_eq_zero hAB hAC hBC, map_zero]
  rfl

/-- Symmetric form of `nonnegResidueProduct_left` in the second factor. -/
theorem nonnegResidueProduct_right {A B C : VertexOperator R V} {r₀ r₁ r₂ : ℕ}
    (hBC : B.IsLocalOfOrder C r₀) (hAB : A.IsLocalOfOrder B r₁) (hAC : A.IsLocalOfOrder C r₂)
    (n : ℕ) :
    A.IsLocalOfOrder (nonnegResidueProduct n B C) (r₀ + r₁ + r₂) :=
  (hBC.nonnegResidueProduct_left hAB.symm hAC.symm n).symm

private theorem mulSub_pow_normalOrder_bc_eq_zero {A B C : VertexOperator R V} {r₂ : ℕ}
    (hBC : B.IsLocalOfOrder C r₂) (v : V) :
    (FormalDistribution.mulSub ^ r₂)
      (fun y z ↦ (∑ᶠ i : ℕ, (A[[-(i : ℤ) - 1]]) ((⁅B[[y + i]], C[[z]]⁆) v)) +
        ∑ᶠ i : ℕ, (⁅B[[y - 1 - i]], C[[z]]⁆) ((A[[(i : ℤ)]]) v)) = 0 := by
  have hBC' := (isLocalOfOrder_iff_mulSub_pow_eq_zero B C r₂).mp hBC
  ext y z
  obtain ⟨Q, hQ⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨P₀, hP₀⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  choose P hP using fun q : ℕ ↦ B.exists_forall_ncoeff_apply_eq_zero ((C[[z + q]]) v)
  let K := max Q (P₀ + y.natAbs + ∑ q ∈ range (r₂ + 1), P q)
  rw [FormalDistribution.mulSub_pow_apply]
  have hterm : ∀ pq ∈ antidiagonal r₂,
      r₂.choose pq.1 • (-1 : ℤ) ^ pq.2 •
        ((∑ᶠ i : ℕ, (A[[-(i : ℤ) - 1]]) ((⁅B[[y + pq.1 + i]], C[[z + pq.2]]⁆) v)) +
          ∑ᶠ i : ℕ, (⁅B[[y + pq.1 - 1 - i]], C[[z + pq.2]]⁆) ((A[[(i : ℤ)]]) v)) =
      (∑ i ∈ range K, (A[[-(i : ℤ) - 1]]) ((r₂.choose pq.1 • (-1 : ℤ) ^ pq.2 •
          B.commutatorDistribution C (y + i + pq.1) (z + pq.2)) v)) +
        ∑ i ∈ range K, (r₂.choose pq.1 • (-1 : ℤ) ^ pq.2 •
          B.commutatorDistribution C (y - 1 - i + pq.1) (z + pq.2)) ((A[[(i : ℤ)]]) v) := by
    intro pq hpq
    have hpq₂ : pq.2 ∈ range (r₂ + 1) := mem_range.mpr (by have := mem_antidiagonal.mp hpq; omega)
    have hle : P pq.2 ≤ ∑ q ∈ range (r₂ + 1), P q :=
      single_le_sum (fun q _ ↦ Nat.zero_le (P q)) hpq₂
    have hs₁ : (∑ᶠ i : ℕ, (A[[-(i : ℤ) - 1]]) ((⁅B[[y + pq.1 + i]], C[[z + pq.2]]⁆) v)) =
        ∑ i ∈ range K, (A[[-(i : ℤ) - 1]]) ((⁅B[[y + pq.1 + i]], C[[z + pq.2]]⁆) v) := by
      refine finsum_eq_sum_range_of_vanish fun i hi ↦ ?_
      rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
        hP pq.2 _ (by omega), hP₀ _ (by omega), map_zero, sub_self, map_zero]
    have hs₂ : (∑ᶠ i : ℕ, (⁅B[[y + pq.1 - 1 - i]], C[[z + pq.2]]⁆) ((A[[(i : ℤ)]]) v)) =
        ∑ i ∈ range K, (⁅B[[y + pq.1 - 1 - i]], C[[z + pq.2]]⁆) ((A[[(i : ℤ)]]) v) :=
      finsum_eq_sum_range_of_vanish fun i hi ↦ by rw [hQ _ (by omega), map_zero]
    rw [hs₁, hs₂, smul_add, smul_add, smul_sum, smul_sum, smul_sum, smul_sum]
    congr 1 <;> refine sum_congr rfl fun i _ ↦ ?_
    · rw [← map_zsmul, ← map_nsmul, LinearMap.smul_apply, LinearMap.smul_apply,
        commutatorDistribution_apply, ← Ring.lie_def,
        show y + (pq.1 : ℤ) + i = y + i + pq.1 by omega]
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, commutatorDistribution_apply, ← Ring.lie_def,
        show y + (pq.1 : ℤ) - 1 - i = y - 1 - i + pq.1 by omega]
  rw [sum_congr rfl hterm, sum_add_distrib, sum_comm, sum_comm (s := antidiagonal r₂)]
  have hz₁ : ∑ i ∈ range K, ∑ pq ∈ antidiagonal r₂, (A[[-(i : ℤ) - 1]])
      ((r₂.choose pq.1 • (-1 : ℤ) ^ pq.2 •
        B.commutatorDistribution C (y + i + pq.1) (z + pq.2)) v) = 0 := by
    refine sum_eq_zero fun i _ ↦ ?_
    rw [← map_sum, ← LinearMap.sum_apply, ← FormalDistribution.mulSub_pow_apply, hBC',
      Pi.zero_apply, Pi.zero_apply, LinearMap.zero_apply, map_zero]
  have hz₂ : ∑ i ∈ range K, ∑ pq ∈ antidiagonal r₂,
      (r₂.choose pq.1 • (-1 : ℤ) ^ pq.2 •
        B.commutatorDistribution C (y - 1 - i + pq.1) (z + pq.2)) ((A[[(i : ℤ)]]) v) = 0 := by
    refine sum_eq_zero fun i _ ↦ ?_
    rw [← LinearMap.sum_apply, ← FormalDistribution.mulSub_pow_apply, hBC',
      Pi.zero_apply, Pi.zero_apply, LinearMap.zero_apply]
  rw [hz₁, hz₂, add_zero]
  rfl

private theorem normalOrder_commutator_decomp (A B C : VertexOperator R V) (v : V) (y z : ℤ) :
    ((normalOrder A B).commutatorDistribution C y z) v =
      ((∑ᶠ i : ℕ, (A[[-(i : ℤ) - 1]]) ((⁅B[[y + i]], C[[z]]⁆) v)) +
        ∑ᶠ i : ℕ, (⁅B[[y - 1 - i]], C[[z]]⁆) ((A[[(i : ℤ)]]) v)) +
      splitDist (fun x y' z' ↦ (⁅A[[x]], C[[z']]⁆) ((B[[y']]) v))
        (fun x y' z' ↦ (B[[y']]) ((⁅A[[x]], C[[z']]⁆) v)) y z := by
  obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨P₂, hP₂⟩ := B.exists_forall_ncoeff_apply_eq_zero ((C[[z]]) v)
  obtain ⟨Q₁, hQ₁⟩ := A.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨Q₂, hQ₂⟩ := A.exists_forall_ncoeff_apply_eq_zero ((C[[z]]) v)
  let K := max (max P₁ P₂) (max Q₁ Q₂) + y.natAbs + 1
  have hBv (i : ℕ) (hi : K ≤ i) : (B[[y + i]]) v = 0 := hP₁ _ (by omega)
  have hBCv (i : ℕ) (hi : K ≤ i) : (B[[y + i]]) ((C[[z]]) v) = 0 := hP₂ _ (by omega)
  have hAv (i : ℕ) (hi : K ≤ i) : (A[[(i : ℤ)]]) v = 0 := hQ₁ _ (by omega)
  have hACv (i : ℕ) (hi : K ≤ i) : (A[[(i : ℤ)]]) ((C[[z]]) v) = 0 := hQ₂ _ (by omega)
  rw [commutatorDistribution_apply, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    ncoeff_normalOrder, normalOrderCoeff_eq_sum A B y ((C[[z]]) v) hBCv hACv,
    normalOrderCoeff_eq_sum A B y v hBv hAv, map_add, map_sum, map_sum]
  simp only [splitDist]
  rw [finsum_eq_sum_range_of_vanish (K := K) fun i hi ↦ by
      rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
        hBCv i hi, hBv i hi, map_zero, sub_self, map_zero],
    finsum_eq_sum_range_of_vanish (K := K) fun i hi ↦ by rw [hAv i hi, map_zero],
    finsum_eq_sum_range_of_vanish (K := K) fun i hi ↦ by rw [hBv i hi, map_zero],
    finsum_eq_sum_range_of_vanish (K := K) fun i hi ↦ by
      rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
        hACv i hi, hAv i hi, map_zero, sub_self, map_zero] ]
  have hleib (X Y Z : Module.End R V) :
      X (Y (Z v)) - Z (X (Y v)) = (⁅X, Z⁆) (Y v) + X ((⁅Y, Z⁆) v) := by
    simp only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, map_sub]
    abel
  have hsub (a b c d : V) : (a + b) - (c + d) = (a - c) + (b - d) := by abel
  have hadd (a b c d : V) : (a + b) + (c + d) = (a + c) + (b + d) := by abel
  rw [hsub, ← sum_sub_distrib, ← sum_sub_distrib, hadd, ← sum_add_distrib, ← sum_add_distrib,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [hleib (A[[-(i : ℤ) - 1]]) (B[[y + i]]) (C[[z]]),
    add_comm ((⁅A[[-(i : ℤ) - 1]], C[[z]]⁆) _),
    show y - (i : ℤ) - 1 = y - 1 - i by omega, hleib (B[[y - 1 - i]]) (A[[(i : ℤ)]]) (C[[z]])]

private theorem mulSub_pow_normalOrder_ac_eq_zero {A B C : VertexOperator R V} {r₀ r₁ r₂ : ℕ}
    (hAB : A.IsLocalOfOrder B r₀) (hAC : A.IsLocalOfOrder C r₁) (hBC : B.IsLocalOfOrder C r₂)
    (v : V) :
    (FormalDistribution.mulSub ^ (r₀ + 2 * r₁ + r₂))
      (splitDist (fun x y z ↦ (⁅A[[x]], C[[z]]⁆) ((B[[y]]) v))
        (fun x y z ↦ (B[[y]]) ((⁅A[[x]], C[[z]]⁆) v))) = 0 := by
  have hAC' := (isLocalOfOrder_iff_mulSub_pow_eq_zero A C r₁).mp hAC
  let ev : Module.End R V →+ V :=
    { toFun := fun f ↦ f v, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  let F₁ : ℤ → ℤ → ℤ → V := fun x y z ↦ (⁅A[[x]], C[[z]]⁆) ((B[[y]]) v)
  let F₂ : ℤ → ℤ → ℤ → V := fun x y z ↦ (B[[y]]) ((⁅A[[x]], C[[z]]⁆) v)
  have hF₁ (j : ℕ) (x y z : ℤ) : ((δ₁₃ ^ j) F₁) x y z =
      ((FormalDistribution.mulSub ^ j) (A.commutatorDistribution C) x z) ((B[[y]]) v) := by
    let ψ : Module.End R V →+ V :=
      { toFun := fun X ↦ X ((B[[y]]) v), map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    have h := mulSub_pow_comp ψ (A.commutatorDistribution C) j x z
    simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, commutatorDistribution_apply,
      ← Ring.lie_def] at h
    exact (δ₁₃_pow_apply j F₁ x y z).trans h
  have hF₂ (j : ℕ) (x y z : ℤ) : ((δ₁₃ ^ j) F₂) x y z =
      (B[[y]]) (((FormalDistribution.mulSub ^ j) (A.commutatorDistribution C) x z) v) := by
    let ψ : Module.End R V →+ V :=
      { toFun := fun X ↦ (B[[y]]) (X v), map_zero' := map_zero _,
        map_add' := fun _ _ ↦ map_add _ _ _ }
    have h := mulSub_pow_comp ψ (A.commutatorDistribution C) j x z
    simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, commutatorDistribution_apply,
      ← Ring.lie_def] at h
    exact (δ₁₃_pow_apply j F₂ x y z).trans h
  have htrunc : SplitTrunc F₁ F₂ := fun y z ↦ by
    obtain ⟨P, hP⟩ := B.exists_forall_ncoeff_apply_eq_zero v
    obtain ⟨Q₁, hQ₁⟩ := A.exists_forall_ncoeff_apply_eq_zero v
    obtain ⟨Q₂, hQ₂⟩ := A.exists_forall_ncoeff_apply_eq_zero ((C[[z]]) v)
    refine ⟨⟨P + y.natAbs, fun i hi ↦ by dsimp only [F₁]; rw [hP _ (by omega), map_zero]⟩,
      ⟨max Q₁ Q₂, fun i hi ↦ ?_⟩⟩
    dsimp only [F₂]
    rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
      hQ₂ _ (by have := le_trans (le_max_right _ _) hi; omega),
      hQ₁ _ (by have := le_trans (le_max_left _ _) hi; omega), map_zero, sub_self, map_zero]
  rw [show r₀ + 2 * r₁ + r₂ = (r₀ + r₁ + r₂) + r₁ by omega]
  refine mulSub_pow_splitDist_eq_zero htrunc
    (by funext x y z; rw [hF₁, hAC', Pi.zero_apply, Pi.zero_apply, LinearMap.zero_apply]; rfl)
    (by funext x y z
        rw [hF₂, hAC', Pi.zero_apply, Pi.zero_apply, LinearMap.zero_apply, map_zero]; rfl)
    fun j _ ↦ ?_
  have hloc := (hAC.nonnegResidueProduct_left hAB hBC.symm j).symm
  rw [show r₁ + r₀ + r₂ = r₀ + r₁ + r₂ by omega, isLocalOfOrder_iff_mulSub_pow_eq_zero] at hloc
  have hb : (fun y z ↦ ((δ₁₃ ^ j) F₁) 0 y z - ((δ₁₃ ^ j) F₂) 0 y z) =
      -(fun y z ↦ ev (B.commutatorDistribution (nonnegResidueProduct j A C) y z)) := by
    ext y z
    rw [Pi.neg_apply, Pi.neg_apply, hF₁, hF₂, FormalDistribution.mulSub_pow_apply]
    have hres : ∑ ij ∈ antidiagonal j, j.choose ij.1 • (-1 : ℤ) ^ ij.2 •
          A.commutatorDistribution C (0 + ij.1) (z + ij.2) =
        (nonnegResidueProduct j A C)[[z]] := by
      rw [ncoeff_nonnegResidueProduct]
      exact sum_congr rfl fun ij _ ↦ by rw [zero_add, commutatorDistribution_apply]
    rw [hres]
    simp only [ev, AddMonoidHom.coe_mk, ZeroHom.coe_mk, commutatorDistribution_apply,
      LinearMap.sub_apply, mul_apply_eq_comp, neg_sub]
  rw [hb, map_neg, neg_eq_zero]
  ext y z
  rw [mulSub_pow_comp ev _ (r₀ + r₁ + r₂) y z, hloc]
  rfl

/-- **Dong's lemma for normal ordering.** If `(A, B)`, `(A, C)`, `(B, C)` are mutually local of
orders `r₀`, `r₁`, `r₂`, then `normalOrder A B` is local with `C` of order `r₀ + 2 * r₁ + r₂`. -/
theorem normalOrder_left {A B C : VertexOperator R V} {r₀ r₁ r₂ : ℕ}
    (hAB : A.IsLocalOfOrder B r₀) (hAC : A.IsLocalOfOrder C r₁) (hBC : B.IsLocalOfOrder C r₂) :
    (normalOrder A B).IsLocalOfOrder C (r₀ + 2 * r₁ + r₂) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  ext y₀ z₀ v
  let ev : Module.End R V →+ V :=
    { toFun := fun f ↦ f v, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  have hev := mulSub_pow_comp ev ((normalOrder A B).commutatorDistribution C)
    (r₀ + 2 * r₁ + r₂) y₀ z₀
  simp only [ev, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hev
  rw [← hev, Pi.zero_apply, Pi.zero_apply, LinearMap.zero_apply]
  have hdecomp : (fun y z ↦ ((normalOrder A B).commutatorDistribution C y z) v) =
      (fun y z ↦ (∑ᶠ i : ℕ, (A[[-(i : ℤ) - 1]]) ((⁅B[[y + i]], C[[z]]⁆) v)) +
        ∑ᶠ i : ℕ, (⁅B[[y - 1 - i]], C[[z]]⁆) ((A[[(i : ℤ)]]) v)) +
      splitDist (fun x y z ↦ (⁅A[[x]], C[[z]]⁆) ((B[[y]]) v))
        (fun x y z ↦ (B[[y]]) ((⁅A[[x]], C[[z]]⁆) v)) := by
    ext y z
    exact normalOrder_commutator_decomp A B C v y z
  rw [hdecomp, map_add, Pi.add_apply, Pi.add_apply]
  have h₁ : ((FormalDistribution.mulSub ^ (r₀ + 2 * r₁ + r₂))
      (fun y z ↦ (∑ᶠ i : ℕ, (A[[-(i : ℤ) - 1]]) ((⁅B[[y + i]], C[[z]]⁆) v)) +
        ∑ᶠ i : ℕ, (⁅B[[y - 1 - i]], C[[z]]⁆) ((A[[(i : ℤ)]]) v))) y₀ z₀ = 0 := by
    rw [show r₀ + 2 * r₁ + r₂ = (r₀ + 2 * r₁) + r₂ by omega, pow_add, end_mul_apply,
      mulSub_pow_normalOrder_bc_eq_zero hBC v, map_zero, Pi.zero_apply, Pi.zero_apply]
  rw [h₁, mulSub_pow_normalOrder_ac_eq_zero hAB hAC hBC v, Pi.zero_apply, Pi.zero_apply, add_zero]

/-- Symmetric form of `normalOrder_left` in the second factor. -/
theorem normalOrder_right {A B C : VertexOperator R V} {r₀ r₁ r₂ : ℕ}
    (hBC : B.IsLocalOfOrder C r₀) (hAB : A.IsLocalOfOrder B r₁) (hAC : A.IsLocalOfOrder C r₂) :
    A.IsLocalOfOrder (normalOrder B C) (r₀ + 2 * r₁ + r₂) :=
  (hBC.normalOrder_left hAB.symm hAC.symm).symm

/-- **Dong's lemma.** Mutual locality of fields is preserved by every integer residue product
`nthProduct n A B` (`n : ℤ`), over any commutative ring. -/
theorem nthProduct_left {A B C : VertexOperator R V} {r₀ r₁ r₂ : ℕ}
    (hAB : A.IsLocalOfOrder B r₀) (hAC : A.IsLocalOfOrder C r₁) (hBC : B.IsLocalOfOrder C r₂)
    (n : ℤ) :
    (nthProduct n A B).IsLocalOfOrder C (r₀ + 2 * r₁ + r₂ + 3 * (-n - 1).toNat) := by
  by_cases hn : 0 ≤ n
  · rw [nthProduct_of_nonneg hn]
    exact (hAB.nonnegResidueProduct_left hAC hBC n.toNat).mono (by omega)
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
    rw [nthProduct_neg_natCast_sub_one, show (-(-(k : ℤ) - 1) - 1).toNat = k by omega,
      show r₀ + 2 * r₁ + r₂ + 3 * k = (r₀ + k) + 2 * (r₁ + k) + r₂ by omega]
    exact (hAB.hasseDeriv_left k).normalOrder_left (hAC.hasseDeriv_left k) hBC

/-- Symmetric form of `nthProduct_left` (**Dong's lemma** in the second factor). -/
theorem nthProduct_right {A B C : VertexOperator R V} {r₀ r₁ r₂ : ℕ}
    (hBC : B.IsLocalOfOrder C r₀) (hAB : A.IsLocalOfOrder B r₁) (hAC : A.IsLocalOfOrder C r₂)
    (n : ℤ) :
    A.IsLocalOfOrder (nthProduct n B C) (r₀ + 2 * r₁ + r₂ + 3 * (-n - 1).toNat) :=
  (hBC.nthProduct_left hAB.symm hAC.symm n).symm

end IsLocalOfOrder

end VertexOperator
