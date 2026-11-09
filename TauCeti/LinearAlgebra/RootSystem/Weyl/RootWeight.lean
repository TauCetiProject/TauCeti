/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import TauCeti.LinearAlgebra.Finsupp.LinearCombination
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic

/-!
# The integral weights of the roots relative to a base

Let `b` be a base of a finite crystallographic root system `P`. A root `αⱼ` determines the integral
family `k ↦ ⟨αⱼ, αₖ∨⟩` indexed by the simple roots, its weight. The weight of a simple root `αᵢ` is
the `i`-th row of the Cartan matrix, and the simple reflection `sᵢ` acts on weights by
`χ ↦ χ - χ i • b.cartanMatrix.row i`. Since every root is obtained from a simple root by simple
reflections, a property of integral weights can be propagated from the rows of the Cartan matrix to
the weights of all roots. This is how the weight spaces of a Lie algebra presented by Serre's
relations are compared at all the roots, starting from the simple ones.

Conversely, a set of integral weights that is stable under the simple reflections, whose nonzero
members are nonnegative or nonpositive integral combinations of the simple roots, and which
contains no multiple `m • αᵢ`, `m ≥ 2`, of a simple root, consists of zero and weights of roots.
A positive member pairs positively with some simple coroot, because the Cartan matrix is of finite
type (`TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_apply_mul_nonpos`); reflecting in that
simple root lowers the height, and the descent ends at a simple root. This is how the weights of a
Lie algebra presented by Serre's relations are shown to be roots.

## Main results

* `RootPairing.pairingIn_reflectionPerm_left_eq_sub`: the action of a reflection on the pairings of
  a root.
* `RootPairing.Base.linearIndependent_cartanMatrix_row`: the rows of the Cartan matrix are linearly
  independent over `ℤ`.
* `RootPairing.Base.pairingIn_eq_cartanMatrix_row`: the weight of a simple root is a row of the
  Cartan matrix.
* `RootPairing.Base.induction_pairingIn_reflection`: the induction principle on weights.
* `RootPairing.Base.exists_eq_pairingIn_of_reflection_mem`: the nonzero members of a
  reflection-stable set of signed weights with no multiples `m • αᵢ`, `m ≥ 2`, are root weights.

## References

* [J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972], §10.3
  and §18.3
-/

public section

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- A reflection acts on the pairings of a root by
`⟨sᵢ αⱼ, αₖ∨⟩ = ⟨αⱼ, αₖ∨⟩ - ⟨αⱼ, αᵢ∨⟩ * ⟨αᵢ, αₖ∨⟩`. -/
theorem RootPairing.pairingIn_reflectionPerm_left_eq_sub (S : Type*) [CommRing S] [Algebra S R]
    [FaithfulSMul S R] [P.IsValuedIn S] (i j k : ι) :
    P.pairingIn S (P.reflectionPerm i j) k =
      P.pairingIn S j k - P.pairingIn S j i * P.pairingIn S i k := by
  apply FaithfulSMul.algebraMap_injective S R
  simp only [algebraMap_pairingIn, map_sub, map_mul]
  rw [← P.root_coroot_eq_pairing (P.reflectionPerm i j) k, P.root_reflectionPerm,
    P.reflection_apply_root]
  simp

namespace RootPairing.Base

variable [P.IsCrystallographic] [CharZero R] [Finite ι] [IsDomain R]

/-- The rows of the Cartan matrix of a base of a finite crystallographic root system are linearly
independent over `ℤ`. -/
theorem linearIndependent_cartanMatrix_row [P.IsRootSystem] (b : P.Base) :
    LinearIndependent ℤ b.cartanMatrix.row := by
  classical
  refine b.cartanMatrix.linearIndependent_rows_of_det_ne_zero ?_
  rw [← Matrix.nondegenerate_iff_det_ne_zero]
  exact b.cartanMatrix_nondegenerate

omit [CharZero R] [Finite ι] [IsDomain R] in
/-- The weight `k ↦ ⟨αᵢ, αₖ∨⟩` of a simple root `αᵢ` is the `i`-th row of the Cartan matrix. -/
theorem pairingIn_eq_cartanMatrix_row (b : P.Base) (i : b.support) :
    (fun k : b.support ↦ P.pairingIn ℤ i k) = b.cartanMatrix.row i := by
  funext k
  simp [cartanMatrixIn_def]

/-- **Induction on the weights of the roots.** For a base of a finite reduced crystallographic root
pairing, a property of integral weights that holds at the rows of the Cartan matrix (the weights of
the simple roots) and is stable under the simple reflections holds at the weight of every root. -/
theorem induction_pairingIn_reflection [P.IsReduced] (b : P.Base) {Q : (b.support → ℤ) → Prop}
    (hsimple : ∀ i : b.support, Q (b.cartanMatrix.row i))
    (hrefl : ∀ (χ : b.support → ℤ) (i : b.support), Q χ → Q (χ - χ i • b.cartanMatrix.row i))
    (j : ι) : Q fun k : b.support ↦ P.pairingIn ℤ j k := by
  let w (j : ι) : b.support → ℤ := fun k ↦ P.pairingIn ℤ j k
  have hrow (i : b.support) : w i = b.cartanMatrix.row i := b.pairingIn_eq_cartanMatrix_row i
  have hreflect (i : b.support) (j : ι) :
      w (P.reflectionPerm i j) = w j - w j i • b.cartanMatrix.row i := by
    funext k
    rw [Pi.sub_apply, Pi.smul_apply, ← hrow, smul_eq_mul]
    exact P.pairingIn_reflectionPerm_left_eq_sub ℤ i j k
  have hneg (i : ι) : w (P.reflectionPerm i i) = -w i := by
    funext k
    simp [w]
  -- Negation is not a simple reflection in general, so both signs have to be carried along.
  suffices h : Q (w j) ∧ Q (-w j) from h.1
  refine b.induction_reflect j (p := fun j ↦ Q (w j) ∧ Q (-w j)) ?_ ?_ ?_
  · rintro i ⟨h₁, h₂⟩
    rw [hneg, neg_neg]
    exact ⟨h₂, h₁⟩
  · intro i hi
    have hsi := hrow ⟨i, hi⟩
    refine ⟨hsi ▸ hsimple _, ?_⟩
    rw [← hneg, hreflect ⟨i, hi⟩ i, hsi]
    exact hrefl _ _ (hsimple _)
  · rintro i l ⟨h₁, h₂⟩ hl
    rw [hreflect ⟨l, hl⟩ i]
    refine ⟨hrefl _ _ h₁, ?_⟩
    have hsub : -(w i - w i ⟨l, hl⟩ • b.cartanMatrix.row ⟨l, hl⟩) =
        -w i - (-w i) ⟨l, hl⟩ • b.cartanMatrix.row ⟨l, hl⟩ := by
      funext k
      simp only [Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact hsub ▸ hrefl _ _ h₂

/-- The descent step: a positive integral combination of the simple roots in a set of weights as
in `RootPairing.Base.exists_eq_pairingIn_of_reflection_mem` is the weight of a root, by induction
on its height. -/
private theorem exists_eq_pairingIn_of_sum_smul_mem [P.IsRootSystem] (b : P.Base)
    {S : Set (b.support → ℤ)} (hrefl : ∀ χ ∈ S, ∀ i, χ - χ i • b.cartanMatrix.row i ∈ S)
    (hsign : ∀ c : b.support → ℤ, ∑ j, c j • b.cartanMatrix.row j ∈ S → 0 ≤ c ∨ c ≤ 0)
    (hmul : ∀ (i : b.support) (m : ℕ), 2 ≤ m → m • b.cartanMatrix.row i ∉ S) (n : ℕ) :
    ∀ c : b.support → ℤ, 0 ≤ c → c ≠ 0 → ∑ j, c j = n → ∑ j, c j • b.cartanMatrix.row j ∈ S →
      ∃ k : ι, ∑ j, c j • b.cartanMatrix.row j = fun l : b.support ↦ P.pairingIn ℤ k l := by
  classical
  induction n using Nat.strong_induction_on with | _ n ih => ?_
  intro c hc hc0 hn hS
  set χ := ∑ j, c j • b.cartanMatrix.row j with hχ
  -- Some simple coroot pairs positively with `χ`, since `χ` is a nonzero positive combination.
  -- Otherwise `c` would be a nonzero subdominant vector for the finite-type transposed Cartan
  -- matrix, since `χ i = ∑ j, c j * ⟨αⱼ, αᵢ∨⟩`.
  obtain ⟨i, hi⟩ : ∃ i, 0 < χ i := by
    by_contra! hle
    refine hc0 (funext fun j ↦ ?_)
    have h0 := (TauCeti.isFiniteType_cartanMatrix b).transpose
      |>.eq_zero_of_forall_mul_sum_apply_mul_nonpos (x := fun j ↦ (c j : ℚ)) fun i ↦ ?_
    · simpa using congrFun h0 j
    · have hχi : χ i = ∑ j, b.cartanMatrix j i * c j := by
        simp [hχ, Finset.sum_apply, mul_comm]
      have : ((∑ j, b.cartanMatrix j i * c j : ℤ) : ℚ) ≤ 0 := by exact_mod_cast hχi ▸ hle i
      push_cast at this
      exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hc i) (by simpa using this)
  by_cases hsupp : ∀ j, j ≠ i → c j = 0
  · -- `χ` is a multiple of the simple root `αᵢ`, so it is `αᵢ` itself.
    have hχi : χ = c i • b.cartanMatrix.row i :=
      Finset.sum_eq_single i (fun j _ hj ↦ by simp [hsupp j hj]) (by simp)
    have hci : c i ≠ 0 := fun h0 ↦ hc0 (funext fun j ↦ by
      rcases eq_or_ne j i with rfl | hj
      · exact h0
      · exact hsupp j hj)
    obtain hci1 | hci2 : c i = 1 ∨ 2 ≤ c i := by have := hc i; simp at this; omega
    · exact ⟨i, by rw [hχi, hci1, one_smul, pairingIn_eq_cartanMatrix_row]⟩
    · refine (hmul i (c i).toNat (by omega) ?_).elim
      rwa [← natCast_zsmul, Int.toNat_of_nonneg (hc i), ← hχi]
  · -- Otherwise reflecting in `αᵢ` lowers the height and keeps a positive coefficient.
    push Not at hsupp
    obtain ⟨j, hji, hcj⟩ := hsupp
    have hcj' : 0 < c j := lt_of_le_of_ne (hc j) (Ne.symm hcj)
    set c' := c - χ i • Pi.single i 1 with hc'
    have hc'j : c' j = c j := by simp [hc', hji]
    have hsum' : ∑ j, c' j • b.cartanMatrix.row j = χ - χ i • b.cartanMatrix.row i := by
      simp [hc', sub_smul, Finset.sum_sub_distrib, Pi.single_apply, hχ]
    have hS' : ∑ j, c' j • b.cartanMatrix.row j ∈ S := hsum' ▸ hrefl χ hS i
    have hc'pos : 0 ≤ c' := by
      rcases hsign c' hS' with h | h
      · exact h
      · have := h j
        simp only [Pi.zero_apply, hc'j] at this
        omega
    have hc'0 : c' ≠ 0 := fun h0 ↦ by
      have := congrFun h0 j
      simp only [hc'j, Pi.zero_apply] at this
      omega
    have hn' : ∑ j, c' j = n - χ i := by
      simp only [hc', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_pi_single', Finset.mem_univ, ite_true, mul_one, hn]
    have hsum0 : 0 ≤ ∑ j, c' j := Finset.sum_nonneg fun j _ ↦ hc'pos j
    obtain ⟨k, hk⟩ := ih (∑ j, c' j).toNat (by omega) c' hc'pos hc'0
      (Int.toNat_of_nonneg hsum0).symm hS'
    rw [hsum'] at hk
    -- `χ` is the reflection in `αᵢ` of the weight of the root `k`.
    have hki : P.pairingIn ℤ k i = -χ i := by
      rw [← congrFun hk i]
      simp
      ring
    refine ⟨P.reflectionPerm i k, funext fun l ↦ ?_⟩
    rw [P.pairingIn_reflectionPerm_left_eq_sub ℤ i k l, ← congrFun hk l, hki]
    simp [cartanMatrixIn_def]

/-- **The weights in a reflection-stable signed set are the weights of roots.** Let `b` be a base
of a finite crystallographic root system, and `S` a set of integral weights, indexed by the simple
roots, that is carried into itself by every simple reflection `χ ↦ χ - χᵢ • αᵢ`. Suppose every
nonzero member of `S` is a nonnegative or a nonpositive integral combination of the simple roots
(the rows of the Cartan matrix), and that `S` contains no multiple `m • αᵢ`, `m ≥ 2`, of a simple
root. Then every nonzero member of `S` is the weight `k ↦ ⟨α, αₖ∨⟩` of a root `α`.

The proof descends on the height. A positive member pairs positively with some simple coroot `αᵢ∨`,
because the Cartan matrix is of finite type. Unless it is a multiple of `αᵢ`, its reflection in
`αᵢ` still has a positive coefficient, hence is positive, and has smaller height. -/
theorem exists_eq_pairingIn_of_reflection_mem [P.IsRootSystem] (b : P.Base)
    {S : Set (b.support → ℤ)} (hrefl : ∀ χ ∈ S, ∀ i, χ - χ i • b.cartanMatrix.row i ∈ S)
    (hsign : ∀ χ ∈ S, χ ≠ 0 → χ ∈ AddSubsemigroup.closure (Set.range b.cartanMatrix.row) ∨
      χ ∈ AddSubsemigroup.closure (Set.range (-b.cartanMatrix.row)))
    (hmul : ∀ (i : b.support) (m : ℕ), 2 ≤ m → m • b.cartanMatrix.row i ∉ S)
    {χ : b.support → ℤ} (hχ : χ ∈ S) (h0 : χ ≠ 0) :
    ∃ k : ι, χ = fun l : b.support ↦ P.pairingIn ℤ k l := by
  classical
  have hli := b.linearIndependent_cartanMatrix_row
  -- Membership in either cone gives a coefficient vector with entries of one sign.
  have hcone (ψ : b.support → ℤ) (hψ : ψ ∈ AddSubsemigroup.closure (Set.range b.cartanMatrix.row)) :
      ∃ c : b.support → ℤ, 0 ≤ c ∧ ψ = ∑ j, c j • b.cartanMatrix.row j := by
    obtain ⟨n, hn, rfl⟩ :=
      AddSubsemigroup.exists_nonneg_linearCombination_eq_of_mem_closure_range hψ
    refine ⟨n, hn, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  have hcone' (ψ : b.support → ℤ)
      (hψ : ψ ∈ AddSubsemigroup.closure (Set.range (-b.cartanMatrix.row))) :
      ∃ c : b.support → ℤ, 0 ≤ c ∧ ψ = -∑ j, c j • b.cartanMatrix.row j := by
    obtain ⟨n, hn, rfl⟩ :=
      AddSubsemigroup.exists_nonneg_linearCombination_eq_of_mem_closure_range hψ
    refine ⟨n, hn, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp only [Pi.neg_apply, smul_neg, Finset.sum_neg_distrib]
  -- The coefficients of an integral combination of the rows are unique.
  have huniq {c d : b.support → ℤ}
      (h : ∑ j, c j • b.cartanMatrix.row j = ∑ j, d j • b.cartanMatrix.row j) : c = d := by
    have := Fintype.linearIndependent_iff.1 hli (c - d) (by
      simpa [sub_smul, Finset.sum_sub_distrib, sub_eq_zero] using h)
    exact funext fun j ↦ sub_eq_zero.1 (this j)
  have hsign' (c : b.support → ℤ) (hc : ∑ j, c j • b.cartanMatrix.row j ∈ S) :
      0 ≤ c ∨ c ≤ 0 := by
    by_cases hc0 : ∑ j, c j • b.cartanMatrix.row j = 0
    · exact .inl (huniq (hc0.trans (by simp))).ge
    rcases hsign _ hc hc0 with hpos | hneg
    · obtain ⟨d, hd, hcd⟩ := hcone _ hpos
      exact .inl (huniq hcd ▸ hd)
    · obtain ⟨d, hd, hcd⟩ := hcone' _ hneg
      have : c = -d := huniq (by simpa [neg_smul, Finset.sum_neg_distrib] using hcd)
      exact .inr (this ▸ neg_nonpos.2 hd)
  have hc0 {c : b.support → ℤ} (hχc : χ = ∑ j, c j • b.cartanMatrix.row j ∨
      χ = -∑ j, c j • b.cartanMatrix.row j) : c ≠ 0 := by
    rintro rfl
    exact h0 (by rcases hχc with h | h <;> simpa using h)
  rcases hsign χ hχ h0 with hpos | hneg
  · obtain ⟨c, hc, rfl⟩ := hcone χ hpos
    exact exists_eq_pairingIn_of_sum_smul_mem b hrefl hsign' hmul _ c hc (hc0 (.inl rfl))
      (Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ ↦ hc j)).symm hχ
  · -- A negative member is handled through the negated set, using the negated root.
    obtain ⟨c, hc, rfl⟩ := hcone' χ hneg
    obtain ⟨k, hk⟩ := exists_eq_pairingIn_of_sum_smul_mem b (S := -S)
      (fun ψ hψ i ↦ by
        have := hrefl _ hψ i
        rw [Set.mem_neg]
        convert this using 1
        simp [sub_eq_add_neg, add_comm])
      (fun d hd ↦ by
        have := hsign' (-d) (by simpa [neg_smul, Finset.sum_neg_distrib] using hd)
        rcases this with h | h
        · exact .inr (neg_nonneg.1 h)
        · exact .inl (neg_nonpos.1 h))
      (fun i m hm hmem ↦ hmul i m hm (by
        have := hrefl _ hmem i
        convert this using 1
        funext l
        simp
        ring))
      _ c hc (hc0 (.inr rfl)) (Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ ↦ hc j)).symm
      (by simpa using hχ)
    refine ⟨P.reflectionPerm k k, ?_⟩
    rw [hk]
    funext l
    simp

end RootPairing.Base
