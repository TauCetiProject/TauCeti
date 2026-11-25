/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Seminorm

/-!
# Changing the family of the word seminorms

Let `π` be a continuous representation of a real Lie group `G` on a normed space `V`, and let
`P^X_k(v) = ∑_{|w| ≤ k} ‖dπ(X_w) v‖` be the word seminorm of order `k` along a finite family
`X` of left-invariant derivations (`ContRepresentation.wordSeminorm`).

A word of length at most `k + 1` is empty or a word of length at most `k` followed by one letter,
so `P^X_{k+1}(v) = ‖v‖ + ∑ i, P^X_k(dπ(X_i) v)`. With the derivative estimate
`P^X_k(dπ(Y) v) ≤ (∑ i, |c i|) P^X_{k+1}(v)` for `Y = ∑ i, c i • X i`, induction on `k` compares
the word seminorms along two families: if `Y j = ∑ i, c j i • X i` for every `j`, then
`P^Y_k ≤ (1 + ∑ j, ∑ i, |c j i|)^k P^X_k`. For two real bases of the Lie algebra each family is a
combination of the other, so the two families of word seminorms bound each other and define the
same topology on the smooth vectors: the word-seminorm topology does not depend on the basis.

## Main results

* `TauCeti.BoundedWord.sum_succ`: a sum over the words of length at most `k + 1`, split into the
  empty word and the words `w i` with `|w| ≤ k`.
* `ContRepresentation.wordSeminorm_succ`: `P_{k+1}(v) = ‖v‖ + ∑ i, P_k(dπ(X_i) v)`.
* `ContRepresentation.wordSeminorm_le_of_eq_sum`: if `Y j = ∑ i, c j i • X i`, then
  `P^Y_k ≤ (1 + ∑ j, ∑ i, |c j i|)^k P^X_k`.
* `ContRepresentation.wordSeminorm_basis_le`: the comparison for two real bases.
* `ContRepresentation.isBounded_wordSeminorm_basis`: the word seminorms along one basis are
  bounded by those along another, as families of seminorms (`Seminorm.IsBounded`).

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §§2.1–2.5.
-/

public section

noncomputable section

open scoped ContDiff Manifold NNReal

namespace TauCeti

namespace BoundedWord

variable {ι : Type*} {k : ℕ}

/-- The empty word, of length at most `k`. -/
def nil : BoundedWord ι k :=
  ⟨0, Fin.elim0⟩

/-- The empty word has no letters. -/
@[simp]
theorem ofFn_nil : List.ofFn (nil : BoundedWord ι k).2 = [] :=
  (rfl)

/-- A word of length at most `k + 1` is the empty word or a word of length at most `k` followed
by one letter. -/
def consOption : Option (BoundedWord ι k × ι) → BoundedWord ι (k + 1)
  | none => nil
  | some p => p.1.snoc p.2

/-- Every word of length at most `k + 1` is uniquely empty or of the form `w i` with `|w| ≤ k`. -/
theorem consOption_bijective : Function.Bijective (consOption (ι := ι) (k := k)) := by
  refine ⟨fun p q h ↦ ?_, fun w ↦ ?_⟩
  · have h' := congrArg (fun w : BoundedWord ι (k + 1) ↦ List.ofFn w.2) h
    rcases p with _ | ⟨w, i⟩ <;> rcases q with _ | ⟨w', i'⟩
    · rfl
    · simp [consOption] at h'
    · simp [consOption] at h'
    · simp only [consOption, BoundedWord.ofFn_snoc] at h'
      obtain ⟨hw, hi⟩ := List.append_inj' h' rfl
      rw [ofFn_injective hw, (List.singleton_inj.mp hi)]
  · obtain ⟨n, f⟩ := w
    induction n using Fin.cases with
    | zero => exact ⟨none, Sigma.ext rfl (heq_of_eq (funext fun x ↦ x.elim0))⟩
    | succ n =>
      refine ⟨some (⟨n, Fin.init f⟩, f (Fin.last n)), ofFn_injective ?_⟩
      simp only [consOption, ofFn_snoc]
      rw [List.ofFn_succ', List.concat_eq_append]
      rfl

/-- **A sum over the words of length at most `k + 1`** is the term of the empty word plus the
terms of the words `w i` with `|w| ≤ k`. -/
theorem sum_succ {M : Type*} [AddCommMonoid M] [Fintype ι] (f : BoundedWord ι (k + 1) → M) :
    ∑ w, f w = f nil + ∑ i, ∑ w : BoundedWord ι k, f (w.snoc i) := by
  rw [← (Fintype.sum_bijective _ consOption_bijective (f ∘ consOption) f fun _ ↦ rfl),
    Fintype.sum_option, Fintype.sum_prod_type_right]
  rfl

end BoundedWord

end TauCeti

namespace ContRepresentation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  {π : ContRepresentation 𝕜 G V} {ι κ : Type*} [Fintype ι] [Fintype κ]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The recursion for the word seminorms.** `P_{k+1}(v) = ‖v‖ + ∑ i, P_k(dπ(X_i) v)`: a word
of length at most `k + 1` is empty or a word of length at most `k` followed by a letter `i`, and
`dπ(X_{w i}) v = dπ(X_w) dπ(X_i) v`. -/
theorem wordSeminorm_succ (X : ι → LeftInvariantDerivation I G) (k : ℕ)
    (v : lieSmoothVectors I π) :
    wordSeminorm I π X (k + 1) v =
      ‖(v : V)‖ + ∑ i, wordSeminorm I π X k (lieSmoothVectorsDerivative I π (X i) v) := by
  rw [wordSeminorm_apply, BoundedWord.sum_succ (M := ℝ)]
  simp only [BoundedWord.ofFn_nil, wordAction_nil, BoundedWord.ofFn_snoc, wordAction_append,
    wordAction_singleton, one_apply_eq_self, mul_apply_eq_comp, wordSeminorm_apply]

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]

/-- **Comparison of the word seminorms along two families.** If `Y j = ∑ i, c j i • X i` for
every `j`, then `P^Y_k ≤ (1 + ∑ j, ∑ i, |c j i|)^k P^X_k`. -/
theorem wordSeminorm_le_of_eq_sum (X : ι → LeftInvariantDerivation I G)
    {Y : κ → LeftInvariantDerivation I G} (c : κ → ι → ℝ) (hY : ∀ j, Y j = ∑ i, c j i • X i)
    (k : ℕ) (v : lieSmoothVectors I π) :
    wordSeminorm I π Y k v ≤
      (1 + ∑ j, ∑ i, |c j i|) ^ k * wordSeminorm I π X k v := by
  set S := ∑ j, ∑ i, |c j i|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    have hC : 1 ≤ (1 + S) ^ k := one_le_pow₀ (le_add_of_nonneg_right hS)
    have hv : ‖(v : V)‖ ≤ (1 + S) ^ k * wordSeminorm I π X (k + 1) v := by
      rw [← wordSeminorm_zero X]
      exact (wordSeminorm_mono X (Nat.zero_le _) v).trans
        (le_mul_of_one_le_left (apply_nonneg _ _) hC)
    have hsum : ∑ j, wordSeminorm I π Y k (lieSmoothVectorsDerivative I π (Y j) v) ≤
        (1 + S) ^ k * (S * wordSeminorm I π X (k + 1) v) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ ↦ (ih _).trans ?_
      exact mul_le_mul_of_nonneg_left
        (wordSeminorm_lieSmoothVectorsDerivative_le_of_eq_sum X k (c j) (hY j) v)
        (pow_nonneg (by positivity) _)
    rw [wordSeminorm_succ]
    calc ‖(v : V)‖ + ∑ j, wordSeminorm I π Y k (lieSmoothVectorsDerivative I π (Y j) v)
      _ ≤ (1 + S) ^ k * wordSeminorm I π X (k + 1) v +
          (1 + S) ^ k * (S * wordSeminorm I π X (k + 1) v) := add_le_add hv hsum
      _ = (1 + S) ^ (k + 1) * wordSeminorm I π X (k + 1) v := by ring

/-- **The word seminorms along two bases are comparable.** For real bases `b` and `b'` of the
left-invariant derivations, `P^{b'}_k ≤ (1 + ∑ j, ∑ i, |b.repr (b' j) i|)^k P^b_k`. -/
theorem wordSeminorm_basis_le (b : Module.Basis ι ℝ (LeftInvariantDerivation I G))
    (b' : Module.Basis κ ℝ (LeftInvariantDerivation I G)) (k : ℕ) (v : lieSmoothVectors I π) :
    wordSeminorm I π b' k v ≤
      (1 + ∑ j, ∑ i, |b.repr (b' j) i|) ^ k * wordSeminorm I π b k v :=
  wordSeminorm_le_of_eq_sum b (fun j i ↦ b.repr (b' j) i) (fun j ↦ (b.sum_repr (b' j)).symm) k v

/-- **The word-seminorm topology does not depend on the basis.** For real bases `b` and `b'` of
the left-invariant derivations, the family `k ↦ P^{b'}_k` is bounded by the family
`k ↦ P^b_k`; by symmetry the two families define the same topology. -/
theorem isBounded_wordSeminorm_basis (b : Module.Basis ι ℝ (LeftInvariantDerivation I G))
    (b' : Module.Basis κ ℝ (LeftInvariantDerivation I G)) :
    Seminorm.IsBounded (wordSeminorm I π b) (wordSeminorm I π b') LinearMap.id := by
  intro k
  refine ⟨{k}, ⟨(1 + ∑ j, ∑ i, |b.repr (b' j) i|) ^ k, by positivity⟩, fun v ↦ ?_⟩
  change _ ≤ ((1 + ∑ j, ∑ i, |b.repr (b' j) i|) ^ k : ℝ) * _
  rw [Seminorm.comp_id, Finset.sup_singleton]
  exact wordSeminorm_basis_le b b' k v

end ContRepresentation
