/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Word seminorms along a family of operators

Let `p` be a seminorm on a module `M` over a seminormed commutative ring `𝕜`, and let
`D : ι → Module.End 𝕜 M` be a finite family of operators. For a word `w = [i₁, …, iₙ]` in `ι`
write `D_w = D_{i₁} ∘ ⋯ ∘ D_{iₙ}`. The *word seminorm* of order `k` is

`P^D_k(x) = ∑_{|w| ≤ k} p(D_w x)`,

summed over all words of length at most `k`. The word seminorms increase with `k`, satisfy the
recursion `P^D_{k+1}(x) = p(x) + ∑ i, P^D_k(D_i x)`, and the operators lower the order by one: if
`A = ∑ i, c i • D i`, then `P^D_k(A x) ≤ (∑ i, ‖c i‖) P^D_{k+1}(x)`, because appending a letter to
the words of length at most `k` gives distinct words of length at most `k + 1`. Induction on `k`
then compares the word seminorms along two families: if `D' j = ∑ i, c j i • D i` for every `j`,
then `P^{D'}_k ≤ (1 + ∑ j, ∑ i, ‖c j i‖)^k P^D_k`.

For the norm on the smooth vectors of a Lie group representation and `D i = dπ(X_i)` these are the
word seminorms `ContRepresentation.wordSeminorm` along a family `X` of Lie algebra elements.

## Main definitions

* `TauCeti.BoundedWord ι k`: the words in `ι` of length at most `k`.
* `TauCeti.BoundedWord.castSucc`, `TauCeti.BoundedWord.snoc`: a word of length at most `k` as a
  word of length at most `k + 1`, unchanged or with a letter appended.
* `TauCeti.BoundedWord.nil`: the empty word.
* `TauCeti.BoundedWord.snocOptionEquiv`: the words of length at most `k + 1` as the empty word or a
  word of length at most `k` followed by one letter.
* `Seminorm.endWordSeminorm p D k`: the word seminorm `P^D_k` of a seminorm `p` along a family `D`
  of operators.

## Main results

* `TauCeti.BoundedWord.sum_succ`: a sum over the words of length at most `k + 1`, split into the
  empty word and the words `w i` with `|w| ≤ k`.
* `Seminorm.endWordSeminorm_succ`: `P^D_{k+1}(x) = p(x) + ∑ i, P^D_k(D_i x)`.
* `Seminorm.endWordSeminorm_mono`: `P^D_k ≤ P^D_l` for `k ≤ l`.
* `Seminorm.endWordSeminorm_apply_le_of_eq_sum`: if `A = ∑ i, c i • D i`, then
  `P^D_k(A x) ≤ (∑ i, ‖c i‖) P^D_{k+1}(x)`.
* `Seminorm.endWordSeminorm_le_of_eq_sum`: if `D' j = ∑ i, c j i • D i`, then
  `P^{D'}_k ≤ (1 + ∑ j, ∑ i, ‖c j i‖)^k P^D_k`.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §§2.1–2.4.
-/

public section

noncomputable section

namespace TauCeti

/-! ### Words of bounded length -/


/-- The words in `ι` of length at most `k`: a word of length `n ≤ k` is `⟨n, w⟩` with
`w : Fin n → ι`. -/
abbrev BoundedWord (ι : Type*) (k : ℕ) : Type _ :=
  Σ n : Fin (k + 1), Fin n → ι

namespace BoundedWord

variable {ι : Type*} {k : ℕ}

/-- A word of length at most `k` is determined by its list of letters. -/
theorem ofFn_injective : Function.Injective fun w : BoundedWord ι k ↦ List.ofFn w.2 := by
  rintro ⟨n, f⟩ ⟨n', f'⟩ h
  obtain ⟨hn, hf⟩ := Sigma.mk.inj_iff.mp (List.ofFn_inj'.mp h)
  obtain rfl : n = n' := Fin.ext hn
  simp only [heq_iff_eq] at hf
  rw [hf]

/-- A word of length at most `k`, read as a word of length at most `k + 1`. -/
def castSucc (w : BoundedWord ι k) : BoundedWord ι (k + 1) :=
  ⟨w.1.castSucc, w.2⟩

/-- `castSucc` does not change the letters of a word. -/
@[simp]
theorem ofFn_castSucc (w : BoundedWord ι k) : List.ofFn w.castSucc.2 = List.ofFn w.2 :=
  (rfl)

/-- Distinct words stay distinct when read with a larger length bound. -/
theorem castSucc_injective : Function.Injective (castSucc (ι := ι) (k := k)) := fun w w' h ↦
  ofFn_injective (by simpa using congrArg (fun w : BoundedWord ι (k + 1) ↦ List.ofFn w.2) h)

/-- The word `w i` of length at most `k + 1` obtained by appending the letter `i` to a word `w` of
length at most `k`. -/
def snoc (w : BoundedWord ι k) (i : ι) : BoundedWord ι (k + 1) :=
  ⟨w.1.succ, Fin.snoc (α := fun _ ↦ ι) w.2 i⟩

/-- The letters of `w.snoc i` are those of `w` followed by `i`. -/
@[simp]
theorem ofFn_snoc (w : BoundedWord ι k) (i : ι) :
    List.ofFn (w.snoc i).2 = List.ofFn w.2 ++ [i] := by
  simp only [snoc, List.ofFn_succ']
  simp

/-- Appending a fixed letter is injective. -/
theorem snoc_left_injective (i : ι) : Function.Injective fun w : BoundedWord ι k ↦ w.snoc i :=
  fun w w' h ↦ ofFn_injective (by
    simpa using congrArg (fun w : BoundedWord ι (k + 1) ↦ List.ofFn w.2) h)

/-- The empty word, of length at most `k`. -/
def nil : BoundedWord ι k :=
  ⟨0, Fin.elim0⟩

/-- The empty word has no letters. -/
@[simp]
theorem ofFn_nil : List.ofFn (nil : BoundedWord ι k).2 = [] :=
  (rfl)

/-- Every word of length at most `k + 1` is uniquely the empty word (the image of `none`) or a
word `w i` with `|w| ≤ k` (the image of `some (w, i)`). -/
noncomputable def snocOptionEquiv : Option (BoundedWord ι k × ι) ≃ BoundedWord ι (k + 1) :=
  Equiv.ofBijective (Option.elim · nil fun p ↦ p.1.snoc p.2) <| by
    refine ⟨fun p q h ↦ ?_, fun w ↦ ?_⟩
    · have h' := congrArg (fun w : BoundedWord ι (k + 1) ↦ List.ofFn w.2) h
      rcases p with _ | ⟨w, i⟩ <;> rcases q with _ | ⟨w', i'⟩
      · rfl
      · simp at h'
      · simp at h'
      · simp only [Option.elim_some, ofFn_snoc] at h'
        obtain ⟨hw, hi⟩ := List.append_inj' h' rfl
        rw [ofFn_injective hw, (List.singleton_inj.mp hi)]
    · obtain ⟨n, f⟩ := w
      induction n using Fin.cases with
      | zero => exact ⟨none, Sigma.ext rfl (heq_of_eq (funext fun x ↦ x.elim0))⟩
      | succ n =>
        exact ⟨some (⟨n, Fin.init f⟩, f (Fin.last n)),
          Sigma.ext rfl (heq_of_eq (Fin.snoc_init_self f))⟩

/-- `snocOptionEquiv` sends `none` to the empty word. -/
@[simp]
theorem snocOptionEquiv_none : snocOptionEquiv none = (nil : BoundedWord ι (k + 1)) :=
  (rfl)

/-- `snocOptionEquiv` sends `some (w, i)` to `w.snoc i`. -/
@[simp]
theorem snocOptionEquiv_some (w : BoundedWord ι k) (i : ι) :
    snocOptionEquiv (some (w, i)) = w.snoc i :=
  (rfl)

/-- **A sum over the words of length at most `k + 1`** is the term of the empty word plus the
terms of the words `w i` with `|w| ≤ k`. -/
theorem sum_succ {M : Type*} [AddCommMonoid M] [Fintype ι] (f : BoundedWord ι (k + 1) → M) :
    ∑ w, f w = f nil + ∑ i, ∑ w : BoundedWord ι k, f (w.snoc i) := by
  rw [← snocOptionEquiv.sum_comp, Fintype.sum_option, Fintype.sum_prod_type_right]
  simp

end BoundedWord

end TauCeti

namespace Seminorm

open TauCeti

/-! ### The word seminorms along a family of operators -/

variable {𝕜 M ι κ : Type*} [SeminormedCommRing 𝕜] [AddCommGroup M] [Module 𝕜 M] [Fintype ι]

/-- The word seminorm `P^D_k(x) = ∑_{|w| ≤ k} p(D_w x)` of a seminorm `p` along a family `D` of
operators, summed over all words `w = [i₁, …, iₙ]` in `ι` of length at most `k`, where
`D_w = D_{i₁} ∘ ⋯ ∘ D_{iₙ}`. For the norm on the smooth vectors and `D i = dπ(X_i)` this is
`ContRepresentation.wordSeminorm`. -/
def endWordSeminorm (p : Seminorm 𝕜 M) (D : ι → Module.End 𝕜 M) (k : ℕ) : Seminorm 𝕜 M :=
  ∑ w : BoundedWord ι k, p.comp ((List.ofFn w.2).map D).prod

/-- The word seminorm along a family of operators as an explicit sum over words. -/
theorem endWordSeminorm_apply (p : Seminorm 𝕜 M) (D : ι → Module.End 𝕜 M) (k : ℕ) (x : M) :
    p.endWordSeminorm D k x = ∑ w : BoundedWord ι k, p (((List.ofFn w.2).map D).prod x) := by
  rw [← FunLike.coeAddMonoidHom_apply]
  simp [endWordSeminorm, map_sum, Finset.sum_apply]

/-- The word seminorm of order zero is the seminorm `p`. -/
@[simp]
theorem endWordSeminorm_zero (p : Seminorm 𝕜 M) (D : ι → Module.End 𝕜 M) (x : M) :
    p.endWordSeminorm D 0 x = p x := by
  rw [endWordSeminorm_apply, Fintype.sum_sigma, Fin.sum_univ_one]
  simp

/-- **The recursion for the word seminorms.** `P^D_{k+1}(x) = p(x) + ∑ i, P^D_k(D_i x)`: a word
of length at most `k + 1` is empty or a word of length at most `k` followed by a letter `i`, and
`D_{w i} x = D_w D_i x`. -/
theorem endWordSeminorm_succ (p : Seminorm 𝕜 M) (D : ι → Module.End 𝕜 M) (k : ℕ) (x : M) :
    p.endWordSeminorm D (k + 1) x = p x + ∑ i, p.endWordSeminorm D k (D i x) := by
  rw [endWordSeminorm_apply, BoundedWord.sum_succ (M := ℝ)]
  simp only [BoundedWord.ofFn_nil, BoundedWord.ofFn_snoc, List.map_nil, List.prod_nil,
    List.map_append, List.prod_append, List.map_cons, List.prod_cons, mul_one,
    one_apply_eq_self, mul_apply_eq_comp, endWordSeminorm_apply]

/-- The word seminorms increase with the order: `P^D_k ≤ P^D_{k+1}`. -/
theorem endWordSeminorm_le_succ (p : Seminorm 𝕜 M) (D : ι → Module.End 𝕜 M) (k : ℕ) (x : M) :
    p.endWordSeminorm D k x ≤ p.endWordSeminorm D (k + 1) x := by
  classical
  rw [endWordSeminorm_apply, endWordSeminorm_apply]
  exact Finset.sum_le_sum_of_injOn BoundedWord.castSucc BoundedWord.castSucc_injective.injOn
    (Finset.subset_univ _) (fun _ _ ↦ le_rfl) fun _ _ _ ↦ apply_nonneg _ _

/-- The word seminorms increase with the order: `P^D_k ≤ P^D_l` for `k ≤ l`. -/
theorem endWordSeminorm_mono (p : Seminorm 𝕜 M) (D : ι → Module.End 𝕜 M) {k l : ℕ} (hkl : k ≤ l)
    (x : M) : p.endWordSeminorm D k x ≤ p.endWordSeminorm D l x :=
  monotone_nat_of_le_succ (fun n ↦ p.endWordSeminorm_le_succ D n x) hkl

/-- **The derivative estimate along a family element.** `P^D_k(D_i x) ≤ P^D_{k+1}(x)`. -/
theorem endWordSeminorm_apply_le (p : Seminorm 𝕜 M) (D : ι → Module.End 𝕜 M) (k : ℕ) (i : ι)
    (x : M) : p.endWordSeminorm D k (D i x) ≤ p.endWordSeminorm D (k + 1) x := by
  rw [endWordSeminorm_succ]
  exact le_add_of_nonneg_of_le (apply_nonneg _ _) (Finset.single_le_sum
    (f := fun i ↦ p.endWordSeminorm D k (D i x)) (fun _ _ ↦ apply_nonneg _ _) (Finset.mem_univ i))

/-- **The derivative estimate.** If `A = ∑ i, c i • D i`, then
`P^D_k(A x) ≤ (∑ i, ‖c i‖) P^D_{k+1}(x)`. -/
theorem endWordSeminorm_apply_le_of_eq_sum (p : Seminorm 𝕜 M) (D : ι → Module.End 𝕜 M) (k : ℕ)
    {A : Module.End 𝕜 M} (c : ι → 𝕜) (hA : A = ∑ i, c i • D i) (x : M) :
    p.endWordSeminorm D k (A x) ≤ (∑ i, ‖c i‖) * p.endWordSeminorm D (k + 1) x := by
  rw [hA, LinearMap.sum_apply, Finset.sum_mul]
  refine (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans
    (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [LinearMap.smul_apply, map_smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (p.endWordSeminorm_apply_le D k i x) (norm_nonneg _)

/-! ### Comparison of two families -/

variable [Fintype κ]

/-- **Comparison of the word seminorms along two families of operators.** If
`D' j = ∑ i, c j i • D i` for every `j`, then `P^{D'}_k ≤ (1 + ∑ j, ∑ i, ‖c j i‖)^k P^D_k`. -/
theorem endWordSeminorm_le_of_eq_sum (p : Seminorm 𝕜 M) (D : ι → Module.End 𝕜 M)
    {D' : κ → Module.End 𝕜 M} (c : κ → ι → 𝕜) (hD : ∀ j, D' j = ∑ i, c j i • D i) (k : ℕ)
    (x : M) :
    p.endWordSeminorm D' k x ≤ (1 + ∑ j, ∑ i, ‖c j i‖) ^ k * p.endWordSeminorm D k x := by
  set S := ∑ j, ∑ i, ‖c j i‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hC : 1 ≤ (1 + S) ^ k := one_le_pow₀ (le_add_of_nonneg_right hS)
    have hx : p x ≤ (1 + S) ^ k * p.endWordSeminorm D (k + 1) x := by
      rw [← p.endWordSeminorm_zero D]
      exact (p.endWordSeminorm_mono D (Nat.zero_le _) x).trans
        (le_mul_of_one_le_left (apply_nonneg _ _) hC)
    have hsum : ∑ j, p.endWordSeminorm D' k (D' j x) ≤
        (1 + S) ^ k * (S * p.endWordSeminorm D (k + 1) x) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ ↦ (ih _).trans ?_
      exact mul_le_mul_of_nonneg_left
        (p.endWordSeminorm_apply_le_of_eq_sum D k (c j) (hD j) x) (pow_nonneg (by positivity) _)
    rw [endWordSeminorm_succ]
    calc p x + ∑ j, p.endWordSeminorm D' k (D' j x)
      _ ≤ (1 + S) ^ k * p.endWordSeminorm D (k + 1) x +
          (1 + S) ^ k * (S * p.endWordSeminorm D (k + 1) x) := add_le_add hx hsum
      _ = (1 + S) ^ (k + 1) * p.endWordSeminorm D (k + 1) x := by ring

end Seminorm
