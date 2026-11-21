/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import TauCeti.Data.Fin.StrictAnti

/-!
# Strictly monotone finite selections of naturals

A strictly monotone selection `k : Fin m → ℕ` of `m` natural numbers extends to a strictly
monotone self-map `φ : ℕ → ℕ` agreeing with `k` on the first `m` inputs. The extension can be
chosen to be an eventual translation, `φ n = n + C` for `m ≤ n`: past the selection it shifts by
a constant. That clause is what is needed when a reindexing of a sequence by `φ` must agree, past a
finite prefix, with a fixed iterate of the one-sided shift.

A strictly monotone sequence of naturals indexed by `Fin m` grows by at least the index gap. This
is deduced from its decreasing counterpart `StrictAnti.add_sub_le_nat` by reversing the indices.
Consequently, for a strictly increasing `p : Fin r → Fin n`, the complementary gaps
`n - r + i - p i` are antitone in `i`, and summed together with the gaps `p i - i` they give
`r (n - r)`. Moreover, the complement of the image of `p` has cardinality `k` whenever `r + k = n`,
and any strictly increasing `p' ≤ p` with `p' ≠ p` can be strictly increased at some index
while remaining strictly increasing and below `p`.

## Main results

* `StrictMono.exists_strictMono_nat_extending_fin_eventually_add`: the extension, as an eventual
  translation.
* `StrictMono.exists_strictMono_nat_extending_fin`: the extension, without the translation clause.
* `StrictMono.add_sub_le_nat`: a strictly monotone sequence of naturals grows by at least the index
  gap; the increasing counterpart of `StrictAnti.add_sub_le_nat`.
* `StrictMono.antitone_sub_sub`, `StrictMono.sum_sub_add_sum_sub_eq_mul`: for `p : Fin r → Fin n`
  strictly increasing, `n - r + i - p i` is antitone in `i` and
  `∑ i, (p i - i) + ∑ i, (n - r + i - p i) = r (n - r)`.
* `StrictMono.card_compl_image_eq_of_add_eq`: when `r + k = n`, `#(univ.image p)ᶜ = k`.
* `StrictMono.exists_update_strictMono`: strictly increasing `p'` at some index preserves
  strict monotonicity, stays below `p`, and reduces `∑ i, (p i - p' i)`.
* `TauCeti.doubleOrderEmb`: lifts an order embedding `Fin r ↪o Fin n` to consecutive pairs
  `Fin (2 * r) ↪o Fin (2 * n)` (`i ↦ 2 * e (i / 2) + i % 2`), with even/odd and injectivity lemmas.

The extension is adapted from `cameronfreer/exchangeability`, pinned at
`e0532e59ceff23edab44dda9ab0655debbc9cc22`.
-/

public section

variable {m : ℕ} {k : Fin m → ℕ}

/-- A strictly monotone finite selection `k : Fin m → ℕ` extends to a strictly increasing self-map
of `ℕ` that agrees with `k` on the first `m` inputs and is **eventually a translation**: beyond the
selection it adds a fixed constant `C`. -/
theorem StrictMono.exists_strictMono_nat_extending_fin_eventually_add (hk : StrictMono k) :
    ∃ (φ : ℕ → ℕ) (C : ℕ), StrictMono φ ∧ (∀ i : Fin m, φ i.val = k i) ∧
      ∀ n, m ≤ n → φ n = n + C := by
  let C := Finset.univ.sup k + 1
  let φ : ℕ → ℕ := fun n => if h : n < m then k ⟨n, h⟩ else n + C
  refine ⟨φ, C, ?_, ?_, ?_⟩
  · intro a b hab
    dsimp only [φ]
    by_cases ha : a < m
    · by_cases hb : b < m
      · rw [dite_eq_left ha, dite_eq_left hb]
        exact hk (Fin.lt_def.mpr hab)
      · rw [dite_eq_left ha, dite_eq_right hb]
        have hle_sup : k ⟨a, ha⟩ ≤ Finset.univ.sup k :=
          Finset.le_sup (f := k) (Finset.mem_univ (⟨a, ha⟩ : Fin m))
        exact (Nat.lt_succ_of_le hle_sup).trans_le (Nat.le_add_left C b)
    · by_cases hb : b < m
      · exact (ha (hab.trans hb)).elim
      · rw [dite_eq_right ha, dite_eq_right hb]
        exact Nat.add_lt_add_right hab C
  · intro i
    simp [φ, i.isLt]
  · intro n hn
    simp [φ, Nat.not_lt.mpr hn]

/-- A strictly monotone finite selection `k : Fin m → ℕ` extends to a strictly increasing
self-map of `ℕ` that agrees with `k` on the first `m` inputs.

`StrictMono.exists_strictMono_nat_extending_fin_eventually_add` additionally records that the
extension is eventually a translation. -/
theorem StrictMono.exists_strictMono_nat_extending_fin (hk : StrictMono k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i : Fin m, φ i.val = k i :=
  let ⟨φ, _, hφ, hφ_eq, _⟩ := hk.exists_strictMono_nat_extending_fin_eventually_add
  ⟨φ, hφ, hφ_eq⟩

/-- **A strictly monotone sequence of naturals grows by at least the index gap**: it gains at least
one unit at each step, hence at least `j - i` units between the indices `i ≤ j`. -/
theorem StrictMono.add_sub_le_nat {η : Fin m → ℕ} (hη : StrictMono η) {i j : Fin m}
    (hij : i ≤ j) : η i + ((j : ℕ) - (i : ℕ)) ≤ η j := by
  have h := (hη.comp_strictAnti Fin.rev_strictAnti).add_sub_le_nat (Fin.rev_le_rev.mpr hij)
  have := Fin.le_def.mp hij
  have := j.isLt
  simp only [Function.comp_apply, Fin.rev_rev, Fin.val_rev] at h
  omega

namespace StrictMono

variable {n r : ℕ} {p : Fin r → Fin n}

/-- For a strictly increasing `p : Fin r → Fin n`, the sequence `n - r + i - p i` is antitone,
since `p` grows by at least the index gap (`StrictMono.add_sub_le_nat`). -/
theorem antitone_sub_sub (hp : StrictMono p) : Antitone fun i : Fin r ↦ n - r + i - p i := by
  intro i k hik
  have := (Fin.val_strictMono.comp hp).add_sub_le_nat hik
  have := Fin.le_def.mp hik
  simp only [Function.comp_apply] at *
  omega

/-- For a strictly increasing `p : Fin r → Fin n`, the gaps `p i - i` and the complementary gaps
`n - r + i - p i` add up to `n - r` at each index, hence to `r (n - r)` in total. -/
theorem sum_sub_add_sum_sub_eq_mul (hp : StrictMono p) :
    ∑ i, ((p i : ℕ) - i) + ∑ i, (n - r + i - p i) = r * (n - r) := by
  have hp' := Fin.val_strictMono.comp hp
  have h (i : Fin r) : (p i : ℕ) - i + (n - r + i - p i) = n - r := by
    have h₀ := hp'.add_sub_le_nat (Fin.le_def.mpr (Nat.zero_le i) : (⟨0, i.pos⟩ : Fin r) ≤ i)
    have h₁ := hp'.add_sub_le_nat (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.isLt) :
      i ≤ ⟨r - 1, by omega⟩)
    have := (p ⟨r - 1, by omega⟩).isLt
    simp only [Function.comp_apply] at h₀ h₁
    omega
  simp [← Finset.sum_add_distrib, h]

/-- For a strictly increasing `p : Fin r → Fin n` with `r + k = n`, the complement of the image of
`p` has cardinality `k`. -/
theorem card_compl_image_eq_of_add_eq (hp : StrictMono p) {k : ℕ} (hnk : r + k = n) :
    (Finset.univ.image p)ᶜ.card = k := by
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_image_of_injective _ hp.injective,
    Finset.card_univ, Fintype.card_fin]
  omega

/-- Given strictly increasing `p, p' : Fin r → Fin n` with `p' ≤ p` coordinatewise and `p' ≠ p`,
there exist an index `i₀ : Fin r` and a value `v : Fin n` with `p' i₀ < v` such that
`Function.update p' i₀ v` is strictly increasing, bounded above by `p`, satisfies `v < p' l`
for all `i₀ < l`, and has strictly smaller gap sum `∑ i, (p i - p' i)`. -/
theorem exists_update_strictMono {p' : Fin r → Fin n} (hp : StrictMono p)
    (hp' : StrictMono p') (hle : ∀ i, p' i ≤ p i) (hne : p' ≠ p) :
    ∃ (i₀ : Fin r) (v : Fin n), p' i₀ < v ∧ StrictMono (Function.update p' i₀ v) ∧
      (∀ i, Function.update p' i₀ v i ≤ p i) ∧ (∀ l : Fin r, i₀ < l → v < p' l) ∧
      ∑ i, ((p i : ℕ) - Function.update p' i₀ v i) < ∑ i, ((p i : ℕ) - p' i) := by
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.mp hne
  have hD : ({i : Fin r | p' i < p i} : Finset (Fin r)).Nonempty :=
    ⟨i₁, Finset.mem_filter.mpr ⟨Finset.mem_univ i₁, lt_of_le_of_ne (hle i₁) hi₁⟩⟩
  let i₀ : Fin r := ({i : Fin r | p' i < p i} : Finset (Fin r)).max' hD
  have hi₀ : p' i₀ < p i₀ := (Finset.mem_filter.mp (Finset.max'_mem _ hD)).2
  let v : Fin n := ⟨(p' i₀ : ℕ) + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hi₀) (p i₀).isLt⟩
  have huv : p' i₀ < v := Fin.lt_def.mpr (Nat.lt_succ_self _)
  have hvp : v ≤ p i₀ := Fin.le_def.mpr (Nat.succ_le_of_lt hi₀)
  have hgt (l : Fin r) (hl : i₀ < l) : v < p' l := by
    have hmax : p' l = p l := le_antisymm (hle l) (not_lt.mp fun hlt ↦
      hl.not_ge (Finset.le_max' _ l (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hlt⟩)))
    exact hmax ▸ hvp.trans_lt (hp hl)
  refine ⟨i₀, v, huv, fun a c hac ↦ ?_, fun i ↦ by by_cases hi : i = i₀ <;> simp [hi, hvp, hle i],
    hgt, Finset.sum_lt_sum (fun i _ ↦ by by_cases hi : i = i₀ <;> simp [hi]; omega)
      ⟨i₀, Finset.mem_univ i₀, by simp only [Function.update_self]; dsimp only [v]; omega⟩⟩
  by_cases ha : a = i₀
  · subst a; rw [Function.update_self, Function.update_of_ne hac.ne']; exact hgt c hac
  · rw [Function.update_of_ne ha]
    by_cases hc : c = i₀
    · subst c; rw [Function.update_self]; exact (hp' hac).trans huv
    · rw [Function.update_of_ne hc]; exact hp' hac

end StrictMono

namespace TauCeti

/-- Lifting an order embedding `Fin r ↪o Fin n` to consecutive pairs `Fin (2 * r) ↪o Fin (2 * n)`
by `i ↦ 2 * e (i / 2) + i % 2`. -/
@[expose]
def doubleOrderEmb {n r : ℕ} (e : Fin r ↪o Fin n) : Fin (2 * r) ↪o Fin (2 * n) :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ ⟨2 * (e ⟨(i : ℕ) / 2, by omega⟩ : ℕ) + (i : ℕ) % 2, by omega⟩)
    (fun i j hij ↦ by
      rw [Fin.mk_lt_mk]
      have hdiv : (i : ℕ) / 2 ≤ (j : ℕ) / 2 := Nat.div_le_div_right (le_of_lt hij)
      rcases hdiv.eq_or_lt with heq | hlt
      · have hfin : (⟨(i : ℕ) / 2, by omega⟩ : Fin r) = ⟨(j : ℕ) / 2, by omega⟩ := Fin.ext heq
        rw [hfin]
        omega
      · have hlt' : (e ⟨(i : ℕ) / 2, by omega⟩ : ℕ) < (e ⟨(j : ℕ) / 2, by omega⟩ : ℕ) :=
          e.strictMono hlt
        omega)

/-- The underlying natural number value of `doubleOrderEmb e i`. -/
@[simp]
theorem doubleOrderEmb_apply_val {n r : ℕ} (e : Fin r ↪o Fin n) (i : Fin (2 * r)) :
    (doubleOrderEmb e i : ℕ) = 2 * (e ⟨(i : ℕ) / 2, by omega⟩ : ℕ) + (i : ℕ) % 2 :=
  rfl

/-- At even index `2 * j`, `doubleOrderEmb e` evaluates to `2 * e j`. -/
@[simp]
theorem doubleOrderEmb_even {n r : ℕ} (e : Fin r ↪o Fin n) (j : Fin r) :
    doubleOrderEmb e ⟨2 * (j : ℕ), by omega⟩ = ⟨2 * (e j : ℕ), by omega⟩ := by
  apply Fin.ext
  rw [doubleOrderEmb_apply_val]
  have h1 : (⟨(2 * (j : ℕ)) / 2, by omega⟩ : Fin r) = j :=
    Fin.ext (Nat.mul_div_cancel_left (j : ℕ) (by omega))
  rw [h1, Nat.mul_mod_right, add_zero]

/-- At odd index `2 * j + 1`, `doubleOrderEmb e` evaluates to `2 * e j + 1`. -/
@[simp]
theorem doubleOrderEmb_odd {n r : ℕ} (e : Fin r ↪o Fin n) (j : Fin r) :
    doubleOrderEmb e ⟨2 * (j : ℕ) + 1, by omega⟩ = ⟨2 * (e j : ℕ) + 1, by omega⟩ := by
  apply Fin.ext
  rw [doubleOrderEmb_apply_val]
  have h1 : (⟨(2 * (j : ℕ) + 1) / 2, by omega⟩ : Fin r) = j :=
    Fin.ext (by dsimp; omega)
  rw [h1, Nat.mul_add_mod]

/-- Lifting order embeddings to consecutive pairs via `doubleOrderEmb` is injective. -/
theorem doubleOrderEmb_injective {n r : ℕ} :
    Function.Injective (doubleOrderEmb (n := n) (r := r)) := by
  intro e₁ e₂ h
  ext j
  have hj := congrArg (fun f : Fin (2 * r) ↪o Fin (2 * n) ↦ (f ⟨2 * (j : ℕ), by omega⟩ : ℕ)) h
  simp only [doubleOrderEmb_even] at hj
  omega

end TauCeti
