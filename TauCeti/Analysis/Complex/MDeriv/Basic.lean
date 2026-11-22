/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Analysis.Complex.PartialDeriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Complex.IteratedDeriv

/-!
# Mixed partial derivatives of entire functions on `ℂⁿ`

Using the coordinate partial derivatives `∂ᵢ f (z) = Df(z) eᵢ` (`TauCeti.partialDeriv`), this
file defines, for a multi-index `σ ∈ ℕⁿ`, the mixed partial derivative

  `D^σ f = ∂₀^{σ₀} (∂₁^{σ₁} ( ⋯ (∂_{n-1}^{σ_{n-1}} f)))`

(`TauCeti.mDeriv`). This is ordinary differentiation, not divided by `σ! = ∏ᵢ σᵢ!`, and it is a
mixed partial derivative of multi-order `σ`, not the derivative of total order `∑ᵢ σᵢ` along a
single direction. For entire functions the order in which the partial derivatives are taken does
not matter, since second derivatives of `C²` functions are symmetric.

## Main results

* `TauCeti.mDeriv`, `TauCeti.mDeriv_def`: the mixed partial derivative `D^σ f` and its defining
  `List.finRange` fold equation.
* `TauCeti.mDeriv_zero`, `TauCeti.mDeriv_add_single`: `D⁰ f = f` and `D^{σ + eᵢ} f = ∂ᵢ (D^σ f)`
  for entire `f`; these two characterize `D^σ` on entire functions.
* `TauCeti.mDeriv_single`, `TauCeti.mDeriv_mDeriv`: `D^{k eᵢ} f = ∂ᵢ^k f`, and
  `D^σ (D^τ f) = D^{σ + τ} f` for entire `f`.
* `TauCeti.mDeriv_eq_iterate_partialDeriv_mDeriv_update_zero`: splitting off the `i`-th
  coordinate `D^σ f = ∂ᵢ^{σᵢ} (D^{update σ i 0} f)`.
* `TauCeti.differentiable_mDeriv`, `TauCeti.mDeriv_add`, `TauCeti.mDeriv_sub`,
  `TauCeti.mDeriv_const_mul`, `TauCeti.mDeriv_sum`, `TauCeti.mDeriv_mul_of_update_eq`: `D^σ`
  preserves entire functions, is linear on them, and commutes with multiplication by entire factors
  independent of the differentiated coordinates.
* `TauCeti.mDeriv_prod`: `D^σ (z ↦ ∏ᵢ gᵢ(zᵢ)) = z ↦ ∏ᵢ gᵢ^{(σᵢ)}(zᵢ)`.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  the notation `D^σ` for derivatives in several variables (§4.3–4.4).
-/

public section

open Function Finset

namespace TauCeti

variable {n : ℕ}

/-- The mixed partial derivative `D^σ f = ∂₀^{σ₀} (∂₁^{σ₁} ( ⋯ (∂_{n-1}^{σ_{n-1}} f)))` of a
function `f : ℂⁿ → ℂ` of multi-order `σ ∈ ℕⁿ`. It is not divided by `σ!`. -/
noncomputable def mDeriv (σ : Fin n → ℕ) (f : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  (List.finRange n).foldr (fun i g ↦ (partialDeriv i)^[σ i] g) f

/-- Defining equation of `mDeriv` as a fold of iterated coordinate partial derivatives over
`List.finRange n`. -/
theorem mDeriv_def (σ : Fin n → ℕ) (f : (Fin n → ℂ) → ℂ) :
    mDeriv σ f = (List.finRange n).foldr (fun i g ↦ (partialDeriv i)^[σ i] g) f := (rfl)

/-! ### Iterated partial derivatives along a list of coordinates -/

section List

variable {f g : (Fin n → ℂ) → ℂ}

/-- The iterated partial derivatives along the coordinates of `l`, with multiplicities `σ`;
`mDeriv σ` is the case `l = [0, 1, …, n - 1]`. -/
private noncomputable def listDeriv (l : List (Fin n)) (σ : Fin n → ℕ)
    (f : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  l.foldr (fun i g ↦ (partialDeriv i)^[σ i] g) f

private theorem mDeriv_eq_listDeriv (σ : Fin n → ℕ) (f : (Fin n → ℂ) → ℂ) :
    mDeriv σ f = listDeriv (List.finRange n) σ f := (rfl)

private theorem listDeriv_nil (σ : Fin n → ℕ) (f : (Fin n → ℂ) → ℂ) :
    listDeriv [] σ f = f := (rfl)

private theorem listDeriv_cons (i : Fin n) (l : List (Fin n)) (σ : Fin n → ℕ)
    (f : (Fin n → ℂ) → ℂ) :
    listDeriv (i :: l) σ f = (partialDeriv i)^[σ i] (listDeriv l σ f) := (rfl)

private theorem listDeriv_congr {l : List (Fin n)} {σ τ : Fin n → ℕ} (h : ∀ i ∈ l, σ i = τ i)
    (f : (Fin n → ℂ) → ℂ) : listDeriv l σ f = listDeriv l τ f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [listDeriv_cons, listDeriv_cons, h i (by simp), ih fun j hj ↦ h j (by simp [hj])]

private theorem differentiable_listDeriv (hf : Differentiable ℂ f) (l : List (Fin n))
    (σ : Fin n → ℕ) : Differentiable ℂ (listDeriv l σ f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact differentiable_iterate_partialDeriv ih i _

private theorem listDeriv_add_single (hf : Differentiable ℂ f) {l : List (Fin n)}
    (hl : l.Nodup) {i : Fin n} (hi : i ∈ l) (σ : Fin n → ℕ) :
    listDeriv l (σ + Pi.single i 1) f = partialDeriv i (listDeriv l σ f) := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    obtain ⟨hjl, hl⟩ := List.nodup_cons.mp hl
    rw [listDeriv_cons, listDeriv_cons]
    by_cases hij : i = j
    · subst hij
      rw [listDeriv_congr (τ := σ) (fun k hk ↦ by simp [ne_of_mem_of_not_mem hk hjl])]
      simp [iterate_succ_apply']
    · rw [ih hl (List.mem_of_ne_of_mem hij hi), Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hij),
        add_zero, iterate_partialDeriv_comm (differentiable_listDeriv hf l σ)]

private theorem listDeriv_add (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (l : List (Fin n)) (σ : Fin n → ℕ) :
    listDeriv l σ (f + g) = listDeriv l σ f + listDeriv l σ g := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [listDeriv_cons, listDeriv_cons, listDeriv_cons, ih,
      iterate_partialDeriv_add (differentiable_listDeriv hf l σ) (differentiable_listDeriv hg l σ)]

private theorem listDeriv_const_mul (c : ℂ) (l : List (Fin n)) (σ : Fin n → ℕ) :
    listDeriv l σ (fun z ↦ c * f z) = fun z ↦ c * listDeriv l σ f z := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [listDeriv_cons, listDeriv_cons, ih, iterate_partialDeriv_const_mul]

private theorem listDeriv_single {l : List (Fin n)} (hl : l.Nodup) (i : Fin n) (k : ℕ)
    (f : (Fin n → ℂ) → ℂ) :
    listDeriv l (Pi.single i k) f = if i ∈ l then (partialDeriv i)^[k] f else f := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    obtain ⟨hjl, hl⟩ := List.nodup_cons.mp hl
    rw [listDeriv_cons, ih hl]
    by_cases hij : i = j
    · subst hij
      simp [hjl]
    · simp [hij]

private theorem listDeriv_mul_of_update_eq {φ : (Fin n → ℂ) → ℂ} (hφ : Differentiable ℂ φ)
    (hf : Differentiable ℂ f) (l : List (Fin n)) {σ : Fin n → ℕ}
    (hφσ : ∀ j ∈ l, σ j ≠ 0 → ∀ z s, φ (update z j s) = φ z) :
    listDeriv l σ (fun z ↦ φ z * f z) = fun z ↦ φ z * listDeriv l σ f z := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [listDeriv_cons, listDeriv_cons, ih fun j hj ↦ hφσ j (List.mem_cons_of_mem i hj)]
    rcases eq_or_ne (σ i) 0 with h0 | hne
    · simp [h0]
    · exact iterate_partialDeriv_mul_of_update_eq hφ (differentiable_listDeriv hf l σ)
        (hφσ i List.mem_cons_self hne) (σ i)

private theorem listDeriv_partialDeriv (hf : Differentiable ℂ f) (l : List (Fin n))
    (σ : Fin n → ℕ) (i : Fin n) :
    listDeriv l σ (partialDeriv i f) = partialDeriv i (listDeriv l σ f) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [listDeriv_cons, listDeriv_cons, ih,
      iterate_partialDeriv_comm (differentiable_listDeriv hf l σ)]

private theorem listDeriv_iterate_partialDeriv (hf : Differentiable ℂ f) (l : List (Fin n))
    (σ : Fin n → ℕ) (i : Fin n) (k : ℕ) :
    listDeriv l σ ((partialDeriv i)^[k] f) = (partialDeriv i)^[k] (listDeriv l σ f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply',
      listDeriv_partialDeriv (differentiable_iterate_partialDeriv hf i k), ih]

private theorem listDeriv_listDeriv (hf : Differentiable ℂ f) (l : List (Fin n))
    (σ τ : Fin n → ℕ) : listDeriv l σ (listDeriv l τ f) = listDeriv l (σ + τ) f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [listDeriv_cons, listDeriv_cons, listDeriv_cons,
      listDeriv_iterate_partialDeriv (differentiable_listDeriv hf l τ), ih, Pi.add_apply,
      iterate_add_apply]

end List

/-! ### Basic properties of `mDeriv` -/

/-- The zeroth mixed partial derivative of `f` is `f`. -/
@[simp]
theorem mDeriv_zero (f : (Fin n → ℂ) → ℂ) : mDeriv 0 f = f := by
  rw [mDeriv_eq_listDeriv]
  induction List.finRange n with
  | nil => rfl
  | cons i l ih => rw [listDeriv_cons, ih, Pi.zero_apply, iterate_zero_apply]

/-- A mixed partial derivative of the zero function is zero. -/
@[simp]
theorem mDeriv_zero_fun (σ : Fin n → ℕ) : mDeriv σ (0 : (Fin n → ℂ) → ℂ) = 0 := by
  rw [mDeriv_eq_listDeriv]
  induction List.finRange n with
  | nil => rfl
  | cons i l ih =>
    rw [listDeriv_cons, ih]
    induction σ i with
    | zero => rfl
    | succ k ihk => rw [iterate_succ_apply', ihk, partialDeriv_zero_fun]

/-- A mixed partial derivative of an entire function is entire. -/
theorem differentiable_mDeriv {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) (σ : Fin n → ℕ) :
    Differentiable ℂ (mDeriv σ f) :=
  differentiable_listDeriv hf _ σ

/-- Raising the `i`-th order of a mixed partial derivative of an entire function by one applies
`∂ᵢ`: `D^{σ + eᵢ} f = ∂ᵢ (D^σ f)`. -/
theorem mDeriv_add_single {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) (σ : Fin n → ℕ)
    (i : Fin n) : mDeriv (σ + Pi.single i 1) f = partialDeriv i (mDeriv σ f) :=
  listDeriv_add_single hf (List.nodup_finRange n) (List.mem_finRange i) σ

/-- Mixed partial derivatives of an entire function compose by adding multi-orders:
`D^σ (D^τ f) = D^{σ + τ} f`. -/
theorem mDeriv_mDeriv {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) (σ τ : Fin n → ℕ) :
    mDeriv σ (mDeriv τ f) = mDeriv (σ + τ) f :=
  listDeriv_listDeriv hf _ σ τ

/-- The mixed partial derivative of multi-order `k eᵢ` is `∂ᵢ^k`. -/
@[simp]
theorem mDeriv_single (f : (Fin n → ℂ) → ℂ) (i : Fin n) (k : ℕ) :
    mDeriv (Pi.single i k) f = (partialDeriv i)^[k] f := by
  rw [mDeriv_eq_listDeriv, listDeriv_single (List.nodup_finRange n)]
  simp

/-- Splitting off the `i`-th coordinate of a mixed partial derivative of an entire function:
`D^σ f = ∂ᵢ^{σᵢ} (D^{update σ i 0} f)`. -/
theorem mDeriv_eq_iterate_partialDeriv_mDeriv_update_zero {f : (Fin n → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (σ : Fin n → ℕ) (i : Fin n) :
    mDeriv σ f = (partialDeriv i)^[σ i] (mDeriv (update σ i 0) f) := by
  have hσ : σ = Pi.single i (σ i) + update σ i 0 := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  conv_lhs => rw [hσ]
  rw [← mDeriv_mDeriv hf, mDeriv_single]

/-- `D^σ` is additive on entire functions. -/
theorem mDeriv_add {f g : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (σ : Fin n → ℕ) : mDeriv σ (f + g) = mDeriv σ f + mDeriv σ g :=
  listDeriv_add hf hg _ σ

/-- `D^σ` commutes with multiplication by a constant. -/
@[simp]
theorem mDeriv_const_mul {f : (Fin n → ℂ) → ℂ} (c : ℂ) (σ : Fin n → ℕ) :
    mDeriv σ (fun z ↦ c * f z) = fun z ↦ c * mDeriv σ f z :=
  listDeriv_const_mul c _ σ

/-- `D^σ` commutes with subtraction on entire functions. -/
theorem mDeriv_sub {f g : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (σ : Fin n → ℕ) : mDeriv σ (f - g) = mDeriv σ f - mDeriv σ g := by
  have hsub : f - g = f + fun z ↦ (-1 : ℂ) * g z := by ext z; simp [sub_eq_add_neg]
  rw [hsub, mDeriv_add hf (hg.const_mul (-1)), mDeriv_const_mul]
  ext z
  simp [sub_eq_add_neg]

/-- An entire factor independent of every coordinate differentiated by `σ` pulls out of `D^σ`. -/
theorem mDeriv_mul_of_update_eq {φ f : (Fin n → ℂ) → ℂ} (hφ : Differentiable ℂ φ)
    (hf : Differentiable ℂ f) {σ : Fin n → ℕ}
    (hφσ : ∀ j, σ j ≠ 0 → ∀ z s, φ (update z j s) = φ z) :
    mDeriv σ (fun z ↦ φ z * f z) = fun z ↦ φ z * mDeriv σ f z :=
  listDeriv_mul_of_update_eq hφ hf _ fun j _ ↦ hφσ j

/-- `D^σ` commutes with finite sums of entire functions. -/
theorem mDeriv_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin n → ℂ) → ℂ}
    (hf : ∀ a ∈ s, Differentiable ℂ (f a)) (σ : Fin n → ℕ) :
    mDeriv σ (∑ a ∈ s, f a) = ∑ a ∈ s, mDeriv σ (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, mDeriv_add (hf a (mem_insert_self a s))
      (Differentiable.sum fun b hb ↦ hf b (mem_insert_of_mem hb)),
      ih fun b hb ↦ hf b (mem_insert_of_mem hb)]

/-! ### Separated products -/

section Product

variable {g : Fin n → ℂ → ℂ}

/-- **Mixed partial derivatives of a separated product.** If `g₀, …, g_{n-1}` are entire
functions of one variable, then `D^σ (z ↦ ∏ᵢ gᵢ(zᵢ)) = z ↦ ∏ᵢ gᵢ^{(σᵢ)}(zᵢ)`. -/
theorem mDeriv_prod (hg : ∀ i, Differentiable ℂ (g i)) (σ : Fin n → ℕ) :
    mDeriv σ (fun z ↦ ∏ i, g i (z i)) = fun z ↦ ∏ i, iteratedDeriv (σ i) (g i) (z i) := by
  have key (l : List (Fin n)) (hl : l.Nodup) : ∀ g : Fin n → ℂ → ℂ, (∀ i, Differentiable ℂ (g i)) →
      listDeriv l σ (fun z ↦ ∏ i, g i (z i)) =
        fun z ↦ ∏ i, (if i ∈ l then iteratedDeriv (σ i) (g i) else g i) (z i) := by
    induction l with
    | nil => intro g _; simp [listDeriv_nil]
    | cons j l ih =>
      intro g hg
      obtain ⟨hjl, hl⟩ := List.nodup_cons.mp hl
      have hgl : ∀ i, Differentiable ℂ (if i ∈ l then iteratedDeriv (σ i) (g i) else g i) := by
        intro i
        split_ifs
        · exact (hg i).iteratedDeriv _
        · exact hg i
      rw [listDeriv_cons, ih hl g hg, iterate_partialDeriv_prod hgl]
      ext z
      refine prod_congr rfl fun i _ ↦ ?_
      by_cases hij : i = j
      · subst hij; simp [hjl]
      · simp [hij]
  rw [mDeriv_eq_listDeriv, key _ (List.nodup_finRange n) g hg]
  simp

end Product

end TauCeti
