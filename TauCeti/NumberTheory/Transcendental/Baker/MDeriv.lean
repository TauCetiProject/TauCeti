/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Matrix.Mul
public import TauCeti.Analysis.Complex.PartialDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Complex.IteratedDeriv

/-!
# Mixed partial derivatives of entire functions on `ℂⁿ`

The transcendence method of Schneider, Lang and Baker in several variables differentiates entire
functions `f : ℂⁿ → ℂ` along the coordinate directions. Using the partial derivatives
`∂ᵢ f (z) = Df(z) eᵢ` (`TauCeti.partialDeriv`), this file defines, for a multi-index `σ ∈ ℕⁿ`, the
mixed partial derivative

  `D^σ f = ∂₀^{σ₀} (∂₁^{σ₁} ( ⋯ (∂_{n-1}^{σ_{n-1}} f)))`

(`TauCeti.Baker.mDeriv`). This is ordinary differentiation, not divided by `σ! = ∏ᵢ σᵢ!`, and it
is a mixed partial derivative of multi-order `σ`, not the derivative of total order `∑ᵢ σᵢ` along
a single direction. For entire functions the order in which the partial derivatives are taken does
not matter, since second derivatives of `C²` functions are symmetric.

The auxiliary functions of the method are integer combinations of the exponential monomials
`z ↦ z^τ e^{w · z}`, and the formulas for their derivatives are what the arithmetic estimates
consume. Both factor over the coordinates, so they are special cases of the formula for a
separated product `z ↦ ∏ᵢ gᵢ(zᵢ)` of entire functions of one variable, whose mixed partial
derivative is `z ↦ ∏ᵢ gᵢ^{(σᵢ)}(zᵢ)`.

## Main results

* `TauCeti.Baker.mDeriv_zero`, `TauCeti.Baker.mDeriv_add_single`: `D⁰ f = f` and
  `D^{σ + eᵢ} f = ∂ᵢ (D^σ f)` for entire `f`; these two characterize `D^σ` on entire functions.
* `TauCeti.Baker.mDeriv_mDeriv`: `D^σ (D^τ f) = D^{σ + τ} f` for entire `f`.
* `TauCeti.Baker.differentiable_mDeriv`, `TauCeti.Baker.mDeriv_add`,
  `TauCeti.Baker.mDeriv_const_mul`, `TauCeti.Baker.mDeriv_sum`: `D^σ` preserves entire functions
  and is linear on them.
* `TauCeti.Baker.mDeriv_prod`: `D^σ (z ↦ ∏ᵢ gᵢ(zᵢ)) = z ↦ ∏ᵢ gᵢ^{(σᵢ)}(zᵢ)`.
* `TauCeti.Baker.mDeriv_exp_dotProduct`: `D^σ (z ↦ e^{w · z}) = z ↦ w^σ e^{w · z}`.
* `TauCeti.Baker.mDeriv_monomial_mul_exp`: the Leibniz expansion of `D^σ (z ↦ z^τ e^{w · z})`.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  the notation `D^σ` for derivatives in several variables, and the derivatives of exponential
  monomials computed in §4.4, Lemma 4.9.
-/

public section

open Function Finset

namespace TauCeti.Baker

variable {n : ℕ}

/-- The mixed partial derivative `D^σ f = ∂₀^{σ₀} (∂₁^{σ₁} ( ⋯ (∂_{n-1}^{σ_{n-1}} f)))` of a
function `f : ℂⁿ → ℂ` of multi-order `σ ∈ ℕⁿ`. It is not divided by `σ!`. -/
noncomputable def mDeriv (σ : Fin n → ℕ) (f : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  (List.finRange n).foldr (fun i g ↦ (partialDeriv i)^[σ i] g) f

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

private theorem listDeriv_single_one {l : List (Fin n)} (hl : l.Nodup) (i : Fin n)
    (f : (Fin n → ℂ) → ℂ) :
    listDeriv l (Pi.single i 1) f = if i ∈ l then partialDeriv i f else f := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    obtain ⟨hjl, hl⟩ := List.nodup_cons.mp hl
    rw [listDeriv_cons, ih hl]
    by_cases hij : i = j
    · subst hij
      simp [hjl]
    · simp [hij]

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

/-- The mixed partial derivative of multi-order `eᵢ` is `∂ᵢ`. -/
@[simp]
theorem mDeriv_single_one (f : (Fin n → ℂ) → ℂ) (i : Fin n) :
    mDeriv (Pi.single i 1) f = partialDeriv i f := by
  rw [mDeriv_eq_listDeriv, listDeriv_single_one (List.nodup_finRange n)]
  simp

/-- `D^σ` is additive on entire functions. -/
theorem mDeriv_add {f g : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (σ : Fin n → ℕ) : mDeriv σ (f + g) = mDeriv σ f + mDeriv σ g :=
  listDeriv_add hf hg _ σ

/-- `D^σ` commutes with multiplication by a constant. -/
@[simp]
theorem mDeriv_const_mul {f : (Fin n → ℂ) → ℂ} (c : ℂ) (σ : Fin n → ℕ) :
    mDeriv σ (fun z ↦ c * f z) = fun z ↦ c * mDeriv σ f z :=
  listDeriv_const_mul c _ σ

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

/-! ### Separated products and exponential monomials -/

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

/-- **Mixed partial derivatives of an exponential.** `D^σ (z ↦ e^{w · z}) = z ↦ w^σ e^{w · z}`,
where `w^σ = ∏ᵢ wᵢ^{σᵢ}`. -/
theorem mDeriv_exp_dotProduct (w : Fin n → ℂ) (σ : Fin n → ℕ) :
    mDeriv σ (fun z ↦ Complex.exp (w ⬝ᵥ z)) =
      fun z ↦ (∏ i, w i ^ σ i) * Complex.exp (w ⬝ᵥ z) := by
  have hexp (z : Fin n → ℂ) : Complex.exp (w ⬝ᵥ z) = ∏ i, Complex.exp (w i * z i) := by
    rw [dotProduct, Complex.exp_sum]
  simp_rw [hexp]
  rw [mDeriv_prod (g := fun i s ↦ Complex.exp (w i * s)) fun i ↦ by fun_prop]
  ext z
  simp [prod_mul_distrib]

/-- **The Leibniz expansion for exponential monomials.** For `τ, σ ∈ ℕⁿ` and `w ∈ ℂⁿ`,

  `D^σ (z ↦ z^τ e^{w · z}) = z ↦ (∏ᵢ ∑_{k ≤ σᵢ} (σᵢ choose k) τᵢ(τᵢ - 1)⋯(τᵢ - k + 1) zᵢ^{τᵢ - k}
    wᵢ^{σᵢ - k}) e^{w · z}`.

The terms with `k > τᵢ` vanish, since then the descending factorial `τᵢ(τᵢ - 1)⋯(τᵢ - k + 1)`
is zero. -/
theorem mDeriv_monomial_mul_exp (τ σ : Fin n → ℕ) (w : Fin n → ℂ) :
    mDeriv σ (fun z ↦ (∏ i, z i ^ τ i) * Complex.exp (w ⬝ᵥ z)) =
      fun z ↦ (∏ i, ∑ k ∈ range (σ i + 1),
        ((σ i).choose k * (τ i).descFactorial k : ℂ) * z i ^ (τ i - k) * w i ^ (σ i - k)) *
        Complex.exp (w ⬝ᵥ z) := by
  have hfun (z : Fin n → ℂ) : (∏ i, z i ^ τ i) * Complex.exp (w ⬝ᵥ z) =
      ∏ i, (z i ^ τ i * Complex.exp (w i * z i)) := by
    rw [dotProduct, Complex.exp_sum, prod_mul_distrib]
  simp_rw [hfun]
  rw [mDeriv_prod (g := fun i s ↦ s ^ τ i * Complex.exp (w i * s)) fun i ↦ by fun_prop]
  ext z
  rw [dotProduct, Complex.exp_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [iteratedDeriv_fun_mul (by fun_prop) (by fun_prop), sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [iteratedDeriv_pow, iteratedDeriv_cexp_const_mul]
  ring

end Product

end TauCeti.Baker
