/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Mixed partial derivatives of entire functions on `ℂⁿ`

The transcendence method of Schneider, Lang and Baker in several variables differentiates entire
functions `f : ℂⁿ → ℂ` along the coordinate directions. This file defines the partial derivative
`∂ᵢ f (z) = Df(z) eᵢ` (`TauCeti.Baker.partialDeriv`) and, for a multi-index `σ ∈ ℕⁿ`, the mixed
partial derivative

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

* `TauCeti.Baker.partialDeriv_comm`: partial derivatives of an entire function commute.
* `TauCeti.Baker.mDeriv_zero`, `TauCeti.Baker.mDeriv_add_single`: `D⁰ f = f` and
  `D^{σ + eᵢ} f = ∂ᵢ (D^σ f)` for entire `f`; these two characterize `D^σ` on entire functions.
* `TauCeti.Baker.differentiable_mDeriv`, `TauCeti.Baker.mDeriv_add`,
  `TauCeti.Baker.mDeriv_const_mul`, `TauCeti.Baker.mDeriv_sum`: `D^σ` preserves entire functions
  and is linear on them.
* `TauCeti.Baker.mDeriv_prod_apply`: `D^σ (z ↦ ∏ᵢ gᵢ(zᵢ)) = z ↦ ∏ᵢ gᵢ^{(σᵢ)}(zᵢ)`.
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

/-- The partial derivative `∂ᵢ f (z) = Df(z) eᵢ` of a function `f : ℂⁿ → ℂ` in the direction of
the `i`-th coordinate vector. -/
noncomputable def partialDeriv (i : Fin n) (f : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  fun z ↦ fderiv ℂ f z (Pi.single i 1)

theorem partialDeriv_def (i : Fin n) (f : (Fin n → ℂ) → ℂ) :
    partialDeriv i f = fun z ↦ fderiv ℂ f z (Pi.single i 1) := (rfl)

theorem partialDeriv_apply (i : Fin n) (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    partialDeriv i f z = fderiv ℂ f z (Pi.single i 1) := (rfl)

/-- The partial derivative `∂ᵢ f (z)` is the derivative of `f` restricted to the line through `z`
parallel to the `i`-th coordinate axis. -/
theorem partialDeriv_eq_deriv_update {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℂ f z) (i : Fin n) :
    partialDeriv i f z = deriv (fun s ↦ f (update z i s)) (z i) := by
  have hf' : HasFDerivAt f (fderiv ℂ f z) (update z i (z i)) := by
    rw [update_eq_self]
    exact hf.hasFDerivAt
  have hline := (hf'.comp (z i) (hasFDerivAt_update z (i := i) (z i))).hasDerivAt
  refine (hline.deriv.trans ?_).symm
  simp only [partialDeriv_apply, ContinuousLinearMap.comp_apply]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- A partial derivative of an entire function is entire. -/
theorem differentiable_partialDeriv {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (i : Fin n) : Differentiable ℂ (partialDeriv i f) := by
  have hf2 : ContDiff ℂ 2 f :=
    contDiffOn_univ.mp (hf.differentiableOn.contDiffOn_of_finiteDimensional isOpen_univ)
  have h : ContDiff ℂ 1 (fderiv ℂ f) := hf2.fderiv_right (by norm_num)
  exact (h.differentiable one_ne_zero).clm_apply (differentiable_const _)

/-- **Partial derivatives of an entire function commute.** -/
theorem partialDeriv_comm {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) (i j : Fin n) :
    partialDeriv i (partialDeriv j f) = partialDeriv j (partialDeriv i f) := by
  have hf2 : ContDiff ℂ 2 f :=
    contDiffOn_univ.mp (hf.differentiableOn.contDiffOn_of_finiteDimensional isOpen_univ)
  have hdf : Differentiable ℂ (fderiv ℂ f) :=
    (hf2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have key (k l : Fin n) (z : Fin n → ℂ) : partialDeriv k (partialDeriv l f) z =
      fderiv ℂ (fderiv ℂ f) z (Pi.single k 1) (Pi.single l 1) := by
    rw [partialDeriv_apply, partialDeriv_def l f,
      fderiv_clm_apply (hdf z) (differentiableAt_const _)]
    simp
  ext z
  rw [key, key]
  exact hf2.contDiffAt.isSymmSndFDerivAt (by simp) _ _

/-- `∂ᵢ` is additive on entire functions. -/
theorem partialDeriv_add {f g : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (i : Fin n) :
    partialDeriv i (f + g) = partialDeriv i f + partialDeriv i g := by
  ext z
  simp [partialDeriv_apply, fderiv_add (hf z) (hg z)]

/-- `∂ᵢ` commutes with multiplication by a constant on entire functions. -/
theorem partialDeriv_const_mul {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) (c : ℂ)
    (i : Fin n) : partialDeriv i (fun z ↦ c * f z) = fun z ↦ c * partialDeriv i f z := by
  ext z
  simp [partialDeriv_apply, fderiv_const_mul (hf z)]

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

private theorem differentiable_iterate_partialDeriv (hf : Differentiable ℂ f) (i : Fin n)
    (k : ℕ) : Differentiable ℂ ((partialDeriv i)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [iterate_succ_apply']; exact differentiable_partialDeriv ih i

private theorem differentiable_listDeriv (hf : Differentiable ℂ f) (l : List (Fin n))
    (σ : Fin n → ℕ) : Differentiable ℂ (listDeriv l σ f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact differentiable_iterate_partialDeriv ih i _

private theorem iterate_partialDeriv_comm (hf : Differentiable ℂ f) (i j : Fin n) (k : ℕ) :
    (partialDeriv i)^[k] (partialDeriv j f) = partialDeriv j ((partialDeriv i)^[k] f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih,
      partialDeriv_comm (differentiable_iterate_partialDeriv hf i k)]

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
  have hiter (i : Fin n) (k : ℕ) {f g : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f)
      (hg : Differentiable ℂ g) :
      (partialDeriv i)^[k] (f + g) = (partialDeriv i)^[k] f + (partialDeriv i)^[k] g := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply', ih,
        partialDeriv_add (differentiable_iterate_partialDeriv hf i k)
          (differentiable_iterate_partialDeriv hg i k)]
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [listDeriv_cons, listDeriv_cons, listDeriv_cons, ih,
      hiter i _ (differentiable_listDeriv hf l σ) (differentiable_listDeriv hg l σ)]

private theorem listDeriv_const_mul (hf : Differentiable ℂ f) (c : ℂ) (l : List (Fin n))
    (σ : Fin n → ℕ) : listDeriv l σ (fun z ↦ c * f z) = fun z ↦ c * listDeriv l σ f z := by
  have hiter (i : Fin n) (k : ℕ) {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) :
      (partialDeriv i)^[k] (fun z ↦ c * f z) = fun z ↦ c * (partialDeriv i)^[k] f z := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iterate_succ_apply', iterate_succ_apply', ih,
        partialDeriv_const_mul (differentiable_iterate_partialDeriv hf i k)]
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [listDeriv_cons, listDeriv_cons, ih, hiter i _ (differentiable_listDeriv hf l σ)]

end List

/-! ### Basic properties of `mDeriv` -/

@[simp]
theorem mDeriv_zero (f : (Fin n → ℂ) → ℂ) : mDeriv 0 f = f := by
  rw [mDeriv_eq_listDeriv]
  induction List.finRange n with
  | nil => rfl
  | cons i l ih => rw [listDeriv_cons, ih, Pi.zero_apply, iterate_zero_apply]

/-- A mixed partial derivative of an entire function is entire. -/
theorem differentiable_mDeriv {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) (σ : Fin n → ℕ) :
    Differentiable ℂ (mDeriv σ f) :=
  differentiable_listDeriv hf _ σ

/-- Raising the `i`-th order of a mixed partial derivative of an entire function by one applies
`∂ᵢ`: `D^{σ + eᵢ} f = ∂ᵢ (D^σ f)`. -/
theorem mDeriv_add_single {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) (σ : Fin n → ℕ)
    (i : Fin n) : mDeriv (σ + Pi.single i 1) f = partialDeriv i (mDeriv σ f) :=
  listDeriv_add_single hf (List.nodup_finRange n) (List.mem_finRange i) σ

/-- The mixed partial derivative of multi-order `eᵢ` of an entire function is `∂ᵢ`. -/
theorem mDeriv_single_one {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) (i : Fin n) :
    mDeriv (Pi.single i 1) f = partialDeriv i f := by
  simpa using mDeriv_add_single hf 0 i

/-- `D^σ` is additive on entire functions. -/
theorem mDeriv_add {f g : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (σ : Fin n → ℕ) : mDeriv σ (f + g) = mDeriv σ f + mDeriv σ g :=
  listDeriv_add hf hg _ σ

/-- `D^σ` commutes with multiplication by a constant on entire functions. -/
theorem mDeriv_const_mul {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) (c : ℂ)
    (σ : Fin n → ℕ) : mDeriv σ (fun z ↦ c * f z) = fun z ↦ c * mDeriv σ f z :=
  listDeriv_const_mul hf c _ σ

/-- `D^σ` commutes with finite sums of entire functions. -/
theorem mDeriv_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin n → ℂ) → ℂ}
    (hf : ∀ a ∈ s, Differentiable ℂ (f a)) (σ : Fin n → ℕ) :
    mDeriv σ (∑ a ∈ s, f a) = ∑ a ∈ s, mDeriv σ (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa [Pi.zero_def] using mDeriv_const_mul (f := 0) (differentiable_const 0) 0 σ
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, mDeriv_add (hf a (mem_insert_self a s))
      (Differentiable.sum fun b hb ↦ hf b (mem_insert_of_mem hb)),
      ih fun b hb ↦ hf b (mem_insert_of_mem hb)]

/-! ### Separated products and exponential monomials -/

section Product

variable {g : Fin n → ℂ → ℂ}

private theorem partialDeriv_prod_apply (hg : ∀ i, Differentiable ℂ (g i)) (j : Fin n) :
    partialDeriv j (fun z ↦ ∏ i, g i (z i)) = fun z ↦ ∏ i, update g j (deriv (g j)) i (z i) := by
  ext z
  have hd : DifferentiableAt ℂ (fun z : Fin n → ℂ ↦ ∏ i, g i (z i)) z :=
    (HasFDerivAt.finsetProd fun i _ ↦
      ((hg i) (z i)).hasFDerivAt.comp z (hasFDerivAt_apply i z)).differentiableAt
  rw [partialDeriv_eq_deriv_update hd]
  have hsplit (h : ℂ → ℂ) (s : ℂ) : ∏ i, update g j h i (update z j s i) =
      h s * ∏ i ∈ univ \ {j}, g i (z i) := by
    rw [← prod_update_of_mem (mem_univ j) (fun i ↦ g i (z i)) (h s)]
    refine prod_congr rfl fun i _ ↦ ?_
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hfun : (fun s ↦ ∏ i, g i (update z j s i)) = fun s ↦ g j s * ∏ i ∈ univ \ {j}, g i (z i) :=
    funext fun s ↦ by simpa using hsplit (g j) s
  have hR := hsplit (deriv (g j)) (z j)
  rw [update_eq_self] at hR
  rw [hfun, hR, deriv_mul_const ((hg j) _)]

private theorem iterate_partialDeriv_prod_apply (hg : ∀ i, Differentiable ℂ (g i)) (j : Fin n)
    (k : ℕ) : (partialDeriv j)^[k] (fun z ↦ ∏ i, g i (z i)) =
      fun z ↦ ∏ i, update g j (iteratedDeriv k (g j)) i (z i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hgk : ∀ i, Differentiable ℂ (update g j (iteratedDeriv k (g j)) i) := by
      intro i
      by_cases hij : i = j
      · subst hij
        simpa using ((hg i).contDiff (n := ⊤)).differentiable_iteratedDeriv k (by simp)
      · simpa [hij] using hg i
    rw [iterate_succ_apply', ih, partialDeriv_prod_apply hgk, update_idem, update_self,
      iteratedDeriv_succ]

/-- **Mixed partial derivatives of a separated product.** If `g₀, …, g_{n-1}` are entire
functions of one variable, then `D^σ (z ↦ ∏ᵢ gᵢ(zᵢ)) = z ↦ ∏ᵢ gᵢ^{(σᵢ)}(zᵢ)`. -/
theorem mDeriv_prod_apply (hg : ∀ i, Differentiable ℂ (g i)) (σ : Fin n → ℕ) :
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
        · exact ((hg i).contDiff (n := ⊤)).differentiable_iteratedDeriv _ (by simp)
        · exact hg i
      rw [listDeriv_cons, ih hl g hg, iterate_partialDeriv_prod_apply hgl]
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
  rw [mDeriv_prod_apply (g := fun i s ↦ Complex.exp (w i * s)) fun i ↦ by fun_prop]
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
  rw [mDeriv_prod_apply (g := fun i s ↦ s ^ τ i * Complex.exp (w i * s)) fun i ↦ by fun_prop]
  ext z
  rw [dotProduct, Complex.exp_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [iteratedDeriv_fun_mul (by fun_prop) (by fun_prop), sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [iteratedDeriv_pow, iteratedDeriv_cexp_const_mul]
  ring

end Product

end TauCeti.Baker
