/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.Analysis.Complex.DividedDifference.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Analysis.Complex.DividedDifference.Analytic

/-!
# Dividing an entire function by a polynomial in one variable

Let `ι` be finite, `E` be a complete complex normed space, `P ∈ ℂ[X]` be monic of degree `p`,
`f : (ι → ℂ) → E` be entire, and `i : ι`. Dividing `f` by `zᵢ - ζ` (`TauCeti.partialDslope`)
successively at the roots `ζ` of `P`, counted with multiplicity, writes

  `f z = f₀ z + P(zᵢ) • f₁ z`

with the quotient `f₁ = TauCeti.partialDivByMonic i f P` and the remainder
`f₀ = TauCeti.partialModByMonic i f P` entire, and `f₀` a polynomial of degree less than `p` in
`zᵢ`, in the sense that `∂ᵢ^p f₀ = 0` (see `TauCeti.Analysis.Complex.CoordinateDivision.Degree`
for the scalar `ℂ` line-polynomial characterizations). This is Euclidean division by a monic
polynomial (Mathlib's `Polynomial.divByMonic` and `Polynomial.modByMonic`) for entire functions of
the `i`-th variable, and as there the quotient and remainder are unique. Moreover:

* if the roots of `P` lie in the closed disc `closedBall (c i) r`, `0 < R`, `5 r ≤ R` and
  `‖f‖ ≤ M` on `closedBall c R`, then `‖f₀‖ ≤ 3 ^ p M` and `‖f₁‖ ≤ (3 / R) ^ p M` there (see
  `TauCeti.Analysis.Complex.CoordinateDivision.Estimate`);
* on entire functions, the partial derivatives `∂ⱼ` with `j ≠ i` commute with `f ↦ f₀` and
  `f ↦ f₁`, so `f₀` and `f₁` preserve coordinate polynomial degree bounds in `zⱼ` whenever `f`
  satisfies them (see `TauCeti.Analysis.Complex.CoordinateDivision.Degree`);
* `f₀ = 0`, that is `P(zᵢ)` divides `f`, if and only if `∂ᵢ^κ f` vanishes on the hyperplane
  `zᵢ = ζ` for every root `ζ` of `P` and every `κ` less than its multiplicity.

Applied in each coordinate in turn to the polynomials `∏_{ζ ∈ Eᵢ} (X - ζ) ^ S₀`, this division
proves Schwarz's lemma for Cartesian products `E₁ × ⋯ × Eₙ`, which bounds an entire function
for which all mixed partial derivatives with each coordinate order strictly below `S₀` vanish on
such a grid. That lemma is the extrapolation step of the transcendence method of Schneider, Lang and
Baker.

## Main definitions and results

* `TauCeti.partialDivByMonic i f P`, `TauCeti.partialModByMonic i f P`: the quotient and the
  remainder of `f` by `P(zᵢ)`.
* `TauCeti.partialDivByList i f l`, `TauCeti.partialModByList i f l`: the underlying list
  quotient and remainder along a list `l : List ℂ` of nodes, with Newton's recursion
  `TauCeti.partialModByList_cons` and monic identifications
  `TauCeti.partialDivByMonic_eq_partialDivByList` and
  `TauCeti.partialModByMonic_eq_partialModByList`.
* `TauCeti.partialModByMonic_add_smul_partialDivByMonic`: `f₀ z + P(zᵢ) • f₁ z = f z`.
* `TauCeti.iterate_partialDeriv_partialModByMonic_eq_zero`: `∂ᵢ^p f₀ = 0`.
* `TauCeti.eq_partialDivByMonic`, `TauCeti.eq_partialModByMonic`: uniqueness.
* `TauCeti.partialDivByMonic_add`, `TauCeti.partialModByMonic_add`: additivity on entire functions.
* `TauCeti.partialDivByMonic_const_smul`, `TauCeti.partialModByMonic_const_smul`: compatibility
  with constant scalar multiplication.
* `TauCeti.iterate_partialDeriv_partialDivByMonic_of_ne`,
  `TauCeti.iterate_partialDeriv_partialModByMonic_of_ne`: `∂ⱼ^m` commutes with both on entire
  functions for `j ≠ i`.
* `TauCeti.partialModByMonic_eq_zero_iff`: the divisibility criterion.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, §4.3, Lemma 4.8 and its proof (pp. 123–126).
-/

public section

open Function Metric Polynomial

namespace TauCeti

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The quotient of `f : (ι → ℂ) → E` by `P(zᵢ)`, for a monic `P ∈ ℂ[X]`: the iterated divided
difference of `f` in the `i`-th variable at the roots of `P`, counted with multiplicity. For entire
`f` it is the unique entire `f₁` with `f z = f₀ z + P(zᵢ) • f₁ z` for an entire `f₀` of degree
less than `natDegree P` in `zᵢ` (`TauCeti.eq_partialDivByMonic`). -/
noncomputable def partialDivByMonic (i : ι) (f : (ι → ℂ) → E) (P : ℂ[X]) : (ι → ℂ) → E :=
  P.roots.toList.foldl (fun g ζ ↦ partialDslope i g ζ) f

/-- Defining identity of `partialDivByMonic` as an iterated divided difference along the roots of
`P`. -/
theorem partialDivByMonic_def (i : ι) (f : (ι → ℂ) → E) (P : ℂ[X]) :
    partialDivByMonic i f P = P.roots.toList.foldl (fun g ζ ↦ partialDslope i g ζ) f := (rfl)

/-- The remainder of `f : (ι → ℂ) → E` modulo `P(zᵢ)`, for a monic `P ∈ ℂ[X]`:
`f z - P(zᵢ) • partialDivByMonic i f P z`. For entire `f` it is a polynomial of degree less than
`natDegree P` in `zᵢ` (`TauCeti.iterate_partialDeriv_partialModByMonic_eq_zero`). -/
noncomputable def partialModByMonic (i : ι) (f : (ι → ℂ) → E) (P : ℂ[X]) : (ι → ℂ) → E :=
  fun z ↦ f z - P.eval (z i) • partialDivByMonic i f P z

theorem partialModByMonic_apply (i : ι) (f : (ι → ℂ) → E) (P : ℂ[X]) (z : ι → ℂ) :
    partialModByMonic i f P z = f z - P.eval (z i) • partialDivByMonic i f P z := (rfl)

/-- **Division with remainder.** `f z = f₀ z + P(zᵢ) • f₁ z`. -/
theorem partialModByMonic_add_smul_partialDivByMonic (i : ι) (f : (ι → ℂ) → E) (P : ℂ[X])
    (z : ι → ℂ) : partialModByMonic i f P z + P.eval (z i) • partialDivByMonic i f P z = f z := by
  rw [partialModByMonic_apply, sub_add_cancel]

@[simp]
theorem partialDivByMonic_one (i : ι) (f : (ι → ℂ) → E) : partialDivByMonic i f 1 = f := by
  simp [partialDivByMonic]

@[simp]
theorem partialModByMonic_one (i : ι) (f : (ι → ℂ) → E) : partialModByMonic i f 1 = 0 := by
  ext z
  simp [partialModByMonic_apply]

@[simp]
theorem partialDivByMonic_zero_fun (i : ι) (P : ℂ[X]) :
    partialDivByMonic i (0 : (ι → ℂ) → E) P = 0 := by
  unfold partialDivByMonic
  induction P.roots.toList with
  | nil => rfl
  | cons ζ l ih => rw [List.foldl_cons, partialDslope_zero_fun, ih]

@[simp]
theorem partialModByMonic_zero_fun (i : ι) (P : ℂ[X]) :
    partialModByMonic i (0 : (ι → ℂ) → E) P = 0 := by
  ext z
  simp [partialModByMonic_apply]

/-- Dividing by the linear polynomial `X - ζ` is taking the divided difference at `ζ`. -/
@[simp]
theorem partialDivByMonic_X_sub_C (i : ι) (f : (ι → ℂ) → E) (ζ : ℂ) :
    partialDivByMonic i f (X - C ζ) = partialDslope i f ζ := by
  simp [partialDivByMonic, roots_X_sub_C]

/-- The remainder modulo `zᵢ - ζ` is `f` with its `i`-th variable replaced by `ζ`. -/
@[simp]
theorem partialModByMonic_X_sub_C (i : ι) (f : (ι → ℂ) → E) (ζ : ℂ) :
    partialModByMonic i f (X - C ζ) = fun z ↦ f (update z i ζ) := by
  ext z
  rw [partialModByMonic_apply, partialDivByMonic_X_sub_C, eval_sub, eval_X, eval_C,
    sub_smul_partialDslope, sub_sub_cancel]

/-! ### Division along a list of nodes -/

section List

/-- The iterated divided difference of `f` in the `i`-th variable along a list of nodes. -/
noncomputable def partialDivByList (i : ι) (f : (ι → ℂ) → E) (l : List ℂ) : (ι → ℂ) → E :=
  l.foldl (fun g ζ ↦ partialDslope i g ζ) f

/-- The remainder of `f` modulo the product of `zᵢ - ζ` over a list of nodes. -/
noncomputable def partialModByList (i : ι) (f : (ι → ℂ) → E) (l : List ℂ) : (ι → ℂ) → E :=
  fun z ↦ f z - ((l.map fun ζ ↦ X - C ζ).prod).eval (z i) • partialDivByList i f l z

/-- Dividing along the empty list of nodes leaves `f` unchanged. -/
theorem partialDivByList_nil (i : ι) (f : (ι → ℂ) → E) : partialDivByList i f [] = f := by
  simp [partialDivByList]

/-- Dividing along `ζ :: l` first takes the divided difference at `ζ`, then divides along `l`. -/
theorem partialDivByList_cons (i : ι) (f : (ι → ℂ) → E) (ζ : ℂ) (l : List ℂ) :
    partialDivByList i f (ζ :: l) = partialDivByList i (partialDslope i f ζ) l := by
  simp [partialDivByList]

/-- The remainder along the empty list of nodes is zero. -/
theorem partialModByList_nil (i : ι) (f : (ι → ℂ) → E) : partialModByList i f [] = 0 := by
  ext z
  simp [partialModByList, partialDivByList_nil]

/-- The quotient by `P(zᵢ)` is the iterated divided difference along the roots of `P`, listed with
multiplicity. -/
theorem partialDivByMonic_eq_partialDivByList (i : ι) (f : (ι → ℂ) → E) (P : ℂ[X]) :
    partialDivByMonic i f P = partialDivByList i f P.roots.toList := by
  rw [partialDivByMonic_def, partialDivByList]

variable {i : ι} {f : (ι → ℂ) → E}

/-- Newton's recursion for the remainder: dividing first by `zᵢ - ζ`,
`f₀ = f (update z i ζ) + (zᵢ - ζ) • (remainder of the divided difference)`. -/
theorem partialModByList_cons (ζ : ℂ) (l : List ℂ) :
    partialModByList i f (ζ :: l) = fun z ↦
      f (update z i ζ) + (z i - ζ) • partialModByList i (partialDslope i f ζ) l z := by
  ext z
  simp only [partialModByList, partialDivByList, List.map_cons, List.prod_cons, eval_mul, eval_sub,
    eval_X, eval_C, List.foldl_cons, mul_smul]
  rw [smul_sub, ← add_sub_assoc, add_sub_smul_partialDslope]

/-- Over the roots of a monic polynomial, listed with multiplicity, the product of `X - ζ` is the
polynomial. -/
private theorem prod_map_roots_toList {P : ℂ[X]} (hP : P.Monic) :
    (P.roots.toList.map fun ζ ↦ X - C ζ).prod = P := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
  exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP IsAlgClosed.card_roots_eq_natDegree

/-- For a monic polynomial `P`, the remainder `partialModByMonic i f P` equals the list remainder
along `P.roots.toList`. -/
theorem partialModByMonic_eq_partialModByList {P : ℂ[X]} (hP : P.Monic) :
    partialModByMonic i f P = partialModByList i f P.roots.toList := by
  ext z
  rw [partialModByMonic_apply, partialModByList, prod_map_roots_toList hP,
    partialDivByMonic_eq_partialDivByList]

/-- Division along `l` commutes with scalar multiplication by a constant. -/
private theorem listQuot_const_smul (c : ℂ) (l : List ℂ) :
    partialDivByList i (c • f) l = c • partialDivByList i f l := by
  induction l generalizing f with
  | nil => rw [partialDivByList_nil, partialDivByList_nil]
  | cons ζ l ih => rw [partialDivByList_cons, partialDslope_const_smul, ih, partialDivByList_cons]

section Entire

variable [Finite ι] [CompleteSpace E]

private theorem differentiable_listQuot (hf : Differentiable ℂ f) (l : List ℂ) :
    Differentiable ℂ (partialDivByList i f l) := by
  induction l generalizing f with
  | nil => rw [partialDivByList_nil]; exact hf
  | cons ζ _ ih => rw [partialDivByList_cons]; exact ih (differentiable_partialDslope hf i ζ)

private theorem differentiable_listRem (hf : Differentiable ℂ f) (l : List ℂ) :
    Differentiable ℂ (partialModByList i f l) := by
  have := Fintype.ofFinite ι
  have hq := differentiable_listQuot (i := i) hf l
  unfold partialModByList
  fun_prop

/-- The remainder along `l` has degree less than the length of `l` in `zᵢ`. -/
private theorem iterate_partialDeriv_listRem (hf : Differentiable ℂ f) (l : List ℂ) :
    (partialDeriv i)^[l.length] (partialModByList i f l) = 0 := by
  have := Fintype.ofFinite ι
  induction l generalizing f with
  | nil =>
    ext z
    simp [partialModByList_nil]
  | cons ζ l ih =>
    have hg := differentiable_partialDslope hf i ζ
    have hh := differentiable_listRem (i := i) hg l
    have hsplit : partialModByList i f (ζ :: l) = (fun z ↦ f (update z i ζ)) +
        fun z ↦ (z i - ζ) • partialModByList i (partialDslope i f ζ) l z := by
      rw [partialModByList_cons]
      -- The sum of two functions is their pointwise sum.
      rfl
    have hconst : (partialDeriv i)^[l.length + 1] (fun z ↦ f (update z i ζ)) = 0 := by
      rw [iterate_succ_apply, partialDeriv_comp_update_self hf]
      exact iterate_fixed (partialDeriv_zero_fun i) _
    have hzero : (partialDeriv i)^[l.length + 1] (partialModByList i (partialDslope i f ζ) l) =
        0 := by
      rw [iterate_succ_apply', ih hg, partialDeriv_zero_fun]
    rw [List.length_cons, hsplit,
      iterate_partialDeriv_add (differentiable_comp_update_const hf i ζ) (by fun_prop),
      hconst, iterate_partialDeriv_sub_smul_self hh, ih hg, hzero]
    ext z
    simp

/-- For `g` entire, `(zᵢ - ζ₀) • g` vanishes along `zᵢ = ζ` to the order counted by `ζ₀ :: l` if
and only if `g` vanishes there to the order counted by `l`. -/
private theorem vanish_sub_smul_iff {g : (ι → ℂ) → E} (hg : Differentiable ℂ g) (ζ₀ : ℂ)
    (l : List ℂ) :
    (∀ ζ, ∀ κ < (ζ₀ :: l).count ζ, ∀ z,
      (partialDeriv i)^[κ] (fun w ↦ (w i - ζ₀) • g w) (update z i ζ) = 0) ↔
    ∀ ζ, ∀ κ < l.count ζ, ∀ z, (partialDeriv i)^[κ] g (update z i ζ) = 0 := by
  constructor
  · intro h ζ κ hκ z
    by_cases hζ : ζ = ζ₀
    · subst hζ
      have := h ζ (κ + 1) (by rw [List.count_cons_self]; omega) z
      rw [iterate_partialDeriv_sub_smul_self hg] at this
      simpa [Nat.cast_add_one_ne_zero] using this
    · have hc : (ζ₀ :: l).count ζ = l.count ζ := List.count_cons_of_ne (Ne.symm hζ)
      have hne : ζ - ζ₀ ≠ 0 := sub_ne_zero.2 hζ
      induction κ with
      | zero => simpa [hne] using h ζ 0 (hc ▸ hκ) z
      | succ κ ihκ =>
        have := h ζ (κ + 1) (hc ▸ hκ) z
        rw [iterate_partialDeriv_sub_smul_self hg] at this
        simpa [ihκ (by omega), hne] using this
  · intro h ζ κ hκ z
    by_cases hζ : ζ = ζ₀
    · subst hζ
      rw [List.count_cons_self] at hκ
      cases κ with
      | zero => simp
      | succ κ =>
        rw [iterate_partialDeriv_sub_smul_self hg]
        simp [h ζ κ (by omega) z]
    · rw [List.count_cons_of_ne (Ne.symm hζ)] at hκ
      cases κ with
      | zero => simpa using Or.inr (h ζ 0 hκ z)
      | succ κ =>
        rw [iterate_partialDeriv_sub_smul_self hg]
        simp [h ζ κ (by omega) z, h ζ (κ + 1) hκ z]

/-- A multiple of the product of `zᵢ - ζ` over `l` vanishes along each `zᵢ = ζ` to the order
counted by `l`. -/
private theorem vanish_prod_smul {g : (ι → ℂ) → E} (hg : Differentiable ℂ g) (l : List ℂ) :
    ∀ ζ, ∀ κ < l.count ζ, ∀ z, (partialDeriv i)^[κ]
      (fun w ↦ ((l.map fun ζ ↦ X - C ζ).prod).eval (w i) • g w) (update z i ζ) = 0 := by
  have := Fintype.ofFinite ι
  induction l with
  | nil => simp
  | cons ζ₀ l ih =>
    have hG : Differentiable ℂ fun w ↦ ((l.map fun ζ ↦ X - C ζ).prod).eval (w i) • g w := by
      fun_prop
    simpa only [List.map_cons, List.prod_cons, eval_mul, eval_sub, eval_X, eval_C, mul_smul]
      using (vanish_sub_smul_iff hG ζ₀ l).2 ih

/-- The remainder along `l` vanishes exactly when `f` vanishes along each `zᵢ = ζ` to the order
counted by `l`. -/
private theorem listRem_eq_zero_iff (hf : Differentiable ℂ f) (l : List ℂ) :
    partialModByList i f l = 0 ↔
      ∀ ζ, ∀ κ < l.count ζ, ∀ z, (partialDeriv i)^[κ] f (update z i ζ) = 0 := by
  constructor
  · intro h
    have hfq : f = fun w ↦
        ((l.map fun ζ ↦ X - C ζ).prod).eval (w i) • partialDivByList i f l w := by
      ext w
      simpa [partialModByList, sub_eq_zero] using congrFun h w
    rw [hfq]
    exact vanish_prod_smul (differentiable_listQuot hf l) l
  · induction l generalizing f with
    | nil => intro _; ext z; simp [partialModByList_nil]
    | cons ζ₀ l ih =>
      intro h
      have hζ₀ (z : ι → ℂ) : f (update z i ζ₀) = 0 := by
        simpa using h ζ₀ 0 (by simp) z
      have hg := differentiable_partialDslope hf i ζ₀
      have hfg : f = fun w ↦ (w i - ζ₀) • partialDslope i f ζ₀ w := by
        ext w
        rw [← add_sub_smul_partialDslope i f ζ₀ w, hζ₀, zero_add]
      rw [hfg] at h
      rw [partialModByList_cons, ih hg ((vanish_sub_smul_iff hg ζ₀ l).1 h)]
      ext z
      simp [hζ₀]

/-- Uniqueness of division along `l`. -/
private theorem eq_listQuot {f₀ g : (ι → ℂ) → E} (hf₀ : Differentiable ℂ f₀)
    (hg : Continuous g) (l : List ℂ) (hdeg : (partialDeriv i)^[l.length] f₀ = 0)
    (h : ∀ z, f z = f₀ z + ((l.map fun ζ ↦ X - C ζ).prod).eval (z i) • g z) :
    g = partialDivByList i f l := by
  have := Fintype.ofFinite ι
  induction l generalizing f f₀ with
  | nil =>
    ext z
    simp only [List.length_nil, iterate_zero, id_eq] at hdeg
    simp [partialDivByList_nil, h z, hdeg]
  | cons ζ l ih =>
    set G : (ι → ℂ) → E := fun z ↦ ((l.map fun ζ ↦ X - C ζ).prod).eval (z i) • g z with hGdef
    have hG : Continuous G := by
      have hprod : Continuous fun z : ι → ℂ ↦ ((l.map fun ζ ↦ X - C ζ).prod).eval (z i) :=
        ((l.map fun ζ ↦ X - C ζ).prod).continuous.comp (continuous_apply i)
      exact hprod.smul hg
    have hf : f = fun z ↦ f₀ z + (z i - ζ) • G z := by
      ext z
      simp [h z, hGdef, mul_smul]
    have hdiv : partialDslope i f ζ = fun z ↦ partialDslope i f₀ ζ z + G z := by
      refine (eq_partialDslope_of_sub_smul_eq
        ((differentiable_partialDslope hf₀ i ζ).continuous.add hG) fun z ↦ ?_).symm
      rw [hf]
      simp only [update_self, sub_self, zero_smul, add_zero, Pi.add_apply, smul_add,
        sub_smul_partialDslope]
      abel
    exact ih (f := partialDslope i f ζ) (differentiable_partialDslope hf₀ i ζ)
      (iterate_partialDeriv_partialDslope_eq_zero hf₀ hdeg ζ) fun z ↦ by rw [hdiv]

/-- `∂ⱼ^m` commutes with division along `l` in the variable `zᵢ`, for `j ≠ i`. -/
private theorem iterate_partialDeriv_listQuot_of_ne (hf : Differentiable ℂ f) {j : ι}
    (hji : j ≠ i) (l : List ℂ) (m : ℕ) :
    (partialDeriv j)^[m] (partialDivByList i f l) =
      partialDivByList i ((partialDeriv j)^[m] f) l := by
  induction l generalizing f with
  | nil => rw [partialDivByList_nil, partialDivByList_nil]
  | cons ζ l ih =>
    rw [partialDivByList_cons, partialDivByList_cons, ih (differentiable_partialDslope hf i ζ),
      iterate_partialDeriv_partialDslope_of_ne hf hji ζ m]

/-- Division along `l` is additive on entire functions. -/
private theorem listQuot_add {g : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (l : List ℂ) :
    partialDivByList i (f + g) l = partialDivByList i f l + partialDivByList i g l := by
  induction l generalizing f g with
  | nil => rw [partialDivByList_nil, partialDivByList_nil, partialDivByList_nil]
  | cons ζ l ih =>
    rw [partialDivByList_cons, partialDivByList_cons, partialDivByList_cons,
      partialDslope_add hf hg i ζ,
      ih (differentiable_partialDslope hf i ζ) (differentiable_partialDslope hg i ζ)]

end Entire

end List

/-! ### The quotient and the remainder -/

/-- The quotient by `P(zᵢ)` commutes with scalar multiplication by a constant. -/
theorem partialDivByMonic_const_smul (c : ℂ) (i : ι) (f : (ι → ℂ) → E) (P : ℂ[X]) :
    partialDivByMonic i (c • f) P = c • partialDivByMonic i f P := by
  simp only [partialDivByMonic_eq_partialDivByList]
  exact listQuot_const_smul c _

/-- The remainder modulo `P(zᵢ)` commutes with scalar multiplication by a constant. -/
theorem partialModByMonic_const_smul (c : ℂ) (i : ι) (f : (ι → ℂ) → E) (P : ℂ[X]) :
    partialModByMonic i (c • f) P = c • partialModByMonic i f P := by
  ext z
  simp only [partialModByMonic_apply, partialDivByMonic_const_smul, Pi.smul_apply, smul_sub]
  rw [smul_comm c (P.eval (z i))]

section Entire

variable [Finite ι] [CompleteSpace E] {i : ι} {f : (ι → ℂ) → E} {P : ℂ[X]}

/-- The quotient of an entire function by `P(zᵢ)` is entire. -/
theorem differentiable_partialDivByMonic (hf : Differentiable ℂ f) (i : ι) (P : ℂ[X]) :
    Differentiable ℂ (partialDivByMonic i f P) := by
  rw [partialDivByMonic_eq_partialDivByList]
  exact differentiable_listQuot hf _

/-- The remainder of an entire function modulo `P(zᵢ)` is entire. -/
theorem differentiable_partialModByMonic (hf : Differentiable ℂ f) (i : ι) (P : ℂ[X]) :
    Differentiable ℂ (partialModByMonic i f P) := by
  have := Fintype.ofFinite ι
  have hq := differentiable_partialDivByMonic hf i P
  unfold partialModByMonic
  fun_prop

/-- **The remainder has degree less than `natDegree P` in `zᵢ`:** for monic `P` of degree
`p = P.natDegree` and entire `f`, `∂ᵢ^p (partialModByMonic i f P) = 0`. -/
theorem iterate_partialDeriv_partialModByMonic_eq_zero (hP : P.Monic) (hf : Differentiable ℂ f) :
    (partialDeriv i)^[P.natDegree] (partialModByMonic i f P) = 0 := by
  rw [partialModByMonic_eq_partialModByList hP, ← IsAlgClosed.card_roots_eq_natDegree,
    ← Multiset.length_toList]
  exact iterate_partialDeriv_listRem hf _

/-- **Uniqueness of the quotient.** For monic `P` of degree `p = P.natDegree`, if
`f z = f₀ z + P(zᵢ) • g z` with `f₀` entire, `g` continuous, and `∂ᵢ^p f₀ = 0`, then `g` is the
quotient of `f` by `P(zᵢ)`. -/
theorem eq_partialDivByMonic {f₀ g : (ι → ℂ) → E} (hP : P.Monic) (hf₀ : Differentiable ℂ f₀)
    (hg : Continuous g) (hdeg : (partialDeriv i)^[P.natDegree] f₀ = 0)
    (h : ∀ z, f z = f₀ z + P.eval (z i) • g z) : g = partialDivByMonic i f P := by
  rw [partialDivByMonic_eq_partialDivByList]
  refine eq_listQuot hf₀ hg P.roots.toList ?_ ?_
  · rwa [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree]
  · rwa [prod_map_roots_toList hP]

/-- **Uniqueness of the remainder.** For monic `P` of degree `p = P.natDegree`, if
`f z = f₀ z + P(zᵢ) • g z` with `f₀` entire, `g` continuous, and `∂ᵢ^p f₀ = 0`, then `f₀` is the
remainder of `f` modulo `P(zᵢ)`. -/
theorem eq_partialModByMonic {f₀ g : (ι → ℂ) → E} (hP : P.Monic) (hf₀ : Differentiable ℂ f₀)
    (hg : Continuous g) (hdeg : (partialDeriv i)^[P.natDegree] f₀ = 0)
    (h : ∀ z, f z = f₀ z + P.eval (z i) • g z) : f₀ = partialModByMonic i f P := by
  ext z
  rw [partialModByMonic_apply, ← eq_partialDivByMonic hP hf₀ hg hdeg h, h z, add_sub_cancel_right]

/-- The quotient by `P(zᵢ)` is additive on entire functions. -/
theorem partialDivByMonic_add {g : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (i : ι) (P : ℂ[X]) :
    partialDivByMonic i (f + g) P = partialDivByMonic i f P + partialDivByMonic i g P := by
  simp only [partialDivByMonic_eq_partialDivByList]
  exact listQuot_add hf hg _

/-- The remainder modulo `P(zᵢ)` is additive on entire functions. -/
theorem partialModByMonic_add {g : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (i : ι) (P : ℂ[X]) :
    partialModByMonic i (f + g) P = partialModByMonic i f P + partialModByMonic i g P := by
  ext z
  simp only [partialModByMonic_apply, partialDivByMonic_add hf hg, Pi.add_apply, smul_add]
  abel

/-- On entire functions, the iterated partial derivatives `∂ⱼ^m` in another variable `j ≠ i` commute
with the quotient by `P(zᵢ)`. In particular, if `f` is a polynomial of degree at most `e` in `zⱼ`,
in the sense that `∂ⱼ^(e+1) f = 0`, then so is the quotient. -/
theorem iterate_partialDeriv_partialDivByMonic_of_ne (hf : Differentiable ℂ f) {j : ι}
    (hji : j ≠ i) (P : ℂ[X]) (m : ℕ) :
    (partialDeriv j)^[m] (partialDivByMonic i f P) =
      partialDivByMonic i ((partialDeriv j)^[m] f) P := by
  simp only [partialDivByMonic_eq_partialDivByList]
  exact iterate_partialDeriv_listQuot_of_ne hf hji _ m

/-- On entire functions, the iterated partial derivatives `∂ⱼ^m` in another variable `j ≠ i` commute
with the remainder modulo `P(zᵢ)`. In particular, if `f` is a polynomial of degree at most `e` in
`zⱼ`, in the sense that `∂ⱼ^(e+1) f = 0`, then so is the remainder. -/
theorem iterate_partialDeriv_partialModByMonic_of_ne (hf : Differentiable ℂ f) {j : ι}
    (hji : j ≠ i) (P : ℂ[X]) (m : ℕ) :
    (partialDeriv j)^[m] (partialModByMonic i f P) =
      partialModByMonic i ((partialDeriv j)^[m] f) P := by
  have := Fintype.ofFinite ι
  have hq := differentiable_partialDivByMonic hf i P
  have hsplit : partialModByMonic i f P =
      f + fun z ↦ (fun s ↦ -P.eval s) (z i) • partialDivByMonic i f P z := by
    ext z
    simp [partialModByMonic_apply, sub_eq_add_neg]
  rw [hsplit, iterate_partialDeriv_add hf (by fun_prop),
    iterate_partialDeriv_fun_smul_of_ne (c := fun s ↦ -P.eval s) (by fun_prop) hq hji,
    iterate_partialDeriv_partialDivByMonic_of_ne hf hji]
  ext z
  simp [partialModByMonic_apply, sub_eq_add_neg]

/-- **Divisibility criterion.** For monic `P`, `P(zᵢ)` divides the entire function `f`, that is
the remainder vanishes, if and only if `∂ᵢ^κ f` vanishes on the hyperplane `zᵢ = ζ` for every
`ζ` and every `κ` less than the multiplicity of `ζ` as a root of `P`. -/
theorem partialModByMonic_eq_zero_iff (hP : P.Monic) (hf : Differentiable ℂ f) :
    partialModByMonic i f P = 0 ↔
      ∀ ζ, ∀ κ < rootMultiplicity ζ P, ∀ z, (partialDeriv i)^[κ] f (update z i ζ) = 0 := by
  simp_rw [partialModByMonic_eq_partialModByList hP, listRem_eq_zero_iff hf, ← count_roots,
    ← Multiset.coe_count, Multiset.coe_toList]

end Entire

end TauCeti
