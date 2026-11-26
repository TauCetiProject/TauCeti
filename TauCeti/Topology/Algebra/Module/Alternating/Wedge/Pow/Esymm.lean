/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow.Basic
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.Logic.Equiv.Fin.Basic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary

/-!
# Mixed wedge powers of two-forms on diagonal pairs

Let `α` and `ω` be real two-forms on a real vector space, and let `qᵢ = b (i, 0)` and
`pᵢ = b (i, 1)`, for `i < k + l`, be vectors on which both forms are diagonal:
`α(qᵢ, qⱼ) = ω(qᵢ, qⱼ) = 0`, `α(qᵢ, pⱼ) = cᵢ δᵢⱼ` and `ω(qᵢ, pⱼ) = δᵢⱼ`. Then

`(α ^ k ∧ ω ^ l)(q₀, p₀, q₁, p₁, …) = k! l! σ_k(c)`

where `σ_k` is the `k`-th elementary symmetric function
(`ContinuousAlternatingMap.pairedWedge_wedgePow_wedgePow_apply_finProdFinEquiv`). For `l = 0` it
is the value `k! ∏ᵢ cᵢ` of the top power
(`ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv_eq_mul_prod`). It is the pointwise
content of the form identity `α ^ k ∧ ω ^ (n - k) = (k! (n - k)! / n!) σ_k(λ[α]) ω ^ n` for a
(1,1)-form `α` on a Hermitian vector space.

The proof is by induction on the number of pairs, splitting off the first pair
(`TauCeti.comp_finProdFinEquiv_symm_succ`) and expanding along `q₀` with the interior-product rule
for the wedge (`ContinuousAlternatingMap.curryLeftTopological_pairedWedge`). For `k = 0` or `l = 0`
it is the value of a top power. Otherwise the vector `q₀` goes either into `α ^ k` or into `ω ^ l`.
In each case the power rule `ι_v φ ^ (k + 1) = (k + 1) ι_v φ ∧ φ ^ k` leaves the one-form
`α(q₀, ·)` or `ω(q₀, ·)`, which kills the later pairs and takes the value `c₀` or `1` on `p₀`
(`ContinuousAlternatingMap.pairedWedge_curryLeftTopological_wedgePow_succ_apply`). This gives the
recursion `σ_{k+1}(c₀, c') = σ_{k+1}(c') + c₀ σ_k(c')` of the elementary symmetric functions
(`Multiset.esymm_cons`).

## Main results

* `ContinuousAlternatingMap.pairedWedge_wedgePow_wedgePow_apply_finProdFinEquiv`: the value
  `k! l! σ_k(c)` of `α ^ k ∧ ω ^ l` on diagonal pairs.
-/

public section

open TauCeti

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- **The expansion along the first vector.** If `α(q, ·)` and `ω(q, ·)` kill the vectors of
`T`, then `(α ^ (k + 1) ∧ ω ^ (l + 1))(q, p, T)` is `(k + 1) α(q, p) (α ^ k ∧ ω ^ (l + 1))(T)` plus
`(l + 1) ω(q, p) (α ^ (k + 1) ∧ ω ^ l)(T)`. -/
private theorem pairedWedge_wedgePow_succ_wedgePow_succ_apply_vecCons
    (α ω : E [⋀^Fin 2]→L[ℝ] ℝ) (k l : ℕ) {n : ℕ} (q p : E) (T : Fin n → E)
    (h : 2 * (k + 1) + 2 * (l + 1) = n + 2) (hα : ∀ i, α ![q, T i] = 0)
    (hω : ∀ i, ω ![q, T i] = 0) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (wedgePow α (k + 1)) (wedgePow ω (l + 1))
        (Matrix.vecCons q (Matrix.vecCons p T) ∘ Fin.cast h) =
      (k + 1) * (α ![q, p] *
        pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          (wedgePow α k) (wedgePow ω (l + 1)) (T ∘ Fin.cast (by omega))) +
      (l + 1) * (ω ![q, p] *
        pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          (wedgePow α (k + 1)) (wedgePow ω l) (T ∘ Fin.cast (by omega))) := by
  have hcons : Matrix.vecCons q (Matrix.vecCons p T) ∘ Fin.cast h = Matrix.vecCons q
      (Matrix.vecCons p T ∘ Fin.cast (by omega : 2 * k + 1 + 1 + (2 * l + 1) = n + 1)) := by
    ext r
    refine Fin.cases ?_ (fun r ↦ ?_) r <;> simp
  rw [hcons, ← curryLeftTopological_apply_apply (n := 2 * k + 1 + 1 + (2 * l + 1)),
    curryLeftTopological_pairedWedge (k := 2 * k + 1) (l := 2 * l + 1),
    Even.neg_one_pow ⟨k + 1, by ring⟩, one_smul,
    pairedWedge_comm_of_even _ (fun a b ↦ mul_comm a b) ((even_two_mul _).mul_right _),
    Fin.comp_cast_comp_cast, Fin.comp_cast_comp_cast]
  -- The vector `q` in `α ^ (k + 1)`.
  have h₁ := pairedWedge_curryLeftTopological_wedgePow_succ_apply α k (wedgePow ω (l + 1)) q p T
    (by omega) hα
  -- The vector `q` in `ω ^ (l + 1)`, after moving `ι_q ω ^ (l + 1)` to the front and back.
  have h₂ := pairedWedge_curryLeftTopological_wedgePow_succ_apply ω l (wedgePow α (k + 1)) q p T
    (by omega) hω
  rw [pairedWedge_comm_of_even _ (fun a b ↦ mul_comm a b) ((even_two_mul _).mul_right _),
    Fin.comp_cast_comp_cast] at h₂
  -- `h₁` and `h₂` are the two summands, up to the definitional equalities
  -- `2 * (k + 1) = 2 * k + 1 + 1` and `2 * (l + 1) = 2 * l + 1 + 1` of the degrees.
  exact congrArg₂ (· + ·) h₁ h₂

/-- The value of `α ^ k ∧ ω ^ l` on diagonal pairs, with the pair listing read along any
`Fin.cast` and the elementary symmetric function of the multiset of the values `cᵢ`. -/
private theorem pairedWedge_wedgePow_wedgePow_apply_esymm (α ω : E [⋀^Fin 2]→L[ℝ] ℝ) {m : ℕ}
    (b : Fin m × Fin 2 → E) (c : Fin m → ℝ) (hα₀₀ : ∀ i j, α ![b (i, 0), b (j, 0)] = 0)
    (hα₀₁ : ∀ i j, α ![b (i, 0), b (j, 1)] = if i = j then c i else 0)
    (hω₀₀ : ∀ i j, ω ![b (i, 0), b (j, 0)] = 0)
    (hω₀₁ : ∀ i j, ω ![b (i, 0), b (j, 1)] = if i = j then 1 else 0) {k l : ℕ}
    (hkl : 2 * k + 2 * l = 2 * m) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (wedgePow α k) (wedgePow ω l)
        ((fun r : Fin (2 * m) ↦ b (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 m) r))) ∘
          Fin.cast hkl) =
      k.factorial * l.factorial * (Finset.univ.val.map c).esymm k := by
  induction m generalizing k l with
  | zero =>
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ l = 0 := by omega
    rw [pairedWedge_apply_zero_left, wedgePow_zero_apply, wedgePow_zero_apply]
    simp
  | succ m ih =>
    rcases k with _ | k
    · -- `k = 0`: the top power of `ω`.
      obtain rfl : l = m + 1 := by omega
      rw [pairedWedge_apply_zero_left, wedgePow_zero_apply, Fin.comp_cast_comp_cast, Fin.cast_refl,
        Function.comp_id, wedgePow_apply_finProdFinEquiv ω b hω₀₀ hω₀₁]
      simp
    rcases l with _ | l
    · -- `l = 0`: the top power of `α`.
      obtain rfl : k = m := by omega
      rw [pairedWedge_comm_of_even _ (fun a b ↦ mul_comm a b) ((even_two_mul _).mul_right _),
        pairedWedge_apply_zero_left, wedgePow_zero_apply, Fin.comp_cast_comp_cast,
        Fin.comp_cast_comp_cast, Fin.cast_refl, Function.comp_id,
        wedgePow_apply_finProdFinEquiv_eq_mul_prod α b c hα₀₀ hα₀₁]
      simp [← Multiset.esymm_card_eq_prod, Finset.prod_eq_multiset_prod]
    -- Both powers are positive: expand along the first vector `q₀ = b (0, 0)`, which `α` and `ω`
    -- pair with the later vectors to zero, then use the induction hypothesis on the later pairs.
    have ih' := @ih (b ∘ Prod.map Fin.succ id) (c ∘ Fin.succ) (fun i j ↦ hα₀₀ _ _)
      (fun i j ↦ by simpa using hα₀₁ i.succ j.succ) (fun i j ↦ hω₀₀ _ _)
      (fun i j ↦ by simpa using hω₀₁ i.succ j.succ)
    have hc : Finset.univ.val.map c = c 0 ::ₘ Finset.univ.val.map (c ∘ Fin.succ) := by
      simp [List.ofFn_succ]
    rw [comp_finProdFinEquiv_symm_succ, pairedWedge_wedgePow_succ_wedgePow_succ_apply_vecCons
        α ω k l _ _ _ _ (fun r ↦ apply_zero_comp_succ_eq_zero α b c hα₀₀ hα₀₁ _)
        (fun r ↦ apply_zero_comp_succ_eq_zero ω b 1 hω₀₀ hω₀₁ _),
      ih', ih', hc, Multiset.esymm_cons, Nat.factorial_succ k, Nat.factorial_succ l]
    rw [show α ![b (0, 0), b (0, 1)] = c 0 by simpa using hα₀₁ 0 0,
      show ω ![b (0, 0), b (0, 1)] = 1 by simpa using hω₀₁ 0 0]
    push_cast
    ring

/-- **Mixed wedge powers on diagonal pairs.** If the vectors `qᵢ = b (i, 0)` and `pᵢ = b (i, 1)`,
`i < m`, satisfy `α(qᵢ, qⱼ) = ω(qᵢ, qⱼ) = 0`, `α(qᵢ, pⱼ) = cᵢ δᵢⱼ` and `ω(qᵢ, pⱼ) = δᵢⱼ`, then for
`k + l = m` the form `α ^ k ∧ ω ^ l` takes the value `k! l! σ_k(c)` on `(q₀, p₀, q₁, p₁, …)`,
where `σ_k` is the `k`-th elementary symmetric polynomial. -/
theorem pairedWedge_wedgePow_wedgePow_apply_finProdFinEquiv (α ω : E [⋀^Fin 2]→L[ℝ] ℝ)
    {m k l : ℕ} (hkl : k + l = m) (b : Fin m × Fin 2 → E) (c : Fin m → ℝ)
    (hα₀₀ : ∀ i j, α ![b (i, 0), b (j, 0)] = 0)
    (hα₀₁ : ∀ i j, α ![b (i, 0), b (j, 1)] = if i = j then c i else 0)
    (hω₀₀ : ∀ i j, ω ![b (i, 0), b (j, 0)] = 0)
    (hω₀₁ : ∀ i j, ω ![b (i, 0), b (j, 1)] = if i = j then 1 else 0) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (wedgePow α k) (wedgePow ω l)
        (fun r ↦ b (finProdFinEquiv.symm (Fin.cast (by omega) r))) =
      k.factorial * l.factorial * MvPolynomial.eval c (MvPolynomial.esymm (Fin m) ℝ k) := by
  have h := pairedWedge_wedgePow_wedgePow_apply_esymm α ω b c hα₀₀ hα₀₁ hω₀₀ hω₀₁
    (k := k) (l := l) (by omega)
  simp only [Function.comp_def, Fin.cast_cast] at h
  rw [h, ← MvPolynomial.aeval_eq_eval,
    MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin m) (R := ℝ)]

end ContinuousAlternatingMap
