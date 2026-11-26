/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow.Basic
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

The proof is by induction on the number of pairs, expanding along `q₀` with the interior-product
rule for the wedge (`ContinuousAlternatingMap.curryLeftTopological_pairedWedge`). The vector `q₀`
goes either into `α ^ k` or into `ω ^ l`. In each case the power rule
`ι_v φ ^ (k + 1) = (k + 1) ι_v φ ∧ φ ^ k` leaves the one-form `α(q₀, ·)` or `ω(q₀, ·)`, which kills
the later pairs and takes the value `c₀` or `1` on `p₀`
(`ContinuousAlternatingMap.pairedWedge_curryLeftTopological_wedgePow_succ_apply`). This gives the
recursion `σ_{k+1}(c₀, c') = σ_{k+1}(c') + c₀ σ_k(c')` of the elementary symmetric functions
(`Multiset.esymm_cons`).

## Main results

* `ContinuousAlternatingMap.pairedWedge_curryLeftTopological_wedgePow_succ_apply`: inserting a
  vector `q` into `φ ^ (k + 1)` and wedging with `ψ` gives `(k + 1) φ(q, p) (φ ^ k ∧ ψ)(R)` on
  `(p, R)` when `φ(q, ·)` kills `R`.
* `ContinuousAlternatingMap.pairedWedge_wedgePow_wedgePow_apply_finProdFinEquiv`: the value
  `k! l! σ_k(c)` of `α ^ k ∧ ω ^ l` on diagonal pairs.
-/

public section

open TauCeti

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- **Inserting a vector into a power and wedging.** For a two-form `φ`, a form `ψ` of degree `d`
and vectors `q`, `p`, `R` such that `φ(q, Rᵢ) = 0` for every `i`, the interior product of `q` with
`φ ^ (k + 1)`, wedged with `ψ`, takes the value `(k + 1) φ(q, p) (φ ^ k ∧ ψ)(R)` on `(p, R)`.
The tuples are listed through a function `h` of the natural numbers, with `h 0 = p` and
`h (i + 1) = Rᵢ`. -/
theorem pairedWedge_curryLeftTopological_wedgePow_succ_apply (φ : E [⋀^Fin 2]→L[ℝ] ℝ) (k : ℕ)
    {d : ℕ} (ψ : E [⋀^Fin d]→L[ℝ] ℝ) (q : E) (h : ℕ → E)
    (hqh : ∀ i < 2 * k + d, φ ![q, h (i + 1)] = 0) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (curryLeftTopological (n := 2 * k + 1) (wedgePow φ (k + 1)) q) ψ
        (fun r : Fin (2 * k + 1 + d) ↦ h r) =
      (k + 1) * (φ ![q, h 0] * pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
        (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (wedgePow φ k) ψ
        (fun r : Fin (2 * k + d) ↦ h (r + 1))) := by
  rw [pairedWedge_apply_of_left_eq_smul_cast _ _ (Nat.add_comm 1 (2 * k)) ((k : ℝ) + 1)
    (fun w ↦ by rw [curryLeftTopological_apply_apply, wedgePow_succ_apply_vecCons, smul_eq_mul]),
    smul_eq_mul, pairedWedge_mul_assoc]
  congr 1
  have hcons : ((fun r : Fin (2 * k + 1 + d) ↦ h r) ∘ Fin.cast (by omega)) ∘
      Fin.cast (Nat.add_assoc 1 (2 * k) d).symm =
      Matrix.vecCons (h 0) (fun r : Fin (2 * k + d) ↦ h (r + 1)) ∘
        Fin.cast (Nat.add_comm 1 (2 * k + d)) := by
    funext r
    simp only [Function.comp_apply, Fin.val_cast]
    obtain ⟨r, hr⟩ := r
    cases r with
    | zero => rfl
    | succ r => rfl
  rw [hcons, pairedWedge_apply_vecCons_of_forall _ _ _ _ _ _ fun i ↦ by
      rw [curryLeftTopological_apply_apply]
      simpa using hqh i i.isLt,
    curryLeftTopological_apply_apply, ContinuousLinearMap.mul_apply']

/-- The multiset `{c₀, …, c_m}` of the first `m + 1` values of `c` is `c₀` added to the first `m`
values of `c` shifted by one. -/
private theorem map_range_succ (c : ℕ → ℝ) (m : ℕ) :
    (Multiset.range (m + 1)).map c = c 0 ::ₘ (Multiset.range m).map (fun i ↦ c (i + 1)) := by
  rw [Multiset.range, List.range_succ_eq_map, ← Multiset.cons_coe, Multiset.map_cons,
    ← Multiset.map_coe, Multiset.map_map]
  rfl

/-- The diagonal conditions for the pairs `(g (2 i), g (2 i + 1))`, `i < m + 1`, restrict to the
later pairs `(g (2 i + 2), g (2 i + 3))`, `i < m`. -/
private theorem shift_diagonal (φ : E [⋀^Fin 2]→L[ℝ] ℝ) {m : ℕ} {g : ℕ → E} {c : ℕ → ℝ}
    (h₀₀ : ∀ i < m + 1, ∀ j < m + 1, φ ![g (2 * i), g (2 * j)] = 0)
    (h₀₁ : ∀ i < m + 1, ∀ j < m + 1, φ ![g (2 * i), g (2 * j + 1)] = if i = j then c i else 0) :
    (∀ i < m, ∀ j < m, φ ![g (2 * i + 2), g (2 * j + 2)] = 0) ∧
      (∀ i < m, ∀ j < m, φ ![g (2 * i + 2), g (2 * j + 1 + 2)] =
        if i = j then c (i + 1) else 0) :=
  ⟨fun i hi j hj ↦ by simpa [Nat.mul_succ] using h₀₀ (i + 1) (by omega) (j + 1) (by omega),
    fun i hi j hj ↦ by
      simpa [Nat.mul_succ, add_assoc] using h₀₁ (i + 1) (by omega) (j + 1) (by omega)⟩

/-- Under the diagonal conditions, the one-form `φ(g 0, ·)` kills the later pairs. -/
private theorem apply_zero_later_eq_zero (φ : E [⋀^Fin 2]→L[ℝ] ℝ) {m : ℕ} {g : ℕ → E}
    {c : ℕ → ℝ} (h₀₀ : ∀ i < m + 1, ∀ j < m + 1, φ ![g (2 * i), g (2 * j)] = 0)
    (h₀₁ : ∀ i < m + 1, ∀ j < m + 1, φ ![g (2 * i), g (2 * j + 1)] = if i = j then c i else 0)
    (i : ℕ) (hi : i < 2 * m) : φ ![g 0, g (i + 2)] = 0 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  · simpa [Nat.mul_succ] using h₀₀ 0 (by omega) (j + 1) (by omega)
  · simpa [Nat.mul_succ, add_assoc] using h₀₁ 0 (by omega) (j + 1) (by omega)

/-- Splitting the first pair off a power of a two-form, for tuples listed through a function `g`
of the natural numbers: if `φ(g 0, ·)` kills the later vectors, then
`φ ^ (l + 1)(g) = (l + 1) φ(g 0, g 1) φ ^ l(g (· + 2))`. -/
private theorem wedgePow_succ_apply_nat (φ : E [⋀^Fin 2]→L[ℝ] ℝ) (l : ℕ) (g : ℕ → E)
    (hg : ∀ i < 2 * l, φ ![g 0, g (i + 2)] = 0) :
    wedgePow φ (l + 1) (fun r : Fin (2 * (l + 1)) ↦ g r) =
      (l + 1) * (φ ![g 0, g 1] * wedgePow φ l (fun r : Fin (2 * l) ↦ g (r + 2))) := by
  have hcons : (fun r : Fin (2 * (l + 1)) ↦ g r) =
      Matrix.vecCons (g 0) (Matrix.vecCons (g 1) fun r : Fin (2 * l) ↦ g (r + 2)) := by
    funext r
    obtain ⟨r, hr⟩ := r
    rcases r with _ | _ | r <;> rfl
  rw [hcons, wedgePow_succ_apply_vecCons_vecCons φ l (g 1) fun i ↦ hg i i.isLt]

/-- **The expansion along the first vector.** If `α(g 0, ·)` and `ω(g 0, ·)` kill the later
vectors, then `(α ^ (k + 1) ∧ ω ^ (l + 1))(g)` is
`(k + 1) α(g 0, g 1) (α ^ k ∧ ω ^ (l + 1))(g (· + 2))` plus
`(l + 1) ω(g 0, g 1) (α ^ (k + 1) ∧ ω ^ l)(g (· + 2))`. -/
private theorem pairedWedge_wedgePow_succ_wedgePow_succ_apply_nat (α ω : E [⋀^Fin 2]→L[ℝ] ℝ)
    (k l : ℕ) (g : ℕ → E) (hα : ∀ i < 2 * (k + l + 1), α ![g 0, g (i + 2)] = 0)
    (hω : ∀ i < 2 * (k + l + 1), ω ![g 0, g (i + 2)] = 0) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (wedgePow α (k + 1)) (wedgePow ω (l + 1))
        (fun r : Fin (2 * (k + 1) + 2 * (l + 1)) ↦ g r) =
      (k + 1) * (α ![g 0, g 1] *
        pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          (wedgePow α k) (wedgePow ω (l + 1))
          (fun r : Fin (2 * k + 2 * (l + 1)) ↦ g (r + 1 + 1))) +
      (l + 1) * (ω ![g 0, g 1] *
        pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          (wedgePow α (k + 1)) (wedgePow ω l)
          (fun r : Fin (2 * (k + 1) + 2 * l) ↦ g (r + 1 + 1))) := by
  have hcons : (fun r : Fin (2 * (k + 1) + 2 * (l + 1)) ↦ g r) =
      Matrix.vecCons (g 0) (fun r : Fin (2 * k + 1 + 1 + (2 * l + 1)) ↦ g (r + 1)) := by
    funext r
    obtain ⟨r, hr⟩ := r
    rcases r with _ | r <;> rfl
  rw [hcons, ← curryLeftTopological_apply_apply (n := 2 * k + 1 + 1 + (2 * l + 1)),
    curryLeftTopological_pairedWedge (k := 2 * k + 1) (l := 2 * l + 1),
    Even.neg_one_pow ⟨k + 1, by ring⟩, one_smul]
  -- The vector `g 0` in `α ^ (k + 1)`.
  have h₁ := pairedWedge_curryLeftTopological_wedgePow_succ_apply α k (wedgePow ω (l + 1))
    (g 0) (fun i ↦ g (i + 1)) fun i hi ↦ hα i (by omega)
  -- The vector `g 0` in `ω ^ (l + 1)`, after moving `ι_{g 0} ω ^ (l + 1)` to the front and back.
  have h₂ := pairedWedge_curryLeftTopological_wedgePow_succ_apply ω l (wedgePow α (k + 1))
    (g 0) (fun i ↦ g (i + 1)) fun i hi ↦ hω i (by omega)
  have hcomm := pairedWedge_comm (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (fun a b ↦ mul_comm a b) (wedgePow α (k + 1))
    (curryLeftTopological (n := 2 * l + 1) (wedgePow ω (l + 1)) (g 0))
    (fun r : Fin (2 * (k + 1) + (2 * l + 1)) ↦ g (r + 1))
  have hcomm' := pairedWedge_comm (ContinuousLinearMap.mul ℝ ℝ).continuous₂
    (fun a b ↦ mul_comm a b) (wedgePow ω l) (wedgePow α (k + 1))
    (fun r : Fin (2 * l + 2 * (k + 1)) ↦ g (r + 1 + 1))
  rw [Even.neg_one_pow ⟨(k + 1) * (2 * l + 1), by ring⟩, one_smul] at hcomm
  rw [Even.neg_one_pow ⟨l * (2 * (k + 1)), by ring⟩, one_smul] at hcomm'
  exact congrArg₂ (· + ·) h₁ ((hcomm.trans h₂).trans (by rw [hcomm']; rfl))

/-- The value of `α ^ k ∧ ω ^ l` on diagonal pairs, with the pairs listed through a function `g`
of the natural numbers: `qᵢ = g (2 i)` and `pᵢ = g (2 i + 1)`. -/
private theorem pairedWedge_wedgePow_wedgePow_apply_nat (α ω : E [⋀^Fin 2]→L[ℝ] ℝ) :
    ∀ (m k l : ℕ), k + l = m → ∀ (g : ℕ → E) (c : ℕ → ℝ),
    (∀ i < m, ∀ j < m, α ![g (2 * i), g (2 * j)] = 0) →
    (∀ i < m, ∀ j < m, α ![g (2 * i), g (2 * j + 1)] = if i = j then c i else 0) →
    (∀ i < m, ∀ j < m, ω ![g (2 * i), g (2 * j)] = 0) →
    (∀ i < m, ∀ j < m, ω ![g (2 * i), g (2 * j + 1)] = if i = j then (fun _ ↦ 1) i else 0) →
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (wedgePow α k) (wedgePow ω l) (fun r : Fin (2 * k + 2 * l) ↦ g r) =
      k.factorial * l.factorial * ((Multiset.range m).map c).esymm k := by
  intro m
  induction m with
  | zero =>
    intro k l hkl g c _ _ _ _
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ l = 0 := by omega
    rw [pairedWedge_apply_zero_left, wedgePow_zero_apply, wedgePow_zero_apply]
    simp
  | succ m ih =>
    intro k l hkl g c hα₀₀ hα₀₁ hω₀₀ hω₀₁
    -- The later pairs, listed through `g (· + 2)`, with the values `c (· + 1)`.
    have ih' := fun k l hkl ↦ ih k l hkl (fun i ↦ g (i + 2)) (fun i ↦ c (i + 1))
      (shift_diagonal α hα₀₀ hα₀₁).1 (shift_diagonal α hα₀₀ hα₀₁).2
      (shift_diagonal ω hω₀₀ hω₀₁).1 (shift_diagonal ω hω₀₀ hω₀₁).2
    have hαq := apply_zero_later_eq_zero α hα₀₀ hα₀₁
    have hωq := apply_zero_later_eq_zero ω hω₀₀ hω₀₁
    have hα01 : α ![g 0, g 1] = c 0 := by simpa using hα₀₁ 0 (by omega) 0 (by omega)
    have hω01 : ω ![g 0, g 1] = 1 := by simpa using hω₀₁ 0 (by omega) 0 (by omega)
    rw [map_range_succ]
    rcases k with _ | k <;> rcases l with _ | l
    · omega
    · -- `k = 0`: the top power of `ω`.
      obtain rfl : l = m := by omega
      have h0 := ih' 0 l (by omega)
      rw [pairedWedge_apply_zero_left, wedgePow_zero_apply, ContinuousLinearMap.mul_apply',
        one_mul] at h0 ⊢
      rw [show (fun r : Fin (2 * 0 + 2 * (l + 1)) ↦ g r) ∘ Fin.cast (Nat.zero_add _).symm =
          fun r : Fin (2 * (l + 1)) ↦ g r from rfl, wedgePow_succ_apply_nat ω l g hωq, hω01]
      rw [show (fun r : Fin (2 * l) ↦ g (r + 2)) =
          (fun r : Fin (2 * 0 + 2 * l) ↦ g (r + 2)) ∘ Fin.cast (Nat.zero_add _).symm from rfl, h0]
      simp [Nat.factorial_succ]
    · -- `l = 0`: the top power of `α`.
      obtain rfl : k = m := by omega
      have h0 := ih' k 0 (by omega)
      rw [pairedWedge_apply_zero_right, wedgePow_zero_apply, ContinuousLinearMap.mul_apply',
        mul_one] at h0 ⊢
      rw [show (fun r : Fin (2 * (k + 1) + 2 * 0) ↦ g r) = fun r : Fin (2 * (k + 1)) ↦ g r from rfl,
        wedgePow_succ_apply_nat α k g hαq, hα01,
        show (fun r : Fin (2 * k) ↦ g (r + 2)) = fun r : Fin (2 * k + 2 * 0) ↦ g (r + 2) from rfl,
        h0, Multiset.esymm_cons,
        Multiset.esymm_of_card_lt (n := k + 1) (by simp)]
      simp [Nat.factorial_succ]
      ring
    · -- Both powers are positive: expand along the first vector.
      rw [pairedWedge_wedgePow_succ_wedgePow_succ_apply_nat α ω k l g
          (fun i hi ↦ hαq i (by omega)) (fun i hi ↦ hωq i (by omega)), hα01, hω01,
        ih' k (l + 1) (by omega), ih' (k + 1) l (by omega), Multiset.esymm_cons,
        Nat.factorial_succ k, Nat.factorial_succ l]
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
  -- List the pairs and the values through functions of the natural numbers.
  set g : ℕ → E := fun n ↦
    if h : n / 2 < m then b (⟨n / 2, h⟩, ⟨n % 2, Nat.mod_lt _ two_pos⟩) else 0 with hg
  set c' : ℕ → ℝ := fun n ↦ if h : n < m then c ⟨n, h⟩ else 0 with hc'
  have hg₀ (i : ℕ) (hi : i < m) : g (2 * i) = b (⟨i, hi⟩, 0) := by
    have h₁ : 2 * i / 2 = i := by omega
    have h₂ : 2 * i % 2 = 0 := by omega
    simp only [hg, h₁, h₂, hi, ↓reduceDIte]
    rfl
  have hg₁ (i : ℕ) (hi : i < m) : g (2 * i + 1) = b (⟨i, hi⟩, 1) := by
    have h₁ : (2 * i + 1) / 2 = i := by omega
    have h₂ : (2 * i + 1) % 2 = 1 := by omega
    simp only [hg, h₁, h₂, hi, ↓reduceDIte]
    rfl
  have hfam : (fun r : Fin (2 * k + 2 * l) ↦ b (finProdFinEquiv.symm (Fin.cast (by omega) r))) =
      fun r : Fin (2 * k + 2 * l) ↦ g r := by
    funext r
    have hr : (r : ℕ) / 2 < m := by omega
    simp only [hg, hr, ↓reduceDIte, finProdFinEquiv_symm_apply]
    congr 1
  have hval : (Multiset.range m).map c' = Finset.univ.val.map c := by
    rw [← Finset.range_val, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ, Finset.map_val,
      Multiset.map_map]
    congr 1
    funext i
    simp [hc', i.isLt]
  have hev : MvPolynomial.eval c (MvPolynomial.esymm (Fin m) ℝ k) =
      (Finset.univ.val.map c).esymm k := by
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin m) (R := ℝ)]
    rfl
  rw [hfam, hev, ← hval]
  refine pairedWedge_wedgePow_wedgePow_apply_nat α ω m k l hkl g c' (fun i hi j hj ↦ ?_)
    (fun i hi j hj ↦ ?_) (fun i hi j hj ↦ ?_) (fun i hi j hj ↦ ?_)
  · rw [hg₀ i hi, hg₀ j hj]
    exact hα₀₀ _ _
  · rw [hg₀ i hi, hg₁ j hj, hα₀₁]
    simp [hc', hi, Fin.ext_iff]
  · rw [hg₀ i hi, hg₀ j hj]
    exact hω₀₀ _ _
  · rw [hg₀ i hi, hg₁ j hj, hω₀₁]
    simp [Fin.ext_iff]

end ContinuousAlternatingMap
