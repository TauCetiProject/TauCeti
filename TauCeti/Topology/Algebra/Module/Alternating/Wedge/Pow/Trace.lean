/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow.Basic
import TauCeti.Logic.Equiv.Fin.Basic

/-!
# A two-form wedged with a power of a two-form on standard pairs

Let `ω` and `α` be real two-forms on a real vector space, and let `qᵢ = b (i, 0)` and
`pᵢ = b (i, 1)`, for `i ≤ m`, be vectors with `ω(qᵢ, qⱼ) = 0`, `ω(qᵢ, pⱼ) = δᵢⱼ` and
`ω(pᵢ, pⱼ) = 0`: a symplectic basis of their span. Then

`(ω ^ m ∧ α)(q₀, p₀, …, qₘ, pₘ) = m! · ∑ᵢ α(qᵢ, pᵢ)`

(`ContinuousAlternatingMap.pairedWedge_wedgePow_apply_finProdFinEquiv`). For `α = ω` it is the
value `(m + 1)!` of the top power (`ContinuousAlternatingMap.wedgePow_apply_finProdFinEquiv`). It
is the pointwise content of the trace identity `n α ∧ ω ^ (n - 1) = (tr_ω α) ω ^ n` of Kähler
geometry.

The proof is by induction on `m`, expanding along `q₀` and then `p₀` with the interior-product
rule for the wedge (`ContinuousAlternatingMap.curryLeftTopological_pairedWedge`) and the power
rule `ι_v ω ^ (m + 1) = (m + 1) ι_v ω ∧ ω ^ m`
(`ContinuousAlternatingMap.wedgePow_succ_apply_vecCons`). Inserting `q₀` into `ω ^ (m + 1)`
leaves the one-form `ω(q₀, ·)`, which kills the later pairs and pairs with `p₀` to one, so that
term reduces to the induction hypothesis. Inserting `q₀` into `α` and then `p₀` leaves
`α(q₀, p₀) ω ^ (m + 1)` on the later pairs, plus a term with `ω(p₀, ·)`, which kills them.
-/

public section

open TauCeti

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- Inserting `q` into `α` and wedging with `ω ^ (m + 1)`: when `ω(p, ·)` kills the vectors of
`R`, the value on `(p, R)` is `α(q, p) ω ^ (m + 1)(R)`. -/
private theorem pairedWedge_wedgePow_succ_curry_apply (ω α : E [⋀^Fin 2]→L[ℝ] ℝ) (m : ℕ)
    (q p : E) (R : Fin (2 * (m + 1)) → E) (hpR : ∀ i, ω ![p, R i] = 0) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (wedgePow ω (m + 1)) (curryLeftTopological (n := 1) α q) (Matrix.vecCons p R) =
      wedgePow ω (m + 1) R * α ![q, p] := by
  -- Peel `p` off the `(2 m + 3)`-form, splitting its degree as `(2 m + 1 + 1) + (0 + 1)` so that
  -- the interior-product rule sees the `(2 m + 2)`-form `ω ^ (m + 1)` and the one-form `ι_q α`.
  rw [← curryLeftTopological_apply_apply (n := 2 * m + 1 + 1 + 0),
    curryLeftTopological_pairedWedge (k := 2 * m + 1) (l := 0)]
  -- The term with `ω(p, ·)` vanishes on vectors that it kills.
  have hzero : ∀ w : Fin (2 * m + 1 + (0 + 1)) → E, (∀ i, ω ![p, w i] = 0) →
      pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (curryLeftTopological (n := 2 * m + 1) (wedgePow ω (m + 1)) p)
        (curryLeftTopological (n := 1) α q) w = 0 := by
    intro w hw
    rw [pairedWedge_apply]
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun σ _ ↦ ?_)
    rw [curryLeftTopological_apply_apply, wedgePow_succ_apply_vecCons,
      pairedWedge_apply_eq_zero_of_forall _ _ _ _ _ fun i ↦ ?_]
    · simp
    · rw [curryLeftTopological_apply_apply]
      simpa using hw _
  rw [hzero (R ∘ Fin.cast (by omega)) fun i ↦ hpR _, zero_add, pairedWedge_apply_zero_right]
  simp [curryLeftTopological_apply_apply, Even.neg_one_pow (n := 2 * m + 1 + 1) ⟨m + 1, by ring⟩]

/-- **A two-form wedged with a power of a two-form on standard pairs.** If the vectors
`qᵢ = b (i, 0)` and `pᵢ = b (i, 1)`, `i ≤ m`, satisfy `ω(qᵢ, qⱼ) = 0`, `ω(qᵢ, pⱼ) = δᵢⱼ` and
`ω(pᵢ, pⱼ) = 0`, then `(ω ^ m ∧ α)(q₀, p₀, …, qₘ, pₘ) = m! · ∑ᵢ α(qᵢ, pᵢ)`. -/
theorem pairedWedge_wedgePow_apply_finProdFinEquiv (ω α : E [⋀^Fin 2]→L[ℝ] ℝ) {m : ℕ}
    (b : Fin (m + 1) × Fin 2 → E) (h₀₀ : ∀ i j, ω ![b (i, 0), b (j, 0)] = 0)
    (h₀₁ : ∀ i j, ω ![b (i, 0), b (j, 1)] = if i = j then 1 else 0)
    (h₁₁ : ∀ i j, ω ![b (i, 1), b (j, 1)] = 0) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (wedgePow ω m) α
        (fun r : Fin (2 * (m + 1)) ↦
          b (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 (m + 1)) r))) =
      m.factorial * ∑ i, α ![b (i, 0), b (i, 1)] := by
  induction m with
  | zero =>
    rw [comp_finProdFinEquiv_symm_succ, pairedWedge_apply_zero_left, wedgePow_zero_apply,
      ContinuousLinearMap.mul_apply', one_mul, Nat.factorial_zero, Nat.cast_one, one_mul,
      Fin.sum_univ_one]
    congr 1
    funext i
    fin_cases i <;> rfl
  | succ m ih =>
    rw [comp_finProdFinEquiv_symm_succ]
    set b' := b ∘ Prod.map Fin.succ id with hb'
    set R : Fin (2 * (m + 1)) → E :=
      fun r ↦ b' (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 (m + 1)) r)) with hR
    -- The one-forms `ω(q₀, ·)` and `ω(p₀, ·)` kill the later pairs.
    have hq (jk : Fin (m + 1) × Fin 2) : ω ![b (0, 0), b' jk] = 0 :=
      apply_zero_comp_succ_eq_zero ω b 1 h₀₀ h₀₁ jk
    have hp (jk : Fin (m + 1) × Fin 2) : ω ![b (0, 1), b' jk] = 0 := by
      obtain ⟨j, k⟩ := jk
      fin_cases k
      · rw [apply_vecCons_swap, neg_eq_zero]
        simpa [hb', Fin.succ_ne_zero j] using h₀₁ j.succ 0
      · exact h₁₁ 0 j.succ
    have h₀₀' : ∀ i j, ω ![b' (i, 0), b' (j, 0)] = 0 := fun i j ↦ h₀₀ _ _
    have h₀₁' : ∀ i j, ω ![b' (i, 0), b' (j, 1)] = if i = j then 1 else 0 :=
      fun i j ↦ by simpa [hb'] using h₀₁ i.succ j.succ
    have h₁₁' : ∀ i j, ω ![b' (i, 1), b' (j, 1)] = 0 := fun i j ↦ h₁₁ _ _
    -- Inserting `q₀` into `ω ^ (m + 1)`, then into `α`.
    have hω := pairedWedge_curryLeftTopological_wedgePow_succ_apply ω m α (b (0, 0)) (b (0, 1)) R
      (by omega) fun r ↦ hq _
    rw [show ω ![b (0, 0), b (0, 1)] = 1 by simpa using h₀₁ 0 0, one_mul] at hω
    -- The cast `Fin (2 * m + 2) → Fin (2 * (m + 1))` on the right is the identity.
    conv at hω => rhs; rw [Fin.cast_refl, Function.comp_id]
    have hα := pairedWedge_wedgePow_succ_curry_apply ω α m (b (0, 0)) (b (0, 1)) R fun r ↦ hp _
    -- The values on the later pairs.
    have hih := ih b' h₀₀' h₀₁' h₁₁'
    have htop := wedgePow_apply_finProdFinEquiv ω b' h₀₀' h₀₁'
    rw [← hR] at hih htop
    -- Expand along `q₀`; the sign `(-1) ^ (2 m + 2)` is `1`.
    rw [← curryLeftTopological_apply_apply (n := 2 * (m + 1) + 1),
      curryLeftTopological_pairedWedge (k := 2 * m + 1) (l := 1),
      Even.neg_one_pow ⟨m + 1, by ring⟩, one_smul, hω, hα, hih, htop,
      Fin.sum_univ_succ (f := fun i : Fin (m + 1 + 1) ↦ α ![b (i, 0), b (i, 1)]),
      Nat.factorial_succ]
    simp only [hb', Function.comp_apply, Prod.map_apply, id]
    push_cast
    ring

end ContinuousAlternatingMap
