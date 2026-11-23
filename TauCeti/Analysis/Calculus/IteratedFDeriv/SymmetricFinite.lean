/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Symmetry of iterated derivatives of finitely smooth maps

Over `ℝ` or `ℂ`, the `k`-th iterated derivative at `x` of a map which is `C^k` at `x` is a
symmetric multilinear map: permuting its arguments does not change its value. Mathlib proves the
case `k = 2` for `C^2` maps (`ContDiffAt.isSymmSndFDerivAt`) and every `k` for analytic maps over
any field (`ContDiffAt.iteratedFDeriv_comp_perm`). This file treats every `k` for maps which are
only `C^k`, as needed for the derivatives of smooth but non-analytic maps, such as local sections
of vector bundles in charts. As for `ContDiffAt.isSymmSndFDerivAt`, the statements take the
smoothness hypothesis `minSmoothness 𝕜 k ≤ n`, which asks for `C^k` over `ℝ` or `ℂ` and for
analyticity over other fields.

The proof is by induction on `k`. A permutation of `k + 2` arguments is a product of
transpositions. A transposition of two of the last `k + 1` arguments is handled by the induction
hypothesis, applied to the `(k + 1)`-th derivative at every point near `x` and then
differentiated. The transposition of the first two arguments is the symmetry of the second
derivative of the `k`-th iterated derivative. Every other transposition is conjugate to the
latter by a transposition of the former kind.

## Main results

* `ContDiffAt.iteratedFDeriv_comp_perm_of_le`: the iterated derivative of a finitely smooth map is
  symmetric over `ℝ` or `ℂ`, and that of an analytic map is symmetric over any field.
* `ContDiffAt.domDomCongr_iteratedFDeriv_of_le`: the same, as an equality of multilinear maps.
-/

public section

open Equiv Filter
open scoped ContDiff Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {x : E} {n : ℕ∞ω}

namespace TauCeti

/-- The iterated derivative of order `k + 2`, evaluated on `v`, is the second derivative of the
iterated derivative of order `k` in the directions `v 0` and `v 1`, applied to the remaining
directions. -/
private theorem iteratedFDeriv_add_two_apply {k : ℕ} (hf : ContDiffAt 𝕜 (k + 2) f x)
    (v : Fin (k + 2) → E) :
    iteratedFDeriv 𝕜 (k + 2) f x v =
      fderiv 𝕜 (fderiv 𝕜 (iteratedFDeriv 𝕜 k f)) x (v 0) (v 1) (fun i ↦ v i.succ.succ) := by
  have hd₁ : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 (k + 1) f) x :=
    (hf.iteratedFDeriv_right (m := 1) (by norm_cast; omega)).differentiableAt one_ne_zero
  have hd₂ : DifferentiableAt 𝕜 (fderiv 𝕜 (iteratedFDeriv 𝕜 k f)) x :=
    ((hf.iteratedFDeriv_right (m := 2) (i := k) (by norm_cast; omega)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt one_ne_zero
  have htail : (fun y ↦ iteratedFDeriv 𝕜 (k + 1) f y (Fin.tail v)) =
      fun y ↦ fderiv 𝕜 (iteratedFDeriv 𝕜 k f) y (v 1) (fun i ↦ v i.succ.succ) := by
    funext y
    rw [iteratedFDeriv_succ_apply_left]
    simp only [Fin.tail_def, Fin.succ_zero_eq_one]
  rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply hd₁, htail,
    fderiv_continuousMultilinear_apply_const_apply (hd₂.clm_apply (differentiableAt_const _)),
    fderiv_clm_apply hd₂ (differentiableAt_const _)]
  simp

/-- A transposition of two of the last `k + 1` arguments does not change the
iterated derivative of order `k + 2`, if the iterated derivatives of order `k + 1` near `x` are
symmetric. -/
private theorem iteratedFDeriv_comp_swap_succ_succ {k : ℕ} (hf : ContDiffAt 𝕜 (k + 2) f x)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ (w : Fin (k + 1) → E) (σ : Perm (Fin (k + 1))),
      iteratedFDeriv 𝕜 (k + 1) f y (w ∘ σ) = iteratedFDeriv 𝕜 (k + 1) f y w)
    (a b : Fin (k + 1)) (v : Fin (k + 2) → E) :
    iteratedFDeriv 𝕜 (k + 2) f x (v ∘ swap a.succ b.succ) = iteratedFDeriv 𝕜 (k + 2) f x v := by
  have hd : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 (k + 1) f) x :=
    (hf.iteratedFDeriv_right (m := 1) (by norm_cast; omega)).differentiableAt one_ne_zero
  have htail : Fin.tail (v ∘ swap a.succ b.succ) = Fin.tail v ∘ swap a b := by
    ext i
    simp only [Fin.tail, Function.comp_apply, (Fin.succ_injective _).map_swap]
  have hhead : (v ∘ swap a.succ b.succ) 0 = v 0 := by
    simp [swap_apply_of_ne_of_ne (Fin.succ_ne_zero a).symm (Fin.succ_ne_zero b).symm]
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left, htail, hhead,
    ← fderiv_continuousMultilinear_apply_const_apply hd,
    ← fderiv_continuousMultilinear_apply_const_apply hd]
  congr 1
  exact Filter.EventuallyEq.fderiv_eq (hsymm.mono fun y hy ↦ hy _ _)

/-- Transposing the first two arguments does not change the iterated derivative of order `k + 2`
of a map which is `C^n` at `x` with `minSmoothness 𝕜 (k + 2) ≤ n`. -/
private theorem iteratedFDeriv_comp_swap_zero_one {k : ℕ} (hf : ContDiffAt 𝕜 n f x)
    (hk : minSmoothness 𝕜 (k + 2) ≤ n) (v : Fin (k + 2) → E) :
    iteratedFDeriv 𝕜 (k + 2) f x (v ∘ swap 0 1) = iteratedFDeriv 𝕜 (k + 2) f x v := by
  have hf' : ContDiffAt 𝕜 (k + 2) f x := hf.of_le (le_minSmoothness.trans hk)
  have h2 : ContDiffAt 𝕜 (minSmoothness 𝕜 2) (iteratedFDeriv 𝕜 k f) x :=
    hf.iteratedFDeriv_right (by rwa [← minSmoothness_add, add_comm])
  rw [iteratedFDeriv_add_two_apply hf', iteratedFDeriv_add_two_apply hf']
  have hrest : (fun i : Fin k ↦ (v ∘ swap 0 1) i.succ.succ) = fun i ↦ v i.succ.succ := by
    ext i
    simp only [Function.comp_apply]
    rw [swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one i)]
  rw [hrest]
  simp only [Function.comp_apply, swap_apply_left, swap_apply_right]
  rw [(h2.isSymmSndFDerivAt le_rfl).eq]

/-- The iterated derivative of order `k` at `x` of a map which is `C^n` at `x` with
`minSmoothness 𝕜 k ≤ n` is symmetric. -/
private theorem iteratedFDeriv_comp_perm_of_minSmoothness_le :
    ∀ (k : ℕ) {n : ℕ∞ω} {f : E → F} {x : E}, ContDiffAt 𝕜 n f x → minSmoothness 𝕜 k ≤ n →
      ∀ (v : Fin k → E) (σ : Perm (Fin k)),
        iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v
  | 0, _, _, _, _, _, v, σ => by rw [Subsingleton.elim σ 1, Perm.coe_one, Function.comp_id]
  | 1, _, _, _, _, _, v, σ => by rw [Subsingleton.elim σ 1, Perm.coe_one, Function.comp_id]
  | k + 2, n, f, x, hf, hk, v, σ => by
    have hf' : ContDiffAt 𝕜 (k + 2) f x := hf.of_le (by exact_mod_cast le_minSmoothness.trans hk)
    -- The permutations which leave the derivative invariant are closed under products.
    let S : Perm (Fin (k + 2)) → Prop := fun τ ↦
      ∀ w, iteratedFDeriv 𝕜 (k + 2) f x (w ∘ τ) = iteratedFDeriv 𝕜 (k + 2) f x w
    have hmul : ∀ τ₁ τ₂, S τ₁ → S τ₂ → S (τ₁ * τ₂) := fun τ₁ τ₂ h₁ h₂ w ↦ by
      rw [Perm.coe_mul, ← Function.comp_assoc, h₂, h₁]
    -- Near `x`, the derivatives of order `k + 1` are symmetric by the induction hypothesis.
    have hsymm : ∀ᶠ y in 𝓝 x, ∀ (w : Fin (k + 1) → E) (τ : Perm (Fin (k + 1))),
        iteratedFDeriv 𝕜 (k + 1) f y (w ∘ τ) = iteratedFDeriv 𝕜 (k + 1) f y w := by
      -- At a finite order of smoothness, `f` is smooth at every point near `x`.
      obtain ⟨n', hn', hn'n, hn'_ne⟩ := exist_minSmoothness_le_ne_infty hk
      exact ((hf.of_le hn'n).eventually hn'_ne).mono fun y hy ↦
        iteratedFDeriv_comp_perm_of_minSmoothness_le (k + 1) hy
          ((minSmoothness_monotone (by norm_cast; omega)).trans hn')
    have hsucc : ∀ a b : Fin (k + 1), S (swap a.succ b.succ) :=
      fun a b ↦ iteratedFDeriv_comp_swap_succ_succ hf' hsymm a b
    have hzero : S (swap 0 1) := iteratedFDeriv_comp_swap_zero_one hf (by exact_mod_cast hk)
    -- Every transposition leaves the derivative invariant, hence so does every permutation.
    have hswap : ∀ i j : Fin (k + 2), S (swap i j) := by
      have hzero' : ∀ j : Fin (k + 2), S (swap 0 j) := by
        intro j
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨b, rfl⟩
        · exact fun w ↦ by rw [swap_self, coe_refl, Function.comp_id]
        rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨c, rfl⟩
        · exact hzero
        -- `swap 0 j` is the conjugate of `swap 0 1` by `swap 1 j`, which fixes `0`.
        have hconj : swap (0 : Fin (k + 2)) c.succ.succ =
            swap (1 : Fin (k + 2)) c.succ.succ * swap 0 1 * swap 1 c.succ.succ := by
          rw [swap_mul_swap_mul_swap (by simp) (Fin.succ_ne_zero _).symm, swap_comm]
        rw [hconj]
        exact hmul _ _ (hmul _ _ (hsucc 0 c.succ) hzero) (hsucc 0 c.succ)
      intro i j
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨a, rfl⟩
      · exact hzero' j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨b, rfl⟩
      · rw [swap_comm]
        exact hzero' _
      · exact hsucc a b
    exact Perm.swap_induction_on (motive := S) σ (fun w ↦ by rw [Perm.coe_one, Function.comp_id])
      (fun τ i j _ hτ ↦ hmul _ _ (hswap i j) hτ) v

end TauCeti

open TauCeti in
/-- **Symmetry of iterated derivatives.** If `f` is `C^n` at `x` with `minSmoothness 𝕜 k ≤ n`
(that is, `k ≤ n` over `ℝ` or `ℂ` and `n = ω` otherwise), then permuting the arguments of the
`k`-th iterated derivative of `f` at `x` does not change its value. -/
theorem ContDiffAt.iteratedFDeriv_comp_perm_of_le {k : ℕ}
    (hf : ContDiffAt 𝕜 n f x) (hk : minSmoothness 𝕜 k ≤ n) (v : Fin k → E) (σ : Perm (Fin k)) :
    iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v :=
  iteratedFDeriv_comp_perm_of_minSmoothness_le k hf hk v σ

/-- **Symmetry of iterated derivatives**, as an equality of multilinear maps: if `f` is `C^n` at
`x` with `minSmoothness 𝕜 k ≤ n`, then reindexing the `k`-th iterated derivative of `f` at `x` by
a permutation gives back the same multilinear map. -/
theorem ContDiffAt.domDomCongr_iteratedFDeriv_of_le {k : ℕ}
    (hf : ContDiffAt 𝕜 n f x) (hk : minSmoothness 𝕜 k ≤ n) (σ : Perm (Fin k)) :
    (iteratedFDeriv 𝕜 k f x).domDomCongr σ = iteratedFDeriv 𝕜 k f x := by
  ext v
  exact hf.iteratedFDeriv_comp_perm_of_le hk v σ
