/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Symmetry of iterated derivatives of `Cⁿ` maps

Over `ℝ` or `ℂ`, the `n`-th iterated derivative of a map which is `Cⁿ` at a point is a symmetric
multilinear map there. Mathlib proves this for second derivatives
(`ContDiffAt.isSymmSndFDerivAt`) and for analytic maps (`ContDiffAt.iteratedFDeriv_comp_perm`).
Over a general field the statement uses the smoothness exponent `minSmoothness 𝕜 n`, which is `n`
over `ℝ` or `ℂ` and `ω` otherwise, following `ContDiffAt.isSymmSndFDerivAt`.

The proof is by induction on `n`. Writing the `(n + 1)`-st derivative as the derivative of the
`n`-th one shows invariance under permutations fixing the first direction; writing it as the
`n`-th derivative of the derivative shows invariance under permutations fixing the last one.
Together with the symmetry of second derivatives, these transpositions generate all permutations.

Symmetric Taylor coefficients are the fibres of higher-order jet bundles.
-/

public section

open Equiv Filter Fin Function
open scoped Topology ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A map into multilinear maps whose values near `x` are invariant under a permutation of the
arguments has invariant derivatives at `x`. -/
theorem fderiv_domDomCongr_of_eventually {n : ℕ} {Φ : E → E [×n]→L[𝕜] F} {x : E}
    (σ : Perm (Fin n)) (hΦ : ∀ᶠ y in 𝓝 x, (Φ y).domDomCongr σ = Φ y) (w : E) :
    (fderiv 𝕜 Φ x w).domDomCongr σ = fderiv 𝕜 Φ x w := by
  by_cases hd : DifferentiableAt 𝕜 Φ x
  · let L : (E [×n]→L[𝕜] F) →L[𝕜] E [×n]→L[𝕜] F :=
      (ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E F σ :
        (E [×n]→L[𝕜] F) →L[𝕜] E [×n]→L[𝕜] F)
    have h₁ : HasFDerivAt (fun y ↦ L (Φ y)) (L.comp (fderiv 𝕜 Φ x)) x :=
      L.hasFDerivAt.comp x hd.hasFDerivAt
    have h₂ : HasFDerivAt (fun y ↦ L (Φ y)) (fderiv 𝕜 Φ x) x :=
      hd.hasFDerivAt.congr_of_eventuallyEq (hΦ.mono fun y hy ↦ hy)
    exact congrArg (fun T ↦ T w) (h₁.unique h₂)
  · ext v
    simp [fderiv_zero_of_not_differentiableAt hd]

/-- The `(n + 2)`-nd iterated derivative is the second derivative of the `n`-th one, with the
first two directions as arguments of the second derivative. -/
theorem iteratedFDeriv_add_two_apply {f : E → F} {x : E} {n : ℕ} (v : Fin (n + 2) → E) :
    iteratedFDeriv 𝕜 (n + 2) f x v =
      fderiv 𝕜 (fderiv 𝕜 (iteratedFDeriv 𝕜 n f)) x (v 0) (v 1) (tail (tail v)) := by
  have h := LinearIsometryEquiv.comp_fderiv (𝕜 := 𝕜)
    (iso := (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) F).symm)
    (f := fderiv 𝕜 (iteratedFDeriv 𝕜 n f)) (x := x)
  rw [← iteratedFDeriv_succ_eq_comp_left] at h
  rw [iteratedFDeriv_succ_apply_left, h]
  -- Uncurrying the first argument is `continuousMultilinearCurryLeftEquiv_symm_apply`, which
  -- holds by definition.
  rfl

/-- **Symmetry of iterated derivatives.** If `f` is `Cⁿ` at `x` (analytic, over a field other
than `ℝ` or `ℂ`), then its `n`-th iterated derivative at `x` does not depend on the order of its
arguments. -/
theorem ContDiffAt.iteratedFDeriv_comp_perm_of_minSmoothness_le {N : ℕ∞ω} {n : ℕ} {f : E → F}
    {x : E} (hf : ContDiffAt 𝕜 N f x) (hn : minSmoothness 𝕜 n ≤ N) (σ : Perm (Fin n))
    (v : Fin n → E) :
    iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v := by
  induction n generalizing f x N with
  | zero => exact congrArg _ (funext fun i ↦ i.elim0)
  | succ n ih =>
    -- Invariance under transpositions fixing the first direction, by symmetry of the `n`-th
    -- derivative at nearby points.
    have hL (a b : Fin n) (v : Fin (n + 1) → E) :
        iteratedFDeriv 𝕜 (n + 1) f x (v ∘ swap a.succ b.succ) =
          iteratedFDeriv 𝕜 (n + 1) f x v := by
      obtain ⟨N', hN', hN'N, hN'top⟩ := exist_minSmoothness_le_ne_infty hn
      have hev : ∀ᶠ y in 𝓝 x, (iteratedFDeriv 𝕜 n f y).domDomCongr (swap a b) =
          iteratedFDeriv 𝕜 n f y := by
        filter_upwards [(hf.of_le hN'N).eventually hN'top] with y hy
        ext w
        exact ih hy ((minSmoothness_monotone (Nat.cast_le.2 n.le_succ)).trans hN') _ w
      have h0 : (v ∘ swap a.succ b.succ) 0 = v 0 := by
        simp [swap_apply_of_ne_of_ne (succ_ne_zero a).symm (succ_ne_zero b).symm]
      have ht : tail (v ∘ swap a.succ b.succ) = tail v ∘ swap a b := by
        funext i
        simp [tail, succ_injective _ |>.swap_apply]
      rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left, h0, ht]
      exact congrArg (fun M : E [×n]→L[𝕜] F ↦ M (tail v))
        (fderiv_domDomCongr_of_eventually (swap a b) hev (v 0))
    -- Invariance under the transposition of the first two directions, by symmetry of second
    -- derivatives.
    have h01 (hn1 : 1 ≤ n) (v : Fin (n + 1) → E) :
        iteratedFDeriv 𝕜 (n + 1) f x (v ∘ swap 0 1) = iteratedFDeriv 𝕜 (n + 1) f x v := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hsymm : IsSymmSndFDerivAt 𝕜 (iteratedFDeriv 𝕜 k f) x :=
        (hf.iteratedFDeriv_right (m := minSmoothness 𝕜 2) (i := k)
          (by rw [← minSmoothness_add]; convert hn using 2; push_cast; ring)).isSymmSndFDerivAt
          le_rfl
      have htt : tail (tail (v ∘ swap 0 1)) = tail (tail v) := by
        funext i
        simp [tail, swap_apply_of_ne_of_ne, Fin.ext_iff]
      rw [iteratedFDeriv_add_two_apply, iteratedFDeriv_add_two_apply, htt]
      simp only [comp_apply, swap_apply_left, swap_apply_right]
      rw [hsymm (v 1) (v 0)]
    have hmul {σ τ : Perm (Fin (n + 1))}
        (hσ : ∀ v, iteratedFDeriv 𝕜 (n + 1) f x (v ∘ σ) = iteratedFDeriv 𝕜 (n + 1) f x v)
        (hτ : ∀ v, iteratedFDeriv 𝕜 (n + 1) f x (v ∘ τ) = iteratedFDeriv 𝕜 (n + 1) f x v)
        (v : Fin (n + 1) → E) :
        iteratedFDeriv 𝕜 (n + 1) f x (v ∘ ⇑(σ * τ)) = iteratedFDeriv 𝕜 (n + 1) f x v :=
      (hτ (v ∘ σ)).trans (hσ v)
    -- Every transposition is a product of the previous ones.
    have hL' (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0) (v : Fin (n + 1) → E) :
        iteratedFDeriv 𝕜 (n + 1) f x (v ∘ swap a b) = iteratedFDeriv 𝕜 (n + 1) f x v := by
      obtain ⟨a, rfl⟩ := exists_succ_eq.2 ha
      obtain ⟨b, rfl⟩ := exists_succ_eq.2 hb
      exact hL a b v
    have h0 (b : Fin (n + 1)) (hb : b ≠ 0) (v : Fin (n + 1) → E) :
        iteratedFDeriv 𝕜 (n + 1) f x (v ∘ swap 0 b) = iteratedFDeriv 𝕜 (n + 1) f x v := by
      have hn1 : 1 ≤ n := by
        rcases n with _ | n
        · exact absurd (Fin.ext (by omega)) hb
        · omega
      have h10 : (1 : Fin (n + 1)) ≠ 0 := by
        rw [Ne, Fin.ext_iff, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)]
        omega
      rw [swap_comm, ← swap_mul_swap_mul_swap h10.symm hb.symm]
      exact hmul (hmul (hL' 1 b h10 hb) (h01 hn1)) (hL' 1 b h10 hb) v
    have hswap (a b : Fin (n + 1)) (hab : a ≠ b) (v : Fin (n + 1) → E) :
        iteratedFDeriv 𝕜 (n + 1) f x (v ∘ swap a b) = iteratedFDeriv 𝕜 (n + 1) f x v := by
      rcases eq_or_ne a 0 with rfl | ha
      · exact h0 b hab.symm v
      rcases eq_or_ne b 0 with rfl | hb
      · rw [swap_comm]
        exact h0 a ha v
      · exact hL' a b ha hb v
    induction σ using Perm.swap_induction_on generalizing v with
    | one => rfl
    | swap_mul τ a b hab hτ =>
      exact (hτ (v ∘ swap a b)).trans (hswap a b hab v)

/-- **Symmetry of iterated derivatives.** If `f` is `Cⁿ` at `x` (analytic, over a field other
than `ℝ` or `ℂ`), then its `n`-th iterated derivative at `x` is invariant under permutations of
its arguments. -/
theorem ContDiffAt.domDomCongr_iteratedFDeriv_of_minSmoothness_le {N : ℕ∞ω} {n : ℕ}
    {f : E → F} {x : E} (hf : ContDiffAt 𝕜 N f x) (hn : minSmoothness 𝕜 n ≤ N)
    (σ : Perm (Fin n)) :
    (iteratedFDeriv 𝕜 n f x).domDomCongr σ = iteratedFDeriv 𝕜 n f x := by
  ext v
  exact hf.iteratedFDeriv_comp_perm_of_minSmoothness_le hn σ v
