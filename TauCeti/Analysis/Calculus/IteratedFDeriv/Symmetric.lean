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

The main result is `ContDiffAt.iteratedFDeriv_comp_perm_of_minSmoothness_le`, with the
bundled form `ContDiffAt.domDomCongr_iteratedFDeriv_of_minSmoothness_le`. It is proved by
induction on `n` from two auxiliary results: the derivative of a map whose values are invariant
under a permutation of the arguments is invariant too
(`TauCeti.domDomCongr_fderiv_apply_of_eventually`), and the `(n + 2)`-nd derivative is the second
derivative of the `n`-th one (`TauCeti.iteratedFDeriv_add_two_apply`). The first gives invariance
under the transpositions of two directions other than the first one; the second, with the
symmetry of second derivatives, gives invariance under the transposition of the first two
directions. These generate all permutations (`Equiv.Perm.mclosure_swap_castSucc_succ`).

Symmetric Taylor coefficients are the fibres of higher-order jet bundles.
-/

public section

open Equiv Filter Fin Function
open scoped Topology ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace TauCeti

/-- A map into multilinear maps whose values near `x` are invariant under a permutation of the
arguments has invariant derivatives at `x`. -/
theorem domDomCongr_fderiv_apply_of_eventually {ι : Type*} [Finite ι] {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {Φ : E → ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ G) F}
    {x : E} (σ : Perm ι) (hΦ : ∀ᶠ y in 𝓝 x, (Φ y).domDomCongr σ = Φ y) (w : E) :
    (fderiv 𝕜 Φ x w).domDomCongr σ = fderiv 𝕜 Φ x w := by
  cases nonempty_fintype ι
  -- The isometry `domDomCongrₗᵢ 𝕜 G F σ` is `domDomCongr σ` by definition.
  let L := ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 G F σ
  have h := L.comp_fderiv (f := Φ) (x := x)
  rw [EventuallyEq.fderiv_eq (f₁ := L ∘ Φ) hΦ] at h
  exact congr($h.symm w)

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
  simp [tail]

end TauCeti

open TauCeti

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
        (domDomCongr_fderiv_apply_of_eventually (swap a b) hev (v 0))
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
    -- These transpositions generate all permutations.
    suffices ∀ v, iteratedFDeriv 𝕜 (n + 1) f x (v ∘ σ) = iteratedFDeriv 𝕜 (n + 1) f x v from this v
    have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin n ↦ swap i.castSucc i.succ) :=
      Perm.mclosure_swap_castSucc_succ n ▸ Submonoid.mem_top σ
    induction hσ using Submonoid.closure_induction with
    | mem τ hτ =>
      obtain ⟨i, rfl⟩ := hτ
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := i.pos; omega⟩
      induction i using Fin.cases with
      | zero => simpa using h01 (Nat.succ_pos k)
      | succ j => simpa [← succ_castSucc] using hL j.castSucc j.succ
    | one => exact fun v ↦ rfl
    | mul τ ρ _ _ hτ hρ => exact fun v ↦ (hρ (v ∘ τ)).trans (hτ v)

/-- **Symmetry of iterated derivatives.** If `f` is `Cⁿ` at `x` (analytic, over a field other
than `ℝ` or `ℂ`), then its `n`-th iterated derivative at `x` is invariant under permutations of
its arguments. -/
theorem ContDiffAt.domDomCongr_iteratedFDeriv_of_minSmoothness_le {N : ℕ∞ω} {n : ℕ}
    {f : E → F} {x : E} (hf : ContDiffAt 𝕜 N f x) (hn : minSmoothness 𝕜 n ≤ N)
    (σ : Perm (Fin n)) :
    (iteratedFDeriv 𝕜 n f x).domDomCongr σ = iteratedFDeriv 𝕜 n f x := by
  ext v
  exact hf.iteratedFDeriv_comp_perm_of_minSmoothness_le hn σ v
