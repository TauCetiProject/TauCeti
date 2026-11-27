/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Orders of vanishing of products

A function vanishes to order `m` at `x` when its iterated derivatives of every order `i < m`
vanish at `x`. By the Leibniz rule, orders of vanishing add under multiplication: if `g` vanishes
to order `m` and `h` to order `n` at `x`, then `g * h` vanishes to order `m + n` at `x`. This is
the analytic half of the identification of the powers of the ideal of functions vanishing at a
point with the functions whose jets vanish there.

The same holds for the application `f y (g y)` of a family of continuous linear maps to a family
of vectors. Applied repeatedly through currying, it shows that a smooth family of multilinear maps
evaluated on `k` copies of the increment `y - x` vanishes to order `k` at `x`, the form in which
the remainder of Taylor's formula enters the coefficients of a local operator.

In particular a product `f₁ ⋯ fᵣ • u` of `r` functions vanishing at `x` with a map `u` vanishes to
order `r` at `x` (`TauCeti.iteratedFDeriv_prod_smul_eq_zero_of_lt`).
-/

public section

namespace TauCeti

variable {𝕜 E F G A : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedRing A] [NormedAlgebra 𝕜 A]

/-- **Orders of vanishing add under application.** If the iterated derivatives of a family of
continuous linear maps `f` of order `i < m` and those of `g` of order `i < n` vanish at `x`, then
so do those of `y ↦ f y (g y)` of every order `k < m + n`. -/
theorem iteratedFDeriv_clm_apply_eq_zero_of_lt_add {f : E → F →L[𝕜] G} {g : E → F}
    {N : WithTop ℕ∞} {x : E} (hf : ContDiffAt 𝕜 N f x) (hg : ContDiffAt 𝕜 N g x) {m n k : ℕ}
    (hfx : ∀ i < m, iteratedFDeriv 𝕜 i f x = 0) (hgx : ∀ i < n, iteratedFDeriv 𝕜 i g x = 0)
    (hk : k < m + n) (hkN : k ≤ N) :
    iteratedFDeriv 𝕜 k (fun y ↦ f y (g y)) x = 0 := by
  -- Work on an open neighbourhood of `x` on which both factors are `C^k`.
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn hkN (by simp)
  obtain ⟨v, hv, hgv⟩ := hg.contDiffOn hkN (by simp)
  obtain ⟨s, hsuv, hs, hxs⟩ := mem_nhds_iff.mp (Filter.inter_mem hu hv)
  have hbound := norm_iteratedFDerivWithin_clm_apply (hfu.mono fun _ hy ↦ (hsuv hy).1)
    (hgv.mono fun _ hy ↦ (hsuv hy).2) hs.uniqueDiffOn hxs le_rfl
  simp only [iteratedFDerivWithin_of_isOpen _ hs hxs] at hbound
  refine norm_le_zero_iff.mp (hbound.trans ?_)
  -- Each Leibniz term has a factor `D^i f x` with `i < m` or `D^(k-i) g x` with `k - i < n`.
  refine (Finset.sum_eq_zero fun i hi ↦ ?_).le
  rw [Finset.mem_range] at hi
  rcases lt_or_ge i m with him | him
  · simp [hfx i him]
  · simp [hgx (k - i) (by omega)]

/-- **Orders of vanishing add under multiplication.** If the iterated derivatives of `g` of order
`i < m` and those of `h` of order `i < n` vanish at `x`, then so do those of `g * h` of every
order `k < m + n`. -/
theorem iteratedFDeriv_mul_eq_zero_of_lt_add {g h : E → A} {N : WithTop ℕ∞} {x : E}
    (hg : ContDiffAt 𝕜 N g x) (hh : ContDiffAt 𝕜 N h x) {m n k : ℕ}
    (hgx : ∀ i < m, iteratedFDeriv 𝕜 i g x = 0) (hhx : ∀ i < n, iteratedFDeriv 𝕜 i h x = 0)
    (hk : k < m + n) (hkN : k ≤ N) :
    iteratedFDeriv 𝕜 k (fun y ↦ g y * h y) x = 0 := by
  -- The product is the application of the left multiplications `y ↦ (g y * ·)` to `h`, and
  -- these vanish to the same order as `g`, up to the order `k` that matters.
  let L := ContinuousLinearMap.mul 𝕜 A
  refine iteratedFDeriv_clm_apply_eq_zero_of_lt_add (f := L ∘ g) (m := min m (k + 1))
    (L.contDiff.contDiffAt.comp x hg) hh (fun i hi ↦ ?_) hhx (by omega) hkN
  rw [L.iteratedFDeriv_comp_left hg (le_trans (by exact_mod_cast (by omega : i ≤ k)) hkN),
    hgx i (by omega)]
  ext
  simp

/-- **A multilinear map on `k` copies of the increment vanishes to order `k`.** If the iterated
derivatives of a family `S` of continuous `k`-multilinear maps of order `i < m` vanish at `x`, then
so do those of `y ↦ S y (y - x, …, y - x)` of every order `n < m + k`. -/
theorem iteratedFDeriv_apply_sub_eq_zero_of_lt_add {N : WithTop ℕ∞} {x : E} :
    ∀ {k : ℕ} {S : E → E [×k]→L[𝕜] F}, ContDiffAt 𝕜 N S x → ∀ {m n : ℕ},
      (∀ i < m, iteratedFDeriv 𝕜 i S x = 0) → n < m + k → n ≤ N →
        iteratedFDeriv 𝕜 n (fun y ↦ S y fun _ ↦ y - x) x = 0
  | 0, S, hS, _, n, hSx, hn, hnN => by
    -- With no slots, `S y` is evaluated on the empty tuple, a continuous linear image of `S y`.
    have h : (fun y ↦ S y fun _ ↦ y - x) =
        ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin 0 ↦ E) F (fun _ ↦ x) ∘ S := by
      ext y
      exact congrArg (S y) (Subsingleton.elim _ _)
    rw [h, ContinuousLinearMap.iteratedFDeriv_comp_left _ hS hnN, hSx n (by omega)]
    ext
    simp
  | k + 1, S, hS, m, n, hSx, hn, hnN => by
    -- Curry off the first slot: `S y (y - x, …) = S' y (y - x, …)` with `S' y = S y (y - x, ·)`,
    -- which vanishes to one more order than `S`, up to the order `n` that matters. The spaces of
    -- the currying isometry are given explicitly: unifying them against the instances it carries
    -- otherwise fails.
    have hL : ContDiff 𝕜 N (fun A : E [×k + 1]→L[𝕜] F ↦ A.curryLeft) :=
      LinearIsometryEquiv.contDiff (𝕜 := 𝕜) (E := E [×k + 1]→L[𝕜] F)
        (F := E →L[𝕜] E [×k]→L[𝕜] F)
        (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) ↦ E) F)
    let S' : E → E [×k]→L[𝕜] F := fun y ↦ (S y).curryLeft (y - x)
    have hLS : ContDiffAt 𝕜 N (fun y ↦ (S y).curryLeft) x := hL.contDiffAt.comp x hS
    have hsub : ContDiffAt 𝕜 N (fun y : E ↦ y - x) x := contDiffAt_id.sub contDiffAt_const
    have hS'x : ∀ i < min m n + 1, iteratedFDeriv 𝕜 i S' x = 0 := fun i hi ↦
      iteratedFDeriv_clm_apply_eq_zero_of_lt_add (n := 1) hLS hsub
        (fun j hj ↦ by
          have h := LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := 𝕜)
            (F := E [×k + 1]→L[𝕜] F) (G := E →L[𝕜] E [×k]→L[𝕜] F)
            (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) ↦ E) F) S x j
          rw [hSx j (by omega), norm_zero, norm_eq_zero] at h
          exact h)
        (fun j hj ↦ by
          obtain rfl : j = 0 := by omega
          ext
          simp) hi
        (le_trans (by exact_mod_cast (by omega : i ≤ n)) hnN)
    have h : (fun y ↦ S y fun _ ↦ y - x) = fun y ↦ S' y fun _ ↦ y - x := by
      ext y
      rw [ContinuousMultilinearMap.curryLeft_apply]
      exact congrArg (S y) (funext fun i ↦ by cases i using Fin.cases <;> rfl)
    rw [h]
    exact iteratedFDeriv_apply_sub_eq_zero_of_lt_add (hLS.clm_apply hsub) hS'x (by omega) hnN

/-- **Orders of vanishing of a product.** A product `f₁ ⋯ fᵣ • u` of `r` functions vanishing at `x`
with a map `u`, all `C^r` at `x`, has vanishing derivatives of every order below `r` at `x`. -/
theorem iteratedFDeriv_prod_smul_eq_zero_of_lt {r : ℕ} {f : Fin r → E → 𝕜} {u : E → F} {x : E}
    (hf : ∀ i, ContDiffAt 𝕜 r (f i) x) (hu : ContDiffAt 𝕜 r u x) (hfx : ∀ i, f i x = 0) {k : ℕ}
    (hk : k < r) :
    iteratedFDeriv 𝕜 k (fun y ↦ (∏ i, f i y) • u y) x = 0 := by
  induction r generalizing k with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ r ih =>
    -- Split off the first factor, which vanishes to order `1`, from the rest, which vanishes to
    -- order `r` by induction.
    have hle : (r : WithTop ℕ∞) ≤ ((r + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast Nat.le_succ r
    have hfun : (fun y ↦ (∏ i, f i y) • u y) =
        fun y ↦ (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] F →L[𝕜] F) (f 0 y)
          ((∏ i : Fin r, f i.succ y) • u y) := by
      funext y
      rw [Fin.prod_univ_succ, mul_smul, ContinuousLinearMap.lsmul_apply]
    have hrest : ContDiffAt 𝕜 r (fun y ↦ (∏ i : Fin r, f i.succ y) • u y) x :=
      (contDiffAt_prod fun i _ ↦ (hf i.succ).of_le hle).smul (hu.of_le hle)
    rw [hfun]
    refine iteratedFDeriv_clm_apply_eq_zero_of_lt_add (m := 1) (n := r)
      (((ContinuousLinearMap.lsmul 𝕜 𝕜).contDiff.contDiffAt.comp x (hf 0)).of_le hle)
      hrest (fun i hi ↦ ?_)
      (fun i hi ↦ ih (fun j ↦ (hf j.succ).of_le hle) (hu.of_le hle) (fun j ↦ hfx j.succ) hi)
      (show k < 1 + r by omega) (by exact_mod_cast Nat.lt_succ_iff.mp hk)
    obtain rfl : i = 0 := by omega
    ext
    simp [hfx]

end TauCeti
