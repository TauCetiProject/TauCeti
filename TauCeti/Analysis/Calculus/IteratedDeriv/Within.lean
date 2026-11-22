/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Derivatives of iterated derivatives within a set

At a point `x` with `s ∈ 𝓝 x`, the `k`-th iterated derivative within `s` of a function that is
`C^n` with `k < n` has an ordinary derivative at `x`, namely the `(k+1)`-th iterated derivative
within `s`. This upgrades
Mathlib's `ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin` to a `HasDerivAt`
statement with an explicit derivative.

For a `NormedAlgebra 𝕜 𝕜'` and a `C^n` function `f : 𝕜' → E` on a set `s` with unique
`𝕜'`-derivatives (possibly with boundary, such as a closed vertical strip in `ℂ`), this file also
computes the `𝕜`-derivatives along affine lines `t ↦ z₀ + t • d` mapped into `s`, and shows that a
continuous `𝕜`-linear map vanishing on `f (z₀ + t • d)` for `t ∈ I` vanishes on every
`d ^ k • iteratedDerivWithin k f s (z₀ + x • d)` (`k ≤ n`, `x ∈ I`).

## Main declarations

* `ContDiffWithinAt.hasDerivAt_iteratedDerivWithin`: the pointwise statement.
* `ContDiffOn.hasDerivAt_iteratedDerivWithin`: the same, from smoothness on all of `s`.
* `ContDiffOn.hasDerivWithinAt_pow_smul_iteratedDerivWithin_add_smul`: one-step `𝕜`-derivative of
  `t ↦ d ^ k • iteratedDerivWithin k f s (z₀ + t • d)` along a line inside `s`.
* `ContDiffOn.iteratedDerivWithin_comp_add_smul` and `ContDiffOn.iteratedDeriv_comp_add_smul`:
  `k`-th `𝕜`-iterated derivative of `t ↦ f (z₀ + t • d)` along a line inside `s`.
* `ContDiffOn.map_pow_smul_iteratedDerivWithin_eq_zero`: vanishing of a continuous `𝕜`-linear map
  on `f` along a line propagates to all `d ^ k • iteratedDerivWithin k f s` (`k ≤ n`).

For the plain fundamental-theorem identity on a compact interval use Mathlib's
`intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc` together with
`iteratedDerivWithin_one`.
-/

public section

open Set
open scoped ContDiff Topology

section Interior

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {g : 𝕜 → E} {s : Set 𝕜} {x : 𝕜} {n : ℕ∞ω} {k : ℕ}

/-- If `g` is `C^n` within `s` at a point `x` with `s ∈ 𝓝 x`, then for `k < n` the `k`-th
iterated derivative within `s` has derivative at `x` equal to the `(k+1)`-th iterated derivative
within `s`. -/
theorem ContDiffWithinAt.hasDerivAt_iteratedDerivWithin (hg : ContDiffWithinAt 𝕜 n g s x)
    (hk : k < n) (hx : s ∈ 𝓝 x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x := by
  -- Near `x` the set `s` agrees with its interior, which is open and so uniquely differentiable.
  have hu : interior s ∈ 𝓝 x := interior_mem_nhds.2 hx
  have hev (j : ℕ) : iteratedDerivWithin j g s =ᶠ[𝓝 x] iteratedDerivWithin j g (interior s) := by
    have hset : s =ᶠ[𝓝 x] interior s := by
      filter_upwards [hu] with y hy
      exact ⟨fun _ => hy, fun _ => interior_subset hy⟩
    filter_upwards [iteratedFDerivWithin_eventually_congr_set (𝕜 := 𝕜) (f := g) hset j] with y hy
    simp only [iteratedDerivWithin_eq_iteratedFDerivWithin, hy]
  have h : HasDerivAt (iteratedDerivWithin k g (interior s))
      (iteratedDerivWithin (k + 1) g (interior s) x) x := by
    rw [iteratedDerivWithin_succ]
    exact ((hg.mono interior_subset).differentiableWithinAt_iteratedDerivWithin hk
      (by
        rw [insert_eq_of_mem (mem_of_mem_nhds hu)]
        exact isOpen_interior.uniqueDiffOn)
      ).hasDerivWithinAt.hasDerivAt hu
  rw [(hev (k + 1)).eq_of_nhds]
  exact h.congr_of_eventuallyEq (hev k)

/-- If `g` is `C^n` on `s` and `s ∈ 𝓝 x`, then for `k < n` the `k`-th iterated derivative within
`s` has derivative at `x` equal to the `(k+1)`-th iterated derivative within `s`. -/
theorem ContDiffOn.hasDerivAt_iteratedDerivWithin (hg : ContDiffOn 𝕜 n g s) (hk : k < n)
    (hx : s ∈ 𝓝 x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x :=
  (hg x (mem_of_mem_nhds hx)).hasDerivAt_iteratedDerivWithin hk hx

end Interior

section NormedAlgebra

variable {𝕜 𝕜' E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Along an affine line `t ↦ z₀ + t • d` mapping `I : Set 𝕜` into a uniquely `𝕜'`-differentiable
set `s : Set 𝕜'`, differentiating `t ↦ d ^ k • iteratedDerivWithin k f s (z₀ + t • d)` within `I`
yields `d ^ (k + 1) • iteratedDerivWithin (k + 1) f s (z₀ + x • d)` for any `k < n`. -/
theorem ContDiffOn.hasDerivWithinAt_pow_smul_iteratedDerivWithin_add_smul {f : 𝕜' → E}
    {s : Set 𝕜'} {I : Set 𝕜} {z₀ d : 𝕜'} {n : ℕ∞ω} {k : ℕ} {x : 𝕜}
    (hf : ContDiffOn 𝕜' n f s) (hs : UniqueDiffOn 𝕜' s) (hk : (k : ℕ∞ω) < n)
    (hmaps : MapsTo (fun t : 𝕜 => z₀ + t • d) I s) (hx : x ∈ I) :
    HasDerivWithinAt (fun t : 𝕜 => d ^ k • iteratedDerivWithin k f s (z₀ + t • d))
      (d ^ (k + 1) • iteratedDerivWithin (k + 1) f s (z₀ + x • d)) I x := by
  have h1 : HasDerivWithinAt (iteratedDerivWithin k f s)
      (iteratedDerivWithin (k + 1) f s (z₀ + x • d)) s (z₀ + x • d) := by
    rw [iteratedDerivWithin_succ]
    exact (hf.differentiableOn_iteratedDerivWithin hk hs (z₀ + x • d) (hmaps hx)).hasDerivWithinAt
  have hline : HasDerivWithinAt (fun t : 𝕜 => z₀ + t • d) d I x := by
    simpa only [one_smul] using (((hasDerivAt_id' x).smul_const d).const_add z₀).hasDerivWithinAt
  have hcomp : HasDerivWithinAt (fun t : 𝕜 => iteratedDerivWithin k f s (z₀ + t • d))
      (d • iteratedDerivWithin (k + 1) f s (z₀ + x • d)) I x := by
    simpa only [Function.comp_def] using h1.scomp x hline hmaps
  have hsmul : HasDerivWithinAt (fun t : 𝕜 => d ^ k • iteratedDerivWithin k f s (z₀ + t • d))
      (d ^ k • (d • iteratedDerivWithin (k + 1) f s (z₀ + x • d))) I x :=
    ContinuousLinearMap.lsmul 𝕜' 𝕜' (E := E) (d ^ k) |>.restrictScalars 𝕜
      |>.hasFDerivAt.comp_hasDerivWithinAt x hcomp
  simpa only [smul_smul, ← pow_succ] using hsmul

/-- Formula for the `k`-th iterated derivative within `I` of `t ↦ f (z₀ + t • d)` along a line
mapped into a uniquely `𝕜'`-differentiable set `s`. -/
theorem ContDiffOn.iteratedDerivWithin_comp_add_smul {f : 𝕜' → E} {s : Set 𝕜'} {I : Set 𝕜}
    {z₀ d : 𝕜'} {n : ℕ∞ω} (hf : ContDiffOn 𝕜' n f s) (hs : UniqueDiffOn 𝕜' s)
    (hI : UniqueDiffOn 𝕜 I) (hmaps : MapsTo (fun t : 𝕜 => z₀ + t • d) I s) :
    ∀ {k : ℕ}, (k : ℕ∞ω) ≤ n → ∀ {x : 𝕜}, x ∈ I →
      iteratedDerivWithin k (fun t : 𝕜 => f (z₀ + t • d)) I x =
        d ^ k • iteratedDerivWithin k f s (z₀ + x • d)
  | 0, _, _, _ => by simp
  | k + 1, hk, x, hx => by
    have hk_lt : (k : ℕ∞ω) < n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self k) hk
    have ih : EqOn (iteratedDerivWithin k (fun t : 𝕜 => f (z₀ + t • d)) I)
        (fun t : 𝕜 => d ^ k • iteratedDerivWithin k f s (z₀ + t • d)) I :=
      fun _ ht => hf.iteratedDerivWithin_comp_add_smul hs hI hmaps hk_lt.le ht
    rw [iteratedDerivWithin_succ]
    exact ((hf.hasDerivWithinAt_pow_smul_iteratedDerivWithin_add_smul hs hk_lt hmaps
      hx).congr ih (ih hx)).derivWithin (hI x hx)

/-- Formula for the `k`-th ordinary iterated derivative of `t ↦ f (z₀ + t • d)` along a line
contained in a uniquely `𝕜'`-differentiable set `s`. -/
theorem ContDiffOn.iteratedDeriv_comp_add_smul {f : 𝕜' → E} {s : Set 𝕜'} {z₀ d : 𝕜'} {n : ℕ∞ω}
    (hf : ContDiffOn 𝕜' n f s) (hs : UniqueDiffOn 𝕜' s) (hmem : ∀ t : 𝕜, z₀ + t • d ∈ s)
    {k : ℕ} (hk : (k : ℕ∞ω) ≤ n) (x : 𝕜) :
    iteratedDeriv k (fun t : 𝕜 => f (z₀ + t • d)) x =
      d ^ k • iteratedDerivWithin k f s (z₀ + x • d) := by
  rw [← iteratedDerivWithin_univ]
  exact hf.iteratedDerivWithin_comp_add_smul hs uniqueDiffOn_univ (fun t _ => hmem t) hk
    (mem_univ x)

/-- If a continuous `𝕜`-linear map `L : E →L[𝕜] F` vanishes on `f (z₀ + t • d)` for all `t ∈ I`,
where `I` has unique `𝕜`-derivatives and maps into a uniquely `𝕜'`-differentiable set `s` on which
`f` is `C^n`, then `L` vanishes on every `d ^ k • iteratedDerivWithin k f s (z₀ + x • d)` for
`k ≤ n` and `x ∈ I`. -/
theorem ContDiffOn.map_pow_smul_iteratedDerivWithin_eq_zero {f : 𝕜' → E} {s : Set 𝕜'} {I : Set 𝕜}
    {z₀ d : 𝕜'} {n : ℕ∞ω} (hf : ContDiffOn 𝕜' n f s) (hs : UniqueDiffOn 𝕜' s)
    (hI : UniqueDiffOn 𝕜 I) (hmaps : MapsTo (fun t : 𝕜 => z₀ + t • d) I s) (L : E →L[𝕜] F)
    (hzero : ∀ x ∈ I, L (f (z₀ + x • d)) = 0) :
    ∀ {k : ℕ}, (k : ℕ∞ω) ≤ n → ∀ {x : 𝕜}, x ∈ I →
      L (d ^ k • iteratedDerivWithin k f s (z₀ + x • d)) = 0
  | k, hk, x, hx => by
    have hfline : ContDiffOn 𝕜 n (fun t : 𝕜 => f (z₀ + t • d)) I :=
      (hf.restrict_scalars 𝕜).comp (by fun_prop) hmaps
    rw [← hf.iteratedDerivWithin_comp_add_smul hs hI hmaps hk hx]
    have hcomm : L (iteratedDerivWithin k (fun t : 𝕜 => f (z₀ + t • d)) I x) =
        iteratedDerivWithin k (fun t : 𝕜 => L (f (z₀ + t • d))) I x := by
      simpa only [iteratedDerivWithin_eq_iteratedFDerivWithin,
        ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
        Function.comp_def] using
        congrArg (fun M => M fun _ => (1 : 𝕜))
          (L.iteratedFDerivWithin_comp_left (hfline x hx) hI hx hk).symm
    rw [hcomm, iteratedDerivWithin_congr (fun t ht => hzero t ht) hx,
      iteratedDerivWithin_fun_const_zero]

end NormedAlgebra
