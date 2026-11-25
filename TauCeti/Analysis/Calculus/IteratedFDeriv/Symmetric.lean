/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.GroupTheory.Perm.Fin
import TauCeti.Analysis.Normed.Module.Multilinear.Curry

/-!
# Symmetry of higher iterated derivatives

Over `ℝ` or `ℂ`, the `k`-th iterated derivative of a map which is `C^k` at a point is a
symmetric multilinear map there: permuting its arguments does not change its value. Over other
fields the same holds for analytic maps. As in Mathlib's `ContDiffAt.isSymmSndFDerivAt`, both
cases are covered by the hypothesis `minSmoothness 𝕜 k ≤ n` on a map which is `C^n` at the point.

Mathlib proves the second-order statement for `C^2` maps (`ContDiffAt.isSymmSndFDerivAt`) and the
statement of every order for analytic maps (`ContDiffAt.iteratedFDeriv_comp_perm`). The general
case is deduced from the second-order one by induction on `k`. Every permutation of `Fin (k + 2)`
is a product of the transposition of the first two arguments, which is the symmetry of a second
derivative of the `k`-th derivative, and of permutations fixing the first argument, which act
on the `k + 1` arguments of the derivative of the `k`-th derivative and are handled by the
inductive hypothesis at all points near the base point.

The hypothesis is local: only `C^k` regularity near the point is needed, not on the whole space.
For maps which are `C^k` everywhere over `ℝ` or `ℂ`, the symmetry also follows from
`List.Perm.iteratedFDerivAlong_eq` in `TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList`.
The local form is what identifies the finite jets of local sections, which are smooth only near
the point, with tuples of symmetric multilinear maps.

## Main results

* `ContinuousMultilinearMap.fderiv_apply_comp_perm_of_eventually`: the derivative of a family of
  multilinear maps which are invariant under a permutation near a point is invariant at the point.
* `ContDiffAt.iteratedFDeriv_comp_perm_of_minSmoothness_le`: permuting the arguments of the
  `k`-th iterated derivative of a map which is `C^k` at a point (analytic over other fields) does
  not change its value.
-/

public section

open Equiv Filter Topology
open scoped ContDiff

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {x : E}

/-- The derivative of a family of multilinear maps which are invariant under one permutation of
their arguments near a point is invariant under the same permutation at that point. -/
theorem ContinuousMultilinearMap.fderiv_apply_comp_perm_of_eventually {X ι : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [Finite ι] {a : X}
    {G : X → ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F} (σ : Perm ι)
    (hG : ∀ᶠ y in 𝓝 a, ∀ v : ι → E, G y (v ∘ σ) = G y v) (w : X) (v : ι → E) :
    fderiv 𝕜 G a w (v ∘ σ) = fderiv 𝕜 G a w v := by
  have := Fintype.ofFinite ι
  have hcongr : (ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E F σ) ∘ G =ᶠ[𝓝 a] G :=
    hG.mono fun y hy ↦ by ext v; exact hy v
  have hd := congrArg (fun L ↦ L w v) (hcongr.fderiv_eq (𝕜 := 𝕜))
  simp only [LinearIsometryEquiv.comp_fderiv, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_coe'', ContinuousMultilinearMap.domDomCongrₗᵢ_apply,
    ContinuousMultilinearMap.domDomCongr_apply] at hd
  exact hd

/-- A permutation fixing the first argument preserves the `k + 1`-st iterated derivative when the
`k`-th iterated derivative is symmetric near the point. -/
private theorem iteratedFDeriv_succ_comp_perm_of_apply_zero {k : ℕ}
    (hk : ∀ᶠ y in 𝓝 x, ∀ (v : Fin k → E) (σ : Perm (Fin k)),
      iteratedFDeriv 𝕜 k f y (v ∘ σ) = iteratedFDeriv 𝕜 k f y v)
    (σ : Perm (Fin (k + 1))) (hσ : σ 0 = 0) (v : Fin (k + 1) → E) :
    iteratedFDeriv 𝕜 (k + 1) f x (v ∘ σ) = iteratedFDeriv 𝕜 (k + 1) f x v := by
  obtain ⟨⟨p, e⟩, rfl⟩ := Perm.decomposeFin.symm.surjective σ
  rw [Perm.decomposeFin_symm_apply_zero] at hσ
  subst hσ
  have htail : Fin.tail (v ∘ Perm.decomposeFin.symm (0, e)) = Fin.tail v ∘ e := by
    funext i
    simp [Fin.tail, Perm.decomposeFin_symm_apply_succ]
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left, htail]
  simp only [Function.comp_apply, Perm.decomposeFin_symm_apply_zero]
  exact ContinuousMultilinearMap.fderiv_apply_comp_perm_of_eventually e
    (hk.mono fun y hy v ↦ hy v e) _ _

/-- The transposition of the first two arguments preserves the `k + 2`-nd iterated derivative
of a map whose `k`-th iterated derivative has a symmetric second derivative. -/
private theorem iteratedFDeriv_comp_swap_zero_one {k : ℕ}
    (hf : IsSymmSndFDerivAt 𝕜 (iteratedFDeriv 𝕜 k f) x) (v : Fin (k + 2) → E) :
    iteratedFDeriv 𝕜 (k + 2) f x (v ∘ swap 0 1) = iteratedFDeriv 𝕜 (k + 2) f x v := by
  have key (u : Fin (k + 2) → E) : iteratedFDeriv 𝕜 (k + 2) f x u =
      fderiv 𝕜 (fderiv 𝕜 (iteratedFDeriv 𝕜 k f)) x (u 0) (u 1) (Fin.tail (Fin.tail u)) := by
    -- The spaces are given explicitly: unifying them against the instances carried by the
    -- currying isometry otherwise fails.
    have h := LinearIsometryEquiv.comp_fderiv (𝕜 := 𝕜) (E := E →L[𝕜] E [×k]→L[𝕜] F)
      (F := E [×k + 1]→L[𝕜] F) (G := E)
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) ↦ E) F).symm
      (f := fderiv 𝕜 (iteratedFDeriv 𝕜 k f)) (x := x)
    rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_eq_comp_left, h]
    simp [continuousMultilinearCurryLeftEquiv_symm_apply, Fin.tail]
  have htail : Fin.tail (Fin.tail (v ∘ swap 0 1)) = Fin.tail (Fin.tail v) := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    rw [swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (by simp [Fin.ext_iff])]
  rw [key, key, htail, Function.comp_apply, Function.comp_apply, swap_apply_left,
    swap_apply_right, hf]

/-- Over `ℝ` or `ℂ`, the `k`-th iterated derivative of a map which is `C^k` at a point is
symmetric there. Over other fields, the same holds for analytic maps. -/
theorem ContDiffAt.iteratedFDeriv_comp_perm_of_minSmoothness_le {n : ℕ∞ω} {k : ℕ}
    (hf : ContDiffAt 𝕜 n f x) (hk : minSmoothness 𝕜 k ≤ n) (v : Fin k → E)
    (σ : Perm (Fin k)) :
    iteratedFDeriv 𝕜 k f x (v ∘ σ) = iteratedFDeriv 𝕜 k f x v := by
  induction k generalizing n x with
  | zero => rw [Subsingleton.elim σ 1, Perm.coe_one, Function.comp_id]
  | succ k ih =>
    -- The `k`-th derivative is symmetric at every point near `x`.
    obtain ⟨m, hkm, hmn, hm⟩ := exist_minSmoothness_le_ne_infty hk
    have hnear : ∀ᶠ y in 𝓝 x, ∀ (v : Fin k → E) (σ : Perm (Fin k)),
        iteratedFDeriv 𝕜 k f y (v ∘ σ) = iteratedFDeriv 𝕜 k f y v :=
      ((hf.of_le hmn).eventually hm).mono fun y hy ↦
        ih hy ((minSmoothness_monotone (by simp)).trans hkm)
    have hfix (τ : Perm (Fin (k + 1))) (hτ : τ 0 = 0) (u : Fin (k + 1) → E) :
        iteratedFDeriv 𝕜 (k + 1) f x (u ∘ τ) = iteratedFDeriv 𝕜 (k + 1) f x u :=
      iteratedFDeriv_succ_comp_perm_of_apply_zero hnear τ hτ u
    cases k with
    | zero => rw [Subsingleton.elim (α := Perm (Fin 1)) σ 1, Perm.coe_one, Function.comp_id]
    | succ j =>
      -- The transposition of the first two arguments is the symmetry of a second derivative.
      have hsymm : IsSymmSndFDerivAt 𝕜 (iteratedFDeriv 𝕜 j f) x := by
        refine (hf.iteratedFDeriv_right (m := minSmoothness 𝕜 2) ?_).isSymmSndFDerivAt le_rfl
        rw [← minSmoothness_add]
        exact le_of_eq_of_le (by push_cast; ring_nf) hk
      have hswap01 (u : Fin (j + 2) → E) :
          iteratedFDeriv 𝕜 (j + 2) f x (u ∘ swap 0 1) = iteratedFDeriv 𝕜 (j + 2) f x u :=
        iteratedFDeriv_comp_swap_zero_one hsymm u
      -- Every transposition `swap 0 p` is conjugate to `swap 0 1` by a permutation fixing `0`.
      have hswap (p : Fin (j + 2)) (u : Fin (j + 2) → E) :
          iteratedFDeriv 𝕜 (j + 2) f x (u ∘ swap 0 p) = iteratedFDeriv 𝕜 (j + 2) f x u := by
        by_cases hp0 : p = 0
        · subst hp0
          rw [swap_self, coe_refl, Function.comp_id]
        by_cases hp1 : p = 1
        · subst hp1
          exact hswap01 u
        have h01 : (0 : Fin (j + 2)) ≠ 1 := by simp
        have hfix1 : swap (1 : Fin (j + 2)) p 0 = 0 :=
          swap_apply_of_ne_of_ne h01 (Ne.symm hp0)
        rw [swap_comm, ← swap_mul_swap_mul_swap h01 (Ne.symm hp0), Perm.coe_mul,
          Perm.coe_mul, ← Function.comp_assoc, ← Function.comp_assoc,
          hfix _ hfix1, hswap01, hfix _ hfix1]
      -- Every permutation is a transposition `swap 0 p` followed by one fixing `0`.
      have hσ : σ = swap 0 (σ 0) * (swap 0 (σ 0) * σ) := (swap_mul_self_mul _ _ _).symm
      rw [hσ, Perm.coe_mul, ← Function.comp_assoc,
        hfix _ (by simp [Perm.mul_apply, swap_apply_right]), hswap]
