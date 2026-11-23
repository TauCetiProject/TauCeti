/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Smooth dependence of iterated derivatives on parameters

If `f : X → E → F` is jointly `C^n` near `(x₀, g x₀)` and `g` is `C^m` at `x₀`, then the iterated
derivative `x ↦ D^i (f x) (g x)` of order `i` in the second variable, evaluated along `g`, is
`C^m` at `x₀` as soon as `m + i ≤ n`. This is the iterated form of Mathlib's `ContDiffAt.fderiv`,
the case `i = 1`. It applies, for instance, when both the function being differentiated and the
point of evaluation move with a parameter, as for the derivatives at `x` of a function built from
data attached to `x`.

## Main results

* `ContDiffAt.iteratedFDeriv`: the parametric iterated derivative is `C^m`.
-/

public section

open Function
open scoped ContDiff

variable {𝕜 X E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n m : ℕ∞ω}

/-- The iterated derivative in the second variable of a jointly `C^n` map is jointly `C^m`, when
`m + i ≤ n`. -/
private theorem contDiffAt_iteratedFDeriv_snd {f : X → E → F} {p : X × E}
    (hf : ContDiffAt 𝕜 n (uncurry f) p) {i : ℕ} (hmn : m + i ≤ n) :
    ContDiffAt 𝕜 m (fun q : X × E ↦ iteratedFDeriv 𝕜 i (f q.1) q.2) p := by
  induction i generalizing m with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, comp_apply]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm.contDiff.contDiffAt).comp p
      (hf.of_le (by simpa using hmn))
  | succ i ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left, comp_apply]
    -- Differentiate `w ↦ D^i (f q.1) w` at `q.2`, with the parameter `q`.
    have hih : ContDiffAt 𝕜 (m + 1) (fun q : X × E ↦ iteratedFDeriv 𝕜 i (f q.1) q.2) p :=
      ih (by rw [add_assoc, add_comm (1 : ℕ∞ω)]; exact_mod_cast hmn)
    have hd : ContDiffAt 𝕜 m (fun q : X × E ↦ fderiv 𝕜 (iteratedFDeriv 𝕜 i (f q.1)) q.2) p :=
      ContDiffAt.fderiv (f := fun (q : X × E) (w : E) ↦ iteratedFDeriv 𝕜 i (f q.1) w)
        (hih.comp (p, p.2) (contDiff_fst.fst.prodMk contDiff_snd).contDiffAt) contDiffAt_snd le_rfl
    exact (LinearIsometryEquiv.contDiff _).contDiffAt.comp p hd

/-- **Iterated derivatives depending on a parameter.** If `f : X → E → F` is jointly `C^n` at
`(x₀, g x₀)` and `g` is `C^m` at `x₀`, then `x ↦ D^i (f x) (g x)` is `C^m` at `x₀`, provided
`m + i ≤ n`. -/
protected theorem ContDiffAt.iteratedFDeriv {f : X → E → F} {g : X → E} {x₀ : X} {i : ℕ}
    (hf : ContDiffAt 𝕜 n (uncurry f) (x₀, g x₀)) (hg : ContDiffAt 𝕜 m g x₀) (hmn : m + i ≤ n) :
    ContDiffAt 𝕜 m (fun x ↦ iteratedFDeriv 𝕜 i (f x) (g x)) x₀ :=
  (contDiffAt_iteratedFDeriv_snd (f := f) hf hmn).comp (f := fun x ↦ (x, g x)) x₀
    (contDiffAt_id.prodMk hg)
