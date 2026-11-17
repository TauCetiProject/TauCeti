/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import TauCeti.Analysis.Complex.Wirtinger.OpenSet

/-!
# The Dolbeault lemma on discs and the plane

Let `D ⊆ ℂ` be an open disc of radius `R ≤ ∞` and let `f : ℂ → W` be `Cⁿ` on `D`, for `n ≥ 1`, with
values in a complex Banach space. Then the inhomogeneous Cauchy–Riemann equation `\bar∂ g = f` has
a `Cⁿ` solution `g` on all of `D`. Here `\bar∂ g` is the conjugate Wirtinger derivative
`TauCeti.conjWirtingerDeriv g z 1 = (∂ₓ g + i ∂ᵧ g) / 2`.

All three statements are immediate specializations of global `\bar∂` solvability on arbitrary open
subsets of `ℂ` (`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq`). This is the local
`\bar∂`-lemma behind the vanishing of `H¹(D, 𝒪)` on discs, which makes discs acyclic for the
structure sheaf of a Riemann surface.

## Main results

* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball`: the Dolbeault lemma on a
  disc `Metric.eball c R`, `R ≤ ∞`.
* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_ball`: the same for a disc of
  real radius.
* `TauCeti.exists_contDiff_conjWirtingerDeriv_apply_one_eq`: every `Cⁿ` function on the plane is
  `\bar∂` of a `Cⁿ` function, without any support condition.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Lemma 13.1 and Theorem 13.2 (Dolbeault's lemma).
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.4.4.
-/

public section

open Complex Metric
open scoped ENNReal

namespace TauCeti

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {n : ℕ∞}

/-- **The Dolbeault lemma on a disc.** Let `f` be `Cⁿ`, `n ≥ 1`, on the open disc `eball c R`
of radius `R ≤ ∞`. Then there is a function `g`, `Cⁿ` on the disc, with `\bar∂ g = f` on the
disc. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball {f : ℂ → W} {c : ℂ}
    {R : ℝ≥0∞} (hn : 1 ≤ n) (hf : ContDiffOn ℝ n f (eball c R)) :
    ∃ g : ℂ → W, ContDiffOn ℝ n g (eball c R) ∧
      ∀ z ∈ eball c R, conjWirtingerDeriv g z 1 = f z :=
  exists_contDiffOn_conjWirtingerDeriv_apply_one_eq hn isOpen_eball hf

/-- **The Dolbeault lemma on a disc of real radius.** If `f` is `Cⁿ`, `n ≥ 1`, on `ball c R`,
there is a function `g`, `Cⁿ` on `ball c R`, with `\bar∂ g = f` there. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_ball {f : ℂ → W} {c : ℂ} {R : ℝ}
    (hn : 1 ≤ n) (hf : ContDiffOn ℝ n f (ball c R)) :
    ∃ g : ℂ → W, ContDiffOn ℝ n g (ball c R) ∧
      ∀ z ∈ ball c R, conjWirtingerDeriv g z 1 = f z := by
  rw [← eball_ofReal] at hf ⊢
  exact exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball hn hf

/-- **The Dolbeault lemma on the plane.** Every `Cⁿ` function `f : ℂ → W`, `n ≥ 1`, is `\bar∂ g`
for a `Cⁿ` function `g`; no support condition on `f` is needed. -/
theorem exists_contDiff_conjWirtingerDeriv_apply_one_eq {f : ℂ → W} (hn : 1 ≤ n)
    (hf : ContDiff ℝ n f) :
    ∃ g : ℂ → W, ContDiff ℝ n g ∧ ∀ z, conjWirtingerDeriv g z 1 = f z := by
  obtain ⟨g, hg, hgf⟩ := exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball
    (c := 0) (R := ⊤) hn (by simpa using hf.contDiffOn)
  exact ⟨g, contDiffOn_univ.1 (by simpa using hg), fun z ↦ hgf z (by simp)⟩

end TauCeti
