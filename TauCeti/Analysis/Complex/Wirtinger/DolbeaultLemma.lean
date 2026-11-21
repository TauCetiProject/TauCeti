/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
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
* `TauCeti.exists_contDiffOn_differentiableOn_sub_of_eball`: smooth functions `g k` on open sets
  covering a disc `Metric.eball c R`, `R ≤ ∞`, with holomorphic pairwise differences, are all `f`
  plus a holomorphic function for one smooth `f` on the disc.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Lemma 13.1 and Theorem 13.2 (Dolbeault's lemma), and the proof of §14.7.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.4.4.
-/

public section

open Complex Filter Metric Set Topology
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

/-! ### Smooth data with holomorphic differences

Smooth functions `g k` on open sets `Ω k ⊆ ℂ` whose pairwise differences are holomorphic have
conjugate Wirtinger derivatives that agree on overlaps. On a disc covered by the `Ω k` these glue
to one smooth function, and the Dolbeault lemma solves for it: some smooth `f` on the disc has
every `f - g k` holomorphic. -/

/-- **Smooth data with holomorphic differences glue on a disc.** Let `g k` be smooth on open sets
`Ω k` covering the disc `eball c R`, `R ≤ ∞`, with `g k - g l` complex differentiable on
`Ω k ∩ Ω l`. Then some `f`, smooth on the disc, has `f - g k` complex differentiable on
`eball c R ∩ Ω k` for every `k`. -/
theorem exists_contDiffOn_differentiableOn_sub_of_eball {ι : Type*} {Ω : ι → Set ℂ}
    {g : ι → ℂ → W} {c : ℂ} {R : ℝ≥0∞} (hΩ : ∀ k, IsOpen (Ω k))
    (hg : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (g k) (Ω k))
    (hgg : ∀ k l, DifferentiableOn ℂ (g k - g l) (Ω k ∩ Ω l))
    (hcov : eball c R ⊆ ⋃ k, Ω k) :
    ∃ f : ℂ → W, ContDiffOn ℝ (⊤ : ℕ∞) f (eball c R) ∧
      ∀ k, DifferentiableOn ℂ (f - g k) (eball c R ∩ Ω k) := by
  classical
  -- The real differentiability of `g k` at points of `Ω k`.
  have hgd (k : ι) {z : ℂ} (hz : z ∈ Ω k) : DifferentiableAt ℝ (g k) z :=
    ((hg k).contDiffAt ((hΩ k).mem_nhds hz)).differentiableAt (by simp)
  -- `\bar∂ (g k)` and `\bar∂ (g l)` agree on `Ω k ∩ Ω l`.
  have hagree (k l : ι) {z : ℂ} (hk : z ∈ Ω k) (hl : z ∈ Ω l) :
      conjWirtingerDeriv (g k) z 1 = conjWirtingerDeriv (g l) z 1 := by
    have hkl : DifferentiableAt ℂ (g k - g l) z :=
      (hgg k l).differentiableAt (((hΩ k).inter (hΩ l)).mem_nhds ⟨hk, hl⟩)
    have := congrArg (· 1) hkl.conjWirtingerDeriv_eq_zero
    simp only [conjWirtingerDeriv_sub (hgd k hk) (hgd l hl)] at this
    simpa [sub_eq_zero] using this
  -- The glued datum: `\bar∂` of any `g k` defined at the point.
  let θ : ℂ → W := fun z ↦
    if h : ∃ k, z ∈ Ω k then conjWirtingerDeriv (g h.choose) z 1 else 0
  have hθ (k : ι) {z : ℂ} (hz : z ∈ Ω k) : θ z = conjWirtingerDeriv (g k) z 1 := by
    have h : ∃ k, z ∈ Ω k := ⟨k, hz⟩
    simp only [θ, h, ↓reduceDIte]
    exact hagree _ _ h.choose_spec hz
  have hθs : ContDiffOn ℝ (⊤ : ℕ∞) θ (eball c R) := by
    refine contDiffOn_of_locally_contDiffOn fun z hz ↦ ?_
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov hz)
    refine ⟨Ω k, hΩ k, hk, ?_⟩
    refine (((hg k).conjWirtingerDeriv_apply_of_isOpen (hΩ k) (by simp) 1).mono
      inter_subset_right).congr ?_
    exact fun w hw ↦ hθ k hw.2
  obtain ⟨f, hf, hfθ⟩ := exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_eball
    (n := ⊤) le_top hθs
  refine ⟨f, hf, fun k z hz ↦ ?_⟩
  have hfd : DifferentiableAt ℝ f z :=
    (hf.contDiffAt (isOpen_eball.mem_nhds hz.1)).differentiableAt (by simp)
  have hd : DifferentiableAt ℝ (f - g k) z := hfd.sub (hgd k hz.2)
  refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero hd).2 ?_)
    |>.differentiableWithinAt
  rw [conjWirtingerDeriv_sub hfd (hgd k hz.2), sub_apply, hfθ z hz.1,
    hθ k hz.2, sub_self]

end TauCeti
