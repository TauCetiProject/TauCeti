/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.Runge.Approximation
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Complex.Wirtinger.Potential

/-!
# The Dolbeault lemma on open subsets of the plane

Let `Ω ⊆ ℂ` be open and let `f : ℂ → W` be `Cⁿ` on `Ω`, for `n ≥ 1`, with values in a complex
Banach space. Then the inhomogeneous Cauchy–Riemann equation `\bar∂ g = f` has a `Cⁿ` solution `g`
on all of `Ω`. Here `\bar∂ g` is the conjugate Wirtinger derivative
`TauCeti.conjWirtingerDeriv g z 1 = (∂ₓ g + i ∂ᵧ g) / 2`. No connectedness, boundedness or
topological condition on `Ω` is needed.

Exhaust `Ω` by the compact sets `K k = TauCeti.filledExhaustion Ω k`, each filled in `Ω` and
contained in the interior of the next. Cutting `f` off near `K (k + 1)` and applying the Cauchy
transform gives a solution `h k` of `\bar∂ (h k) = f` on `K (k + 1)`
(`IsCompact.exists_contDiff_conjWirtingerDeriv_apply_one_eq`). These local solutions do not
converge, but consecutive ones differ by a function `h (k + 1) - h k` that is holomorphic on the
interior of `K (k + 1)`, a neighbourhood of `K k`. Since `K k` is filled in `Ω`, Runge's theorem
(`TauCeti.IsRungeCompactPair.exists_differentiableOn_norm_sub_lt`) gives a function `P k`,
holomorphic on all of `Ω`, within `2⁻ᵏ` of that difference on `K k`. The corrected solutions
`h k - ∑_{j < k} P j` then converge on `Ω`: on the interior of `K m` the limit is `h m` plus a
uniform limit of holomorphic functions (`IsOpen.exists_differentiableOn_eqOn_add_tsum`), so it is
`Cⁿ` and has the same `\bar∂` as `h m`, namely `f`.

In the language of Dolbeault cohomology, this says that `H^{0,1}(Ω) = 0` for every open `Ω ⊆ ℂ`:
the structure sheaf of holomorphic functions has no first cohomology on open subsets of the plane.

## Main results

* `IsOpen.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq`: the Dolbeault lemma on an open set
  `Ω ⊆ ℂ`.
* `TauCeti.exists_contDiff_conjWirtingerDeriv_apply_one_eq`: every `Cⁿ` function on the plane is
  `\bar∂` of a `Cⁿ` function, without any support condition.
* `IsOpen.exists_contDiffOn_differentiableOn_sub`: smooth functions `g k` on open sets covering
  an open set `U ⊆ ℂ`, with holomorphic pairwise differences, are all `f` plus a holomorphic
  function for one smooth `f` on `U`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.4.4.
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Lemma 13.1 and Theorem 13.2 (Dolbeault's lemma on discs), and the proof of §14.7.
-/

public section

open Complex Filter Metric Set Topology
open scoped ENNReal

namespace TauCeti

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {n : ℕ∞}

/-- **The Dolbeault lemma on an open subset of the plane.** Let `f` be `Cⁿ`, `n ≥ 1`, on an open
set `Ω ⊆ ℂ`. Then there is a function `g`, `Cⁿ` on `Ω`, with `\bar∂ g = f` on `Ω`. -/
theorem _root_.IsOpen.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq {f : ℂ → W}
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hn : 1 ≤ n) (hf : ContDiffOn ℝ n f Ω) :
    ∃ g : ℂ → W, ContDiffOn ℝ n g Ω ∧ ∀ z ∈ Ω, conjWirtingerDeriv g z 1 = f z := by
  -- The filled exhaustion `K k` of `Ω`, each stage inside the interior of the next.
  set K : ℕ → Set ℂ := filledExhaustion Ω
  have hK_mono : Monotone K := filledExhaustion_monotone Ω
  have hK_int (k : ℕ) : K k ⊆ interior (K (k + 1)) := filledExhaustion_subset_interior_succ Ω k
  -- Local solutions `h k`, with `\bar∂ (h k) = f` on `K (k + 1)`.
  have hloc (k : ℕ) : ∃ h : ℂ → W, ContDiff ℝ n h ∧
      ∀ z ∈ K (k + 1), conjWirtingerDeriv h z 1 = f z :=
    (isCompact_filledExhaustion Ω (k + 1)).exists_contDiff_conjWirtingerDeriv_apply_one_eq hn hΩ
      (filledExhaustion_subset Ω (k + 1)) hf
  choose h hh hh_eq using hloc
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hn).ne'
  have hd (k : ℕ) : Differentiable ℝ (h k) := (hh k).differentiable hn0
  -- Consecutive local solutions differ by a holomorphic function near `K k`.
  have hdiff (k : ℕ) : DifferentiableOn ℂ (h (k + 1) - h k) (interior (K (k + 1))) := fun z hz ↦ by
    refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero
      ((hd (k + 1)).sub (hd k) z)).2 ?_).differentiableWithinAt
    rw [conjWirtingerDeriv_sub (hd (k + 1) z) (hd k z), sub_apply,
      hh_eq (k + 1) z (hK_mono (k + 1).le_succ (interior_subset hz)),
      hh_eq k z (interior_subset hz), sub_self]
  -- Runge corrections `P k`, holomorphic on `Ω` and within `2⁻ᵏ` of the differences on `K k`.
  have happrox (k : ℕ) : ∃ P : ℂ → W, DifferentiableOn ℂ P Ω ∧
      ∀ z ∈ K k, ‖(h (k + 1) - h k) z - P z‖ < (1 / 2 : ℝ) ^ k :=
    (hΩ.isRungeCompactPair_filledExhaustion k).exists_differentiableOn_norm_sub_lt isOpen_interior
      (hK_int k) (hdiff k) (by positivity)
  choose P hP hP_lt using happrox
  -- On the interior of `K m`, the limit is `h m` plus a holomorphic function.
  set G : ℂ → W := fun z ↦ h 0 z + ∑' k, (h (k + 1) - h k - P k) z
  have hkey (m : ℕ) : ∃ R : ℂ → W, DifferentiableOn ℂ R (interior (K m)) ∧
      EqOn G (h m + R) (interior (K m)) :=
    isOpen_interior.exists_differentiableOn_eqOn_add_tsum
      (fun k ↦ (hP k).mono (interior_subset.trans (filledExhaustion_subset Ω m)))
      (fun k hk ↦ (hdiff k).mono (interior_mono (hK_mono (hk.trans k.le_succ))))
      fun k hk z hz ↦ (hP_lt k z (hK_mono hk (interior_subset hz))).le
  -- Every point of `Ω` lies in some `K m`, inside the interior of `K (m + 1)`.
  have hglue := contDiffOn_and_conjWirtingerDeriv_eq_of_locally_eq_add (G := G)
    (n := n) (U := Ω) (v := fun _ : Unit ↦ (1 : ℂ)) (f := fun _ ↦ f) (by exact_mod_cast hn)
    fun z hz ↦ by
      obtain ⟨m, hm⟩ := mem_iUnion.mp (hΩ.iUnion_filledExhaustion.symm ▸ hz : z ∈ ⋃ k, K k)
      obtain ⟨R, hR, hGR⟩ := hkey (m + 1)
      exact ⟨interior (K (m + 1)), isOpen_interior, hK_int m hm, h (m + 1), R,
        (hh (m + 1)).contDiffOn,
        fun w hw _ ↦ hh_eq (m + 1) w (hK_mono (m + 1).le_succ (interior_subset hw)),
        hR.contDiffOn isOpen_interior, hGR⟩
  exact ⟨G, hglue.1, fun z hz ↦ hglue.2 z hz ()⟩

/-- **The Dolbeault lemma on the plane.** Every `Cⁿ` function `f : ℂ → W`, `n ≥ 1`, is `\bar∂ g`
for a `Cⁿ` function `g`; no support condition on `f` is needed. -/
theorem exists_contDiff_conjWirtingerDeriv_apply_one_eq {f : ℂ → W} (hn : 1 ≤ n)
    (hf : ContDiff ℝ n f) :
    ∃ g : ℂ → W, ContDiff ℝ n g ∧ ∀ z, conjWirtingerDeriv g z 1 = f z := by
  obtain ⟨g, hg, hgf⟩ :=
    isOpen_univ.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq hn hf.contDiffOn
  exact ⟨g, contDiffOn_univ.1 hg, fun z ↦ hgf z (mem_univ z)⟩

/-! ### Smooth data with holomorphic differences

Smooth functions `g k` on open sets `Ω k ⊆ ℂ` whose pairwise differences are holomorphic have
conjugate Wirtinger derivatives that agree on overlaps. On an open set `U` covered by the `Ω k`
these glue to one smooth function, and the Dolbeault lemma solves for it: some smooth `f` on `U`
has every `f - g k` holomorphic. -/

/-- **Smooth data with holomorphic differences glue on an open set.** Let `g k` be smooth on open
sets `Ω k` covering an open set `U ⊆ ℂ`, with `g k - g l` complex differentiable on `Ω k ∩ Ω l`.
Then some `f`, smooth on `U`, has `f - g k` complex differentiable on `U ∩ Ω k` for every `k`. -/
theorem _root_.IsOpen.exists_contDiffOn_differentiableOn_sub {U : Set ℂ} (hU : IsOpen U)
    {ι : Type*} {Ω : ι → Set ℂ} {g : ι → ℂ → W} (hΩ : ∀ k, IsOpen (Ω k))
    (hg : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (g k) (Ω k))
    (hgg : ∀ k l, DifferentiableOn ℂ (g k - g l) (Ω k ∩ Ω l))
    (hcov : U ⊆ ⋃ k, Ω k) :
    ∃ f : ℂ → W, ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      ∀ k, DifferentiableOn ℂ (f - g k) (U ∩ Ω k) := by
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
  have hθs : ContDiffOn ℝ (⊤ : ℕ∞) θ U := by
    refine contDiffOn_of_locally_contDiffOn fun z hz ↦ ?_
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov hz)
    refine ⟨Ω k, hΩ k, hk, ?_⟩
    refine (((hg k).conjWirtingerDeriv_apply_of_isOpen (hΩ k) (by simp) 1).mono
      inter_subset_right).congr ?_
    exact fun w hw ↦ hθ k hw.2
  obtain ⟨f, hf, hfθ⟩ :=
    hU.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq (n := ⊤) le_top hθs
  refine ⟨f, hf, fun k z hz ↦ ?_⟩
  have hfd : DifferentiableAt ℝ f z :=
    (hf.contDiffAt (hU.mem_nhds hz.1)).differentiableAt (by simp)
  have hd : DifferentiableAt ℝ (f - g k) z := hfd.sub (hgd k hz.2)
  refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero hd).2 ?_)
    |>.differentiableWithinAt
  rw [conjWirtingerDeriv_sub hfd (hgd k hz.2), sub_apply, hfθ z hz.1,
    hθ k hz.2, sub_self]

end TauCeti
