/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.Runge.Approximation
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Complex.Wirtinger.Potential
import TauCeti.Logic.Function.Extend

/-!
# Global solutions of the inhomogeneous Cauchy–Riemann equation on open subsets of `ℂ`

Let `Ω ⊆ ℂ` be an arbitrary open set, with no connectivity assumption, and let `f : ℂ → W` be
`Cⁿ` on `Ω`, for `n ≥ 1`, with values in a complex Banach space. Then the inhomogeneous
Cauchy–Riemann equation `\bar∂ g = f` has a `Cⁿ` solution `g` on all of `Ω`
(`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq`). Here `\bar∂ g` is the conjugate
Wirtinger derivative `TauCeti.conjWirtingerDeriv g z 1 = (∂ₓ g + i ∂ᵧ g) / 2`.

The construction exhausts `Ω` by compact sets `K k ⊆ interior (K (k + 1))` that are filled in
`Ω` (`IsOpen.exists_isFilledIn_compact_exhaustion`). Multiplying `f` by a smooth compactly
supported cutoff equal to `1` near `K (k + 1)` and taking its Cauchy transform
(`TauCeti.exists_contDiff_conjWirtingerDeriv_apply_one_eq_of_hasCompactSupport`) produces a
global `Cⁿ` function `h k` solving `\bar∂ (h k) = f` on `K (k + 1)`. Consecutive local solutions
differ by a function holomorphic on `interior (K (k + 1))`
(`TauCeti.differentiableOn_sub_of_conjWirtingerDeriv_eq`). Runge approximation on the Runge
compact pair `(Ω, K k)` (`TauCeti.IsRungeCompactPair.exists_differentiableOn_norm_sub_lt`) yields
a holomorphic correction `P k` on `Ω` within `2⁻ᵏ` of `h (k + 1) - h k` on `K k`. The telescoping
series `h 0 + ∑' k, (h (k + 1) - h k - P k)` differs on `interior (K m)` from `h m` by a uniform
limit of holomorphic functions (`TauCeti.exists_differentiableOn_eqOn_add_tsum`), so it is `Cⁿ` on
`Ω` and solves `\bar∂ g = f` (`TauCeti.contDiffOn_and_conjWirtingerDeriv_eq_of_locally_eq_add`).

Applying global solvability to `∂ f` solves `\bar∂ g = ∂ f`
(`TauCeti.exists_contDiffOn_conjWirtingerDeriv_eq_wirtingerDeriv`), which is the coefficient
condition for the one-form `g dz + f dbar z` to be closed. For smooth functions `g k` on open sets
`Ω k` covering `U` with holomorphic pairwise differences, gluing `\bar∂ (g k)` and solving
`\bar∂ f = θ` yields one smooth `f` on `U` with every `f - g k` holomorphic on `U ∩ Ω k`
(`TauCeti.exists_contDiffOn_differentiableOn_sub`).

## Main results

* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq`: global `Cⁿ` solvability of
  `\bar∂ g = f` on an arbitrary open subset of `ℂ`, for `1 ≤ n : ℕ∞` and Banach-valued data.
* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_eq_wirtingerDeriv`: closed completion
  `\bar∂ g = ∂ f` on an arbitrary open subset of `ℂ`.
* `TauCeti.exists_contDiffOn_differentiableOn_sub`: smooth functions `g k` on open sets covering an
  open set `U ⊆ ℂ` with holomorphic pairwise differences equal `f` minus a holomorphic function for
  one smooth `f` on `U`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 12.2.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.4.4 and §1.4.
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  the proof of §14.7.
-/

public section

open Complex Filter Metric Set Topology
open scoped ContDiff

namespace TauCeti

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Global solvability of `\bar∂ g = f` on an open subset of `ℂ`.** Let `Ω ⊆ ℂ` be an arbitrary
open set, `n ≥ 1`, and let `f : ℂ → W` be `Cⁿ` on `Ω` with values in a complex Banach space.
Then there exists `g : ℂ → W`, `Cⁿ` on `Ω`, such that `conjWirtingerDeriv g z 1 = f z` for
every `z ∈ Ω`. No connectivity hypothesis on `Ω` is required. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eq [CompleteSpace W] {n : ℕ∞}
    {f : ℂ → W} {Ω : Set ℂ} (hn : 1 ≤ n) (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ n f Ω) :
    ∃ g : ℂ → W, ContDiffOn ℝ n g Ω ∧ ∀ z ∈ Ω, conjWirtingerDeriv g z 1 = f z := by
  obtain ⟨K, hKcpt, hKint, hKunion, hKfill⟩ := hΩ.exists_isFilledIn_compact_exhaustion
  have hKΩ (k : ℕ) : K k ⊆ Ω := hKunion ▸ subset_iUnion K k
  have hKmono : Monotone K :=
    monotone_nat_of_le_succ fun k ↦ (hKint k).trans interior_subset
  -- Local solutions `h k` solving `\bar∂ (h k) = f` on `K (k + 1)`.
  have hloc (k : ℕ) : ∃ h : ℂ → W, ContDiff ℝ n h ∧
      ∀ z ∈ K (k + 1), conjWirtingerDeriv h z 1 = f z := by
    obtain ⟨ψ, hψ, -, hψ1, hψc, hψΩ⟩ :=
      (hKcpt (k + 1)).exists_contDiff_cutoff hΩ (hKΩ (k + 1))
    have hcut : ContDiff ℝ n (fun z ↦ ψ z • f z) :=
      hf.contDiff_smul_of_tsupport_subset hΩ (hψ.of_le (by simp)).contDiffOn hψΩ
    obtain ⟨h, hh, hheq⟩ :=
      exists_contDiff_conjWirtingerDeriv_apply_one_eq_of_hasCompactSupport hn hcut hψc.smul_right
    refine ⟨h, hh, fun z hz ↦ ?_⟩
    have hψz : ψ z = 1 := mem_singleton_iff.1 (mem_preimage.1 (interior_subset (hψ1 hz)))
    rw [hheq z, hψz, one_smul]
  choose h hh hh_eq using hloc
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hn).ne'
  have hd (k : ℕ) : Differentiable ℝ (h k) := (hh k).differentiable hn0
  -- Consecutive local solutions differ by a function holomorphic on `interior (K (k + 1))`.
  have hdiff (k : ℕ) : DifferentiableOn ℂ (h (k + 1) - h k) (interior (K (k + 1))) :=
    differentiableOn_sub_of_conjWirtingerDeriv_eq isOpen_interior (hd (k + 1)).differentiableOn
      (hd k).differentiableOn fun z hz ↦ by
        rw [hh_eq (k + 1) z (interior_subset (hKint (k + 1) (interior_subset hz))),
          hh_eq k z (interior_subset hz)]
  -- Approximate each difference within `2⁻ᵏ` on `K k` by a function `P k` holomorphic on `Ω`.
  have happrox (k : ℕ) : ∃ P : ℂ → W, DifferentiableOn ℂ P Ω ∧
      ∀ z ∈ K k, ‖(h (k + 1) - h k) z - P z‖ < (1 / 2 : ℝ) ^ k :=
    (isRungeCompactPair_iff.2 ⟨hΩ, hKcpt k, hKΩ k, hKfill k⟩).exists_differentiableOn_norm_sub_lt
      isOpen_interior (hKint k) (hdiff k) (by positivity)
  choose P hP hP_lt using happrox
  set G : ℂ → W := fun z ↦ h 0 z + ∑' k, (h (k + 1) - h k - P k) z
  have hkey (m : ℕ) : ∃ L : ℂ → W, DifferentiableOn ℂ L (interior (K m)) ∧
      EqOn G (h m + L) (interior (K m)) :=
    exists_differentiableOn_eqOn_add_tsum isOpen_interior summable_geometric_two
      (fun k ↦ (hP k).mono (interior_subset.trans (hKΩ m)))
      (fun k hmk ↦ (hdiff k).mono (interior_subset.trans ((hKmono hmk).trans (hKint k))))
      (fun k hmk z hz ↦ (hP_lt k z (hKmono hmk (interior_subset hz))).le)
  have hglue := contDiffOn_and_conjWirtingerDeriv_eq_of_locally_eq_add (G := G)
    (n := n) (U := Ω) (v := fun _ : Unit ↦ (1 : ℂ)) (f := fun _ ↦ f) (by exact_mod_cast hn)
    fun z hz ↦ by
      obtain ⟨k, hzk⟩ := mem_iUnion.1 (hKunion.symm ▸ hz)
      obtain ⟨L, hL, hGL⟩ := hkey (k + 1)
      exact ⟨interior (K (k + 1)), isOpen_interior, hKint k hzk, h (k + 1), L,
        (hh (k + 1)).contDiffOn,
        fun w hw _ ↦ hh_eq (k + 1) w (interior_subset (hKint (k + 1) (interior_subset hw))),
        hL.contDiffOn isOpen_interior, hGL⟩
  exact ⟨G, hglue.1, fun z hz ↦ hglue.2 z hz ()⟩

/-- **Closed completion on an open subset of `ℂ`.** For every `Cⁿ` function `f : ℂ → W` on an
arbitrary open set `Ω ⊆ ℂ` with `1 ≤ m` and `m + 1 ≤ n`, there exists a `Cᵐ` function
`g : ℂ → W` on `Ω` solving `\bar∂ g = ∂ f` on `Ω`. When `W = ℂ`, this is the coefficient equation
for `g dz + f dbar z` to be closed. -/
theorem exists_contDiffOn_conjWirtingerDeriv_eq_wirtingerDeriv [CompleteSpace W] {m n : ℕ∞}
    {f : ℂ → W} {Ω : Set ℂ} (hm : 1 ≤ m) (hmn : m + 1 ≤ n) (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ n f Ω) :
    ∃ g : ℂ → W, ContDiffOn ℝ m g Ω ∧
      ∀ z ∈ Ω, conjWirtingerDeriv g z 1 = wirtingerDeriv f z 1 := by
  have hwf : ContDiffOn ℝ m (fun z ↦ wirtingerDeriv f z 1) Ω := fun z hz ↦
    ((hf.contDiffAt (hΩ.mem_nhds hz)).wirtingerDeriv_apply (by exact_mod_cast hmn) 1)
      |>.contDiffWithinAt
  exact exists_contDiffOn_conjWirtingerDeriv_apply_one_eq hm hΩ hwf

/-- **Smooth data with holomorphic differences glue on an open subset of `ℂ`.** Let `g k` be
smooth on open sets `Ω k` covering the open set `U ⊆ ℂ`, with `g k - g l` complex differentiable on
`Ω k ∩ Ω l`. Then some `f`, smooth on `U`, has `f - g k` complex differentiable on `U ∩ Ω k` for
every `k`. -/
theorem exists_contDiffOn_differentiableOn_sub [CompleteSpace W] {ι : Type*} {U : Set ℂ}
    {Ω : ι → Set ℂ} {g : ι → ℂ → W} (hU : IsOpen U) (hΩ : ∀ k, IsOpen (Ω k))
    (hg : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (g k) (Ω k))
    (hgg : ∀ k l, DifferentiableOn ℂ (g k - g l) (Ω k ∩ Ω l))
    (hcov : U ⊆ ⋃ k, Ω k) :
    ∃ f : ℂ → W, ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      ∀ k, DifferentiableOn ℂ (f - g k) (U ∩ Ω k) := by
  -- The real differentiability of `g k` at points of `Ω k`.
  have hgd (k : ι) {z : ℂ} (hz : z ∈ Ω k) : DifferentiableAt ℝ (g k) z :=
    ((hg k).contDiffAt ((hΩ k).mem_nhds hz)).differentiableAt (by simp)
  -- `\bar∂ (g k)` and `\bar∂ (g l)` agree on `Ω k ∩ Ω l`.
  have hagree (k l : ι) (z : ℂ) (hk : z ∈ Ω k) (hl : z ∈ Ω l) :
      conjWirtingerDeriv (g k) z 1 = conjWirtingerDeriv (g l) z 1 := by
    have hkl : DifferentiableAt ℂ (g k - g l) z :=
      (hgg k l).differentiableAt (((hΩ k).inter (hΩ l)).mem_nhds ⟨hk, hl⟩)
    have := congrArg (· 1) hkl.conjWirtingerDeriv_eq_zero
    simp only [conjWirtingerDeriv_sub (hgd k hk) (hgd l hl)] at this
    simpa [sub_eq_zero] using this
  -- Glue `\bar∂ (g k)` across the cover and extend by zero outside `⋃ k, Ω k`.
  obtain ⟨θ, hθ, -⟩ :=
    Function.exists_eqOn_of_agree (U := Ω) (f := fun k z ↦ conjWirtingerDeriv (g k) z 1) hagree 0
  have hθs : ContDiffOn ℝ (⊤ : ℕ∞) θ U := by
    refine contDiffOn_of_locally_contDiffOn fun z hz ↦ ?_
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov hz)
    refine ⟨Ω k, hΩ k, hk, ?_⟩
    refine (((hg k).conjWirtingerDeriv_apply_of_isOpen (hΩ k) (by simp) 1).mono
      inter_subset_right).congr ?_
    exact fun w hw ↦ hθ k hw.2
  obtain ⟨f, hf, hfθ⟩ := exists_contDiffOn_conjWirtingerDeriv_apply_one_eq (n := ⊤) le_top hU hθs
  refine ⟨f, hf, fun k z hz ↦ ?_⟩
  have hfd : DifferentiableAt ℝ f z :=
    (hf.contDiffAt (hU.mem_nhds hz.1)).differentiableAt (by simp)
  have hd : DifferentiableAt ℝ (f - g k) z := hfd.sub (hgd k hz.2)
  refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero hd).2 ?_)
    |>.differentiableWithinAt
  rw [conjWirtingerDeriv_sub hfd (hgd k hz.2), sub_apply, hfθ z hz.1, hθ k hz.2, sub_self]

end TauCeti
