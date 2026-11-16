/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Complex.Wirtinger.Potential
import TauCeti.Analysis.Normed.Module.Exhaustion

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
differ by a function holomorphic on `interior (K (k + 1))`. Discretizing the Cauchy–Pompeiu
representation on `K k` (`IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le`) and approximating
each simple fraction by a function holomorphic on `Ω`
(`IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`) yields a holomorphic correction `P k` on
`Ω` within `2⁻ᵏ` of `h (k + 1) - h k` on `K k`. The telescoping series
`h 0 + ∑' k, (h (k + 1) - h k - P k)` differs on `interior (K m)` from `h m` by a uniform limit
of holomorphic functions, so it is `Cⁿ` on `Ω` and solves `\bar∂ g = f`
(`TauCeti.contDiffOn_and_conjWirtingerDeriv_eq_of_locally_eq_add`).

Given any particular `Cⁿ` solution `u₀`, a function `u` is a `Cⁿ` solution of `\bar∂ u = f` on `Ω`
exactly when `u - u₀` is holomorphic on `Ω`
(`TauCeti.contDiffOn_and_conjWirtingerDeriv_apply_one_eq_iff`), so the solution space is an
affine space over the holomorphic functions on `Ω`. Applying global solvability to `∂ f` solves
`\bar∂ g = ∂ f` (`TauCeti.exists_contDiffOn_conjWirtingerDeriv_eq_wirtingerDeriv`), which is the
coefficient condition for the one-form `g dz + f dbar z` to be closed.

## Main results

* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq`: global `Cⁿ` solvability of
  `\bar∂ g = f` on an arbitrary open subset of `ℂ`, for `1 ≤ n : ℕ∞` and Banach-valued data.
* `TauCeti.contDiffOn_and_conjWirtingerDeriv_apply_one_eq_iff`: affine characterization of the
  solution space of `\bar∂ u = f` on an open set.
* `TauCeti.exists_contDiffOn_conjWirtingerDeriv_eq_wirtingerDeriv`: closed completion
  `\bar∂ g = ∂ f` on an arbitrary open subset of `ℂ`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 12.2.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.4.4 and §1.4.
-/

public section

open Complex Filter Metric Set Topology
open scoped ContDiff

namespace TauCeti

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- On a compact set `K` filled in an open set `Ω ⊆ ℂ`, every bounded holomorphic function on an
open neighbourhood `V` of `K` with values in a complex normed space is uniformly approximable
on `K` by functions holomorphic on `Ω`. -/
private theorem exists_differentiableOn_norm_sub_lt_of_isFilledIn {K V Ω : Set ℂ}
    (hK : IsCompact K) (hV : IsOpen V) (hΩ : IsOpen Ω) (hKV : K ⊆ V) (hKΩ : K ⊆ Ω)
    (hfill : IsFilledIn K Ω) {g : ℂ → W} (hg : DifferentiableOn ℂ g V)
    {M : ℝ} (hM : ∀ z ∈ V, ‖g z‖ ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℂ → W, DifferentiableOn ℂ P Ω ∧ ∀ z ∈ K, ‖g z - P z‖ < ε := by
  set M' : ℝ := max M 1
  have hM'_pos : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hM' : ∀ z ∈ V, ‖g z‖ ≤ M' := fun z hz ↦ (hM z hz).trans (le_max_left M 1)
  -- Discretize Cauchy–Pompeiu on `K` into finitely many simple fractions with poles outside `K`.
  obtain ⟨N, ζ, c, hζ, hdisc⟩ :=
    hK.exists_norm_sub_sum_mul_sub_inv_smul_le hV hKV (ε := ε / (2 * M')) (by positivity)
  have hdisc' (w : ℂ) (hw : w ∈ K) :
      ‖g w - ∑ i, (c i * (w - ζ i)⁻¹) • g (ζ i)‖ ≤ ε / 2 := by
    have h := hdisc g M' hg hM' w hw
    have hmul : ε / (2 * M') * M' = ε / 2 := by field_simp
    rwa [hmul] at h
  -- Approximate each simple fraction `(w - ζ i)⁻¹` on `K` by a holomorphic function on `Ω`.
  have hrunge (i : Fin N) : ∃ q : ℂ → ℂ, DifferentiableOn ℂ q Ω ∧
      ∀ w ∈ K, ‖(w - ζ i)⁻¹ - q w‖ <
        ε / (2 * ((N : ℝ) + 1) * (‖c i‖ * ‖g (ζ i)‖ + 1)) :=
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ (hζ i).2 (by positivity)
  choose q hq hq_lt using hrunge
  refine ⟨fun w ↦ ∑ i, (c i * q i w) • g (ζ i),
    DifferentiableOn.fun_sum fun i _ ↦ ((differentiableOn_const _).mul (hq i)).smul_const _,
    fun w hw ↦ ?_⟩
  have hsplit : g w - ∑ i, (c i * q i w) • g (ζ i) =
      (g w - ∑ i, (c i * (w - ζ i)⁻¹) • g (ζ i)) +
        ∑ i, (c i * ((w - ζ i)⁻¹ - q i w)) • g (ζ i) := by
    simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
    abel
  have hterm (i : Fin N) :
      ‖(c i * ((w - ζ i)⁻¹ - q i w)) • g (ζ i)‖ ≤ ε / (2 * ((N : ℝ) + 1)) := by
    rw [norm_smul, norm_mul]
    have hcoeff : ‖c i‖ * ‖g (ζ i)‖ ≤ ‖c i‖ * ‖g (ζ i)‖ + 1 :=
      le_add_of_nonneg_right zero_le_one
    have hden : (0 : ℝ) < ‖c i‖ * ‖g (ζ i)‖ + 1 := by positivity
    calc ‖c i‖ * ‖(w - ζ i)⁻¹ - q i w‖ * ‖g (ζ i)‖
        = (‖c i‖ * ‖g (ζ i)‖) * ‖(w - ζ i)⁻¹ - q i w‖ := by ring
      _ ≤ (‖c i‖ * ‖g (ζ i)‖ + 1) *
            (ε / (2 * ((N : ℝ) + 1) * (‖c i‖ * ‖g (ζ i)‖ + 1))) :=
          mul_le_mul hcoeff (hq_lt i w hw).le (norm_nonneg _) hden.le
      _ = ε / (2 * ((N : ℝ) + 1)) := by field_simp
  have hsum_lt : ∑ i : Fin N, ‖(c i * ((w - ζ i)⁻¹ - q i w)) • g (ζ i)‖ < ε / 2 := by
    calc ∑ i : Fin N, ‖(c i * ((w - ζ i)⁻¹ - q i w)) • g (ζ i)‖
        ≤ ∑ _i : Fin N, ε / (2 * ((N : ℝ) + 1)) := Finset.sum_le_sum fun i _ ↦ hterm i
      _ = (N : ℝ) * (ε / (2 * ((N : ℝ) + 1))) := by simp
      _ < ((N : ℝ) + 1) * (ε / (2 * ((N : ℝ) + 1))) :=
          mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
      _ = ε / 2 := by field_simp
  calc ‖g w - ∑ i, (c i * q i w) • g (ζ i)‖
      ≤ ‖g w - ∑ i, (c i * (w - ζ i)⁻¹) • g (ζ i)‖ +
          ‖∑ i, (c i * ((w - ζ i)⁻¹ - q i w)) • g (ζ i)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ε / 2 + ∑ i, ‖(c i * ((w - ζ i)⁻¹ - q i w)) • g (ζ i)‖ :=
        add_le_add (hdisc' w hw) (norm_sum_le _ _)
    _ < ε / 2 + ε / 2 := add_lt_add_right hsum_lt _
    _ = ε := add_halves ε

/-- Telescoping step along an exhaustion `K k ⊆ interior (K (k + 1))` of `Ω`: if consecutive
differences `h (k + 1) - h k` are holomorphic on `interior (K (k + 1))` and approximated within
`2⁻ᵏ` on `K k` by functions `P k` holomorphic on `Ω`, then on `interior (K m)` the corrected
series `h 0 + ∑' k, (h (k + 1) - h k - P k)` is `h m` plus a holomorphic function. -/
private theorem exists_differentiableOn_eqOn_add_tsum_of_exhaustion [CompleteSpace W]
    {Ω : Set ℂ} {K : ℕ → Set ℂ} (hKint : ∀ k, K k ⊆ interior (K (k + 1)))
    (hKΩ : ∀ k, K k ⊆ Ω) {h P : ℕ → ℂ → W} (hP : ∀ k, DifferentiableOn ℂ (P k) Ω)
    (hdiff : ∀ k, DifferentiableOn ℂ (h (k + 1) - h k) (interior (K (k + 1))))
    (hP_lt : ∀ k, ∀ z ∈ K k, ‖(h (k + 1) - h k) z - P k z‖ < (1 / 2 : ℝ) ^ k) (m : ℕ) :
    ∃ L : ℂ → W, DifferentiableOn ℂ L (interior (K m)) ∧
      EqOn (fun z ↦ h 0 z + ∑' k, (h (k + 1) - h k - P k) z)
        (h m + L) (interior (K m)) := by
  have hKmono : Monotone K :=
    monotone_nat_of_le_succ fun k ↦ (hKint k).trans interior_subset
  have hint_sub {k : ℕ} (hmk : m ≤ k) : interior (K m) ⊆ K k :=
    interior_subset.trans (hKmono hmk)
  set e : ℕ → ℂ → W := fun k ↦ h (k + 1) - h k - P k
  have he_le {k : ℕ} (hmk : m ≤ k) {z : ℂ} (hz : z ∈ interior (K m)) :
      ‖e k z‖ ≤ (1 / 2 : ℝ) ^ k :=
    (hP_lt k z (hint_sub hmk hz)).le
  have hsumm : Summable fun k ↦ (1 / 2 : ℝ) ^ (k + m) :=
    (summable_nat_add_iff m).2 summable_geometric_two
  refine ⟨fun z ↦ ∑' k, e (k + m) z - ∑ k ∈ Finset.range m, P k z, ?_, fun z hz ↦ ?_⟩
  · refine DifferentiableOn.sub ?_
      (DifferentiableOn.fun_sum fun k _ ↦ (hP k).mono (interior_subset.trans (hKΩ m)))
    refine (tendstoUniformlyOn_tsum hsumm fun k z hz ↦ he_le (Nat.le_add_left m k) hz)
      |>.differentiableOn (Eventually.of_forall fun s ↦ DifferentiableOn.fun_sum fun k _ ↦ ?_)
      isOpen_interior
    exact ((hdiff (k + m)).mono ((hint_sub (Nat.le_add_left m k)).trans (hKint (k + m)))).sub
      ((hP (k + m)).mono (interior_subset.trans (hKΩ m)))
  · have hs : Summable fun k ↦ e k z := (summable_nat_add_iff m).1 <|
      .of_norm_bounded hsumm fun k ↦ he_le (Nat.le_add_left m k) hz
    have htel : ∑ k ∈ Finset.range m, e k z =
        h m z - h 0 z - ∑ k ∈ Finset.range m, P k z := by
      simp only [e, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_range_sub fun k ↦ h k z]
    simp only [Pi.add_apply]
    rw [← hs.sum_add_tsum_nat_add m, htel]
    abel

/-- **Global solvability of `\bar∂ g = f` on an open subset of `ℂ`.** Let `Ω ⊆ ℂ` be an arbitrary
open set, `n ≥ 1`, and let `f : ℂ → W` be `Cⁿ` on `Ω` with values in a complex Banach space.
Then there exists `g : ℂ → W`, `Cⁿ` on `Ω`, such that `conjWirtingerDeriv g z 1 = f z` for
every `z ∈ Ω`. No connectivity hypothesis on `Ω` is required. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eq [CompleteSpace W] {n : ℕ∞}
    {f : ℂ → W} {Ω : Set ℂ} (hn : 1 ≤ n) (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ n f Ω) :
    ∃ g : ℂ → W, ContDiffOn ℝ n g Ω ∧ ∀ z ∈ Ω, conjWirtingerDeriv g z 1 = f z := by
  obtain ⟨K, hKcpt, hKint, hKunion, hKfill⟩ := hΩ.exists_isFilledIn_compact_exhaustion
  have hKΩ (k : ℕ) : K k ⊆ Ω := hKunion ▸ subset_iUnion K k
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
    fun z hz ↦ by
      refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero
        ((hd (k + 1)).sub (hd k) z)).2 ?_).differentiableWithinAt
      rw [conjWirtingerDeriv_sub (hd (k + 1) z) (hd k z), sub_apply,
        hh_eq (k + 1) z (interior_subset (hKint (k + 1) (interior_subset hz))),
        hh_eq k z (interior_subset hz), sub_self]
  -- Approximate each difference within `2⁻ᵏ` on `K k` by a function `P k` holomorphic on `Ω`.
  have happrox (k : ℕ) : ∃ P : ℂ → W, DifferentiableOn ℂ P Ω ∧
      ∀ z ∈ K k, ‖(h (k + 1) - h k) z - P z‖ < (1 / 2 : ℝ) ^ k := by
    obtain ⟨M, hM⟩ :=
      (hKcpt (k + 1)).exists_bound_of_continuousOn
        ((hh (k + 1)).sub (hh k)).continuous.continuousOn
    exact exists_differentiableOn_norm_sub_lt_of_isFilledIn (hKcpt k) isOpen_interior hΩ
      (hKint k) (hKΩ k) (hKfill k) (hdiff k) (fun z hz ↦ hM z (interior_subset hz))
      (by positivity)
  choose P hP hP_lt using happrox
  set G : ℂ → W := fun z ↦ h 0 z + ∑' k, (h (k + 1) - h k - P k) z
  have hkey (m : ℕ) : ∃ L : ℂ → W, DifferentiableOn ℂ L (interior (K m)) ∧
      EqOn G (h m + L) (interior (K m)) :=
    exists_differentiableOn_eqOn_add_tsum_of_exhaustion hKint hKΩ hP hdiff hP_lt m
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

/-- **Affine solution space of `\bar∂ u = f`.** Given a particular `Cⁿ` solution `u₀` of
`\bar∂ u₀ = f` on an open set `Ω ⊆ ℂ`, for `n ≥ 1`, another function `u` is a `Cⁿ` solution of
`\bar∂ u = f` on `Ω` if and only if `u - u₀` is holomorphic on `Ω`. -/
theorem contDiffOn_and_conjWirtingerDeriv_apply_one_eq_iff [CompleteSpace W] {u₀ u f : ℂ → W}
    {Ω : Set ℂ} {n : WithTop ℕ∞} (hn : 1 ≤ n) (hΩ : IsOpen Ω) (hu₀ : ContDiffOn ℝ n u₀ Ω)
    (hsol : ∀ z ∈ Ω, conjWirtingerDeriv u₀ z 1 = f z) :
    (ContDiffOn ℝ n u Ω ∧ ∀ z ∈ Ω, conjWirtingerDeriv u z 1 = f z) ↔
      DifferentiableOn ℂ (u - u₀) Ω := by
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  constructor
  · rintro ⟨hu, huf⟩ z hz
    have hd₁ : DifferentiableAt ℝ u z :=
      (hu.contDiffAt (hΩ.mem_nhds hz)).differentiableAt hn0
    have hd₀ : DifferentiableAt ℝ u₀ z :=
      (hu₀.contDiffAt (hΩ.mem_nhds hz)).differentiableAt hn0
    refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (hd₁.sub hd₀)).2 ?_)
      |>.differentiableWithinAt
    rw [conjWirtingerDeriv_sub hd₁ hd₀, sub_apply, huf z hz, hsol z hz, sub_self]
  · intro hdiff
    have hcd : ContDiffOn ℝ n (u - u₀) Ω :=
      ((hdiff.contDiffOn hΩ).of_le le_top).restrict_scalars ℝ
    have hu_eq : u = u₀ + (u - u₀) := by ext z; simp
    refine ⟨hu_eq ▸ hu₀.add hcd, fun z hz ↦ ?_⟩
    have hd₀ : DifferentiableAt ℝ u₀ z :=
      (hu₀.contDiffAt (hΩ.mem_nhds hz)).differentiableAt hn0
    have hdh : DifferentiableAt ℂ (u - u₀) z := hdiff.differentiableAt (hΩ.mem_nhds hz)
    rw [hu_eq, conjWirtingerDeriv_add hd₀ (hdh.restrictScalars ℝ), add_apply, hsol z hz,
      hdh.conjWirtingerDeriv_eq_zero, zero_apply, add_zero]

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

end TauCeti
