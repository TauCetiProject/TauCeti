/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Compactness.LocallyCompact
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Complex.Runge.Rational
import TauCeti.Analysis.Complex.Runge.SimpleFraction
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Topology.ConnectedComponents

/-!
# Runge's approximation theorem, finite-rank Runge operators, and jet interpolation

Let `K` be a compact subset of a set `Ω ⊆ ℂ` such that `K` is filled in `Ω`
(`TauCeti.IsFilledIn K Ω`), meaning no connected component of `Ω \ K` has compact closure
contained in `Ω`. This file proves Runge's approximation theorem in its finite-rank operator,
vector-valued, equivalence, polynomial, and finite-jet interpolation forms.

* **Finite-rank Runge operators** (`TauCeti.IsFilledIn.exists_norm_sub_sum_smul_le`): filledness of
  compact `K ⊆ Ω` ensures that `Ωᶜ` meets every bounded connected component of `Kᶜ`, so
  `TauCeti.exists_rational_norm_sub_sum_smul_le` yields finitely many evaluation points
  `ζ i ∈ V \ K` and holomorphic kernels `g i` on `Ω` (without requiring `Ω` to be open) such that
  `f ↦ ∑ i, g i · • f (ζ i)` approximates every holomorphic `f : ℂ → F` bounded by `M` on `V`
  within `ε * M` on `K`. The points and kernels depend only on `K`, `Ω`, `V`, and `ε`, not on `f`
  or the complex normed target space `F`.
* **Vector-valued Runge approximation** (`TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`):
  restricting the finite-rank operator to the interior of a compact collar `L` between `K` and `U`
  approximates any holomorphic function `f : ℂ → F` on an open neighbourhood `U` of `K` uniformly
  on `K` by functions holomorphic on `Ω`, without requiring `Ω` to be open.
* **Converse and equivalences**
  (`TauCeti.isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt`,
  `TauCeti.isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt`,
  `TauCeti.isFilledIn_iff_forall_exists_differentiableOn_norm_inv_sub_lt`): for open `Ω`, if a
  component `C` of `Ω \ K` had compact closure in `Ω`, approximating `(z - a)⁻¹` for `a ∈ C` would
  produce `1 - (z - a) g z` violating the maximum modulus principle
  (`Complex.norm_le_of_forall_mem_frontier_norm_le`). Thus filledness is equivalent to uniform
  approximation of neighbourhood-holomorphic functions, and equally to simple-fraction
  approximation.
* **Polynomial Runge approximation** (`Differentiable.exists_polynomial_norm_sub_lt`,
  `TauCeti.IsFilledIn.exists_polynomial_norm_sub_lt`,
  `TauCeti.isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt`): when `Ω = univ`,
  approximating the resulting entire function by a Taylor partial sum yields a complex polynomial;
  for compact `K`, polynomial approximability is equivalent to connectedness of `Kᶜ`.
* **Finite-jet interpolation**
  (`TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt_and_iteratedDeriv_eq`): given a finite
  set `S ⊆ Ω` and orders `m : ℂ → ℕ`, a Hermite interpolating polynomial `P` (from
  `Ideal.exists_forall_sub_mem_ideal`) and iterated divided differences
  (`Complex.differentiableOn_dslope`) reduce jet-preserving Runge approximation to rational Runge
  approximation of the holomorphic quotient `(f - P) / ∏_{a ∈ S} (z - a)^{m a}` with poles outside
  `Ω`, again without requiring `Ω` to be open.

## References

* A. Rainer, *Advanced Complex Analysis*, §11 (Theorem 11.1, Lemma 11.3, Theorem 11.7).
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.3.1.
-/

public section

open Filter Function Metric Polynomial Set Topology
open scoped NNReal

universe u

namespace TauCeti

/-! ### Finite-rank Runge operators and vector-valued approximation -/

/-- If a closed set `K ⊆ Ω` is filled in `Ω`, then `Ωᶜ` meets every bounded connected component of
`Kᶜ`, without requiring `Ω` to be open. -/
private theorem IsFilledIn.compl_inter_connectedComponentIn_nonempty {K Ω : Set ℂ}
    (hfill : IsFilledIn K Ω) (hK : IsClosed K) (hKΩ : K ⊆ Ω) :
    ∀ x ∈ filledHull K \ K, (Ωᶜ ∩ connectedComponentIn Kᶜ x).Nonempty := by
  rintro x ⟨hxH, hxK⟩
  by_contra h
  have hDΩ : connectedComponentIn Kᶜ x ⊆ Ω := fun y hy ↦ by_contra fun hyΩ ↦ h ⟨y, hyΩ, hy⟩
  have hCD : connectedComponentIn (Ω \ K) x ⊆ connectedComponentIn Kᶜ x :=
    connectedComponentIn_mono x (sdiff_subset_compl _ _)
  have hclD : closure (connectedComponentIn Kᶜ x) ⊆ Ω := by
    rw [closure_eq_self_union_frontier]
    exact union_subset hDΩ <| (frontier_connectedComponentIn_subset_compl hK.isOpen_compl x).trans
      (by rwa [compl_compl])
  exact isFilledIn_iff.mp hfill x ⟨hDΩ (mem_connectedComponentIn hxK), hxK⟩
    ⟨(mem_filledHull_iff.mp hxH).isCompact_closure.of_isClosed_subset isClosed_closure
      (closure_mono hCD), (closure_mono hCD).trans hclD⟩

/-- **Finite-rank Runge approximation operator.** Let `K` be a compact set filled in `Ω ⊆ ℂ`
(without requiring `Ω` to be open), and let `V ⊆ ℂ` be an open neighbourhood of `K`. For every
`ε > 0` there are finitely many evaluation points `ζ i ∈ V \ K` and functions `g i : ℂ → ℂ`
holomorphic on `Ω` such that every `f : ℂ → F` into a complex normed space, holomorphic on `V` and
bounded by `M` there, satisfies `‖f w - ∑ i, g i w • f (ζ i)‖ ≤ ε * M` for all `w ∈ K`.

The points `ζ i` and holomorphic kernels `g i` depend only on `K`, `Ω`, `V`, and `ε`, not on `f`
or `F`. The resulting operator `f ↦ ∑ i, g i · • f (ζ i)` is linear in `f`, takes values in
functions holomorphic on `Ω`, and has finite rank for scalar `f`. -/
theorem IsFilledIn.exists_norm_sub_sum_smul_le {K Ω V : Set ℂ} (hfill : IsFilledIn K Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hV : IsOpen V) (hKV : K ⊆ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
      (∀ i, ζ i ∈ V \ K) ∧ (∀ i, DifferentiableOn ℂ (g i) Ω) ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] (f : ℂ → F) (M : ℝ),
        DifferentiableOn ℂ f V → (∀ z ∈ V, ‖f z‖ ≤ M) →
        ∀ w ∈ K, ‖f w - ∑ i, g i w • f (ζ i)‖ ≤ ε * M := by
  obtain ⟨N, ζ, p, q, hζ, -, hqΩ, hop⟩ := exists_rational_norm_sub_sum_smul_le.{u} hK hV hKV
    (hfill.compl_inter_connectedComponentIn_nonempty hK.isClosed hKΩ) hε
  refine ⟨N, ζ, fun i w ↦ (p i).eval w / (q i).eval w, hζ, fun i ↦
    (p i).differentiable.differentiableOn.div (q i).differentiable.differentiableOn
      fun z hz h0 ↦ (hqΩ i z h0).1 hz, hop⟩

/-- **Runge's approximation theorem.** Let `K` be a compact set filled in `Ω ⊆ ℂ` (without
requiring `Ω` to be open), and let `f : ℂ → F` be holomorphic on an open neighbourhood `U` of `K`
with values in a complex normed space `F`. For every `ε > 0` there is a function `g : ℂ → F`
holomorphic on `Ω` such that `‖f z - g z‖ < ε` for all `z ∈ K`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt {K Ω U : Set ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] (hfill : IsFilledIn K Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → F}
    (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨M₀, hM₀⟩ := hL.bddAbove_image (hf.continuousOn.mono hLU).norm
  set M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ z ∈ interior L, ‖f z‖ ≤ M := fun z hz ↦
    (hM₀ ⟨z, interior_subset hz, rfl⟩).trans (le_max_left _ _)
  obtain ⟨N, ζ, g, -, hg, happrox⟩ := hfill.exists_norm_sub_sum_smul_le hK hKΩ isOpen_interior
    hKL (ε := ε / (2 * (M + 1))) (by positivity)
  refine ⟨fun w ↦ ∑ i, g i w • f (ζ i),
    DifferentiableOn.fun_sum fun i _ ↦ (hg i).smul_const (f (ζ i)), fun w hw ↦ ?_⟩
  have hle := happrox f M (hf.mono (interior_subset.trans hLU)) hM w hw
  have hlt : ε / (2 * (M + 1)) * M < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  exact hle.trans_lt hlt

/-! ### Converse and universal equivalences -/

/-- **Converse of Runge's theorem.** If `Ω ⊆ ℂ` is open and every simple fraction `(z - a)⁻¹` with
`a ∈ Ω \ K` can be uniformly approximated on `K` by functions holomorphic on `Ω`, then `K` is
filled in `Ω`. No compactness or closedness of `K` is needed. -/
theorem isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt {K Ω : Set ℂ}
    (hΩ : IsOpen Ω)
    (h : ∀ a ∈ Ω \ K, ∀ ε > 0,
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε) :
    IsFilledIn K Ω := by
  rw [isFilledIn_iff]
  rintro a ha ⟨hcpt, hsub⟩
  set C := connectedComponentIn (Ω \ K) a
  have hfr : frontier C ⊆ closure K := fun y hy ↦ by_contra fun hyK ↦
    frontier_connectedComponentIn_subset_compl_interior a hy
      (interior_maximal (sdiff_subset_sdiff_right subset_closure) (hΩ.sdiff isClosed_closure)
        ⟨hsub hy.1, hyK⟩)
  obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall a
  set M : ℝ := max R 1
  have hM : 0 < M := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨g, hg, hga⟩ := h a ha (2 * M)⁻¹ (by positivity)
  set f : ℂ → ℂ := fun z ↦ 1 - (z - a) * g z
  have hf_diff : DifferentiableOn ℂ f Ω :=
    (differentiableOn_const 1).sub ((differentiableOn_id.sub (differentiableOn_const a)).mul hg)
  have hf_cl : DiffContOnCl ℂ f C :=
    ⟨hf_diff.mono ((connectedComponentIn_subset _ _).trans sdiff_subset),
      hf_diff.continuousOn.mono hsub⟩
  have hf_fr : ∀ y ∈ frontier C, ‖f y‖ ≤ 1 / 2 := by
    intro y hy
    have hcont : ContinuousAt (fun z ↦ ‖f z‖ - ‖z - a‖ * (2 * M)⁻¹) y :=
      ((hf_diff.continuousOn.continuousAt (hΩ.mem_nhds (hsub hy.1))).norm).sub
        (((continuous_id.sub continuous_const).norm.mul continuous_const).continuousAt)
    have hle_K : ∀ z ∈ K, ‖f z‖ - ‖z - a‖ * (2 * M)⁻¹ ≤ 0 := by
      intro z hz
      have hza : z - a ≠ 0 := sub_ne_zero.mpr fun hza ↦ ha.2 (hza ▸ hz)
      have hfz : f z = (z - a) * ((z - a)⁻¹ - g z) := by
        simp only [f]; field_simp [hza]
      rw [hfz, norm_mul]
      linarith [mul_le_mul_of_nonneg_left (hga z hz).le (norm_nonneg (z - a))]
    have hy_le : ‖f y‖ ≤ ‖y - a‖ * (2 * M)⁻¹ := by
      have hnb : (𝓝[K] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hfr hy)
      have h0 := le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall hle_K)
      linarith
    have hyM : ‖y - a‖ ≤ M :=
      (dist_eq_norm y a ▸ mem_closedBall.mp (hR hy.1)).trans (le_max_left _ _)
    calc ‖f y‖ ≤ ‖y - a‖ * (2 * M)⁻¹ := hy_le
      _ ≤ M * (2 * M)⁻¹ := mul_le_mul_of_nonneg_right hyM (by positivity)
      _ = 1 / 2 := by field_simp [hM.ne']
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le
    (hcpt.isBounded.subset subset_closure) hf_cl hf_fr
    (subset_closure (mem_connectedComponentIn ha))
  simp [f] at hmax
  norm_num at hmax

/-- **Runge's theorem (equivalence with simple-fraction approximation).** A compact subset `K` of
an open set `Ω ⊆ ℂ` is filled in `Ω` if and only if every simple fraction `(z - a)⁻¹` with
`a ∈ Ω \ K` is uniformly approximable on `K` by functions holomorphic on `Ω`. -/
theorem isFilledIn_iff_forall_exists_differentiableOn_norm_inv_sub_lt {K Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔
      ∀ a ∈ Ω \ K, ∀ ε > 0,
        ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε :=
  ⟨fun hfill _ ha _ hε ↦ hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ ha.2 hε,
    isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt hΩ⟩

/-- **Runge's theorem (universal equivalence).** A compact subset `K` of an open set `Ω ⊆ ℂ` is
filled in `Ω` if and only if every function holomorphic on an open neighbourhood of `K` is
uniformly approximable on `K` by functions holomorphic on `Ω`. -/
theorem isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt {K Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔
      ∀ (U : Set ℂ), IsOpen U → K ⊆ U → ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  refine ⟨fun hfill _ hU hKU _ hf _ hε ↦
    hfill.exists_differentiableOn_norm_sub_lt hK hKΩ hU hKU hf hε, fun h ↦ ?_⟩
  refine isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt hΩ fun a ha ε hε ↦ ?_
  have hU : IsOpen ({a}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  have hKU : K ⊆ ({a}ᶜ : Set ℂ) := fun z hz hza ↦ ha.2 (hza ▸ hz)
  have hf : DifferentiableOn ℂ (fun z : ℂ ↦ (z - a)⁻¹) {a}ᶜ :=
    (differentiableOn_id.sub (differentiableOn_const a)).inv fun z hz ↦ sub_ne_zero.mpr hz
  exact h {a}ᶜ hU hKU _ hf ε hε

/-! ### Polynomial Runge approximation -/

/-- Every entire function `f : ℂ → ℂ` is uniformly approximable on any bounded set by complex
polynomials (namely partial sums of its Taylor series at `0`). -/
theorem _root_.Differentiable.exists_polynomial_norm_sub_lt {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {K : Set ℂ} (hK : Bornology.IsBounded K) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  obtain ⟨R₀, hR₀⟩ := hK.subset_ball 0
  set R : ℝ := max R₀ 0
  set t : ℝ≥0 := (R + 2).toNNReal
  have ht : (t : ℝ) = R + 2 := Real.coe_toNNReal _ (by positivity)
  set t' : ℝ≥0 := (R + 1).toNNReal
  have ht' : (t' : ℝ) = R + 1 := Real.coe_toNNReal _ (by positivity)
  have hps := DifferentiableOn.hasFPowerSeriesOnBall
    (hf.differentiableOn : DifferentiableOn ℂ f (closedBall 0 t))
    (by rw [← NNReal.coe_pos, ht]; positivity)
  have hu := hps.tendstoUniformlyOn (r' := t')
    (ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, ht, ht']; linarith))
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 hu ε hε).exists
  set p := cauchyPowerSeries f 0 t
  refine ⟨∑ k ∈ Finset.range N, C (p k fun _ ↦ 1) * X ^ k, fun z hz ↦ ?_⟩
  have hzt' : z ∈ ball (0 : ℂ) t' := by
    have hzR : dist z 0 < R := (mem_ball.mp (hR₀ hz)).trans_le (le_max_left _ _)
    rw [mem_ball, ht']; linarith
  have heval : (∑ k ∈ Finset.range N, C (p k fun _ ↦ 1) * X ^ k).eval z = p.partialSum N z := by
    rw [← coe_evalRingHom, map_sum, FormalMultilinearSeries.partialSum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hsmul : (fun _ : Fin k ↦ z) = fun _ : Fin k ↦ z • (1 : ℂ) := by
      ext; simp
    rw [hsmul, (p k).map_smul_univ]
    simp only [coe_evalRingHom, eval_mul, eval_C, eval_pow, eval_X, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [mul_comm]
  rw [heval]
  simpa [dist_eq_norm, zero_add] using hN z hzt'

/-- **Polynomial Runge theorem.** If `K ⊆ ℂ` is compact and filled in `ℂ`, every function
holomorphic on an open neighbourhood `U` of `K` can be uniformly approximated on `K` by complex
polynomials. -/
theorem IsFilledIn.exists_polynomial_norm_sub_lt {K U : Set ℂ} (hfill : IsFilledIn K univ)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  obtain ⟨g, hg, hfg⟩ := hfill.exists_differentiableOn_norm_sub_lt hK (subset_univ K)
    hU hKU hf (half_pos hε)
  obtain ⟨p, hgp⟩ := (differentiableOn_univ.mp hg).exists_polynomial_norm_sub_lt hK.isBounded
    (half_pos hε)
  refine ⟨p, fun z hz ↦ ?_⟩
  calc ‖f z - p.eval z‖ = ‖(f z - g z) + (g z - p.eval z)‖ := by ring_nf
    _ ≤ ‖f z - g z‖ + ‖g z - p.eval z‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hfg z hz) (hgp z hz)
    _ = ε := add_halves ε

/-- **Polynomial Runge equivalence.** For compact `K ⊆ ℂ`, the complement `Kᶜ` is connected if and
only if every function holomorphic on an open neighbourhood of `K` is uniformly approximable on `K`
by complex polynomials. -/
theorem isConnected_compl_iff_forall_exists_polynomial_norm_sub_lt {K : Set ℂ} (hK : IsCompact K) :
    IsConnected Kᶜ ↔
      ∀ (U : Set ℂ), IsOpen U → K ⊆ U → ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
        ∀ ε > 0, ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat
  rw [← filledHull_eq_self_iff_isConnected_compl hrank hK.isBounded,
    ← isFilledIn_univ_iff hK.isClosed]
  refine ⟨fun hfill _ hU hKU _ hf _ hε ↦ hfill.exists_polynomial_norm_sub_lt hK hU hKU hf hε,
    fun h ↦ ?_⟩
  rw [isFilledIn_iff_forall_exists_differentiableOn_norm_sub_lt isOpen_univ hK (subset_univ K)]
  intro U hU hKU f hf ε hε
  obtain ⟨p, hp⟩ := h U hU hKU f hf ε hε
  exact ⟨fun z ↦ p.eval z, p.differentiable.differentiableOn, hp⟩

/-! ### Finite-jet interpolation refinement -/

/-- The `k`-th derivative at `a` of the Taylor polynomial `∑_{j < n} (c j / j!) (z - a)^j` is
`c k` for `k < n`. -/
private theorem iteratedDeriv_eval_taylorPoly (a : ℂ) (n : ℕ) (c : ℕ → ℂ) {k : ℕ} (hk : k < n) :
    iteratedDeriv k (fun z ↦ (∑ j ∈ Finset.range n,
      C (c j / (j.factorial : ℂ)) * (X - C a) ^ j).eval z) a = c k := by
  have hTeval : (fun z ↦ (∑ j ∈ Finset.range n,
      C (c j / (j.factorial : ℂ)) * (X - C a) ^ j).eval z) =
      ∑ j ∈ Finset.range n, fun z ↦ (c j / (j.factorial : ℂ)) * (z - a) ^ j := by
    ext z; rw [← coe_evalRingHom, map_sum]; simp
  rw [hTeval, iteratedDeriv_sum fun j _ ↦ by fun_prop, Finset.sum_eq_single k]
  · rw [iteratedDeriv_const_mul_field]
    have hshift : iteratedDeriv k (fun z : ℂ ↦ (z - a) ^ k) a = (k.factorial : ℂ) := by
      have hcomp := congrFun (iteratedDeriv_comp_sub_const k (fun z : ℂ ↦ z ^ k) a) a
      rw [sub_self, iteratedDeriv_fun_pow_zero] at hcomp
      simpa using hcomp
    rw [hshift, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))]
  · intro j _ hjk
    rw [iteratedDeriv_const_mul_field]
    have hshift : iteratedDeriv k (fun z : ℂ ↦ (z - a) ^ j) a = 0 := by
      have hcomp := congrFun (iteratedDeriv_comp_sub_const k (fun z : ℂ ↦ z ^ j) a) a
      rw [sub_self, iteratedDeriv_fun_pow_zero] at hcomp
      simpa [Ne.symm hjk] using hcomp
    rw [hshift, mul_zero]
  · intro hk_not; exact absurd (Finset.mem_range.mpr hk) hk_not

/-- **Hermite polynomial interpolation.** Given finitely many points `S ⊆ ℂ`, orders `m : ℂ → ℕ`,
and prescribed derivative values `c : ℂ → ℕ → ℂ`, there is a polynomial `p : ℂ[X]` whose `k`-th
derivative at `a` equals `c a k` for every `a ∈ S` and `k < m a`. -/
private theorem exists_polynomial_iteratedDeriv_eval_eq (S : Finset ℂ) (m : ℂ → ℕ)
    (c : ℂ → ℕ → ℂ) :
    ∃ p : ℂ[X], ∀ a ∈ S, ∀ k < m a, iteratedDeriv k (fun z ↦ p.eval z) a = c a k := by
  let I : S → Ideal ℂ[X] := fun a ↦ Ideal.span {(X - C (a : ℂ)) ^ m a}
  have hcop : Pairwise (IsCoprime on I) := by
    intro a b hab
    have hne : (a : ℂ) ≠ b := fun h ↦ hab (Subtype.ext h)
    have h1 : IsCoprime (X - C (a : ℂ)) (X - C (b : ℂ)) :=
      Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (h1.pow (m := m a) (n := m b))
  let T : S → ℂ[X] := fun a ↦
    ∑ j ∈ Finset.range (m a), C (c a j / (j.factorial : ℂ)) * (X - C (a : ℂ)) ^ j
  obtain ⟨p, hp⟩ := Ideal.exists_forall_sub_mem_ideal hcop T
  refine ⟨p, fun a ha k hk ↦ ?_⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (hp ⟨a, ha⟩)
  have hp_an : AnalyticAt ℂ (fun z ↦ p.eval z) a := p.differentiable.analyticAt a
  have hT_an : AnalyticAt ℂ (fun z ↦ (T ⟨a, ha⟩).eval z) a :=
    (T ⟨a, ha⟩).differentiable.analyticAt a
  have hord : ((m a : ℕ) : ℕ∞) ≤
      analyticOrderAt (fun z ↦ p.eval z - (T ⟨a, ha⟩).eval z) a := by
    refine (hp_an.sub hT_an).natCast_le_analyticOrderAt_of_eventually_eq_pow_smul
      (u := fun z ↦ r.eval z) r.differentiable.continuous.continuousAt
      (Eventually.of_forall fun z ↦ ?_)
    simpa [smul_eq_mul] using congrArg (Polynomial.eval z) hr
  have hzero :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hp_an.sub hT_an)).mp hord k hk
  have hpeq : iteratedDeriv k (fun z ↦ p.eval z) a =
      iteratedDeriv k (fun z ↦ (T ⟨a, ha⟩).eval z) a := by
    have hsub := iteratedDeriv_fun_sub (n := k) hp_an.contDiffAt hT_an.contDiffAt
    exact sub_eq_zero.mp (hsub ▸ hzero)
  rw [hpeq]
  exact iteratedDeriv_eval_taylorPoly a (m a) (c a) hk

/-- Repeatedly dividing a holomorphic function on an open set `U` by `(z - a)` at a zero of order
at least `m` produces a holomorphic quotient on `U`. -/
private theorem exists_differentiableOn_eq_pow_sub_mul {U : Set ℂ} (hU : IsOpen U) {a : ℂ}
    (ha : a ∈ U) :
    ∀ (m : ℕ) {h : ℂ → ℂ}, DifferentiableOn ℂ h U → (m : ℕ∞) ≤ analyticOrderAt h a →
      ∃ q : ℂ → ℂ, DifferentiableOn ℂ q U ∧ ∀ z, h z = (z - a) ^ m * q z
  | 0, h, hh, _ => ⟨h, hh, fun z ↦ by simp⟩
  | m + 1, h, hh, hord => by
      have hha : AnalyticAt ℂ h a := hh.analyticAt (hU.mem_nhds ha)
      have h0 : h a = 0 := by
        simpa using (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hha).mp hord 0
          (Nat.zero_lt_succ m)
      have hd_diff : DifferentiableOn ℂ (dslope h a) U :=
        (Complex.differentiableOn_dslope (hU.mem_nhds ha)).mpr hh
      have hd_ord : (m : ℕ∞) ≤ analyticOrderAt (dslope h a) a := by
        have hadd := hha.analyticOrderAt_dslope_add_one h0
        rw [← hadd, Nat.cast_add, Nat.cast_one] at hord
        exact (ENat.add_le_add_iff_right (ENat.natCast_ne_top 1)).mp hord
      obtain ⟨q, hq, hqe⟩ := exists_differentiableOn_eq_pow_sub_mul hU ha m hd_diff hd_ord
      refine ⟨q, hq, fun z ↦ ?_⟩
      calc h z = (z - a) * dslope h a z := by
            simpa [smul_eq_mul] using (sub_smul_dslope_of_zero h0 z).symm
        _ = (z - a) * ((z - a) ^ m * q z) := by rw [hqe z]
        _ = (z - a) ^ (m + 1) * q z := by rw [pow_succ', mul_assoc]

/-- Dividing a holomorphic function on an open set `U` by `∏_{a ∈ S} (z - a)^{m a}` when it
vanishes to order at least `m a` at each `a ∈ S ⊆ U`. -/
private theorem exists_differentiableOn_eq_prod_pow_sub_mul {U : Set ℂ} (hU : IsOpen U)
    (m : ℂ → ℕ) :
    ∀ (S : Finset ℂ), (S : Set ℂ) ⊆ U → ∀ {h : ℂ → ℂ}, DifferentiableOn ℂ h U →
      (∀ a ∈ S, (m a : ℕ∞) ≤ analyticOrderAt h a) →
      ∃ q : ℂ → ℂ, DifferentiableOn ℂ q U ∧ ∀ z, h z = (∏ a ∈ S, (z - a) ^ m a) * q z := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ h hh _; exact ⟨h, hh, fun z ↦ by simp⟩
  | @insert a s has ih =>
      intro hSU h hh hord
      have haU : a ∈ U := hSU (Finset.mem_coe.mpr (Finset.mem_insert_self a s))
      have hsU : (s : Set ℂ) ⊆ U := fun b hb ↦
        hSU (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hb)))
      obtain ⟨h₁, hh₁, heq₁⟩ := exists_differentiableOn_eq_pow_sub_mul hU haU (m a) hh
        (hord a (Finset.mem_insert_self a s))
      have hord₁ : ∀ b ∈ s, (m b : ℕ∞) ≤ analyticOrderAt h₁ b := by
        intro b hb
        have hba : b - a ≠ 0 := sub_ne_zero.mpr fun hba ↦ has (hba ▸ hb)
        have hmul : h = (fun z ↦ (z - a) ^ m a) * h₁ := funext heq₁
        have hpow_an : AnalyticAt ℂ (fun z : ℂ ↦ (z - a) ^ m a) b := by fun_prop
        have hpow_ne : (b - a) ^ m a ≠ 0 := pow_ne_zero _ hba
        have hord_eq : analyticOrderAt h b = analyticOrderAt h₁ b := by
          rw [hmul, analyticOrderAt_mul hpow_an (hh₁.analyticAt (hU.mem_nhds (hsU hb))),
            (hpow_an.analyticOrderAt_eq_zero).mpr hpow_ne, zero_add]
        rw [← hord_eq]
        exact hord b (Finset.mem_insert_of_mem hb)
      obtain ⟨q, hq, heq₂⟩ := ih hsU hh₁ hord₁
      refine ⟨q, hq, fun z ↦ ?_⟩
      rw [Finset.prod_insert has, mul_assoc, ← heq₂ z, ← heq₁ z]

/-- Dividing a holomorphic function on an open neighbourhood `U` of `K` by `∏_{a ∈ S} (z - a)^{m a}`
on an open neighbourhood `U' ⊆ U` of `K`, assuming the required vanishing orders at `S ∩ K`. -/
private theorem exists_open_differentiableOn_quotient {K U : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U)
    (S : Finset ℂ) (m : ℂ → ℕ) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h U)
    (hord : ∀ a ∈ S, a ∈ K → (m a : ℕ∞) ≤ analyticOrderAt h a) :
    ∃ (U' : Set ℂ) (q : ℂ → ℂ), IsOpen U' ∧ K ⊆ U' ∧ DifferentiableOn ℂ q U' ∧
      ∀ z ∈ U', h z = (∏ a ∈ S, (z - a) ^ m a) * q z := by
  classical
  set Sin : Finset ℂ := S.filter (· ∈ K)
  set Sout : Finset ℂ := S.filter (· ∉ K)
  set U' : Set ℂ := U \ (Sout : Set ℂ)
  have hU' : IsOpen U' := hU.sdiff Sout.finite_toSet.isClosed
  have hKU' : K ⊆ U' := fun z hz ↦ ⟨hKU hz, fun hz' ↦ (Finset.mem_filter.mp hz').2 hz⟩
  have hSinU' : (Sin : Set ℂ) ⊆ U' := fun z hz ↦ hKU' (Finset.mem_filter.mp hz).2
  obtain ⟨q₁, hq₁, hq₁_eq⟩ := exists_differentiableOn_eq_prod_pow_sub_mul hU' m Sin hSinU'
    (hh.mono sdiff_subset) fun a ha ↦ hord a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
  set Qout : ℂ → ℂ := fun z ↦ ∏ b ∈ Sout, (z - b) ^ m b
  have hQout_diff : Differentiable ℂ Qout := by fun_prop
  have hQout_ne : ∀ z ∈ U', Qout z ≠ 0 := fun z hz ↦
    Finset.prod_ne_zero_iff.mpr fun b hb ↦ pow_ne_zero _ (sub_ne_zero.mpr fun hzb ↦ hz.2 (hzb ▸ hb))
  refine ⟨U', fun z ↦ q₁ z / Qout z, hU', hKU', hq₁.div hQout_diff.differentiableOn hQout_ne,
    fun z hz ↦ ?_⟩
  have hsplit : (∏ a ∈ S, (z - a) ^ m a) = (∏ a ∈ Sin, (z - a) ^ m a) * Qout z :=
    (Finset.prod_filter_mul_prod_filter_not S (· ∈ K) fun a ↦ (z - a) ^ m a).symm
  rw [hq₁_eq z, hsplit, mul_assoc, mul_div_cancel₀ _ (hQout_ne z hz)]

/-- Multiplying a function analytic at `a ∈ S` by `∏_{b ∈ S} (z - b)^{m b}` annihilates all
derivatives of order `< m a` at `a`. -/
private theorem iteratedDeriv_prod_pow_sub_mul_eq_zero (S : Finset ℂ) (m : ℂ → ℕ) {r : ℂ → ℂ}
    {a : ℂ} (ha : a ∈ S) (hra : AnalyticAt ℂ r a) {k : ℕ} (hk : k < m a) :
    iteratedDeriv k (fun z ↦ (∏ b ∈ S, (z - b) ^ m b) * r z) a = 0 := by
  classical
  have hQ_an : AnalyticAt ℂ (fun z : ℂ ↦ ∏ b ∈ S, (z - b) ^ m b) a := by fun_prop
  have hQa : AnalyticAt ℂ (fun z ↦ (∏ b ∈ S, (z - b) ^ m b) * r z) a := hQ_an.mul hra
  have hord : ((m a : ℕ) : ℕ∞) ≤ analyticOrderAt (fun z ↦ (∏ b ∈ S, (z - b) ^ m b) * r z) a := by
    refine hQa.natCast_le_analyticOrderAt_of_eventually_eq_pow_smul
      (u := fun z ↦ (∏ b ∈ S.erase a, (z - b) ^ m b) * r z)
      ((by fun_prop : Continuous fun z : ℂ ↦ ∏ b ∈ S.erase a, (z - b) ^ m b).continuousAt.mul
        hra.continuousAt) (Eventually.of_forall fun z ↦ ?_)
    simp only [smul_eq_mul, ← mul_assoc]
    rw [Finset.mul_prod_erase S (fun b ↦ (z - b) ^ m b) ha]
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hQa).mp hord k hk

/-- **Runge approximation with finite-jet interpolation.** Let `K` be a compact set filled in
`Ω ⊆ ℂ` (without requiring `Ω` to be open), let `f : ℂ → ℂ` be holomorphic on an open neighbourhood
`U` of `K`, and let `S ⊆ Ω` be a finite set with orders `m : ℂ → ℕ`. For every `ε > 0` there is a
function `g : ℂ → ℂ` holomorphic on `Ω` such that `‖f z - g z‖ < ε` on `K` and
`iteratedDeriv k g a = iteratedDeriv k f a` for all `a ∈ S` and `k < m a`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt_and_iteratedDeriv_eq
    {K Ω U : Set ℂ} (hfill : IsFilledIn K Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (S : Finset ℂ) (hSΩ : (S : Set ℂ) ⊆ Ω) (m : ℂ → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ (∀ z ∈ K, ‖f z - g z‖ < ε) ∧
      ∀ a ∈ S, ∀ k < m a, iteratedDeriv k g a = iteratedDeriv k f a := by
  classical
  obtain ⟨P, hP⟩ := exists_polynomial_iteratedDeriv_eval_eq S m fun a k ↦ iteratedDeriv k f a
  have hord_in : ∀ a ∈ S, a ∈ K → (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ f z - P.eval z) a := by
    intro a haS haK
    have hfa : AnalyticAt ℂ f a := hf.analyticAt (hU.mem_nhds (hKU haK))
    have hPa : AnalyticAt ℂ (fun z ↦ P.eval z) a := P.differentiable.analyticAt a
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hfa.fun_sub hPa)]
    intro k hk
    rw [iteratedDeriv_fun_sub hfa.contDiffAt hPa.contDiffAt, hP a haS k hk, sub_self]
  obtain ⟨U', q, hU', hKU', hq, hq_eq⟩ := exists_open_differentiableOn_quotient hU hKU S m
    (hf.fun_sub P.differentiable.differentiableOn) hord_in
  set Q : ℂ → ℂ := fun z ↦ ∏ a ∈ S, (z - a) ^ m a
  have hQ_diff : Differentiable ℂ Q := by fun_prop
  obtain ⟨M₀, hM₀⟩ := hK.bddAbove_image hQ_diff.continuous.norm.continuousOn
  set M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  obtain ⟨p_r, q_r, -, hqrΩ, hqr⟩ := exists_rational_norm_sub_lt hK hU' hKU'
    (hfill.compl_inter_connectedComponentIn_nonempty hK.isClosed hKΩ) hq
    (ε := ε / (M + 1)) (by positivity)
  set r : ℂ → ℂ := fun z ↦ p_r.eval z / q_r.eval z
  set W : Set ℂ := {z : ℂ | q_r.eval z ≠ 0}
  have hW_open : IsOpen W := isOpen_ne_fun q_r.differentiable.continuous continuous_const
  have hΩW : Ω ⊆ W := fun z hz h0 ↦ (hqrΩ z h0).1 hz
  have hrW : DifferentiableOn ℂ r W :=
    p_r.differentiable.differentiableOn.div q_r.differentiable.differentiableOn fun _ hz ↦ hz
  refine ⟨fun z ↦ P.eval z + Q z * r z,
    P.differentiable.differentiableOn.add (hQ_diff.differentiableOn.mul (hrW.mono hΩW)),
    fun z hz ↦ ?_, fun a ha k hk ↦ ?_⟩
  · have hfg : f z - (P.eval z + Q z * r z) = Q z * (q z - r z) := by
      linear_combination hq_eq z (hKU' hz)
    have hQz : ‖Q z‖ ≤ M := (hM₀ ⟨z, hz, rfl⟩).trans (le_max_left _ _)
    rw [hfg, norm_mul]
    calc ‖Q z‖ * ‖q z - r z‖ ≤ M * (ε / (M + 1)) :=
          mul_le_mul hQz (hqr z hz).le (norm_nonneg _) hM0
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  · have hra : AnalyticAt ℂ r a := hrW.analyticAt (hW_open.mem_nhds (hΩW (hSΩ ha)))
    rw [iteratedDeriv_fun_add (P.differentiable.analyticAt a).contDiffAt
      ((hQ_diff.analyticAt a).fun_mul hra).contDiffAt,
      iteratedDeriv_prod_pow_sub_mul_eq_zero S m ha hra hk, add_zero, hP a ha k hk]

end TauCeti
