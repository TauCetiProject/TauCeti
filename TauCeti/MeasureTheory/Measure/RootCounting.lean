/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import TauCeti.MeasureTheory.Measure.FiniteMeasure.Basic

/-!
# Measures concentrating on the roots of a polynomial

Let `V : Fin m → ℂ` list the roots, with multiplicity, of the monic polynomial
`P(x) = ∏ᵢ (x - V i)`. This file proves the *compact moment lemma*: a bounded signed measure on
`ℂ` whose holomorphic moments are the power sums of the roots, whose negative part is small and
which gives small mass to `|P|²` is close, uniformly, to the counting measure `∑ᵢ δ_{V i}`.

Write the signed measure as `μ - ν` with `μ` and `ν` finite measures carried by the closed ball
`closedBall 0 ρ`, which also contains the roots. Suppose that

* the first `m` moments are those of the roots, `∫ xᵏ dμ - ∫ xᵏ dν = ∑ᵢ (V i)ᵏ` for `k < m`
  (for `k = 0` this says that the total mass is `m`);
* the negative part is small, `ν(ℂ) ≤ ε`;
* the variance of `P` is small, `∫ |P(x)|² dμ ≤ ε`.

Then for every test function `f : ℂ → ℂ` that is `L`-Lipschitz and bounded by `B` on the ball,

`‖∫ f dμ - ∫ f dν - ∑ᵢ f (V i)‖ ≤ δ`,

where `ε > 0` depends only on `m`, `ρ`, `L`, `B` and `δ`
(`TauCeti.exists_pos_forall_norm_integral_sub_integral_sub_sum_le`). For `L = B = 1` this says
that `μ - ν` converges to the counting measure of the roots in the bounded-Lipschitz distance,
uniformly in the measures and in the roots, as `ε → 0`. No rate is asserted; `ε` comes from a
compactness argument. The roots may collide, and the conclusion is uniform across collisions: no
separation of the roots is assumed.

The proof is by contradiction and compactness. Along a sequence of counterexamples with
`ε → 0`, the measures `μ` (of mass at most `m + 1`, carried by the ball) have a narrow cluster
point by Prokhorov's theorem, the roots have a cluster point in the ball, and the test functions,
restricted to the ball, have a uniform cluster point by the Arzelà–Ascoli theorem. In the limit
`ν` disappears, `∫ |P|² dμ = 0` forces the limit measure to be carried by the limiting roots, and
its first `m` moments are their power sums. Such a measure is the counting measure of the roots
(`TauCeti.eq_sum_dirac_of_ae_exists_eq`): integrating the Lagrange interpolation polynomial of a
function on the at most `m` distinct roots, a polynomial of degree less than `m`, computes the
integral of the function from the moments alone. This contradicts the uniform lower bound on the
error.

Applied to the mixed moments `x^ℓ conj x`, which are Lipschitz and bounded on the ball, the lemma
shows that `∫ x^ℓ conj x dμ - ∫ x^ℓ conj x dν - ∑ᵢ (V i)^ℓ conj (V i)` tends to zero uniformly
(`TauCeti.exists_pos_forall_norm_integral_pow_mul_conj_sub_integral_sub_sum_le`).

In Taubes's analysis of Seiberg–Witten solutions near a pseudoholomorphic curve, `μ - ν` is the
rescaled curvature slice of the solution on a normal fibre, of total flux `m`, and `V` are the
roots of the monic polynomial whose coefficients are the Newton coefficients of its moments, so
that the power sums of the roots are the moments `M_k`. The lemma turns the smallness of the
negative mass and of the Newton-polynomial variance into the smallness of the mixed-moment errors
`Q_ℓ - ∑ᵢ (V i)^ℓ conj (V i)`, which enter the `\bar∂`-equation of the Newton coefficients
(`TauCeti.conjWirtingerDeriv_add_esymm_erase_eq_of_newton`). A multiset of roots of cardinality
`m` is turned into a tuple `V` by enumerating it.

## Main results

* `TauCeti.integral_eq_sum_of_ae_exists_eq`, `TauCeti.eq_sum_dirac_of_ae_exists_eq`: a finite
  measure carried by the points `V i` whose first `m` moments are their power sums is the counting
  measure `∑ᵢ δ_{V i}`.
* `TauCeti.exists_pos_forall_norm_integral_sub_integral_sub_sum_le`: the compact moment lemma.
* `TauCeti.exists_pos_forall_norm_integral_pow_mul_conj_sub_integral_sub_sum_le`: the mixed-moment
  errors tend to zero uniformly.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open MeasureTheory Filter Topology Metric Polynomial
open scoped BoundedContinuousFunction ComplexConjugate NNReal

namespace TauCeti

section Counting

variable {m : ℕ} {μ : Measure ℂ} [IsFiniteMeasure μ] {V : Fin m → ℂ}

/-- **A measure on the roots with the moments of the roots integrates like their counting
measure.** Let `μ` be a finite measure on `ℂ` carried by the points `V i`, `i < m`, whose first
`m` moments are the power sums of these points, `∫ xᵏ dμ = ∑ᵢ (V i)ᵏ` for `k < m`. Then every
function `g : ℂ → ℂ` has `∫ g dμ = ∑ᵢ g (V i)`. -/
theorem integral_eq_sum_of_ae_exists_eq (hμ : ∀ᵐ x ∂μ, ∃ i, x = V i)
    (hmom : ∀ k < m, ∫ x, x ^ k ∂μ = ∑ i, V i ^ k) (g : ℂ → ℂ) :
    ∫ x, g x ∂μ = ∑ i, g (V i) := by
  classical
  -- Polynomials of degree less than `m` integrate like the counting measure, by the moments.
  have hpoly (p : ℂ[X]) (hp : p.degree < m) : ∫ x, p.eval x ∂μ = ∑ i, p.eval (V i) := by
    rcases eq_or_ne p 0 with rfl | hp0
    · simp
    have hn : p.natDegree < m := (natDegree_lt_iff_degree_lt hp0).2 hp
    simp_rw [eval_eq_sum_range' hn]
    -- Each monomial is bounded on the points `V i`, which carry `μ`, hence integrable.
    have hint (k : ℕ) : Integrable (fun x ↦ p.coeff k * x ^ k) μ :=
      .of_bound (continuous_const.mul (continuous_pow k)).aestronglyMeasurable
        (∑ i, ‖p.coeff k * V i ^ k‖) <| hμ.mono fun _ ⟨i, hi⟩ ↦ hi ▸
          Finset.single_le_sum (f := fun i ↦ ‖p.coeff k * V i ^ k‖) (fun _ _ ↦ norm_nonneg _)
            (Finset.mem_univ i)
    rw [integral_finsetSum (f := fun k x ↦ p.coeff k * x ^ k) _ fun k _ ↦ hint k]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [integral_const_mul, hmom k (Finset.mem_range.1 hk), Finset.mul_sum]
  -- The Lagrange interpolation polynomial of `g` on the distinct roots agrees with `g` there.
  set Z : Finset ℂ := Finset.univ.image V
  set p := Lagrange.interpolate Z id g
  have hinj : Set.InjOn id (Z : Set ℂ) := Function.injective_id.injOn
  have hpZ {z : ℂ} (hz : z ∈ Z) : p.eval z = g z :=
    Lagrange.eval_interpolate_at_node g hinj hz
  have hV (i : Fin m) : V i ∈ Z := Finset.mem_image_of_mem V (Finset.mem_univ i)
  have hdeg : p.degree < m := (Lagrange.degree_interpolate_lt g hinj).trans_le <| by
    exact_mod_cast (Finset.card_image_le.trans (Finset.card_univ.trans (Fintype.card_fin m)).le)
  calc ∫ x, g x ∂μ = ∫ x, p.eval x ∂μ :=
        integral_congr_ae <| hμ.mono fun _ ⟨i, hi⟩ ↦ hi ▸ (hpZ (hV i)).symm
    _ = ∑ i, p.eval (V i) := hpoly p hdeg
    _ = ∑ i, g (V i) := Finset.sum_congr rfl fun i _ ↦ hpZ (hV i)

/-- **A measure on the roots with the moments of the roots is their counting measure.** Let `μ`
be a finite measure on `ℂ` carried by the points `V i`, `i < m`, whose first `m` moments are the
power sums of these points, `∫ xᵏ dμ = ∑ᵢ (V i)ᵏ` for `k < m`. Then `μ = ∑ᵢ δ_{V i}`, the
counting measure of the points with multiplicity. -/
theorem eq_sum_dirac_of_ae_exists_eq (hμ : ∀ᵐ x ∂μ, ∃ i, x = V i)
    (hmom : ∀ k < m, ∫ x, x ^ k ∂μ = ∑ i, V i ^ k) :
    μ = ∑ i, Measure.dirac (V i) := by
  ext s hs
  have h := integral_eq_sum_of_ae_exists_eq hμ hmom fun x ↦ ((s.indicator 1 x : ℝ) : ℂ)
  rw [integral_complex_ofReal, integral_indicator_one hs, ← Complex.ofReal_sum,
    Complex.ofReal_inj] at h
  rw [FunLike.coe_sum, Finset.sum_apply, ← ENNReal.ofReal_toReal (measure_ne_top μ s),
    ← measureReal_def, h, ENNReal.ofReal_sum_of_nonneg (f := fun i ↦ s.indicator 1 (V i))
      fun _ _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Measure.dirac_apply' _ hs]
  by_cases hi : V i ∈ s <;> simp [hi]

end Counting

section Compactness

/-- **The compact moment lemma.** Let `m : ℕ`, `ρ : ℝ`, `L ≥ 0` and `B : ℝ`. For every `δ > 0`
there is `ε > 0` with the following property. Let `μ` and `ν` be finite measures on `ℂ` carried
by the closed ball `closedBall 0 ρ`, and let `V : Fin m → ℂ` be points of the ball, the roots with
multiplicity of the monic polynomial `P(x) = ∏ᵢ (x - V i)`. Suppose the signed measure `μ - ν`
has the moments of the roots, `∫ xᵏ dμ - ∫ xᵏ dν = ∑ᵢ (V i)ᵏ` for `k < m`, that its negative
part `ν` has mass at most `ε`, and that `∫ |P|² dμ ≤ ε`. Then for every `f : ℂ → ℂ` that is
`L`-Lipschitz and bounded by `B` on the ball, `‖∫ f dμ - ∫ f dν - ∑ᵢ f (V i)‖ ≤ δ`.

For `L = B = 1` this says that `μ - ν` is `δ`-close to the counting measure `∑ᵢ δ_{V i}` in the
bounded-Lipschitz distance, uniformly in `μ`, `ν` and the roots, which may collide. -/
theorem exists_pos_forall_norm_integral_sub_integral_sub_sum_le (m : ℕ) (ρ : ℝ) (L : ℝ≥0)
    (B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (V : Fin m → ℂ),
      μ (closedBall 0 ρ)ᶜ = 0 → ν (closedBall 0 ρ)ᶜ = 0 → (∀ i, V i ∈ closedBall (0 : ℂ) ρ) →
      (∀ k < m, ∫ x, x ^ k ∂μ - ∫ x, x ^ k ∂ν = ∑ i, V i ^ k) → ν.real Set.univ ≤ ε →
      ∫ x, ‖∏ i, (x - V i)‖ ^ 2 ∂μ ≤ ε →
      ∀ f : ℂ → ℂ, LipschitzOnWith L f (closedBall 0 ρ) →
        (∀ x ∈ closedBall (0 : ℂ) ρ, ‖f x‖ ≤ B) →
        ‖∫ x, f x ∂μ - ∫ x, f x ∂ν - ∑ i, f (V i)‖ ≤ δ := by
  classical
  set K := closedBall (0 : ℂ) ρ
  -- Argue by contradiction along a sequence of counterexamples with `ε = 1 / (n + 1)`.
  by_contra! hcon
  choose μ ν hμf hνf V hμK hνK hVK hmom hν hvar f hfL hfb herr using
    fun n : ℕ ↦ hcon (1 / (n + 1)) Nat.one_div_pos_of_nat
  have hK : IsCompact K := isCompact_closedBall 0 ρ
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  -- The masses of the `μ n` are at most `m + 1`.
  have hmass (n : ℕ) : (μ n).real Set.univ ≤ m + 1 := by
    have hε : 1 / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by simp) (by positivity)
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using (hvar n).trans hε
    · have h := congrArg Complex.re (hmom n 0 hm)
      simp only [pow_zero, integral_const, Complex.real_smul, mul_one, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Complex.sub_re, Complex.ofReal_re,
        Complex.natCast_re] at h
      linarith [hν n]
  -- The data of the counterexamples lie in a compact set: the measures by Prokhorov's theorem,
  -- the roots in a product of balls, and the test functions on the ball by Arzelà–Ascoli.
  let C : ℝ≥0 := m + 1
  let μF : ℕ → FiniteMeasure ℂ := fun n ↦ ⟨μ n, hμf n⟩
  have hμF (n : ℕ) : ((μF n : FiniteMeasure ℂ) : Measure ℂ) = μ n := rfl
  let S₁ : Set (FiniteMeasure ℂ) := {μ | μ.mass ≤ C ∧ ∀ _ : ℕ, μ Kᶜ ≤ 0}
  have hS₁ : IsCompact S₁ := isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le
    (u := fun _ ↦ 0) (K := fun _ ↦ K) C tendsto_const_nhds (fun _ ↦ hK) (Or.inr monotone_const)
  let A : Set (K →ᵇ ℂ) := {g | LipschitzWith L g ∧ ∀ x, ‖g x‖ ≤ B}
  have hS₃ : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall 0 B) (isCompact_closedBall 0 B) A
      (fun g x hg ↦ mem_closedBall_zero_iff.2 (hg.2 x))
      (LipschitzWith.uniformEquicontinuous (fun g : A ↦ ⇑(g : K →ᵇ ℂ)) L
        fun g ↦ g.2.1).equicontinuous
  let F : ℕ → K →ᵇ ℂ := fun n ↦
    BoundedContinuousFunction.mkOfCompact ⟨K.domRestrict (f n), (hfL n).to_restrict.continuous⟩
  have hFA (n : ℕ) : F n ∈ A := ⟨(hfL n).to_restrict, fun x ↦ hfb n x x.2⟩
  let S := S₁ ×ˢ (Set.univ.pi fun _ : Fin m ↦ K) ×ˢ closure A
  have hS : IsCompact S := hS₁.prod ((isCompact_univ_pi fun _ ↦ hK).prod hS₃)
  let u : ℕ → FiniteMeasure ℂ × (Fin m → ℂ) × (K →ᵇ ℂ) := fun n ↦ (μF n, V n, F n)
  have hu (n : ℕ) : u n ∈ S := by
    refine ⟨⟨?_, fun _ ↦ ?_⟩, fun i _ ↦ hVK n i, subset_closure (hFA n)⟩
    · rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass, hμF, ← ofReal_measureReal,
        ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (by simpa [C] using hmass n)
    · rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, hμF, hμK n]
      simp
  obtain ⟨⟨μ₀, V₀, F₀⟩, ⟨⟨-, hμ₀K⟩, hV₀K, -⟩, hcl⟩ :=
    hS.exists_mapClusterPt (f := atTop) (tendsto_principal.2 (Eventually.of_forall hu))
  obtain ⟨U, hU, hUlim⟩ := mapClusterPt_iff_ultrafilter.1 hcl
  have hμlim : Tendsto μF U (𝓝 μ₀) := (continuous_fst.tendsto _).comp hUlim
  have hVlim : Tendsto V U (𝓝 V₀) := ((continuous_fst.comp continuous_snd).tendsto _).comp hUlim
  have hFlim : Tendsto F U (𝓝 F₀) := ((continuous_snd.comp continuous_snd).tendsto _).comp hUlim
  have hεlim : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) U (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hU
  have hμ₀K' : (μ₀ : Measure ℂ) Kᶜ = 0 := by
    have h := hμ₀K 0
    rwa [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_zero,
      nonpos_iff_eq_zero] at h
  -- Integrals against `μ n` of functions converging uniformly on the ball converge.
  have hlim {𝕜 : Type} [RCLike 𝕜] {gs : ℕ → ℂ → 𝕜} {g : ℂ → 𝕜} (hgs : ∀ n, ContinuousOn (gs n) K)
      (hg : ContinuousOn g K) (hunif : TendstoUniformlyOn gs g U K) :
      Tendsto (fun n ↦ ∫ x, gs n x ∂μ n) U (𝓝 (∫ x, g x ∂(μ₀ : Measure ℂ))) :=
    FiniteMeasure.tendsto_integral_of_tendstoUniformlyOn_closedBall hμlim
      (Eventually.of_forall hμK) hμ₀K' hgs hg hunif
  -- Integrals against `ν n` of functions bounded by `C` on the ball tend to zero.
  have hνlim {gs : ℕ → ℂ → ℂ} {C : ℝ} (hgs : ∀ n, ∀ x ∈ K, ‖gs n x‖ ≤ C) :
      Tendsto (fun n ↦ ∫ x, gs n x ∂ν n) U (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n : ℕ ↦ |C| * (1 / ((n : ℝ) + 1))) (fun n ↦ ?_) ?_
    · refine (norm_integral_le_of_norm_le_const ((show ∀ᵐ x ∂ν n, x ∈ K from
        mem_ae_iff.2 (hνK n)).mono fun x hx ↦ (hgs n x hx).trans (le_abs_self C))).trans ?_
      exact mul_le_mul_of_nonneg_left (hν n) (abs_nonneg C)
    · simpa using hεlim.const_mul |C|
  -- The limit measure is carried by the limiting roots.
  have hsupp : ∀ᵐ x ∂(μ₀ : Measure ℂ), ∃ i, x = V₀ i := by
    let G : (Fin m → ℂ) → K → ℝ := fun W x ↦ ‖∏ i, ((x : ℂ) - W i)‖ ^ 2
    have hG : Continuous ↿G := by
      refine Continuous.pow (Continuous.norm ?_) 2
      exact continuous_finsetProd _ fun i _ ↦
        (continuous_subtype_val.comp continuous_snd).sub ((continuous_apply i).comp continuous_fst)
    have hunif : TendstoUniformlyOn (fun n x ↦ ‖∏ i, (x - V n i)‖ ^ 2)
        (fun x ↦ ‖∏ i, (x - V₀ i)‖ ^ 2) U K := by
      rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
      exact fun s hs ↦ hVlim.eventually (Continuous.tendstoUniformly G hG V₀ s hs)
    have hcont (W : Fin m → ℂ) : Continuous fun x : ℂ ↦ ‖∏ i, (x - W i)‖ ^ 2 :=
      (continuous_finsetProd _ fun i _ ↦ continuous_id.sub continuous_const).norm.pow 2
    have h := hlim (fun n ↦ (hcont (V n)).continuousOn) (hcont V₀).continuousOn hunif
    have h0 : ∫ x, ‖∏ i, (x - V₀ i)‖ ^ 2 ∂(μ₀ : Measure ℂ) ≤ 0 :=
      le_of_tendsto_of_tendsto' h hεlim hvar
    have hint : Integrable (fun x ↦ ‖∏ i, (x - V₀ i)‖ ^ 2) (μ₀ : Measure ℂ) := by
      have h := (hcont V₀).continuousOn.integrableOn_compact (μ := (μ₀ : Measure ℂ)) hK
      rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hμ₀K')] at h
    have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ by positivity) hint).1
      (le_antisymm h0 (integral_nonneg fun x ↦ by positivity))
    filter_upwards [hae] with x hx
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 (by simpa using hx)
    exact ⟨i, sub_eq_zero.1 (norm_eq_zero.1 hi)⟩
  -- The limit measure has the moments of the limiting roots.
  have hmom₀ (k : ℕ) (hk : k < m) :
      ∫ x, x ^ k ∂(μ₀ : Measure ℂ) = ∑ i, V₀ i ^ k := by
    have h₁ : Tendsto (fun n ↦ ∫ x, x ^ k ∂μ n) U (𝓝 (∫ x, x ^ k ∂(μ₀ : Measure ℂ))) :=
      hlim (fun _ ↦ (continuous_pow k).continuousOn) (continuous_pow k).continuousOn
        fun _ hs ↦ Eventually.of_forall fun _ _ _ ↦ refl_mem_uniformity hs
    have hsum : Tendsto (fun n ↦ ∑ i, V n i ^ k) U (𝓝 (∑ i, V₀ i ^ k)) :=
      tendsto_finsetSum _ fun i _ ↦
        ((continuous_pow k).tendsto _).comp (((continuous_apply i).tendsto _).comp hVlim)
    have hν0 : Tendsto (fun n ↦ ∫ x, x ^ k ∂ν n) U (𝓝 0) :=
      hνlim (gs := fun _ x ↦ x ^ k) (C := |ρ| ^ k) fun _ x hx ↦ by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg x)
          ((mem_closedBall_zero_iff.1 hx).trans (le_abs_self ρ)) k
    have h₂ : Tendsto (fun n ↦ ∫ x, x ^ k ∂μ n) U (𝓝 (∑ i, V₀ i ^ k + 0)) :=
      (hsum.add hν0).congr fun n ↦ by rw [← hmom n k hk, sub_add_cancel]
    rw [add_zero] at h₂
    exact tendsto_nhds_unique h₁ h₂
  -- Hence the limit measure is the counting measure of the limiting roots.
  let f₀ : ℂ → ℂ := fun x ↦ if hx : x ∈ K then F₀ ⟨x, hx⟩ else 0
  have hf₀ : K.domRestrict f₀ = F₀ := funext fun x ↦ by simp [f₀, x.2]
  have hcount := integral_eq_sum_of_ae_exists_eq hsupp hmom₀ f₀
  -- The errors converge to the error of the limit, which is zero.
  have h₁ : Tendsto (fun n ↦ ∫ x, f n x ∂μ n) U (𝓝 (∫ x, f₀ x ∂(μ₀ : Measure ℂ))) := by
    refine hlim (fun n ↦ (hfL n).continuousOn) ?_ ?_
    · rw [continuousOn_iff_continuous_domRestrict, hf₀]
      exact F₀.continuous
    · rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
      have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 hFlim
      rwa [← hf₀] at h
  have h₂ : Tendsto (fun n ↦ ∫ x, f n x ∂ν n) U (𝓝 0) := hνlim (hfb ·)
  have h₃ : Tendsto (fun n ↦ ∑ i, f n (V n i)) U (𝓝 (∑ i, f₀ (V₀ i))) := by
    refine tendsto_finsetSum _ fun i _ ↦ ?_
    have hVi : Tendsto (fun n ↦ (⟨V n i, hVK n i⟩ : K)) U (𝓝 ⟨V₀ i, hV₀K i trivial⟩) :=
      tendsto_subtype_rng.2 (((continuous_apply i).tendsto _).comp hVlim)
    have h := (continuous_eval.tendsto (F₀, ⟨V₀ i, hV₀K i trivial⟩)).comp (hFlim.prodMk_nhds hVi)
    rw [show f₀ (V₀ i) = F₀ ⟨V₀ i, hV₀K i trivial⟩ by simp [f₀, hV₀K i trivial]]
    exact h
  have h := ((h₁.sub h₂).sub h₃).norm
  rw [hcount, sub_zero, sub_self, norm_zero] at h
  exact hδ.not_ge (ge_of_tendsto h (Eventually.of_forall fun n ↦ (herr n).le))

/-- **The mixed moments converge.** Let `m, ℓ : ℕ` and `ρ : ℝ`. For every `δ > 0` there is
`ε > 0` with the following property. Let `μ` and `ν` be finite measures on `ℂ` carried by
`closedBall 0 ρ` and let `V : Fin m → ℂ` be points of the ball, with
`∫ xᵏ dμ - ∫ xᵏ dν = ∑ᵢ (V i)ᵏ` for `k < m`, `ν(ℂ) ≤ ε` and `∫ |∏ᵢ (x - V i)|² dμ ≤ ε`. Then the
mixed moment `Q_ℓ = ∫ x^ℓ conj x d(μ - ν)` is `δ`-close to `∑ᵢ (V i)^ℓ conj (V i)`. -/
theorem exists_pos_forall_norm_integral_pow_mul_conj_sub_integral_sub_sum_le (m : ℕ) (ρ : ℝ)
    (ℓ : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (V : Fin m → ℂ),
      μ (closedBall 0 ρ)ᶜ = 0 → ν (closedBall 0 ρ)ᶜ = 0 → (∀ i, V i ∈ closedBall (0 : ℂ) ρ) →
      (∀ k < m, ∫ x, x ^ k ∂μ - ∫ x, x ^ k ∂ν = ∑ i, V i ^ k) → ν.real Set.univ ≤ ε →
      ∫ x, ‖∏ i, (x - V i)‖ ^ 2 ∂μ ≤ ε →
      ‖∫ x, x ^ ℓ * conj x ∂μ - ∫ x, x ^ ℓ * conj x ∂ν - ∑ i, V i ^ ℓ * conj (V i)‖ ≤ δ := by
  have hg : ContDiff ℝ 1 fun x : ℂ ↦ x ^ ℓ * conj x :=
    (contDiff_id.pow ℓ).mul Complex.conjCLE.contDiff
  obtain ⟨L, hL⟩ := hg.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall 0 ρ)
    (isCompact_closedBall 0 ρ)
  obtain ⟨B, hB⟩ :=
    (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn hg.continuous.continuousOn
  obtain ⟨ε, hε, h⟩ := exists_pos_forall_norm_integral_sub_integral_sub_sum_le m ρ L B hδ
  exact ⟨ε, hε, fun μ ν _ _ V hμ hν hV hmom hνε hvar ↦
    h μ ν V hμ hν hV hmom hνε hvar _ hL hB⟩

end Compactness

end TauCeti
