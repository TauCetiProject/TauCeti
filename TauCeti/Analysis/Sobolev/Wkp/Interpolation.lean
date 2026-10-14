/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Zero
public import TauCeti.MeasureTheory.Function.Lp.Translation
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Density

/-!
# The interpolation inequality for the gradient

The `Lᵖ` norm of the gradient of a function is controlled by the `Lᵖ` norms of the function and
of its Hessian: for every `ε > 0`,

`‖∇u‖_p ≤ ε ‖D²u‖_p + (n² / ε) ‖u‖_p`, `1 ≤ p < ∞`, `n = dim E`.

This is how a first-order term is absorbed into the left-hand side of a second-order estimate. In
the `W^{2,p}` theory of non-divergence-form operators with continuous coefficients, the
Calderón–Zygmund estimate is applied to `ζ u` for cutoffs `ζ` supported on small balls, and the
derivatives falling on `ζ` produce the terms `‖∇u‖_p` that this inequality absorbs.

* `ContDiff.eLpNorm_fderiv_apply_le`: for a `C²` function `u` and a direction `h`,
  `‖Du · h‖_p ≤ ε ‖h‖² ‖D²u‖_p + ε⁻¹ ‖u‖_p`.
* `ContDiff.eLpNorm_fderiv_le`: the same for the full derivative on a finite-dimensional inner
  product space, with constants `ε` and `n² / ε`.
* `TauCeti.Wkp.norm_iteratedGradient_lowerOrder_le_of_mem_wkp0Submodule`: the inequality for
  `u ∈ W^{2,p}_0(Ω)`, on any open `Ω`, with the weak gradient and the weak Hessian.
* `TauCeti.Wkp.norm_iteratedGradient_lowerOrder_le`: the inequality on all of `W^{2,p}(E)`.

## The argument

Write `δ_t u = t⁻¹ (u(· + t h) - u)` for the difference quotient. Halving the step changes it by a
second difference, `δ_{t/2} u - δ_t u = -t⁻¹ (u(· + t h) - 2 u(· + t h / 2) + u)`, whose `Lᵖ` norm
is at most `(t / 4) ‖h‖² ‖D²u‖_p` by the second-order translation estimate
`ContDiff.eLpNorm_comp_add_add_sub_sub_le_mul_eLpNorm_fderiv_fderiv`. Starting from
`‖δ_{2ε} u‖_p ≤ ε⁻¹ ‖u‖_p` and summing over the dyadic steps `2ε / 2ᵏ` gives
`‖δ_{2ε/2ᵏ} u‖_p ≤ ε ‖h‖² ‖D²u‖_p + ε⁻¹ ‖u‖_p` for every `k`. The difference quotients converge
pointwise to `Du · h`, so Fatou's lemma bounds `‖Du · h‖_p` in the same way. Summing over an
orthonormal basis, `‖Du‖ ≤ ∑ᵢ |Du · eᵢ|` gives the gradient bound. For `W^{2,p}_0(Ω)` both sides
are continuous in the Sobolev norm, and the test functions are dense.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.28.
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 5.2.
-/

public section

noncomputable section

open MeasureTheory Filter Topology TopologicalSpace Module
open scoped ENNReal

section Smooth

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F] {mu : Measure E}
  [SFinite mu] [mu.IsAddRightInvariant] {u : E → F} {p : ℝ≥0∞}

/-- **The interpolation inequality for a directional derivative.** For a `C²` function `u`, a
direction `h` and `ε > 0`,

`‖Du · h‖_p ≤ ε ‖h‖² ‖D²u‖_p + ε⁻¹ ‖u‖_p`, `1 ≤ p < ∞`.

No support, integrability or boundedness hypothesis is needed. -/
theorem ContDiff.eLpNorm_fderiv_apply_le (hu : ContDiff ℝ 2 u) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (h : E) {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (fun x => fderiv ℝ u x h) p mu ≤
      ENNReal.ofReal ε * ‖h‖ₑ ^ 2 * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu +
        ENNReal.ofReal ε⁻¹ * eLpNorm u p mu := by
  set B := ENNReal.ofReal ε * ‖h‖ₑ ^ 2 * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu
  set U := eLpNorm u p mu
  -- `c k = 2ᵏ / (2ε)` is the inverse of the `k`-th dyadic step `2ε / 2ᵏ`, and `Q k` is the
  -- difference quotient with that step.
  set c : ℕ → ℝ := fun k => 2 ^ k / (2 * ε) with hc_def
  set Q : ℕ → E → F := fun k => c k • fun x => u (x + (c k)⁻¹ • h) - u x with hQ_def
  have hc_pos (k : ℕ) : 0 < c k := by positivity
  have hcont : Continuous u := hu.continuous
  -- The quotient with the first step `2ε` is at most `ε⁻¹ ‖u‖_p`.
  have hQ0 : eLpNorm (Q 0) p mu ≤ ENNReal.ofReal ε⁻¹ * U := by
    have htr : eLpNorm (fun x => u (x + (c 0)⁻¹ • h)) p mu = U :=
      eLpNorm_comp_measurePreserving (g := u) hcont.aestronglyMeasurable
        (measurePreserving_add_right mu _)
    calc eLpNorm (Q 0) p mu
        = ‖c 0‖ₑ * eLpNorm (fun x => u (x + (c 0)⁻¹ • h) - u x) p mu :=
          eLpNorm_const_smul _ _ _ _
      _ ≤ ‖c 0‖ₑ * (U + U) := by
          gcongr
          exact (eLpNorm_sub_le (f := fun x => u (x + (c 0)⁻¹ • h)) hp).trans_eq (by rw [htr])
      _ = ENNReal.ofReal ε⁻¹ * U := by
          rw [← two_mul, ← mul_assoc, Real.enorm_of_nonneg (hc_pos 0).le,
            ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (hc_pos 0).le]
          congr 2
          simp only [hc_def, pow_zero]
          field_simp
  -- Halving the step costs at most `2⁻ᵏ⁻¹ ε ‖h‖² ‖D²u‖_p`, by the second-order translation
  -- estimate.
  have hstep (k : ℕ) : eLpNorm (Q (k + 1)) p mu ≤ eLpNorm (Q k) p mu + 2⁻¹ ^ (k + 1) * B := by
    obtain ⟨s, hs⟩ : ∃ s, (c (k + 1))⁻¹ = s := ⟨_, rfl⟩
    have hcs : c (k + 1) = 2 * c k := by
      simp only [hc_def, pow_succ]
      ring
    have hsh : (c k)⁻¹ • h = s • h + s • h := by
      rw [← add_smul, ← hs, hcs]
      congr 1
      field_simp [(hc_pos k).ne']
      ring
    set D : E → F := fun x => u (x + s • h + s • h) - u (x + s • h) - (u (x + s • h) - u x)
    have hQD : Q (k + 1) = Q k - c k • D := by
      ext x
      simp only [hQ_def, D, Pi.sub_apply, Pi.smul_apply, hs, hsh, ← add_assoc]
      rw [hcs]
      module
    have hD : eLpNorm D p mu ≤ ‖s • h‖ₑ * ‖s • h‖ₑ *
        eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu :=
      hu.eLpNorm_comp_add_add_sub_sub_le_mul_eLpNorm_fderiv_fderiv hp hp' _ _
    have hcoef : ‖c k‖ₑ * (‖s • h‖ₑ * ‖s • h‖ₑ) = 2⁻¹ ^ (k + 1) * ENNReal.ofReal ε * ‖h‖ₑ ^ 2 := by
      have hreal : c k * s ^ 2 = ε * 2⁻¹ ^ (k + 1) := by
        rw [← hs, hcs, inv_pow (2 : ℝ) (k + 1)]
        simp only [hc_def]
        field_simp
        ring
      rw [enorm_smul, ← pow_two, mul_pow, ← mul_assoc, ← enorm_pow, ← enorm_mul, hreal,
        enorm_mul, enorm_pow, enorm_inv two_ne_zero, Real.enorm_of_nonneg hε.le,
        Real.enorm_of_nonneg zero_le_two, ENNReal.ofReal_ofNat]
      ring
    calc eLpNorm (Q (k + 1)) p mu
        ≤ eLpNorm (Q k) p mu + eLpNorm (c k • D) p mu := by
          rw [hQD]
          exact eLpNorm_sub_le hp
      _ ≤ eLpNorm (Q k) p mu + 2⁻¹ ^ (k + 1) * B := by
          rw [eLpNorm_const_smul (c k) D]
          gcongr eLpNorm (Q k) p mu + ?_
          calc ‖c k‖ₑ * eLpNorm D p mu
              ≤ ‖c k‖ₑ * (‖s • h‖ₑ * ‖s • h‖ₑ * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu) := by
                gcongr
            _ = 2⁻¹ ^ (k + 1) * B := by
                rw [← mul_assoc, hcoef]
                simp only [B]
                ring
  -- Summing the dyadic steps bounds every difference quotient `Q k` by the right-hand side.
  have hQ (k : ℕ) : eLpNorm (Q k) p mu + 2⁻¹ ^ k * B ≤ B + ENNReal.ofReal ε⁻¹ * U := by
    induction k with
    | zero =>
        rw [pow_zero, one_mul, add_comm]
        gcongr
    | succ k ih =>
        calc eLpNorm (Q (k + 1)) p mu + 2⁻¹ ^ (k + 1) * B
            ≤ eLpNorm (Q k) p mu + 2⁻¹ ^ (k + 1) * B + 2⁻¹ ^ (k + 1) * B := by
              gcongr
              exact hstep k
          _ = eLpNorm (Q k) p mu + 2⁻¹ ^ k * B := by
              rw [add_assoc, ← add_mul, pow_succ, ← mul_add, ENNReal.inv_two_add_inv_two,
                mul_one]
          _ ≤ B + ENNReal.ofReal ε⁻¹ * U := ih
  -- The difference quotients converge pointwise to `Du · h`; conclude by Fatou's lemma.
  have hlim (x : E) : Tendsto (fun k => Q k x) atTop (𝓝 (fderiv ℝ u x h)) := by
    have hc : Tendsto (fun k => ‖c k‖) atTop atTop :=
      tendsto_norm_atTop_atTop.comp
        ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_div_const (by positivity))
    exact ((hu.differentiable (by norm_num)) x).hasFDerivAt.lim h hc
  have hQcont (k : ℕ) : Continuous (Q k) := by
    simp only [hQ_def]
    fun_prop
  calc eLpNorm (fun x => fderiv ℝ u x h) p mu
      ≤ atTop.liminf fun k => eLpNorm (Q k) p mu :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun k => (hQcont k).aestronglyMeasurable) _
          ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable
          (ae_of_all _ hlim)
    _ ≤ B + ENNReal.ofReal ε⁻¹ * U :=
        liminf_le_of_frequently_le' (Frequently.of_forall fun k => le_self_add.trans (hQ k))

end Smooth

section InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {mu : Measure E}
  [SFinite mu] [mu.IsAddRightInvariant] {u : E → F} {p : ℝ≥0∞}

/-- **The interpolation inequality for the derivative.** For a `C²` function `u` on a real inner
product space `E` of dimension `n` and `ε > 0`,

`‖Du‖_p ≤ ε ‖D²u‖_p + (n² / ε) ‖u‖_p`, `1 ≤ p < ∞`.

No support, integrability or boundedness hypothesis is needed. -/
theorem ContDiff.eLpNorm_fderiv_le (hu : ContDiff ℝ 2 u) (hp : 1 ≤ p) (hp' : p ≠ ∞) {ε : ℝ}
    (hε : 0 < ε) :
    eLpNorm (fderiv ℝ u) p mu ≤
      ENNReal.ofReal ε * eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu +
        ENNReal.ofReal ((finrank ℝ E) ^ 2 / ε) * eLpNorm u p mu := by
  set n := finrank ℝ E
  set b := stdOrthonormalBasis ℝ E
  set A := eLpNorm (fderiv ℝ (fderiv ℝ u)) p mu
  set U := eLpNorm u p mu
  have hmeas (i : Fin n) : AEStronglyMeasurable (fun x => fderiv ℝ u x (b i)) mu :=
    ((hu.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable
  -- Each partial derivative obeys the directional inequality with `ε / n` in place of `ε`.
  have hpartial (i : Fin n) : eLpNorm (fun x => fderiv ℝ u x (b i)) p mu ≤
      ENNReal.ofReal (ε / n) * A + ENNReal.ofReal (n / ε) * U := by
    have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Fin.pos i)
    have h := hu.eLpNorm_fderiv_apply_le (mu := mu) hp hp' (b i) (div_pos hε hn)
    rwa [← ofReal_norm, b.orthonormal.1 i, ENNReal.ofReal_one, one_pow, mul_one,
      inv_div] at h
  calc eLpNorm (fderiv ℝ u) p mu
      ≤ eLpNorm (∑ i, fun x => ‖fderiv ℝ u x (b i)‖) p mu :=
        eLpNorm_mono_real (hu.continuous_fderiv (by norm_num)).aestronglyMeasurable fun x => by
          rw [Finset.sum_apply]
          exact (fderiv ℝ u x).opNorm_le_sum_norm_apply_orthonormalBasis b
    _ ≤ ∑ i, eLpNorm (fun x => ‖fderiv ℝ u x (b i)‖) p mu := eLpNorm_sum_le hp
    _ = ∑ i, eLpNorm (fun x => fderiv ℝ u x (b i)) p mu :=
        Finset.sum_congr rfl fun i _ => eLpNorm_norm _ (hmeas i)
    _ ≤ ∑ _i : Fin n, (ENNReal.ofReal (ε / n) * A + ENNReal.ofReal (n / ε) * U) :=
        Finset.sum_le_sum fun i _ => hpartial i
    _ ≤ ENNReal.ofReal ε * A + ENNReal.ofReal (n ^ 2 / ε) * U := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add,
          ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        gcongr
        · rcases eq_or_ne (n : ℝ) 0 with hn | hn
          · rw [hn, zero_mul]
            exact hε.le
          · rw [mul_div_cancel₀ _ hn]
        · rw [mul_div_assoc', sq]

end InnerProductSpace

namespace TauCeti

section Sobolev

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The interpolation inequality in `W^{2,p}_0(Ω)`.** Let `Ω ⊆ E` be open, `1 ≤ p < ∞` and
`ε > 0`. Every `u ∈ W^{2,p}_0(Ω)` satisfies

`‖∇u‖_p ≤ ε ‖D²u‖_p + (n² / ε) ‖u‖_p`, `n = dim E`,

where `∇u` is the weak gradient `TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)` and
`D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. No boundedness or boundary
regularity of `Ω` is needed. -/
theorem Wkp.norm_iteratedGradient_lowerOrder_le_of_mem_wkp0Submodule (hp : p ≠ ∞)
    {u : Wkp mu Omega p 2} (hu : u ∈ wkp0Submodule mu Omega p 2) {ε : ℝ} (hε : 0 < ε) :
    ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ ≤
      ε * ‖Wkp.iteratedGradient 1 u‖ + (finrank ℝ E) ^ 2 / ε * ‖Wkp.value 2 u‖ := by
  -- Both sides are continuous on `W^{2,p}(Ω)`, so it suffices to treat test functions.
  refine wkp0Submodule_subset_of_isClosed 2
    (s := {v | ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 v)‖ ≤
      ε * ‖Wkp.iteratedGradient 1 v‖ + (finrank ℝ E) ^ 2 / ε * ‖Wkp.value 2 v‖})
    (isClosed_le ?_ ?_) (fun φ => ?_) hu
  · simp only [← Wkp.iteratedGradientL_apply, ← Wkp.lowerOrderL_apply]
    exact ((Wkp.iteratedGradientL 0).continuous.comp (Wkp.lowerOrderL 1).continuous).norm
  · simp only [← Wkp.iteratedGradientL_apply, ← Wkp.valueL_apply]
    exact (continuous_const.mul (Wkp.iteratedGradientL 1).continuous.norm).add
      (continuous_const.mul (Wkp.valueL 2).continuous.norm)
  -- For a test function `φ`, the three norms are the `Lᵖ` norms of `Dφ`, `D²φ` and `φ` on all of
  -- `E`, since `φ` and its derivatives vanish outside `Ω`.
  have hφ : ContDiff ℝ 2 (φ : E → ℝ) := φ.contDiff.of_le (by simp)
  have hsupp (i : ℕ) : Function.support (iteratedFDeriv ℝ i (φ : E → ℝ)) ⊆ Omega :=
    (support_iteratedFDeriv_subset i).trans φ.tsupport_subset
  have hcont (i : ℕ) (hi : i ≤ 2) : Continuous (iteratedFDeriv ℝ i (φ : E → ℝ)) :=
    hφ.continuous_iteratedFDeriv (by exact_mod_cast hi)
  have hD2cont : Continuous (fderiv ℝ (fderiv ℝ (φ : E → ℝ))) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hval (k : ℕ) : (Wkp.value k (Wkp.ofTestFunctionₗ (mu := mu) (p := p) k φ) : E → ℝ)
      =ᵐ[mu.restrict Omega] φ := by
    rw [Wkp.value_ofTestFunctionₗ]
    exact testFunctionLp_apply_ae p φ
  -- `eLpNorm_restrict_eq_of_support_subset` is applied to the pointwise norms: for the
  -- derivative fields themselves, unifying its `ENormedAddMonoid` instance is very slow.
  have hrestrict1 : eLpNorm (fderiv ℝ (φ : E → ℝ)) p (mu.restrict Omega) =
      eLpNorm (fderiv ℝ (φ : E → ℝ)) p mu := by
    have hm := (hφ.continuous_fderiv (by norm_num)).aestronglyMeasurable (μ := mu)
    rw [← eLpNorm_norm _ hm.restrict, ← eLpNorm_norm _ hm]
    exact eLpNorm_restrict_eq_of_support_subset hm.norm
      (by simpa using (support_fderiv_subset ℝ).trans φ.tsupport_subset)
  have hrestrict2 : eLpNorm (iteratedFDeriv ℝ 2 (φ : E → ℝ)) p (mu.restrict Omega) =
      eLpNorm (iteratedFDeriv ℝ 2 (φ : E → ℝ)) p mu := by
    have hm := (hcont 2 le_rfl).aestronglyMeasurable (μ := mu)
    rw [← eLpNorm_norm _ hm.restrict, ← eLpNorm_norm _ hm]
    exact eLpNorm_restrict_eq_of_support_subset hm.norm (by simpa using hsupp 2)
  have hE1 : eLpNorm (iteratedFDeriv ℝ 1 (φ : E → ℝ)) p (mu.restrict Omega) =
      eLpNorm (fderiv ℝ (φ : E → ℝ)) p (mu.restrict Omega) :=
    eLpNorm_congr_norm_ae (hcont 1 (by norm_num)).aestronglyMeasurable
      (hφ.continuous_fderiv (by norm_num)).aestronglyMeasurable
      (ae_of_all _ fun _ => norm_iteratedFDeriv_one _)
  have hE2 : eLpNorm (iteratedFDeriv ℝ 2 (φ : E → ℝ)) p mu =
      eLpNorm (fderiv ℝ (fderiv ℝ (φ : E → ℝ))) p mu :=
    eLpNorm_congr_norm_ae (hcont 2 le_rfl).aestronglyMeasurable hD2cont.aestronglyMeasurable
      (ae_of_all _ fun _ => (norm_iteratedFDeriv_fderiv (n := 1)).symm.trans
        (norm_iteratedFDeriv_one _))
  have hD : ‖Wkp.iteratedGradient 0
      (Wkp.lowerOrder 1 (Wkp.ofTestFunctionₗ (mu := mu) (p := p) 2 φ))‖ =
      (eLpNorm (fderiv ℝ (φ : E → ℝ)) p mu).toReal := by
    rw [Wkp.lowerOrder_ofTestFunctionₗ, Wkp.norm_iteratedGradient_eq_lpNorm_of_contDiffOn 0 _
      (hφ.of_le (by norm_num)).contDiffOn (hval 1), lpNorm, hE1, hrestrict1]
  have hD2 : ‖Wkp.iteratedGradient 1 (Wkp.ofTestFunctionₗ (mu := mu) (p := p) 2 φ)‖ =
      (eLpNorm (fderiv ℝ (fderiv ℝ (φ : E → ℝ))) p mu).toReal := by
    rw [Wkp.norm_iteratedGradient_eq_lpNorm_of_contDiffOn 1 _ hφ.contDiffOn (hval 2), lpNorm,
      hrestrict2, hE2]
  have hV : ‖Wkp.value 2 (Wkp.ofTestFunctionₗ (mu := mu) (p := p) 2 φ)‖ =
      (eLpNorm (φ : E → ℝ) p mu).toReal := by
    rw [Wkp.value_ofTestFunctionₗ, ← toReal_enorm, enorm_testFunctionLp_eq_eLpNorm]
  -- The smooth inequality, read in `ℝ`: all three seminorms are finite.
  have hA : eLpNorm (fderiv ℝ (fderiv ℝ (φ : E → ℝ))) p mu ≠ ∞ := by
    rw [← hE2, ← hrestrict2]
    exact (Wkp.memLp_iteratedFDeriv_of_contDiffOn 2 _ hφ.contDiffOn (hval 2) 2
      le_rfl).eLpNorm_ne_top
  have hU : eLpNorm (φ : E → ℝ) p mu ≠ ∞ := by
    rw [← enorm_testFunctionLp_eq_eLpNorm (mu := mu) p φ]
    exact enorm_ne_top
  rw [Set.mem_ofPred_eq, hD, hD2, hV]
  calc (eLpNorm (fderiv ℝ (φ : E → ℝ)) p mu).toReal
      ≤ (ENNReal.ofReal ε * eLpNorm (fderiv ℝ (fderiv ℝ (φ : E → ℝ))) p mu +
          ENNReal.ofReal ((finrank ℝ E) ^ 2 / ε) * eLpNorm (φ : E → ℝ) p mu).toReal :=
        ENNReal.toReal_mono (by finiteness) (hφ.eLpNorm_fderiv_le Fact.out hp hε)
    _ = ε * (eLpNorm (fderiv ℝ (fderiv ℝ (φ : E → ℝ))) p mu).toReal +
          (finrank ℝ E) ^ 2 / ε * (eLpNorm (φ : E → ℝ) p mu).toReal := by
        rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le, ENNReal.toReal_ofReal (by positivity)]

/-- **The interpolation inequality in `W^{2,p}(E)`.** Let `1 ≤ p < ∞` and `ε > 0`. Every
`u ∈ W^{2,p}(E)` satisfies

`‖∇u‖_p ≤ ε ‖D²u‖_p + (n² / ε) ‖u‖_p`, `n = dim E`,

where `∇u` is the weak gradient `TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)` and
`D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. -/
theorem Wkp.norm_iteratedGradient_lowerOrder_le (hp : p ≠ ∞) (u : Wkp mu ⊤ p 2) {ε : ℝ}
    (hε : 0 < ε) :
    ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ ≤
      ε * ‖Wkp.iteratedGradient 1 u‖ + (finrank ℝ E) ^ 2 / ε * ‖Wkp.value 2 u‖ :=
  Wkp.norm_iteratedGradient_lowerOrder_le_of_mem_wkp0Submodule hp
    (by rw [wkp0Submodule_top_eq_top hp]; trivial) hε

end Sobolev

end TauCeti
