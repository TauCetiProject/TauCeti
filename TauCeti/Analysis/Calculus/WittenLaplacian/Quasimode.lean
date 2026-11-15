/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.WittenLaplacian.Localization
public import TauCeti.Analysis.Calculus.WittenLaplacian.Quadratic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Quasimodes of the Witten Laplacian at nondegenerate critical points

Consider a function `f` on `ℝ^ι` that, near a nondegenerate critical point `p`, is the model
`c + ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2` in the given Euclidean coordinates, as for a Morse function and a metric
that are both standard near `p`. The Witten Laplacian `Δ_t` of the model has the Gaussian ground
state `Ψ = Ψ_{0,s₋}(· - p)` in the degree `s₋ = {i | aᵢ < 0}` of the Morse index, with eigenvalue
`0` (`TauCeti.Analysis.Calculus.WittenLaplacian.Quadratic`). This file shows that cutting `Ψ` off
near `p` produces a *quasimode* of the Witten Laplacian of `f`: a compactly supported form whose
Rayleigh quotient is exponentially small as `t → ∞`. These quasimodes are the trial forms for the
upper-bound half of Witten's semiclassical analysis. Once `Δ_t` is realized as a self-adjoint
operator, the min-max principle turns a space of such forms of dimension `m` into `m` exponentially
small eigenvalues; that spectral step is not taken here. The lower bounds of
`TauCeti.Analysis.Calculus.WittenLaplacian.Localization` are the complementary half.

Let `J` be a compactly supported `C²` cutoff. By the localization formula for a single cutoff
(`TauCeti.integral_sum_euclideanWittenLaplacian_smul_mul_eq`) and the eigenform equation,

`∫ ⟨Δ_t (J Ψ), J Ψ⟩ = π^{-n/2} ∫ |∇J|² e^{-t ∑ᵢ |aᵢ| (xᵢ - pᵢ)²}`

(`TauCeti.integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_zero_mul_eq`;
the general Hermite eigenform is
`TauCeti.integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_mul_eq`). If
`J = 1` on the ellipsoid `∑ᵢ |aᵢ| (xᵢ - pᵢ)² < ρ`, then `∇J` vanishes there, so this energy is at
most a constant times `e^{-t ρ}`, while the mass `∫ |J Ψ|²` is at least a constant times
`e^{-t ρ'}` for every `0 < ρ' ≤ ρ`. Together, the Rayleigh quotient of `J Ψ` is at most
`C e^{-t (ρ - ρ')}` with `C` independent of `t`
(`integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_zero_mul_le_mul`).

For finitely many critical points with cutoffs of pairwise disjoint supports, the cut-off ground
states have no cross terms in the quadratic form of `Δ_t`, so the same exponential bound holds on
their span
(`integral_sum_euclideanWittenLaplacian_sum_smul_diagonalQuadraticWittenEigenform_zero_mul_le`).

## Main results

* `TauCeti.integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_mul_eq`:
  the energy of a cut-off Hermite eigenform of the model.
* `TauCeti.integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_zero_mul_eq`
  and
  `TauCeti.integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_zero_mul_le`:
  the energy of a cut-off ground state, and its exponential upper bound.
* `TauCeti.mul_measureReal_le_integral_sum_smul_diagonalQuadraticWittenEigenform_zero_sq`: the
  lower bound for the mass of a cut-off ground state.
* `integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_zero_mul_le_mul`:
  the Rayleigh quotient of a cut-off ground state is exponentially small.
* `integral_sum_euclideanWittenLaplacian_sum_smul_diagonalQuadraticWittenEigenform_zero_mul_le`:
  the same bound on the span of the cut-off ground states at several critical points.

## References

* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692, §2.
* B. Simon, *Semiclassical analysis of low lying eigenvalues. I. Non-degenerate minima: asymptotic
  expansions*, Ann. Inst. H. Poincaré Sect. A **38** (1983), 295–308, for cut-off
  harmonic-oscillator ground states as trial functions.
* H. L. Cycon, R. G. Froese, W. Kirsch and B. Simon, *Schrödinger Operators*, Texts and
  Monographs in Physics, Springer (1987), Chapter 11.
* B. Helffer and J. Sjöstrand, *Puits multiples en mécanique semi-classique IV: étude du
  complexe de Witten*, Comm. Partial Differential Equations **10** (1985), 245–340.
-/

public section

open Filter MeasureTheory Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **The energy of a cut-off Hermite eigenform.** Let `J` be a compactly supported `C²` cutoff,
and let `f` agree near every point of the support of `J` with the model
`c + ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2` centred at `p`. Let `Ψ = Ψ_{k,s}(· - p)` be a Hermite eigenform of the
model translated to `p`, with eigenvalue `μ = μ(k, s)`. Then for `t ≥ 0`

`∫ ⟨Δ_t (J Ψ), J Ψ⟩ = μ ∫ J² |Ψ|² + ∫ |∇J|² |Ψ|²`. -/
theorem integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_mul_eq
    {f J : (ι → ℝ) → ℝ} {a p : ι → ℝ} {c : ℝ}
    (hf : ∀ x ∈ tsupport J, f =ᶠ[𝓝 x] fun y ↦ c + diagonalQuadratic a (y - p))
    (hJ : ContDiff ℝ 2 J) (hJc : HasCompactSupport J) {t : ℝ} (ht : 0 ≤ t) (k : ι → ℕ)
    (s : Finset ι) :
    ∫ x, ∑ s', euclideanWittenLaplacian f t
        (J • fun y ↦ diagonalQuadraticWittenEigenform a t k s (y - p)) x s' *
        (J • fun y ↦ diagonalQuadraticWittenEigenform a t k s (y - p)) x s' =
      diagonalQuadraticWittenEigenvalue a t k s *
          (∫ x, J x ^ 2 * ∑ s', diagonalQuadraticWittenEigenform a t k s (x - p) s' ^ 2) +
        ∫ x, (∑ i, fderiv ℝ J x (Pi.single i 1) ^ 2) *
          ∑ s', diagonalQuadraticWittenEigenform a t k s (x - p) s' ^ 2 := by
  set Ψ : (ι → ℝ) → Finset ι → ℝ := fun y ↦ diagonalQuadraticWittenEigenform a t k s (y - p)
  have hΨ : ContDiff ℝ 2 Ψ :=
    (contDiff_diagonalQuadraticWittenEigenform a t k s).comp (contDiff_id.sub contDiff_const)
  have hq : euclideanWittenLaplacian (fun y ↦ c + diagonalQuadratic a (y - p)) t Ψ =
      diagonalQuadraticWittenEigenvalue a t k s • Ψ := by
    rw [euclideanWittenLaplacian_const_add, euclideanWittenLaplacian_comp_sub,
      euclideanWittenLaplacian_diagonalQuadraticWittenEigenform a ht k s]
    funext y
    simp only [Pi.smul_apply, Ψ]
  -- Near the support of `J` the function `f` is the model, and off it `J Ψ` vanishes.
  have hloc : ∀ x, ∑ s', euclideanWittenLaplacian f t (J • Ψ) x s' * (J • Ψ) x s' =
      ∑ s', euclideanWittenLaplacian (fun y ↦ c + diagonalQuadratic a (y - p)) t (J • Ψ) x s' *
        (J • Ψ) x s' := by
    intro x
    by_cases hx : x ∈ tsupport J
    · rw [(euclideanWittenLaplacian_eventuallyEq (hf x hx) (EventuallyEq.refl _ _) t).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hmodel : ContDiff ℝ 2 fun y ↦ c + diagonalQuadratic a (y - p) :=
    contDiff_const.add ((contDiff_diagonalQuadratic a).comp (contDiff_id.sub contDiff_const))
  rw [integral_congr_ae (Eventually.of_forall hloc),
    integral_sum_euclideanWittenLaplacian_smul_mul_eq (fun x _ ↦ hmodel.contDiffAt) hJ hJc hΨ t, hq,
    ← integral_const_mul]
  congr 2
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s' _ ↦ by ring

/-- **The energy of a cut-off ground state.** Let `J` be a compactly supported `C²` cutoff, and let
`f` agree near every point of the support of `J` with the model `c + ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2`. Let
`Ψ` be the ground state `Ψ_{0,s₋}` of the model translated to `p`, where `s₋` is the set of indices
with `aᵢ < 0`. Then for `t ≥ 0` the energy of the cut-off ground state is the localization error

`∫ ⟨Δ_t (J Ψ), J Ψ⟩ = π^{-n/2} ∫ |∇J|² e^{-t ∑ᵢ |aᵢ| (xᵢ - pᵢ)²}`. -/
theorem integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_zero_mul_eq
    {f J : (ι → ℝ) → ℝ} {a p : ι → ℝ} {c : ℝ}
    (hf : ∀ x ∈ tsupport J, f =ᶠ[𝓝 x] fun y ↦ c + diagonalQuadratic a (y - p))
    (hJ : ContDiff ℝ 2 J) (hJc : HasCompactSupport J) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, ∑ s, euclideanWittenLaplacian f t
        (J • fun y ↦ diagonalQuadraticWittenEigenform a t 0 {i | a i < 0} (y - p)) x s *
        (J • fun y ↦ diagonalQuadraticWittenEigenform a t 0 {i | a i < 0} (y - p)) x s =
      (∫ x, (∑ i, fderiv ℝ J x (Pi.single i 1) ^ 2) *
        Real.exp (-(t * ∑ i, |a i| * (x i - p i) ^ 2))) / √Real.pi ^ Fintype.card ι := by
  rw [integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_mul_eq hf hJ hJc
    ht, diagonalQuadraticWittenEigenvalue_zero_filter_neg, zero_mul, zero_add, ← integral_div]
  congr 1
  funext x
  rw [sum_diagonalQuadraticWittenEigenform_zero_apply_sq a ht, mul_div_assoc]
  simp only [Pi.sub_apply]

/-- The weight `|∇J|² e^{-t q}` of the energy of a cut-off ground state is integrable. -/
private theorem integrable_sum_fderiv_apply_sq_mul_exp {J : (ι → ℝ) → ℝ} (hJ : ContDiff ℝ 2 J)
    (hJc : HasCompactSupport J) (q : (ι → ℝ) → ℝ) (hq : Continuous q) :
    Integrable fun x ↦ (∑ i, fderiv ℝ J x (Pi.single i 1) ^ 2) * Real.exp (-q x) := by
  refine Continuous.integrable_of_hasCompactSupport ((continuous_finsetSum _ fun i _ ↦
    ((hJ.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2).mul
      (Real.continuous_exp.comp hq.neg)) (hJc.mono' fun x hx ↦ ?_)
  by_contra h
  exact hx (by simp [fderiv_of_notMem_tsupport ℝ h])

/-- **The energy of a cut-off ground state is exponentially small.** In the setting of
`TauCeti.integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_zero_mul_eq`,
suppose that `J = 1` on the ellipsoid `∑ᵢ |aᵢ| (xᵢ - pᵢ)² < ρ` and that `|∇J|² ≤ G`. Then for
`t ≥ 0`

`∫ ⟨Δ_t (J Ψ), J Ψ⟩ ≤ π^{-n/2} G vol(supp J) e^{-t ρ}`. -/
theorem integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_zero_mul_le
    {f J : (ι → ℝ) → ℝ} {a p : ι → ℝ} {c : ℝ}
    (hf : ∀ x ∈ tsupport J, f =ᶠ[𝓝 x] fun y ↦ c + diagonalQuadratic a (y - p))
    (hJ : ContDiff ℝ 2 J) (hJc : HasCompactSupport J) {t : ℝ} (ht : 0 ≤ t) {ρ G : ℝ}
    (hJ1 : ∀ x, ∑ i, |a i| * (x i - p i) ^ 2 < ρ → J x = 1)
    (hG : ∀ x, ∑ i, fderiv ℝ J x (Pi.single i 1) ^ 2 ≤ G) :
    ∫ x, ∑ s, euclideanWittenLaplacian f t
        (J • fun y ↦ diagonalQuadraticWittenEigenform a t 0 {i | a i < 0} (y - p)) x s *
        (J • fun y ↦ diagonalQuadraticWittenEigenform a t 0 {i | a i < 0} (y - p)) x s ≤
      G * volume.real (tsupport J) * Real.exp (-(t * ρ)) / √Real.pi ^ Fintype.card ι := by
  set q : (ι → ℝ) → ℝ := fun x ↦ ∑ i, |a i| * (x i - p i) ^ 2
  have hq : Continuous q := by fun_prop
  have hG₀ : 0 ≤ G := (Finset.sum_nonneg fun i _ ↦ sq_nonneg _).trans (hG 0)
  rw [integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_zero_mul_eq hf hJ
    hJc ht]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hpt : ∀ x, (∑ i, fderiv ℝ J x (Pi.single i 1) ^ 2) * Real.exp (-(t * q x)) ≤
      (tsupport J).indicator (fun _ ↦ G * Real.exp (-(t * ρ))) x := by
    intro x
    by_cases hx : x ∈ tsupport J
    · rw [Set.indicator_of_mem hx]
      by_cases hqx : q x < ρ
      · -- `J = 1` near `x`, so `∇J` vanishes at `x`.
        have hJx : J =ᶠ[𝓝 x] fun _ ↦ 1 :=
          eventually_of_mem ((isOpen_lt hq continuous_const).mem_nhds hqx) fun y hy ↦ hJ1 y hy
        have h0 : fderiv ℝ J x = 0 := by
          rw [hJx.fderiv_eq]
          simp
        simp only [h0, zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          Finset.sum_const_zero, zero_mul]
        positivity
      · exact mul_le_mul (hG x) (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le hG₀
    · simp [Set.indicator_of_notMem hx, fderiv_of_notMem_tsupport ℝ hx]
  calc _ ≤ ∫ x, (tsupport J).indicator (fun _ ↦ G * Real.exp (-(t * ρ))) x :=
        integral_mono (integrable_sum_fderiv_apply_sq_mul_exp hJ hJc _ (hq.const_mul t))
          ((integrableOn_const hJc.isCompact.measure_lt_top.ne).integrable_indicator
            (isClosed_tsupport J).measurableSet) hpt
    _ = _ := by
        rw [integral_indicator_const _ (isClosed_tsupport J).measurableSet, smul_eq_mul]
        ring

/-- **The mass of a cut-off ground state.** If a continuous compactly supported cutoff `J` equals
`1` on the ellipsoid `E = {x | ∑ᵢ |aᵢ| (xᵢ - pᵢ)² < ρ}`, then for `t ≥ 0` the cut-off ground state
`J Ψ` of the model centred at `p` has `π^{-n/2} e^{-t ρ} vol(E) ≤ ∫ |J Ψ|²`. -/
theorem mul_measureReal_le_integral_sum_smul_diagonalQuadraticWittenEigenform_zero_sq
    {J : (ι → ℝ) → ℝ} {a p : ι → ℝ} (hJ : Continuous J) (hJc : HasCompactSupport J) {t : ℝ}
    (ht : 0 ≤ t) {ρ : ℝ} (hJ1 : ∀ x, ∑ i, |a i| * (x i - p i) ^ 2 < ρ → J x = 1) :
    Real.exp (-(t * ρ)) / √Real.pi ^ Fintype.card ι *
        volume.real {x : ι → ℝ | ∑ i, |a i| * (x i - p i) ^ 2 < ρ} ≤
      ∫ x, ∑ s,
        (J • fun y ↦ diagonalQuadraticWittenEigenform a t 0 {i | a i < 0} (y - p)) x s ^ 2 := by
  set Ψ : (ι → ℝ) → Finset ι → ℝ := J • fun y ↦
    diagonalQuadraticWittenEigenform a t 0 {i | a i < 0} (y - p)
  set q : (ι → ℝ) → ℝ := fun x ↦ ∑ i, |a i| * (x i - p i) ^ 2
  have hS : IsOpen {x | q x < ρ} := isOpen_lt (by fun_prop) continuous_const
  have hSJ : {x | q x < ρ} ⊆ tsupport J := fun x hx ↦
    subset_tsupport J (by simp [Function.mem_support, hJ1 x hx])
  have hΨ : Continuous Ψ := hJ.smul ((contDiff_diagonalQuadraticWittenEigenform a t 0 _
    (n := 0)).continuous.comp (continuous_id.sub continuous_const))
  have hM : Integrable fun x ↦ ∑ s, Ψ x s ^ 2 :=
    (continuous_finsetSum _ fun s _ ↦ ((continuous_apply s).comp hΨ).pow 2)
      |>.integrable_of_hasCompactSupport (hJc.mono' fun x hx ↦ by
        by_contra h
        exact hx (by simp [Ψ, image_eq_zero_of_notMem_tsupport h]))
  calc _ ≤ ∫ x in {x | q x < ρ}, ∑ s, Ψ x s ^ 2 := by
        refine setIntegral_ge_of_const_le_real hS.measurableSet
          (measure_mono hSJ |>.trans_lt hJc.isCompact.measure_lt_top).ne (fun x hx ↦ ?_)
          hM.integrableOn
        simp only [Ψ, Pi.smul_apply', hJ1 x hx, one_smul]
        rw [sum_diagonalQuadraticWittenEigenform_zero_apply_sq a ht]
        simp only [Pi.sub_apply]
        gcongr
        exact le_of_lt hx
    _ ≤ _ := setIntegral_le_integral hM (Eventually.of_forall fun x ↦
        Finset.sum_nonneg fun s _ ↦ sq_nonneg _)

/-- **The cut-off ground state is a quasimode.** Let `J` be a compactly supported `C²` cutoff with
`|∇J|² ≤ G`, equal to `1` on the ellipsoid `∑ᵢ |aᵢ| (xᵢ - pᵢ)² < ρ`, and let `f` agree near every
point of the support of `J` with the model `c + ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2`. For `0 < ρ' ≤ ρ`, let `E'` be
the smaller ellipsoid `∑ᵢ |aᵢ| (xᵢ - pᵢ)² < ρ'`. Then for `t ≥ 0` the cut-off ground state `J Ψ` has
Rayleigh quotient

`∫ ⟨Δ_t (J Ψ), J Ψ⟩ ≤ G vol(supp J) / vol(E') · e^{-t (ρ - ρ')} ∫ |J Ψ|²`,

exponentially small as `t → ∞` with a constant independent of `t`. -/
theorem integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_zero_mul_le_mul
    {f J : (ι → ℝ) → ℝ} {a p : ι → ℝ} {c : ℝ}
    (hf : ∀ x ∈ tsupport J, f =ᶠ[𝓝 x] fun y ↦ c + diagonalQuadratic a (y - p))
    (hJ : ContDiff ℝ 2 J) (hJc : HasCompactSupport J) {t : ℝ} (ht : 0 ≤ t) {ρ ρ' G : ℝ}
    (hρ' : 0 < ρ') (hρ'ρ : ρ' ≤ ρ) (hJ1 : ∀ x, ∑ i, |a i| * (x i - p i) ^ 2 < ρ → J x = 1)
    (hG : ∀ x, ∑ i, fderiv ℝ J x (Pi.single i 1) ^ 2 ≤ G) :
    ∫ x, ∑ s, euclideanWittenLaplacian f t
        (J • fun y ↦ diagonalQuadraticWittenEigenform a t 0 {i | a i < 0} (y - p)) x s *
        (J • fun y ↦ diagonalQuadraticWittenEigenform a t 0 {i | a i < 0} (y - p)) x s ≤
      G * volume.real (tsupport J) /
          volume.real {x : ι → ℝ | ∑ i, |a i| * (x i - p i) ^ 2 < ρ'} *
        Real.exp (-(t * (ρ - ρ'))) *
          ∫ x, ∑ s,
        (J • fun y ↦ diagonalQuadraticWittenEigenform a t 0 {i | a i < 0} (y - p)) x s ^ 2 := by
  set S : Set (ι → ℝ) := {x | ∑ i, |a i| * (x i - p i) ^ 2 < ρ'}
  have hG₀ : 0 ≤ G := (Finset.sum_nonneg fun i _ ↦ sq_nonneg _).trans (hG 0)
  have hJ1' : ∀ x, ∑ i, |a i| * (x i - p i) ^ 2 < ρ' → J x = 1 := fun x hx ↦
    hJ1 x (hx.trans_le hρ'ρ)
  -- The ball `S` around `p` is open, nonempty and contained in the support of `J`.
  have hS : 0 < volume.real S := by
    have hSJ : S ⊆ tsupport J := fun x hx ↦ subset_tsupport J (by simp [hJ1' x hx])
    refine ENNReal.toReal_pos ((isOpen_lt (by fun_prop) continuous_const).measure_pos volume
      ⟨p, by simpa [S] using hρ'⟩).ne' (measure_mono hSJ |>.trans_lt
        hJc.isCompact.measure_lt_top).ne
  calc _ ≤ G * volume.real (tsupport J) * Real.exp (-(t * ρ)) / √Real.pi ^ Fintype.card ι :=
        integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_zero_mul_le hf
          hJ hJc ht hJ1 hG
    _ = G * volume.real (tsupport J) / volume.real S * Real.exp (-(t * (ρ - ρ'))) *
          (Real.exp (-(t * ρ')) / √Real.pi ^ Fintype.card ι * volume.real S) := by
        rw [show -(t * ρ) = -(t * (ρ - ρ')) + -(t * ρ') by ring, Real.exp_add]
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_measureReal_le_integral_sum_smul_diagonalQuadraticWittenEigenform_zero_sq hJ.continuous
          hJc ht hJ1') (by positivity)

/-- **Quasimodes at several critical points.** Let `(p b)_{b ∈ B}` be finitely many points, and
let `f` agree near every point of the support of a cutoff `J b` with the model
`c b + ∑ᵢ a b i (yᵢ - p b i)² / 2` centred at `p b`. Suppose the compactly supported `C²` cutoffs
`J b` have pairwise disjoint supports, satisfy `|∇J b|² ≤ G b`, and equal `1` on the ellipsoids
`∑ᵢ |a b i| (xᵢ - p b i)² < ρ`. For `0 < ρ' ≤ ρ`, let `K` bound `G b vol(supp J b) / vol(E' b)`,
where `E' b` is the smaller ellipsoid `∑ᵢ |a b i| (xᵢ - p b i)² < ρ'`. Then for `t ≥ 0` every
linear combination `ψ = ∑_b w b J b Ψ_b` of the cut-off ground states satisfies

`∫ ⟨Δ_t ψ, ψ⟩ ≤ K e^{-t (ρ - ρ')} ∫ |ψ|²`. -/
theorem integral_sum_euclideanWittenLaplacian_sum_smul_diagonalQuadraticWittenEigenform_zero_mul_le
    {β : Type*} {B : Finset β} {f : (ι → ℝ) → ℝ} {J : β → (ι → ℝ) → ℝ} {a p : β → ι → ℝ}
    {c : β → ℝ}
    (hf : ∀ b ∈ B, ∀ x ∈ tsupport (J b),
      f =ᶠ[𝓝 x] fun y ↦ c b + diagonalQuadratic (a b) (y - p b))
    (hJ : ∀ b ∈ B, ContDiff ℝ 2 (J b)) (hJc : ∀ b ∈ B, HasCompactSupport (J b))
    (hdisj : (B : Set β).PairwiseDisjoint fun b ↦ tsupport (J b)) {t : ℝ} (ht : 0 ≤ t)
    {ρ ρ' K : ℝ} {G : β → ℝ} (hρ' : 0 < ρ') (hρ'ρ : ρ' ≤ ρ)
    (hJ1 : ∀ b ∈ B, ∀ x, ∑ i, |a b i| * (x i - p b i) ^ 2 < ρ → J b x = 1)
    (hG : ∀ b ∈ B, ∀ x, ∑ i, fderiv ℝ (J b) x (Pi.single i 1) ^ 2 ≤ G b)
    (hK : ∀ b ∈ B, G b * volume.real (tsupport (J b)) /
      volume.real {x : ι → ℝ | ∑ i, |a b i| * (x i - p b i) ^ 2 < ρ'} ≤ K) (w : β → ℝ) :
    ∫ x, ∑ s, euclideanWittenLaplacian f t (∑ b ∈ B, w b • (J b • fun y ↦
        diagonalQuadraticWittenEigenform (a b) t 0 {i | a b i < 0} (y - p b))) x s *
        (∑ b ∈ B, w b • (J b • fun y ↦
          diagonalQuadraticWittenEigenform (a b) t 0 {i | a b i < 0} (y - p b))) x s ≤
      K * Real.exp (-(t * (ρ - ρ'))) *
        ∫ x, ∑ s, (∑ b ∈ B, w b • (J b • fun y ↦
          diagonalQuadraticWittenEigenform (a b) t 0 {i | a b i < 0} (y - p b))) x s ^ 2 := by
  set Ψ : β → (ι → ℝ) → Finset ι → ℝ := fun b ↦ J b • fun y ↦
    diagonalQuadraticWittenEigenform (a b) t 0 {i | a b i < 0} (y - p b)
  have hΨJ : ∀ b, tsupport (Ψ b) ⊆ tsupport (J b) := fun b ↦
    tsupport_smul_subset_left (J b) fun y ↦
      diagonalQuadraticWittenEigenform (a b) t 0 {i | a b i < 0} (y - p b)
  refine integral_sum_euclideanWittenLaplacian_sum_smul_mul_le (φ := Ψ)
    (fun b hb x hx ↦ ?_) (fun b hb ↦ (hJ b hb).smul
      ((contDiff_diagonalQuadraticWittenEigenform _ t 0 _).comp (contDiff_id.sub contDiff_const)))
    (fun b hb ↦ (hJc b hb).smul_right) (hdisj.mono hΨJ) (fun b hb ↦ ?_) w
  · exact (contDiff_const.add ((contDiff_diagonalQuadratic (a b)).comp
      (contDiff_id.sub contDiff_const))).contDiffAt.congr_of_eventuallyEq (hf b hb x (hΨJ b hx))
  · refine
      (integral_sum_euclideanWittenLaplacian_smul_diagonalQuadraticWittenEigenform_zero_mul_le_mul
        (hf b hb) (hJ b hb) (hJc b hb) ht hρ' hρ'ρ (hJ1 b hb) (hG b hb)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hK b hb) (Real.exp_pos _).le)
      (integral_nonneg fun x ↦ Finset.sum_nonneg fun s _ ↦ sq_nonneg (Ψ b x s))

end TauCeti
