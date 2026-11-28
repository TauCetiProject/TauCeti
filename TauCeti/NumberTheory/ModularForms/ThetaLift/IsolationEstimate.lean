/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Peak isolation and weighted product integration

A peak of a nonzero bounded normed-group-valued function has norm greater than half the supremum
norm. An averaged family of orthogonality identities and a reproducing formula bound a kernel at
the basepoint. The average and reproduction are retained explicitly; a single zero integral does
not carry this estimate. A normalized kernel average gives the sharper constant, while the
factor-two bound supplied by a peak gives the `(4 * B + 1) * δ` constant needed for the isolation
argument.

A weighted integral of factors on a finite product of measure spaces is bounded by multiplying the
placewise estimates. The global maximum weight is dominated by the product of the weights truncated
below at one, so no factor involving the number of places is needed.

## Main results

* `TauCeti.ThetaLift.exists_isPeak_of_ne_zero`: constructs a peak from a uniform norm bound.
* `TauCeti.ThetaLift.norm_apply_one_le_of_isolation_family`: general scaled isolation estimate.
* `TauCeti.ThetaLift.norm_apply_one_le_of_forall_isPeak`: normalized `(2 * B + w e) * δ` estimate.
* `TauCeti.ThetaLift.norm_apply_one_le_of_forall_isPeak_of_weight_le_one`: `(4 * B + 1) * δ`
  estimate.
* `TauCeti.ThetaLift.norm_apply_one_le_of_isPeak_of_act`: peak-orbit isolation corollary.
* `TauCeti.ThetaLift.integral_norm_prod_mul_pow_le`: integrability and sharp product-of-places
  weighted integral comparison.

## References

The arguments follow [ShortProof](https://github.com/lsernau/grh-lean), `lsernau/grh-lean` at
commit `72fead102f663d5c7a407964a13dc0cf9d977207`, file
`grh/src/New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean`. The abstract formulation makes
the averaged orthogonality and reproducing hypotheses explicit. The proofs are independent.
-/

public noncomputable section

open scoped ComplexConjugate
open MeasureTheory

namespace TauCeti.ThetaLift

/-- A peak has norm strictly greater than half the positive supremum norm. -/
def IsPeak {X E : Type*} [SeminormedAddCommGroup E] (F : X → E) (x : X) : Prop :=
  0 < sSup (Set.range fun y ↦ ‖F y‖) ∧ sSup (Set.range fun y ↦ ‖F y‖) / 2 < ‖F x‖

/-- A bounded nonzero function into a normed additive group has a peak. -/
theorem exists_isPeak_of_ne_zero {X E : Type*} [NormedAddCommGroup E] {F : X → E}
    (hbounded : ∃ M : ℝ, ∀ x, ‖F x‖ ≤ M) (hF : F ≠ 0) : ∃ x, IsPeak F x := by
  obtain ⟨M, hM⟩ := hbounded
  obtain ⟨x, hx⟩ : ∃ x, F x ≠ 0 := Function.ne_iff.mp hF
  have hne : (Set.range fun y ↦ ‖F y‖).Nonempty := ⟨‖F x‖, ⟨x, rfl⟩⟩
  have hbdd : BddAbove (Set.range fun y ↦ ‖F y‖) := ⟨M, by
    rintro _ ⟨x, rfl⟩
    exact hM x⟩
  have hpos : 0 < sSup (Set.range fun y ↦ ‖F y‖) := by
    exact (norm_pos_iff.mpr hx).trans_le (le_csSup hbdd ⟨x, rfl⟩)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := exists_lt_of_lt_csSup hne (half_lt_self hpos)
  exact ⟨x, hpos, hx⟩

/-- The pointwise supremum norm bound on a function with a peak. -/
theorem IsPeak.norm_le {X E : Type*} [SeminormedAddCommGroup E] {F : X → E} {x : X}
    (hx : IsPeak F x) (y : X) : ‖F y‖ ≤ 2 * ‖F x‖ := by
  obtain ⟨hxpos, hxpeak⟩ := hx
  have hbdd : BddAbove (Set.range fun y ↦ ‖F y‖) := by
    by_contra h
    rw [csSup_of_not_bddAbove h] at hxpos
    simp at hxpos
  have hle : ‖F y‖ ≤ sSup (Set.range fun y ↦ ‖F y‖) := le_csSup hbdd ⟨y, rfl⟩
  linarith

/-- The value at a peak is nonzero. -/
theorem IsPeak.ne_zero {X E : Type*} [NormedAddCommGroup E] {F : X → E} {x : X}
    (hx : IsPeak F x) : F x ≠ 0 :=
  norm_pos_iff.mp ((div_pos hx.1 (by norm_num)).trans hx.2)

/-- Orthogonality turns a weighted kernel error into an integral error bound. -/
theorem norm_integral_mul_le_of_orth
    {G : Type*} [MeasurableSpace G] {μ : Measure G}
    {W K K' K₀ m : G → ℂ} {w : G → ℝ} {C δ : ℝ}
    (hC : 0 ≤ C) (hW : ∀ h, ‖W h‖ ≤ C)
    (hK : ∀ h, ‖K h - K₀ h‖ ≤ δ * w h)
    (hK' : ∀ h, ‖K' h - K₀ h‖ ≤ δ * w h)
    (hq : Integrable (fun h ↦ ‖m h‖ * w h) μ)
    (hint : Integrable (fun h ↦ W h * K h * m h) μ)
    (hint' : Integrable (fun h ↦ W h * K' h * m h) μ)
    (horth : ∫ h, W h * K' h * m h ∂μ = 0) :
    ‖∫ h, W h * K h * m h ∂μ‖ ≤
      2 * δ * C * ∫ h, ‖m h‖ * w h ∂μ := by
  have hdiff (h : G) : ‖W h * K h * m h - W h * K' h * m h‖ ≤
      (2 * δ * C) * (‖m h‖ * w h) := by
    have hmul : W h * K h * m h - W h * K' h * m h =
        W h * (K h - K' h) * m h := by ring
    rw [hmul, norm_mul, norm_mul]
    have hKK : ‖K h - K' h‖ ≤ δ * w h + δ * w h := by
      calc
        ‖K h - K' h‖ ≤ ‖K h - K₀ h‖ + ‖K₀ h - K' h‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ δ * w h + δ * w h := by
          rw [norm_sub_rev (K₀ h) (K' h)]
          exact add_le_add (hK h) (hK' h)
    calc
      _ ≤ C * (δ * w h + δ * w h) * ‖m h‖ := by
        gcongr
        exact hW h
      _ = (2 * δ * C) * (‖m h‖ * w h) := by ring
  have hint_eq : (∫ h, W h * K h * m h ∂μ) =
      ∫ h, (W h * K h * m h - W h * K' h * m h) ∂μ := by
    rw [integral_sub hint hint', horth, sub_zero]
  rw [hint_eq]
  simpa only [integral_const_mul] using
    norm_integral_le_of_norm_le (hq.const_mul (2 * δ * C)) (.of_forall hdiff)

/-- Averaged orthogonality and reproduction give the scaled isolation bound. -/
theorem norm_apply_one_le_of_isolation_family
    {X G Θ : Type*} [MeasurableSpace G] [MeasurableSpace Θ]
    {μ : Measure G} {ν : Measure Θ} [SFinite μ] [IsProbabilityMeasure ν]
    {F : X → ℂ} {x : X} {e : G} {m m' : G → ℂ} {w : G → ℝ}
    {K K₀ : G → ℂ} {K' : Θ → G → ℂ} {W : Θ → G → ℂ} {B δ I r : ℝ}
    (hI : 0 < I) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hFx : F x ≠ 0)
    (hq : Integrable (fun h ↦ ‖m' h‖ * w h) μ)
    (hq_le : (∫ h, ‖m' h‖ * w h ∂μ) ≤ B * I)
    (hK : ∀ h, ‖K h - K₀ h‖ ≤ δ * w h)
    (hK' : ∀ θ h, ‖K' θ h - K₀ h‖ ≤ δ * w h)
    (hW_le : ∀ θ h, ‖W θ h‖ ≤ r * ‖F x‖)
    (hW_mean : ∀ h, ∫ θ, W θ h ∂ν = starRingEnd ℂ (m h * F x))
    (hW_int : Integrable (Function.uncurry fun θ h ↦ W θ h * K h * m' h) (ν.prod μ))
    (hint' : ∀ θ, Integrable (fun h ↦ W θ h * K' θ h * m' h) μ)
    (horth : ∀ θ, ∫ h, W θ h * K' θ h * m' h ∂μ = 0)
    (hrepr : (∫ h, (K h * m' h) * starRingEnd ℂ (m h * F x) ∂μ) =
      (I : ℂ) * (K e * m' e) * starRingEnd ℂ (F x))
    (hm' : m' e = 1) : ‖K₀ e‖ ≤ (2 * r * B + w e) * δ := by
  have hslice (θ : Θ) (hθ : Integrable (fun h ↦ W θ h * K h * m' h) μ) :
      ‖∫ h, W θ h * K h * m' h ∂μ‖ ≤ (2 * δ * (r * ‖F x‖)) * (B * I) := by
    calc
      _ ≤ 2 * δ * (r * ‖F x‖) * ∫ h, ‖m' h‖ * w h ∂μ :=
        norm_integral_mul_le_of_orth (mul_nonneg hr (norm_nonneg _)) (hW_le θ) hK
          (hK' θ) hq hθ (hint' θ) (horth θ)
      _ ≤ (2 * δ * (r * ‖F x‖)) * (B * I) := by gcongr
  have havg : ‖∫ θ, ∫ h, W θ h * K h * m' h ∂μ ∂ν‖ ≤
      (2 * δ * (r * ‖F x‖)) * (B * I) := by
    simpa [Measure.real] using
      norm_integral_le_of_norm_le_const (hW_int.prod_right_ae.mono hslice)
  have hmean (h : G) : ∫ θ, W θ h * K h * m' h ∂ν =
      (K h * m' h) * starRingEnd ℂ (m h * F x) := by
    calc
      _ = ∫ θ, (K h * m' h) * W θ h ∂ν := by congr with θ; ring
      _ = _ := by rw [integral_const_mul, hW_mean]
  have hrepr' : ∫ h, ∫ θ, W θ h * K h * m' h ∂ν ∂μ =
      (I : ℂ) * (K e * m' e) * starRingEnd ℂ (F x) := by
    simpa only [hmean] using hrepr
  have hmain : I * ‖K e‖ * ‖F x‖ ≤ (2 * δ * (r * ‖F x‖)) * (B * I) := by
    calc
      _ = ‖(I : ℂ) * (K e * m' e) * starRingEnd ℂ (F x)‖ := by
        simp [hm', Real.norm_eq_abs, abs_of_pos hI]
      _ = ‖∫ θ, ∫ h, W θ h * K h * m' h ∂μ ∂ν‖ := by
        rw [integral_integral_swap hW_int, hrepr']
      _ ≤ _ := havg
  have hKe : ‖K e‖ ≤ 2 * r * B * δ := by
    apply le_of_mul_le_mul_right ?_ (mul_pos hI (norm_pos_iff.mpr hFx))
    calc
      _ = I * ‖K e‖ * ‖F x‖ := by ring
      _ ≤ (2 * δ * (r * ‖F x‖)) * (B * I) := hmain
      _ = (2 * r * B * δ) * (I * ‖F x‖) := by ring
  calc
    ‖K₀ e‖ ≤ ‖K e‖ + ‖K e - K₀ e‖ := norm_le_insert _ _
    _ ≤ 2 * r * B * δ + δ * w e := add_le_add hKe (hK e)
    _ = (2 * r * B + w e) * δ := by ring

/-- The normalized isolation family gives the sharp `(2 * B + w e) * δ` isolation estimate. -/
theorem norm_apply_one_le_of_forall_isPeak
    {X G Θ : Type*} [MeasurableSpace G] [MeasurableSpace Θ]
    {μ : Measure G} {ν : Measure Θ} [SFinite μ] [IsProbabilityMeasure ν]
    {F : X → ℂ} {x : X} {e : G} {m m' : G → ℂ} {w : G → ℝ}
    {K K₀ : G → ℂ} {K' : Θ → G → ℂ} {W : Θ → G → ℂ} {B δ : ℝ}
    (hFx : F x ≠ 0) (hδ : 0 ≤ δ) (hI : 0 < ∫ h, ‖m h‖ ^ 2 ∂μ)
    (hq : Integrable (fun h ↦ ‖m' h‖ * w h) μ)
    (hq_le : (∫ h, ‖m' h‖ * w h ∂μ) ≤ B * ∫ h, ‖m h‖ ^ 2 ∂μ)
    (hK : ∀ h, ‖K h - K₀ h‖ ≤ δ * w h)
    (hK' : ∀ θ h, ‖K' θ h - K₀ h‖ ≤ δ * w h)
    (hW_le : ∀ θ h, ‖W θ h‖ ≤ ‖F x‖)
    (hW_mean : ∀ h, ∫ θ, W θ h ∂ν = starRingEnd ℂ (m h * F x))
    (hW_int : Integrable (Function.uncurry fun θ h ↦ W θ h * K h * m' h) (ν.prod μ))
    (hint' : ∀ θ, Integrable (fun h ↦ W θ h * K' θ h * m' h) μ)
    (horth : ∀ θ, ∫ h, W θ h * K' θ h * m' h ∂μ = 0)
    (hrepr : (∫ h, (K h * m' h) * starRingEnd ℂ (m h * F x) ∂μ) =
      ((∫ h, ‖m h‖ ^ 2 ∂μ : ℝ) : ℂ) * (K e * m' e) * starRingEnd ℂ (F x))
    (hm' : m' e = 1) : ‖K₀ e‖ ≤ (2 * B + w e) * δ := by
  simpa using norm_apply_one_le_of_isolation_family (I := ∫ h, ‖m h‖ ^ 2 ∂μ) (r := 1)
    hI hδ zero_le_one hFx hq hq_le
    hK hK' (by simpa using hW_le) hW_mean hW_int hint' horth hrepr hm'

/-- A factor-two bound on the kernel family with `w e ≤ 1` gives the `(4 * B + 1) * δ` corollary. -/
theorem norm_apply_one_le_of_forall_isPeak_of_weight_le_one
    {X G Θ : Type*} [MeasurableSpace G] [MeasurableSpace Θ]
    {μ : Measure G} {ν : Measure Θ} [SFinite μ] [IsProbabilityMeasure ν]
    {F : X → ℂ} {x : X} {e : G} {m m' : G → ℂ} {w : G → ℝ}
    {K K₀ : G → ℂ} {K' : Θ → G → ℂ} {W : Θ → G → ℂ} {B δ : ℝ}
    (hFx : F x ≠ 0) (hδ : 0 ≤ δ) (hI : 0 < ∫ h, ‖m h‖ ^ 2 ∂μ) (hwe : w e ≤ 1)
    (hq : Integrable (fun h ↦ ‖m' h‖ * w h) μ)
    (hq_le : (∫ h, ‖m' h‖ * w h ∂μ) ≤ B * ∫ h, ‖m h‖ ^ 2 ∂μ)
    (hK : ∀ h, ‖K h - K₀ h‖ ≤ δ * w h)
    (hK' : ∀ θ h, ‖K' θ h - K₀ h‖ ≤ δ * w h)
    (hW_le : ∀ θ h, ‖W θ h‖ ≤ 2 * ‖F x‖)
    (hW_mean : ∀ h, ∫ θ, W θ h ∂ν = starRingEnd ℂ (m h * F x))
    (hW_int : Integrable (Function.uncurry fun θ h ↦ W θ h * K h * m' h) (ν.prod μ))
    (hint' : ∀ θ, Integrable (fun h ↦ W θ h * K' θ h * m' h) μ)
    (horth : ∀ θ, ∫ h, W θ h * K' θ h * m' h ∂μ = 0)
    (hrepr : (∫ h, (K h * m' h) * starRingEnd ℂ (m h * F x) ∂μ) =
      ((∫ h, ‖m h‖ ^ 2 ∂μ : ℝ) : ℂ) * (K e * m' e) * starRingEnd ℂ (F x))
    (hm' : m' e = 1) : ‖K₀ e‖ ≤ (4 * B + 1) * δ := by
  have hbound := norm_apply_one_le_of_isolation_family
    (I := ∫ h, ‖m h‖ ^ 2 ∂μ) (r := 2) hI hδ (by positivity) hFx hq hq_le
    hK hK' hW_le hW_mean hW_int hint' horth hrepr hm'
  calc
    _ ≤ (2 * 2 * B + w e) * δ := hbound
    _ ≤ (4 * B + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ

/-- The peak bound for normalized conjugates on a group orbit gives the `(4 * B + 1) * δ`
isolation estimate. -/
theorem norm_apply_one_le_of_isPeak_of_act
    {X G Θ : Type*} [MeasurableSpace G] [MeasurableSpace Θ]
    {μ : Measure G} {ν : Measure Θ} [SFinite μ] [IsProbabilityMeasure ν]
    {F : X → ℂ} {x : X} {e : G} {m m' : G → ℂ} {w : G → ℝ}
    {K K₀ : G → ℂ} {K' : Θ → G → ℂ} {W : Θ → G → ℂ} {B δ : ℝ}
    (act : X → G → X) (rot : Θ → X) (a : Θ → ℂ)
    (hx : IsPeak F x) (hδ : 0 ≤ δ) (hI : 0 < ∫ h, ‖m h‖ ^ 2 ∂μ) (hwe : w e ≤ 1)
    (hq : Integrable (fun h ↦ ‖m' h‖ * w h) μ)
    (hq_le : (∫ h, ‖m' h‖ * w h ∂μ) ≤ B * ∫ h, ‖m h‖ ^ 2 ∂μ)
    (hK : ∀ h, ‖K h - K₀ h‖ ≤ δ * w h)
    (hK' : ∀ θ h, ‖K' θ h - K₀ h‖ ≤ δ * w h)
    (ha : ∀ θ, ‖a θ‖ = 1)
    (hW : ∀ θ h, W θ h = starRingEnd ℂ (F (act (rot θ) h) * a θ))
    (hW_mean : ∀ h, ∫ θ, W θ h ∂ν = starRingEnd ℂ (m h * F x))
    (hW_int : Integrable (Function.uncurry fun θ h ↦ W θ h * K h * m' h) (ν.prod μ))
    (hint' : ∀ θ, Integrable (fun h ↦ W θ h * K' θ h * m' h) μ)
    (horth : ∀ θ, ∫ h, W θ h * K' θ h * m' h ∂μ = 0)
    (hrepr : (∫ h, (K h * m' h) * starRingEnd ℂ (m h * F x) ∂μ) =
      ((∫ h, ‖m h‖ ^ 2 ∂μ : ℝ) : ℂ) * (K e * m' e) * starRingEnd ℂ (F x))
    (hm' : m' e = 1) : ‖K₀ e‖ ≤ (4 * B + 1) * δ := by
  have hW_le (θ : Θ) (h : G) : ‖W θ h‖ ≤ 2 * ‖F x‖ := by
    rw [hW θ h]
    simpa [ha θ] using hx.norm_le (act (rot θ) h)
  exact norm_apply_one_le_of_forall_isPeak_of_weight_le_one hx.ne_zero hδ hI hwe hq hq_le
    hK hK' hW_le hW_mean hW_int hint' horth hrepr hm'

/-- A truncated factor is at most the product of all truncated factors. -/
theorem max_one_le_prod_max_one {ι : Type*} [Fintype ι] (f : ι → ℝ) (τ : ι) :
    max 1 (f τ) ≤ ∏ σ, max 1 (f σ) := by
  have hsub : ({τ} : Finset ι) ⊆ Finset.univ := by simp
  have hnonneg : ∀ σ ∈ ({τ} : Finset ι), 0 ≤ max 1 (f σ) := by
    intro σ _
    exact zero_le_one.trans (le_max_left _ _)
  have hone : ∀ σ ∈ Finset.univ, σ ∉ ({τ} : Finset ι) → 1 ≤ max 1 (f σ) := by
    intro σ _ _
    exact le_max_left _ _
  simpa using Finset.prod_le_prod_of_subset_of_one_le₀ hsub hnonneg hone

/-- A finite maximum power is at most the product of truncated powers. -/
theorem iSup_pow_le_prod_max_one_pow {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ τ, 0 ≤ f τ) (A : ℕ) :
    (⨆ τ, f τ) ^ A ≤ ∏ τ, (max 1 (f τ)) ^ A := by
  rw [Finset.prod_pow]
  apply pow_le_pow_left₀ (Real.iSup_nonneg hf)
  exact ciSup_le fun τ ↦ (le_max_right _ _).trans (max_one_le_prod_max_one f τ)

/-- The weighted product is dominated by its placewise weighted majorant. -/
theorem prod_norm_mul_iSup_pow_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {G E : ι → Type*} [∀ τ, SeminormedAddCommGroup (E τ)]
    (m' : (τ : ι) → G τ → E τ) (nrm : (τ : ι) → G τ → ℝ)
    (hnrm : ∀ τ x, 0 ≤ nrm τ x) (A : ℕ) (h : (τ : ι) → G τ) :
    (∏ τ, ‖m' τ (h τ)‖) * (⨆ τ, nrm τ (h τ)) ^ A ≤
      ∏ τ, (‖m' τ (h τ)‖ * (max 1 (nrm τ (h τ))) ^ A) := by
  rw [Finset.prod_mul_distrib]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
  exact iSup_pow_le_prod_max_one_pow _ (fun τ ↦ hnrm τ (h τ)) A

/-- Placewise integrability supplies the global weighted-product measurability. -/
theorem aestronglyMeasurable_prod_norm_mul_iSup_pow {ι : Type*} [Fintype ι]
    {G E : ι → Type*} [∀ τ, MeasurableSpace (G τ)] [∀ τ, SeminormedAddCommGroup (E τ)]
    {μ : (τ : ι) → Measure (G τ)} [∀ τ, SigmaFinite (μ τ)]
    (m' : (τ : ι) → G τ → E τ) (nrm : (τ : ι) → G τ → ℝ)
    (hnrm_meas : ∀ τ, Measurable (nrm τ)) (A : ℕ)
    (hint : ∀ τ, Integrable (fun x ↦ ‖m' τ x‖ * (max 1 (nrm τ x)) ^ A) (μ τ)) :
    AEStronglyMeasurable (fun h : (τ : ι) → G τ ↦
      (∏ τ, ‖m' τ (h τ)‖) * (⨆ τ, nrm τ (h τ)) ^ A) (Measure.pi μ) := by
  let V (h : (τ : ι) → G τ) := ∏ τ, (max 1 (nrm τ (h τ))) ^ A
  let Q (h : (τ : ι) → G τ) := ∏ τ, (‖m' τ (h τ)‖ * (max 1 (nrm τ (h τ))) ^ A)
  have hQ : Integrable Q (Measure.pi μ) := Integrable.fintype_prod_dep hint
  have hn (τ : ι) : Measurable (fun h : (σ : ι) → G σ ↦ nrm τ (h τ)) :=
    (hnrm_meas τ).comp (measurable_pi_apply τ)
  have hV : Measurable V := Finset.measurable_fun_prod Finset.univ fun τ _ ↦
    (measurable_const.max (hn τ)).pow_const A
  have hV_pos (h : (τ : ι) → G τ) : 0 < V h := Finset.prod_pos fun τ _ ↦
    pow_pos (zero_lt_one.trans_le (le_max_left _ _)) A
  have heq (h : (τ : ι) → G τ) :
      (∏ τ, ‖m' τ (h τ)‖) * (⨆ τ, nrm τ (h τ)) ^ A =
        Q h * (⨆ τ, nrm τ (h τ)) ^ A / V h := by
    dsimp only [Q, V]
    rw [Finset.prod_mul_distrib]
    symm
    rw [div_eq_mul_inv]
    calc
      _ = ((∏ τ, ‖m' τ (h τ)‖) * (⨆ τ, nrm τ (h τ)) ^ A) *
          ((∏ τ, (max 1 (nrm τ (h τ))) ^ A) *
            (∏ τ, (max 1 (nrm τ (h τ))) ^ A)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (hV_pos h).ne', mul_one]
  have hfun : (fun h : (τ : ι) → G τ ↦
      (∏ τ, ‖m' τ (h τ)‖) * (⨆ τ, nrm τ (h τ)) ^ A) =
      (fun h ↦ Q h * (⨆ τ, nrm τ (h τ)) ^ A / V h) := funext heq
  rw [hfun]
  exact (hQ.aestronglyMeasurable.mul
    ((Measurable.iSup hn).pow_const A).aestronglyMeasurable).div₀ hV.aestronglyMeasurable

/-- The common-weight form of the product estimate has no cardinality loss. -/
theorem integral_norm_prod_mul_pow_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {G E E' : ι → Type*} [∀ τ, MeasurableSpace (G τ)]
    [∀ τ, SeminormedAddCommGroup (E τ)] [∀ τ, SeminormedAddCommGroup (E' τ)]
    {μ : (τ : ι) → Measure (G τ)} [∀ τ, SigmaFinite (μ τ)]
    (m_u : (τ : ι) → G τ → E τ) (m_u' : (τ : ι) → G τ → E' τ)
    (nrm : (τ : ι) → G τ → ℝ) (c : ι → ℝ) (A : ℕ)
    (hnrm_meas : ∀ τ, Measurable (nrm τ)) (hnrm : ∀ τ x, 0 ≤ nrm τ x)
    (hint : ∀ τ, Integrable (fun x ↦ ‖m_u' τ x‖ * (max 1 (nrm τ x)) ^ A) (μ τ))
    (hle : ∀ τ, ∫ x, ‖m_u' τ x‖ * (max 1 (nrm τ x)) ^ A ∂μ τ ≤
      c τ * ∫ x, ‖m_u τ x‖ ^ 2 ∂μ τ) :
    Integrable (fun h : (τ : ι) → G τ ↦
        (∏ τ, ‖m_u' τ (h τ)‖) * (⨆ τ, nrm τ (h τ)) ^ A) (Measure.pi μ) ∧
      ∫ h, (∏ τ, ‖m_u' τ (h τ)‖) * (⨆ τ, nrm τ (h τ)) ^ A ∂Measure.pi μ ≤
        (∏ τ, c τ) * ∫ h, (∏ τ, ‖m_u τ (h τ)‖) ^ 2 ∂Measure.pi μ := by
  have hprod_int : Integrable (fun h : (τ : ι) → G τ ↦
      ∏ τ, (‖m_u' τ (h τ)‖ * (max 1 (nrm τ (h τ))) ^ A)) (Measure.pi μ) :=
    Integrable.fintype_prod_dep hint
  have hbound (h : (τ : ι) → G τ) :
      (∏ τ, ‖m_u' τ (h τ)‖) * (⨆ τ, nrm τ (h τ)) ^ A ≤
        ∏ τ, (‖m_u' τ (h τ)‖ * (max 1 (nrm τ (h τ))) ^ A) :=
    prod_norm_mul_iSup_pow_le m_u' nrm hnrm A h
  have htarget_int : Integrable (fun h : (τ : ι) → G τ ↦
      (∏ τ, ‖m_u' τ (h τ)‖) * (⨆ τ, nrm τ (h τ)) ^ A) (Measure.pi μ) := by
    apply hprod_int.mono'
      (aestronglyMeasurable_prod_norm_mul_iSup_pow m_u' nrm hnrm_meas A hint)
    apply Filter.Eventually.of_forall
    intro h
    rw [Real.norm_of_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
      (pow_nonneg (Real.iSup_nonneg fun τ ↦ hnrm τ (h τ)) A))]
    exact hbound h
  have hsq : ∫ h, (∏ τ, ‖m_u τ (h τ)‖) ^ 2 ∂Measure.pi μ =
      ∏ τ, ∫ x, ‖m_u τ x‖ ^ 2 ∂μ τ := by
    calc
      _ = ∫ h, ∏ τ, ‖m_u τ (h τ)‖ ^ 2 ∂Measure.pi μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun h ↦
          (Finset.prod_pow Finset.univ 2 fun τ ↦ ‖m_u τ (h τ)‖).symm
      _ = _ := by
        rw [integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := μ)
          (fun τ x ↦ ‖m_u τ x‖ ^ 2)]
  refine ⟨htarget_int, ?_⟩
  calc
    _ ≤ ∫ h, ∏ τ, (‖m_u' τ (h τ)‖ * (max 1 (nrm τ (h τ))) ^ A)
        ∂Measure.pi μ := integral_mono htarget_int hprod_int hbound
    _ = ∏ τ, ∫ x, ‖m_u' τ x‖ * (max 1 (nrm τ x)) ^ A ∂μ τ := by
      rw [integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := μ)
        (fun τ x ↦ ‖m_u' τ x‖ * (max 1 (nrm τ x)) ^ A)]
    _ ≤ ∏ τ, (c τ * ∫ x, ‖m_u τ x‖ ^ 2 ∂μ τ) := by
      apply Finset.prod_le_prod₀
      · intro τ _
        exact integral_nonneg fun x ↦ mul_nonneg (norm_nonneg _)
          (pow_nonneg (zero_le_one.trans (le_max_left _ _)) A)
      · intro τ _
        exact hle τ
    _ = _ := by rw [Finset.prod_mul_distrib, hsq]

end TauCeti.ThetaLift
