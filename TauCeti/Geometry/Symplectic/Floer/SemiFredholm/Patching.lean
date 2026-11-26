/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Patching semi-Fredholm estimates on punctured domains

The semi-Fredholm estimate of the linearized Floer operator `D_u` on a punctured domain `S` with
cylindrical ends is patched together from estimates on the ends and an `L²` estimate on a compact
truncation of `S`, by cutting a section off with functions that are smooth on `S`. This file
records the two steps of the patching that do not depend on the domain.

* `TauCeti.SymplecticForm.integral_norm_floerLinearization_fun_smul_sq_le`: for a function `f`
  smooth on an open set `S` with `|f| ≤ 1` there, whose derivative is supported in a compact set
  `K` and bounded by `M` there, and for `‖J‖ ≤ B` along `u` on `K`, a `C²` section `ξ` with compact
  support in `S` satisfies `∫ ‖D_u (f ξ)‖² ≤ 2 ∫ ‖D_u ξ‖² + 2 (M (1 + B))² ∫_K ‖ξ‖²`.
* `TauCeti.Floer.exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_le`: for a monotone
  family of compact truncations `K T`, an estimate at every height `R₀` of the energy on the ends
  beyond `R₀ + 1` plus the energy on `K R₀`, by `C' (X ξ + ∫_{K (R₀ + 1)} ‖ξ‖²)`, gives the estimate
  at a single height `T` of the energy on the ends beyond `T` plus the energy on `K T`.

These are shared by the pair of pants (`TauCeti.Geometry.Symplectic.Floer.PairOfPants.SemiFredholm`)
and the spheres with moving input ends
(`TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds.SemiFredholm`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate on punctured Riemann surfaces with cylindrical
  ends.
-/

public section

open Set MeasureTheory

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The `L²` norm of the operator on a cut-off section.** Let `f` be `C²` on an open set `S`
with `|f| ≤ 1` there, with derivative supported in a compact set `K` and bounded by `M` there, and
let `‖J‖ ≤ B` along `u` on `K`. Then for a `C²` section `ξ` with compact support in `S`,
`∫ ‖D (f ξ)‖² ≤ 2 ∫ ‖D ξ‖² + 2 (M (1 + B))² ∫_K ‖ξ‖²`. -/
theorem integral_norm_floerLinearization_fun_smul_sq_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hJ : ∀ z ∈ S, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ S, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ S, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ S, ContDiffAt ℝ 1 u z) {K : Set (ℝ × ℝ)} (hK : IsCompact K) {f : ℝ × ℝ → ℝ}
    (hf : ∀ z ∈ S, ContDiffAt ℝ 2 f z) (hf₁ : ∀ z ∈ S, |f z| ≤ 1)
    (hfK : ∀ z ∈ S, fderiv ℝ f z ≠ 0 → z ∈ K) {M B : ℝ}
    (hM : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ M) (hB : ∀ z ∈ K, ‖J z (u z)‖ ≤ B) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 2 ξ) (hξc : HasCompactSupport ξ) (hξS : tsupport ξ ⊆ S) :
    ∫ z, ‖ω.floerLinearization J Ks Kt u (fun w ↦ f w • ξ w) z‖ ^ 2 ≤
      2 * (∫ z, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
        2 * (M * (1 + B)) ^ 2 * ∫ z in K, ‖ξ z‖ ^ 2 := by
  have hint {η : ℝ × ℝ → V} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
      (hηS : tsupport η ⊆ S) :
      Integrable fun z ↦ 1 * ‖ω.floerLinearization J Ks Kt u η z‖ ^ 2 := by
    simpa only [one_mul] using ω.integrable_norm_floerLinearization_sq
      (ω.continuous_floerLinearization_of_tsupport_subset hJ hKs hKt hu (hη.of_le one_le_two)
        hηS) hηc
  have hfξ : ContDiff ℝ 2 fun z ↦ f z • ξ z :=
    (ContinuousLinearMap.lsmul ℝ ℝ).contDiff_of_tsupport_subset_right
      (fun z hz ↦ (hf z hz).contDiffWithinAt) hξ.contDiffOn hS hξS
  simpa only [one_mul, mul_one] using integral_mul_norm_fun_smul_sq_le
    (D := ω.floerLinearization J Ks Kt u) (w := fun _ ↦ 1) (b := fun z ↦ ‖J z (u z)‖)
    (S := S) (fun _ ↦ zero_le_one) hK hfK hM hB zero_le_one (fun _ _ ↦ le_rfl) hξ.continuous
    (fun z hzS _ _ hM' hB' ↦ ω.norm_floerLinearization_fun_smul_sq_le J Ks Kt u ξ
      ((hf z hzS).differentiableAt two_ne_zero) (hξ.differentiable two_ne_zero z) (hf₁ z hzS)
      hM' hB')
    (fun z hzS ↦ ω.floerLinearization_of_notMem_tsupport J Ks Kt u fun h ↦
      hzS (hξS (tsupport_smul_subset_right _ _ h)))
    (hint hξ hξc hξS)
    (hint hfξ (hξc.smul_left (f := f)) ((tsupport_smul_subset_right _ _).trans hξS))

end TauCeti.SymplecticForm

namespace TauCeti.Floer

/-- **Patching at two heights.** Let `K T` be a monotone family of compact truncations of a
domain `S`, let `G q ξ` be a field `ξ` read on the end `q`, and let `r > 0`. Suppose that for
every height `R₀ ≥ r` above the heights `R q`, the energy of `G q ξ` beyond `R₀ + 1` on the ends
plus the energy of `ξ` on `K R₀` is at most `C' (X ξ + ∫_{K (R₀ + 1)} ‖ξ‖²)`. Then at a single
height `T ≥ r` the ends beyond `T` and the truncation `K T` are bounded by
`C (X ξ + ∫_{K (T + 1)} ‖ξ‖²)`: the bound at `R₀` controls the ends and the bound at `R₀ + 1` the
truncation. -/
theorem exists_forall_sum_setIntegral_add_setIntegral_le_of_forall_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {ι : Type*} [Fintype ι]
    {S : Set (ℝ × ℝ)} {K : ℝ → Set (ℝ × ℝ)} (hK : ∀ T, IsCompact (K T)) (hKm : Monotone K)
    {r : ℝ} (hr : 0 < r) {R : ι → ℝ} {G : ι → (ℝ × ℝ → W) → ℝ × ℝ → W}
    {X : (ℝ × ℝ → W) → ℝ}
    (h : ∀ R₀, r ≤ R₀ → (∀ q, R q < R₀) → ∃ C', 0 ≤ C' ∧ ∀ ⦃ξ : ℝ × ℝ → W⦄, ContDiff ℝ 2 ξ →
      HasCompactSupport ξ → tsupport ξ ⊆ S →
      (∑ q, ∫ ζ in Ioi (R₀ + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G q ξ) ζ) +
          ∫ z in K R₀, sobolevDensity ξ z ≤
        C' * (X ξ + ∫ z in K (R₀ + 1), ‖ξ z‖ ^ 2)) :
    ∃ C', 0 ≤ C' ∧ ∃ T, r ≤ T ∧ ∀ ⦃ξ : ℝ × ℝ → W⦄, ContDiff ℝ 2 ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ S →
      (∑ q, ∫ ζ in Ioi T ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G q ξ) ζ) +
        ∫ z in K T, sobolevDensity ξ z ≤ C' * (X ξ + ∫ z in K (T + 1), ‖ξ z‖ ^ 2) := by
  -- Patch at the heights `R₀` and `R₀ + 1`: the first controls the ends beyond `R₀ + 1`, the
  -- second the truncation `K (R₀ + 1)`.
  set R₀ := r + ∑ q, |R q|
  have hsum : 0 ≤ ∑ q, |R q| := Finset.sum_nonneg fun q _ ↦ abs_nonneg _
  have hR (q : ι) : R q < R₀ := by
    have := (le_abs_self (R q)).trans
      (Finset.single_le_sum (fun r _ ↦ abs_nonneg (R r)) (Finset.mem_univ q))
    linarith
  obtain ⟨C₁, hC₁, h₁⟩ := h R₀ (by linarith) hR
  obtain ⟨C₂, hC₂, h₂⟩ := h (R₀ + 1) (by linarith) fun q ↦ (hR q).trans (lt_add_one _)
  refine ⟨C₁ + C₂, by positivity, R₀ + 1, by linarith, fun ξ hξ hξc hξS ↦ ?_⟩
  have e₁ := h₁ hξ hξc hξS
  have e₂ := h₂ hξ hξc hξS
  have hY : ∫ z in K (R₀ + 1), ‖ξ z‖ ^ 2 ≤ ∫ z in K (R₀ + 1 + 1), ‖ξ z‖ ^ 2 :=
    setIntegral_mono_set ((hξ.continuous.norm.pow 2).continuousOn.integrableOn_compact (hK _))
      (ae_of_all _ fun _ ↦ sq_nonneg _) (.of_forall fun _ hz ↦ hKm (by linarith) hz)
  have hcore₀ : 0 ≤ ∫ z in K R₀, sobolevDensity ξ z :=
    setIntegral_nonneg (hK _).measurableSet fun z _ ↦ sobolevDensity_nonneg ξ z
  have hends₀ : 0 ≤ ∑ q, ∫ ζ in Ioi (R₀ + 1 + 1) ×ˢ Icc (0 : ℝ) 1, sobolevDensity (G q ξ) ζ :=
    Finset.sum_nonneg fun q _ ↦ setIntegral_nonneg (measurableSet_Ioi.prod measurableSet_Icc)
      fun ζ _ ↦ sobolevDensity_nonneg _ ζ
  nlinarith [mul_le_mul_of_nonneg_left hY hC₁]

end TauCeti.Floer
