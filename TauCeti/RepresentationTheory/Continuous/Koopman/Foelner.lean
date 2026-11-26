/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Foelner
public import TauCeti.RepresentationTheory.Continuous.AlmostInvariant
public import TauCeti.RepresentationTheory.Continuous.Koopman.Basic

/-!
# Følner vectors in counting-measure Koopman representations

For a group `G` acting measurably on a space `X` with measurable singletons, the normalized
indicator of a finite nonempty set `F ⊆ X` tensor a unit vector `c ∈ E` is a unit vector in
`ℓ²(X, E)` whose squared Koopman displacement under `g` equals the relative translation boundary
`|g • F ∆ F| / |F|`. Consequently, finite Følner sets on `X` — and in particular any
counting-measure Følner family `IsFoelner G Measure.count l F` along a nontrivial filter — yield
almost invariant vectors in `ℓ²(X, E)` whenever `E` is nontrivial.

## Main results

* `Finset.norm_count_koopman_sub_indicatorConstLp`: Koopman displacement of a constant indicator on
  a finite set `F ⊆ X`.
* `MeasureTheory.Measure.hasAlmostInvariantVectors_count_koopman_of_forall_exists_finset`: finite
  Følner sets on `X` produce almost invariant vectors in `ℓ²(X, E)`.
* `IsFoelner.hasAlmostInvariantVectors_count_koopman`: a counting-measure Følner family on `X` along
  a nontrivial filter produces almost invariant vectors in `ℓ²(X, E)`.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open MeasureTheory Filter Finset
open scoped ENNReal Pointwise symmDiff

namespace MeasureTheory.Measure

variable {G X 𝕜 E : Type*} [Group G] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MulAction G X] [MeasurableConstSMul G X]

/-- In counting-measure `L²`, the Koopman displacement of a constant indicator supported on a
finite set `F` is `√|g • F ∆ F| * ‖c‖`. -/
theorem _root_.Finset.norm_count_koopman_sub_indicatorConstLp [DecidableEq X] [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (F : Finset X) (g : G) (c : E) :
    ‖(count : Measure X).koopman G 𝕜 E 2 g
        (indicatorConstLp 2 F.measurableSet (by simp) c) -
      indicatorConstLp 2 F.measurableSet (by simp) c‖ =
        Real.sqrt (#((g • F) ∆ F) : ℝ) * ‖c‖ := by
  have hpre : (fun x : X ↦ g⁻¹ • x) ⁻¹' (F : Set X) = (g • F : Finset X) := by
    ext x
    simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_smul_finset]
    exact ⟨fun hx ↦ ⟨g⁻¹ • x, hx, smul_inv_smul g x⟩,
      fun ⟨y, hy, hyx⟩ ↦ by rwa [← hyx, inv_smul_smul]⟩
  rw [koopman_apply, Lp.indicatorConstLp_compMeasurePreserving, ← dist_eq_norm_sub,
    dist_indicatorConstLp_eq_norm, norm_indicatorConstLp (p := 2) (by simp) (by simp)]
  simp [hpre, ← Finset.coe_symmDiff, measureReal_def, Real.sqrt_eq_rpow,
    -Finset.coe_smul_finset, mul_comm]

/-- **Action-level Følner-indicator almost invariant vectors.** If `E` is nontrivial and a `G`-set
`X` admits finite nonempty Følner sets for every finite subset of `G` and positive tolerance, then
the counting-measure Koopman representation on `ℓ²(X, E)` has almost invariant vectors. -/
theorem hasAlmostInvariantVectors_count_koopman_of_forall_exists_finset [DecidableEq X]
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E]
    (hF : ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset X, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F) :
    ((count : Measure X).koopman G 𝕜 E 2).HasAlmostInvariantVectors := by
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  rw [ContRepresentation.hasAlmostInvariantVectors_def]
  intro K ε hε
  let c : E := (‖w‖⁻¹ : 𝕜) • w
  have hc : ‖c‖ = 1 := norm_smul_inv_norm hw
  obtain ⟨F, hF_ne, hboundary⟩ := hF K (ε ^ 2) (sq_pos_of_pos hε)
  let ξ : Lp E 2 (count : Measure X) := indicatorConstLp 2 F.measurableSet (by simp) c
  have hnorm : ‖ξ‖ = Real.sqrt (#F : ℝ) := by
    rw [norm_indicatorConstLp (by simp) (by simp)]
    simp [hc, measureReal_def, Real.sqrt_eq_rpow]
  have hcard : (0 : ℝ) < #F := Nat.cast_pos.mpr hF_ne.card_pos
  have hξ : ξ ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; positivity)
  refine ⟨(‖ξ‖⁻¹ : 𝕜) • ξ, norm_smul_inv_norm hξ, fun g hg ↦ ?_⟩
  rw [map_smul, ← smul_sub]
  have hdisp : ‖(count : Measure X).koopman G 𝕜 E 2 g ξ - ξ‖ =
      Real.sqrt (#((g • F) ∆ F) : ℝ) := by
    simpa [hc] using F.norm_count_koopman_sub_indicatorConstLp (G := G) (𝕜 := 𝕜) g c
  have hroot : Real.sqrt (#((g • F) ∆ F) : ℝ) < ε * Real.sqrt (#F : ℝ) := by
    apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hcard.le]
    exact hboundary g hg
  simpa [norm_smul, hnorm, hdisp, abs_of_nonneg (Real.sqrt_nonneg _)] using
    (inv_mul_lt_iff₀ (Real.sqrt_pos.mpr hcard)).mpr (by simpa [mul_comm] using hroot)

end MeasureTheory.Measure

/-- A counting-measure Følner family along a nontrivial filter produces almost invariant unit
vectors in the vector-valued Koopman representation `ℓ²(X, E)` whenever `E` is nontrivial. -/
theorem IsFoelner.hasAlmostInvariantVectors_count_koopman {G X 𝕜 E ι : Type*} [Group G]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MulAction G X] [MeasurableConstSMul G X]
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E]
    {l : Filter ι} [l.NeBot] {F : ι → Set X}
    (hF : IsFoelner G (Measure.count : Measure X) l F) :
    ((Measure.count : Measure X).koopman G 𝕜 E 2).HasAlmostInvariantVectors := by
  classical
  exact Measure.hasAlmostInvariantVectors_count_koopman_of_forall_exists_finset
    fun K _ hε ↦ hF.exists_finset_card_smul_symmDiff_lt K hε
