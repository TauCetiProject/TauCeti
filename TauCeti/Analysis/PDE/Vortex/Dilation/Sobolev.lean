/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Dilation.Basic
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Dilations on the affine Sobolev field space

Pulling a field back by the dilation `z ↦ t • z` (`TauCeti.Vortex.dilateField`) acts on the
affine Sobolev field space `A_m^k` of framed plane vortex fields.

* Nonzero dilations preserve the natural-order Sobolev fields
  (`TauCeti.Vortex.dilateField_mem_sobolevFields_natCast_iff`).
* A positive dilation fixes the reference field off a disc, since the winding phase is homogeneous
  of degree `0` and the angular form `dθ` is invariant under dilations
  (`TauCeti.Vortex.hasCompactSupport_dilateField_referenceField_sub`), so it maps `A_m^k` onto
  itself (`TauCeti.Vortex.dilateField_mem_framedFieldSpace_iff`).
* For `t ≠ 0`, pullback of a gauge, `u ↦ u (t ·)`, preserves the Sobolev gauge groups `G_s` of
  integer order `s > 1` (`TauCeti.Vortex.comp_smul_mem_sobolevGaugeGroup_iff`). Since pulling back
  a gauge transform is the gauge transform by the pulled-back gauge
  (`TauCeti.Vortex.dilateField_gaugeTransform`), a nonzero dilation maps `G_s` gauge orbits onto
  `G_s` gauge orbits (`TauCeti.Vortex.exists_sobolevGaugeGroup_gaugeTransform_dilateField_eq_iff`).
  For `k > 1` and `t > 0` it therefore intertwines the actions of `G_(k+1)` on `A_m^k`
  (`TauCeti.Vortex.exists_sobolevGaugeGroup_smul_dilateField_eq_iff`).

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

open Complex Filter Topology TemperedDistribution

namespace TauCeti.Vortex

variable {t : ℝ} {m : ℕ}

/-- Nonzero dilations preserve the natural-order Sobolev fields. -/
theorem dilateField_mem_sobolevFields_natCast (ht : t ≠ 0) {k : ℕ}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields k) :
    dilateField t y ∈ sobolevFields k := by
  have h (j : Fin 4) : (fun z ↦ y (t • z) j) ∈ realSobolevFunctions ℂ k 2 :=
    comp_smul_mem_realSobolevFunctions_natCast (by norm_num) (by norm_num) ht
      (mem_sobolevFields.1 hy j)
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · simpa [dilateField_apply, Pi.smul_def] using Submodule.smul_mem _ t (h 0)
  · simpa [dilateField_apply, Pi.smul_def] using Submodule.smul_mem _ t (h 1)
  · simpa [dilateField_apply] using h 2
  · simpa [dilateField_apply] using h 3

/-- A field lies in `H^k` exactly when its pullback by a nonzero dilation does. -/
theorem dilateField_mem_sobolevFields_natCast_iff (ht : t ≠ 0) {k : ℕ}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    dilateField t y ∈ sobolevFields k ↔ y ∈ sobolevFields k := by
  refine ⟨fun h ↦ ?_, dilateField_mem_sobolevFields_natCast ht⟩
  simpa [inv_mul_cancel₀ ht] using dilateField_mem_sobolevFields_natCast (inv_ne_zero ht) h

/-- A positive dilation fixes the reference field off a disc: the winding phase is homogeneous of
degree `0` and the angular form `dθ` is invariant. So the two differ by a compactly supported
field. -/
theorem hasCompactSupport_dilateField_referenceField_sub (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (ht : 0 < t) : HasCompactSupport (dilateField t (referenceField f m) - referenceField f m) := by
  rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact]
  have hr := f.rOut_pos
  have hst := div_nonneg (Real.sqrt_nonneg f.rOut) ht.le
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop
    (√f.rOut + √f.rOut / t + 1)] with z hz
  have hsq {s : ℝ} (hs : √f.rOut ≤ s) : f.rOut ≤ s ^ 2 :=
    (Real.sq_sqrt hr.le).symm.le.trans (pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2)
  have h₁ : f.rOut ≤ ‖z‖ ^ 2 := hsq (by linarith [Real.sqrt_nonneg f.rOut])
  have h₂ : f.rOut ≤ ‖t • z‖ ^ 2 := hsq (by
    rw [norm_smul, Real.norm_of_nonneg ht.le, ← div_le_iff₀' ht]
    linarith [Real.sqrt_nonneg f.rOut])
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith [Real.sqrt_nonneg f.rOut])
  simp only [Pi.sub_apply, Pi.zero_apply, dilateField_apply, referenceField_eq_of_rOut_le f m h₁,
    referenceField_eq_of_rOut_le f m h₂, smul_div_norm_smul ht, sub_eq_zero]
  ext i
  fin_cases i <;> simp [abs_of_pos ht] <;> field_simp

/-- **Dilation of the affine field space.** A positive dilation maps `A_m^k` into itself, for
every natural order `k`. -/
theorem dilateField_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {k : ℕ} (ht : 0 < t)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m k) :
    dilateField t x ∈ framedFieldSpace f m k := by
  rw [mem_framedFieldSpace] at hx ⊢
  have href := mem_sobolevFields_of_hasCompactSupport
    (y := dilateField t (referenceField f m) - referenceField f m)
    ((contDiff_dilateField (contDiff_referenceField f m) t).sub (contDiff_referenceField f m))
    (hasCompactSupport_dilateField_referenceField_sub f m ht) k
  have hsplit : dilateField t x - referenceField f m = dilateField t (x - referenceField f m) +
      (dilateField t (referenceField f m) - referenceField f m) := by
    rw [dilateField_sub]
    abel
  rw [hsplit]
  exact add_mem (dilateField_mem_sobolevFields_natCast ht.ne' hx) href

/-- A field lies in `A_m^k` exactly when its pullback by a positive dilation does. -/
theorem dilateField_mem_framedFieldSpace_iff {f : ContDiffBump (0 : ℝ)} {k : ℕ} (ht : 0 < t)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} :
    dilateField t x ∈ framedFieldSpace f m k ↔ x ∈ framedFieldSpace f m k := by
  refine ⟨fun h ↦ ?_, dilateField_mem_framedFieldSpace ht⟩
  simpa [inv_mul_cancel₀ ht.ne'] using dilateField_mem_framedFieldSpace (inv_pos.2 ht) h

/-! ### The Sobolev gauge groups -/

/-- Pullback by a nonzero dilation preserves the Sobolev gauge group `G_s` of each integer
order `s > 1`. The order is any real `s` equal to a natural number, so that this applies both to
`G_k` and to the group `G_(k+1)` indexed by `(k : ℝ) + 1` that acts on `A_m^k`. -/
theorem comp_smul_mem_sobolevGaugeGroup (ht : t ≠ 0) {s : ℝ} {hs : 1 < s} {k : ℕ}
    (hsk : s = k) {u : ℂ → Circle} (hu : u ∈ sobolevGaugeGroup hs) :
    (fun z ↦ u (t • z)) ∈ sobolevGaugeGroup hs := by
  subst hsk
  obtain ⟨hc, h₁, h₂⟩ := (mem_sobolevGaugeGroup hs u).1 hu
  exact (mem_sobolevGaugeGroup hs _).2 ⟨hc.comp (continuous_const_smul t),
    comp_smul_mem_realSobolevFunctions_natCast (by norm_num) (by norm_num) ht h₁,
    comp_smul_mem_realSobolevFunctions_natCast (by norm_num) (by norm_num) ht h₂⟩

/-- A gauge lies in the Sobolev gauge group `G_s` of integer order `s > 1` exactly when its
pullback by a nonzero dilation does. -/
theorem comp_smul_mem_sobolevGaugeGroup_iff (ht : t ≠ 0) {s : ℝ} {hs : 1 < s} {k : ℕ}
    (hsk : s = k) {u : ℂ → Circle} :
    (fun z ↦ u (t • z)) ∈ sobolevGaugeGroup hs ↔ u ∈ sobolevGaugeGroup hs := by
  refine ⟨fun h ↦ ?_, comp_smul_mem_sobolevGaugeGroup ht hsk⟩
  simpa only [smul_smul, mul_inv_cancel₀ ht, one_smul] using
    comp_smul_mem_sobolevGaugeGroup (inv_ne_zero ht) hsk h

/-- **Dilation preserves Sobolev gauge orbits.** For `t ≠ 0` and an integer order `s > 1`, the
fields `x` and `y` are related by a gauge transformation in `G_s` exactly when their pullbacks by
`z ↦ t z` are. -/
theorem exists_sobolevGaugeGroup_gaugeTransform_dilateField_eq_iff (ht : t ≠ 0) {s : ℝ}
    {hs : 1 < s} {k : ℕ} (hsk : s = k) {x y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    (∃ u ∈ sobolevGaugeGroup hs, gaugeTransform u (dilateField t y) = dilateField t x) ↔
      ∃ u ∈ sobolevGaugeGroup hs, gaugeTransform u y = x := by
  -- Pulling back a relating gauge by `t` relates the pulled-back fields; pulling back by `t⁻¹`
  -- undoes the dilation.
  have key {r : ℝ} (hr : r ≠ 0) {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
      (h : ∃ u ∈ sobolevGaugeGroup hs, gaugeTransform u y = x) :
      ∃ u ∈ sobolevGaugeGroup hs, gaugeTransform u (dilateField r y) = dilateField r x := by
    obtain ⟨u, hu, rfl⟩ := h
    exact ⟨_, comp_smul_mem_sobolevGaugeGroup hr hsk hu, (dilateField_gaugeTransform r u y).symm⟩
  refine ⟨fun h ↦ ?_, key ht⟩
  simpa [inv_mul_cancel₀ ht] using key (inv_ne_zero ht) h

/-- **Dilation intertwines the actions of `G_(k+1)` on `A_m^k`.** For `k > 1` and `t > 0`, two
framed fields of `A_m^k` lie in the same `G_(k+1)` orbit exactly when their pullbacks by
`z ↦ t z` do. -/
theorem exists_sobolevGaugeGroup_smul_dilateField_eq_iff {k : ℕ} [Fact (1 < k)]
    {hs : 1 < (k : ℝ) + 1} {f : ContDiffBump (0 : ℝ)} (ht : 0 < t)
    {x y : framedFieldSpace f m k} :
    (∃ u : sobolevGaugeGroup hs, u • (⟨dilateField t y,
        dilateField_mem_framedFieldSpace ht y.property⟩ : framedFieldSpace f m k) =
      ⟨dilateField t x, dilateField_mem_framedFieldSpace ht x.property⟩) ↔
      ∃ u : sobolevGaugeGroup hs, u • y = x := by
  simp only [Subtype.ext_iff, coe_sobolevGaugeGroup_smul, Subtype.exists, exists_prop]
  exact exists_sobolevGaugeGroup_gaugeTransform_dilateField_eq_iff ht.ne' (Nat.cast_succ k).symm

end TauCeti.Vortex
