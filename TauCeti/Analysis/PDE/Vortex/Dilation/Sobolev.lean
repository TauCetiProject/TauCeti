/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Dilation.Basic
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables

/-!
# Dilations on the Sobolev scale of framed plane vortices

Pullback by the dilation `z ↦ t z` (`TauCeti.Vortex.dilateField`) multiplies the connection
components of a plane vortex field by `t` and composes all components with the dilation. It
carries, for `t ≠ 0`, the equation `*iF_a = c (1 - |α|²) / 8` to the same equation with coupling
`t² c` (`TauCeti.Vortex.coupledEquation_dilateField_eq_zero_iff'`); for `t = (2r)^(-1/2)` this
turns the large-parameter equation `*iF_a = (r / 4) (1 - |α|²)` into the normalized plane vortex
equation (`TauCeti.Vortex.equation_dilateField_inv_sqrt_eq_zero_iff`). This file shows that the
dilation is compatible with the concrete Sobolev scale on which plane vortices are studied, at
natural orders `k`:

* **Sobolev fields.** For `t ≠ 0`, the dilation preserves the Sobolev fields `H^k(ℂ; ℝ⁴)`
  (`dilateField_mem_sobolevFields_natCast_iff`): it is a linear change of variables followed by
  multiplication of two components by the constant `t`.
* **The affine field space.** For `t > 0`, the dilation fixes the reference field
  `(-i m dθ, (z / |z|)^m)` outside a disc, since `dθ` and `z / |z|` are invariant under positive
  dilations (`hasCompactSupport_dilateField_referenceField_sub`). Hence it preserves the affine
  space `A_m^k = x_m + H^k` of framed degree-`m` fields
  (`dilateField_mem_framedFieldSpace_natCast_iff`). For `t < 0` and odd `m` it does not, since
  the end framing changes sign.
* **Sobolev gauge groups.** For `t ≠ 0`, pullback of a gauge, `u ↦ u (t ·)`, preserves the Sobolev
  gauge groups `G_s` of integer order `s > 1` (`comp_smul_mem_sobolevGaugeGroup_iff`). Since
  pulling back a gauge transform is the gauge transform by the pulled-back gauge
  (`TauCeti.Vortex.dilateField_gaugeTransform`), a nonzero dilation maps `G_s` gauge orbits onto
  `G_s` gauge orbits (`exists_sobolevGaugeGroup_gaugeTransform_dilateField_eq_iff`). For `k > 1`
  and `t > 0` it therefore intertwines the actions of `G_(k+1)` on `A_m^k`
  (`exists_sobolevGaugeGroup_smul_dilateField_eq_iff`).

With the scaling of the zero divisor and of the end framing
(`TauCeti.Vortex.isZeroMultiplicity_sectionValue_dilateField`,
`TauCeti.Vortex.tendsto_sectionValue_dilateField`), pullback to the coordinate `w = √(2r) z`
carries a framed degree-`m` solution in `A_m^k` of the equation with coupling `2r` and divisor
`D` to a plane vortex in `A_m^k` with divisor `√(2r) D`, and back.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter TemperedDistribution
open scoped ContDiff Topology

variable {t : ℝ}

/-! ### Sobolev fields -/

/-- Pullback by a nonzero dilation preserves the integer-order Sobolev fields. -/
theorem dilateField_mem_sobolevFields_natCast (ht : t ≠ 0) {k : ℕ}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields k) :
    dilateField t y ∈ sobolevFields k := by
  have h (j : Fin 4) : (fun z ↦ y (t • z) j) ∈ realSobolevFunctions ℂ k 2 :=
    comp_smul_mem_realSobolevFunctions_natCast (by norm_num) (by norm_num) ht
      (mem_sobolevFields.1 hy j)
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · convert Submodule.smul_mem _ t (h 0) using 1
    ext z
    simp
  · convert Submodule.smul_mem _ t (h 1) using 1
    ext z
    simp
  · simpa using h 2
  · simpa using h 3

/-- A field lies in `H^k` exactly when its pullback by a nonzero dilation does. -/
theorem dilateField_mem_sobolevFields_natCast_iff (ht : t ≠ 0) {k : ℕ}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    dilateField t y ∈ sobolevFields k ↔ y ∈ sobolevFields k := by
  refine ⟨fun h ↦ ?_, dilateField_mem_sobolevFields_natCast ht⟩
  simpa [inv_mul_cancel₀ ht] using dilateField_mem_sobolevFields_natCast (inv_ne_zero ht) h

/-! ### The reference field and the affine field space -/

/-- Off the discs where the cutoffs act, a positive dilation fixes the reference field: its
connection `-i m dθ` and its section `(z / |z|)^m` are invariant under `z ↦ t z`. -/
theorem dilateField_referenceField_apply_eq (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (ht : 0 < t) {z : ℂ} (hz : f.rOut ≤ ‖z‖ ^ 2) (htz : f.rOut ≤ ‖t • z‖ ^ 2) :
    dilateField t (referenceField f m) z = referenceField f m z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 (ne_zero_of_rOut_le_norm_sq f hz)
  have hnorm : ‖t • z‖ = t * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
  have hphase : t • z / (‖t • z‖ : ℂ) = z / (‖z‖ : ℂ) := by
    rw [hnorm, Complex.real_smul, ofReal_mul, mul_div_mul_left _ _ (ofReal_ne_zero.2 ht.ne')]
  rw [dilateField_apply, referenceField_eq_of_rOut_le f m htz, referenceField_eq_of_rOut_le f m hz,
    hphase, hnorm]
  ext i
  fin_cases i <;> simp <;> field_simp

/-- A positive dilation changes the reference field of degree `m` only on a compact set. -/
theorem hasCompactSupport_dilateField_referenceField_sub (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (ht : 0 < t) : HasCompactSupport (dilateField t (referenceField f m) - referenceField f m) := by
  rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact]
  have h₁ : ∀ᶠ z : ℂ in cocompact ℂ, √f.rOut ≤ ‖z‖ :=
    tendsto_norm_cocompact_atTop.eventually_ge_atTop _
  have h₂ : ∀ᶠ z : ℂ in cocompact ℂ, √f.rOut / t ≤ ‖z‖ :=
    tendsto_norm_cocompact_atTop.eventually_ge_atTop _
  filter_upwards [h₁, h₂] with z hz₁ hz₂
  have htz : √f.rOut ≤ ‖t • z‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht.le]
    rwa [div_le_iff₀ ht, mul_comm] at hz₂
  rw [Pi.sub_apply, dilateField_referenceField_apply_eq f m ht (Real.sqrt_le_iff.1 hz₁).2
    (Real.sqrt_le_iff.1 htz).2, sub_self, Pi.zero_apply]

/-- A positive dilation changes the reference field by a field in every Sobolev space. -/
theorem dilateField_referenceField_sub_mem_sobolevFields (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (ht : 0 < t) (s : ℝ) : dilateField t (referenceField f m) - referenceField f m ∈
      sobolevFields s :=
  mem_sobolevFields_of_hasCompactSupport
    ((contDiff_dilateField (contDiff_referenceField f m) t).sub (contDiff_referenceField f m))
    (hasCompactSupport_dilateField_referenceField_sub f m ht) s

/-- **Positive dilations act on `A_m^k`.** Pullback by `z ↦ t z`, `t > 0`, maps the affine space
of framed degree-`m` fields of natural order `k` to itself. -/
theorem dilateField_mem_framedFieldSpace_natCast {f : ContDiffBump (0 : ℝ)} {m k : ℕ} (ht : 0 < t)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m k) :
    dilateField t x ∈ framedFieldSpace f m k := by
  rw [mem_framedFieldSpace] at hx ⊢
  have hsplit : dilateField t x - referenceField f m = dilateField t (x - referenceField f m) +
      (dilateField t (referenceField f m) - referenceField f m) := by
    rw [dilateField_sub]
    abel
  rw [hsplit]
  exact add_mem (dilateField_mem_sobolevFields_natCast ht.ne' hx)
    (dilateField_referenceField_sub_mem_sobolevFields f m ht k)

/-- A field lies in `A_m^k` exactly when its pullback by a positive dilation does. -/
theorem dilateField_mem_framedFieldSpace_natCast_iff {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (ht : 0 < t) {x : ℂ → EuclideanSpace ℝ (Fin 4)} :
    dilateField t x ∈ framedFieldSpace f m k ↔ x ∈ framedFieldSpace f m k := by
  refine ⟨fun h ↦ ?_, dilateField_mem_framedFieldSpace_natCast ht⟩
  simpa [inv_mul_cancel₀ ht.ne'] using dilateField_mem_framedFieldSpace_natCast (inv_pos.2 ht) h

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
    {hs : 1 < (k : ℝ) + 1} {f : ContDiffBump (0 : ℝ)} {m : ℕ} (ht : 0 < t)
    {x y : framedFieldSpace f m k} :
    (∃ u : sobolevGaugeGroup hs, u • (⟨dilateField t y,
        dilateField_mem_framedFieldSpace_natCast ht y.2⟩ : framedFieldSpace f m k) =
      ⟨dilateField t x, dilateField_mem_framedFieldSpace_natCast ht x.2⟩) ↔
      ∃ u : sobolevGaugeGroup hs, u • y = x := by
  simp only [Subtype.ext_iff, coe_sobolevGaugeGroup_smul, Subtype.exists, exists_prop]
  exact exists_sobolevGaugeGroup_gaugeTransform_dilateField_eq_iff ht.ne' (Nat.cast_succ k).symm

end TauCeti.Vortex
