/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.DiscPreparation
public import TauCeti.RingTheory.PowerSeries.Entire.Topology
public import TauCeti.RingTheory.PowerSeries.GaussNorm.Radius

/-!
# Approximation by normalised disc polynomials

For a normalised disc preparation `f = P * U` at radius `r`, shrinking to a
positive radius `s ≤ r` gives

```text
‖U - 1‖_s ≤ s / r,       ‖P‖_s = ‖f‖_s,
‖f - P‖_s ≤ ‖f‖_s * (s / r).
```

Thus disc polynomials at radii tending to infinity converge to `f` in every
fixed Gauss norm, and hence in the topology of entire series. The convergence
statement applies to any family of normalised preparations; uniqueness of disc
preparation makes the result independent of choices. For an entire series with
constant coefficient one, such a family exists over a complete nonarchimedean
field. These are the polynomial approximants used in entire product expansions.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§3–4.
-/

public section

open Filter
open scoped Topology

namespace TauCeti.PowerSeries

open _root_.PowerSeries

variable {K : Type*} [NormedField K]
  {r s : ℝ} {d : ℕ} {f U : PowerSeries K} {P : Polynomial K}

namespace IsDiscPreparation

/-- The normalised cofactor is uniformly close to one on a smaller disc, with
an explicit bound depending only on the ratio of radii. -/
theorem gaussNorm_sub_one_le_div (h : IsDiscPreparation r d f P U)
    (hr : 0 < r) (hs : 0 ≤ s) (hsr : s ≤ r) :
    (U - 1).gaussNorm norm s ≤ s / r := by
  have hbound := PowerSeries.gaussNorm_sub_one_le_mul_div (f := U) hr hs hsr
    (hasGaussNorm_of_isRestricted (h.isRestricted.sub (isRestricted_one r)))
    h.constantCoeff_eq_one
  exact hbound.trans (mul_le_of_le_one_left (by positivity) h.gaussNorm_sub_one_lt.le)

variable [IsUltrametricDist K]

/-- The disc polynomial has the same Gauss norm as the series on every positive
smaller disc, not only on the preparation disc. -/
theorem gaussNorm_coe_of_le (h : IsDiscPreparation r d f P U)
    (hs : 0 < s) (hsr : s ≤ r) :
    (P : PowerSeries K).gaussNorm norm s = f.gaussNorm norm s := by
  have hUs := isRestricted_of_abs_le h.isRestricted (abs_le_abs_of_nonneg hs.le hsr)
  have hclose : (U - 1).gaussNorm norm s < 1 :=
    (gaussNorm_le_gaussNorm_of_le norm_nonneg hs.le hsr
      (hasGaussNorm_of_isRestricted (h.isRestricted.sub (isRestricted_one r)))).trans_lt
        h.gaussNorm_sub_one_lt
  rw [h.eq_mul, gaussNorm_mul_of_isRestricted hs (isRestricted_polynomial P) hUs,
    gaussNorm_eq_one_of_gaussNorm_sub_one_lt hUs hclose, mul_one]

/-- The normalised disc polynomial approximates the series on every smaller
positive disc, with error at most `‖f‖_s * (s / r)`. -/
theorem gaussNorm_sub_le_mul_div (h : IsDiscPreparation r d f P U)
    (hs : 0 < s) (hsr : s ≤ r) :
    (f - P).gaussNorm norm s ≤ f.gaussNorm norm s * (s / r) := by
  have hUs := isRestricted_of_abs_le h.isRestricted (abs_le_abs_of_nonneg hs.le hsr)
  have heq : f - P = (P : PowerSeries K) * (U - 1) := by
    rw [h.eq_mul, mul_sub, mul_one]
  rw [heq, gaussNorm_mul_of_isRestricted hs (isRestricted_polynomial P)
    (hUs.sub (isRestricted_one s)), h.gaussNorm_coe_of_le hs hsr]
  exact mul_le_mul_of_nonneg_left (h.gaussNorm_sub_one_le_div (hs.trans_le hsr) hs.le hsr)
    (PowerSeries.gaussNorm_nonneg _ _ _ norm_nonneg)

end IsDiscPreparation

variable [IsUltrametricDist K] {ι : Type*} {l : Filter ι} {ρ : ι → ℝ} {D : ι → ℕ}
  {p : ι → Polynomial K} {u : ι → PowerSeries K}

omit [IsUltrametricDist K] in
/-- At radii tending to infinity, any family of normalised disc cofactors tends
to one in each fixed positive-radius Gauss norm. Only eventual preparation is needed. -/
theorem tendsto_gaussNorm_sub_one_of_isDiscPreparation
    (hρ : Tendsto ρ l atTop)
    (h : ∀ᶠ i in l, IsDiscPreparation (ρ i) (D i) f (p i) (u i)) (hs : 0 < s) :
    Tendsto (fun i ↦ (u i - 1).gaussNorm norm s) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦
    PowerSeries.gaussNorm_nonneg _ _ _ norm_nonneg) ?_
    ((tendsto_const_nhds (x := s)).div_atTop hρ)
  filter_upwards [h, hρ.eventually_ge_atTop s] with i hi hsi
  exact hi.gaussNorm_sub_one_le_div (hs.trans_le hsi) hs.le hsi

/-- At radii tending to infinity, the normalised disc polynomials converge to
the series in every fixed positive-radius Gauss norm. -/
theorem tendsto_gaussNorm_sub_of_isDiscPreparation
    (hρ : Tendsto ρ l atTop)
    (h : ∀ᶠ i in l, IsDiscPreparation (ρ i) (D i) f (p i) (u i)) (hs : 0 < s) :
    Tendsto (fun i ↦ (f - p i).gaussNorm norm s) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦
    PowerSeries.gaussNorm_nonneg _ _ _ norm_nonneg) ?_
    (by simpa using
      ((tendsto_const_nhds (x := s)).div_atTop hρ).const_mul (f.gaussNorm norm s))
  filter_upwards [h, hρ.eventually_ge_atTop s] with i hi hsi
  exact hi.gaussNorm_sub_le_mul_div hs hsi

end TauCeti.PowerSeries

namespace PowerSeries.IsEntire

open TauCeti.PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {f : PowerSeries K}
  {ι : Type*} {l : Filter ι} {ρ : ι → ℝ} {D : ι → ℕ}
  {p : ι → Polynomial K} {u : ι → PowerSeries K}

/-- Disc polynomials converge in the topology of entire series whenever their
preparation radii tend to infinity. -/
theorem tendsto_polynomialHom_of_isDiscPreparation (hf : f.IsEntire)
    (hρ : Tendsto ρ l atTop)
    (h : ∀ᶠ i in l, IsDiscPreparation (ρ i) (D i) f (p i) (u i)) :
    Tendsto (fun i ↦ IsEntire.polynomialHom (p i)) l
      (𝓝 (⟨f, IsEntire.mem_subring.mpr hf⟩ : IsEntire.subring K)) := by
  rw [IsEntire.tendsto_iff]
  intro s
  let : Fact (0 < (s : ℝ)) := ⟨s.2⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim := tendsto_gaussNorm_sub_of_isDiscPreparation hρ h s.2
  simpa only [dist_eq_norm_sub', norm_eq_gaussNorm, AddSubgroupClass.coe_sub,
    IsEntire.coe_restrict, IsEntire.coe_polynomialHom] using hlim

variable [CompleteSpace K]

/-- An entire series with constant coefficient one admits normalised preparations
at all positive radii whose polynomial factors converge in the entire-series topology.
The factors are uniquely determined at each radius by normalised disc preparation. -/
theorem exists_discPreparations_tendsto (hf : f.IsEntire) (h0 : constantCoeff f = 1) :
    ∃ (p : Set.Ioi (0 : ℝ) → Polynomial K) (u : Set.Ioi (0 : ℝ) → PowerSeries K)
      (D : Set.Ioi (0 : ℝ) → ℕ),
      (∀ r : Set.Ioi (0 : ℝ), IsDiscPreparation (r : ℝ) (D r) f (p r) (u r)) ∧
      Tendsto (fun r ↦ IsEntire.polynomialHom (p r)) atTop
        (𝓝 (⟨f, IsEntire.mem_subring.mpr hf⟩ : IsEntire.subring K)) := by
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at h0
  have hex (r : Set.Ioi (0 : ℝ)) : ∃ (D : ℕ) (p : Polynomial K) (u : PowerSeries K),
      IsDiscPreparation (r : ℝ) D f p u := by
    obtain ⟨D, hD⟩ := exists_isDistinguished r.2 (hf.isRestricted r) hf0
    exact ⟨D, hD.exists_isDiscPreparation r.2 (hf.isRestricted r) h0⟩
  choose D p u h using hex
  refine ⟨p, u, D, h, tendsto_polynomialHom_of_isDiscPreparation hf ?_
    (Eventually.of_forall h)⟩
  exact tendsto_Ioi_atTop.mp tendsto_id

end PowerSeries.IsEntire
