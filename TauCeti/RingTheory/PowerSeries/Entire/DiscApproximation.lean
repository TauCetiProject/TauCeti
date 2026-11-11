/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.DiscPreparation
public import TauCeti.RingTheory.PowerSeries.Entire.Topology

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
