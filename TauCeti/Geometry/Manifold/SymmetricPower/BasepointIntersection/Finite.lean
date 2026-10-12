/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SymmetricPower.BasepointIntersection.Basic
import TauCeti.Analysis.Analytic.IsolatedZeros

/-!
# Finiteness of basepoint intersections in a symmetric chart

The basepoint divisor of a symmetric power is an affine complex hyperplane in each
elementary-symmetric chart that meets it. A holomorphic curve staying in one such chart therefore
has a single analytic scalar equation for its intersections with the divisor. If the curve meets
the complement of the divisor on a connected parameter domain, the identity theorem makes every
intersection isolated. In particular, a compact subset of that domain contains only finitely many
intersections, and each has finite positive order of vanishing.

This is the chart-level finiteness and positivity statement behind the basepoint multiplicity of
a holomorphic disk. The chart condition is local: a disk whose image is not contained in one chart
must be covered by charts before its global intersection number can be defined.

The geometric convention follows Ozsváth--Szabó, *Holomorphic disks and topological invariants
for closed three-manifolds*, §2.
-/

public section

open Filter Set
open scoped Manifold Topology

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] [T2Space α] [ChartedSpace ℂ α] {n : ℕ}
variable {f : ℂ → Sym α n} {U K : Set ℂ} {s : Sym α n}

/-- A fixed symmetric chart gives an analytic scalar equation for the basepoint divisor
along a curve. If the curve meets and leaves the divisor in `U`, the equation has a
zero and a nonzero value there. This specializes
`exists_continuousLinearMap_ne_zero_mem_iff_symChartAt`. -/
theorem exists_analyticOnNhd_basepointDivisor_equation_in_chart (z : α)
    (hchart : ∀ t ∈ U, f t ∈ (symChartAt (K := ℂ) s).source)
    (ha : AnalyticOnNhd ℂ (fun t => symChartAt (K := ℂ) s (f t)) U)
    (houtside : ∃ t ∈ U, f t ∉ Sym.basepointDivisor z)
    (w : ℂ) (hwU : w ∈ U) (hwD : f w ∈ Sym.basepointDivisor z) :
    ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (b : ℂ) (g : ℂ → ℂ),
      ℓ ≠ 0 ∧ g = (fun t => ℓ (symChartAt (K := ℂ) s (f t)) - b) ∧
      AnalyticOnNhd ℂ g U ∧
      (∀ t ∈ U, (f t ∈ Sym.basepointDivisor z ↔ g t = 0)) ∧
      ∃ t₀ ∈ U, g t₀ ≠ 0 := by
  obtain ⟨ℓ, b, hℓne, hiff⟩ :=
    exists_continuousLinearMap_ne_zero_mem_iff_symChartAt (K := ℂ) z s
      ⟨f w, hchart w hwU, hwD⟩
  let g : ℂ → ℂ := fun t => ℓ (symChartAt (K := ℂ) s (f t)) - b
  have hg : AnalyticOnNhd ℂ g U := by
    intro t ht
    exact ((ℓ.analyticAt _).comp (ha t ht)).sub analyticAt_const
  have hzero : ∀ t ∈ U, (f t ∈ Sym.basepointDivisor z ↔ g t = 0) := by
    intro t ht
    simpa only [g, sub_eq_zero] using hiff (f t) (hchart t ht)
  obtain ⟨t₀, ht₀U, ht₀D⟩ := houtside
  have hgt₀ : g t₀ ≠ 0 := by
    intro hzero₀
    exact ht₀D ((hzero t₀ ht₀U).2 hzero₀)
  exact ⟨ℓ, b, g, hℓne, rfl, hg, hzero, t₀, ht₀U, hgt₀⟩

/-- On a connected parameter domain, a holomorphic curve whose image lies in one symmetric
chart either lies in the basepoint divisor everywhere or meets it at only finitely many points
of each compact subset. This states the latter case, witnessed by one point outside the divisor.
The chart-coordinate map is required to be analytic on a neighborhood of every point of `U`.
-/
theorem finite_basepointDivisor_intersections_in_chart (z : α)
    (hU : IsPreconnected U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hchart : ∀ w ∈ U, f w ∈ (symChartAt (K := ℂ) s).source)
    (ha : AnalyticOnNhd ℂ (fun w => symChartAt (K := ℂ) s (f w)) U)
    (houtside : ∃ w ∈ U, f w ∉ Sym.basepointDivisor z) :
    (K ∩ f ⁻¹' Sym.basepointDivisor z).Finite := by
  by_cases hhit : ∃ w ∈ U, f w ∈ Sym.basepointDivisor z
  · obtain ⟨w, hwU, hwD⟩ := hhit
    obtain ⟨ℓ, b, g, _, _, hg, hzero, t₀, ht₀U, hgt₀⟩ :=
      exists_analyticOnNhd_basepointDivisor_equation_in_chart z hchart ha houtside w hwU hwD
    have hfinite : {t ∈ K | g t = 0}.Finite :=
      finite_setOf_mem_and_eq_zero_of_isCompact hg hU ht₀U hgt₀ hK hKU
    have heq : K ∩ f ⁻¹' Sym.basepointDivisor z = {t ∈ K | g t = 0} := by
      ext t
      by_cases htK : t ∈ K
      · simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, htK, true_and]
        exact hzero t (hKU htK)
      · simp [htK]
    rw [heq]
    exact hfinite
  · have hempty : K ∩ f ⁻¹' Sym.basepointDivisor z = ∅ := by
      ext t
      constructor
      · rintro ⟨htK, htD⟩
        exact (hhit ⟨t, hKU htK, htD⟩).elim
      · simp
    rw [hempty]
    exact finite_empty

/-- If an analytic curve stays in one symmetric chart over a connected domain and is not
contained in the basepoint divisor, each intersection has a finite, positive order of vanishing.
The equation characterizes divisor membership throughout the domain.
In particular, the infinite-order case of `basepointDivisor_intersection_order` cannot occur
under these hypotheses. -/
theorem basepointDivisor_intersection_order_ne_top_in_chart (z : α)
    (hU : IsPreconnected U)
    (hchart : ∀ t ∈ U, f t ∈ (symChartAt (K := ℂ) s).source)
    (ha : AnalyticOnNhd ℂ (fun t => symChartAt (K := ℂ) s (f t)) U)
    (houtside : ∃ t ∈ U, f t ∉ Sym.basepointDivisor z)
    (w : ℂ) (hwU : w ∈ U)
    (hwD : f w ∈ Sym.basepointDivisor z) :
    ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (b : ℂ) (g : ℂ → ℂ),
      ℓ ≠ 0 ∧ g = (fun t => ℓ (symChartAt (K := ℂ) s (f t)) - b) ∧
      AnalyticAt ℂ g w ∧ g w = 0 ∧
      (∀ t ∈ U, (f t ∈ Sym.basepointDivisor z ↔ g t = 0)) ∧
      analyticOrderAt g w ≠ 0 ∧ analyticOrderAt g w ≠ ⊤ := by
  obtain ⟨ℓ, b, g, hℓne, hgformula, hg, hzero, t₀, ht₀U, hgt₀⟩ :=
    exists_analyticOnNhd_basepointDivisor_equation_in_chart z hchart ha houtside w hwU hwD
  have hgw : g w = 0 := (hzero w hwU).1 hwD
  have horder₀ : analyticOrderAt g t₀ ≠ ⊤ := by
    rw [(hg t₀ ht₀U).analyticOrderAt_eq_zero.mpr hgt₀]
    exact ENat.zero_ne_top
  have hfinite : analyticOrderAt g w ≠ ⊤ :=
    hg.analyticOrderAt_ne_top_of_isPreconnected hU ht₀U hwU horder₀
  have hpositive : analyticOrderAt g w ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hg w hwU, hgw⟩
  exact ⟨ℓ, b, g, hℓne, hgformula, hg w hwU, hgw, hzero, hpositive, hfinite⟩

end TauCeti

end
