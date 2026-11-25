/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic
import TauCeti.AlgebraicGeometry.WeilDivisor.Order
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Divisor

/-!
# Meromorphic functions with one prescribed pole

On a compact connected Riemann surface, a second global section of `𝒪(n[p])` gives a finite
holomorphic map to the Riemann sphere with exactly one pole, at `p`. Its degree equals the pole
multiplicity and is at most `n`.
-/

public noncomputable section

open OnePoint
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X]

/-- A finite holomorphic map to the sphere whose poles are bounded by `n[p]` has exactly one
pole, at `p`. Its order there is minus its degree, and its degree is at most `n`. -/
theorem FiniteHolomorphicMap.singlePole_of_neg_le_meromorphicOrderAt
    (F : FiniteHolomorphicMap X (OnePoint ℂ)) (p : X) (n : ℕ)
    (hF : ∀ x, ((-WeilDivisor.coeff (n • WeilDivisor.ofPoint p) x : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun y ↦ affineChart (F y)) x) :
    degree F ≤ n ∧ F ⁻¹' {∞} = {p} ∧
      meromorphicOrderAt (fun y ↦ affineChart (F y)) p = ((-(degree F : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  have hD := nsmul_nonneg (WeilDivisor.ofPoint_nonneg p) n
  have hdiv := F.divisorPullback_ofPoint_infty_le_of_neg_le_meromorphicOrderAt hD hF
  have hpoint (x : X) (hx : F x = ∞) : x = p := by
    by_contra hxp
    have h := WeilDivisor.le_iff.mp hdiv x
    rw [coeff_divisorPullback, hx, WeilDivisor.coeff_ofPoint_self, mul_one,
      WeilDivisor.coeff_nsmul, WeilDivisor.coeff_ofPoint_of_ne hxp, mul_zero] at h
    exact (localMultiplicity_pos F x).not_ge (by exact_mod_cast h)
  obtain ⟨x, hx⟩ := F.surjective ∞
  have hp : F p = ∞ := by simpa only [hpoint x hx] using hx
  have hfib : F ⁻¹' {∞} = {p} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨hpoint y, fun h ↦ h.symm ▸ hp⟩
  have hfin : (F.finite_fiber ∞).toFinset = {p} := by
    ext y
    simp only [Set.Finite.mem_toFinset, hfib, Set.mem_singleton_iff, Finset.mem_singleton]
  have hdeg : degree F = localMultiplicity F p := by
    rw [degree_eq_fiber_sum F ∞, hfin, Finset.sum_singleton]
  have horder : meromorphicOrderAt (fun y ↦ affineChart (F y)) p =
      ((-(degree F : ℤ) : ℤ) : WithTop ℤ) := by
    rw [hdeg, F.meromorphicOrderAt_affineChart_comp_of_eq_infty hp]
  have hbound := F.degree_le_degree_of_neg_le_meromorphicOrderAt hD hF
  simp only [map_nsmul, WeilDivisor.degree_ofPoint, nsmul_eq_mul, mul_one] at hbound
  exact ⟨by exact_mod_cast hbound, hfib, horder⟩

variable [ConnectedSpace X]

/-- A second section of `𝒪(n[p])` gives a finite holomorphic map of degree at most `n`, with
its entire fibre over infinity concentrated at `p` and pole order equal to its degree. -/
theorem exists_finiteHolomorphicMap_singlePole_of_one_lt_finrank_divisorSections
    (p : X) (n : ℕ) (h : 1 < Module.finrank ℂ (divisorSections (n • WeilDivisor.ofPoint p) ⊤)) :
    ∃ F : FiniteHolomorphicMap X (OnePoint ℂ), degree F ≤ n ∧ F ⁻¹' {∞} = {p} ∧
      meromorphicOrderAt (fun y ↦ affineChart (F y)) p = ((-(degree F : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨F, hF⟩ := exists_finiteHolomorphicMap_of_one_lt_finrank_divisorSections _ h
  exact ⟨F, F.singlePole_of_neg_le_meromorphicOrderAt p n hF⟩

end TauCeti.RiemannSurface
