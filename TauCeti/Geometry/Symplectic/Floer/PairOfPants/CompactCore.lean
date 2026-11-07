/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Curvature.CompactSupport
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature

/-!
# Curvature control for independent perturbations on the compact core

The canonical pair-of-pants datum is zero on its core and equals the prescribed Hamiltonians
on its cylindrical tails. Adding an independently chosen Hamiltonian one-form supported in the
interior of the core preserves those tails. Its curvature adds to the canonical curvature
without mixed Poisson-bracket terms, since the two one-forms have disjoint domain supports.

For a jointly `C¹` family of such core perturbations, the integrated curvature is bounded
uniformly on compact parameter and target windows. The bound is the existing sum of the three
end-Hamiltonian bounds plus one finite core allowance. It holds over the entire punctured
surface, independently of truncation, and along arbitrary maps whose core images lie in the
target window. This permits localized coefficient variations while retaining an energy
allowance uniform over a compact family. The target here is a symplectic vector space, as in
the localized Hamiltonian-variation construction.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  for localized Hamiltonian variations and curvature in the inhomogeneous equation.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, for perturbation
  data fixed on cylindrical ends.
-/

public section

open Function MeasureTheory Set
open TauCeti.ThricePuncturedSphere

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Independent `C¹` core variations preserve a uniform integrated curvature bound for the
pair of pants. The open set `U` lies in the zero region of the canonical datum and contains the
common compact support `D` of both variation components. Only the images of `D`, not of the
whole punctured surface, must lie in the compact target window `Q`. -/
theorem exists_lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_add_le
    (ω : SymplecticForm V) {H : Puncture → ℝ → V → ℝ}
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {δs δt : P → ℝ × ℝ → V → ℝ}
    (hδs : ContDiff ℝ 1 (fun q : (P × (ℝ × ℝ)) × V ↦ δs q.1.1 q.1.2 q.2))
    (hδt : ContDiff ℝ 1 (fun q : (P × (ℝ × ℝ)) × V ↦ δt q.1.1 q.1.2 q.2))
    {A : Set P} {D U : Set (ℝ × ℝ)} {Q : Set V}
    (hA : IsCompact A) (hD : IsCompact D) (hQ : IsCompact Q) (hU : IsOpen U) (hDU : D ⊆ U)
    (hcore : ∀ z ∈ U, ∀ q : Puncture,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ 1)
    (hs : ∀ p ∈ A, ∀ z ∉ D, δs p z = 0) (ht : ∀ p ∈ A, ∀ z ∉ D, δt p z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ A, ∀ u : ℝ × ℝ → V, (∀ z ∈ D, u z ∈ Q) →
      ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1 + δs p z x)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I +
          δt p z x) z (u z)‖ₑ ≤ ENNReal.ofReal ((∑ q, B q) + C) := by
  obtain ⟨C, hC, hbound⟩ :=
    ω.exists_lintegral_enorm_hamiltonianCurvature_le_of_isCompact hδs hδt hA hD hQ hs ht
  refine ⟨C, hC, fun p hp u hu ↦ ?_⟩
  have hzero (v : ℂ) (z : ℝ × ℝ) (hz : z ∈ U) :
      (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v) = 0 := by
    funext x
    simp [pairOfPantsPerturbation_eq_zero_of_forall_le (hcore z hz) x]
  have heq (z : ℝ × ℝ) := ω.hamiltonianCurvature_add_of_eq_zero_on hD.isClosed hU hDU
    (hzero 1) (hzero Complex.I) (hs p hp) (ht p hp) z (u z)
  calc
    _ ≤ (∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ) + ∫⁻ z, ‖ω.hamiltonianCurvature (δs p) (δt p) z (u z)‖ₑ := by
      -- Split over the measurable core support: the map need not be measurable, so
      -- additivity for arbitrary sums of densities is not available.
      rw [← lintegral_add_compl _ hD.measurableSet, add_comm]
      apply add_le_add
      · refine (setLIntegral_mono' hD.measurableSet.compl fun z hz ↦ ?_).trans
          (setLIntegral_le_lintegral _ _)
        rw [heq, ω.hamiltonianCurvature_eq_zero_of_notMem hD.isClosed (hs p hp) (ht p hp) hz,
          add_zero]
      · refine (setLIntegral_mono' hD.measurableSet fun z hz ↦ ?_).trans
          (setLIntegral_le_lintegral _ _)
        rw [heq, ω.hamiltonianCurvature_congr_of_eventuallyEq
          (Filter.eventually_of_mem (hU.mem_nhds (hDU hz)) (hzero 1))
          (Filter.eventually_of_mem (hU.mem_nhds (hDU hz)) (hzero Complex.I))]
        simp [hamiltonianCurvature_def]
    _ ≤ (∑ q, ENNReal.ofReal (B q)) + ENNReal.ofReal C :=
      add_le_add (ω.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le hH hHs hB u)
        (hbound p hp u hu)
    _ = ENNReal.ofReal ((∑ q, B q) + C) := by
      have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 0)
      rw [ENNReal.ofReal_add (Finset.sum_nonneg fun q _ ↦ hB₀ q) hC,
        ENNReal.ofReal_sum_of_nonneg fun q _ ↦ hB₀ q]

end TauCeti.SymplecticForm
