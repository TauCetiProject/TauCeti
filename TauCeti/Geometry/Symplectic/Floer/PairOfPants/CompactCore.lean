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
allowance uniform over a compact family.

The bound is stated for a finite-dimensional manifold target with a nondegenerate two-form, such
as a closed symplectic manifold, where the curvature of the core family is continuous because the
Hamiltonian vector fields of a jointly `C¹` family are jointly continuous. The statement for a
symplectic vector space target is its specialization to the constant form
`SymplecticForm.constSmooth`.

## Main results

* `SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_add_le`: for a
  single perturbation supported in the core, on any manifold target, the curvature allowance of
  the sum is at most `B₀ + B₁ + B_∞` plus the curvature allowance of the core perturbation.
* `exists_lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_add_le`, in the namespace
  `SmoothTwoForm.IsNondegenerate` for a manifold target and in `SymplecticForm` for a vector-space
  target: the uniform bound for a compact family of core perturbations.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  for localized Hamiltonian variations and curvature in the inhomogeneous equation.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, for perturbation
  data fixed on cylindrical ends.
-/

public section

open Function MeasureTheory Set
open scoped Manifold
open TauCeti.ThricePuncturedSphere

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I (⊤ : ℕ∞) M]
  {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ} {B : Puncture → ℝ}

/-- Adding a perturbation supported in the core adds its curvature allowance to that of the
pair of pants. The open set `U` lies in the zero region of the canonical datum and contains the
closed support `D` of both components of the perturbation `δ`. Then along every map `u`, the
integral of `|R_(K + δ)(u)|` is at most `B₀ + B₁ + B_∞` plus the integral of `|R_δ(u)|`. -/
theorem lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_add_le
    (ω : SmoothTwoForm I M) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hB : ∀ q t x, |H q t x| ≤ B q) {δs δt : ℝ × ℝ → M → ℝ} {D U : Set (ℝ × ℝ)}
    (hD : IsClosed D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hcore : ∀ z ∈ U, ∀ q : Puncture,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ 1)
    (hs : ∀ z ∉ D, δs z = 0) (ht : ∀ z ∉ D, δt z = 0) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1 + δs z x)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I +
          δt z x) z (u z)‖ₑ ≤
      ENNReal.ofReal (∑ q, B q) + ∫⁻ z, ‖ω.hamiltonianCurvature δs δt z (u z)‖ₑ := by
  have hzero (v : ℂ) (z : ℝ × ℝ) (hz : z ∈ U) :
      (fun x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v) = 0 := by
    funext x
    simp [pairOfPantsPerturbation_eq_zero_of_forall_le (hcore z hz) x]
  have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 (u 0))
  rw [ω.lintegral_enorm_hamiltonianCurvature_add_of_eq_zero_on hD hU hDU (hzero 1)
    (hzero Complex.I) hs ht u, ENNReal.ofReal_sum_of_nonneg fun q _ ↦ hB₀ q]
  exact add_le_add_left
    (ω.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le hH hHs hB u) _

variable [FiniteDimensional ℝ E]
  {E' G' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace G']
  {J : ModelWithCorners ℝ E' G'} [TopologicalSpace N] [ChartedSpace G' N] [IsManifold J 1 N]

/-- Independent `C¹` core variations preserve a uniform integrated curvature bound for the
pair of pants with a finite-dimensional manifold target carrying a nondegenerate two-form. The
open set `U` lies in the zero region of the canonical datum and contains the common compact
support `D` of both variation components. Only the images of `D`, not of the whole punctured
surface, must lie in the compact target window `Q`. -/
theorem IsNondegenerate.exists_lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_add_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hB : ∀ q t x, |H q t x| ≤ B q) {δs δt : N → ℝ × ℝ → M → ℝ}
    (hδs : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 1
      (fun q : (N × (ℝ × ℝ)) × M ↦ δs q.1.1 q.1.2 q.2))
    (hδt : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 1
      (fun q : (N × (ℝ × ℝ)) × M ↦ δt q.1.1 q.1.2 q.2))
    {A : Set N} {D U : Set (ℝ × ℝ)} {Q : Set M}
    (hA : IsCompact A) (hD : IsCompact D) (hQ : IsCompact Q) (hU : IsOpen U) (hDU : D ⊆ U)
    (hcore : ∀ z ∈ U, ∀ q : Puncture,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ 1)
    (hs : ∀ p ∈ A, ∀ z ∉ D, δs p z = 0) (ht : ∀ p ∈ A, ∀ z ∉ D, δt p z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ A, ∀ u : ℝ × ℝ → M, (∀ z ∈ D, u z ∈ Q) →
      ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1 + δs p z x)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I +
          δt p z x) z (u z)‖ₑ ≤ ENNReal.ofReal ((∑ q, B q) + C) := by
  obtain ⟨C, hC, hbound⟩ :=
    hω.exists_lintegral_enorm_hamiltonianCurvature_le_of_isCompact hδs hδt hA hD hQ hs ht
  refine ⟨C, hC, fun p hp u hu ↦ ?_⟩
  rw [ENNReal.ofReal_add (Finset.sum_nonneg fun q _ ↦ (abs_nonneg _).trans (hB q 0 (u 0))) hC]
  exact (ω.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_add_le hH hHs hB
    hD.isClosed hU hDU hcore (hs p hp) (ht p hp) u).trans (add_le_add le_rfl (hbound p hp u hu))

end TauCeti.SmoothTwoForm

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
  simpa only [hamiltonianCurvature_constSmooth] using (isNondegenerate_constSmooth ω)
    |>.exists_lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_add_le hH
      (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hB
      (contMDiff_prod_prod_modelWithCornersSelf_iff.2
        (contMDiff_prod_modelWithCornersSelf_iff.2 hδs.contMDiff))
      (contMDiff_prod_prod_modelWithCornersSelf_iff.2
        (contMDiff_prod_modelWithCornersSelf_iff.2 hδt.contMDiff)) hA hD hQ hU hDU hcore hs ht

end TauCeti.SymplecticForm
