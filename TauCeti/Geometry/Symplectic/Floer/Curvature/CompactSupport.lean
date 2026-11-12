/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
public import TauCeti.Geometry.Manifold.ContMDiff.Prod
public import TauCeti.Geometry.Symplectic.Floer.Manifold

/-!
# Uniform curvature bounds for compactly supported perturbation families

A jointly `C¹` family of Hamiltonian one-forms with a common compact domain support has a
uniform integrated curvature bound on compact parameter and target windows. The bound holds
along arbitrary maps into the target window, without a measurability assumption on those maps.
It controls localized perturbations of Floer data without multiplying a bound by the length
of a cylindrical end.

The curvature includes both domain derivatives and the Poisson bracket. Joint `C¹` regularity
controls all three terms; a bound on the Hamiltonians alone would not suffice.

The results are stated for a finite-dimensional manifold target `M` with a nondegenerate two-form
`ω`, such as a closed symplectic manifold, and a parameter manifold `N`. There the Poisson bracket
is continuous jointly in the parameter and the target point because the Hamiltonian vector fields
of a jointly `C¹` family are jointly continuous
(`TauCeti.SmoothTwoForm.IsNondegenerate.continuous_poissonBracket_uncurry`). The statements for a
symplectic vector space target and a normed parameter space are their specializations to the
constant form `TauCeti.SymplecticForm.constSmooth`.

## Main results

* `SmoothTwoForm.IsNondegenerate.continuous_hamiltonianCurvature_family`,
  `SymplecticForm.continuous_hamiltonianCurvature_family`: the curvature of a jointly `C¹`
  family is jointly continuous in the parameter, the domain point and the target point.
* `SmoothTwoForm.IsNondegenerate.exists_lintegral_enorm_hamiltonianCurvature_le_of_isCompact`,
  `SymplecticForm.exists_lintegral_enorm_hamiltonianCurvature_le_of_isCompact`: the
  uniform integrated curvature bound for a family with a common compact domain support.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  for the curvature of Hamiltonian perturbations and its role in energy estimates.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {ω : SmoothTwoForm I M}

/-- For a nondegenerate two-form on a finite-dimensional manifold, the curvature of a jointly
`C¹` family of Hamiltonian one-forms is continuous jointly in the parameter, the domain point and
the target point. -/
theorem IsNondegenerate.continuous_hamiltonianCurvature_family (hω : ω.IsNondegenerate)
    {Ks Kt : N → ℝ × ℝ → M → ℝ}
    (hKs : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 1
      (fun q : (N × (ℝ × ℝ)) × M ↦ Ks q.1.1 q.1.2 q.2))
    (hKt : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 1
      (fun q : (N × (ℝ × ℝ)) × M ↦ Kt q.1.1 q.1.2 q.2)) :
    Continuous (fun q : (N × (ℝ × ℝ)) × M ↦
      ω.hamiltonianCurvature (Ks q.1.1) (Kt q.1.1) q.1.2 q.2) := by
  have hD (K : N → ℝ × ℝ → M → ℝ)
      (hK : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 1
        (fun q : (N × (ℝ × ℝ)) × M ↦ K q.1.1 q.1.2 q.2)) (v : ℝ × ℝ) :
      Continuous (fun q : (N × (ℝ × ℝ)) × M ↦ fderiv ℝ (fun z ↦ K q.1.1 z q.2) q.1.2 v) := by
    -- Regard the target point as a further parameter, so that the domain is the vector-space
    -- factor whose derivative is taken.
    have hK' : ContMDiff ((J.prod I).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ) 1
        (uncurry fun (p : N × M) (z : ℝ × ℝ) ↦ K p.1 z p.2) :=
      hK.comp ((contMDiff_fst.fst.prodMk contMDiff_snd).prodMk contMDiff_fst.snd)
    have hd : Continuous (fun p : (N × M) × (ℝ × ℝ) ↦ fderiv ℝ (fun z ↦ K p.1.1 z p.1.2) p.2) :=
      (show ContMDiff _ _ 0 _ from fun z ↦ (hK' z).fderiv_right (by norm_num)).continuous
    exact (hd.comp ((continuous_fst.fst.prodMk continuous_snd).prodMk
      continuous_fst.snd)).clm_apply continuous_const
  exact (((hD Kt hKt _).sub (hD Ks hKs _)).sub
    (hω.continuous_poissonBracket_uncurry (f := fun p : N × (ℝ × ℝ) ↦ Ks p.1 p.2)
      (g := fun p : N × (ℝ × ℝ) ↦ Kt p.1 p.2) hKs hKt)).congr fun _ ↦
    (hamiltonianCurvature_def _ _ _ _ _).symm

/-- For a nondegenerate two-form on a finite-dimensional manifold, a jointly `C¹` family
supported in a common compact domain set has a finite integrated curvature bound, uniform over
compact parameter and target windows and over all maps into the target window. In particular the
bound is independent of any truncation of the domain. -/
theorem IsNondegenerate.exists_lintegral_enorm_hamiltonianCurvature_le_of_isCompact
    (hω : ω.IsNondegenerate) {Ks Kt : N → ℝ × ℝ → M → ℝ}
    (hKs : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 1
      (fun q : (N × (ℝ × ℝ)) × M ↦ Ks q.1.1 q.1.2 q.2))
    (hKt : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 1
      (fun q : (N × (ℝ × ℝ)) × M ↦ Kt q.1.1 q.1.2 q.2))
    {A : Set N} {D : Set (ℝ × ℝ)} {Q : Set M}
    (hA : IsCompact A) (hD : IsCompact D) (hQ : IsCompact Q)
    (hs : ∀ p ∈ A, ∀ z ∉ D, Ks p z = 0) (ht : ∀ p ∈ A, ∀ z ∉ D, Kt p z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ A, ∀ u : ℝ × ℝ → M, (∀ z ∈ D, u z ∈ Q) →
      ∫⁻ z, ‖ω.hamiltonianCurvature (Ks p) (Kt p) z (u z)‖ₑ ≤ ENNReal.ofReal C := by
  obtain ⟨B, hB⟩ := ((hA.prod hD).prod hQ).exists_bound_of_continuousOn
    (hω.continuous_hamiltonianCurvature_family hKs hKt).continuousOn
  refine ⟨max B 0 * volume.real D, mul_nonneg (le_max_right _ _) (measureReal_nonneg),
    fun p hp u hu ↦ ?_⟩
  calc
    ∫⁻ z, ‖ω.hamiltonianCurvature (Ks p) (Kt p) z (u z)‖ₑ
      = ∫⁻ z in D, ‖ω.hamiltonianCurvature (Ks p) (Kt p) z (u z)‖ₑ := by
        symm
        apply setLIntegral_eq_of_support_subset
        intro z hz
        by_contra hzD
        have h0 := ω.hamiltonianCurvature_eq_zero_of_notMem hD.isClosed
          (hs p hp) (ht p hp) hzD (u z)
        simp [h0] at hz
    _ ≤ ∫⁻ _ in D, ENNReal.ofReal (max B 0) := by
        apply setLIntegral_mono' hD.measurableSet
        intro z hz
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal ((hB ((p, z), u z) ⟨⟨hp, hz⟩, hu z hz⟩).trans
          (le_max_left _ _))
    _ = ENNReal.ofReal (max B 0 * volume.real D) := by
        rw [setLIntegral_const, ENNReal.ofReal_mul (le_max_right _ _),
          ofReal_measureReal hD.measure_lt_top.ne]

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The curvature of a jointly `C¹` Hamiltonian family is continuous jointly in the external
parameter, domain point and target point. -/
theorem continuous_hamiltonianCurvature_family (ω : SymplecticForm V)
    {Ks Kt : P → ℝ × ℝ → V → ℝ}
    (hKs : ContDiff ℝ 1 (fun q : (P × (ℝ × ℝ)) × V ↦ Ks q.1.1 q.1.2 q.2))
    (hKt : ContDiff ℝ 1 (fun q : (P × (ℝ × ℝ)) × V ↦ Kt q.1.1 q.1.2 q.2)) :
    Continuous (fun q : (P × (ℝ × ℝ)) × V ↦
      ω.hamiltonianCurvature (Ks q.1.1) (Kt q.1.1) q.1.2 q.2) := by
  simpa using (isNondegenerate_constSmooth ω).continuous_hamiltonianCurvature_family
    (contMDiff_prod_prod_modelWithCornersSelf_iff.2 hKs.contMDiff)
      (contMDiff_prod_prod_modelWithCornersSelf_iff.2 hKt.contMDiff)

/-- A jointly `C¹` family supported in a common compact domain set has a finite integrated
curvature bound, uniform over compact parameter and target windows and over all maps into the
target window. In particular the bound is independent of any truncation of the domain. -/
theorem exists_lintegral_enorm_hamiltonianCurvature_le_of_isCompact
    (ω : SymplecticForm V) {Ks Kt : P → ℝ × ℝ → V → ℝ}
    (hKs : ContDiff ℝ 1 (fun q : (P × (ℝ × ℝ)) × V ↦ Ks q.1.1 q.1.2 q.2))
    (hKt : ContDiff ℝ 1 (fun q : (P × (ℝ × ℝ)) × V ↦ Kt q.1.1 q.1.2 q.2))
    {A : Set P} {D : Set (ℝ × ℝ)} {Q : Set V}
    (hA : IsCompact A) (hD : IsCompact D) (hQ : IsCompact Q)
    (hs : ∀ p ∈ A, ∀ z ∉ D, Ks p z = 0) (ht : ∀ p ∈ A, ∀ z ∉ D, Kt p z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ A, ∀ u : ℝ × ℝ → V, (∀ z ∈ D, u z ∈ Q) →
      ∫⁻ z, ‖ω.hamiltonianCurvature (Ks p) (Kt p) z (u z)‖ₑ ≤ ENNReal.ofReal C := by
  simpa using
    (isNondegenerate_constSmooth ω).exists_lintegral_enorm_hamiltonianCurvature_le_of_isCompact
      (contMDiff_prod_prod_modelWithCornersSelf_iff.2 hKs.contMDiff)
      (contMDiff_prod_prod_modelWithCornersSelf_iff.2 hKt.contMDiff) hA hD hQ hs ht

end TauCeti.SymplecticForm
