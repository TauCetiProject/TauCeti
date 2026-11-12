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
of a jointly `C^(n+1)` family is jointly `C^n` in the parameter and the target point
(`TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_poissonBracket_uncurry`). The statements for a
symplectic vector space target and a normed parameter space are their specializations to the
constant form `TauCeti.SymplecticForm.constSmooth`.

## Main results

* `SmoothTwoForm.IsNondegenerate.contMDiff_hamiltonianCurvature_family`: the curvature of a
  jointly `C^(n+1)` family is jointly `C^n` in the parameter, the domain point and the target
  point.
* `SymplecticForm.continuous_hamiltonianCurvature_family`: the curvature of a jointly `C¹`
  family with a symplectic vector space target is jointly continuous.
* `SmoothTwoForm.IsNondegenerate.exists_lintegral_enorm_hamiltonianCurvature_le_of_isCompact`,
  `SymplecticForm.exists_lintegral_enorm_hamiltonianCurvature_le_of_isCompact`: the
  uniform integrated curvature bound for a family with a common compact domain support.
* `SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_add_of_eq_zero_on`: a perturbation supported
  inside the zero region of a one-form adds its integrated curvature exactly.

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
`C^(n+1)` family of Hamiltonian one-forms is jointly `C^n` in the parameter, the domain point and
the target point, for `n ≤ ∞`. -/
theorem IsNondegenerate.contMDiff_hamiltonianCurvature_family (hω : ω.IsNondegenerate)
    {n : WithTop ℕ∞} (hn : n ≤ (⊤ : ℕ∞)) {Ks Kt : N → ℝ × ℝ → M → ℝ}
    (hKs : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) (n + 1)
      (fun q : (N × (ℝ × ℝ)) × M ↦ Ks q.1.1 q.1.2 q.2))
    (hKt : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) (n + 1)
      (fun q : (N × (ℝ × ℝ)) × M ↦ Kt q.1.1 q.1.2 q.2)) :
    ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) n (fun q : (N × (ℝ × ℝ)) × M ↦
      ω.hamiltonianCurvature (Ks q.1.1) (Kt q.1.1) q.1.2 q.2) := by
  have hD (K : N → ℝ × ℝ → M → ℝ)
      (hK : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) (n + 1)
        (fun q : (N × (ℝ × ℝ)) × M ↦ K q.1.1 q.1.2 q.2)) (v : ℝ × ℝ) :
      ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) n
        (fun q : (N × (ℝ × ℝ)) × M ↦ fderiv ℝ (fun z ↦ K q.1.1 z q.2) q.1.2 v) := by
    -- Regard the target point as a further parameter, so that the domain is the vector-space
    -- factor whose derivative is taken.
    have hK' : ContMDiff ((J.prod I).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ) (n + 1)
        (uncurry fun (p : N × M) (z : ℝ × ℝ) ↦ K p.1 z p.2) :=
      hK.comp ((contMDiff_fst.fst.prodMk contMDiff_snd).prodMk contMDiff_fst.snd)
    have hd : ContMDiff ((J.prod I).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ × ℝ →L[ℝ] ℝ) n
        (fun p : (N × M) × (ℝ × ℝ) ↦ fderiv ℝ (fun z ↦ K p.1.1 z p.1.2) p.2) :=
      fun z ↦ hK'.contMDiffAt.fderiv_right le_rfl
    exact (hd.comp ((contMDiff_fst.fst.prodMk contMDiff_snd).prodMk
      contMDiff_fst.snd)).clm_apply contMDiff_const
  exact (((hD Kt hKt _).sub (hD Ks hKs _)).sub
    (hω.contMDiff_poissonBracket_uncurry hn (f := fun p : N × (ℝ × ℝ) ↦ Ks p.1 p.2)
      (g := fun p : N × (ℝ × ℝ) ↦ Kt p.1 p.2) hKs hKt)).congr fun _ ↦
    hamiltonianCurvature_def _ _ _ _ _

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
    (hω.contMDiff_hamiltonianCurvature_family (n := 0) (by simp) (by simpa using hKs)
      (by simpa using hKt)).continuous.continuousOn
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

omit [FiniteDimensional ℝ E] in
/-- Adding a perturbation `δ` supported in a closed set `D`, inside an open set `U` on which the
one-form `K` vanishes, adds the integrated curvatures exactly: along every map `u`, the integral
of `|R_(K + δ)(u)|` is the integral of `|R_K(u)|` plus the integral of `|R_δ(u)|`. -/
theorem lintegral_enorm_hamiltonianCurvature_add_of_eq_zero_on (ω : SmoothTwoForm I M)
    {Ks Kt δs δt : ℝ × ℝ → M → ℝ} {D U : Set (ℝ × ℝ)}
    (hD : IsClosed D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hKs : ∀ z ∈ U, Ks z = 0) (hKt : ∀ z ∈ U, Kt z = 0)
    (hδs : ∀ z ∉ D, δs z = 0) (hδt : ∀ z ∉ D, δt z = 0) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature (fun w y ↦ Ks w y + δs w y) (fun w y ↦ Kt w y + δt w y) z
        (u z)‖ₑ =
      (∫⁻ z, ‖ω.hamiltonianCurvature Ks Kt z (u z)‖ₑ) +
        ∫⁻ z, ‖ω.hamiltonianCurvature δs δt z (u z)‖ₑ := by
  have hK {z : ℝ × ℝ} (hz : z ∈ D) (x : M) : ω.hamiltonianCurvature Ks Kt z x = 0 :=
    ω.hamiltonianCurvature_eq_zero_of_eventuallyEq_zero
      (eventually_of_mem (hU.mem_nhds (hDU hz)) hKs)
      (eventually_of_mem (hU.mem_nhds (hDU hz)) hKt) x
  have hδ {z : ℝ × ℝ} (hz : z ∉ D) (x : M) : ω.hamiltonianCurvature δs δt z x = 0 :=
    ω.hamiltonianCurvature_eq_zero_of_notMem hD hδs hδt hz x
  have heq (z : ℝ × ℝ) :=
    ω.hamiltonianCurvature_add_of_eq_zero_on hD hU hDU hKs hKt hδs hδt z (u z)
  -- Split each integral over the measurable support `D`: the map need not be measurable, so
  -- additivity for arbitrary sums of densities is not available. On `D` only `δ` contributes, and
  -- off `D` only `K`.
  rw [← lintegral_add_compl _ hD.measurableSet,
    ← lintegral_add_compl (fun z ↦ ‖ω.hamiltonianCurvature Ks Kt z (u z)‖ₑ) hD.measurableSet,
    ← lintegral_add_compl (fun z ↦ ‖ω.hamiltonianCurvature δs δt z (u z)‖ₑ) hD.measurableSet,
    setLIntegral_congr_fun hD.measurableSet (f := fun z ↦ ‖ω.hamiltonianCurvature Ks Kt z (u z)‖ₑ)
      (g := 0) fun z hz ↦ by simp [hK hz],
    setLIntegral_congr_fun hD.measurableSet.compl
      (f := fun z ↦ ‖ω.hamiltonianCurvature δs δt z (u z)‖ₑ) (g := 0) fun z hz ↦ by simp [hδ hz],
    setLIntegral_congr_fun hD.measurableSet fun z hz ↦ by rw [heq, hK hz, zero_add],
    setLIntegral_congr_fun hD.measurableSet.compl fun z hz ↦ by rw [heq, hδ hz, add_zero]]
  simp [add_comm]

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
  have hKs' := contMDiff_prod_prod_modelWithCornersSelf_iff.2
    (contMDiff_prod_modelWithCornersSelf_iff.2 hKs.contMDiff)
  have hKt' := contMDiff_prod_prod_modelWithCornersSelf_iff.2
    (contMDiff_prod_modelWithCornersSelf_iff.2 hKt.contMDiff)
  simpa using ((isNondegenerate_constSmooth ω).contMDiff_hamiltonianCurvature_family (n := 0)
    (by simp) (by simpa using hKs') (by simpa using hKt')).continuous

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
      (contMDiff_prod_prod_modelWithCornersSelf_iff.2
        (contMDiff_prod_modelWithCornersSelf_iff.2 hKs.contMDiff))
      (contMDiff_prod_prod_modelWithCornersSelf_iff.2
        (contMDiff_prod_modelWithCornersSelf_iff.2 hKt.contMDiff)) hA hD hQ hs ht

end TauCeti.SymplecticForm
