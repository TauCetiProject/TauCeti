/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart.Stokes
import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.SmoothPartition
import TauCeti.Analysis.Calculus.DifferentialForm.Integral

/-!
# Stokes' theorem away from the boundary

Compactly supported exact top forms have zero canonical oriented integral when the primitive
is supported away from the boundary. The manifold may use any model with corners.
Extension by zero reduces a chart-supported form to flat compact Stokes, and an actual finite
smooth partition gives the global result (`TauCeti.integralTopForm_mextDeriv_eq_zero`).

Combining `integralTopForm_mextDeriv_eq_zero_of_disjoint_boundary` with the cylinder homotopy
operator (`TauCeti.homotopyOperator`) in positive degree and local constancy in degree zero yields
homotopy invariance of top-form periods on smooth oriented manifolds possibly with boundary or
corners (`TauCeti.integralTopForm_mpullback_sub_eq_zero_of_disjoint_boundary`,
`TauCeti.integralTopForm_mpullback_eq_of_disjoint_boundary`), for any closed `C¹` form on a `C²`
target manifold (which need not be finite-dimensional, compact, Hausdorff, or boundaryless) and any
`C²` homotopy whose time-varying locus is compactly supported away from `I.boundary M`.
-/

public section

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ}

/-- The canonical integral of a chart-supported exterior derivative vanishes when the form's
support avoids the boundary. This applies to every real model with corners. -/
theorem integralTopForm_mextDeriv_eq_zero_of_tsupport_subset_chart [IsManifold I 2 M]
    (l : Manifold.OrientationLift I M (Fin (n + 1)))
    {φ : RoughForm I M ℝ n} (hφ : IsSmoothForm I 1 φ) (α : M)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ (extChartAt I α).source)
    (hσ : ∀ x ∈ (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ), l.signAt α x = l.signAt α α)
    (hd : Disjoint (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) (I.boundary M)) :
    integralTopForm (Manifold.Orientation.mk l) (TauCeti.mextDeriv φ) = 0 := by
  classical
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  let η := (extChartAt I α).target.indicator (φ.inChartAt α)
  have hω := hφ.contDiff_indicator_inChartAt α hc hs hd
  have hcω := φ.hasCompactSupport_indicator_inChartAt α hc hs
  have hr := Module.Basis.integral_extDeriv_eq_zero b hω hcω
  have he (y : E) : (TauCeti.mextDeriv φ).signedInChartAt b α (fun _ ↦ 1) y =
      extDeriv η y b := by
    by_cases hy : y ∈ (extChartAt I α).target
    · have hderiv := hφ.extDerivWithin_indicator_inChartAt α hc hs
        (extChartAt_target_subset_range α hy)
      have hde : extDerivWithin η (range I) y = extDeriv η y := by
        by_cases ht : y ∈ _root_.tsupport η
        · have hn := mem_interior_iff_mem_nhds.mp
            (φ.tsupport_indicator_inChartAt_subset_interior α hc hs hd ht)
          rw [extDerivWithin, extDeriv,
            fderivWithin_of_mem_nhds (mem_of_superset hn (extChartAt_target_subset_range α))]
        · rw [extDerivWithin, extDeriv, fderiv_of_notMem_tsupport ℝ ht,
            (HasFDerivWithinAt.of_notMem_tsupport ℝ ht).fderivWithin
              (I.uniqueDiffOn y (extChartAt_target_subset_range α hy))]
      rw [indicator_of_mem hy, hde] at hderiv
      rw [RoughForm.signedInChartAt_apply, dite_eq_left hy]
      simp only [Units.val_one, Int.cast_one, one_mul]
      exact (congrArg (fun A ↦ A b) hderiv).symm
    · have hn : y ∉ _root_.tsupport η := φ.notMem_tsupport_indicator_inChartAt α hc hs hy
      rw [RoughForm.signedInChartAt_apply, dite_eq_right hy, extDeriv,
        fderiv_of_notMem_tsupport ℝ hn]
      simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
        zero_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
        smul_zero, Finset.sum_const_zero]
  have hi := hφ.continuous_mextDeriv.integrableTopForm
    (φ.isCompact_tsupport_mextDeriv hc) b
  rw [integralTopForm_eq_chartIntegral l _ hi α (φ.tsupport_mextDeriv_subset.trans hs),
    l.chartIntegral_eq_const_mul_unsigned _ b α (l.signAt α α)
      (fun x hx ↦ hσ x (φ.tsupport_mextDeriv_subset hx))]
  simp_rw [he]
  rw [hr.2, mul_zero]

/-- On any smooth manifold with corners, the actual exterior derivative of a compactly
supported C1 form whose support avoids the boundary has zero canonical oriented integral. -/
theorem integralTopForm_mextDeriv_eq_zero_of_disjoint_boundary [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] (o : Manifold.Orientation I M (Fin (n + 1)))
    {φ : RoughForm I M ℝ n} (hφ : IsSmoothForm I 1 φ) (hc : IsCompact
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ))
    (hd : Disjoint (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) (I.boundary M)) :
    integralTopForm o (TauCeti.mextDeriv φ) = 0 := by
  classical
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  obtain ⟨s, ρ, heq, hp⟩ := φ.exists_finset_smooth_partition_in_charts l hφ hc
  let ψ : M → RoughForm I M ℝ n := fun i x ↦ ρ i x • φ x
  have hψ : ∀ i ∈ s, IsSmoothForm I 1 (ψ i) := fun i hi ↦ (hp i hi).1
  have hcψ : ∀ i ∈ s, IsCompact
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) (ψ i)) := fun i hi ↦ (hp i hi).2.1
  have hm : ∀ i ∈ s, IntegrableTopForm (TauCeti.mextDeriv (ψ i)) := by
    intro i hi
    exact (hψ i hi).continuous_mextDeriv.integrableTopForm
      ((ψ i).isCompact_tsupport_mextDeriv (hcψ i hi)) b
  have hmd : TauCeti.mextDeriv φ = ∑ i ∈ s, TauCeti.mextDeriv (ψ i) := by
    rw [heq]
    exact mextDeriv_sum ψ s hψ
  rw [hmd, integralTopForm_sum _ _ _ hm]
  apply Finset.sum_eq_zero
  intro i hi
  apply integralTopForm_mextDeriv_eq_zero_of_tsupport_subset_chart l (hψ i hi) i (hcψ i hi)
  · simpa only [extChartAt_source] using (hp i hi).2.2.1
  · exact (hp i hi).2.2.2.1
  -- Give the support lemma the fixed model fibre explicitly; inferring this tangent-fibre
  -- identification here exceeds the elaborator's standard heartbeat budget.
  · exact hd.mono_left (_root_.tsupport_smul_subset_right (ρ i)
    (show M → E [⋀^Fin _]→L[ℝ] ℝ from φ))

/-- On a boundaryless smooth manifold, compactly supported exact top forms have zero integral.
Intrinsic boundarylessness suffices, even when the model itself has boundary. -/
theorem integralTopForm_mextDeriv_eq_zero [BoundarylessManifold I M]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (o : Manifold.Orientation I M (Fin (n + 1)))
    {φ : RoughForm I M ℝ n} (hφ : IsSmoothForm I 1 φ) (hc : IsCompact
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ)) :
    integralTopForm o (TauCeti.mextDeriv φ) = 0 :=
  integralTopForm_mextDeriv_eq_zero_of_disjoint_boundary o hφ hc
    (by simp only [ModelWithCorners.Boundaryless.boundary_eq_empty, disjoint_empty])

section Homotopy

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']

/-- **Vanishing of period differences along compactly supported interior homotopies.** Let `(M, o)`
be a Hausdorff `σ`-compact oriented smooth `k`-manifold (possibly with boundary or corners) and
`F : M × [0, 1] → M'` be a `C²` homotopy from `f` to `f'` into a `C²` manifold `M'` (which need not
be finite-dimensional, compact, Hausdorff, or boundaryless) whose time-varying locus has compact
closure disjoint from `I.boundary M`. Then `∫_M (f'^* η - f^* η) = 0` for every closed `C¹`
`k`-form `η` on `M'`. -/
theorem integralTopForm_mpullback_sub_eq_zero_of_disjoint_boundary [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] [IsManifold I' 2 M'] {k : ℕ}
    (o : Manifold.Orientation I M (Fin k))
    {f f' : M → M'} {F : M × Icc (0 : ℝ) 1 → M'} (hF : ContMDiff (I.prod (𝓡∂ 1)) I' 2 F)
    (h₀ : ∀ x, F (x, 0) = f x) (h₁ : ∀ x, F (x, 1) = f' x)
    (hc : IsCompact (closure {x : M | ∃ t, F (x, t) ≠ F (x, 0)}))
    (hd : Disjoint (closure {x : M | ∃ t, F (x, t) ≠ F (x, 0)}) (I.boundary M))
    {η : RoughForm I' M' ℝ k} (hη : IsSmoothForm I' 1 η) (hclosed : mextDeriv η = 0) :
    integralTopForm o (mpullback I I' f' η - mpullback I I' f η) = 0 := by
  cases k with
  | zero =>
    have hηeq : η = RoughForm.ofFunction I' (fun y ↦ η y ![]) :=
      (RoughForm.eq_ofFunction η).trans
        (by congr with y; exact congrArg (η y) (Subsingleton.elim 0 ![]))
    have hfn : ContMDiff I' 𝓘(ℝ) 1 (fun y ↦ η y ![]) := by
      rw [← isSmoothForm_ofFunction_iff, ← hηeq]
      exact hη
    have hlc := (mextDeriv_ofFunction_eq_zero_iff (hfn.mdifferentiable one_ne_zero)).1
      (hηeq ▸ hclosed)
    have hpull : mpullback I I' f' η = mpullback I I' f η := by
      funext x; ext v
      have hxt := hlc.comp_continuous (hF.continuous.comp (Continuous.prodMk_right x))
      have h01 := (congrArg (fun y ↦ η y ![]) (h₁ x)).symm.trans
        ((hxt.apply_eq_of_preconnectedSpace 1 0).trans (congrArg (fun y ↦ η y ![]) (h₀ x)))
      rw [mpullback_apply, mpullback_apply, congrArg (η (f' x)) (Subsingleton.elim _ ![]),
        congrArg (η (f x)) (Subsingleton.elim _ ![]), h01]
    rw [hpull, sub_self, integralTopForm_zero]
  | succ m =>
    have hι (t : Icc (0 : ℝ) 1) : ContMDiff I (I.prod (𝓡∂ 1)) 2 (fun x : M ↦ (x, t)) :=
      (contMDiff_id.prodMk contMDiff_const).of_le le_top
    obtain rfl : F ∘ (fun x ↦ (x, (0 : Icc (0 : ℝ) 1))) = f := funext h₀
    obtain rfl : F ∘ (fun x ↦ (x, (1 : Icc (0 : ℝ) 1))) = f' := funext h₁
    let ψ := mpullback (I.prod (𝓡∂ 1)) I' F η
    have hψ : IsSmoothForm (I.prod (𝓡∂ 1)) 1 ψ := hη.mpullback (by rwa [one_add_one_eq_two])
    have hψc : mextDeriv ψ = 0 := hη.mextDeriv_mpullback_eq_zero hclosed hF
    have : IsManifold I ((1 : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
    have hderiv : mextDeriv (homotopyOperator ψ) =
        mpullback I I' (F ∘ fun x ↦ (x, 1)) η - mpullback I I' (F ∘ fun x ↦ (x, 0)) η := by
      funext x
      rw [Pi.sub_apply, mextDeriv_homotopyOperator hψ hψc x,
        ← congrFun (mpullback_comp ((hι 1).mdifferentiable (by simp))
          (hF.mdifferentiable (by simp)) η) x,
        ← congrFun (mpullback_comp ((hι 0).mdifferentiable (by simp))
          (hF.mdifferentiable (by simp)) η) x]
    have hsupp : (_root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ) (homotopyOperator ψ)) ⊆
        closure {x : M | ∃ t, F (x, t) ≠ F (x, 0)} :=
      closure_mono fun _ hx ↦ not_forall.1 fun hstat ↦
        hx (homotopyOperator_mpullback_apply_eq_zero hstat η)
    rw [← hderiv]
    exact integralTopForm_mextDeriv_eq_zero_of_disjoint_boundary o hψ.homotopyOperator
      (hc.of_isClosed_subset (isClosed_tsupport _) hsupp) (hd.mono_left hsupp)

/-- **Homotopy invariance of top-form periods away from the boundary.** On a compact Hausdorff
oriented smooth `k`-manifold `(M, o)` (possibly with boundary or corners), a `C²` homotopy
`F : M × [0, 1] → M'` into a `C²` manifold `M'` whose time-varying locus has closure disjoint from
`I.boundary M` preserves the period `∫_M f^* η` of every closed `C¹` `k`-form `η` on `M'`. When `M`
is boundaryless (`[BoundarylessManifold I M]`), `I.boundary M = ∅` so the boundary condition holds
automatically. -/
theorem integralTopForm_mpullback_eq_of_disjoint_boundary [IsManifold I ∞ M] [T2Space M]
    [CompactSpace M] [IsManifold I' 2 M'] {k : ℕ}
    (o : Manifold.Orientation I M (Fin k))
    {f f' : M → M'} {F : M × Icc (0 : ℝ) 1 → M'} (hF : ContMDiff (I.prod (𝓡∂ 1)) I' 2 F)
    (h₀ : ∀ x, F (x, 0) = f x) (h₁ : ∀ x, F (x, 1) = f' x)
    (hd : Disjoint (closure {x : M | ∃ t, F (x, t) ≠ F (x, 0)}) (I.boundary M))
    {η : RoughForm I' M' ℝ k} (hη : IsSmoothForm I' 1 η) (hclosed : mextDeriv η = 0) :
    integralTopForm o (mpullback I I' f η) = integralTopForm o (mpullback I I' f' η) := by
  have hι (t : Icc (0 : ℝ) 1) : ContMDiff I (I.prod (𝓡∂ 1)) 1 (fun x : M ↦ (x, t)) :=
    (contMDiff_id.prodMk contMDiff_const).of_le le_top
  have hf : ContMDiff I I' 1 f := by
    rw [← funext h₀]; exact (hF.of_le one_le_two).comp (hι 0)
  have hf' : ContMDiff I I' 1 f' := by
    rw [← funext h₁]; exact (hF.of_le one_le_two).comp (hι 1)
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm)
  have hi₀ : IntegrableTopForm (mpullback I I' f η) :=
    ((hη.of_le zero_le_one).mpullback hf).integrableTopForm (isClosed_tsupport _).isCompact b
  have hi₁ : IntegrableTopForm (mpullback I I' f' η) :=
    ((hη.of_le zero_le_one).mpullback hf').integrableTopForm (isClosed_tsupport _).isCompact b
  have hzero := integralTopForm_mpullback_sub_eq_zero_of_disjoint_boundary o hF h₀ h₁
    isClosed_closure.isCompact hd hη hclosed
  rw [integralTopForm_sub_of_integrable o hi₁ hi₀, sub_eq_zero] at hzero
  exact hzero.symm

end Homotopy

end TauCeti
