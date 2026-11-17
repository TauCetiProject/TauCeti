/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.Calculus.ContinuousMap.Local
public import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem

/-!
# Smooth parameter dependence for autonomous ODEs

A locally smooth parameterized autonomous field on Banach spaces admits a smooth family of
solutions near a parameter where the field vanishes locally in the state variable. The implicit
function theorem is applied to the Picard residual in the space of continuous paths. Its path
derivative at the constant base solution is the identity.

Only paths staying in the open smoothness domain are used. Local superposition in the uniform
norm therefore suffices: no globally smooth extension or smooth bump function is needed.

## Main results

* `ODE.exists_contDiffOn_picard_solution`: a `C^(n+1)` family of solutions on an open parameter
  neighbourhood, for `n` finite or infinite, for a `C^(n+1)` field on an open neighbourhood of the
  base parameter and state. Each path stays in that domain and satisfies the Picard equation,
  the ODE at interior times, and its right-hand version at the initial endpoint.
* `ODE.exists_contDiffAt_picard_solution`: the finite-order germ version.
* `TauCeti.ODE.exists_lipschitzOnWith_eventually_path_mem`: a Lipschitz set around the base state
  that contains all nearby paths of a family continuous in the parameter.

## References

* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press, 1969, Chapter X.
-/

public section

open Filter Set Topology
open scoped ContDiff

noncomputable section

universe u

namespace ODE

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The parameter and path assembled as a continuous path in the product. -/
private def picardInput : E × C(Icc (0 : ℝ) 1, F) →L[ℝ] C(Icc (0 : ℝ) 1, E × F) :=
  (((ContinuousLinearMap.inl ℝ E F).compLeftContinuous ℝ _).comp
    (ContinuousLinearMap.const ℝ _)).coprod
      ((ContinuousLinearMap.inr ℝ E F).compLeftContinuous ℝ _)

@[simp]
private theorem picardInput_apply (p : E × C(Icc (0 : ℝ) 1, F)) :
    picardInput p = (ContinuousMap.const _ p.1).prodMk p.2 := by
  ext t <;> simp [picardInput]

/-- The parameter-path pairs staying in the field domain form an open set. -/
private theorem isOpen_picardDomain {s : Set (E × F)} (hs : IsOpen s) :
    IsOpen {p : E × C(Icc (0 : ℝ) 1, F) | ∀ t, (p.1, p.2 t) ∈ s} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hnear := (picardInput (E := E) (F := F)).continuous.continuousAt.eventually
    (ContinuousMap.eventually_mapsTo isCompact_univ hs (fun t _ ↦ by simpa using hp t))
  filter_upwards [hnear] with q hq t
  simpa using hq (mem_univ t)

/-- The locally defined Picard residual, totalized by `ContinuousMap.mkD`. -/
private def picardResidual (f : E × F → F) (x₀ : F)
    (p : E × C(Icc (0 : ℝ) 1, F)) : C(Icc (0 : ℝ) 1, F) :=
  p.2 - ContinuousMap.const _ x₀ - ContinuousMap.unitIntervalIntegral
    (ContinuousMap.mkD (fun t ↦ f (picardInput p t)) 0)

private theorem picardResidual_eq_zero_iff (f : E × F → F) {s : Set (E × F)}
    (hf : ContinuousOn f s) (x₀ : F) (p : E) (q : C(Icc (0 : ℝ) 1, F))
    (hp : ∀ t, (p, q t) ∈ s) :
    picardResidual f x₀ (p, q) = 0 ↔ ∀ t : Icc (0 : ℝ) 1,
      q t = x₀ + ∫ r in (0 : ℝ)..t, f (p, q (projIcc 0 1 zero_le_one r)) := by
  have hcomp : ContinuousMap.mkD (fun t ↦ f (picardInput (p, q) t)) 0 =
      ⟨fun t ↦ f (p, q t), hf.comp_continuous (by fun_prop) hp⟩ := by
    simp only [picardInput_apply, ContinuousMap.prod_eval, ContinuousMap.const_apply]
    exact ContinuousMap.mkD_of_continuous (hf.comp_continuous (by fun_prop) hp)
  rw [picardResidual, hcomp]
  simp [ContinuousMap.ext_iff, sub_sub, sub_eq_zero]

/-- The residual is smooth at every parameter-path pair staying in the smoothness domain. -/
private theorem contDiffAt_picardResidual (n : ℕ∞) (f : E × F → F) {s : Set (E × F)}
    (hs : IsOpen s) (hf : ContDiffOn ℝ (n : ℕ∞ω) f s) (x₀ : F)
    (p : E × C(Icc (0 : ℝ) 1, F)) (hp : ∀ t, (p.1, p.2 t) ∈ s) :
    ContDiffAt ℝ (n : ℕ∞ω) (picardResidual f x₀) p := by
  have hcomp := (ContinuousMap.contDiffAt_mkD_comp n hs hf (by simpa using hp) 0).comp p
    (picardInput (E := E) (F := F)).contDiff.contDiffAt
  have hI : ContDiff ℝ (n : ℕ∞ω)
      (ContinuousMap.unitIntervalIntegral : C(Icc (0 : ℝ) 1, F) → C(Icc (0 : ℝ) 1, F)) :=
    ContinuousLinearMap.contDiff _
  exact (contDiffAt_snd.sub contDiffAt_const).sub (hI.comp_contDiffAt p hcomp)

/-- Local vanishing makes the path derivative of the residual the identity. -/
private theorem hasStrictFDerivAt_picardResidual_path (f : E × F → F) (p₀ : E) (x₀ : F)
    (hzero : ∀ᶠ y in 𝓝 x₀, f (p₀, y) = 0) :
    HasStrictFDerivAt
      (fun q : C(Icc (0 : ℝ) 1, F) ↦ picardResidual f x₀ (p₀, q))
      (ContinuousLinearMap.id ℝ C(Icc (0 : ℝ) 1, F)) (ContinuousMap.const _ x₀) := by
  obtain ⟨U, hUsub, hUopen, hx₀U⟩ := mem_nhds_iff.mp hzero
  have heq : (fun q : C(Icc (0 : ℝ) 1, F) ↦ q - ContinuousMap.const _ x₀) =ᶠ[
      𝓝 (ContinuousMap.const _ x₀)]
      (fun q ↦ picardResidual f x₀ (p₀, q)) := by
    filter_upwards [ContinuousMap.eventually_mapsTo isCompact_univ hUopen
      (fun _ _ ↦ hx₀U)] with q hq
    have hcomp : ContinuousMap.mkD (fun t ↦ f (picardInput (p₀, q) t)) 0 = 0 := by
      have hzero_comp : (fun t ↦ f (picardInput (p₀, q) t)) =
          (0 : Icc (0 : ℝ) 1 → F) := by
        funext t
        simpa using hUsub (hq (mem_univ t))
      rw [hzero_comp, ← ContinuousMap.coe_zero, ContinuousMap.mkD_eq_self]
    rw [picardResidual, hcomp, map_zero, sub_zero]
  exact (hasStrictFDerivAt_sub_const (ContinuousMap.const _ x₀)).congr_of_eventuallyEq heq

/-- Local vanishing makes the full residual derivative invertible in the path direction. -/
private theorem isInvertible_fderiv_picardResidual_path (f : E × F → F) (p₀ : E) (x₀ : F)
    (hR : DifferentiableAt ℝ (picardResidual f x₀) (p₀, ContinuousMap.const _ x₀))
    (hzero : ∀ᶠ y in 𝓝 x₀, f (p₀, y) = 0) :
    (fderiv ℝ (picardResidual f x₀) (p₀, ContinuousMap.const _ x₀) ∘L
      ContinuousLinearMap.inr ℝ E C(Icc (0 : ℝ) 1, F)).IsInvertible := by
  have hpartial := hasStrictFDerivAt_picardResidual_path f p₀ x₀ hzero
  have heq := (hR.hasFDerivAt.comp (ContinuousMap.const _ x₀)
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) p₀ (ContinuousMap.const _ x₀))).unique
      hpartial.hasFDerivAt
  rw [heq]
  exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩

omit [NormedSpace ℝ E] in
/-- The Picard equation gives the ODE at interior times and from the right at zero. -/
private theorem picard_solution_derivatives [CompleteSpace F] (f : E × F → F)
    {s : Set (E × F)} (hf : ContinuousOn f s) (x₀ : F) (p : E)
    (q : C(Icc (0 : ℝ) 1, F)) (hpath : ∀ t, (p, q t) ∈ s)
    (hpicard : ∀ t : Icc (0 : ℝ) 1,
      q t = x₀ + ∫ r in (0 : ℝ)..t, f (p, q (projIcc 0 1 zero_le_one r))) :
    (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun r ↦ q (projIcc 0 1 zero_le_one r))
      (f (p, q (projIcc 0 1 zero_le_one t))) t) ∧
    ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt (fun r ↦ q (projIcc 0 1 zero_le_one r))
      (f (p, q (projIcc 0 1 zero_le_one t))) (Ici t) t := by
  -- Constant extension beyond [0,1] supplies a continuous integrand; equality with the
  -- path is used only within the interval.
  have hcont : Continuous (fun r : ℝ ↦ f (p, q (projIcc 0 1 zero_le_one r))) :=
    hf.comp_continuous (by fun_prop) (fun r ↦ hpath _)
  have heq : EqOn (fun r ↦ q (projIcc 0 1 zero_le_one r))
      (fun r ↦ x₀ + ∫ v in (0 : ℝ)..r, f (p, q (projIcc 0 1 zero_le_one v)))
      (Icc 0 1) := fun r hr ↦ by
    simp only [projIcc_of_mem zero_le_one hr]
    exact hpicard ⟨r, hr⟩
  have hderiv (t : ℝ) : HasDerivAt
      (fun r ↦ x₀ + ∫ v in (0 : ℝ)..r, f (p, q (projIcc 0 1 zero_le_one v)))
      (f (p, q (projIcc 0 1 zero_le_one t))) t :=
    (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add x₀
  exact ⟨fun t ht ↦ (hderiv t).congr_of_eventuallyEq
    (heq.eventuallyEq_of_mem (Icc_mem_nhds ht.1 ht.2)),
    fun t ht ↦ (hderiv t).hasDerivWithinAt.congr_of_eventuallyEq
      ((heq.mono (Icc_subset_Icc_left ht.1)).eventuallyEq_of_mem (Icc_mem_nhdsGE ht.2))
      (heq ⟨ht.1, ht.2.le⟩)⟩

/-- A field that is `C^(n+1)` on an open neighbourhood of a parameter and state, and locally zero
in the state at that parameter, admits a `C^(n+1)` parameter family of solutions on `[0,1]`.
The paths stay in the smoothness domain. The equation holds at interior times and from the right
at zero.
Both parameter and state spaces may be arbitrary Banach spaces. -/
theorem exists_contDiffOn_picard_solution [CompleteSpace E] [CompleteSpace F]
    {n : ℕ∞} (f : E × F → F) (p₀ : E) (x₀ : F) {s : Set (E × F)}
    (hs : IsOpen s) (hbase : (p₀, x₀) ∈ s) (hf : ContDiffOn ℝ (n + 1) f s)
    (hzero : ∀ᶠ y in 𝓝 x₀, f (p₀, y) = 0) :
    ∃ (γ : E → C(Icc (0 : ℝ) 1, F)) (U : Set E),
      IsOpen U ∧ p₀ ∈ U ∧ ContDiffOn ℝ (n + 1) γ U ∧
      γ p₀ = ContinuousMap.const _ x₀ ∧
      ∀ p ∈ U,
        (∀ t : Icc (0 : ℝ) 1, (p, γ p t) ∈ s) ∧
        (∀ t : Icc (0 : ℝ) 1, γ p t = x₀ + ∫ r in (0 : ℝ)..t,
          f (p, γ p (projIcc 0 1 zero_le_one r))) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt
          (fun r ↦ γ p (projIcc 0 1 zero_le_one r))
          (f (p, γ p (projIcc 0 1 zero_le_one t))) t) ∧
        ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt
          (fun r ↦ γ p (projIcc 0 1 zero_le_one r))
          (f (p, γ p (projIcc 0 1 zero_le_one t))) (Ici t) t := by
  let R := picardResidual f x₀
  let u : E × C(Icc (0 : ℝ) 1, F) := (p₀, ContinuousMap.const _ x₀)
  let S := {p : E × C(Icc (0 : ℝ) 1, F) | ∀ t, (p.1, p.2 t) ∈ s}
  have hS : IsOpen S := isOpen_picardDomain hs
  have hu : u ∈ S := fun _ ↦ hbase
  have hRglobal : ContDiffOn ℝ (n + 1) R S := fun p hp ↦
    (contDiffAt_picardResidual (n + 1) f hs (by exact_mod_cast hf) x₀ p hp).contDiffWithinAt
  have hR : ContDiffAt ℝ (n + 1) R u := hRglobal.contDiffAt (hS.mem_nhds hu)
  have hn : (n : ℕ∞ω) + 1 ≠ 0 := by simp
  have hinvertible := isInvertible_fderiv_picardResidual_path f p₀ x₀
    (hR.differentiableAt hn) hzero
  -- The implicit solution is smooth on one open neighbourhood, even at infinite regularity.
  -- Shrink it so the residual vanishes and all paths remain in the original field domain.
  let γ : E → C(Icc (0 : ℝ) 1, F) := hR.implicitFunction hn hinvertible
  have hRbase : R u = 0 := by
    apply (picardResidual_eq_zero_iff f hf.continuousOn x₀ p₀
      (ContinuousMap.const _ x₀) (fun _ ↦ hbase)).2
    intro t
    simp [hzero.self_of_nhds]
  have hγeq : ∀ᶠ p in 𝓝 p₀, R (p, γ p) = 0 := by
    filter_upwards [hR.eventually_apply_implicitFunction hn hinvertible] with p hp
    rw [hp, hRbase]
  obtain ⟨U, hU, hp₀U, hγU⟩ :=
    ContDiffOn.exists_isOpen_contDiffOn_implicitFunction hRglobal hS hu hn hinvertible
  have hγat : ContDiffAt ℝ (n + 1) γ p₀ := hγU.contDiffAt (hU.mem_nhds hp₀U)
  have hγbase : γ p₀ = ContinuousMap.const _ x₀ :=
    hR.implicitFunction_apply_self hn hinvertible
  have hpaths : ∀ᶠ p in 𝓝 p₀, (p, γ p) ∈ S := by
    have hcont := (continuousAt_id.prodMk hγat.continuousAt)
    exact hcont.eventually (hS.mem_nhds (by simpa only [hγbase, u, id_eq] using hu))
  obtain ⟨V, hVsub, hV, hp₀V⟩ := mem_nhds_iff.mp (hγeq.and hpaths)
  refine ⟨γ, U ∩ V, hU.inter hV, ⟨hp₀U, hp₀V⟩,
    hγU.mono inter_subset_left, hγbase, ?_⟩
  intro p hp
  have hpath := (hVsub hp.2).2
  have hpicard := (picardResidual_eq_zero_iff f hf.continuousOn x₀ p (γ p) hpath).mp
    (hVsub hp.2).1
  exact ⟨hpath, hpicard,
    picard_solution_derivatives f hf.continuousOn x₀ p (γ p) hpath hpicard⟩

/-- A field that is `C^(n+1)` at the base parameter and state of Banach spaces, and locally zero
in the state at that parameter, admits a `C^(n+1)` germ of a family of solutions on `[0,1]`. -/
theorem exists_contDiffAt_picard_solution [CompleteSpace E] [CompleteSpace F]
    (n : ℕ) (f : E × F → F) (p₀ : E) (x₀ : F)
    (hf : ContDiffAt ℝ (n + 1) f (p₀, x₀))
    (hzero : ∀ᶠ y in 𝓝 x₀, f (p₀, y) = 0) :
    ∃ γ : E → C(Icc (0 : ℝ) 1, F),
      ContDiffAt ℝ (n + 1) γ p₀ ∧ γ p₀ = ContinuousMap.const _ x₀ ∧
      ∀ᶠ p in 𝓝 p₀,
        (∀ t : Icc (0 : ℝ) 1, γ p t = x₀ + ∫ r in (0 : ℝ)..t,
          f (p, γ p (projIcc 0 1 zero_le_one r))) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt
          (fun r ↦ γ p (projIcc 0 1 zero_le_one r))
          (f (p, γ p (projIcc 0 1 zero_le_one t))) t) ∧
        ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt
          (fun r ↦ γ p (projIcc 0 1 zero_le_one r))
          (f (p, γ p (projIcc 0 1 zero_le_one t))) (Ici t) t := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVs, hV, hbase⟩ := mem_nhds_iff.mp hs
  obtain ⟨γ, U, hU, hp₀U, hγU, hγbase, hprop⟩ :=
    exists_contDiffOn_picard_solution (n := n) f p₀ x₀ hV hbase
      (by exact_mod_cast hfs.mono hVs) hzero
  refine ⟨γ, (by exact_mod_cast hγU.contDiffAt (hU.mem_nhds hp₀U)), hγbase, ?_⟩
  filter_upwards [hU.mem_nhds hp₀U] with p hp
  exact (hprop p hp).2

end ODE

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- For a field that is `C^1` at `(p₀, x₀)` and a family of paths in `[0, 1]` that is continuous at
`p₀` with constant value `x₀` there, there are a Lipschitz set `S` around `x₀` and a neighbourhood
`P` of `p₀` such that `F (p, ·)` is Lipschitz on `S` for `p ∈ P`, and nearby paths stay in `S`. -/
theorem ODE.exists_lipschitzOnWith_eventually_path_mem
    {F : E × V → V} {p₀ : E} {x₀ : V} (hF : ContDiffAt ℝ 1 F (p₀, x₀))
    {γ : E → C(Icc (0 : ℝ) 1, V)} (hγ : ContinuousAt γ p₀)
    (hγ₀ : γ p₀ = ContinuousMap.const _ x₀) :
    ∃ (K : NNReal) (S : Set V) (P : Set E), S ∈ 𝓝 x₀ ∧ P ∈ 𝓝 p₀ ∧
      (∀ p ∈ P, LipschitzOnWith K (fun y => F (p, y)) S) ∧
      ∀ᶠ p in 𝓝 p₀, ∀ t : Icc (0 : ℝ) 1, γ p t ∈ S := by
  obtain ⟨K, W, hW, hFlip⟩ := hF.exists_lipschitzOnWith
  rw [nhds_prod_eq] at hW
  obtain ⟨P, hP, S, hS, hPS⟩ := Filter.mem_prod_iff.mp hW
  have hfixed (p : E) (hp : p ∈ P) : LipschitzOnWith K (fun y => F (p, y)) S := by
    intro y hy z hz
    have h := hFlip (x := (p, y)) (y := (p, z)) (hPS ⟨hp, hy⟩) (hPS ⟨hp, hz⟩)
    simpa only [Prod.edist_eq, edist_self, zero_max] using h
  obtain ⟨U, hUS, hUopen, hUcenter⟩ := mem_nhds_iff.mp hS
  refine ⟨K, S, P, hS, hP, hfixed, ?_⟩
  filter_upwards [hγ.eventually
    (ContinuousMap.eventually_mapsTo isCompact_univ hUopen fun t _ ↦ by
      simpa [hγ₀] using hUcenter)] with p hp t
  exact hUS (hp (Set.mem_univ t))

end TauCeti
