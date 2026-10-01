/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
public import TauCeti.Analysis.Calculus.ContinuousMap

/-!
# Smooth parameter dependence for autonomous ODEs

This file develops the Banach-space implicit-equation argument that makes a local solution of a
smooth parameterized autonomous ODE depend smoothly on its parameter.

## Main results

* `ODE.exists_contDiffAt_picard_solution_of_contDiff`: for a globally `C^(n+1)` field on complete
  spaces, with `n` finite or infinite, a `C^(n+1)` family of local solutions of the Picard
  integral equation, satisfying the ODE at interior times and from the right at the initial
  endpoint.
* `ODE.exists_contDiffAt_picard_solution`: the same for a germ of a `C^(n+1)` field with `n`
  finite, in finite dimension.
-/

public section

open scoped ContDiff

noncomputable section

universe u

namespace ODE

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Pair a parameter with every value of a continuous path, as a continuous linear map. -/
private noncomputable def parameterizedPath :
    E × C(K, F) →L[ℝ] C(K, E × F) := by
  let L : E × C(K, F) →ₗ[ℝ] C(K, E × F) :=
    { toFun := fun p ↦ ⟨fun t ↦ (p.1, p.2 t), continuous_const.prodMk p.2.continuous⟩
      map_add' := fun _ _ ↦ by ext t <;> rfl
      map_smul' := fun _ _ ↦ by ext t <;> rfl }
  exact LinearMap.mkContinuous L 1 fun p ↦ by
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg p)).2
    intro t
    rw [Prod.norm_def, Prod.norm_def]
    exact max_le_max le_rfl (ContinuousMap.norm_coe_le_norm p.2 t)

@[simp]
private theorem parameterizedPath_apply (p : E × C(K, F)) (t : K) :
    parameterizedPath p t = (p.1, p.2 t) := by
  rw [parameterizedPath]
  rfl

/-- The Picard integral equation, written as a zero of a map between Banach spaces of continuous
paths. -/
private noncomputable def picardResidual (f : C(E × F, F)) (x₀ : F) :
    E × C(Set.Icc (0 : ℝ) 1, F) → C(Set.Icc (0 : ℝ) 1, F) := fun p ↦
  p.2 - ContinuousMap.const _ x₀ -
    ContinuousMap.unitIntervalIntegral (f.comp (parameterizedPath p))

/-- The Picard residual is the path minus its initial value and integrated vector field. -/
@[simp]
private theorem picardResidual_apply (f : C(E × F, F)) (x₀ : F)
    (p : E × C(Set.Icc (0 : ℝ) 1, F)) :
    picardResidual f x₀ p = p.2 - ContinuousMap.const _ x₀ -
      ContinuousMap.unitIntervalIntegral (f.comp (parameterizedPath p)) := by
  rfl

/-- **A path's Picard residual vanishes exactly when it satisfies the Picard integral equation.**
Mathlib states the same equivalence for its own path space as `ODE.FunSpace.isFixedPt_next_iff`. -/
private theorem picardResidual_eq_zero_iff (gc : C(E × F, F)) (x₀ : F) (p : E)
    (q : C(Set.Icc (0 : ℝ) 1, F)) :
    picardResidual gc x₀ (p, q) = 0 ↔ ∀ t : Set.Icc (0 : ℝ) 1,
      q t = x₀ + ∫ s in (0 : ℝ)..t, gc (p, q (Set.projIcc 0 1 zero_le_one s)) := by
  simp [ContinuousMap.ext_iff, sub_sub, sub_eq_zero]

/-- A vector field of class `Cⁿ` gives a Picard residual of class `Cⁿ`. -/
private theorem contDiff_picardResidual (n : ℕ∞) (f : C(E × F, F))
    (hf : ContDiff ℝ n f) (x₀ : F) :
    ContDiff ℝ n (picardResidual f x₀) := by
  have hcomp : ContDiff ℝ n
      (fun p : E × C(Set.Icc (0 : ℝ) 1, F) ↦ f.comp (parameterizedPath p)) :=
    (ContinuousMap.contDiff_postcomp n f hf).comp
      (parameterizedPath (E := E) (F := F) (K := Set.Icc (0 : ℝ) 1)).contDiff
  exact (contDiff_snd.sub contDiff_const).sub
    ((ContinuousMap.unitIntervalIntegral (E := F)).contDiff.fun_comp hcomp)

/-- At a parameter for which the vector field vanishes locally in the state variable, the partial
derivative of the Picard residual in the path variable is the identity. -/
private theorem hasStrictFDerivAt_picardResidual_path
    (f : C(E × F, F)) (p₀ : E) (x₀ : F)
    (hf : ∀ᶠ y in nhds x₀, f (p₀, y) = 0) :
    HasStrictFDerivAt
      (fun γ : C(Set.Icc (0 : ℝ) 1, F) ↦ picardResidual f x₀ (p₀, γ))
      (ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, F))
      (ContinuousMap.const _ x₀) := by
  obtain ⟨U, hUzero, hUopen, hU⟩ := mem_nhds_iff.mp hf
  have heq :
      (fun γ : C(Set.Icc (0 : ℝ) 1, F) ↦
        γ - ContinuousMap.const _ x₀) =ᶠ[nhds (ContinuousMap.const _ x₀)]
      (fun γ ↦ picardResidual f x₀ (p₀, γ)) := by
    filter_upwards [ContinuousMap.eventually_mapsTo isCompact_univ hUopen fun _ _ ↦ hU] with γ hγ
    have hcomp : f.comp (parameterizedPath (p₀, γ)) = 0 := by
      ext t
      simpa using hUzero (hγ (Set.mem_univ t))
    simp only [picardResidual_apply, hcomp, map_zero, sub_zero]
  exact (hasStrictFDerivAt_sub_const (ContinuousMap.const _ x₀)).congr_of_eventuallyEq heq

/-- A path on `[0, 1]` satisfying the integral equation `q t = x₀ + ∫₀ᵗ v` for a continuous `v`
has derivative `v t` at every interior time, and from the right at every `t ∈ [0, 1)`. -/
private theorem hasDerivAt_of_forall_eq_integral [CompleteSpace F] {v : ℝ → F}
    (hv : Continuous v) {x₀ : F} {q : C(Set.Icc (0 : ℝ) 1, F)}
    (hq : ∀ t : Set.Icc (0 : ℝ) 1, q t = x₀ + ∫ s in (0 : ℝ)..t, v s) :
    (∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun s ↦ q (Set.projIcc 0 1 zero_le_one s)) (v t) t) ∧
    ∀ t ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun s ↦ q (Set.projIcc 0 1 zero_le_one s)) (v t) (Set.Ici t) t := by
  have heq : Set.EqOn (fun s ↦ q (Set.projIcc 0 1 zero_le_one s))
      (fun s ↦ x₀ + ∫ u in (0 : ℝ)..s, v u) (Set.Icc 0 1) := fun s hs ↦ by
    simpa only [Set.projIcc_of_mem zero_le_one hs] using hq ⟨s, hs⟩
  have hderiv (t : ℝ) : HasDerivAt (fun s ↦ x₀ + ∫ u in (0 : ℝ)..s, v u) (v t) t :=
    (hv.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add x₀
  refine ⟨fun t ht ↦ (hderiv t).congr_of_eventuallyEq
      (heq.eventuallyEq_of_mem (Icc_mem_nhds ht.1 ht.2)),
    fun t ht ↦ (hderiv t).hasDerivWithinAt.congr_of_eventuallyEq
      ((heq.mono (Set.Icc_subset_Icc_left ht.1)).eventuallyEq_of_mem (Icc_mem_nhdsGE ht.2))
      (heq ⟨ht.1, ht.2.le⟩)⟩

/-- **The path-derivative of the Picard residual at the constant base solution is invertible.**
For a continuously differentiable field vanishing near `x₀` at the base parameter `p₀`, the
restriction of
`fderiv ℝ (picardResidual gc x₀)` to the path direction is invertible at `(p₀, const x₀)`. -/
private theorem isInvertible_fderiv_picardResidual_comp_inr
    (gc : C(E × F, F)) (hg : ContDiff ℝ 1 gc) (p₀ : E) (x₀ : F)
    (hgzero : ∀ᶠ y in nhds x₀, gc (p₀, y) = 0) :
    (fderiv ℝ (picardResidual gc x₀)
          (p₀, (ContinuousMap.const _ x₀ : C(Set.Icc (0 : ℝ) 1, F))) ∘L
        ContinuousLinearMap.inr ℝ E C(Set.Icc (0 : ℝ) 1, F)).IsInvertible := by
  have hR : ContDiffAt ℝ 1 (picardResidual gc x₀)
      (p₀, (ContinuousMap.const _ x₀ : C(Set.Icc (0 : ℝ) 1, F))) :=
    (contDiff_picardResidual 1 gc (by exact_mod_cast hg) x₀).contDiffAt
  have hpartial := hasStrictFDerivAt_picardResidual_path gc p₀ x₀ hgzero
  have hdiff := hR.differentiableAt (by norm_num)
  have hpartialEq :=
    (hdiff.hasFDerivAt.comp (ContinuousMap.const (Set.Icc (0 : ℝ) 1) x₀)
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) p₀
        (ContinuousMap.const (Set.Icc (0 : ℝ) 1) x₀))).unique hpartial.hasFDerivAt
  rw [hpartialEq]
  exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩

/-- A globally `C^(n+1)` parameterized autonomous vector field on complete spaces, which vanishes
near the base state at the base parameter, admits a `C^(n+1)` family of local solutions through
that state, for `n` finite or infinite. Each nearby path satisfies the Picard integral equation,
the corresponding ODE at every interior time, and its right-hand version at the initial
endpoint. -/
theorem exists_contDiffAt_picard_solution_of_contDiff
    [CompleteSpace E] [CompleteSpace F]
    {n : ℕ∞} (f : E × F → F) (p₀ : E) (x₀ : F)
    (hf : ContDiff ℝ (n + 1) f)
    (hzero : ∀ᶠ y in nhds x₀, f (p₀, y) = 0) :
    ∃ γ : E → C(Set.Icc (0 : ℝ) 1, F),
      ContDiffAt ℝ (n + 1) γ p₀ ∧
      γ p₀ = ContinuousMap.const _ x₀ ∧
      ∀ᶠ p in nhds p₀,
        (∀ t : Set.Icc (0 : ℝ) 1,
          γ p t = x₀ + ∫ s in (0 : ℝ)..t,
            f (p, γ p (Set.projIcc 0 1 zero_le_one s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivAt (fun s ↦ γ p (Set.projIcc 0 1 zero_le_one s))
            (f (p, γ p (Set.projIcc 0 1 zero_le_one t))) t) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) 1,
          HasDerivWithinAt (fun s ↦ γ p (Set.projIcc 0 1 zero_le_one s))
            (f (p, γ p (Set.projIcc 0 1 zero_le_one t))) (Set.Ici t) t := by
  let gc : C(E × F, F) := ⟨f, hf.continuous⟩
  let R := picardResidual gc x₀
  let basePath : C(Set.Icc (0 : ℝ) 1, F) := ContinuousMap.const _ x₀
  let u : E × C(Set.Icc (0 : ℝ) 1, F) := (p₀, basePath)
  have hgc : ContDiff ℝ (n + 1) gc := hf
  have hR : ContDiffAt ℝ (n + 1) R u := by
    exact_mod_cast (contDiff_picardResidual (n + 1) gc (by exact_mod_cast hgc) x₀).contDiffAt
  have hn : (n : ℕ∞ω) + 1 ≠ 0 := by simp
  -- At the constant base solution the path derivative of the residual is the identity, so the
  -- implicit function theorem produces a smooth parameter-to-path germ.
  have hinvertible :
      (fderiv ℝ R u ∘L
        ContinuousLinearMap.inr ℝ E C(Set.Icc (0 : ℝ) 1, F)).IsInvertible :=
    isInvertible_fderiv_picardResidual_comp_inr gc (hgc.of_le le_add_self) p₀ x₀ hzero
  let γ : E → C(Set.Icc (0 : ℝ) 1, F) := hR.implicitFunction hn hinvertible
  have hRbase : R u = 0 := by
    have hcomp : gc.comp (parameterizedPath u) = 0 := by
      ext t
      rw [ContinuousMap.comp_apply, parameterizedPath_apply]
      exact hzero.self_of_nhds
    simp only [R, picardResidual_apply, u, basePath, hcomp, map_zero, sub_self]
  have hγeq : ∀ᶠ p in nhds p₀, R (p, γ p) = 0 := by
    filter_upwards [hR.eventually_apply_implicitFunction hn hinvertible] with p hp
    rw [hp, hRbase]
  refine ⟨γ, hR.contDiffAt_implicitFunction hn hinvertible,
    hR.implicitFunction_apply_self hn hinvertible, ?_⟩
  filter_upwards [hγeq] with p hp
  have hpicard := (picardResidual_eq_zero_iff gc x₀ p (γ p)).mp hp
  exact ⟨hpicard, hasDerivAt_of_forall_eq_integral (by fun_prop) hpicard⟩

/-- A parameterized autonomous vector field which is `C^(n+1)` at the base point of a
finite-dimensional space and vanishes near the base state at the base parameter admits a
`C^(n+1)` family of local solutions through that state. Each nearby path satisfies the Picard
integral equation, the corresponding ODE at every interior time, and its right-hand version at the
initial endpoint. -/
theorem exists_contDiffAt_picard_solution
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (n : ℕ) (f : E × F → F) (p₀ : E) (x₀ : F)
    (hf : ContDiffAt ℝ (n + 1) f (p₀, x₀))
    (hzero : ∀ᶠ y in nhds x₀, f (p₀, y) = 0) :
    ∃ γ : E → C(Set.Icc (0 : ℝ) 1, F),
      ContDiffAt ℝ (n + 1) γ p₀ ∧
      γ p₀ = ContinuousMap.const _ x₀ ∧
      ∀ᶠ p in nhds p₀,
        (∀ t : Set.Icc (0 : ℝ) 1,
          γ p t = x₀ + ∫ s in (0 : ℝ)..t,
            f (p, γ p (Set.projIcc 0 1 zero_le_one s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivAt (fun s ↦ γ p (Set.projIcc 0 1 zero_le_one s))
            (f (p, γ p (Set.projIcc 0 1 zero_le_one t))) t) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) 1,
          HasDerivWithinAt (fun s ↦ γ p (Set.projIcc 0 1 zero_le_one s))
            (f (p, γ p (Set.projIcc 0 1 zero_le_one t))) (Set.Ici t) t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  -- Replace the local vector-field germ by a global smooth representative, which does not change
  -- the ODE near the base point.
  obtain ⟨g, hg, -, hgf⟩ :=
    hf.exists_contDiff_eventuallyEq_of_finiteDimensional (n + 1)
  have hgzero : ∀ᶠ y in nhds x₀, g (p₀, y) = 0 := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hgf, hzero]
      with y hy hyzero
    exact hy.trans hyzero
  obtain ⟨γ, hγsmooth, hγbase, hprop⟩ :=
    exists_contDiffAt_picard_solution_of_contDiff (n := n) g p₀ x₀ (by exact_mod_cast hg) hgzero
  refine ⟨γ, by exact_mod_cast hγsmooth, hγbase, ?_⟩
  -- Restrict to parameters whose whole Picard path remains where the representative agrees with
  -- the original field; then transfer the integral equation and its derivative consequences.
  obtain ⟨U, hUgf, hUopen, hU⟩ := mem_nhds_iff.mp hgf
  have hpathsNear : ∀ᶠ p in nhds p₀, Set.MapsTo (parameterizedPath (p, γ p)) Set.univ U :=
    (parameterizedPath.continuous.continuousAt.comp
      (continuousAt_id.prodMk hγsmooth.continuousAt)).eventually
      (ContinuousMap.eventually_mapsTo isCompact_univ hUopen fun t _ ↦ by
        simpa [hγbase] using hU)
  filter_upwards [hprop, hpathsNear] with p hp hpnear
  obtain ⟨hpicard, hderiv, hright⟩ := hp
  have hpoint (t : Set.Icc (0 : ℝ) 1) : g (p, γ p t) = f (p, γ p t) :=
    hUgf (by simpa using hpnear (Set.mem_univ t))
  refine ⟨fun t ↦ (hpicard t).trans (congrArg (x₀ + ·) ?_), ?_, ?_⟩
  · exact intervalIntegral.integral_congr fun s _ ↦ hpoint (Set.projIcc 0 1 zero_le_one s)
  · exact fun t ht ↦ (hderiv t ht).congr_deriv (hpoint (Set.projIcc 0 1 zero_le_one t))
  · exact fun t ht ↦ (hright t ht).congr_deriv (hpoint (Set.projIcc 0 1 zero_le_one t))

end ODE
