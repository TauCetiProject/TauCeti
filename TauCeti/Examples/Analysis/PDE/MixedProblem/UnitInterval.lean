/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MixedProblem
public import TauCeti.Analysis.PDE.Spectrum.Interval
import TauCeti.Analysis.Sobolev.W1p.BoundaryPart.ChangeOfVariables
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import TauCeti.Examples.Analysis.Sobolev.W1p.BoundaryPart.UnitIntervalLeftEndpoint
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Mixed and Neumann problems on the unit interval

On the interval `(0, 1)`, realized as the open subset `TauCeti.PDE.intervalDomain 0 1` of the
Euclidean line, this file solves three weak boundary value problems for `-u''` explicitly. They
are the one-dimensional checks of the mixed problem
(`TauCeti.PDE.existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq`) and of the
Neumann problem (`TauCeti.PDE.exists_forall_energyFormH1_eq_iff`).

* **A mixed problem.** With Dirichlet part `Γ = {0}`, the weak form of `-u'' = 1`, `u(0) = 0`,
  `u'(1) = 0` asks for `u ∈ H¹_Γ(0, 1)` with `∫ u' v' = ∫ v` for every `v ∈ H¹_Γ(0, 1)`. Its
  weak solutions are exactly the functions equal to `x - x² / 2`
  (`mem_w1pVanishingOnSubmodule_and_forall_energyFormH1_eq_iff`), so it has exactly one weak
  solution (`existsUnique_mem_w1pVanishingOnSubmodule_and_forall_energyFormH1_eq`). Nothing is
  imposed at `1`: the Neumann condition `u'(1) = 0` is the natural boundary condition of the
  test space, whose elements need not vanish at `1`.
  Uniqueness is the coercive case of the mixed problem, through the Poincaré–Friedrichs
  inequality `‖v‖ ≤ ‖v'‖` on `H¹_Γ(0, 1)`
  (`TauCeti.Examples.UnitIntervalLeftEndpoint.norm_value_le_norm_gradient`).
* **The Neumann compatibility condition fails.** With `Γ = ∅`, `-u'' = 1` has no weak solution:
  there is no `u ∈ H¹(0, 1)` with `∫ u' v' = ∫ v` for every `v ∈ H¹(0, 1)`
  (`not_exists_forall_energyFormH1_eq_setIntegral`), since `v = 1` gives `0 = 1`. Classically,
  `u'' = -1` forces `u'(1) - u'(0) = -1`, incompatible with `u'(0) = u'(1) = 0`.
* **A mass term restores coercivity.** With `Γ = ∅`, `-u'' + u = 1` has the constant `1` as its
  unique weak solution (`forall_energyFormH1_eq_setIntegral_iff`): the energy form
  `∫ (u' v' + u v)` is the `H¹` inner product, coercive with no Poincaré inequality.

The Sobolev functions on the interval domain are compared with those on the real interval
`(0, 1)` along the isometry `t ↦ t e₀` of `ℝ` onto the Euclidean line
(`TauCeti.W1p.compAffineIsometryEquivL`), where they have continuous representatives and endpoint
values (`TauCeti.W1p.intervalTraceL`).

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §8.4,
  Example 5 (a mixed problem in one dimension), Proposition 9.24 and Problem 47 (the Neumann
  problem and its compatibility condition).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace TauCeti TauCeti.PDE
open scoped InnerProductSpace

namespace TauCeti.Examples.MixedProblemUnitInterval

/-- The isometry `t ↦ t e₀` from the real line onto the Euclidean line. -/
private def lineIso : ℝ ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr.toAffineIsometryEquiv

@[simp] private theorem lineIso_apply_zero (t : ℝ) : lineIso t 0 = t :=
  OrthonormalBasis.singleton_repr _ _

@[simp] private theorem lineIso_symm_apply (x : EuclideanSpace ℝ (Fin 1)) :
    lineIso.symm x = x 0 := by
  rw [AffineIsometryEquiv.symm_apply_eq]
  ext i
  fin_cases i
  simp

private theorem Ioo_eq_preimage :
    ((⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ) =
      lineIso ⁻¹' (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1))) := by
  ext t
  simp

private theorem intervalDomain_eq_preimage :
    (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1))) =
      lineIso.symm ⁻¹' ((⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ) := by
  ext x
  simp

/-- The pullback of a Sobolev function on the interval domain to the real interval `(0, 1)`. -/
private abbrev pull :
    W1p volume (intervalDomain 0 1) 2 →L[ℝ] W1p volume (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) 2 :=
  W1p.compAffineIsometryEquivL lineIso Ioo_eq_preimage

/-- The pushforward of a Sobolev function on `(0, 1)` to the interval domain. -/
private abbrev push :
    W1p volume (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) 2 →L[ℝ] W1p volume (intervalDomain 0 1) 2 :=
  W1p.compAffineIsometryEquivL lineIso.symm intervalDomain_eq_preimage

private theorem pull_push (u : W1p volume (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) 2) :
    pull (push u) = u :=
  W1p.compAffineIsometryEquivL_symm_compAffineIsometryEquivL lineIso.symm _ _ u

/-- The derivative of the pullback is the coordinate of the gradient. -/
private theorem gradient_pull_ae (u : W1p volume (intervalDomain 0 1) 2) :
    W1p.gradient (pull u) =ᵐ[volume.restrict (Ioo 0 1)]
      fun t => W1p.gradient u (lineIso t) 0 := by
  filter_upwards [W1p.gradient_compAffineIsometryEquivL_ae lineIso Ioo_eq_preimage u] with t ht
  -- The linear part of `lineIso` is the linear isometry it is built from.
  rw [ht]
  exact lineIso_symm_apply _

/-- Integrals over the interval domain are integrals over `(0, 1)`. -/
private theorem setIntegral_intervalDomain_eq (F : EuclideanSpace ℝ (Fin 1) → ℝ) :
    ∫ x in intervalDomain 0 1, F x = ∫ t in Ioo 0 1, F (lineIso t) := by
  rw [← setIntegral_intervalDomain]
  simp_rw [← lineIso_symm_apply, AffineIsometryEquiv.apply_symm_apply]

/-- The integral of a Sobolev function over the interval domain is that of its pullback. -/
private theorem setIntegral_value_pull (v : W1p volume (intervalDomain 0 1) 2) :
    ∫ x in intervalDomain 0 1, W1p.value v x = ∫ t in Ioo 0 1, W1p.value (pull v) t := by
  rw [setIntegral_intervalDomain_eq]
  exact integral_congr_ae (W1p.value_compAffineIsometryEquivL_ae lineIso Ioo_eq_preimage v).symm

/-- The Dirichlet form of `-u''` on the interval domain, computed on `(0, 1)`. -/
private theorem energyFormH1_eq_setIntegral_pull (u v : W1p volume (intervalDomain 0 1) 2) :
    energyFormH1 (fun _ => 1) 0 0 u v =
      ∫ t in Ioo 0 1, W1p.gradient (pull v) t * W1p.gradient (pull u) t := by
  rw [energyFormH1_one_zero_zero_apply, setIntegral_intervalDomain_eq]
  refine integral_congr_ae ?_
  filter_upwards [gradient_pull_ae u, gradient_pull_ae v] with t hu hv
  simp [hu, hv, dotProduct]

/-- The boundary part `{0}` corresponds to the endpoint `0` of `(0, 1)`. -/
private theorem preimage_lineIso_zero : lineIso ⁻¹' {0} = {0} := by
  ext t
  simp [← AffineIsometryEquiv.eq_symm_apply]

/-- The pullback of a function vanishing at `0` vanishes at `0`. -/
private theorem pull_mem {v : W1p volume (intervalDomain 0 1) 2}
    (hv : v ∈ w1pVanishingOnSubmodule volume (intervalDomain 0 1) 2 {0}) :
    pull v ∈ w1pVanishingOnSubmodule volume (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) 2 {0} := by
  have h := W1p.compAffineIsometryEquivL_mem_w1pVanishingOnSubmodule lineIso Ioo_eq_preimage hv
  rwa [preimage_lineIso_zero] at h

/-- **Integration by parts against `1 - t` on `(0, 1)`**: `∫ v' (1 - t) = ∫ v - v(0)`. -/
private theorem setIntegral_gradient_mul_one_sub
    (v : W1p volume (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) 2) :
    ∫ t in Ioo 0 1, W1p.gradient v t * (1 - t) =
      (∫ t in Ioo 0 1, W1p.value v t) - (W1p.intervalTraceL zero_lt_one v).1 := by
  have hf : AbsolutelyContinuousOnInterval (fun t : ℝ => 1 - t) 0 1 :=
    (contDiff_const.sub contDiff_id).contDiffOn.absolutelyContinuousOnInterval
  have h := hf.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt (f' := fun _ => -1)
    (W1p.absolutelyContinuousOnInterval_intervalRepresentativeL zero_lt_one v)
    (ae_of_all _ fun t _ => by simpa using (hasDerivAt_id t).const_sub 1)
    (W1p.ae_hasDerivAt_intervalRepresentativeL zero_lt_one v)
  simp only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at h
  rw [integral_congr_ae (W1p.value_ae_eq_intervalRepresentativeL zero_lt_one v),
    W1p.intervalTraceL_apply]
  simp only [mul_comm (W1p.gradient v _)]
  rw [h]
  simp only [sub_self, zero_mul, sub_zero, one_mul, neg_mul, integral_neg, projIcc_left]
  ring

/-- The solution `t - t² / 2` of the mixed problem on `(0, 1)`, with derivative `1 - t`. -/
private theorem exists_value_gradient_ae_eq :
    ∃ w : W1p volume (⟨Ioo 0 1, isOpen_Ioo⟩ : Opens ℝ) 2,
      W1p.value w =ᵐ[volume.restrict (Ioo 0 1)] (fun t => t - t ^ 2 / 2) ∧
        W1p.gradient w =ᵐ[volume.restrict (Ioo 0 1)] (fun t => 1 - t) := by
  have hd : deriv (fun t : ℝ => t - t ^ 2 / 2) = fun t => 1 - t := funext fun t => by
    have h : HasDerivAt (fun t : ℝ => t - t ^ 2 / 2) (1 - 2 * t ^ (2 - 1) / 2) t :=
      (hasDerivAt_id' t).sub ((hasDerivAt_pow 2 t).div_const 2)
    rw [h.deriv]
    norm_num
  have hf : ContDiff ℝ 1 (fun t : ℝ => t - t ^ 2 / 2) := by fun_prop
  obtain ⟨w, hw, hg⟩ := AbsolutelyContinuousOnInterval.exists_w1p_value_gradient_ae_eq (p := 2)
    hf.contDiffOn.absolutelyContinuousOnInterval
    (hd ▸ (show Continuous fun t : ℝ => 1 - t by fun_prop).continuousOn
      |>.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self 2)
  exact ⟨w, hw, hd ▸ hg⟩

attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p
  W1pVanishingOn.instNormedAddCommGroup W1pVanishingOn.instInnerProductSpace

/-- The Poincaré–Friedrichs inequality with constant `1` on `H¹_{{0}}` of the interval domain. -/
private theorem norm_value_le_norm_gradient {u : W1p volume (intervalDomain 0 1) 2}
    (hu : u ∈ w1pVanishingOnSubmodule volume (intervalDomain 0 1) 2 {0}) :
    ‖W1p.value u‖ ≤ 1 * ‖W1p.gradient u‖ := by
  rw [one_mul, ← W1p.norm_value_compAffineIsometryEquivL lineIso Ioo_eq_preimage,
    ← W1p.norm_gradient_compAffineIsometryEquivL lineIso Ioo_eq_preimage]
  exact UnitIntervalLeftEndpoint.norm_value_le_norm_gradient (pull_mem hu)

/-- The energy form of `-u''` is coercive on `H¹_{{0}}` of the interval domain. -/
private theorem isCoercive :
    IsCoercive (energyFormH1LVanishingOn (memLp_energyIntegrand_const_zero_zero
      (mu := volume) (Omega := intervalDomain 0 1) (1 : Matrix (Fin 1) (Fin 1) ℝ)) {0}) :=
  UniformlyEllipticOn.isCoercive_energyFormH1LVanishingOn_of_poincare
    (uniformlyEllipticOn_const_one_one _) aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _ _ => rfl) (gamma := 0) (fun _ _ => by simp) (fun _ _ => le_rfl)
    (fun _ hu => norm_value_le_norm_gradient hu) _

/-- The function `x - x² / 2` on the interval domain lies in `H¹_{{0}}` and solves the mixed
problem `∫ u' v' = ∫ v` for every `v ∈ H¹_{{0}}`. -/
private theorem exists_solution :
    ∃ u : W1p volume (intervalDomain 0 1) 2,
      W1p.value u =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
          (fun x => x 0 - x 0 ^ 2 / 2) ∧
        u ∈ w1pVanishingOnSubmodule volume (intervalDomain 0 1) 2 {0} ∧
        ∀ v ∈ w1pVanishingOnSubmodule volume (intervalDomain 0 1) 2 {0},
          energyFormH1 (fun _ => 1) 0 0 u v = ∫ x in intervalDomain 0 1, W1p.value v x := by
  obtain ⟨w, hw, hg⟩ := exists_value_gradient_ae_eq
  have hmp : MeasurePreserving lineIso.symm
      (volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1))))
      (volume.restrict (Ioo 0 1)) :=
    intervalDomain_eq_preimage ▸ lineIso.symm.measurePreserving.restrict_preimage measurableSet_Ioo
  refine ⟨push w, ?_, ?_, fun v hv => ?_⟩
  · filter_upwards [W1p.value_compAffineIsometryEquivL_ae lineIso.symm intervalDomain_eq_preimage
      w, hmp.quasiMeasurePreserving.ae hw] with x h1 h2
    rw [h1, h2, lineIso_symm_apply]
  · -- It vanishes at `0`, since its continuous representative is `t - t² / 2`.
    rw [← W1p.compAffineIsometryEquivL_mem_w1pVanishingOnSubmodule_iff lineIso Ioo_eq_preimage,
      preimage_lineIso_zero, pull_push,
      W1p.mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_fst_eq_zero (by simp)
        zero_lt_one]
    have hrep := (W1p.intervalRepresentativeL_eq_iff zero_lt_one w
      ⟨fun t => (t : ℝ) - (t : ℝ) ^ 2 / 2, by fun_prop⟩).2 (by
        filter_upwards [hw, ae_restrict_mem measurableSet_Ioo] with t ht htI
        simp [ht, projIcc_of_mem zero_le_one (Ioo_subset_Icc_self htI)])
    simp [hrep]
  · -- It solves the weak equation, by integration by parts against `1 - t`.
    rw [energyFormH1_eq_setIntegral_pull, pull_push, setIntegral_value_pull,
      integral_congr_ae (hg.mono fun t ht => by rw [ht]), setIntegral_gradient_mul_one_sub,
      W1p.intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton zero_lt_one
        (pull_mem hv), sub_zero]

/-- **The mixed problem `-u'' = 1`, `u(0) = 0`, `u'(1) = 0` on `(0, 1)`.** On the interval
domain `(0, 1)` with Dirichlet part `Γ = {0}`, an element `u ∈ H¹(0, 1)` is a weak solution of
the mixed problem, that is `u ∈ H¹_Γ(0, 1)` and `∫ u' v' = ∫ v` for every `v ∈ H¹_Γ(0, 1)`,
exactly when `u = x - x² / 2`. -/
theorem mem_w1pVanishingOnSubmodule_and_forall_energyFormH1_eq_iff
    {u : W1p volume (intervalDomain 0 1) 2} :
    (u ∈ w1pVanishingOnSubmodule volume (intervalDomain 0 1) 2 {0} ∧
      ∀ v ∈ w1pVanishingOnSubmodule volume (intervalDomain 0 1) 2 {0},
        energyFormH1 (fun _ => 1) 0 0 u v = ∫ x in intervalDomain 0 1, W1p.value v x) ↔
      W1p.value u =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x => x 0 - x 0 ^ 2 / 2 := by
  obtain ⟨u₀, hval, hmem, heq⟩ := exists_solution
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · -- Uniqueness, from coercivity on `H¹_{{0}}`.
    let ℓ : StrongDual ℝ (W1pVanishingOn volume (intervalDomain 0 1) 2 {0}) :=
      W1p.integralL.comp (W1pVanishingOn volume (intervalDomain 0 1) 2 {0}).subtypeL
    have : u = u₀ :=
      (existsUnique_sub_mem_w1pVanishingOnSubmodule_forall_energyFormH1_eq _ isCoercive 0
        ℓ).unique ⟨by simpa using hu.1, fun v => by simpa [ℓ] using hu.2 v v.property⟩
        ⟨by simpa using hmem, fun v => by simpa [ℓ] using heq v v.property⟩
    exact this ▸ hval
  · have : u = u₀ := W1p.ext_value (Lp.ext (hu.trans hval.symm))
    exact this ▸ ⟨hmem, heq⟩

/-- **The mixed problem `-u'' = 1`, `u(0) = 0`, `u'(1) = 0` on `(0, 1)` is uniquely solvable**:
there is exactly one `u ∈ H¹_{{0}}(0, 1)` with `∫ u' v' = ∫ v` for every `v ∈ H¹_{{0}}(0, 1)`. By
`mem_w1pVanishingOnSubmodule_and_forall_energyFormH1_eq_iff` it is `x - x² / 2`. -/
theorem existsUnique_mem_w1pVanishingOnSubmodule_and_forall_energyFormH1_eq :
    ∃! u : W1p volume (intervalDomain 0 1) 2,
      u ∈ w1pVanishingOnSubmodule volume (intervalDomain 0 1) 2 {0} ∧
        ∀ v ∈ w1pVanishingOnSubmodule volume (intervalDomain 0 1) 2 {0},
          energyFormH1 (fun _ => 1) 0 0 u v = ∫ x in intervalDomain 0 1, W1p.value v x := by
  obtain ⟨u₀, hval, hsol⟩ := exists_solution
  refine ⟨u₀, hsol, fun u hu => W1p.ext_value (Lp.ext ?_)⟩
  exact (mem_w1pVanishingOnSubmodule_and_forall_energyFormH1_eq_iff.1 hu).trans hval.symm

/-- **The Neumann problem for `-u'' = 1` on `(0, 1)` has no weak solution.** With `Γ = ∅` and no
boundary datum, the compatibility condition `∫ f = 0` fails for `f = 1`: there is no
`u ∈ H¹(0, 1)` with `∫ u' v' = ∫ v` for every `v ∈ H¹(0, 1)`, as testing with `v = 1` shows. -/
theorem not_exists_forall_energyFormH1_eq_setIntegral :
    ¬ ∃ u : W1p volume (intervalDomain 0 1) 2, ∀ v : W1p volume (intervalDomain 0 1) 2,
      energyFormH1 (fun _ => 1) 0 0 u v = ∫ x in intervalDomain 0 1, W1p.value v x := by
  rintro ⟨u, hu⟩
  have h := hu (W1p.const 1)
  rw [energyFormH1_const_right, integral_congr_ae (W1p.value_const_ae 1),
    setIntegral_intervalDomain_eq] at h
  simp at h

/-- The energy form of `-u'' + u` is the Dirichlet form plus the `L²` inner product. -/
private theorem energyFormH1_one_zero_one (u v : W1p volume (intervalDomain 0 1) 2) :
    energyFormH1 (fun _ => 1) 0 (fun _ => 1) u v =
      energyFormH1 (fun _ => 1) 0 0 u v + ⟪W1p.value u, W1p.value v⟫_ℝ := by
  simpa only [Pi.zero_apply, zero_sub, neg_neg, neg_mul, one_mul, sub_neg_eq_add, zero_add]
    using
    energyFormH1_mass_sub_const (c := 0) (memLp_energyIntegrand_const_zero_zero (mu := volume)
      (Omega := intervalDomain 0 1) (1 : Matrix (Fin 1) (Fin 1) ℝ)) (-1) u v

/-- **The Neumann problem for `-u'' + u = 1` on `(0, 1)`.** With `Γ = ∅` and no boundary datum,
the mass term makes the energy form coercive on all of `H¹(0, 1)`, with no Poincaré inequality,
and the constant `1` is the unique weak solution: `∫ (u' v' + u v) = ∫ v` for every
`v ∈ H¹(0, 1)` exactly when `u = 1`. -/
theorem forall_energyFormH1_eq_setIntegral_iff
    {u : W1p volume (intervalDomain 0 1) 2} :
    (∀ v : W1p volume (intervalDomain 0 1) 2,
      energyFormH1 (fun _ => 1) 0 (fun _ => 1) u v =
        ∫ x in intervalDomain 0 1, W1p.value v x) ↔
      u = W1p.const 1 := by
  have hconst (v : W1p volume (intervalDomain 0 1) 2) :
      energyFormH1 (fun _ => 1) 0 (fun _ => 1) (W1p.const 1) v =
        ∫ x in intervalDomain 0 1, W1p.value v x := by
    rw [energyFormH1_one_zero_one, energyFormH1_one_zero_zero_eq_inner, W1p.gradient_const,
      inner_zero_left, zero_add, W1p.inner_value_eq_setIntegral]
    refine integral_congr_ae ?_
    filter_upwards [W1p.value_const_ae (mu := volume) (Omega := intervalDomain 0 1) (p := 2) 1]
      with x hx
    rw [hx, one_mul]
  refine ⟨fun hu => ?_, fun hu => hu ▸ hconst⟩
  -- The difference `w = u - 1` has zero energy `‖w'‖² + ‖w‖² = ‖w‖²_{H¹}`.
  have hcoeff : MemLp (fun x => energyIntegrand ((fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) x)
      ((0 : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) x) ((fun _ => (1 : ℝ)) x)) ⊤
      (volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))) :=
    memLp_top_const (energyIntegrand (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 1)
  have hw := energyFormH1_sub_left hcoeff u (u - W1p.const 1) (W1p.const 1)
  rw [hu, hconst, sub_self, energyFormH1_one_zero_one, energyFormH1_one_zero_zero_eq_inner,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, add_comm,
    ← W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq] at hw
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hw))

end TauCeti.Examples.MixedProblemUnitInterval
