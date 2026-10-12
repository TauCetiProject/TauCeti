/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.EnergyEstimate
public import TauCeti.Analysis.ODE.Inhomogeneous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Galerkin approximations of autonomous parabolic equations

Let `ι : V → H` embed an energy space into a real pivot Hilbert space, and let
`A : V → V*` be a bounded linear operator. For a finite-dimensional real inner product space
`F` and a continuous linear map `e : F → V` whose composite with `ι` is injective, the
Galerkin equation is

`⟪ι(e c'(t)), ι(e v)⟫ + A(e c(t))(e v) = f(t)(e v)` for every `v : F`.

For continuous `f : ℝ → V*`, this equation has a unique global `C¹` solution for any initial
coordinate vector. No symmetry or coercivity of `A` is needed for this existence result.
Injectivity into the pivot space makes the finite-dimensional mass operator invertible.
Mathlib's `ContinuousLinearMap.bilinearComp` restricts the forms, and
`InnerProductSpace.continuousLinearMapOfBilin` represents them as operators.

On a finite-dimensional subspace of `V`, Gårding's inequality gives the usual energy estimate
with constants independent of the subspace. This is the estimate needed to pass from Galerkin
approximations to a weak parabolic solution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.2, Theorems 1 and 2.
-/

public section

noncomputable section

open MeasureTheory Set InnerProductSpace
open scoped InnerProductSpace

namespace TauCeti.PDE

variable {V H F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Existence and uniqueness of Galerkin approximations.** For a bounded autonomous energy
operator, continuous forcing and a finite-dimensional trial map injective into the pivot space,
the projected parabolic equation has a unique global `C¹` solution with prescribed value at
any time `t₀`. The coordinates need not be orthonormal in the pivot space. -/
theorem existsUnique_galerkinSolution (ι : V →L[ℝ] H) (A : V →L[ℝ] StrongDual ℝ V)
    (e : F →L[ℝ] V) (he : Function.Injective (ι.comp e)) {f : ℝ → StrongDual ℝ V}
    (hf : Continuous f) (x : F) (t₀ : ℝ) :
    ∃! c : ℝ → F, c t₀ = x ∧ ContDiff ℝ 1 c ∧ ∀ t v,
      ⟪ι (e (deriv c t)), ι (e v)⟫_ℝ + A (e (c t)) (e v) = f t (e v) := by
  -- Represent the restricted mass and energy forms by operators on the coordinate space.
  let j := ι.comp e
  let M := continuousLinearMapOfBilin (j.gelfandDual.comp j)
  let D := continuousLinearMapOfBilin (A.bilinearComp e e)
  let R : StrongDual ℝ V →L[ℝ] F :=
    (toDual ℝ F).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.compL ℝ F V ℝ).flip e)
  have hM (z v : F) : ⟪M z, v⟫_ℝ = ⟪j z, j v⟫_ℝ := by
    simp [M]
  have hD (z v : F) : ⟪D z, v⟫_ℝ = A (e z) (e v) := by
    simp [D]
  have hR (g : StrongDual ℝ V) (v : F) : ⟪R g, v⟫_ℝ = g (e v) := by
    simp [R]
  -- Testing the mass operator on its argument proves injectivity; finite dimension gives an
  -- inverse, without any coercivity assumption on the energy form.
  have hMinj : Function.Injective M := by
    refine (injective_iff_map_eq_zero M).2 fun z hz ↦ ?_
    have hjz : j z = 0 := by
      have hnorm : ‖j z‖ ^ 2 = 0 := by
        simpa [hz, real_inner_self_eq_norm_sq] using (hM z z).symm
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    exact he (by simpa only [map_zero] using hjz)
  let Q : F ≃L[ℝ] F :=
    (LinearEquiv.ofInjectiveEndo M.toLinearMap hMinj).toContinuousLinearEquiv
  have hQ (z : F) : Q z = M z := by
    simp [Q]
  let B : F →L[ℝ] F := -(Q.symm.toContinuousLinearMap.comp D)
  let g : ℝ → F := fun t ↦ Q.symm (R (f t))
  have hg : Continuous g := Q.symm.continuous.comp (R.continuous.comp hf)
  have hEq (z d : F) (t : ℝ) :
      (∀ v, ⟪ι (e d), ι (e v)⟫_ℝ + A (e z) (e v) = f t (e v)) ↔
        d = B z + g t := by
    constructor
    · intro h
      have hmass : Q d = R (f t) - D z := by
        apply ext_inner_right ℝ
        intro v
        simp only [hQ, hM, inner_sub_left, hR, hD]
        exact eq_sub_of_add_eq (h v)
      have := congrArg Q.symm hmass
      simpa [B, g, map_sub, sub_eq_add_neg, add_comm] using this
    · rintro rfl
      have hmass : M (B z + g t) = R (f t) - D z := by
        rw [← hQ]
        simp [B, g, sub_eq_add_neg, add_comm]
      intro v
      have hv := congrArg (fun w : F ↦ ⟪w, v⟫_ℝ) hmass
      simp only [hM, inner_sub_left, hR, hD] at hv
      exact (eq_sub_iff_add_eq).1 hv
  -- Solve the reduced ODE, then transfer both its equation and its uniqueness back.
  obtain ⟨c, hc, huniq⟩ := B.existsUnique_hasDerivAt_add hg x t₀
  have hderiv : deriv c = fun t ↦ B (c t) + g t := by
    funext t
    exact (hc.2 t).deriv
  have hc1 : ContDiff ℝ 1 c := contDiff_one_iff_deriv.2
    ⟨fun t ↦ (hc.2 t).differentiableAt,
      hderiv ▸ (B.continuous.comp
        (continuous_iff_continuousAt.2 fun t ↦ (hc.2 t).continuousAt)).add hg⟩
  refine ⟨c, ⟨hc.1, hc1, fun t ↦ (hEq _ _ t).2 ((hc.2 t).deriv)⟩, ?_⟩
  intro d hd
  apply huniq d
  refine ⟨hd.1, fun t ↦ ?_⟩
  rw [← (hEq (d t) (deriv d t) t).1 (hd.2.2 t)]
  exact (hd.2.1.differentiable one_ne_zero t).hasDerivAt

/-- **The uniform Galerkin energy estimate.** If the energy operator satisfies Gårding's
inequality on the trial subspace with constants `α > 0` and `β ≥ 0`, every `C¹` projected
solution on a complete trial subspace satisfies the parabolic energy estimate on `[t₀, T]`
with the same constants.
The right-hand side uses the norm of the original forcing in `V*`, not its coordinate norm. -/
theorem norm_sq_add_mul_integral_le_galerkin (ι : V →L[ℝ] H)
    (A : V →L[ℝ] StrongDual ℝ V) (G : Submodule ℝ V) [CompleteSpace G]
    {c : ℝ → G} (hc : ContDiff ℝ 1 c) {f : ℝ → StrongDual ℝ V} (hf : Continuous f)
    {α β t₀ T : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hA : ∀ v : G, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A v v)
    (heq : ∀ t (v : G),
      ⟪ι (↑(deriv c t) : V), ι v⟫_ℝ + A (c t) v = f t v)
    {t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖ι (c t)‖ ^ 2 + α * ∫ s in t₀..t, ‖c s‖ ^ 2 ≤
      Real.exp (2 * β * (t - t₀)) * (‖ι (c t₀)‖ ^ 2 + α⁻¹ * ∫ s in t₀..t, ‖f s‖ ^ 2) := by
  let j : G →L[ℝ] H := ι.comp G.subtypeL
  let L := j.gelfandDual.comp j
  let Ag := A.bilinearComp G.subtypeL G.subtypeL
  let fg : ℝ → StrongDual ℝ G := fun s ↦ (f s).comp G.subtypeL
  have hcc : Continuous c := hc.continuous
  have hdc : Continuous (deriv c) := hc.continuous_deriv (by simp)
  have hfg : Continuous fg := by fun_prop
  have hweak : HasWeakLineDerivOn volume ⟨Ioo t₀ T, isOpen_Ioo⟩ c (deriv c) 1 := by
    refine hasWeakLineDerivOn_of_hasLineDerivAt
      (hcc.locallyIntegrable.locallyIntegrableOn _) (hdc.locallyIntegrable.locallyIntegrableOn _) ?_
    intro s _
    simpa using (hc.differentiable one_ne_zero s).hasDerivAt.hasFDerivAt.hasLineDerivAt (1 : ℝ)
  have hcp : MemLp c 2 (volume.restrict (Ioo t₀ T)) :=
    hcc.continuousOn.memLp_restrict_of_subset_isCompact
      isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self 2
  have hdcp : MemLp (fun s ↦ L (deriv c s)) 2 (volume.restrict (Ioo t₀ T)) :=
    (L.continuous.comp hdc).continuousOn.memLp_restrict_of_subset_isCompact
      isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self 2
  have hfp : MemLp fg 2 (volume.restrict (Ioo t₀ T)) :=
    ContinuousOn.memLp_restrict_of_subset_isCompact (E := StrongDual ℝ G) (μ := volume)
      hfg.continuousOn isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self 2
  have hAg : ∀ᵐ s ∂volume.restrict (Ioo t₀ T),
      ∀ v, α * ‖v‖ ^ 2 - β * ‖j v‖ ^ 2 ≤ Ag v v := by
    exact .of_forall fun _ v ↦ by simpa [j, Ag] using hA v
  have heqg : ∀ᵐ s ∂volume.restrict (Ioo t₀ T), L (deriv c s) + Ag (c s) = fg s := by
    refine .of_forall fun s ↦ ?_
    ext v
    simpa [L, j, Ag, fg] using heq s v
  have hest := (hweak.clm_comp L).norm_sq_add_mul_integral_le_of_gelfandDual
    hcp hdcp hfp hα hβ hAg heqg
    (j.continuous.comp hcc).continuousOn (.of_forall fun _ ↦ rfl) ht
  have hfnorm (s : ℝ) : ‖fg s‖ ≤ ‖f s‖ := by
    calc
      ‖fg s‖ ≤ ‖f s‖ * ‖G.subtypeL‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖f s‖ * 1 := mul_le_mul_of_nonneg_left G.norm_subtypeL_le (norm_nonneg _)
      _ = ‖f s‖ := mul_one _
  have hint : ∫ s in t₀..t, ‖fg s‖ ^ 2 ≤ ∫ s in t₀..t, ‖f s‖ ^ 2 := by
    have hfg2 : Continuous (fun s ↦ ‖fg s‖ ^ 2) :=
      (Continuous.norm (E := StrongDual ℝ G) hfg).pow 2
    have hf2 : Continuous (fun s ↦ ‖f s‖ ^ 2) :=
      (Continuous.norm (E := StrongDual ℝ V) hf).pow 2
    refine intervalIntegral.integral_mono_on ht.1
      (hfg2.intervalIntegrable t₀ t) (hf2.intervalIntegrable t₀ t) fun s _ ↦ ?_
    exact pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg (fg s)) (hfnorm s) 2
  have hest' : ‖ι (c t)‖ ^ 2 + α * ∫ s in t₀..t, ‖c s‖ ^ 2 ≤
      Real.exp (2 * β * (t - t₀)) * (‖ι (c t₀)‖ ^ 2 + α⁻¹ * ∫ s in t₀..t, ‖fg s‖ ^ 2) := by
    simpa [j] using hest
  refine hest'.trans ?_
  gcongr

end TauCeti.PDE
