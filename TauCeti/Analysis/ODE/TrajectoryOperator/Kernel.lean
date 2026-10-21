/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.ODE.TrajectoryOperator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.ODE.Caratheodory
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The kernel of the trajectory operator consists of classical solutions

Let `A : ℝ → End(F)` be a continuous family of bounded operators on a real Banach space `F`. An
element `u` of the kernel of the trajectory operator `D_A u = u' + A u` on the weak-derivative
graph over `Lᵖ(ℝ, F)` is a weak solution of `u' = -A u`. Since `A u` is locally integrable, `u` is
almost everywhere a constant plus a primitive of `-A u`; that primitive is continuous, so along it
the integrand `-A u` is continuous, and the primitive is a classical `C¹` solution. Conversely,
every classical solution `v` of `v' + A v = 0` with `v ∈ Lᵖ` comes from the kernel of `D_A`: its
derivative `-A v` is again in `Lᵖ` because `A` is essentially bounded.

For `p = 2` this identifies the kernel of `D_A` with the space
`TauCeti.squareIntegrableSolutions A` of initial values `v 0` of square-integrable solutions of
`v' + A v = 0`, by evaluating the continuous representative at time `0`; that this is injective is
uniqueness of solutions of linear equations. Neither symmetry of `A`, finite dimensionality of `F`
nor any Fredholm property of `D_A` is used. The resulting formula for the index of `D_A` as a
difference of dimensions of spaces of square-integrable solutions is
`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finrank_sub_finrank_of_isClosed_range`.

## Main declarations

* `TauCeti.squareIntegrableSolutions`: the initial values of the square-integrable solutions of
  `v' + A(s) v = 0`.
* `TauCeti.WeakDerivStep.exists_hasDerivAt_of_trajectoryOperator_eq_zero`: an element of the
  kernel of `D_A` has a classical solution of `v' = -A v` as representative.
* `TauCeti.WeakDerivStep.exists_trajectoryOperator_eq_zero_of_hasDerivAt`: an `Lᵖ` classical
  solution of `v' = -A v` is the value of an element of the kernel of `D_A`.
* `TauCeti.WeakDerivStep.kerTrajectoryOperatorEquiv`: the kernel of `D_A` on `W^{1,2}(ℝ, F)` is
  linearly equivalent to `TauCeti.squareIntegrableSolutions A`.
* `TauCeti.WeakDerivStep.finrank_ker_trajectoryOperator`: the kernel of `D_A` on
  `W^{1,2}(ℝ, F)` has the dimension of `TauCeti.squareIntegrableSolutions A`.

## References

* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (the kernel and cokernel of the
  linearized trajectory operator as spaces of decaying solutions).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The initial values at time `0` of the square-integrable solutions `v : ℝ → F` of the linear
equation `v' + A(s) v = 0` on the whole line. For the coefficient of a trajectory operator
`D_A = d/ds + A`, this is a model of the kernel of `D_A`
(`TauCeti.WeakDerivStep.kerTrajectoryOperatorEquiv`). -/
def squareIntegrableSolutions (A : ℝ → F →L[ℝ] F) : Submodule ℝ F where
  carrier := {x | ∃ v : ℝ → F, v 0 = x ∧ (∀ s, HasDerivAt v (-A s (v s)) s) ∧ MemLp v 2}
  zero_mem' := ⟨0, rfl, fun s ↦ by simp, MemLp.zero⟩
  add_mem' := by
    rintro _ _ ⟨v, rfl, hv, hv2⟩ ⟨w, rfl, hw, hw2⟩
    exact ⟨v + w, rfl, fun s ↦ by simpa [add_comm] using (hv s).add (hw s), hv2.add hw2⟩
  smul_mem' := by
    rintro c _ ⟨v, rfl, hv, hv2⟩
    exact ⟨c • v, rfl, fun s ↦ by simpa using (hv s).const_smul c, hv2.const_smul c⟩

/-- A vector lies in `TauCeti.squareIntegrableSolutions A` when it is the value at time `0` of a
square-integrable solution of `v' + A v = 0`. -/
theorem mem_squareIntegrableSolutions {A : ℝ → F →L[ℝ] F} {x : F} :
    x ∈ squareIntegrableSolutions A ↔
      ∃ v : ℝ → F, v 0 = x ∧ (∀ s, HasDerivAt v (-A s (v s)) s) ∧ MemLp v 2 :=
  Iff.rfl

end TauCeti

namespace TauCeti.WeakDerivStep

section Banach

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {A : ℝ → F →L[ℝ] F}

/-- **Elements of the kernel are classical solutions.** If `A` is continuous and `u` lies in the
kernel of the trajectory operator `D_A u = u' + A u` on the weak-derivative graph over `Lᵖ(ℝ, F)`,
then the value of `u` agrees almost everywhere with a classical solution `v` of `v' = -A v`. -/
theorem exists_hasDerivAt_of_trajectoryOperator_eq_zero (hA : Continuous A)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    {u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    (hu : trajectoryOperator AL u = 0) :
    ∃ v : ℝ → F, (∀ s, HasDerivAt v (-A s (v s)) s) ∧
      ⇑(prev (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
        =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] v := by
  set w : ℝ → F :=
    ⇑(prev (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
  have h : HasWeakLineDerivOn volume ⊤ w (fun s ↦ -A s (w s)) 1 := by
    refine ((trajectoryOperator_eq_iff_hasWeakLineDerivOn AL u 0).mp hu).congr_ae_deriv ?_
    filter_upwards [Lp.coeFn_zero F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), hAL]
      with s h0 hs
    rw [h0, hs, Pi.zero_apply, zero_sub]
  obtain ⟨c, hc⟩ := h.exists_ae_eq_add_intervalIntegral_top 0
  have hli : LocallyIntegrable (fun s ↦ -A s (w s)) volume :=
    locallyIntegrableOn_univ.1 (by simpa using h.locallyIntegrableOn_deriv)
  have hint (a b : ℝ) : IntervalIntegrable (fun s ↦ -A s (w s)) volume a b :=
    (hli.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  set v : ℝ → F := fun t ↦ c + ∫ s in 0..t, -A s (w s)
  have hvc : Continuous v := continuous_const.add (intervalIntegral.continuous_primitive hint 0)
  -- Along `v` the integrand is continuous, and the primitive of `-A v` is `v` itself.
  have hv : ∀ t, v t = c + ∫ s in 0..t, -A s (v s) := fun t ↦
    congrArg (c + ·) <| intervalIntegral.integral_congr_ae <| by
      filter_upwards [hc] with s hs _
      rw [hs]
  refine ⟨v, fun t ↦ ?_, by simpa using hc⟩
  have hcont : Continuous fun s ↦ -A s (v s) := (hA.clm_apply hvc).neg
  exact ((hcont.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add c).congr_of_eventuallyEq
    (Eventually.of_forall hv)

/-- **Classical solutions lie in the kernel.** If `v` is a classical solution of `v' = -A v` that
lies in `Lᵖ(ℝ, F)`, then `v` is the value of an element `u` of the weak-derivative graph over
`Lᵖ(ℝ, F)` with `D_A u = 0`. No continuity of `A` is needed: the derivative `-A v` lies in `Lᵖ`
because `A` is essentially bounded. -/
theorem exists_trajectoryOperator_eq_zero_of_hasDerivAt
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {v : ℝ → F}
    (hv : ∀ s, HasDerivAt v (-A s (v s)) s) (hvp : MemLp v p) :
    ∃ u : WeakDerivStep volume ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      trajectoryOperator AL u = 0 ∧
        ⇑(prev (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
          =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] v := by
  have hvp' : MemLp v p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by simpa using hvp
  set x := hvp'.toLp v
  have hx : (x : ℝ → F) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] v := hvp'.coeFn_toLp
  -- The derivative `-A v` agrees almost everywhere with the `Lᵖ` path `-(A x)`.
  have hd : (fun s ↦ -A s (v s)) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (0 : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) s - AL s (x s) := by
    filter_upwards [Lp.coeFn_zero F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), hAL, hx]
      with s h0 hs hxs
    rw [h0, hs, hxs, Pi.zero_apply, zero_sub]
  have hloc' : LocallyIntegrableOn (fun s ↦ -A s (v s)) (⊤ : Opens ℝ) volume := by
    refine (Lp.locallyIntegrableOn
      (-(ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p AL x) Fact.out).congr ?_
    filter_upwards [Lp.coeFn_neg ((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p AL x),
      (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).coeFn_holder (r := p) AL x, hAL, hx]
      with s hneg hAs hALs hxs
    rw [hneg, Pi.neg_apply, hAs, ContinuousLinearMap.id_apply, hALs, hxs]
  have h : HasWeakLineDerivOn volume ⊤ v (fun s ↦ -A s (v s)) 1 :=
    hasWeakLineDerivOn_of_hasLineDerivAt ((hvp.locallyIntegrable Fact.out).locallyIntegrableOn _)
      hloc' fun s _ ↦ by simpa using (hv s).hasFDerivAt.hasLineDerivAt 1
  obtain ⟨u, hux, hu⟩ := exists_prev_eq_and_trajectoryOperator_eq_of_hasWeakLineDerivOn AL
    ((h.congr_ae hx.symm).congr_ae_deriv hd)
  exact ⟨u, hu, by rw [hux]; exact hx⟩

end Banach

section SquareIntegrable

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {A : ℝ → F →L[ℝ] F}

/-- The continuous representative of an element of the kernel of `D_A`, a classical solution of
`v' = -A v`. -/
private def kerSolution (hA : Continuous A)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (u : (trajectoryOperator (p := 2) AL).ker) : ℝ → F :=
  Classical.choose (exists_hasDerivAt_of_trajectoryOperator_eq_zero hA hAL u.2)

private theorem hasDerivAt_kerSolution (hA : Continuous A)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (u : (trajectoryOperator (p := 2) AL).ker) (s : ℝ) :
    HasDerivAt (kerSolution hA hAL u) (-A s (kerSolution hA hAL u s)) s :=
  (Classical.choose_spec (exists_hasDerivAt_of_trajectoryOperator_eq_zero hA hAL u.2)).1 s

private theorem continuous_kerSolution (hA : Continuous A)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (u : (trajectoryOperator (p := 2) AL).ker) : Continuous (kerSolution hA hAL u) :=
  Differentiable.continuous fun s ↦ (hasDerivAt_kerSolution hA hAL u s).differentiableAt

private theorem prev_ae_eq_kerSolution (hA : Continuous A)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (u : (trajectoryOperator (p := 2) AL).ker) :
    ⇑(prev (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u.1)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] kerSolution hA hAL u :=
  (Classical.choose_spec (exists_hasDerivAt_of_trajectoryOperator_eq_zero hA hAL u.2)).2

/-- Any continuous representative of an element of the kernel is its chosen solution. -/
private theorem kerSolution_eq (hA : Continuous A)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (u : (trajectoryOperator (p := 2) AL).ker) {v : ℝ → F} (hv : Continuous v)
    (huv : ⇑(prev (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u.1)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] v) :
    kerSolution hA hAL u = v := by
  have h := (prev_ae_eq_kerSolution hA hAL u).symm.trans huv
  rw [Opens.coe_top, Measure.restrict_univ] at h
  exact (Continuous.ae_eq_iff_eq volume (continuous_kerSolution hA hAL u) hv).1 h

/-- Evaluation at time `0` of the continuous representative, as a linear map from the kernel of
`D_A` to `F`. -/
private def kerEval (hA : Continuous A)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    (trajectoryOperator (p := 2) AL).ker →ₗ[ℝ] F where
  toFun u := kerSolution hA hAL u 0
  map_add' u w := by
    rw [kerSolution_eq hA hAL (u + w)
      ((continuous_kerSolution hA hAL u).add (continuous_kerSolution hA hAL w)) ?_]
    · rfl
    rw [Submodule.coe_add, prev_add]
    exact (Lp.coeFn_add _ _).trans
      ((prev_ae_eq_kerSolution hA hAL u).add (prev_ae_eq_kerSolution hA hAL w))
  map_smul' c u := by
    rw [kerSolution_eq hA hAL (c • u) ((continuous_kerSolution hA hAL u).const_smul c) ?_]
    · rfl
    rw [Submodule.coe_smul, prev_smul]
    exact (Lp.coeFn_smul c _).trans ((prev_ae_eq_kerSolution hA hAL u).const_smul c)

private theorem kerEval_apply (hA : Continuous A)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (u : (trajectoryOperator (p := 2) AL).ker) : kerEval hA hAL u = kerSolution hA hAL u 0 :=
  rfl

private theorem kerEval_mem (hA : Continuous A)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (u : (trajectoryOperator (p := 2) AL).ker) :
    kerEval hA hAL u ∈ squareIntegrableSolutions A := by
  refine ⟨kerSolution hA hAL u, rfl, hasDerivAt_kerSolution hA hAL u, ?_⟩
  have h := (Lp.memLp (prev _ u.1)).ae_eq (prev_ae_eq_kerSolution hA hAL u)
  simpa using h

/-- A solution vanishing at time `0` vanishes identically, so evaluation is injective. -/
private theorem kerEval_injective (hA : Continuous A)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    Function.Injective (kerEval hA hAL) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h0 : kerSolution hA hAL u = 0 := hA.neg.eq_of_hasDerivAt_clm_apply
    (hasDerivAt_kerSolution hA hAL u) (fun s ↦ by simp) (t₀ := 0)
    ((kerEval_apply hA hAL u).symm.trans hu)
  have hprev : prev _ u.1 = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    simpa [h0] using prev_ae_eq_kerSolution hA hAL u
  exact Subtype.ext (ext (by rw [hprev, Submodule.coe_zero, prev_zero]))

/-- Every square-integrable solution is the continuous representative of a kernel element. -/
private theorem exists_kerEval_eq (hA : Continuous A)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {x : F}
    (hx : x ∈ squareIntegrableSolutions A) : ∃ u, kerEval hA hAL u = x := by
  obtain ⟨v, rfl, hv, hv2⟩ := hx
  obtain ⟨u, hu, huv⟩ := exists_trajectoryOperator_eq_zero_of_hasDerivAt (p := 2) hAL hv hv2
  refine ⟨⟨u, hu⟩, ?_⟩
  rw [kerEval_apply, kerSolution_eq hA hAL ⟨u, hu⟩
    (Differentiable.continuous fun s ↦ (hv s).differentiableAt) huv]

/-- Evaluation at time `0` is a bijection onto the square-integrable solutions. -/
private theorem bijective_codRestrict_kerEval (hA : Continuous A)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    Function.Bijective ((kerEval hA hAL).codRestrict _ (kerEval_mem hA hAL)) :=
  ⟨fun _ _ h ↦ kerEval_injective hA hAL (congrArg Subtype.val h), fun x ↦
    (exists_kerEval_eq hA hAL x.2).imp fun _ h ↦ Subtype.ext h⟩

/-- **The kernel of the trajectory operator is the space of square-integrable solutions.** For a
continuous family `A` of bounded operators on a real Banach space `F`, with `L∞` class `AL`,
evaluating the continuous representative at time `0` is a linear equivalence from the kernel of
`D_A u = u' + A u` on `W^{1,2}(ℝ, F)` to the initial values of the square-integrable solutions of
`v' + A v = 0`. -/
def kerTrajectoryOperatorEquiv (hA : Continuous A)
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    (trajectoryOperator (p := 2) AL).ker ≃ₗ[ℝ] squareIntegrableSolutions A :=
  LinearEquiv.ofBijective _ (bijective_codRestrict_kerEval hA hAL)

/-- The equivalence `kerTrajectoryOperatorEquiv` evaluates at time `0` any continuous
representative of the value of a kernel element. -/
theorem kerTrajectoryOperatorEquiv_apply (hA : Continuous A)
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (u : (trajectoryOperator (p := 2) AL).ker) {v : ℝ → F} (hv : Continuous v)
    (huv : ⇑(prev (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u.1)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] v) :
    (kerTrajectoryOperatorEquiv hA AL hAL u : F) = v 0 := by
  rw [kerTrajectoryOperatorEquiv, LinearEquiv.ofBijective_apply, LinearMap.codRestrict_apply,
    kerEval_apply, kerSolution_eq hA hAL u hv huv]

/-- The kernel of `D_A u = u' + A u` on `W^{1,2}(ℝ, F)` has the dimension of the space of
square-integrable solutions of `v' + A v = 0`. -/
theorem finrank_ker_trajectoryOperator (hA : Continuous A)
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker =
      Module.finrank ℝ (squareIntegrableSolutions A) :=
  (kerTrajectoryOperatorEquiv hA AL hAL).finrank_eq

end SquareIntegrable

end TauCeti.WeakDerivStep
