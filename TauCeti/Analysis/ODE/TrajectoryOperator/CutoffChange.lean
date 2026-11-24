/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.FreeEndpoint
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel

/-!
# Changing the cutoffs of free endpoint variables

The extended trajectory operator of `TauCeti.Analysis.ODE.TrajectoryOperator.FreeEndpoint`,

`D_extended (ξ, v) = D_{A - w'} ξ + ∑ i, exp w • D_A (χ i • v i)`,

adjoins free endpoint variables `v i` to the weighted trajectory operator, extended into the line
by cutoffs `χ i`. This file shows that it does not depend on the cutoffs, up to an explicit
bounded isomorphism of its domain: only the behaviour of the cutoffs near the ends matters.

Let `χ' i` be other cutoffs with `χ i - χ' i` compactly supported, and let `w` be a `C¹` weight.
The solution `u = exp (-w) • ξ + ∑ i, χ i • v i` attached to `(ξ, v)` by
`TauCeti.WeakDerivStep.coprod_endTailL_eq_zero_iff` is the solution attached to `(ξ + g, v)` for
the cutoffs `χ'`, where `g` is the **change-of-cutoff path**

`g = exp w • ∑ i, (χ i - χ' i) • v i` (`TauCeti.cutoffChangePath`).

It is `C¹` with compact support, hence lies in `W^{1,p}`, and depends linearly on `v`
(`TauCeti.WeakDerivStep.cutoffChangeL`). Its image under the weighted trajectory operator is the
difference of the end tails of `v` for the two families of cutoffs
(`TauCeti.WeakDerivStep.trajectoryOperator_cutoffChangeL`). So the shear

`(ξ, v) ↦ (ξ + g, v)` (`TauCeti.WeakDerivStep.cutoffChangeEquiv`)

is a continuous linear automorphism of `W^{1,p} × ∏ i, K i` which carries the extended operator for
the cutoffs `χ'` to the one for `χ`
(`TauCeti.WeakDerivStep.coprod_endTailL_comp_cutoffChangeEquiv`). Consequently the two extended
operators have the same range, isomorphic kernels and the same index, and one is Fredholm exactly
when the other is. The shears are coherent: the one from a family of cutoffs to itself is the
identity, they compose, and the inverse of a shear is the shear back. For the same reason the
space `TauCeti.weightedAsymptoticSolutions` of initial values and free endpoint variables of the
solutions whose weighted difference from the free variables is square integrable does not depend
on the cutoffs.

## Main declarations

* `TauCeti.cutoffChangePath`: the path `exp w • ∑ i, (χ i - χ' i) • v i`.
* `TauCeti.WeakDerivStep.cutoffChangeL`: the change-of-cutoff path as a continuous linear map from
  the free variables to `W^{1,p}`, characterized by
  `TauCeti.WeakDerivStep.prev_cutoffChangeL_ae_eq`, with `cutoffChangeL_self`,
  `cutoffChangeL_add_cutoffChangeL` and `neg_cutoffChangeL`.
* `TauCeti.WeakDerivStep.trajectoryOperator_cutoffChangeL`: its image under the weighted
  trajectory operator is the difference of the end tails.
* `TauCeti.WeakDerivStep.cutoffChangeEquiv`: the shear `(ξ, v) ↦ (ξ + g, v)`, with
  `cutoffChangeEquiv_self`, `cutoffChangeEquiv_trans` and `cutoffChangeEquiv_symm`.
* `TauCeti.WeakDerivStep.coprod_endTailL_comp_cutoffChangeEquiv`: the shear intertwines the
  extended operators of the two families of cutoffs.
* `TauCeti.WeakDerivStep.range_coprod_endTailL_eq_of_hasCompactSupport_sub`,
  `TauCeti.WeakDerivStep.map_ker_coprod_endTailL_cutoffChangeEquiv`,
  `TauCeti.WeakDerivStep.index_coprod_endTailL_eq_of_hasCompactSupport_sub` and
  `TauCeti.WeakDerivStep.isFredholm_coprod_endTailL_iff_of_hasCompactSupport_sub`: the range, the
  kernel, the index and Fredholmness do not depend on the cutoffs.
* `TauCeti.weightedAsymptoticSolutions_eq_of_hasCompactSupport_sub`: neither does the space of
  solutions with prescribed initial value and free endpoint variables.

## References

* R. B. Lockhart and R. C. McOwen, *Elliptic differential operators on noncompact manifolds*,
  Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) **12** (1985), 409–447 (weighted spaces with asymptotic
  kernel elements adjoined).
* F. Bourgeois, *A Morse–Bott approach to contact homology*, PhD thesis, Stanford, 2002,
  Chapter 4 (Fredholm theory for Morse–Bott asymptotics, with free asymptotic variables).
-/

public section

noncomputable section

open Filter MeasureTheory TopologicalSpace Set
open scoped ENNReal Topology

namespace TauCeti

section CutoffChangePath

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι]
  {K : ι → Submodule ℝ F} {w w' : ℝ → ℝ} {χ χ' χ'' : ι → ℝ → ℝ}

/-- The **change-of-cutoff path** `exp w • ∑ i, (χ i - χ' i) • v i`: adding it to the weighted
component `ξ` of a point `(ξ, v)` of the domain of the extended trajectory operator for the
cutoffs `χ'` gives the point with the same solution `exp (-w) • ξ + ∑ i, χ i • v i` for the
cutoffs `χ`. -/
def cutoffChangePath (w : ℝ → ℝ) (χ χ' : ι → ℝ → ℝ) (v : Π i, K i) (s : ℝ) : F :=
  Real.exp (w s) • ∑ i, (χ i s - χ' i s) • (v i : F)

theorem cutoffChangePath_apply (v : Π i, K i) (s : ℝ) :
    cutoffChangePath w χ χ' v s = Real.exp (w s) • ∑ i, (χ i s - χ' i s) • (v i : F) := (rfl)

@[simp]
theorem cutoffChangePath_self (v : Π i, K i) : cutoffChangePath w χ χ v = 0 := by
  ext s
  simp [cutoffChangePath_apply]

theorem cutoffChangePath_add_cutoffChangePath (v : Π i, K i) :
    cutoffChangePath w χ χ' v + cutoffChangePath w χ' χ'' v = cutoffChangePath w χ χ'' v := by
  ext s
  simp only [Pi.add_apply, cutoffChangePath_apply, ← smul_add, ← Finset.sum_add_distrib,
    ← add_smul, sub_add_sub_cancel]

theorem cutoffChangePath_symm (v : Π i, K i) :
    cutoffChangePath w χ' χ v = -cutoffChangePath w χ χ' v := by
  ext s
  rw [Pi.neg_apply, cutoffChangePath_apply, cutoffChangePath_apply, ← smul_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [← neg_smul, neg_sub]

theorem cutoffChangePath_add (v v' : Π i, K i) :
    cutoffChangePath w χ χ' (v + v') = cutoffChangePath w χ χ' v + cutoffChangePath w χ χ' v' := by
  ext s
  simp only [Pi.add_apply, cutoffChangePath_apply, Submodule.coe_add, smul_add,
    Finset.sum_add_distrib]

theorem cutoffChangePath_smul (c : ℝ) (v : Π i, K i) :
    cutoffChangePath w χ χ' (c • v) = c • cutoffChangePath w χ χ' v := by
  ext s
  simp only [Pi.smul_apply, cutoffChangePath_apply, Submodule.coe_smul, Finset.smul_sum,
    smul_comm c]

/-- The change-of-cutoff path has compact support when each difference of cutoffs has. -/
theorem hasCompactSupport_cutoffChangePath (hsupp : ∀ i, HasCompactSupport (χ i - χ' i))
    (v : Π i, K i) : HasCompactSupport (cutoffChangePath w χ χ' v) := by
  have hsum : HasCompactSupport (∑ i, fun s ↦ (χ i s - χ' i s) • (v i : F)) :=
    HasCompactSupport.finset_sum fun i _ ↦ (hsupp i).smul_right
  rw [Finset.sum_fn] at hsum
  exact hsum.smul_left

theorem contDiff_cutoffChangePath (hw : ContDiff ℝ 1 w) (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hχ' : ∀ i, ContDiff ℝ 1 (χ' i)) (v : Π i, K i) :
    ContDiff ℝ 1 (cutoffChangePath w χ χ' v) :=
  hw.exp.smul (ContDiff.sum fun i _ ↦ ((hχ i).sub (hχ' i)).smul contDiff_const)

/-- **The derivative of the change-of-cutoff path.** Its image under the trajectory operator of
`A - w' • id` is the difference of the end tails of `v` for the cutoffs `χ` and `χ'`. -/
theorem hasDerivAt_cutoffChangePath {A : ℝ → F →L[ℝ] F} {s : ℝ} (hw : HasDerivAt w (w' s) s)
    (hχ : ∀ i, DifferentiableAt ℝ (χ i) s) (hχ' : ∀ i, DifferentiableAt ℝ (χ' i) s)
    (v : Π i, K i) :
    HasDerivAt (cutoffChangePath w χ χ' v)
      (∑ i, endTail w (χ i) A (v i) s - ∑ i, endTail w (χ' i) A (v i) s -
        (A s - w' s • ContinuousLinearMap.id ℝ F) (cutoffChangePath w χ χ' v s)) s := by
  have hS : HasDerivAt (fun s ↦ ∑ i, (χ i s - χ' i s) • (v i : F))
      (∑ i, (deriv (χ i) s - deriv (χ' i) s) • (v i : F)) s :=
    HasDerivAt.fun_sum fun i _ ↦
      ((hχ i).hasDerivAt.sub (hχ' i).hasDerivAt).smul_const (v i : F)
  refine (hw.exp.smul hS).congr_deriv ?_
  simp only [endTail_apply, cutoffChangePath_apply, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, map_sum, map_sub, sub_smul, Finset.sum_sub_distrib,
    Finset.smul_sum, smul_add, smul_sub, Finset.sum_add_distrib, mul_smul, smul_comm (w' s)]
  abel

/-- **The solutions with given initial value and free endpoint variables do not depend on the
cutoffs**, as long as each difference of cutoffs is continuous with compact support: changing the
cutoffs adds `TauCeti.cutoffChangePath` to the weighted difference
`exp w • (u - ∑ i, χ i • v i)` of a solution `u`, and this path is square integrable. -/
theorem weightedAsymptoticSolutions_eq_of_hasCompactSupport_sub (A : ℝ → F →L[ℝ] F)
    (hw : Continuous w) (hχ : ∀ i, Continuous (χ i - χ' i))
    (hsupp : ∀ i, HasCompactSupport (χ i - χ' i)) :
    weightedAsymptoticSolutions A w K χ = weightedAsymptoticSolutions A w K χ' := by
  ext q
  have hg : MemLp (cutoffChangePath w χ χ' q.2) 2 :=
    (hw.rexp.smul (continuous_finsetSum _ fun i _ ↦ (hχ i).smul continuous_const)
      |>.memLp_of_hasCompactSupport (hasCompactSupport_cutoffChangePath hsupp q.2))
  have heq (u : ℝ → F) : (fun s ↦ Real.exp (w s) • (u s - ∑ i, χ' i s • (q.2 i : F))) =
      (fun s ↦ Real.exp (w s) • (u s - ∑ i, χ i s • (q.2 i : F))) +
        cutoffChangePath w χ χ' q.2 := by
    ext s
    rw [Pi.add_apply, cutoffChangePath_apply, ← smul_add]
    congr 1
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  simp only [mem_weightedAsymptoticSolutions, heq]
  exact exists_congr fun u ↦ and_congr_right' <| and_congr_right'
    ⟨fun h ↦ h.add hg, fun h ↦ by simpa using h.sub hg⟩

end CutoffChangePath

namespace WeakDerivStep

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {ι : Type*} [Fintype ι] {K : ι → Submodule ℝ F} [∀ i, FiniteDimensional ℝ (K i)]
  {w : ℝ → ℝ} {A : ℝ → F →L[ℝ] F} {χ χ' χ'' : ι → ℝ → ℝ}

omit [∀ i, FiniteDimensional ℝ (K i)] in
/-- The change-of-cutoff path is the value of an element of `W^{1,p}`. -/
private theorem exists_prev_ae_eq_cutoffChangePath (hw : ContDiff ℝ 1 w)
    (hχ : ∀ i, ContDiff ℝ 1 (χ i)) (hχ' : ∀ i, ContDiff ℝ 1 (χ' i))
    (hsupp : ∀ i, HasCompactSupport (χ i - χ' i)) (v : Π i, K i) :
    ∃ u : WeakDerivStep volume ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
        =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] cutoffChangePath w χ χ' v :=
  exists_prev_ae_eq_of_contDiff_of_hasCompactSupport (contDiff_cutoffChangePath hw hχ hχ' v)
    (hasCompactSupport_cutoffChangePath hsupp v)

omit [∀ i, FiniteDimensional ℝ (K i)] in
/-- The chosen element representing the change-of-cutoff path is the only one. -/
private theorem eq_choose_of_prev_ae_eq (hw : ContDiff ℝ 1 w)
    (hχ : ∀ i, ContDiff ℝ 1 (χ i)) (hχ' : ∀ i, ContDiff ℝ 1 (χ' i))
    (hsupp : ∀ i, HasCompactSupport (χ i - χ' i)) {v : Π i, K i}
    {u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    (hu : ⇑(prev (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] cutoffChangePath w χ χ' v) :
    (exists_prev_ae_eq_cutoffChangePath hw hχ hχ' hsupp v).choose = u := by
  ext1
  exact Lp.ext ((exists_prev_ae_eq_cutoffChangePath hw hχ hχ' hsupp v).choose_spec.trans hu.symm)

/-- The **change of cutoffs** on the free endpoint variables: the continuous linear map sending
`v` to the change-of-cutoff path `exp w • ∑ i, (χ i - χ' i) • v i`, as an element of `W^{1,p}`
(`TauCeti.WeakDerivStep.prev_cutoffChangeL_ae_eq`). -/
def cutoffChangeL (hw : ContDiff ℝ 1 w) (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hχ' : ∀ i, ContDiff ℝ 1 (χ' i)) (hsupp : ∀ i, HasCompactSupport (χ i - χ' i)) :
    (Π i, K i) →L[ℝ] WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :=
  LinearMap.toContinuousLinearMap
    { toFun v := (exists_prev_ae_eq_cutoffChangePath (p := p) hw hχ hχ' hsupp v).choose
      map_add' v v' := eq_choose_of_prev_ae_eq hw hχ hχ' hsupp <| by
        rw [prev_add, cutoffChangePath_add]
        exact (Lp.coeFn_add _ _).trans
          ((exists_prev_ae_eq_cutoffChangePath hw hχ hχ' hsupp v).choose_spec.add
            (exists_prev_ae_eq_cutoffChangePath hw hχ hχ' hsupp v').choose_spec)
      map_smul' c v := eq_choose_of_prev_ae_eq hw hχ hχ' hsupp <| by
        rw [RingHom.id_apply, prev_smul, cutoffChangePath_smul]
        exact (Lp.coeFn_smul _ _).trans
          ((exists_prev_ae_eq_cutoffChangePath hw hχ hχ' hsupp v).choose_spec.const_smul c) }

variable {hw : ContDiff ℝ 1 w} {hχ : ∀ i, ContDiff ℝ 1 (χ i)} {hχ' : ∀ i, ContDiff ℝ 1 (χ' i)}
  {hχ'' : ∀ i, ContDiff ℝ 1 (χ'' i)} {hsupp : ∀ i, HasCompactSupport (χ i - χ' i)}

/-- The change of cutoffs is represented by the change-of-cutoff path. -/
theorem prev_cutoffChangeL_ae_eq (v : Π i, K i) :
    ⇑(prev (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
      (cutoffChangeL hw hχ hχ' hsupp v)) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      cutoffChangePath w χ χ' v :=
  (exists_prev_ae_eq_cutoffChangePath (p := p) hw hχ hχ' hsupp v).choose_spec

/-- An element of `W^{1,p}` is the change of cutoffs of `v` as soon as it is represented by the
change-of-cutoff path. -/
theorem cutoffChangeL_eq_of_prev_ae_eq {v : Π i, K i}
    {u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    (hu : ⇑(prev (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] cutoffChangePath w χ χ' v) :
    cutoffChangeL hw hχ hχ' hsupp v = u :=
  eq_choose_of_prev_ae_eq hw hχ hχ' hsupp hu

/-- The change of cutoffs from a family of cutoffs to itself vanishes. -/
@[simp]
theorem cutoffChangeL_self {hsupp : ∀ i, HasCompactSupport (χ i - χ i)} :
    cutoffChangeL (p := p) (K := K) hw hχ hχ hsupp = 0 := by
  refine ContinuousLinearMap.ext fun v ↦ cutoffChangeL_eq_of_prev_ae_eq ?_
  rw [zero_apply, prev_zero, cutoffChangePath_self]
  exact Lp.coeFn_zero ..

/-- Changes of cutoffs add up. -/
theorem cutoffChangeL_add_cutoffChangeL {hsupp' : ∀ i, HasCompactSupport (χ' i - χ'' i)}
    {hsupp'' : ∀ i, HasCompactSupport (χ i - χ'' i)} :
    cutoffChangeL (p := p) (K := K) hw hχ hχ' hsupp + cutoffChangeL hw hχ' hχ'' hsupp' =
      cutoffChangeL hw hχ hχ'' hsupp'' := by
  refine ContinuousLinearMap.ext fun v ↦ (cutoffChangeL_eq_of_prev_ae_eq ?_).symm
  rw [add_apply, prev_add, ← cutoffChangePath_add_cutoffChangePath]
  exact (Lp.coeFn_add _ _).trans ((prev_cutoffChangeL_ae_eq v).add (prev_cutoffChangeL_ae_eq v))

/-- The negative of a change of cutoffs is the change of cutoffs back. -/
theorem neg_cutoffChangeL {hsupp' : ∀ i, HasCompactSupport (χ' i - χ i)} :
    -cutoffChangeL (p := p) (K := K) hw hχ hχ' hsupp = cutoffChangeL hw hχ' hχ hsupp' := by
  refine ContinuousLinearMap.ext fun v ↦ (cutoffChangeL_eq_of_prev_ae_eq ?_).symm
  rw [neg_apply, ← prevL_apply, map_neg, prevL_apply, cutoffChangePath_symm]
  exact (Lp.coeFn_neg _).trans (prev_cutoffChangeL_ae_eq v).neg

/-- **The weighted trajectory operator of the change of cutoffs.** For `AL` the class of
`A - deriv w • id`, the change of cutoffs of `v` is sent to the difference of the end tails of
`v` for the cutoffs `χ` and `χ'`. -/
theorem trajectoryOperator_cutoffChangeL
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - deriv w s • ContinuousLinearMap.id ℝ F)
    (hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) A v) p)
    (hmem' : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ' i) A v) p) (v : Π i, K i) :
    trajectoryOperator AL (cutoffChangeL hw hχ hχ' hsupp v) =
      endTailL w χ A hmem v - endTailL w χ' A hmem' v := by
  have hg : MemLp (fun s ↦ ∑ i, endTail w (χ i) A (v i) s - ∑ i, endTail w (χ' i) A (v i) s) p :=
    (memLp_finsetSum _ fun i _ ↦ hmem i (v i) (v i).property).sub
      (memLp_finsetSum _ fun i _ ↦ hmem' i (v i) (v i).property)
  obtain ⟨u, hDu, hu⟩ := exists_trajectoryOperator_ae_eq_of_hasDerivAt hAL
    (fun s ↦ hasDerivAt_cutoffChangePath (hw.differentiable one_ne_zero s).hasDerivAt
      (fun i ↦ (hχ i).differentiable one_ne_zero s)
      (fun i ↦ (hχ' i).differentiable one_ne_zero s) v)
    ((contDiff_cutoffChangePath hw hχ hχ' v).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_cutoffChangePath hsupp v)) hg
  rw [cutoffChangeL_eq_of_prev_ae_eq hu]
  refine Lp.ext ?_
  filter_upwards [hDu, Lp.coeFn_sub (endTailL w χ A hmem v) (endTailL w χ' A hmem' v),
    endTailL_apply_ae hmem v, endTailL_apply_ae hmem' v] with s h h₁ h₂ h₃
  rw [h, h₁, Pi.sub_apply, h₂, h₃]

/-- The **change of cutoffs** on the domain `W^{1,p} × ∏ i, K i` of the extended trajectory
operator: the shear `(ξ, v) ↦ (ξ + g, v)`, with `g` the change-of-cutoff path of `v`. It carries the
extended operator for the cutoffs `χ'` to the one for `χ`
(`TauCeti.WeakDerivStep.coprod_endTailL_comp_cutoffChangeEquiv`). -/
def cutoffChangeEquiv (hw : ContDiff ℝ 1 w) (hχ : ∀ i, ContDiff ℝ 1 (χ i))
    (hχ' : ∀ i, ContDiff ℝ 1 (χ' i)) (hsupp : ∀ i, HasCompactSupport (χ i - χ' i)) :
    (WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ×
        Π i, K i) ≃L[ℝ]
      (WeakDerivStep volume ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ×
          Π i, K i) :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (.id ℝ _ + (ContinuousLinearMap.inl ℝ _ _).comp
      ((cutoffChangeL hw hχ hχ' hsupp).comp (ContinuousLinearMap.snd ℝ _ _)))
    (.id ℝ _ - (ContinuousLinearMap.inl ℝ _ _).comp
      ((cutoffChangeL hw hχ hχ' hsupp).comp (ContinuousLinearMap.snd ℝ _ _)))
    (ContinuousLinearMap.ext fun x ↦ by simp) (ContinuousLinearMap.ext fun x ↦ by simp)

theorem cutoffChangeEquiv_apply
    (x : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ×
        Π i, K i) :
    cutoffChangeEquiv hw hχ hχ' hsupp x = (x.1 + cutoffChangeL hw hχ hχ' hsupp x.2, x.2) := by
  simp [cutoffChangeEquiv, Prod.ext_iff]

theorem cutoffChangeEquiv_symm_apply
    (x : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) ×
        Π i, K i) :
    (cutoffChangeEquiv hw hχ hχ' hsupp).symm x =
      (x.1 - cutoffChangeL hw hχ hχ' hsupp x.2, x.2) := by
  simp [cutoffChangeEquiv, Prod.ext_iff]

/-- **The extended operator does not depend on the cutoffs.** Let `AL` be the class of
`A - deriv w • id`, and `χ`, `χ'` two families of `C¹` cutoffs with `χ i - χ' i` compactly
supported. The extended operator for the cutoffs `χ'`, composed with the shear
`(ξ, v) ↦ (ξ + g, v)`, is the extended operator for the cutoffs `χ`. -/
theorem coprod_endTailL_comp_cutoffChangeEquiv
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ A s - deriv w s • ContinuousLinearMap.id ℝ F)
    (hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) A v) p)
    (hmem' : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ' i) A v) p) :
    ((trajectoryOperator AL).coprod (endTailL w χ' A hmem')).comp
        (cutoffChangeEquiv (p := p) (K := K) hw hχ hχ' hsupp).toContinuousLinearMap =
      (trajectoryOperator AL).coprod (endTailL w χ A hmem) := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, cutoffChangeEquiv_apply]
  simp only [ContinuousLinearMap.coprod_apply, map_add,
    trajectoryOperator_cutoffChangeL hAL hmem hmem']
  abel

/-- The change of cutoffs from a family of cutoffs to itself is the identity. -/
@[simp]
theorem cutoffChangeEquiv_self {hsupp : ∀ i, HasCompactSupport (χ i - χ i)} :
    cutoffChangeEquiv (p := p) (K := K) hw hχ hχ hsupp = ContinuousLinearEquiv.refl ℝ _ := by
  refine ContinuousLinearEquiv.ext (funext fun x ↦ ?_)
  rw [cutoffChangeEquiv_apply, cutoffChangeL_self]
  simp

/-- Changes of cutoffs compose. -/
theorem cutoffChangeEquiv_trans {hsupp' : ∀ i, HasCompactSupport (χ' i - χ'' i)}
    {hsupp'' : ∀ i, HasCompactSupport (χ i - χ'' i)} :
    (cutoffChangeEquiv (p := p) (K := K) hw hχ hχ' hsupp).trans
        (cutoffChangeEquiv hw hχ' hχ'' hsupp') =
      cutoffChangeEquiv hw hχ hχ'' hsupp'' := by
  refine ContinuousLinearEquiv.ext (funext fun x ↦ ?_)
  simp only [ContinuousLinearEquiv.trans_apply, cutoffChangeEquiv_apply]
  rw [add_assoc, ← cutoffChangeL_add_cutoffChangeL (hχ' := hχ') (hsupp := hsupp) (hsupp' := hsupp'),
    add_apply]

/-- The inverse of a change of cutoffs is the change of cutoffs back. -/
theorem cutoffChangeEquiv_symm {hsupp' : ∀ i, HasCompactSupport (χ' i - χ i)} :
    (cutoffChangeEquiv (p := p) (K := K) hw hχ hχ' hsupp).symm =
      cutoffChangeEquiv hw hχ' hχ hsupp' := by
  refine ContinuousLinearEquiv.ext (funext fun x ↦ ?_)
  rw [cutoffChangeEquiv_symm_apply, cutoffChangeEquiv_apply, sub_eq_add_neg,
    ← neg_cutoffChangeL (hsupp := hsupp), neg_apply]

section Consequences

variable {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
  (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
    fun s ↦ A s - deriv w s • ContinuousLinearMap.id ℝ F)
  (hmem : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ i) A v) p)
  (hmem' : ∀ i, ∀ v ∈ K i, MemLp (endTail w (χ' i) A v) p)

include hAL

/-- **The range of the extended operator does not depend on the cutoffs**, as long as they differ
on a compact set. -/
theorem range_coprod_endTailL_eq_of_hasCompactSupport_sub (hw : ContDiff ℝ 1 w)
    (hχ : ∀ i, ContDiff ℝ 1 (χ i)) (hχ' : ∀ i, ContDiff ℝ 1 (χ' i))
    (hsupp : ∀ i, HasCompactSupport (χ i - χ' i)) :
    ((trajectoryOperator AL).coprod (endTailL w χ A hmem)).range =
      ((trajectoryOperator AL).coprod (endTailL w χ' A hmem')).range := by
  rw [← coprod_endTailL_comp_cutoffChangeEquiv (hw := hw) (hχ := hχ) (hχ' := hχ') (hsupp := hsupp)
    hAL hmem hmem']
  exact LinearEquiv.range_comp (cutoffChangeEquiv hw hχ hχ' hsupp).toLinearEquiv _

/-- **The kernels of the extended operators correspond under the change of cutoffs**: the shear
`(ξ, v) ↦ (ξ + g, v)` maps the kernel for the cutoffs `χ` onto the kernel for the cutoffs `χ'`. -/
theorem map_ker_coprod_endTailL_cutoffChangeEquiv :
    ((trajectoryOperator AL).coprod (endTailL w χ A hmem)).ker.map
        (cutoffChangeEquiv (p := p) (K := K) hw hχ hχ' hsupp).toLinearEquiv.toLinearMap =
      ((trajectoryOperator AL).coprod (endTailL w χ' A hmem')).ker := by
  rw [← coprod_endTailL_comp_cutoffChangeEquiv (hw := hw) (hχ := hχ) (hχ' := hχ') (hsupp := hsupp)
    hAL hmem hmem']
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.ker_comp]
  exact Submodule.map_comap_eq_of_surjective
    (cutoffChangeEquiv (p := p) (K := K) hw hχ hχ' hsupp).surjective _

/-- **The index of the extended operator does not depend on the cutoffs**, as long as they differ
on a compact set. -/
theorem index_coprod_endTailL_eq_of_hasCompactSupport_sub (hw : ContDiff ℝ 1 w)
    (hχ : ∀ i, ContDiff ℝ 1 (χ i)) (hχ' : ∀ i, ContDiff ℝ 1 (χ' i))
    (hsupp : ∀ i, HasCompactSupport (χ i - χ' i)) :
    ((trajectoryOperator AL).coprod (endTailL w χ A hmem)).index =
      ((trajectoryOperator AL).coprod (endTailL w χ' A hmem')).index := by
  rw [← coprod_endTailL_comp_cutoffChangeEquiv (hw := hw) (hχ := hχ) (hχ' := hχ') (hsupp := hsupp)
    hAL hmem hmem', ContinuousLinearMap.index_comp_equiv]

/-- **Fredholmness of the extended operator does not depend on the cutoffs**, as long as they
differ on a compact set. -/
theorem isFredholm_coprod_endTailL_iff_of_hasCompactSupport_sub (hw : ContDiff ℝ 1 w)
    (hχ : ∀ i, ContDiff ℝ 1 (χ i)) (hχ' : ∀ i, ContDiff ℝ 1 (χ' i))
    (hsupp : ∀ i, HasCompactSupport (χ i - χ' i)) :
    ((trajectoryOperator AL).coprod (endTailL w χ A hmem)).IsFredholm ↔
      ((trajectoryOperator AL).coprod (endTailL w χ' A hmem')).IsFredholm := by
  rw [← coprod_endTailL_comp_cutoffChangeEquiv (hw := hw) (hχ := hχ) (hχ' := hχ') (hsupp := hsupp)
    hAL hmem hmem', ContinuousLinearMap.isFredholm_comp_equiv]

end Consequences

end WeakDerivStep

end TauCeti
