/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Inverse
public import TauCeti.Analysis.Complex.Beltrami.HigherHolder
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Analysis.Holder.Jet.Bounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Native inverse Hölder readings

The exponential and logarithm, locally invertible scalar families and the native higher-order
Beltrami solutions have bounded-open Hölder inverse readings. The examples also include independent
universes, infinite-dimensional complex coefficients, zero fibres and empty or disconnected domains.
-/

public section

noncomputable section

open Set Filter Metric TopologicalSpace
open scoped Topology NNReal ContDiff

namespace TauCeti.Examples.HolderInverse

/-- The actual logarithm has a native `C^{m+1,α}` reading near `exp 1`. -/
theorem logarithm_reading (m : ℕ) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ r > 0, ball (Real.exp 1) r ⊆ Ioi 0 ∧
      ∃ g : CkHolderSpaceOn (m + 1) α ⟨ball (Real.exp 1) r, isOpen_ball⟩ ℝ,
        ∀ x, g x = Real.log x := by
  have he : ⇑Real.expPartialHomeomorph = Real.exp :=
    funext Real.expPartialHomeomorph_apply
  have hC : ContDiffOn ℝ (m + 2) Real.exp univ := Real.contDiff_exp.contDiffOn
  obtain ⟨K, hK⟩ := hC.exists_holderOnWith_iteratedFDeriv isOpen_univ hα
    (isCompact_closedBall (1 : ℝ) 1) (subset_univ _)
  have hC' : ContDiffOn ℝ (m + 1) Real.expPartialHomeomorph (closedBall 1 1) := by
    rw [he]
    exact Real.contDiff_exp.contDiffOn
  have hK' : HolderOnWith K α (iteratedFDeriv ℝ (m + 1) Real.expPartialHomeomorph)
      (closedBall 1 1) := by simpa only [he] using hK
  have hd : fderiv ℝ Real.exp 1 = Real.exp 1 • ContinuousLinearMap.id ℝ ℝ :=
    ((hasFDerivAt_id (1 : ℝ)).exp).fderiv
  have hinv : (fderiv ℝ Real.expPartialHomeomorph 1).IsInvertible := by
    rw [he, hd]
    exact (ContinuousLinearMap.isInvertible_smul_iff (Real.exp_ne_zero 1)).2
      (ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ ℝ))
  have ha : (1 : ℝ) ∈ Real.expPartialHomeomorph.source := by
    simpa only [Real.expPartialHomeomorph_source] using (mem_univ (1 : ℝ))
  have h := Real.expPartialHomeomorph.exists_ckHolderSpaceOn_symm ha hC' hα
    (closedBall_mem_nhds 1 (by norm_num : (0 : ℝ) < 1)) hK' hinv
  have hinverse : ⇑Real.expPartialHomeomorph.symm = Real.log :=
    funext Real.expPartialHomeomorph_symm_apply
  rw [he, Real.expPartialHomeomorph_target, hinverse] at h
  exact h

/-- The logarithm reading takes the value `1` at the centre `exp 1`. -/
theorem logarithm_reading_at_centre (m : ℕ) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ r > 0, ∃ g : CkHolderSpaceOn (m + 1) α ⟨ball (Real.exp 1) r, isOpen_ball⟩ ℝ,
      ∃ h : Real.exp 1 ∈ ball (Real.exp 1) r, g ⟨Real.exp 1, h⟩ = 1 := by
  obtain ⟨r, hr, _, g, hg⟩ := logarithm_reading m hα
  refine ⟨r, hr, g, mem_ball_self hr, ?_⟩
  rw [hg, Real.log_exp]

/-- One constant controls all actual logarithm jets through the selected order. -/
theorem logarithm_jet_norm_bounds (m : ℕ) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ r > 0, ∃ M ≥ 0, ∀ i ≤ m + 1, ∀ x ∈ ball (Real.exp 1) r,
      ‖iteratedFDeriv ℝ i Real.log x‖ ≤ M := by
  obtain ⟨r, hr, _, g, hg⟩ := logarithm_reading m hα
  exact ⟨r, hr, ‖g‖, norm_nonneg _, fun i hi x hx ↦
    g.norm_iteratedFDeriv_apply_le (fun y ↦ (hg y).symm) hi ⟨x, hx⟩⟩

/-- The derivatives of this native forward map differ at `0` and `1`. -/
theorem exponential_derivatives_differ : fderiv ℝ Real.exp 0 ≠ fderiv ℝ Real.exp 1 := by
  intro h
  have h' := congrArg (fun L ↦ L 1) h
  have h0 : fderiv ℝ Real.exp 0 = Real.exp 0 • ContinuousLinearMap.id ℝ ℝ :=
    ((hasFDerivAt_id (0 : ℝ)).exp).fderiv
  have h1 : fderiv ℝ Real.exp 1 = Real.exp 1 • ContinuousLinearMap.id ℝ ℝ :=
    ((hasFDerivAt_id (1 : ℝ)).exp).fderiv
  rw [h0, h1] at h'
  have he : Real.exp 0 = Real.exp 1 := by simpa using h'
  exact (by norm_num : (0 : ℝ) ≠ 1) (Real.exp_injective he)

/-- A nonconstant operator family, invertible at `0` but singular at `-1`. -/
def affineFamily (x : ℝ) : ℝ →L[ℝ] ℝ := (1 + x) • ContinuousLinearMap.id ℝ ℝ

/-- The family is invertible at the base point. -/
theorem affineFamily_zero_isInvertible : (affineFamily 0).IsInvertible := by
  simpa [affineFamily] using (ContinuousLinearMap.isInvertible_equiv
    (f := ContinuousLinearEquiv.refl ℝ ℝ))

/-- The family fails to be invertible at `-1`. -/
theorem affineFamily_neg_one_not_isInvertible : ¬(affineFamily (-1)).IsInvertible := by
  rintro ⟨L, hL⟩
  have hz : L (1 : ℝ) = 0 := by
    simpa [affineFamily] using congrArg (fun f : ℝ →L[ℝ] ℝ ↦ f 1) hL
  exact (by norm_num : (1 : ℝ) ≠ 0) (L.injective (hz.trans L.map_zero.symm))

/-- Every finite order has a native inverse reading despite the singular member at `-1`. -/
theorem affineFamily_inverse_reading (n : ℕ) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ r > 0, ∃ g : CkHolderSpaceOn n α ⟨ball (0 : ℝ) r, isOpen_ball⟩ (ℝ →L[ℝ] ℝ),
      ∀ x, g x = (affineFamily x).inverse := by
  have hC : ContDiff ℝ (n + 1) affineFamily := by unfold affineFamily; fun_prop
  obtain ⟨K, hK⟩ := hC.contDiffOn.exists_holderOnWith_iteratedFDeriv isOpen_univ hα
    (isCompact_closedBall (0 : ℝ) 1) (subset_univ _)
  have hCn : ContDiffOn ℝ n affineFamily (ball 0 1) :=
    (hC.of_le (by simp)).contDiffOn
  obtain ⟨r, hr, _, _, g, hg⟩ := hCn.exists_ckHolderSpaceOn_clm_inverse
    (ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)) hα
    (hK.mono ball_subset_closedBall) affineFamily_zero_isInvertible
  exact ⟨r, hr, g, hg⟩

/-- Every small coefficient in the native higher-order Beltrami theorem gives an inverse-chart
reading of the same Hölder order, without additional coefficient regularity. -/
theorem higherHolder_inverse_reading (k : ℕ) {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ μ ∈ supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r),
      ‖μ‖ < δ → ∃ h ∈ supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r),
        ‖h‖ ≤ 2 * ‖μ‖ ∧
        let ψ : ℂ → ℂ := fun z ↦ z + cauchyTransform h z
        ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ (e : ℂ → ℂ) = ψ ∧
          (∀ z, conjWirtingerDeriv ψ z 1 = μ z * wirtingerDeriv ψ z 1) ∧
          ∃ ρ > 0, ball (ψ c) ρ ⊆ e.target ∧
            ∃ g : CkHolderSpaceOn (k + 1) α ⟨ball (ψ c) ρ, isOpen_ball⟩ ℂ,
              ∀ x, g x = e.symm x := by
  obtain ⟨δ, hδ, C, hsolve⟩ :=
    exists_ckHolder_conjWirtingerDeriv_eq_mul_wirtingerDeriv k hα hα1 c r
  refine ⟨δ, hδ, fun μ hμ hμδ ↦ ?_⟩
  obtain ⟨h, hh, hn, hψ, _, hpde, _, _, htop, hstrict⟩ := hsolve μ hμ hμδ
  let ψ : ℂ → ℂ := fun z ↦ z + cauchyTransform h z
  obtain ⟨L, hL⟩ := hstrict c (mem_closedBall_self hr.le)
  let e := hL.toOpenPartialHomeomorph ψ
  have he : (e : ℂ → ℂ) = ψ := hL.toOpenPartialHomeomorph_coe
  have hc : c ∈ e.source := hL.mem_toOpenPartialHomeomorph_source
  have hinv : (fderiv ℝ e c).IsInvertible := by
    rw [he]
    exact ⟨L, hL.hasFDerivAt.fderiv.symm⟩
  have hC : ContDiffOn ℝ (k + 1) e (closedBall c r) := by
    rw [he]
    exact hψ.contDiffOn
  have hH : HolderOnWith (C * ‖μ‖₊) α (iteratedFDeriv ℝ (k + 1) e) (closedBall c r) := by
    rw [he]
    exact htop
  obtain ⟨ρ, hρ, hρt, g, hg⟩ := e.exists_ckHolderSpaceOn_symm hc hC hα1.le
    (closedBall_mem_nhds c hr) hH hinv
  refine ⟨h, hh, hn, e, hc, he, hpde, ?_⟩
  simpa only [he] using ⟨ρ, hρ, hρt, g, hg⟩

universe u v w

/-- The continuous linear identification of two independently lifted complex lines. -/
def liftedLineEquiv : ULift.{v} ℂ ≃L[ℂ] ULift.{w} ℂ :=
  (ContinuousLinearEquiv.ulift : ULift.{v} ℂ ≃L[ℂ] ℂ).trans
    (ContinuousLinearEquiv.ulift : ULift.{w} ℂ ≃L[ℂ] ℂ).symm

/-- Parameter, domain and codomain occupy independent universes; the inverse reading carries
the image of the lifted value `1` back to `1`. -/
theorem lifted_inverse_reading (n : ℕ) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ r > 0, ∃ g : CkHolderSpaceOn n α ⟨ball (0 : ULift.{u} ℝ) r, isOpen_ball⟩
      (ULift.{w} ℂ →L[ℂ] ULift.{v} ℂ),
      ∀ x, g x (liftedLineEquiv.{v, w} (ULift.up 1)) = ULift.up 1 := by
  let L := liftedLineEquiv.{v, w}
  have hC : ContDiffOn ℝ n (fun _ : ULift.{u} ℝ ↦ (L : ULift.{v} ℂ →L[ℂ] ULift.{w} ℂ)) univ :=
    contDiffOn_const
  have hconst : HolderOnWith 0 α
      (iteratedFDeriv ℝ n (fun _ : ULift.{u} ℝ ↦
        (L : ULift.{v} ℂ →L[ℂ] ULift.{w} ℂ))) univ :=
    (holderWith_iteratedFDeriv_const (𝕜 := ℝ) (E' := ULift.{u} ℝ)
      n α (L : ULift.{v} ℂ →L[ℂ] ULift.{w} ℂ)).holderOnWith univ
  obtain ⟨r, hr, _, _, g, hg⟩ := hC.exists_ckHolderSpaceOn_clm_inverse (a := 0) Filter.univ_mem
    hα hconst ContinuousLinearMap.isInvertible_equiv
  refine ⟨r, hr, g, fun x ↦ ?_⟩
  rw [hg, ContinuousLinearMap.inverse_equiv]
  exact L.symm_apply_apply _

/-- The infinite-dimensional separable complex Hilbert space `ℓ²(ℕ)`. -/
abbrev CoefficientSpace := lp (fun _ : ℕ ↦ ℂ) 2

/-- An invertible, nonconstant complex-linear family on the infinite coefficient space. -/
def exponentialFamily (x : ℝ) : CoefficientSpace →L[ℂ] CoefficientSpace :=
  (Real.exp x : ℂ) • ContinuousLinearMap.id ℂ CoefficientSpace

/-- The first coordinate vector is nonzero in the coefficient space. -/
theorem coefficient_basis_ne_zero : (lp.single 2 0 (1 : ℂ) : CoefficientSpace) ≠ 0 := by
  intro h
  have h0 := congrArg (fun z : CoefficientSpace ↦ z 0) h
  simp at h0

/-- The parameter-one operator has the nontrivial scalar `exp 1` on the first coordinate. -/
theorem exponentialFamily_one_basis :
    exponentialFamily 1 (lp.single 2 0 (1 : ℂ)) 0 = (Real.exp 1 : ℂ) := by
  simp [exponentialFamily]

/-- Every finite order gives a complex-linear inverse reading on the infinite model; its
base-point reading fixes the nonzero first coordinate vector. -/
theorem infinite_inverse_reading (n : ℕ) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ r > 0, ∃ g : CkHolderSpaceOn n α ⟨ball (0 : ℝ) r, isOpen_ball⟩
      (CoefficientSpace →L[ℂ] CoefficientSpace),
      (∀ x, g x = (exponentialFamily x).inverse) ∧
      ∃ h : (0 : ℝ) ∈ ball 0 r, g ⟨0, h⟩ (lp.single 2 0 (1 : ℂ)) = lp.single 2 0 1 := by
  have hExp : ContDiff ℝ (n + 1) (fun x : ℝ ↦ (Real.exp x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_exp
  have hC : ContDiff ℝ (n + 1) exponentialFamily := hExp.smul contDiff_const
  obtain ⟨K, hK⟩ := hC.contDiffOn.exists_holderOnWith_iteratedFDeriv isOpen_univ hα
    (isCompact_closedBall (0 : ℝ) 1) (subset_univ _)
  have hCn : ContDiffOn ℝ n exponentialFamily (ball 0 1) := (hC.of_le (by simp)).contDiffOn
  have hinv : (exponentialFamily 0).IsInvertible := by
    simpa [exponentialFamily] using (ContinuousLinearMap.isInvertible_equiv
      (f := ContinuousLinearEquiv.refl ℂ CoefficientSpace))
  obtain ⟨r, hr, _, _, g, hg⟩ := hCn.exists_ckHolderSpaceOn_clm_inverse
    (ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)) hα (hK.mono ball_subset_closedBall) hinv
  refine ⟨r, hr, g, hg, mem_ball_self hr, ?_⟩
  rw [hg]
  simp [exponentialFamily]

/-- The parameter space may itself be infinite-dimensional. -/
theorem infinite_parameter_inverse_reading (n : ℕ) :
    ∃ r > 0, ∃ g : CkHolderSpaceOn n 1 ⟨ball (0 : CoefficientSpace) r, isOpen_ball⟩
      (ℂ →L[ℂ] ℂ), ∀ x, g x 1 = 1 := by
  let L := ContinuousLinearEquiv.refl ℂ ℂ
  have hC : ContDiffOn ℝ n (fun _ : CoefficientSpace ↦ (L : ℂ →L[ℂ] ℂ)) univ := contDiffOn_const
  obtain ⟨r, hr, _, _, g, hg⟩ := hC.exists_ckHolderSpaceOn_clm_inverse (a := 0) Filter.univ_mem
    le_rfl ((holderWith_iteratedFDeriv_const (𝕜 := ℝ) n 1 _).holderOnWith univ)
    ContinuousLinearMap.isInvertible_equiv
  refine ⟨r, hr, g, fun x ↦ ?_⟩
  rw [hg, ContinuousLinearMap.inverse_equiv]
  simp only [L, ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.refl_apply]

/-- Inverting the identity on the zero complex space also exercises the order-zero,
exponent-zero endpoint. -/
theorem zero_fibre_inverse_reading (n : ℕ) :
    ∃ r > 0, ∃ g : CkHolderSpaceOn n 0 ⟨ball (0 : ℝ) r, isOpen_ball⟩
      ((Fin 0 → ℂ) →L[ℂ] (Fin 0 → ℂ)), ∀ x, g x = 0 := by
  let L := ContinuousLinearEquiv.refl ℂ (Fin 0 → ℂ)
  have hC : ContDiffOn ℝ n (fun _ : ℝ ↦ (L : (Fin 0 → ℂ) →L[ℂ] (Fin 0 → ℂ))) univ :=
    contDiffOn_const
  obtain ⟨r, hr, _, _, g, hg⟩ := hC.exists_ckHolderSpaceOn_clm_inverse (a := 0) Filter.univ_mem
    (by norm_num : (0 : ℝ≥0) ≤ 1)
    ((holderWith_iteratedFDeriv_const (𝕜 := ℝ) n 0 _).holderOnWith univ)
    ContinuousLinearMap.isInvertible_equiv
  exact ⟨r, hr, g, fun x ↦ (hg x).trans (Subsingleton.elim _ _)⟩

/-- A zero-dimensional parameter space still gives a nonzero coefficient inverse reading. -/
theorem zero_parameter_inverse_reading (n : ℕ) :
    ∃ r > 0, ∃ g : CkHolderSpaceOn n 1 ⟨ball (0 : Fin 0 → ℝ) r, isOpen_ball⟩ (ℂ →L[ℂ] ℂ),
      ∃ h : (0 : Fin 0 → ℝ) ∈ ball 0 r, g ⟨0, h⟩ 1 = 1 := by
  let L := ContinuousLinearEquiv.refl ℂ ℂ
  have hC : ContDiffOn ℝ n (fun _ : Fin 0 → ℝ ↦ (L : ℂ →L[ℂ] ℂ)) univ := contDiffOn_const
  obtain ⟨r, hr, _, _, g, hg⟩ := hC.exists_ckHolderSpaceOn_clm_inverse (a := 0) Filter.univ_mem
    le_rfl ((holderWith_iteratedFDeriv_const (𝕜 := ℝ) n 1 _).holderOnWith univ)
    ContinuousLinearMap.isInvertible_equiv
  refine ⟨r, hr, g, mem_ball_self hr, ?_⟩
  rw [hg, ContinuousLinearMap.inverse_equiv]
  simp only [L, ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.refl_apply]

/-- Restricting the identity to any open domain gives inverse readings about every source point. -/
theorem identity_domain_inverse_reading (m : ℕ) {α : ℝ≥0} (hα : α ≤ 1)
    (U : Set ℝ) (hU : IsOpen U) {a : ℝ} (ha : a ∈ U) :
    ∃ r > 0, ball a r ⊆ U ∧
      ∃ g : CkHolderSpaceOn (m + 1) α ⟨ball a r, isOpen_ball⟩ ℝ, ∀ x, g x = x := by
  let e := OpenPartialHomeomorph.ofSet U hU
  have hpartial : e.toPartialEquiv = PartialEquiv.ofSet U :=
    OpenPartialHomeomorph.ofSet_toPartialEquiv hU
  have he : ⇑e = id := by
    calc
      ⇑e = ⇑e.toPartialEquiv := (OpenPartialHomeomorph.coe_toPartialEquiv e).symm
      _ = ⇑(PartialEquiv.ofSet U) :=
        congrArg (fun f : PartialEquiv ℝ ℝ ↦ (f : ℝ → ℝ)) hpartial
      _ = id := PartialEquiv.ofSet_coe U
  have hsource : e.source = U := OpenPartialHomeomorph.ofSet_source U hU
  have htarget : e.target = U := OpenPartialHomeomorph.ofSet_target U hU
  have hsymmObj : e.symm = e := OpenPartialHomeomorph.ofSet_symm hU
  have hsymm : ⇑e.symm = id :=
    (congrArg (fun f : OpenPartialHomeomorph ℝ ℝ ↦ (f : ℝ → ℝ)) hsymmObj).trans he
  have hC : ContDiffOn ℝ (m + 2) e univ := by
    rw [he]
    exact contDiff_id.contDiffOn
  obtain ⟨K, hK⟩ := hC.exists_holderOnWith_iteratedFDeriv isOpen_univ hα
    (isCompact_closedBall a 1) (subset_univ _)
  have hd : HasFDerivAt e (ContinuousLinearMap.id ℝ ℝ) a := by
    rw [he]
    exact hasFDerivAt_id a
  have hinv : (fderiv ℝ e a).IsInvertible := by
    rw [hd.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ ℝ)
  have ha' : a ∈ e.source := by simpa only [hsource] using ha
  have hC' : ContDiffOn ℝ (m + 1) e (closedBall a 1) := by
    rw [he]
    exact contDiff_id.contDiffOn
  have h := e.exists_ckHolderSpaceOn_symm ha' hC' hα
    (closedBall_mem_nhds a (by norm_num : (0 : ℝ) < 1)) hK hinv
  rw [he, htarget, hsymm, id_eq] at h
  exact h

/-- The empty original source is allowed without a nonemptiness hypothesis. -/
theorem empty_domain_inverse_reading (m : ℕ) {α : ℝ≥0} (hα : α ≤ 1) :
    ∀ a ∈ (∅ : Set ℝ), ∃ r > 0, ball a r ⊆ ∅ ∧
      ∃ g : CkHolderSpaceOn (m + 1) α ⟨ball a r, isOpen_ball⟩ ℝ, ∀ x, g x = x := by
  intro a ha
  exact identity_domain_inverse_reading m hα ∅ isOpen_empty ha

/-- The native empty-domain Hölder carrier is obtained by restricting an inverse reading. -/
theorem empty_carrier_inverse_reading (m : ℕ) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ g : CkHolderSpaceOn (m + 1) α (⊥ : Opens ℝ) ℝ, ∀ x, g x = x := by
  obtain ⟨r, _, _, g, hg⟩ := identity_domain_inverse_reading m hα univ isOpen_univ (mem_univ 0)
  let h : (⊥ : Opens ℝ) ≤ ⟨ball (0 : ℝ) r, isOpen_ball⟩ := bot_le
  refine ⟨CkHolderSpaceOn.restrictL h g, fun x ↦ ?_⟩
  rw [CkHolderSpaceOn.restrictL_apply]
  exact hg _

/-- The disconnected open domain used for two separate nonzero inverse readings. -/
def disconnectedDomain : Set ℝ := Iio (-1) ∪ Ioi 1

private theorem isOpen_disconnectedDomain : IsOpen disconnectedDomain :=
  isOpen_Iio.union isOpen_Ioi

/-- The left component contains a nonzero centre with an inverse reading. -/
theorem disconnected_left_inverse_reading (m : ℕ) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ r > 0, ball (-2 : ℝ) r ⊆ disconnectedDomain ∧
      ∃ g : CkHolderSpaceOn (m + 1) α ⟨ball (-2 : ℝ) r, isOpen_ball⟩ ℝ,
        ∃ h : (-2 : ℝ) ∈ ball (-2) r, g ⟨-2, h⟩ = -2 := by
  obtain ⟨r, hr, hrs, g, hg⟩ := identity_domain_inverse_reading m hα disconnectedDomain
    isOpen_disconnectedDomain (Or.inl (by norm_num : (-2 : ℝ) < -1))
  exact ⟨r, hr, hrs, g, mem_ball_self hr, hg _⟩

/-- The right component contains a distinct nonzero centre with an inverse reading. -/
theorem disconnected_right_inverse_reading (m : ℕ) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ r > 0, ball (2 : ℝ) r ⊆ disconnectedDomain ∧
      ∃ g : CkHolderSpaceOn (m + 1) α ⟨ball (2 : ℝ) r, isOpen_ball⟩ ℝ,
        ∃ h : (2 : ℝ) ∈ ball 2 r, g ⟨2, h⟩ = 2 := by
  obtain ⟨r, hr, hrs, g, hg⟩ := identity_domain_inverse_reading m hα disconnectedDomain
    isOpen_disconnectedDomain (Or.inr (by norm_num : (1 : ℝ) < 2))
  exact ⟨r, hr, hrs, g, mem_ball_self hr, hg _⟩

end TauCeti.Examples.HolderInverse
