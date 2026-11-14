/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Smooth
public import TauCeti.Geometry.Symplectic.PolarCompatible

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# The canonical unitary transport between compatible complex structures

Let `E` be a finite-dimensional real inner product space carrying a symplectic form `ω` and an
`ω`-compatible complex structure `J₀` whose metric is the inner product of `E`:
`ω(u, J₀ v) = ⟪u, v⟫`. Every other `ω`-compatible complex structure `J` has its own metric
`g_J = ω(·, J ·)`, and the canonical change of metric from `⟪·, ·⟫` to `g_J` is the inverse square
root `T_J = H^(-1/2)` of the Riesz operator `H` of `g_J`
(`ContinuousLinearMap.metricChangeTransport`). This file shows that `T_J` is a unitary
isomorphism from `(E, ω, J₀)` to `(E, ω, J)`
(`SymplecticForm.unitaryTransport`):

* it carries `J₀` to `J`, `T_J ∘ J₀ = J ∘ T_J`
  (`SymplecticForm.unitaryTransport_apply_eq_apply_unitaryTransport`);
* it preserves `ω` (`SymplecticForm.apply_unitaryTransport_unitaryTransport`);
* it is an isometry from `⟪·, ·⟫` to `g_J`
  (`SymplecticForm.apply_unitaryTransport_apply_unitaryTransport`);
* it is the identity at `J = J₀` (`SymplecticForm.unitaryTransport_eq_one`);
* it depends smoothly, indeed analytically, on `J`: a smooth family of compatible structures has
  a smooth family of unitary transports (`ContDiffOn.unitaryTransport`), and likewise for
  continuous and differentiable families (`ContinuousOn.unitaryTransport`,
  `DifferentiableWithinAt.unitaryTransport`).

The Riesz operator of `g_J` is `H = -J₀ J`
(`SymplecticForm.continuousLinearMapOfBilin_associatedBilinForm`), and the key identity is
`H J₀ H = J₀`, which says that conjugation by `J₀` inverts `H`. Hence
`J₀ H^(1/2) J₀⁻¹` is a positive square root of `H⁻¹`, so it is `T_J`, and then
`T_J J₀ = J₀ H^(1/2) = J₀ H T_J = J T_J`. Preservation of `ω` follows, since
`ω(u, v) = g_J(u, -J v)` and `ω(u, v) = ⟪u, -J₀ v⟫`.

Since `T_J` is a function of `J` alone, a family of compatible structures `J_t` that is periodic in
`t` gives a periodic family `T_{J_t}` of unitary frames, as smooth in `t` as `J_t` is. Such a
frame trivializes the symplectic vector bundle along a loop with its complex structures, and it is
used to reduce the linearized Floer operator along an orbit, whose complex structures `J_t` vary
with `t`, to an operator with the constant complex structure `J₀`.

## Main definitions

* `TauCeti.SymplecticForm.unitaryTransport ω J`: the operator `T_J`.
* `TauCeti.SymplecticForm.unitaryTransportEquiv`: `T_J` as a continuous linear equivalence, for
  compatible `J`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford Graduate
  Texts in Mathematics 27, Oxford University Press, 2017, Section 2.5 (compatible complex
  structures, the factorization `J = J₀ H` with `H` positive and symplectic, and unitary frames
  of a compatible pair).
-/

public section

open InnerProductSpace


namespace TauCeti

namespace SymplecticForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ω : SymplecticForm E} {J₀ J : AlmostComplexStructure E}

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

/-- The **unitary transport** of a complex structure `J`: the canonical change of metric
`H^(-1/2)` from the inner product of `E` to the metric `g_J = ω(·, J ·)`, where `H` is the Riesz
operator of `g_J`. When the inner product is the metric of an `ω`-compatible structure `J₀` and
`J` is `ω`-compatible, it is a symplectic isomorphism carrying `J₀` to `J`
(`SymplecticForm.unitaryTransport_apply_eq_apply_unitaryTransport`,
`SymplecticForm.apply_unitaryTransport_unitaryTransport`). -/
noncomputable def unitaryTransport (ω : SymplecticForm E) (J : AlmostComplexStructure E) :
    E →L[ℝ] E :=
  (ω.associatedBilinForm J).toContinuousBilinearMap.metricChangeTransport

theorem unitaryTransport_def (ω : SymplecticForm E) (J : AlmostComplexStructure E) :
    ω.unitaryTransport J =
      (ω.associatedBilinForm J).toContinuousBilinearMap.metricChangeTransport :=
  (rfl)

section Reference

variable (hJ₀ : ∀ u v, ω u (J₀ v) = ⟪u, v⟫_ℝ)
include hJ₀

/-- If the inner product of `E` is the metric `ω(·, J₀ ·)` of a complex structure `J₀`, then the
Riesz operator of the metric `g_J = ω(·, J ·)` of a complex structure `J` preserving `ω` is
`-J₀ J`. -/
theorem continuousLinearMapOfBilin_associatedBilinForm (hJ : ω.Invariant J) :
    (ω.associatedBilinForm J).toContinuousBilinearMap♯ =
      -(LinearMap.toContinuousLinearMap J₀.toLinearMap *
        LinearMap.toContinuousLinearMap J.toLinearMap) := by
  ext u
  refine ext_inner_right ℝ fun w ↦ ?_
  have h := ω.inner_apply_eq_of_apply_apply_eq_inner hJ₀ (J u) w
  rw [continuousLinearMapOfBilin_apply, LinearMap.toContinuousBilinearMap_apply,
    associatedBilinForm_apply]
  simp only [neg_apply, mul_apply_eq_comp, LinearMap.coe_toContinuousLinearMap', inner_neg_left, h]
  rw [ω.neg_eq]
  exact hJ.associatedBilinForm_apply_swap u w

end Reference

/-- The Riesz operator of the metric `g_J = ω(·, J ·)` of an `ω`-compatible structure is strictly
positive. -/
theorem Compatible.isStrictlyPositive_continuousLinearMapOfBilin (hJ : ω.Compatible J) :
    IsStrictlyPositive (ω.associatedBilinForm J).toContinuousBilinearMap♯ :=
  isStrictlyPositive_continuousLinearMapOfBilin_iff.2 <| by
    simp only [LinearMap.toContinuousBilinearMap_apply, associatedBilinForm_apply]
    exact ⟨hJ.associatedBilinForm_apply_swap, fun _ hv ↦ hJ.associated_pos hv⟩

/-- The unitary transport of an `ω`-compatible structure as a continuous linear equivalence, whose
inverse is the positive square root of the Riesz operator of `g_J = ω(·, J ·)`. -/
noncomputable def unitaryTransportEquiv (hJ : ω.Compatible J) : E ≃L[ℝ] E :=
  (ω.associatedBilinForm J).toContinuousBilinearMap.metricChangeEquiv
    hJ.isStrictlyPositive_continuousLinearMapOfBilin

@[simp]
theorem coe_unitaryTransportEquiv (hJ : ω.Compatible J) :
    (unitaryTransportEquiv hJ : E →L[ℝ] E) = ω.unitaryTransport J :=
  ContinuousLinearMap.coe_metricChangeEquiv _

@[simp]
theorem unitaryTransportEquiv_apply (hJ : ω.Compatible J) (v : E) :
    unitaryTransportEquiv hJ v = ω.unitaryTransport J v :=
  ContinuousLinearMap.metricChangeEquiv_apply _ v

/-- The inverse of the unitary transport is the positive square root of the Riesz operator of
`g_J = ω(·, J ·)`. -/
theorem coe_unitaryTransportEquiv_symm (hJ : ω.Compatible J) :
    ((unitaryTransportEquiv hJ).symm : E →L[ℝ] E) =
      CFC.sqrt (ω.associatedBilinForm J).toContinuousBilinearMap♯ :=
  ContinuousLinearMap.coe_metricChangeEquiv_symm _

/-- Evaluation of the inverse of the unitary transport. -/
theorem unitaryTransportEquiv_symm_apply (hJ : ω.Compatible J) (v : E) :
    (unitaryTransportEquiv hJ).symm v =
      CFC.sqrt (ω.associatedBilinForm J).toContinuousBilinearMap♯ v :=
  ContinuousLinearMap.metricChangeEquiv_symm_apply _ v

@[simp]
theorem unitaryTransportEquiv_symm_apply_unitaryTransport (hJ : ω.Compatible J) (v : E) :
    (unitaryTransportEquiv hJ).symm (ω.unitaryTransport J v) = v := by
  rw [← unitaryTransportEquiv_apply hJ, ContinuousLinearEquiv.symm_apply_apply]

@[simp]
theorem unitaryTransport_unitaryTransportEquiv_symm_apply (hJ : ω.Compatible J) (v : E) :
    ω.unitaryTransport J ((unitaryTransportEquiv hJ).symm v) = v := by
  rw [← unitaryTransportEquiv_apply hJ, ContinuousLinearEquiv.apply_symm_apply]

@[simp]
theorem unitaryTransportEquiv_symm_mul_unitaryTransport (hJ : ω.Compatible J) :
    ((unitaryTransportEquiv hJ).symm : E →L[ℝ] E) * ω.unitaryTransport J = 1 := by
  ext v
  simp

@[simp]
theorem unitaryTransport_mul_unitaryTransportEquiv_symm (hJ : ω.Compatible J) :
    ω.unitaryTransport J * ((unitaryTransportEquiv hJ).symm : E →L[ℝ] E) = 1 := by
  ext v
  simp

/-- The unitary transport of an `ω`-compatible structure is a strictly positive operator. -/
theorem Compatible.isStrictlyPositive_unitaryTransport (hJ : ω.Compatible J) :
    IsStrictlyPositive (ω.unitaryTransport J) :=
  ContinuousLinearMap.isStrictlyPositive_metricChangeTransport
    hJ.isStrictlyPositive_continuousLinearMapOfBilin

/-- **The unitary transport is an isometry** from the inner product of `E` to the metric
`g_J = ω(·, J ·)` of an `ω`-compatible structure. -/
@[simp]
theorem apply_unitaryTransport_apply_unitaryTransport (hJ : ω.Compatible J) (u v : E) :
    ω (ω.unitaryTransport J u) (J (ω.unitaryTransport J v)) = ⟪u, v⟫_ℝ := by
  simpa only [unitaryTransport_def, LinearMap.toContinuousBilinearMap_apply,
    associatedBilinForm_apply] using
    ContinuousLinearMap.apply_metricChangeTransport_metricChangeTransport
      hJ.isStrictlyPositive_continuousLinearMapOfBilin u v

section Reference

variable (hJ₀ : ∀ u v, ω u (J₀ v) = ⟪u, v⟫_ℝ)
include hJ₀

/-- If the inner product of `E` is the metric `ω(·, J₀ ·)` of `J₀`, then the unitary transport of
`J₀` itself is the identity. -/
@[simp]
theorem unitaryTransport_eq_one : ω.unitaryTransport J₀ = 1 := by
  have h : (ω.associatedBilinForm J₀).toContinuousBilinearMap = innerSL ℝ := by
    ext u v
    rw [LinearMap.toContinuousBilinearMap_apply, associatedBilinForm_apply, hJ₀,
      innerSL_apply_apply]
  rw [unitaryTransport_def, h, ContinuousLinearMap.metricChangeTransport_innerSL]

/-- **The unitary transport intertwines the complex structures**, as an identity of operators:
if the inner product of `E` is the metric `ω(·, J₀ ·)` of `J₀` and `J` is `ω`-compatible, then
`T_J ∘ J₀ = J ∘ T_J`. -/
theorem unitaryTransport_mul_toContinuousLinearMap (hJ : ω.Compatible J) :
    ω.unitaryTransport J * LinearMap.toContinuousLinearMap J₀.toLinearMap =
      LinearMap.toContinuousLinearMap J.toLinearMap * ω.unitaryTransport J := by
  set A := LinearMap.toContinuousLinearMap J₀.toLinearMap
  set B := LinearMap.toContinuousLinearMap J.toLinearMap
  set H := (ω.associatedBilinForm J).toContinuousBilinearMap♯
  have hpos := hJ.isStrictlyPositive_continuousLinearMapOfBilin
  have hH : H = -(A * B) := continuousLinearMapOfBilin_associatedBilinForm hJ₀ hJ.invariant
  have hAA : A * A = -1 := AlmostComplexStructure.toContinuousLinearMap_mul_self J₀
  have hBB : B * B = -1 := AlmostComplexStructure.toContinuousLinearMap_mul_self J
  -- Conjugation by `J₀` inverts `H`: `X = J₀ H J₀ = J J₀` satisfies `H X = X H = -1`.
  set X := A * H * A
  have hX : X = B * A := by
    simp only [X, hH, mul_neg, neg_mul, ← mul_assoc, hAA, neg_neg, one_mul]
  have hHX : H * X = -1 := by
    rw [hX, hH, neg_mul, show A * B * (B * A) = A * (B * B) * A by simp only [mul_assoc], hBB]
    simp [hAA]
  have hXH : X * H = -1 := by
    rw [hX, hH, mul_neg, show B * A * (A * B) = B * (A * A) * B by simp only [mul_assoc], hAA]
    simp [hBB]
  have hRX : Commute (CFC.sqrt H) X := by
    rw [CFC.sqrt_eq_rpow, CFC.rpow_def]
    exact Commute.cfc_nnreal (hHX.trans hXH.symm) _
  set R := CFC.sqrt H
  have hRR : R * R = H := CFC.sqrt_mul_sqrt_self H hpos.nonneg
  -- The candidate `J₀ R J₀⁻¹ = -J₀ R J₀` for `T_J`.
  have hT : ω.unitaryTransport J = -(A * R * A) := by
    refine (ContinuousLinearMap.metricChangeTransport_eq_iff hpos).2 ⟨?_, ?_⟩
    · have hconj := (ContinuousLinearMap.nonneg_iff_isPositive.1 (CFC.sqrt_nonneg H)).conj_adjoint A
      rw [ω.adjoint_eq_neg_of_forall_inner_apply_eq (A := A)
        (ω.inner_apply_eq_of_apply_apply_eq_inner hJ₀)] at hconj
      rw [ContinuousLinearMap.nonneg_iff_isPositive]
      convert hconj using 1
      simp only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_assoc, R, A]
    · have h₁ : R * X * R = -1 := by
        rw [hRX.eq, mul_assoc, hRR, hXH]
      calc -(A * R * A) * H * -(A * R * A) = A * (R * X * R) * A := by
            simp only [X]
            noncomm_ring
        _ = 1 := by rw [h₁]; simp [hAA]
  have hRT : R * ω.unitaryTransport J = 1 :=
    ContinuousLinearMap.sqrt_mul_metricChangeTransport hpos
  have hB : B = A * H := by rw [hH, mul_neg, ← mul_assoc, hAA]; simp
  calc ω.unitaryTransport J * A = A * R := by rw [hT]; simp [mul_assoc, hAA]
    _ = A * R * (R * ω.unitaryTransport J) := by rw [hRT, mul_one]
    _ = B * ω.unitaryTransport J := by rw [hB, ← hRR]; noncomm_ring

/-- **The unitary transport is complex linear** from `(E, J₀)` to `(E, J)`: if the inner product
of `E` is the metric `ω(·, J₀ ·)` of `J₀` and `J` is `ω`-compatible, then
`T_J (J₀ v) = J (T_J v)`. -/
theorem unitaryTransport_apply_eq_apply_unitaryTransport (hJ : ω.Compatible J) (v : E) :
    ω.unitaryTransport J (J₀ v) = J (ω.unitaryTransport J v) := by
  simpa using congr($(unitaryTransport_mul_toContinuousLinearMap hJ₀ hJ) v)

/-- If the inner product of `E` is the metric `ω(·, J₀ ·)` of `J₀` and `J` is `ω`-compatible, then
the unitary transport is complex linear from `(E, J₀)` to `(E, J)`. -/
theorem isComplexLinearMap_unitaryTransport (hJ : ω.Compatible J) :
    IsComplexLinearMap J₀ J (ω.unitaryTransport J : E →ₗ[ℝ] E) :=
  (isComplexLinearMap_iff_apply _ _ _).2 (unitaryTransport_apply_eq_apply_unitaryTransport hJ₀ hJ)

/-- **The unitary transport is symplectic**: if the inner product of `E` is the metric
`ω(·, J₀ ·)` of `J₀` and `J` is `ω`-compatible, then the unitary transport preserves `ω`. -/
theorem apply_unitaryTransport_unitaryTransport (hJ : ω.Compatible J) (u v : E) :
    ω (ω.unitaryTransport J u) (ω.unitaryTransport J v) = ω u v := by
  -- `ω(a, b) = g_J(a, -J b)`, and `-J (T v) = T (-J₀ v)`.
  have h : ω.unitaryTransport J v = J (ω.unitaryTransport J (-J₀ v)) := by
    rw [map_neg, unitaryTransport_apply_eq_apply_unitaryTransport hJ₀ hJ, map_neg,
      AlmostComplexStructure.apply_apply, neg_neg]
  rw [h, apply_unitaryTransport_apply_unitaryTransport hJ, ← hJ₀, map_neg,
    AlmostComplexStructure.apply_apply, neg_neg]

/-- **The inverse unitary transport is complex linear** from `(E, J)` to `(E, J₀)`: if the inner
product of `E` is the metric `ω(·, J₀ ·)` of `J₀` and `J` is `ω`-compatible, then
`T_J⁻¹ (J v) = J₀ (T_J⁻¹ v)`. -/
theorem unitaryTransportEquiv_symm_apply_eq_apply_unitaryTransportEquiv_symm
    (hJ : ω.Compatible J) (v : E) :
    (unitaryTransportEquiv hJ).symm (J v) = J₀ ((unitaryTransportEquiv hJ).symm v) := by
  conv_lhs => rw [← unitaryTransport_unitaryTransportEquiv_symm_apply hJ v,
    ← unitaryTransport_apply_eq_apply_unitaryTransport hJ₀ hJ]
  exact unitaryTransportEquiv_symm_apply_unitaryTransport hJ _

/-- **The inverse unitary transport is symplectic**: if the inner product of `E` is the metric
`ω(·, J₀ ·)` of `J₀` and `J` is `ω`-compatible, then `T_J⁻¹` preserves `ω`. -/
theorem apply_unitaryTransportEquiv_symm_unitaryTransportEquiv_symm (hJ : ω.Compatible J)
    (u v : E) :
    ω ((unitaryTransportEquiv hJ).symm u) ((unitaryTransportEquiv hJ).symm v) = ω u v := by
  rw [← apply_unitaryTransport_unitaryTransport hJ₀ hJ,
    unitaryTransport_unitaryTransportEquiv_symm_apply,
    unitaryTransport_unitaryTransportEquiv_symm_apply]

end Reference

/-- **The inverse unitary transport is an isometry** from the metric `g_J = ω(·, J ·)` of an
`ω`-compatible structure to the inner product of `E`. -/
theorem inner_unitaryTransportEquiv_symm_unitaryTransportEquiv_symm (hJ : ω.Compatible J)
    (u v : E) :
    ⟪(unitaryTransportEquiv hJ).symm u, (unitaryTransportEquiv hJ).symm v⟫_ℝ = ω u (J v) := by
  rw [← apply_unitaryTransport_apply_unitaryTransport hJ,
    unitaryTransport_unitaryTransportEquiv_symm_apply,
    unitaryTransport_unitaryTransportEquiv_symm_apply]

end SymplecticForm

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ω : SymplecticForm E}

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

/-- The metric `g_J = ω(·, J ·)` is a continuous linear function of the operator `J`. -/
private theorem toContinuousBilinearMap_associatedBilinForm_eq (ω : SymplecticForm E)
    (J : AlmostComplexStructure E) :
    (ω.associatedBilinForm J).toContinuousBilinearMap =
      (ContinuousLinearMap.compL ℝ E E ℝ).flip (LinearMap.toContinuousLinearMap J.toLinearMap) ∘L
        ω.toBilinForm.toContinuousBilinearMap := by
  ext u v
  simp

section Continuous

variable {X : Type*} [TopologicalSpace X] {s : Set X} {J : X → AlmostComplexStructure E}

/-- **The unitary transport depends continuously on the complex structure.** A continuous family
of `ω`-compatible complex structures has a continuous family of unitary transports. -/
theorem _root_.ContinuousOn.unitaryTransport (hJ : ContinuousOn J s)
    (hc : ∀ x ∈ s, ω.Compatible (J x)) :
    ContinuousOn (fun x ↦ ω.unitaryTransport (J x)) s := by
  have hJ' : ContinuousOn (fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) s :=
    AlmostComplexStructure.isEmbedding_toContinuousLinearMap.continuous.comp_continuousOn hJ
  have hg : ContinuousOn (fun x ↦ (ω.associatedBilinForm (J x)).toContinuousBilinearMap) s := by
    simp only [toContinuousBilinearMap_associatedBilinForm_eq]
    exact ((ContinuousLinearMap.compL ℝ E E ℝ).flip.continuous.comp_continuousOn hJ').clm_comp
      continuousOn_const
  exact ContinuousLinearMap.continuousOn_metricChangeTransport.comp hg fun x hx ↦
    (hc x hx).isStrictlyPositive_continuousLinearMapOfBilin

/-- A continuous family of `ω`-compatible complex structures has a continuous family of unitary
transports. -/
theorem _root_.Continuous.unitaryTransport (hJ : Continuous J) (hc : ∀ x, ω.Compatible (J x)) :
    Continuous fun x ↦ ω.unitaryTransport (J x) :=
  continuousOn_univ.1 <| hJ.continuousOn.unitaryTransport fun x _ ↦ hc x

end Continuous

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {s : Set P} {x : P}
  {J : P → AlmostComplexStructure E} {n : WithTop ℕ∞}

/-- **The unitary transport depends differentiably on the complex structure.** If a family of
complex structures, `ω`-compatible on `s` and at `x`, is differentiable within `s` at `x` in the
operator norm, then so is its family of unitary transports. -/
theorem _root_.DifferentiableWithinAt.unitaryTransport
    (hJ : DifferentiableWithinAt ℝ (fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) s x)
    (hc : ∀ y ∈ s, ω.Compatible (J y)) (hx : ω.Compatible (J x)) :
    DifferentiableWithinAt ℝ (fun x ↦ ω.unitaryTransport (J x)) s x := by
  have hg : DifferentiableWithinAt ℝ
      (fun x ↦ (ω.associatedBilinForm (J x)).toContinuousBilinearMap) s x := by
    simp only [toContinuousBilinearMap_associatedBilinForm_eq]
    exact ((ContinuousLinearMap.compL ℝ E E ℝ).flip.differentiableAt.comp_differentiableWithinAt
      x hJ).clm_comp (differentiableWithinAt_const _)
  exact (((ContinuousLinearMap.contDiffOn_metricChangeTransport (n := 1)).differentiableOn
    one_ne_zero) _ hx.isStrictlyPositive_continuousLinearMapOfBilin).comp x hg fun y hy ↦
      (hc y hy).isStrictlyPositive_continuousLinearMapOfBilin

/-- A family of `ω`-compatible complex structures that is differentiable at `x` in the operator
norm has a family of unitary transports differentiable at `x`. -/
theorem _root_.DifferentiableAt.unitaryTransport
    (hJ : DifferentiableAt ℝ (fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) x)
    (hc : ∀ y, ω.Compatible (J y)) :
    DifferentiableAt ℝ (fun x ↦ ω.unitaryTransport (J x)) x :=
  differentiableWithinAt_univ.1 <|
    hJ.differentiableWithinAt.unitaryTransport (fun y _ ↦ hc y) (hc x)

/-- A differentiable family of `ω`-compatible complex structures has a differentiable family of
unitary transports. -/
theorem _root_.Differentiable.unitaryTransport
    (hJ : Differentiable ℝ fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap)
    (hc : ∀ y, ω.Compatible (J y)) :
    Differentiable ℝ fun x ↦ ω.unitaryTransport (J x) :=
  fun x ↦ (hJ x).unitaryTransport hc

/-- **The unitary transport depends smoothly on the complex structure.** A family of
`ω`-compatible complex structures that is `C^n` in the operator norm has a `C^n` family of unitary
transports. -/
theorem _root_.ContDiffOn.unitaryTransport
    (hJ : ContDiffOn ℝ n (fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) s)
    (hc : ∀ x ∈ s, ω.Compatible (J x)) :
    ContDiffOn ℝ n (fun x ↦ ω.unitaryTransport (J x)) s := by
  have hg : ContDiffOn ℝ n
      (fun x ↦ (ω.associatedBilinForm (J x)).toContinuousBilinearMap) s := by
    simp only [toContinuousBilinearMap_associatedBilinForm_eq]
    exact ((ContinuousLinearMap.compL ℝ E E ℝ).flip.contDiff.comp_contDiffOn hJ).clm_comp
      (contDiffOn_const (c := ω.toBilinForm.toContinuousBilinearMap))
  exact hg.metricChangeTransport fun x hx ↦ (hc x hx).isStrictlyPositive_continuousLinearMapOfBilin

/-- A `C^n` family of `ω`-compatible complex structures has a `C^n` family of unitary
transports. -/
theorem _root_.ContDiff.unitaryTransport
    (hJ : ContDiff ℝ n fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap)
    (hc : ∀ x, ω.Compatible (J x)) :
    ContDiff ℝ n fun x ↦ ω.unitaryTransport (J x) :=
  contDiffOn_univ.1 <| hJ.contDiffOn.unitaryTransport fun x _ ↦ hc x

end Smooth

end TauCeti
