/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.Flat.Operator
public import TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Basic
public import TauCeti.Analysis.PDE.SeibergWitten.Normal.Frame
public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed

/-!
# Normal intertwining for the gauge-fixed flat Seiberg–Witten operator

On an abstract oriented four-dimensional real inner product space `V` with almost complex structure
`J`, an adapted orthonormal frame `e` splits `V` into tangential and normal complex planes via
`normalCoord e : V → ℂ`. Pulling back an arbitrary plane field `x : ℂ → ℝ⁴` (with no regularity or
PDE hypothesis on `x`) gives the canonical-line background
`(normalConnection e x, normalModelSpinor e u₀ x 0)`.

This file defines the eight-component normal model operator
`normalModelOperator x w = (L_x (Prod.fst ∘ w), L_x* (Prod.snd ∘ w))` and its formal `L²` adjoint
`normalModelAdjoint`, relates `normalDomainEquiv` pointwise to `(normalModelConnection e y (-η),
normalModelSpinor e u₀ y (-η))` (`normalDomainEquiv_apply_normalCoord`), and proves
(`gaugeFixedFlatOperator_normalPerturbation`) that for any background `x` and any perturbation
`w : ℂ → ℝ⁴ × ℝ⁴` differentiable at `normalCoord e p`, applying `gaugeFixedFlatOperator` at the
pulled-back background to the pointwise pullback of `w` through `normalDomainEquiv` equals
`normalTargetEquiv (normalModelOperator x w (normalCoord e p))`.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334, §2–3.
-/

public section

noncomputable section

open CliffordAlgebra Complex Module exteriorPower
open scoped RealInnerProductSpace InnerProductSpace

namespace TauCeti.SeibergWitten

/-! ### The eight-component normal model operator and its formal adjoint -/

section NormalModelDefs

variable (x : ℂ → EuclideanSpace ℝ (Fin 4))

/-- **The eight-component normal model operator** `𝓜_x (y, η) = (L_x y, L_x* η)` on `ℂ`. -/
def normalModelOperator (w : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) :=
  (Vortex.gaugeFixedOperator x (Prod.fst ∘ w) z, Vortex.gaugeFixedAdjoint x (Prod.snd ∘ w) z)

/-- **The formal `L²` adjoint** `𝓜_x* (ϕ, ψ) = (L_x* ϕ, L_x ψ)` of `normalModelOperator x`. -/
def normalModelAdjoint (ξ : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) :=
  (Vortex.gaugeFixedAdjoint x (Prod.fst ∘ ξ) z, Vortex.gaugeFixedOperator x (Prod.snd ∘ ξ) z)

@[simp] theorem normalModelOperator_apply
    (w : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    normalModelOperator x w z = (Vortex.gaugeFixedOperator x (Prod.fst ∘ w) z,
      Vortex.gaugeFixedAdjoint x (Prod.snd ∘ w) z) := (rfl)

@[simp] theorem normalModelAdjoint_apply
    (ξ : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    normalModelAdjoint x ξ z = (Vortex.gaugeFixedAdjoint x (Prod.fst ∘ ξ) z,
      Vortex.gaugeFixedOperator x (Prod.snd ∘ ξ) z) := (rfl)

@[simp] theorem fst_comp_normalModelOperator_mk (y η : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Prod.fst ∘ normalModelOperator x (fun z ↦ (y z, η z)) = Vortex.gaugeFixedOperator x y := by
  funext z; rw [Function.comp_apply, normalModelOperator_apply]; rfl

@[simp] theorem snd_comp_normalModelOperator_mk (y η : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Prod.snd ∘ normalModelOperator x (fun z ↦ (y z, η z)) = Vortex.gaugeFixedAdjoint x η := by
  funext z; rw [Function.comp_apply, normalModelOperator_apply]; rfl

/-- `normalModelOperator x` sends the zero field to zero. -/
@[simp] theorem normalModelOperator_zero : normalModelOperator x 0 = 0 := by
  funext z; simp [normalModelOperator_apply]

/-- `normalModelAdjoint x` sends the zero field to zero. -/
@[simp] theorem normalModelAdjoint_zero : normalModelAdjoint x 0 = 0 := by
  funext z; simp [normalModelAdjoint_apply]

/-- `normalModelOperator x` is additive at points where both input fields are differentiable. -/
theorem normalModelOperator_add
    {w v : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hw : DifferentiableAt ℝ w z) (hv : DifferentiableAt ℝ v z) :
    normalModelOperator x (w + v) z = normalModelOperator x w z + normalModelOperator x v z :=
  Prod.ext (Vortex.gaugeFixedOperator_add x hw.fst hv.fst)
    (Vortex.gaugeFixedAdjoint_add x hw.snd hv.snd)

/-- `normalModelOperator x` is `ℝ`-homogeneous. -/
theorem normalModelOperator_smul (r : ℝ)
    (w : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    normalModelOperator x (r • w) z = r • normalModelOperator x w z :=
  Prod.ext (Vortex.gaugeFixedOperator_smul x (Prod.fst ∘ w) r z)
    (Vortex.gaugeFixedAdjoint_smul x (Prod.snd ∘ w) r z)

/-- `normalModelAdjoint x` is additive at points where both input fields are differentiable. -/
theorem normalModelAdjoint_add
    {ξ ν : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hξ : DifferentiableAt ℝ ξ z) (hν : DifferentiableAt ℝ ν z) :
    normalModelAdjoint x (ξ + ν) z = normalModelAdjoint x ξ z + normalModelAdjoint x ν z :=
  Prod.ext (Vortex.gaugeFixedAdjoint_add x hξ.fst hν.fst)
    (Vortex.gaugeFixedOperator_add x hξ.snd hν.snd)

/-- `normalModelAdjoint x` is `ℝ`-homogeneous. -/
theorem normalModelAdjoint_smul (r : ℝ)
    (ξ : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    normalModelAdjoint x (r • ξ) z = r • normalModelAdjoint x ξ z :=
  Prod.ext (Vortex.gaugeFixedAdjoint_smul x (Prod.fst ∘ ξ) r z)
    (Vortex.gaugeFixedOperator_smul x (Prod.snd ∘ ξ) r z)

end NormalModelDefs

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

attribute [local instance] finiteDimensional_of_finrank_four

/-! ### Exact eight-component normal intertwining theorem -/

section NormalIntertwining

section FrameHypotheses

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
  (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
  (hu₀₁ : ‖u₀‖ = 1)
include hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁

/-- Pointwise evaluation of `normalDomainEquiv` on `(y ∘ normalCoord e, η ∘ normalCoord e)`
recovers `(normalModelConnection e y (-η) p, normalModelSpinor e u₀ y (-η) p)`. -/
theorem normalDomainEquiv_apply_normalCoord (y η : ℂ → EuclideanSpace ℝ (Fin 4)) (p : V) :
    normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
        (y (normalCoord e p), η (normalCoord e p)) =
      (normalModelConnection e y (-η) p, normalModelSpinor e u₀ y (-η) p) := by
  rw [normalDomainEquiv_apply]
  refine Prod.ext (normalFrameForm_eq_of_apply (by simp) (by simp) (by simp) (by simp)) ?_
  simp [normalFrameSpinor_def, normalModelSpinor_apply, Vortex.sectionValue_apply, sub_eq_add_neg]
  module

omit h₂ in
private theorem gaugeFixedFlatOperator_normalPerturbation_snd_fst
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) {y η : ℂ → EuclideanSpace ℝ (Fin 4)} {p : V}
    (hy : DifferentiableAt ℝ y (normalCoord e p)) (hη : DifferentiableAt ℝ η (normalCoord e p)) :
    (gaugeFixedFlatOperator o ρ e hkl (normalConnection e x) (normalModelSpinor e u₀ x 0)
      (normalModelConnection e y (-η)) (normalModelSpinor e u₀ y (-η)) p).2.1 =
      normalFrameSelfDual o hkl he h₀ h₂₃
        (Vortex.gaugeFixedOperator x y (normalCoord e p))
        (Vortex.gaugeFixedAdjoint x η (normalCoord e p)) := by
  let z := normalCoord e p
  have hη' : DifferentiableAt ℝ (-η) z := hη.neg
  have hadj : Vortex.gaugeFixedAdjoint x (-η) z = -Vortex.gaugeFixedAdjoint x η z := by
    simpa only [neg_one_smul] using Vortex.gaugeFixedAdjoint_smul x η (-1) z
  have hω_sd := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  set c := (gaugeFixedFlatOperator o ρ e hkl (normalConnection e x) (normalModelSpinor e u₀ x 0)
    (normalModelConnection e y (-η)) (normalModelSpinor e u₀ y (-η)) p).2.1
  have hinner {j : Fin 4}
      {σ : Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1}
      (hσ : σ = o.selfDualWedge hkl (e 0) (e j)) :
      ⟪σ, c⟫ = ⟪flatDeformationCurvature o ρ hkl (normalModelConnection e y (-η))
          (normalModelSpinor e u₀ x 0) (normalModelSpinor e u₀ y (-η)) p,
        ιMulti ℝ 2 ![e 0, e j]⟫ := by
    rw [hσ, o.inner_selfDualWedge_left hkl c, coe_gaugeFixedFlatOperator_snd_fst,
      real_inner_smul_left, real_inner_comm (ιMulti ℝ 2 ![e 0, e j]), ← mul_assoc,
      mul_div_assoc', Real.mul_self_sqrt zero_le_two]
    ring
  have hc0 : ⟪J.kahlerSelfDual o hkl hω_sd, c⟫ = Vortex.gaugeFixedOperator x y z 1 := by
    rw [hinner (AlmostComplexStructure.kahlerSelfDual_eq_selfDualWedge he h₀ h₂₃ hω_sd),
      inner_flatDeformationCurvature_normalModel_zero_one hQ hkl he h₀ h₂₃ hρ hu₀ x hu₀₁ hy hη']
  have hc1 : ⟪AlmostComplexStructure.antiInvariantSelfDual₁ o e hkl, c⟫ =
      Vortex.gaugeFixedAdjoint x η z 0 := by
    unfold AlmostComplexStructure.antiInvariantSelfDual₁
    rw [hinner rfl,
      inner_flatDeformationCurvature_normalModel_zero_two hQ hkl he h₀ h₂₃ hρ hu₀ x hu₀₁ hy hη',
      hadj, PiLp.neg_apply, neg_neg]
  have hc2 : ⟪AlmostComplexStructure.antiInvariantSelfDual₂ o e hkl, c⟫ =
      Vortex.gaugeFixedAdjoint x η z 1 := by
    unfold AlmostComplexStructure.antiInvariantSelfDual₂
    rw [hinner rfl,
      inner_flatDeformationCurvature_normalModel_zero_three hQ hkl he h₀ h₂₃ hρ hu₀ x hu₀₁ hy hη',
      hadj, PiLp.neg_apply, neg_neg]
  rw [AlmostComplexStructure.eq_inner_kahlerSelfDual_add_antiInvariantSelfDual
    (e := e) (he := he) (h₀ := h₀) (h₂ := h₂₃) hω_sd c, hc0, hc1, hc2,
    normalFrameSelfDual_def]

/-- **Eight-real-component normal intertwining theorem**: for an arbitrary plane field
`x : ℂ → ℝ⁴` (with no regularity or PDE hypothesis on `x`) and a perturbation field
`w : ℂ → ℝ⁴ × ℝ⁴` differentiable at `normalCoord e p`, applying `gaugeFixedFlatOperator` at the
pulled-back background `(normalConnection e x, normalModelSpinor e u₀ x 0)` to the pointwise
pullback of `w` through `normalDomainEquiv` equals
`normalTargetEquiv (normalModelOperator x w (normalCoord e p))`. -/
theorem gaugeFixedFlatOperator_normalPerturbation (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {w : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)} {p : V}
    (hw : DifferentiableAt ℝ w (normalCoord e p)) :
    gaugeFixedFlatOperator o ρ e hkl (normalConnection e x) (normalModelSpinor e u₀ x 0)
        (fun q ↦ (normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
          (w (normalCoord e q))).fst)
        (fun q ↦ (normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
          (w (normalCoord e q))).snd) p =
      normalTargetEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
        (normalModelOperator x w (normalCoord e p)) := by
  let z := normalCoord e p
  have hy : DifferentiableAt ℝ (Prod.fst ∘ w) z := hw.fst
  have hη : DifferentiableAt ℝ (Prod.snd ∘ w) z := hw.snd
  have hη' : DifferentiableAt ℝ (-(Prod.snd ∘ w)) z := hη.neg
  have hfst :
      (fun q ↦ (normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
        (w (normalCoord e q))).fst) =
      normalModelConnection e (Prod.fst ∘ w) (-(Prod.snd ∘ w)) :=
    funext fun q ↦ congrArg Prod.fst
      (normalDomainEquiv_apply_normalCoord hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
        (Prod.fst ∘ w) (Prod.snd ∘ w) q)
  have hsnd :
      (fun q ↦ (normalDomainEquiv o ρ hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
        (w (normalCoord e q))).snd) =
      normalModelSpinor e u₀ (Prod.fst ∘ w) (-(Prod.snd ∘ w)) :=
    funext fun q ↦ congrArg Prod.snd
      (normalDomainEquiv_apply_normalCoord hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁
        (Prod.fst ∘ w) (Prod.snd ∘ w) q)
  have hadj : Vortex.gaugeFixedAdjoint x (-(Prod.snd ∘ w)) z =
      -Vortex.gaugeFixedAdjoint x (Prod.snd ∘ w) z := by
    simpa only [neg_one_smul] using Vortex.gaugeFixedAdjoint_smul x (Prod.snd ∘ w) (-1) z
  rw [hfst, hsnd, normalTargetEquiv_apply, normalModelOperator_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  -- Gauge row (`ℝ`).
  · rw [gaugeFixedFlatOperator_apply]
    simpa [z] using flatDeformationGauge_normalModel hQ h₀ h₂₃ hρ hu₀ x hu₀₁ hy hη'
  -- Curvature row (`Λ⁺ V`).
  · exact gaugeFixedFlatOperator_normalPerturbation_snd_fst hQ hkl he h₀ h₂₃ hρ hu₀ hu₀₁ x hy hη
  -- Dirac row (`W⁻`).
  · rw [gaugeFixedFlatOperator_apply, normalFrameNegSpinor_def]
    apply Subtype.ext
    have hdir := flatDeformationDirac_normalModel hQ h₀ h₂₃ hu₀ x hy hη'
    rw [normalModelConnection_zero_right] at hdir
    dsimp only
    rw [hdir]
    simp only [Submodule.coe_sub, Submodule.coe_smul, coe_halfSpinCliffordMul_apply_apply,
      LinearEquiv.coe_ofEq_apply, hadj, PiLp.neg_apply, ofReal_neg, z]
    module

end FrameHypotheses
end NormalIntertwining
end TauCeti.SeibergWitten
