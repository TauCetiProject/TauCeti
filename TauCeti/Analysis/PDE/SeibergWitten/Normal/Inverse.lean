/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.RightInverse
import TauCeti.Analysis.PDE.Vortex.AdjointKernel
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Distribution.TestFunction.Lp

/-!
# Normal slow projections, kernel/cokernel identifications, and complementary weak `L²` inverse

By `TauCeti.SeibergWitten.gaugeFixedFlatSW_normalPerturbation`, the linearized gauge-fixed flat
Seiberg–Witten operator along `ℂ` intertwines with `𝓜_x (y, η) = (L_x y, L_x* η)`. This file
develops `normalModelOperator`, `normalModelAdjoint`, `normalModelKernelEquiv`,
`normalModelAdjointKernelEquiv`, `weakVortexKernel`, `normalDomainSlowProj`, `normalTargetSlowProj`,
`normalComplementaryInverse`, and `exists_normalComplementaryInverse`.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334, §2–3.
-/

public section

noncomputable section

open Complex Filter MeasureTheory
open scoped RealInnerProductSpace Topology ENNReal

namespace TauCeti.SeibergWitten

local notation "E4" => (EuclideanSpace ℝ (Fin 4))
local notation "Lp4(" μ ")" => (Lp (EuclideanSpace ℝ (Fin 4)) 2 (μ))
local notation "NormalL2(" μ ")" =>
  (WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 (μ) × Lp (EuclideanSpace ℝ (Fin 4)) 2 (μ)))
local notation "VGFOp" => Vortex.gaugeFixedOperator
local notation "VGFAdj" => Vortex.gaugeFixedAdjoint
local notation "memLpVGFOp(" hx ", " hy ", " hyc ")" =>
  (Continuous.memLp_of_hasCompactSupport (Vortex.continuous_gaugeFixedOperator (hx) (hy))
    (Vortex.hasCompactSupport_gaugeFixedOperator (hyc)))
local notation "memLpVGFAdj(" hx ", " hη ", " hηc ")" =>
  (Continuous.memLp_of_hasCompactSupport (Vortex.continuous_gaugeFixedAdjoint (hx) (hη))
    (Vortex.hasCompactSupport_gaugeFixedAdjoint (hηc)))

/-! ### The eight-component normal model operator and kernel/cokernel identifications -/

section NormalModel

/-- **The eight-component normal model operator** `𝓜_x (y, η) = (L_x y, L_x* η)` on `ℂ`. -/
def normalModelOperator (x : ℂ → E4) (w : ℂ → E4 × E4) (z : ℂ) : E4 × E4 :=
  (VGFOp x (Prod.fst ∘ w) z, VGFAdj x (Prod.snd ∘ w) z)

/-- **The formal `L²` adjoint** `𝓜_x* (ϕ, ψ) = (L_x* ϕ, L_x ψ)` of `normalModelOperator x`. -/
def normalModelAdjoint (x : ℂ → E4) (ξ : ℂ → E4 × E4) (z : ℂ) : E4 × E4 :=
  (VGFAdj x (Prod.fst ∘ ξ) z, VGFOp x (Prod.snd ∘ ξ) z)
@[simp] theorem normalModelOperator_apply (x : ℂ → E4) (w : ℂ → E4 × E4) (z : ℂ) :
    normalModelOperator x w z = (VGFOp x (Prod.fst ∘ w) z, VGFAdj x (Prod.snd ∘ w) z) := (rfl)
@[simp] theorem normalModelAdjoint_apply (x : ℂ → E4) (ξ : ℂ → E4 × E4) (z : ℂ) :
    normalModelAdjoint x ξ z = (VGFAdj x (Prod.fst ∘ ξ) z, VGFOp x (Prod.snd ∘ ξ) z) := (rfl)
private theorem integral_inner_gaugeFixedOperator_of_hasCompactSupport_right
    {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x y η : ℂ → E4}
    (hx : Continuous x) (hy : ContDiff ℝ 1 y) (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪VGFOp x y z, η z⟫ ∂μ = ∫ z, ⟪y z, VGFAdj x η z⟫ ∂μ := by
  have hyi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ y w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hy
  have hηi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ η w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hη
  have hηic (i : Fin 4) : HasCompactSupport fun w ↦ η w i :=
    hηc.comp_left (g := EuclideanSpace.proj (𝕜 := ℝ) i) (map_zero _)
  set V₁ : ℂ → ℝ := fun w ↦ y w 0 * η w 0 - y w 1 * η w 1 + y w 2 * η w 2 + y w 3 * η w 3
  set V₂ : ℂ → ℝ := fun w ↦ y w 1 * η w 0 + y w 0 * η w 1 - y w 3 * η w 2 + y w 2 * η w 3
  have hV₁ : ContDiff ℝ 1 V₁ := by have := hyi; have := hηi; fun_prop
  have hV₂ : ContDiff ℝ 1 V₂ := by have := hyi; have := hηi; fun_prop
  have hV₁c : HasCompactSupport V₁ :=
    (((hηic 0).mul_left.sub (hηic 1).mul_left).add (hηic 2).mul_left).add (hηic 3).mul_left
  have hV₂c : HasCompactSupport V₂ :=
    (((hηic 0).mul_left.add (hηic 1).mul_left).sub (hηic 2).mul_left).add (hηic 3).mul_left
  have hint (V : ℂ → ℝ) (hV : ContDiff ℝ 1 V) (hVc : HasCompactSupport V) (v : ℂ) :
      Integrable (fun z ↦ fderiv ℝ V z v) μ :=
    ((hV.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hVc.fderiv_apply (𝕜 := ℝ) v)
  have hmain : Integrable (fun z ↦ ⟪y z, VGFAdj x η z⟫) μ :=
    (hy.continuous.inner (Vortex.continuous_gaugeFixedAdjoint hx hη))
      |>.integrable_of_hasCompactSupport
      ((Vortex.hasCompactSupport_gaugeFixedAdjoint (x := x) hηc).mono fun z hz h0 ↦
        hz (by simp [h0]))
  have hgreen (z : ℂ) : ⟪VGFOp x y z, η z⟫ =
      ⟪y z, VGFAdj x η z⟫ + fderiv ℝ V₁ z 1 + fderiv ℝ V₂ z I := by
    have hy_d (i : Fin 4) := (hyi i).differentiable one_ne_zero z
    have hη_d (i : Fin 4) := (hηi i).differentiable one_ne_zero z
    simp (disch := fun_prop) [V₁, V₂, PiLp.inner_apply, Fin.sum_univ_four, fderiv_fun_mul,
      fderiv_fun_add, fderiv_fun_sub]; ring
  simp_rw [hgreen]
  rw [integral_add (hmain.fun_add (hint V₁ hV₁ hV₁c 1)) (hint V₂ hV₂ hV₂c I),
    integral_add hmain (hint V₁ hV₁ hV₁c 1),
    integral_fderiv_apply_eq_zero_of_hasCompactSupport hV₁ hV₁c,
    integral_fderiv_apply_eq_zero_of_hasCompactSupport hV₂ hV₂c, add_zero, add_zero]

/-- **Formal `L²` adjointness of `normalModelOperator` and `normalModelAdjoint`**. -/
theorem integral_inner_normalModelOperator {μ : Measure ℂ} [μ.IsAddHaarMeasure]
    {x : ℂ → E4} {w ξ : ℂ → E4 × E4}
    (hx : Continuous x) (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w) (hξ : ContDiff ℝ 1 ξ) :
    ∫ z, (⟪(normalModelOperator x w z).1, (ξ z).1⟫ + ⟪(normalModelOperator x w z).2, (ξ z).2⟫) ∂μ =
      ∫ z, (⟪(w z).1, (normalModelAdjoint x ξ z).1⟫ +
        ⟪(w z).2, (normalModelAdjoint x ξ z).2⟫) ∂μ := by
  have hw₁ := contDiff_fst.comp hw; have hw₂ := contDiff_snd.comp hw
  have hw₁c : HasCompactSupport (Prod.fst ∘ w) := hwc.comp_left rfl
  have hw₂c : HasCompactSupport (Prod.snd ∘ w) := hwc.comp_left rfl
  have hξ₁ := contDiff_fst.comp hξ; have hξ₂ := contDiff_snd.comp hξ
  have hsupp_l {u v : ℂ → E4} (hu : HasCompactSupport u) :
      HasCompactSupport fun z ↦ ⟪u z, v z⟫ := hu.mono fun _ hz h0 ↦ hz (by simp [h0])
  have hiL₁ : Integrable (fun z ↦ ⟪VGFOp x (Prod.fst ∘ w) z, (ξ z).1⟫) μ :=
    ((Vortex.continuous_gaugeFixedOperator hx hw₁).inner hξ₁.continuous)
      |>.integrable_of_hasCompactSupport
        (hsupp_l (Vortex.hasCompactSupport_gaugeFixedOperator (x := x) hw₁c))
  have hiL₂ : Integrable (fun z ↦ ⟪VGFAdj x (Prod.snd ∘ w) z, (ξ z).2⟫) μ :=
    ((Vortex.continuous_gaugeFixedAdjoint hx hw₂).inner hξ₂.continuous)
      |>.integrable_of_hasCompactSupport
        (hsupp_l (Vortex.hasCompactSupport_gaugeFixedAdjoint (x := x) hw₂c))
  have hiR₁ : Integrable (fun z ↦ ⟪(w z).1, VGFAdj x (Prod.fst ∘ ξ) z⟫) μ :=
    (hw₁.continuous.inner (Vortex.continuous_gaugeFixedAdjoint hx hξ₁))
      |>.integrable_of_hasCompactSupport (hsupp_l hw₁c)
  have hiR₂ : Integrable (fun z ↦ ⟪(w z).2, VGFOp x (Prod.snd ∘ ξ) z⟫) μ :=
    (hw₂.continuous.inner (Vortex.continuous_gaugeFixedOperator hx hξ₂))
      |>.integrable_of_hasCompactSupport (hsupp_l hw₂c)
  simp only [normalModelOperator_apply, normalModelAdjoint_apply]
  rw [integral_add hiL₁ hiL₂, integral_add hiR₁ hiR₂]
  refine congrArg₂ (· + ·) (Vortex.integral_inner_gaugeFixedOperator hx hw₁ hw₁c hξ₁) ?_
  calc ∫ z, ⟪VGFAdj x (Prod.snd ∘ w) z, (ξ z).2⟫ ∂μ
      = ∫ z, ⟪(Prod.snd ∘ ξ) z, VGFAdj x (Prod.snd ∘ w) z⟫ ∂μ :=
        integral_congr_ae (ae_of_all _ fun _ ↦ real_inner_comm _ _)
    _ = ∫ z, ⟪VGFOp x (Prod.snd ∘ ξ) z, (Prod.snd ∘ w) z⟫ ∂μ :=
        (integral_inner_gaugeFixedOperator_of_hasCompactSupport_right hx hξ₂ hw₂ hw₂c).symm
    _ = ∫ z, ⟪(w z).2, VGFOp x (Prod.snd ∘ ξ) z⟫ ∂μ :=
        integral_congr_ae (ae_of_all _ fun _ ↦ real_inner_comm _ _)
private def mkPairKernel (P : (ℂ → E4 × E4) → ℂ → E4 × E4)
    (hadd : ∀ {w v}, ContDiff ℝ 2 w → ContDiff ℝ 2 v → ∀ z, P (w + v) z = P w z + P v z)
    (hsmul : ∀ (r : ℝ) w z, P (r • w) z = r • P w z) : Submodule ℝ (ℂ → E4 × E4) where
  carrier := {w | ContDiff ℝ 2 w ∧ MemLp (Prod.fst ∘ w) 2 volume ∧
    MemLp (Prod.snd ∘ w) 2 volume ∧ ∀ z, P w z = 0}
  add_mem' := fun ⟨hw, hw₁, hw₂, hwk⟩ ⟨hv, hv₁, hv₂, hvk⟩ ↦
    ⟨hw.add hv, hw₁.add hv₁, hw₂.add hv₂, fun z ↦ by rw [hadd hw hv z, hwk z, hvk z, add_zero]⟩
  zero_mem' := ⟨contDiff_const, MemLp.zero, MemLp.zero, fun z ↦ by simpa using hsmul 0 0 z⟩
  smul_mem' r _ := fun ⟨hw, hw₁, hw₂, hwk⟩ ↦
    ⟨contDiff_const.smul hw, hw₁.const_smul r, hw₂.const_smul r,
      fun z ↦ by rw [hsmul r _ z, hwk z, smul_zero]⟩

/-- **The classical `C²` `L²` kernel of `normalModelOperator x`**. -/
def normalModelKernel (x : ℂ → E4) : Submodule ℝ (ℂ → E4 × E4) :=
  mkPairKernel (normalModelOperator x)
    (fun hw hv z ↦ Prod.ext
      (Vortex.gaugeFixedOperator_add x ((contDiff_fst.comp hw).differentiable (by norm_num) z)
        ((contDiff_fst.comp hv).differentiable (by norm_num) z))
      (Vortex.gaugeFixedAdjoint_add x ((contDiff_snd.comp hw).differentiable (by norm_num) z)
        ((contDiff_snd.comp hv).differentiable (by norm_num) z)))
    (fun r w z ↦ Prod.ext (Vortex.gaugeFixedOperator_smul x (Prod.fst ∘ w) r z)
      (Vortex.gaugeFixedAdjoint_smul x (Prod.snd ∘ w) r z))
@[simp] theorem mem_normalModelKernel {x : ℂ → E4} {w : ℂ → E4 × E4} :
    w ∈ normalModelKernel x ↔ ContDiff ℝ 2 w ∧ MemLp (Prod.fst ∘ w) 2 volume ∧
      MemLp (Prod.snd ∘ w) 2 volume ∧ ∀ z, normalModelOperator x w z = 0 := (Iff.rfl)

/-- **The classical `C²` `L²` kernel of `normalModelAdjoint x`**. -/
def normalModelAdjointKernel (x : ℂ → E4) : Submodule ℝ (ℂ → E4 × E4) :=
  mkPairKernel (normalModelAdjoint x)
    (fun hξ hν z ↦ Prod.ext
      (Vortex.gaugeFixedAdjoint_add x ((contDiff_fst.comp hξ).differentiable (by norm_num) z)
        ((contDiff_fst.comp hν).differentiable (by norm_num) z))
      (Vortex.gaugeFixedOperator_add x ((contDiff_snd.comp hξ).differentiable (by norm_num) z)
        ((contDiff_snd.comp hν).differentiable (by norm_num) z)))
    (fun r ξ z ↦ Prod.ext (Vortex.gaugeFixedAdjoint_smul x (Prod.fst ∘ ξ) r z)
      (Vortex.gaugeFixedOperator_smul x (Prod.snd ∘ ξ) r z))
@[simp] theorem mem_normalModelAdjointKernel {x : ℂ → E4} {ξ : ℂ → E4 × E4} :
    ξ ∈ normalModelAdjointKernel x ↔ ContDiff ℝ 2 ξ ∧ MemLp (Prod.fst ∘ ξ) 2 volume ∧
      MemLp (Prod.snd ∘ ξ) 2 volume ∧ ∀ z, normalModelAdjoint x ξ z = 0 := (Iff.rfl)
theorem snd_eq_zero_of_mem_normalModelKernel {x : ℂ → E4}
    (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0)
    {w : ℂ → E4 × E4} (hw : w ∈ normalModelKernel x) : Prod.snd ∘ w = 0 := by
  rcases hw with ⟨hwc, -, hw₂, hwk⟩
  exact Vortex.eq_zero_of_memLp_of_gaugeFixedAdjoint_eq_zero hx (contDiff_snd.comp hwc) hw₂ hsol
    (funext fun z ↦ (Prod.mk.inj (hwk z)).2)
theorem fst_eq_zero_of_mem_normalModelAdjointKernel {x : ℂ → E4}
    (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0)
    {ξ : ℂ → E4 × E4} (hξ : ξ ∈ normalModelAdjointKernel x) : Prod.fst ∘ ξ = 0 := by
  rcases hξ with ⟨hξc, hξ₁, -, hξk⟩
  exact Vortex.eq_zero_of_memLp_of_gaugeFixedAdjoint_eq_zero hx (contDiff_fst.comp hξc) hξ₁ hsol
    (funext fun z ↦ (Prod.mk.inj (hξk z)).1)

/-- **Kernel identification at a plane vortex**: `y ↦ (y, 0)`. -/
def normalModelKernelEquiv {x : ℂ → E4}
    (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0) :
    Vortex.gaugeFixedKernel x ≃ₗ[ℝ] normalModelKernel x where
  toFun y :=
    let hy := Vortex.mem_gaugeFixedKernel.1 y.2
    ⟨fun z ↦ (y.1 z, 0), hy.1.prodMk contDiff_const, hy.2.1, MemLp.zero, fun z ↦ Prod.ext
      (hy.2.2 z) (show VGFAdj x 0 z = 0 by simpa using Vortex.gaugeFixedAdjoint_smul x 0 0 z)⟩
  map_add' _ _ := by ext z <;> simp
  map_smul' _ _ := by ext z <;> simp
  invFun w := ⟨Prod.fst ∘ w.1, Vortex.mem_gaugeFixedKernel.2
    ⟨contDiff_fst.comp w.2.1, w.2.2.1, fun z ↦ (Prod.mk.inj (w.2.2.2.2 z)).1⟩⟩
  left_inv _ := by ext; rfl
  right_inv w := Subtype.ext <| funext fun z ↦ Prod.ext rfl
    (congrFun (snd_eq_zero_of_mem_normalModelKernel hx hsol w.2) z).symm

/-- **Cokernel (adjoint kernel) identification at a plane vortex**: `g ↦ (0, g)`. -/
def normalModelAdjointKernelEquiv {x : ℂ → E4}
    (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0) :
    Vortex.gaugeFixedKernel x ≃ₗ[ℝ] normalModelAdjointKernel x where
  toFun g :=
    let hg := Vortex.mem_gaugeFixedKernel.1 g.2
    ⟨fun z ↦ (0, g.1 z), contDiff_const.prodMk hg.1, MemLp.zero, hg.2.1, fun z ↦ Prod.ext
      (show VGFAdj x 0 z = 0 by simpa using Vortex.gaugeFixedAdjoint_smul x 0 0 z) (hg.2.2 z)⟩
  map_add' _ _ := by ext z <;> simp
  map_smul' _ _ := by ext z <;> simp
  invFun ξ := ⟨Prod.snd ∘ ξ.1, Vortex.mem_gaugeFixedKernel.2
    ⟨contDiff_snd.comp ξ.2.1, ξ.2.2.2.1, fun z ↦ (Prod.mk.inj (ξ.2.2.2.2 z)).2⟩⟩
  left_inv _ := by ext; rfl
  right_inv ξ := Subtype.ext <| funext fun z ↦ Prod.ext
    (congrFun (fst_eq_zero_of_mem_normalModelAdjointKernel hx hsol ξ.2) z).symm rfl
@[simp] theorem coe_normalModelKernelEquiv_apply {x : ℂ → E4} (hx : Differentiable ℝ x)
    (hsol : ∀ z, Vortex.equation x z = 0) (y : Vortex.gaugeFixedKernel x) (z : ℂ) :
    (normalModelKernelEquiv hx hsol y : ℂ → E4 × E4) z = (y.1 z, 0) := (rfl)
@[simp] theorem coe_normalModelAdjointKernelEquiv_apply {x : ℂ → E4} (hx : Differentiable ℝ x)
    (hsol : ∀ z, Vortex.equation x z = 0) (g : Vortex.gaugeFixedKernel x) (z : ℂ) :
    (normalModelAdjointKernelEquiv hx hsol g : ℂ → E4 × E4) z = (0, g.1 z) := (rfl)
@[simp] theorem coe_normalModelKernelEquiv_symm_apply {x : ℂ → E4} (hx : Differentiable ℝ x)
    (hsol : ∀ z, Vortex.equation x z = 0) (w : normalModelKernel x) (z : ℂ) :
    ((normalModelKernelEquiv hx hsol).symm w : ℂ → E4) z = (w.1 z).1 := (rfl)
@[simp] theorem coe_normalModelAdjointKernelEquiv_symm_apply {x : ℂ → E4} (hx : Differentiable ℝ x)
    (hsol : ∀ z, Vortex.equation x z = 0) (ξ : normalModelAdjointKernel x) (z : ℂ) :
    ((normalModelAdjointKernelEquiv hx hsol).symm ξ : ℂ → E4) z = (ξ.1 z).2 := (rfl)

end NormalModel

/-! ### Normal slow projections `Π₊`, `Π₋` and complementary weak `L²` inverse `𝒬` -/

section SlowProjectionsAndInverse

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → E4}

private abbrev VortexTestField := TestFunction (⊤ : TopologicalSpace.Opens ℂ) E4 2
omit [μ.IsAddHaarMeasure] in private theorem memLp_vortexAdjoint [IsFiniteMeasureOnCompacts μ]
    (hx : Continuous x) (η : VortexTestField) : MemLp (VGFAdj x η) 2 μ :=
  (Vortex.continuous_gaugeFixedAdjoint hx (η.contDiff.of_le (by norm_cast)))
    |>.memLp_of_hasCompactSupport (Vortex.hasCompactSupport_gaugeFixedAdjoint η.hasCompactSupport)
private def vortexAdjointToLp (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hx : Continuous x) :
    VortexTestField →ₗ[ℝ] Lp4(μ) where
  toFun η := (memLp_vortexAdjoint hx η).toLp (VGFAdj x η)
  map_add' η ν := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ Vortex.gaugeFixedAdjoint_add x
      (η.contDiff.differentiable (by norm_num) z) (ν.contDiff.differentiable (by norm_num) z))
  map_smul' t η := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ Vortex.gaugeFixedAdjoint_smul x η t z)
private theorem inner_vortexAdjointToLp (hx : Continuous x) (u : Lp4(μ)) (η : VortexTestField) :
    ⟪u, vortexAdjointToLp μ hx η⟫ = ∫ z, ⟪u z, VGFAdj x η z⟫ ∂μ :=
  L2.inner_toLp u (memLp_vortexAdjoint hx η)

/-- **The weak `L²` vortex kernel `K_x`**, defined as `(range L_x*)ᗮ` over `C²_c(ℂ; ℝ⁴)`. -/
def weakVortexKernel (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hx : Continuous x) :
    Submodule ℝ Lp4(μ) :=
  (LinearMap.range (vortexAdjointToLp μ hx))ᗮ
instance instIsClosedWeakVortexKernel (hx : Continuous x) :
    IsClosed (weakVortexKernel μ hx : Set Lp4(μ)) := Submodule.isClosed_orthogonal _
instance instHasOrthogonalProjectionWeakVortexKernel (hx : Continuous x) :
    (weakVortexKernel μ hx).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

local notation "KProj(" μ ", " hx ")" => (Submodule.starProjection (weakVortexKernel (μ) (hx)))

theorem mem_weakVortexKernel_iff (hx : Continuous x) (u : Lp4(μ)) : u ∈ weakVortexKernel μ hx ↔
      ∀ η : ℂ → E4, ContDiff ℝ 2 η → HasCompactSupport η → ∫ z, ⟪u z, VGFAdj x η z⟫ ∂μ = 0 := by
  rw [weakVortexKernel, Submodule.mem_orthogonal]
  refine ⟨fun h η hη hηc ↦ ?_, ?_⟩
  · let η' : VortexTestField := ⟨η, hη, hηc, by simp⟩
    have h0 := h (vortexAdjointToLp μ hx η') ⟨η', rfl⟩
    rwa [real_inner_comm, inner_vortexAdjointToLp hx] at h0
  · rintro h _ ⟨η, rfl⟩
    rw [real_inner_comm, inner_vortexAdjointToLp hx]; exact h η η.contDiff η.hasCompactSupport

omit [μ.IsAddHaarMeasure] in
private theorem integral_inner_toLp_left {f g : ℂ → E4} (hf : MemLp f 2 μ) :
    ∫ z, ⟪(hf.toLp f) z, g z⟫ ∂μ = ∫ z, ⟪f z, g z⟫ ∂μ := by
  refine integral_congr_ae ?_; filter_upwards [hf.coeFn_toLp] with z hz; rw [hz]
theorem toLp_mem_weakVortexKernel_of_gaugeFixedOperator_eq_zero (hx : Continuous x)
    {y : ℂ → E4} (hy : ContDiff ℝ 1 y) (hy_lp : MemLp y 2 μ)
    (hy_ker : ∀ z, VGFOp x y z = 0) : hy_lp.toLp y ∈ weakVortexKernel μ hx := by
  rw [mem_weakVortexKernel_iff hx]; intro η hη hηc
  rw [integral_inner_toLp_left hy_lp, ← integral_inner_gaugeFixedOperator_of_hasCompactSupport_right
    hx hy (hη.of_le (by norm_num)) hηc]; simp [hy_ker]
theorem toLp_mem_weakVortexKernel_of_mem_gaugeFixedKernel (hx : Continuous x)
    {y : ℂ → E4} (hy : y ∈ Vortex.gaugeFixedKernel x) :
    (Vortex.mem_gaugeFixedKernel.1 hy).2.1.toLp y ∈ weakVortexKernel volume hx := by
  rcases Vortex.mem_gaugeFixedKernel.1 hy with ⟨hyc, hy_lp, hy_ker⟩
  exact toLp_mem_weakVortexKernel_of_gaugeFixedOperator_eq_zero hx
    (hyc.of_le (by norm_num)) hy_lp hy_ker

omit [μ.IsAddHaarMeasure] in
private def diagL2 (A B : Lp4(μ) →L[ℝ] Lp4(μ)) : NormalL2(μ) →L[ℝ] NormalL2(μ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap ∘L
    ((A ∘L WithLp.fstL 2 ℝ _ _).prod (B ∘L WithLp.sndL 2 ℝ _ _))
omit [μ.IsAddHaarMeasure] in private theorem diagL2_comp (A₁ B₁ A₂ B₂ : Lp4(μ) →L[ℝ] Lp4(μ)) :
    diagL2 A₁ B₁ ∘L diagL2 A₂ B₂ = diagL2 (A₁ ∘L A₂) (B₁ ∘L B₂) := by
  ext w : 1; apply (WithLp.ofLp_injective 2); rfl
omit [μ.IsAddHaarMeasure] in private theorem isSelfAdjoint_diagL2 {A B : Lp4(μ) →L[ℝ] Lp4(μ)}
    (hA : ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫) (hB : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) :
    IsSelfAdjoint (diagL2 A B) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v; simp only [ContinuousLinearMap.coe_coe]
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  exact congrArg₂ (· + ·) (hA u.fst v.fst) (hB u.snd v.snd)
omit [μ.IsAddHaarMeasure] in private theorem norm_diagL2_le {A B : Lp4(μ) →L[ℝ] Lp4(μ)} {c : ℝ}
    (hc : 0 ≤ c) (hA : ‖A‖ ≤ c) (hB : ‖B‖ ≤ c) : ‖diagL2 A B‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun w ↦ ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2]
  have h1 : ‖(diagL2 A B w).fst‖ ^ 2 ≤ c ^ 2 * ‖w.fst‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _)
      ((A.le_opNorm w.fst).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) 2
  have h2 : ‖(diagL2 A B w).snd‖ ^ 2 ≤ c ^ 2 * ‖w.snd‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _)
      ((B.le_opNorm w.snd).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))) 2
  linarith

/-- **The normal domain slow projection** `Π₊(y, η) = (P_{K_x} y, 0)`. -/
def normalDomainSlowProj (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hx : Continuous x) :
    NormalL2(μ) →L[ℝ] NormalL2(μ) := diagL2 KProj(μ, hx) 0

/-- **The normal target slow projection** `Π₋(f, g) = (0, P_{K_x} g)`. -/
def normalTargetSlowProj (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hx : Continuous x) :
    NormalL2(μ) →L[ℝ] NormalL2(μ) := diagL2 0 KProj(μ, hx)
@[simp] theorem ofLp_normalDomainSlowProj (hx : Continuous x) (w : NormalL2(μ)) :
    WithLp.ofLp (normalDomainSlowProj μ hx w) = (KProj(μ, hx) (WithLp.ofLp w).1, 0) := (rfl)
@[simp] theorem fst_normalDomainSlowProj (hx : Continuous x) (w : NormalL2(μ)) :
    (normalDomainSlowProj μ hx w).fst = KProj(μ, hx) w.fst := (rfl)
@[simp] theorem snd_normalDomainSlowProj (hx : Continuous x) (w : NormalL2(μ)) :
    (normalDomainSlowProj μ hx w).snd = 0 := (rfl)
@[simp] theorem ofLp_normalTargetSlowProj (hx : Continuous x) (w : NormalL2(μ)) :
    WithLp.ofLp (normalTargetSlowProj μ hx w) = (0, KProj(μ, hx) (WithLp.ofLp w).2) := (rfl)
@[simp] theorem fst_normalTargetSlowProj (hx : Continuous x) (w : NormalL2(μ)) :
    (normalTargetSlowProj μ hx w).fst = 0 := (rfl)
@[simp] theorem snd_normalTargetSlowProj (hx : Continuous x) (w : NormalL2(μ)) :
    (normalTargetSlowProj μ hx w).snd = KProj(μ, hx) w.snd := (rfl)
private theorem starProjection_weakVortexKernel_comp_self (hx : Continuous x) :
    KProj(μ, hx) ∘L KProj(μ, hx) = KProj(μ, hx) :=
  ContinuousLinearMap.ext fun _ ↦
    Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)
private theorem norm_starProjection_weakVortexKernel_le (hx : Continuous x) :
    ‖KProj(μ, hx)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    simpa using (weakVortexKernel μ hx).norm_starProjection_apply_le u
@[simp] theorem normalDomainSlowProj_comp_self (hx : Continuous x) :
    normalDomainSlowProj μ hx ∘L normalDomainSlowProj μ hx = normalDomainSlowProj μ hx := by
  rw [normalDomainSlowProj, diagL2_comp, starProjection_weakVortexKernel_comp_self,
    ContinuousLinearMap.zero_comp]
@[simp] theorem normalTargetSlowProj_comp_self (hx : Continuous x) :
    normalTargetSlowProj μ hx ∘L normalTargetSlowProj μ hx = normalTargetSlowProj μ hx := by
  rw [normalTargetSlowProj, diagL2_comp, ContinuousLinearMap.zero_comp,
    starProjection_weakVortexKernel_comp_self]
theorem isSelfAdjoint_normalDomainSlowProj (hx : Continuous x) :
    IsSelfAdjoint (normalDomainSlowProj μ hx) := by
  rw [normalDomainSlowProj]; exact isSelfAdjoint_diagL2
    (weakVortexKernel μ hx).inner_starProjection_left_eq_right (fun _ _ ↦ by simp)
theorem isSelfAdjoint_normalTargetSlowProj (hx : Continuous x) :
    IsSelfAdjoint (normalTargetSlowProj μ hx) := by
  rw [normalTargetSlowProj]; exact isSelfAdjoint_diagL2 (fun _ _ ↦ by simp)
    (weakVortexKernel μ hx).inner_starProjection_left_eq_right
theorem norm_normalDomainSlowProj_le (hx : Continuous x) : ‖normalDomainSlowProj μ hx‖ ≤ 1 := by
  rw [normalDomainSlowProj]
  exact norm_diagL2_le zero_le_one (norm_starProjection_weakVortexKernel_le hx) (by simp)
theorem norm_normalTargetSlowProj_le (hx : Continuous x) : ‖normalTargetSlowProj μ hx‖ ≤ 1 := by
  rw [normalTargetSlowProj]
  exact norm_diagL2_le zero_le_one (by simp) (norm_starProjection_weakVortexKernel_le hx)

omit [μ.IsAddHaarMeasure] in
/-- **The complementary normal weak `L²` inverse** `𝒬(f, g) = (Q f, Q† g)`. -/
def normalComplementaryInverse (Q : Lp4(μ) →L[ℝ] Lp4(μ)) : NormalL2(μ) →L[ℝ] NormalL2(μ) :=
  diagL2 Q (ContinuousLinearMap.adjoint Q)

omit [μ.IsAddHaarMeasure] in
@[simp] theorem ofLp_normalComplementaryInverse (Q : Lp4(μ) →L[ℝ] Lp4(μ)) (w : NormalL2(μ)) :
    WithLp.ofLp (normalComplementaryInverse Q w) =
      (Q (WithLp.ofLp w).1, ContinuousLinearMap.adjoint Q (WithLp.ofLp w).2) := (rfl)
omit [μ.IsAddHaarMeasure] in
@[simp] theorem fst_normalComplementaryInverse (Q : Lp4(μ) →L[ℝ] Lp4(μ)) (w : NormalL2(μ)) :
    (normalComplementaryInverse Q w).fst = Q w.fst := (rfl)
omit [μ.IsAddHaarMeasure] in
@[simp] theorem snd_normalComplementaryInverse (Q : Lp4(μ) →L[ℝ] Lp4(μ)) (w : NormalL2(μ)) :
    (normalComplementaryInverse Q w).snd = ContinuousLinearMap.adjoint Q w.snd := (rfl)
omit [μ.IsAddHaarMeasure] in theorem norm_normalComplementaryInverse_le (Q : Lp4(μ) →L[ℝ] Lp4(μ)) :
    ‖normalComplementaryInverse Q‖ ≤ ‖Q‖ :=
  norm_diagL2_le (norm_nonneg Q) le_rfl
    (LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint Q).le
private theorem apply_mem_orthogonal_weakVortexKernel (hx : Continuous x) {Q : Lp4(μ) →L[ℝ] Lp4(μ)}
    (hQorth : ∀ f u, u ∈ weakVortexKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0) (f : Lp4(μ)) :
    Q f ∈ (weakVortexKernel μ hx)ᗮ :=
  (Submodule.mem_orthogonal _ _).2 fun u hu ↦ by
    rw [real_inner_comm, L2.inner_def]; exact hQorth f u hu
theorem normalDomainSlowProj_comp_normalComplementaryInverse (hx : Continuous x)
    {Q : Lp4(μ) →L[ℝ] Lp4(μ)}
    (hQorth : ∀ f u, u ∈ weakVortexKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0) :
    normalDomainSlowProj μ hx ∘L normalComplementaryInverse Q = 0 := by
  ext w : 1; apply (WithLp.ofLp_injective 2)
  rw [ContinuousLinearMap.comp_apply, ofLp_normalDomainSlowProj, ofLp_normalComplementaryInverse,
    (Submodule.starProjection_apply_eq_zero_iff (K := weakVortexKernel μ hx)).2
      (apply_mem_orthogonal_weakVortexKernel hx hQorth _)]; rfl
theorem normalComplementaryInverse_comp_normalTargetSlowProj (hx : Continuous x)
    {Q : Lp4(μ) →L[ℝ] Lp4(μ)}
    (hQorth : ∀ f u, u ∈ weakVortexKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0) :
    normalComplementaryInverse Q ∘L normalTargetSlowProj μ hx = 0 := by
  ext w : 1; apply (WithLp.ofLp_injective 2)
  have hadj0 : ContinuousLinearMap.adjoint Q (KProj(μ, hx) (WithLp.ofLp w).2) = 0 :=
    ext_inner_right ℝ fun h ↦ by
      rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm, L2.inner_def]
      exact hQorth h _ (Submodule.starProjection_apply_mem _ _)
  rw [ContinuousLinearMap.comp_apply, ofLp_normalComplementaryInverse, ofLp_normalTargetSlowProj,
    map_zero, hadj0]; rfl
theorem apply_toLp_gaugeFixedOperator_eq_sub_starProjection (hx : Continuous x)
    {Q : Lp4(μ) →L[ℝ] Lp4(μ)} (hQsol : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q f z, VGFAdj x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (hQorth : ∀ f u, u ∈ weakVortexKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0)
    {ψ : ℂ → E4} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    let hψ_lp : MemLp ψ 2 μ := hψ.continuous.memLp_of_hasCompactSupport hψc
    let hLψ_lp : MemLp (VGFOp x ψ) 2 μ := memLpVGFOp(hx, hψ, hψc)
    Q (hLψ_lp.toLp (VGFOp x ψ)) = hψ_lp.toLp ψ - KProj(μ, hx) (hψ_lp.toLp ψ) := by
  intro hψ_lp hLψ_lp; set S := vortexAdjointToLp μ hx
  refine LinearMap.eq_of_inner_apply_eq_of_mem_orthogonal S
    (apply_mem_orthogonal_weakVortexKernel hx hQorth _)
    (Submodule.sub_starProjection_mem_orthogonal _) fun η ↦ ?_
  have hPK_zero : ⟪KProj(μ, hx) (hψ_lp.toLp ψ), S η⟫ = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal _ _).1 (Submodule.starProjection_apply_mem _ _) (S η) ⟨η, rfl⟩
  rw [inner_vortexAdjointToLp hx, hQsol _ η η.contDiff η.hasCompactSupport, inner_sub_left,
    hPK_zero, sub_zero, inner_vortexAdjointToLp hx, integral_inner_toLp_left hLψ_lp,
    Vortex.integral_inner_gaugeFixedOperator hx hψ hψc (η.contDiff.of_le (by norm_cast)),
    integral_inner_toLp_left hψ_lp]

/-- **Exact `L²` left-inverse identity**: `𝒬 (L_x y, L_x* η) = (1 - Π₊) (y, η)` on `C²_c`. -/
theorem normalComplementaryInverse_toLp_normalModelOperator (hx : Continuous x)
    {Q : Lp4(μ) →L[ℝ] Lp4(μ)} (hQsol : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q f z, VGFAdj x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (hQorth : ∀ f u, u ∈ weakVortexKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0)
    {y η : ℂ → E4} (hy : ContDiff ℝ 2 y) (hyc : HasCompactSupport y)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    let hy_lp : MemLp y 2 μ := hy.continuous.memLp_of_hasCompactSupport hyc
    let hη_lp : MemLp η 2 μ := hη.continuous.memLp_of_hasCompactSupport hηc
    let hLy_lp : MemLp (VGFOp x y) 2 μ := memLpVGFOp(hx, hy.of_le (by norm_num), hyc)
    let hAη_lp : MemLp (VGFAdj x η) 2 μ := memLpVGFAdj(hx, hη.of_le (by norm_num), hηc)
    normalComplementaryInverse Q
        (WithLp.toLp 2 (hLy_lp.toLp (VGFOp x y), hAη_lp.toLp (VGFAdj x η))) =
      (1 - normalDomainSlowProj μ hx) (WithLp.toLp 2 (hy_lp.toLp y, hη_lp.toLp η)) := by
  intro hy_lp hη_lp hLy_lp hAη_lp; apply (WithLp.ofLp_injective 2)
  rw [ofLp_normalComplementaryInverse, sub_apply, one_apply_eq_self, WithLp.ofLp_sub,
    ofLp_normalDomainSlowProj]
  refine Prod.ext (apply_toLp_gaugeFixedOperator_eq_sub_starProjection hx hQsol hQorth
    (hy.of_le (by norm_num)) hyc) ?_
  dsimp only [Prod.snd_sub]; rw [sub_zero]; exact ext_inner_right ℝ fun h ↦ by
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm, L2.inner_toLp (Q h) hAη_lp,
      hQsol h η hη hηc, ← L2.inner_toLp h hη_lp, real_inner_comm]

/-- **Weak right-inverse identity**: `𝓜_x (𝒬 w) = (1 - Π₋) w` weakly against `(ϕ, ψ) ∈ C²_c`. -/
theorem integral_inner_normalComplementaryInverse_normalModelAdjoint (hx : Continuous x)
    {Q : Lp4(μ) →L[ℝ] Lp4(μ)} (hQsol : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q f z, VGFAdj x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (hQorth : ∀ f u, u ∈ weakVortexKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0)
    (w : NormalL2(μ)) {ϕ ψ : ℂ → E4} (hϕ : ContDiff ℝ 2 ϕ) (hϕc : HasCompactSupport ϕ)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    let q := WithLp.ofLp (normalComplementaryInverse Q w)
    let r := WithLp.ofLp ((1 - normalTargetSlowProj μ hx) w)
    (∫ z, ⟪q.1 z, VGFAdj x ϕ z⟫ ∂μ) + (∫ z, ⟪q.2 z, VGFOp x ψ z⟫ ∂μ) =
      (∫ z, ⟪r.1 z, ϕ z⟫ ∂μ) + (∫ z, ⟪r.2 z, ψ z⟫ ∂μ) := by
  intro q r
  have hq : q = (Q (WithLp.ofLp w).1, ContinuousLinearMap.adjoint Q (WithLp.ofLp w).2) := rfl
  have hr : r = ((WithLp.ofLp w).1, (WithLp.ofLp w).2 - KProj(μ, hx) (WithLp.ofLp w).2) := by
    dsimp only [r]; rw [sub_apply, one_apply_eq_self, WithLp.ofLp_sub, ofLp_normalTargetSlowProj]
    exact Prod.ext (sub_zero _) rfl
  refine congrArg₂ (· + ·)
    (by rw [congrArg Prod.fst hq, congrArg Prod.fst hr]; exact hQsol _ ϕ hϕ hϕc) ?_
  have hψ_lp : MemLp ψ 2 μ := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hLψ_lp : MemLp (VGFOp x ψ) 2 μ := memLpVGFOp(hx, hψ.of_le (by norm_num), hψc)
  calc ∫ z, ⟪q.2 z, VGFOp x ψ z⟫ ∂μ
      = ⟪ContinuousLinearMap.adjoint Q (WithLp.ofLp w).2, hLψ_lp.toLp (VGFOp x ψ)⟫ := by
        rw [congrArg Prod.snd hq]; exact (L2.inner_toLp _ hLψ_lp).symm
    _ = ⟪(WithLp.ofLp w).2, hψ_lp.toLp ψ - KProj(μ, hx) (hψ_lp.toLp ψ)⟫ := by
        rw [ContinuousLinearMap.adjoint_inner_left,
          apply_toLp_gaugeFixedOperator_eq_sub_starProjection hx hQsol hQorth
            (hψ.of_le (by norm_num)) hψc]
    _ = ⟪r.2, hψ_lp.toLp ψ⟫ := by
        rw [congrArg Prod.snd hr, inner_sub_left, inner_sub_right,
          (weakVortexKernel μ hx).inner_starProjection_left_eq_right]
    _ = ∫ z, ⟪r.2 z, ψ z⟫ ∂μ := L2.inner_toLp r.2 hψ_lp

/-- **Existence of the complementary normal weak `L²` inverse at a plane vortex.** -/
theorem exists_normalComplementaryInverse (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, Vortex.equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ 𝒬 : NormalL2(μ) →L[ℝ] NormalL2(μ),
      normalDomainSlowProj μ hx.continuous ∘L 𝒬 = 0 ∧
      𝒬 ∘L normalTargetSlowProj μ hx.continuous = 0 ∧
      (∀ (y η : ℂ → E4) (hy : ContDiff ℝ 2 y) (hyc : HasCompactSupport y)
          (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η),
        let hy_lp : MemLp y 2 μ := hy.continuous.memLp_of_hasCompactSupport hyc
        let hη_lp : MemLp η 2 μ := hη.continuous.memLp_of_hasCompactSupport hηc
        let hLy_lp : MemLp (VGFOp x y) 2 μ := memLpVGFOp(hx.continuous, hy.of_le (by norm_num), hyc)
        let hAη_lp : MemLp (VGFAdj x η) 2 μ :=
          memLpVGFAdj(hx.continuous, hη.of_le (by norm_num), hηc)
        𝒬 (WithLp.toLp 2 (hLy_lp.toLp (VGFOp x y), hAη_lp.toLp (VGFAdj x η))) =
          (1 - normalDomainSlowProj μ hx.continuous)
            (WithLp.toLp 2 (hy_lp.toLp y, hη_lp.toLp η))) ∧
      ∀ w (ϕ ψ : ℂ → E4),
        ContDiff ℝ 2 ϕ → HasCompactSupport ϕ → ContDiff ℝ 2 ψ → HasCompactSupport ψ →
        let q := WithLp.ofLp (𝒬 w)
        let r := WithLp.ofLp ((1 - normalTargetSlowProj μ hx.continuous) w)
        (∫ z, ⟪q.1 z, VGFAdj x ϕ z⟫ ∂μ) + (∫ z, ⟪q.2 z, VGFOp x ψ z⟫ ∂μ) =
          (∫ z, ⟪r.1 z, ϕ z⟫ ∂μ) + (∫ z, ⟪r.2 z, ψ z⟫ ∂μ) := by
  obtain ⟨Q, hQsol, hQorth⟩ :=
    Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (μ := μ) hx hsol hlim
  have hQorth' : ∀ f u, u ∈ weakVortexKernel μ hx.continuous → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0 :=
    fun f u hu ↦ hQorth f u ((mem_weakVortexKernel_iff hx.continuous u).1 hu)
  exact ⟨normalComplementaryInverse Q,
    normalDomainSlowProj_comp_normalComplementaryInverse hx.continuous hQorth',
    normalComplementaryInverse_comp_normalTargetSlowProj hx.continuous hQorth',
    fun _ _ hy hyc hη hηc ↦ normalComplementaryInverse_toLp_normalModelOperator hx.continuous
      hQsol hQorth' hy hyc hη hηc,
    fun w _ _ hϕ hϕc hψ hψc ↦ integral_inner_normalComplementaryInverse_normalModelAdjoint
      hx.continuous hQsol hQorth' w hϕ hϕc hψ hψc⟩

end SlowProjectionsAndInverse

end TauCeti.SeibergWitten
