/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.PDE.Vortex.WeakKernel
import TauCeti.Analysis.InnerProductSpace.ProdL2
import TauCeti.Analysis.PDE.Vortex.AdjointKernel

/-!
# Normal slow projections, kernel/cokernel identifications, and complementary weak `L²` inverse

By `gaugeFixedFlatOperator_normalPerturbation`, linearizing the four-dimensional gauge-fixed flat
Seiberg–Witten operator along a normal plane around a pulled-back configuration `x : ℂ → ℝ⁴` gives
the decoupled pair `𝓜_x (y, η) = (L_x y, L_x* η)` with formal `L²` adjoint
`𝓜_x* (ϕ, ψ) = (L_x* ϕ, L_x ψ)`, where `L_x = Vortex.gaugeFixedOperator x` and
`L_x* = Vortex.gaugeFixedAdjoint x`.

At a differentiable plane vortex (`Vortex.equation x = 0`), the `L²` kernel of `L_x*` vanishes, so
the classical `C²` `L²` kernels of `𝓜_x` and `𝓜_x*` both identify with `Vortex.gaugeFixedKernel x`
in the `y`- and `ψ`-slots respectively. In the normal reduction, this splits the product Hilbert
space `NormalL2 volume = L²(ℂ; ℝ⁴) ⊕₂ L²(ℂ; ℝ⁴)` into slow components along
`K_x = Vortex.weakGaugeFixedKernel x` — projected out by `normalDomainSlowProj`
(`Π₊(y, η) = (P_{K_x} y, 0)`) and `normalTargetSlowProj` (`Π₋(f, g) = (0, P_{K_x} g)`) — and fast
components on their complements, where the block-diagonal operator `normalComplementaryInverse Q`
(`𝒬(f, g) = (Q f, Q† g)`) built from the vortex weak right inverse `Q` inverts `𝓜_x`.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334, §2–3.
-/

public section

noncomputable section

open Complex Filter MeasureTheory
open scoped RealInnerProductSpace Topology ENNReal

namespace TauCeti.SeibergWitten

/-! ### The eight-component normal model operator and kernel/cokernel identifications -/

section NormalModel

section Defs
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
end Defs

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}
  {w ξ : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)}

/-- **Formal `L²` adjointness of `normalModelOperator` and `normalModelAdjoint`**. -/
theorem integral_inner_normalModelOperator {μ : Measure ℂ} [μ.IsAddHaarMeasure]
    (hx : Continuous x) (hw : ContDiff ℝ 1 w) (hξ : ContDiff ℝ 1 ξ)
    (hc : HasCompactSupport w ∨ HasCompactSupport ξ) :
    ∫ z, (⟪(normalModelOperator x w z).fst, (ξ z).fst⟫ +
        ⟪(normalModelOperator x w z).snd, (ξ z).snd⟫) ∂μ =
      ∫ z, (⟪(w z).fst, (normalModelAdjoint x ξ z).fst⟫ +
        ⟪(w z).snd, (normalModelAdjoint x ξ z).snd⟫) ∂μ := by
  have hw₁ := contDiff_fst.comp hw; have hw₂ := contDiff_snd.comp hw
  have hξ₁ := contDiff_fst.comp hξ; have hξ₂ := contDiff_snd.comp hξ
  have hc₁ : HasCompactSupport (Prod.fst ∘ w) ∨ HasCompactSupport (Prod.fst ∘ ξ) :=
    hc.imp (·.comp_left rfl) (·.comp_left rfl)
  have hc₂ : HasCompactSupport (Prod.snd ∘ w) ∨ HasCompactSupport (Prod.snd ∘ ξ) :=
    hc.imp (·.comp_left rfl) (·.comp_left rfl)
  have hint {u v : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : Continuous u) (hv : Continuous v)
      (huv : HasCompactSupport u ∨ HasCompactSupport v) : Integrable (fun z ↦ ⟪u z, v z⟫) μ :=
    (hu.inner hv).integrable_of_hasCompactSupport <| huv.elim
      (fun h ↦ h.mono fun _ hz h0 ↦ hz (by simp [h0]))
      (fun h ↦ h.mono fun _ hz h0 ↦ hz (by simp [h0]))
  simp only [normalModelOperator_apply, normalModelAdjoint_apply]
  rw [integral_add
        (hint (v := fun z ↦ (ξ z).fst) (Vortex.continuous_gaugeFixedOperator hx hw₁) hξ₁.continuous
          (hc₁.imp Vortex.hasCompactSupport_gaugeFixedOperator id))
        (hint (v := fun z ↦ (ξ z).snd) (Vortex.continuous_gaugeFixedAdjoint hx hw₂) hξ₂.continuous
          (hc₂.imp Vortex.hasCompactSupport_gaugeFixedAdjoint id)),
    integral_add
        (hint (u := fun z ↦ (w z).fst) hw₁.continuous (Vortex.continuous_gaugeFixedAdjoint hx hξ₁)
          (hc₁.imp id Vortex.hasCompactSupport_gaugeFixedAdjoint))
        (hint (u := fun z ↦ (w z).snd) hw₂.continuous (Vortex.continuous_gaugeFixedOperator hx hξ₂)
          (hc₂.imp id Vortex.hasCompactSupport_gaugeFixedOperator))]
  refine congrArg₂ (· + ·) (Vortex.integral_inner_gaugeFixedOperator hw₁ hξ₁ hc₁) ?_
  exact (integral_congr_ae (ae_of_all _ fun _ ↦ real_inner_comm _ _)).trans <|
    (Vortex.integral_inner_gaugeFixedOperator hξ₂ hw₂ hc₂.symm).symm.trans <|
      integral_congr_ae (ae_of_all _ fun _ ↦ real_inner_comm _ _)

private def mkPairKernel
    (P : (ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) →
      ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) (hzero : P 0 = 0)
    (hadd : ∀ {w v z}, DifferentiableAt ℝ w z → DifferentiableAt ℝ v z →
      P (w + v) z = P w z + P v z)
    (hsmul : ∀ (r : ℝ) w z, P (r • w) z = r • P w z) :
    Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) where
  carrier := {w | ContDiff ℝ 2 w ∧ MemLp (Prod.fst ∘ w) 2 volume ∧
    MemLp (Prod.snd ∘ w) 2 volume ∧ ∀ z, P w z = 0}
  add_mem' := fun ⟨hw, hw₁, hw₂, hwk⟩ ⟨hv, hv₁, hv₂, hvk⟩ ↦
    ⟨hw.add hv, hw₁.add hv₁, hw₂.add hv₂, fun z ↦ by
      rw [hadd (hw.differentiable (by norm_num) z) (hv.differentiable (by norm_num) z), hwk z,
        hvk z, add_zero]⟩
  zero_mem' := ⟨contDiff_const, MemLp.zero, MemLp.zero, fun z ↦ by simp [hzero]⟩
  smul_mem' r _ := fun ⟨hw, hw₁, hw₂, hwk⟩ ↦ ⟨contDiff_const.smul hw, hw₁.const_smul r,
    hw₂.const_smul r, fun z ↦ by rw [hsmul r _ z, hwk z, smul_zero]⟩
/-- **The classical `C²` `L²` kernel of `normalModelOperator x`**. -/
def normalModelKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :=
  mkPairKernel (normalModelOperator x) (normalModelOperator_zero x)
    (normalModelOperator_add x) (normalModelOperator_smul x)
@[simp] theorem mem_normalModelKernel :
    w ∈ normalModelKernel x ↔ ContDiff ℝ 2 w ∧ MemLp (Prod.fst ∘ w) 2 volume ∧
      MemLp (Prod.snd ∘ w) 2 volume ∧ ∀ z, normalModelOperator x w z = 0 := (Iff.rfl)
/-- **The classical `C²` `L²` kernel of `normalModelAdjoint x`**. -/
def normalModelAdjointKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :=
  mkPairKernel (normalModelAdjoint x) (normalModelAdjoint_zero x)
    (normalModelAdjoint_add x) (normalModelAdjoint_smul x)
@[simp] theorem mem_normalModelAdjointKernel :
    ξ ∈ normalModelAdjointKernel x ↔ ContDiff ℝ 2 ξ ∧ MemLp (Prod.fst ∘ ξ) 2 volume ∧
      MemLp (Prod.snd ∘ ξ) 2 volume ∧ ∀ z, normalModelAdjoint x ξ z = 0 := (Iff.rfl)
/-- At a differentiable plane vortex, the `L_x*` block of `normalModelOperator x` has trivial `L²`
kernel, so the second component of every element of `normalModelKernel x` vanishes. -/
theorem snd_eq_zero_of_mem_normalModelKernel (hx : Differentiable ℝ x)
    (hsol : ∀ z, Vortex.equation x z = 0) (hw : w ∈ normalModelKernel x) : Prod.snd ∘ w = 0 := by
  rcases hw with ⟨hwc, -, hw₂, hwk⟩
  exact Vortex.eq_zero_of_memLp_of_gaugeFixedAdjoint_eq_zero hx (contDiff_snd.comp hwc) hw₂ hsol
    (funext fun z ↦ (Prod.mk.inj (hwk z)).2)
/-- At a differentiable plane vortex, the `L_x*` block of `normalModelAdjoint x` has trivial `L²`
kernel, so the first component of every element of `normalModelAdjointKernel x` vanishes. -/
theorem fst_eq_zero_of_mem_normalModelAdjointKernel (hx : Differentiable ℝ x)
    (hsol : ∀ z, Vortex.equation x z = 0) (hξ : ξ ∈ normalModelAdjointKernel x) :
    Prod.fst ∘ ξ = 0 := by
  rcases hξ with ⟨hξc, hξ₁, -, hξk⟩
  exact Vortex.eq_zero_of_memLp_of_gaugeFixedAdjoint_eq_zero hx (contDiff_fst.comp hξc) hξ₁ hsol
    (funext fun z ↦ (Prod.mk.inj (hξk z)).1)

section KernelEquivs
variable (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0)
/-- **Kernel identification at a plane vortex**: `y ↦ (y, 0)`. -/
def normalModelKernelEquiv : Vortex.gaugeFixedKernel x ≃ₗ[ℝ] normalModelKernel x where
  toFun y := let hy := Vortex.mem_gaugeFixedKernel.1 y.property
    ⟨fun z ↦ (y.val z, 0), hy.1.prodMk contDiff_const, hy.2.1, MemLp.zero, fun z ↦
      Prod.ext (hy.2.2 z) (congrFun (Vortex.gaugeFixedAdjoint_zero x) z)⟩
  map_add' _ _ := by ext z <;> simp
  map_smul' _ _ := by ext z <;> simp
  invFun w := ⟨Prod.fst ∘ w.val, Vortex.mem_gaugeFixedKernel.2
    ⟨contDiff_fst.comp w.property.1, w.property.2.1, fun z ↦ (Prod.mk.inj (w.property.2.2.2 z)).1⟩⟩
  left_inv _ := by ext z; simp
  right_inv w := Subtype.ext <| funext fun z ↦ Prod.ext rfl
    (congrFun (snd_eq_zero_of_mem_normalModelKernel hx hsol w.property) z).symm
/-- **Cokernel (adjoint kernel) identification at a plane vortex**: `g ↦ (0, g)`. -/
def normalModelAdjointKernelEquiv : Vortex.gaugeFixedKernel x ≃ₗ[ℝ] normalModelAdjointKernel x where
  toFun g := let hg := Vortex.mem_gaugeFixedKernel.1 g.property
    ⟨fun z ↦ (0, g.val z), contDiff_const.prodMk hg.1, MemLp.zero, hg.2.1, fun z ↦
      Prod.ext (congrFun (Vortex.gaugeFixedAdjoint_zero x) z) (hg.2.2 z)⟩
  map_add' _ _ := by ext z <;> simp
  map_smul' _ _ := by ext z <;> simp
  invFun ξ := ⟨Prod.snd ∘ ξ.val, Vortex.mem_gaugeFixedKernel.2
    ⟨contDiff_snd.comp ξ.property.1, ξ.property.2.2.1,
      fun z ↦ (Prod.mk.inj (ξ.property.2.2.2 z)).2⟩⟩
  left_inv _ := by ext z; simp
  right_inv ξ := Subtype.ext <| funext fun z ↦ Prod.ext
    (congrFun (fst_eq_zero_of_mem_normalModelAdjointKernel hx hsol ξ.property) z).symm rfl
@[simp] theorem coe_normalModelKernelEquiv_apply (y : Vortex.gaugeFixedKernel x) (z : ℂ) :
    (normalModelKernelEquiv hx hsol y : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) z =
      (y.val z, 0) := (rfl)
@[simp] theorem coe_normalModelAdjointKernelEquiv_apply (g : Vortex.gaugeFixedKernel x) (z : ℂ) :
    (normalModelAdjointKernelEquiv hx hsol g :
      ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) z = (0, g.val z) := (rfl)
@[simp] theorem coe_normalModelKernelEquiv_symm_apply (w : normalModelKernel x) (z : ℂ) :
    ((normalModelKernelEquiv hx hsol).symm w : ℂ → EuclideanSpace ℝ (Fin 4)) z = (w.val z).fst :=
  (rfl)
@[simp] theorem coe_normalModelAdjointKernelEquiv_symm_apply
    (ξ : normalModelAdjointKernel x) (z : ℂ) :
    ((normalModelAdjointKernelEquiv hx hsol).symm ξ : ℂ → EuclideanSpace ℝ (Fin 4)) z =
      (ξ.val z).snd := (rfl)
end KernelEquivs
end NormalModel

/-! ### Normal slow projections `Π₊`, `Π₋` and complementary weak `L²` inverse `𝒬` -/

section SlowProjectionsAndInverse

/-- The eight-real-component normal `L²` Hilbert space `L²(ℂ; ℝ⁴) ⊕₂ L²(ℂ; ℝ⁴)`. -/
abbrev NormalL2 (μ : Measure ℂ) : Type :=
  WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

section SlowProj
/-- **The normal domain slow projection** `Π₊(y, η) = (P_{K_x} y, 0)` on `NormalL2 volume`. -/
def normalDomainSlowProj (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    NormalL2 volume →L[ℝ] NormalL2 volume :=
  (Vortex.weakGaugeFixedKernel x).starProjection.withLpProdMap 2 0
/-- **The normal target slow projection** `Π₋(f, g) = (0, P_{K_x} g)` on `NormalL2 volume`. -/
def normalTargetSlowProj (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    NormalL2 volume →L[ℝ] NormalL2 volume :=
  (0 : _ →L[ℝ] _).withLpProdMap 2 (Vortex.weakGaugeFixedKernel x).starProjection
@[simp] theorem ofLp_normalDomainSlowProj (w : NormalL2 volume) :
    WithLp.ofLp (normalDomainSlowProj x w) =
      ((Vortex.weakGaugeFixedKernel x).starProjection (WithLp.ofLp w).fst, 0) := by
  simp [normalDomainSlowProj]
@[simp] theorem fst_normalDomainSlowProj (w : NormalL2 volume) :
    (normalDomainSlowProj x w).fst =
      (Vortex.weakGaugeFixedKernel x).starProjection w.fst := by simp [normalDomainSlowProj]
@[simp] theorem snd_normalDomainSlowProj (w : NormalL2 volume) :
    (normalDomainSlowProj x w).snd = 0 := by simp [normalDomainSlowProj]
@[simp] theorem ofLp_normalTargetSlowProj (w : NormalL2 volume) :
    WithLp.ofLp (normalTargetSlowProj x w) =
      (0, (Vortex.weakGaugeFixedKernel x).starProjection (WithLp.ofLp w).snd) := by
  simp [normalTargetSlowProj]
@[simp] theorem fst_normalTargetSlowProj (w : NormalL2 volume) :
    (normalTargetSlowProj x w).fst = 0 := by simp [normalTargetSlowProj]
@[simp] theorem snd_normalTargetSlowProj (w : NormalL2 volume) :
    (normalTargetSlowProj x w).snd =
      (Vortex.weakGaugeFixedKernel x).starProjection w.snd := by simp [normalTargetSlowProj]
/-- `normalDomainSlowProj` is idempotent. -/
@[simp] theorem normalDomainSlowProj_comp_self :
    normalDomainSlowProj x ∘L normalDomainSlowProj x = normalDomainSlowProj x := by
  rw [normalDomainSlowProj, ← ContinuousLinearMap.withLpProdMap_comp,
    Submodule.starProjection_comp_starProjection_of_le (le_refl _), ContinuousLinearMap.zero_comp]
/-- `normalTargetSlowProj` is idempotent. -/
@[simp] theorem normalTargetSlowProj_comp_self :
    normalTargetSlowProj x ∘L normalTargetSlowProj x = normalTargetSlowProj x := by
  rw [normalTargetSlowProj, ← ContinuousLinearMap.withLpProdMap_comp, ContinuousLinearMap.zero_comp,
    Submodule.starProjection_comp_starProjection_of_le (le_refl _)]
/-- `normalDomainSlowProj` is self-adjoint on `NormalL2 volume`. -/
theorem isSelfAdjoint_normalDomainSlowProj : IsSelfAdjoint (normalDomainSlowProj x) :=
  (isSelfAdjoint_starProjection (Vortex.weakGaugeFixedKernel x)).withLpProdMap
    (IsSelfAdjoint.zero _)
/-- `normalTargetSlowProj` is self-adjoint on `NormalL2 volume`. -/
theorem isSelfAdjoint_normalTargetSlowProj : IsSelfAdjoint (normalTargetSlowProj x) :=
  (IsSelfAdjoint.zero _).withLpProdMap
    (isSelfAdjoint_starProjection (Vortex.weakGaugeFixedKernel x))
/-- `normalDomainSlowProj` is a contraction (`‖Π₊‖ ≤ 1`). -/
theorem norm_normalDomainSlowProj_le : ‖normalDomainSlowProj x‖ ≤ 1 := by
  rw [normalDomainSlowProj, ContinuousLinearMap.norm_withLpProdMap, norm_zero, max_le_iff]
  exact ⟨(Vortex.weakGaugeFixedKernel x).starProjection_norm_le, zero_le_one⟩
/-- `normalTargetSlowProj` is a contraction (`‖Π₋‖ ≤ 1`). -/
theorem norm_normalTargetSlowProj_le : ‖normalTargetSlowProj x‖ ≤ 1 := by
  rw [normalTargetSlowProj, ContinuousLinearMap.norm_withLpProdMap, norm_zero, max_le_iff]
  exact ⟨zero_le_one, (Vortex.weakGaugeFixedKernel x).starProjection_norm_le⟩
end SlowProj

section ComplementaryInverse
variable {μ : Measure ℂ}
  (Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)
/-- The block-diagonal operator `𝒬(f, g) = (Q f, Q† g)` on `NormalL2 μ`. When `Q` is a weak right
inverse of `L_x` with range orthogonal to `Vortex.weakGaugeFixedKernel x`, this operator acts as
the complementary inverse of `normalModelOperator x` orthogonal to the slow subspaces. -/
def normalComplementaryInverse : NormalL2 μ →L[ℝ] NormalL2 μ :=
  Q.withLpProdMap 2 (ContinuousLinearMap.adjoint Q)
@[simp] theorem ofLp_normalComplementaryInverse (w : NormalL2 μ) :
    WithLp.ofLp (normalComplementaryInverse Q w) =
      (Q (WithLp.ofLp w).fst, ContinuousLinearMap.adjoint Q (WithLp.ofLp w).snd) := by
  simp [normalComplementaryInverse]
@[simp] theorem fst_normalComplementaryInverse (w : NormalL2 μ) :
    (normalComplementaryInverse Q w).fst = Q w.fst := by simp [normalComplementaryInverse]
@[simp] theorem snd_normalComplementaryInverse (w : NormalL2 μ) :
    (normalComplementaryInverse Q w).snd = ContinuousLinearMap.adjoint Q w.snd := by
  simp [normalComplementaryInverse]
/-- The operator norm of `normalComplementaryInverse Q` equals `‖Q‖`. -/
@[simp] theorem norm_normalComplementaryInverse : ‖normalComplementaryInverse Q‖ = ‖Q‖ := by
  simp [normalComplementaryInverse]
end ComplementaryInverse

variable {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) →L[ℝ]
  Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)}

private theorem starProjection_weakGaugeFixedKernel_comp_eq_zero
    (hQorth : ∀ f u, u ∈ Vortex.weakGaugeFixedKernel x → ∫ z, ⟪Q f z, u z⟫ = 0) :
    (Vortex.weakGaugeFixedKernel x).starProjection ∘L Q = 0 := by
  ext f : 1
  rw [ContinuousLinearMap.comp_apply, zero_apply, Submodule.starProjection_apply_eq_zero_iff]
  exact (Submodule.mem_orthogonal' _ _).2 fun u hu ↦ by rw [L2.inner_def]; exact hQorth f u hu
/-- If the range of `Q` is orthogonal to `Vortex.weakGaugeFixedKernel x`, then
`normalDomainSlowProj x ∘L normalComplementaryInverse Q = 0`. -/
theorem normalDomainSlowProj_comp_normalComplementaryInverse
    (hQorth : ∀ f u, u ∈ Vortex.weakGaugeFixedKernel x → ∫ z, ⟪Q f z, u z⟫ = 0) :
    normalDomainSlowProj x ∘L normalComplementaryInverse Q = 0 := by
  rw [normalDomainSlowProj, normalComplementaryInverse, ← ContinuousLinearMap.withLpProdMap_comp,
    starProjection_weakGaugeFixedKernel_comp_eq_zero hQorth, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.withLpProdMap_zero]
/-- If the range of `Q` is orthogonal to `Vortex.weakGaugeFixedKernel x`, then
`normalComplementaryInverse Q ∘L normalTargetSlowProj x = 0`. -/
theorem normalComplementaryInverse_comp_normalTargetSlowProj
    (hQorth : ∀ f u, u ∈ Vortex.weakGaugeFixedKernel x → ∫ z, ⟪Q f z, u z⟫ = 0) :
    normalComplementaryInverse Q ∘L normalTargetSlowProj x = 0 := by
  have hadj : ContinuousLinearMap.adjoint Q ∘L (Vortex.weakGaugeFixedKernel x).starProjection =
      0 := by
    rw [← (isSelfAdjoint_starProjection (Vortex.weakGaugeFixedKernel x)).adjoint_eq,
      ← ContinuousLinearMap.adjoint_comp,
      starProjection_weakGaugeFixedKernel_comp_eq_zero hQorth, map_zero]
  rw [normalComplementaryInverse, normalTargetSlowProj, ← ContinuousLinearMap.withLpProdMap_comp,
    ContinuousLinearMap.comp_zero, hadj, ContinuousLinearMap.withLpProdMap_zero]
/-- **Exact `L²` left-inverse identity**: `𝒬 (𝓜_x (y, η)) = (1 - Π₊) (y, η)` for `y ∈ C¹_c`
and `η ∈ C²_c`. -/
theorem normalComplementaryInverse_toLp_normalModelOperator (hx : Continuous x)
    (hQsol : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q f z, Vortex.gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫)
    (hQorth : ∀ f u, u ∈ Vortex.weakGaugeFixedKernel x → ∫ z, ⟪Q f z, u z⟫ = 0)
    {y η : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ 1 y) (hyc : HasCompactSupport y)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    let w : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) := fun z ↦ (y z, η z)
    let hy_lp : MemLp y 2 volume := hy.continuous.memLp_of_hasCompactSupport hyc
    let hη_lp : MemLp η 2 volume := hη.continuous.memLp_of_hasCompactSupport hηc
    let hLy_lp : MemLp (Prod.fst ∘ normalModelOperator x w) 2 volume := by
      have hfst : Prod.fst ∘ w = y := funext fun _ ↦ rfl
      rw [show Prod.fst ∘ normalModelOperator x w = Vortex.gaugeFixedOperator x y from
        funext fun z ↦ by simp [normalModelOperator_apply, hfst]]
      exact (Vortex.continuous_gaugeFixedOperator hx hy).memLp_of_hasCompactSupport
        (Vortex.hasCompactSupport_gaugeFixedOperator hyc)
    let hAη_lp : MemLp (Prod.snd ∘ normalModelOperator x w) 2 volume := by
      have hsnd : Prod.snd ∘ w = η := funext fun _ ↦ rfl
      rw [show Prod.snd ∘ normalModelOperator x w = Vortex.gaugeFixedAdjoint x η from
        funext fun z ↦ by simp [normalModelOperator_apply, hsnd]]
      exact Vortex.memLp_gaugeFixedAdjoint hx (hη.of_le (by norm_num)) hηc
    normalComplementaryInverse Q (WithLp.toLp 2 (hLy_lp.toLp (Prod.fst ∘ normalModelOperator x w),
        hAη_lp.toLp (Prod.snd ∘ normalModelOperator x w))) =
      (1 - normalDomainSlowProj x) (WithLp.toLp 2 (hy_lp.toLp y, hη_lp.toLp η)) := by
  intro w hy_lp hη_lp hLy_lp hAη_lp; apply WithLp.ofLp_injective 2
  rw [ofLp_normalComplementaryInverse, sub_apply, one_apply_eq_self, WithLp.ofLp_sub,
    ofLp_normalDomainSlowProj]
  have h1 : Prod.fst ∘ normalModelOperator x w = Vortex.gaugeFixedOperator x y :=
    funext fun z ↦ by
      have hfst : Prod.fst ∘ w = y := funext fun _ ↦ rfl
      simp [normalModelOperator_apply, hfst]
  have h2 : Prod.snd ∘ normalModelOperator x w = Vortex.gaugeFixedAdjoint x η :=
    funext fun z ↦ by
      have hsnd : Prod.snd ∘ w = η := funext fun _ ↦ rfl
      simp [normalModelOperator_apply, hsnd]
  have hLy_eq : hLy_lp.toLp (Prod.fst ∘ normalModelOperator x w) =
      ((Vortex.continuous_gaugeFixedOperator hx hy).memLp_of_hasCompactSupport
        (Vortex.hasCompactSupport_gaugeFixedOperator hyc)).toLp
        (Vortex.gaugeFixedOperator x y) := by
    have haux : ∀ {f g : ℂ → EuclideanSpace ℝ (Fin 4)}, f = g →
        ∀ (hf : MemLp f 2 volume) (hg : MemLp g 2 volume), hf.toLp f = hg.toLp g := by
      rintro f _ rfl _ _; rfl
    exact haux h1 _ _
  refine Prod.ext ?_ ?_
  · dsimp only [Prod.fst_sub]
    rw [hLy_eq]
    exact Vortex.apply_toLp_gaugeFixedOperator_eq_sub_starProjection hx hQsol hQorth hy hyc
  · dsimp only [Prod.snd_sub]; rw [sub_zero]; exact ext_inner_right ℝ fun h ↦ by
      rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm, L2.inner_toLp (Q h) hAη_lp]
      simp_rw [congrFun h2]
      rw [hQsol h η hη hηc, ← L2.inner_toLp h hη_lp, real_inner_comm]

/-- **Weak right-inverse identity**: `𝓜_x (𝒬 w) = (1 - Π₋) w` weakly against `ϕ ∈ C²_c` and
`ψ ∈ C¹_c`. -/
theorem integral_inner_normalComplementaryInverse_normalModelAdjoint (hx : Continuous x)
    (hQsol : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q f z, Vortex.gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫)
    (hQorth : ∀ f u, u ∈ Vortex.weakGaugeFixedKernel x → ∫ z, ⟪Q f z, u z⟫ = 0)
    (w : NormalL2 volume) {ϕ ψ : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hϕ : ContDiff ℝ 2 ϕ) (hϕc : HasCompactSupport ϕ)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    let ξ : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) := fun z ↦ (ϕ z, ψ z)
    let q := WithLp.ofLp (normalComplementaryInverse Q w)
    let r := WithLp.ofLp ((1 - normalTargetSlowProj x) w)
    (∫ z, ⟪q.fst z, (normalModelAdjoint x ξ z).fst⟫) +
        (∫ z, ⟪q.snd z, (normalModelAdjoint x ξ z).snd⟫) =
      (∫ z, ⟪r.fst z, (ξ z).fst⟫) + (∫ z, ⟪r.snd z, (ξ z).snd⟫) := by
  intro ξ q r
  have hr1 : r.fst = (WithLp.ofLp w).fst := by simp [r, WithLp.ofLp_sub]
  have hr2 : r.snd = (WithLp.ofLp w).snd -
      (Vortex.weakGaugeFixedKernel x).starProjection (WithLp.ofLp w).snd := by
    simp [r, WithLp.ofLp_sub]
  have hq2 : q.snd = ContinuousLinearMap.adjoint Q (WithLp.ofLp w).snd := by simp [q]
  have hfst : Prod.fst ∘ ξ = ϕ := funext fun _ ↦ rfl
  have hsnd : Prod.snd ∘ ξ = ψ := funext fun _ ↦ rfl
  simp only [normalModelAdjoint_apply, hfst, hsnd]
  refine congrArg₂ (· + ·) (by simpa [q, hr1, ξ] using hQsol _ ϕ hϕ hϕc) ?_
  have hψ_lp : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hLψ_lp := (Vortex.continuous_gaugeFixedOperator hx hψ).memLp_of_hasCompactSupport
    (μ := volume) (p := 2) (Vortex.hasCompactSupport_gaugeFixedOperator hψc)
  rw [hq2, ← L2.inner_toLp _ hLψ_lp, ContinuousLinearMap.adjoint_inner_left,
    Vortex.apply_toLp_gaugeFixedOperator_eq_sub_starProjection hx hQsol hQorth hψ hψc,
    inner_sub_right, ← (Vortex.weakGaugeFixedKernel x).inner_starProjection_left_eq_right,
    ← inner_sub_left, ← hr2, L2.inner_toLp r.snd hψ_lp]

/-- **Existence of the complementary normal weak `L²` inverse at a plane vortex.** -/
theorem exists_normalComplementaryInverse (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, Vortex.equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ 𝒬 : NormalL2 volume →L[ℝ] NormalL2 volume,
      normalDomainSlowProj x ∘L 𝒬 = 0 ∧
      𝒬 ∘L normalTargetSlowProj x = 0 ∧
      (∀ (y η : ℂ → EuclideanSpace ℝ (Fin 4)) (hy : ContDiff ℝ 1 y) (hyc : HasCompactSupport y)
          (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η),
        let w : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) := fun z ↦ (y z, η z)
        let hy_lp : MemLp y 2 volume := hy.continuous.memLp_of_hasCompactSupport hyc
        let hη_lp : MemLp η 2 volume := hη.continuous.memLp_of_hasCompactSupport hηc
        let hLy_lp : MemLp (Prod.fst ∘ normalModelOperator x w) 2 volume := by
          have hfst : Prod.fst ∘ w = y := funext fun _ ↦ rfl
          rw [show Prod.fst ∘ normalModelOperator x w = Vortex.gaugeFixedOperator x y from
            funext fun z ↦ by simp [normalModelOperator_apply, hfst]]
          exact (Vortex.continuous_gaugeFixedOperator hx.continuous hy).memLp_of_hasCompactSupport
            (Vortex.hasCompactSupport_gaugeFixedOperator hyc)
        let hAη_lp : MemLp (Prod.snd ∘ normalModelOperator x w) 2 volume := by
          have hsnd : Prod.snd ∘ w = η := funext fun _ ↦ rfl
          rw [show Prod.snd ∘ normalModelOperator x w = Vortex.gaugeFixedAdjoint x η from
            funext fun z ↦ by simp [normalModelOperator_apply, hsnd]]
          exact Vortex.memLp_gaugeFixedAdjoint hx.continuous (hη.of_le (by norm_num)) hηc
        𝒬 (WithLp.toLp 2 (hLy_lp.toLp (Prod.fst ∘ normalModelOperator x w),
            hAη_lp.toLp (Prod.snd ∘ normalModelOperator x w))) =
          (1 - normalDomainSlowProj x)
            (WithLp.toLp 2 (hy_lp.toLp y, hη_lp.toLp η))) ∧
      ∀ w (ϕ ψ : ℂ → EuclideanSpace ℝ (Fin 4)),
        ContDiff ℝ 2 ϕ → HasCompactSupport ϕ → ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        let ξ : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) := fun z ↦ (ϕ z, ψ z)
        let q := WithLp.ofLp (𝒬 w)
        let r := WithLp.ofLp ((1 - normalTargetSlowProj x) w)
        (∫ z, ⟪q.fst z, (normalModelAdjoint x ξ z).fst⟫) +
            (∫ z, ⟪q.snd z, (normalModelAdjoint x ξ z).snd⟫) =
          (∫ z, ⟪r.fst z, (ξ z).fst⟫) + (∫ z, ⟪r.snd z, (ξ z).snd⟫) := by
  obtain ⟨Q, hQsol, hQorth⟩ :=
    Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (μ := volume) hx hsol
      hlim
  have hQorth' f u hu :=
    hQorth f u ((Vortex.mem_weakGaugeFixedKernel_iff_contDiff_two hx.continuous).1 hu)
  exact ⟨normalComplementaryInverse Q,
    normalDomainSlowProj_comp_normalComplementaryInverse hQorth',
    normalComplementaryInverse_comp_normalTargetSlowProj hQorth',
    fun _ _ hy hyc hη hηc ↦ normalComplementaryInverse_toLp_normalModelOperator hx.continuous
      hQsol hQorth' hy hyc hη hηc,
    fun w _ _ hϕ hϕc hψ hψc ↦ integral_inner_normalComplementaryInverse_normalModelAdjoint
      hx.continuous hQsol hQorth' w hϕ hϕc hψ hψc⟩

end SlowProjectionsAndInverse

end TauCeti.SeibergWitten
