/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.PDE.SeibergWitten.Normal.Operator
public import TauCeti.Analysis.PDE.Vortex.WeakKernel
import TauCeti.Analysis.InnerProductSpace.Spectral.BlockSum
import TauCeti.Analysis.PDE.Vortex.AdjointKernel
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Normal slow projections, kernel identifications, and complementary `L²` inverse

By `gaugeFixedFlatOperator_normalPerturbation`, linearizing the four-dimensional gauge-fixed flat
Seiberg–Witten operator along a normal plane around a pulled-back configuration `x : ℂ → ℝ⁴` gives
the decoupled pair `𝓜_x (y, η) = (L_x y, L_x* η)` (`normalModelOperator`) with formal `L²` adjoint
`𝓜_x* (ϕ, ψ) = (L_x* ϕ, L_x ψ)` (`normalModelAdjoint`), where `L_x = Vortex.gaugeFixedOperator x`
and `L_x* = Vortex.gaugeFixedAdjoint x`.

At a differentiable plane vortex (`Vortex.equation x = 0`), the classical `C²` square-integrable
kernel of `L_x*` vanishes, so the classical `C²` square-integrable kernels of `𝓜_x` and `𝓜_x*` both
identify with `Vortex.gaugeFixedKernel x` in the `y`- and `ψ`-slots respectively. In the normal
reduction, this splits the product Hilbert space `NormalL2 volume = L²(ℂ; ℝ⁴) ⊕₂ L²(ℂ; ℝ⁴)` into
slow components along `K_x = Vortex.weakGaugeFixedKernel x` — projected out by
`normalDomainSlowProj` (`Π₊(y, η) = (P_{K_x} y, 0)`) and `normalTargetSlowProj`
(`Π₋(f, g) = (0, P_{K_x} g)`) — and fast components on their complements. On `NormalL2 μ` for a
general measure `μ`, `normalComplementaryInverse Q` defines the block-diagonal map
`𝒬(f, g) = (Q f, Q† g)`. For `μ = volume`, when `Q` is a weak right inverse of `L_x` with range
orthogonal to `K_x`, `𝒬` satisfies the `L²` left-inverse identity `𝒬 (𝓜_x (y, η)) = (1 - Π₊) (y, η)`
on compactly supported `C¹ × C²` inputs (`normalComplementaryInverse_toLp_normalModelOperator`) and
the weak right-inverse identity `𝓜_x (𝒬 w) = (1 - Π₋) w` against `normalModelAdjoint x` on
compactly supported `C² × C¹` test pairs
(`integral_inner_normalComplementaryInverse_normalModelAdjoint`).

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334, §2–3.
-/

public section

noncomputable section

open Complex Filter MeasureTheory
open scoped RealInnerProductSpace ContDiff Topology

namespace TauCeti.SeibergWitten

/-! ### Classical kernel and adjoint-kernel identifications -/

section NormalModel

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
  simp only [normalModelOperator_apply, normalModelAdjoint_apply]
  rw [integral_add
        ((hc₁.imp Vortex.hasCompactSupport_gaugeFixedOperator id).elim
          ((Vortex.continuous_gaugeFixedOperator hx hw₁).integrable_inner_of_hasCompactSupport_left
            hξ₁.continuous)
          ((Vortex.continuous_gaugeFixedOperator hx hw₁).integrable_inner_of_hasCompactSupport_right
            hξ₁.continuous))
        ((hc₂.imp Vortex.hasCompactSupport_gaugeFixedAdjoint id).elim
          ((Vortex.continuous_gaugeFixedAdjoint hx hw₂).integrable_inner_of_hasCompactSupport_left
            hξ₂.continuous)
          ((Vortex.continuous_gaugeFixedAdjoint hx hw₂).integrable_inner_of_hasCompactSupport_right
            hξ₂.continuous)),
    integral_add
        ((hc₁.imp id Vortex.hasCompactSupport_gaugeFixedAdjoint).elim
          (hw₁.continuous.integrable_inner_of_hasCompactSupport_left
            (Vortex.continuous_gaugeFixedAdjoint hx hξ₁))
          (hw₁.continuous.integrable_inner_of_hasCompactSupport_right
            (Vortex.continuous_gaugeFixedAdjoint hx hξ₁)))
        ((hc₂.imp id Vortex.hasCompactSupport_gaugeFixedOperator).elim
          (hw₂.continuous.integrable_inner_of_hasCompactSupport_left
            (Vortex.continuous_gaugeFixedOperator hx hξ₂))
          (hw₂.continuous.integrable_inner_of_hasCompactSupport_right
            (Vortex.continuous_gaugeFixedOperator hx hξ₂)))]
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
private def normalModelKernelSwapEquiv (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    normalModelKernel x ≃ₗ[ℝ] normalModelAdjointKernel x where
  toFun w :=
    let hw := mem_normalModelKernel.1 w.property
    let f : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) :=
      fun z ↦ LinearEquiv.prodComm ℝ _ _ (w.val z)
    have hf₁ : Prod.fst ∘ f = Prod.snd ∘ w.val := rfl
    have hf₂ : Prod.snd ∘ f = Prod.fst ∘ w.val := rfl
    ⟨f, (contDiff_snd.comp hw.1).prodMk (contDiff_fst.comp hw.1), hw.2.2.1, hw.2.1, fun z ↦ by
      rw [normalModelAdjoint_apply, hf₁, hf₂]
      exact Prod.ext (by simpa [normalModelOperator_apply] using (Prod.mk.inj (hw.2.2.2 z)).2)
        (by simpa [normalModelOperator_apply] using (Prod.mk.inj (hw.2.2.2 z)).1)⟩
  map_add' _ _ := by ext z <;> rfl
  map_smul' _ _ := by ext z <;> rfl
  invFun ξ :=
    let hξ := mem_normalModelAdjointKernel.1 ξ.property
    let f : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) :=
      fun z ↦ (LinearEquiv.prodComm ℝ _ _).symm (ξ.val z)
    have hf₁ : Prod.fst ∘ f = Prod.snd ∘ ξ.val := rfl
    have hf₂ : Prod.snd ∘ f = Prod.fst ∘ ξ.val := rfl
    ⟨f, (contDiff_snd.comp hξ.1).prodMk (contDiff_fst.comp hξ.1), hξ.2.2.1, hξ.2.1, fun z ↦ by
      rw [normalModelOperator_apply, hf₁, hf₂]
      exact Prod.ext (by simpa [normalModelAdjoint_apply] using (Prod.mk.inj (hξ.2.2.2 z)).2)
        (by simpa [normalModelAdjoint_apply] using (Prod.mk.inj (hξ.2.2.2 z)).1)⟩
  left_inv _ := by ext z <;> rfl
  right_inv _ := by ext z <;> rfl

/-- At a differentiable plane vortex, the `L_x*` block of `normalModelOperator x` has trivial
classical `C²` square-integrable kernel, so the second component of every element of
`normalModelKernel x` vanishes. -/
theorem snd_eq_zero_of_mem_normalModelKernel (hx : Differentiable ℝ x)
    (hsol : ∀ z, Vortex.equation x z = 0) (hw : w ∈ normalModelKernel x) : Prod.snd ∘ w = 0 := by
  rcases (mem_normalModelKernel.1 hw) with ⟨hwc, -, hw₂, hwk⟩
  exact Vortex.eq_zero_of_memLp_of_gaugeFixedAdjoint_eq_zero hx (contDiff_snd.comp hwc) hw₂ hsol
    (funext fun z ↦ by simpa [normalModelOperator_apply] using (Prod.mk.inj (hwk z)).2)

/-- At a differentiable plane vortex, the `L_x*` block of `normalModelAdjoint x` has trivial
classical `C²` square-integrable kernel, so the first component of every element of
`normalModelAdjointKernel x` vanishes. -/
theorem fst_eq_zero_of_mem_normalModelAdjointKernel (hx : Differentiable ℝ x)
    (hsol : ∀ z, Vortex.equation x z = 0) (hξ : ξ ∈ normalModelAdjointKernel x) :
    Prod.fst ∘ ξ = 0 :=
  snd_eq_zero_of_mem_normalModelKernel hx hsol
    ((normalModelKernelSwapEquiv x).symm ⟨ξ, hξ⟩).property

section KernelEquivs
variable (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0)
/-- **Classical kernel identification at a plane vortex**: `y ↦ (y, 0)`. -/
def normalModelKernelEquiv : Vortex.gaugeFixedKernel x ≃ₗ[ℝ] normalModelKernel x where
  toFun y := let hy := Vortex.mem_gaugeFixedKernel.1 y.property
    ⟨fun z ↦ (y.val z, 0), hy.1.prodMk contDiff_const, hy.2.1, MemLp.zero, fun z ↦ by
      rw [normalModelOperator_apply]
      exact Prod.ext (hy.2.2 z) (congrFun (Vortex.gaugeFixedAdjoint_zero x) z)⟩
  map_add' _ _ := by ext z <;> simp
  map_smul' _ _ := by ext z <;> simp
  invFun w := let hw := mem_normalModelKernel.1 w.property
    ⟨Prod.fst ∘ w.val, Vortex.mem_gaugeFixedKernel.2
      ⟨contDiff_fst.comp hw.1, hw.2.1, fun z ↦ by
        simpa [normalModelOperator_apply] using (Prod.mk.inj (hw.2.2.2 z)).1⟩⟩
  left_inv _ := by ext z; simp
  right_inv w := Subtype.ext <| funext fun z ↦ Prod.ext rfl
    (congrFun (snd_eq_zero_of_mem_normalModelKernel hx hsol w.property) z).symm
/-- **Classical adjoint-kernel identification at a plane vortex**: `g ↦ (0, g)`. -/
def normalModelAdjointKernelEquiv : Vortex.gaugeFixedKernel x ≃ₗ[ℝ] normalModelAdjointKernel x :=
  (normalModelKernelEquiv hx hsol).trans (normalModelKernelSwapEquiv x)
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

section KernelToLp

private def mkPairKernelToLp
    (K : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)))
    (h1 : ∀ w ∈ K, MemLp (Prod.fst ∘ w) 2 volume)
    (h2 : ∀ w ∈ K, MemLp (Prod.snd ∘ w) 2 volume) :
    K →ₗ[ℝ]
      WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) ×
        Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) where
  toFun w := WithLp.toLp 2 ((h1 w.val w.property).toLp (Prod.fst ∘ w.val),
    (h2 w.val w.property).toLp (Prod.snd ∘ w.val))
  map_add' u v := by
    apply WithLp.ofLp_injective 2
    simp only [WithLp.ofLp_add]
    exact Prod.ext (MemLp.toLp_add (h1 u.val u.property) (h1 v.val v.property))
      (MemLp.toLp_add (h2 u.val u.property) (h2 v.val v.property))
  map_smul' r w := by
    apply WithLp.ofLp_injective 2
    simp only [RingHom.id_apply, WithLp.ofLp_smul]
    exact Prod.ext (MemLp.toLp_const_smul r (h1 w.val w.property))
      (MemLp.toLp_const_smul r (h2 w.val w.property))

/-- The real-linear map sending a classical kernel element `w ∈ normalModelKernel x` to its
componentwise `L²` class in `L²(ℂ; ℝ⁴) ⊕₂ L²(ℂ; ℝ⁴)`. -/
def normalModelKernelToLp (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    normalModelKernel x →ₗ[ℝ]
      WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) ×
        Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) :=
  mkPairKernelToLp (normalModelKernel x) (fun _ hw ↦ (mem_normalModelKernel.1 hw).2.1)
    (fun _ hw ↦ (mem_normalModelKernel.1 hw).2.2.1)

/-- The real-linear map sending a classical adjoint-kernel element `ξ ∈ normalModelAdjointKernel x`
to its componentwise `L²` class in `L²(ℂ; ℝ⁴) ⊕₂ L²(ℂ; ℝ⁴)`. -/
def normalModelAdjointKernelToLp (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    normalModelAdjointKernel x →ₗ[ℝ]
      WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) ×
        Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) :=
  mkPairKernelToLp (normalModelAdjointKernel x)
    (fun _ hξ ↦ (mem_normalModelAdjointKernel.1 hξ).2.1)
    (fun _ hξ ↦ (mem_normalModelAdjointKernel.1 hξ).2.2.1)

@[simp] theorem fst_normalModelKernelToLp (w : normalModelKernel x) :
    (normalModelKernelToLp x w).fst =
      (mem_normalModelKernel.1 w.property).2.1.toLp (Prod.fst ∘ w.val) :=
  (rfl)

@[simp] theorem snd_normalModelKernelToLp (w : normalModelKernel x) :
    (normalModelKernelToLp x w).snd =
      (mem_normalModelKernel.1 w.property).2.2.1.toLp (Prod.snd ∘ w.val) :=
  (rfl)

@[simp] theorem fst_normalModelAdjointKernelToLp (ξ : normalModelAdjointKernel x) :
    (normalModelAdjointKernelToLp x ξ).fst =
      (mem_normalModelAdjointKernel.1 ξ.property).2.1.toLp (Prod.fst ∘ ξ.val) :=
  (rfl)

@[simp] theorem snd_normalModelAdjointKernelToLp (ξ : normalModelAdjointKernel x) :
    (normalModelAdjointKernelToLp x ξ).snd =
      (mem_normalModelAdjointKernel.1 ξ.property).2.2.1.toLp (Prod.snd ∘ ξ.val) :=
  (rfl)

end KernelToLp
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
  (ContinuousLinearMap.isSelfAdjoint_withLpProdMap_iff _ _).2
    ⟨isSelfAdjoint_starProjection (Vortex.weakGaugeFixedKernel x), IsSelfAdjoint.zero _⟩
/-- `normalTargetSlowProj` is self-adjoint on `NormalL2 volume`. -/
theorem isSelfAdjoint_normalTargetSlowProj : IsSelfAdjoint (normalTargetSlowProj x) :=
  (ContinuousLinearMap.isSelfAdjoint_withLpProdMap_iff _ _).2
    ⟨IsSelfAdjoint.zero _, isSelfAdjoint_starProjection (Vortex.weakGaugeFixedKernel x)⟩
/-- `normalDomainSlowProj` is a contraction (`‖Π₊‖ ≤ 1`). -/
theorem norm_normalDomainSlowProj_le : ‖normalDomainSlowProj x‖ ≤ 1 := by
  rw [normalDomainSlowProj, ContinuousLinearMap.norm_withLpProdMap, norm_zero, max_le_iff]
  exact ⟨(Vortex.weakGaugeFixedKernel x).starProjection_norm_le, zero_le_one⟩
/-- `normalTargetSlowProj` is a contraction (`‖Π₋‖ ≤ 1`). -/
theorem norm_normalTargetSlowProj_le : ‖normalTargetSlowProj x‖ ≤ 1 := by
  rw [normalTargetSlowProj, ContinuousLinearMap.norm_withLpProdMap, norm_zero, max_le_iff]
  exact ⟨zero_le_one, (Vortex.weakGaugeFixedKernel x).starProjection_norm_le⟩

/-- At a smooth plane vortex with bounded derivatives through order `3`, the range of
`normalDomainSlowProj x` is the componentwise `L²` image of the classical kernel
`normalModelKernel x`. -/
theorem range_normalDomainSlowProj (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, Vortex.equation x z = 0) :
    (normalDomainSlowProj x).range = LinearMap.range (normalModelKernelToLp x) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, rfl⟩
    have hmem : (normalDomainSlowProj x v).fst ∈
        LinearMap.range (Vortex.gaugeFixedKernelToLp x) := by
      rw [fst_normalDomainSlowProj, Vortex.range_gaugeFixedKernelToLp hx hbound]
      exact Submodule.starProjection_apply_mem _ _
    obtain ⟨y, hy⟩ := hmem
    refine ⟨normalModelKernelEquiv (hx.differentiable (by simp)) hsol y,
      WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)⟩
    · rw [WithLp.ofLp_fst, fst_normalModelKernelToLp, ContinuousLinearMap.coe_coe,
        WithLp.ofLp_fst, ← hy, Vortex.gaugeFixedKernelToLp_apply]
      exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (funext fun _ ↦ rfl))
    · rw [WithLp.ofLp_snd, snd_normalModelKernelToLp, ContinuousLinearMap.coe_coe,
        WithLp.ofLp_snd, snd_normalDomainSlowProj]
      have h0 : MemLp (0 : ℂ → EuclideanSpace ℝ (Fin 4)) 2 volume := MemLp.zero
      rw [← MemLp.toLp_zero h0]
      exact MemLp.toLp_congr _ h0 (Filter.EventuallyEq.of_eq (funext fun _ ↦ rfl))
  · rintro _ ⟨w, rfl⟩
    have hw := mem_normalModelKernel.1 w.property
    have hmem : (normalModelKernelToLp x w).fst ∈ Vortex.weakGaugeFixedKernel x := by
      rw [fst_normalModelKernelToLp]
      exact Vortex.toLp_mem_weakGaugeFixedKernel_of_gaugeFixedOperator_eq_zero hx.continuous
        (contDiff_fst.comp (hw.1.of_le one_le_two)) hw.2.1
        fun z ↦ by simpa [normalModelOperator_apply] using (Prod.mk.inj (hw.2.2.2 z)).1
    have hsnd : (normalModelKernelToLp x w).snd = 0 := by
      rw [snd_normalModelKernelToLp]
      have h0 : MemLp (0 : ℂ → EuclideanSpace ℝ (Fin 4)) 2 volume := MemLp.zero
      rw [← MemLp.toLp_zero h0]
      exact MemLp.toLp_congr _ h0 (Filter.EventuallyEq.of_eq
        (snd_eq_zero_of_mem_normalModelKernel (hx.differentiable (by simp)) hsol w.property))
    refine ⟨normalModelKernelToLp x w, WithLp.ofLp_injective 2 ?_⟩
    rw [ContinuousLinearMap.coe_coe, ofLp_normalDomainSlowProj]
    exact Prod.ext (by simpa [WithLp.ofLp_fst] using Submodule.starProjection_eq_self_iff.2 hmem)
      (by simpa [WithLp.ofLp_snd] using hsnd.symm)

/-- At a smooth plane vortex with bounded derivatives through order `3`, the range of
`normalTargetSlowProj x` is the componentwise `L²` image of the classical adjoint kernel
`normalModelAdjointKernel x`. -/
theorem range_normalTargetSlowProj (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, Vortex.equation x z = 0) :
    (normalTargetSlowProj x).range = LinearMap.range (normalModelAdjointKernelToLp x) := by
  let S := LinearIsometryEquiv.withLpProdComm 2 ℝ
    (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ))
    (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ))
  have hproj : (normalTargetSlowProj x).range =
      (normalDomainSlowProj x).range.map S.toLinearEquiv.toLinearMap := by
    ext w
    refine ⟨fun ⟨v, hv⟩ ↦ ⟨normalDomainSlowProj x (S v), ⟨S v, rfl⟩, ?_⟩,
      fun ⟨_, ⟨u, rfl⟩, hu⟩ ↦ ⟨S u, ?_⟩⟩
    · rw [← hv]; apply WithLp.ofLp_injective 2; simp [S]
    · rw [← hu]; apply WithLp.ofLp_injective 2; simp [S]
  have hker : LinearMap.range (normalModelAdjointKernelToLp x) =
      (LinearMap.range (normalModelKernelToLp x)).map S.toLinearEquiv.toLinearMap := by
    have hcomp : normalModelAdjointKernelToLp x ∘ₗ (normalModelKernelSwapEquiv x).toLinearMap =
        S.toLinearEquiv.toLinearMap ∘ₗ normalModelKernelToLp x := by
      refine LinearMap.ext fun w ↦ WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
      · simp only [S, LinearMap.comp_apply, LinearEquiv.coe_coe, WithLp.ofLp_fst,
          fst_normalModelAdjointKernelToLp, LinearIsometryEquiv.coe_toLinearEquiv,
          LinearIsometryEquiv.withLpProdComm_apply, snd_normalModelKernelToLp]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq rfl)
      · simp only [S, LinearMap.comp_apply, LinearEquiv.coe_coe, WithLp.ofLp_snd,
          snd_normalModelAdjointKernelToLp, LinearIsometryEquiv.coe_toLinearEquiv,
          LinearIsometryEquiv.withLpProdComm_apply, fst_normalModelKernelToLp]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq rfl)
    have hrange := congrArg LinearMap.range hcomp
    rwa [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, LinearMap.range_comp] at hrange
  rw [hproj, hker, range_normalDomainSlowProj hx hbound hsol]
end SlowProj

section ComplementaryInverse
variable {μ : Measure ℂ}
  (Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)
/-- The block-diagonal operator `𝒬(f, g) = (Q f, Q† g)` on `NormalL2 μ` for a general measure `μ`.
For `μ = volume`, when `Q` is a weak right inverse of `L_x` with range orthogonal to
`Vortex.weakGaugeFixedKernel x`, `𝒬` satisfies the `L²` left-inverse identity
`𝒬 (𝓜_x (y, η)) = (1 - Π₊) (y, η)` on compactly supported `C¹ × C²` inputs
(`normalComplementaryInverse_toLp_normalModelOperator`) and the weak right-inverse identity
`𝓜_x (𝒬 w) = (1 - Π₋) w` against `normalModelAdjoint x` on compactly supported `C² × C¹` test
pairs (`integral_inner_normalComplementaryInverse_normalModelAdjoint`). -/
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

/-- The first component of `normalModelOperator x (y, η)` lies in `Lᵖ` for continuous `x` and
compactly supported `C¹` `y`. -/
theorem memLp_fst_normalModelOperator (hx : Continuous x) {y η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : ContDiff ℝ 1 y) (hyc : HasCompactSupport y) {p : ENNReal} {μ : Measure ℂ}
    [IsFiniteMeasureOnCompacts μ] :
    MemLp (Prod.fst ∘ normalModelOperator x fun z ↦ (y z, η z)) p μ := by
  rw [fst_comp_normalModelOperator_mk]
  exact (Vortex.continuous_gaugeFixedOperator hx hy).memLp_of_hasCompactSupport
    (Vortex.hasCompactSupport_gaugeFixedOperator hyc)

/-- The second component of `normalModelOperator x (y, η)` lies in `Lᵖ` for continuous `x` and
compactly supported `C¹` `η`. -/
theorem memLp_snd_normalModelOperator (hx : Continuous x) {y η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) {p : ENNReal} {μ : Measure ℂ}
    [IsFiniteMeasureOnCompacts μ] :
    MemLp (Prod.snd ∘ normalModelOperator x fun z ↦ (y z, η z)) p μ := by
  rw [snd_comp_normalModelOperator_mk]
  exact Vortex.memLp_gaugeFixedAdjoint hx hη hηc

private theorem starProjection_weakGaugeFixedKernel_comp_eq_zero
    (hQorth : ∀ f, Q f ∈ (Vortex.weakGaugeFixedKernel x)ᗮ) :
    (Vortex.weakGaugeFixedKernel x).starProjection ∘L Q = 0 := by
  ext f : 1
  rw [ContinuousLinearMap.comp_apply, zero_apply, Submodule.starProjection_apply_eq_zero_iff]
  exact hQorth f

/-- If the range of `Q` is orthogonal to `Vortex.weakGaugeFixedKernel x`, then
`normalDomainSlowProj x ∘L normalComplementaryInverse Q = 0`. -/
theorem normalDomainSlowProj_comp_normalComplementaryInverse
    (hQorth : ∀ f, Q f ∈ (Vortex.weakGaugeFixedKernel x)ᗮ) :
    normalDomainSlowProj x ∘L normalComplementaryInverse Q = 0 := by
  rw [normalDomainSlowProj, normalComplementaryInverse, ← ContinuousLinearMap.withLpProdMap_comp,
    starProjection_weakGaugeFixedKernel_comp_eq_zero hQorth, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.withLpProdMap_zero]

/-- If the range of `Q` is orthogonal to `Vortex.weakGaugeFixedKernel x`, then
`normalComplementaryInverse Q ∘L normalTargetSlowProj x = 0`. -/
theorem normalComplementaryInverse_comp_normalTargetSlowProj
    (hQorth : ∀ f, Q f ∈ (Vortex.weakGaugeFixedKernel x)ᗮ) :
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
    (hQsol : ∀ f, Vortex.IsGaugeFixedWeakSolution volume x f (Q f))
    (hQorth : ∀ f, Q f ∈ (Vortex.weakGaugeFixedKernel x)ᗮ)
    {y η : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ 1 y) (hyc : HasCompactSupport y)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    let w : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) := fun z ↦ (y z, η z)
    let hy_lp : MemLp y 2 volume := hy.continuous.memLp_of_hasCompactSupport hyc
    let hη_lp : MemLp η 2 volume := hη.continuous.memLp_of_hasCompactSupport hηc
    let hLy_lp : MemLp (Prod.fst ∘ normalModelOperator x w) 2 volume :=
      memLp_fst_normalModelOperator hx hy hyc
    let hAη_lp : MemLp (Prod.snd ∘ normalModelOperator x w) 2 volume :=
      memLp_snd_normalModelOperator hx (hη.of_le one_le_two) hηc
    normalComplementaryInverse Q (WithLp.toLp 2 (hLy_lp.toLp (Prod.fst ∘ normalModelOperator x w),
        hAη_lp.toLp (Prod.snd ∘ normalModelOperator x w))) =
      (1 - normalDomainSlowProj x) (WithLp.toLp 2 (hy_lp.toLp y, hη_lp.toLp η)) := by
  intro w hy_lp hη_lp hLy_lp hAη_lp; apply WithLp.ofLp_injective 2
  rw [ofLp_normalComplementaryInverse, sub_apply, one_apply_eq_self, WithLp.ofLp_sub,
    ofLp_normalDomainSlowProj]
  have hLy_eq : hLy_lp.toLp (Prod.fst ∘ normalModelOperator x w) =
      ((Vortex.continuous_gaugeFixedOperator hx hy).memLp_of_hasCompactSupport
        (Vortex.hasCompactSupport_gaugeFixedOperator hyc)).toLp
        (Vortex.gaugeFixedOperator x y) :=
    MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (fst_comp_normalModelOperator_mk x y η))
  refine Prod.ext ?_ ?_
  · dsimp only [Prod.fst_sub]
    rw [hLy_eq]
    exact Vortex.apply_toLp_gaugeFixedOperator_eq_sub_starProjection hx hQsol hQorth hy hyc
  · dsimp only [Prod.snd_sub]; rw [sub_zero]; exact ext_inner_right ℝ fun h ↦ by
      rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm, L2.inner_toLp (Q h) hAη_lp]
      dsimp only [w]
      simp_rw [congrFun (snd_comp_normalModelOperator_mk x y η)]
      rw [(hQsol h).integral_inner_eq hη hηc, ← L2.inner_toLp h hη_lp, real_inner_comm]

/-- **Weak right-inverse identity**: `𝓜_x (𝒬 w) = (1 - Π₋) w` weakly against `ϕ ∈ C²_c` and
`ψ ∈ C¹_c`. -/
theorem integral_inner_normalComplementaryInverse_normalModelAdjoint (hx : Continuous x)
    (hQsol : ∀ f, Vortex.IsGaugeFixedWeakSolution volume x f (Q f))
    (hQorth : ∀ f, Q f ∈ (Vortex.weakGaugeFixedKernel x)ᗮ)
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
  refine congrArg₂ (· + ·) (by simpa [q, hr1, ξ] using (hQsol _).integral_inner_eq hϕ hϕc) ?_
  have hψ_lp : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hLψ_lp := (Vortex.continuous_gaugeFixedOperator hx hψ).memLp_of_hasCompactSupport
    (μ := volume) (p := 2) (Vortex.hasCompactSupport_gaugeFixedOperator hψc)
  rw [hq2, ← L2.inner_toLp _ hLψ_lp, ContinuousLinearMap.adjoint_inner_left,
    Vortex.apply_toLp_gaugeFixedOperator_eq_sub_starProjection hx hQsol hQorth hψ hψc,
    inner_sub_right, ← (Vortex.weakGaugeFixedKernel x).inner_starProjection_left_eq_right,
    ← inner_sub_left, ← hr2, L2.inner_toLp r.snd hψ_lp]

/-- **Existence of the complementary normal weak `L²` inverse at a plane vortex.** Given a
`ContDiff ℝ 1` plane vortex `x` (`Vortex.equation x = 0`) satisfying the asymptotic boundary
condition `4 * (x z 2 ^ 2 + x z 3 ^ 2) → 1` along `cocompact ℂ`, there exists a bounded linear map
`𝒬 : NormalL2 volume →L[ℝ] NormalL2 volume` such that:
1. `normalDomainSlowProj x ∘L 𝒬 = 0` (`Π₊ ∘ 𝒬 = 0`);
2. `𝒬 ∘L normalTargetSlowProj x = 0` (`𝒬 ∘ Π₋ = 0`);
3. `𝒬` is an `L²` left-inverse of `normalModelOperator x` modulo `normalDomainSlowProj x` on
   `ContDiff ℝ 1` × `ContDiff ℝ 2` compactly supported pairs `(y, η)`;
4. `𝒬` is a weak right-inverse of `normalModelOperator x` modulo `normalTargetSlowProj x` against
   `normalModelAdjoint x` on `ContDiff ℝ 2` × `ContDiff ℝ 1` compactly supported test pairs
   `(ϕ, ψ)`. -/
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
        let hLy_lp : MemLp (Prod.fst ∘ normalModelOperator x w) 2 volume :=
          memLp_fst_normalModelOperator hx.continuous hy hyc
        let hAη_lp : MemLp (Prod.snd ∘ normalModelOperator x w) 2 volume :=
          memLp_snd_normalModelOperator hx.continuous (hη.of_le one_le_two) hηc
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
  obtain ⟨Q, hQ⟩ :=
    Vortex.exists_continuousLinearMap_mem_orthogonal_weakGaugeFixedKernel hx hsol hlim
  exact ⟨normalComplementaryInverse Q,
    normalDomainSlowProj_comp_normalComplementaryInverse fun f ↦ (hQ f).2,
    normalComplementaryInverse_comp_normalTargetSlowProj fun f ↦ (hQ f).2,
    fun _ _ hy hyc hη hηc ↦ normalComplementaryInverse_toLp_normalModelOperator hx.continuous
      (fun f ↦ (hQ f).1) (fun f ↦ (hQ f).2) hy hyc hη hηc,
    fun w _ _ hϕ hϕc hψ hψc ↦ integral_inner_normalComplementaryInverse_normalModelAdjoint
      hx.continuous (fun f ↦ (hQ f).1) (fun f ↦ (hQ f).2) w hϕ hϕc hψ hψc⟩

end SlowProjectionsAndInverse

end TauCeti.SeibergWitten
