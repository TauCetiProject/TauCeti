/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.PDE.Vortex.RightInverse
import TauCeti.Analysis.InnerProductSpace.BlockSum
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
space `NormalL2 μ = L²(ℂ; ℝ⁴) ⊕₂ L²(ℂ; ℝ⁴)` into slow components along
`K_x = Vortex.weakGaugeFixedKernel μ hx` — projected out by `normalDomainSlowProj`
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
end Defs

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}
  {w ξ : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)}

/-- **Formal `L²` adjointness of `normalModelOperator` and `normalModelAdjoint`**. -/
theorem integral_inner_normalModelOperator {μ : Measure ℂ} [μ.IsAddHaarMeasure]
    (hx : Continuous x) (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w) (hξ : ContDiff ℝ 1 ξ) :
    ∫ z, (⟪(normalModelOperator x w z).1, (ξ z).1⟫ + ⟪(normalModelOperator x w z).2, (ξ z).2⟫) ∂μ =
      ∫ z, (⟪(w z).1, (normalModelAdjoint x ξ z).1⟫ +
        ⟪(w z).2, (normalModelAdjoint x ξ z).2⟫) ∂μ := by
  have hw₁ := contDiff_fst.comp hw; have hw₂ := contDiff_snd.comp hw
  have hw₁c : HasCompactSupport (Prod.fst ∘ w) := hwc.comp_left rfl
  have hw₂c : HasCompactSupport (Prod.snd ∘ w) := hwc.comp_left rfl
  have hξ₁ := contDiff_fst.comp hξ; have hξ₂ := contDiff_snd.comp hξ
  have hint {u v : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : Continuous u) (hv : Continuous v)
      (huc : HasCompactSupport u) : Integrable (fun z ↦ ⟪u z, v z⟫) μ :=
    (hu.inner hv).integrable_of_hasCompactSupport (huc.mono fun _ hz h0 ↦ hz (by simp [h0]))
  simp only [normalModelOperator_apply, normalModelAdjoint_apply]
  rw [integral_add (hint (v := fun z ↦ (ξ z).1) (Vortex.continuous_gaugeFixedOperator hx hw₁)
          hξ₁.continuous (Vortex.hasCompactSupport_gaugeFixedOperator hw₁c))
        (hint (v := fun z ↦ (ξ z).2) (Vortex.continuous_gaugeFixedAdjoint hx hw₂)
          hξ₂.continuous (Vortex.hasCompactSupport_gaugeFixedAdjoint hw₂c)),
    integral_add (hint (u := fun z ↦ (w z).1) hw₁.continuous
          (Vortex.continuous_gaugeFixedAdjoint hx hξ₁) hw₁c)
        (hint (u := fun z ↦ (w z).2) hw₂.continuous
          (Vortex.continuous_gaugeFixedOperator hx hξ₂) hw₂c)]
  refine congrArg₂ (· + ·) (Vortex.integral_inner_gaugeFixedOperator hx hw₁ hw₁c hξ₁) ?_
  calc ∫ z, ⟪Vortex.gaugeFixedAdjoint x (Prod.snd ∘ w) z, (ξ z).2⟫ ∂μ
      = ∫ z, ⟪(Prod.snd ∘ ξ) z, Vortex.gaugeFixedAdjoint x (Prod.snd ∘ w) z⟫ ∂μ :=
        integral_congr_ae (ae_of_all _ fun _ ↦ real_inner_comm _ _)
    _ = ∫ z, ⟪Vortex.gaugeFixedOperator x (Prod.snd ∘ ξ) z, (Prod.snd ∘ w) z⟫ ∂μ :=
        (Vortex.integral_inner_gaugeFixedOperator_of_hasCompactSupport_right hx hξ₂ hw₂ hw₂c).symm
    _ = ∫ z, ⟪(w z).2, Vortex.gaugeFixedOperator x (Prod.snd ∘ ξ) z⟫ ∂μ :=
        integral_congr_ae (ae_of_all _ fun _ ↦ real_inner_comm _ _)

private def mkPairKernel
    (P : (ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) →
      ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) (hzero : P 0 = 0)
    (hadd : ∀ {w v}, ContDiff ℝ 2 w → ContDiff ℝ 2 v → ∀ z, P (w + v) z = P w z + P v z)
    (hsmul : ∀ (r : ℝ) w z, P (r • w) z = r • P w z) :
    Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) where
  carrier := {w | ContDiff ℝ 2 w ∧ MemLp (Prod.fst ∘ w) 2 volume ∧
    MemLp (Prod.snd ∘ w) 2 volume ∧ ∀ z, P w z = 0}
  add_mem' := fun ⟨hw, hw₁, hw₂, hwk⟩ ⟨hv, hv₁, hv₂, hvk⟩ ↦
    ⟨hw.add hv, hw₁.add hv₁, hw₂.add hv₂, fun z ↦ by rw [hadd hw hv z, hwk z, hvk z, add_zero]⟩
  zero_mem' := ⟨contDiff_const, MemLp.zero, MemLp.zero, fun z ↦ by simp [hzero]⟩
  smul_mem' r _ := fun ⟨hw, hw₁, hw₂, hwk⟩ ↦ ⟨contDiff_const.smul hw, hw₁.const_smul r,
    hw₂.const_smul r, fun z ↦ by rw [hsmul r _ z, hwk z, smul_zero]⟩
private theorem diff_fst (hw : ContDiff ℝ 2 w) (z : ℂ) : DifferentiableAt ℝ (Prod.fst ∘ w) z :=
  (contDiff_fst.comp hw).differentiable (by norm_num) z
private theorem diff_snd (hw : ContDiff ℝ 2 w) (z : ℂ) : DifferentiableAt ℝ (Prod.snd ∘ w) z :=
  (contDiff_snd.comp hw).differentiable (by norm_num) z
/-- **The classical `C²` `L²` kernel of `normalModelOperator x`**. -/
def normalModelKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :=
  mkPairKernel (normalModelOperator x) (normalModelOperator_zero x)
    (fun hw hv z ↦ Prod.ext (Vortex.gaugeFixedOperator_add x (diff_fst hw z) (diff_fst hv z))
      (Vortex.gaugeFixedAdjoint_add x (diff_snd hw z) (diff_snd hv z)))
    (fun r w z ↦ Prod.ext (Vortex.gaugeFixedOperator_smul x (Prod.fst ∘ w) r z)
      (Vortex.gaugeFixedAdjoint_smul x (Prod.snd ∘ w) r z))
@[simp] theorem mem_normalModelKernel :
    w ∈ normalModelKernel x ↔ ContDiff ℝ 2 w ∧ MemLp (Prod.fst ∘ w) 2 volume ∧
      MemLp (Prod.snd ∘ w) 2 volume ∧ ∀ z, normalModelOperator x w z = 0 := (Iff.rfl)
/-- **The classical `C²` `L²` kernel of `normalModelAdjoint x`**. -/
def normalModelAdjointKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) :=
  mkPairKernel (normalModelAdjoint x) (normalModelAdjoint_zero x)
    (fun hξ hν z ↦ Prod.ext (Vortex.gaugeFixedAdjoint_add x (diff_fst hξ z) (diff_fst hν z))
      (Vortex.gaugeFixedOperator_add x (diff_snd hξ z) (diff_snd hν z)))
    (fun r ξ z ↦ Prod.ext (Vortex.gaugeFixedAdjoint_smul x (Prod.fst ∘ ξ) r z)
      (Vortex.gaugeFixedOperator_smul x (Prod.snd ∘ ξ) r z))
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
  toFun y := let hy := Vortex.mem_gaugeFixedKernel.1 y.2
    ⟨fun z ↦ (y.1 z, 0), hy.1.prodMk contDiff_const, hy.2.1, MemLp.zero, fun z ↦ by
      have h0 : (Prod.snd ∘ fun w ↦ (y.1 w, (0 : EuclideanSpace ℝ (Fin 4)))) = 0 := by ext; rfl
      rw [normalModelOperator_apply, h0, Vortex.gaugeFixedAdjoint_zero]
      exact Prod.ext (hy.2.2 z) rfl⟩
  map_add' _ _ := by ext z <;> simp
  map_smul' _ _ := by ext z <;> simp
  invFun w := ⟨Prod.fst ∘ w.1, Vortex.mem_gaugeFixedKernel.2
    ⟨contDiff_fst.comp w.2.1, w.2.2.1, fun z ↦ (Prod.mk.inj (w.2.2.2.2 z)).1⟩⟩
  left_inv _ := by ext; rfl
  right_inv w := Subtype.ext <| funext fun z ↦ Prod.ext rfl
    (congrFun (snd_eq_zero_of_mem_normalModelKernel hx hsol w.2) z).symm
/-- **Cokernel (adjoint kernel) identification at a plane vortex**: `g ↦ (0, g)`. -/
def normalModelAdjointKernelEquiv : Vortex.gaugeFixedKernel x ≃ₗ[ℝ] normalModelAdjointKernel x where
  toFun g := let hg := Vortex.mem_gaugeFixedKernel.1 g.2
    ⟨fun z ↦ (0, g.1 z), contDiff_const.prodMk hg.1, MemLp.zero, hg.2.1, fun z ↦ by
      have h0 : (Prod.fst ∘ fun w ↦ ((0 : EuclideanSpace ℝ (Fin 4)), g.1 w)) = 0 := by ext; rfl
      rw [normalModelAdjoint_apply, h0, Vortex.gaugeFixedAdjoint_zero]
      exact Prod.ext rfl (hg.2.2 z)⟩
  map_add' _ _ := by ext z <;> simp
  map_smul' _ _ := by ext z <;> simp
  invFun ξ := ⟨Prod.snd ∘ ξ.1, Vortex.mem_gaugeFixedKernel.2
    ⟨contDiff_snd.comp ξ.2.1, ξ.2.2.2.1, fun z ↦ (Prod.mk.inj (ξ.2.2.2.2 z)).2⟩⟩
  left_inv _ := by ext; rfl
  right_inv ξ := Subtype.ext <| funext fun z ↦ Prod.ext
    (congrFun (fst_eq_zero_of_mem_normalModelAdjointKernel hx hsol ξ.2) z).symm rfl
@[simp] theorem coe_normalModelKernelEquiv_apply (y : Vortex.gaugeFixedKernel x) (z : ℂ) :
    (normalModelKernelEquiv hx hsol y : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) z =
      (y.1 z, 0) := (rfl)
@[simp] theorem coe_normalModelAdjointKernelEquiv_apply (g : Vortex.gaugeFixedKernel x) (z : ℂ) :
    (normalModelAdjointKernelEquiv hx hsol g :
      ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) z = (0, g.1 z) := (rfl)
@[simp] theorem coe_normalModelKernelEquiv_symm_apply (w : normalModelKernel x) (z : ℂ) :
    ((normalModelKernelEquiv hx hsol).symm w : ℂ → EuclideanSpace ℝ (Fin 4)) z = (w.1 z).1 := (rfl)
@[simp] theorem coe_normalModelAdjointKernelEquiv_symm_apply
    (ξ : normalModelAdjointKernel x) (z : ℂ) :
    ((normalModelAdjointKernelEquiv hx hsol).symm ξ : ℂ → EuclideanSpace ℝ (Fin 4)) z =
      (ξ.1 z).2 := (rfl)
end KernelEquivs
end NormalModel

/-! ### Normal slow projections `Π₊`, `Π₋` and complementary weak `L²` inverse `𝒬` -/

section SlowProjectionsAndInverse

/-- The eight-real-component normal `L²` Hilbert space `L²(ℂ; ℝ⁴) ⊕₂ L²(ℂ; ℝ⁴)`. -/
abbrev NormalL2 (μ : Measure ℂ) : Type :=
  WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}

section SlowProj
variable (hx : Continuous x)
/-- **The normal domain slow projection** `Π₊(y, η) = (P_{K_x} y, 0)` on `NormalL2 μ`. -/
def normalDomainSlowProj (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hx : Continuous x) :
    NormalL2 μ →L[ℝ] NormalL2 μ :=
  (Vortex.weakGaugeFixedKernel μ hx).starProjection.withLpProdMap 2 0
/-- **The normal target slow projection** `Π₋(f, g) = (0, P_{K_x} g)` on `NormalL2 μ`. -/
def normalTargetSlowProj (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hx : Continuous x) :
    NormalL2 μ →L[ℝ] NormalL2 μ :=
  (0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ]
    Lp (EuclideanSpace ℝ (Fin 4)) 2 μ).withLpProdMap 2
    (Vortex.weakGaugeFixedKernel μ hx).starProjection
@[simp] theorem ofLp_normalDomainSlowProj (w : NormalL2 μ) :
    WithLp.ofLp (normalDomainSlowProj μ hx w) =
      ((Vortex.weakGaugeFixedKernel μ hx).starProjection (WithLp.ofLp w).1, 0) := by
  simp [normalDomainSlowProj]
@[simp] theorem fst_normalDomainSlowProj (w : NormalL2 μ) :
    (normalDomainSlowProj μ hx w).fst =
      (Vortex.weakGaugeFixedKernel μ hx).starProjection w.fst := by simp [normalDomainSlowProj]
@[simp] theorem snd_normalDomainSlowProj (w : NormalL2 μ) :
    (normalDomainSlowProj μ hx w).snd = 0 := by simp [normalDomainSlowProj]
@[simp] theorem ofLp_normalTargetSlowProj (w : NormalL2 μ) :
    WithLp.ofLp (normalTargetSlowProj μ hx w) =
      (0, (Vortex.weakGaugeFixedKernel μ hx).starProjection (WithLp.ofLp w).2) := by
  simp [normalTargetSlowProj]
@[simp] theorem fst_normalTargetSlowProj (w : NormalL2 μ) :
    (normalTargetSlowProj μ hx w).fst = 0 := by simp [normalTargetSlowProj]
@[simp] theorem snd_normalTargetSlowProj (w : NormalL2 μ) :
    (normalTargetSlowProj μ hx w).snd =
      (Vortex.weakGaugeFixedKernel μ hx).starProjection w.snd := by simp [normalTargetSlowProj]
/-- `normalDomainSlowProj` is idempotent. -/
@[simp] theorem normalDomainSlowProj_comp_self :
    normalDomainSlowProj μ hx ∘L normalDomainSlowProj μ hx = normalDomainSlowProj μ hx := by
  rw [normalDomainSlowProj, ContinuousLinearMap.withLpProdMap_comp,
    Submodule.starProjection_comp_starProjection_of_le (le_refl _), ContinuousLinearMap.zero_comp]
/-- `normalTargetSlowProj` is idempotent. -/
@[simp] theorem normalTargetSlowProj_comp_self :
    normalTargetSlowProj μ hx ∘L normalTargetSlowProj μ hx = normalTargetSlowProj μ hx := by
  rw [normalTargetSlowProj, ContinuousLinearMap.withLpProdMap_comp, ContinuousLinearMap.zero_comp,
    Submodule.starProjection_comp_starProjection_of_le (le_refl _)]
/-- `normalDomainSlowProj` is self-adjoint on `NormalL2 μ`. -/
theorem isSelfAdjoint_normalDomainSlowProj : IsSelfAdjoint (normalDomainSlowProj μ hx) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
    (Vortex.weakGaugeFixedKernel μ hx).starProjection_isSymmetric).withLpProdMap
    (IsSelfAdjoint.zero _)
/-- `normalTargetSlowProj` is self-adjoint on `NormalL2 μ`. -/
theorem isSelfAdjoint_normalTargetSlowProj : IsSelfAdjoint (normalTargetSlowProj μ hx) :=
  (IsSelfAdjoint.zero _).withLpProdMap (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
    (Vortex.weakGaugeFixedKernel μ hx).starProjection_isSymmetric)
/-- `normalDomainSlowProj` is a contraction (`‖Π₊‖ ≤ 1`). -/
theorem norm_normalDomainSlowProj_le : ‖normalDomainSlowProj μ hx‖ ≤ 1 := by
  rw [normalDomainSlowProj, ContinuousLinearMap.norm_withLpProdMap, norm_zero, max_le_iff]
  exact ⟨(Vortex.weakGaugeFixedKernel μ hx).starProjection_norm_le, zero_le_one⟩
/-- `normalTargetSlowProj` is a contraction (`‖Π₋‖ ≤ 1`). -/
theorem norm_normalTargetSlowProj_le : ‖normalTargetSlowProj μ hx‖ ≤ 1 := by
  rw [normalTargetSlowProj, ContinuousLinearMap.norm_withLpProdMap, norm_zero, max_le_iff]
  exact ⟨zero_le_one, (Vortex.weakGaugeFixedKernel μ hx).starProjection_norm_le⟩
end SlowProj

section ComplementaryInverse
variable (Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)
omit [μ.IsAddHaarMeasure] in
/-- The block-diagonal operator `𝒬(f, g) = (Q f, Q† g)` on `NormalL2 μ`. When `Q` is a weak right
inverse of `L_x` with range orthogonal to `Vortex.weakGaugeFixedKernel μ hx`, this operator acts as
the complementary inverse of `normalModelOperator x` orthogonal to the slow subspaces. -/
def normalComplementaryInverse : NormalL2 μ →L[ℝ] NormalL2 μ :=
  Q.withLpProdMap 2 (ContinuousLinearMap.adjoint Q)
omit [μ.IsAddHaarMeasure] in @[simp] theorem ofLp_normalComplementaryInverse (w : NormalL2 μ) :
    WithLp.ofLp (normalComplementaryInverse Q w) =
      (Q (WithLp.ofLp w).1, ContinuousLinearMap.adjoint Q (WithLp.ofLp w).2) := by
  simp [normalComplementaryInverse]
omit [μ.IsAddHaarMeasure] in @[simp] theorem fst_normalComplementaryInverse (w : NormalL2 μ) :
    (normalComplementaryInverse Q w).fst = Q w.fst := by simp [normalComplementaryInverse]
omit [μ.IsAddHaarMeasure] in @[simp] theorem snd_normalComplementaryInverse (w : NormalL2 μ) :
    (normalComplementaryInverse Q w).snd = ContinuousLinearMap.adjoint Q w.snd := by
  simp [normalComplementaryInverse]
omit [μ.IsAddHaarMeasure] in
/-- The operator norm of `normalComplementaryInverse Q` equals `‖Q‖`. -/
@[simp] theorem norm_normalComplementaryInverse : ‖normalComplementaryInverse Q‖ = ‖Q‖ := by
  simp [normalComplementaryInverse]
end ComplementaryInverse

variable {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}

/-- If the range of `Q` is orthogonal to `Vortex.weakGaugeFixedKernel μ hx`, then
`normalDomainSlowProj μ hx ∘L normalComplementaryInverse Q = 0`. -/
theorem normalDomainSlowProj_comp_normalComplementaryInverse (hx : Continuous x)
    (hQorth : ∀ f u, u ∈ Vortex.weakGaugeFixedKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0) :
    normalDomainSlowProj μ hx ∘L normalComplementaryInverse Q = 0 := by
  ext w : 1; apply (WithLp.ofLp_injective 2)
  have hQmem : Q (WithLp.ofLp w).1 ∈ (Vortex.weakGaugeFixedKernel μ hx)ᗮ :=
    (Submodule.mem_orthogonal _ _).2 fun u hu ↦ by
      rw [real_inner_comm, L2.inner_def]; exact hQorth _ u hu
  rw [ContinuousLinearMap.comp_apply, ofLp_normalDomainSlowProj, ofLp_normalComplementaryInverse,
    (Submodule.starProjection_apply_eq_zero_iff (K := Vortex.weakGaugeFixedKernel μ hx)).2 hQmem]
  rfl
/-- If the range of `Q` is orthogonal to `Vortex.weakGaugeFixedKernel μ hx`, then
`normalComplementaryInverse Q ∘L normalTargetSlowProj μ hx = 0`. -/
theorem normalComplementaryInverse_comp_normalTargetSlowProj (hx : Continuous x)
    (hQorth : ∀ f u, u ∈ Vortex.weakGaugeFixedKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0) :
    normalComplementaryInverse Q ∘L normalTargetSlowProj μ hx = 0 := by
  ext w : 1; apply (WithLp.ofLp_injective 2)
  have hadj0 : ContinuousLinearMap.adjoint Q
      ((Vortex.weakGaugeFixedKernel μ hx).starProjection (WithLp.ofLp w).2) = 0 :=
    ext_inner_right ℝ fun h ↦ by
      rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm, L2.inner_def]
      exact hQorth h _ (Submodule.starProjection_apply_mem _ _)
  rw [ContinuousLinearMap.comp_apply, ofLp_normalComplementaryInverse, ofLp_normalTargetSlowProj,
    map_zero, hadj0]; rfl
/-- **Exact `L²` left-inverse identity**: `𝒬 (L_x y, L_x* η) = (1 - Π₊) (y, η)` on `C²_c`. -/
theorem normalComplementaryInverse_toLp_normalModelOperator (hx : Continuous x)
    (hQsol : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q f z, Vortex.gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (hQorth : ∀ f u, u ∈ Vortex.weakGaugeFixedKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0)
    {y η : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ 2 y) (hyc : HasCompactSupport y)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    let hy_lp : MemLp y 2 μ := hy.continuous.memLp_of_hasCompactSupport hyc
    let hη_lp : MemLp η 2 μ := hη.continuous.memLp_of_hasCompactSupport hηc
    let hLy_lp := (Vortex.continuous_gaugeFixedOperator hx
      (hy.of_le (by norm_num))).memLp_of_hasCompactSupport (μ := μ) (p := 2)
        (Vortex.hasCompactSupport_gaugeFixedOperator hyc)
    let hAη_lp : MemLp (Vortex.gaugeFixedAdjoint x η) 2 μ :=
      Vortex.memLp_gaugeFixedAdjoint hx ⟨η, hη, hηc, by simp⟩
    normalComplementaryInverse Q (WithLp.toLp 2 (hLy_lp.toLp (Vortex.gaugeFixedOperator x y),
        hAη_lp.toLp (Vortex.gaugeFixedAdjoint x η))) =
      (1 - normalDomainSlowProj μ hx) (WithLp.toLp 2 (hy_lp.toLp y, hη_lp.toLp η)) := by
  intro hy_lp hη_lp hLy_lp hAη_lp; apply (WithLp.ofLp_injective 2)
  rw [ofLp_normalComplementaryInverse, sub_apply, one_apply_eq_self, WithLp.ofLp_sub,
    ofLp_normalDomainSlowProj]
  refine Prod.ext (Vortex.apply_toLp_gaugeFixedOperator_eq_sub_starProjection hx hQsol hQorth
    (hy.of_le (by norm_num)) hyc) ?_
  dsimp only [Prod.snd_sub]; rw [sub_zero]; exact ext_inner_right ℝ fun h ↦ by
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm, L2.inner_toLp (Q h) hAη_lp,
      hQsol h η hη hηc, ← L2.inner_toLp h hη_lp, real_inner_comm]
/-- **Weak right-inverse identity**: `𝓜_x (𝒬 w) = (1 - Π₋) w` weakly against `(ϕ, ψ) ∈ C²_c`. -/
theorem integral_inner_normalComplementaryInverse_normalModelAdjoint (hx : Continuous x)
    (hQsol : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q f z, Vortex.gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (hQorth : ∀ f u, u ∈ Vortex.weakGaugeFixedKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0)
    (w : NormalL2 μ) {ϕ ψ : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hϕ : ContDiff ℝ 2 ϕ) (hϕc : HasCompactSupport ϕ)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    let q := WithLp.ofLp (normalComplementaryInverse Q w)
    let r := WithLp.ofLp ((1 - normalTargetSlowProj μ hx) w)
    (∫ z, ⟪q.1 z, Vortex.gaugeFixedAdjoint x ϕ z⟫ ∂μ) +
        (∫ z, ⟪q.2 z, Vortex.gaugeFixedOperator x ψ z⟫ ∂μ) =
      (∫ z, ⟪r.1 z, ϕ z⟫ ∂μ) + (∫ z, ⟪r.2 z, ψ z⟫ ∂μ) := by
  intro q r
  have hq := ofLp_normalComplementaryInverse Q w
  have hr : r = ((WithLp.ofLp w).1,
      (WithLp.ofLp w).2 - (Vortex.weakGaugeFixedKernel μ hx).starProjection (WithLp.ofLp w).2) := by
    dsimp only [r]; rw [sub_apply, one_apply_eq_self, WithLp.ofLp_sub, ofLp_normalTargetSlowProj]
    exact Prod.ext (sub_zero _) rfl
  refine congrArg₂ (· + ·)
    (by rw [congrArg Prod.fst hq, congrArg Prod.fst hr]; exact hQsol _ ϕ hϕ hϕc) ?_
  have hψ_lp : MemLp ψ 2 μ := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hLψ_lp : MemLp (Vortex.gaugeFixedOperator x ψ) 2 μ :=
    (Vortex.continuous_gaugeFixedOperator hx (hψ.of_le (by norm_num))).memLp_of_hasCompactSupport
      (Vortex.hasCompactSupport_gaugeFixedOperator hψc)
  calc ∫ z, ⟪q.2 z, Vortex.gaugeFixedOperator x ψ z⟫ ∂μ
      = ⟪ContinuousLinearMap.adjoint Q (WithLp.ofLp w).2,
          hLψ_lp.toLp (Vortex.gaugeFixedOperator x ψ)⟫ := by
        rw [congrArg Prod.snd hq]; exact (L2.inner_toLp _ hLψ_lp).symm
    _ = ⟪(WithLp.ofLp w).2,
          hψ_lp.toLp ψ - (Vortex.weakGaugeFixedKernel μ hx).starProjection (hψ_lp.toLp ψ)⟫ := by
        rw [ContinuousLinearMap.adjoint_inner_left,
          Vortex.apply_toLp_gaugeFixedOperator_eq_sub_starProjection hx hQsol hQorth
            (hψ.of_le (by norm_num)) hψc]
    _ = ⟪r.2, hψ_lp.toLp ψ⟫ := by
        rw [congrArg Prod.snd hr, inner_sub_left, inner_sub_right,
          (Vortex.weakGaugeFixedKernel μ hx).inner_starProjection_left_eq_right]
    _ = ∫ z, ⟪r.2 z, ψ z⟫ ∂μ := L2.inner_toLp r.2 hψ_lp
/-- **Existence of the complementary normal weak `L²` inverse at a plane vortex.** -/
theorem exists_normalComplementaryInverse (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, Vortex.equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ 𝒬 : NormalL2 μ →L[ℝ] NormalL2 μ,
      normalDomainSlowProj μ hx.continuous ∘L 𝒬 = 0 ∧
      𝒬 ∘L normalTargetSlowProj μ hx.continuous = 0 ∧
      (∀ (y η : ℂ → EuclideanSpace ℝ (Fin 4)) (hy : ContDiff ℝ 2 y) (hyc : HasCompactSupport y)
          (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η),
        let hy_lp : MemLp y 2 μ := hy.continuous.memLp_of_hasCompactSupport hyc
        let hη_lp : MemLp η 2 μ := hη.continuous.memLp_of_hasCompactSupport hηc
        let hLy_lp := (Vortex.continuous_gaugeFixedOperator hx.continuous
          (hy.of_le (by norm_num))).memLp_of_hasCompactSupport (μ := μ) (p := 2)
            (Vortex.hasCompactSupport_gaugeFixedOperator hyc)
        let hAη_lp : MemLp _ 2 μ :=
          Vortex.memLp_gaugeFixedAdjoint hx.continuous ⟨η, hη, hηc, by simp⟩
        𝒬 (WithLp.toLp 2 (hLy_lp.toLp (Vortex.gaugeFixedOperator x y),
            hAη_lp.toLp (Vortex.gaugeFixedAdjoint x η))) =
          (1 - normalDomainSlowProj μ hx.continuous)
            (WithLp.toLp 2 (hy_lp.toLp y, hη_lp.toLp η))) ∧
      ∀ w (ϕ ψ : ℂ → EuclideanSpace ℝ (Fin 4)),
        ContDiff ℝ 2 ϕ → HasCompactSupport ϕ → ContDiff ℝ 2 ψ → HasCompactSupport ψ →
        let q := WithLp.ofLp (𝒬 w)
        let r := WithLp.ofLp ((1 - normalTargetSlowProj μ hx.continuous) w)
        (∫ z, ⟪q.1 z, Vortex.gaugeFixedAdjoint x ϕ z⟫ ∂μ) +
            (∫ z, ⟪q.2 z, Vortex.gaugeFixedOperator x ψ z⟫ ∂μ) =
          (∫ z, ⟪r.1 z, ϕ z⟫ ∂μ) + (∫ z, ⟪r.2 z, ψ z⟫ ∂μ) := by
  obtain ⟨Q, hQsol, hQorth⟩ :=
    Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (μ := μ) hx hsol hlim
  have hQorth' :
      ∀ f u, u ∈ Vortex.weakGaugeFixedKernel μ hx.continuous → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0 :=
    fun f u hu ↦ hQorth f u ((Vortex.mem_weakGaugeFixedKernel_iff hx.continuous u).1 hu)
  exact ⟨normalComplementaryInverse Q,
    normalDomainSlowProj_comp_normalComplementaryInverse hx.continuous hQorth',
    normalComplementaryInverse_comp_normalTargetSlowProj hx.continuous hQorth',
    fun _ _ hy hyc hη hηc ↦ normalComplementaryInverse_toLp_normalModelOperator hx.continuous
      hQsol hQorth' hy hyc hη hηc,
    fun w _ _ hϕ hϕc hψ hψc ↦ integral_inner_normalComplementaryInverse_normalModelAdjoint
      hx.continuous hQsol hQorth' w hϕ hϕc hψ hψc⟩

end SlowProjectionsAndInverse

end TauCeti.SeibergWitten
