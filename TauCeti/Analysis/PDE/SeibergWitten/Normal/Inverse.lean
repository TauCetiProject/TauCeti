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

By `TauCeti.SeibergWitten.gaugeFixedFlatSW_normalPerturbation`
(`TauCeti.Analysis.PDE.SeibergWitten.Normal.Operator`), the eight-real-component linearized
gauge-fixed flat Seiberg–Witten operator along a normal plane `ℂ` intertwines with the paired planar
operator

`𝓜_x (y, η) = (L_x y, L_x* η)`

combining the four-component gauge-fixed plane-vortex operator `L_x = Vortex.gaugeFixedOperator x`
on the canonical/normal block `y` with its formal adjoint `L_x* = Vortex.gaugeFixedAdjoint x` on the
anti-canonical/tangential block `η`.

This file develops the kernel/cokernel structure, slow orthogonal projections `Π₊, Π₋`, and
complementary weak `L²` inverse `𝒬` of `𝓜_x`:

* **Normal model operator and kernel/cokernel identifications.** On `ℂ`, `normalModelOperator x` has
  formal `L²` adjoint `normalModelAdjoint x (ϕ, ψ) = (L_x* ϕ, L_x ψ)`
  (`integral_inner_normalModelOperator`). At any differentiable plane vortex
  (`Vortex.equation x = 0`), `TauCeti.Analysis.PDE.Vortex.AdjointKernel` forces the paired `L_x*`
  component to vanish on `C²` square-integrable fields, giving canonical real-linear equivalences
  `normalModelKernelEquiv : Vortex.gaugeFixedKernel x ≃ₗ[ℝ] normalModelKernel x` (`y ↦ (y, 0)`) and
  `normalModelAdjointKernelEquiv : Vortex.gaugeFixedKernel x ≃ₗ[ℝ] normalModelAdjointKernel x`
  (`g ↦ (0, g)`). In particular, `normalModelOperator x` has `L²` index zero (`ker ≃ K_x` and
  `coker ≃ K_x`), whereas `L_x` alone has vanishing cokernel; the vortex index alone does not
  identify the full eight-component normal operator.
* **Slow projections `Π₊, Π₋` and complementary weak `L²` inverse `𝒬`.** On
  `WithLp 2 (L²(ℂ; ℝ⁴) × L²(ℂ; ℝ⁴))`, `weakVortexKernel` is the closed subspace `K_x` of weak `L²`
  solutions of `L_x u = 0` (containing `Vortex.gaugeFixedKernel x`). The orthogonal slow projections
  `normalDomainSlowProj` (`Π₊(y, η) = (P_{K_x} y, 0)`) and `normalTargetSlowProj`
  (`Π₋(f, g) = (0, P_{K_x} g)`) are self-adjoint idempotents of operator norm at most `1`. Given any
  weak right inverse `Q` of `L_x` orthogonal to `K_x`, `normalComplementaryInverse Q`
  (`𝒬(f, g) = (Q f, Q† g)`) satisfies `‖𝒬‖ ≤ ‖Q‖`, `Π₊ ∘L 𝒬 = 0`, `𝒬 ∘L Π₋ = 0`, the exact `L²`
  left-inverse identity `𝒬 (L_x y, L_x* η) = (1 - Π₊) (y, η)` on compactly supported `C²`
  perturbations, and the weak right-inverse identity `𝓜_x (𝒬 w) = (1 - Π₋) w` against all compactly
  supported `C²` test fields. At any `C¹` plane vortex with `|α| → 1` at infinity,
  `exists_normalComplementaryInverse` supplies `𝒬`.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334, §2–3.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980.
-/

public section

noncomputable section

open Complex Filter MeasureTheory
open scoped RealInnerProductSpace Topology ENNReal

namespace TauCeti.SeibergWitten

/-! ### The eight-component normal model operator and kernel/cokernel identifications -/

section NormalModel

/-- **The eight-component normal model operator** `𝓜_x (y, η) = (L_x y, L_x* η)` on the normal
plane `ℂ`, combining the gauge-fixed vortex operator `L_x` on the canonical/normal block `y` with
its formal adjoint `L_x*` on the anti-canonical/tangential block `η`. -/
def normalModelOperator (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (w : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) :=
  (Vortex.gaugeFixedOperator x (Prod.fst ∘ w) z,
   Vortex.gaugeFixedAdjoint x (Prod.snd ∘ w) z)

/-- **The formal `L²` adjoint** `𝓜_x* (ϕ, ψ) = (L_x* ϕ, L_x ψ)` of `normalModelOperator x`,
swapping the vortex operator and its formal adjoint. -/
def normalModelAdjoint (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (ξ : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) :=
  (Vortex.gaugeFixedAdjoint x (Prod.fst ∘ ξ) z,
   Vortex.gaugeFixedOperator x (Prod.snd ∘ ξ) z)

@[simp]
theorem normalModelOperator_apply (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (w : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    normalModelOperator x w z =
      (Vortex.gaugeFixedOperator x (Prod.fst ∘ w) z,
       Vortex.gaugeFixedAdjoint x (Prod.snd ∘ w) z) :=
  (rfl)

@[simp]
theorem normalModelAdjoint_apply (x : ℂ → EuclideanSpace ℝ (Fin 4))
    (ξ : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    normalModelAdjoint x ξ z =
      (Vortex.gaugeFixedAdjoint x (Prod.fst ∘ ξ) z,
       Vortex.gaugeFixedOperator x (Prod.snd ∘ ξ) z) :=
  (rfl)

/-- Integration by parts for `L_x` when the test field `η` (rather than `y`) is compactly
supported. -/
private theorem integral_inner_gaugeFixedOperator_of_hasCompactSupport_right
    {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x y η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Continuous x) (hy : ContDiff ℝ 1 y) (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪Vortex.gaugeFixedOperator x y z, η z⟫ ∂μ =
      ∫ z, ⟪y z, Vortex.gaugeFixedAdjoint x η z⟫ ∂μ := by
  have hyi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ y w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hy
  have hηi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ η w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hη
  have hηic (i : Fin 4) : HasCompactSupport fun w ↦ η w i :=
    hηc.comp_left (g := EuclideanSpace.proj (𝕜 := ℝ) i) (map_zero _)
  set V₁ : ℂ → ℝ := fun w ↦ y w 0 * η w 0 - y w 1 * η w 1 + y w 2 * η w 2 + y w 3 * η w 3
  set V₂ : ℂ → ℝ := fun w ↦ y w 1 * η w 0 + y w 0 * η w 1 - y w 3 * η w 2 + y w 2 * η w 3
  have hV₁ : ContDiff ℝ 1 V₁ := by
    have := hyi; have := hηi
    fun_prop
  have hV₂ : ContDiff ℝ 1 V₂ := by
    have := hyi; have := hηi
    fun_prop
  have hV₁c : HasCompactSupport V₁ :=
    (((hηic 0).mul_left.sub (hηic 1).mul_left).add (hηic 2).mul_left).add (hηic 3).mul_left
  have hV₂c : HasCompactSupport V₂ :=
    (((hηic 0).mul_left.add (hηic 1).mul_left).sub (hηic 2).mul_left).add (hηic 3).mul_left
  have hint (V : ℂ → ℝ) (hV : ContDiff ℝ 1 V) (hVc : HasCompactSupport V) (v : ℂ) :
      Integrable (fun z ↦ fderiv ℝ V z v) μ :=
    ((hV.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hVc.fderiv_apply (𝕜 := ℝ) v)
  have hmain : Integrable (fun z ↦ ⟪y z, Vortex.gaugeFixedAdjoint x η z⟫) μ :=
    (hy.continuous.inner
      (Vortex.continuous_gaugeFixedAdjoint hx hη)).integrable_of_hasCompactSupport
      ((Vortex.hasCompactSupport_gaugeFixedAdjoint (x := x) hηc).mono fun z hz h0 ↦
        hz (by simp [h0]))
  have hgreen (z : ℂ) : ⟪Vortex.gaugeFixedOperator x y z, η z⟫ =
      ⟪y z, Vortex.gaugeFixedAdjoint x η z⟫ + fderiv ℝ V₁ z 1 + fderiv ℝ V₂ z I := by
    have hy_d (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ y w i) z :=
      (hyi i).differentiable one_ne_zero z
    have hη_d (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ η w i) z :=
      (hηi i).differentiable one_ne_zero z
    simp (disch := fun_prop) [V₁, V₂, PiLp.inner_apply, Fin.sum_univ_four, fderiv_fun_mul,
      fderiv_fun_add, fderiv_fun_sub]
    ring
  simp_rw [hgreen]
  rw [integral_add _ (hint V₂ hV₂ hV₂c I), integral_add hmain (hint V₁ hV₁ hV₁c 1),
    integral_fderiv_apply_eq_zero_of_hasCompactSupport hV₁ hV₁c,
    integral_fderiv_apply_eq_zero_of_hasCompactSupport hV₂ hV₂c, add_zero, add_zero]
  exact hmain.add (hint V₁ hV₁ hV₁c 1)

/-- **Formal `L²` adjointness of `normalModelOperator` and `normalModelAdjoint`**:
`∫ (⟪L_x w₁, ξ₁⟫ + ⟪L_x* w₂, ξ₂⟫) = ∫ (⟪w₁, L_x* ξ₁⟫ + ⟪w₂, L_x ξ₂⟫)` for a continuous field `x`,
a compactly supported `C¹` field `w`, and a `C¹` field `ξ`. -/
theorem integral_inner_normalModelOperator {μ : Measure ℂ} [μ.IsAddHaarMeasure]
    {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {w ξ : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)}
    (hx : Continuous x) (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w)
    (hξ : ContDiff ℝ 1 ξ) :
    ∫ z, (⟪(normalModelOperator x w z).1, (ξ z).1⟫ +
        ⟪(normalModelOperator x w z).2, (ξ z).2⟫) ∂μ =
      ∫ z, (⟪(w z).1, (normalModelAdjoint x ξ z).1⟫ +
        ⟪(w z).2, (normalModelAdjoint x ξ z).2⟫) ∂μ := by
  have hw₁ : ContDiff ℝ 1 (Prod.fst ∘ w) := contDiff_fst.comp hw
  have hw₂ : ContDiff ℝ 1 (Prod.snd ∘ w) := contDiff_snd.comp hw
  have hw₁c : HasCompactSupport (Prod.fst ∘ w) := hwc.comp_left rfl
  have hw₂c : HasCompactSupport (Prod.snd ∘ w) := hwc.comp_left rfl
  have hξ₁ : ContDiff ℝ 1 (Prod.fst ∘ ξ) := contDiff_fst.comp hξ
  have hξ₂ : ContDiff ℝ 1 (Prod.snd ∘ ξ) := contDiff_snd.comp hξ
  have hsupp_l {u v : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : HasCompactSupport u) :
      HasCompactSupport fun z ↦ ⟪u z, v z⟫ :=
    hu.mono fun z hz h0 ↦ hz (by simp [h0])
  have hiL₁ : Integrable (fun z ↦ ⟪Vortex.gaugeFixedOperator x (Prod.fst ∘ w) z, (ξ z).1⟫) μ :=
    ((Vortex.continuous_gaugeFixedOperator hx hw₁).inner hξ₁.continuous)
      |>.integrable_of_hasCompactSupport
        (hsupp_l (Vortex.hasCompactSupport_gaugeFixedOperator hw₁c))
  have hiL₂ : Integrable (fun z ↦ ⟪Vortex.gaugeFixedAdjoint x (Prod.snd ∘ w) z, (ξ z).2⟫) μ :=
    ((Vortex.continuous_gaugeFixedAdjoint hx hw₂).inner hξ₂.continuous)
      |>.integrable_of_hasCompactSupport
        (hsupp_l (Vortex.hasCompactSupport_gaugeFixedAdjoint hw₂c))
  have hiR₁ : Integrable (fun z ↦ ⟪(w z).1, Vortex.gaugeFixedAdjoint x (Prod.fst ∘ ξ) z⟫) μ :=
    (hw₁.continuous.inner (Vortex.continuous_gaugeFixedAdjoint hx hξ₁))
      |>.integrable_of_hasCompactSupport (hsupp_l hw₁c)
  have hiR₂ : Integrable (fun z ↦ ⟪(w z).2, Vortex.gaugeFixedOperator x (Prod.snd ∘ ξ) z⟫) μ :=
    (hw₂.continuous.inner (Vortex.continuous_gaugeFixedOperator hx hξ₂))
      |>.integrable_of_hasCompactSupport (hsupp_l hw₂c)
  simp only [normalModelOperator_apply, normalModelAdjoint_apply]
  rw [integral_add hiL₁ hiL₂, integral_add hiR₁ hiR₂]
  congr 1
  · exact Vortex.integral_inner_gaugeFixedOperator hx hw₁ hw₁c hξ₁
  calc ∫ z, ⟪Vortex.gaugeFixedAdjoint x (Prod.snd ∘ w) z, (ξ z).2⟫ ∂μ
      = ∫ z, ⟪(Prod.snd ∘ ξ) z, Vortex.gaugeFixedAdjoint x (Prod.snd ∘ w) z⟫ ∂μ :=
        integral_congr_ae (ae_of_all _ fun z ↦ real_inner_comm _ _)
    _ = ∫ z, ⟪Vortex.gaugeFixedOperator x (Prod.snd ∘ ξ) z, (Prod.snd ∘ w) z⟫ ∂μ :=
        (integral_inner_gaugeFixedOperator_of_hasCompactSupport_right hx hξ₂ hw₂ hw₂c).symm
    _ = ∫ z, ⟪(w z).2, Vortex.gaugeFixedOperator x (Prod.snd ∘ ξ) z⟫ ∂μ :=
        integral_congr_ae (ae_of_all _ fun z ↦ real_inner_comm _ _)

/-- **The classical `C²` `L²` kernel of `normalModelOperator x`**, parallel to
`Vortex.gaugeFixedKernel x`. -/
def normalModelKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) where
  carrier := {w | ContDiff ℝ 2 w ∧ MemLp (Prod.fst ∘ w) 2 volume ∧
    MemLp (Prod.snd ∘ w) 2 volume ∧ ∀ z, normalModelOperator x w z = 0}
  add_mem' := by
    rintro w v ⟨hw, hw₁, hw₂, hwk⟩ ⟨hv, hv₁, hv₂, hvk⟩
    refine ⟨hw.add hv, hw₁.add hv₁, hw₂.add hv₂, fun z ↦ ?_⟩
    have hd₁w := (contDiff_fst.comp hw).differentiable (by norm_num) z
    have hd₁v := (contDiff_fst.comp hv).differentiable (by norm_num) z
    have hd₂w := (contDiff_snd.comp hw).differentiable (by norm_num) z
    have hd₂v := (contDiff_snd.comp hv).differentiable (by norm_num) z
    have hfst : Prod.fst ∘ (w + v) = (Prod.fst ∘ w) + (Prod.fst ∘ v) := rfl
    have hsnd : Prod.snd ∘ (w + v) = (Prod.snd ∘ w) + (Prod.snd ∘ v) := rfl
    rw [normalModelOperator_apply, hfst, hsnd,
      Vortex.gaugeFixedOperator_add x hd₁w hd₁v, Vortex.gaugeFixedAdjoint_add x hd₂w hd₂v,
      (Prod.mk.inj (hwk z)).1, (Prod.mk.inj (hvk z)).1,
      (Prod.mk.inj (hwk z)).2, (Prod.mk.inj (hvk z)).2, add_zero, Prod.mk_zero_zero]
  zero_mem' := ⟨contDiff_const, MemLp.zero, MemLp.zero, fun z ↦ by
    have h0 : (Prod.fst ∘ (0 : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4))) = 0 := rfl
    have h0' : (Prod.snd ∘ (0 : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4))) = 0 := rfl
    have hadj0 : Vortex.gaugeFixedAdjoint x 0 z = 0 := by
      simpa using Vortex.gaugeFixedAdjoint_smul x 0 0 z
    simp [normalModelOperator_apply, h0, h0', hadj0]⟩
  smul_mem' r w := by
    rintro ⟨hw, hw₁, hw₂, hwk⟩
    refine ⟨contDiff_const.smul hw, hw₁.const_smul r, hw₂.const_smul r, fun z ↦ ?_⟩
    have hfst : Prod.fst ∘ (r • w) = r • (Prod.fst ∘ w) := rfl
    have hsnd : Prod.snd ∘ (r • w) = r • (Prod.snd ∘ w) := rfl
    rw [normalModelOperator_apply, hfst, hsnd,
      Vortex.gaugeFixedOperator_smul, Vortex.gaugeFixedAdjoint_smul,
      (Prod.mk.inj (hwk z)).1, (Prod.mk.inj (hwk z)).2, smul_zero, Prod.mk_zero_zero]

@[simp]
theorem mem_normalModelKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {w : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)} :
    w ∈ normalModelKernel x ↔
      ContDiff ℝ 2 w ∧ MemLp (Prod.fst ∘ w) 2 volume ∧
        MemLp (Prod.snd ∘ w) 2 volume ∧ ∀ z, normalModelOperator x w z = 0 :=
  Iff.rfl

/-- **The classical `C²` `L²` kernel of `normalModelAdjoint x`** (representing the `C²` `L²`
cokernel of `normalModelOperator x`). -/
def normalModelAdjointKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) where
  carrier := {ξ | ContDiff ℝ 2 ξ ∧ MemLp (Prod.fst ∘ ξ) 2 volume ∧
    MemLp (Prod.snd ∘ ξ) 2 volume ∧ ∀ z, normalModelAdjoint x ξ z = 0}
  add_mem' := by
    rintro ξ ν ⟨hξ, hξ₁, hξ₂, hξk⟩ ⟨hν, hν₁, hν₂, hνk⟩
    refine ⟨hξ.add hν, hξ₁.add hν₁, hξ₂.add hν₂, fun z ↦ ?_⟩
    have hd₁ξ := (contDiff_fst.comp hξ).differentiable (by norm_num) z
    have hd₁ν := (contDiff_fst.comp hν).differentiable (by norm_num) z
    have hd₂ξ := (contDiff_snd.comp hξ).differentiable (by norm_num) z
    have hd₂ν := (contDiff_snd.comp hν).differentiable (by norm_num) z
    have hfst : Prod.fst ∘ (ξ + ν) = (Prod.fst ∘ ξ) + (Prod.fst ∘ ν) := rfl
    have hsnd : Prod.snd ∘ (ξ + ν) = (Prod.snd ∘ ξ) + (Prod.snd ∘ ν) := rfl
    rw [normalModelAdjoint_apply, hfst, hsnd,
      Vortex.gaugeFixedAdjoint_add x hd₁ξ hd₁ν, Vortex.gaugeFixedOperator_add x hd₂ξ hd₂ν,
      (Prod.mk.inj (hξk z)).1, (Prod.mk.inj (hνk z)).1,
      (Prod.mk.inj (hξk z)).2, (Prod.mk.inj (hνk z)).2, add_zero, Prod.mk_zero_zero]
  zero_mem' := ⟨contDiff_const, MemLp.zero, MemLp.zero, fun z ↦ by
    have h0 : (Prod.fst ∘ (0 : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4))) = 0 := rfl
    have h0' : (Prod.snd ∘ (0 : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4))) = 0 := rfl
    have hadj0 : Vortex.gaugeFixedAdjoint x 0 z = 0 := by
      simpa using Vortex.gaugeFixedAdjoint_smul x 0 0 z
    simp [normalModelAdjoint_apply, h0, h0', hadj0]⟩
  smul_mem' r ξ := by
    rintro ⟨hξ, hξ₁, hξ₂, hξk⟩
    refine ⟨contDiff_const.smul hξ, hξ₁.const_smul r, hξ₂.const_smul r, fun z ↦ ?_⟩
    have hfst : Prod.fst ∘ (r • ξ) = r • (Prod.fst ∘ ξ) := rfl
    have hsnd : Prod.snd ∘ (r • ξ) = r • (Prod.snd ∘ ξ) := rfl
    rw [normalModelAdjoint_apply, hfst, hsnd,
      Vortex.gaugeFixedAdjoint_smul, Vortex.gaugeFixedOperator_smul,
      (Prod.mk.inj (hξk z)).1, (Prod.mk.inj (hξk z)).2, smul_zero, Prod.mk_zero_zero]

@[simp]
theorem mem_normalModelAdjointKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {ξ : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)} :
    ξ ∈ normalModelAdjointKernel x ↔
      ContDiff ℝ 2 ξ ∧ MemLp (Prod.fst ∘ ξ) 2 volume ∧
        MemLp (Prod.snd ∘ ξ) 2 volume ∧ ∀ z, normalModelAdjoint x ξ z = 0 :=
  Iff.rfl

/-- At any differentiable plane vortex (`Vortex.equation x = 0`), the anti-canonical/tangential
component `w.2` of every `w ∈ normalModelKernel x` vanishes identically. -/
theorem snd_eq_zero_of_mem_normalModelKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0)
    {w : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)}
    (hw : w ∈ normalModelKernel x) : Prod.snd ∘ w = 0 := by
  rcases hw with ⟨hwc, -, hw₂, hwk⟩
  exact Vortex.eq_zero_of_memLp_of_gaugeFixedAdjoint_eq_zero hx (contDiff_snd.comp hwc) hw₂ hsol
    (funext fun z ↦ (Prod.mk.inj (hwk z)).2)

/-- At any differentiable plane vortex (`Vortex.equation x = 0`), the first component `ξ.1` of
every `ξ ∈ normalModelAdjointKernel x` vanishes identically. -/
theorem fst_eq_zero_of_mem_normalModelAdjointKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0)
    {ξ : ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)}
    (hξ : ξ ∈ normalModelAdjointKernel x) : Prod.fst ∘ ξ = 0 := by
  rcases hξ with ⟨hξc, hξ₁, -, hξk⟩
  exact Vortex.eq_zero_of_memLp_of_gaugeFixedAdjoint_eq_zero hx (contDiff_fst.comp hξc) hξ₁ hsol
    (funext fun z ↦ (Prod.mk.inj (hξk z)).1)

/-- **Kernel identification at a plane vortex**: `y ↦ (y, 0)` identifies `Vortex.gaugeFixedKernel x`
with the eight-component kernel `normalModelKernel x`. -/
def normalModelKernelEquiv {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0) :
    Vortex.gaugeFixedKernel x ≃ₗ[ℝ] normalModelKernel x where
  toFun y :=
    let hy := Vortex.mem_gaugeFixedKernel.1 y.2
    ⟨fun z ↦ (y.1 z, 0), hy.1.prodMk contDiff_const, hy.2.1, MemLp.zero, fun z ↦ by
      have hsnd : (Prod.snd ∘ fun ζ ↦ (y.1 ζ, (0 : EuclideanSpace ℝ (Fin 4)))) = 0 := rfl
      have hadj0 : Vortex.gaugeFixedAdjoint x 0 z = 0 := by
        simpa using Vortex.gaugeFixedAdjoint_smul x 0 0 z
      rw [normalModelOperator_apply, hsnd, hadj0]
      exact Prod.ext (hy.2.2 z) rfl⟩
  map_add' y₁ y₂ := by ext z <;> simp
  map_smul' r y := by ext z <;> simp
  invFun w := ⟨Prod.fst ∘ w.1, Vortex.mem_gaugeFixedKernel.2
    ⟨contDiff_fst.comp w.2.1, w.2.2.1, fun z ↦ (Prod.mk.inj (w.2.2.2.2 z)).1⟩⟩
  left_inv y := by ext z; rfl
  right_inv w := by
    have hsnd := snd_eq_zero_of_mem_normalModelKernel hx hsol w.2
    apply Subtype.ext
    funext z
    exact Prod.ext rfl (congrFun hsnd z).symm

/-- **Cokernel (adjoint kernel) identification at a plane vortex**: `g ↦ (0, g)` identifies
`Vortex.gaugeFixedKernel x` with `normalModelAdjointKernel x`. Thus the obstruction to solving
`normalModelOperator x (y, η) = (f, g)` lies entirely in the anti-canonical/tangential block `g`
and is canonically isomorphic to the vortex deformation space `Vortex.gaugeFixedKernel x`. -/
def normalModelAdjointKernelEquiv {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0) :
    Vortex.gaugeFixedKernel x ≃ₗ[ℝ] normalModelAdjointKernel x where
  toFun g :=
    let hg := Vortex.mem_gaugeFixedKernel.1 g.2
    ⟨fun z ↦ (0, g.1 z), contDiff_const.prodMk hg.1, MemLp.zero, hg.2.1, fun z ↦ by
      have hfst : (Prod.fst ∘ fun ζ ↦ ((0 : EuclideanSpace ℝ (Fin 4)), g.1 ζ)) = 0 := rfl
      have hadj0 : Vortex.gaugeFixedAdjoint x 0 z = 0 := by
        simpa using Vortex.gaugeFixedAdjoint_smul x 0 0 z
      rw [normalModelAdjoint_apply, hfst, hadj0]
      exact Prod.ext rfl (hg.2.2 z)⟩
  map_add' g₁ g₂ := by ext z <;> simp
  map_smul' r g := by ext z <;> simp
  invFun ξ := ⟨Prod.snd ∘ ξ.1, Vortex.mem_gaugeFixedKernel.2
    ⟨contDiff_snd.comp ξ.2.1, ξ.2.2.2.1, fun z ↦ (Prod.mk.inj (ξ.2.2.2.2 z)).2⟩⟩
  left_inv g := by ext z; rfl
  right_inv ξ := by
    have hfst := fst_eq_zero_of_mem_normalModelAdjointKernel hx hsol ξ.2
    apply Subtype.ext
    funext z
    exact Prod.ext (congrFun hfst z).symm rfl

@[simp]
theorem coe_normalModelKernelEquiv_apply {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0)
    (y : Vortex.gaugeFixedKernel x) (z : ℂ) :
    (normalModelKernelEquiv hx hsol y :
        ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) z =
      (y.1 z, 0) :=
  (rfl)

@[simp]
theorem coe_normalModelAdjointKernelEquiv_apply {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0)
    (g : Vortex.gaugeFixedKernel x) (z : ℂ) :
    (normalModelAdjointKernelEquiv hx hsol g :
        ℂ → EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4)) z =
      (0, g.1 z) :=
  (rfl)

@[simp]
theorem coe_normalModelKernelEquiv_symm_apply {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0)
    (w : normalModelKernel x) (z : ℂ) :
    ((normalModelKernelEquiv hx hsol).symm w : ℂ → EuclideanSpace ℝ (Fin 4)) z = (w.1 z).1 :=
  (rfl)

@[simp]
theorem coe_normalModelAdjointKernelEquiv_symm_apply {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Differentiable ℝ x) (hsol : ∀ z, Vortex.equation x z = 0)
    (ξ : normalModelAdjointKernel x) (z : ℂ) :
    ((normalModelAdjointKernelEquiv hx hsol).symm ξ : ℂ → EuclideanSpace ℝ (Fin 4)) z =
      (ξ.1 z).2 :=
  (rfl)

end NormalModel

/-! ### Normal slow projections `Π₊`, `Π₋` and complementary weak `L²` inverse `𝒬` -/

section SlowProjectionsAndInverse

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}

private abbrev VortexTestField :=
  TestFunction (⊤ : TopologicalSpace.Opens ℂ) (EuclideanSpace ℝ (Fin 4)) 2

omit [μ.IsAddHaarMeasure] in
private theorem memLp_vortexAdjoint [IsFiniteMeasureOnCompacts μ]
    (hx : Continuous x) (η : VortexTestField) :
    MemLp (Vortex.gaugeFixedAdjoint x η) 2 μ :=
  (Vortex.continuous_gaugeFixedAdjoint hx (η.contDiff.of_le (by norm_cast)))
    |>.memLp_of_hasCompactSupport (Vortex.hasCompactSupport_gaugeFixedAdjoint η.hasCompactSupport)

private def vortexAdjointToLp (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hx : Continuous x) :
    VortexTestField →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ where
  toFun η := (memLp_vortexAdjoint hx η).toLp (Vortex.gaugeFixedAdjoint x η)
  map_add' η ν := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ ?_)
    rw [FunLike.coe_add, Pi.add_apply]
    exact Vortex.gaugeFixedAdjoint_add x (η.contDiff.differentiable (by norm_num) z)
      (ν.contDiff.differentiable (by norm_num) z)
  map_smul' t η := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ ?_)
    rw [FunLike.coe_smul, Pi.smul_apply]
    exact Vortex.gaugeFixedAdjoint_smul x η t z

private theorem inner_vortexAdjointToLp (hx : Continuous x)
    (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) (η : VortexTestField) :
    ⟪u, vortexAdjointToLp μ hx η⟫ = ∫ z, ⟪u z, Vortex.gaugeFixedAdjoint x η z⟫ ∂μ :=
  L2.inner_toLp u (memLp_vortexAdjoint hx η)

/-- **The weak `L²` vortex kernel `K_x`**: the closed subspace of `L²(ℂ; ℝ⁴)` consisting of weak
solutions of `L_x u = 0`, defined as the orthogonal complement of `{L_x* η | η ∈ C²_c(ℂ; ℝ⁴)}`. -/
def weakVortexKernel (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hx : Continuous x) :
    Submodule ℝ (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :=
  (LinearMap.range (vortexAdjointToLp μ hx))ᗮ

instance instIsClosedWeakVortexKernel (hx : Continuous x) :
    IsClosed (weakVortexKernel μ hx : Set (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)) :=
  Submodule.isClosed_orthogonal _

instance instHasOrthogonalProjectionWeakVortexKernel (hx : Continuous x) :
    (weakVortexKernel μ hx).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- Membership in `weakVortexKernel` is the weak equation `∫ ⟪u, L_x* η⟫ = 0` against all compactly
supported `C²` test fields `η`. -/
theorem mem_weakVortexKernel_iff (hx : Continuous x)
    (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    u ∈ weakVortexKernel μ hx ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪u z, Vortex.gaugeFixedAdjoint x η z⟫ ∂μ = 0 := by
  rw [weakVortexKernel, Submodule.mem_orthogonal]
  constructor
  · intro h η hη hηc
    let η' : VortexTestField := ⟨η, hη, hηc, by simp⟩
    have h0 := h (vortexAdjointToLp μ hx η') ⟨η', rfl⟩
    rwa [real_inner_comm, inner_vortexAdjointToLp hx] at h0
  · rintro h _ ⟨η, rfl⟩
    rw [real_inner_comm, inner_vortexAdjointToLp hx]
    exact h η η.contDiff η.hasCompactSupport

/-- Every `C¹` `L²` solution of `L_x y = 0` defines an element of `weakVortexKernel μ hx`. -/
theorem toLp_mem_weakVortexKernel_of_gaugeFixedOperator_eq_zero (hx : Continuous x)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ 1 y) (hy_lp : MemLp y 2 μ)
    (hy_ker : ∀ z, Vortex.gaugeFixedOperator x y z = 0) :
    hy_lp.toLp y ∈ weakVortexKernel μ hx := by
  rw [mem_weakVortexKernel_iff hx]
  intro η hη hηc
  have hcongr : ∫ z, ⟪(hy_lp.toLp y) z, Vortex.gaugeFixedAdjoint x η z⟫ ∂μ =
      ∫ z, ⟪y z, Vortex.gaugeFixedAdjoint x η z⟫ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hy_lp.coeFn_toLp] with z hz
    rw [hz]
  rw [hcongr, ← integral_inner_gaugeFixedOperator_of_hasCompactSupport_right hx
    hy (hη.of_le (by norm_num)) hηc]
  simp [hy_ker]

/-- Every classical `C²` `L²` solution in `Vortex.gaugeFixedKernel x` defines an element of
`weakVortexKernel volume hx`. -/
theorem toLp_mem_weakVortexKernel_of_mem_gaugeFixedKernel (hx : Continuous x)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ Vortex.gaugeFixedKernel x) :
    (Vortex.mem_gaugeFixedKernel.1 hy).2.1.toLp y ∈ weakVortexKernel volume hx := by
  rcases Vortex.mem_gaugeFixedKernel.1 hy with ⟨hyc, hy_lp, hy_ker⟩
  exact toLp_mem_weakVortexKernel_of_gaugeFixedOperator_eq_zero hx
    (hyc.of_le (by norm_num)) hy_lp hy_ker

omit [μ.IsAddHaarMeasure] in
/-- Lift a pair of bounded operators `(A, B)` on `L²(ℂ; ℝ⁴)` to the `ℓ²` direct sum
`WithLp 2 (L² × L²)`. -/
private def diagL2 (A B : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ]
    Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) →L[ℝ]
      WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap ∘L
    ((A ∘L WithLp.fstL 2 ℝ _ _).prod (B ∘L WithLp.sndL 2 ℝ _ _))

/-- **The normal domain slow projection** `Π₊(y, η) = (P_{K_x} y, 0)` onto the weak kernel
`K_x × {0}` of `normalModelOperator x`. -/
def normalDomainSlowProj (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hx : Continuous x) :
    WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) →L[ℝ]
      WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :=
  diagL2 (weakVortexKernel μ hx).starProjection 0

/-- **The normal target slow projection** `Π₋(f, g) = (0, P_{K_x} g)` onto the weak obstruction
space `{0} × K_x` (the weak kernel of `normalModelAdjoint x`). -/
def normalTargetSlowProj (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hx : Continuous x) :
    WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) →L[ℝ]
      WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :=
  diagL2 0 (weakVortexKernel μ hx).starProjection

@[simp]
theorem ofLp_normalDomainSlowProj (hx : Continuous x)
    (w : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)) :
    WithLp.ofLp (normalDomainSlowProj μ hx w) =
      ((weakVortexKernel μ hx).starProjection (WithLp.ofLp w).1, 0) :=
  (rfl)

@[simp]
theorem fst_normalDomainSlowProj (hx : Continuous x)
    (w : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)) :
    (normalDomainSlowProj μ hx w).fst = (weakVortexKernel μ hx).starProjection w.fst :=
  (rfl)

@[simp]
theorem snd_normalDomainSlowProj (hx : Continuous x)
    (w : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)) :
    (normalDomainSlowProj μ hx w).snd = 0 :=
  (rfl)

@[simp]
theorem ofLp_normalTargetSlowProj (hx : Continuous x)
    (w : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)) :
    WithLp.ofLp (normalTargetSlowProj μ hx w) =
      (0, (weakVortexKernel μ hx).starProjection (WithLp.ofLp w).2) :=
  (rfl)

@[simp]
theorem fst_normalTargetSlowProj (hx : Continuous x)
    (w : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)) :
    (normalTargetSlowProj μ hx w).fst = 0 :=
  (rfl)

@[simp]
theorem snd_normalTargetSlowProj (hx : Continuous x)
    (w : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)) :
    (normalTargetSlowProj μ hx w).snd = (weakVortexKernel μ hx).starProjection w.snd :=
  (rfl)

@[simp]
theorem normalDomainSlowProj_comp_self (hx : Continuous x) :
    normalDomainSlowProj μ hx ∘L normalDomainSlowProj μ hx = normalDomainSlowProj μ hx := by
  ext w : 1
  apply (WithLp.ofLp_injective 2)
  rw [ContinuousLinearMap.comp_apply, ofLp_normalDomainSlowProj, ofLp_normalDomainSlowProj]
  exact Prod.ext (Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _))
    rfl

@[simp]
theorem normalTargetSlowProj_comp_self (hx : Continuous x) :
    normalTargetSlowProj μ hx ∘L normalTargetSlowProj μ hx = normalTargetSlowProj μ hx := by
  ext w : 1
  apply (WithLp.ofLp_injective 2)
  rw [ContinuousLinearMap.comp_apply, ofLp_normalTargetSlowProj, ofLp_normalTargetSlowProj]
  exact Prod.ext rfl
    (Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _))

theorem isSelfAdjoint_normalDomainSlowProj (hx : Continuous x) :
    IsSelfAdjoint (normalDomainSlowProj μ hx) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  simp only [ContinuousLinearMap.coe_coe]
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply, ofLp_normalDomainSlowProj,
    ofLp_normalDomainSlowProj, inner_zero_left, inner_zero_right, add_zero, add_zero]
  exact (weakVortexKernel μ hx).inner_starProjection_left_eq_right _ _

theorem isSelfAdjoint_normalTargetSlowProj (hx : Continuous x) :
    IsSelfAdjoint (normalTargetSlowProj μ hx) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  simp only [ContinuousLinearMap.coe_coe]
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply, ofLp_normalTargetSlowProj,
    ofLp_normalTargetSlowProj, inner_zero_left, inner_zero_right, zero_add, zero_add]
  exact (weakVortexKernel μ hx).inner_starProjection_left_eq_right _ _

theorem norm_normalDomainSlowProj_le (hx : Continuous x) :
    ‖normalDomainSlowProj μ hx‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w ↦ ?_
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2, fst_normalDomainSlowProj, snd_normalDomainSlowProj]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  have hle := (weakVortexKernel μ hx).norm_starProjection_apply_le w.fst
  have hsq : ‖(weakVortexKernel μ hx).starProjection w.fst‖ ^ 2 ≤ ‖w.fst‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  linarith [sq_nonneg ‖w.snd‖]

theorem norm_normalTargetSlowProj_le (hx : Continuous x) :
    ‖normalTargetSlowProj μ hx‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w ↦ ?_
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2, fst_normalTargetSlowProj, snd_normalTargetSlowProj]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  have hle := (weakVortexKernel μ hx).norm_starProjection_apply_le w.snd
  have hsq : ‖(weakVortexKernel μ hx).starProjection w.snd‖ ^ 2 ≤ ‖w.snd‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  linarith [sq_nonneg ‖w.fst‖]

omit [μ.IsAddHaarMeasure] in
/-- **The complementary normal weak `L²` inverse** `𝒬(f, g) = (Q f, Q† g)` associated to a weak
right inverse `Q` of `L_x`. -/
def normalComplementaryInverse
    (Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) →L[ℝ]
      WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :=
  diagL2 Q (ContinuousLinearMap.adjoint Q)

omit [μ.IsAddHaarMeasure] in
@[simp]
theorem ofLp_normalComplementaryInverse
    (Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)
    (w : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)) :
    WithLp.ofLp (normalComplementaryInverse Q w) =
      (Q (WithLp.ofLp w).1, ContinuousLinearMap.adjoint Q (WithLp.ofLp w).2) :=
  (rfl)

omit [μ.IsAddHaarMeasure] in
@[simp]
theorem fst_normalComplementaryInverse
    (Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)
    (w : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)) :
    (normalComplementaryInverse Q w).fst = Q w.fst :=
  (rfl)

omit [μ.IsAddHaarMeasure] in
@[simp]
theorem snd_normalComplementaryInverse
    (Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)
    (w : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ)) :
    (normalComplementaryInverse Q w).snd = ContinuousLinearMap.adjoint Q w.snd :=
  (rfl)

omit [μ.IsAddHaarMeasure] in
/-- `normalComplementaryInverse Q` has operator norm bounded by `‖Q‖`. -/
theorem norm_normalComplementaryInverse_le
    (Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    ‖normalComplementaryInverse Q‖ ≤ ‖Q‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Q) fun w ↦ ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2, fst_normalComplementaryInverse, snd_normalComplementaryInverse]
  have h1 : ‖Q w.fst‖ ^ 2 ≤ ‖Q‖ ^ 2 * ‖w.fst‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (Q.le_opNorm _) 2
  have h2 : ‖ContinuousLinearMap.adjoint Q w.snd‖ ^ 2 ≤ ‖Q‖ ^ 2 * ‖w.snd‖ ^ 2 := by
    have hadj : ‖ContinuousLinearMap.adjoint Q‖ = ‖Q‖ :=
      LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint Q
    rw [← hadj, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((ContinuousLinearMap.adjoint Q).le_opNorm _) 2
  linarith

/-- Whenever `Q` maps `L²` into `(weakVortexKernel μ hx)ᗮ`, `Π₊ ∘L 𝒬 = 0`: the range of `𝒬` lies in
the fast domain channel `ker Π₊`. -/
theorem normalDomainSlowProj_comp_normalComplementaryInverse (hx : Continuous x)
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQorth : ∀ f u, u ∈ weakVortexKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0) :
    normalDomainSlowProj μ hx ∘L normalComplementaryInverse Q = 0 := by
  ext w : 1
  apply (WithLp.ofLp_injective 2)
  have hmem : Q (WithLp.ofLp w).1 ∈ (weakVortexKernel μ hx)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [real_inner_comm, L2.inner_def]
    exact hQorth _ u hu
  rw [ContinuousLinearMap.comp_apply, ofLp_normalDomainSlowProj, ofLp_normalComplementaryInverse,
    (Submodule.starProjection_apply_eq_zero_iff (K := weakVortexKernel μ hx)).2 hmem]
  rfl

/-- By Hilbert-space duality, whenever `Q` maps into `(weakVortexKernel μ hx)ᗮ`, its adjoint `Q†`
annihilates `weakVortexKernel μ hx`, so `𝒬 ∘L Π₋ = 0`. -/
theorem normalComplementaryInverse_comp_normalTargetSlowProj (hx : Continuous x)
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQorth : ∀ f u, u ∈ weakVortexKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0) :
    normalComplementaryInverse Q ∘L normalTargetSlowProj μ hx = 0 := by
  ext w : 1
  apply (WithLp.ofLp_injective 2)
  have hadj0 : ContinuousLinearMap.adjoint Q
      ((weakVortexKernel μ hx).starProjection (WithLp.ofLp w).2) = 0 := by
    refine ext_inner_right ℝ fun h ↦ ?_
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm, L2.inner_def]
    exact hQorth h _ (Submodule.starProjection_apply_mem _ _)
  rw [ContinuousLinearMap.comp_apply, ofLp_normalComplementaryInverse, ofLp_normalTargetSlowProj,
    map_zero, hadj0]
  rfl

/-- On compactly supported `C¹` fields `ψ`, a weak right inverse `Q` orthogonal to
`weakVortexKernel μ hx` acts as the fast projection `1 - P_{K_x}` after `L_x`:
`Q (toLp (L_x ψ)) = (1 - P_{K_x}) (toLp ψ)`. -/
theorem apply_toLp_gaugeFixedOperator_eq_sub_starProjection (hx : Continuous x)
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQsol : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q f z, Vortex.gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (hQorth : ∀ f u, u ∈ weakVortexKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0)
    {ψ : ℂ → EuclideanSpace ℝ (Fin 4)} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    let hψ_lp : MemLp ψ 2 μ := hψ.continuous.memLp_of_hasCompactSupport hψc
    let hLψ_lp : MemLp (Vortex.gaugeFixedOperator x ψ) 2 μ :=
      (Vortex.continuous_gaugeFixedOperator hx hψ).memLp_of_hasCompactSupport
        (Vortex.hasCompactSupport_gaugeFixedOperator hψc)
    Q (hLψ_lp.toLp (Vortex.gaugeFixedOperator x ψ)) =
      hψ_lp.toLp ψ - (weakVortexKernel μ hx).starProjection (hψ_lp.toLp ψ) := by
  intro hψ_lp hLψ_lp
  set S := vortexAdjointToLp μ hx
  have hQ_mem : Q (hLψ_lp.toLp (Vortex.gaugeFixedOperator x ψ)) ∈ (LinearMap.range S)ᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [real_inner_comm, L2.inner_def]
    exact hQorth _ u hu
  have hP_mem : hψ_lp.toLp ψ - (weakVortexKernel μ hx).starProjection (hψ_lp.toLp ψ) ∈
      (LinearMap.range S)ᗮᗮ :=
    Submodule.sub_starProjection_mem_orthogonal _
  refine LinearMap.eq_of_inner_apply_eq_of_mem_orthogonal S hQ_mem hP_mem fun η ↦ ?_
  rw [inner_vortexAdjointToLp hx, hQsol _ η η.contDiff η.hasCompactSupport, inner_sub_left]
  have hPK_zero : ⟪(weakVortexKernel μ hx).starProjection (hψ_lp.toLp ψ), S η⟫ = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal _ _).1 (Submodule.starProjection_apply_mem _ _) (S η) ⟨η, rfl⟩
  rw [hPK_zero, sub_zero, inner_vortexAdjointToLp hx]
  calc ∫ z, ⟪(hLψ_lp.toLp (Vortex.gaugeFixedOperator x ψ)) z, η z⟫ ∂μ
      = ∫ z, ⟪Vortex.gaugeFixedOperator x ψ z, η z⟫ ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hLψ_lp.coeFn_toLp] with z hz
        rw [hz]
    _ = ∫ z, ⟪ψ z, Vortex.gaugeFixedAdjoint x η z⟫ ∂μ :=
        Vortex.integral_inner_gaugeFixedOperator hx hψ hψc (η.contDiff.of_le (by norm_cast))
    _ = ∫ z, ⟪(hψ_lp.toLp ψ) z, Vortex.gaugeFixedAdjoint x η z⟫ ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hψ_lp.coeFn_toLp] with z hz
        rw [hz]

/-- **Exact `L²` left-inverse identity on the fast domain channel `1 - Π₊`**: for compactly
supported `C²` perturbations `(y, η)`, `𝒬 (L_x y, L_x* η) = (1 - Π₊) (y, η)` in `L²`. -/
theorem normalComplementaryInverse_toLp_normalModelOperator (hx : Continuous x)
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQsol : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q f z, Vortex.gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (hQorth : ∀ f u, u ∈ weakVortexKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0)
    {y η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : ContDiff ℝ 2 y) (hyc : HasCompactSupport y)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    let hy_lp : MemLp y 2 μ := hy.continuous.memLp_of_hasCompactSupport hyc
    let hη_lp : MemLp η 2 μ := hη.continuous.memLp_of_hasCompactSupport hηc
    let hLy_lp : MemLp (Vortex.gaugeFixedOperator x y) 2 μ :=
      (Vortex.continuous_gaugeFixedOperator hx (hy.of_le (by norm_num))).memLp_of_hasCompactSupport
        (Vortex.hasCompactSupport_gaugeFixedOperator hyc)
    let hAη_lp : MemLp (Vortex.gaugeFixedAdjoint x η) 2 μ :=
      (Vortex.continuous_gaugeFixedAdjoint hx (hη.of_le (by norm_num))).memLp_of_hasCompactSupport
        (Vortex.hasCompactSupport_gaugeFixedAdjoint hηc)
    normalComplementaryInverse Q
        (WithLp.toLp 2 (hLy_lp.toLp (Vortex.gaugeFixedOperator x y),
          hAη_lp.toLp (Vortex.gaugeFixedAdjoint x η))) =
      (1 - normalDomainSlowProj μ hx) (WithLp.toLp 2 (hy_lp.toLp y, hη_lp.toLp η)) := by
  intro hy_lp hη_lp hLy_lp hAη_lp
  apply (WithLp.ofLp_injective 2)
  rw [ofLp_normalComplementaryInverse, sub_apply, one_apply_eq_self, WithLp.ofLp_sub,
    ofLp_normalDomainSlowProj]
  refine Prod.ext ?_ ?_
  · exact apply_toLp_gaugeFixedOperator_eq_sub_starProjection hx hQsol hQorth
      (hy.of_le (by norm_num)) hyc
  · dsimp only [Prod.snd_sub]
    rw [sub_zero]
    refine ext_inner_right ℝ fun h ↦ ?_
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm, L2.inner_toLp (Q h) hAη_lp,
      hQsol h η hη hηc, ← L2.inner_toLp h hη_lp, real_inner_comm]

/-- **Weak right-inverse identity on the fast target channel `1 - Π₋`**: for every
`w ∈ WithLp 2 (L² × L²)` and every pair of compactly supported `C²` test fields `(ϕ, ψ)`,
`𝓜_x (𝒬 w) = (1 - Π₋) w` weakly against `(ϕ, ψ)`. -/
theorem integral_inner_normalComplementaryInverse_normalModelAdjoint (hx : Continuous x)
    {Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQsol : ∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪Q f z, Vortex.gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (hQorth : ∀ f u, u ∈ weakVortexKernel μ hx → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0)
    (w : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ))
    {ϕ ψ : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hϕ : ContDiff ℝ 2 ϕ) (hϕc : HasCompactSupport ϕ)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    let q := WithLp.ofLp (normalComplementaryInverse Q w)
    let r := WithLp.ofLp ((1 - normalTargetSlowProj μ hx) w)
    (∫ z, ⟪q.1 z, Vortex.gaugeFixedAdjoint x ϕ z⟫ ∂μ) +
        (∫ z, ⟪q.2 z, Vortex.gaugeFixedOperator x ψ z⟫ ∂μ) =
      (∫ z, ⟪r.1 z, ϕ z⟫ ∂μ) + (∫ z, ⟪r.2 z, ψ z⟫ ∂μ) := by
  intro q r
  have hq : q = (Q (WithLp.ofLp w).1, ContinuousLinearMap.adjoint Q (WithLp.ofLp w).2) :=
    ofLp_normalComplementaryInverse Q w
  have hr : r = ((WithLp.ofLp w).1,
      (WithLp.ofLp w).2 - (weakVortexKernel μ hx).starProjection (WithLp.ofLp w).2) := by
    dsimp only [r]
    rw [sub_apply, one_apply_eq_self, WithLp.ofLp_sub, ofLp_normalTargetSlowProj]
    exact Prod.ext (sub_zero _) rfl
  have h1 : ∫ z, ⟪q.1 z, Vortex.gaugeFixedAdjoint x ϕ z⟫ ∂μ = ∫ z, ⟪r.1 z, ϕ z⟫ ∂μ := by
    rw [congrArg Prod.fst hq, congrArg Prod.fst hr]
    exact hQsol (WithLp.ofLp w).1 ϕ hϕ hϕc
  have h2 : ∫ z, ⟪q.2 z, Vortex.gaugeFixedOperator x ψ z⟫ ∂μ = ∫ z, ⟪r.2 z, ψ z⟫ ∂μ := by
    have hψ_lp : MemLp ψ 2 μ := hψ.continuous.memLp_of_hasCompactSupport hψc
    have hLψ_lp : MemLp (Vortex.gaugeFixedOperator x ψ) 2 μ :=
      (Vortex.continuous_gaugeFixedOperator hx (hψ.of_le (by norm_num))).memLp_of_hasCompactSupport
        (Vortex.hasCompactSupport_gaugeFixedOperator hψc)
    calc ∫ z, ⟪q.2 z, Vortex.gaugeFixedOperator x ψ z⟫ ∂μ
        = ⟪ContinuousLinearMap.adjoint Q (WithLp.ofLp w).2,
            hLψ_lp.toLp (Vortex.gaugeFixedOperator x ψ)⟫ := by
          rw [congrArg Prod.snd hq]
          exact (L2.inner_toLp _ hLψ_lp).symm
      _ = ⟪(WithLp.ofLp w).2, Q (hLψ_lp.toLp (Vortex.gaugeFixedOperator x ψ))⟫ :=
          ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = ⟪(WithLp.ofLp w).2,
            hψ_lp.toLp ψ - (weakVortexKernel μ hx).starProjection (hψ_lp.toLp ψ)⟫ := by
          rw [apply_toLp_gaugeFixedOperator_eq_sub_starProjection hx hQsol hQorth
            (hψ.of_le (by norm_num)) hψc]
      _ = ⟪r.2, hψ_lp.toLp ψ⟫ := by
          rw [congrArg Prod.snd hr, inner_sub_left, inner_sub_right,
            (weakVortexKernel μ hx).inner_starProjection_left_eq_right]
      _ = ∫ z, ⟪r.2 z, ψ z⟫ ∂μ := L2.inner_toLp r.2 hψ_lp
  rw [h1, h2]

/-- **Existence of the complementary normal weak `L²` inverse at a plane vortex.** For any `C¹`
solution `x` of `Vortex.equation` with `|α| → 1` at infinity, there exists a bounded operator `𝒬`
on `WithLp 2 (L²(ℂ; ℝ⁴) × L²(ℂ; ℝ⁴))` satisfying `Π₊ ∘L 𝒬 = 0`, `𝒬 ∘L Π₋ = 0`, the exact `L²`
left-inverse identity `𝒬 (L_x y, L_x* η) = (1 - Π₊) (y, η)` on compactly supported `C²`
perturbations, and the weak right-inverse identity `𝓜_x (𝒬 w) = (1 - Π₋) w`. -/
theorem exists_normalComplementaryInverse (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, Vortex.equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ 𝒬 : WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) →L[ℝ]
        WithLp 2 (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ × Lp (EuclideanSpace ℝ (Fin 4)) 2 μ),
      normalDomainSlowProj μ hx.continuous ∘L 𝒬 = 0 ∧
      𝒬 ∘L normalTargetSlowProj μ hx.continuous = 0 ∧
      (∀ (y η : ℂ → EuclideanSpace ℝ (Fin 4))
          (hy : ContDiff ℝ 2 y) (hyc : HasCompactSupport y)
          (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η),
        let hy_lp : MemLp y 2 μ := hy.continuous.memLp_of_hasCompactSupport hyc
        let hη_lp : MemLp η 2 μ := hη.continuous.memLp_of_hasCompactSupport hηc
        let hLy_lp : MemLp (Vortex.gaugeFixedOperator x y) 2 μ :=
          (Vortex.continuous_gaugeFixedOperator hx.continuous
            (hy.of_le (by norm_num))).memLp_of_hasCompactSupport
            (Vortex.hasCompactSupport_gaugeFixedOperator hyc)
        let hAη_lp : MemLp (Vortex.gaugeFixedAdjoint x η) 2 μ :=
          (Vortex.continuous_gaugeFixedAdjoint hx.continuous
            (hη.of_le (by norm_num))).memLp_of_hasCompactSupport
            (Vortex.hasCompactSupport_gaugeFixedAdjoint hηc)
        𝒬 (WithLp.toLp 2 (hLy_lp.toLp (Vortex.gaugeFixedOperator x y),
            hAη_lp.toLp (Vortex.gaugeFixedAdjoint x η))) =
          (1 - normalDomainSlowProj μ hx.continuous)
            (WithLp.toLp 2 (hy_lp.toLp y, hη_lp.toLp η))) ∧
      ∀ w (ϕ ψ : ℂ → EuclideanSpace ℝ (Fin 4)),
        ContDiff ℝ 2 ϕ → HasCompactSupport ϕ →
        ContDiff ℝ 2 ψ → HasCompactSupport ψ →
        let q := WithLp.ofLp (𝒬 w)
        let r := WithLp.ofLp ((1 - normalTargetSlowProj μ hx.continuous) w)
        (∫ z, ⟪q.1 z, Vortex.gaugeFixedAdjoint x ϕ z⟫ ∂μ) +
            (∫ z, ⟪q.2 z, Vortex.gaugeFixedOperator x ψ z⟫ ∂μ) =
          (∫ z, ⟪r.1 z, ϕ z⟫ ∂μ) + (∫ z, ⟪r.2 z, ψ z⟫ ∂μ) := by
  obtain ⟨Q, hQsol, hQorth⟩ :=
    Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (μ := μ) hx hsol hlim
  have hQorth' : ∀ f u, u ∈ weakVortexKernel μ hx.continuous → ∫ z, ⟪Q f z, u z⟫ ∂μ = 0 :=
    fun f u hu ↦ hQorth f u ((mem_weakVortexKernel_iff hx.continuous u).1 hu)
  exact ⟨normalComplementaryInverse Q,
    normalDomainSlowProj_comp_normalComplementaryInverse hx.continuous hQorth',
    normalComplementaryInverse_comp_normalTargetSlowProj hx.continuous hQorth',
    fun y η hy hyc hη hηc ↦
      normalComplementaryInverse_toLp_normalModelOperator hx.continuous hQsol hQorth'
        hy hyc hη hηc,
    fun w ϕ ψ hϕ hϕc hψ hψc ↦
      integral_inner_normalComplementaryInverse_normalModelAdjoint hx.continuous hQsol hQorth' w
        hϕ hϕc hψ hψc⟩

end SlowProjectionsAndInverse

end TauCeti.SeibergWitten
