/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.VectorBundle.FiniteDimensional
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.Chart
import TauCeti.Geometry.Manifold.VectorBundle.Section.Support

/-!
# Global sections of a point twist

Let `X` be a complex curve, `E → X` a `C^n` vector bundle over `𝓘(ℂ)` with model fibre `F`, and
`x : X`. This file compares the `C^n` sections of `E` with those of its point twist `E(x)`
(`TauCeti.pointTwistCore`), as Mathlib's spaces of sections `Cₛ^n⟮𝓘(ℂ); F, E⟯`. For `n = ∞`, or
`n = ω`, these are the holomorphic sections, and for a holomorphic line bundle `L` the comparison
is the kernel half of the sequence
`0 → ker D_L → ker D_{L(x)} → L(x)_x → coker D_L → coker D_{L(x)} → 0`,
with `D` the Cauchy–Riemann operator, of the point-twisting step in the proof of the Riemann–Roch
theorem (McDuff–Salamon, Theorem C.1.10).

Multiplication by the canonical section of `𝒪(x)` is a linear map `TauCeti.pointTwistMulₗ` from
the sections of `E` to those of `E(x)`. It is injective, since `X` has no isolated points. The
evaluation `TauCeti.pointTwistEvalₗ` sends a section `τ` of `E(x)` to its leading coefficient at
`x`, a vector of `E x`. For `n ≠ 0` and a complete model fibre, the range of the first map is the
kernel of the second (`TauCeti.range_pointTwistMulₗ`): a section of `E(x)` whose leading
coefficient vanishes at `x` is, in the chart of `E` at `x`, its reading divided by the centred
chart coordinate, and a `C^n` function vanishing at `x` is the centred chart coordinate times a
`C^n` function (`TauCeti.exists_contMDiffAt_eventually_eq_pointTwistCoord_smul`, by the divided
slope `dslope`). Hence the space of sections grows by at most the rank of `E`
(`TauCeti.finrank_contMDiffSection_pointTwistCore_le`).

## Main definitions

* `TauCeti.pointTwistMulₗ`: multiplication by the canonical section of `𝒪(x)` on sections.
* `TauCeti.pointTwistEvalₗ`: the leading coefficient at `x` of a section of the point twist.

## Main results

* `TauCeti.pointTwistMulₗ_injective` and `TauCeti.range_pointTwistMulₗ`: the sequence
  `0 → H⁰(E) → H⁰(E(x)) → E x` is exact.
* `TauCeti.finiteDimensional_contMDiffSection_pointTwistCore` and
  `TauCeti.finrank_contMDiffSection_pointTwistCore_le`: `dim H⁰(E(x)) ≤ dim H⁰(E) + rank E`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10.
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, §16.
-/

public section

noncomputable section

open Bundle Set Topology Filter
open scoped Manifold ContDiff

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {n : ℕ∞ω}

/-! ### Division by the centred chart coordinate -/

/-- For `n ≠ 0`, a function to a complete space that is `C^n` at `x` and vanishes at `x` is, near
`x`, the centred chart coordinate at `x` times a function that is `C^n` at `x`. -/
theorem exists_contMDiffAt_eventually_eq_pointTwistCoord_smul [IsManifold 𝓘(ℂ) n X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (hn : n ≠ 0)
    {h : X → F} {x : X} (hh : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, F) n h x) (hx : h x = 0) :
    ∃ k : X → F, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, F) n k x ∧
      ∀ᶠ z in 𝓝 x, h z = pointTwistCoord x z • k z := by
  have : IsManifold 𝓘(ℂ) 1 X := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have hx' := mem_chart_source ℂ x
  -- `k` is the divided slope at `x` of the reading of `h` in the chart at `x`
  have hg : AnalyticAt ℂ (h ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
    analyticAt_comp_chartAt_symm ((contMDiffAt_iff_eventually_mdifferentiableAt hn).1 hh)
  refine ⟨dslope (h ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ∘ chartAt ℂ x,
    (hg.dslope _).contDiffAt.contMDiffAt.comp x
      ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := n)).contMDiffAt
        ((chartAt ℂ x).open_source.mem_nhds hx')), ?_⟩
  filter_upwards [(chartAt ℂ x).open_source.mem_nhds hx'] with z hz
  rw [pointTwistCoord_apply, Function.comp_apply, sub_smul_dslope, Function.comp_apply,
    Function.comp_apply, (chartAt ℂ x).left_inv hz, (chartAt ℂ x).left_inv hx', hx, sub_zero]

section General

variable [IsManifold 𝓘(ℂ) n X]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
  (E : X → Type*) [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)]
  [∀ z, TopologicalSpace (E z)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E] [ContMDiffVectorBundle n F E 𝓘(ℂ)]

/-! ### Multiplication by the canonical section and evaluation -/

/-- Multiplication by the canonical section of `𝒪(x)`, from the `C^n` sections of `E` to the `C^n`
sections of the point twist `E(x)`. -/
def pointTwistMulₗ (x : X) :
    Cₛ^n⟮𝓘(ℂ); F, E⟯ →ₗ[ℂ] Cₛ^n⟮𝓘(ℂ); F, (pointTwistCore F E x).Fiber⟯ where
  toFun s := ⟨fun z ↦ pointTwistMul F E x z (s z), contMDiff_pointTwistMul_section s.contMDiff⟩
  map_add' s t := ContMDiffSection.ext fun z ↦ map_add (pointTwistMul F E x z) (s z) (t z)
  map_smul' c s := ContMDiffSection.ext fun z ↦ map_smul (pointTwistMul F E x z) c (s z)

/-- The leading coefficient at `x` of a `C^n` section of the point twist `E(x)`, a vector of the
fibre `E x`; it is the value of the section at `x` in the chart of `E` at `x`. -/
def pointTwistEvalₗ (x : X) :
    Cₛ^n⟮𝓘(ℂ); F, (pointTwistCore F E x).Fiber⟯ →ₗ[ℂ] E x where
  toFun τ := pointTwistPoleMul F E x x (τ x)
  map_add' τ τ' := map_add (pointTwistPoleMul F E x x) (τ x) (τ' x)
  map_smul' c τ := map_smul (pointTwistPoleMul F E x x) c (τ x)

variable {F E}

@[simp] theorem pointTwistMulₗ_apply (x : X) (s : Cₛ^n⟮𝓘(ℂ); F, E⟯) (z : X) :
    pointTwistMulₗ F E x s z = pointTwistMul F E x z (s z) :=
  (rfl)

omit [IsManifold 𝓘(ℂ) n X] [ContMDiffVectorBundle n F E 𝓘(ℂ)] in
@[simp] theorem pointTwistEvalₗ_apply (x : X) (τ : Cₛ^n⟮𝓘(ℂ); F, (pointTwistCore F E x).Fiber⟯) :
    pointTwistEvalₗ F E x τ = pointTwistPoleMul F E x x (τ x) :=
  (rfl)

/-- Multiplication by the canonical section of `𝒪(x)` is injective on `C^n` sections. -/
theorem pointTwistMulₗ_injective (x : X) :
    Function.Injective (pointTwistMulₗ (n := n) F E x) := by
  have : PerfectSpace X := ChartedSpace.perfectSpace (H := ℂ)
  refine fun s t hst ↦ ContMDiffSection.eq_of_forall_ne (x := x) fun z hz ↦ ?_
  have h := congr($hst z)
  rw [pointTwistMulₗ_apply, pointTwistMulₗ_apply] at h
  rw [← pointTwistDiv_pointTwistMul (F := F) hz (s z), h, pointTwistDiv_pointTwistMul hz]

/-- The leading coefficient of the product of a section with the canonical section of `𝒪(x)`
vanishes at `x`. -/
theorem pointTwistEvalₗ_comp_pointTwistMulₗ (x : X) :
    pointTwistEvalₗ F E x ∘ₗ pointTwistMulₗ (n := n) F E x = 0 := by
  ext s
  simp

/-- **Division by the canonical section.** For `n ≠ 0` and a complete model fibre, a `C^n` section
`τ` of the point twist whose leading coefficient vanishes at `x` is the product of a `C^n` section
of `E` with the canonical section of `𝒪(x)`. -/
theorem exists_pointTwistMul_eq [CompleteSpace F] (hn : n ≠ 0) {x : X}
    {τ : ∀ z, (pointTwistCore F E x).Fiber z}
    (hτ : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n (fun z ↦ TotalSpace.mk' F z (τ z)))
    (hτx : pointTwistPoleMul F E x x (τ x) = 0) :
    ∃ σ : ∀ z, E z, ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n (fun z ↦ TotalSpace.mk' F z (σ z)) ∧
      ∀ z, pointTwistMul F E x z (σ z) = τ z := by
  classical
  have hx : x ∈ (trivializationAt F E x).baseSet := mem_baseSet_trivializationAt F E x
  -- the reading of the leading coefficient in the chart of `E` at `x` vanishes at `x`, so it is
  -- the centred chart coordinate times a function `k` that is `C^n` at `x`
  have hhx : (trivializationAt F E x ⟨x, pointTwistPoleMul F E x x (τ x)⟩).2 = 0 := by
    rw [hτx, ← (trivializationAt F E x).continuousLinearMapAt_apply_of_mem ℂ hx, map_zero]
  obtain ⟨k, hk, hhk⟩ := exists_contMDiffAt_eventually_eq_pointTwistCoord_smul hn
    ((contMDiffAt_section x).1 (contMDiffAt_pointTwist_section_iff_self.1 (hτ x))) hhx
  have hτ0 : τ x = 0 := (trivializationAt_pointTwistPoleMul_self (F := F) x (τ x)).symm.trans hhx
  -- the section of `E`: off `x` the reading of `τ`, at `x` the value of `k` in the chart of `E`
  let σ : ∀ z, E z := Function.update (fun z ↦ pointTwistDiv F E x z (τ z)) x
    ((trivializationAt F E x).symm x (k x))
  have hσx : σ x = (trivializationAt F E x).symm x (k x) := Function.update_self ..
  have hσne : ∀ z, z ≠ x → σ z = pointTwistDiv F E x z (τ z) := fun z hz ↦
    Function.update_of_ne hz ..
  refine ⟨σ, fun z₀ ↦ ?_, fun z ↦ ?_⟩
  · by_cases hz₀ : z₀ = x
    · subst hz₀
      rw [contMDiffAt_section]
      refine hk.congr_of_eventuallyEq ?_
      filter_upwards [hhk, (trivializationAt F E z₀).open_baseSet.mem_nhds hx,
        (chartAt ℂ z₀).open_source.mem_nhds (mem_chart_source ℂ z₀)] with z hz hzb hzc
      by_cases hzx : z = z₀
      · subst hzx
        rw [hσx, (trivializationAt F E z).apply_mk_symm hx]
      · have hc : pointTwistCoord z₀ z ≠ 0 := pointTwistCoord_ne_zero hzc hzx
        -- stated for `w : F`, since the fibres of `E(x)` are not syntactically `F`
        have key (w : F) : (trivializationAt F E z₀ ⟨z, pointTwistPoleMul F E z₀ z w⟩).2 =
            pointTwistCoord z₀ z • (trivializationAt F E z₀ ⟨z, pointTwistDiv F E z₀ z w⟩).2 := by
          rw [pointTwistPoleMul_eq_smul_pointTwistDiv hzx,
            ← (trivializationAt F E z₀).continuousLinearMapAt_apply_of_mem ℂ hzb, map_smul,
            (trivializationAt F E z₀).continuousLinearMapAt_apply_of_mem ℂ hzb]
        refine smul_right_injective F hc ?_
        dsimp only
        rw [← hz, hσne z hzx]
        exact (key (τ z)).symm
    · have : T1Space X := ChartedSpace.t1Space ℂ X
      have h₁ := (contMDiffAt_pointTwist_section_iff_of_ne hz₀).1 (hτ z₀)
      refine h₁.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_compl_singleton.mem_nhds hz₀] with z hz
      rw [hσne z hz]
  · by_cases hzx : z = x
    · subst hzx
      rw [pointTwistMul_self, hτ0]
      rfl
    · rw [hσne z hzx]
      exact pointTwistMul_pointTwistDiv (F := F) hzx (τ z)

/-- **Exactness at the sections of the point twist.** For `n ≠ 0` and a complete model fibre,
a `C^n` section of `E(x)` is the product of a section of `E` with the canonical section of `𝒪(x)`
exactly when its leading coefficient vanishes at `x`. -/
theorem range_pointTwistMulₗ [CompleteSpace F] (hn : n ≠ 0) (x : X) :
    LinearMap.range (pointTwistMulₗ (n := n) F E x) = LinearMap.ker (pointTwistEvalₗ F E x) := by
  refine le_antisymm ?_ fun τ hτ ↦ ?_
  · rintro _ ⟨s, rfl⟩
    simp
  · obtain ⟨σ, hσ, hστ⟩ := exists_pointTwistMul_eq hn τ.contMDiff hτ
    exact ⟨⟨σ, hσ⟩, ContMDiffSection.ext hστ⟩

/-- If `E` has finite rank and finitely many independent `C^n` sections, so has its point twist. -/
theorem finiteDimensional_contMDiffSection_pointTwistCore [FiniteDimensional ℂ F] (hn : n ≠ 0)
    (x : X) [FiniteDimensional ℂ Cₛ^n⟮𝓘(ℂ); F, E⟯] :
    FiniteDimensional ℂ Cₛ^n⟮𝓘(ℂ); F, (pointTwistCore F E x).Fiber⟯ := by
  have := FiniteDimensional.complete ℂ F
  have := VectorBundle.finiteDimensional ℂ F E x
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (pointTwistEvalₗ F E x)
    (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, ← range_pointTwistMulₗ hn, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

/-- **Twisting at a point adds at most the rank.** `dim H⁰(E(x)) ≤ dim H⁰(E) + rank E`. -/
theorem finrank_contMDiffSection_pointTwistCore_le [FiniteDimensional ℂ F] (hn : n ≠ 0)
    (x : X) [FiniteDimensional ℂ Cₛ^n⟮𝓘(ℂ); F, E⟯] :
    Module.finrank ℂ Cₛ^n⟮𝓘(ℂ); F, (pointTwistCore F E x).Fiber⟯ ≤
      Module.finrank ℂ Cₛ^n⟮𝓘(ℂ); F, E⟯ + Module.finrank ℂ F := by
  have := FiniteDimensional.complete ℂ F
  have := finiteDimensional_contMDiffSection_pointTwistCore (F := F) (E := E) hn x
  have := VectorBundle.finiteDimensional ℂ F E x
  rw [← LinearMap.finrank_range_add_finrank_ker (pointTwistEvalₗ F E x), ← range_pointTwistMulₗ hn,
    LinearMap.finrank_range_of_inj (pointTwistMulₗ_injective x), add_comm]
  gcongr
  exact (Submodule.finrank_le _).trans (VectorBundle.finrank_eq ℂ F E x).le

end General

end TauCeti
