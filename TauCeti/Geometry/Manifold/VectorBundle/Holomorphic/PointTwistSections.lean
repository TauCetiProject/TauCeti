/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sheaf
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Normalize
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# Global sections of a point twist

Let `X` be a complex curve, `E → X` a `C^n` vector bundle over `𝓘(ℂ)` with model fibre `F`, and
`x : X`. This file compares the `C^n` sections of `E` with those of its point twist `E(x)`
(`TauCeti.pointTwistCore`), as Mathlib's spaces of sections `Cₛ^n⟮𝓘(ℂ); F, E⟯`. For `n = ∞`, or
`n = ω`, these are the holomorphic sections, and for a holomorphic line bundle `L` the comparison
is the kernel half of the sequence
`0 → ker ∂̄_L → ker ∂̄_{L(x)} → L(x)_x → coker ∂̄_L → coker ∂̄_{L(x)} → 0`
of the point-twisting step in the proof of the Riemann–Roch theorem (McDuff–Salamon,
Theorem C.1.10).

Multiplication by the canonical section of `𝒪(x)` is a linear map `TauCeti.pointTwistMulₗ` from
the sections of `E` to those of `E(x)`. It is injective, since `X` has no isolated points. The
evaluation `TauCeti.pointTwistEvalₗ` sends a section `τ` of `E(x)` to its leading coefficient at
`x`, a vector of `E x`. For `n ≠ 0` and a complete model fibre, the range of the first map is the
kernel of the second (`TauCeti.range_pointTwistMulₗ`): a section of `E(x)` whose leading
coefficient vanishes at `x` is, in the chart of `E` at `x`, its reading divided by the centred
chart coordinate, and the divided slope `dslope` of a holomorphic function is holomorphic. Hence
the space of sections grows by at most the rank of `E` (`TauCeti.finrank_pointTwist_le`).

For the trivial line bundle the sections of the twist `𝒪(x)` are the sections of the divisor
sheaf `𝒪_x` of the point divisor, normalized to zero at `x`
(`TauCeti.pointTwistSectionsEquivDivisorSections`). On the Riemann sphere, the affine coordinate
`z` is a global section of the twist of the trivial bundle at `∞`, vanishing exactly at `0`
(`TauCeti.contMDiff_pointTwistOfPole_affineChart` and
`TauCeti.pointTwistOfPole_affineChart_eq_zero_iff`), while it is not a holomorphic section of the
trivial bundle itself (`OnePoint.not_mdifferentiable_section_twistCore_zero_of_coe`). This is the
zero count for `𝒪(1)`: one simple zero.

## Main definitions

* `TauCeti.pointTwistMulₗ`: multiplication by the canonical section of `𝒪(x)` on sections.
* `TauCeti.pointTwistEvalₗ`: the leading coefficient at `x` of a section of the point twist.
* `TauCeti.pointTwistSectionsEquivDivisorSections`: the sections of `𝒪(x)` as the sections of the
  divisor sheaf of the point divisor.

## Main results

* `TauCeti.pointTwistMulₗ_injective` and `TauCeti.range_pointTwistMulₗ`: the sequence
  `0 → H⁰(E) → H⁰(E(x)) → E x` is exact.
* `TauCeti.finiteDimensional_pointTwist` and `TauCeti.finrank_pointTwist_le`:
  `dim H⁰(E(x)) ≤ dim H⁰(E) + rank E`.

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

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {n : ℕ∞ω}

/-! ### Sections agreeing off a point -/

section Eq

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : X → Type*} [∀ z, AddCommGroup (V z)] [∀ z, TopologicalSpace (V z)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]

/-- Two `C^n` sections of a vector bundle over a complex curve that agree off a point are equal:
the point is not isolated, and the sections are continuous. -/
theorem ContMDiffSection.eq_of_forall_ne {s t : Cₛ^n⟮𝓘(ℂ); F, V⟯} {x : X}
    (h : ∀ z, z ≠ x → s z = t z) : s = t := by
  have : PerfectSpace X := ChartedSpace.perfectSpace (H := ℂ)
  refine ContMDiffSection.ext fun z ↦ ?_
  by_cases hzx : z = x
  · subst hzx
    have hz := mem_baseSet_trivializationAt F V z
    have hcont (u : Cₛ^n⟮𝓘(ℂ); F, V⟯) :
        ContinuousAt (fun y ↦ (trivializationAt F V z ⟨y, u y⟩).2) z :=
      ((contMDiffAt_section z).1 (u.contMDiff z)).continuousAt
    have heq : (fun y ↦ (trivializationAt F V z ⟨y, s y⟩).2) =ᶠ[𝓝[≠] z]
        fun y ↦ (trivializationAt F V z ⟨y, t y⟩).2 :=
      eventually_nhdsWithin_of_forall fun y hy ↦ by dsimp only; rw [h y hy]
    have key := tendsto_nhds_unique
      (((hcont s).tendsto.mono_left nhdsWithin_le_nhds).congr' heq)
      ((hcont t).tendsto.mono_left nhdsWithin_le_nhds)
    rw [← (trivializationAt F V z).symm_apply_apply_mk hz (s z), key,
      (trivializationAt F V z).symm_apply_apply_mk hz]
  · exact h z hzx

end Eq

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
  refine fun s t hst ↦ ContMDiffSection.eq_of_forall_ne (x := x) fun z hz ↦ ?_
  have h := congr($hst z)
  rw [pointTwistMulₗ_apply, pointTwistMulₗ_apply] at h
  rw [← pointTwistDiv_pointTwistMul (F := F) hz (s z), h, pointTwistDiv_pointTwistMul hz]

/-- In the chart of `E` at `x`, the leading coefficient at `x` reads the vector itself. -/
theorem trivializationAt_pointTwistPoleMul_self (x : X) (w : F) :
    (trivializationAt F E x ⟨x, pointTwistPoleMul F E x x w⟩).2 = w := by
  classical
  rw [pointTwistPoleMul_apply, decide_eq_true rfl, pointTwistFactor_self, one_smul]
  exact congrArg Prod.snd
    ((trivializationAt F E x).apply_mk_symm (mem_baseSet_trivializationAt F E x) w)

/-- The leading coefficient at `x` is injective on the fibre of the point twist at `x`. -/
theorem pointTwistPoleMul_self_injective (x : X) :
    Function.Injective (pointTwistPoleMul F E x x) := fun w w' h ↦ by
  rw [← trivializationAt_pointTwistPoleMul_self (E := E) x w, h,
    trivializationAt_pointTwistPoleMul_self]

/-- The leading coefficient of the product of a section with the canonical section of `𝒪(x)`
vanishes at `x`. -/
theorem pointTwistEvalₗ_comp_pointTwistMulₗ (x : X) :
    pointTwistEvalₗ F E x ∘ₗ pointTwistMulₗ (n := n) F E x = 0 := by
  ext s
  simp

/-- **Division by the canonical section.** A `C^n` section `τ` of the point twist whose leading
coefficient vanishes at `x` is the product of a `C^n` section of `E` with the canonical section of
`𝒪(x)`. In the chart of `E` at `x` the section of `E` is the divided slope `dslope` of the reading
of `τ`, which is holomorphic by the removable singularity theorem. -/
theorem exists_pointTwistMul_eq [CompleteSpace F] (hn : n ≠ 0) {x : X}
    {τ : ∀ z, (pointTwistCore F E x).Fiber z}
    (hτ : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n (fun z ↦ TotalSpace.mk' F z (τ z)))
    (hτx : pointTwistPoleMul F E x x (τ x) = 0) :
    ∃ σ : ∀ z, E z, ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, F)) n (fun z ↦ TotalSpace.mk' F z (σ z)) ∧
      ∀ z, pointTwistMul F E x z (σ z) = τ z := by
  classical
  have hx : x ∈ (trivializationAt F E x).baseSet := mem_baseSet_trivializationAt F E x
  -- the value of `τ` at `x` is `0`
  have hτ0 : τ x = 0 :=
    pointTwistPoleMul_self_injective (F := F) (E := E) x
      (by rw [hτx]; exact (map_zero (pointTwistPoleMul F E x x)).symm)
  -- the reading of `τ` in the chart of the point twist at `x`
  obtain ⟨B, hBdef⟩ : ∃ B, (pointTwistCore F E x).baseSet (x, true) = B := ⟨_, rfl⟩
  have hB : B = (trivializationAt F E x).baseSet ∩ (chartAt ℂ x).source := by
    rw [← hBdef, pointTwistCore_baseSet, pointTwistBaseSet_true]
  have hmem : ∀ z ∈ B, z ∈ (trivializationAt F E x).baseSet ∧ z ∈ (chartAt ℂ x).source :=
    fun z hz ↦ by rw [hB] at hz; exact hz
  have hBo : IsOpen B := hBdef ▸ (pointTwistCore F E x).isOpen_baseSet _
  have hxB : x ∈ B := hB ▸ ⟨hx, mem_chart_source ℂ x⟩
  let h : X → F := fun z ↦ ((pointTwistCore F E x).localTriv (x, true) ⟨z, τ z⟩).2
  have hh : ∀ z ∈ B, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, F) n h z := by
    intro z hz
    have hz' : z ∈ (trivializationAt F (pointTwistCore F E x).Fiber x).baseSet := by
      rw [pointTwistCore_trivializationAt_self, pointTwistCore_localTriv_baseSet,
        pointTwistBaseSet_true, ← hB]
      exact hz
    have := ((trivializationAt F (pointTwistCore F E x).Fiber x).contMDiffAt_section_iff
      (IB := 𝓘(ℂ)) (n := n) (s := τ) hz').1 (hτ z)
    rwa [pointTwistCore_trivializationAt_self] at this
  -- `h` is the reading of the leading coefficient in the chart of `E` at `x`
  have hhe : ∀ z ∈ B, h z = (trivializationAt F E x ⟨z, pointTwistPoleMul F E x z (τ z)⟩).2 :=
    fun z hz ↦ (trivializationAt_pointTwistPoleMul (hBdef ▸ hz) (τ z)).symm
  have hhx : h x = 0 := by
    rw [hhe x hxB, hτx, ← (trivializationAt F E x).continuousLinearMapAt_apply_of_mem ℂ hx,
      map_zero]
  -- off `x`, `h` is the centred coordinate times the reading of `pointTwistDiv τ`
  have hhne : ∀ z ∈ B, z ≠ x → h z =
      pointTwistCoord x z • (trivializationAt F E x ⟨z, pointTwistDiv F E x z (τ z)⟩).2 := by
    intro z hz hzx
    have key (w : F) : (trivializationAt F E x ⟨z, pointTwistPoleMul F E x z w⟩).2 =
        pointTwistCoord x z • (trivializationAt F E x ⟨z, pointTwistDiv F E x z w⟩).2 := by
      rw [pointTwistPoleMul_eq_smul_pointTwistDiv hzx,
        ← (trivializationAt F E x).continuousLinearMapAt_apply_of_mem ℂ (hmem z hz).1, map_smul,
        (trivializationAt F E x).continuousLinearMapAt_apply_of_mem ℂ (hmem z hz).1]
    rw [hhe z hz]
    exact key (τ z)
  -- the reading in the chart of `X` at `x`
  let φ := chartAt ℂ x
  let g : ℂ → F := h ∘ φ.symm
  let a := φ x
  let U := φ.target ∩ φ.symm ⁻¹' B
  have hUo : IsOpen U := φ.isOpen_inter_preimage_symm hBo
  have haU : a ∈ U := ⟨φ.map_source (mem_chart_source ℂ x), by
    rw [mem_preimage, φ.left_inv (mem_chart_source ℂ x)]; exact hxB⟩
  have hgd : DifferentiableOn ℂ g U := by
    intro w hw
    have h₁ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, F) n g w :=
      (hh _ hw.2).comp w ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := n)).contMDiffAt
        (φ.open_target.mem_nhds hw.1))
    exact ((contMDiffAt_iff_contDiffAt.1 h₁).differentiableAt hn).differentiableWithinAt
  have hd : DifferentiableOn ℂ (dslope g a) U := (Complex.differentiableOn_dslope (hUo.mem_nhds haU)).2 hgd
  have hk : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, F) n (dslope g a ∘ φ) x :=
    ((hd.analyticAt (hUo.mem_nhds haU)).contDiffAt.contMDiffAt).comp x
      ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := n)).contMDiffAt
        (φ.open_source.mem_nhds (mem_chart_source ℂ x)))
  -- the section of `E`
  let σ : ∀ z, E z := Function.update (fun z ↦ pointTwistDiv F E x z (τ z)) x
    ((trivializationAt F E x).symm x (dslope g a a))
  have hσx : σ x = (trivializationAt F E x).symm x (dslope g a a) := Function.update_self ..
  have hσne : ∀ z, z ≠ x → σ z = pointTwistDiv F E x z (τ z) := fun z hz ↦
    Function.update_of_ne hz ..
  refine ⟨σ, fun z₀ ↦ ?_, fun z ↦ ?_⟩
  · by_cases hz₀ : z₀ = x
    · subst hz₀
      rw [contMDiffAt_section]
      refine hk.congr_of_eventuallyEq ?_
      filter_upwards [hBo.mem_nhds hxB] with z hz
      by_cases hzx : z = z₀
      · subst hzx
        rw [hσx, (trivializationAt F E z).apply_mk_symm hx]
        rfl
      · have hcoord : pointTwistCoord z₀ z = φ z - a := by
          have := pointTwistCoord_chartAt_symm (φ.map_source (hmem z hz).2)
          rwa [φ.left_inv (hmem z hz).2] at this
        have hc : pointTwistCoord z₀ z ≠ 0 := pointTwistCoord_ne_zero (hmem z hz).2 hzx
        have hφz : φ z ≠ a := fun h' ↦ hc (by rw [hcoord, h', sub_self])
        rw [hσne z hzx, Function.comp_apply, dslope_of_ne _ hφz, slope_def_module]
        simp only [g, a, Function.comp_apply]
        rw [φ.left_inv (hmem z hz).2, φ.left_inv (mem_chart_source ℂ z₀), hhx, sub_zero,
          hhne z hz hzx, ← hcoord]
        exact (inv_smul_smul₀ hc _).symm
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
theorem finiteDimensional_pointTwist [CompleteSpace F] [FiniteDimensional ℂ F] (hn : n ≠ 0)
    (x : X) [FiniteDimensional ℂ Cₛ^n⟮𝓘(ℂ); F, E⟯] :
    FiniteDimensional ℂ Cₛ^n⟮𝓘(ℂ); F, (pointTwistCore F E x).Fiber⟯ := by
  have : FiniteDimensional ℂ (E x) := LinearEquiv.finiteDimensional
    ((trivializationAt F E x).linearEquivAt ℂ x (mem_baseSet_trivializationAt F E x)).symm
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (pointTwistEvalₗ F E x)
    (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, ← range_pointTwistMulₗ hn, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

/-- **Twisting at a point adds at most the rank.** `dim H⁰(E(x)) ≤ dim H⁰(E) + rank E`. -/
theorem finrank_pointTwist_le [CompleteSpace F] [FiniteDimensional ℂ F] (hn : n ≠ 0)
    (x : X) [FiniteDimensional ℂ Cₛ^n⟮𝓘(ℂ); F, E⟯] :
    Module.finrank ℂ Cₛ^n⟮𝓘(ℂ); F, (pointTwistCore F E x).Fiber⟯ ≤
      Module.finrank ℂ Cₛ^n⟮𝓘(ℂ); F, E⟯ + Module.finrank ℂ F := by
  have := finiteDimensional_pointTwist (F := F) (E := E) hn x
  have e := (trivializationAt F E x).linearEquivAt ℂ x (mem_baseSet_trivializationAt F E x)
  have : FiniteDimensional ℂ (E x) := LinearEquiv.finiteDimensional e.symm
  rw [← LinearMap.finrank_range_add_finrank_ker (pointTwistEvalₗ F E x), ← range_pointTwistMulₗ hn,
    LinearMap.finrank_range_of_inj (pointTwistMulₗ_injective x), add_comm]
  gcongr
  exact (Submodule.finrank_le _).trans e.finrank_eq.le

end General

/-! ### The point twist of the trivial line bundle -/

section Trivial

variable [IsManifold 𝓘(ℂ) ω X]

omit [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
private theorem ofPoint_apply_self (x : X) : (WeilDivisor.ofPoint x) x = 1 :=
  WeilDivisor.coeff_ofPoint_self x

omit [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
private theorem ofPoint_apply_of_ne {x y : X} (h : y ≠ x) : (WeilDivisor.ofPoint x) y = 0 :=
  WeilDivisor.coeff_ofPoint_of_ne h

omit [IsManifold 𝓘(ℂ) ω X] in
private theorem contMDiffAt_trivial_section_iff {m : ℕ∞ω} {f : X → ℂ} {y : X} :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ)) m
        (fun z ↦ TotalSpace.mk' ℂ (E := Bundle.Trivial X ℂ) z (f z)) y ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) m f y :=
  contMDiffAt_section y

omit [IsManifold 𝓘(ℂ) ω X] in
/-- On the chart at `x`, the centred coordinate is the chart minus its value at `x`. -/
theorem pointTwistCoord_eq_of_mem {x z : X} (hz : z ∈ (chartAt ℂ x).source) :
    pointTwistCoord x z = chartAt ℂ x z - chartAt ℂ x x := by
  have := pointTwistCoord_chartAt_symm ((chartAt ℂ x).map_source hz)
  rwa [(chartAt ℂ x).left_inv hz] at this

/-- A holomorphic section of `𝒪(x)`, read as a function normalized to `0` at `x`, is a local
section at every point of the divisor sheaf of the point divisor `x`. -/
theorem isDivisorSectionAt_pointTwistDiv (x : X)
    (τ : Cₛ^ω⟮𝓘(ℂ); ℂ, (pointTwistCore ℂ (Bundle.Trivial X ℂ) x).Fiber⟯) (y : X) :
    RiemannSurface.IsDivisorSectionAt (WeilDivisor.ofPoint x)
      (fun z ↦ (pointTwistDiv ℂ (Bundle.Trivial X ℂ) x z (τ z) : ℂ)) y := by
  have : T1Space X := ChartedSpace.t1Space ℂ X
  by_cases hy : y = x
  · subst hy
    have h1 : (WeilDivisor.ofPoint y) y = 1 := ofPoint_apply_self y
    have hD : 0 < (WeilDivisor.ofPoint y) y := h1 ▸ one_pos
    let ρ : X → ℂ := fun z ↦ pointTwistPoleMul ℂ (Bundle.Trivial X ℂ) y z (τ z)
    have hρ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ρ y :=
      contMDiffAt_trivial_section_iff.1 (contMDiffAt_pointTwist_section_iff_self.1 (τ.contMDiff y))
    have hρm : RiemannSurface.MeromorphicAt ρ y :=
      RiemannSurface.meromorphicAt_of_eventually_mdifferentiableAt
        ((contMDiffAt_iff_eventually_mdifferentiableAt (by simp)).1 hρ)
    have hρo : 0 ≤ RiemannSurface.meromorphicOrderAt ρ y :=
      RiemannSurface.meromorphicOrderAt_nonneg_of_continuousAt hρ.continuousAt
    have hc := (chartAt ℂ y).meromorphicAt_coordinate_zpow (IsManifold.chart_mem_maximalAtlas y)
      (chartAt ℂ y y) (-1) (mem_chart_source ℂ y)
    have hco := (chartAt ℂ y).meromorphicOrderAt_coordinate_zpow (IsManifold.chart_mem_maximalAtlas y)
      (chartAt ℂ y y) (-1) (mem_chart_source ℂ y)
    simp only [↓reduceIte] at hco
    have heq : (fun z ↦ (pointTwistDiv ℂ (Bundle.Trivial X ℂ) y z (τ z) : ℂ)) =ᶠ[𝓝[≠] y]
        (fun z ↦ (chartAt ℂ y z - chartAt ℂ y y) ^ (-1 : ℤ)) * ρ := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
        ((chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))] with z hzy hz
      have hc0 := pointTwistCoord_ne_zero hz hzy
      have key (w : ℂ) : (pointTwistDiv ℂ (Bundle.Trivial X ℂ) y z w : ℂ) =
          (chartAt ℂ y z - chartAt ℂ y y) ^ (-1 : ℤ) *
            (pointTwistPoleMul ℂ (Bundle.Trivial X ℂ) y z w : ℂ) := by
        rw [pointTwistPoleMul_eq_smul_pointTwistDiv hzy, smul_eq_mul, ← pointTwistCoord_eq_of_mem hz,
          zpow_neg_one, inv_mul_cancel_left₀ hc0]
      exact key (τ z)
    refine ⟨(hc.mul hρm).congr heq.symm, ?_, fun h ↦ absurd h (not_le.2 hD), fun _ ↦ ?_⟩
    · rw [RiemannSurface.meromorphicOrderAt_congr heq,
        RiemannSurface.meromorphicOrderAt_mul hc hρm, hco]
      rw [h1]
      exact le_add_of_nonneg_right hρo
    · exact congr($(pointTwistDiv_self ℂ (Bundle.Trivial X ℂ) y) (τ y))
  · have hD : (WeilDivisor.ofPoint x) y = 0 := ofPoint_apply_of_ne hy
    rw [RiemannSurface.isDivisorSectionAt_iff_of_eq_zero hD]
    exact contMDiffAt_trivial_section_iff.1
      ((contMDiffAt_pointTwist_section_iff_of_ne hy).1 (τ.contMDiff y))

/-- A local section at every point of the divisor sheaf of the point divisor `x` is the reading of
a holomorphic section of `𝒪(x)`: its product with the centred chart coordinate extends
holomorphically over `x`. -/
theorem exists_contMDiff_pointTwistOfPole {x : X} {G : X → ℂ}
    (hG : ∀ y, RiemannSurface.IsDivisorSectionAt (WeilDivisor.ofPoint x) G y) :
    ∃ ρ : X → ℂ, ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ)) ω
      (fun z ↦ TotalSpace.mk' ℂ z (pointTwistOfPole ℂ (E := Bundle.Trivial X ℂ) x G ρ z)) := by
  have : T1Space X := ChartedSpace.t1Space ℂ X
  let q : X → ℂ := fun z ↦ pointTwistCoord x z * G z
  have hcoord : (fun z ↦ pointTwistCoord x z) =ᶠ[𝓝[≠] x]
      fun z ↦ (chartAt ℂ x z - chartAt ℂ x x) ^ (1 : ℤ) := by
    filter_upwards [nhdsWithin_le_nhds
      ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))] with z hz
    rw [zpow_one, pointTwistCoord_eq_of_mem hz]
  have hc := ((chartAt ℂ x).meromorphicAt_coordinate_zpow (IsManifold.chart_mem_maximalAtlas x)
    (chartAt ℂ x x) 1 (mem_chart_source ℂ x)).congr hcoord.symm
  have hco := (chartAt ℂ x).meromorphicOrderAt_coordinate_zpow (IsManifold.chart_mem_maximalAtlas x)
    (chartAt ℂ x x) 1 (mem_chart_source ℂ x)
  simp only [↓reduceIte] at hco
  rw [← RiemannSurface.meromorphicOrderAt_congr hcoord] at hco
  have hq : RiemannSurface.MeromorphicAt q x := hc.mul (hG x).meromorphicAt
  have hqo : 0 ≤ RiemannSurface.meromorphicOrderAt q x := by
    have h1 : (WeilDivisor.ofPoint x) x = 1 := ofPoint_apply_self x
    have hG' := (hG x).neg_le_meromorphicOrderAt
    rw [h1] at hG'
    change 0 ≤ RiemannSurface.meromorphicOrderAt ((fun z ↦ pointTwistCoord x z) * G) x
    rw [RiemannSurface.meromorphicOrderAt_mul hc (hG x).meromorphicAt, hco]
    calc (0 : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) := by norm_cast
      _ ≤ _ := add_le_add_right hG' _
  refine ⟨fun y ↦ OnePoint.affineChart (RiemannSurface.sphereMap q y),
    contMDiff_pointTwistOfPole (fun y hy ↦ ?_) ?_ ?_⟩
  · have hD : (WeilDivisor.ofPoint x) y = 0 := ofPoint_apply_of_ne hy
    exact (contMDiffAt_trivial_section_iff.2 ((hG y).contMDiffAt hD.le)).contMDiffWithinAt
  · exact contMDiffAt_trivial_section_iff.2 (RiemannSurface.contMDiffAt_affineChart_sphereMap hq hqo)
  · exact RiemannSurface.affineChart_sphereMap_eventuallyEq hq

/-- **The sections of `𝒪(x)` are the sections of the divisor sheaf `𝒪_x`.** Reading a holomorphic
section of the point twist of the trivial line bundle as a function normalized to `0` at `x`
identifies the holomorphic sections of `𝒪(x)` with the global sections of the divisor sheaf of
the point divisor `x`. -/
def pointTwistSectionsEquivDivisorSections (x : X) :
    Cₛ^ω⟮𝓘(ℂ); ℂ, (pointTwistCore ℂ (Bundle.Trivial X ℂ) x).Fiber⟯ ≃ₗ[ℂ]
      RiemannSurface.divisorSections (WeilDivisor.ofPoint x) ⊤ where
  toFun τ := ⟨fun z ↦ (pointTwistDiv ℂ (Bundle.Trivial X ℂ) x z.1 (τ z.1) : ℂ),
    RiemannSurface.comp_val_mem_divisorSections fun y _ ↦ isDivisorSectionAt_pointTwistDiv x τ y⟩
  map_add' τ τ' := Subtype.ext <| funext fun z ↦
    map_add (pointTwistDiv ℂ (Bundle.Trivial X ℂ) x z.1) (τ z.1) (τ' z.1)
  map_smul' c τ := Subtype.ext <| funext fun z ↦
    map_smul (pointTwistDiv ℂ (Bundle.Trivial X ℂ) x z.1) c (τ z.1)
  invFun g := ⟨_, (exists_contMDiff_pointTwistOfPole
    (RiemannSurface.divisorSections.isDivisorSectionAt g)).choose_spec⟩
  left_inv τ := ContMDiffSection.eq_of_forall_ne (x := x) fun z hz ↦ by
    change pointTwistOfPole ℂ (E := Bundle.Trivial X ℂ) x _ _ z = τ z
    rw [pointTwistOfPole_of_ne ℂ hz]
    exact pointTwistMul_pointTwistDiv (F := ℂ) hz (τ z)
  right_inv g := by
    refine Subtype.ext <| funext fun ⟨z, hz'⟩ ↦ ?_
    change (pointTwistDiv ℂ (Bundle.Trivial X ℂ) x z (pointTwistOfPole ℂ x _ _ z) : ℂ) =
      g.1 ⟨z, hz'⟩
    by_cases hzx : z = x
    · subst hzx
      have hD : 0 < (WeilDivisor.ofPoint z) z := (ofPoint_apply_self z).symm ▸ one_pos
      rw [pointTwistDiv_self]
      exact ((RiemannSurface.divisorSections.isDivisorSectionAt g z).apply_eq_zero hD).symm
    · exact pointTwistDiv_pointTwistOfPole hzx _ _

end Trivial

/-! ### The zero count on the Riemann sphere -/

section OnePoint

open OnePoint

/-- On the Riemann sphere, the affine coordinate `z` is a holomorphic section of the twist `𝒪(∞)`
of the trivial line bundle at `∞`: in the inverted chart `w = 1 / z` its leading coefficient is
`w z = 1`. -/
theorem contMDiff_pointTwistOfPole_affineChart :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ)) ω (fun z ↦ TotalSpace.mk' ℂ z
      (pointTwistOfPole ℂ (E := Bundle.Trivial (OnePoint ℂ) ℂ) (∞ : OnePoint ℂ)
        (fun z ↦ affineChart z) (fun _ ↦ 1) z)) := by
  refine contMDiff_pointTwistOfPole (fun z hz ↦ ?_) ?_ ?_
  · have h := contMDiffOn_of_mem_maximalAtlas
      (affineChart_mem_maximalAtlas (𝕜 := ℂ) (n := ω))
    exact (contMDiffAt_trivial_section_iff.2 (h.contMDiffAt
      (affineChart.open_source.mem_nhds (by simpa using hz)))).contMDiffWithinAt
  · exact contMDiffAt_trivial_section_iff.2 contMDiffAt_const
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      ((chartAt ℂ (∞ : OnePoint ℂ)).open_source.mem_nhds (mem_chart_source ℂ (∞ : OnePoint ℂ)))]
      with z hzi hz
    have hc0 := pointTwistCoord_ne_zero hz hzi
    rw [pointTwistCoord_eq_of_mem hz, chartAt_infty, invChart_infty, sub_zero] at hc0 ⊢
    change (1 : ℂ) = invChart z * affineChart z
    rw [← inv_invChart, mul_inv_cancel₀ hc0]

/-- The section `z` of the twist `𝒪(∞)` of the trivial line bundle on the Riemann sphere vanishes
exactly at `0`. With `OnePoint.not_mdifferentiable_section_twistCore_zero_of_coe`, which says that
`z` is not a holomorphic section of the untwisted bundle, this is the zero count for `𝒪(1)`: a
global section with a single zero. -/
theorem pointTwistOfPole_affineChart_eq_zero_iff {z : OnePoint ℂ} :
    pointTwistOfPole ℂ (E := Bundle.Trivial (OnePoint ℂ) ℂ) (∞ : OnePoint ℂ)
        (fun z ↦ affineChart z) (fun _ ↦ 1) z = 0 ↔ z = ((0 : ℂ) : OnePoint ℂ) := by
  induction z using OnePoint.rec with
  | infty =>
    rw [pointTwistOfPole_self]
    exact ⟨fun h ↦ absurd h (one_ne_zero (α := ℂ)), fun h ↦ absurd h (infty_ne_coe 0)⟩
  | coe w =>
    rw [pointTwistOfPole_of_ne ℂ (coe_ne_infty w), pointTwistMul_apply_of_ne (coe_ne_infty w)]
    rw [affineChart_coe]
    exact coe_eq_coe.symm

end OnePoint

end TauCeti
