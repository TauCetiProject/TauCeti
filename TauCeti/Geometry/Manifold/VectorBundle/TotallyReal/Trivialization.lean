/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RingTheory.AlgebraTower
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import TauCeti.LinearAlgebra.TotallyReal.Complex
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.LinearAlgebra.Complex.Module
import TauCeti.Topology.VectorBundle.Complex.SmulI
import TauCeti.Topology.VectorBundle.RealForm

/-!
# Standard trivializations of totally real subbundles

Let `V` be a `C^n` complex vector bundle over a real manifold `B` (real-smooth, with complex-linear
fibres) and `L` a family of real subspaces of its fibres with a `C^n` real local frame `σ` on an
open set `U`. Where the fibres of `L` are maximal totally real, so that `V x = L x ⊕ i L x`, the
frame `σ` is a complex basis of `V x` (`TauCeti.IsSubbundleFrameOn.complexBasis`). Together with
its multiples `i σ`, it is a real `C^n` local frame of `V`, the doubled frame
`TauCeti.complexDoubledFrame σ`. Given a complex basis `b` of the model fibre `F`, the
trivialization of this real frame sending `σ i x` to `b i` and `i σ i x` to `i b i` is
complex-linear on fibres, lies in the maximal atlas of `C^n` trivializations of `V`, and sends
`L x` onto the real span of `b`. With `F = ℂ^ι` and the standard basis, it identifies `(V, L)`
over a neighbourhood `W` of a point with `(W × ℂ^ι, W × ℝ^ι)`.

Maximal total reality is an open condition along a frame
(`TauCeti.eventually_isMaximalTotallyReal`), so it suffices to assume it at a single point, and
the frame only needs to be defined near that point. So every smooth totally real boundary
condition on a complex vector bundle is locally the constant condition `ℝ^ι ⊆ ℂ^ι` in suitable
smooth complex trivializations.

## Main definitions

* `TauCeti.complexDoubledFrame`: the family `(σ i, i σ i)`, indexed by `Fin 2 × ι`.

## Main results

* `TauCeti.IsSubbundleFrameOn.isLocalFrameOn_complexDoubledFrame`: the doubled frame of a `C^n`
  real frame of a maximal totally real subbundle is a real `C^n` local frame of `V`.
* `IsLocalFrameOn.isLinear_complex_trivialization_complexDoubledFrame`: its trivialization is
  complex-linear on fibres.
* `IsLocalFrameOn.mem_iff_trivialization_complexDoubledFrame_mem_span`: it sends the real span
  of the frame onto the real span of the basis of the model fibre.
* `TauCeti.IsSubbundleFrameOn.exists_trivialization_totallyReal`: near a point where its fibre is
  maximal totally real, a family of real subspaces with a `C^n` local frame is the real span of a
  basis in a complex-linear trivialization of the maximal atlas.
* `TauCeti.IsSubbundleFrameOn.exists_trivialization_totallyReal_pi`: the same with model fibre
  `ι → ℂ`, where the real span of the standard basis is `ℝ^ι`.
* `TauCeti.HasLocalContMDiffSubbundleFrames.exists_trivialization_totallyReal` and
  `TauCeti.HasLocalContMDiffSubbundleFrames.exists_trivialization_totallyReal_pi`: the same for a
  real subbundle with `C^n` local frames.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  AMS (2012), Section C.1 and Section C.4.
-/

public section

noncomputable section

open Bundle Set Module
open scoped Manifold ContDiff Topology

namespace TauCeti

section Frame

variable {B : Type*} {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] {ι : Type*}

/-- The doubled frame of a family of sections `σ` of a complex vector bundle: the real family
`(σ i, i σ i)`, indexed by `Fin 2 × ι`, whose member `(k, i)` is `Complex.basisOneI k • σ i`. -/
def complexDoubledFrame (σ : ι → Π x, V x) : Fin 2 × ι → Π x, V x :=
  fun p x ↦ Complex.basisOneI p.1 • σ p.2 x

theorem complexDoubledFrame_apply (σ : ι → Π x, V x) (p : Fin 2 × ι) (x : B) :
    complexDoubledFrame σ p x = Complex.basisOneI p.1 • σ p.2 x :=
  (rfl)

@[simp]
theorem complexDoubledFrame_zero (σ : ι → Π x, V x) (i : ι) (x : B) :
    complexDoubledFrame σ (0, i) x = σ i x := by
  simp [complexDoubledFrame_apply]

@[simp]
theorem complexDoubledFrame_one (σ : ι → Π x, V x) (i : ι) (x : B) :
    complexDoubledFrame σ (1, i) x = Complex.I • σ i x := by
  simp [complexDoubledFrame_apply]

end Frame

end TauCeti

variable {X H B : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  {n : ℕ∞ω} {ι : Type*} {U : Set B} {σ : ι → Π x, V x} {L : ∀ x, Submodule ℝ (V x)}

section ModelFibre

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]

namespace IsLocalFrameOn

open TauCeti

variable [Module ℂ F] [IsScalarTower ℝ ℂ F] [VectorBundle ℝ F V] [Finite ι]
  (hs : IsLocalFrameOn IB F n (complexDoubledFrame σ) U) (hU : IsOpen U) (b : Basis ι ℂ F)

omit [∀ x, IsScalarTower ℝ ℂ (V x)] in
/-- The trivialization of a doubled frame sends `σ i x` to `b i`. -/
@[simp]
theorem trivialization_complexDoubledFrame_apply_frame {x : B} (hx : x ∈ U) (i : ι) :
    hs.trivialization hU (Complex.basisOneI.smulTower b) ⟨x, σ i x⟩ = (x, b i) := by
  simpa [Basis.smulTower_apply] using hs.trivialization_apply_frame hU
    (Complex.basisOneI.smulTower b) hx (0, i)

omit [∀ x, IsScalarTower ℝ ℂ (V x)] in
/-- The trivialization of a doubled frame sends `i σ i x` to `i b i`. -/
@[simp]
theorem trivialization_complexDoubledFrame_apply_I_smul_frame {x : B} (hx : x ∈ U) (i : ι) :
    hs.trivialization hU (Complex.basisOneI.smulTower b) ⟨x, Complex.I • σ i x⟩ =
      (x, Complex.I • b i) := by
  simpa [Basis.smulTower_apply] using hs.trivialization_apply_frame hU
    (Complex.basisOneI.smulTower b) hx (1, i)

/-- **The trivialization of a doubled frame is complex-linear.** On each fibre over `U` the
trivialization sending `σ i x` to `b i` and `i σ i x` to `i b i` commutes with multiplication
by `i`, hence is complex-linear. -/
instance isLinear_complex_trivialization_complexDoubledFrame :
    (hs.trivialization hU (Complex.basisOneI.smulTower b)).IsLinear ℂ :=
  Trivialization.isLinear_complex_of_map_I_smul _ fun x hxe v ↦ by
    set e := hs.trivialization hU (Complex.basisOneI.smulTower b)
    have hx : x ∈ U := by simpa [e] using hxe
    -- Both sides are real-linear in `v` and agree on the real basis given by the doubled frame.
    have hJ : e.linearMapAt ℝ x ∘ₗ (LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ =
        (LinearMap.lsmul ℂ F Complex.I).restrictScalars ℝ ∘ₗ e.linearMapAt ℝ x := by
      refine (hs.toBasisAt hx).ext fun ⟨k, i⟩ ↦ ?_
      have h0 := hs.trivialization_complexDoubledFrame_apply_frame hU b hx i
      have h1 := hs.trivialization_complexDoubledFrame_apply_I_smul_frame hU b hx i
      fin_cases k
      · simp [toBasisAt_coe, e.coe_linearMapAt_of_mem hxe, e, h0, h1]
      · have hneg : Complex.I • Complex.I • σ i x = -σ i x := by
          rw [smul_smul, Complex.I_mul_I, neg_one_smul]
        have hm := (e.linear ℝ hxe).map_neg (σ i x)
        simp [toBasisAt_coe, e.coe_linearMapAt_of_mem hxe, e, hneg, hm, h0, h1, smul_smul]
    simpa [e.coe_linearMapAt_of_mem hxe] using LinearMap.congr_fun hJ v

omit [∀ x, IsScalarTower ℝ ℂ (V x)] in
include hs in
/-- **A doubled totally real frame straightens `L`.** If `σ` spans a real subspace `L` of `V x`
at a point `x ∈ U`, the trivialization of the doubled frame sends `L` onto the real span of the
basis `b` of the model fibre. -/
theorem mem_iff_trivialization_complexDoubledFrame_mem_span {x : B} (hx : x ∈ U)
    {L : Submodule ℝ (V x)} (hσL : Submodule.span ℝ (range (σ · x)) = L) (v : V x) :
    v ∈ L ↔ (hs.trivialization hU (Complex.basisOneI.smulTower b) ⟨x, v⟩).2 ∈
      Submodule.span ℝ (range b) := by
  set e := hs.trivialization hU (Complex.basisOneI.smulTower b)
  have hxe : x ∈ e.baseSet := by simpa [e] using hx
  set f := e.linearEquivAt ℝ x hxe
  have hmap : L.map f.toLinearMap = Submodule.span ℝ (range b) := by
    rw [← hσL, Submodule.map_span, ← range_comp]
    congr 2
    ext i
    simp [f, e, Trivialization.linearEquivAt_apply,
      hs.trivialization_complexDoubledFrame_apply_frame hU b hx i]
  rw [← e.linearEquivAt_apply (R := ℝ) x hxe v, ← hmap,
    Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

end IsLocalFrameOn

section ComplexBundle

variable [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [VectorBundle ℂ F V]

local instance : VectorBundle ℝ F V := VectorBundle.restrictScalars ℝ ℂ F V

namespace TauCeti

namespace IsSubbundleFrameOn

/-- **The doubled frame of a totally real frame.** On a set `U` where the fibres of `L` are
maximal totally real, a `C^n` real local frame `σ` of `L` gives the real `C^n` local frame
`(σ i, i σ i)` of `V`. -/
theorem isLocalFrameOn_complexDoubledFrame (hX : IsSubbundleFrameOn F L σ U)
    (hL : ∀ x ∈ U,
      IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x))
    (hσ : ∀ i, CMDiff[U] n (T% (σ i))) :
    IsLocalFrameOn IB F n (complexDoubledFrame σ) U := by
  have hb {x : B} (hx : x ∈ U) : (complexDoubledFrame σ · x) =
      ⇑(Complex.basisOneI.smulTower (hX.complexBasis hx (hL x hx))) := by
    ext p
    simp [complexDoubledFrame_apply, Basis.smulTower_apply]
  exact ⟨fun hx ↦ hb hx ▸ Basis.linearIndependent _, fun hx ↦ hb hx ▸ (Basis.span_eq _).ge,
    fun p ↦ contMDiffOn_const.smul_totalSpace (hσ p.2)⟩

variable [Finite ι] [ContMDiffVectorBundle n F V IB]

/-- **Standard form of a totally real subbundle along a frame.** Let `σ` be a `C^n` real local
frame on a neighbourhood `U` of `x₀` of a family `L` of real subspaces of the fibres of a `C^n`
complex vector bundle, and let the fibre of `L` at `x₀` be maximal totally real. Then within any
neighbourhood `s` of `x₀` there is a trivialization of the maximal atlas of `C^n` trivializations
around `x₀`, complex-linear on fibres, sending each fibre of `L` onto the real span of a given
complex basis `b` of the model fibre. -/
theorem exists_trivialization_totallyReal (hX : IsSubbundleFrameOn F L σ U)
    (hσ : ∀ i, CMDiff[U] n (T% (σ i))) {x₀ : B} (hU : U ∈ 𝓝 x₀)
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x₀) Complex.I).restrictScalars ℝ) (L x₀))
    (b : Basis ι ℂ F) {s : Set B} (hs : s ∈ 𝓝 x₀) :
    ∃ (e : Trivialization F (π F V)) (_ : e.IsLinear ℂ),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F V) ∧
      x₀ ∈ e.baseSet ∧ e.baseSet ⊆ s ∧
      ∀ x ∈ e.baseSet, ∀ v : V x, v ∈ L x ↔ (e ⟨x, v⟩).2 ∈ Submodule.span ℝ (range b) := by
  -- Shrink `U` to an open neighbourhood of `x₀` inside `s` where `L` is maximal totally real.
  obtain ⟨U', hU'U, hU', hx₀U'⟩ := mem_nhds_iff.mp hU
  obtain ⟨W, hWsub, hW, hx₀W⟩ := mem_nhds_iff.mp <|
    Filter.inter_mem (Filter.inter_mem hU hs)
      (eventually_isMaximalTotallyReal hU' (hX.mono hU'U) hx₀U' hL)
  have hWU : W ⊆ U := fun y hy ↦ (hWsub hy).1.1
  have hXW := hX.mono hWU
  have hfr : IsLocalFrameOn IB F n (complexDoubledFrame σ) W :=
    hXW.isLocalFrameOn_complexDoubledFrame (fun y hy ↦ (hWsub hy).2) fun i ↦ (hσ i).mono hWU
  refine ⟨hfr.trivialization hW (Complex.basisOneI.smulTower b), inferInstance,
    hfr.trivialization_mem_maximalAtlas hW _, by simpa using hx₀W, ?_, fun x hx v ↦ ?_⟩
  · rw [IsLocalFrameOn.baseSet_trivialization]
    exact fun y hy ↦ (hWsub hy).1.2
  · rw [IsLocalFrameOn.baseSet_trivialization] at hx
    exact hfr.mem_iff_trivialization_complexDoubledFrame_mem_span hW b hx (hXW.span_eq hx) v

end IsSubbundleFrameOn

namespace HasLocalContMDiffSubbundleFrames

variable [Finite ι] [ContMDiffVectorBundle n F V IB]

/-- **Standard form of a totally real subbundle.** Let `L` be a real subbundle of a `C^n` complex
vector bundle with `C^n` local frames, whose fibre at `x₀` is maximal totally real. Within any
neighbourhood `s` of `x₀` there is a trivialization of the maximal atlas of `C^n` trivializations
around `x₀`, complex-linear on fibres, sending each fibre of `L` onto the real span of a given
complex basis `b` of the model fibre. -/
theorem exists_trivialization_totallyReal (hLs : HasLocalContMDiffSubbundleFrames IB n F ι L)
    {x₀ : B}
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x₀) Complex.I).restrictScalars ℝ) (L x₀))
    (b : Basis ι ℂ F) {s : Set B} (hs : s ∈ 𝓝 x₀) :
    ∃ (e : Trivialization F (π F V)) (_ : e.IsLinear ℂ),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F V) ∧
      x₀ ∈ e.baseSet ∧ e.baseSet ⊆ s ∧
      ∀ x ∈ e.baseSet, ∀ v : V x, v ∈ L x ↔ (e ⟨x, v⟩).2 ∈ Submodule.span ℝ (range b) := by
  obtain ⟨U, hU, hx₀U, σ, hX, hσ⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hLs x₀
  exact hX.exists_trivialization_totallyReal hσ (hU.mem_nhds hx₀U) hL b hs

end HasLocalContMDiffSubbundleFrames

end TauCeti

end ComplexBundle

end ModelFibre

section PiModelFibre

variable [Fintype ι] [TopologicalSpace (TotalSpace (ι → ℂ) V)] [FiberBundle (ι → ℂ) V]
  [VectorBundle ℂ (ι → ℂ) V]

local instance : VectorBundle ℝ (ι → ℂ) V := VectorBundle.restrictScalars ℝ ℂ (ι → ℂ) V

variable [ContMDiffVectorBundle n (ι → ℂ) V IB]

namespace TauCeti

namespace IsSubbundleFrameOn

/-- **Standard form of a totally real subbundle along a frame, model fibre `ℂ^ι`.** For a `C^n`
complex vector bundle with model fibre `ι → ℂ`, let `σ` be a `C^n` real local frame on a
neighbourhood `U` of `x₀` of a family `L` of real subspaces of the fibres, maximal totally real at
`x₀`. Within
any neighbourhood `s` of `x₀`, a complex-linear trivialization `e` of the maximal atlas around `x₀`
identifies `(V, L)` over its base set `W ⊆ s` with `(W × ℂ^ι, W × ℝ^ι)`: a vector lies in `L`
exactly when its coordinates are real. -/
theorem exists_trivialization_totallyReal_pi
    (hX : IsSubbundleFrameOn (ι → ℂ) L σ U)
    (hσ : ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, ι → ℂ)) n (fun x ↦ TotalSpace.mk' (ι → ℂ) x (σ i x)) U)
    {x₀ : B} (hU : U ∈ 𝓝 x₀)
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x₀) Complex.I).restrictScalars ℝ) (L x₀))
    {s : Set B} (hs : s ∈ 𝓝 x₀) :
    ∃ (e : Trivialization (ι → ℂ) (π (ι → ℂ) V)) (_ : e.IsLinear ℂ),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear B (ι → ℂ) IB n).maximalAtlas (TotalSpace (ι → ℂ) V) ∧
      x₀ ∈ e.baseSet ∧ e.baseSet ⊆ s ∧
      ∀ x ∈ e.baseSet, ∀ v : V x, v ∈ L x ↔ ∀ i, ((e ⟨x, v⟩).2 i).im = 0 := by
  obtain ⟨e, he, hmem, hx₀e, hes, heL⟩ :=
    hX.exists_trivialization_totallyReal hσ hU hL (Pi.basisFun ℂ ι) hs
  exact ⟨e, he, hmem, hx₀e, hes, fun x hx v ↦ (heL x hx v).trans
    (mem_span_real_range_basisFun_iff _)⟩

end IsSubbundleFrameOn

namespace HasLocalContMDiffSubbundleFrames

/-- **Standard form of a totally real subbundle, model fibre `ℂ^ι`.** For a `C^n` complex vector
bundle with model fibre `ι → ℂ` and a real subbundle `L` with `C^n` local frames whose fibre at
`x₀` is maximal totally real, within any neighbourhood `s` of `x₀` a complex-linear
trivialization `e` of the maximal atlas around `x₀` identifies `(V, L)` over its base set
`W ⊆ s` with `(W × ℂ^ι, W × ℝ^ι)`: a vector lies in `L` exactly when its coordinates are real. -/
theorem exists_trivialization_totallyReal_pi
    (hLs : HasLocalContMDiffSubbundleFrames IB n (ι → ℂ) ι L) {x₀ : B}
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x₀) Complex.I).restrictScalars ℝ) (L x₀))
    {s : Set B} (hs : s ∈ 𝓝 x₀) :
    ∃ (e : Trivialization (ι → ℂ) (π (ι → ℂ) V)) (_ : e.IsLinear ℂ),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear B (ι → ℂ) IB n).maximalAtlas (TotalSpace (ι → ℂ) V) ∧
      x₀ ∈ e.baseSet ∧ e.baseSet ⊆ s ∧
      ∀ x ∈ e.baseSet, ∀ v : V x, v ∈ L x ↔ ∀ i, ((e ⟨x, v⟩).2 i).im = 0 := by
  obtain ⟨U, hU, hx₀U, σ, hX, hσ⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hLs x₀
  exact hX.exists_trivialization_totallyReal_pi hσ (hU.mem_nhds hx₀U) hL hs

end HasLocalContMDiffSubbundleFrames

end TauCeti

end PiModelFibre
