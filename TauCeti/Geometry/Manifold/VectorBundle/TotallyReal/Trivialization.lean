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

/-!
# Standard trivializations of totally real subbundles

Let `V` be a `C^n` complex vector bundle over a real manifold `B` (real-smooth, with complex-linear
fibres) and `L` a real subbundle of `V` with `C^n` local frames whose fibres are maximal totally
real, so that `V x = L x ⊕ i L x`. A real local frame `X` of `L` on `U` is then a complex basis of
`V x` at every point of `U`. Together with its multiples `i X`, it is a real `C^n` local frame of
`V` on `U`, the doubled frame `TauCeti.complexDoubledFrame X`. Given a complex basis `b` of the
model fibre `F`, the trivialization of this real frame sending `X i x` to `b i` and `i X i x` to
`i b i` is complex-linear on fibres, lies in the maximal atlas of `C^n` trivializations of `V`, and
sends `L x` onto the real span of `b`. With `F = ℂ^ι` and the standard basis, it identifies
`(V, L)` over `U` with `(U × ℂ^ι, U × ℝ^ι)`.

So every smooth totally real boundary condition on a complex vector bundle is locally the constant
condition `ℝ^ι ⊆ ℂ^ι` in suitable smooth complex trivializations.

## Main definitions

* `TauCeti.complexDoubledFrame`: the family `(X i, i X i)`, indexed by `Fin 2 × ι`.
* `TauCeti.IsSubbundleFrameOn.complexBasis`: a real local frame of a maximal totally real
  subspace, as a complex basis of the fibre.

## Main results

* `TauCeti.IsSubbundleFrameOn.isLocalFrameOn_complexDoubledFrame`: the doubled frame of a `C^n`
  real frame of a maximal totally real subbundle is a real `C^n` local frame of `V`.
* `IsLocalFrameOn.isLinear_complex_trivialization_complexDoubledFrame`: its trivialization is
  complex-linear on fibres.
* `IsLocalFrameOn.mem_iff_trivialization_complexDoubledFrame_mem_span`: it sends `L x` onto the
  real span of the basis of the model fibre.
* `TauCeti.HasLocalContMDiffSubbundleFrames.exists_trivialization_totallyReal`: near every point
  where its fibres are maximal totally real, a `C^n` totally real subbundle is the real span of a
  basis in a complex-linear trivialization of the maximal atlas.
* `TauCeti.HasLocalContMDiffSubbundleFrames.exists_trivialization_totallyReal_pi`: the same with
  model fibre `ι → ℂ`, where the real span of the standard basis is `ℝ^ι`.

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

@[simp]
theorem complexDoubledFrame_zero (σ : ι → Π x, V x) (i : ι) (x : B) :
    complexDoubledFrame σ (0, i) x = σ i x := by
  simp [complexDoubledFrame]

@[simp]
theorem complexDoubledFrame_one (σ : ι → Π x, V x) (i : ι) (x : B) :
    complexDoubledFrame σ (1, i) x = Complex.I • σ i x := by
  simp [complexDoubledFrame]

variable [TopologicalSpace B] {F : Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, Module ℝ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  {L : ∀ x, Submodule ℝ (V x)} {σ : ι → Π x, V x} {U : Set B}

/-- At a point where `L` is maximal totally real, a real local frame of `L` is a complex basis
of the fibre of `V`. -/
def IsSubbundleFrameOn.complexBasis (hX : IsSubbundleFrameOn F L σ U) {x : B} (hx : x ∈ U)
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    Basis ι ℂ (V x) :=
  hL.complexBasis (hX.basis hx)

@[simp]
theorem IsSubbundleFrameOn.coe_complexBasis (hX : IsSubbundleFrameOn F L σ U) {x : B}
    (hx : x ∈ U)
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x)) :
    ⇑(hX.complexBasis hx hL) = (σ · x) := by
  ext i
  simp [complexBasis, hX.coe_basis hx]

end Frame

end TauCeti

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  {n : ℕ∞ω} {ι : Type*} {U : Set B} {L : ∀ x, Submodule ℝ (V x)} {σ : ι → Π x, V x}

local instance : VectorBundle ℝ F V := VectorBundle.restrictScalars ℝ ℂ F V

namespace TauCeti

omit [∀ x, Module ℝ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)] in
/-- A constant complex multiple of a `C^n` section of a real-smooth complex vector bundle is
`C^n`: read in a trivialization of the atlas, it is the image of the section under a fixed
real-linear operator of the model fibre. -/
private theorem contMDiffOn_complex_smul (c : ℂ) {σ : Π x, V x} (hσ : CMDiff[U] n (T% σ)) :
    CMDiff[U] n (T% (fun x ↦ c • σ x)) := by
  intro x₀ hx₀
  have h := hσ x₀ hx₀
  rw [Bundle.contMDiffWithinAt_section] at h ⊢
  set e := trivializationAt F V x₀
  let A : F →L[ℝ] F := (c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ
  have hx₀e : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have heq (x : B) (hx : x ∈ e.baseSet) : (e ⟨x, c • σ x⟩).2 = A (e ⟨x, σ x⟩).2 := by
    simpa [A] using (e.linear ℂ hx).map_smul c (σ x)
  refine (((A.contMDiff) _).comp_contMDiffWithinAt x₀ h).congr_of_eventuallyEq ?_ (heq x₀ hx₀e)
  filter_upwards [nhdsWithin_le_nhds (e.open_baseSet.mem_nhds hx₀e)] with x hx
  exact heq x hx

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
    simp [complexDoubledFrame, Basis.smulTower_apply]
  exact ⟨fun hx ↦ hb hx ▸ Basis.linearIndependent _, fun hx ↦ hb hx ▸ (Basis.span_eq _).ge,
    fun p ↦ contMDiffOn_complex_smul _ (hσ p.2)⟩

end IsSubbundleFrameOn

end TauCeti

namespace IsLocalFrameOn

open TauCeti

variable [Finite ι] (hs : IsLocalFrameOn IB F n (complexDoubledFrame σ) U) (hU : IsOpen U)
  (b : Basis ι ℂ F)

/-- The trivialization of a doubled frame sends `σ i x` to `b i`. -/
theorem trivialization_complexDoubledFrame_apply_zero {x : B} (hx : x ∈ U) (i : ι) :
    hs.trivialization hU (Complex.basisOneI.smulTower b) ⟨x, σ i x⟩ = (x, b i) := by
  simpa [Basis.smulTower_apply] using hs.trivialization_apply_frame hU
    (Complex.basisOneI.smulTower b) hx (0, i)

/-- The trivialization of a doubled frame sends `i σ i x` to `i b i`. -/
theorem trivialization_complexDoubledFrame_apply_one {x : B} (hx : x ∈ U) (i : ι) :
    hs.trivialization hU (Complex.basisOneI.smulTower b) ⟨x, Complex.I • σ i x⟩ =
      (x, Complex.I • b i) := by
  simpa [Basis.smulTower_apply] using hs.trivialization_apply_frame hU
    (Complex.basisOneI.smulTower b) hx (1, i)

/-- **The trivialization of a doubled frame is complex-linear.** On each fibre over `U` the
trivialization sending `σ i x` to `b i` and `i σ i x` to `i b i` commutes with multiplication
by `i`, hence is complex-linear. -/
instance isLinear_complex_trivialization_complexDoubledFrame :
    (hs.trivialization hU (Complex.basisOneI.smulTower b)).IsLinear ℂ where
  linear x hx := by
    set e := hs.trivialization hU (Complex.basisOneI.smulTower b)
    rw [baseSet_trivialization] at hx
    have hlin := e.linear ℝ (by simpa [e] using hx)
    let f : V x →ₗ[ℝ] F := ⟨⟨fun v ↦ (e ⟨x, v⟩).2, hlin.map_add⟩, hlin.map_smul⟩
    let JV : V x →ₗ[ℝ] V x := (LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ
    let JF : F →ₗ[ℝ] F := (LinearMap.lsmul ℂ F Complex.I).restrictScalars ℝ
    -- Both composites agree on the real basis given by the doubled frame.
    have hJ : f ∘ₗ JV = JF ∘ₗ f := by
      refine (hs.toBasisAt hx).ext fun p ↦ ?_
      obtain ⟨k, i⟩ := p
      have h0 := hs.trivialization_complexDoubledFrame_apply_zero hU b hx i
      have h1 := hs.trivialization_complexDoubledFrame_apply_one hU b hx i
      fin_cases k
      · simp [toBasisAt_coe, f, JV, JF, e, h0, h1]
      · have hneg : Complex.I • Complex.I • σ i x = -σ i x := by
          rw [smul_smul, Complex.I_mul_I, neg_one_smul]
        have hm := hlin.map_neg (σ i x)
        simp [toBasisAt_coe, f, JV, JF, e, hneg, hm, h0, h1, smul_smul]
    refine ⟨hlin.map_add, fun c v ↦ ?_⟩
    have hIv : f (Complex.I • v) = Complex.I • f v := LinearMap.congr_fun hJ v
    change f (c • v) = c • f v
    have hV (r : ℝ) (w : V x) : (r : ℂ) • w = r • w := algebraMap_smul ℂ r w
    have hF (r : ℝ) (w : F) : (r : ℂ) • w = r • w := algebraMap_smul ℂ r w
    rw [← Complex.re_add_im c, add_smul, add_smul, mul_smul, mul_smul, hV, hV, hF, hF, map_add,
      map_smul, map_smul, hIv]

include hs in
/-- **A doubled totally real frame straightens `L`.** If `σ` spans `L x` over `ℝ` at a point
`x ∈ U`, the trivialization of the doubled frame sends `L x` onto the real span of the basis `b`
of the model fibre. -/
theorem mem_iff_trivialization_complexDoubledFrame_mem_span {x : B} (hx : x ∈ U)
    (hσL : Submodule.span ℝ (range (σ · x)) = L x) (v : V x) :
    v ∈ L x ↔ (hs.trivialization hU (Complex.basisOneI.smulTower b) ⟨x, v⟩).2 ∈
      Submodule.span ℝ (range b) := by
  set e := hs.trivialization hU (Complex.basisOneI.smulTower b)
  have hxe : x ∈ e.baseSet := by simpa [e] using hx
  set f := e.linearEquivAt ℝ x hxe
  have hmap : (L x).map f.toLinearMap = Submodule.span ℝ (range b) := by
    rw [← hσL, Submodule.map_span, ← range_comp]
    congr 2
    ext i
    simp [f, e, Trivialization.linearEquivAt_apply,
      hs.trivialization_complexDoubledFrame_apply_zero hU b hx i]
  change v ∈ L x ↔ f v ∈ _
  rw [← hmap, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

end IsLocalFrameOn

namespace TauCeti

/-- The real span of the standard basis of `ι → ℂ` is `ℝ^ι`, the vectors with real entries. -/
private theorem mem_span_range_basisFun_iff [Finite ι] (w : ι → ℂ) :
    w ∈ Submodule.span ℝ (range (Pi.basisFun ℂ ι)) ↔ ∀ i, (w i).im = 0 := by
  classical
  let := Fintype.ofFinite ι
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ i
    simp [Finset.sum_apply, Pi.basisFun_apply, Pi.single_apply]
  · intro hw
    refine ⟨fun i ↦ (w i).re, funext fun j ↦ ?_⟩
    simp [Finset.sum_apply, Pi.basisFun_apply, Pi.single_apply, Complex.ext_iff, hw j]

namespace HasLocalContMDiffSubbundleFrames

variable [Finite ι] [ContMDiffVectorBundle n F V IB]

/-- **Standard form of a totally real subbundle.** Let `L` be a real subbundle of a `C^n` complex
vector bundle with `C^n` local frames, whose fibres are maximal totally real over an open set
`s`. Near every point of `s` there is a trivialization of the maximal atlas of `C^n`
trivializations, complex-linear on fibres and with base set inside `s`, sending each fibre of `L`
onto the real span of a given complex basis `b` of the model fibre. -/
theorem exists_trivialization_totallyReal (hLs : HasLocalContMDiffSubbundleFrames IB n F ι L)
    {s : Set B} (hs : IsOpen s)
    (hL : ∀ x ∈ s,
      IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x))
    (b : Basis ι ℂ F) {x₀ : B} (hx₀ : x₀ ∈ s) :
    ∃ (e : Trivialization F (π F V)) (_ : e.IsLinear ℂ),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F V) ∧
      x₀ ∈ e.baseSet ∧ e.baseSet ⊆ s ∧
      ∀ x ∈ e.baseSet, ∀ v : V x, v ∈ L x ↔ (e ⟨x, v⟩).2 ∈ Submodule.span ℝ (range b) := by
  obtain ⟨U, hU, hx₀U, σ, hX, hσ⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hLs x₀
  have hX' := hX.mono (inter_subset_left (t := s))
  have hfr : IsLocalFrameOn IB F n (complexDoubledFrame σ) (U ∩ s) :=
    hX'.isLocalFrameOn_complexDoubledFrame (fun x hx ↦ hL x hx.2)
      fun i ↦ (hσ i).mono inter_subset_left
  have hUs := hU.inter hs
  refine ⟨hfr.trivialization hUs (Complex.basisOneI.smulTower b), inferInstance,
    hfr.trivialization_mem_maximalAtlas hUs _, ?_, ?_, fun x hx v ↦ ?_⟩
  · simpa using And.intro hx₀U hx₀
  · simp
  · rw [IsLocalFrameOn.baseSet_trivialization] at hx
    exact hfr.mem_iff_trivialization_complexDoubledFrame_mem_span hUs b hx (hX'.span_eq hx) v

omit [Finite ι] in
/-- **Standard form of a totally real subbundle, model fibre `ℂ^ι`.** For a `C^n` complex vector
bundle with model fibre `ι → ℂ`, near every point of an open set `s` where the fibres of a real
subbundle `L` with `C^n` local frames are maximal totally real, a complex-linear trivialization of
the maximal atlas identifies `(V, L)` with `(U × ℂ^ι, U × ℝ^ι)`: a vector lies in `L` exactly when
its coordinates are real. -/
theorem exists_trivialization_totallyReal_pi [Fintype ι] [TopologicalSpace (TotalSpace (ι → ℂ) V)]
    [FiberBundle (ι → ℂ) V] [VectorBundle ℂ (ι → ℂ) V] [VectorBundle ℝ (ι → ℂ) V]
    [ContMDiffVectorBundle n (ι → ℂ) V IB]
    (hLs : HasLocalContMDiffSubbundleFrames IB n (ι → ℂ) ι L) {s : Set B} (hs : IsOpen s)
    (hL : ∀ x ∈ s,
      IsMaximalTotallyReal ((LinearMap.lsmul ℂ (V x) Complex.I).restrictScalars ℝ) (L x))
    {x₀ : B} (hx₀ : x₀ ∈ s) :
    ∃ (e : Trivialization (ι → ℂ) (π (ι → ℂ) V)) (_ : e.IsLinear ℂ),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear B (ι → ℂ) IB n).maximalAtlas (TotalSpace (ι → ℂ) V) ∧
      x₀ ∈ e.baseSet ∧ e.baseSet ⊆ s ∧
      ∀ x ∈ e.baseSet, ∀ v : V x, v ∈ L x ↔ ∀ i, ((e ⟨x, v⟩).2 i).im = 0 := by
  obtain ⟨e, he, hmem, hx₀e, hes, heL⟩ :=
    hLs.exists_trivialization_totallyReal hs hL (Pi.basisFun ℂ ι) hx₀
  exact ⟨e, he, hmem, hx₀e, hes, fun x hx v ↦ (heL x hx v).trans
    (mem_span_range_basisFun_iff _)⟩

end HasLocalContMDiffSubbundleFrames

end TauCeti
