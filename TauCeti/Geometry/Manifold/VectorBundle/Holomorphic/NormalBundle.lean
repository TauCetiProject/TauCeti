/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Transverse
public import TauCeti.Geometry.Symplectic.Finrank
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Normal line bundles of complex hypersurfaces and the real-hypersurface obstruction

For an embedded complex submanifold `i : Z → M` of complex codimension one
(`Module.finrank ℂ EZ + 1 = Module.finrank ℂ EM`), `SmoothEmbedding.tangentMap_injective`
(`TauCeti.Geometry.Manifold.SmoothEmbedding.Basic`) makes `tangentMap 𝓘(ℂ, EZ) 𝓘(ℂ, EM) i`
complex-linear and injective; promoting `i` via `SmoothEmbedding.ofNeZero`
(`TauCeti.Geometry.Manifold.Complex.Immersion`) and applying
`TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.TangentSubbundle` realizes
`x ↦ i.tangentRange x hn` as a holomorphic (`C^∞`, and `C^ω` after regularity promotion) vector
subbundle of `i* TM` biholomorphic to `TZ`; and `SmoothEmbedding.finrank_normalSpace_eq_one`
(`TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic`) together with
`TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Transverse` identifies the
rank-one quotient `i* TM / TZ` (`i.NormalSpace`) with the scalar transition-cocycle model built from
transverse complex charts.

This file characterizes closedness of complex hypersurfaces by holomorphic local defining equations
(`isClosed_range_iff_forall_exists_mdifferentiableOn_eq_zero`), establishes `C^ω` complex
analyticity of the scalar cocycle and its `VectorBundleCore`
(`contMDiffOn_omega_transverseNormalCore_coordChange_one`,
`isContMDiff_omega_transverseNormalCore`), and proves that no real-codimension-one smooth
hypersurface (such as `TauCeti.realAxisEmbedding`) has `J`-invariant tangent spaces
(`not_forall_almostComplexStructure_mem_tangentRange`,
`not_forall_ofComplexManifold_mem_tangentRange`) or an almost complex / compatible `ℂ`-module
structure on its normal fibres (`isEmpty_almostComplexStructure_normalSpace`,
`not_exists_module_complex_isScalarTower_normalSpace`).

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §§2.1–2.2.
* Phillip Griffiths and Joseph Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Ch. 0–1.
-/

public noncomputable section

open Set Function Bundle Topology Manifold
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

namespace SmoothEmbedding

section ComplexHypersurface

variable {EZ EM Z M : Type*}
  [NormedAddCommGroup EZ] [NormedSpace ℂ EZ]
  [NormedAddCommGroup EM] [NormedSpace ℂ EM] [FiniteDimensional ℂ EM]
  [TopologicalSpace Z] [ChartedSpace EZ Z]
  [TopologicalSpace M] [ChartedSpace EM M] [IsManifold 𝓘(ℂ, EM) ∞ M]

/-- **Holomorphic local defining equations for closed embedded complex hypersurfaces.** An embedded
complex submanifold `i : Z → M` of complex codimension one (`finrank ℂ EZ + 1 = finrank ℂ EM`) has
closed image in `M` if and only if every ambient point `y₀ : M` admits an open neighbourhood `S`
and a holomorphic (`MDifferentiableOn`) function `g : M → ℂ` on `S` whose zero locus in `S` is
`S ∩ Set.range i` and whose differential `mvfderiv 𝓘(ℂ, EM) g y` is nonzero along `S ∩ Set.range i`.
Unlike the smooth case over `ℝ`, no `C¹` derivative-continuity hypothesis on `g` is needed. -/
theorem isClosed_range_iff_forall_exists_mdifferentiableOn_eq_zero
    (i : SmoothEmbedding 𝓘(ℂ, EZ) 𝓘(ℂ, EM) ∞ Z M)
    (hcodim : Module.finrank ℂ EZ + 1 = Module.finrank ℂ EM) :
    IsClosed (Set.range i) ↔
      ∀ y₀ : M, ∃ S : Set M, IsOpen S ∧ y₀ ∈ S ∧ ∃ g : M → ℂ,
        MDifferentiableOn 𝓘(ℂ, EM) 𝓘(ℂ) g S ∧
        (∀ y ∈ S, y ∈ Set.range i ↔ g y = 0) ∧
        ∀ y ∈ S ∩ Set.range i, mvfderiv 𝓘(ℂ, EM) g y ≠ 0 := by
  rw [i.isClosed_range_iff_forall_exists_contMDiffOn_eq_zero (by simp)
    (by rw [Module.finrank_self]; omega)]
  exact forall_congr' fun _ ↦ exists_congr fun S ↦ and_congr_right fun hS ↦
    and_congr_right fun _ ↦ exists_congr fun _ ↦ and_congr
      (TauCeti.contMDiffOn_iff_mdifferentiableOn (by simp : (∞ : ℕ∞ω) ≠ 0) hS)
      (and_congr_right fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
        TauCeti.isRegularPoint_iff_mvfderiv_ne_zero)

variable [FiniteDimensional ℂ EZ] [IsManifold 𝓘(ℂ, EZ) ∞ Z]

/-- **Complex analyticity (`C^ω`) of the scalar transition cocycle of a complex hypersurface.** On
every overlap of transverse complex charts of `i`, the scalar transition function
`z ↦ coordChange z₀ z₁ z 1` satisfies `ContMDiffOn 𝓘(ℂ, EZ) 𝓘(ℂ) ω`. -/
theorem contMDiffOn_omega_transverseNormalCore_coordChange_one
    (i : SmoothEmbedding 𝓘(ℂ, EZ) 𝓘(ℂ, EM) ∞ Z M)
    (hdim : Module.finrank ℂ ℂ = Module.finrank ℂ EM - Module.finrank ℂ EZ) (z₀ z₁ : Z) :
    haveI : IsManifold 𝓘(ℂ, EZ) (∞ + 1) Z := .of_le (n := ∞) (by simp)
    ContMDiffOn 𝓘(ℂ, EZ) 𝓘(ℂ) ω
      (fun z ↦ (i.transverseNormalCore (m := ∞) (by simp) (by simp) hdim).coordChange z₀ z₁ z 1)
      (i ⁻¹' i.transverseAmbientSet (by simp) hdim z₀ ∩
        i ⁻¹' i.transverseAmbientSet (by simp) hdim z₁) :=
  haveI : IsManifold 𝓘(ℂ, EZ) (∞ + 1) Z := .of_le (n := ∞) (by simp)
  ((i.contMDiffOn_transverseNormalCore_coordChange_one (m := ∞) (by simp) (by simp) hdim
    z₀ z₁).mdifferentiableOn (by simp)).contMDiffOn
    (((i.isOpen_transverseAmbientSet (by simp) hdim z₀).preimage (map_continuous i)).inter
      ((i.isOpen_transverseAmbientSet (by simp) hdim z₁).preimage (map_continuous i)))

/-- **The transverse transition-cocycle core of a complex hypersurface is complex-analytic
(`C^ω`).** -/
instance isContMDiff_omega_transverseNormalCore
    (i : SmoothEmbedding 𝓘(ℂ, EZ) 𝓘(ℂ, EM) ∞ Z M)
    (hdim : Module.finrank ℂ ℂ = Module.finrank ℂ EM - Module.finrank ℂ EZ) :
    haveI : IsManifold 𝓘(ℂ, EZ) (∞ + 1) Z := .of_le (n := ∞) (by simp)
    (i.transverseNormalCore (m := ∞) (by simp) (by simp) hdim).IsContMDiff 𝓘(ℂ, EZ) ω := by
  have : IsManifold 𝓘(ℂ, EZ) (∞ + 1) Z := .of_le (n := ∞) (by simp)
  rw [VectorBundleCore.isContMDiff_iff_contMDiffOn_coordChange_one]
  intro z₀ z₁
  simpa only [i.transverseNormalCore_baseSet] using
    i.contMDiffOn_omega_transverseNormalCore_coordChange_one hdim z₀ z₁

end ComplexHypersurface

section RealHypersurfaceObstruction

section RealAmbient

variable {EH EM HH HM H M : Type*}
  [NormedAddCommGroup EH] [NormedSpace ℝ EH]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [TopologicalSpace HH] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EH HH} {J : ModelWithCorners ℝ EM HM}
  [TopologicalSpace H] [ChartedSpace HH H]
  [TopologicalSpace M] [ChartedSpace HM M]

/-- **A real-smooth hypersurface never has `J`-invariant tangent spaces.** For any `C^n` (`n ≠ 0`)
real embedding `f : H → M` of real codimension one (`finrank ℝ EH + 1 = finrank ℝ EM`) and any
almost complex structure `Jx` on the ambient tangent space `TangentSpace J (f x)`, the tangent
image `f.tangentRange x hn` is not preserved by `Jx`. -/
theorem not_forall_almostComplexStructure_mem_tangentRange {n : ℕ∞ω}
    (f : SmoothEmbedding I J n H M) (hn : n ≠ 0)
    (hcodim : Module.finrank ℝ EH + 1 = Module.finrank ℝ EM) (x : H)
    (Jx : AlmostComplexStructure (TangentSpace J (f x))) :
    ¬ ∀ v ∈ f.tangentRange x hn, Jx v ∈ f.tangentRange x hn := by
  intro hinv
  have hEH : Even (Module.finrank ℝ EH) := by
    rw [← TauCeti.finrank_tangentSpace (I := I) (x := x),
      ← LinearMap.finrank_range_of_inj (f.isImmersion.mfderiv_injective hn x)]
    exact Jx.even_finrank_of_forall_mem hinv
  have hEM : Even (Module.finrank ℝ EM) := by
    rw [← TauCeti.finrank_tangentSpace (I := J) (x := f x)]
    exact Jx.even_finrank_real
  obtain ⟨a, ha⟩ := hEH
  obtain ⟨b, hb⟩ := hEM
  omega

/-- **The normal space of a real-smooth hypersurface admits no almost complex structure.** For any
`C^n` (`n ≠ 0`) real embedding `f : H → M` of real codimension one
(`finrank ℝ EH + 1 = finrank ℝ EM`), each normal fibre `f.NormalSpace x hn` is one-dimensional over
`ℝ` and therefore carries no almost complex structure. -/
theorem isEmpty_almostComplexStructure_normalSpace {n : ℕ∞ω}
    (f : SmoothEmbedding I J n H M) (hn : n ≠ 0)
    (hcodim : Module.finrank ℝ EH + 1 = Module.finrank ℝ EM) (x : H) :
    IsEmpty (AlmostComplexStructure (f.NormalSpace x hn)) :=
  AlmostComplexStructure.isEmpty_of_odd_finrank
    (f.finrank_normalSpace_eq_one hn hcodim x ▸ odd_one)

/-- **The normal space of a real-smooth hypersurface admits no compatible `ℂ`-module structure.**
In particular, the quotient bundle `f* TM / TH` of a real-smooth hypersurface cannot be given any
complex vector-bundle structure compatible with its real vector-space fibres. -/
theorem not_exists_module_complex_isScalarTower_normalSpace {n : ℕ∞ω}
    (f : SmoothEmbedding I J n H M) (hn : n ≠ 0)
    (hcodim : Module.finrank ℝ EH + 1 = Module.finrank ℝ EM) (x : H) :
    ¬ ∃ m : Module ℂ (f.NormalSpace x hn),
      @IsScalarTower ℝ ℂ (f.NormalSpace x hn) _ m.toSMul _ := by
  rintro ⟨m, hst⟩
  let _ : Module ℂ (f.NormalSpace x hn) := m
  have _ : IsScalarTower ℝ ℂ (f.NormalSpace x hn) := hst
  exact (f.isEmpty_almostComplexStructure_normalSpace hn hcodim x).false
    (AlmostComplexStructure.ofComplexModule (f.NormalSpace x hn))

end RealAmbient

/-- **A real-smooth hypersurface in a complex manifold never has `J`-invariant tangent spaces.**
For any `C^n` (`n ≠ 0`) real embedding `f : H → M` of real codimension one
(`finrank ℝ EH + 1 = finrank ℝ EM`) into a complex manifold `M`, at every point `x : H` the tangent
image `f.tangentRange x hn` is not preserved by the ambient complex structure
`SmoothAlmostComplexStructure.ofComplexManifold EM M (f x)`; in particular `tangentMap f` cannot
cut out a complex vector subbundle of `f* TM`. -/
theorem not_forall_ofComplexManifold_mem_tangentRange {EH EM H M : Type*}
    [NormedAddCommGroup EH] [NormedSpace ℝ EH] [NormedAddCommGroup EM] [NormedSpace ℂ EM]
    [TopologicalSpace H] [ChartedSpace EH H]
    [TopologicalSpace M] [ChartedSpace EM M] [IsManifold 𝓘(ℂ, EM) ∞ M] {n : ℕ∞ω}
    (f : SmoothEmbedding 𝓘(ℝ, EH) 𝓘(ℝ, EM) n H M) (hn : n ≠ 0)
    (hcodim : Module.finrank ℝ EH + 1 = Module.finrank ℝ EM) (x : H) :
    ¬ ∀ v ∈ f.tangentRange x hn,
      SmoothAlmostComplexStructure.ofComplexManifold EM M (f x) v ∈ f.tangentRange x hn :=
  fun hinv ↦ f.not_forall_almostComplexStructure_mem_tangentRange hn hcodim x
    ((SmoothAlmostComplexStructure.ofComplexManifold EM M).almostComplexStructureAt (f x))
    fun v hv ↦ by
      rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
      exact hinv v hv

end RealHypersurfaceObstruction

end SmoothEmbedding

/-- The inclusion `x ↦ (x : ℂ)` of the real axis into the complex plane as a `C^∞` closed real
hypersurface embedding. -/
def realAxisEmbedding : SmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ ℝ ℂ :=
  SmoothEmbedding.ofIsSmoothEmbedding Complex.ofRealCLM
    (Complex.ofRealCLM.isSmoothEmbedding_of_injective Complex.ofReal_injective)

@[simp]
theorem realAxisEmbedding_apply (x : ℝ) : realAxisEmbedding x = (x : ℂ) := by
  rw [realAxisEmbedding, SmoothEmbedding.ofIsSmoothEmbedding_apply, Complex.ofRealCLM_apply]

@[simp]
theorem coe_realAxisEmbedding : ⇑realAxisEmbedding = Complex.ofReal :=
  funext realAxisEmbedding_apply

/-- The image of `realAxisEmbedding` in `ℂ` is the real axis `{z : ℂ | z.im = 0}`. -/
theorem range_realAxisEmbedding : Set.range realAxisEmbedding = {z : ℂ | z.im = 0} := by
  ext z
  simp only [Set.mem_range, realAxisEmbedding_apply, Set.mem_ofPred_eq]
  exact ⟨fun ⟨x, hx⟩ ↦ hx ▸ Complex.ofReal_im x, fun hz ↦ ⟨z.re, Complex.ext rfl hz.symm⟩⟩

/-- `realAxisEmbedding` has closed image in `ℂ`. -/
theorem isClosed_range_realAxisEmbedding : IsClosed (Set.range realAxisEmbedding) :=
  coe_realAxisEmbedding ▸ Complex.isUniformEmbedding_ofReal.isClosedEmbedding.isClosed_range

/-- At every point `x : ℝ`, the unit real tangent vector `1` lies in
`realAxisEmbedding.tangentRange`, whereas its image `Complex.I` under the complex structure of `ℂ`
does not. -/
theorem one_mem_and_I_notMem_tangentRange_realAxisEmbedding (x : ℝ) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (realAxisEmbedding x)).symm (1 : ℂ) ∈
        realAxisEmbedding.tangentRange x (by simp) ∧
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (realAxisEmbedding x)).symm Complex.I ∉
        realAxisEmbedding.tangentRange x (by simp) := by
  have hcoe : (realAxisEmbedding : ℝ → ℂ) = Complex.ofRealCLM :=
    funext fun y ↦ (realAxisEmbedding_apply y).trans (Complex.ofRealCLM_apply y).symm
  have hmf (v : TangentSpace 𝓘(ℝ, ℝ) x) :
      NormedSpace.fromTangentSpace (𝕜 := ℝ) (realAxisEmbedding x)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) realAxisEmbedding x v) =
      Complex.ofRealCLM (NormedSpace.fromTangentSpace (𝕜 := ℝ) x v) := by
    simp [hcoe, mfderiv_eq_fderiv]
  refine ⟨(realAxisEmbedding.mem_tangentRange_iff x _ _).2
    ⟨(NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm (1 : ℝ),
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (realAxisEmbedding x)).injective ?_⟩,
    fun hI ↦ ?_⟩
  · rw [hmf, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact Complex.ofReal_one
  · obtain ⟨v, hv⟩ := (realAxisEmbedding.mem_tangentRange_iff x _ _).1 hI
    have hv' := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (realAxisEmbedding x)) hv
    rw [hmf, ContinuousLinearEquiv.apply_symm_apply] at hv'
    simpa using congrArg Complex.im hv'

/-- At every point `x : ℝ`, the tangent range of `realAxisEmbedding : ℝ → ℂ` is not preserved by
the ambient complex structure of `ℂ`. -/
theorem not_forall_ofComplexManifold_mem_tangentRange_realAxisEmbedding (x : ℝ) :
    ¬ ∀ v ∈ realAxisEmbedding.tangentRange x (by simp),
      SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ (realAxisEmbedding x) v ∈
        realAxisEmbedding.tangentRange x (by simp) :=
  realAxisEmbedding.not_forall_ofComplexManifold_mem_tangentRange (by simp)
    (by rw [Module.finrank_self, Complex.finrank_real_complex]) x

/-- At every point `x : ℝ`, the normal space of `realAxisEmbedding : ℝ → ℂ` admits no compatible
`ℂ`-module structure. -/
theorem not_exists_module_complex_isScalarTower_normalSpace_realAxisEmbedding (x : ℝ) :
    ¬ ∃ m : Module ℂ (realAxisEmbedding.NormalSpace x (by simp)),
      @IsScalarTower ℝ ℂ (realAxisEmbedding.NormalSpace x (by simp)) _ m.toSMul _ :=
  realAxisEmbedding.not_exists_module_complex_isScalarTower_normalSpace (by simp)
    (by rw [Module.finrank_self, Complex.finrank_real_complex]) x

end TauCeti
