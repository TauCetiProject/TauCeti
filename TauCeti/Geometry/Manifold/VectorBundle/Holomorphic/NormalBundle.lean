/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.DefiningEquation
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.DefiningFunctions
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Level
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.AlmostComplexStructure

/-!
# Normal line bundles of complex hypersurfaces and the real-hypersurface obstruction

For an embedded complex submanifold `i : Z → M` of complex codimension one
(`Module.finrank ℂ EZ + 1 = Module.finrank ℂ EM`), the differential `mfderiv 𝓘(ℂ, EZ) 𝓘(ℂ, EM) i x`
on each fibre `x : Z` is `ℂ`-linear and injective (`Manifold.IsImmersion.mfderiv_injective`), and
`SmoothEmbedding.tangentMap_injective` (`TauCeti.Geometry.Manifold.SmoothEmbedding.Basic`) shows
that the induced total tangent map `tangentMap 𝓘(ℂ, EZ) 𝓘(ℂ, EM) i` is injective; promoting `i` via
`SmoothEmbedding.ofNeZero` (`TauCeti.Geometry.Manifold.Complex.Immersion`) and applying
`TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.TangentSubbundle` realizes
`x ↦ i.tangentRange x hn` as a holomorphic (`C^∞`, and `C^ω` after regularity promotion) vector
subbundle of `i* TM` biholomorphic to `TZ`; `SmoothEmbedding.finrank_normalSpace_eq_one`
(`TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic`) shows that the quotient
`i* TM / TZ` (`i.NormalSpace`) has complex rank one; and `DefiningFunctions.normalBundleDiffeomorph`
(`TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.DefiningFunctions`) identifies
`i.NormalSpace` biholomorphically with the transition-cocycle model `DefiningFunctions.core` built
from transverse local defining functions.

This file characterizes closedness of complex hypersurfaces by holomorphic local defining equations
(`isClosed_range_iff_forall_exists_mdifferentiableOn_eq_zero`), constructs compatible holomorphic
trivializations of `i.NormalSpace` directly from local holomorphic equations without a separate
derivative-continuity hypothesis (`normalSpaceTrivializationOfMDifferentiableOn`,
`normalSpaceTrivializationOfMDifferentiableOn_mem_maximalAtlas`), upgrades the transition cocycle
`DefiningFunctions.core` of any complex submanifold to complex-analytic (`C^ω`) regularity
(`DefiningFunctions.contMDiffOn_omega_coordChange`, `DefiningFunctions.isContMDiff_omega_core`), and
specializes the pointwise almost-complex obstructions of
`TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.AlmostComplexStructure` to complex ambient
manifolds (`not_forall_ofComplexManifold_mem_tangentRange`) and the closed real axis
`TauCeti.realAxisEmbedding` (`one_mem_and_I_notMem_tangentRange_realAxisEmbedding`,
`not_forall_ofComplexManifold_mem_tangentRange_realAxisEmbedding`,
`not_exists_module_complex_isScalarTower_normalSpace_realAxisEmbedding`).

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §§2.1–2.2.
* Phillip Griffiths and Joseph Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Ch. 0–1.
-/

public noncomputable section

open Set Function Bundle Topology Manifold
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

namespace SmoothEmbedding

section ComplexSubmanifold

variable {EZ EM P H G Z M : Type*}
  [NormedAddCommGroup EZ] [NormedSpace ℂ EZ] [FiniteDimensional ℂ EZ]
  [NormedAddCommGroup EM] [NormedSpace ℂ EM] [FiniteDimensional ℂ EM]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℂ EZ H} {J : ModelWithCorners ℂ EM G} [I.Boundaryless]
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I 1 Z]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J 1 M]
  {n : ℕ∞ω} {i : SmoothEmbedding I J n Z M}

/-- **Complex analyticity (`C^ω`) of defining-function transition maps.** On a boundaryless
finite-dimensional complex submanifold `i : Z → M` of regularity `n` with `∞ ≤ n` (i.e. `n = ∞` or
`n = ω`), the transition maps `φ.coordChange` of any defining-function atlas
`φ : i.DefiningFunctions P` are complex-analytic (`C^ω`) on base-set overlaps. -/
theorem DefiningFunctions.contMDiffOn_omega_coordChange (φ : i.DefiningFunctions P) (hn : n ≠ 0)
    (hinf : ∞ ≤ n) (hdim : Module.finrank ℂ EZ + Module.finrank ℂ P = Module.finrank ℂ EM)
    (z₀ z₁ : Z) :
    ContMDiffOn I 𝓘(ℂ, P →L[ℂ] P) ω (φ.coordChange hn hdim z₀ z₁)
      (φ.baseSet z₀ ∩ φ.baseSet z₁) :=
  ((φ.contMDiffOn_coordChange hn hdim (m := ∞) (by simpa using hinf) z₀ z₁).mdifferentiableOn
    (by simp)).contMDiffOn ((φ.isOpen_baseSet z₀).inter (φ.isOpen_baseSet z₁))

/-- **The transition-cocycle core of a complex submanifold is complex-analytic (`C^ω`).** -/
theorem DefiningFunctions.isContMDiff_omega_core (φ : i.DefiningFunctions P) (hn : n ≠ 0)
    (hinf : ∞ ≤ n) (hdim : Module.finrank ℂ EZ + Module.finrank ℂ P = Module.finrank ℂ EM) :
    (φ.core hn hdim).IsContMDiff I ω :=
  ⟨fun z₀ z₁ ↦ by
    simpa only [DefiningFunctions.core_coordChange, DefiningFunctions.core_baseSet] using
      φ.contMDiffOn_omega_coordChange hn hinf hdim z₀ z₁⟩

end ComplexSubmanifold

section ComplexHypersurface

variable {EZ EM Z M : Type*} [NormedAddCommGroup EZ] [NormedSpace ℂ EZ]
  [NormedAddCommGroup EM] [NormedSpace ℂ EM] [FiniteDimensional ℂ EM]
  [TopologicalSpace Z] [ChartedSpace EZ Z]
  [TopologicalSpace M] [ChartedSpace EM M] [IsManifold 𝓘(ℂ, EM) ∞ M]
  (i : SmoothEmbedding 𝓘(ℂ, EZ) 𝓘(ℂ, EM) ∞ Z M)

/-- **Holomorphic local defining equations for closed embedded complex hypersurfaces.** An embedded
complex submanifold `i : Z → M` of complex codimension one (`finrank ℂ EZ + 1 = finrank ℂ EM`) has
closed image in `M` if and only if every ambient point `y₀ : M` admits an open neighbourhood `S`
and a holomorphic (`MDifferentiableOn`) function `g : M → ℂ` on `S` whose zero locus in `S` is
`S ∩ Set.range i` and whose differential `mvfderiv 𝓘(ℂ, EM) g y` is nonzero along `S ∩ Set.range i`.
Unlike the smooth case over `ℝ`, no `C¹` derivative-continuity hypothesis on `g` is needed. -/
theorem isClosed_range_iff_forall_exists_mdifferentiableOn_eq_zero
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

end ComplexHypersurface

section HolomorphicLevelTrivialization

variable {EZ EM Z M : Type*} [NormedAddCommGroup EZ] [NormedSpace ℂ EZ] [FiniteDimensional ℂ EZ]
  [NormedAddCommGroup EM] [NormedSpace ℂ EM] [FiniteDimensional ℂ EM]
  [TopologicalSpace Z] [ChartedSpace EZ Z] [IsManifold 𝓘(ℂ, EZ) 1 Z]
  [TopologicalSpace M] [ChartedSpace EM M] [IsManifold 𝓘(ℂ, EM) 1 M]
  {n m : ℕ∞ω} (i : SmoothEmbedding 𝓘(ℂ, EZ) 𝓘(ℂ, EM) n Z M) (hn : n ≠ 0) (hm : m + 1 ≤ n)
  (hdim : Module.finrank ℂ ℂ = Module.finrank ℂ EM - Module.finrank ℂ EZ)
  {W : Set Z} (hW : IsOpen W) {U : Set M} (hU : IsOpen U) (hiW : MapsTo i W U)
  {g : M → ℂ} (hg : MDifferentiableOn 𝓘(ℂ, EM) 𝓘(ℂ) g U) {c : ℂ}
  (hgi : ∀ z ∈ W, g (i z) = c) (hreg : ∀ z ∈ W, mvfderiv 𝓘(ℂ, EM) g (i z) ≠ 0)

/-- **Holomorphic trivialization of the normal line bundle from a local holomorphic equation.**
Given a holomorphic (`MDifferentiableOn`) function `g : M → ℂ` on an open `U ⊆ M` containing
`i '' W` that is constant along `i '' W` with nonvanishing complex differential `mvfderiv 𝓘(ℂ, EM) g
(i z) ≠ 0` along `W`, automatic complex analyticity promotes `g` without a separate `C¹` hypothesis
and yields a `ℂ`-linear trivialization of `i.NormalSpace` over `W` in the `C^m` (`m = ∞` or `m = ω`)
maximal atlas. -/
def normalSpaceTrivializationOfMDifferentiableOn :
    Trivialization ℂ (π ℂ (fun z ↦ i.NormalSpace z hn)) :=
  haveI : IsManifold 𝓘(ℂ, EZ) (m + 1) Z := IsManifold.of_ne_zero (m + 1) one_ne_zero inferInstance
  haveI : IsManifold 𝓘(ℂ, EM) (m + 1) M := IsManifold.of_ne_zero (m + 1) one_ne_zero inferInstance
  i.normalSpaceTrivializationOfLevel hn hm hdim hW hU hiW
    ((hg.contMDiffOn hU).of_le le_top) hgi
    (fun z hz ↦ TauCeti.isRegularPoint_iff_mvfderiv_ne_zero.2 (hreg z hz))

@[simp] theorem baseSet_normalSpaceTrivializationOfMDifferentiableOn :
    (i.normalSpaceTrivializationOfMDifferentiableOn hn hm hdim hW hU hiW hg hgi hreg).baseSet =
      W := by
  have : IsManifold 𝓘(ℂ, EZ) (m + 1) Z := IsManifold.of_ne_zero (m + 1) one_ne_zero inferInstance
  have : IsManifold 𝓘(ℂ, EM) (m + 1) M := IsManifold.of_ne_zero (m + 1) one_ne_zero inferInstance
  rw [normalSpaceTrivializationOfMDifferentiableOn.eq_def]
  exact i.baseSet_normalSpaceTrivializationOfLevel hn hm hdim hW hU hiW _ hgi _

instance isLinear_normalSpaceTrivializationOfMDifferentiableOn :
    (i.normalSpaceTrivializationOfMDifferentiableOn hn hm hdim hW hU hiW hg hgi hreg).IsLinear
      ℂ := by
  have : IsManifold 𝓘(ℂ, EZ) (m + 1) Z := IsManifold.of_ne_zero (m + 1) one_ne_zero inferInstance
  have : IsManifold 𝓘(ℂ, EM) (m + 1) M := IsManifold.of_ne_zero (m + 1) one_ne_zero inferInstance
  rw [normalSpaceTrivializationOfMDifferentiableOn.eq_def]
  exact i.isLinear_normalSpaceTrivializationOfLevel hn hm hdim hW hU hiW _ hgi _

/-- `normalSpaceTrivializationOfMDifferentiableOn` belongs to the `C^m` maximal atlas of
`i.NormalSpace` (including `m = ∞`, and `m = ω` when `n = ω`). -/
theorem normalSpaceTrivializationOfMDifferentiableOn_mem_maximalAtlas :
    letI := i.normalSpaceFiberBundle hn hdim
    (i.normalSpaceTrivializationOfMDifferentiableOn hn hm hdim hW hU hiW hg hgi
      hreg).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear Z ℂ 𝓘(ℂ, EZ) m).maximalAtlas
        (TotalSpace ℂ (fun z ↦ i.NormalSpace z hn)) := by
  have : IsManifold 𝓘(ℂ, EZ) (m + 1) Z := IsManifold.of_ne_zero (m + 1) one_ne_zero inferInstance
  have : IsManifold 𝓘(ℂ, EM) (m + 1) M := IsManifold.of_ne_zero (m + 1) one_ne_zero inferInstance
  rw [normalSpaceTrivializationOfMDifferentiableOn.eq_def]
  exact i.normalSpaceTrivializationOfLevel_mem_maximalAtlas hn hm hdim hW hU hiW _ hgi _

@[simp] theorem normalSpaceTrivializationOfMDifferentiableOn_normalClass
    {z : Z} (hz : z ∈ W) (v : TangentSpace 𝓘(ℂ, EM) (i z)) :
    i.normalSpaceTrivializationOfMDifferentiableOn hn hm hdim hW hU hiW hg hgi hreg
        ⟨z, i.normalClass z hn v⟩ = (z, mfderiv 𝓘(ℂ, EM) 𝓘(ℂ) g (i z) v) := by
  have : IsManifold 𝓘(ℂ, EZ) (m + 1) Z := IsManifold.of_ne_zero (m + 1) one_ne_zero inferInstance
  have : IsManifold 𝓘(ℂ, EM) (m + 1) M := IsManifold.of_ne_zero (m + 1) one_ne_zero inferInstance
  rw [normalSpaceTrivializationOfMDifferentiableOn.eq_def]
  exact i.normalSpaceTrivializationOfLevel_normalClass hn hm hdim hW hU hiW _ hgi _ hz v

end HolomorphicLevelTrivialization

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
    fun v hv ↦ by rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]; exact hinv v hv

end SmoothEmbedding

/-- The inclusion `x ↦ (x : ℂ)` of the real axis into the complex plane as a `C^∞` closed real
hypersurface embedding. -/
def realAxisEmbedding : SmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ ℝ ℂ :=
  SmoothEmbedding.ofIsSmoothEmbedding Complex.ofRealCLM
    (Complex.ofRealCLM.isSmoothEmbedding_of_injective Complex.ofReal_injective)

@[simp] theorem realAxisEmbedding_apply (x : ℝ) : realAxisEmbedding x = (x : ℂ) := by
  rw [realAxisEmbedding, SmoothEmbedding.ofIsSmoothEmbedding_apply, Complex.ofRealCLM_apply]

@[simp] theorem coe_realAxisEmbedding : ⇑realAxisEmbedding = Complex.ofReal :=
  funext realAxisEmbedding_apply

/-- The image of `realAxisEmbedding` in `ℂ` is the real axis `{z : ℂ | z.im = 0}`. -/
theorem range_realAxisEmbedding : Set.range realAxisEmbedding = {z : ℂ | z.im = 0} := by
  ext z; simp only [Set.mem_range, realAxisEmbedding_apply, Set.mem_ofPred_eq]
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
    simp only [hcoe, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨(realAxisEmbedding.mem_tangentRange_iff x _ _).2
    ⟨(NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm (1 : ℝ),
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (realAxisEmbedding x)).injective ?_⟩, fun hI ↦ ?_⟩
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
