/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.TangentSubbundle
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Transverse
public import TauCeti.Geometry.Symplectic.Finrank
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Normal line bundles of complex hypersurfaces and the real-hypersurface obstruction

For an embedded complex submanifold `i : Z → M` of complex codimension one
(`Module.finrank ℂ EZ + 1 = Module.finrank ℂ EM`), `TangentSubbundle` and `Transverse` make
`tangentMap 𝓘(ℂ, EZ) 𝓘(ℂ, EM) i` complex-linear and injective, realize `i.pullbackTangentRange` as
a holomorphic (`C^∞`, indeed `C^ω`) vector subbundle of `i* TM` biholomorphic to `TZ`, and identify
the rank-one quotient `i* TM / TZ` (`i.NormalSpace`) with the scalar transition-cocycle model built
from transverse complex charts. This file proves automatic `C^n` (`∞`, `ω`) upgrades for
holomorphic embeddings (`MDifferentiable.isImmersion_of_injective_mfderiv`,
`SmoothEmbedding.ofMDifferentiable`), characterizes closedness by holomorphic local defining
equations (`isClosed_range_iff_forall_exists_mdifferentiableOn_eq_zero`), establishes `C^ω`
regularity of the scalar cocycle (`contMDiffOn_omega_transverseNormalCore_coordChange_one`), and
proves that no real-codimension-one smooth hypersurface (such as `TauCeti.realAxisEmbedding`) has
`J`-invariant tangent spaces or a compatible `ℂ`-module structure on its normal fibres.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §§2.1–2.2.
* Phillip Griffiths and Joseph Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Ch. 0–1.
-/

public noncomputable section

open Set Function Bundle Topology Manifold
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

section HolomorphicUpgrade

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  [TopologicalSpace G] {J : ModelWithCorners ℂ F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]

/-- A holomorphic (`MDifferentiable`) map between `C¹` complex manifolds with injective complex
differential everywhere is a `C^n` immersion for every `n : ℕ∞ω`, including `n = ∞` and `n = ω`. -/
theorem _root_.MDifferentiable.isImmersion_of_injective_mfderiv
    [IsManifold I 1 M] [IsManifold J 1 N] {f : M → N}
    (hf : MDifferentiable I J f) (hdf : ∀ x, Injective (mfderiv I J f x)) (n : ℕ∞ω) :
    IsImmersion I J n f := by
  have : IsManifold I (max n 1) M := IsManifold.of_ne_zero (max n 1) one_ne_zero inferInstance
  have : IsManifold J (max n 1) N := IsManifold.of_ne_zero (max n 1) one_ne_zero inferInstance
  have : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  exact ((hf.contMDiff (n := max n 1)).isImmersion_of_injective_mfderiv (le_max_right n 1)
    hdf).of_le (le_max_left n 1)

/-- A holomorphic topological embedding between `C¹` complex manifolds with injective complex
differential everywhere is a `C^n` smooth embedding for every `n : ℕ∞ω` (`∞` and `ω` included). -/
theorem _root_.MDifferentiable.isSmoothEmbedding_of_isEmbedding_of_injective_mfderiv
    [IsManifold I 1 M] [IsManifold J 1 N] {f : M → N}
    (hf : MDifferentiable I J f) (hemb : IsEmbedding f)
    (hdf : ∀ x, Injective (mfderiv I J f x)) (n : ℕ∞ω) :
    IsSmoothEmbedding I J n f :=
  ⟨hf.isImmersion_of_injective_mfderiv hdf n, hemb⟩

namespace SmoothEmbedding

/-- Bundle a holomorphic (`MDifferentiable`) topological embedding with injective complex
differential into a `SmoothEmbedding I J n M N` of arbitrary smoothness order `n : ℕ∞ω` (in
particular `n = ∞` or `n = ω`). -/
def ofMDifferentiable [IsManifold I 1 M] [IsManifold J 1 N] (f : M → N)
    (hf : MDifferentiable I J f) (hemb : IsEmbedding f)
    (hdf : ∀ x, Injective (mfderiv I J f x)) (n : ℕ∞ω) :
    SmoothEmbedding I J n M N :=
  haveI : IsManifold I n M := IsManifold.of_ne_zero n one_ne_zero inferInstance
  haveI : IsManifold J n N := IsManifold.of_ne_zero n one_ne_zero inferInstance
  haveI : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  ofIsSmoothEmbedding f (hf.isSmoothEmbedding_of_isEmbedding_of_injective_mfderiv hemb hdf n)

@[simp]
theorem coe_ofMDifferentiable [IsManifold I 1 M] [IsManifold J 1 N] (f : M → N)
    (hf : MDifferentiable I J f) (hemb : IsEmbedding f)
    (hdf : ∀ x, Injective (mfderiv I J f x)) (n : ℕ∞ω) :
    ⇑(ofMDifferentiable (I := I) (J := J) f hf hemb hdf n) = f := by
  rw [ofMDifferentiable.eq_def, coe_ofIsSmoothEmbedding]

/-- Bundle a holomorphic closed topological embedding with injective complex differential into a
`SmoothEmbedding I J n M N` with closed range. -/
def ofMDifferentiableOfIsClosedEmbedding [IsManifold I 1 M] [IsManifold J 1 N] (f : M → N)
    (hf : MDifferentiable I J f) (hemb : IsClosedEmbedding f)
    (hdf : ∀ x, Injective (mfderiv I J f x)) (n : ℕ∞ω) :
    SmoothEmbedding I J n M N :=
  ofMDifferentiable f hf hemb.isEmbedding hdf n

@[simp]
theorem coe_ofMDifferentiableOfIsClosedEmbedding [IsManifold I 1 M] [IsManifold J 1 N]
    (f : M → N) (hf : MDifferentiable I J f) (hemb : IsClosedEmbedding f)
    (hdf : ∀ x, Injective (mfderiv I J f x)) (n : ℕ∞ω) :
    ⇑(ofMDifferentiableOfIsClosedEmbedding (I := I) (J := J) f hf hemb hdf n) = f :=
  coe_ofMDifferentiable f hf hemb.isEmbedding hdf n

/-- Any `C^m₀` (`m₀ ≠ 0`) complex embedding promotes to a `C^n` complex embedding for every
`n : ℕ∞ω`, including complex-analytic order `n = ω`. -/
def ofComplexNeZero {m₀ : ℕ∞ω} [IsManifold I m₀ M] [IsManifold J m₀ N]
    (f : SmoothEmbedding I J m₀ M N) (hm₀ : m₀ ≠ 0) (n : ℕ∞ω) :
    SmoothEmbedding I J n M N :=
  haveI : IsManifold I 1 M := IsManifold.of_ne_zero 1 hm₀ inferInstance
  haveI : IsManifold J 1 N := IsManifold.of_ne_zero 1 hm₀ inferInstance
  ofMDifferentiable f (f.contMDiff.mdifferentiable hm₀) f.isEmbedding
    (f.isImmersion.mfderiv_injective hm₀) n

@[simp]
theorem coe_ofComplexNeZero {m₀ : ℕ∞ω} [IsManifold I m₀ M] [IsManifold J m₀ N]
    (f : SmoothEmbedding I J m₀ M N) (hm₀ : m₀ ≠ 0) (n : ℕ∞ω) :
    ⇑(f.ofComplexNeZero hm₀ n) = f := by
  have : IsManifold I 1 M := IsManifold.of_ne_zero 1 hm₀ inferInstance
  have : IsManifold J 1 N := IsManifold.of_ne_zero 1 hm₀ inferInstance
  rw [ofComplexNeZero.eq_def, coe_ofMDifferentiable]

end SmoothEmbedding

end HolomorphicUpgrade

namespace SmoothEmbedding

section ComplexHypersurface

variable {EZ EM Z M : Type*}
  [NormedAddCommGroup EZ] [NormedSpace ℂ EZ] [FiniteDimensional ℂ EZ]
  [NormedAddCommGroup EM] [NormedSpace ℂ EM] [FiniteDimensional ℂ EM]
  [TopologicalSpace Z] [ChartedSpace EZ Z] [IsManifold 𝓘(ℂ, EZ) ∞ Z]
  [TopologicalSpace M] [ChartedSpace EM M] [IsManifold 𝓘(ℂ, EM) ∞ M]

omit [IsManifold 𝓘(ℂ, EZ) ∞ Z] in
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
  have : IsManifold 𝓘(ℂ, EM) 1 M := IsManifold.of_ne_zero 1 (by simp : (∞ : ℕ∞ω) ≠ 0) inferInstance
  rw [i.isClosed_range_iff_forall_exists_transverse_zero (by simp)
    (finrank_self_eq_sub_of_codim_one hcodim)]
  exact forall_congr' fun _ ↦ exists_congr fun S ↦ and_congr_right fun hS ↦
    and_congr_right fun _ ↦ exists_congr fun _ ↦ and_congr
      (TauCeti.contMDiffOn_iff_mdifferentiableOn (by simp : (∞ : ℕ∞ω) ≠ 0) hS)
      (and_congr_right fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
        TauCeti.isRegularPoint_iff_mvfderiv_ne_zero)

/-- **Holomorphicity (`MDifferentiableOn`) and complex analyticity (`C^ω`) of the scalar transition
cocycle of a complex hypersurface.** On every overlap of transverse complex charts of `i`, the
scalar transition function `z ↦ coordChange z₀ z₁ z 1` is complex-analytic (`C^ω`), hence
holomorphic (`MDifferentiableOn`). -/
theorem contMDiffOn_omega_transverseNormalCore_coordChange_one
    (i : SmoothEmbedding 𝓘(ℂ, EZ) 𝓘(ℂ, EM) ∞ Z M)
    (hcodim : Module.finrank ℂ EZ + 1 = Module.finrank ℂ EM) (z₀ z₁ : Z) :
    haveI : IsManifold 𝓘(ℂ, EZ) (∞ + 1) Z :=
      IsManifold.of_ne_zero (∞ + 1) (by simp : (∞ : ℕ∞ω) ≠ 0) ‹IsManifold 𝓘(ℂ, EZ) ∞ Z›
    let hdim := finrank_self_eq_sub_of_codim_one hcodim
    ContMDiffOn 𝓘(ℂ, EZ) 𝓘(ℂ) ω
      (fun z ↦ (i.transverseNormalCore (m := ∞) (by simp) (by simp) hdim).coordChange z₀ z₁ z 1)
      (i ⁻¹' i.transverseAmbSet (m := ∞) (by simp) hdim z₀ ∩
        i ⁻¹' i.transverseAmbSet (m := ∞) (by simp) hdim z₁) := by
  have : IsManifold 𝓘(ℂ, EZ) (∞ + 1) Z :=
    IsManifold.of_ne_zero (∞ + 1) (by simp : (∞ : ℕ∞ω) ≠ 0) ‹IsManifold 𝓘(ℂ, EZ) ∞ Z›
  have : IsManifold 𝓘(ℂ, EZ) 1 Z :=
    IsManifold.of_ne_zero 1 (by simp : (∞ : ℕ∞ω) ≠ 0) ‹IsManifold 𝓘(ℂ, EZ) ∞ Z›
  intro hdim
  exact ((i.contMDiffOn_transverseNormalCore_coordChange_one (m := ∞) (by simp) (by simp) hdim
    z₀ z₁).mdifferentiableOn (by simp)).contMDiffOn
    (((i.isOpen_transverseAmbSet (by simp) hdim z₀).preimage (map_continuous i)).inter
      ((i.isOpen_transverseAmbSet (by simp) hdim z₁).preimage (map_continuous i)))

end ComplexHypersurface

section RealHypersurfaceObstruction

variable {EH EM H M : Type*}
  [NormedAddCommGroup EH] [NormedSpace ℝ EH]
  [NormedAddCommGroup EM] [NormedSpace ℂ EM]
  [TopologicalSpace H] [ChartedSpace EH H]
  [TopologicalSpace M] [ChartedSpace EM M]

/-- **A real-smooth hypersurface in a complex manifold never has `J`-invariant tangent spaces.**
For any `C^n` (`n ≠ 0`) real embedding `f : H → M` of real codimension one
(`finrank ℝ EH + 1 = finrank ℝ EM`) into a complex manifold `M`, at every point `x : H` the tangent
image `f.tangentRange x hn` is not preserved by the ambient complex structure
`SmoothAlmostComplexStructure.ofComplexManifold EM M (f x)`; in particular `tangentMap f` cannot
cut out a complex vector subbundle of `f* TM`. -/
theorem not_forall_ofComplexManifold_mem_tangentRange [IsManifold 𝓘(ℂ, EM) ∞ M] {n : ℕ∞ω}
    (f : SmoothEmbedding 𝓘(ℝ, EH) 𝓘(ℝ, EM) n H M) (hn : n ≠ 0)
    (hcodim : Module.finrank ℝ EH + 1 = Module.finrank ℝ EM) (x : H) :
    ¬ ∀ v ∈ f.tangentRange x hn,
      SmoothAlmostComplexStructure.ofComplexManifold EM M (f x) v ∈ f.tangentRange x hn := by
  intro hinv
  let Jx := (SmoothAlmostComplexStructure.ofComplexManifold EM M).almostComplexStructureAt (f x)
  obtain ⟨a, ha⟩ : Even (Module.finrank ℝ EH) :=
    LinearMap.finrank_range_of_inj (f.isImmersion.mfderiv_injective hn x) ▸
      Jx.even_finrank_of_forall_mem fun v hv ↦ by
        rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]; exact hinv v hv
  obtain ⟨b, hb⟩ : Even (Module.finrank ℝ EM) := Jx.even_finrank_real
  omega

/-- **The normal space of a real-smooth hypersurface admits no almost complex structure.** For any
`C^n` (`n ≠ 0`) real embedding `f : H → M` of real codimension one
(`finrank ℝ EH + 1 = finrank ℝ EM`), each normal fibre `f.NormalSpace x hn` is one-dimensional over
`ℝ` and therefore carries no almost complex structure. -/
theorem isEmpty_almostComplexStructure_normalSpace [FiniteDimensional ℂ EM] {n : ℕ∞ω}
    (f : SmoothEmbedding 𝓘(ℝ, EH) 𝓘(ℝ, EM) n H M) (hn : n ≠ 0)
    (hcodim : Module.finrank ℝ EH + 1 = Module.finrank ℝ EM) (x : H) :
    IsEmpty (AlmostComplexStructure (f.NormalSpace x hn)) :=
  AlmostComplexStructure.isEmpty_of_odd_finrank
    (f.finrank_normalSpace_of_codim_one hn hcodim x ▸ odd_one)

/-- **The normal space of a real-smooth hypersurface admits no compatible `ℂ`-module structure.**
In particular, the quotient bundle `f* TM / TH` of a real-smooth hypersurface cannot be given any
complex vector-bundle structure compatible with its real vector-space fibres. -/
theorem not_exists_complex_module_normalSpace [FiniteDimensional ℂ EM] {n : ℕ∞ω}
    (f : SmoothEmbedding 𝓘(ℝ, EH) 𝓘(ℝ, EM) n H M) (hn : n ≠ 0)
    (hcodim : Module.finrank ℝ EH + 1 = Module.finrank ℝ EM) (x : H) :
    ¬ ∃ m : Module ℂ (f.NormalSpace x hn),
      @IsScalarTower ℝ ℂ (f.NormalSpace x hn) _ m.toSMul _ := by
  rintro ⟨m, hst⟩
  let _ : Module ℂ (f.NormalSpace x hn) := m
  have _ : IsScalarTower ℝ ℂ (f.NormalSpace x hn) := hst
  exact (f.isEmpty_almostComplexStructure_normalSpace hn hcodim x).false
    { toLinearMap := DistribSMul.toLinearMap ℝ (f.NormalSpace x hn) Complex.I
      square_neg := Complex.toLinearMap_I_comp_toLinearMap_I }

end RealHypersurfaceObstruction

end SmoothEmbedding

/-- The inclusion `x ↦ (x : ℂ)` of the real axis into the complex plane as a `C^∞` closed real
hypersurface embedding. -/
def realAxisEmbedding : SmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ ℝ ℂ :=
  SmoothEmbedding.ofIsSmoothEmbedding Complex.ofRealCLM
    (Complex.ofRealCLM.isSmoothEmbedding_of_injective Complex.ofReal_injective)

@[simp]
theorem realAxisEmbedding_apply (x : ℝ) : realAxisEmbedding x = (x : ℂ) := by
  rw [realAxisEmbedding.eq_def, SmoothEmbedding.ofIsSmoothEmbedding_apply]; rfl

/-- `realAxisEmbedding` has closed image `{z : ℂ | z.im = 0}` in `ℂ`. -/
theorem isClosed_range_realAxisEmbedding : IsClosed (Set.range realAxisEmbedding) := by
  suffices Set.range realAxisEmbedding = {z : ℂ | z.im = 0} by
    exact this ▸ isClosed_eq Complex.continuous_im continuous_const
  ext z
  simp only [Set.mem_range, realAxisEmbedding_apply, Set.mem_ofPred_eq]
  exact ⟨fun ⟨x, hx⟩ ↦ hx ▸ Complex.ofReal_im x, fun hz ↦ ⟨z.re, Complex.ext rfl hz.symm⟩⟩

/-- `realAxisEmbedding` has real codimension one in `ℂ`. -/
theorem finrank_real_codim_realAxisEmbedding :
    Module.finrank ℝ ℝ + 1 = Module.finrank ℝ ℂ := by
  rw [Module.finrank_self, Complex.finrank_real_complex]

/-- At every point `x : ℝ`, the unit real tangent vector `1` lies in
`realAxisEmbedding.tangentRange`, whereas its image `Complex.I` under the complex structure of `ℂ`
does not. -/
theorem one_mem_and_I_notMem_tangentRange_realAxisEmbedding (x : ℝ) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (realAxisEmbedding x)).symm (1 : ℂ) ∈
        realAxisEmbedding.tangentRange x (by simp) ∧
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (realAxisEmbedding x)).symm Complex.I ∉
        realAxisEmbedding.tangentRange x (by simp) := by
  have hcoe : (realAxisEmbedding : ℝ → ℂ) = Complex.ofRealCLM := funext realAxisEmbedding_apply
  have hmf (v : TangentSpace 𝓘(ℝ, ℝ) x) :
      NormedSpace.fromTangentSpace (𝕜 := ℝ) (realAxisEmbedding x)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) realAxisEmbedding x v) =
      Complex.ofRealCLM (NormedSpace.fromTangentSpace (𝕜 := ℝ) x v) := by
    rw [hcoe, mfderiv_eq_fderiv, Complex.ofRealCLM.fderiv]; rfl
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

/-- The closed real-smooth hypersurface `realAxisEmbedding : ℝ → ℂ` neither has `J`-invariant
tangent spaces nor admits any compatible `ℂ`-module structure on its normal fibres. -/
theorem realAxisEmbedding_obstruction (x : ℝ) :
    (¬ ∀ v ∈ realAxisEmbedding.tangentRange x (by simp),
      SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ (realAxisEmbedding x) v ∈
        realAxisEmbedding.tangentRange x (by simp)) ∧
      ¬ ∃ m : Module ℂ (realAxisEmbedding.NormalSpace x (by simp)),
        @IsScalarTower ℝ ℂ (realAxisEmbedding.NormalSpace x (by simp)) _ m.toSMul _ :=
  ⟨realAxisEmbedding.not_forall_ofComplexManifold_mem_tangentRange (by simp)
    finrank_real_codim_realAxisEmbedding x,
    realAxisEmbedding.not_exists_complex_module_normalSpace (by simp)
      finrank_real_codim_realAxisEmbedding x⟩

end TauCeti
