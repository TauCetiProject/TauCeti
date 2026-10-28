/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Analysis.Normed.Lp.PiLp
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# Fredholm operators on finite products

A coordinatewise operator on a finite product is Fredholm exactly when each block
is Fredholm. Quasi-inverses assemble coordinatewise; conversely, compressing a
quasi-inverse to a diagonal block recovers a quasi-inverse for that block. Transport to
`PiLp` gives the finite Hilbert direct-sum theorem at exponent two. The index is the
sum of the block indices, using the algebraic kernel and cokernel dimension formulas.

This is the finite direct-sum argument for Fredholm operators, as in Conway,
*A Course in Functional Analysis*, Chapter XI.
-/

public section

namespace ContinuousLinearMap

open LinearMap.FiniteRangeSetoid

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Finite ι]
  {E F : ι → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, Module 𝕜 (E i)]
  [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)] [∀ i, T2Space (E i)]
  [∀ i, AddCommGroup (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, Module 𝕜 (F i)]
  [∀ i, IsTopologicalAddGroup (F i)] [∀ i, ContinuousSMul 𝕜 (F i)] [∀ i, T2Space (F i)]

/-- A finite product of Fredholm operators is Fredholm. -/
theorem IsFredholm.piMap {f : ∀ i, E i →L[𝕜] F i} (h : ∀ i, (f i).IsFredholm) :
    (ContinuousLinearMap.piMap f).IsFredholm := by
  choose g hg using fun i ↦ (h i).exists_isQuasiInverse
  exact .of_isQuasiInverse (v := ContinuousLinearMap.piMap g)
    (LinearMap.IsQuasiInverse.piMap hg)

omit [Finite ι] in
/-- Every diagonal block of a Fredholm coordinatewise operator is Fredholm. -/
theorem IsFredholm.of_piMap {f : ∀ i, E i →L[𝕜] F i}
    (h : (ContinuousLinearMap.piMap f).IsFredholm) (i : ι) : (f i).IsFredholm := by
  classical
  obtain ⟨g, hg⟩ := h.exists_isQuasiInverse
  refine .of_isQuasiInverse (v := proj i ∘L g ∘L single 𝕜 F i) ⟨?_, ?_⟩
  · rw [LinearMap.IsLeftQuasiInverse, equiv_iff_hasNoetherianRange]
    have hi := (equiv_iff_hasNoetherianRange.mp hg.1).comp_right
      (LinearMap.single 𝕜 E i) |>.comp_left (LinearMap.proj i)
    convert hi using 1
    ext x
    simpa only [toLinearMap_comp, coe_proj, LinearMap.sub_apply, LinearMap.coe_comp,
      LinearMap.coe_proj, coe_coe, single_apply, Function.comp_apply, Function.eval,
      LinearMap.id_coe, id_eq, coe_piMap, LinearMap.coe_single, LinearMap.coe_piMap,
      Pi.sub_apply, Pi.single_eq_same, sub_left_inj] using
      congrArg (fun y ↦ g y i)
        (LinearMap.piMap_single (fun i ↦ (f i).toLinearMap) i x).symm
  · rw [LinearMap.IsRightQuasiInverse, equiv_iff_hasNoetherianRange]
    have hi := (equiv_iff_hasNoetherianRange.mp hg.2).comp_right
      (LinearMap.single 𝕜 F i) |>.comp_left (LinearMap.proj i)
    convert hi using 1
    ext x
    simp

/-- A coordinatewise operator on a finite product is Fredholm iff every block is. -/
@[simp]
theorem isFredholm_piMap_iff (f : ∀ i, E i →L[𝕜] F i) :
    (piMap f).IsFredholm ↔ ∀ i, (f i).IsFredholm :=
  ⟨fun h i ↦ h.of_piMap i, IsFredholm.piMap⟩

end ContinuousLinearMap

open scoped ENNReal

namespace PiLp

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜]
  {p : ℝ≥0∞} {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]

/-- A block-diagonal operator on a finite `Lᵖ` product is Fredholm exactly when each block is.
In particular, `p = 2` gives the finite Hilbert direct sum. -/
@[simp]
theorem isFredholm_mapCLM_iff [CompleteSpace 𝕜] [Finite ι] (f : ∀ i, E i →L[𝕜] F i) :
    (mapCLM (p := p) f).IsFredholm ↔ ∀ i, (f i).IsFredholm := by
  constructor
  · intro h
    apply (ContinuousLinearMap.isFredholm_piMap_iff f).mp
    convert (h.equiv_comp (continuousLinearEquiv p 𝕜 F)).comp_equiv
      (continuousLinearEquiv p 𝕜 E).symm using 1
    ext x i
    simp
  · intro h
    rw [mapCLM_def]
    exact ((ContinuousLinearMap.IsFredholm.piMap h).comp_equiv
      (continuousLinearEquiv p 𝕜 E)).equiv_comp (continuousLinearEquiv p 𝕜 F).symm

/-- The index of a finite block-diagonal `Lᵖ` operator is the sum of the block indices. -/
@[simp]
theorem index_mapCLM [Fintype ι] (f : ∀ i, E i →L[𝕜] F i)
    [∀ i, FiniteDimensional 𝕜 (f i).ker]
    [∀ i, FiniteDimensional 𝕜 (F i ⧸ (f i).range)] :
    (mapCLM (p := p) f).index = ∑ i, (f i).index := by
  simp [mapCLM_def]

end PiLp
