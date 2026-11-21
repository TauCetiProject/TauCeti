/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Complex.OperatorNorm

/-!
# Coordinates of local Sobolev maps

A map into a finite-dimensional real normed space is locally Sobolev of order `k` if and
only if all its coordinates in a finite basis are (`Module.Basis.memWkpLoc_iff`). The same
criterion holds for local `Lᵖ` membership on any topological measurable space
(`Module.Basis.memLpLoc_iff`). These criteria allow scalar local estimates to be applied to
vector-valued maps without choosing compatible representatives of their iterated weak derivatives.

The criteria include the zero-dimensional codomain, order zero, and the exponent infinity.
They also show that testing one basis is equivalent to testing every basis.
Conversely, real functions in a local Sobolev class, one for each vector of a finite basis,
are the coordinates of a single map in that class (`Module.Basis.exists_memWkpLoc_repr_eq`).

For maps on a finite-dimensional real normed space `E`, a weak derivative `D` is likewise tested
through its partial derivatives `x ↦ D x (b i)` along any finite basis `b` of `E`
(`Module.Basis.memWkpLoc_succ_of_hasWeakFDerivOn`, `Module.Basis.memWkpLoc_succ_iff_apply`), for an
arbitrary codomain `V`. On `ℂ` this specializes to the two partial derivatives `z ↦ D z 1` and
`z ↦ D z I` (`TauCeti.MemLpLoc.memWkpLoc_succ_of_hasWeakFDerivOn`,
`TauCeti.memWkpLoc_succ_iff_apply_one_apply_I`).

On an open set, the precise representative of a locally `Lᵖ` map is reconstructed from the
precise representatives of its coordinates wherever these are continuous
(`Module.Basis.eqOn_preciseRepresentative_sum_repr`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (vector-valued Sobolev spaces).
-/

public noncomputable section

open TauCeti MeasureTheory
open scoped ENNReal

namespace Module.Basis

section MemLpLoc

variable {α F : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Finite ι]
  {μ : Measure α} {p : ℝ≥0∞} {U : Set α} {f : α → F}

/-- Local `Lᵖ` membership can be tested in any finite basis of the codomain, on any topological
measurable space and with respect to any measure. No completeness assumption on the codomain is
needed beyond finite dimensionality. -/
theorem memLpLoc_iff (b : Module.Basis ι ℝ F) :
    MemLpLoc p U f μ ↔ ∀ i, MemLpLoc p U (fun z => b.repr (f z) i) μ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · intro h i
    exact h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemLpLoc p U (fun z => ∑ i, b.repr (f z) i • b i) μ :=
      MemLpLoc.sum Finset.univ fun i _ => (h i).smul_const (b i)
    simpa only [b.sum_repr] using hs

end MemLpLoc

section MemWkpLoc

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Finite ι]
  {μ : Measure E} {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F}

/-- Local Sobolev membership of every order can be tested in any finite basis of the codomain.
Scalar coordinate witnesses may be chosen independently; finite sums reconstruct the map
in the same Sobolev class. -/
theorem memWkpLoc_iff (b : Module.Basis ι ℝ F) :
    MemWkpLoc p U k f μ ↔ ∀ i, MemWkpLoc p U k (fun z => b.repr (f z) i) μ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · intro h i
    exact h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemWkpLoc p U k (fun z => ∑ i, b.repr (f z) i • b i) μ := by
      apply MemWkpLoc.sum
      intro i _
      exact (h i).smul_const (b i)
    simpa only [b.sum_repr] using hs

/-- Real functions `v i` in `MemWkpLoc p U k`, one for each vector of a finite basis `b` of `F`,
are the coordinates in `b` of a single function `E → F` in `MemWkpLoc p U k`. -/
theorem exists_memWkpLoc_repr_eq (b : Module.Basis ι ℝ F) {v : ι → E → ℝ}
    (hv : ∀ i, MemWkpLoc p U k (v i) μ) :
    ∃ V : E → F, MemWkpLoc p U k V μ ∧ ∀ i, (fun z => b.repr (V z) i) = v i := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hrepr : ∀ i, (fun z => b.repr (b.equivFun.symm fun j => v j z) i) = v i := fun i =>
    funext fun z => by rw [← b.equivFun_apply, b.equivFun.apply_symm_apply]
  exact ⟨_, b.memWkpLoc_iff.2 fun i => (hrepr i).symm ▸ hv i, hrepr⟩

open TopologicalSpace in
/-- **Assembling a weak derivative from its partial derivatives along a basis.** A locally `Lᵖ`
map on `U ⊆ E` with a weak derivative `D` on `interior U` whose partial derivatives
`x ↦ D x (b i)` along a finite basis `b` of `E` lie in `W^{k,p}_loc(U)` lies in
`W^{k+1,p}_loc(U)`. -/
theorem memWkpLoc_succ_of_hasWeakFDerivOn (b : Module.Basis ι ℝ E) {D : E → E →L[ℝ] F}
    (hf : MemLpLoc p U f μ) (hD : HasWeakFDerivOn μ (Opens.interior U) f D)
    (hb : ∀ i, MemWkpLoc p U k (fun x => D x (b i)) μ) :
    MemWkpLoc p U (k + 1) f μ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  have : CompleteSpace F := hD.completeSpace
  refine memWkpLoc_succ_iff.2 ⟨hf, D, hD, ?_⟩
  have hDeq : D = fun x => ∑ i,
      StrongDual.smulRightL ℝ E F (LinearMap.toContinuousLinearMap (b.coord i))
        (D x (b i)) := by
    funext x
    ext v
    calc D x v = D x (∑ i, b.repr v i • b i) := by rw [b.sum_repr]
      _ = _ := by rw [map_sum]; simp
  rw [hDeq]
  exact MemWkpLoc.sum Finset.univ fun i _ =>
    (hb i).clm_comp (StrongDual.smulRightL ℝ E F _)

open TopologicalSpace in
/-- **Local Sobolev classes through partial derivatives along a basis.** A map lies in
`W^{k+1,p}_loc(U)` exactly when it is locally `Lᵖ` on `U` and has a weak derivative on `interior U`
whose partial derivatives along a finite basis `b` of `E` lie in `W^{k,p}_loc(U)`. -/
theorem memWkpLoc_succ_iff_apply (b : Module.Basis ι ℝ E) :
    MemWkpLoc p U (k + 1) f μ ↔ MemLpLoc p U f μ ∧ ∃ D : E → E →L[ℝ] F,
      HasWeakFDerivOn μ (Opens.interior U) f D ∧
        ∀ i, MemWkpLoc p U k (fun x => D x (b i)) μ := by
  refine ⟨fun h => ?_, fun ⟨hf, D, hD, hb⟩ => b.memWkpLoc_succ_of_hasWeakFDerivOn hf hD hb⟩
  obtain ⟨hf, D, hD, hDk⟩ := memWkpLoc_succ_iff.1 h
  have : CompleteSpace F := hD.completeSpace
  exact ⟨hf, D, hD, fun i => hDk.clm_comp (ContinuousLinearMap.apply ℝ F (b i))⟩

end MemWkpLoc

section PreciseRepresentative

open TopologicalSpace TauCeti.MeasureTheory

variable {α F : Type*} [PseudoMetricSpace α] [LocallyCompactSpace α] [SecondCountableTopology α]
  [MeasurableSpace α] [BorelSpace α] {μ : Measure α} [IsUnifLocDoublingMeasure μ]
  [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] {p : ℝ≥0∞} {Ω : Opens α} {f : α → F}

/-- On an open set `Ω`, the precise representative of a locally `Lᵖ` map, `1 ≤ p`, whose
coordinates in a finite basis `b` have precise representatives continuous on `Ω`, is the
combination of those precise representatives with the vectors of `b`. -/
theorem eqOn_preciseRepresentative_sum_repr (b : Module.Basis ι ℝ F) (hp : 1 ≤ p)
    (hf : MemLpLoc p Ω f μ)
    (hc : ∀ i, ContinuousOn (preciseRepresentative μ fun z => b.repr (f z) i) Ω) :
    Set.EqOn (preciseRepresentative μ f)
      (fun z => ∑ i, preciseRepresentative μ (fun w => b.repr (f w) i) z • b i) Ω := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  refine eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
    (hf.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed) ?_
    (continuousOn_finsetSum _ fun i _ => (hc i).smul continuousOn_const)
  have hcoord : ∀ i, (fun z => b.repr (f z) i) =ᵐ[μ.restrict Ω]
      preciseRepresentative μ fun z => b.repr (f z) i := fun i =>
    (b.memLpLoc_iff.1 hf i).ae_eq_preciseRepresentative hp
  filter_upwards [ae_all_iff.2 hcoord] with z hz
  conv_lhs => rw [← b.sum_repr (f z)]
  exact Finset.sum_congr rfl fun i _ => by rw [← hz i]

end PreciseRepresentative

end Module.Basis

/-! ### Local Sobolev classes through the two partial derivatives on `ℂ` -/

namespace TauCeti

open Complex TopologicalSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : Measure ℂ} {q : ℝ≥0∞}
  {U : Set ℂ} {k : ℕ}

/-- **Assembling a weak derivative from its partial derivatives.** A locally `L^q` map with a
weak derivative `D` on the interior of `U` whose partial derivatives `z ↦ D z 1` and `z ↦ D z I`
lie in `W^{k,q}_loc(U)` lies in `W^{k+1,q}_loc(U)`. The derivative `D` is rebuilt from its two
partial derivatives with `ContinuousLinearMap.smulRightL`. -/
theorem MemLpLoc.memWkpLoc_succ_of_hasWeakFDerivOn {ξ : ℂ → V} {D : ℂ → ℂ →L[ℝ] V}
    (hξ : MemLpLoc q U ξ μ) (hD : HasWeakFDerivOn μ (Opens.interior U) ξ D)
    (h1 : MemWkpLoc q U k (fun z => D z 1) μ) (hI : MemWkpLoc q U k (fun z => D z I) μ) :
    MemWkpLoc q U (k + 1) ξ μ := by
  have := hD.completeSpace
  refine memWkpLoc_succ_iff.2 ⟨hξ, D, hD, ?_⟩
  rw [ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM D]
  exact (h1.clm_comp _).add (hI.clm_comp _)

/-- **Local Sobolev classes through partial derivatives.** A map lies in `W^{k+1,q}_loc(U)`
exactly when it is locally `L^q` on `U` and has a weak derivative on the interior of `U` whose
partial derivatives `z ↦ D z 1` and `z ↦ D z I` lie in `W^{k,q}_loc(U)`. -/
theorem memWkpLoc_succ_iff_apply_one_apply_I {ξ : ℂ → V} :
    MemWkpLoc q U (k + 1) ξ μ ↔ MemLpLoc q U ξ μ ∧ ∃ D : ℂ → ℂ →L[ℝ] V,
      HasWeakFDerivOn μ (Opens.interior U) ξ D ∧
        (MemWkpLoc q U k (fun z => D z 1) μ) ∧ MemWkpLoc q U k (fun z => D z I) μ := by
  refine ⟨fun h => ?_, fun ⟨hξ, D, hD, h1, hI⟩ =>
    hξ.memWkpLoc_succ_of_hasWeakFDerivOn hD h1 hI⟩
  obtain ⟨hξ, D, hD, hDk⟩ := memWkpLoc_succ_iff.1 h
  have := hD.completeSpace
  exact ⟨hξ, D, hD, hDk.clm_comp (ContinuousLinearMap.apply ℝ V 1),
    hDk.clm_comp (ContinuousLinearMap.apply ℝ V I)⟩

end TauCeti
