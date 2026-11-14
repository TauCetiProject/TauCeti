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
# Coordinates of local Lebesgue and Sobolev maps

A map into a finite-dimensional real normed space is locally `Lᵖ` or locally Sobolev if and only if
all its coordinates in a finite basis are (`Module.Basis.memLpLoc_iff`,
`Module.Basis.memW1pLoc_iff`, `Module.Basis.memWkpLoc_iff`). These criteria allow scalar local
estimates to be applied to vector-valued maps into finite-dimensional codomains without choosing
compatible representatives of their weak derivatives, and include the zero-dimensional codomain and
the exponent infinity.

On the domain side, a candidate weak derivative `Du` of a map into an arbitrary Banach space `F`
lies in `MemLpLoc p Ω` if and only if its directional evaluations `x ↦ Du x (b i)` along a finite
basis `b` of `E` lie in `MemLpLoc p Ω` (`Module.Basis.memW1pLoc_iff_apply`). On `ℂ` with the basis
`{1, I}`, `TauCeti.memWkpLoc_succ_iff_apply_one_apply_I` extends this to higher-order `MemWkpLoc`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (vector-valued Sobolev spaces).
-/

public noncomputable section

open TauCeti MeasureTheory TopologicalSpace

namespace Module.Basis

/-- Local `Lᵖ` membership into a finite-dimensional codomain can be tested in any finite basis.
No completeness of the codomain or metric structure on the domain is needed. -/
theorem memLpLoc_iff {E F ι : Type*} [TopologicalSpace E] [MeasureSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι] (b : Module.Basis ι ℝ F)
    {p : ENNReal} {U : Set E} {f : E → F} :
    MemLpLoc p U f ↔ ∀ i, MemLpLoc p U (fun x => b.repr (f x) i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · intro h i
    exact h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemLpLoc p U (fun x => ∑ i, b.repr (f x) i • b i) :=
      MemLpLoc.sum Finset.univ fun i _ =>
        (h i).clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (b i))
    simpa only [b.sum_repr] using hs

/-- First-order local Sobolev membership into a finite-dimensional codomain can be tested in any
finite basis. Scalar coordinate weak derivatives may be chosen independently; finite sums
reconstruct the map in `MemW1pLoc p Ω`. -/
theorem memW1pLoc_iff {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Finite ι] (b : Module.Basis ι ℝ F) {p : ENNReal} {Ω : Opens E} {u : E → F} :
    MemW1pLoc p Ω u ↔ ∀ i, MemW1pLoc p Ω (fun x => b.repr (u x) i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · intro h i
    exact h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemW1pLoc p Ω (fun x => ∑ i, b.repr (u x) i • b i) :=
      MemW1pLoc.sum Finset.univ fun i _ =>
        (h i).clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (b i))
    simpa only [b.sum_repr] using hs

/-- First-order local Sobolev membership for an arbitrary codomain `F` can be tested by evaluating
a weak Fréchet derivative along the vectors of a finite basis of the domain `E`. -/
theorem memW1pLoc_iff_apply {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι]
    (b : Module.Basis ι ℝ E) {p : ENNReal} {Ω : Opens E} {u : E → F} :
    MemW1pLoc p Ω u ↔
      MemLpLoc p Ω u ∧ ∃ Du : E → E →L[ℝ] F,
        HasWeakFDerivOn volume Ω u Du ∧ ∀ i, MemLpLoc p Ω (fun x => Du x (b i)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  rw [TauCeti.memW1pLoc_iff]
  refine ⟨fun ⟨hu, Du, hDu, hDuLp⟩ =>
    ⟨hu, Du, hDu, fun i => hDuLp.clm_comp (ContinuousLinearMap.apply ℝ F (b i))⟩,
    fun ⟨hu, Du, hDu, hDuLp⟩ => ⟨hu, Du, hDu, ?_⟩⟩
  let ℓ : ι → E →L[ℝ] ℝ := fun i =>
    (ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap
  have hs : MemLpLoc p Ω
      (fun x => ∑ i, ContinuousLinearMap.smulRightL ℝ E F (ℓ i) (Du x (b i))) :=
    MemLpLoc.sum Finset.univ fun i _ =>
      (hDuLp i).clm_comp (ContinuousLinearMap.smulRightL ℝ E F (ℓ i))
  convert hs using 1
  ext x y
  conv_lhs => rw [← b.sum_repr y]
  rw [map_sum]
  simp [ℓ]

/-- Higher-order planar local Sobolev membership can be tested in any finite basis of the
codomain. -/
theorem memWkpLoc_iff {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι]
    (b : Module.Basis ι ℝ F) {p : ENNReal} {U : Set ℂ} {k : ℕ} {f : ℂ → F} :
    MemWkpLoc p U k f ↔ ∀ i, MemWkpLoc p U k (fun z => b.repr (f z) i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · intro h i
    exact h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemWkpLoc p U k (fun z => ∑ i, b.repr (f z) i • b i) := by
      apply MemWkpLoc.sum
      intro i _
      exact (h i).clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (b i))
    simpa only [b.sum_repr] using hs

end Module.Basis

/-! ### Local Sobolev classes through the two partial derivatives -/

namespace TauCeti

open Complex TopologicalSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ENNReal} {U : Set ℂ} {k : ℕ}

/-- **Assembling a weak derivative from its partial derivatives.** A locally `L^q` map with a
weak derivative `D` on the interior of `U` whose partial derivatives `z ↦ D z 1` and `z ↦ D z I`
lie in `W^{k,q}_loc(U)` lies in `W^{k+1,q}_loc(U)`. The derivative `D` is rebuilt from its two
partial derivatives with `ContinuousLinearMap.smulRightL`. -/
theorem MemLpLoc.memWkpLoc_succ_of_hasWeakFDerivOn {ξ : ℂ → V} {D : ℂ → ℂ →L[ℝ] V}
    (hξ : MemLpLoc q U ξ) (hD : HasWeakFDerivOn volume (Opens.interior U) ξ D)
    (h1 : MemWkpLoc q U k fun z => D z 1) (hI : MemWkpLoc q U k fun z => D z I) :
    MemWkpLoc q U (k + 1) ξ := by
  have := hD.completeSpace
  refine memWkpLoc_succ_iff.2 ⟨hξ, D, hD, ?_⟩
  rw [ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM D]
  exact (h1.clm_comp _).add (hI.clm_comp _)

/-- **Local Sobolev classes through partial derivatives.** A map lies in `W^{k+1,q}_loc(U)`
exactly when it is locally `L^q` on `U` and has a weak derivative on the interior of `U` whose
partial derivatives `z ↦ D z 1` and `z ↦ D z I` lie in `W^{k,q}_loc(U)`. -/
theorem memWkpLoc_succ_iff_apply_one_apply_I {ξ : ℂ → V} :
    MemWkpLoc q U (k + 1) ξ ↔ MemLpLoc q U ξ ∧ ∃ D : ℂ → ℂ →L[ℝ] V,
      HasWeakFDerivOn volume (Opens.interior U) ξ D ∧
        (MemWkpLoc q U k fun z => D z 1) ∧ MemWkpLoc q U k fun z => D z I := by
  refine ⟨fun h => ?_, fun ⟨hξ, D, hD, h1, hI⟩ =>
    hξ.memWkpLoc_succ_of_hasWeakFDerivOn hD h1 hI⟩
  obtain ⟨hξ, D, hD, hDk⟩ := memWkpLoc_succ_iff.1 h
  have := hD.completeSpace
  exact ⟨hξ, D, hD, hDk.clm_comp (ContinuousLinearMap.apply ℝ V 1),
    hDk.clm_comp (ContinuousLinearMap.apply ℝ V I)⟩

end TauCeti
