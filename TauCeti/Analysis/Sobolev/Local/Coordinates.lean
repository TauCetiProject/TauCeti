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
# Coordinates and partial derivatives of local Sobolev maps

A map into a finite-dimensional real normed space is locally Sobolev of order `k` if and
only if all its coordinates in a finite basis are (`Module.Basis.memWkpLoc_iff`). The same
criterion holds for local `Lᵖ` membership on any topological measure space
(`Module.Basis.memLpLoc_iff`). These criteria allow scalar local estimates to be applied to
vector-valued maps without choosing compatible representatives of their iterated weak derivatives.

The criteria include the zero-dimensional codomain, order zero, and the exponent infinity.
They also show that testing one basis is equivalent to testing every basis.

Dually, for any finite basis `b` of a real normed domain `E` and any Banach codomain `V`, a weak
derivative `D : E → E →L[ℝ] V` lies in `W^{k,q}_loc(U)` as soon as its directional components
`x ↦ D x (b i)` do (`Module.Basis.memWkpLoc_succ_of_hasWeakFDerivOn`,
`Module.Basis.memWkpLoc_succ_iff_apply`). On `ℂ`, `TauCeti.memWkpLoc_succ_iff_apply_one_apply_I`
specializes this to the two partial derivatives `z ↦ D z 1` and `z ↦ D z I`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (vector-valued Sobolev spaces).
-/

public noncomputable section

open TauCeti MeasureTheory TopologicalSpace

namespace Module.Basis

section Codomain

/-- Local `Lᵖ` membership can be tested in any finite basis of the codomain. Neither completeness
of the codomain nor a vector-space structure on the domain is needed. -/
theorem memLpLoc_iff {E F ι : Type*} [TopologicalSpace E] [MeasureSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι]
    {p : ENNReal} {U : Set E} {f : E → F} (b : Module.Basis ι ℝ F) :
    MemLpLoc p U f ↔ ∀ i, MemLpLoc p U (fun z => b.repr (f z) i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · exact fun h i =>
      h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemLpLoc p U (fun z => ∑ i, b.repr (f z) i • b i) :=
      MemLpLoc.sum _ fun i _ => (h i).smulRight (b i)
    simpa only [b.sum_repr] using hs

/-- Local Sobolev membership of every order can be tested in any finite basis of the codomain.
Scalar coordinate witnesses may be chosen independently; finite sums reconstruct the map
in the same Sobolev class. -/
theorem memWkpLoc_iff {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι]
    {p : ENNReal} {U : Set E} {k : ℕ} {f : E → F} (b : Module.Basis ι ℝ F) :
    MemWkpLoc p U k f ↔ ∀ i, MemWkpLoc p U k (fun z => b.repr (f z) i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · intro h i
    exact h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemWkpLoc p U k (fun z => ∑ i, b.repr (f z) i • b i) :=
      MemWkpLoc.sum _ fun i _ => (h i).smulRight (b i)
    simpa only [b.sum_repr] using hs

end Codomain

section Domain

variable {E V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {q : ENNReal} {U : Set E} {k : ℕ}

/-- **Assembling a weak derivative from its directional derivatives along a domain basis.** A
locally `L^q` map with a weak derivative `D` on `interior U` whose directional components
`x ↦ D x (b i)` along a finite basis `b` of `E` lie in `W^{k,q}_loc(U)` lies in
`W^{k+1,q}_loc(U)`, for any codomain `V`. -/
theorem memWkpLoc_succ_of_hasWeakFDerivOn (b : Module.Basis ι ℝ E) {ξ : E → V}
    {D : E → E →L[ℝ] V} (hξ : MemLpLoc q U ξ)
    (hD : HasWeakFDerivOn volume (Opens.interior U) ξ D)
    (hb : ∀ i, MemWkpLoc q U k fun z => D z (b i)) :
    MemWkpLoc q U (k + 1) ξ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  have := hD.completeSpace
  refine memWkpLoc_succ_iff.2 ⟨hξ, D, hD, ?_⟩
  have hDeq : D = fun z => ∑ i,
      ContinuousLinearMap.smulRightL ℝ E V (b.coord i).toContinuousLinearMap (D z (b i)) := by
    funext z
    ext v
    calc D z v = D z (∑ i, b.repr v i • b i) := by rw [b.sum_repr]
      _ = _ := by rw [map_sum]; simp
  rw [hDeq]
  exact MemWkpLoc.sum _ fun i _ =>
    (hb i).clm_comp (ContinuousLinearMap.smulRightL ℝ E V (b.coord i).toContinuousLinearMap)

/-- **Local Sobolev classes through partial derivatives in a finite domain basis.** A map lies in
`W^{k+1,q}_loc(U)` if and only if it is locally `L^q` on `U` and admits a weak Fréchet derivative
`D` on `interior U` whose directional components `x ↦ D x (b i)` lie in `W^{k,q}_loc(U)`. -/
theorem memWkpLoc_succ_iff_apply (b : Module.Basis ι ℝ E) {ξ : E → V} :
    MemWkpLoc q U (k + 1) ξ ↔ MemLpLoc q U ξ ∧ ∃ D : E → E →L[ℝ] V,
      HasWeakFDerivOn volume (Opens.interior U) ξ D ∧
        ∀ i, MemWkpLoc q U k fun z => D z (b i) := by
  refine ⟨fun h => ?_, fun ⟨hξ, D, hD, hb⟩ => b.memWkpLoc_succ_of_hasWeakFDerivOn hξ hD hb⟩
  obtain ⟨hξ, D, hD, hDk⟩ := memWkpLoc_succ_iff.1 h
  have := hD.completeSpace
  exact ⟨hξ, D, hD, fun i => hDk.clm_comp (ContinuousLinearMap.apply ℝ V (b i))⟩

end Domain

end Module.Basis

/-! ### Local Sobolev classes on `ℂ` through the two partial derivatives -/

namespace TauCeti

open Complex

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
