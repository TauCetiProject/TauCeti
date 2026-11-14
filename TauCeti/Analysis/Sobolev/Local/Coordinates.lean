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
vector-valued maps without choosing compatible representatives of their iterated weak
derivatives, including the zero-dimensional codomain, order zero, and exponent infinity.

On the domain side, for any finite basis `b` of a real normed space `E` and any codomain `V`,
a weak derivative `D : E → E →L[ℝ] V` is reconstructed from its directional components
`x ↦ D x (b i)` via `ContinuousLinearMap.smulRightL`. Thus `Module.Basis.memWkpLoc_succ_iff_apply`
characterizes `W^{k+1,q}_loc(U)` by local `L^q` membership and `x ↦ D x (b i) ∈ W^{k,q}_loc(U)`
for all `i`, and `Module.Basis.memWkpLoc_succ_iff_hasWeakLineDerivOn` identifies the coordinate-free
definition `TauCeti.MemWkpLoc` with the classical partial-derivative definition for `1 ≤ q`.
For maps on `ℂ`, `TauCeti.memWkpLoc_succ_iff_apply_one_apply_I` specializes this to `1` and `I`.

## References

* L. C. Evans, *Partial Differential Equations*, second edition, §5.2.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (vector-valued Sobolev spaces).
-/

public noncomputable section

open TauCeti MeasureTheory TopologicalSpace

namespace Module.Basis

section Codomain

variable {ι : Type*} [Finite ι]

/-- Local `Lᵖ` membership can be tested in any finite basis of the codomain, on any topological
measure space. No completeness of the codomain is needed. -/
theorem memLpLoc_iff {E F : Type*} [TopologicalSpace E] [MeasureSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ENNReal} {U : Set E} {f : E → F}
    (b : Module.Basis ι ℝ F) :
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

/-- Local Sobolev membership of every order can be tested in any finite basis of the codomain.
Scalar coordinate witnesses may be chosen independently; finite sums reconstruct the map
in the same Sobolev class. -/
theorem memWkpLoc_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ENNReal} {U : Set E} {k : ℕ} {f : E → F} (b : Module.Basis ι ℝ F) :
    MemWkpLoc p U k f ↔ ∀ i, MemWkpLoc p U k (fun x => b.repr (f x) i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · intro h i
    exact h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemWkpLoc p U k (fun x => ∑ i, b.repr (f x) i • b i) :=
      MemWkpLoc.sum Finset.univ fun i _ =>
        (h i).clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (b i))
    simpa only [b.sum_repr] using hs

end Codomain

section Domain

variable {E V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {q : ENNReal} {U : Set E} {k : ℕ}

/-- **Assembling a weak derivative from its directional components in a domain basis.** If `ξ` is
locally `L^q` on `U` and has a weak derivative `D` on `interior U` whose directional components
`x ↦ D x (b i)` along a finite basis `b` of `E` lie in `W^{k,q}_loc(U)`, then
`ξ ∈ W^{k+1,q}_loc(U)`. No finite-dimensionality of `V` is needed. -/
theorem memWkpLoc_succ_of_hasWeakFDerivOn (b : Module.Basis ι ℝ E) {ξ : E → V}
    {D : E → E →L[ℝ] V} (hξ : MemLpLoc q U ξ)
    (hD : HasWeakFDerivOn volume (Opens.interior U) ξ D)
    (hb : ∀ i, MemWkpLoc q U k fun x => D x (b i)) :
    MemWkpLoc q U (k + 1) ξ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  have : CompleteSpace V := hD.completeSpace
  refine memWkpLoc_succ_iff.2 ⟨hξ, D, hD, ?_⟩
  have hR (c : E →L[ℝ] ℝ) (w : V) :
      ContinuousLinearMap.smulRightL ℝ E V c w = c.smulRight w := rfl
  have hDeq : D = fun x => ∑ i,
      ContinuousLinearMap.smulRightL ℝ E V (b.coord i).toContinuousLinearMap (D x (b i)) := by
    ext x y
    simp only [hR, sum_apply,
      ContinuousLinearMap.smulRight_apply, LinearMap.coe_toContinuousLinearMap', b.coord_apply]
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    simp only [map_smul]
  rw [hDeq]
  exact MemWkpLoc.sum Finset.univ fun i _ =>
    (hb i).clm_comp (ContinuousLinearMap.smulRightL ℝ E V (b.coord i).toContinuousLinearMap)

/-- **Local Sobolev classes through directional components of a weak derivative.** For any finite
basis `b` of `E`, `ξ ∈ W^{k+1,q}_loc(U)` iff `ξ ∈ L^q_loc(U)` and `ξ` has a weak derivative `D`
on `interior U` with `x ↦ D x (b i) ∈ W^{k,q}_loc(U)` for every `i`. -/
theorem memWkpLoc_succ_iff_apply (b : Module.Basis ι ℝ E) {ξ : E → V} :
    MemWkpLoc q U (k + 1) ξ ↔ MemLpLoc q U ξ ∧ ∃ D : E → E →L[ℝ] V,
      HasWeakFDerivOn volume (Opens.interior U) ξ D ∧
        ∀ i, MemWkpLoc q U k fun x => D x (b i) := by
  refine ⟨fun h => ?_, fun ⟨hξ, D, hD, hb⟩ => b.memWkpLoc_succ_of_hasWeakFDerivOn hξ hD hb⟩
  obtain ⟨hξ, D, hD, hDk⟩ := memWkpLoc_succ_iff.1 h
  have : CompleteSpace V := hD.completeSpace
  exact ⟨hξ, D, hD, fun i => hDk.clm_comp (ContinuousLinearMap.apply ℝ V (b i))⟩

/-- **Equivalence with partial weak derivatives in a finite domain basis.** For `1 ≤ q` and a
complete codomain `V`, `ξ ∈ W^{k+1,q}_loc(U)` if and only if `ξ ∈ L^q_loc(U)` and each basis
direction `b i` admits a weak directional derivative on `interior U` lying in `W^{k,q}_loc(U)`. -/
theorem memWkpLoc_succ_iff_hasWeakLineDerivOn [IsFiniteMeasureOnCompacts (volume : Measure E)]
    [CompleteSpace V] (b : Module.Basis ι ℝ E) (hq : 1 ≤ q) {ξ : E → V} :
    MemWkpLoc q U (k + 1) ξ ↔ MemLpLoc q U ξ ∧
      ∀ i, ∃ d : E → V, HasWeakLineDerivOn volume (Opens.interior U) ξ d (b i) ∧
        MemWkpLoc q U k d := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  constructor
  · intro h
    obtain ⟨hξ, D, hD, hb⟩ := (b.memWkpLoc_succ_iff_apply).1 h
    exact ⟨hξ, fun i => ⟨fun x => D x (b i), hD.hasWeakLineDerivOn (b i), hb i⟩⟩
  · rintro ⟨hξ, hd⟩
    choose d hd_weak hd_mem using hd
    let D : E → E →L[ℝ] V := fun x => ∑ i, (b.coord i).toContinuousLinearMap.smulRight (d i x)
    have hDb : ∀ i x, D x (b i) = d i x := fun i x => by
      simp [D, b.coord_apply, b.repr_self, Finsupp.single_apply]
    have hξ_int : LocallyIntegrableOn ξ (Opens.interior U) volume :=
      (hξ.mono_set interior_subset).locallyIntegrableOn hq isOpen_interior.isLocallyClosed
    have hD : HasWeakFDerivOn volume (Opens.interior U) ξ D :=
      b.hasWeakFDerivOn_of_forall hξ_int fun i => by simpa only [hDb i] using hd_weak i
    exact b.memWkpLoc_succ_of_hasWeakFDerivOn hξ hD fun i => by simpa only [hDb i] using hd_mem i

/-- **Order-one partial-derivative characterization in a finite domain basis.** For `1 ≤ q` and a
complete codomain `V`, `ξ ∈ W^{1,q}_loc(U)` if and only if `ξ ∈ L^q_loc(U)` and each basis
direction `b i` admits a locally `L^q` weak directional derivative on `interior U`. -/
theorem memWkpLoc_one_iff_hasWeakLineDerivOn [IsFiniteMeasureOnCompacts (volume : Measure E)]
    [CompleteSpace V] (b : Module.Basis ι ℝ E) (hq : 1 ≤ q) {ξ : E → V} :
    MemWkpLoc q U 1 ξ ↔ MemLpLoc q U ξ ∧
      ∀ i, ∃ d : E → V, HasWeakLineDerivOn volume (Opens.interior U) ξ d (b i) ∧
        MemLpLoc q U d := by
  simpa only [memWkpLoc_zero_iff] using
    b.memWkpLoc_succ_iff_hasWeakLineDerivOn (k := 0) (U := U) (ξ := ξ) hq

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
