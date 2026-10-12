/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Analysis.Calculus.Morse.Prod
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.Morse.Index

/-!
# Morse functions on a product manifold

If `f` is a Morse function on `M` and `g` is a Morse function on `N`, the separated sum
`f ∘ Prod.fst + g ∘ Prod.snd` is a Morse function on the product manifold `M × N`. Its critical
points are the pairs `(x, y)` of critical points of `f` and `g`, and its Morse index at such a pair
is the sum of the two indices. This is the classical construction of the standard Morse function
on a product, for instance on a torus `S¹ × S¹` as the sum of two height functions.

The product chart at `(x, y)` is the product of the preferred charts at `x` and `y`, so all the
statements reduce to the calculus of separated sums on the model space `E × E'`. The two model
spaces are assumed boundaryless where the manifold differential `mvfderiv` must be split into its
two components, since only then is the coordinate expression of a smooth function differentiable
in the ordinary sense at the chart image of a point. The Morse statements themselves need neither
boundary nor openness hypotheses, because `IsMorseOn` tests criticality in the preferred charts,
where a function which is Morse on a set has a differentiable coordinate expression at every point
of the set.

## Main declarations

* `TauCeti.isManifoldNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff` and
  `TauCeti.IsManifoldNondegenerateCriticalPoint.comp_fst_add_comp_snd`: nondegenerate critical
  points of the separated sum are the pairs of nondegenerate critical points.
* `TauCeti.mvfderiv_comp_fst_add_comp_snd_eq_zero_iff`: the critical points of the separated sum
  are the pairs of critical points.
* `TauCeti.IsMorseOn.comp_fst_add_comp_snd` and `TauCeti.IsMorse.comp_fst_add_comp_snd`: the
  separated sum of two Morse functions is Morse.
* `TauCeti.manifoldMorseIndex_comp_fst_add_comp_snd` and
  `TauCeti.IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_comp_fst_add_comp_snd`: the
  Morse index of the separated sum is the sum of the indices.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E E' H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {f : M → ℝ} {g : N → ℝ}
  {x : M} {y : N}

/-- In the preferred chart of the product at `(x, y)`, the coordinate expression of a separated
sum is the separated sum of the coordinate expressions of the summands in the preferred charts at
`x` and at `y`. This is not a `simp` lemma: `simp` unfolds `extChartAt` on the left-hand side
before this lemma could fire. -/
theorem comp_fst_add_comp_snd_comp_extChartAt_prod_symm :
    (f ∘ Prod.fst + g ∘ Prod.snd) ∘ (extChartAt (I.prod I') (x, y)).symm =
      (f ∘ (extChartAt I x).symm) ∘ Prod.fst + (g ∘ (extChartAt I' y).symm) ∘ Prod.snd := by
  funext p
  simp only [Function.comp_apply, Pi.add_apply, extChartAt_prod, PartialEquiv.prod_coe_symm]

/-- **Nondegenerate critical points of a separated sum.** When the coordinate expressions of `f`
at `x` and of `g` at `y` are twice continuously differentiable, `(x, y)` is a nondegenerate
critical point of `f ∘ Prod.fst + g ∘ Prod.snd` exactly when `x` is a nondegenerate critical point
of `f` and `y` is one of `g`. This is not a `simp` lemma: `simp` unfolds `extChartAt` in the
hypotheses, so the lemma could never discharge them. -/
theorem isManifoldNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff
    (hf : ContDiffAt ℝ 2 (f ∘ (extChartAt I x).symm) (extChartAt I x x))
    (hg : ContDiffAt ℝ 2 (g ∘ (extChartAt I' y).symm) (extChartAt I' y y)) :
    IsManifoldNondegenerateCriticalPoint (I.prod I') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) ↔
      IsManifoldNondegenerateCriticalPoint I f x ∧
        IsManifoldNondegenerateCriticalPoint I' g y := by
  rw [isManifoldNondegenerateCriticalPoint_iff (I.prod I'),
    isManifoldNondegenerateCriticalPoint_iff I, isManifoldNondegenerateCriticalPoint_iff I',
    comp_fst_add_comp_snd_comp_extChartAt_prod_symm]
  simp only [extChartAt_prod, PartialEquiv.prod_coe]
  exact isNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff hf hg

/-- A pair of nondegenerate critical points of `f` and `g` is a nondegenerate critical point of
the separated sum `f ∘ Prod.fst + g ∘ Prod.snd`. -/
theorem IsManifoldNondegenerateCriticalPoint.comp_fst_add_comp_snd
    (hf : IsManifoldNondegenerateCriticalPoint I f x)
    (hg : IsManifoldNondegenerateCriticalPoint I' g y) :
    IsManifoldNondegenerateCriticalPoint (I.prod I') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) :=
  (isManifoldNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff
    ((isManifoldNondegenerateCriticalPoint_iff I).1 hf).contDiffAt
    ((isManifoldNondegenerateCriticalPoint_iff I').1 hg).contDiffAt).2 ⟨hf, hg⟩

/-- **The critical points of a separated sum are the pairs of critical points.** On boundaryless
manifolds, the differential of `f ∘ Prod.fst + g ∘ Prod.snd` vanishes at `(x, y)` exactly when the
differentials of `f` at `x` and of `g` at `y` both vanish. -/
@[simp]
theorem mvfderiv_comp_fst_add_comp_snd_eq_zero_iff [I.Boundaryless] [I'.Boundaryless]
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hg : MDifferentiableAt I' 𝓘(ℝ) g y) :
    mvfderiv (I.prod I') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) = 0 ↔
      mvfderiv I f x = 0 ∧ mvfderiv I' g y = 0 := by
  have hsum : MDifferentiableAt (I.prod I') 𝓘(ℝ) (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) :=
    (hf.comp (x, y) mdifferentiableAt_fst).add (hg.comp (x, y) mdifferentiableAt_snd)
  rw [hsum.mvfderiv_eq_fderiv_comp_extChartAt_symm, hf.mvfderiv_eq_fderiv_comp_extChartAt_symm,
    hg.mvfderiv_eq_fderiv_comp_extChartAt_symm, comp_fst_add_comp_snd_comp_extChartAt_prod_symm]
  simp only [extChartAt_prod, PartialEquiv.prod_coe]
  exact fderiv_comp_fst_add_comp_snd_eq_zero_iff hf.differentiableAt_comp_extChartAt_symm
    hg.differentiableAt_comp_extChartAt_symm

/-- **The separated sum of two Morse functions is Morse on the product of the sets.** A function
which is Morse on a set has a differentiable coordinate expression at every point of the set, so a
critical point of the sum has both components critical. -/
theorem IsMorseOn.comp_fst_add_comp_snd {s : Set M} {t : Set N} (hf : IsMorseOn I f s)
    (hg : IsMorseOn I' g t) : IsMorseOn (I.prod I') (f ∘ Prod.fst + g ∘ Prod.snd) (s ×ˢ t) := by
  refine isMorseOn_iff.2 ⟨(hf.contMDiffOn.comp contMDiffOn_fst fun p hp ↦ hp.1).add
    (hg.contMDiffOn.comp contMDiffOn_snd fun p hp ↦ hp.2), ?_⟩
  rintro ⟨x, y⟩ ⟨hx, hy⟩ hcrit
  rw [comp_fst_add_comp_snd_comp_extChartAt_prod_symm] at hcrit
  simp only [extChartAt_prod, PartialEquiv.prod_coe] at hcrit
  obtain ⟨h₁, h₂⟩ := (fderiv_comp_fst_add_comp_snd_eq_zero_iff
    (hf.differentiableAt_comp_extChartAt_symm hx)
    (hg.differentiableAt_comp_extChartAt_symm hy)).1 hcrit
  exact (hf.isManifoldNondegenerateCriticalPoint hx h₁).comp_fst_add_comp_snd
    (hg.isManifoldNondegenerateCriticalPoint hy h₂)

/-- **The separated sum of two Morse functions is a Morse function on the product manifold.** -/
theorem IsMorse.comp_fst_add_comp_snd (hf : IsMorse I f) (hg : IsMorse I' g) :
    IsMorse (I.prod I') (f ∘ Prod.fst + g ∘ Prod.snd) := by
  rw [← isMorseOn_univ, ← univ_prod_univ]
  exact (hf.isMorseOn univ).comp_fst_add_comp_snd (hg.isMorseOn univ)

/-- **The Morse index of a separated sum is additive.** When the coordinate expressions of `f` at
`x` and of `g` at `y` are twice continuously differentiable, the index of
`f ∘ Prod.fst + g ∘ Prod.snd` at `(x, y)` is the sum of the indices of `f` at `x` and of `g` at
`y`. This is not a `simp` lemma: `simp` unfolds `extChartAt` in the hypotheses, so the lemma could
never discharge them. -/
theorem manifoldMorseIndex_comp_fst_add_comp_snd [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (hf : ContDiffAt ℝ 2 (f ∘ (extChartAt I x).symm) (extChartAt I x x))
    (hg : ContDiffAt ℝ 2 (g ∘ (extChartAt I' y).symm) (extChartAt I' y y)) :
    manifoldMorseIndex (I.prod I') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) =
      manifoldMorseIndex I f x + manifoldMorseIndex I' g y := by
  rw [manifoldMorseIndex_def, manifoldMorseIndex_def, manifoldMorseIndex_def,
    comp_fst_add_comp_snd_comp_extChartAt_prod_symm]
  simp only [extChartAt_prod, PartialEquiv.prod_coe]
  exact morseIndex_comp_fst_add_comp_snd hf hg

/-- At a pair of nondegenerate critical points, the Morse index of the separated sum is the sum of
the two Morse indices. -/
theorem IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_comp_fst_add_comp_snd
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    (hf : IsManifoldNondegenerateCriticalPoint I f x)
    (hg : IsManifoldNondegenerateCriticalPoint I' g y) :
    manifoldMorseIndex (I.prod I') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) =
      manifoldMorseIndex I f x + manifoldMorseIndex I' g y :=
  TauCeti.manifoldMorseIndex_comp_fst_add_comp_snd
    ((isManifoldNondegenerateCriticalPoint_iff I).1 hf).contDiffAt
    ((isManifoldNondegenerateCriticalPoint_iff I').1 hg).contDiffAt

end TauCeti

end
