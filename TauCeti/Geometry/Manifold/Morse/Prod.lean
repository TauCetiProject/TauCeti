/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Analysis.Calculus.Morse.Prod
public import TauCeti.Geometry.Manifold.Instances.NormedProd
public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.Morse.Index
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod

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

When `M` and `N` are charted on normed spaces `E` and `E'`, the last section reads `M × N` on the
normed space `E × E'` (`TauCeti.prodNormedChartedSpace`), with the model `𝓘(ℝ, E × E')`, in which
the Morse complex is stated, and transports these statements to it along
`modelWithCornersSelf_prod`.

## Main declarations

* `TauCeti.isManifoldNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff` and
  `TauCeti.IsManifoldNondegenerateCriticalPoint.comp_fst_add_comp_snd`: nondegenerate critical
  points of the separated sum are the pairs of nondegenerate critical points.
* `TauCeti.mvfderiv_comp_fst_add_comp_snd_eq_zero_iff`: the critical points of the separated sum
  are the pairs of critical points.
* `TauCeti.IsMorseOn.comp_fst_add_comp_snd` and `TauCeti.IsMorse.comp_fst_add_comp_snd`: the
  separated sum of two Morse functions is Morse.
* `TauCeti.criticalHessian_comp_fst_add_comp_snd_apply`: the critical Hessian of the separated
  sum is block diagonal.
* `TauCeti.manifoldMorseIndex_comp_fst_add_comp_snd` and
  `TauCeti.IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_comp_fst_add_comp_snd`: the
  Morse index of the separated sum is the sum of the indices.
* `TauCeti.mvfderiv_comp_fst_add_comp_snd_apply_prodNormed`,
  `TauCeti.criticalPoints_comp_fst_add_comp_snd_prodNormed` and
  `TauCeti.IsMorse.comp_fst_add_comp_snd_prodNormed`: the differential, the critical set and the
  Morse property of the separated sum for the model `𝓘(ℝ, E × E')`.

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

/-- **Nondegenerate critical points of a separated sum.** The point `(x, y)` is a nondegenerate
critical point of `f ∘ Prod.fst + g ∘ Prod.snd` exactly when `x` is a nondegenerate critical point
of `f` and `y` is one of `g`. -/
@[simp]
theorem isManifoldNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff :
    IsManifoldNondegenerateCriticalPoint (I.prod I') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) ↔
      IsManifoldNondegenerateCriticalPoint I f x ∧
        IsManifoldNondegenerateCriticalPoint I' g y := by
  rw [isManifoldNondegenerateCriticalPoint_iff (I.prod I'),
    isManifoldNondegenerateCriticalPoint_iff I, isManifoldNondegenerateCriticalPoint_iff I',
    comp_fst_add_comp_snd_comp_extChartAt_prod_symm]
  simp only [extChartAt_prod, PartialEquiv.prod_coe]
  exact isNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff

/-- A pair of nondegenerate critical points of `f` and `g` is a nondegenerate critical point of
the separated sum `f ∘ Prod.fst + g ∘ Prod.snd`. -/
theorem IsManifoldNondegenerateCriticalPoint.comp_fst_add_comp_snd
    (hf : IsManifoldNondegenerateCriticalPoint I f x)
    (hg : IsManifoldNondegenerateCriticalPoint I' g y) :
    IsManifoldNondegenerateCriticalPoint (I.prod I') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) :=
  isManifoldNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff.2 ⟨hf, hg⟩

/-- **The critical points of a separated sum are the pairs of critical points.** On boundaryless
manifolds, the differential of `f ∘ Prod.fst + g ∘ Prod.snd` vanishes at `(x, y)` exactly when the
differentials of `f` at `x` and of `g` at `y` both vanish. -/
@[simp]
theorem mvfderiv_comp_fst_add_comp_snd_eq_zero_iff [I.Boundaryless] [I'.Boundaryless]
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hg : MDifferentiableAt I' 𝓘(ℝ) g y) :
    mvfderiv (I.prod I') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) = 0 ↔
      mvfderiv I f x = 0 ∧ mvfderiv I' g y = 0 := by
  rw [mvfderiv_eq_fderiv_comp_extChartAt_symm, mvfderiv_eq_fderiv_comp_extChartAt_symm,
    mvfderiv_eq_fderiv_comp_extChartAt_symm, comp_fst_add_comp_snd_comp_extChartAt_prod_symm]
  simp only [extChartAt_prod, PartialEquiv.prod_coe]
  exact fderiv_comp_fst_add_comp_snd_eq_zero_iff hf.differentiableAt_comp_extChartAt_symm
    hg.differentiableAt_comp_extChartAt_symm

/-- **The separated sum of two Morse functions is Morse on the product of the sets.** A function
which is Morse on a set has a differentiable coordinate expression at every point of the set, so a
critical point of the sum has both components critical. -/
theorem IsMorseOn.comp_fst_add_comp_snd {s : Set M} {t : Set N} (hf : IsMorseOn I f s)
    (hg : IsMorseOn I' g t) : IsMorseOn (I.prod I') (f ∘ Prod.fst + g ∘ Prod.snd) (s ×ˢ t) := by
  refine isMorseOn_iff.2 ⟨(hf.contMDiffOn.comp contMDiffOn_fst fun _ hp ↦ (Set.mem_prod.1 hp).1).add
    (hg.contMDiffOn.comp contMDiffOn_snd fun _ hp ↦ (Set.mem_prod.1 hp).2), ?_⟩
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

/-- **The critical Hessian of a separated sum is block diagonal.** When the coordinate expressions
of `f` at `x` and of `g` at `y` are twice continuously differentiable, the critical Hessian of
`f ∘ Prod.fst + g ∘ Prod.snd` at `(x, y)` pairs the `M`-components through the critical Hessian of
`f` and the `N`-components through that of `g`. -/
theorem criticalHessian_comp_fst_add_comp_snd_apply
    (hf : ContDiffAt ℝ 2 (f ∘ (extChartAt I x).symm) (extChartAt I x x))
    (hg : ContDiffAt ℝ 2 (g ∘ (extChartAt I' y).symm) (extChartAt I' y y)) (v w : E × E') :
    criticalHessian (I.prod I') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) v w =
      criticalHessian I f x v.1 w.1 + criticalHessian I' g y v.2 w.2 := by
  have hD := congr($(fderiv_fderiv_comp_fst_add_comp_snd hf hg) v w)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap', Prod.map_fst, Prod.map_snd,
    ContinuousLinearMap.coprodEquivL_apply_apply] at hD
  rw [criticalHessian_def, criticalHessian_def, criticalHessian_def,
    comp_fst_add_comp_snd_comp_extChartAt_prod_symm]
  simp only [extChartAt_prod, PartialEquiv.prod_coe]
  -- The tangent spaces at `(x, y)`, `x` and `y` are the model spaces `E × E'`, `E` and `E'`.
  exact hD

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

/-! ### The separated sum read on `E × E'`

When `M` and `N` are charted on normed spaces `E` and `E'`, the product `M × N` can also be read
on the normed space `E × E'` (`TauCeti.prodNormedChartedSpace`), with the model `𝓘(ℝ, E × E')`.
This model equals `𝓘(ℝ, E).prod 𝓘(ℝ, E')` only propositionally (`modelWithCornersSelf_prod`), so
each statement below is proved for a model `I` equal to the product model, which `subst` replaces
by the product model, and then specialized to `𝓘(ℝ, E × E')`. -/

namespace TauCeti

attribute [local instance 10] prodNormedChartedSpace

variable {E E' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace E' N]
  {f : M → ℝ} {g : N → ℝ}

section Transport

variable {I : ModelWithCorners ℝ (E × E') (E × E')}

private theorem manifoldMorseIndex_comp_fst_add_comp_snd_of_eq [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] (hI : I = 𝓘(ℝ, E).prod 𝓘(ℝ, E')) {x : M} {y : N}
    (hf : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (hg : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E') g y) :
    manifoldMorseIndex I (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) =
      manifoldMorseIndex 𝓘(ℝ, E) f x + manifoldMorseIndex 𝓘(ℝ, E') g y := by
  subst hI; exact hf.manifoldMorseIndex_comp_fst_add_comp_snd hg

private theorem isMorse_comp_fst_add_comp_snd_of_eq (hI : I = 𝓘(ℝ, E).prod 𝓘(ℝ, E'))
    (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g) :
    IsMorse I (f ∘ Prod.fst + g ∘ Prod.snd) := by
  subst hI; exact hf.comp_fst_add_comp_snd hg

private theorem mvfderiv_comp_fst_add_comp_snd_apply_of_eq (hI : I = 𝓘(ℝ, E).prod 𝓘(ℝ, E'))
    {z : M × N} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f z.1)
    (hg : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ) g z.2) (u : E × E') :
    mvfderiv I (f ∘ Prod.fst + g ∘ Prod.snd) z u =
      mvfderiv 𝓘(ℝ, E) f z.1 u.1 + mvfderiv 𝓘(ℝ, E') g z.2 u.2 := by
  subst hI
  rw [mvfderiv_add (hf.comp z mdifferentiableAt_fst) (hg.comp z mdifferentiableAt_snd)]
  exact congr($(mvfderiv_comp_fst_apply f z u) + $(mvfderiv_comp_snd_apply g z u))

private theorem mvfderiv_comp_fst_add_comp_snd_eq_zero_iff_of_eq
    (hI : I = 𝓘(ℝ, E).prod 𝓘(ℝ, E')) {z : M × N} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f z.1)
    (hg : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ) g z.2) :
    mvfderiv I (f ∘ Prod.fst + g ∘ Prod.snd) z = 0 ↔
      mvfderiv 𝓘(ℝ, E) f z.1 = 0 ∧ mvfderiv 𝓘(ℝ, E') g z.2 = 0 := by
  subst hI; exact mvfderiv_comp_fst_add_comp_snd_eq_zero_iff hf hg

end Transport

/-- At a pair of nondegenerate critical points, the Morse index of the separated sum, for the
model `𝓘(ℝ, E × E')`, is the sum of the two Morse indices. -/
theorem IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_comp_fst_add_comp_snd_prodNormed
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] {x : M} {y : N}
    (hf : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (hg : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E') g y) :
    manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (x, y) =
      manifoldMorseIndex 𝓘(ℝ, E) f x + manifoldMorseIndex 𝓘(ℝ, E') g y :=
  manifoldMorseIndex_comp_fst_add_comp_snd_of_eq modelWithCornersSelf_prod hf hg

/-- The separated sum of two Morse functions is a Morse function for the model `𝓘(ℝ, E × E')`. -/
theorem IsMorse.comp_fst_add_comp_snd_prodNormed (hf : IsMorse 𝓘(ℝ, E) f)
    (hg : IsMorse 𝓘(ℝ, E') g) : IsMorse 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) :=
  isMorse_comp_fst_add_comp_snd_of_eq modelWithCornersSelf_prod hf hg

/-- **The differential of a separated sum** is the sum of the differentials of the summands. -/
theorem mvfderiv_comp_fst_add_comp_snd_apply_prodNormed {z : M × N}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f z.1) (hg : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ) g z.2)
    (u : E × E') :
    mvfderiv 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) z u =
      mvfderiv 𝓘(ℝ, E) f z.1 u.1 + mvfderiv 𝓘(ℝ, E') g z.2 u.2 :=
  mvfderiv_comp_fst_add_comp_snd_apply_of_eq modelWithCornersSelf_prod hf hg u

/-- **The critical points of a separated sum are the pairs of critical points**, for the model
`𝓘(ℝ, E × E')`. -/
theorem mvfderiv_comp_fst_add_comp_snd_eq_zero_iff_prodNormed {z : M × N}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f z.1) (hg : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ) g z.2) :
    mvfderiv 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) z = 0 ↔
      mvfderiv 𝓘(ℝ, E) f z.1 = 0 ∧ mvfderiv 𝓘(ℝ, E') g z.2 = 0 :=
  mvfderiv_comp_fst_add_comp_snd_eq_zero_iff_of_eq modelWithCornersSelf_prod hf hg

/-- The form of `TauCeti.mvfderiv_comp_fst_add_comp_snd_eq_zero_iff_prodNormed` for
the manifold derivative `mfderiv`, in which adapted pseudo-gradients are stated. -/
theorem mfderiv_comp_fst_add_comp_snd_eq_zero_iff_prodNormed {z : M × N}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f z.1) (hg : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ) g z.2) :
    mfderiv 𝓘(ℝ, E × E') 𝓘(ℝ) (f ∘ Prod.fst + g ∘ Prod.snd) z = 0 ↔
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z.1 = 0 ∧ mfderiv 𝓘(ℝ, E') 𝓘(ℝ) g z.2 = 0 := by
  simp only [← mvfderiv_eq_zero_iff]
  exact mvfderiv_comp_fst_add_comp_snd_eq_zero_iff_prodNormed hf hg

/-- **The critical set of a separated sum** is the product of the critical sets, for the model
`𝓘(ℝ, E × E')`. -/
theorem criticalPoints_comp_fst_add_comp_snd_prodNormed (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) :
    criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) =
      criticalPoints 𝓘(ℝ, E) f ×ˢ criticalPoints 𝓘(ℝ, E') g := by
  ext z
  simp only [mem_criticalPoints, mem_prod]
  exact mvfderiv_comp_fst_add_comp_snd_eq_zero_iff_prodNormed (hf z.1) (hg z.2)

end TauCeti

end
