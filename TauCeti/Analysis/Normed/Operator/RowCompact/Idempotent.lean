/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import TauCeti.Analysis.Normed.Operator.RingOpNorm.Idempotent
public import TauCeti.Analysis.Normed.Operator.RowCompact

/-!
# Row-compact idempotents have finite projective range

Let `R` be a complete ultrametric normed ring with Tate scalars and `I` a discrete index type.
If `e` is a row-compact idempotent endomorphism of the model space `C₀(I, R)`, its range is a
finitely generated projective `R`-module. The finite spectral projectors of the Riesz theory of
compact operators over coefficient rings are such idempotents; their finite projective ranges
replace the finite-dimensional generalised eigenspaces of the field case.

The range is compared with a sufficiently large finite coordinate projection
`π_S = ZeroAtInftyContinuousMap.indicatorCLM R S`: row compactness gives
`‖e - e ∘ π_S ∘ e‖ < 1` for some finite `S`, and `π_S` factors through the coordinates
`C₀(I, R) → (S → R)`. Hence the range of `e` is a direct summand of the finite free module
`S → R`. No Noetherian hypothesis is needed and the scalars may have nilpotents. The range need
not be free.

## Main results

* `ContinuousLinearMap.IsRowCompact.exists_ringOpNorm_sub_mul_indicatorCLM_mul_lt_one`: a
  row-compact idempotent `e` satisfies `‖e - e ∘ π_S ∘ e‖ < 1` for some finite `S`.
* `ContinuousLinearMap.IsRowCompact.exists_comp_eq_id_of_isIdempotentElem`: the range of a
  row-compact idempotent is a direct summand of `S → R` for a finite set `S` of coordinates.
* `ContinuousLinearMap.IsRowCompact.finite_range_of_isIdempotentElem`,
  `ContinuousLinearMap.IsRowCompact.projective_range_of_isIdempotentElem`: the range of a
  row-compact idempotent is finitely generated and projective.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open Filter ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]
  [NormedRing R] [IsUltrametricDist R] [TauCeti.NormedRing.IsTate R] [CompleteSpace R]

namespace ContinuousLinearMap

open scoped TauCeti.RingOpNorm

omit [CompleteSpace R] in
/-- A row-compact idempotent endomorphism `e` of `C₀(I, R)` is close to its compression by a
finite coordinate projection: `‖e - e ∘ π_S ∘ e‖ < 1` for some finite set `S` of coordinates. -/
theorem IsRowCompact.exists_ringOpNorm_sub_mul_indicatorCLM_mul_lt_one
    {e : C₀(I, R) →L[R] C₀(I, R)} (hu : e.IsRowCompact) (he : IsIdempotentElem e) :
    ∃ S : Finset I, ‖e - e * indicatorCLM R (S : Set I) * e‖ < 1 := by
  have hlim := (isRowCompact_iff_tendsto_ringOpNorm_sub_indicatorCLM_comp.1 hu).const_mul ‖e‖
  rw [mul_zero] at hlim
  obtain ⟨S, hS⟩ := (hlim.eventually_lt_const one_pos).exists
  refine ⟨S, ?_⟩
  have hee (x : C₀(I, R)) : e (e x) = e x := congr($he.eq x)
  have : e - e * indicatorCLM R (S : Set I) * e =
      e.comp (e - (indicatorCLM R (S : Set I)).comp e) := by
    ext x : 1
    simp [hee]
  rw [this]
  exact (ringOpNorm_comp_le _ _).trans_lt hS

/-- **The range of a row-compact idempotent is a direct summand of a finite free module.** For a
row-compact idempotent endomorphism `e` of `C₀(I, R)` there are a finite set `S` of coordinates
and linear maps `f : (S → R) → range e`, `g : range e → (S → R)` with `f ∘ g = id`. -/
theorem IsRowCompact.exists_comp_eq_id_of_isIdempotentElem {e : C₀(I, R) →L[R] C₀(I, R)}
    (hu : e.IsRowCompact) (he : IsIdempotentElem e) :
    ∃ (S : Finset I) (f : (S → R) →ₗ[R] LinearMap.range (e : C₀(I, R) →ₗ[R] C₀(I, R)))
      (g : LinearMap.range (e : C₀(I, R) →ₗ[R] C₀(I, R)) →ₗ[R] S → R), f ∘ₗ g = .id := by
  obtain ⟨S, hS⟩ := hu.exists_ringOpNorm_sub_mul_indicatorCLM_mul_lt_one he
  refine ⟨S, ContinuousLinearMap.exists_comp_eq_id_of_isIdempotentElem
    (c := indicatorCLM R (S : Set I)) he
    (LinearMap.pi fun s : S ↦ ((evalCLM R (s : I) : C₀(I, R) →L[R] R) : C₀(I, R) →ₗ[R] R))
    (Fintype.linearCombination R fun s : S ↦ ZeroAtInftyContinuousMap.single (s : I) (1 : R))
    ?_ hS⟩
  ext x : 1
  simp [Fintype.linearCombination_apply, smul_single_one, indicatorCLM_finset_apply]

/-- **A row-compact idempotent has finitely generated range.** -/
theorem IsRowCompact.finite_range_of_isIdempotentElem {e : C₀(I, R) →L[R] C₀(I, R)}
    (hu : e.IsRowCompact) (he : IsIdempotentElem e) :
    Module.Finite R (LinearMap.range (e : C₀(I, R) →ₗ[R] C₀(I, R))) :=
  have ⟨_, f, g, hfg⟩ := hu.exists_comp_eq_id_of_isIdempotentElem he
  .of_surjective f (LinearMap.surjective_of_comp_eq_id g f hfg)

/-- **A row-compact idempotent has projective range.** -/
theorem IsRowCompact.projective_range_of_isIdempotentElem {e : C₀(I, R) →L[R] C₀(I, R)}
    (hu : e.IsRowCompact) (he : IsIdempotentElem e) :
    Module.Projective R (LinearMap.range (e : C₀(I, R) →ₗ[R] C₀(I, R))) :=
  have ⟨_, f, g, hfg⟩ := hu.exists_comp_eq_id_of_isIdempotentElem he
  .of_split g f hfg

end ContinuousLinearMap
