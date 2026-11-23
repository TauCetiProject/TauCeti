/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Beurling.Basic
public import TauCeti.MeasureTheory.Function.Lp.Basic
public import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional

/-!
# Beurling transformation in finite-dimensional complex norms

For every finite-dimensional complex normed target and every finite `1 < p < ∞`,
`TauCeti.beurlingL` is a bounded complex-linear operator on whole-plane `Lᵖ` with the
original target norm. Its scalar coordinates are transformed by the scalar Beurling operator.
The construction is independent of the finite basis and commutes with constant complex-linear
coefficient maps.

## Main declarations

* `beurlingWithBasis`, `beurlingWithBasis_eq`: reconstruction in any finite complex basis.
* `beurlingL`, `beurling_eq_withBasis`: the intrinsic operator and its basis formulas.
* `functional_beurling`, `beurling_naturality`: compatibility with scalar functionals and
  complex-linear coefficient maps.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.2.
-/

public noncomputable section

open MeasureTheory Complex Metric Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

section Finite

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℂ F] in
/-- Scalar Beurling transformation followed by finite reconstruction in the original norm. -/
def beurlingWithBasis (b : Module.Basis ι ℂ F) (hp : 1 < p) (hp_top : p ≠ ∞) :
    Lp F p (volume : Measure ℂ) →L[ℂ] Lp F p (volume : Measure ℂ) := by
  letI := b.finiteDimensional_of_finite
  exact ∑ i, ((ContinuousLinearMap.toSpanSingleton ℂ (b i)).compLpL p volume).comp
    ((beurlingLp (F := ℂ) p hp hp_top).comp (((b.coord i).toContinuousLinearMap).compLpL p volume))

omit [FiniteDimensional ℂ F] in
/-- Every scalar functional intertwines the finite reconstruction with scalar Beurling. -/
theorem functional_beurlingWithBasis (b : Module.Basis ι ℂ F)
    (hp : 1 < p) (hp_top : p ≠ ∞) (ℓ : F →L[ℂ] ℂ)
    (u : Lp F p (volume : Measure ℂ)) :
    ℓ.compLpL p volume (beurlingWithBasis b hp hp_top u) =
      beurlingLp (F := ℂ) p hp hp_top (ℓ.compLpL p volume u) := by
  classical
  let : FiniteDimensional ℂ F := b.finiteDimensional_of_finite
  have h := congrArg (fun v ↦ ℓ.compLpL p volume v) (eq_sum_basis_compLpL b u)
  simp only [map_sum, ContinuousLinearMap.compLpL_toSpanSingleton] at h
  simp only [beurlingWithBasis, sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    ContinuousLinearMap.compLpL_toSpanSingleton]
  rw [h, map_sum]
  simp only [map_smul]

/-- The finite sum giving the original-norm Beurling representative. -/
theorem coe_beurlingWithBasis (b : Module.Basis ι ℂ F) (hp : 1 < p) (hp_top : p ≠ ∞)
    (u : Lp F p (volume : Measure ℂ)) :
    beurlingWithBasis b hp hp_top u =ᵐ[volume]
      fun w ↦ ∑ i, (beurlingLp (F := ℂ) p hp hp_top
        (((b.coord i).toContinuousLinearMap).compLpL p volume u) w) • b i := by
  classical
  simp only [beurlingWithBasis, sum_apply, ContinuousLinearMap.comp_apply]
  have hi (i : ι) := (ContinuousLinearMap.toSpanSingleton ℂ (b i)).coeFn_compLpL
    (beurlingLp (F := ℂ) p hp hp_top (((b.coord i).toContinuousLinearMap).compLpL p volume u))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦
    (ContinuousLinearMap.toSpanSingleton ℂ (b i)).compLpL p volume
      (beurlingLp (F := ℂ) p hp hp_top (((b.coord i).toContinuousLinearMap).compLpL p volume u))),
    ae_all_iff.mpr hi] with w hsum hcoords
  simp only [hsum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [ContinuousLinearMap.toSpanSingleton_apply] using hcoords i

omit [FiniteDimensional ℂ F] in
/-- The finite-coordinate construction does not depend on the chosen basis. -/
theorem beurlingWithBasis_eq {κ : Type*} [Fintype κ]
    (b : Module.Basis ι ℂ F) (d : Module.Basis κ ℂ F) (hp : 1 < p) (hp_top : p ≠ ∞) :
    beurlingWithBasis b hp hp_top = beurlingWithBasis d hp hp_top := by
  classical
  let : FiniteDimensional ℂ F := b.finiteDimensional_of_finite
  ext1 u
  rw [eq_sum_basis_compLpL d (beurlingWithBasis b hp hp_top u)]
  simp_rw [functional_beurlingWithBasis b hp hp_top]
  simp only [beurlingWithBasis, sum_apply, ContinuousLinearMap.comp_apply]

/-- The global Beurling map on the original finite-dimensional complex normed target. -/
def beurlingL (hp : 1 < p) (hp_top : p ≠ ∞) :
    Lp F p (volume : Measure ℂ) →L[ℂ] Lp F p (volume : Measure ℂ) :=
  beurlingWithBasis (Module.finBasis ℂ F) hp hp_top

/-- The intrinsic original-norm operator has the same reconstruction in every complex basis. -/
theorem beurling_eq_withBasis (b : Module.Basis ι ℂ F) (hp : 1 < p) (hp_top : p ≠ ∞) :
    beurlingL (F := F) hp hp_top = beurlingWithBasis b hp hp_top := by
  rw [beurlingL]
  exact beurlingWithBasis_eq _ b hp hp_top

/-- Every scalar functional intertwines the intrinsic vector and scalar Beurling maps. -/
theorem functional_beurling (hp : 1 < p) (hp_top : p ≠ ∞) (ℓ : F →L[ℂ] ℂ)
    (u : Lp F p (volume : Measure ℂ)) :
    ℓ.compLpL p volume (beurlingL hp hp_top u) =
      beurlingLp (F := ℂ) p hp hp_top (ℓ.compLpL p volume u) := by
  rw [beurlingL]
  exact functional_beurlingWithBasis _ hp hp_top ℓ u

/-- The original-norm Beurling map is natural for complex-linear coefficient maps. -/
theorem beurling_naturality {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] (hp : 1 < p) (hp_top : p ≠ ∞) (L : F →L[ℂ] G)
    (u : Lp F p (volume : Measure ℂ)) :
    L.compLpL p volume (beurlingL hp hp_top u) =
      beurlingL hp hp_top (L.compLpL p volume u) := by
  classical
  let d := Module.finBasis ℂ G
  rw [eq_sum_basis_compLpL d (L.compLpL p volume (beurlingL hp hp_top u)),
    eq_sum_basis_compLpL d (beurlingL hp hp_top (L.compLpL p volume u))]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [ContinuousLinearMap.compLpL_compLpL, functional_beurling,
    ← ContinuousLinearMap.compLpL_compLpL, ← functional_beurling]

end Finite

end TauCeti
