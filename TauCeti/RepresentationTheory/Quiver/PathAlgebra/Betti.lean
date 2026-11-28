/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Betti
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedCartanMatrix
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedResolutionClass

/-!
# Betti Poincaré matrix of a finite acyclic path algebra

For a finite acyclic quiver `Q` over a field `k`, the first-arrow resolution
`TauCeti.PathAlgebra.gradedVertexSimpleProjectiveResolution` of each graded vertex simple `Sⱼ` is
a linear (in particular minimal) `TauCeti.GradedProjectiveResolution` of length one. Consequently,
the Betti Poincaré matrix of any minimal resolutions of the graded vertex simples in the graded
vertex-projective basis `[kQ eᵢ]` is `B(q, t) = I + q t Aᵀ`, where the `(i, j)` entry of `A` counts
arrows `i ⟶ j`. Setting `t = -1` recovers `I - q Aᵀ`, the inverse of the graded Cartan matrix
`C(q) = (I - q Aᵀ)⁻¹`.

## Main results

* `TauCeti.PathAlgebra.bettiPoincarePowerSeriesMatrix_gradedVertexSimple` and
  `TauCeti.PathAlgebra.bettiPoincarePowerSeriesMatrix_gradedVertexSimple_apply`: the Betti
  Poincaré matrix of any minimal resolutions of the graded vertex simples of a finite acyclic
  path algebra is `I + q t Aᵀ`, with `(i, j)` entry `δᵢⱼ + |j ⟶ i| q t`.
* `TauCeti.PathAlgebra.bettiPoincarePowerSeriesMatrix_map_eval_neg_one_trunc_two`: evaluating
  the truncated Betti Poincaré matrix at `t = -1` gives `1 - q Aᵀ`.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Sections 2--3, for the first-arrow resolution of vertex simples.
* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Section 1.2, for linear resolutions and Koszulity of path
  algebras.
-/

public section

noncomputable section

namespace TauCeti.PathAlgebra

open CategoryTheory CategoryTheory.Limits LaurentPolynomial
open scoped Matrix

universe u v w

variable {k : Type w} {Q : Type u} [Quiver.{v} Q]

/-! ### Betti Poincaré matrix of a finite acyclic path algebra -/

section BettiMatrix

variable (k Q) [Field k] [Finite Q] [FiniteDimensional k (pathAlgebra k Q)]

private theorem coeff_zero_bettiPoincarePowerSeries_gradedVertexSimpleProjectiveResolution
    [DecidableEq Q] (i j : Q) [Finite ((a : Q) × (j ⟶ a))] :
    PowerSeries.coeff 0
        ((gradedVertexSimpleProjectiveResolution k Q j).bettiPoincarePowerSeries
          (gradedVertexProjectiveClassBasis k Q) i) =
      if i = j then 1 else 0 := by
  let _ := integerGradedAlgebra k Q
  let _ := Fintype.ofFinite Q
  let r₀ := gradedVertexSimpleProjectiveResolution k Q j
  rw [GradedProjectiveResolution.coeff_bettiPoincarePowerSeries]
  have hterm :
      LaurentK0.of.{max u v w}
          (gradedFiniteProjectiveModulesExactStructure (integerGrade k Q))
          (r₀.finiteProjectiveTerm 0) =
        gradedVertexProjectiveClassBasis k Q j := by
    rw [gradedVertexProjectiveClassBasis_apply, gradedVertexProjectiveClass_eq]
    congr 1
    exact ObjectProperty.FullSubcategory.ext (by simp [r₀])
  rw [hterm, Module.Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

private theorem coeff_one_bettiPoincarePowerSeries_gradedVertexSimpleProjectiveResolution
    (i j : Q) [Finite ((a : Q) × (j ⟶ a))] :
    PowerSeries.coeff 1
        ((gradedVertexSimpleProjectiveResolution k Q j).bettiPoincarePowerSeries
          (gradedVertexProjectiveClassBasis k Q) i) =
      (Nat.card (j ⟶ i) : LaurentPolynomial ℤ) * T 1 := by
  classical
  let _ := integerGradedAlgebra k Q
  let _ := Fintype.ofFinite Q
  let r₀ := gradedVertexSimpleProjectiveResolution k Q j
  rw [GradedProjectiveResolution.coeff_bettiPoincarePowerSeries]
  have hterm :
      r₀.finiteProjectiveTerm 1 =
        ⟨gradedArrowSum k Q j, gradedFiniteProjectiveModules_gradedArrowSum k Q j⟩ :=
    ObjectProperty.FullSubcategory.ext (by simp [r₀])
  rw [hterm, laurentK0_gradedArrowSum_eq_sum k Q j]
  simp_rw [← gradedVertexProjectiveClassBasis_apply k Q]
  rw [Module.Basis.repr_sum_self]

/-- Entrywise form of `TauCeti.PathAlgebra.bettiPoincarePowerSeriesMatrix_gradedVertexSimple`: in
the graded vertex-projective basis `[kQ eᵢ]`, the `(i, j)` entry of the Betti Poincaré matrix of
any minimal graded projective resolutions `r` of the graded vertex simples `Sⱼ` is
`δᵢⱼ + |j ⟶ i| q t`. -/
theorem bettiPoincarePowerSeriesMatrix_gradedVertexSimple_apply [DecidableEq Q]
    (r : ∀ l, GradedProjectiveResolution.{w, max u v w, max u v w, max u v w}
      (integerGrade k Q) (gradedVertexSimple k Q l).grading)
    [∀ l n, Module.Finite (pathAlgebra k Q) ((r l).X n)]
    (hr : ∀ l, (r l).IsMinimal) (i j : Q) :
    bettiPoincarePowerSeriesMatrix r (gradedVertexProjectiveClassBasis k Q) i j =
      (if i = j then 1 else 0) +
        PowerSeries.C ((Nat.card (j ⟶ i) : LaurentPolynomial ℤ) * T 1) * PowerSeries.X := by
  let _ := integerGradedAlgebra k Q
  let _ := Fintype.ofFinite Q
  let _ (a b : Q) : Finite (a ⟶ b) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance a b
  rw [bettiPoincarePowerSeriesMatrix_eq_of_nonneg (gradedVertexProjectiveClassBasis k Q)
    (fun _ hp => integerGrade_eq_bot_of_neg k Q hp) hr
    (fun l => isMinimal_gradedVertexSimpleProjectiveResolution k Q l),
    bettiPoincarePowerSeriesMatrix_apply,
    ← (gradedVertexSimpleProjectiveResolution k Q j).trunc_bettiPoincarePowerSeries
      (gradedVertexProjectiveClassBasis k Q) i (N := 1)
      fun n hn => subsingleton_gradedVertexSimpleProjectiveResolution_X_of_two_le k Q j hn,
    PowerSeries.trunc_succ _ 1, PowerSeries.trunc_succ _ 0, PowerSeries.trunc_zero', zero_add,
    coeff_zero_bettiPoincarePowerSeries_gradedVertexSimpleProjectiveResolution,
    coeff_one_bettiPoincarePowerSeries_gradedVertexSimpleProjectiveResolution]
  by_cases hij : i = j <;>
    simp [hij, PowerSeries.monomial_eq_C_mul_X_pow, -map_mul, -map_natCast]

/-- **The Betti Poincaré matrix of a finite acyclic path algebra is `I + q t Aᵀ`.** In the graded
vertex-projective basis `[kQ eᵢ]`, the Betti Poincaré matrix of any minimal graded projective
resolutions `r` of the graded vertex simples `Sⱼ` is `1 + (q t) • Aᵀ`, where the `(i, j)` entry
of `A` counts arrows `i ⟶ j`. -/
theorem bettiPoincarePowerSeriesMatrix_gradedVertexSimple [DecidableEq Q]
    (r : ∀ l, GradedProjectiveResolution.{w, max u v w, max u v w, max u v w}
      (integerGrade k Q) (gradedVertexSimple k Q l).grading)
    [∀ l n, Module.Finite (pathAlgebra k Q) ((r l).X n)]
    (hr : ∀ l, (r l).IsMinimal) :
    bettiPoincarePowerSeriesMatrix r (gradedVertexProjectiveClassBasis k Q) =
      1 + (PowerSeries.C (T 1 : LaurentPolynomial ℤ) * PowerSeries.X) •
        (Matrix.of fun i j : Q => (Nat.card (i ⟶ j) : PowerSeries (LaurentPolynomial ℤ)))ᵀ := by
  refine Matrix.ext fun i j => ?_
  rw [bettiPoincarePowerSeriesMatrix_gradedVertexSimple_apply k Q r hr i j, Matrix.add_apply,
    Matrix.one_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul,
    ← map_natCast PowerSeries.C, mul_right_comm, ← map_mul, mul_comm (T 1)]

/-- **Evaluation of the Betti Poincaré matrix of a finite acyclic path algebra at `t = -1`**
gives `1 - q Aᵀ`, the left and right inverse of the graded Cartan matrix `C(q)`. -/
theorem bettiPoincarePowerSeriesMatrix_map_eval_neg_one_trunc_two [DecidableEq Q]
    (r : ∀ l, GradedProjectiveResolution.{w, max u v w, max u v w, max u v w}
      (integerGrade k Q) (gradedVertexSimple k Q l).grading)
    [∀ l n, Module.Finite (pathAlgebra k Q) ((r l).X n)]
    (hr : ∀ l, (r l).IsMinimal) :
    (bettiPoincarePowerSeriesMatrix r (gradedVertexProjectiveClassBasis k Q)).map
        (fun P => (PowerSeries.trunc 2 P).eval (-1)) =
      1 - (T 1 : LaurentPolynomial ℤ) •
        (Matrix.of fun i j : Q => (Nat.card (i ⟶ j) : LaurentPolynomial ℤ))ᵀ := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, bettiPoincarePowerSeriesMatrix_gradedVertexSimple_apply k Q r hr i j,
    map_add]
  by_cases hij : i = j <;>
    simp [hij, PowerSeries.trunc_one, PowerSeries.trunc_C_mul, PowerSeries.trunc_X,
      Polynomial.eval_X, sub_eq_add_neg, -map_mul, -map_natCast]

end BettiMatrix

end TauCeti.PathAlgebra
