/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Analysis.Matrix.Charpoly
public import TauCeti.Analysis.Polynomial.SymmetricPower
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Borel

/-!
# Continuity of the complex eigenvalue measure

The empirical measure of the characteristic roots of a complex matrix depends continuously on
the matrix, for the weak topology on probability measures. In particular it is measurable for
the entrywise measurable structure on matrices. This allows a random non-Hermitian matrix to
be treated as a random probability measure, even when its eigenvalues collide.

The construction follows `TauCeti.Sym.coeffHomeomorph`: the lower coefficients of a monic
polynomial determine its root multiset continuously as a point of the symmetric power.
A continuous test function has a continuous sum on that symmetric power, since its pullback
to ordered tuples is a finite sum. Thus no continuous ordering of complex roots is required,
and algebraic multiplicities are preserved throughout.
-/

public section

open MeasureTheory Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The empirical complex eigenvalue measure is continuous, including at matrices with
repeated characteristic roots. -/
@[continuity, fun_prop]
theorem continuous_eigenvalueMeasure :
    Continuous (eigenvalueMeasure : Matrix n n ℂ → ProbabilityMeasure ℂ) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  have hsum : Continuous (fun s : Sym ℂ (Fintype.card n) =>
      ((s : Multiset ℂ).map f).sum) := by
    apply TauCeti.Sym.continuous_iff_comp_ofFn.mpr
    simpa only [Function.comp_def, TauCeti.Sym.coe_ofFn, Multiset.map_coe,
      Multiset.sum_coe, List.map_ofFn, List.sum_ofFn, Function.comp_apply] using
      (continuous_finsetSum (Finset.univ : Finset (Fin (Fintype.card n)))
        fun i _ => f.continuous.comp (continuous_apply i))
  have hroots (A : Matrix n n ℂ) :
      (((TauCeti.Sym.coeffHomeomorph ℂ (Fintype.card n)).symm
        (fun i => A.charpoly.coeff i) : Sym ℂ (Fintype.card n)) : Multiset ℂ) =
        A.charpoly.roots := by
    simp only [TauCeti.Sym.coeffHomeomorph_symm_apply, TauCeti.Sym.coeffEquiv_symm_apply]
    rw [TauCeti.Polynomial.monicOfCoeff_coeff A.charpoly_monic (charpoly_natDegree_eq_dim A)]
  simp_rw [integral_eigenvalueMeasure, ← hroots]
  exact (hsum.comp ((TauCeti.Sym.coeffHomeomorph ℂ (Fintype.card n)).symm.continuous.comp
    (continuous_pi fun i => continuous_charpoly_coeff i))).fun_const_smul _

/-- A complex matrix's empirical eigenvalue measure is measurable for the entrywise
measurable structure. -/
@[fun_prop]
theorem measurable_eigenvalueMeasure :
    Measurable (eigenvalueMeasure : Matrix n n ℂ → ProbabilityMeasure ℂ) :=
  continuous_eigenvalueMeasure.measurable_probabilityMeasure

end Matrix
