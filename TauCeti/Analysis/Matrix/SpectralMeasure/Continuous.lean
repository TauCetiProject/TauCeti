/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Topology.Instances.Matrix
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
The empirical-measure map descends continuously from ordered tuples to that symmetric power,
using `TauCeti.Probability.continuous_empiricalMeasureOfFintype`. Thus no continuous ordering of
complex roots is required, and algebraic multiplicities are preserved throughout.
-/

public section

open MeasureTheory Topology TauCeti.Probability

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The empirical complex eigenvalue measure is continuous, including at matrices with
repeated characteristic roots. -/
@[continuity, fun_prop]
theorem continuous_eigenvalueMeasure :
    Continuous (eigenvalueMeasure : Matrix n n ℂ → ProbabilityMeasure ℂ) := by
  classical
  have hnonempty (s : Sym ℂ (Fintype.card n)) : Nonempty (s : Multiset ℂ) :=
    Fintype.card_pos_iff.mp (by
      simpa only [Multiset.card_coe, Sym.card_coe] using Fintype.card_pos (α := n))
  let μ (s : Sym ℂ (Fintype.card n)) : ProbabilityMeasure ℂ :=
    letI := hnonempty s
    empiricalMeasureOfFintype fun z : (s : Multiset ℂ) => (z : ℂ)
  have hμ : Continuous μ := by
    apply Sym.continuous_iff_comp_ofFn.mpr
    have hcomp : μ ∘ Sym.ofFn =
        (empiricalMeasureOfFintype : (Fin (Fintype.card n) → ℂ) → ProbabilityMeasure ℂ) := by
      funext a
      apply empiricalMeasureOfFintype_eq_of_map_univ_val_eq
      rw [Multiset.map_univ_coe, Sym.coe_ofFn, Fin.univ_val_map]
    rw [hcomp]
    exact continuous_empiricalMeasureOfFintype
  have hroots (A : Matrix n n ℂ) :
      (((TauCeti.Sym.coeffHomeomorph ℂ (Fintype.card n)).symm
        (fun i => A.charpoly.coeff i) : Sym ℂ (Fintype.card n)) : Multiset ℂ) =
        A.charpoly.roots := by
    rw [TauCeti.Sym.coeffHomeomorph_symm_apply,
      TauCeti.Sym.coeffEquiv_symm_coeff_of_monic A.charpoly_monic (charpoly_natDegree_eq_dim A)]
  have hmeasure : eigenvalueMeasure = μ ∘ fun A : Matrix n n ℂ =>
      (TauCeti.Sym.coeffHomeomorph ℂ (Fintype.card n)).symm
        (fun i => A.charpoly.coeff i) := by
    funext A
    rw [eigenvalueMeasure_def]
    apply empiricalMeasureOfFintype_eq_of_map_univ_val_eq
    simp only [Multiset.map_univ_coe, hroots]
  rw [hmeasure]
  exact hμ.comp ((TauCeti.Sym.coeffHomeomorph ℂ (Fintype.card n)).symm.continuous.comp
    (continuous_pi fun i => continuous_charpoly_coeff i))

/-- A complex matrix's empirical eigenvalue measure is measurable for the entrywise
measurable structure. -/
@[fun_prop]
theorem measurable_eigenvalueMeasure :
    Measurable (eigenvalueMeasure : Matrix n n ℂ → ProbabilityMeasure ℂ) :=
  continuous_eigenvalueMeasure.measurable_probabilityMeasure

end Matrix
