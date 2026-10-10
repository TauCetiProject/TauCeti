/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Polarised diagonal integrals

The bounded Borel functional calculus of a normal operator is built by
*polarising* the diagonal integrals of the previous module.  For a symbol
`f` and vectors `ψ, ξ` set

`pair f ψ ξ = ¼ Σ_{k<4} iᵏ ∫ f ∂(diagMeasure (ξ + iᵏ • ψ))`.

For **continuous** `f` this is exactly `⟪ψ, cfcHom f ξ⟫` (`pair_of_continuous`),
by the polarisation identity for the sesquilinear form of a bounded operator.
For a general bounded Borel `f` it is the definition of what
`⟪ψ, borelCalculus f ξ⟫` *ought* to be, and the next module shows it really is
the matrix element of an operator.

## The transport principle

Every algebraic identity satisfied by `pair` on continuous symbols transports to
bounded Borel symbols by a single mechanism, isolated here as
`norm_pair_sub_pair_le`: the difference of two `pair`s at the same pair of
vectors is bounded by the `L¹` distance of the symbols measured against *any*
finite measure dominating the four diagonal measures involved.  Since an
identity only ever involves finitely many vectors, one takes the (finite) sum of
all the diagonal measures in sight and approximates once, in that one `L¹`.

This is what makes the construction short: no monotone-class induction, no
Jordan–von Neumann argument recovering additivity from the parallelogram law,
and no operator-monotone limits.

## Sources

The construction is the classical one for the bounded Borel functional calculus of
a normal operator: represent the diagonal functionals by measures
(Riesz--Markov--Kakutani), polarise, and extend from continuous to bounded Borel
symbols by approximation in `L¹` of the diagonal measures.  It follows the standard
textbook treatment of the spectral theorem for normal operators (Rudin,
*Functional Analysis*; Conway, *A Course in Functional Analysis*) rather than any
one source's proof.

The route was chosen against the Spectra library's Herglotz/Poisson construction;
the Spectra-removal plan records that comparison, and
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean` carries
the provenance of the route itself.

## Provenance

*New*; see `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean`
for the provenance of the route as a whole.
-/

public section

open scoped InnerProductSpace ENNReal CompactlySupported
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

section PolarizationIdentity

omit [CompleteSpace H] in
/-- **Polarisation for a bounded operator.**  The sesquilinear form of `T` is
recovered from its quadratic form by the four-term complex polarisation sum. -/
theorem inner_polarization (T : H →L[ℂ] H) (ψ ξ : H) :
    (1 / 4 : ℂ) *
        (⟪ξ + ψ, T (ξ + ψ)⟫_ℂ
          + Complex.I * ⟪ξ + Complex.I • ψ, T (ξ + Complex.I • ψ)⟫_ℂ
          - ⟪ξ - ψ, T (ξ - ψ)⟫_ℂ
          - Complex.I * ⟪ξ - Complex.I • ψ, T (ξ - Complex.I • ψ)⟫_ℂ)
      = ⟪ψ, T ξ⟫_ℂ := by
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

end PolarizationIdentity

section Pair

variable (ha : IsStarNormal a)

/-- The **polarised diagonal integral** of a symbol at a pair of vectors.  For
continuous symbols this is `⟪ψ, cfcHom f ξ⟫`; it is the blueprint for the
matrix elements of the bounded Borel calculus. -/
noncomputable def pair (f : spectrum ℂ a → ℂ) (ψ ξ : H) : ℂ :=
  (1 / 4 : ℂ) *
    ((∫ x, f x ∂(diagMeasure ha (ξ + ψ)))
      + Complex.I * (∫ x, f x ∂(diagMeasure ha (ξ + Complex.I • ψ)))
      - (∫ x, f x ∂(diagMeasure ha (ξ - ψ)))
      - Complex.I * (∫ x, f x ∂(diagMeasure ha (ξ - Complex.I • ψ))))

/-- Rewrite form of `pair`, so call sites need not unfold the definition.

Added 2026-07-30: `BorelCalculus/Operator` was doing `rw [pair]`, which requires the
body to be exposed. Tau Ceti's `api-design` rubric asks for the lemma instead. -/
theorem pair_def (f : spectrum ℂ a → ℂ) (ψ ξ : H) :
    pair ha f ψ ξ = (1 / 4 : ℂ) *
      ((∫ x, f x ∂(diagMeasure ha (ξ + ψ)))
        + Complex.I * (∫ x, f x ∂(diagMeasure ha (ξ + Complex.I • ψ)))
        - (∫ x, f x ∂(diagMeasure ha (ξ - ψ)))
        - Complex.I * (∫ x, f x ∂(diagMeasure ha (ξ - Complex.I • ψ)))) := (rfl)

/-- On continuous symbols the polarised diagonal integral is the matrix element
of the continuous functional calculus. -/
theorem pair_of_continuous (f : C(spectrum ℂ a, ℂ)) (ψ ξ : H) :
    pair ha (fun x => f x) ψ ξ = ⟪ψ, cfcHom ha f ξ⟫_ℂ := by
  rw [pair, integral_diagMeasure, integral_diagMeasure, integral_diagMeasure,
    integral_diagMeasure]
  exact inner_polarization (cfcHom ha f) ψ ξ

omit [CompleteSpace H] in
/-- Two symbols close in `L¹` of a dominating measure have close integrals
against the dominated one. -/
theorem norm_integral_sub_integral_le {f g : spectrum ℂ a → ℂ}
    {μ ν : Measure (spectrum ℂ a)} (hdom : μ ≤ ν)
    (hf : Integrable f ν) (hg : Integrable g ν) :
    ‖(∫ x, f x ∂μ) - (∫ x, g x ∂μ)‖ ≤ ∫ x, ‖f x - g x‖ ∂ν := by
  have hfμ : Integrable f μ := hf.mono_measure hdom
  have hgμ : Integrable g μ := hg.mono_measure hdom
  calc ‖(∫ x, f x ∂μ) - (∫ x, g x ∂μ)‖
      = ‖∫ x, (f x - g x) ∂μ‖ := by rw [integral_sub hfμ hgμ]
    _ ≤ ∫ x, ‖f x - g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x - g x‖ ∂ν :=
        integral_mono_measure hdom (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (hf.sub hg).norm

/-- The four diagonal measures entering `pair ha f ψ ξ`. -/
noncomputable def pairVectors (ψ ξ : H) : Fin 4 → H :=
  ![ξ + ψ, ξ + Complex.I • ψ, ξ - ψ, ξ - Complex.I • ψ]

/-- The `L¹` transport bound: two symbols that are close in `L¹` of a measure
dominating the four diagonal measures have close polarised integrals. -/
theorem norm_pair_sub_pair_le {f g : spectrum ℂ a → ℂ}
    (ν : Measure (spectrum ℂ a)) (ψ ξ : H)
    (hdom : ∀ i : Fin 4, diagMeasure ha (pairVectors ψ ξ i) ≤ ν)
    (hf : Integrable f ν) (hg : Integrable g ν) :
    ‖pair ha f ψ ξ - pair ha g ψ ξ‖ ≤ ∫ x, ‖f x - g x‖ ∂ν := by
  set I := ∫ x, ‖f x - g x‖ ∂ν with hI
  have hInn : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  -- the four polarization coordinates.  Naming them is the whole point: every step below
  -- is a triangle inequality on `d 0 + i · d 1 - d 2 - i · d 3`, which is unreadable while
  -- each `d i` is spelled out as a difference of two integrals against a diagonal measure.
  set d : Fin 4 → ℂ := fun i =>
    (∫ x, f x ∂(diagMeasure ha (pairVectors ψ ξ i)))
      - (∫ x, g x ∂(diagMeasure ha (pairVectors ψ ξ i))) with hd
  have key : ∀ i : Fin 4, ‖d i‖ ≤ I := by
    intro i
    set μ := diagMeasure ha (pairVectors ψ ξ i) with hμ
    have hfμ : Integrable f μ := hf.mono_measure (hdom i)
    have hgμ : Integrable g μ := hg.mono_measure (hdom i)
    calc ‖d i‖ = ‖∫ x, (f x - g x) ∂μ‖ := by rw [hd, integral_sub hfμ hgμ]
      _ ≤ ∫ x, ‖f x - g x‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ I :=
          integral_mono_measure (hdom i) (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (hf.sub hg).norm
  have hexp : pair ha f ψ ξ - pair ha g ψ ξ =
      (1 / 4 : ℂ) * (d 0 + Complex.I * d 1 - d 2 - Complex.I * d 3) := by
    simp only [hd, pair, pairVectors, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring
  have hsum : ‖d 0 + Complex.I * d 1 - d 2 - Complex.I * d 3‖ ≤ 4 * I := by
    have h0 := key 0
    have h2 := key 2
    have e1 : ‖Complex.I * d 1‖ ≤ I := by
      rw [norm_mul, Complex.norm_I, one_mul]; exact key 1
    have e3 : ‖Complex.I * d 3‖ ≤ I := by
      rw [norm_mul, Complex.norm_I, one_mul]; exact key 3
    calc ‖d 0 + Complex.I * d 1 - d 2 - Complex.I * d 3‖
        ≤ ‖d 0 + Complex.I * d 1 - d 2‖ + ‖Complex.I * d 3‖ := norm_sub_le _ _
      _ ≤ (‖d 0 + Complex.I * d 1‖ + ‖d 2‖) + I := by gcongr; exact norm_sub_le _ _
      _ ≤ ((‖d 0‖ + ‖Complex.I * d 1‖) + I) + I := by gcongr; exact norm_add_le _ _
      _ ≤ ((I + I) + I) + I := by gcongr
      _ = 4 * I := by ring
  rw [hexp, norm_mul]
  have hquarter : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [hquarter]
  calc 1 / 4 * _ ≤ 1 / 4 * (4 * I) := by gcongr
    _ = I := by ring

end Pair

section Approximation

/-- Every `L¹` symbol on the spectrum is `L¹`-approximable by continuous ones:
the spectrum is a compact metric space, so finite measures on it are weakly
regular. -/
theorem exists_continuous_integral_norm_sub_le (ν : Measure (spectrum ℂ a))
    [IsFiniteMeasure ν] {f : spectrum ℂ a → ℂ} (hf : Integrable f ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(spectrum ℂ a, ℂ), Integrable (fun x => g x) ν ∧ ∫ x, ‖f x - g x‖ ∂ν ≤ ε := by
  have hmem : MemLp f 1 ν := memLp_one_iff_integrable.mpr hf
  obtain ⟨g, hgle, hgmem⟩ :=
    hmem.exists_boundedContinuous_eLpNorm_sub_le (p := 1) (by simp)
      (ε := ENNReal.ofReal ε) (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hε)
  have hgint : Integrable (fun x => g x) ν := memLp_one_iff_integrable.mp hgmem
  refine ⟨g.toContinuousMap, hgint, ?_⟩
  -- names the application so the norm bound applies to it directly.
  change (∫ x, ‖f x - g x‖ ∂ν) ≤ ε
  have hint : ∫ x, ‖f x - g x‖ ∂ν = (eLpNorm (f - ⇑g) 1 ν).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      integral_norm_eq_lintegral_enorm (μ := ν) (f := fun x => f x - g x)
        (hf.sub hgint).aestronglyMeasurable]
    · rfl
    · simpa only [Pi.sub_apply] using (hf.sub hgint).aestronglyMeasurable
  rw [hint]
  calc (eLpNorm (f - ⇑g) 1 ν).toReal ≤ (ENNReal.ofReal ε).toReal := by
        apply ENNReal.toReal_mono _ hgle
        simp
    _ = ε := ENNReal.toReal_ofReal hε.le

end Approximation

section SumMeasure

variable (ha : IsStarNormal a)

/-- A finite sum of diagonal measures is finite. -/
theorem isFiniteMeasure_sum_diagMeasure {ι : Type*} [Fintype ι] (v : ι → H) :
    IsFiniteMeasure (∑ j, diagMeasure ha (v j)) := by
  refine ⟨?_⟩
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  exact ENNReal.sum_lt_top.mpr fun j _ => measure_lt_top _ _

/-- Each summand of a finite sum of diagonal measures is dominated by the sum. -/
theorem diagMeasure_le_sum {ι : Type*} [Fintype ι] (v : ι → H) (i : ι) :
    diagMeasure ha (v i) ≤ ∑ j, diagMeasure ha (v j) :=
  Finset.single_le_sum (f := fun j => diagMeasure ha (v j)) (fun _ _ => Measure.zero_le _)
    (Finset.mem_univ i)

end SumMeasure

end BorelCalculus
end TauCeti
