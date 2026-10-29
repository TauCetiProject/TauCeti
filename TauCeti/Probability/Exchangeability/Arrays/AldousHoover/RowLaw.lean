/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.AldousHoover.Basic
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import TauCeti.Probability.Exchangeability.MixedIID.Basic
public import TauCeti.Probability.Process.Array.AldousHoover.RowLaw
-- Non-public: the canonical conditionally i.i.d. law, the mixture representation and its
-- injectivity are used only inside proofs.
import TauCeti.Probability.Exchangeability.ConditionallyIID.Construct
import TauCeti.Probability.Exchangeability.ConditionallyIID.Map
import TauCeti.Probability.Exchangeability.MixedIID.Mixture
import TauCeti.MeasureTheory.Measure.Mixture.Injective

/-!
# Row directing measures of separate Aldous--Hoover codings

In the separate Aldous--Hoover coding

```text
X i j = g (U, U_row i, U_col j, U_cell i j)
```

the global and column noise, paired with the rows, has the i.i.d. mixture law driven by the random
row law `separateRowLaw g` (`map_arrayRow_separateArray_noiseMeasure`, in
`TauCeti.Probability.Process.Array.AldousHoover.RowLaw`). So the row directing measure of a coded
array is the random probability measure `separateRowLaw g` evaluated at the global and column
noise (`conditionallyIIDWith_arrayRow_separateArray`), and its row mixing law is the law of
`separateRowLaw g` under uniform noise.

Conversely, the law of an array is determined by the mixing law of its rows, and the mixture
determines the mixing law. Hence an array whose rows have a mixing representative `ν` has the law
of the coding `g` exactly when `ν` has the law of `separateRowLaw g`
(`map_eq_map_separateArray_iff`). This reduces the separate Aldous--Hoover representation of an
array to realizing the law of its row directing measure — a random probability measure on paths
whose law is invariant under column permutations — as the law of such a random row law driven by
one global and i.i.d. column variables.

## Main results

* `TauCeti.Probability.AldousHoover.conditionallyIIDWith_arrayRow_separateArray` — the rows of a
  separate coding are conditionally i.i.d. with directing measure the random row law;
* `TauCeti.Probability.AldousHoover.map_eq_map_separateArray_iff` — an array has the law of the
  coding `g` if and only if its row mixing law is that law.

## References

* D. Aldous, ["Representations for partially exchangeable arrays of random variables"]
  (https://doi.org/10.1016/0047-259X(81)90099-3), *Journal of Multivariate Analysis* 11
  (1981), 581--598.
* O. Kallenberg, [*Probabilistic Symmetries and Invariance Principles*]
  (https://doi.org/10.1007/0-387-28836-4), Springer, 2005, Chapter 7.

-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti

namespace Probability

namespace AldousHoover

variable {α : Type*} [MeasurableSpace α]

/-! ## The rows of a separate coding -/

/-- **The rows of a separate Aldous--Hoover coding are conditionally i.i.d.**, with directing
measure the random row law evaluated at the global variable and the column variables. -/
theorem conditionallyIIDWith_arrayRow_separateArray {g : I × I × I × I → α}
    (hg : Measurable g) :
    ConditionallyIIDWith (noiseMeasure Axis (ℕ × ℕ)) (arrayRow (separateArray g))
      fun u => separateRowLaw g (u .global, fun j => u (.vertex .column j)) := by
  have h := conditionallyIIDWith_iidMixtureLaw
    (π := (volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => volume))
    (measurable_separateRowLaw hg)
  rw [← map_arrayRow_separateArray_noiseMeasure hg] at h
  -- Pulling back along the noise map turns the canonical coordinates into the rows of the coding.
  exact h.of_map <| ((measurable_pi_apply _).prodMk
    (Measurable.of_eval fun _ => measurable_pi_apply _)).prodMk <|
      Measurable.of_eval fun i => Measurable.of_eval fun j => by
        simpa only [arrayRow_apply, Function.comp_def] using
          (measurable_pi_apply (i, j)).comp (measurable_separateArray g hg)

/-! ## Codings through the row mixing law -/

/-- **An array has the law of a separate coding exactly when its rows have the coding's mixing
law.** If `ν` is a mixing representative of the rows of `X`, then `X` has the law of the separate
Aldous--Hoover coding through `g` if and only if `ν` has the law of the random row law
`separateRowLaw g` under uniform global and column noise. -/
theorem map_eq_map_separateArray_iff {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α} {ν : Ω → ProbabilityMeasure (ℕ → α)}
    (hν : MixedIIDWith μ (arrayRow X) ν) {g : I × I × I × I → α} (hg : Measurable g) :
    μ.map (fun ω p => X p ω) =
        (noiseMeasure Axis (ℕ × ℕ)).map (fun u p => separateArray g p u) ↔
      μ.map ν =
        ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
          (separateRowLaw g) := by
  have hX : ∀ p, AEMeasurable (X p) μ := fun p => by
    convert (measurable_pi_apply p.2).comp_aemeasurable (hν.aemeasurable p.1) using 1
    funext ω
    simp
  have hU : ∀ p, AEMeasurable (separateArray g p) (noiseMeasure Axis (ℕ × ℕ)) := fun p =>
    (measurable_pi_apply p).comp_aemeasurable (measurable_separateArray g hg).aemeasurable
  -- Both array laws are uncurried row path laws, and both row path laws are i.i.d. mixtures.
  have hpathX := pathLaw_eq_bind_infinitePi_of_mixedIIDWith hν
  have hpathU := pathLaw_eq_bind_infinitePi_of_mixedIIDWith
    (mixedIIDWith_of_conditionallyIIDWith (conditionallyIIDWith_arrayRow_separateArray hg))
  rw [map_separateRowLaw_noiseMeasure hg] at hpathU
  rw [← map_uncurry_pathLaw_arrayRow hX, ← map_uncurry_pathLaw_arrayRow hU, hpathX, hpathU]
  -- Uncurrying is a measurable equivalence, and the mixture determines the mixing law.
  refine ⟨fun h => TauCeti.MeasureTheory.Measure.ext_of_bind_infinitePi_eq
    ((MeasurableEquiv.curry ℕ ℕ α).symm.map_measurableEquiv_injective h), fun h => by rw [h]⟩

end AldousHoover

end Probability

end TauCeti
