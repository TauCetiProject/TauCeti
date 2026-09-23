/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.AldousHoover.Basic
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import TauCeti.Probability.Exchangeability.MixedIID.Basic
-- Non-public: the canonical conditionally i.i.d. law, the mixture representation and its
-- injectivity, and the splitting of the noise are used only inside proofs.
import TauCeti.Probability.Exchangeability.ConditionallyIID.Congr
import TauCeti.Probability.Exchangeability.ConditionallyIID.Construct
import TauCeti.Probability.Exchangeability.ConditionallyIID.Map
import TauCeti.Probability.Exchangeability.MixedIID.Mixture
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.MeasureTheory.Measure.MixtureInjective
import TauCeti.Probability.ProductMeasure

/-!
# The random row law of a separate Aldous--Hoover coding

In the separate Aldous--Hoover coding

```text
X i j = g (U, U_row i, U_col j, U_cell i j)
```

the global variable `U` and the column variables `U_col j` are shared by all rows, while each row
`i` reads its own row variable and its own cells. Conditionally on `z = (U, (U_col j)ⱼ)`, the rows
are therefore i.i.d., each distributed as

```text
separateRowLaw g z = Law (j ↦ g (z.1, V, z.2 j, W j)),
```

for a uniform `V` and an independent i.i.d. uniform sequence `W`. So the row directing measure of
a coded array is the random probability measure `separateRowLaw g` evaluated at the global and
column noise (`conditionallyIIDWith_arrayRow_separateArray`), and its row mixing law is the law of
`separateRowLaw g` under uniform noise.

Conversely, the law of an array is determined by the mixing law of its rows, and the mixture
determines the mixing law. Hence an array whose rows have a mixing representative `ν` has the law
of the coding `g` exactly when `ν` has the law of `separateRowLaw g`
(`map_eq_map_separateArray_iff`). This reduces the separate Aldous--Hoover representation of an
array to realizing the law of its row directing measure — a random probability measure on paths
whose law is invariant under column permutations — as the law of such a random row law driven by
one global and i.i.d. column variables.

## Main definitions

* `TauCeti.Probability.AldousHoover.separateRowLaw` — the law of one row of a separate coding given
  its global and column noise.

## Main results

* `TauCeti.Probability.AldousHoover.conditionallyIIDWith_arrayRow_separateArray` — the rows of a
  separate coding are conditionally i.i.d. with directing measure the random row law;
* `TauCeti.Probability.AldousHoover.map_separateRowLaw_noiseMeasure` — its law is the law of
  `separateRowLaw g` under uniform noise;
* `TauCeti.Probability.AldousHoover.separateRowLaw_colReindex` — permuting columns reindexes
  the row law;
* `TauCeti.Probability.AldousHoover.map_separateRowLaw_colReindex` — the row mixing law is
  invariant under column permutations;
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

/-! ## The random row law -/

/-- The row of a separate coding read from the global-and-column noise `z` and the row noise `r`
(the row variable and the cells of the row). -/
private theorem measurable_separateRow {g : I × I × I × I → α} (hg : Measurable g) :
    Measurable (Function.uncurry fun (z r : I × (ℕ → I)) (j : ℕ) =>
      g (z.1, r.1, z.2 j, r.2 j)) :=
  Measurable.of_eval fun j => hg.comp <|
    (measurable_fst.comp measurable_fst).prodMk <| (measurable_fst.comp measurable_snd).prodMk <|
      (((measurable_pi_apply j).comp measurable_snd).comp measurable_fst).prodMk
        (((measurable_pi_apply j).comp measurable_snd).comp measurable_snd)

/-- **The random row law of a separate Aldous--Hoover coding.** Given the global variable `z.1` and
the column variables `z.2 j`, this is the law of the row `j ↦ g (z.1, V, z.2 j, W j)` for a
uniform row variable `V` and an independent i.i.d. uniform sequence `W` of cell variables.

It is meaningful for a measurable `g`, which every statement about it assumes; the pushforward of a
probability measure is a probability measure in any case. -/
def separateRowLaw (g : I × I × I × I → α) (z : I × (ℕ → I)) : ProbabilityMeasure (ℕ → α) :=
  ⟨((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
      fun r j => g (z.1, r.1, z.2 j, r.2 j), inferInstance⟩

@[simp]
theorem separateRowLaw_toMeasure (g : I × I × I × I → α) (z : I × (ℕ → I)) :
    (separateRowLaw g z : Measure (ℕ → α)) =
      ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        fun r j => g (z.1, r.1, z.2 j, r.2 j) :=
  (rfl)

/-- The random row law depends measurably on the global and column noise. -/
theorem measurable_separateRowLaw {g : I × I × I × I → α} (hg : Measurable g) :
    Measurable (separateRowLaw g) :=
  (TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry
    (measurable_separateRow hg)).subtype_mk

/-- Permuting the columns of the noise reindexes the corresponding row law. -/
theorem separateRowLaw_colReindex {g : I × I × I × I → α} (hg : Measurable g)
    (z : I × (ℕ → I)) (τ : Equiv.Perm ℕ) :
    (separateRowLaw g z).map (permReindex τ) =
      separateRowLaw g (z.1, fun j => z.2 (τ j)) := by
  apply ProbabilityMeasure.toMeasure_injective
  let ρ : Measure (I × (ℕ → I)) :=
    (volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))
  let reindex : (I × (ℕ → I)) → I × (ℕ → I) :=
    fun r => (r.1, fun j => r.2 (τ j))
  have hreindex : Measurable reindex :=
    measurable_fst.prodMk ((measurable_reindex τ).comp measurable_snd)
  have hpi : (Measure.infinitePi fun _ : ℕ => (volume : Measure I)).map
      (fun c j => c (τ j)) = Measure.infinitePi fun _ : ℕ => (volume : Measure I) := by
    simpa only using (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => (volume : Measure I)) τ.injective)
  have hρ : ρ.map reindex = ρ := by
    calc
      ρ.map reindex = ((volume : Measure I).map id).prod
          ((Measure.infinitePi fun _ : ℕ => (volume : Measure I)).map
            fun c j => c (τ j)) := by
              exact (Measure.map_prod_map _ _ measurable_id (measurable_reindex τ)).symm
      _ = ρ := by simp [hpi, ρ]
  have hrow : Measurable (fun (r : I × (ℕ → I)) j => g (z.1, r.1, z.2 j, r.2 j)) :=
    (measurable_separateRow hg).comp (measurable_const.prodMk measurable_id)
  have hrow' : Measurable (fun (r : I × (ℕ → I)) j =>
      g (z.1, r.1, z.2 (τ j), r.2 j)) :=
    (measurable_separateRow hg).comp
      ((measurable_const : Measurable fun _ : I × (ℕ → I) =>
        (z.1, fun j => z.2 (τ j))).prodMk measurable_id)
  have hfun : ((permReindex τ) ∘ (fun (r : I × (ℕ → I)) j =>
      g (z.1, r.1, z.2 j, r.2 j))) =
      (fun (r : I × (ℕ → I)) j => g (z.1, r.1, z.2 (τ j), r.2 j)) ∘ reindex := by
    funext r j
    rfl
  simp only [ProbabilityMeasure.toMeasure_map, separateRowLaw_toMeasure]
  rw [show (permReindex τ : (ℕ → α) → ℕ → α) = (fun x j => x (τ j)) from rfl]
  rw [Measure.map_map (measurable_reindex τ) hrow]
  change ρ.map ((permReindex τ) ∘ (fun (r : I × (ℕ → I)) j =>
      g (z.1, r.1, z.2 j, r.2 j))) =
    ρ.map (fun (r : I × (ℕ → I)) j => g (z.1, r.1, z.2 (τ j), r.2 j))
  rw [hfun, ← Measure.map_map hrow' hreindex, hρ]

/-! ## Splitting the separate-coding noise -/

/-- The separate-coding noise indices as pairs of optional indices: the first slot is `none` for the
global and column variables and `some i` for row `i`, and the second slot is `none` for the
variable shared along the line and `some j` for column `j`. -/
private def noiseIndexEquiv : NoiseIndex Axis (ℕ × ℕ) ≃ Option ℕ × Option ℕ where
  toFun
    | .global => (none, none)
    | .vertex .column j => (none, some j)
    | .vertex .row i => (some i, none)
    | .cell p => (some p.1, some p.2)
  invFun
    | (none, none) => .global
    | (none, some j) => .vertex .column j
    | (some i, none) => .vertex .row i
    | (some i, some j) => .cell (i, j)
  left_inv q := by rcases q with _ | ⟨_ | _, _⟩ | ⟨_, _⟩ <;> rfl
  right_inv p := by rcases p with ⟨_ | _, _ | _⟩ <;> rfl

/-- The global-and-column noise of a separate coding, followed by the noise of each row. -/
private def splitNoise (u : NoiseIndex Axis (ℕ × ℕ) → I) :
    (I × (ℕ → I)) × (ℕ → I × (ℕ → I)) :=
  ((u .global, fun j => u (.vertex .column j)),
    fun i => (u (.vertex .row i), fun j => u (.cell (i, j))))

private theorem measurable_splitNoise : Measurable splitNoise :=
  ((measurable_pi_apply _).prodMk (Measurable.of_eval fun _ => measurable_pi_apply _)).prodMk <|
    Measurable.of_eval fun _ =>
      (measurable_pi_apply _).prodMk (Measurable.of_eval fun _ => measurable_pi_apply _)

/-- **The separate-coding noise splits into independent pieces**: the global-and-column noise and
the noise of each row are independent, each distributed as one uniform variable followed by an
i.i.d. uniform sequence. -/
private theorem map_splitNoise_noiseMeasure :
    (noiseMeasure Axis (ℕ × ℕ)).map splitNoise =
      ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).prod
        (Measure.infinitePi fun _ : ℕ =>
          (volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))) := by
  set ρ : Measure (Option ℕ → I) := Measure.infinitePi fun _ => volume with hρ
  -- Split an optional-indexed family into its value at `none` and the rest.
  set s : (Option ℕ → I) → I × (ℕ → I) := fun c => (c none, fun j => c (some j))
  have hs : Measurable s :=
    (measurable_pi_apply _).prodMk (Measurable.of_eval fun _ => measurable_pi_apply _)
  have hs' : Measurable fun (r : ℕ → Option ℕ → I) i => s (r i) :=
    Measurable.of_eval fun _ => hs.comp (measurable_pi_apply _)
  have hρs : ρ.map s = (volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => volume) :=
    TauCeti.MeasureTheory.Measure.infinitePi_map_none_some _
  -- The noise law is the product of its independent uniform coordinates.
  have hnoise : noiseMeasure Axis (ℕ × ℕ) = Measure.infinitePi fun _ => (volume : Measure I) := by
    simpa [map_eval_noiseMeasure] using
      (iIndepFun_eval_noiseMeasure Axis (ℕ × ℕ)).map_fun_eq_infinitePi_map
        fun q => measurable_pi_apply q
  -- Reindex by pairs of optional indices, curry, and split both levels at `none`.
  set f₁ : (NoiseIndex Axis (ℕ × ℕ) → I) → (Option ℕ × Option ℕ → I) :=
    fun u p => u (noiseIndexEquiv.symm p)
  set f₂ := ⇑(MeasurableEquiv.curry (Option ℕ) (Option ℕ) I)
  set f₃ : (Option ℕ → Option ℕ → I) → (Option ℕ → I) × (ℕ → Option ℕ → I) :=
    fun c => (c none, fun i => c (some i))
  set f₄ : (Option ℕ → I) × (ℕ → Option ℕ → I) → (I × (ℕ → I)) × (ℕ → I × (ℕ → I)) :=
    Prod.map s fun r i => s (r i)
  have h₁ : Measurable f₁ := Measurable.of_eval fun _ => measurable_pi_apply _
  have h₂ : Measurable f₂ := MeasurableEquiv.measurable _
  have h₃ : Measurable f₃ :=
    (measurable_pi_apply _).prodMk (Measurable.of_eval fun _ => measurable_pi_apply _)
  have hcomp : splitNoise = f₄ ∘ f₃ ∘ f₂ ∘ f₁ := rfl
  rw [hcomp, ← Measure.map_map (hs.prodMap hs') (h₃.comp (h₂.comp h₁)),
    ← Measure.map_map h₃ (h₂.comp h₁), ← Measure.map_map h₂ h₁, hnoise,
    Measure.map_infinitePi_infinitePi_of_inj noiseIndexEquiv.symm.injective,
    Measure.infinitePi_map_curry (fun _ _ => (volume : Measure I)),
    TauCeti.MeasureTheory.Measure.infinitePi_map_none_some, ← hρ,
    ← Measure.map_prod_map _ _ hs hs', Measure.infinitePi_map_pi _ fun _ => hs, hρs]

/-! ## The rows of a separate coding -/

/-- **The rows of a separate Aldous--Hoover coding are conditionally i.i.d.**, with directing
measure the random row law evaluated at the global variable and the column variables. -/
theorem conditionallyIIDWith_arrayRow_separateArray {g : I × I × I × I → α}
    (hg : Measurable g) :
    ConditionallyIIDWith (noiseMeasure Axis (ℕ × ℕ)) (arrayRow (separateArray g))
      fun u => separateRowLaw g (u .global, fun j => u (.vertex .column j)) := by
  set G : I × (ℕ → I) → I × (ℕ → I) → ℕ → α := fun z r j => g (z.1, r.1, z.2 j, r.2 j)
  have hΨ : Measurable fun q : (I × (ℕ → I)) × (ℕ → I × (ℕ → I)) =>
      (q.1, fun i => G q.1 (q.2 i)) :=
    measurable_fst.prodMk <| Measurable.of_eval fun i =>
      (measurable_separateRow hg).comp (measurable_fst.prodMk
        ((measurable_pi_apply i).comp measurable_snd))
  -- The global-and-column noise paired with the rows has the canonical conditionally i.i.d. law.
  have hlaw : (noiseMeasure Axis (ℕ × ℕ)).map
      ((fun q : (I × (ℕ → I)) × (ℕ → I × (ℕ → I)) => (q.1, fun i => G q.1 (q.2 i))) ∘
        splitNoise) =
      iidMixtureLaw ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => volume))
        (separateRowLaw g) := by
    rw [← Measure.map_map hΨ measurable_splitNoise, map_splitNoise_noiseMeasure]
    exact map_prod_infinitePi_eq_iidMixtureLaw _ (measurable_separateRow hg)
      fun z => (separateRowLaw_toMeasure g z).symm
  have h := conditionallyIIDWith_iidMixtureLaw
    (π := (volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => volume))
    (measurable_separateRowLaw hg)
  rw [← hlaw] at h
  refine (h.of_map (hΨ.comp measurable_splitNoise)).congr_process fun n => ?_
  exact .of_forall fun u => funext fun j => by simp [splitNoise, G]

/-- **The row mixing law of a separate coding** is the law of the random row law under uniform
global and column noise. -/
theorem map_separateRowLaw_noiseMeasure {g : I × I × I × I → α} (hg : Measurable g) :
    (noiseMeasure Axis (ℕ × ℕ)).map
        (fun u => separateRowLaw g (u .global, fun j => u (.vertex .column j))) =
      ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        (separateRowLaw g) := by
  have hcomp : (fun u : NoiseIndex Axis (ℕ × ℕ) → I =>
      separateRowLaw g (u .global, fun j => u (.vertex .column j))) =
      separateRowLaw g ∘ Prod.fst ∘ splitNoise := rfl
  rw [hcomp, ← Measure.map_map (measurable_separateRowLaw hg)
      (measurable_fst.comp measurable_splitNoise),
    ← Measure.map_map measurable_fst measurable_splitNoise, map_splitNoise_noiseMeasure,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- The mixing law of a separate coding is invariant under reindexing the columns of its random
row law. -/
theorem map_separateRowLaw_colReindex {g : I × I × I × I → α} (hg : Measurable g)
    (τ : Equiv.Perm ℕ) :
    (((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        (separateRowLaw g)).map (fun P => P.map (permReindex τ)) =
      ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        (separateRowLaw g) := by
  rw [← map_separateRowLaw_noiseMeasure hg]
  have hnoise : Measurable (fun u : NoiseIndex Axis (ℕ × ℕ) → I =>
      separateRowLaw g (u .global, fun j => u (.vertex .column j))) :=
    (measurable_separateRowLaw hg).comp <|
      (measurable_pi_apply _).prodMk (Measurable.of_eval fun _ => measurable_pi_apply _)
  have hpush : Measurable fun P : ProbabilityMeasure (ℕ → α) =>
      P.map (permReindex τ) :=
    TauCeti.MeasureTheory.measurable_probabilityMeasure_map (measurable_reindex τ)
  rw [Measure.map_map hpush hnoise]
  have hfun : (fun P : ProbabilityMeasure (ℕ → α) => P.map (permReindex τ)) ∘
      (fun u : NoiseIndex Axis (ℕ × ℕ) → I =>
        separateRowLaw g (u .global, fun j => u (.vertex .column j))) =
      (fun u => separateRowLaw g (u .global, fun j => u (.vertex .column j))) ∘
        separateNoiseCongr 1 τ := by
    funext u
    dsimp only [Function.comp_apply]
    rw [separateRowLaw_colReindex hg, separateNoiseCongr_apply_global]
    simp only [separateNoiseCongr_apply_vertex, separateVertexPerm_column]
  rw [hfun, ← Measure.map_map hnoise (separateNoiseCongr 1 τ).measurable,
    map_separateNoiseCongr_noiseMeasure]

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
