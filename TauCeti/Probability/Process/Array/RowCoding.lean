/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Array
public import TauCeti.Probability.Process.IIDMixture.Coding
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.MeasureTheory.Measure.Mixture.Injective

/-!
# Sampling array rows from a random path law

Draw a probability measure `P` on `ℕ → α` with law `π`, and sample independent rows from `P`
using one uniform variable per row. The coupled law `arrayRowCodingLaw π` retains `P` as a
coordinate; `rowCodingArrayLaw π` is its array marginal. No symmetry of `π` is required.

The parameter marginal is `π`, and currying the array marginal gives the mixture of infinite
powers `Measure.deFinettiBarycenter π`. Consequently the array marginal determines every finite
mixing law. When `π` is invariant under a column permutation `τ`, the coupled law is
equivariant for reindexing the rows by any `σ` and the columns by `τ`, with `τ` also acting on
the retained path law by pushforward. These constructions provide the sampling laws used by array
representation theorems, independently of any exchangeability assumption.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581–598.
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Lemma 4.22, for randomization
  by a uniform variable.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- Every entry of a coded array is measurable in the parameter and the noise. -/
theorem measurable_unitIntervalCoding_entry (p : ℕ × ℕ) :
    Measurable fun q : ProbabilityMeasure (ℕ → α) × (ℕ → unitInterval) =>
      unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2 :=
  (measurable_pi_apply p.2).comp ((measurable_uncurry_unitIntervalCoding (ℕ → α)).comp
    (measurable_fst.prodMk ((measurable_pi_apply p.1).comp measurable_snd)))

/-- The measurable map which retains a path law and uses one independent uniform variable to
sample each row from it. -/
theorem measurable_arrayRowCoding :
    Measurable fun q : ProbabilityMeasure (ℕ → α) × (ℕ → unitInterval) ↦
      (q.1, fun p : ℕ × ℕ ↦ unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2) :=
  measurable_fst.prodMk (Measurable.of_eval fun p ↦ measurable_unitIntervalCoding_entry p)

/-- The canonical coupled law of a random path measure and the array obtained by independently
sampling its rows. -/
def arrayRowCodingLaw (π : Measure (ProbabilityMeasure (ℕ → α))) :
    Measure (ProbabilityMeasure (ℕ → α) × (ℕ × ℕ → α)) :=
  (π.prod (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure unitInterval))).map
    fun q ↦ (q.1,
      fun p : ℕ × ℕ ↦ unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2)

/-- The defining pushforward formula for `arrayRowCodingLaw`. -/
theorem arrayRowCodingLaw_def (π : Measure (ProbabilityMeasure (ℕ → α))) :
    arrayRowCodingLaw π =
      (π.prod (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure unitInterval))).map
        fun q ↦ (q.1,
          fun p : ℕ × ℕ ↦ unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2) :=
  (rfl)

/-- The coupled row-coding law is the image of the i.i.d. mixture law of row paths under
uncurrying the sampled rows into an array. -/
theorem arrayRowCodingLaw_eq_map_iidMixtureLaw (π : Measure (ProbabilityMeasure (ℕ → α))) :
    arrayRowCodingLaw π = (iidMixtureLaw π id).map (Prod.map id Function.uncurry) := by
  rw [arrayRowCodingLaw_def,
    ← Measure.map_prod_unitIntervalCoding_eq_iidMixtureLaw (α := ℕ → α) π,
    Measure.map_map (measurable_id.prodMap measurable_uncurry)
      (measurable_fst.prodMk measurable_unitIntervalCodingPath)]
  refine congrArg (Measure.map · _) ?_
  funext q
  rfl

/-- The coupled row-coding construction sends the zero mixing law to zero. -/
@[simp]
theorem arrayRowCodingLaw_zero :
    arrayRowCodingLaw (0 : Measure (ProbabilityMeasure (ℕ → α))) = 0 := by
  rw [arrayRowCodingLaw_def, Measure.zero_prod, Measure.map_zero]

/-- The coupled row-coding construction preserves sums of mixing laws. -/
@[simp]
theorem arrayRowCodingLaw_add (π₁ π₂ : Measure (ProbabilityMeasure (ℕ → α)))
    [SFinite π₁] [SFinite π₂] :
    arrayRowCodingLaw (π₁ + π₂) = arrayRowCodingLaw π₁ + arrayRowCodingLaw π₂ := by
  rw [arrayRowCodingLaw_def, arrayRowCodingLaw_def, arrayRowCodingLaw_def, Measure.add_prod]
  exact Measure.map_add _ _ measurable_arrayRowCoding

/-- The coupled row-coding construction preserves nonnegative scalar multiples of mixing laws. -/
@[simp]
theorem arrayRowCodingLaw_smul (c : ℝ≥0∞) (π : Measure (ProbabilityMeasure (ℕ → α))) :
    arrayRowCodingLaw (c • π) = c • arrayRowCodingLaw π := by
  rw [arrayRowCodingLaw_def, arrayRowCodingLaw_def, Measure.prod_smul_left]
  exact Measure.map_smul _ measurable_arrayRowCoding.aemeasurable

/-- Coding a probability law of random path measures gives a probability law of the coupled
parameter and array. -/
instance instIsProbabilityMeasureArrayRowCodingLaw
    (π : Measure (ProbabilityMeasure (ℕ → α))) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (arrayRowCodingLaw π) := by
  rw [arrayRowCodingLaw_def]
  infer_instance

/-- The first marginal of the coupled coding law is the supplied law of the random path measure. -/
@[simp]
theorem map_fst_arrayRowCodingLaw (π : Measure (ProbabilityMeasure (ℕ → α))) :
    (arrayRowCodingLaw π).map Prod.fst = π := by
  rw [arrayRowCodingLaw_def, Measure.map_map measurable_fst measurable_arrayRowCoding]
  have hcomp :
      Prod.fst ∘ (fun q : ProbabilityMeasure (ℕ → α) × (ℕ → unitInterval) ↦
        (q.1, fun p : ℕ × ℕ ↦ unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2)) =
          Prod.fst := rfl
  rw [hcomp, Measure.map_fst_prod, measure_univ, one_smul]

/-- The array marginal of the coupled coding law is the uncurried de Finetti barycenter of the
law of the random path measure. -/
@[simp]
theorem map_snd_arrayRowCodingLaw (π : Measure (ProbabilityMeasure (ℕ → α))) :
    (arrayRowCodingLaw π).map Prod.snd =
      (Measure.deFinettiBarycenter π).map Function.uncurry := by
  rw [arrayRowCodingLaw_def, Measure.map_map measurable_snd measurable_arrayRowCoding,
    ← Measure.map_prod_unitIntervalCoding_eq_deFinettiBarycenter (α := ℕ → α),
    Measure.map_map measurable_uncurry measurable_unitIntervalCodingPath]
  refine congrArg (Measure.map · _) ?_
  funext q p
  rfl

/-- The array law obtained by drawing a random path measure with law `π`, then using independent
uniform variables to sample one row from that path measure at each row index. -/
def rowCodingArrayLaw (π : Measure (ProbabilityMeasure (ℕ → α))) : Measure (ℕ × ℕ → α) :=
  (arrayRowCodingLaw π).map Prod.snd

/-- The row-coding array law is the array marginal of the coupled coding law. -/
theorem rowCodingArrayLaw_eq_map_snd (π : Measure (ProbabilityMeasure (ℕ → α))) :
    rowCodingArrayLaw π = (arrayRowCodingLaw π).map Prod.snd := by
  rw [rowCodingArrayLaw]

/-- The row-coding array construction sends the zero mixing law to zero. -/
@[simp]
theorem rowCodingArrayLaw_zero :
    rowCodingArrayLaw (0 : Measure (ProbabilityMeasure (ℕ → α))) = 0 := by
  rw [rowCodingArrayLaw_eq_map_snd, arrayRowCodingLaw_zero, Measure.map_zero]

/-- The defining pushforward expression for `rowCodingArrayLaw`. -/
theorem rowCodingArrayLaw_def (π : Measure (ProbabilityMeasure (ℕ → α))) :
    rowCodingArrayLaw π =
      (π.prod (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure unitInterval))).map
        fun q p ↦ unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2 := by
  rw [rowCodingArrayLaw, arrayRowCodingLaw_def,
    Measure.map_map measurable_snd measurable_arrayRowCoding]
  rfl

/-- A probability law of random path measures gives a probability row-coding array law. -/
instance instIsProbabilityMeasureRowCodingArrayLaw
    (π : Measure (ProbabilityMeasure (ℕ → α))) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (rowCodingArrayLaw π) := by
  rw [rowCodingArrayLaw_def]
  infer_instance

/-- The row-coding construction preserves sums of mixing laws. -/
@[simp]
theorem rowCodingArrayLaw_add (π₁ π₂ : Measure (ProbabilityMeasure (ℕ → α)))
    [SFinite π₁] [SFinite π₂] :
    rowCodingArrayLaw (π₁ + π₂) = rowCodingArrayLaw π₁ + rowCodingArrayLaw π₂ := by
  simp only [rowCodingArrayLaw_eq_map_snd, arrayRowCodingLaw_add,
    Measure.map_add _ _ measurable_snd]

/-- The row-coding construction preserves nonnegative scalar multiples of mixing laws. -/
@[simp]
theorem rowCodingArrayLaw_smul (c : ℝ≥0∞) (π : Measure (ProbabilityMeasure (ℕ → α))) :
    rowCodingArrayLaw (c • π) = c • rowCodingArrayLaw π := by
  simp only [rowCodingArrayLaw_eq_map_snd, arrayRowCodingLaw_smul,
    Measure.map_smul _ measurable_snd.aemeasurable]

/-- Currying the canonical row-coding array law gives the de Finetti barycenter of its mixing
law. -/
@[simp]
theorem map_curry_rowCodingArrayLaw (π : Measure (ProbabilityMeasure (ℕ → α))) :
    (rowCodingArrayLaw π).map (MeasurableEquiv.curry ℕ ℕ α) = Measure.deFinettiBarycenter π := by
  rw [rowCodingArrayLaw_eq_map_snd, map_snd_arrayRowCodingLaw,
    ← MeasurableEquiv.coe_curry_symm, MeasurableEquiv.map_map_symm]

/-- The row-coding array law determines every finite mixing law on path measures. -/
theorem eq_of_rowCodingArrayLaw_eq {π₁ π₂ : Measure (ProbabilityMeasure (ℕ → α))}
    [IsFiniteMeasure π₁]
    (h : rowCodingArrayLaw π₁ = rowCodingArrayLaw π₂) : π₁ = π₂ := by
  apply TauCeti.MeasureTheory.Measure.ext_of_bind_infinitePi_eq
  have h' := congrArg (fun ρ : Measure (ℕ × ℕ → α) ↦
    ρ.map (MeasurableEquiv.curry ℕ ℕ α)) h
  simpa only [map_curry_rowCodingArrayLaw, Measure.deFinettiBarycenter_def] using h'

/-- Equality of finite mixing laws is equivalent to equality of their row-coding array laws. -/
@[simp]
theorem rowCodingArrayLaw_inj {π₁ π₂ : Measure (ProbabilityMeasure (ℕ → α))}
    [IsFiniteMeasure π₁] :
    rowCodingArrayLaw π₁ = rowCodingArrayLaw π₂ ↔ π₁ = π₂ :=
  ⟨eq_of_rowCodingArrayLaw_eq, fun h ↦ congrArg rowCodingArrayLaw h⟩

/-- If the mixing law `π` is invariant under pushing path laws forward by the column permutation
`τ`, the canonical coupled law is invariant under reindexing the rows by `σ` and the columns by `τ`
while pushing the retained path law forward by `τ`. -/
theorem map_pairReindex_arrayRowCodingLaw_eq_of_col_invariant
    (π : Measure (ProbabilityMeasure (ℕ → α)))
    (σ τ : Equiv.Perm ℕ)
    (hπ : π.map (fun P ↦ P.map (permReindex τ)) = π) :
    (arrayRowCodingLaw π).map
        (fun q ↦
          (q.1.map (permReindex τ), pairReindex σ τ q.2)) =
      arrayRowCodingLaw π := by
  -- Write the coupled law as the image under uncurrying `C` of the i.i.d. mixture law of row
  -- paths. The map `J` pushes the parameter forward by `τ` and reindexes the sampled rows by `σ`
  -- and their entries by `τ`; it sends each fibre `δ_P ⊗ P^{⊗ℕ}` to `δ_{f P} ⊗ (f P)^{⊗ℕ}`, so
  -- it preserves the mixture law when `π` is invariant. The target map factors as `C ∘ J`.
  let f : ProbabilityMeasure (ℕ → α) → ProbabilityMeasure (ℕ → α) :=
    fun P ↦ P.map (permReindex τ)
  let g : (ℕ → (ℕ → α)) → (ℕ → (ℕ → α)) :=
    fun x i ↦ permReindex τ (x (σ i))
  let J : ProbabilityMeasure (ℕ → α) × (ℕ → (ℕ → α)) →
      ProbabilityMeasure (ℕ → α) × (ℕ → (ℕ → α)) := Prod.map f g
  let C : ProbabilityMeasure (ℕ → α) × (ℕ → (ℕ → α)) →
      ProbabilityMeasure (ℕ → α) × (ℕ × ℕ → α) := Prod.map id Function.uncurry
  have hf : Measurable f :=
    TauCeti.MeasureTheory.measurable_probabilityMeasure_map (measurable_reindex τ)
  have hg : Measurable g := by
    exact Measurable.of_eval fun i ↦
      (measurable_reindex τ).comp (measurable_pi_apply (σ i))
  have hJ : Measurable J := hf.prodMap hg
  have hC : Measurable C := measurable_id.prodMap measurable_uncurry
  have hcode : arrayRowCodingLaw π = (iidMixtureLaw π id).map C :=
    arrayRowCodingLaw_eq_map_iidMixtureLaw π
  -- Each fibre `P^{⊗ℕ}` is carried to `(f P)^{⊗ℕ}`: `σ` permutes the i.i.d. rows and `τ`
  -- reindexes each row.
  have hmix : (iidMixtureLaw π id).map J = iidMixtureLaw (π.map f) id :=
    map_prodMap_iidMixtureLaw (P := id) (Q := id) measurable_id measurable_id hf hg fun P ↦
      TauCeti.MeasureTheory.map_infinitePi_comp_injective P σ.injective (measurable_reindex τ)
  have hJlaw : (iidMixtureLaw π id).map J = iidMixtureLaw π id := by
    rw [hmix, hπ]
  have hH : Measurable fun q : ProbabilityMeasure (ℕ → α) × (ℕ × ℕ → α) ↦
      (q.1.map (permReindex τ), pairReindex σ τ q.2) :=
    (hf.comp measurable_fst).prodMk ((measurable_pairReindex σ τ).comp measurable_snd)
  have hcomp :
      (fun q : ProbabilityMeasure (ℕ → α) × (ℕ × ℕ → α) ↦
        (q.1.map (permReindex τ), pairReindex σ τ q.2)) ∘ C =
      C ∘ J := by
    funext q
    dsimp [C, J]
    apply Prod.ext
    · rfl
    · funext p
      simp [Function.uncurry, pairReindex_apply, g, permReindex_apply]
  calc
    (arrayRowCodingLaw π).map
        (fun q ↦
          (q.1.map (permReindex τ), pairReindex σ τ q.2)) =
        ((iidMixtureLaw π id).map C).map (fun q ↦
          (q.1.map (permReindex τ), pairReindex σ τ q.2)) := by
      rw [hcode]
    _ = (iidMixtureLaw π id).map
        ((fun q : ProbabilityMeasure (ℕ → α) × (ℕ × ℕ → α) ↦
          (q.1.map (permReindex τ), pairReindex σ τ q.2)) ∘ C) :=
      Measure.map_map hH hC
    _ = (iidMixtureLaw π id).map (C ∘ J) := by rw [hcomp]
    _ = ((iidMixtureLaw π id).map J).map C := (Measure.map_map hC hJ).symm
    _ = (iidMixtureLaw π id).map C := by rw [hJlaw]
    _ = arrayRowCodingLaw π := hcode.symm

end TauCeti.Probability
