/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Array.AldousHoover.Basic
import Mathlib.Order.Sym2
import TauCeti.Probability.Independence.InfinitePi
import TauCeti.Probability.ProductMeasure

/-!
# Splitting Aldous--Hoover noise into independent layers

The canonical Aldous--Hoover noise is a single family of independent uniform variables.
The maps in this file regroup it into the product spaces used to generate an array in layers:
global, row, column, and cell noise in the separate case; global, vertex, and off-diagonal
unordered-pair noise in the joint case. Their pushforwards are exactly the corresponding
products of uniform laws. No symmetry hypothesis on an array law is involved.

In the joint case, the cell coordinates retained by the split are indexed by strictly increasing
pairs. Diagonal cell noise is discarded; it is independent of the retained variables. Thus the
joint split is a measurable map, rather than an equivalence of the full noise spaces.

The two array representation theorems use these identities to assemble their conditional codings
on the canonical noise space. The underlying product-measure identities are
`TauCeti.Probability.infinitePi_map_pair_comp` and
`TauCeti.MeasureTheory.Measure.infinitePi_map_none_some`.

## References

* D. Aldous, *Representations for partially exchangeable arrays of random variables*,
  Journal of Multivariate Analysis 11 (1981), 581–598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti.Probability.AldousHoover

/-- The noise of a separate Aldous--Hoover coding, sorted into the global variable, the row and
the column variables, and the cell variables. -/
def splitSeparateNoise (u : NoiseIndex Axis (ℕ × ℕ) → I) :
    (I × (ℕ → I) × (ℕ → I)) × (ℕ × ℕ → I) :=
  ((u .global, fun i => u (.vertex .row i), fun j => u (.vertex .column j)),
    fun p => u (.cell p))

/-- The separate noise split reads the global, row, column, and cell coordinates. -/
@[simp]
theorem splitSeparateNoise_apply (u : NoiseIndex Axis (ℕ × ℕ) → I) :
    splitSeparateNoise u =
      ((u .global, fun i => u (.vertex .row i), fun j => u (.vertex .column j)),
        fun p => u (.cell p)) :=
  (rfl)

/-- The separate noise split is measurable. -/
theorem measurable_splitSeparateNoise : Measurable splitSeparateNoise :=
  ((measurable_pi_apply _).prodMk ((Measurable.of_eval fun _ => measurable_pi_apply _).prodMk
    (Measurable.of_eval fun _ => measurable_pi_apply _))).prodMk
      (Measurable.of_eval fun _ => measurable_pi_apply _)

/-- The non-cell noise indices, read as `none` for the global index and `some` of a row or a column
index for a vertex index. -/
private def vertexNoiseIndex : Option (ℕ ⊕ ℕ) → NoiseIndex Axis (ℕ × ℕ)
  | none => .global
  | some (.inl i) => .vertex .row i
  | some (.inr j) => .vertex .column j

private theorem vertexNoiseIndex_injective : Function.Injective vertexNoiseIndex := by
  rintro (_ | _ | _) (_ | _ | _) h <;> simp_all [vertexNoiseIndex]

/-- **The separate-coding noise splits into independent pieces**: the global variable, the i.i.d.
row variables, the i.i.d. column variables and the i.i.d. cell variables are independent uniform
families. -/
@[simp]
theorem map_splitSeparateNoise_noiseMeasure :
    (noiseMeasure Axis (ℕ × ℕ)).map splitSeparateNoise =
      ((volume : Measure I).prod ((Measure.infinitePi fun _ : ℕ => (volume : Measure I)).prod
        (Measure.infinitePi fun _ : ℕ => (volume : Measure I)))).prod
        (Measure.infinitePi fun _ : ℕ × ℕ => (volume : Measure I)) := by
  have hcell : Function.Injective (NoiseIndex.cell : ℕ × ℕ → NoiseIndex Axis (ℕ × ℕ)) :=
    fun _ _ h => NoiseIndex.cell.inj h
  have hdisj : Disjoint (Set.range vertexNoiseIndex) (Set.range NoiseIndex.cell) := by
    rw [Set.disjoint_left]
    rintro _ ⟨(_ | _ | _), rfl⟩ ⟨_, h⟩ <;> cases h
  -- Separate the cell noise, then the global variable, then the rows from the columns.
  set f₁ : (NoiseIndex Axis (ℕ × ℕ) → I) → (Option (ℕ ⊕ ℕ) → I) × (ℕ × ℕ → I) :=
    fun u => (fun o => u (vertexNoiseIndex o), fun p => u (.cell p))
  set f₂ : (Option (ℕ ⊕ ℕ) → I) → I × (ℕ ⊕ ℕ → I) := fun y => (y none, fun s => y (some s))
  set f₃ : (ℕ ⊕ ℕ → I) → (ℕ → I) × (ℕ → I) :=
    fun z => (fun i => z (.inl i), fun j => z (.inr j))
  have h₁ : Measurable f₁ := (Measurable.of_eval fun _ => measurable_pi_apply _).prodMk
    (Measurable.of_eval fun _ => measurable_pi_apply _)
  have h₂ : Measurable f₂ :=
    (measurable_pi_apply _).prodMk (Measurable.of_eval fun _ => measurable_pi_apply _)
  have h₃ : Measurable f₃ := (Measurable.of_eval fun _ => measurable_pi_apply _).prodMk
    (Measurable.of_eval fun _ => measurable_pi_apply _)
  have h₂₃ : Measurable (Prod.map id f₃ ∘ f₂) := (measurable_id.prodMap h₃).comp h₂
  have hsplit : splitSeparateNoise = Prod.map (Prod.map id f₃ ∘ f₂) id ∘ f₁ := by
    funext u
    simp [f₁, f₂, f₃, vertexNoiseIndex]
  rw [hsplit, ← Measure.map_map (h₂₃.prodMap measurable_id) h₁, noiseMeasure_def,
    infinitePi_map_pair_comp _ hcell hdisj,
    Measure.map_infinitePi_infinitePi_of_inj vertexNoiseIndex_injective,
    ← Measure.map_prod_map _ _ h₂₃ measurable_id, Measure.map_id,
    ← Measure.map_map (measurable_id.prodMap h₃) h₂,
    TauCeti.MeasureTheory.Measure.infinitePi_map_none_some,
    ← Measure.map_prod_map _ _ measurable_id h₃, Measure.map_id,
    infinitePi_map_pair_comp _ Sum.inr_injective Set.isCompl_range_inl_range_inr.disjoint,
    Measure.map_infinitePi_infinitePi_of_inj Sum.inl_injective]

/-- The noise of a joint Aldous--Hoover coding, sorted into the global variable, the vertex
variables, and the variables of the off-diagonal unordered pairs, indexed by the increasing
pairs. -/
def splitJointNoise (u : NoiseIndex Unit (Sym2 ℕ) → I) :
    (I × (ℕ → I)) × ({t : ℕ × ℕ // t.1 < t.2} → I) :=
  ((u .global, fun k => u (.vertex () k)), fun t => u (.cell s(t.1.1, t.1.2)))

/-- The joint noise split reads the global, vertex, and off-diagonal cell coordinates. -/
@[simp]
theorem splitJointNoise_apply (u : NoiseIndex Unit (Sym2 ℕ) → I) :
    splitJointNoise u =
      ((u .global, fun k => u (.vertex () k)), fun t => u (.cell s(t.1.1, t.1.2))) :=
  (rfl)

/-- The joint noise split is measurable. -/
theorem measurable_splitJointNoise : Measurable splitJointNoise :=
  ((measurable_pi_apply _).prodMk (Measurable.of_eval fun _ => measurable_pi_apply _)).prodMk
    (Measurable.of_eval fun _ => measurable_pi_apply _)

/-- The non-cell noise indices of a joint coding, read as `none` for the global index and `some k`
for the vertex index `k`. -/
private def jointVertexNoiseIndex : Option ℕ → NoiseIndex Unit (Sym2 ℕ)
  | none => .global
  | some k => .vertex () k

private theorem jointVertexNoiseIndex_injective : Function.Injective jointVertexNoiseIndex := by
  rintro (_ | _) (_ | _) h <;> simp_all [jointVertexNoiseIndex]

/-- **The joint-coding noise splits into independent pieces**: the global variable, the i.i.d.
vertex variables and the i.i.d. variables of the off-diagonal unordered pairs, indexed by the
increasing pairs, are independent uniform families. -/
@[simp]
theorem map_splitJointNoise_noiseMeasure :
    (noiseMeasure Unit (Sym2 ℕ)).map splitJointNoise =
      ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).prod
        (Measure.infinitePi fun _ : {t : ℕ × ℕ // t.1 < t.2} => (volume : Measure I)) := by
  set c : {t : ℕ × ℕ // t.1 < t.2} → NoiseIndex Unit (Sym2 ℕ) := fun t => .cell s(t.1.1, t.1.2)
  -- Increasing pairs are sorted, so `Sym2.mk` is injective on them.
  have hc : Function.Injective c := fun t t' h => by
    have := Sym2.sortEquiv.symm.injective (a₁ := ⟨t.1, t.2.le⟩) (a₂ := ⟨t'.1, t'.2.le⟩)
      (NoiseIndex.cell.inj h)
    exact Subtype.ext (Subtype.ext_iff.1 this :)
  have hdisj : Disjoint (Set.range jointVertexNoiseIndex) (Set.range c) := by
    rw [Set.disjoint_left]
    rintro _ ⟨(_ | _), rfl⟩ ⟨_, h⟩ <;> cases h
  -- Separate the cell noise, then the global variable from the vertex variables.
  set f₁ : (NoiseIndex Unit (Sym2 ℕ) → I) → (Option ℕ → I) × ({t : ℕ × ℕ // t.1 < t.2} → I) :=
    fun u => (fun o => u (jointVertexNoiseIndex o), fun t => u (c t))
  set f₂ : (Option ℕ → I) → I × (ℕ → I) := fun y => (y none, fun k => y (some k))
  have h₁ : Measurable f₁ := (Measurable.of_eval fun _ => measurable_pi_apply _).prodMk
    (Measurable.of_eval fun _ => measurable_pi_apply _)
  have h₂ : Measurable f₂ :=
    (measurable_pi_apply _).prodMk (Measurable.of_eval fun _ => measurable_pi_apply _)
  have hsplit : splitJointNoise = Prod.map f₂ id ∘ f₁ := by
    funext u
    simp [f₁, f₂, c, jointVertexNoiseIndex]
  rw [hsplit, ← Measure.map_map (h₂.prodMap measurable_id) h₁, noiseMeasure_def,
    infinitePi_map_pair_comp _ hc hdisj,
    Measure.map_infinitePi_infinitePi_of_inj jointVertexNoiseIndex_injective,
    ← Measure.map_prod_map _ _ h₂ measurable_id, Measure.map_id,
    TauCeti.MeasureTheory.Measure.infinitePi_map_none_some]

end TauCeti.Probability.AldousHoover

end
