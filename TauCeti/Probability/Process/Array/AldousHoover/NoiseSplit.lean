/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Array.AldousHoover.Basic
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

The general law `map_global_vertex_cell_noiseMeasure` splits arbitrary injective selections of
vertex and cell coordinates; both array-specific laws are derived from it.

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

/-- The global and selected vertex indices, with `none` denoting the global index. -/
private def vertexNoiseIndex {κ ι β : Type*} (v : β → κ × ℕ) : Option β → NoiseIndex κ ι
  | none => .global
  | some b => .vertex (v b).1 (v b).2

/-- The global variable, any injectively selected vertex variables, and any injectively selected
cell variables have the product of uniform laws. Taking `v = id` retains every vertex coordinate;
other selections allow the same law to be used after reindexing the vertex families. -/
theorem map_global_vertex_cell_noiseMeasure {κ ι β γ : Type*} {v : β → κ × ℕ} {c : γ → ι}
    (hv : Function.Injective v) (hc : Function.Injective c) :
    (noiseMeasure κ ι).map
        (fun u => ((u .global, fun b => u (.vertex (v b).1 (v b).2)), fun t => u (.cell (c t)))) =
      ((volume : Measure I).prod (Measure.infinitePi fun _ : β => (volume : Measure I))).prod
        (Measure.infinitePi fun _ : γ => (volume : Measure I)) := by
  have hvertex : Function.Injective (vertexNoiseIndex (ι := ι) v) := by
    rintro (_ | b) (_ | b') h <;>
      simp only [vertexNoiseIndex, reduceCtorEq, NoiseIndex.vertex.injEq, Option.some.injEq] at h ⊢
    exact hv (Prod.ext h.1 h.2)
  have hcell : Function.Injective (fun t => (NoiseIndex.cell (c t) : NoiseIndex κ ι)) :=
    fun _ _ h => hc (NoiseIndex.cell.inj h)
  have hdisj : Disjoint (Set.range (vertexNoiseIndex (ι := ι) v))
      (Set.range fun t => (NoiseIndex.cell (c t) : NoiseIndex κ ι)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨(_ | _), rfl⟩ ⟨_, h⟩ <;> cases h
  -- Separate the cell noise, then split the global variable from the selected vertices.
  set f₁ : (NoiseIndex κ ι → I) → (Option β → I) × (γ → I) :=
    fun u => (fun o => u (vertexNoiseIndex v o), fun t => u (.cell (c t)))
  set f₂ : (Option β → I) → I × (β → I) := fun y => (y none, fun b => y (some b))
  have h₁ : Measurable f₁ := by fun_prop
  have h₂ : Measurable f₂ := by fun_prop
  have hsplit : (fun u : NoiseIndex κ ι → I =>
      ((u .global, fun b => u (.vertex (v b).1 (v b).2)), fun t => u (.cell (c t)))) =
      Prod.map f₂ id ∘ f₁ := by
    funext u
    simp [f₁, f₂, vertexNoiseIndex]
  rw [hsplit, ← Measure.map_map (h₂.prodMap measurable_id) h₁, noiseMeasure_def,
    infinitePi_map_pair_comp _ hcell hdisj,
    Measure.map_infinitePi_infinitePi_of_inj hvertex,
    ← Measure.map_prod_map _ _ h₂ measurable_id, Measure.map_id,
    TauCeti.MeasureTheory.Measure.infinitePi_map_none_some]

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
theorem measurable_splitSeparateNoise : Measurable splitSeparateNoise := by
  unfold splitSeparateNoise
  fun_prop

/-- **The separate-coding noise splits into independent pieces**: the global variable, the i.i.d.
row variables, the i.i.d. column variables and the i.i.d. cell variables are independent uniform
families. -/
@[simp]
theorem map_splitSeparateNoise_noiseMeasure :
    (noiseMeasure Axis (ℕ × ℕ)).map splitSeparateNoise =
      ((volume : Measure I).prod ((Measure.infinitePi fun _ : ℕ => (volume : Measure I)).prod
        (Measure.infinitePi fun _ : ℕ => (volume : Measure I)))).prod
        (Measure.infinitePi fun _ : ℕ × ℕ => (volume : Measure I)) := by
  set v : ℕ ⊕ ℕ → Axis × ℕ := Sum.elim (fun i => (.row, i)) (fun j => (.column, j))
  have hv : Function.Injective v := by
    rintro (i | i) (j | j) h <;> simp_all [v]
  set f : (ℕ ⊕ ℕ → I) → (ℕ → I) × (ℕ → I) :=
    fun z => (fun i => z (.inl i), fun j => z (.inr j))
  have hf : Measurable f := by fun_prop
  have hmeas : Measurable (fun u : NoiseIndex Axis (ℕ × ℕ) → I =>
      ((u .global, fun b => u (.vertex (v b).1 (v b).2)), fun c => u (.cell c))) := by
    fun_prop
  have hsplit : splitSeparateNoise = Prod.map (Prod.map id f) id ∘
      (fun u => ((u .global, fun b => u (.vertex (v b).1 (v b).2)),
        fun c => u (.cell c))) := by
    funext u
    simp [v, f]
  rw [hsplit, ← Measure.map_map ((measurable_id.prodMap hf).prodMap measurable_id) hmeas,
    map_global_vertex_cell_noiseMeasure (c := fun t : ℕ × ℕ => t) hv
      Function.injective_id,
    ← Measure.map_prod_map _ _ (measurable_id.prodMap hf) measurable_id, Measure.map_id,
    ← Measure.map_prod_map _ _ measurable_id hf, Measure.map_id,
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
theorem measurable_splitJointNoise : Measurable splitJointNoise := by
  unfold splitJointNoise
  fun_prop

/-- **The joint-coding noise splits into independent pieces**: the global variable, the i.i.d.
vertex variables and the i.i.d. variables of the off-diagonal unordered pairs, indexed by the
increasing pairs, are independent uniform families. -/
@[simp]
theorem map_splitJointNoise_noiseMeasure :
    (noiseMeasure Unit (Sym2 ℕ)).map splitJointNoise =
      ((volume : Measure I).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).prod
        (Measure.infinitePi fun _ : {t : ℕ × ℕ // t.1 < t.2} => (volume : Measure I)) := by
  -- Increasing pairs are sorted, so `Sym2.mk` is injective on them.
  have hc : Function.Injective (fun t : {t : ℕ × ℕ // t.1 < t.2} => s(t.1.1, t.1.2)) :=
    fun t t' h => by
      rcases Sym2.eq_iff.1 h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Subtype.ext (Prod.ext h₁ h₂)
      · have := t.2
        have := t'.2
        omega
  have hsplit : splitJointNoise = fun u =>
      ((u .global, fun k => u (.vertex ((), k).1 ((), k).2)),
        fun t => u (.cell s(t.1.1, t.1.2))) := by
    funext u
    rfl
  rw [hsplit]
  exact map_global_vertex_cell_noiseMeasure (v := fun k => ((), k))
    (fun _ _ h => (Prod.mk.inj h).2) hc

end TauCeti.Probability.AldousHoover

end
