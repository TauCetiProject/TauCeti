/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Strip.Cell.Context
public import TauCeti.Probability.Exchangeability.Arrays.Strip.VisibleCells
import TauCeti.Probability.Exchangeability.Arrays.Block.Independence
import TauCeti.Probability.Independence.Conditional
import TauCeti.Probability.Kernel.ConditionalRandomization

/-!
# One cell kernel codes every visible cell of an exchangeable array

Split the rows and the columns of a separately exchangeable array into the hidden indices
enumerated by `e` and `f` and their visible complements. The *crossing strips* are all array
positions lying in a hidden row or in a hidden column; a visible cell `(i, j)` meets them in its
own `cellContext e f i j`, the hidden block together with the hidden part of row `i` and the
hidden part of column `j`.

Given that context, the cell is conditionally independent of all the remaining crossing strips:
the strips of the other visible rows and columns say nothing more about it. Together with the
conditional independence of distinct visible cells and with the common conditional cell kernel,
this turns the cell layer into a genuine coding: a **single** measurable function of a context
and a uniform variable generates every visible cell at once, each from its own context and its
own fresh uniform variable, jointly with the crossing strips. That is the strengthening a
representation needs over a family of codings chosen separately at each position, which is all
that conditional independence given the strips gives by itself.

This is the cell noise of the Aldous–Hoover representation of a separately exchangeable array,
with the position-independent coding function the representation asks for; the global noise and
the row and column noises are supplied by the block and vertex strip codings.

## Main results

* `TauCeti.Probability.SeparatelyExchangeable.condIndepFun_cell_crossingStrips` — a visible cell
  is conditionally independent of the crossing strips given its own context.
* `TauCeti.Probability.SeparatelyExchangeable.exists_common_visibleCells_coding` — one common
  coding function generates every finite family of visible cells from their contexts and
  independent uniform variables.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581–598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α]

section Context

variable (e f : ℕ → ℕ) (i j : ℕ)

/-- The cell context of `(i, j)` read off the crossing strips: every position the context looks
at lies in a hidden row or in a hidden column. -/
private def cellContextOfStrips
    (y : (((Set.univ ×ˢ Set.range f) ∪ (Set.range e ×ˢ Set.univ) : Set (ℕ × ℕ))) → α) :
    ((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α) :=
  ((fun q => y ⟨(e q.1, f q.2),
      Set.mem_union_right _ ⟨Set.mem_range_self q.1, Set.mem_univ _⟩⟩,
    fun b => y ⟨(i, f b), Set.mem_union_left _ ⟨Set.mem_univ _, Set.mem_range_self b⟩⟩),
    fun a => y ⟨(e a, j), Set.mem_union_right _ ⟨Set.mem_range_self a, Set.mem_univ _⟩⟩)

private theorem measurable_cellContextOfStrips :
    Measurable (cellContextOfStrips (α := α) e f i j) :=
  ((Measurable.of_eval fun _ => measurable_pi_apply _).prodMk
      (Measurable.of_eval fun _ => measurable_pi_apply _)).prodMk
    (Measurable.of_eval fun _ => measurable_pi_apply _)

omit [MeasurableSpace α] in
private theorem cellContextOfStrips_comp :
    cellContextOfStrips (α := α) e f i j ∘
        (((Set.univ ×ˢ Set.range f) ∪ (Set.range e ×ˢ Set.univ) : Set (ℕ × ℕ))).domRestrict =
      cellContext e f i j := by
  funext x
  refine Prod.ext (Prod.ext (funext fun q => ?_) (funext fun b => ?_)) (funext fun a => ?_) <;>
    simp [cellContextOfStrips]

/-- The entries on the strips adjacent to `(i, j)` read off the cell context, by inverting the
two hidden enumerations. -/
private def cellStripsOfContext (z : ((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) :
    ((insert i (Set.range e) ×ˢ insert j (Set.range f) \ {(i, j)} : Set (ℕ × ℕ))) → α :=
  fun q =>
    if q.1.1 = i then z.1.2 (Function.invFun f q.1.2)
    else if q.1.2 = j then z.2 (Function.invFun e q.1.1)
    else z.1.1 (Function.invFun e q.1.1, Function.invFun f q.1.2)

private theorem measurable_cellStripsOfContext :
    Measurable (cellStripsOfContext (α := α) e f i j) := by
  refine Measurable.of_eval fun q => ?_
  simp only [cellStripsOfContext]
  split_ifs
  · exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_fst)
  · exact (measurable_pi_apply _).comp measurable_snd
  · exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_fst)

omit [MeasurableSpace α] in
private theorem cellStripsOfContext_comp :
    cellStripsOfContext (α := α) e f i j ∘ cellContext e f i j =
      (insert i (Set.range e) ×ˢ insert j (Set.range f) \ {(i, j)} : Set (ℕ × ℕ)).domRestrict := by
  funext x q
  obtain ⟨⟨q₁, q₂⟩, ⟨hq₁, hq₂⟩, hqne⟩ := q
  simp only [Set.mem_singleton_iff, Prod.mk.injEq, not_and] at hqne
  simp only [Function.comp_apply, Set.domRestrict_apply, cellStripsOfContext]
  by_cases h₁ : q₁ = i
  · have hq₂' : q₂ ∈ Set.range f := (Set.mem_insert_iff.1 hq₂).resolve_left (hqne h₁)
    simp [h₁, Function.invFun_eq hq₂']
  · have hq₁' : q₁ ∈ Set.range e := (Set.mem_insert_iff.1 hq₁).resolve_left h₁
    by_cases h₂ : q₂ = j
    · simp [h₁, h₂, Function.invFun_eq hq₁']
    · have hq₂' : q₂ ∈ Set.range f := (Set.mem_insert_iff.1 hq₂).resolve_left h₂
      simp [h₁, h₂, Function.invFun_eq hq₁', Function.invFun_eq hq₂']

end Context

variable [StandardBorelSpace α] [Nonempty α]
  {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]

omit [Nonempty α] in
/-- **A visible cell sees the crossing strips only through its own context.** Let `e` and `f`
enumerate infinitely many hidden rows and hidden columns of a separately exchangeable array, and
let `(i, j)` be a cell outside both hidden ranges. Given the hidden block together with the
hidden part of row `i` and the hidden part of column `j`, the entry at `(i, j)` is conditionally
independent of *all* entries in hidden rows or hidden columns: the strips of the other visible
rows and columns carry no further information about it. -/
theorem SeparatelyExchangeable.condIndepFun_cell_crossingStrips
    (hρ : SeparatelyExchangeable ρ fun p x => x p) {e f : ℕ → ℕ}
    (he : (Set.range e).Infinite) (hf : (Set.range f).Infinite)
    {i j : ℕ} (hi : i ∉ Set.range e) (hj : j ∉ Set.range f) :
    CondIndepFun (MeasurableSpace.comap (cellContext e f i j) inferInstance)
      (measurable_cellContext e f i j).comap_le
      (fun x : ℕ × ℕ → α => x (i, j))
      ((Set.univ ×ˢ Set.range f) ∪ (Set.range e ×ˢ Set.univ) :
        Set (ℕ × ℕ)).domRestrict ρ := by
  -- The cell context and the entries on the strips adjacent to `(i, j)` generate the same
  -- information, and that information is part of the crossing strips.
  have hRC : MeasurableSpace.comap
      ((insert i (Set.range e) ×ˢ insert j (Set.range f) \ {(i, j)} :
        Set (ℕ × ℕ)).domRestrict (π := fun _ => α)) inferInstance ≤
      MeasurableSpace.comap (cellContext (α := α) e f i j) inferInstance := by
    rw [← cellStripsOfContext_comp (α := α) e f i j, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_cellStripsOfContext e f i j).comap_le
  have hCH : MeasurableSpace.comap (cellContext (α := α) e f i j) inferInstance ≤
      MeasurableSpace.comap
        (((Set.univ ×ˢ Set.range f) ∪ (Set.range e ×ˢ Set.univ) :
          Set (ℕ × ℕ)).domRestrict (π := fun _ => α)) inferInstance := by
    rw [← cellContextOfStrips_comp (α := α) e f i j, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_cellContextOfStrips e f i j).comap_le
  -- The one-cell block is conditionally independent of everything outside it, given the rest of
  -- the rectangle spanned by the hidden indices together with `i` and `j`.
  have hbase := hρ.condIndepFun_domRestrict_subblock_compl_of_finite_block_of_subset
    (S := insert i (Set.range e)) (T := insert j (Set.range f))
    (B := {(i, j)}) (C := {(i, j)}) (he.mono (Set.subset_insert _ _))
    (hf.mono (Set.subset_insert _ _)) (Set.finite_singleton _) Set.Subset.rfl
    (Set.singleton_subset_iff.2 ⟨Set.mem_insert _ _, Set.mem_insert _ _⟩)
  rw [condIndepFun_iff_condIndep] at hbase
  have hHsub : ((Set.univ ×ˢ Set.range f) ∪ (Set.range e ×ˢ Set.univ) : Set (ℕ × ℕ)) ⊆
      ({(i, j)} : Set (ℕ × ℕ))ᶜ := by
    rintro p hp hpc
    rw [Set.mem_singleton_iff] at hpc
    subst hpc
    rcases hp with hp | hp
    · exact hj hp.2
    · exact hi hp.1
  have hHC : MeasurableSpace.comap
      (((Set.univ ×ˢ Set.range f) ∪ (Set.range e ×ˢ Set.univ) :
        Set (ℕ × ℕ)).domRestrict (π := fun _ => α)) inferInstance ≤
      MeasurableSpace.comap
        ((({(i, j)} : Set (ℕ × ℕ))ᶜ).domRestrict (π := fun _ => α)) inferInstance := by
    rw [← Set.domRestrict₂_comp_domRestrict hHsub, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Set.measurable_restrict₂ hHsub).comap_le
  have hcell : MeasurableSpace.comap (fun x : ℕ × ℕ → α => x (i, j)) inferInstance ≤
      MeasurableSpace.comap
        (({(i, j)} : Set (ℕ × ℕ)).domRestrict (π := fun _ => α)) inferInstance := by
    have hread : (fun x : ℕ × ℕ → α => x (i, j)) =
        (fun y : ({(i, j)} : Set (ℕ × ℕ)) → α => y ⟨(i, j), rfl⟩) ∘
          ({(i, j)} : Set (ℕ × ℕ)).domRestrict := rfl
    rw [hread, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  have hstep := condIndep_of_condIndep_of_le_right
    (condIndep_of_condIndep_of_le_left hbase hcell) hHC
  rw [condIndepFun_iff_condIndep]
  exact condIndep_of_condIndep_of_le_of_le (measurable_pi_apply (i, j)).comap_le
    (Set.measurable_restrict _).comap_le (Set.measurable_restrict _).comap_le hstep hRC hCH

/-- The crossing-strip coding of a single visible cell: feeding the cell's context and one fresh
uniform variable to a realization of the common conditional cell kernel reproduces the joint law
of the crossing strips and that cell. -/
private theorem map_prod_cellCoding_eq
    (hρ : SeparatelyExchangeable ρ fun p x => x p) {e f : ℕ → ℕ}
    (he : (Set.range e).Infinite) (hf : (Set.range f).Infinite)
    {i j : ℕ} (hi : i ∉ Set.range e) (hj : j ∉ Set.range f)
    {g : ((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α) → I → α} (hg : Measurable (Function.uncurry g))
    (hgmap : ∀ z, (volume : Measure I).map (g z) =
      condDistrib (fun x : ℕ × ℕ → α => x (i, j)) (cellContext e f i j) ρ z) :
    ((ρ.map ((Set.univ ×ˢ Set.range f) ∪ (Set.range e ×ˢ Set.univ) :
          Set (ℕ × ℕ)).domRestrict).prod (volume : Measure I)).map
        (fun q => (q.1, g (cellContextOfStrips e f i j q.1) q.2)) =
      ρ.map fun x => (((Set.univ ×ˢ Set.range f) ∪ (Set.range e ×ˢ Set.univ) :
        Set (ℕ × ℕ)).domRestrict x, x (i, j)) := by
  set H : Set (ℕ × ℕ) := (Set.univ ×ˢ Set.range f) ∪ (Set.range e ×ˢ Set.univ)
  have hZ : Measurable (H.domRestrict (π := fun _ : ℕ × ℕ => α)) := Set.measurable_restrict H
  have hΦ : Measurable (cellContextOfStrips (α := α) e f i j) :=
    measurable_cellContextOfStrips e f i j
  have hψ : Measurable fun y : H → α => (cellContextOfStrips (α := α) e f i j y, y) :=
    hΦ.prodMk measurable_id
  set κ := condDistrib (fun x : ℕ × ℕ → α => x (i, j)) (cellContext e f i j) ρ
  -- Conditionally on its context, the cell forgets the rest of the crossing strips, so the joint
  -- law of the context, the strips and the cell disintegrates through the context kernel.
  have hjoint : ρ.map (fun x => ((cellContext e f i j x, H.domRestrict x), x (i, j))) =
      (ρ.map fun x => (cellContext e f i j x, H.domRestrict x)) ⊗ₘ κ.prodMkRight (H → α) := by
    refine (condDistrib_ae_eq_iff_measure_eq_compProd
      (((measurable_cellContext e f i j).prodMk hZ).aemeasurable)
      (measurable_pi_apply (i, j)).aemeasurable _).1 ?_
    exact (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight (measurable_pi_apply (i, j)) hZ
      (measurable_cellContext e f i j)).1
      (hρ.condIndepFun_cell_crossingStrips he hf hi hj).symm
  -- One uniform variable realizes that kernel, uniformly in the context.
  have hcode : ((ρ.map fun x => (cellContext e f i j x, H.domRestrict x)).prod
      (volume : Measure I)).map (fun q => (q.1, g q.1.1 q.2)) =
      (ρ.map fun x => (cellContext e f i j x, H.domRestrict x)) ⊗ₘ κ.prodMkRight (H → α) :=
    (κ.prodMkRight (H → α)).map_prod_eq_compProd_of_map _ (fun w => g w.1)
      (hg.comp (measurable_fst.prodMap measurable_id)) fun w => hgmap w.1
  -- The context is a function of the strips, so it can be dropped from the joint law.
  have hlaw : (ρ.map fun x => (cellContext e f i j x, H.domRestrict x)) =
      (ρ.map H.domRestrict).map fun y => (cellContextOfStrips (α := α) e f i j y, y) := by
    rw [Measure.map_map hψ hZ]
    congr 1
    rw [← cellContextOfStrips_comp (α := α) e f i j]
    rfl
  have hprod : ((ρ.map H.domRestrict).map
        fun y => (cellContextOfStrips (α := α) e f i j y, y)).prod (volume : Measure I) =
      ((ρ.map H.domRestrict).prod (volume : Measure I)).map
        (Prod.map (fun y : H → α => (cellContextOfStrips (α := α) e f i j y, y)) id) := by
    simpa using Measure.map_prod_map (ρ.map H.domRestrict) (volume : Measure I) hψ measurable_id
  -- measurability of the three maps the calculation pushes measures along
  have hdrop : Measurable fun w : ((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) × (H → α)) × α =>
      (w.1.2, w.2) := (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hpair : Measurable fun q : ((((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α)) × (H → α)) × I =>
      (q.1, g q.1.1 q.2) :=
    measurable_fst.prodMk (hg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hjointMeas : Measurable fun x : ℕ × ℕ → α =>
      ((cellContext e f i j x, H.domRestrict x), x (i, j)) :=
    ((measurable_cellContext e f i j).prodMk hZ).prodMk (measurable_pi_apply (i, j))
  calc ((ρ.map H.domRestrict).prod (volume : Measure I)).map
        (fun q => (q.1, g (cellContextOfStrips e f i j q.1) q.2))
      = ((((ρ.map H.domRestrict).map
            fun y => (cellContextOfStrips (α := α) e f i j y, y)).prod
          (volume : Measure I)).map (fun q => (q.1, g q.1.1 q.2))).map
            fun w => (w.1.2, w.2) := by
        rw [hprod, Measure.map_map hpair (hψ.prodMap measurable_id), Measure.map_map hdrop
          (hpair.comp (hψ.prodMap measurable_id))]
        rfl
    _ = (ρ.map fun x => ((cellContext e f i j x, H.domRestrict x), x (i, j))).map
          fun w => (w.1.2, w.2) := by
        rw [← hlaw, hcode, hjoint]
    _ = ρ.map fun x => (H.domRestrict x, x (i, j)) := by
        rw [Measure.map_map hdrop hjointMeas]
        rfl

/-- **Every visible cell of a separately exchangeable array is generated from its own hidden
context by one common coding function and one fresh uniform variable.** Let `e` and `f` enumerate
infinitely many hidden rows and hidden columns. There is a single measurable `g` such that, for
every finite family of visible cells, feeding each cell's `cellContext` and its own independent
uniform variable to `g` reproduces the joint law of the crossing strips and that whole family of
cells.

The coding function does not depend on the position of the cell, which is what lets it serve as
the cell noise `U i j` of an Aldous–Hoover representation. -/
theorem SeparatelyExchangeable.exists_common_visibleCells_coding
    (hρ : SeparatelyExchangeable ρ fun p x => x p) {e f : ℕ → ℕ}
    (he : (Set.range e).Infinite) (hf : (Set.range f).Infinite) :
    let H : Set (ℕ × ℕ) := (Set.univ ×ˢ Set.range f) ∪ (Set.range e ×ˢ Set.univ)
    let V : Set (ℕ × ℕ) := (Set.range e)ᶜ ×ˢ (Set.range f)ᶜ
    ∃ g : ((ℕ × ℕ → α) × (ℕ → α)) × (ℕ → α) → I → α, Measurable (Function.uncurry g) ∧
      ∀ F : Finset V,
        (ρ.prod (Measure.pi fun _ : F => (volume : Measure I))).map
            (fun q => (H.domRestrict q.1,
              fun p : F => g (cellContext e f p.1.1.1 p.1.1.2 q.1) (q.2 p))) =
          ρ.map fun x => (H.domRestrict x, fun p : F => x p.1.1) := by
  intro H V
  rcases Set.eq_empty_or_nonempty V with hV | ⟨⟨i₀, j₀⟩, hi₀, hj₀⟩
  · -- If the hidden rows or the hidden columns exhaust their index set, there is no visible cell:
    -- every finite family is then empty and the claim only compares the law of the crossing
    -- strips with itself, so any measurable constant coding serves.
    have : IsEmpty V := Set.isEmpty_coe_sort.2 hV
    refine ⟨fun _ _ => Classical.arbitrary α, measurable_const, fun F => ?_⟩
    have : IsEmpty F := ⟨fun p => isEmptyElim p.1⟩
    have hstrips : Measurable fun x : ℕ × ℕ → α => (H.domRestrict x, fun p : F => x p.1.1) :=
      (Set.measurable_restrict H).prodMk (Measurable.of_eval fun p => measurable_pi_apply p.1.1)
    have hfactor : (fun q : (ℕ × ℕ → α) × (F → I) =>
          (H.domRestrict q.1, fun _ : F => Classical.arbitrary α)) =
        (fun x : ℕ × ℕ → α => (H.domRestrict x, fun p : F => x p.1.1)) ∘ Prod.fst :=
      funext fun q => Prod.ext rfl (Subsingleton.elim _ _)
    rw [hfactor, ← Measure.map_map hstrips measurable_fst, Measure.map_fst_prod]
    simp
  obtain ⟨g, hg, hgmap⟩ := hρ.exists_common_cell_coding e f hi₀ hj₀
  refine ⟨g, hg, fun F => ?_⟩
  have hZ : Measurable (H.domRestrict (π := fun _ : ℕ × ℕ => α)) := Set.measurable_restrict H
  -- Distinct visible cells are conditionally independent given the crossing strips.
  have hall := hρ.iCondIndepFun_visibleCells he hf
  have hF : iCondIndepFun (MeasurableSpace.comap H.domRestrict inferInstance)
      (Set.measurable_restrict H).comap_le
      (fun p : F => fun x : ℕ × ℕ → α => x p.1.1) ρ :=
    Kernel.iIndepFun.precomp Subtype.val_injective hall
  -- Each of them is coded from its own context by the common coding function.
  have hglue := hF.map_prod_pi_eq_of_map_prod_eq hZ
    (fun p : F => measurable_pi_apply p.1.1)
    (ρ := fun _ : F => (volume : Measure I))
    (f := fun p : F => fun y u => g (cellContextOfStrips e f p.1.1.1 p.1.1.2 y) u)
    (fun p => hg.comp ((measurable_cellContextOfStrips e f p.1.1.1 p.1.1.2).comp
      measurable_fst |>.prodMk measurable_snd))
    fun p => map_prod_cellCoding_eq hρ he hf p.1.2.1 p.1.2.2 hg
      (fun z => hgmap p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 z)
  have hcoded : Measurable fun p : (H → α) × (F → I) =>
      (p.1, fun r : F => g (cellContextOfStrips e f r.1.1.1 r.1.1.2 p.1) (p.2 r)) :=
    measurable_fst.prodMk (Measurable.of_eval fun r => hg.comp
      (((measurable_cellContextOfStrips e f r.1.1.1 r.1.1.2).comp measurable_fst).prodMk
        ((measurable_pi_apply r).comp measurable_snd)))
  -- The strips are read off `ρ` itself, so the law of the strips paired with the uniform family
  -- is the image of `ρ` paired with that family: the restriction only acts on the first factor.
  have hprod : (ρ.map H.domRestrict).prod (Measure.pi fun _ : F => (volume : Measure I)) =
      (ρ.prod (Measure.pi fun _ : F => (volume : Measure I))).map (Prod.map H.domRestrict id) := by
    simpa using
      Measure.map_prod_map ρ (Measure.pi fun _ : F => (volume : Measure I)) hZ measurable_id
  rw [hprod, Measure.map_map hcoded (hZ.prodMap measurable_id)] at hglue
  refine Eq.trans (congrArg (Measure.map · _) ?_) hglue
  funext q
  refine Prod.ext rfl (funext fun p => ?_)
  exact congrArg (g · (q.2 p))
    (congrFun (cellContextOfStrips_comp (α := α) e f p.1.1.1 p.1.1.2) q.1).symm

end TauCeti.Probability

end

end
