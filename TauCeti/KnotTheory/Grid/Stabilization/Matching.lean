/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Stabilization.Level
public import TauCeti.KnotTheory.Grid.Stabilization.Cone

/-!
# The generator matching for `X`-stabilization

Let `G'` be the `X`-stabilization of a grid diagram `G` at a column `s`. The mapping cone of the
fully blocked comparison from the off-center block to the center block has generators

`G.StabilizeXOffCenterState s ⊕ GridState n`.

These generators are naturally all grid states of `G'`: an off-center generator is already such
a state, while a center generator is sent to the state obtained by inserting the center of the
new block. This file records that equivalence and the fixed-point-free involution obtained by
swapping the two rows of the new block.

The source of each matched pair is selected by the orientation of the cyclic column interval
between the points in those two rows: the source is the endpoint whose height-one rectangle to
its partner avoids the new `O`-marking, so in particular no center generator is a source.
Opposite nondegenerate half-open intervals partition the columns, so exactly one generator in
each pair is a source. The existing stabilization level is constant on each pair because the
swap is realized by a rectangle supported entirely in the row of the new `O`-marking. These facts
provide the matching data needed to prove exactness of the reduced stabilization mapping cone.

## Main definitions

* `TauCeti.GridDiagram.stabilizeXConeStateEquiv`: identifies mapping-cone generators with the
  grid states of the stabilized diagram.
* `TauCeti.GridDiagram.stabilizeXMatching`: swaps the two rows of the stabilization block.
* `TauCeti.GridDiagram.StabilizeXMatchingSource`: selects one endpoint of every matched pair.

## Main results

* `TauCeti.GridDiagram.stabilizeXMatching_involutive`: the matching is an involution.
* `TauCeti.GridDiagram.stabilizeXMatching_ne`: the matching has no fixed points.
* `TauCeti.GridDiagram.stabilizeXMatchingSource_stabilizeXMatching_iff`: exactly one endpoint
  of each pair is a matching source.
* `TauCeti.GridDiagram.not_stabilizeXMatchingSource_inr`: no center generator is a matching
  source.
* `TauCeti.GridDiagram.stabilizeXLevel_swapRows`: the stabilization level is unchanged by
  swapping the two stabilization rows.
* `TauCeti.GridDiagram.stabilizeXLevel_stabilizeXMatching`: the stabilization level is constant on
  matched pairs.

## References

This is the generator matching in the proof of stabilization invariance in
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2, expressed using the
`Q`-filtration from Section 5.2 and Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link
Floer homology*, Section 3.2.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

private theorem stabilizeXCenterState_injective :
    Function.Injective fun x : GridState n =>
      (⟨x.insertPoint s.succ (G.X s).succ, not_not_intro (x.insertPoint_apply_newColumn _ _)⟩ :
        {y : GridState (n + 1) // ¬y s.succ ≠ (G.X s).succ}) :=
  fun _ _ h => GridState.insertPoint_injective _ _ (congrArg Subtype.val h)

private theorem stabilizeXCenterState_surjective :
    Function.Surjective fun x : GridState n =>
      (⟨x.insertPoint s.succ (G.X s).succ, not_not_intro (x.insertPoint_apply_newColumn _ _)⟩ :
        {y : GridState (n + 1) // ¬y s.succ ≠ (G.X s).succ}) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := GridState.exists_insertPoint_eq (not_not.1 hy)
  exact ⟨x, rfl⟩

private noncomputable def stabilizeXCenterStateEquiv :
    GridState n ≃ {y : GridState (n + 1) // ¬y s.succ ≠ (G.X s).succ} :=
  Equiv.ofBijective _
    ⟨G.stabilizeXCenterState_injective s, G.stabilizeXCenterState_surjective s⟩

/-- Mapping-cone generators for the fully blocked `X`-stabilization comparison are naturally the
grid states of the stabilized diagram. The left summand consists of off-center states; the right
summand consists of states obtained by inserting the center of the new block. -/
noncomputable def stabilizeXConeStateEquiv :
    G.StabilizeXOffCenterState s ⊕ GridState n ≃ GridState (n + 1) :=
  ((Equiv.refl _).sumCongr (G.stabilizeXCenterStateEquiv s)).trans
    (Equiv.sumCompl fun y : GridState (n + 1) => y s.succ ≠ (G.X s).succ)

/-- The cone-state equivalence sends an off-center generator to its underlying stabilized state. -/
@[simp]
theorem stabilizeXConeStateEquiv_apply_inl (y : G.StabilizeXOffCenterState s) :
    G.stabilizeXConeStateEquiv s (.inl y) = y.1 := by
  simp [stabilizeXConeStateEquiv]

/-- The cone-state equivalence sends a center generator to the state with the center inserted. -/
@[simp]
theorem stabilizeXConeStateEquiv_apply_inr (x : GridState n) :
    G.stabilizeXConeStateEquiv s (.inr x) = x.insertPoint s.succ (G.X s).succ := by
  simp only [stabilizeXConeStateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.sumCompl_apply_inr]
  exact congrArg Subtype.val (Equiv.ofBijective_apply _ _ x)

/-- The matching on generators of the reduced stabilization mapping cone. Under
`stabilizeXConeStateEquiv`, it swaps the row `(G.X s).castSucc` containing the new `O`-marking
with the following row `(G.X s).succ`. -/
noncomputable def stabilizeXMatching
    (i : G.StabilizeXOffCenterState s ⊕ GridState n) :
    G.StabilizeXOffCenterState s ⊕ GridState n :=
  (G.stabilizeXConeStateEquiv s).symm
    ((G.stabilizeXConeStateEquiv s i).swapRows (G.X s).castSucc (G.X s).succ)

/-- Under the cone-state equivalence, matching a generator swaps the stabilization rows. -/
@[simp]
theorem stabilizeXConeStateEquiv_apply_stabilizeXMatching
    (i : G.StabilizeXOffCenterState s ⊕ GridState n) :
    G.stabilizeXConeStateEquiv s (G.stabilizeXMatching s i) =
      (G.stabilizeXConeStateEquiv s i).swapRows (G.X s).castSucc (G.X s).succ := by
  simp [stabilizeXMatching]

/-- Swapping the two stabilization rows twice returns the original mapping-cone generator. -/
@[simp]
theorem stabilizeXMatching_involutive
    (i : G.StabilizeXOffCenterState s ⊕ GridState n) :
    G.stabilizeXMatching s (G.stabilizeXMatching s i) = i := by
  apply (G.stabilizeXConeStateEquiv s).injective
  simp

/-- The stabilization matching has no fixed points. -/
theorem stabilizeXMatching_ne (i : G.StabilizeXOffCenterState s ⊕ GridState n) :
    G.stabilizeXMatching s i ≠ i := by
  intro h
  have h' := congrArg (G.stabilizeXConeStateEquiv s) h
  rw [G.stabilizeXConeStateEquiv_apply_stabilizeXMatching s] at h'
  let y := G.stabilizeXConeStateEquiv s i
  let c := y.transpose (G.X s).castSucc
  have hc : y c = (G.X s).castSucc := y.apply_transpose_apply _
  have := congrArg (fun z : GridState (n + 1) => z c) h'
  simp only [GridState.swapRows_apply] at this
  rw [hc, Equiv.swap_apply_left] at this
  exact (ne_of_lt (G.X s).castSucc_lt_succ) this.symm

/-- A generator is the source of its matching edge when the stabilization column lies in the
clockwise half-open interval from the column occupied in row `(G.X s).succ` to the column
occupied in row `(G.X s).castSucc`. Equivalently, the height-one rectangle from the generator to
its partner, which covers the complementary interval in the row of the new `O`-marking, avoids
that marking. -/
def StabilizeXMatchingSource
    (i : G.StabilizeXOffCenterState s ⊕ GridState n) : Prop :=
  s.castSucc ∈ Grid.cIco
    ((G.stabilizeXConeStateEquiv s i).transpose (G.X s).succ)
    ((G.stabilizeXConeStateEquiv s i).transpose (G.X s).castSucc)

private theorem stabilizeXMatching_transpose_castSucc
    (i : G.StabilizeXOffCenterState s ⊕ GridState n) :
    (G.stabilizeXConeStateEquiv s (G.stabilizeXMatching s i)).transpose (G.X s).castSucc =
      (G.stabilizeXConeStateEquiv s i).transpose (G.X s).succ := by
  rw [G.stabilizeXConeStateEquiv_apply_stabilizeXMatching s, GridState.swapRows_transpose]
  simp

private theorem stabilizeXMatching_transpose_succ
    (i : G.StabilizeXOffCenterState s ⊕ GridState n) :
    (G.stabilizeXConeStateEquiv s (G.stabilizeXMatching s i)).transpose (G.X s).succ =
      (G.stabilizeXConeStateEquiv s i).transpose (G.X s).castSucc := by
  rw [G.stabilizeXConeStateEquiv_apply_stabilizeXMatching s, GridState.swapRows_transpose]
  simp

/-- Exactly one endpoint of every matched pair is selected as a matching source. -/
@[simp]
theorem stabilizeXMatchingSource_stabilizeXMatching_iff
    (i : G.StabilizeXOffCenterState s ⊕ GridState n) :
    G.StabilizeXMatchingSource s (G.stabilizeXMatching s i) ↔
      ¬G.StabilizeXMatchingSource s i := by
  rw [StabilizeXMatchingSource, StabilizeXMatchingSource,
    G.stabilizeXMatching_transpose_castSucc s, G.stabilizeXMatching_transpose_succ s]
  let a := (G.stabilizeXConeStateEquiv s i).transpose (G.X s).castSucc
  let b := (G.stabilizeXConeStateEquiv s i).transpose (G.X s).succ
  have hab : a ≠ b := fun h =>
    (ne_of_lt (G.X s).castSucc_lt_succ)
      ((G.stabilizeXConeStateEquiv s i).transpose.toPerm.injective h)
  constructor
  · exact fun ha hb => Finset.disjoint_left.1 (Grid.disjoint_cIco_swap a b) ha hb
  · intro hb
    have hmem : s.castSucc ∈ Grid.cIco a b ∪ Grid.cIco b a := by
      rw [Grid.cIco_union_swap hab]
      simp
    exact (Finset.mem_union.1 hmem).resolve_right hb

/-- A center generator is never a matching source: its partner is off-center, and the mapping
cone has no component from the center block to the off-center block. -/
@[simp]
theorem not_stabilizeXMatchingSource_inr (x : GridState n) :
    ¬G.StabilizeXMatchingSource s (.inr x) := by
  rw [StabilizeXMatchingSource, stabilizeXConeStateEquiv_apply_inr]
  set y := x.insertPoint s.succ (G.X s).succ
  have hb : y.transpose (G.X s).succ = s.succ := by
    rw [← GridState.transpose_apply_apply y s.succ]
    simp [y]
  have ha : y.transpose (G.X s).castSucc ≠ s.succ := fun h =>
    (ne_of_lt (G.X s).castSucc_lt_succ) (by rw [← hb] at h; exact y.transpose.toPerm.injective h)
  rw [hb]
  generalize y.transpose (G.X s).castSucc = a at ha
  have ha' : a.val ≠ s.val + 1 := fun h => ha (Fin.ext (by simpa using h))
  rw [Grid.mem_cIco]
  split_ifs with h <;> simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢ <;> omega

private theorem stabilizeXRowSwapRectangle_coveredRows (y : GridState (n + 1)) :
    let a := y.transpose (G.X s).castSucc
    let b := y.transpose (G.X s).succ
    let R : GridRectangleBetween y (y.swapRows (G.X s).castSucc (G.X s).succ) :=
      GridRectangleBetween.ofSwapColumns y _ a b
        (fun h => (ne_of_lt (G.X s).castSucc_lt_succ) (y.transpose.toPerm.injective h)) (by
          rw [GridState.swapColumns_eq_swapRows, y.apply_transpose_apply,
            y.apply_transpose_apply])
    R.toGridRectangle.coveredRows = {(G.X s).castSucc} := by
  dsimp only
  rw [GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_bottom,
    GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.ofSwapColumns_bottom,
    GridRectangleBetween.ofSwapColumns_top]
  simp only [GridState.apply_transpose_apply]
  rw [Grid.cIco_eq_singleton_iff]
  refine ⟨rfl, ?_, ne_of_lt (G.X s).castSucc_lt_succ⟩
  rw [finRotate_apply]
  apply Fin.ext
  simp

/-- The stabilization level is unchanged by swapping the two stabilization rows. The swap is
realized by a rectangle covering only the row of the new `O`-marking and hence no outer square. -/
@[simp]
theorem stabilizeXLevel_swapRows (y : GridState (n + 1)) :
    G.stabilizeXLevel s (y.swapRows (G.X s).castSucc (G.X s).succ) = G.stabilizeXLevel s y := by
  let a := y.transpose (G.X s).castSucc
  let b := y.transpose (G.X s).succ
  have hab : a ≠ b := fun h =>
    (ne_of_lt (G.X s).castSucc_lt_succ) (y.transpose.toPerm.injective h)
  have htarget : y.swapRows (G.X s).castSucc (G.X s).succ = y.swapColumns a b := by
    rw [GridState.swapColumns_eq_swapRows, y.apply_transpose_apply, y.apply_transpose_apply]
  let R : GridRectangleBetween y (y.swapRows (G.X s).castSucc (G.X s).succ) :=
    GridRectangleBetween.ofSwapColumns y _ a b hab htarget
  symm
  apply G.stabilizeXLevel_eq_of_disjoint s R
  rw [Finset.disjoint_left]
  intro q hq houter
  have hrow : q.2 = (G.X s).castSucc := by
    have : q.2 ∈ R.toGridRectangle.coveredRows :=
      (GridRectangle.mem_coveredSquares R.toGridRectangle q).1 hq |>.2
    rw [G.stabilizeXRowSwapRectangle_coveredRows s y, Finset.mem_singleton] at this
    exact this
  exact ((G.mem_stabilizeXOuterSquares s q).1 houter).2 hrow

/-- The stabilization level is constant on matched pairs. -/
theorem stabilizeXLevel_stabilizeXMatching
    (i : G.StabilizeXOffCenterState s ⊕ GridState n) :
    G.stabilizeXLevel s (G.stabilizeXConeStateEquiv s (G.stabilizeXMatching s i)) =
      G.stabilizeXLevel s (G.stabilizeXConeStateEquiv s i) := by
  rw [G.stabilizeXConeStateEquiv_apply_stabilizeXMatching s, stabilizeXLevel_swapRows]

end GridDiagram

end TauCeti
