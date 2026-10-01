/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Stabilization.Map
public import TauCeti.KnotTheory.Grid.Stabilization.Matching
public import TauCeti.KnotTheory.Grid.Stabilization.Reduction
public import TauCeti.KnotTheory.Grid.XHomotopy.Basic
import TauCeti.Algebra.Homology.SquareZero.Contraction
import TauCeti.KnotTheory.Grid.Rectangle.Count

/-!
# Stabilization invariance: the reduced comparison is a quasi-isomorphism

Let `G' = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization of a grid diagram `G`
splitting the `X`-marking of column `s`, write `κ = s.castSucc`, `ρ = (G.X s).castSucc`, and
`ρ' = (G.X s).succ` for the row above `ρ`. `TauCeti.KnotTheory.Grid.Stabilization.Reduction`
reduces stabilization invariance of `GH⁻` along `G'` to one statement over the coefficient ring
`R` with every variable set to zero: the reduced `H_I^N`, from the reduced off-center complex
(fully blocked rectangles of `G'` between states not containing the center `(s.succ, ρ')` of the
new block) to the reduced center complex (fully blocked rectangles of `G`), induces a bijection on
homology. This file proves that statement, so `H_I^N` is a quasi-isomorphism without further
hypotheses. With the instance `TauCeti.GridDiagram.quasiIso_stabilizeXMap`, the comparison map
`GC⁻(G') ⟶ GC⁻(G)` is then a quasi-isomorphism.

The proof shows that the mapping cone of the reduced `H_I^N`, a square-zero endomorphism of the
free module on the generators `G.StabilizeXOffCenterState s ⊕ GridState n`, is exact
(`LinearMap.ker_le_range_mappingCone_iff`), by the matching criterion
`LinearMap.ker_le_range_of_matching` applied to the generator matching of
`TauCeti.KnotTheory.Grid.Stabilization.Matching`: the involution
`TauCeti.GridDiagram.stabilizeXMatching` swapping the rows `ρ` and `ρ'`, with the sources
`TauCeti.GridDiagram.StabilizeXMatchingSource`. It remains to show that every term of the cone
strictly lowers a weight except the edges of this matching, which have coefficient one.

Generators are weighted lexicographically by the level of their underlying state of `G'`
(`GridDiagram.stabilizeXLevel`), which is constant on matched pairs
(`GridDiagram.stabilizeXLevel_stabilizeXMatching`), and by the position of the row the state
uses in column `s.succ`, read cyclically from the row above `ρ'` (`Grid.cyclicPosition`), a
center generator getting the position of `ρ`. The terms of equal weight are the row swaps, along
the thin rectangle in row `ρ` between a state and its row swap
(`GridDiagram.stabilizeXRowSwapRectangle`); the other rectangles covering no outer square are
width-one moves in column `κ`, which lower the position. A row swap term of the cone is a
matching edge:

* between off-center states using neither `ρ` nor `ρ'` in column `s.succ`, the thin rectangle
  from the source avoids the markings `O_new = (κ, ρ)` and `X₂ = (s.succ, ρ)` of row `ρ`, while
  the one from its partner covers them;
* an off-center state using `ρ` in column `s.succ` is a source, matched with the center state of
  its row swap along the thin rectangle through `X₂` counted by the reduced `H_I^N`.

## Main results

* `TauCeti.GridDiagram.homologyMap_constantCoeffReduction_stabilizeXOffCenterToCenter_bijective`:
  the reduced `H_I^N` induces a bijection on homology.
* `TauCeti.GridDiagram.quasiIso_stabilizeXOffCenterToCenterHom`: `H_I^N` is a quasi-isomorphism.

## References

The statement is stabilization invariance in the form of Ozsváth--Stipsicz--Szabó, *Grid Homology
for Knots and Links*, Section 5.2, for the fully blocked comparison. The weight refines the
`Q`-filtration of Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*,
Geom. Topol. 11 (2007), Section 3.2. Where MOST split the associated graded complex, the leading
terms are here matched by row swaps, in the sense of algebraic discrete Morse theory (Sköldberg,
Trans. Amer. Math. Soc. 358 (2006)).
-/

public section

open MvPolynomial Finsupp

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

/-! ### The row swap rectangle -/

/-- A state whose row swap avoids the row `(G.X s).succ` in column `s.succ` does not use the row
`(G.X s).castSucc` there. -/
private theorem apply_succ_ne_castSucc_of_swapRows_apply_ne {y : GridState (n + 1)}
    (h : y.swapRows (G.X s).castSucc (G.X s).succ s.succ ≠ (G.X s).succ) :
    y s.succ ≠ (G.X s).castSucc := fun hy ↦ h (by
  rw [GridState.swapRows_apply, hy, Equiv.swap_apply_left])

/-- A state whose row swap is a center insertion uses the row `(G.X s).castSucc` in column
`s.succ`. -/
private theorem apply_succ_eq_castSucc_of_insertPoint_eq_swapRows {x : GridState n}
    {y : GridState (n + 1)}
    (h : x.insertPoint s.succ (G.X s).succ = y.swapRows (G.X s).castSucc (G.X s).succ) :
    y s.succ = (G.X s).castSucc := by
  have h := congrArg (fun z : GridState (n + 1) ↦ z s.succ) h
  simp only [GridState.insertPoint_apply_newColumn, GridState.swapRows_apply] at h
  rwa [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h

/-! ### Rectangles to the row swap -/

/-- The row swap rectangle is fully blocked exactly when its columns avoid the two marked columns
`s.castSucc` and `s.succ` of the row `(G.X s).castSucc`. -/
private theorem stabilizeXRowSwapRectangle_mem_fullyBlockedRectangles_iff (y : GridState (n + 1)) :
    G.stabilizeXRowSwapRectangle s y ∈
        (G.stabilizeX s.castSucc (G.X s).castSucc s).fullyBlockedRectangles y
          (y.swapRows (G.X s).castSucc (G.X s).succ) ↔
      s.castSucc ∉ Grid.cIco (y.transpose (G.X s).castSucc) (y.transpose (G.X s).succ) ∧
        s.succ ∉ Grid.cIco (y.transpose (G.X s).castSucc) (y.transpose (G.X s).succ) := by
  rw [mem_fullyBlockedRectangles, GridRectangleBetween.AvoidsMarkings,
    GridRectangle.avoidsMarkings_iff_forall, coveredRows_stabilizeXRowSwapRectangle]
  simp only [iff_true_intro (G.isEmpty_stabilizeXRowSwapRectangle s y), true_and,
    Finset.mem_singleton, stabilizeX_O, stabilizeX_X, stabilizeX_O_eq_castSucc_iff,
    stabilizeX_X_eq_castSucc_iff, GridRectangle.mem_coveredColumns,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    stabilizeXRowSwapRectangle_left, stabilizeXRowSwapRectangle_right]
  constructor
  · exact fun h ↦ ⟨fun hk ↦ (h _ hk).1 rfl, fun hk ↦ (h _ hk).2 rfl⟩
  · rintro ⟨h₁, h₂⟩ c hc
    exact ⟨by rintro rfl; exact h₁ hc, by rintro rfl; exact h₂ hc⟩

/-- The side swap of the row swap rectangle covers every row but `(G.X s).castSucc`, so it covers
one of the two markings of its initial column. -/
private theorem not_avoidsMarkings_swapSides_stabilizeXRowSwapRectangle
    (y : GridState (n + 1)) :
    ¬(G.stabilizeXRowSwapRectangle s y).swapSides.AvoidsMarkings
      (G.stabilizeX s.castSucc (G.X s).castSucc s) := by
  set t := (G.stabilizeXRowSwapRectangle s y).swapSides
  intro h
  have hrow (r : Fin (n + 1)) (hr : r ≠ (G.X s).castSucc) : r ∈ t.toGridRectangle.coveredRows := by
    have : r.val ≠ (G.X s).val := fun e ↦ hr (Fin.ext e)
    simp only [t, GridRectangle.mem_coveredRows, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.swapSides_bottom,
      GridRectangleBetween.swapSides_top, stabilizeXRowSwapRectangle_bottom,
      stabilizeXRowSwapRectangle_top, Grid.mem_cIco, Fin.val_succ, Fin.val_castSucc, ne_eq,
      Fin.ext_iff]
    split_ifs <;> omega
  have hl := (GridRectangle.avoidsMarkings_iff_forall _ _).mp h t.left
    (Grid.left_mem_cIco t.left_ne_right)
  rcases eq_or_ne ((G.stabilizeX s.castSucc (G.X s).castSucc s).O t.left) (G.X s).castSucc
    with hO | hO
  · exact hl.2 (hrow _ fun hX ↦
      (G.stabilizeX s.castSucc (G.X s).castSucc s).disjoint t.left (hO.trans hX.symm))
  · exact hl.1 (hrow _ hO)

/-- The only rectangle from a state to its row swap that can be fully blocked is the row swap
rectangle. -/
private theorem fullyBlockedRectangles_swapRows_subset (y : GridState (n + 1)) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).fullyBlockedRectangles y
      (y.swapRows (G.X s).castSucc (G.X s).succ) ⊆ {G.stabilizeXRowSwapRectangle s y} := by
  intro t ht
  rcases (G.stabilizeXRowSwapRectangle s y).eq_or_eq_swapSides t with rfl | rfl
  · exact Finset.mem_singleton_self _
  · exact absurd (avoidsMarkings_of_mem_fullyBlockedRectangles _ _ _ ht)
      (G.not_avoidsMarkings_swapSides_stabilizeXRowSwapRectangle s y)

/-- From a state using the row `(G.X s).castSucc` in column `s.succ`, the row swap rectangle is
counted by the reduced `H_I^N`: it starts at column `s.succ`, is empty, covers `X₂` as its only
`X`-marking and covers no `O`-marking. -/
private theorem stabilizeXRowSwapRectangle_mem_filter_XHomotopyRectangles {y : GridState (n + 1)}
    (hy : y s.succ = (G.X s).castSucc) :
    G.stabilizeXRowSwapRectangle s y ∈
      ((G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopyRectangles s.succ y
        (y.swapRows (G.X s).castSucc (G.X s).succ)).filter fun r ↦
          (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle = ∅ := by
  set G' := G.stabilizeX s.castSucc (G.X s).castSucc s
  set R := G.stabilizeXRowSwapRectangle s y
  have hl : R.left = s.succ := by
    rw [stabilizeXRowSwapRectangle_left, ← hy, GridState.transpose_apply_apply]
  have hbs : R.right ≠ s.succ := hl ▸ R.left_ne_right.symm
  have hrow (q : Fin (n + 1)) : q ∈ R.toGridRectangle.coveredRows ↔ q = (G.X s).castSucc := by
    rw [coveredRows_stabilizeXRowSwapRectangle, Finset.mem_singleton]
  refine Finset.mem_filter.mpr ⟨(G'.mem_XHomotopyRectangles _ _).mpr
    ⟨G.isEmpty_stabilizeXRowSwapRectangle s y, ?_⟩, ?_⟩
  · -- The only `X`-marking in the row `(G.X s).castSucc` is `X₂ = (s.succ, (G.X s).castSucc)`,
    -- in the initial column of the rectangle.
    have hXs : G'.X s.succ = (G.X s).castSucc := by simp [G']
    ext ⟨c, d⟩
    simp only [Finset.mem_inter, GridRectangle.mem_coveredSquares, hrow, mem_XSet,
      Finset.mem_singleton, Prod.mk.injEq, hXs]
    constructor
    · rintro ⟨⟨-, hd⟩, h⟩
      subst hd
      exact ⟨by simpa [G'] using h, rfl⟩
    · rintro ⟨hc, hd⟩
      subst hc hd
      exact ⟨⟨hl ▸ Grid.left_mem_cIco R.left_ne_right, rfl⟩, hXs⟩
  · -- The only `O`-marking in that row is `O_new`, in the column `s.castSucc` just before the
    -- initial column of the rectangle.
    refine Finset.eq_empty_iff_forall_notMem.mpr fun c hc ↦ ?_
    rw [mem_OColumns, GridRectangle.mem_coveredSquares, hrow, stabilizeX_O,
      stabilizeX_O_eq_castSucc_iff] at hc
    obtain ⟨hc, rfl⟩ := hc
    simp only [GridRectangle.mem_coveredColumns, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right, hl] at hc
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) hc
      (Grid.castSucc_mem_cIco_succ hbs)

/-- The side swap of the row swap rectangle from a state using the row `(G.X s).castSucc` in
column `s.succ` covers the marking `X₁ = (s.castSucc, (G.X s).succ)`, so it is not counted by the
`X`-marking homotopy through `X₂`. -/
private theorem swapSides_stabilizeXRowSwapRectangle_notMem_XHomotopyRectangles
    {y : GridState (n + 1)} (hy : y s.succ = (G.X s).castSucc) :
    (G.stabilizeXRowSwapRectangle s y).swapSides ∉
      (G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopyRectangles s.succ y
        (y.swapRows (G.X s).castSucc (G.X s).succ) := by
  set G' := G.stabilizeX s.castSucc (G.X s).castSucc s with hG'
  set R := G.stabilizeXRowSwapRectangle s y
  have hl : R.left = s.succ := by
    rw [stabilizeXRowSwapRectangle_left, ← hy, GridState.transpose_apply_apply]
  have hbs : R.right ≠ s.succ := hl ▸ R.left_ne_right.symm
  intro h
  have hX := ((G'.mem_XHomotopyRectangles _ _).mp h).2
  have hp : (s.castSucc, (G.X s).succ) ∈ R.swapSides.toGridRectangle.coveredSquares ∩ G'.XSet := by
    refine Finset.mem_inter.mpr ⟨(GridRectangle.mem_coveredSquares _ _).mpr ⟨?_, ?_⟩,
      (G'.mem_XSet _).mpr (by simp [hG'])⟩
    · simp only [GridRectangle.mem_coveredColumns, GridRectangleBetween.swapSides_toGridRectangle,
        hl]
      exact Grid.castSucc_mem_cIco_succ hbs
    · simp only [GridRectangle.mem_coveredRows, GridRectangleBetween.swapSides_toGridRectangle, R,
        stabilizeXRowSwapRectangle_top, stabilizeXRowSwapRectangle_bottom]
      exact Grid.left_mem_cIco Fin.castSucc_lt_succ.ne'
  rw [hX, Finset.mem_singleton, Prod.mk.injEq] at hp
  exact Fin.castSucc_lt_succ.ne hp.1

/-- From a state using the row `(G.X s).castSucc` in column `s.succ`, exactly one rectangle to
its row swap is counted by the reduced comparison: the row swap rectangle, and not its side
swap. -/
private theorem card_filter_XHomotopyRectangles_swapRows {y : GridState (n + 1)}
    (hy : y s.succ = (G.X s).castSucc) :
    (((G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopyRectangles s.succ y
      (y.swapRows (G.X s).castSucc (G.X s).succ)).filter fun r ↦
        (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle = ∅).card =
      1 := by
  rw [Finset.card_eq_one]
  refine ⟨_, Finset.eq_singleton_iff_unique_mem.mpr
    ⟨G.stabilizeXRowSwapRectangle_mem_filter_XHomotopyRectangles s hy, fun u hu ↦ ?_⟩⟩
  rcases (G.stabilizeXRowSwapRectangle s y).eq_or_eq_swapSides u with rfl | rfl
  · rfl
  · exact absurd (Finset.mem_filter.mp hu).1
      (G.swapSides_stabilizeXRowSwapRectangle_notMem_XHomotopyRectangles s hy)

/-! ### The matching in terms of states -/

/-- A mapping-cone generator is matched with an off-center generator exactly when the latter's
state is the row swap of the former's. -/
private theorem stabilizeXMatching_eq_inl_iff (i : G.StabilizeXOffCenterState s ⊕ GridState n)
    (z : G.StabilizeXOffCenterState s) :
    G.stabilizeXMatching s i = .inl z ↔
      z.1 = (G.stabilizeXConeStateEquiv s i).swapRows (G.X s).castSucc (G.X s).succ := by
  rw [← (G.stabilizeXConeStateEquiv s).injective.eq_iff,
    stabilizeXConeStateEquiv_apply_stabilizeXMatching, stabilizeXConeStateEquiv_apply_inl, eq_comm]

/-- A mapping-cone generator is matched with a center generator exactly when the latter's
center insertion is the row swap of the former's state. -/
private theorem stabilizeXMatching_eq_inr_iff (i : G.StabilizeXOffCenterState s ⊕ GridState n)
    (x : GridState n) :
    G.stabilizeXMatching s i = .inr x ↔ x.insertPoint s.succ (G.X s).succ =
      (G.stabilizeXConeStateEquiv s i).swapRows (G.X s).castSucc (G.X s).succ := by
  rw [← (G.stabilizeXConeStateEquiv s).injective.eq_iff,
    stabilizeXConeStateEquiv_apply_stabilizeXMatching, stabilizeXConeStateEquiv_apply_inr, eq_comm]

/-- An off-center state using the row `(G.X s).castSucc` in column `s.succ` is a matching
source. -/
private theorem stabilizeXMatchingSource_inl_of_eq {y : G.StabilizeXOffCenterState s}
    (hy : y.1 s.succ = (G.X s).castSucc) : G.StabilizeXMatchingSource s (.inl y) := by
  have ha : y.1.transpose (G.X s).castSucc = s.succ := by
    rw [← hy, GridState.transpose_apply_apply]
  rw [stabilizeXMatchingSource_iff_notMem_cIco, stabilizeXConeStateEquiv_apply_inl, ha]
  exact fun h ↦ Finset.disjoint_left.mp (Grid.disjoint_cIco_swap _ _) h
    (Grid.castSucc_mem_cIco_succ fun he ↦ Fin.castSucc_lt_succ.ne
      (y.1.transpose.toPerm.injective (ha.trans he.symm)))

/-- An off-center state reaching its row swap along a fully blocked rectangle is a matching
source. -/
private theorem stabilizeXMatchingSource_inl_of_mem_fullyBlockedRectangles
    {y : G.StabilizeXOffCenterState s}
    {r : GridRectangleBetween y.1 (y.1.swapRows (G.X s).castSucc (G.X s).succ)}
    (hr : r ∈ (G.stabilizeX s.castSucc (G.X s).castSucc s).fullyBlockedRectangles y.1
      (y.1.swapRows (G.X s).castSucc (G.X s).succ)) :
    G.StabilizeXMatchingSource s (.inl y) := by
  obtain rfl := Finset.mem_singleton.mp (G.fullyBlockedRectangles_swapRows_subset s y.1 hr)
  rw [stabilizeXMatchingSource_iff_notMem_cIco, stabilizeXConeStateEquiv_apply_inl]
  exact ((G.stabilizeXRowSwapRectangle_mem_fullyBlockedRectangles_iff s y.1).mp hr).1

/-- The row swap rectangle from an off-center source using neither row of the new block in
column `s.succ` is fully blocked. -/
private theorem stabilizeXRowSwapRectangle_mem_fullyBlockedRectangles_of_source
    {y : G.StabilizeXOffCenterState s} (hy : y.1 s.succ ≠ (G.X s).castSucc)
    (hsrc : G.StabilizeXMatchingSource s (.inl y)) :
    G.stabilizeXRowSwapRectangle s y.1 ∈
      (G.stabilizeX s.castSucc (G.X s).castSucc s).fullyBlockedRectangles y.1
        (y.1.swapRows (G.X s).castSucc (G.X s).succ) := by
  rw [stabilizeXMatchingSource_iff_notMem_cIco, stabilizeXConeStateEquiv_apply_inl] at hsrc
  rw [stabilizeXRowSwapRectangle_mem_fullyBlockedRectangles_iff]
  have hne {r : Fin (n + 1)} (hr : y.1 s.succ ≠ r) : y.1.transpose r ≠ finRotate _ s.castSucc := by
    rw [finRotate_apply, Fin.coeSucc_eq_succ]
    exact fun h ↦ hr ((congrArg (fun c ↦ y.1 c) h).symm.trans (y.1.apply_transpose_apply r))
  have hs := Grid.mem_cIco_finRotate_iff_of_ne (hne hy) (hne y.2)
  rw [finRotate_apply, Fin.coeSucc_eq_succ] at hs
  rw [hs]
  exact ⟨hsrc, hsrc⟩

/-! ### The weight -/

/-- The weight of a generator of the reduced cone: the level of its state, then the position of
the row its state uses in column `s.succ`, read cyclically from the row above `(G.X s).succ` so
that the two stabilization rows come last. Center generators get the position of the row
`(G.X s).castSucc`. -/
private noncomputable def stabilizeXConeWeight : G.StabilizeXOffCenterState s ⊕ GridState n → ℚ ×ₗ ℕ
  | .inl y => toLex (G.stabilizeXLevel s y.1, Grid.cyclicPosition (G.X s).succ (y.1 s.succ))
  | .inr x => toLex (G.stabilizeXLevel s (x.insertPoint s.succ (G.X s).succ),
      Grid.cyclicPosition (G.X s).succ (G.X s).castSucc)

/-- The stabilization matching preserves the weight. -/
private theorem stabilizeXConeWeight_stabilizeXMatching
    (i : G.StabilizeXOffCenterState s ⊕ GridState n) :
    G.stabilizeXConeWeight s (G.stabilizeXMatching s i) = G.stabilizeXConeWeight s i := by
  rcases h : G.stabilizeXMatching s i with ⟨z, hz⟩ | x
  · have hzi := (G.stabilizeXMatching_eq_inl_iff s i _).mp h
    dsimp only at hzi
    subst hzi
    rcases i with y | x
    · rw [stabilizeXConeStateEquiv_apply_inl] at hz
      simp [stabilizeXConeWeight, Equiv.swap_apply_of_ne_of_ne
        (G.apply_succ_ne_castSucc_of_swapRows_apply_ne s hz) y.2]
    · simp [stabilizeXConeWeight]
  · have hx := (G.stabilizeXMatching_eq_inr_iff s i x).mp h
    have hs := G.apply_succ_eq_castSucc_of_insertPoint_eq_swapRows s hx
    rcases i with y | x'
    · rw [stabilizeXConeStateEquiv_apply_inl] at hx hs
      simp [stabilizeXConeWeight, hx, hs]
    · rw [stabilizeXConeStateEquiv_apply_inr, GridState.insertPoint_apply_newColumn] at hs
      exact absurd hs Fin.castSucc_lt_succ.ne'

/-! ### Rectangles lower the weight -/

/-- **Off-center to off-center.** A fully blocked rectangle of the stabilization between two
off-center states strictly lowers the weight, unless it is the matching edge from a source to
its partner. -/
private theorem stabilizeXConeWeight_lt_or_of_mem_fullyBlockedRectangles
    (y z : G.StabilizeXOffCenterState s)
    {r : GridRectangleBetween y.1 z.1}
    (hr : r ∈ (G.stabilizeX s.castSucc (G.X s).castSucc s).fullyBlockedRectangles y.1 z.1) :
    G.stabilizeXConeWeight s (.inl z) < G.stabilizeXConeWeight s (.inl y) ∨
      (G.StabilizeXMatchingSource s (.inl y) ∧ .inl z = G.stabilizeXMatching s (.inl y)) := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨z, hz⟩ := z
  have hav := avoidsMarkings_of_mem_fullyBlockedRectangles _ _ _ hr
  have hX := r.disjoint_coveredSquares_XSet_of_avoidsMarkings hav
  simp only [stabilizeXConeWeight, Prod.Lex.toLex_lt_toLex]
  rcases G.stabilizeXLevel_lt_or_disjoint s r
      (r.disjoint_coveredSquares_OSet_of_avoidsMarkings hav) with hlt | hdisj
  · exact Or.inl (Or.inl hlt)
  rcases G.coveredRows_eq_or_coveredColumns_eq_of_disjoint_stabilizeXOuterSquares s r hdisj with
    hrows | hcols
  · -- A rectangle in the row `(G.X s).castSucc` is the matching edge to the row swap.
    obtain ⟨hbot, htop, -⟩ := Grid.cIco_eq_singleton_iff.mp hrows
    simp only [GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top,
      finRotate_apply, Fin.coeSucc_eq_succ] at hbot htop
    obtain rfl := r.target_eq_swapRows.trans (by rw [← r.bottom_def, ← r.top_def, hbot, htop])
    exact Or.inr ⟨G.stabilizeXMatchingSource_inl_of_mem_fullyBlockedRectangles s (y := ⟨y, hy⟩) hr,
      ((G.stabilizeXMatching_eq_inl_iff s _ _).mpr
        (by rw [stabilizeXConeStateEquiv_apply_inl])).symm⟩
  · -- A rectangle in the column `s.castSucc` keeps the level and lowers the row position, since
    -- it avoids the marking `X₁ = (s.castSucc, (G.X s).succ)`.
    obtain ⟨hleft, hright, -⟩ := Grid.cIco_eq_singleton_iff.mp hcols
    simp only [GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right,
      finRotate_apply, Fin.coeSucc_eq_succ] at hleft hright
    refine Or.inl (Or.inr ⟨(G.stabilizeXLevel_eq_of_disjoint s r hdisj).symm, ?_⟩)
    have hzs : z s.succ = y s.castSucc := by
      rw [← hright, ← hleft]
      exact r.map_right
    rw [hzs]
    refine Grid.cyclicPosition_lt_of_notMem_cIco
      (fun h ↦ (Fin.castSucc_lt_succ (i := s)).ne (y.toPerm.injective h)) fun hρ' ↦ ?_
    refine Finset.disjoint_left.mp hX ((GridRectangle.mem_coveredSquares _ _).mpr ⟨?_, ?_⟩)
      ((mk_mem_XSet _ s.castSucc (G.X s).succ).mpr (by simp))
    · rw [hcols]
      exact Finset.mem_singleton_self _
    · simpa [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hleft, hright]
        using hρ'

/-- **Off-center to center.** A rectangle counted by the reduced `H_I^N` strictly lowers the
weight, unless it is the matching edge from a source to its partner. -/
private theorem stabilizeXConeWeight_lt_or_of_mem_XHomotopyRectangles
    (y : G.StabilizeXOffCenterState s) (x : GridState n)
    {r : GridRectangleBetween y.1 (x.insertPoint s.succ (G.X s).succ)}
    (hr : r ∈ (G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopyRectangles s.succ y.1
      (x.insertPoint s.succ (G.X s).succ))
    (hO : (G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle = ∅) :
    G.stabilizeXConeWeight s (.inr x) < G.stabilizeXConeWeight s (.inl y) ∨
      (G.StabilizeXMatchingSource s (.inl y) ∧ .inr x = G.stabilizeXMatching s (.inl y)) := by
  set G' := G.stabilizeX s.castSucc (G.X s).castSucc s with hG'
  simp only [stabilizeXConeWeight, Prod.Lex.toLex_lt_toLex]
  rcases G.stabilizeXLevel_lt_or_disjoint s r ((G'.OColumns_eq_empty_iff _).mp hO) with
    hlt | hout
  · exact Or.inl (Or.inl hlt)
  right
  -- The rectangle covers no outer square, so it lies in the row or the column of `O_new`. It
  -- covers `X₂ = (s.succ, (G.X s).castSucc)`, so it lies in the row.
  have hX₂ : (s.succ, (G.X s).castSucc) ∈ r.toGridRectangle.coveredSquares := by
    have hX := ((G'.mem_XHomotopyRectangles s.succ r).mp hr).2
    have h := Finset.mem_of_mem_inter_left (hX ▸ Finset.mem_singleton_self _)
    simpa [hG'] using h
  rcases G.coveredRows_eq_or_coveredColumns_eq_of_disjoint_stabilizeXOuterSquares s r hout with
    hrow | hcol
  swap
  · have h := ((r.toGridRectangle.mem_coveredSquares _).mp hX₂).1
    rw [hcol, Finset.mem_singleton] at h
    exact absurd h Fin.castSucc_lt_succ.ne'
  -- The target is the row swap of the source.
  obtain ⟨hbot, htop, -⟩ := Grid.cIco_eq_singleton_iff.mp hrow
  simp only [GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top,
    finRotate_apply, Fin.coeSucc_eq_succ] at hbot htop
  have hswap := r.target_eq_swapRows.trans (by rw [← r.bottom_def, ← r.top_def, hbot, htop])
  have hy := G.apply_succ_eq_castSucc_of_insertPoint_eq_swapRows s hswap
  exact ⟨G.stabilizeXMatchingSource_inl_of_eq s hy,
    ((G.stabilizeXMatching_eq_inr_iff s _ _).mpr
      (by rw [stabilizeXConeStateEquiv_apply_inl, hswap])).symm⟩

/-- **Center to center.** A fully blocked rectangle of `G` strictly lowers the weight of the
corresponding center generators. -/
private theorem stabilizeXConeWeight_lt_of_mem_fullyBlockedRectangles (x x' : GridState n)
    {r : GridRectangleBetween x x'} (hr : r ∈ G.fullyBlockedRectangles x x') :
    G.stabilizeXConeWeight s (.inr x') < G.stabilizeXConeWeight s (.inr x) := by
  set G' := G.stabilizeX s.castSucc (G.X s).castSucc s with hG'
  set y := x.insertPoint s.succ (G.X s).succ with hy
  set z := x'.insertPoint s.succ (G.X s).succ with hz
  -- The center insertion identifies the fully blocked rectangles of `G` and of `G'`.
  have hcard : (G'.fullyBlockedRectangles y z).card = (G.fullyBlockedRectangles x x').card := by
    have h := G'.constantCoeff_unblockedCoefficient_eq_card_fullyBlockedRectangles ℕ y z
    rw [hy, hz, hG', unblockedCoefficient_stabilizeX_insertPoint, constantCoeff_rename,
      constantCoeff_unblockedCoefficient_eq_card_fullyBlockedRectangles] at h
    exact_mod_cast h.symm
  obtain ⟨r', hr'⟩ : (G'.fullyBlockedRectangles y z).Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact Finset.card_pos.mpr ⟨r, hr⟩
  have hO := r'.disjoint_coveredSquares_OSet_of_avoidsMarkings
    (avoidsMarkings_of_mem_fullyBlockedRectangles _ _ _ hr')
  have hys : y s.succ = (G.X s).succ := GridState.insertPoint_apply_newColumn _ _ _
  simp only [stabilizeXConeWeight, Prod.Lex.toLex_lt_toLex]
  refine Or.inl ((G.stabilizeXLevel_lt_or_disjoint s r' hO).resolve_right fun hdis ↦ ?_)
  -- A rectangle covering no outer square lies in the cross of `O_new`, so it covers `O_new`.
  refine Finset.disjoint_left.mp hO ((GridRectangle.mem_coveredSquares _ _).mpr ?_)
    ((mk_mem_OSet _ s.castSucc (G.X s).castSucc).mpr (by simp [G']))
  simp only [GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top]
  rcases G.coveredRows_eq_or_coveredColumns_eq_of_disjoint_stabilizeXOuterSquares s r' hdis
    with h | h
  · obtain ⟨hb, ht, -⟩ := Grid.cIco_eq_singleton_iff.mp h
    simp only [GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top,
      finRotate_apply, Fin.coeSucc_eq_succ] at hb ht
    have hright : r'.right = s.succ := y.toPerm.injective (ht.trans hys.symm)
    refine ⟨hright ▸ Grid.castSucc_mem_cIco_succ (hright ▸ r'.left_ne_right), ?_⟩
    rw [hb, ht]
    exact Grid.left_mem_cIco Fin.castSucc_lt_succ.ne
  · obtain ⟨hl, hrt, -⟩ := Grid.cIco_eq_singleton_iff.mp h
    simp only [GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right,
      finRotate_apply, Fin.coeSucc_eq_succ] at hl hrt
    rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hl, hrt, hys]
    exact ⟨Grid.left_mem_cIco Fin.castSucc_lt_succ.ne, Grid.castSucc_mem_cIco_succ fun h ↦
      Fin.castSucc_lt_succ.ne (y.toPerm.injective (h.trans hys.symm))⟩

/-! ### The reduced cone -/

section ReducedCone

variable (R : Type*) [CommRing R]

/-- The mapping cone of the reduced `H_I^N`, on the free module over the generators
`G.StabilizeXOffCenterState s ⊕ GridState n`. -/
private noncomputable abbrev stabilizeXReducedCone :
    (G.StabilizeXOffCenterState s ⊕ GridState n →₀ R) →ₗ[R]
      (G.StabilizeXOffCenterState s ⊕ GridState n →₀ R) :=
  LinearMap.sumMappingCone (G.stabilizeXOffCenterDifferential s R).constantCoeffReduction
    (G.stabilizeXCenterDifferential s R).constantCoeffReduction
    (G.stabilizeXOffCenterToCenter s R).constantCoeffReduction

/-- Every term of the reduced cone strictly lowers the weight, except the matching edges. -/
private theorem stabilizeXConeWeight_lt_or_of_mem_support
    (i j : G.StabilizeXOffCenterState s ⊕ GridState n)
    (hj : j ∈ (G.stabilizeXReducedCone s R (single i 1)).support) :
    G.stabilizeXConeWeight s j < G.stabilizeXConeWeight s i ∨
      (G.StabilizeXMatchingSource s i ∧ j = G.stabilizeXMatching s i) := by
  rw [Finsupp.mem_support_iff] at hj
  rcases i with y | x <;> rcases j with z | x'
  · rw [LinearMap.sumMappingCone_single_inl_apply_inl,
      constantCoeffReduction_stabilizeXOffCenterDifferential_single_apply, one_mul,
      neg_ne_zero] at hj
    obtain ⟨r, hr⟩ := Finset.card_ne_zero.mp fun h ↦ hj (by rw [h, Nat.cast_zero])
    exact G.stabilizeXConeWeight_lt_or_of_mem_fullyBlockedRectangles s y z hr
  · rw [LinearMap.sumMappingCone_single_inl_apply_inr,
      constantCoeffReduction_stabilizeXOffCenterToCenter_single_apply, one_mul] at hj
    obtain ⟨r, hr⟩ := Finset.card_ne_zero.mp fun h ↦ hj (by rw [h, Nat.cast_zero])
    rw [Finset.mem_filter] at hr
    exact G.stabilizeXConeWeight_lt_or_of_mem_XHomotopyRectangles s y x' hr.1 hr.2
  · exact absurd (LinearMap.sumMappingCone_single_inr_apply_inl ..) hj
  · rw [LinearMap.sumMappingCone_single_inr_apply_inr,
      constantCoeffReduction_stabilizeXCenterDifferential_single_apply, one_mul] at hj
    obtain ⟨r, hr⟩ := Finset.card_ne_zero.mp fun h ↦ hj (by rw [h, Nat.cast_zero])
    exact Or.inl (G.stabilizeXConeWeight_lt_of_mem_fullyBlockedRectangles s x x' hr)

variable [CharP R 2]

/-- The reduced cone squares to zero. -/
private theorem stabilizeXReducedCone_comp_self :
    G.stabilizeXReducedCone s R ∘ₗ G.stabilizeXReducedCone s R = 0 :=
  LinearMap.sumMappingCone_comp_self
    (G.constantCoeffReduction_stabilizeXOffCenterDifferential_comp_self s R)
    (G.constantCoeffReduction_stabilizeXCenterDifferential_comp_self s R)
    (G.constantCoeffReduction_stabilizeXOffCenterToCenter_comp s R)

/-- The matching edges of the reduced cone have coefficient one. -/
private theorem stabilizeXReducedCone_single_apply_stabilizeXMatching
    (i : G.StabilizeXOffCenterState s ⊕ GridState n) (hi : G.StabilizeXMatchingSource s i) :
    G.stabilizeXReducedCone s R (single i 1) (G.stabilizeXMatching s i) = 1 := by
  rcases i with y | x
  swap
  · exact absurd hi (G.not_stabilizeXMatchingSource_inr s x)
  rcases h : G.stabilizeXMatching s (.inl y) with z | x
  · have hz := (G.stabilizeXMatching_eq_inl_iff s _ z).mp h
    rw [stabilizeXConeStateEquiv_apply_inl] at hz
    have hy := G.apply_succ_ne_castSucc_of_swapRows_apply_ne s (hz ▸ z.2)
    obtain ⟨z, hz'⟩ := z
    dsimp only at hz
    subst hz
    rw [LinearMap.sumMappingCone_single_inl_apply_inl,
      constantCoeffReduction_stabilizeXOffCenterDifferential_single_apply,
      Finset.card_eq_one.mpr ⟨_, Finset.Subset.antisymm
        (G.fullyBlockedRectangles_swapRows_subset s y.1) (Finset.singleton_subset_iff.mpr
          (G.stabilizeXRowSwapRectangle_mem_fullyBlockedRectangles_of_source s hy hi))⟩,
      Nat.cast_one, one_mul, CharTwo.neg_eq]
  · have hx := (G.stabilizeXMatching_eq_inr_iff s _ x).mp h
    rw [stabilizeXConeStateEquiv_apply_inl] at hx
    have hy := G.apply_succ_eq_castSucc_of_insertPoint_eq_swapRows s hx
    rw [LinearMap.sumMappingCone_single_inl_apply_inr,
      constantCoeffReduction_stabilizeXOffCenterToCenter_single_apply, hx,
      G.card_filter_XHomotopyRectangles_swapRows s hy, Nat.cast_one, one_mul]

/-- **The reduced comparison is a quasi-isomorphism.** The reduction of `H_I^N` modulo the
variables induces a bijection from the homology of the reduced off-center complex to the homology
of the reduced center complex. -/
theorem homologyMap_constantCoeffReduction_stabilizeXOffCenterToCenter_bijective :
    Function.Bijective (LinearMap.homologyMap
      (G.stabilizeXOffCenterToCenter s R).constantCoeffReduction
      (G.constantCoeffReduction_stabilizeXOffCenterDifferential_comp_self s R)
      (G.constantCoeffReduction_stabilizeXCenterDifferential_comp_self s R)
      (G.constantCoeffReduction_stabilizeXOffCenterToCenter_comp s R)) := by
  rw [← LinearMap.ker_le_range_mappingCone_iff, ← LinearMap.ker_le_range_sumMappingCone_iff]
  exact LinearMap.ker_le_range_of_matching (G.stabilizeXReducedCone s R)
    (G.stabilizeXReducedCone_comp_self s R) (G.stabilizeXConeWeight s)
    (Finite.wellFounded_of_trans_of_irrefl _) (G.stabilizeXMatching s)
    (G.StabilizeXMatchingSource s) (G.stabilizeXMatching_involutive s)
    (G.stabilizeXConeWeight_stabilizeXMatching s)
    (fun i ↦ by rw [stabilizeXMatchingSource_stabilizeXMatching_iff, not_not])
    (fun i hi ↦ by
      rw [G.stabilizeXReducedCone_single_apply_stabilizeXMatching s R i hi]
      exact isUnit_one)
    (G.stabilizeXConeWeight_lt_or_of_mem_support s R)

/-- **`H_I^N` is a quasi-isomorphism.** Together with the instance `quasiIso_stabilizeXMap`, the
chain map `GC⁻(G') ⟶ GC⁻(G)` of the stabilization splitting the `X`-marking of column `s` is a
quasi-isomorphism. -/
instance quasiIso_stabilizeXOffCenterToCenterHom :
    QuasiIso (G.stabilizeXOffCenterToCenterHom s R) :=
  G.quasiIso_stabilizeXOffCenterToCenterHom_of_bijective s R
    (G.homologyMap_constantCoeffReduction_stabilizeXOffCenterToCenter_bijective s R)

end ReducedCone

end GridDiagram

end TauCeti
