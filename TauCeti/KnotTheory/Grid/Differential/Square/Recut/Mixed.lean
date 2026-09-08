/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Initial
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Terminal

/-!
# Recutting two-step grid rectangle decompositions with a mixed common side

Two composable empty rectangles sharing exactly one side column form an L-shaped domain with a
unique second cut. The cases where the common column is initial for both rectangles or terminal
for both are handled in `Recut.Initial` and `Recut.Terminal`. This file treats the two remaining
orientations: the common column is initial for one rectangle and terminal for the other.

Diagonal reflection turns either mixed column orientation into one of the same-side orientations.
Reflecting its recut back gives the required second decomposition. Accordingly, its side *rows*
rather than its side columns are computed explicitly. The reflected domain is still a repartition,
so the new rectangles have the same combined weight and inherit avoidance of the `X` markings.

## Main results

* `TauCeti.GridRectangleDecomposition.exists_isRepartition_of_isEmpty_of_left_eq_right` and
  `exists_isRepartition_of_isEmpty_of_right_eq_left`: the two mixed common-side configurations
  admit unique recuts through different intermediate states, with both new rectangles empty.
* `exists_isRepartition_of_mem_unblockedRectangles_of_left_eq_right`
  and `exists_isRepartition_of_mem_unblockedRectangles_of_right_eq_left`: the recuts again give
  terms counted by the unblocked differential.

## References

The recut is the overlapping-rectangle case of Ozsváth--Stipsicz--Szabó, *Grid Homology for
Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-- If reflecting a decomposition gives a specified intermediate state obtained by a column
swap, then the original intermediate state is obtained by the corresponding row swap. -/
private theorem middle_eq_swapRows_of_transpose_eq
    (E : GridRectangleDecomposition x z)
    (F : GridRectangleDecomposition x.transpose z.transpose) (hEF : E.transpose = F)
    {a b : Fin n} (hF : F.middle = x.transpose.swapColumns a b) :
    E.middle = x.swapRows a b := by
  have hmiddle : E.middle.transpose = F.middle := by
    simpa only [transpose_middle] using congrArg (fun Q => Q.middle) hEF
  calc
    E.middle = F.middle.transpose := by
      simpa using congrArg GridState.transpose hmiddle
    _ = (x.transpose.swapColumns a b).transpose := congrArg GridState.transpose hF
    _ = x.swapRows a b := by
      rw [← GridState.swapRows_transpose]
      simp

/-! ### Initial side of the first rectangle equals terminal side of the second -/

/-- Two composable empty rectangles whose common column is the initial side of the first and the
terminal side of the second admit a unique recut through a different intermediate state.

The two alternatives record which of the two noncommon corner rows lies inside the other row
span. They compute all four side rows of the recut and hence determine it uniquely after diagonal
reflection. -/
theorem exists_isRepartition_of_isEmpty_of_left_eq_right
    (D : GridRectangleDecomposition x z)
    (hcommon : D.first.left = D.second.right) (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    ∃! E : GridRectangleDecomposition x z,
      D.IsRepartition E ∧ E.middle ≠ D.middle ∧ E.first.IsEmpty ∧ E.second.IsEmpty ∧
        E.first.bottom = D.second.bottom ∧ E.second.bottom = D.first.bottom ∧
          ((D.first.bottom ∈ Grid.cIoo D.second.bottom D.first.top ∧
              E.middle = x.swapRows D.second.bottom D.first.bottom ∧
                E.first.top = D.first.bottom ∧ E.second.top = D.first.top) ∨
            (D.second.bottom ∈ Grid.cIoo D.first.bottom D.first.top ∧
              E.middle = x.swapRows D.second.bottom D.first.top ∧
                E.first.top = D.first.top ∧ E.second.top = D.second.bottom)) := by
  -- Reflection converts this orientation into the common-terminal-side case.
  have htransRight : D.transpose.first.right = D.transpose.second.right := by
    simpa only [transpose_first_right, transpose_second_right, GridRectangleBetween.top_def,
      hcommon] using D.first.map_left.symm
  have hsecondLeft_ne_firstLeft : D.second.left ≠ D.first.left := fun h =>
    D.second.left_ne_right (h.trans hcommon)
  have hmiddle_secondLeft : D.middle D.second.left = x D.second.left :=
    D.first.map_of_ne D.second.left hsecondLeft_ne_firstLeft hother.symm
  have htransLeft : D.transpose.first.left ≠ D.transpose.second.left := by
    simpa only [transpose_first_left, transpose_second_left, GridRectangleBetween.bottom_def,
      hmiddle_secondLeft] using x.toPerm.injective.ne hsecondLeft_ne_firstLeft.symm
  obtain ⟨F, ⟨hrecut, hmiddle, hFfirst, hFsecond, hF1left, hF2left, hrows⟩, hunique⟩ :=
    D.transpose.exists_isRepartition_of_isEmpty_of_right_eq_right htransRight htransLeft
      (D.isEmpty_transpose_first.mpr hfirst) (D.isEmpty_transpose_second.mpr hsecond)
  -- Reflect the known recut back, transporting its domain, emptiness and row data.
  let E : GridRectangleDecomposition x z := (transposeEquiv x z).symm F
  have hEF : E.transpose = F := by
    simpa only [E, transposeEquiv_apply] using (transposeEquiv x z).apply_symm_apply F
  have hrecutE : D.IsRepartition E := IsRepartition.transpose_iff.mp <| by
    rw [hEF]
    exact hrecut
  have hmiddleE : E.middle ≠ D.middle := by
    intro h
    apply hmiddle
    have h' := congrArg GridState.transpose h
    have hEmiddle : E.middle.transpose = F.middle := by
      simpa only [transpose_middle] using congrArg (fun Q => Q.middle) hEF
    simpa only [hEmiddle, transpose_middle] using h'
  have hEfirst : E.first.IsEmpty := by
    apply E.isEmpty_transpose_first.mp
    rw [hEF]
    exact hFfirst
  have hEsecond : E.second.IsEmpty := by
    apply E.isEmpty_transpose_second.mp
    rw [hEF]
    exact hFsecond
  have hE1bottom : E.first.bottom = D.second.bottom := by
    calc
      E.first.bottom = E.transpose.first.left := E.transpose_first_left.symm
      _ = F.first.left := congrArg (fun Q => Q.first.left) hEF
      _ = D.transpose.second.left := hF1left
      _ = D.second.bottom := D.transpose_second_left
  have hE2bottom : E.second.bottom = D.first.bottom := by
    calc
      E.second.bottom = E.transpose.second.left := E.transpose_second_left.symm
      _ = F.second.left := congrArg (fun Q => Q.second.left) hEF
      _ = D.transpose.first.left := hF2left
      _ = D.first.bottom := D.transpose_first_left
  have hrowsE :
      (D.first.bottom ∈ Grid.cIoo D.second.bottom D.first.top ∧
          E.middle = x.swapRows D.second.bottom D.first.bottom ∧
            E.first.top = D.first.bottom ∧ E.second.top = D.first.top) ∨
        (D.second.bottom ∈ Grid.cIoo D.first.bottom D.first.top ∧
          E.middle = x.swapRows D.second.bottom D.first.top ∧
            E.first.top = D.first.top ∧ E.second.top = D.second.bottom) := by
    rcases hrows with ⟨hrow, hFmiddle, hF1right, hF2right⟩ |
        ⟨hrow, hFmiddle, hF1right, hF2right⟩
    · left
      refine ⟨by simpa using hrow, ?_, ?_, ?_⟩
      · apply middle_eq_swapRows_of_transpose_eq E F hEF
        simpa only [transpose_second_left, transpose_first_left] using hFmiddle
      · calc
          E.first.top = E.transpose.first.right := E.transpose_first_right.symm
          _ = F.first.right := congrArg (fun Q => Q.first.right) hEF
          _ = D.transpose.first.left := hF1right
          _ = D.first.bottom := D.transpose_first_left
      · calc
          E.second.top = E.transpose.second.right := E.transpose_second_right.symm
          _ = F.second.right := congrArg (fun Q => Q.second.right) hEF
          _ = D.transpose.first.right := hF2right
          _ = D.first.top := D.transpose_first_right
    · right
      refine ⟨by simpa using hrow, ?_, ?_, ?_⟩
      · apply middle_eq_swapRows_of_transpose_eq E F hEF
        simpa only [transpose_second_left, transpose_first_right] using hFmiddle
      · calc
          E.first.top = E.transpose.first.right := E.transpose_first_right.symm
          _ = F.first.right := congrArg (fun Q => Q.first.right) hEF
          _ = D.transpose.first.right := hF1right
          _ = D.first.top := D.transpose_first_right
      · calc
          E.second.top = E.transpose.second.right := E.transpose_second_right.symm
          _ = F.second.right := congrArg (fun Q => Q.second.right) hEF
          _ = D.transpose.second.left := hF2right
          _ = D.second.bottom := D.transpose_second_left
  refine ⟨E, ⟨hrecutE, hmiddleE, hEfirst, hEsecond, hE1bottom, hE2bottom, hrowsE⟩, ?_⟩
  -- A second candidate reflects to the unique recut of `D.transpose`.
  intro E' hE'
  have hmiddle' : E'.transpose.middle ≠ D.transpose.middle := by
    intro h
    apply hE'.2.1
    have h' := congrArg GridState.transpose h
    simp only [transpose_middle] at h'
    exact (GridState.transpose_transpose E'.middle).symm.trans
      (h'.trans (GridState.transpose_transpose D.middle))
  have hF' : E'.transpose = F := by
    apply hunique E'.transpose
    refine ⟨hE'.1.transpose, hmiddle', ?_, ?_, ?_, ?_, ?_⟩
    · exact E'.isEmpty_transpose_first.mpr hE'.2.2.1
    · exact E'.isEmpty_transpose_second.mpr hE'.2.2.2.1
    · simpa only [transpose_first_left, transpose_second_left] using hE'.2.2.2.2.1
    · simpa only [transpose_second_left, transpose_first_left] using hE'.2.2.2.2.2.1
    · rcases hE'.2.2.2.2.2.2 with ⟨hrow, hmid, htop₁, htop₂⟩ |
          ⟨hrow, hmid, htop₁, htop₂⟩
      · left
        refine ⟨by simpa only [transpose_first_left, transpose_second_left,
          transpose_first_right] using hrow, ?_, ?_, ?_⟩
        · simp only [transpose_middle, hmid, GridState.swapRows_transpose,
            transpose_second_left, transpose_first_left]
        · simpa only [transpose_first_right, transpose_first_left] using htop₁
        · simpa only [transpose_second_right, transpose_first_right] using htop₂
      · right
        refine ⟨by simpa only [transpose_second_left, transpose_first_left,
          transpose_first_right] using hrow, ?_, ?_, ?_⟩
        · simp only [transpose_middle, hmid, GridState.swapRows_transpose,
            transpose_second_left, transpose_first_right]
        · simpa only [transpose_first_right] using htop₁
        · simpa only [transpose_second_right, transpose_second_left] using htop₂
  apply (transposeEquiv x z).injective
  simpa only [transposeEquiv_apply, hEF] using hF'

/-- The mixed-side recut of two terms counted by the unblocked differential again consists of
two counted rectangles. Its covered-square domain, and hence its combined monomial weight, is
unchanged. -/
theorem exists_isRepartition_of_mem_unblockedRectangles_of_left_eq_right
    (G : GridDiagram n) (D : GridRectangleDecomposition x z)
    (hcommon : D.first.left = D.second.right) (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first ∈ G.unblockedRectangles x D.middle)
    (hsecond : D.second ∈ G.unblockedRectangles D.middle z) :
    ∃! E : GridRectangleDecomposition x z,
      D.IsRepartition E ∧ E.middle ≠ D.middle ∧
        E.first ∈ G.unblockedRectangles x E.middle ∧
          E.second ∈ G.unblockedRectangles E.middle z ∧
            E.first.bottom = D.second.bottom ∧ E.second.bottom = D.first.bottom ∧
              ((D.first.bottom ∈ Grid.cIoo D.second.bottom D.first.top ∧
                  E.middle = x.swapRows D.second.bottom D.first.bottom ∧
                    E.first.top = D.first.bottom ∧ E.second.top = D.first.top) ∨
                (D.second.bottom ∈ Grid.cIoo D.first.bottom D.first.top ∧
                  E.middle = x.swapRows D.second.bottom D.first.top ∧
                    E.first.top = D.first.top ∧ E.second.top = D.second.bottom)) := by
  obtain ⟨E, ⟨hrecut, hmiddle, hEfirst, hEsecond, hE1bottom, hE2bottom, hrows⟩, hunique⟩ :=
    D.exists_isRepartition_of_isEmpty_of_left_eq_right hcommon hother
      (G.isEmpty_of_mem_unblockedRectangles hfirst) (G.isEmpty_of_mem_unblockedRectangles hsecond)
  have hX₁ := G.disjoint_XSet_of_mem_unblockedRectangles hfirst
  have hX₂ := G.disjoint_XSet_of_mem_unblockedRectangles hsecond
  refine ⟨E, ⟨hrecut, hmiddle,
    (G.mem_unblockedRectangles _).mpr
      ⟨hEfirst, hrecut.disjoint_coveredSquares_first hX₁ hX₂⟩,
    (G.mem_unblockedRectangles _).mpr
      ⟨hEsecond, hrecut.disjoint_coveredSquares_second hX₁ hX₂⟩,
    hE1bottom, hE2bottom, hrows⟩, ?_⟩
  intro E' hE'
  apply hunique E'
  exact ⟨hE'.1, hE'.2.1, (G.mem_unblockedRectangles _).mp hE'.2.2.1 |>.1,
    (G.mem_unblockedRectangles _).mp hE'.2.2.2.1 |>.1, hE'.2.2.2.2⟩

/-! ### Terminal side of the first rectangle equals initial side of the second -/

/-- Two composable empty rectangles whose common column is the terminal side of the first and the
initial side of the second admit a unique recut through a different intermediate state.

The two alternatives record which of the two noncommon corner rows lies inside the other row
span. They compute all four side rows of the recut and hence determine it uniquely after diagonal
reflection. -/
theorem exists_isRepartition_of_isEmpty_of_right_eq_left
    (D : GridRectangleDecomposition x z)
    (hcommon : D.first.right = D.second.left) (hother : D.first.left ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    ∃! E : GridRectangleDecomposition x z,
      D.IsRepartition E ∧ E.middle ≠ D.middle ∧ E.first.IsEmpty ∧ E.second.IsEmpty ∧
        E.first.top = D.second.top ∧ E.second.top = D.first.top ∧
          ((D.first.top ∈ Grid.cIoo D.first.bottom D.second.top ∧
              E.middle = x.swapRows D.first.top D.second.top ∧
                E.first.bottom = D.first.top ∧ E.second.bottom = D.first.bottom) ∨
            (D.second.top ∈ Grid.cIoo D.first.bottom D.first.top ∧
              E.middle = x.swapRows D.first.bottom D.second.top ∧
                E.first.bottom = D.first.bottom ∧ E.second.bottom = D.second.top)) := by
  -- Reflection converts this orientation into the common-initial-side case.
  have htransLeft : D.transpose.first.left = D.transpose.second.left := by
    simpa only [transpose_first_left, transpose_second_left, GridRectangleBetween.bottom_def,
      hcommon] using D.first.map_right.symm
  have htransRight : D.transpose.first.right ≠ D.transpose.second.right := by
    intro h
    apply hother
    apply D.middle.toPerm.injective
    calc
      D.middle D.first.left = x D.first.right := D.first.map_left
      _ = D.first.top := D.first.top_def.symm
      _ = D.second.top := by
        simpa only [transpose_first_right, transpose_second_right] using h
      _ = D.middle D.second.right := D.second.top_def
  obtain ⟨F, ⟨hrecut, hmiddle, hFfirst, hFsecond, hF1right, hF2right, hrows⟩, hunique⟩ :=
    D.transpose.exists_isRepartition_of_isEmpty_of_left_eq_left htransLeft htransRight
      (D.isEmpty_transpose_first.mpr hfirst) (D.isEmpty_transpose_second.mpr hsecond)
  -- Reflect the known recut back, transporting its domain, emptiness and row data.
  let E : GridRectangleDecomposition x z := (transposeEquiv x z).symm F
  have hEF : E.transpose = F := by
    simpa only [E, transposeEquiv_apply] using (transposeEquiv x z).apply_symm_apply F
  have hrecutE : D.IsRepartition E := IsRepartition.transpose_iff.mp <| by
    rw [hEF]
    exact hrecut
  have hmiddleE : E.middle ≠ D.middle := by
    intro h
    apply hmiddle
    have h' := congrArg GridState.transpose h
    have hEmiddle : E.middle.transpose = F.middle := by
      simpa only [transpose_middle] using congrArg (fun Q => Q.middle) hEF
    simpa only [hEmiddle, transpose_middle] using h'
  have hEfirst : E.first.IsEmpty := by
    apply E.isEmpty_transpose_first.mp
    rw [hEF]
    exact hFfirst
  have hEsecond : E.second.IsEmpty := by
    apply E.isEmpty_transpose_second.mp
    rw [hEF]
    exact hFsecond
  have hE1top : E.first.top = D.second.top := by
    calc
      E.first.top = E.transpose.first.right := E.transpose_first_right.symm
      _ = F.first.right := congrArg (fun Q => Q.first.right) hEF
      _ = D.transpose.second.right := hF1right
      _ = D.second.top := D.transpose_second_right
  have hE2top : E.second.top = D.first.top := by
    calc
      E.second.top = E.transpose.second.right := E.transpose_second_right.symm
      _ = F.second.right := congrArg (fun Q => Q.second.right) hEF
      _ = D.transpose.first.right := hF2right
      _ = D.first.top := D.transpose_first_right
  have hrowsE :
      (D.first.top ∈ Grid.cIoo D.first.bottom D.second.top ∧
          E.middle = x.swapRows D.first.top D.second.top ∧
            E.first.bottom = D.first.top ∧ E.second.bottom = D.first.bottom) ∨
        (D.second.top ∈ Grid.cIoo D.first.bottom D.first.top ∧
          E.middle = x.swapRows D.first.bottom D.second.top ∧
            E.first.bottom = D.first.bottom ∧ E.second.bottom = D.second.top) := by
    rcases hrows with ⟨hrow, hFmiddle, hF1left, hF2left⟩ |
        ⟨hrow, hFmiddle, hF1left, hF2left⟩
    · left
      refine ⟨by simpa using hrow, ?_, ?_, ?_⟩
      · apply middle_eq_swapRows_of_transpose_eq E F hEF
        simpa only [transpose_first_right, transpose_second_right] using hFmiddle
      · calc
          E.first.bottom = E.transpose.first.left := E.transpose_first_left.symm
          _ = F.first.left := congrArg (fun Q => Q.first.left) hEF
          _ = D.transpose.first.right := hF1left
          _ = D.first.top := D.transpose_first_right
      · calc
          E.second.bottom = E.transpose.second.left := E.transpose_second_left.symm
          _ = F.second.left := congrArg (fun Q => Q.second.left) hEF
          _ = D.transpose.first.left := hF2left
          _ = D.first.bottom := D.transpose_first_left
    · right
      refine ⟨by simpa using hrow, ?_, ?_, ?_⟩
      · apply middle_eq_swapRows_of_transpose_eq E F hEF
        simpa only [transpose_first_left, transpose_second_right] using hFmiddle
      · calc
          E.first.bottom = E.transpose.first.left := E.transpose_first_left.symm
          _ = F.first.left := congrArg (fun Q => Q.first.left) hEF
          _ = D.transpose.first.left := hF1left
          _ = D.first.bottom := D.transpose_first_left
      · calc
          E.second.bottom = E.transpose.second.left := E.transpose_second_left.symm
          _ = F.second.left := congrArg (fun Q => Q.second.left) hEF
          _ = D.transpose.second.right := hF2left
          _ = D.second.top := D.transpose_second_right
  refine ⟨E, ⟨hrecutE, hmiddleE, hEfirst, hEsecond, hE1top, hE2top, hrowsE⟩, ?_⟩
  -- A second candidate reflects to the unique recut of `D.transpose`.
  intro E' hE'
  have hmiddle' : E'.transpose.middle ≠ D.transpose.middle := by
    intro h
    apply hE'.2.1
    have h' := congrArg GridState.transpose h
    simp only [transpose_middle] at h'
    exact (GridState.transpose_transpose E'.middle).symm.trans
      (h'.trans (GridState.transpose_transpose D.middle))
  have hF' : E'.transpose = F := by
    apply hunique E'.transpose
    refine ⟨hE'.1.transpose, hmiddle', ?_, ?_, ?_, ?_, ?_⟩
    · exact E'.isEmpty_transpose_first.mpr hE'.2.2.1
    · exact E'.isEmpty_transpose_second.mpr hE'.2.2.2.1
    · simpa only [transpose_first_right, transpose_second_right] using hE'.2.2.2.2.1
    · simpa only [transpose_second_right, transpose_first_right] using hE'.2.2.2.2.2.1
    · rcases hE'.2.2.2.2.2.2 with ⟨hrow, hmid, hbottom₁, hbottom₂⟩ |
          ⟨hrow, hmid, hbottom₁, hbottom₂⟩
      · left
        refine ⟨by simpa only [transpose_first_right, transpose_first_left,
          transpose_second_right] using hrow, ?_, ?_, ?_⟩
        · simp only [transpose_middle, hmid, GridState.swapRows_transpose,
            transpose_first_right, transpose_second_right]
        · simpa only [transpose_first_left, transpose_first_right] using hbottom₁
        · simpa only [transpose_second_left, transpose_first_left] using hbottom₂
      · right
        refine ⟨by simpa only [transpose_second_right, transpose_first_left,
          transpose_first_right] using hrow, ?_, ?_, ?_⟩
        · simp only [transpose_middle, hmid, GridState.swapRows_transpose,
            transpose_first_left, transpose_second_right]
        · simpa only [transpose_first_left] using hbottom₁
        · simpa only [transpose_second_left, transpose_second_right] using hbottom₂
  apply (transposeEquiv x z).injective
  simpa only [transposeEquiv_apply, hEF] using hF'

/-- The other mixed-side recut of two terms counted by the unblocked differential again consists
of two counted rectangles, with unchanged covered-square domain and combined monomial weight. -/
theorem exists_isRepartition_of_mem_unblockedRectangles_of_right_eq_left
    (G : GridDiagram n) (D : GridRectangleDecomposition x z)
    (hcommon : D.first.right = D.second.left) (hother : D.first.left ≠ D.second.right)
    (hfirst : D.first ∈ G.unblockedRectangles x D.middle)
    (hsecond : D.second ∈ G.unblockedRectangles D.middle z) :
    ∃! E : GridRectangleDecomposition x z,
      D.IsRepartition E ∧ E.middle ≠ D.middle ∧
        E.first ∈ G.unblockedRectangles x E.middle ∧
          E.second ∈ G.unblockedRectangles E.middle z ∧
            E.first.top = D.second.top ∧ E.second.top = D.first.top ∧
              ((D.first.top ∈ Grid.cIoo D.first.bottom D.second.top ∧
                  E.middle = x.swapRows D.first.top D.second.top ∧
                    E.first.bottom = D.first.top ∧ E.second.bottom = D.first.bottom) ∨
                (D.second.top ∈ Grid.cIoo D.first.bottom D.first.top ∧
                  E.middle = x.swapRows D.first.bottom D.second.top ∧
                    E.first.bottom = D.first.bottom ∧ E.second.bottom = D.second.top)) := by
  obtain ⟨E, ⟨hrecut, hmiddle, hEfirst, hEsecond, hE1top, hE2top, hrows⟩, hunique⟩ :=
    D.exists_isRepartition_of_isEmpty_of_right_eq_left hcommon hother
      (G.isEmpty_of_mem_unblockedRectangles hfirst) (G.isEmpty_of_mem_unblockedRectangles hsecond)
  have hX₁ := G.disjoint_XSet_of_mem_unblockedRectangles hfirst
  have hX₂ := G.disjoint_XSet_of_mem_unblockedRectangles hsecond
  refine ⟨E, ⟨hrecut, hmiddle,
    (G.mem_unblockedRectangles _).mpr
      ⟨hEfirst, hrecut.disjoint_coveredSquares_first hX₁ hX₂⟩,
    (G.mem_unblockedRectangles _).mpr
      ⟨hEsecond, hrecut.disjoint_coveredSquares_second hX₁ hX₂⟩,
    hE1top, hE2top, hrows⟩, ?_⟩
  intro E' hE'
  apply hunique E'
  exact ⟨hE'.1, hE'.2.1, (G.mem_unblockedRectangles _).mp hE'.2.2.1 |>.1,
    (G.mem_unblockedRectangles _).mp hE'.2.2.2.1 |>.1, hE'.2.2.2.2⟩

end GridRectangleDecomposition

end TauCeti
