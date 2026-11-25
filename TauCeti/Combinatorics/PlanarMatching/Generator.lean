/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Monoidal
import all TauCeti.Combinatorics.Enumerative.PerfectMatching
import all TauCeti.Combinatorics.PlanarMatching.Basic
import all TauCeti.Combinatorics.PlanarMatching.TLDiagram
import all TauCeti.Combinatorics.PlanarMatching.Compose
import all TauCeti.Combinatorics.PlanarMatching.Tensor
import all TauCeti.Combinatorics.PlanarMatching.Category

/-!
# The Temperley–Lieb generators in the diagram category

For `n` boundary points and `i < n - 1`, the diagram `TauCeti.TLDiagCat.e n i : of n ⟶ of n` joins
the bottom points `i` and `i + 1` by a cap, joins the top points `i` and `i + 1` by a cup, and
runs every other point straight up. It is the generator `e₁ = cap ≫ cup` on two strands with `i`
straight strands on its left and `n - 2 - i` on its right (`TauCeti.TLDiagCat.diagram_e`), and it
has no closed circle (`TauCeti.TLDiagCat.circles_e`). Indexing by `Fin (n - 1)` is the
indexing of the generators of the presented Temperley–Lieb algebra `TauCeti.TemperleyLieb R δ n`,
which on `n + 1` points is `Fin n`.

These diagrams satisfy the Temperley–Lieb relations, with the closed circle kept as data:

* `TauCeti.TLDiagCat.e_comp_e_self`: `e n i ≫ e n i` is `e n i` with one closed circle;
* `TauCeti.TLDiagCat.e_comp_e_comp_e`: two generators sharing a strand straighten a zigzag,
  `e n i ≫ e n j ≫ e n i = e n i` when `i` and `j` are adjacent;
* `TauCeti.TLDiagCat.e_comp_e_comm`: generators at distance at least two commute.

Evaluating the circle at a loop value, these become the defining relations of the Temperley–Lieb
algebra in the endomorphism algebras of the linear Temperley–Lieb category.

## Implementation notes

Every relation is reduced, by moving straight strands in and out of the whiskerings, to a relation
between diagrams on at most three points: the quadratic relation on two points, the adjacent
relation on three, and the distant relation is the interchange law `whisker_exchange`. The
relations on two and three points are checked by evaluating both diagrams with `decide +kernel`.
This needs the definitions of matchings, of composition and juxtaposition of diagrams, and of the
category structure, which this file imports with `import all`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395–407.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace TLDiagCat

/-! ### Padding with straight strands -/

/-- An endomorphism `f` of `of m` with `a` straight strands on its left and `b` on its right, read
as an endomorphism of `of N` along `a + m + b = N`. -/
private def pad {m N : ℕ} (a b : ℕ) (h : a + m + b = N) (f : of m ⟶ of m) : of N ⟶ of N :=
  eqToHom (TLDiagCat.ext h.symm) ≫ (of a ◁ f) ▷ of b ≫ eqToHom (TLDiagCat.ext h)

private theorem pad_comp {m N : ℕ} (a b : ℕ) (h : a + m + b = N) (f g : of m ⟶ of m) :
    pad a b h f ≫ pad a b h g = pad a b h (f ≫ g) := by
  simp [pad]

/-- The diagram of a padded endomorphism: the diagram of `f` with straight strands on both
sides. -/
private theorem diagram_pad {m N : ℕ} (a b : ℕ) (h : a + m + b = N) (f : of m ⟶ of m) :
    (pad a b h f).diagram = TLDiagram.cast h h
      (((TLDiagram.id a).tensor f.diagram).tensor (TLDiagram.id b)) := by
  simp only [pad, diagram_comp, diagram_eqToHom, diagram_whiskerRight, diagram_whiskerLeft,
    TLDiagram.cast_id_comp, TLDiagram.comp_cast_id, TLDiagram.cast_cast]

private theorem pad_congr {m N a a' b b' : ℕ} (ha : a = a') (hb : b = b') (h : a + m + b = N)
    (f : of m ⟶ of m) : pad a b h f = pad a' b' (ha ▸ hb ▸ h) f := by
  subst ha hb
  rfl

/-- Straight strands on the left of `f` can be moved into the padding. -/
private theorem pad_whiskerLeft {m N : ℕ} (a b c : ℕ) (h : a + (c + m) + b = N)
    (f : of m ⟶ of m) : pad a b h (of c ◁ f) = pad (a + c) b (by omega) f := by
  -- The tensor product of objects adds the numbers of points, so this holds by definition.
  have hl : (of (a + c) ◁ f) = (of a ⊗ of c) ◁ f := rfl
  rw [pad, pad, hl]
  simp [associator_hom, associator_inv]

/-- Straight strands on the right of `f` can be moved into the padding. -/
private theorem pad_whiskerRight {m N : ℕ} (a b d : ℕ) (h : a + (m + d) + b = N)
    (f : of m ⟶ of m) : pad a b h (f ▷ of d) = pad a (d + b) (by omega) f := by
  -- The tensor product of objects adds the numbers of points, so this holds by definition.
  have hr : (of a ◁ f) ▷ of (d + b) = (of a ◁ f) ▷ (of d ⊗ of b) := rfl
  rw [pad, pad, hr]
  simp [associator_hom, associator_inv]

/-! ### The generators -/

/-- The **Temperley–Lieb generator** `e n i : of n ⟶ of n`, for `i < n - 1`: the bottom points `i`
and `i + 1` are joined by a cap, the top points `i` and `i + 1` by a cup, and every other point
runs straight up. It is `cap ≫ cup` with `i` straight strands on its left and `n - 2 - i` on its
right. -/
def e (n : ℕ) (i : Fin (n - 1)) : of n ⟶ of n :=
  eqToHom (TLDiagCat.ext (by simp; omega)) ≫ (of i ◁ (cap ≫ cup)) ▷ of (n - 2 - i) ≫
    eqToHom (TLDiagCat.ext (by simp; omega))

private theorem e_eq_pad (n : ℕ) (i : Fin (n - 1)) :
    e n i = pad i (n - 2 - i) (by omega) (cap ≫ cup) := (rfl)

/-- The diagram of a generator: the diagram `cap ≫ cup` on two points with `i` straight strands on
its left and `n - 2 - i` on its right, transported to `n` points. -/
theorem diagram_e (n : ℕ) (i : Fin (n - 1)) :
    (e n i).diagram = TLDiagram.cast (by simp; omega) (by simp; omega)
      (((TLDiagram.id i).tensor (TLDiagram.cap.comp TLDiagram.cup)).tensor
        (TLDiagram.id (n - 2 - i))) := by
  rw [e_eq_pad, diagram_pad]
  rfl

/-- On two points the only generator is `cap ≫ cup`. -/
theorem e_two (i : Fin (2 - 1)) : e 2 i = cap ≫ cup := by
  obtain rfl : i = 0 := Fin.ext (by omega)
  ext1
  simp [e_eq_pad, diagram_pad]

/-- The generators have no closed circles. -/
@[simp]
theorem circles_e (n : ℕ) (i : Fin (n - 1)) : (e n i).diagram.circles = 0 := by
  simp [e_eq_pad, diagram_pad]

/-- **The quadratic relation**: stacking a generator on itself closes one circle and leaves the
generator. -/
theorem e_comp_e_self (n : ℕ) (i : Fin (n - 1)) :
    e n i ≫ e n i = Hom.mk ⟨(e n i).diagram.matching, 1⟩ := by
  -- Between the cap and the cup of the lower copy, the upper copy closes a circle.
  have h₂ : (cap ≫ cup) ≫ (cap ≫ cup) = Hom.mk ⟨(cap ≫ cup).diagram.matching, 1⟩ := by
    ext1
    ext1
    · exact PlanarMatching.ext (by decide +kernel)
    · decide
  rw [e_eq_pad, pad_comp, h₂]
  ext1
  ext1 <;> simp [diagram_pad]

/-- The generator on the left two of three points. -/
private abbrev left : of 3 ⟶ of 3 := (cap ≫ cup) ▷ of 1

/-- The generator on the right two of three points. -/
private abbrev right : of 3 ⟶ of 3 := of 1 ◁ (cap ≫ cup)

/-- On three points the two generators straighten a zigzag, checked by computing the diagrams. -/
private theorem left_comp_right_comp_left : left ≫ right ≫ left = left := by
  ext1
  ext1
  · exact PlanarMatching.ext (by decide +kernel)
  · decide +kernel

private theorem right_comp_left_comp_right : right ≫ left ≫ right = right := by
  ext1
  ext1
  · exact PlanarMatching.ext (by decide +kernel)
  · decide +kernel

/-- Two adjacent generators, `e n i` and `e n (i + 1)`, are the two generators on three points
padded by the same straight strands. -/
private theorem e_eq_pad_left_and_e_eq_pad_right (n : ℕ) {i j : Fin (n - 1)}
    (hij : (i : ℕ) + 1 = j) :
    e n i = pad i (n - 3 - i) (by omega) left ∧ e n j = pad i (n - 3 - i) (by omega) right := by
  constructor
  · rw [e_eq_pad, pad_congr rfl (show n - 2 - i = 1 + (n - 3 - i) by omega)]
    exact (pad_whiskerRight _ _ _ _ _).symm
  · rw [e_eq_pad, pad_congr (show (j : ℕ) = i + 1 by omega) (show n - 2 - j = n - 3 - i by omega)]
    exact (pad_whiskerLeft _ _ _ _ _).symm

/-- **The adjacent relation**: two generators sharing a strand straighten a zigzag. -/
theorem e_comp_e_comp_e (n : ℕ) {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    e n i ≫ e n j ≫ e n i = e n i := by
  rcases h with h | h
  · obtain ⟨hi, hj⟩ := e_eq_pad_left_and_e_eq_pad_right n h
    rw [hi, hj, pad_comp, pad_comp, left_comp_right_comp_left]
  · obtain ⟨hj, hi⟩ := e_eq_pad_left_and_e_eq_pad_right n h
    rw [hi, hj, pad_comp, pad_comp, right_comp_left_comp_right]

/-- Two generators `e n i` and `e n j` with `i + 2 ≤ j` are the generators on the first two and
the last two points of `j - i + 2` points, padded by the same straight strands. -/
private theorem e_eq_pad_of_add_two_le (n : ℕ) {i j : Fin (n - 1)} (hij : (i : ℕ) + 2 ≤ j) :
    e n i = pad (m := 2 + (j - i - 2 + 2)) i (n - 2 - j) (by omega)
        ((cap ≫ cup) ▷ of (j - i - 2 + 2)) ∧
      e n j = pad (m := 2 + (j - i - 2 + 2)) i (n - 2 - j) (by omega)
        (of 2 ◁ of (j - i - 2) ◁ (cap ≫ cup)) := by
  constructor
  · rw [e_eq_pad, pad_congr rfl (show n - 2 - i = j - i - 2 + 2 + (n - 2 - j) by omega)]
    exact (pad_whiskerRight _ _ _ _ _).symm
  · rw [e_eq_pad, pad_congr (show (j : ℕ) = i + 2 + (j - i - 2) by omega) rfl,
      ← pad_whiskerLeft, ← pad_whiskerLeft]
    omega

/-- **The distant relation**: generators at distance at least two commute. -/
theorem e_comp_e_comm (n : ℕ) {i j : Fin (n - 1)} (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    e n i ≫ e n j = e n j ≫ e n i := by
  rcases h with h | h
  · obtain ⟨hi, hj⟩ := e_eq_pad_of_add_two_le n h
    rw [hi, hj, pad_comp, pad_comp, whisker_exchange]
  · obtain ⟨hj, hi⟩ := e_eq_pad_of_add_two_le n h
    rw [hi, hj, pad_comp, pad_comp, whisker_exchange]

end TLDiagCat

end TauCeti
