/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Compose
import all TauCeti.Combinatorics.PlanarMatching.Compose
import all TauCeti.Combinatorics.PlanarMatching.Glue
import all TauCeti.Combinatorics.PlanarMatching.Associativity

/-!
# Juxtaposition of Temperley–Lieb diagrams

The tensor product of two Temperley–Lieb diagrams `f : n → m` and `g : n' → m'` is the diagram
`f.tensor g : n + n' → m + m'` drawing `g` to the right of `f`. In the counterclockwise numbering
of the boundary points, the boundary of `f.tensor g` reads the bottom points of `f`, the bottom
points of `g`, the top points of `g` and then the top points of `f`. So the boundary of `g` is a
block of consecutive points sitting inside the boundary of `f`, after its bottom points: the
matching of `f.tensor g` is obtained by **nesting** the matching of `g` into the matching of `f`
(`TauCeti.PlanarMatching.nest`, from `TauCeti.Combinatorics.PlanarMatching.Glue`). The circles of
`f.tensor g` are those of `f` and of `g`.

The main result is the interchange law `TauCeti.TLDiagram.tensor_comp_tensor`: stacking two
juxtapositions is juxtaposing the two stacks, for the matchings and for the circle counts. This,
with `TauCeti.TLDiagram.id_tensor_id`, is the functoriality of juxtaposition for the composition
`TauCeti.TLDiagram.comp`. Juxtaposition is also strictly associative and unital, up to the
relabelling of the sizes (`TauCeti.TLDiagram.matching_tensor_assoc`,
`TauCeti.TLDiagram.matching_zero_tensor`, `TauCeti.TLDiagram.matching_tensor_zero`,
`TauCeti.TLDiagram.tensor_id_zero`). These are the diagram-level laws of the monoidal structure of
the Temperley–Lieb diagram category, whose tensor product adds the numbers of boundary points. The
two zigzags made of a cup, a cap and a strand straighten out to the identity strand
(`TauCeti.TLDiagram.cup_tensor_id_comp_id_tensor_cap`,
`TauCeti.TLDiagram.id_tensor_cup_comp_cap_tensor_id`).

## Main definitions

* `TauCeti.TLDiagram.tensor f g`: the juxtaposition of `f` and `g`, with `g` to the right of `f`.

## Main results

* `TauCeti.TLDiagram.tensor_comp_tensor`: the interchange law
  `(f ⊗ f') ≫ (g ⊗ g') = (f ≫ g) ⊗ (f' ≫ g')`.
* `TauCeti.TLDiagram.id_tensor_id`: the juxtaposition of two identities is an identity.
* `TauCeti.TLDiagram.matching_tensor_assoc`, `TauCeti.TLDiagram.matching_zero_tensor`,
  `TauCeti.TLDiagram.matching_tensor_zero`, `TauCeti.TLDiagram.tensor_id_zero`: associativity and
  unitality of juxtaposition.
* `TauCeti.TLDiagram.cup_tensor_id_comp_id_tensor_cap`,
  `TauCeti.TLDiagram.id_tensor_cup_comp_cap_tensor_id`: the zigzag identities.

## Implementation notes

As in `TauCeti.Combinatorics.PlanarMatching.Associativity`, everything is computed on partner
functions `ℕ → ℕ`. Nesting a block of `l` points at position `c` shifts every outer point `v ≥ c`
to `v + l`. Contracting two consecutive points outside the block, or inside it, commutes with the
nesting, and so does gluing a whole block of nested pairs. The interchange law then follows by
splitting the gluing of `m + m'` middle pairs into the `m` pairs between `f` and `g` and the
`m'` pairs between `f'` and `g'`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
-/

public section

namespace TauCeti

namespace PlanarMatching

/-! ### Contractions commute with nesting -/

section Contract

variable {c L : ℕ}

private theorem skipN_ne (a v : ℕ) : skipN a v ≠ a ∧ skipN a v ≠ a + 1 := by
  simp only [skipN]
  split_ifs <;> omega

/-- Splicing two consecutive outer points commutes with nesting. -/
private theorem splice_nestFn_shiftFrom {φ ψ : ℕ → ℕ} {a : ℕ} (hside : a + 1 < c ∨ c ≤ a)
    (hψ : ∀ j < L, ψ j < L) :
    splice (shiftFrom c L a) (nestFn c L φ ψ) = nestFn c L (splice a φ) ψ := by
  have hs : shiftFrom c L a + 1 = shiftFrom c L (a + 1) := by
    unfold shiftFrom
    split_ifs <;> omega
  funext z
  rcases exists_shiftFrom_or_add c L z with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · simp only [splice, rejoin, hs, shiftFrom_inj, nestFn_shiftFrom]
    split_ifs <;> rfl
  · have := hψ j hj
    have h₁ : shiftFrom c L a < c ∨ c + L ≤ shiftFrom c L a := shiftFrom_lt_or_le c L a
    have h₂ : shiftFrom c L (a + 1) < c ∨ c + L ≤ shiftFrom c L (a + 1) :=
      shiftFrom_lt_or_le c L (a + 1)
    rw [splice_of_ne _ (by omega) (by omega), nestFn_add _ _ _ hj, nestFn_add _ _ _ hj,
      rejoin_of_ne _ (by omega) (by omega)]

/-- Erasing two consecutive outer points commutes with nesting; the block moves from `c` to `c'`,
two places to the left if the erased points lie to its left. -/
private theorem erasePair_nestFn_shiftFrom {χ ψ : ℕ → ℕ} {a c' : ℕ}
    (hc : (c ≤ a ∧ c' = c) ∨ (a + 2 ≤ c ∧ c' + 2 = c)) (hψ : ∀ j < L, ψ j < L)
    (hχ : ∀ z, z ≠ a → z ≠ a + 1 → χ z ≠ a ∧ χ z ≠ a + 1) :
    erasePair (shiftFrom c L a) (nestFn c L χ ψ) = nestFn c' L (erasePair a χ) ψ := by
  funext q
  rcases exists_shiftFrom_or_add c' L q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · have e₁ : skipN (shiftFrom c L a) (shiftFrom c' L v) = shiftFrom c L (skipN a v) := by
      unfold skipN shiftFrom
      split_ifs <;> omega
    obtain ⟨h₁, h₂⟩ := hχ _ (skipN_ne a v).1 (skipN_ne a v).2
    have e₂ : ∀ w, w ≠ a → w ≠ a + 1 →
        unskipN (shiftFrom c L a) (shiftFrom c L w) = shiftFrom c' L (unskipN a w) := by
      intro w hw hw'
      unfold unskipN shiftFrom
      split_ifs <;> omega
    rw [erasePair_apply, e₁, nestFn_shiftFrom, e₂ _ h₁ h₂, nestFn_shiftFrom, erasePair_apply]
  · have := hψ j hj
    have e₁ : skipN (shiftFrom c L a) (c' + j) = c + j := by
      unfold skipN shiftFrom
      split_ifs <;> omega
    have e₂ : unskipN (shiftFrom c L a) (c + ψ j) = c' + ψ j := by
      unfold unskipN shiftFrom
      split_ifs <;> omega
    rw [erasePair_apply, e₁, nestFn_add _ _ _ hj, e₂, nestFn_add _ _ _ hj]

/-- Contracting two consecutive outer points commutes with nesting. -/
private theorem contractFn_nestFn_shiftFrom {K : ℕ} (x : PlanarMatching K) {ψ : ℕ → ℕ}
    {a c' : ℕ} (ha : a + 1 < K) (hc : (c ≤ a ∧ c' = c) ∨ (a + 2 ≤ c ∧ c' + 2 = c))
    (hψ : ∀ j < L, ψ j < L) :
    contractFn (shiftFrom c L a) (nestFn c L (pv x) ψ) = nestFn c' L (contractFn a (pv x)) ψ := by
  unfold contractFn
  rw [splice_nestFn_shiftFrom (by omega) hψ]
  exact erasePair_nestFn_shiftFrom hc hψ fun z hz hz' =>
    splice_ne (pv_pv_eq x) (pv_ne x (by omega)) (pv_ne x ha) hz hz'

private theorem circleInd_nestFn_shiftFrom {φ ψ : ℕ → ℕ} {a : ℕ} (hside : a + 1 < c ∨ c ≤ a) :
    circleInd (shiftFrom c L a) (nestFn c L φ ψ) = circleInd a φ := by
  have hs : shiftFrom c L a + 1 = shiftFrom c L (a + 1) := by
    unfold shiftFrom
    split_ifs <;> omega
  simp only [circleInd, nestFn_shiftFrom, hs, shiftFrom_inj]

/-- Contracting two consecutive points of the inserted block commutes with nesting. -/
private theorem contractFn_nestFn_add (φ : ℕ → ℕ) (y : PlanarMatching L) {a : ℕ}
    (ha : a + 2 ≤ L) :
    contractFn (c + a) (nestFn c L φ (pv y)) = nestFn c (L - 2) φ (contractFn a (pv y)) := by
  have hsp : splice (c + a) (nestFn c L φ (pv y)) = nestFn c L φ (splice a (pv y)) := by
    funext z
    rcases exists_shiftFrom_or_add c L z with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
    · have h₁ := shiftFrom_lt_or_le c L v
      have h₂ := shiftFrom_lt_or_le c L (φ v)
      rw [splice_of_ne _ (by omega) (by omega), nestFn_shiftFrom, nestFn_shiftFrom,
        rejoin_of_ne _ (by omega) (by omega)]
    · rw [nestFn_add _ _ _ hj]
      by_cases hja : j = a
      · rw [splice_of_eq_left _ (by omega), splice_of_eq_left _ hja, Nat.add_assoc]
      by_cases hja' : j = a + 1
      · rw [splice_of_eq_right _ (by omega), splice_of_eq_right _ hja']
      rw [splice_of_ne _ (by omega) (by omega), splice_of_ne _ hja hja', nestFn_add _ _ _ hj]
      have e₁ : nestFn c L φ (pv y) (c + a + 1) = c + pv y (a + 1) := by
        rw [Nat.add_assoc, nestFn_add _ _ _ (by omega)]
      simp only [rejoin, e₁, nestFn_add _ _ _ (by omega : a < L)]
      split_ifs <;> omega
  unfold contractFn
  rw [hsp]
  funext q
  rcases exists_shiftFrom_or_add c (L - 2) q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · have e₁ : skipN (c + a) (shiftFrom c (L - 2) v) = shiftFrom c L v := by
      unfold skipN shiftFrom
      split_ifs <;> omega
    have e₂ : ∀ w, unskipN (c + a) (shiftFrom c L w) = shiftFrom c (L - 2) w := by
      intro w
      unfold unskipN shiftFrom
      split_ifs <;> omega
    rw [erasePair_apply, e₁, nestFn_shiftFrom, e₂, nestFn_shiftFrom]
  · have hs : skipN a j < L := by unfold skipN; split_ifs <;> omega
    have e₁ : skipN (c + a) (c + j) = c + skipN a j := by
      unfold skipN
      split_ifs <;> omega
    have hw := splice_ne (pv_pv_eq y) (pv_ne y (by omega : a < L))
      (pv_ne y (by omega : a + 1 < L)) (skipN_ne a j).1 (skipN_ne a j).2
    have e₂ : ∀ w, w ≠ a → w ≠ a + 1 → unskipN (c + a) (c + w) = c + unskipN a w := by
      intro w hw hw'
      unfold unskipN
      split_ifs <;> omega
    rw [erasePair_apply, e₁, nestFn_add _ _ _ hs, e₂ _ hw.1 hw.2, nestFn_add _ _ _ hj,
      erasePair_apply]

private theorem circleInd_nestFn_add {φ ψ : ℕ → ℕ} {a : ℕ} (ha : a + 1 < L) :
    circleInd (c + a) (nestFn c L φ ψ) = circleInd a ψ := by
  simp only [circleInd, nestFn_add _ _ _ (by omega : a < L)]
  simp only [Nat.add_assoc, Nat.add_left_cancel_iff]

end Contract

/-! ### Gluing commutes with nesting -/

section Glue

/-- Gluing a block of nested pairs to the right of the inserted block commutes with nesting. -/
private theorem glueFn_nestFn_right {c L s : ℕ} (y : PlanarMatching L) :
    ∀ (j K : ℕ) (x : PlanarMatching K), c ≤ s → s + 2 * j ≤ K →
      glueFn (s + L) j (nestFn c L (pv x) (pv y)) = nestFn c L (glueFn s j (pv x)) (pv y) ∧
      glueCircles (s + L) j (nestFn c L (pv x) (pv y)) = glueCircles s j (pv x)
  | 0, K, x, _, _ => ⟨rfl, rfl⟩
  | j + 1, K, x, hcs, hK => by
    obtain ⟨x', hx'⟩ := exists_pv_eq_contractFn x (a := s + j) (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueFn_nestFn_right (c := c) (s := s) y j (K - 2) x' hcs (by omega)
    have hsh : s + L + j = shiftFrom c L (s + j) := by rw [shiftFrom_of_le (by omega)]; omega
    have hψ : ∀ i < L, pv y i < L := fun i hi => pv_lt y hi
    simp only [glueFn, glueCircles]
    rw [hsh, contractFn_nestFn_shiftFrom x (by omega) (Or.inl ⟨by omega, rfl⟩) hψ, ← hx', ih₁,
      ih₂, circleInd_nestFn_shiftFrom (by omega)]
    exact ⟨rfl, rfl⟩

/-- Gluing a block of nested pairs to the left of the inserted block commutes with nesting; the
inserted block moves `2 * j` places to the left. -/
private theorem glueFn_nestFn_left {s L : ℕ} (y : PlanarMatching L) :
    ∀ (j c K : ℕ) (x : PlanarMatching K), s + 2 * j ≤ c → s + 2 * j ≤ K →
      glueFn s j (nestFn c L (pv x) (pv y)) = nestFn (c - 2 * j) L (glueFn s j (pv x)) (pv y) ∧
      glueCircles s j (nestFn c L (pv x) (pv y)) = glueCircles s j (pv x)
  | 0, c, K, x, _, _ => ⟨rfl, rfl⟩
  | j + 1, c, K, x, hsc, hK => by
    obtain ⟨x', hx'⟩ := exists_pv_eq_contractFn x (a := s + j) (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueFn_nestFn_left (s := s) y j (c - 2) (K - 2) x' (by omega) (by omega)
    have hsh : s + j = shiftFrom c L (s + j) := (shiftFrom_of_lt (by omega)).symm
    have hψ : ∀ i < L, pv y i < L := fun i hi => pv_lt y hi
    have hc : c - 2 - 2 * j = c - 2 * (j + 1) := by omega
    have e₁ := contractFn_nestFn_shiftFrom x (c := c) (L := L) (a := s + j) (c' := c - 2)
      (by omega) (Or.inr ⟨by omega, by omega⟩) hψ
    have e₂ := circleInd_nestFn_shiftFrom (φ := pv x) (ψ := pv y) (c := c) (L := L) (a := s + j)
      (by omega)
    rw [← hsh] at e₁ e₂
    simp only [glueFn, glueCircles]
    rw [e₁, e₂, ← hx', ih₁, ih₂, hc]
    exact ⟨rfl, rfl⟩

/-- Gluing a block of nested pairs inside the inserted block commutes with nesting. -/
private theorem glueFn_nestFn_add {c s : ℕ} (φ : ℕ → ℕ) :
    ∀ (j L : ℕ) (y : PlanarMatching L), s + 2 * j ≤ L →
      glueFn (c + s) j (nestFn c L φ (pv y)) = nestFn c (L - 2 * j) φ (glueFn s j (pv y)) ∧
      glueCircles (c + s) j (nestFn c L φ (pv y)) = glueCircles s j (pv y)
  | 0, L, y, _ => ⟨rfl, rfl⟩
  | j + 1, L, y, hL => by
    obtain ⟨y', hy'⟩ := exists_pv_eq_contractFn y (a := s + j) (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueFn_nestFn_add (c := c) (s := s) φ j (L - 2) y' (by omega)
    have hL' : L - 2 - 2 * j = L - 2 * (j + 1) := by omega
    simp only [glueFn, glueCircles]
    rw [Nat.add_assoc, contractFn_nestFn_add φ y (by omega), ← hy', ih₁, ih₂, hL',
      circleInd_nestFn_add (by omega)]
    exact ⟨rfl, rfl⟩

/-- Gluing `j + i` nested pairs is gluing the inner `j` pairs and then the outer `i` pairs. -/
private theorem glueFn_add (a i : ℕ) :
    ∀ (j : ℕ) (φ : ℕ → ℕ),
      glueFn a (j + i) φ = glueFn a i (glueFn (a + i) j φ) ∧
      glueCircles a (j + i) φ = glueCircles a i (glueFn (a + i) j φ) + glueCircles (a + i) j φ
  | 0, φ => by simp [glueFn, glueCircles]
  | j + 1, φ => by
    obtain ⟨ih₁, ih₂⟩ := glueFn_add a i j (contractFn (a + i + j) φ)
    rw [Nat.add_right_comm j 1 i]
    simp only [glueFn, glueCircles]
    rw [← Nat.add_assoc, Nat.add_right_comm a j i, ih₁, ih₂]
    exact ⟨rfl, by omega⟩

end Glue

/-! ### Nesting, juxtaposition and nesting again -/

/-- Juxtaposing on the right does not move a block nested into the left factor. -/
private theorem appendFn_nestFn_left {K K' c L : ℕ} (φ ψ χ : ℕ → ℕ) (hc : c ≤ K) :
    appendFn (K + L) K' (nestFn c L φ ψ) χ = nestFn c L (appendFn K K' φ χ) ψ := by
  funext q
  rcases exists_shiftFrom_or_add c L q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [nestFn_shiftFrom]
    by_cases h₁ : v < K
    · have : shiftFrom c L v < K + L := by unfold shiftFrom; split_ifs <;> omega
      rw [appendFn_of_lt _ _ this, nestFn_shiftFrom, appendFn_of_lt _ _ h₁]
    rw [shiftFrom_of_le (by omega)]
    by_cases h₂ : v < K + K'
    · rw [appendFn_of_le_of_lt _ _ (by omega) (by omega), appendFn_of_le_of_lt _ _ (by omega) h₂,
        shiftFrom_of_le (by omega), Nat.add_sub_add_right]
      omega
    · rw [appendFn_of_le _ _ (by omega), appendFn_of_le _ _ (by omega), shiftFrom_of_le (by omega)]
  · rw [appendFn_of_lt _ _ (by omega), nestFn_add _ _ _ hj, nestFn_add _ _ _ hj]

/-- Juxtaposing on the left moves a block nested into the right factor past the left factor. -/
private theorem appendFn_nestFn_right {K K' c L : ℕ} (φ ψ χ : ℕ → ℕ) (hc : c ≤ K')
    (hφ : ∀ q < K, φ q < K) :
    appendFn K (K' + L) φ (nestFn c L χ ψ) = nestFn (K + c) L (appendFn K K' φ χ) ψ := by
  funext q
  rcases exists_shiftFrom_or_add (K + c) L q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [nestFn_shiftFrom]
    by_cases h₁ : v < K
    · have := hφ v h₁
      rw [shiftFrom_of_lt (by omega), appendFn_of_lt _ _ h₁, appendFn_of_lt _ _ h₁,
        shiftFrom_of_lt (by omega)]
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (Nat.not_lt.mp h₁)
    rw [shiftFrom_add_add]
    by_cases h₂ : u < K'
    · have : shiftFrom c L u < K' + L := by unfold shiftFrom; split_ifs <;> omega
      rw [appendFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel_left,
        nestFn_shiftFrom, appendFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel_left,
        shiftFrom_add_add]
    · have : K' + L ≤ shiftFrom c L u := by unfold shiftFrom; split_ifs <;> omega
      rw [appendFn_of_le _ _ (by omega), appendFn_of_le _ _ (by omega), shiftFrom_add_add]
  · rw [nestFn_add _ _ _ hj, appendFn_of_le_of_lt _ _ (by omega) (by omega),
      show K + c + j - K = c + j by omega, nestFn_add _ _ _ hj, Nat.add_assoc]

private theorem shiftFrom_shiftFrom (c L L' v : ℕ) :
    shiftFrom c L (shiftFrom c L' v) = shiftFrom c (L + L') v := by
  unfold shiftFrom
  split_ifs <;> omega

/-- Nesting two blocks at the same position is nesting their juxtaposition. -/
private theorem nestFn_nestFn_eq_nestFn_appendFn {c L L' : ℕ} (φ ψ χ : ℕ → ℕ) :
    nestFn c L (nestFn c L' φ χ) ψ = nestFn c (L + L') φ (appendFn L L' ψ χ) := by
  funext q
  rcases exists_shiftFrom_or_add c L q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [nestFn_shiftFrom]
    rcases exists_shiftFrom_or_add c L' v with ⟨w, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [nestFn_shiftFrom, shiftFrom_shiftFrom, shiftFrom_shiftFrom, nestFn_shiftFrom]
    · rw [nestFn_add _ _ _ hi, shiftFrom_of_le (by omega), shiftFrom_of_le (by omega),
        show c + i + L = c + (L + i) by omega, nestFn_add _ _ _ (by omega),
        appendFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel_left]
      omega
  · rw [nestFn_add _ _ _ hj, nestFn_add _ _ _ (by omega), appendFn_of_lt _ _ hj]

end PlanarMatching

namespace TLDiagram

variable {n m p n' m' p' n'' m'' : ℕ}

open PlanarMatching

/-- **Juxtaposition** of Temperley–Lieb diagrams: `f.tensor g : n + n' → m + m'` draws
`g : n' → m'` to the right of `f : n → m`. Its matching nests the matching of `g` into that of
`f`, after the bottom points of `f`, and its circles are those of `f` and of `g`. -/
def tensor (f : TLDiagram n m) (g : TLDiagram n' m') : TLDiagram (n + n') (m + m') where
  matching := PlanarMatching.cast (by omega) (f.matching.nest g.matching)
  circles := f.circles + g.circles

/-- The matching of a juxtaposition nests the matching of the right factor into that of the left
factor. -/
@[simp]
theorem matching_tensor (f : TLDiagram n m) (g : TLDiagram n' m') :
    (f.tensor g).matching = PlanarMatching.cast (by omega) (f.matching.nest g.matching) := (rfl)

/-- The circles of a juxtaposition are those of both factors. -/
@[simp]
theorem circles_tensor (f : TLDiagram n m) (g : TLDiagram n' m') :
    (f.tensor g).circles = f.circles + g.circles := (rfl)

/-- Gluing the `m + m'` middle pairs of two stacked juxtapositions glues the `m` pairs between `f`
and `g` and the `m'` pairs between `f'` and `g'`, nesting the second result into the first, and
closes the circles closed in either middle. -/
private theorem glue_append_tensor (f : TLDiagram n m) (g : TLDiagram m p) (f' : TLDiagram n' m')
    (g' : TLDiagram m' p') :
    glueFn (n + n') (m + m') (pv ((f.tensor f').matching.append (g.tensor g').matching)) =
        nestFn n (n' + p') (glueFn n m (pv (f.matching.append g.matching)))
          (glueFn n' m' (pv (f'.matching.append g'.matching))) ∧
      glueCircles (n + n') (m + m') (pv ((f.tensor f').matching.append (g.tensor g').matching)) =
        glueCircles n m (pv (f.matching.append g.matching)) +
          glueCircles n' m' (pv (f'.matching.append g'.matching)) := by
  -- The juxtaposition of `f ⊗ f'` and `g ⊗ g'` nests `f'` and `g'` into the juxtaposition `W` of
  -- `f` and `g`, on either side of the `m` middle pairs between `f` and `g`.
  obtain ⟨W, hW⟩ : ∃ W : PlanarMatching (n + m + m + p),
      pv W = pv (f.matching.append g.matching) :=
    ⟨PlanarMatching.cast (by omega) _, pv_cast_eq _ _⟩
  have hA : pv ((f.tensor f').matching.append (g.tensor g').matching) =
      nestFn n (n' + m') (pv (W.nest g'.matching)) (pv f'.matching) := by
    simp only [pv_append_eq, matching_tensor, pv_cast_eq, pv_nest, hW]
    rw [Nat.add_add_add_comm n n' m m', appendFn_nestFn_left _ _ _ (by omega : n ≤ n + m),
      Nat.add_add_add_comm m m' p p',
      appendFn_nestFn_right _ _ _ (by omega : m ≤ m + p) fun q hq => pv_lt _ hq]
  -- Glue the `m` pairs between `f` and `g` first, then the `m'` pairs between `f'` and `g'`.
  obtain ⟨hS₁, hS₂⟩ := glueFn_add (n + n') m' m
    (pv ((f.tensor f').matching.append (g.tensor g').matching))
  obtain ⟨hR₁, hR₂⟩ := glueFn_nestFn_right (c := n) (s := n) f'.matching m _ (W.nest g'.matching)
    le_rfl (by omega)
  obtain ⟨hL₁, hL₂⟩ := glueFn_nestFn_left (s := n) g'.matching m (n + m + m) _ W (by omega)
    (by omega)
  obtain ⟨hI₁, hI₂⟩ := glueFn_nestFn_add (c := n) (s := n') (glueFn n m (pv W)) m' _
    (f'.matching.append g'.matching) (by omega)
  have e₂ : n + m + m - 2 * m = n := by omega
  have e₃ : n' + m' + (m' + p') - 2 * m' = n' + p' := by omega
  rw [hS₁, hS₂, Nat.add_assoc n n' m', hA, hR₁, hR₂, pv_nest, hL₁, hL₂, e₂,
    nestFn_nestFn_eq_nestFn_appendFn, ← pv_append_eq, hI₁, hI₂, e₃, hW]
  exact ⟨rfl, Nat.add_comm _ _⟩

/-- **The interchange law**: stacking two juxtapositions is juxtaposing the two stacks,
`(f ⊗ f') ≫ (g ⊗ g') = (f ≫ g) ⊗ (f' ≫ g')`. Gluing the `m + m'` middle points closes the circles
closed between `f` and `g` and those closed between `f'` and `g'`, and no others. -/
theorem tensor_comp_tensor (f : TLDiagram n m) (g : TLDiagram m p) (f' : TLDiagram n' m')
    (g' : TLDiagram m' p') :
    (f.tensor f').comp (g.tensor g') = (f.comp g).tensor (f'.comp g') := by
  obtain ⟨hM, hC⟩ := glue_append_tensor f g f' g'
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_comp, pv_glueMiddle, hM]
    simp only [matching_tensor, matching_comp, pv_cast_eq, pv_nest, pv_glueMiddle]
  · rw [circles_comp, glueMiddleCircles_eq, hC]
    simp only [circles_tensor, circles_comp, glueMiddleCircles_eq]
    omega

/-- The juxtaposition of two identity diagrams is an identity diagram. -/
@[simp]
theorem id_tensor_id (n n' : ℕ) : (id n).tensor (id n') = id (n + n') := by
  ext : 1
  · simp [matching_id]
  · simp

/-- **Associativity of juxtaposition**: up to the relabelling of the sizes, `(f ⊗ g) ⊗ h` and
`f ⊗ (g ⊗ h)` have the same matching. They have the same circles by `circles_tensor`. -/
theorem matching_tensor_assoc (f : TLDiagram n m) (g : TLDiagram n' m') (h : TLDiagram n'' m'') :
    ((f.tensor g).tensor h).matching =
      PlanarMatching.cast (by omega) (f.tensor (g.tensor h)).matching := by
  apply eq_of_pv_eq
  simp only [matching_tensor, pv_cast_eq, pv_nest]
  rw [nestFn_nestFn_assoc _ _ _ (by omega : n' ≤ n' + m'),
    show n' + m' + (n'' + m'') = n' + n'' + (m' + m'') by omega]

/-- Juxtaposing with a diagram `0 → 0` on the left keeps the matching, up to the relabelling of
the sizes. -/
theorem matching_zero_tensor (g : TLDiagram 0 0) (f : TLDiagram n m) :
    (g.tensor f).matching = PlanarMatching.cast (by omega) f.matching := by
  rw [matching_tensor, zero_nest, PlanarMatching.cast_cast]

/-- Juxtaposing with a diagram `0 → 0` on the right keeps the matching. -/
theorem matching_tensor_zero (f : TLDiagram n m) (g : TLDiagram 0 0) :
    (f.tensor g).matching = f.matching := by
  apply eq_of_pv_eq
  rw [matching_tensor, pv_cast_eq, nest_zero]

/-- Juxtaposing with the empty diagram on the right changes nothing. -/
@[simp]
theorem tensor_id_zero (f : TLDiagram n m) : f.tensor (id 0) = f := by
  ext : 1
  · exact matching_tensor_zero f (id 0)
  · simp

/-- **A zigzag**: a cup next to a strand, followed by the strand next to a cap, straightens out to
the identity strand and closes no circle. -/
@[simp]
theorem cup_tensor_id_comp_id_tensor_cap : (cup.tensor (id 1)).comp ((id 1).tensor cap) = id 1 := by
  ext : 1
  · refine ext_pv fun q hq => ?_
    simp only [matching_comp, pv_glueMiddle, pv_append_eq, matching_tensor, pv_cast_eq, pv_nest,
      matching_id]
    obtain _ | _ | q := q <;>
      first
      | omega
      | simp [glueFn, contractFn, erasePair, splice, rejoin, skipN, unskipN, appendFn, nestFn,
          shiftFrom, pv_nested, pv_cup_matching, pv_cap_matching]
  · simp only [circles_comp, circles_tensor, glueMiddleCircles_eq, pv_append_eq, matching_tensor,
      pv_cast_eq, pv_nest, matching_id]
    simp [glueCircles, contractFn, erasePair, splice, rejoin, skipN, unskipN, appendFn, nestFn,
      shiftFrom, pv_nested, pv_cup_matching, circleInd]

/-- **The other zigzag**: a strand next to a cup, followed by a cap next to the strand, straightens
out to the identity strand and closes no circle. -/
@[simp]
theorem id_tensor_cup_comp_cap_tensor_id : ((id 1).tensor cup).comp (cap.tensor (id 1)) = id 1 := by
  ext : 1
  · refine ext_pv fun q hq => ?_
    simp only [matching_comp, pv_glueMiddle, pv_append_eq, matching_tensor, pv_cast_eq, pv_nest,
      matching_id]
    obtain _ | _ | q := q <;>
      first
      | omega
      | simp [glueFn, contractFn, erasePair, splice, rejoin, skipN, unskipN, appendFn, nestFn,
          shiftFrom, pv_nested, pv_cup_matching, pv_cap_matching]
  · simp only [circles_comp, circles_tensor, glueMiddleCircles_eq, pv_append_eq, matching_tensor,
      pv_cast_eq, pv_nest, matching_id]
    simp [glueCircles, contractFn, erasePair, splice, rejoin, skipN, unskipN, appendFn, nestFn,
      shiftFrom, pv_nested, pv_cup_matching, pv_cap_matching, circleInd]

end TLDiagram

/-- Juxtaposition is not commutative: a cap next to a strand on its right and a cap next to a
strand on its left are different diagrams `3 → 1`. -/
example : TLDiagram.cap.tensor (TLDiagram.id 1) ≠ (TLDiagram.id 1).tensor TLDiagram.cap := by
  intro h
  have h₀ := congrArg (fun d => PlanarMatching.pv d.matching 0) h
  simp [PlanarMatching.pv_nest, PlanarMatching.nestFn, PlanarMatching.shiftFrom,
    PlanarMatching.pv_nested, TLDiagram.pv_cap_matching] at h₀

end TauCeti
