/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Compose
import all TauCeti.Combinatorics.PlanarMatching.Glue

/-!
# Associativity of the composition of Temperley–Lieb diagrams

For diagrams `f : n → m`, `g : m → p` and `h : p → q`, both bracketings of the composite glue the
three diagrams along their two middle boundaries, and they close the same circles:
`TauCeti.TLDiagram.comp_assoc` says `(f.comp g).comp h = f.comp (g.comp h)`, for the matchings and
for the circle counts.

Stacking the three diagrams juxtaposes their matchings on `n + m + (m + p) + (p + q)` points, with
two blocks of nested pairs to be contracted: the `m` pairs around the junction of `f` and `g`, and
the `p` pairs around the junction of `g` and `h`. The bracketing `(f.comp g).comp h` contracts the
first block and then the second, and `f.comp (g.comp h)` the second and then the first. So the
theorem reduces to the fact that contractions of two disjoint pairs of consecutive points commute,
and close the same number of circles in either order.

## Implementation notes

All index arithmetic is done on partner functions `ℕ → ℕ`, as in
`TauCeti.Combinatorics.PlanarMatching.Glue`: a planar matching of `K` points is read as the map
sending each boundary point to its partner and fixing every number `≥ K`. On partner functions,
contracting the pair `a`, `a + 1` is the composite of two simpler operations: **splicing**, which
joins `a` to `a + 1` and joins their former partners to each other, and **erasing** the pair
`a`, `a + 1` from the boundary. Splicings of disjoint pairs commute, erasures of disjoint pairs
commute, and a splicing commutes with the erasure of a disjoint pair; each of these is a short case
analysis. Gluing a whole block, and juxtaposition, are then handled by induction on the number of
pairs. Everything except the theorem itself is private.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
-/

public section

namespace TauCeti

namespace PlanarMatching

/-! ### Partner functions -/

/-- The new partner of a point whose partner was `v`, once the points `a` and `a + 1` are joined:
the partners of `a` and `a + 1` become partners of each other. -/
private def rejoin (φ : ℕ → ℕ) (a v : ℕ) : ℕ :=
  if v = a then φ (a + 1) else if v = a + 1 then φ a else v

/-- **Splicing** the pair `a`, `a + 1` in the partner function `φ`: `a` and `a + 1` become
partners, and so do their former partners. -/
private def splice (a : ℕ) (φ : ℕ → ℕ) (z : ℕ) : ℕ :=
  if z = a then a + 1 else if z = a + 1 then a else rejoin φ a (φ z)

/-- **Erasing** the points `a` and `a + 1` from the boundary, renumbering the others in order. -/
private def erasePair (a : ℕ) (ψ : ℕ → ℕ) (q : ℕ) : ℕ :=
  unskipN a (ψ (skipN a q))

/-- Contracting the consecutive points `a` and `a + 1`, on partner functions: splice, then erase. -/
private def contractFn (a : ℕ) (φ : ℕ → ℕ) : ℕ → ℕ :=
  erasePair a (splice a φ)

/-- `1` if contracting `a` and `a + 1` closes a circle, that is, if they are partners. -/
private def circleInd (a : ℕ) (φ : ℕ → ℕ) : ℕ :=
  if φ a = a + 1 then 1 else 0

/-- Contracting the `j` nested pairs of consecutive points of the block `n, …, n + 2 * j - 1`,
innermost first, on partner functions: the partner function of
`TauCeti.PlanarMatching.glueMiddle`. -/
private def glueFn (n : ℕ) : ℕ → (ℕ → ℕ) → ℕ → ℕ
  | 0, φ => φ
  | j + 1, φ => glueFn n j (contractFn (n + j) φ)

/-- The number of circles closed by `glueFn n j`: the partner function version of
`TauCeti.PlanarMatching.glueMiddleCircles`. -/
private def glueCircles (n : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | j + 1, φ => glueCircles n j (contractFn (n + j) φ) + circleInd (n + j) φ

/-- Juxtaposition of partner functions on `k` and on `l` points. -/
private def appendFn (k l : ℕ) (φ ψ : ℕ → ℕ) (q : ℕ) : ℕ :=
  if q < k then φ q else if q < k + l then k + ψ (q - k) else q

/-! ### Evaluation lemmas -/

private theorem rejoin_of_eq_left (φ : ℕ → ℕ) {a v : ℕ} (h : v = a) : rejoin φ a v = φ (a + 1) := by
  simp [rejoin, h]

private theorem rejoin_of_eq_right (φ : ℕ → ℕ) {a v : ℕ} (h : v = a + 1) : rejoin φ a v = φ a := by
  simp [rejoin, h]

private theorem rejoin_of_ne (φ : ℕ → ℕ) {a v : ℕ} (h : v ≠ a) (h' : v ≠ a + 1) :
    rejoin φ a v = v := by
  simp [rejoin, h, h']

private theorem splice_of_eq_left (φ : ℕ → ℕ) {a z : ℕ} (h : z = a) : splice a φ z = a + 1 := by
  simp [splice, h]

private theorem splice_of_eq_right (φ : ℕ → ℕ) {a z : ℕ} (h : z = a + 1) : splice a φ z = a := by
  simp [splice, h]

private theorem splice_of_ne (φ : ℕ → ℕ) {a z : ℕ} (h : z ≠ a) (h' : z ≠ a + 1) :
    splice a φ z = rejoin φ a (φ z) := by
  simp [splice, h, h']

private theorem unskipN_of_lt {a v : ℕ} (h : v < a) : unskipN a v = v := by
  simp [unskipN, h]

private theorem unskipN_of_le {a v : ℕ} (h : a ≤ v) : unskipN a v = v - 2 := by
  simp [unskipN, Nat.not_lt.mpr h]

private theorem skipN_of_lt {a q : ℕ} (h : q < a) : skipN a q = q := by
  simp [skipN, h]

private theorem skipN_of_le {a q : ℕ} (h : a ≤ q) : skipN a q = q + 2 := by
  simp [skipN, Nat.not_lt.mpr h]

private theorem erasePair_apply (a : ℕ) (ψ : ℕ → ℕ) (q : ℕ) :
    erasePair a ψ q = unskipN a (ψ (skipN a q)) := (rfl)

private theorem appendFn_of_lt {k l q : ℕ} (φ ψ : ℕ → ℕ) (h : q < k) :
    appendFn k l φ ψ q = φ q := by
  simp [appendFn, h]

private theorem appendFn_of_le_of_lt {k l q : ℕ} (φ ψ : ℕ → ℕ) (h : k ≤ q) (h' : q < k + l) :
    appendFn k l φ ψ q = k + ψ (q - k) := by
  simp [appendFn, Nat.not_lt.mpr h, h']

private theorem appendFn_of_le {k l q : ℕ} (φ ψ : ℕ → ℕ) (h : k + l ≤ q) :
    appendFn k l φ ψ q = q := by
  have hk : ¬q < k := by omega
  simp [appendFn, Nat.not_lt.mpr h, hk]

/-! ### Splicing and erasing commute -/

private theorem splice_involutive {φ : ℕ → ℕ} (hφ : ∀ z, φ (φ z) = z) {a : ℕ} (h₁ : φ a ≠ a)
    (h₂ : φ (a + 1) ≠ a + 1) (z : ℕ) : splice a φ (splice a φ z) = z := by
  have i₁ : ∀ u v, φ u = v → φ v = u := fun u v h => by rw [← h, hφ]
  by_cases hza : z = a
  · rw [splice_of_eq_left _ hza, splice_of_eq_right _ rfl, hza]
  by_cases hza' : z = a + 1
  · rw [splice_of_eq_right _ hza', splice_of_eq_left _ rfl, hza']
  rw [splice_of_ne _ hza hza']
  have := i₁ z a; have := i₁ z (a + 1); have := i₁ (a + 1) a; have := i₁ a (a + 1)
  unfold rejoin
  split_ifs with h₃ h₄
  · rw [splice_of_ne _ (by omega) (by omega), hφ, rejoin_of_eq_right _ rfl]
    omega
  · rw [splice_of_ne _ (by omega) (by omega), hφ, rejoin_of_eq_left _ rfl]
    omega
  · rw [splice_of_ne _ h₃ h₄, hφ, rejoin_of_ne _ hza hza']

private theorem splice_ne_self {φ : ℕ → ℕ} (hφ : ∀ z, φ (φ z) = z) {b z : ℕ} (hz : z ≠ b)
    (hz' : z ≠ b + 1) (h : φ z ≠ z) : splice b φ z ≠ z := by
  have i₁ : ∀ u v, φ u = v → φ v = u := fun u v h => by rw [← h, hφ]
  have := i₁ z b; have := i₁ z (b + 1); have := i₁ b z; have := i₁ (b + 1) z
  rw [splice_of_ne _ hz hz']
  unfold rejoin
  split_ifs <;> omega

private theorem splice_erasePair {ψ : ℕ → ℕ} (hψ : ∀ z, ψ (ψ z) = z) {a b : ℕ} (hab : a + 1 < b)
    (hb : ψ b = b + 1) : splice a (erasePair b ψ) = erasePair b (splice a ψ) := by
  have hb' : ψ (b + 1) = b := by rw [← hb, hψ]
  funext q
  rw [erasePair_apply b (splice a ψ)]
  by_cases hqa : q = a
  · rw [splice_of_eq_left _ hqa, skipN_of_lt (by omega), splice_of_eq_left _ hqa,
      unskipN_of_lt (by omega)]
  by_cases hqa' : q = a + 1
  · rw [splice_of_eq_right _ hqa', skipN_of_lt (by omega), splice_of_eq_right _ hqa',
      unskipN_of_lt (by omega)]
  have hz : skipN b q ≠ a ∧ skipN b q ≠ a + 1 ∧ skipN b q ≠ b ∧ skipN b q ≠ b + 1 := by
    simp only [skipN]; split_ifs <;> omega
  rw [splice_of_ne _ hqa hqa', splice_of_ne _ hz.1 hz.2.1, erasePair_apply]
  generalize skipN b q = z at hz
  have hV : ψ z ≠ b ∧ ψ z ≠ b + 1 := ⟨fun h => hz.2.2.2 (by rw [← hψ z, h, hb]),
    fun h => hz.2.2.1 (by rw [← hψ z, h, hb'])⟩
  by_cases hVa : ψ z = a
  · rw [rejoin_of_eq_left _ hVa, hVa, unskipN_of_lt (by omega), rejoin_of_eq_left _ rfl,
      erasePair_apply, skipN_of_lt (by omega)]
  by_cases hVa' : ψ z = a + 1
  · rw [rejoin_of_eq_right _ hVa', hVa', unskipN_of_lt (by omega), rejoin_of_eq_right _ rfl,
      erasePair_apply, skipN_of_lt (by omega)]
  rw [rejoin_of_ne _ hVa hVa', rejoin_of_ne]
  · simp only [unskipN]; split_ifs <;> omega
  · simp only [unskipN]; split_ifs <;> omega

private theorem splice_erasePair_right {ψ : ℕ → ℕ} (hψ : ∀ z, ψ (ψ z) = z) {a b : ℕ}
    (hab : a ≤ b) (ha : ψ a = a + 1) :
    splice b (erasePair a ψ) = erasePair a (splice (b + 2) ψ) := by
  have ha' : ψ (a + 1) = a := by rw [← ha, hψ]
  funext q
  rw [erasePair_apply a (splice (b + 2) ψ)]
  by_cases hqb : q = b
  · rw [splice_of_eq_left _ hqb, skipN_of_le (by omega), splice_of_eq_left _ (by omega),
      unskipN_of_le (by omega)]
    omega
  by_cases hqb' : q = b + 1
  · rw [splice_of_eq_right _ hqb', skipN_of_le (by omega), splice_of_eq_right _ (by omega),
      unskipN_of_le (by omega)]
    omega
  have hz : skipN a q ≠ a ∧ skipN a q ≠ a + 1 ∧ skipN a q ≠ b + 2 ∧ skipN a q ≠ b + 2 + 1 := by
    simp only [skipN]; split_ifs <;> omega
  rw [splice_of_ne _ hqb hqb', splice_of_ne _ hz.2.2.1 hz.2.2.2, erasePair_apply]
  generalize skipN a q = z at hz
  have hV : ψ z ≠ a ∧ ψ z ≠ a + 1 := ⟨fun h => hz.2.1 (by rw [← hψ z, h, ha]),
    fun h => hz.1 (by rw [← hψ z, h, ha'])⟩
  by_cases hVb : ψ z = b + 2
  · rw [rejoin_of_eq_left _ hVb, hVb, unskipN_of_le (by omega), rejoin_of_eq_left _ (by omega),
      erasePair_apply, skipN_of_le (by omega)]
  by_cases hVb' : ψ z = b + 2 + 1
  · rw [rejoin_of_eq_right _ hVb', hVb', unskipN_of_le (by omega), rejoin_of_eq_right _ (by omega),
      erasePair_apply, skipN_of_le (by omega)]
  rw [rejoin_of_ne _ hVb hVb', rejoin_of_ne]
  · simp only [unskipN]; split_ifs <;> omega
  · simp only [unskipN]; split_ifs <;> omega

private theorem erasePair_erasePair {ψ : ℕ → ℕ} (hψ : ∀ z, ψ (ψ z) = z) {a b : ℕ} (hab : a ≤ b)
    (ha : ψ a = a + 1) (hb : ψ (b + 2) = b + 2 + 1) :
    erasePair a (erasePair (b + 2) ψ) = erasePair b (erasePair a ψ) := by
  have ha' : ψ (a + 1) = a := by rw [← ha, hψ]
  have hb' : ψ (b + 2 + 1) = b + 2 := by rw [← hb, hψ]
  funext q
  simp only [erasePair_apply]
  have hs : skipN (b + 2) (skipN a q) = skipN a (skipN b q) := by
    simp only [skipN]; split_ifs <;> omega
  have hz : skipN a (skipN b q) ≠ a ∧ skipN a (skipN b q) ≠ a + 1 ∧
      skipN a (skipN b q) ≠ b + 2 ∧ skipN a (skipN b q) ≠ b + 2 + 1 := by
    simp only [skipN]; split_ifs <;> omega
  rw [hs]
  generalize skipN a (skipN b q) = z at hz
  have hV : ψ z ≠ a ∧ ψ z ≠ a + 1 ∧ ψ z ≠ b + 2 ∧ ψ z ≠ b + 2 + 1 :=
    ⟨fun h => hz.2.1 (by rw [← hψ z, h, ha]), fun h => hz.1 (by rw [← hψ z, h, ha']),
      fun h => hz.2.2.2 (by rw [← hψ z, h, hb]), fun h => hz.2.2.1 (by rw [← hψ z, h, hb'])⟩
  generalize ψ z = V at hV
  simp only [unskipN]
  split_ifs <;> omega

private theorem rejoin_splice_right {φ : ℕ → ℕ} {a b v : ℕ} (hab : a + 1 < b)
    (h₁ : v = b → φ (b + 1) ≠ a ∧ φ (b + 1) ≠ a + 1) (h₂ : v = b + 1 → φ b ≠ a ∧ φ b ≠ a + 1) :
    rejoin (splice a φ) b v = rejoin φ b v := by
  unfold rejoin
  split_ifs with hv hv'
  · rw [splice_of_ne _ (by omega) (by omega), rejoin_of_ne _ (h₁ hv).1 (h₁ hv).2]
  · rw [splice_of_ne _ (by omega) (by omega), rejoin_of_ne _ (h₂ hv').1 (h₂ hv').2]
  · rfl

private theorem rejoin_splice_left {φ : ℕ → ℕ} {a b v : ℕ} (hab : a + 1 < b)
    (h₁ : v = a → φ (a + 1) ≠ b ∧ φ (a + 1) ≠ b + 1) (h₂ : v = a + 1 → φ a ≠ b ∧ φ a ≠ b + 1) :
    rejoin (splice b φ) a v = rejoin φ a v := by
  unfold rejoin
  split_ifs with hv hv'
  · rw [splice_of_ne _ (by omega) (by omega), rejoin_of_ne _ (h₁ hv).1 (h₁ hv).2]
  · rw [splice_of_ne _ (by omega) (by omega), rejoin_of_ne _ (h₂ hv').1 (h₂ hv').2]
  · rfl

private theorem splice_splice {φ : ℕ → ℕ} (hφ : ∀ z, φ (φ z) = z) {a b : ℕ} (hab : a + 1 < b) :
    splice a (splice b φ) = splice b (splice a φ) := by
  funext z
  by_cases hza : z = a
  · rw [splice_of_eq_left _ hza, splice_of_ne _ (by omega) (by omega), splice_of_eq_left _ hza,
      rejoin_of_ne _ (by omega) (by omega)]
  by_cases hza' : z = a + 1
  · rw [splice_of_eq_right _ hza', splice_of_ne _ (by omega) (by omega), splice_of_eq_right _ hza',
      rejoin_of_ne _ (by omega) (by omega)]
  by_cases hzb : z = b
  · rw [splice_of_eq_left _ hzb, splice_of_ne _ (by omega) (by omega), splice_of_eq_left _ hzb,
      rejoin_of_ne _ (by omega) (by omega)]
  by_cases hzb' : z = b + 1
  · rw [splice_of_eq_right _ hzb', splice_of_ne _ (by omega) (by omega), splice_of_eq_right _ hzb',
      rejoin_of_ne _ (by omega) (by omega)]
  rw [splice_of_ne _ hza hza', splice_of_ne _ hzb hzb', splice_of_ne _ hzb hzb',
    splice_of_ne _ hza hza']
  have e₁ : splice b φ (a + 1) = rejoin φ b (φ (a + 1)) := splice_of_ne _ (by omega) (by omega)
  have e₂ : splice b φ a = rejoin φ b (φ a) := splice_of_ne _ (by omega) (by omega)
  have e₃ : splice a φ (b + 1) = rejoin φ a (φ (b + 1)) := splice_of_ne _ (by omega) (by omega)
  have e₄ : splice a φ b = rejoin φ a (φ b) := splice_of_ne _ (by omega) (by omega)
  have i₁ : ∀ u v, φ u = v → φ v = u := fun u v h => by rw [← h, hφ]
  have hcases : φ z = a ∨ φ z = a + 1 ∨ φ z = b ∨ φ z = b + 1 ∨
      (φ z ≠ a ∧ φ z ≠ a + 1 ∧ φ z ≠ b ∧ φ z ≠ b + 1) := by omega
  rcases hcases with h | h | h | h | h
  · have := i₁ z a h; have := i₁ (b + 1) a; have := i₁ (b + 1) (a + 1); have := i₁ b a
    have := i₁ b (a + 1)
    rw [h, rejoin_of_ne (a := b) (v := a) _ (by omega) (by omega), rejoin_of_eq_left _ rfl, e₁,
      rejoin_of_eq_left _ rfl,
      rejoin_splice_right hab (fun _ => ⟨by omega, by omega⟩) (fun _ => ⟨by omega, by omega⟩)]
  · have := i₁ z (a + 1) h; have := i₁ (b + 1) a; have := i₁ (b + 1) (a + 1); have := i₁ b a
    have := i₁ b (a + 1)
    rw [h, rejoin_of_ne (a := b) (v := a + 1) _ (by omega) (by omega), rejoin_of_eq_right _ rfl,
      e₂, rejoin_of_eq_right _ rfl,
      rejoin_splice_right hab (fun _ => ⟨by omega, by omega⟩) (fun _ => ⟨by omega, by omega⟩)]
  · have := i₁ z b h; have := i₁ (a + 1) b; have := i₁ (a + 1) (b + 1); have := i₁ a b
    have := i₁ a (b + 1)
    rw [h, rejoin_of_eq_left _ rfl, rejoin_of_ne (a := a) (v := b) _ (by omega) (by omega),
      rejoin_of_eq_left _ rfl, e₃,
      rejoin_splice_left hab (fun _ => ⟨by omega, by omega⟩) (fun _ => ⟨by omega, by omega⟩)]
  · have := i₁ z (b + 1) h; have := i₁ (a + 1) b; have := i₁ (a + 1) (b + 1); have := i₁ a b
    have := i₁ a (b + 1)
    rw [h, rejoin_of_eq_right _ rfl, rejoin_of_ne (a := a) (v := b + 1) _ (by omega) (by omega),
      rejoin_of_eq_right _ rfl, e₄,
      rejoin_splice_left hab (fun _ => ⟨by omega, by omega⟩) (fun _ => ⟨by omega, by omega⟩)]
  · rw [rejoin_of_ne _ h.2.2.1 h.2.2.2, rejoin_of_ne _ h.1 h.2.1, rejoin_of_ne _ h.1 h.2.1,
      rejoin_of_ne _ h.2.2.1 h.2.2.2]

/-! ### Circles -/

private theorem circleInd_erasePair {ψ : ℕ → ℕ} (hψ : ∀ z, ψ (ψ z) = z) {a b : ℕ}
    (hab : a + 1 < b) (hb : ψ b = b + 1) : circleInd a (erasePair b ψ) = circleInd a ψ := by
  have hb' : ψ (b + 1) = b := by rw [← hb, hψ]
  have hV : ψ a ≠ b ∧ ψ a ≠ b + 1 := ⟨fun h => by have := hψ a; rw [h, hb] at this; omega,
    fun h => by have := hψ a; rw [h, hb'] at this; omega⟩
  unfold circleInd
  rw [erasePair_apply, skipN_of_lt (by omega)]
  simp only [unskipN]
  split_ifs <;> omega

private theorem circleInd_erasePair_right {ψ : ℕ → ℕ} (hψ : ∀ z, ψ (ψ z) = z) {a b : ℕ}
    (hab : a ≤ b) (ha : ψ a = a + 1) : circleInd b (erasePair a ψ) = circleInd (b + 2) ψ := by
  have ha' : ψ (a + 1) = a := by rw [← ha, hψ]
  have : ψ (b + 2) ≠ a ∧ ψ (b + 2) ≠ a + 1 :=
    ⟨fun h => by have := hψ (b + 2); rw [h, ha] at this; omega,
      fun h => by have := hψ (b + 2); rw [h, ha'] at this; omega⟩
  unfold circleInd
  rw [erasePair_apply, skipN_of_le (by omega)]
  simp only [unskipN]
  split_ifs <;> omega

private theorem circleInd_splice {φ : ℕ → ℕ} (hφ : ∀ z, φ (φ z) = z) {a b : ℕ} (hab : a + 1 < b) :
    circleInd b φ + circleInd a (splice b φ) = circleInd a φ + circleInd b (splice a φ) := by
  have i₁ : ∀ u v, φ u = v → φ v = u := fun u v h => by rw [← h, hφ]
  unfold circleInd
  rw [splice_of_ne _ (by omega) (by omega), splice_of_ne _ (by omega) (by omega)]
  have := i₁ a (a + 1); have := i₁ a b; have := i₁ a (b + 1); have := i₁ (a + 1) b
  have := i₁ (a + 1) (b + 1); have := i₁ b (b + 1); have := i₁ (b + 1) a
  have := i₁ (b + 1) (a + 1); have := i₁ b a; have := i₁ b (a + 1)
  unfold rejoin
  split_ifs <;> omega

/-! ### Partner functions of planar matchings -/

private theorem pv_of_le {K : ℕ} (x : PlanarMatching K) {u : ℕ} (h : K ≤ u) : pv x u = u := by
  simp [pv, Nat.not_lt.mpr h]

private theorem pv_pv_eq {K : ℕ} (x : PlanarMatching K) (u : ℕ) : pv x (pv x u) = u := by
  by_cases hu : u < K
  · exact pv_pv x hu
  · rw [pv_of_le x (u := u) (by omega), pv_of_le x (u := u) (by omega)]

private theorem pv_cast_eq {K K' : ℕ} (h : K = K') (x : PlanarMatching K) :
    pv (cast h x) = pv x :=
  funext (pv_cast h x)

private theorem eq_of_pv_eq {K : ℕ} {x y : PlanarMatching K} (h : pv x = pv y) : x = y :=
  ext_pv fun q _ => congrFun h q

private theorem pv_contract_eq {k : ℕ} (x : PlanarMatching (k + 2)) (a : Fin (k + 1)) :
    pv (x.contract a) = contractFn a (pv x) := by
  funext q
  have ha := a.isLt
  have hs : skipN a q ≠ a ∧ skipN a q ≠ a + 1 := by simp only [skipN]; split_ifs <;> omega
  rw [contractFn, erasePair_apply, splice_of_ne _ hs.1 hs.2]
  by_cases hq : q < k
  · rw [pv_contract x a hq, joinN, rejoin]
  · rw [pv_of_le _ (by omega), skipN_of_le (by omega), pv_of_le _ (by omega),
      rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
    omega

private theorem exists_pv_eq_contractFn {K : ℕ} (x : PlanarMatching K) {a : ℕ} (ha : a + 1 < K) :
    ∃ y : PlanarMatching (K - 2), pv y = contractFn a (pv x) := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
  exact ⟨cast (by omega) (x.contract ⟨a, by omega⟩), by rw [pv_cast_eq, pv_contract_eq]⟩

private theorem pv_append_eq {k l : ℕ} (x : PlanarMatching k) (y : PlanarMatching l) :
    pv (x.append y) = appendFn k l (pv x) (pv y) := by
  funext q
  by_cases h₁ : q < k
  · rw [pv_append_left x y h₁, appendFn_of_lt _ _ h₁]
  by_cases h₂ : q < k + l
  · rw [pv_append_right x y (by omega) h₂, appendFn_of_le_of_lt _ _ (by omega) h₂]
  · rw [pv_of_le _ (by omega), appendFn_of_le _ _ (by omega)]

private theorem pv_glueMiddle {n p : ℕ} :
    ∀ (m : ℕ) (x : PlanarMatching (n + m + (m + p))), pv (glueMiddle m x) = glueFn n m (pv x)
  | 0, x => by rw [glueMiddle_zero, pv_cast_eq, glueFn]
  | m + 1, x => by rw [glueMiddle_succ, pv_glueMiddle m, pv_contract_eq, pv_cast_eq, glueFn]

private theorem glueMiddleCircles_eq {n p : ℕ} :
    ∀ (m : ℕ) (x : PlanarMatching (n + m + (m + p))),
      glueMiddleCircles m x = glueCircles n m (pv x)
  | 0, x => rfl
  | m + 1, x => by
    rw [glueMiddleCircles_succ, glueMiddleCircles_eq m, pv_contract_eq, pv_cast_eq]
    simp only [glueCircles, circleInd, Fin.ext_iff, ← pv_coe, pv_cast]

/-! ### Contractions commute -/

private theorem contractFn_contractFn {K : ℕ} (x : PlanarMatching K) {a b : ℕ} (hab : a ≤ b)
    (hb : b + 3 < K) :
    contractFn a (contractFn (b + 2) (pv x)) = contractFn b (contractFn a (pv x)) := by
  have hφ := pv_pv_eq x
  have h₁ : pv x a ≠ a := pv_ne x (by omega)
  have h₂ : pv x (a + 1) ≠ a + 1 := pv_ne x (by omega)
  have h₃ : pv x (b + 2) ≠ b + 2 := pv_ne x (by omega)
  have h₄ : pv x (b + 2 + 1) ≠ b + 2 + 1 := pv_ne x (by omega)
  have hb₁ := splice_involutive hφ h₃ h₄
  have ha₁ := splice_involutive hφ h₁ h₂
  have hab₁ := splice_involutive hb₁ (splice_ne_self hφ (by omega) (by omega) h₁)
    (splice_ne_self hφ (by omega) (by omega) h₂)
  unfold contractFn
  rw [splice_erasePair hb₁ (by omega) (splice_of_eq_left _ rfl),
    erasePair_erasePair hab₁ hab (splice_of_eq_left _ rfl)
      (by rw [splice_of_ne _ (by omega) (by omega), splice_of_eq_left _ rfl,
        rejoin_of_ne _ (by omega) (by omega)]),
    splice_splice hφ (by omega), splice_erasePair_right ha₁ hab (splice_of_eq_left _ rfl)]

private theorem circleInd_contractFn {K : ℕ} (x : PlanarMatching K) {a b : ℕ} (hab : a ≤ b)
    (hb : b + 3 < K) :
    circleInd (b + 2) (pv x) + circleInd a (contractFn (b + 2) (pv x)) =
      circleInd a (pv x) + circleInd b (contractFn a (pv x)) := by
  have hφ := pv_pv_eq x
  have hb₁ := splice_involutive hφ (pv_ne x (by omega : b + 2 < K))
    (pv_ne x (by omega : b + 2 + 1 < K))
  have ha₁ := splice_involutive hφ (pv_ne x (by omega : a < K)) (pv_ne x (by omega : a + 1 < K))
  unfold contractFn
  rw [circleInd_erasePair hb₁ (by omega) (splice_of_eq_left _ rfl),
    circleInd_erasePair_right ha₁ hab (splice_of_eq_left _ rfl)]
  exact circleInd_splice hφ (by omega)

/-! ### Gluing along two disjoint blocks -/

private theorem contractFn_glueFn {a : ℕ} :
    ∀ (j c K : ℕ) (x : PlanarMatching K), a ≤ c → c + 2 + 2 * j ≤ K →
      contractFn a (glueFn (c + 2) j (pv x)) = glueFn c j (contractFn a (pv x)) ∧
      circleInd a (glueFn (c + 2) j (pv x)) + glueCircles (c + 2) j (pv x) =
        glueCircles c j (contractFn a (pv x)) + circleInd a (pv x)
  | 0, c, K, x, _, _ => ⟨rfl, by simp [glueFn, glueCircles]⟩
  | j + 1, c, K, x, hac, hK => by
    obtain ⟨y, hy⟩ := exists_pv_eq_contractFn x (a := c + 2 + j) (by omega)
    obtain ⟨ih₁, ih₂⟩ := contractFn_glueFn j c (K - 2) y hac (by omega)
    have hc : c + 2 + j = c + j + 2 := by omega
    have e₁ : contractFn a (pv y) = contractFn (c + j) (contractFn a (pv x)) := by
      rw [hy, hc, contractFn_contractFn x (by omega) (by omega)]
    have e₂ := circleInd_contractFn x (a := a) (b := c + j) (by omega) (by omega)
    rw [← hc, ← hy] at e₂
    simp only [glueFn, glueCircles]
    rw [← hy, ih₁, e₁]
    refine ⟨rfl, ?_⟩
    rw [← e₁]
    omega

private theorem glueFn_glueFn {n j : ℕ} :
    ∀ (m d K : ℕ) (x : PlanarMatching K), n + 2 * m + d + 2 * j ≤ K →
      glueFn n m (glueFn (n + 2 * m + d) j (pv x)) = glueFn (n + d) j (glueFn n m (pv x)) ∧
      glueCircles n m (glueFn (n + 2 * m + d) j (pv x)) + glueCircles (n + 2 * m + d) j (pv x) =
        glueCircles (n + d) j (glueFn n m (pv x)) + glueCircles n m (pv x)
  | 0, d, K, x, _ => ⟨by simp [glueFn], by simp [glueFn, glueCircles]⟩
  | m + 1, d, K, x, hK => by
    obtain ⟨y, hy⟩ := exists_pv_eq_contractFn x (a := n + m) (by omega)
    obtain ⟨h₁, h₂⟩ := contractFn_glueFn (a := n + m) j (n + 2 * m + d) K x (by omega)
      (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueFn_glueFn (n := n) (j := j) m d (K - 2) y (by omega)
    have hm : n + 2 * m + d + 2 = n + 2 * (m + 1) + d := by omega
    rw [hm, ← hy] at h₁ h₂
    simp only [glueFn, glueCircles]
    rw [h₁, ← hy, ih₁]
    refine ⟨rfl, ?_⟩
    omega

/-! ### Gluing inside one factor of a juxtaposition -/

private theorem contractFn_appendFn_left {k l : ℕ} (x : PlanarMatching k) (y : PlanarMatching l)
    {a : ℕ} (ha : a + 1 < k) :
    contractFn a (appendFn k l (pv x) (pv y)) =
      appendFn (k - 2) l (contractFn a (pv x)) (pv y) := by
  funext q
  have hs : skipN a q ≠ a ∧ skipN a q ≠ a + 1 := by simp only [skipN]; split_ifs <;> omega
  simp only [contractFn, erasePair_apply, splice_of_ne _ hs.1 hs.2]
  have e₁ : appendFn k l (pv x) (pv y) a = pv x a := appendFn_of_lt _ _ (by omega)
  have e₂ : appendFn k l (pv x) (pv y) (a + 1) = pv x (a + 1) := appendFn_of_lt _ _ (by omega)
  by_cases h₁ : q < k - 2
  · rw [appendFn_of_lt _ _ h₁, appendFn_of_lt _ _ (by simp only [skipN]; split_ifs <;> omega)]
    rw [erasePair_apply, splice_of_ne _ hs.1 hs.2]
    unfold rejoin
    rw [e₁, e₂]
  have hs' : skipN a q = q + 2 := skipN_of_le (by omega)
  rw [hs']
  by_cases h₂ : q < k - 2 + l
  · have hq : q + 2 - k < l := by omega
    have hq' : q - (k - 2) = q + 2 - k := by omega
    have := pv_lt y hq
    rw [appendFn_of_le_of_lt _ _ (by omega) h₂, appendFn_of_le_of_lt _ _ (by omega) (by omega),
      rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega), hq']
    omega
  · rw [appendFn_of_le _ _ (by omega), appendFn_of_le _ _ (by omega),
      rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
    omega

private theorem splice_ne {ψ : ℕ → ℕ} (hψ : ∀ z, ψ (ψ z) = z) {a z : ℕ} (h₁ : ψ a ≠ a)
    (h₂ : ψ (a + 1) ≠ a + 1) (hz : z ≠ a) (hz' : z ≠ a + 1) :
    splice a ψ z ≠ a ∧ splice a ψ z ≠ a + 1 := by
  have h := splice_involutive hψ h₁ h₂ z
  refine ⟨fun h' => hz' ?_, fun h' => hz ?_⟩
  · rw [← h, h', splice_of_eq_left _ rfl]
  · rw [← h, h', splice_of_eq_right _ rfl]

private theorem splice_appendFn_right {k l : ℕ} (φ : ℕ → ℕ) (y : PlanarMatching l) {a z : ℕ}
    (ha : a + 1 < l) (hz : z < l) :
    splice (k + a) (appendFn k l φ (pv y)) (k + z) = k + splice a (pv y) z := by
  by_cases hza : z = a
  · rw [splice_of_eq_left _ (by omega), splice_of_eq_left _ hza, Nat.add_assoc]
  by_cases hza' : z = a + 1
  · rw [splice_of_eq_right _ (by omega), splice_of_eq_right _ hza']
  have e₀ : appendFn k l φ (pv y) (k + z) = k + pv y z := by
    rw [appendFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel_left]
  have e₁ : appendFn k l φ (pv y) (k + a) = k + pv y a := by
    rw [appendFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel_left]
  have e₂ : appendFn k l φ (pv y) (k + a + 1) = k + pv y (a + 1) := by
    rw [appendFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_assoc, Nat.add_sub_cancel_left]
  rw [splice_of_ne _ (by omega) (by omega), splice_of_ne _ hza hza', e₀]
  unfold rejoin
  rw [e₁, e₂]
  split_ifs <;> omega

private theorem contractFn_appendFn_right {k l : ℕ} (x : PlanarMatching k) (y : PlanarMatching l)
    {a : ℕ} (ha : a + 1 < l) :
    contractFn (k + a) (appendFn k l (pv x) (pv y)) =
      appendFn k (l - 2) (pv x) (contractFn a (pv y)) := by
  funext q
  simp only [contractFn, erasePair_apply]
  by_cases h₁ : q < k
  · have := pv_lt x h₁
    rw [skipN_of_lt (by omega), appendFn_of_lt _ _ h₁, splice_of_ne _ (by omega) (by omega),
      appendFn_of_lt _ _ h₁, rejoin_of_ne _ (by omega) (by omega), unskipN_of_lt (by omega)]
  by_cases h₂ : q < k + (l - 2)
  · have hsk : skipN (k + a) q = k + skipN a (q - k) := by simp only [skipN]; split_ifs <;> omega
    have hs₁ : skipN a (q - k) < l := by simp only [skipN]; split_ifs <;> omega
    have hs₂ : skipN a (q - k) ≠ a ∧ skipN a (q - k) ≠ a + 1 := by
      simp only [skipN]; split_ifs <;> omega
    have hw := splice_ne (pv_pv_eq y) (pv_ne y (by omega : a < l)) (pv_ne y (by omega : a + 1 < l))
      hs₂.1 hs₂.2
    rw [hsk, splice_appendFn_right _ _ ha hs₁, appendFn_of_le_of_lt _ _ (by omega) h₂,
      erasePair_apply]
    generalize splice a (pv y) (skipN a (q - k)) = w at hw
    simp only [unskipN]
    split_ifs <;> omega
  · have hs : skipN (k + a) q = q + 2 := skipN_of_le (by omega)
    rw [hs, splice_of_ne _ (by omega) (by omega), appendFn_of_le _ _ (by omega),
      appendFn_of_le _ _ (by omega), rejoin_of_ne _ (by omega) (by omega),
      unskipN_of_le (by omega)]
    omega

private theorem circleInd_appendFn_left {k l : ℕ} (φ ψ : ℕ → ℕ) {a : ℕ} (ha : a + 1 < k) :
    circleInd a (appendFn k l φ ψ) = circleInd a φ := by
  rw [circleInd, appendFn_of_lt _ _ (by omega), circleInd]

private theorem circleInd_appendFn_right {k l : ℕ} (φ ψ : ℕ → ℕ) {a : ℕ} (ha : a + 1 < l) :
    circleInd (k + a) (appendFn k l φ ψ) = circleInd a ψ := by
  rw [circleInd, appendFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel_left,
    circleInd]
  simp only [Nat.add_assoc, Nat.add_left_cancel_iff]

private theorem appendFn_assoc (k l r : ℕ) (φ ψ χ : ℕ → ℕ) :
    appendFn (k + l) r (appendFn k l φ ψ) χ = appendFn k (l + r) φ (appendFn l r ψ χ) := by
  funext q
  simp only [appendFn, Nat.sub_sub]
  split_ifs <;> omega

private theorem glueFn_appendFn_left {n r : ℕ} (z : PlanarMatching r) :
    ∀ (m K : ℕ) (x : PlanarMatching K), n + 2 * m ≤ K →
      appendFn (K - 2 * m) r (glueFn n m (pv x)) (pv z) =
        glueFn n m (appendFn K r (pv x) (pv z)) ∧
      glueCircles n m (appendFn K r (pv x) (pv z)) = glueCircles n m (pv x)
  | 0, K, x, _ => ⟨rfl, rfl⟩
  | m + 1, K, x, hK => by
    obtain ⟨y, hy⟩ := exists_pv_eq_contractFn x (a := n + m) (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueFn_appendFn_left (n := n) z m (K - 2) y (by omega)
    have hK' : K - 2 - 2 * m = K - 2 * (m + 1) := by omega
    simp only [glueFn, glueCircles]
    rw [contractFn_appendFn_left x z (by omega), ← hy, ← ih₁, ih₂,
      circleInd_appendFn_left _ _ (by omega), hK']
    exact ⟨rfl, rfl⟩

private theorem glueFn_appendFn_right {k n : ℕ} (w : PlanarMatching k) :
    ∀ (m K : ℕ) (x : PlanarMatching K), n + 2 * m ≤ K →
      appendFn k (K - 2 * m) (pv w) (glueFn n m (pv x)) =
        glueFn (k + n) m (appendFn k K (pv w) (pv x)) ∧
      glueCircles (k + n) m (appendFn k K (pv w) (pv x)) = glueCircles n m (pv x)
  | 0, K, x, _ => ⟨rfl, rfl⟩
  | m + 1, K, x, hK => by
    obtain ⟨y, hy⟩ := exists_pv_eq_contractFn x (a := n + m) (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueFn_appendFn_right (n := n) w m (K - 2) y (by omega)
    have hK' : K - 2 - 2 * m = K - 2 * (m + 1) := by omega
    simp only [glueFn, glueCircles]
    rw [Nat.add_assoc k n m, contractFn_appendFn_right w x (by omega), ← hy, ← ih₁, ih₂,
      circleInd_appendFn_right _ _ (by omega), hK']
    exact ⟨rfl, rfl⟩

end PlanarMatching

namespace TLDiagram

variable {n m p q : ℕ}

open PlanarMatching in
/-- **Associativity of composition** of Temperley–Lieb diagrams: gluing three diagrams along their
two middle boundaries gives the same matching and the same number of circles in either order. -/
theorem comp_assoc (f : TLDiagram n m) (g : TLDiagram m p) (h : TLDiagram p q) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  have hL := glueFn_appendFn_left (n := n) h.matching m (n + m + (m + p))
    (f.matching.append g.matching) (by omega)
  have hR := glueFn_appendFn_right (n := m) f.matching p (m + p + (p + q))
    (g.matching.append h.matching) (by omega)
  have hG := glueFn_glueFn (n := n) (j := p) m 0 (n + m + (m + p + (p + q)))
    (f.matching.append (g.matching.append h.matching)) (by omega)
  have e₁ : n + m + (m + p) - 2 * m = n + p := by omega
  have e₂ : m + p + (p + q) - 2 * p = m + q := by omega
  have e₃ : n + m + m = n + 2 * m := by omega
  rw [e₁, pv_append_eq] at hL
  rw [e₂, pv_append_eq, ← appendFn_assoc, e₃] at hR
  rw [pv_append_eq, pv_append_eq, ← appendFn_assoc] at hG
  simp only [Nat.add_zero] at hG
  ext : 1
  · apply eq_of_pv_eq
    simp only [matching_comp, pv_glueMiddle, pv_append_eq]
    rw [hL.1, hR.1, hG.1]
  · simp only [circles_comp, matching_comp, glueMiddleCircles_eq, pv_glueMiddle, pv_append_eq]
    rw [hL.1, hR.1, ← hL.2, ← hR.2]
    omega

end TLDiagram

end TauCeti
