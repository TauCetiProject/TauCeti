/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.List.Swap
public import TauCeti.GroupTheory.SpecificGroups.Braid.Word
public import TauCeti.KnotTheory.Signature
public import TauCeti.KnotTheory.TristramLevine.Basic

/-!
# The Seifert matrix of a closed braid

Seifert's algorithm applied to the closure of a braid word `w = σ_{i₁}^{ε₁} ⋯ σ_{iₖ}^{εₖ}` on `n`
strands produces a canonical Seifert surface: `n` parallel discs `D₀, …, D_{n-1}` stacked along the
braid axis, one for each strand position, and one half-twisted band for each letter, the `t`-th
letter `σ_i^ε` joining `Dᵢ` to `D_{i+1}` with a half twist of sign `ε`. The letters on a fixed
*level* `i` are its bands between `Dᵢ` and `D_{i+1}`; two consecutive ones, at positions `t < t'`
of the word with no letter of level `i` in between, span a loop `γ_{t,t'}` that runs up the band
`t`, along `D_{i+1}`, down the band `t'` and back along `Dᵢ`. These loops form a basis of the
first homology of the surface, and this file records the Seifert matrix
`V(γ, γ') = lk(γ, γ'⁺)` in that basis, with `γ'⁺` the push-off of `γ'` along the positive normal of
the surface (the boundary orientation of every disc agreeing with the orientation of the braid).

Writing `γ = γ_{t₁,t₂}` and `γ' = γ_{s₁,s₂}`, the entries are as follows.

* On the diagonal, `V(γ, γ) = -ε` if both bands of `γ` have the same sign `ε`, and `0` otherwise:
  each half twist of sign `ε` contributes `-ε / 2`.
* For two loops on the same level sharing a band, `t₂ = s₁` with the shared band of sign `ε`:
  `V(γ, γ') = -1` and `V(γ', γ) = 0` if `ε = -1`, while `V(γ, γ') = 0` and `V(γ', γ) = 1` if
  `ε = 1`. In both cases `V(γ, γ') - V(γ', γ) = -1`: the two loops cross once inside the shared
  band.
* For `γ` one level above `γ'`, `V(γ, γ')` is `-1` if `s₁ < t₁ < s₂ < t₂`, `1` if
  `t₁ < s₁ < t₂ < s₂`, and `0` otherwise; the two loops cross on their common disc exactly when
  their bands interleave. In the other order the entry vanishes: `γ'` lies on or below the disc
  they share, and the push-off of `γ` lies above it.
* All other entries vanish.

Positions in the word are natural numbers and a loop is labelled by the pair `(t, t')` of its
positions, so that the operations below, which move letters around, act on loop labels by
renaming positions. The matrix is indexed by the finite set `TauCeti.BraidWord.seifertLoops w` of
these labels; for a braid closing up to a knot, every level is used and the surface has genus `g`,
so there are `2 * g` loops.

The normalisation is pinned by the two classical examples: `σ₁³` (the right-handed trefoil) gives
the transpose of `TauCeti.KnotTheory.trefoilSeifertMatrix`, so Alexander polynomial `t - 1 + t⁻¹`
and signature `-2`, and `σ₁ σ₂⁻¹ σ₁ σ₂⁻¹` (the figure-eight knot) gives a matrix congruent to
`TauCeti.KnotTheory.figureEightSeifertMatrix`, so Alexander polynomial `-t + 3 - t⁻¹` and signature
`0`.

Up to relabelling the loops, the Seifert matrix does not change when two letters on distant levels
are exchanged, nor under the Markov stabilization `w ↦ w σₙ^{±1}`, which adds one disc and one
band and no new loop.

The canonical surface is connected exactly when every level `0, …, n - 2` carries a letter, and
only then is the matrix a Seifert matrix of the closure in the sense of S-equivalence. If some
level carries no letter, the surface is disconnected and the matrix forgets the splitting: on two
strands, the empty word gives the `0 × 0` matrix while `σ₁ σ₁⁻¹` gives `[0]`, although both close
to the two-component unlink. Among words using every level, the remaining moves generating Markov
equivalence of braid words (cyclic rotation, the braid relation, and free cancellation that keeps
every level used) change the matrix only up to S-equivalence, as for any two Seifert matrices of
isotopic links; that is what makes its Alexander polynomial and Tristram–Levine signatures
invariants of the closure. Those comparisons are not made here.

## Main definitions

* `TauCeti.BraidWord.IsSeifertLoop`: a pair of positions holding consecutive letters of one level.
* `TauCeti.BraidWord.seifertLoops`: the finite set of these pairs, the basis loops of the canonical
  Seifert surface.
* `TauCeti.BraidWord.seifertMatrix`: the Seifert matrix of the closure in this basis.

## Main results

* `TauCeti.BraidWord.seifertMatrix_apply`: the entries of the Seifert matrix.
* `TauCeti.BraidWord.exists_seifertMatrix_append_cons_cons_comm`: exchanging adjacent letters on
  distant levels relabels the Seifert matrix.
* `TauCeti.BraidWord.exists_seifertMatrix_stabilize`: so does Markov stabilization.
* `TauCeti.BraidWord.alexander_seifertMatrix_trefoil` and
  `TauCeti.BraidWord.signature_seifertMatrix_trefoil`: the right-handed trefoil.
* `TauCeti.BraidWord.alexander_seifertMatrix_figureEight` and
  `TauCeti.BraidWord.signature_seifertMatrix_figureEight`: the figure-eight knot.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 2
  (Seifert's algorithm) and Chapter 6 (Seifert matrices).
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 2 (braids and links).
* H. Seifert, *Über das Geschlecht von Knoten*, Math. Ann. 110 (1935), 571–592.
-/

public section

namespace TauCeti

namespace BraidWord

open KnotTheory LaurentPolynomial

open scoped Matrix

variable {n m : ℕ}

section Defs

variable (w : BraidWord n)

/-- The pair of positions `p = (t, t')` labels a loop of the canonical Seifert surface: `t < t'`
are positions of the word holding letters of the same level, with no letter of that level in
between. The loop runs up the band `t` and down the band `t'`. -/
def IsSeifertLoop (p : ℕ × ℕ) : Prop :=
  p.1 < p.2 ∧ p.2 < w.length ∧ w.levelAt p.2 = w.levelAt p.1 ∧
    ∀ k < p.2, p.1 < k → w.levelAt k ≠ w.levelAt p.1

/-- The defining property of a loop label. -/
theorem isSeifertLoop_iff {p : ℕ × ℕ} :
    w.IsSeifertLoop p ↔ p.1 < p.2 ∧ p.2 < w.length ∧ w.levelAt p.2 = w.levelAt p.1 ∧
      ∀ k < p.2, p.1 < k → w.levelAt k ≠ w.levelAt p.1 :=
  Iff.rfl

instance : DecidablePred w.IsSeifertLoop := fun _ ↦ decidable_of_iff _ w.isSeifertLoop_iff.symm

/-- The labels of the basis loops of the first homology of the canonical Seifert surface of the
closure of `w`: the pairs of consecutive positions of letters on a common level. -/
def seifertLoops : Finset (ℕ × ℕ) :=
  (Finset.range w.length ×ˢ Finset.range w.length).filter w.IsSeifertLoop

@[simp]
theorem mem_seifertLoops {p : ℕ × ℕ} : p ∈ w.seifertLoops ↔ w.IsSeifertLoop p := by
  simp only [seifertLoops, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    and_iff_right_iff_imp]
  exact fun h ↦ ⟨h.1.trans h.2.1, h.2.1⟩

/-- The linking number `lk(γ_a, γ_b⁺)` of two loops of the canonical Seifert surface, labelled by
their pairs of positions. -/
private def seifertEntry (a b : ℕ × ℕ) : ℤ :=
  if a = b then
    if w.signAt a.1 = w.signAt a.2 then -w.signAt a.1 else 0
  else if w.levelAt a.1 = w.levelAt b.1 then
    if a.2 = b.1 then (if w.signAt a.2 = -1 then -1 else 0)
    else if b.2 = a.1 then (if w.signAt a.1 = 1 then 1 else 0)
    else 0
  else if w.levelAt a.1 = (w.levelAt b.1).map (· + 1) then
    if b.1 < a.1 ∧ a.1 < b.2 ∧ b.2 < a.2 then -1
    else if a.1 < b.1 ∧ b.1 < a.2 ∧ a.2 < b.2 then 1
    else 0
  else 0

/-- The **Seifert matrix of the closure of a braid word**, read off the canonical Seifert surface
of Seifert's algorithm in the basis of loops `TauCeti.BraidWord.seifertLoops w`. Its entry at a
pair of loops `(γ, γ')` is the linking number of `γ` with the positive push-off of `γ'`. -/
def seifertMatrix : Matrix w.seifertLoops w.seifertLoops ℤ :=
  Matrix.of fun a b ↦ seifertEntry w a b

/-- The entries of the Seifert matrix of a braid word. For loops `a = (t₁, t₂)` and
`b = (s₁, s₂)`: the diagonal records the signs of the two bands of `a`; loops on one level meet only
when they share a band; and a loop meets the loops one level below it when their bands
interleave. -/
theorem seifertMatrix_apply (a b : w.seifertLoops) :
    w.seifertMatrix a b =
      if a = b then
        if w.signAt a.1.1 = w.signAt a.1.2 then -w.signAt a.1.1 else 0
      else if w.levelAt a.1.1 = w.levelAt b.1.1 then
        if a.1.2 = b.1.1 then (if w.signAt a.1.2 = -1 then -1 else 0)
        else if b.1.2 = a.1.1 then (if w.signAt a.1.1 = 1 then 1 else 0)
        else 0
      else if w.levelAt a.1.1 = (w.levelAt b.1.1).map (· + 1) then
        if b.1.1 < a.1.1 ∧ a.1.1 < b.1.2 ∧ b.1.2 < a.1.2 then -1
        else if a.1.1 < b.1.1 ∧ b.1.1 < a.1.2 ∧ a.1.2 < b.1.2 then 1
        else 0
      else 0 := by
  rw [seifertMatrix, Matrix.of_apply, seifertEntry]
  exact if_congr Subtype.ext_iff.symm rfl rfl

/-- The diagonal entry at a loop whose two bands have the same sign `ε` is `-ε`. -/
@[simp]
theorem seifertMatrix_apply_self (a : w.seifertLoops) :
    w.seifertMatrix a a = if w.signAt a.1.1 = w.signAt a.1.2 then -w.signAt a.1.1 else 0 := by
  simp [seifertMatrix_apply]

/-- A loop has linking number zero with the push-off of a loop on the level above it. -/
theorem seifertMatrix_apply_eq_zero_of_levelAt_eq_map_succ {a b : w.seifertLoops}
    (h : w.levelAt b.1.1 = (w.levelAt a.1.1).map (· + 1)) : w.seifertMatrix a b = 0 := by
  have ha : w.levelAt a.1.1 ≠ none := (w.levelAt_ne_none_iff).2
    (((w.mem_seifertLoops).1 a.2).1.trans ((w.mem_seifertLoops).1 a.2).2.1)
  obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 ha
  rw [hl, Option.map_some] at h
  have hab : a ≠ b := by
    rintro rfl
    rw [hl, Option.some_inj] at h
    omega
  simp only [seifertMatrix_apply, hab, hl, h, ite_false, Option.some_inj, Option.map_some]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

end Defs

/-! ### Moving letters

The two lemmas below transport loops and entries along a renaming `e` of positions which keeps
every letter and the order of any two letters on equal or adjacent levels: these are the only
comparisons the definition makes. -/

section Transport

variable {w : BraidWord n} {w' : BraidWord m} (e : ℕ ≃ ℕ)
  (hlevel : ∀ k, w'.levelAt (e k) = w.levelAt k)
  (hlt : ∀ j k, j < w.length → k < w.length →
    (w.levelAt j = w.levelAt k ∨ w.levelAt j = (w.levelAt k).map (· + 1) ∨
      w.levelAt k = (w.levelAt j).map (· + 1)) → (e j < e k ↔ j < k))
include hlevel

private theorem lt_length_iff_of_levelAt (k : ℕ) : e k < w'.length ↔ k < w.length := by
  rw [← levelAt_ne_none_iff, ← levelAt_ne_none_iff, hlevel]

include hlt in
private theorem isSeifertLoop_map_iff (p : ℕ × ℕ) :
    w'.IsSeifertLoop (e p.1, e p.2) ↔ w.IsSeifertLoop p := by
  simp only [isSeifertLoop_iff, hlevel]
  constructor
  · rintro ⟨h12, h2, hl, hbetween⟩
    have h2' : p.2 < w.length := (lt_length_iff_of_levelAt e hlevel p.2).1 h2
    have h1' : p.1 < w.length := by
      rw [← levelAt_ne_none_iff, ← hl, levelAt_ne_none_iff]
      exact h2'
    refine ⟨(hlt _ _ h1' h2' (Or.inl hl.symm)).1 h12, h2', hl, fun k hk hk' heq ↦ ?_⟩
    have hk'' : k < w.length := hk.trans h2'
    exact hbetween (e k) ((hlt _ _ hk'' h2' (Or.inl (heq.trans hl.symm))).2 hk)
      ((hlt _ _ h1' hk'' (Or.inl heq.symm)).2 hk') (by rw [hlevel, heq])
  · rintro ⟨h12, h2, hl, hbetween⟩
    have h1 : p.1 < w.length := h12.trans h2
    refine ⟨(hlt _ _ h1 h2 (Or.inl hl.symm)).2 h12, (lt_length_iff_of_levelAt e hlevel _).2 h2,
      hl, fun k hk hk' heq ↦ ?_⟩
    obtain ⟨k, rfl⟩ := e.surjective k
    rw [hlevel] at heq
    have hk'' : k < w.length := by
      rw [← levelAt_ne_none_iff, heq, levelAt_ne_none_iff]
      exact h1
    exact hbetween k ((hlt _ _ hk'' h2 (Or.inl (heq.trans hl.symm))).1 hk)
      ((hlt _ _ h1 hk'' (Or.inl heq.symm)).1 hk') heq

include hlt in
private theorem seifertEntry_map (hsign : ∀ k, w'.signAt (e k) = w.signAt k) {a b : ℕ × ℕ}
    (ha : w.IsSeifertLoop a) (hb : w.IsSeifertLoop b) :
    seifertEntry w' (e a.1, e a.2) (e b.1, e b.2) = seifertEntry w a b := by
  obtain ⟨ha12, ha2, hal, -⟩ := ha
  obtain ⟨hb12, hb2, hbl, -⟩ := hb
  have ha1 := ha12.trans ha2
  have hb1 := hb12.trans hb2
  have hab : (e a.1, e a.2) = (e b.1, e b.2) ↔ a = b := by
    simp only [Prod.ext_iff, e.apply_eq_iff_eq]
  simp only [seifertEntry, hlevel, hsign, hab, e.apply_eq_iff_eq]
  by_cases h : w.levelAt a.1 = (w.levelAt b.1).map (· + 1)
  · -- every comparison made in this branch is between positions on adjacent levels
    have h₁ := hlt _ _ hb1 ha1 (Or.inr (Or.inr h))
    have h₂ := hlt _ _ ha1 hb2 (Or.inr (Or.inl (by rw [hbl]; exact h)))
    have h₃ := hlt _ _ hb2 ha2 (Or.inr (Or.inr (by rw [hbl, hal]; exact h)))
    have h₄ := hlt _ _ ha1 hb1 (Or.inr (Or.inl h))
    have h₅ := hlt _ _ hb1 ha2 (Or.inr (Or.inr (by rw [hal]; exact h)))
    have h₆ := hlt _ _ ha2 hb2 (Or.inr (Or.inl (by rw [hal, hbl]; exact h)))
    simp only [h₁, h₂, h₃, h₄, h₅, h₆]
  · simp only [h, ite_false]

include hlt in
/-- A renaming of positions which keeps every letter, and the order of any two letters on equal
or adjacent levels, relabels the Seifert matrix. -/
private theorem exists_seifertMatrix_eq_submatrix_of_equiv
    (hsign : ∀ k, w'.signAt (e k) = w.signAt k) :
    ∃ ι : w'.seifertLoops ≃ w.seifertLoops, w'.seifertMatrix = w.seifertMatrix.submatrix ι ι := by
  let κ : w.seifertLoops ≃ w'.seifertLoops := (e.prodCongr e).subtypeEquiv fun p ↦ by
    simp only [mem_seifertLoops, Equiv.prodCongr_apply, Prod.map,
      isSeifertLoop_map_iff e hlevel hlt]
  refine ⟨κ.symm, Matrix.ext fun a' b' ↦ ?_⟩
  obtain ⟨a, rfl⟩ := κ.surjective a'
  obtain ⟨b, rfl⟩ := κ.surjective b'
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, seifertMatrix, Matrix.of_apply]
  exact seifertEntry_map e hlevel hlt hsign ((w.mem_seifertLoops).1 a.2)
    ((w.mem_seifertLoops).1 b.2)

end Transport

section Commute

variable (u v : BraidWord n) {a b : Fin (n - 1) × ℤˣ}

/-- **Exchanging two adjacent letters on distant levels relabels the Seifert matrix.** The two
bands lie between disjoint pairs of discs, so exchanging them moves no loop across another. -/
theorem exists_seifertMatrix_append_cons_cons_comm
    (h : (a.1 : ℕ) + 2 ≤ b.1 ∨ (b.1 : ℕ) + 2 ≤ a.1) :
    ∃ ι : (u ++ b :: a :: v).seifertLoops ≃ (u ++ a :: b :: v).seifertLoops,
      (u ++ b :: a :: v).seifertMatrix = (u ++ a :: b :: v).seifertMatrix.submatrix ι ι := by
  have hget := List.getElem?_swap_append_cons_cons u v a b
  refine exists_seifertMatrix_eq_submatrix_of_equiv (Equiv.swap u.length (u.length + 1))
    (fun k ↦ by rw [levelAt, levelAt, hget]) (fun j k hj hk hjk ↦ ?_)
    (fun k ↦ by rw [signAt, signAt, hget])
  have hA : (u ++ a :: b :: v).levelAt u.length = some (a.1 : ℕ) := by simp [levelAt]
  have hB : (u ++ a :: b :: v).levelAt (u.length + 1) = some (b.1 : ℕ) := by simp [levelAt]
  have hjk' : ¬ (j = u.length ∧ k = u.length + 1) ∧ ¬ (j = u.length + 1 ∧ k = u.length) := by
    constructor <;> rintro ⟨rfl, rfl⟩ <;>
      simp only [hA, hB, Option.map_some, Option.some_inj] at hjk <;> omega
  simp only [Equiv.swap_apply_def]
  split_ifs <;> omega

end Commute

section Stabilize

variable (w : BraidWord (n + 1)) (ε : ℤˣ)

private theorem isSeifertLoop_stabilize_iff (p : ℕ × ℕ) :
    (w.stabilize ε).IsSeifertLoop p ↔ w.IsSeifertLoop p := by
  have key : ∀ q : ℕ × ℕ, q.2 < w.length →
      ((w.stabilize ε).IsSeifertLoop q ↔ w.IsSeifertLoop q) := by
    rintro ⟨q₁, q₂⟩ hq
    simp only [isSeifertLoop_iff, length_stabilize]
    constructor
    · rintro ⟨h12, -, hl, hbetween⟩
      refine ⟨h12, hq, ?_, fun k hk hk' ↦ ?_⟩
      · rwa [levelAt_stabilize_of_lt w ε hq, levelAt_stabilize_of_lt w ε (h12.trans hq)] at hl
      · have := hbetween k hk hk'
        rwa [levelAt_stabilize_of_lt w ε (hk.trans hq),
          levelAt_stabilize_of_lt w ε (h12.trans hq)] at this
    · rintro ⟨h12, -, hl, hbetween⟩
      refine ⟨h12, by omega, ?_, fun k hk hk' ↦ ?_⟩
      · rwa [levelAt_stabilize_of_lt w ε hq, levelAt_stabilize_of_lt w ε (h12.trans hq)]
      · rw [levelAt_stabilize_of_lt w ε (hk.trans hq), levelAt_stabilize_of_lt w ε (h12.trans hq)]
        exact hbetween k hk hk'
  rcases lt_or_ge p.2 w.length with hp | hp
  · exact key p hp
  refine iff_of_false (fun hl ↦ ?_) fun hl ↦ by have := hl.2.1; omega
  -- the last letter is the only one on the new top level, so it ends no loop
  obtain ⟨h12, h2, hl, -⟩ := hl
  rw [length_stabilize] at h2
  have hp2 : p.2 = w.length := by omega
  have h1 : p.1 < w.length := by omega
  rw [hp2, levelAt_stabilize_length, levelAt_stabilize_of_lt w ε h1, levelAt_of_lt _ h1,
    Option.some_inj] at hl
  have := (w[p.1]'h1).1.isLt
  omega

/-- **Markov stabilization relabels the Seifert matrix.** The new strand adds a disc and a single
band joining it to the surface, which creates no loop. -/
theorem exists_seifertMatrix_stabilize :
    ∃ ι : (w.stabilize ε).seifertLoops ≃ w.seifertLoops,
      (w.stabilize ε).seifertMatrix = w.seifertMatrix.submatrix ι ι := by
  have hloops : ∀ p, p ∈ (w.stabilize ε).seifertLoops ↔ p ∈ w.seifertLoops := fun p ↦ by
    simp only [mem_seifertLoops, isSeifertLoop_stabilize_iff]
  refine ⟨Equiv.subtypeEquivRight hloops, Matrix.ext fun a b ↦ ?_⟩
  obtain ⟨ha12, ha2, -, -⟩ := (w.mem_seifertLoops).1 ((hloops a).1 a.2)
  obtain ⟨hb12, hb2, -, -⟩ := (w.mem_seifertLoops).1 ((hloops b).1 b.2)
  simp only [Matrix.submatrix_apply, Equiv.subtypeEquivRight_apply_coe, seifertMatrix,
    Matrix.of_apply, seifertEntry, levelAt_stabilize_of_lt w ε (ha12.trans ha2),
    levelAt_stabilize_of_lt w ε (hb12.trans hb2), signAt_stabilize_of_lt w ε ha2,
    signAt_stabilize_of_lt w ε (ha12.trans ha2)]

end Stabilize

/-! ### Consequences for the invariants -/

section Invariants

variable {u v : BraidWord n} {a b : Fin (n - 1) × ℤˣ}

/-- Exchanging two adjacent letters on distant levels keeps the Alexander polynomial of the
Seifert matrix. -/
theorem alexander_seifertMatrix_append_cons_cons_comm
    (h : (a.1 : ℕ) + 2 ≤ b.1 ∨ (b.1 : ℕ) + 2 ≤ a.1) :
    alexander (u ++ b :: a :: v).seifertMatrix = alexander (u ++ a :: b :: v).seifertMatrix := by
  obtain ⟨ι, hι⟩ := exists_seifertMatrix_append_cons_cons_comm u v h
  rw [hι, Matrix.alexander_submatrix_equiv_self]

/-- Exchanging two adjacent letters on distant levels keeps the Tristram–Levine signatures of the
Seifert matrix. -/
theorem tristramLevineSignature_seifertMatrix_append_cons_cons_comm
    (h : (a.1 : ℕ) + 2 ≤ b.1 ∨ (b.1 : ℕ) + 2 ≤ a.1) (ω : ℂ) :
    tristramLevineSignature ((u ++ b :: a :: v).seifertMatrix.map ((↑) : ℤ → ℝ)) ω =
      tristramLevineSignature ((u ++ a :: b :: v).seifertMatrix.map ((↑) : ℤ → ℝ)) ω := by
  obtain ⟨ι, hι⟩ := exists_seifertMatrix_append_cons_cons_comm u v h
  rw [hι, ← Matrix.submatrix_map, ← ι.symm_symm, tristramLevineSignature_submatrix_equiv_self]

variable (w : BraidWord (n + 1)) (ε : ℤˣ)

/-- Markov stabilization keeps the Alexander polynomial of the Seifert matrix. -/
theorem alexander_seifertMatrix_stabilize :
    alexander (w.stabilize ε).seifertMatrix = alexander w.seifertMatrix := by
  obtain ⟨ι, hι⟩ := exists_seifertMatrix_stabilize w ε
  rw [hι, Matrix.alexander_submatrix_equiv_self]

/-- Markov stabilization keeps the Tristram–Levine signatures of the Seifert matrix. -/
theorem tristramLevineSignature_seifertMatrix_stabilize (ω : ℂ) :
    tristramLevineSignature ((w.stabilize ε).seifertMatrix.map ((↑) : ℤ → ℝ)) ω =
      tristramLevineSignature (w.seifertMatrix.map ((↑) : ℤ → ℝ)) ω := by
  obtain ⟨ι, hι⟩ := exists_seifertMatrix_stabilize w ε
  rw [hι, ← Matrix.submatrix_map, ← ι.symm_symm, tristramLevineSignature_submatrix_equiv_self]

end Invariants

/-! ### The trefoil and the figure-eight knot -/

section Examples

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The closure of `σ₁³` is the right-handed trefoil. Its canonical Seifert surface has the two
loops `(0, 1)` and `(1, 2)`, and in that basis its Seifert matrix is the transpose of
`TauCeti.KnotTheory.trefoilSeifertMatrix`. -/
theorem seifertMatrix_trefoil :
    ∃ e : Fin 2 ≃ seifertLoops (n := 2) [(0, 1), (0, 1), (0, 1)],
      (seifertMatrix (n := 2) [(0, 1), (0, 1), (0, 1)]).submatrix e e =
        trefoilSeifertMatrixᵀ := by
  have htrefoil : trefoilSeifertMatrix = !![-1, 1; 0, -1] := Matrix.ext trefoilSeifertMatrix_apply
  rw [htrefoil]
  exact ⟨Equiv.ofBijective ![⟨(0, 1), by decide⟩, ⟨(1, 2), by decide⟩] (by decide),
    by decide +kernel⟩

/-- The Seifert matrix of the braid `σ₁³` has the Alexander polynomial `t - 1 + t⁻¹` of the
trefoil. -/
theorem alexander_seifertMatrix_trefoil :
    alexander (seifertMatrix (n := 2) [(0, 1), (0, 1), (0, 1)]) = T 1 - 1 + T (-1) := by
  obtain ⟨e, he⟩ := seifertMatrix_trefoil
  rw [← Matrix.alexander_submatrix_equiv_self _ e, he, alexander_transpose,
    alexander_trefoilSeifertMatrix]

/-- The Seifert matrix of the braid `σ₁³` has the signature `-2` of the right-handed trefoil. -/
theorem signature_seifertMatrix_trefoil :
    Matrix.signature ((seifertMatrix (n := 2) [(0, 1), (0, 1), (0, 1)]).map ((↑) : ℤ → 𝕜)) =
      -2 := by
  obtain ⟨e, he⟩ := seifertMatrix_trefoil
  rw [← Matrix.signature_submatrix_equiv_self e.symm, e.symm_symm, Matrix.submatrix_map, he,
    Matrix.transpose_map, Matrix.signature_transpose, signature_trefoilSeifertMatrix]

/-- The closure of `σ₁ σ₂⁻¹ σ₁ σ₂⁻¹` is the figure-eight knot. Its canonical Seifert surface has
the loop `(1, 3)` on the upper level and `(0, 2)` on the lower one, and in that basis its Seifert
matrix is `!![1, -1; 0, -1]`, congruent to `TauCeti.KnotTheory.figureEightSeifertMatrix` by
reversing the second loop. -/
theorem seifertMatrix_figureEight :
    ∃ e : Fin 2 ≃ seifertLoops (n := 3) [(0, 1), (1, -1), (0, 1), (1, -1)],
      (seifertMatrix (n := 3) [(0, 1), (1, -1), (0, 1), (1, -1)]).submatrix e e =
        !![1, -1; 0, -1] :=
  ⟨Equiv.ofBijective ![⟨(1, 3), by decide⟩, ⟨(0, 2), by decide⟩] (by decide), by decide +kernel⟩

/-- The Seifert matrix of the braid `σ₁ σ₂⁻¹ σ₁ σ₂⁻¹` has the Alexander polynomial
`-t + 3 - t⁻¹` of the figure-eight knot. -/
theorem alexander_seifertMatrix_figureEight :
    alexander (seifertMatrix (n := 3) [(0, 1), (1, -1), (0, 1), (1, -1)]) =
      -T 1 + 3 - T (-1) := by
  obtain ⟨e, he⟩ := seifertMatrix_figureEight
  have hP : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ).det ^ 2 = 1 := by decide
  have hcongr : !![1, 0; 0, -1] * !![1, -1; 0, -1] * (!![1, 0; 0, -1])ᵀ =
      figureEightSeifertMatrix := by
    have hfigureEight : figureEightSeifertMatrix = !![1, 1; 0, -1] :=
      Matrix.ext figureEightSeifertMatrix_apply
    rw [hfigureEight]
    decide +kernel
  rw [← Matrix.alexander_submatrix_equiv_self _ e, he,
    ← alexander_congruence_of_det_sq_eq_one _ hP, hcongr, alexander_figureEightSeifertMatrix]

/-- The Seifert matrix of the braid `σ₁ σ₂⁻¹ σ₁ σ₂⁻¹` has the signature `0` of the figure-eight
knot. -/
theorem signature_seifertMatrix_figureEight :
    Matrix.signature
      ((seifertMatrix (n := 3) [(0, 1), (1, -1), (0, 1), (1, -1)]).map ((↑) : ℤ → 𝕜)) =
      0 := by
  obtain ⟨e, he⟩ := seifertMatrix_figureEight
  have hP : IsUnit (!![(1 : 𝕜), 0; 0, -1]).det := by
    rw [Matrix.det_fin_two_of, isUnit_iff_ne_zero]
    norm_num
  have hmap : (!![1, -1; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → 𝕜) =
      !![1, -1; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hcongr : !![(1 : 𝕜), 0; 0, -1] * !![1, -1; 0, -1] * (!![(1 : 𝕜), 0; 0, -1])ᵀ =
      figureEightSeifertMatrix.map ((↑) : ℤ → 𝕜) := by
    rw [map_figureEightSeifertMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  rw [← Matrix.signature_submatrix_equiv_self e.symm, e.symm_symm, Matrix.submatrix_map, he,
    hmap, ← Matrix.signature_congr hP, hcongr, signature_figureEightSeifertMatrix]

end Examples

end BraidWord

end TauCeti
