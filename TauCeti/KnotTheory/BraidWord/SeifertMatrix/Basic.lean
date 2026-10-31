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

Cyclic rotation `x :: v ↦ v ++ [x]` cuts the same closed braid at another place, so the surface is
the same, but the basis of loops changes on the level `l` of `x`: the loop through the first two
letters of level `l` is replaced by the loop through the last letter of level `l` and the moved
letter. The loops of level `l` around the braid axis sum to zero in the homology of the surface, so
the new loop is minus the sum of the old ones, and the Seifert matrix changes by the corresponding
unimodular congruence `V ↦ P V Pᵀ`. To check this from the entries above, note that for a fixed
loop `b` the entries `V(c, b)` and `V(b, c)`, as `c` runs over the loops of level `l`, are
differences `f c.2 - f c.1` of an explicit function of positions, so their sum over `c` telescopes
along the letters of level `l`.

The canonical surface is connected exactly when every level `0, …, n - 2` carries a letter, and
only then is the matrix a Seifert matrix of the closure in the sense of S-equivalence. If some
level carries no letter, the surface is disconnected and the matrix forgets the splitting: on two
strands, the empty word gives the `0 × 0` matrix while `σ₁ σ₁⁻¹` gives `[0]`, although both close
to the two-component unlink. Among words using every level, the remaining moves generating Markov
equivalence of braid words (the braid relation, and free cancellation that keeps every level used)
change the matrix only up to S-equivalence, as for any two Seifert matrices of isotopic links; that
is what makes its Alexander polynomial an invariant of the closure. The Tristram–Levine signatures
need no condition on the levels: free cancellation on an unused level only adds a zero row and
column, so for every word they are invariant under Markov equivalence
(`TauCeti.MarkovEquiv.tristramLevineSignature_eq` in `TauCeti.KnotTheory.Markov.TristramLevine`).
Those comparisons are not made here.

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
* `TauCeti.BraidWord.exists_seifertMatrix_append_singleton`: moving the first letter to the end
  changes the Seifert matrix by a unimodular congruence.
* `TauCeti.BraidWord.alexander_seifertMatrix_rotate` and
  `TauCeti.BraidWord.tristramLevineSignature_seifertMatrix_rotate`: so cyclic rotation of the word
  keeps the Alexander polynomial and the Tristram–Levine signatures of the Seifert matrix.
* `TauCeti.BraidWord.alexander_seifertMatrix_trefoil` and
  `TauCeti.BraidWord.signature_seifertMatrix_trefoil`: the right-handed trefoil.
* `TauCeti.BraidWord.signature_seifertMatrix_mirrorTrefoil`: the left-handed trefoil.
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

/-- A loop is determined by its first band. -/
theorem IsSeifertLoop.eq_of_fst_eq {w : BraidWord n} {p q : ℕ × ℕ} (hp : w.IsSeifertLoop p)
    (hq : w.IsSeifertLoop q) (h : p.1 = q.1) : p = q := by
  obtain ⟨hp12, -, hpl, hp⟩ := hp
  obtain ⟨hq12, -, hql, hq⟩ := hq
  refine Prod.ext h ?_
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact hq p.2 hlt (h ▸ hp12) (by rw [hpl, h])
  · exact hp q.2 hlt (h ▸ hq12) (by rw [hql, h])

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
    (fun k ↦ by rw [levelAt_def, levelAt_def, hget]) (fun j k hj hk hjk ↦ ?_)
    (fun k ↦ by rw [signAt_def, signAt_def, hget])
  have hA : (u ++ a :: b :: v).levelAt u.length = some (a.1 : ℕ) := by simp
  have hB : (u ++ a :: b :: v).levelAt (u.length + 1) = some (b.1 : ℕ) := by simp
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

/-! ### Telescoping along a level

Seen from a fixed loop `b`, the entries `V(c, b)` and `V(b, c)` as `c` runs over the loops of
one level are differences `f c.2 - f c.1` of a function `f` of positions, so their sum telescopes
along the letters of that level. This is what makes the Seifert matrix compatible with replacing a
loop by minus the sum of all the others on its level, as cyclic rotation of the word does. -/

section Telescope

variable {w : BraidWord n}

/-- A loop is determined by its second band. -/
private theorem IsSeifertLoop.eq_of_snd_eq {p q : ℕ × ℕ} (hp : w.IsSeifertLoop p)
    (hq : w.IsSeifertLoop q) (h : p.2 = q.2) : p = q := by
  obtain ⟨hp12, -, hpl, hp⟩ := hp
  obtain ⟨hq12, -, hql, hq⟩ := hq
  refine Prod.ext ?_ h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact hp q.1 (h ▸ hq12) hlt (by rw [← hql, ← hpl, h])
  · exact hq p.1 (h ▸ hp12) hlt (by rw [← hpl, ← hql, h])

/-- **Telescoping along a level.** If `p₀` and `p₁` are the first and the last positions of the
letters of level `l`, then summing `f c.2 - f c.1` over the loops `c` of that level gives
`f p₁ - f p₀`: the second bands of these loops are the letters of level `l` other than the first,
and their first bands are those other than the last. -/
private theorem sum_seifertLoops_levelAt_sub {l p₀ p₁ : ℕ} (h₀ : w.levelAt p₀ = some l)
    (h₀' : ∀ k < p₀, w.levelAt k ≠ some l) (h₁ : w.levelAt p₁ = some l)
    (h₁' : ∀ k, p₁ < k → w.levelAt k ≠ some l) (f : ℕ → ℤ) :
    ∑ c ∈ w.seifertLoops with w.levelAt c.1 = some l, (f c.2 - f c.1) = f p₁ - f p₀ := by
  set P := (Finset.range w.length).filter fun k ↦ w.levelAt k = some l
  have hP : ∀ k, k ∈ P ↔ w.levelAt k = some l := fun k ↦ by
    simp only [P, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    exact fun h ↦ (levelAt_ne_none_iff w).1 (by simp [h])
  have hle₀ : ∀ k, w.levelAt k = some l → p₀ ≤ k := fun k hk ↦ not_lt.1 fun h ↦ h₀' k h hk
  have hle₁ : ∀ k, w.levelAt k = some l → k ≤ p₁ := fun k hk ↦ not_lt.1 fun h ↦ h₁' k h hk
  have hmem : ∀ c, c ∈ w.seifertLoops.filter (fun c ↦ w.levelAt c.1 = some l) ↔
      w.IsSeifertLoop c ∧ w.levelAt c.1 = some l := fun c ↦ by
    simp only [Finset.mem_filter, mem_seifertLoops]
  have hsnd : ∑ c ∈ w.seifertLoops with w.levelAt c.1 = some l, f c.2 = ∑ k ∈ P.erase p₀, f k := by
    refine Finset.sum_nbij (·.2) (fun c hc ↦ ?_) (fun c hc d hd h ↦ ?_) (fun k hk ↦ ?_)
      (fun _ _ ↦ rfl)
    · obtain ⟨⟨h12, -, hcl, -⟩, hl⟩ := (hmem c).1 hc
      refine Finset.mem_erase.2 ⟨fun h ↦ ?_, (hP _).2 (hcl.trans hl)⟩
      have := hle₀ _ hl
      omega
    · exact ((hmem c).1 hc).1.eq_of_snd_eq ((hmem d).1 hd).1 h
    · obtain ⟨hk0, hk⟩ := Finset.mem_erase.1 (Finset.mem_coe.1 hk)
      have hkl := (hP k).1 hk
      have hlt : p₀ < k := lt_of_le_of_ne (hle₀ k hkl) (Ne.symm hk0)
      -- the letter of level `l` just before `k`
      set q := Nat.findGreatest (fun j ↦ j < k ∧ w.levelAt j = some l) k
      have hq : q < k ∧ w.levelAt q = some l :=
        Nat.findGreatest_spec (P := fun j ↦ j < k ∧ w.levelAt j = some l) hlt.le ⟨hlt, h₀⟩
      refine ⟨(q, k), (hmem _).2 ⟨⟨hq.1, (levelAt_ne_none_iff w).1 (by simp [hkl]),
        hkl.trans hq.2.symm, fun j hj hj' hjl ↦ ?_⟩, hq.2⟩, rfl⟩
      exact Nat.findGreatest_is_greatest hj' hj.le ⟨hj, hjl.trans hq.2⟩
  have hfst : ∑ c ∈ w.seifertLoops with w.levelAt c.1 = some l, f c.1 = ∑ k ∈ P.erase p₁, f k := by
    refine Finset.sum_nbij (·.1) (fun c hc ↦ ?_) (fun c hc d hd h ↦ ?_) (fun k hk ↦ ?_)
      (fun _ _ ↦ rfl)
    · obtain ⟨⟨h12, -, hcl, -⟩, hl⟩ := (hmem c).1 hc
      refine Finset.mem_erase.2 ⟨fun h ↦ ?_, (hP _).2 hl⟩
      have := hle₁ _ (hcl.trans hl)
      omega
    · exact ((hmem c).1 hc).1.eq_of_fst_eq ((hmem d).1 hd).1 h
    · obtain ⟨hk1, hk⟩ := Finset.mem_erase.1 (Finset.mem_coe.1 hk)
      have hkl := (hP k).1 hk
      have hlt : k < p₁ := lt_of_le_of_ne (hle₁ k hkl) hk1
      -- the letter of level `l` just after `k`
      have hex : ∃ j, k < j ∧ w.levelAt j = some l := ⟨p₁, hlt, h₁⟩
      classical
      set q := Nat.find hex
      have hq : k < q ∧ w.levelAt q = some l := Nat.find_spec hex
      refine ⟨(k, q), (hmem _).2 ⟨⟨hq.1, (levelAt_ne_none_iff w).1 (by simp [hq.2]),
        hq.2.trans hkl.symm, fun j hj hj' hjl ↦ Nat.find_min hex hj ⟨hj', hjl.trans hkl⟩⟩, hkl⟩,
        rfl⟩
  have hp₀ : p₀ ∈ P := (hP _).2 h₀
  have hp₁ : p₁ ∈ P := (hP _).2 h₁
  rw [Finset.sum_sub_distrib, hsnd, hfst, Finset.sum_erase_eq_sub hp₀,
    Finset.sum_erase_eq_sub hp₁]
  ring

variable (w) in
/-- The entries of a column of the Seifert matrix, on the loops of the level of that column, as
differences: a loop meets a loop `b` of its own level only at the two bands of `b`. -/
private def columnPotential (b : ℕ × ℕ) (p : ℕ) : ℤ :=
  if p = b.1 then (if w.signAt b.1 = 1 then 0 else -1)
  else if p = b.2 then (if w.signAt b.2 = 1 then -1 else 0) else 0

variable (w) in
/-- The entries of a row of the Seifert matrix, on the loops of the level of that row, as
differences. -/
private def rowPotential (a : ℕ × ℕ) (p : ℕ) : ℤ :=
  if p = a.1 then (if w.signAt a.1 = 1 then 1 else 0)
  else if p = a.2 then (if w.signAt a.2 = 1 then 0 else 1) else 0

/-- Whether a position lies strictly between the two bands of a loop. -/
private def betweenIndicator (b : ℕ × ℕ) (p : ℕ) : ℤ :=
  if b.1 < p ∧ p < b.2 then 1 else 0

private theorem seifertEntry_eq_columnPotential_sub {c b : ℕ × ℕ} (hc : w.IsSeifertLoop c)
    (hb : w.IsSeifertLoop b) (h : w.levelAt c.1 = w.levelAt b.1) :
    seifertEntry w c b = columnPotential w b c.2 - columnPotential w b c.1 := by
  have h₁ : c.1 = b.1 → c = b := hc.eq_of_fst_eq hb
  have h₂ : c.2 = b.2 → c = b := hc.eq_of_snd_eq hb
  obtain ⟨hc12, hc2, -, -⟩ := hc
  obtain ⟨hb12, hb2, -, -⟩ := hb
  have hs₁ := signAt_eq_one_or_eq_neg_one w (hb12.trans hb2)
  have hs₂ := signAt_eq_one_or_eq_neg_one w hb2
  by_cases hcb : c = b
  · subst hcb
    simp only [seifertEntry, columnPotential, ite_true, hc12.ne', hc12.ne]
    rcases hs₁ with hs₁ | hs₁ <;> rcases hs₂ with hs₂ | hs₂ <;> simp [hs₁, hs₂]
  · have h₁' : c.1 ≠ b.1 := mt h₁ hcb
    have h₂' : c.2 ≠ b.2 := mt h₂ hcb
    simp only [seifertEntry, columnPotential, hcb, h, ite_false, ite_true]
    -- only a loop sharing a band with `b` meets it; the sign read is that of the shared band
    rcases eq_or_ne c.2 b.1 with hx | hx
    · rw [hx]
      split_ifs <;> omega
    rcases eq_or_ne b.2 c.1 with hy | hy
    · rw [← hy]
      split_ifs <;> omega
    split_ifs <;> omega

private theorem seifertEntry_eq_rowPotential_sub {a d : ℕ × ℕ} (ha : w.IsSeifertLoop a)
    (hd : w.IsSeifertLoop d) (h : w.levelAt a.1 = w.levelAt d.1) :
    seifertEntry w a d = rowPotential w a d.2 - rowPotential w a d.1 := by
  have h₁ : d.1 = a.1 → d = a := hd.eq_of_fst_eq ha
  have h₂ : d.2 = a.2 → d = a := hd.eq_of_snd_eq ha
  obtain ⟨ha12, ha2, -, -⟩ := ha
  obtain ⟨hd12, hd2, -, -⟩ := hd
  have hs₁ := signAt_eq_one_or_eq_neg_one w (ha12.trans ha2)
  have hs₂ := signAt_eq_one_or_eq_neg_one w ha2
  by_cases had : a = d
  · subst had
    simp only [seifertEntry, rowPotential, ite_true, ha12.ne', ha12.ne]
    rcases hs₁ with hs₁ | hs₁ <;> rcases hs₂ with hs₂ | hs₂ <;> simp [hs₁, hs₂]
  · have h₁' : d.1 ≠ a.1 := fun h ↦ had (h₁ h).symm
    have h₂' : d.2 ≠ a.2 := fun h ↦ had (h₂ h).symm
    simp only [seifertEntry, rowPotential, had, h, ite_false, ite_true]
    split_ifs <;> omega

/-- A loop one level above `b` meets `b` according to how its bands sit relative to those of `b`:
the entry is a difference in the upper loop. -/
private theorem seifertEntry_eq_betweenIndicator_sub {c b : ℕ × ℕ} (hc : w.IsSeifertLoop c)
    (h : w.levelAt c.1 = (w.levelAt b.1).map (· + 1)) (hbl : w.levelAt b.2 = w.levelAt b.1) :
    seifertEntry w c b = betweenIndicator b c.2 - betweenIndicator b c.1 := by
  obtain ⟨hc12, hc2, hcl, -⟩ := hc
  have hne : ∀ i j, w.levelAt i = w.levelAt c.1 → w.levelAt j = w.levelAt b.1 → i ≠ j := by
    rintro i j hi hj rfl
    rw [hi, h] at hj
    cases hb : w.levelAt b.1 <;> simp_all
  have hcb : c ≠ b := fun hcb ↦ hne c.1 b.1 rfl rfl (by rw [hcb])
  have hlev : w.levelAt c.1 ≠ w.levelAt b.1 := fun hl ↦ hne c.1 c.1 rfl hl rfl
  have h11 := hne c.1 b.1 rfl rfl
  have h12 := hne c.1 b.2 rfl hbl
  have h21 := hne c.2 b.1 hcl rfl
  have h22 := hne c.2 b.2 hcl hbl
  simp only [seifertEntry, betweenIndicator, hcb, hlev, ite_false]
  simp only [h, ↓reduceIte]
  split_ifs <;> omega

/-- The same entry as a difference in the lower loop. -/
private theorem seifertEntry_eq_betweenIndicator_sub' {c b : ℕ × ℕ} (hb : w.IsSeifertLoop b)
    (h : w.levelAt c.1 = (w.levelAt b.1).map (· + 1)) (hcl : w.levelAt c.2 = w.levelAt c.1) :
    seifertEntry w c b = betweenIndicator c b.1 - betweenIndicator c b.2 := by
  obtain ⟨hb12, hb2, hbl, -⟩ := hb
  have hne : ∀ i j, w.levelAt i = w.levelAt c.1 → w.levelAt j = w.levelAt b.1 → i ≠ j := by
    rintro i j hi hj rfl
    rw [hi, h] at hj
    cases hb : w.levelAt b.1 <;> simp_all
  have hcb : c ≠ b := fun hcb ↦ hne c.1 b.1 rfl rfl (by rw [hcb])
  have hlev : w.levelAt c.1 ≠ w.levelAt b.1 := fun hl ↦ hne c.1 c.1 rfl hl rfl
  have h11 := hne c.1 b.1 rfl rfl
  have h12 := hne c.1 b.2 rfl hbl
  have h21 := hne c.2 b.1 hcl rfl
  have h22 := hne c.2 b.2 hcl hbl
  simp only [seifertEntry, betweenIndicator, hcb, hlev, ite_false]
  simp only [h, ↓reduceIte]
  split_ifs <;> omega

/-- Loops on levels which are neither equal nor with the first one level above the second do
not meet. -/
private theorem seifertEntry_eq_zero {c b : ℕ × ℕ} (h : w.levelAt c.1 ≠ w.levelAt b.1)
    (h' : w.levelAt c.1 ≠ (w.levelAt b.1).map (· + 1)) : seifertEntry w c b = 0 := by
  have hcb : c ≠ b := fun hcb ↦ h (by rw [hcb])
  simp [seifertEntry, hcb, h, h']

end Telescope

/-! ### Cyclic rotation

Moving the first letter `x` of the word `x :: v` to the end gives `v ++ [x]`, whose closure is the
same diagram cut at a different place (`TauCeti.BraidWord.closure_rotate`). Seifert's algorithm
gives the same surface, and the loops on the levels other than the level `l` of `x` are the same
loops. On level `l`, the loop through the first two letters of level `l` disappears, and the loop
through the last letter of level `l` and the moved letter `x` appears. The loops of level `l`, taken
all the way around the braid axis, sum to zero in the first homology of the surface, so the new
loop is minus the sum of the old loops of level `l`. This is a unimodular change of basis, and it
carries the Seifert matrix of `x :: v` to that of `v ++ [x]`. -/

section Rotate

variable (x : Fin (n - 1) × ℤˣ) (v : BraidWord n)

/-- Shifting a loop with positive endpoints one position earlier and back gives the same loop. -/
private theorem sub_one_add_one_pair {c : ℕ × ℕ} (h₁ : c.1 ≠ 0) (h₂ : c.2 ≠ 0) :
    (c.1 - 1 + 1, c.2 - 1 + 1) = c :=
  Prod.ext (Nat.sub_one_add_one h₁) (Nat.sub_one_add_one h₂)

private theorem levelAt_append_singleton_of_lt {k : ℕ} (hk : k < v.length) :
    (v ++ [x]).levelAt k = levelAt (n := n) (x :: v) (k + 1) := by
  simp [levelAt, List.getElem?_append_left hk]

private theorem levelAt_append_singleton_length :
    (v ++ [x]).levelAt v.length = some (x.1 : ℕ) := by
  simp

private theorem levelAt_cons_zero : levelAt (n := n) (x :: v) 0 = some (x.1 : ℕ) := by
  simp

private theorem signAt_append_singleton_of_lt {k : ℕ} (hk : k < v.length) :
    (v ++ [x]).signAt k = signAt (n := n) (x :: v) (k + 1) := by
  simp [signAt_def, List.getElem?_append_left hk]

private theorem signAt_append_singleton_length :
    (v ++ [x]).signAt v.length = signAt (n := n) (x :: v) 0 := by
  simp

/-- Loops of `v ++ [x]` avoiding the moved letter are the loops of `x :: v` avoiding its first
letter, shifted by one position. -/
private theorem isSeifertLoop_append_singleton_iff {p : ℕ × ℕ} (hp : p.2 < v.length) :
    (v ++ [x]).IsSeifertLoop p ↔
      IsSeifertLoop (n := n) (x :: v) (p.1 + 1, p.2 + 1) := by
  simp only [isSeifertLoop_iff, List.length_append, List.length_cons]
  constructor
  · rintro ⟨h12, -, hl, hb⟩
    refine ⟨by omega, by omega, ?_, fun k hk hk' ↦ ?_⟩
    · rwa [levelAt_append_singleton_of_lt x v hp,
        levelAt_append_singleton_of_lt x v (h12.trans hp)] at hl
    · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have := hb k (by omega) (by omega)
      rwa [levelAt_append_singleton_of_lt x v (by omega),
        levelAt_append_singleton_of_lt x v (h12.trans hp)] at this
  · rintro ⟨h12, -, hl, hb⟩
    refine ⟨by omega, by omega, ?_, fun k hk hk' ↦ ?_⟩
    · rwa [levelAt_append_singleton_of_lt x v hp,
        levelAt_append_singleton_of_lt x v (by omega)]
    · rw [levelAt_append_singleton_of_lt x v (by omega),
        levelAt_append_singleton_of_lt x v (by omega)]
      exact hb (k + 1) (by omega) (by omega)

/-- The level of `x` in `x :: v` has a last letter. -/
private theorem exists_levelAt_cons_last : ∃ m, levelAt (n := n) (x :: v) m = some (x.1 : ℕ) ∧
    ∀ k, m < k → levelAt (n := n) (x :: v) k ≠ some (x.1 : ℕ) := by
  refine ⟨Nat.findGreatest (fun k ↦ levelAt (n := n) (x :: v) k = some (x.1 : ℕ)) v.length,
    Nat.findGreatest_spec (P := fun k ↦ levelAt (n := n) (x :: v) k = some (x.1 : ℕ))
      (Nat.zero_le _) (levelAt_cons_zero x v), fun k hk hkl ↦ ?_⟩
  have hklen : k < v.length + 1 := by
    simpa using (levelAt_ne_none_iff (x :: v : BraidWord n)).1 (by simp [hkl])
  exact Nat.findGreatest_is_greatest hk (by omega) hkl

variable {x v}

private theorem lt_length_of_levelAt_cons {m : ℕ}
    (hm : levelAt (n := n) (x :: v) m = some (x.1 : ℕ)) : m < v.length + 1 := by
  simpa using (levelAt_ne_none_iff (x :: v : BraidWord n)).1 (by simp [hm])

/-- A loop of `v ++ [x]` not ending at the moved letter lies in `v`. -/
private theorem snd_lt_length_of_ne {a : ℕ × ℕ} (ha : (v ++ [x]).IsSeifertLoop a)
    (h : a.2 ≠ v.length) : a.2 < v.length := by
  have := ha.2.1
  simp only [List.length_append, List.length_singleton] at this
  omega

/-- A loop of `v ++ [x]` ending at the moved letter starts at the last letter of `x :: v` on the
level of `x`. -/
private theorem fst_add_one_eq_of_snd_eq_length {m : ℕ}
    (hm : levelAt (n := n) (x :: v) m = some (x.1 : ℕ))
    (hm' : ∀ k, m < k → levelAt (n := n) (x :: v) k ≠ some (x.1 : ℕ)) {a : ℕ × ℕ}
    (ha : (v ++ [x]).IsSeifertLoop a) (h : a.2 = v.length) : a.1 + 1 = m := by
  obtain ⟨h12, -, hl, hb⟩ := ha
  rw [h, levelAt_append_singleton_length, levelAt_append_singleton_of_lt x v (h ▸ h12)] at hl
  have hle : a.1 + 1 ≤ m := not_lt.1 fun hlt ↦ hm' _ hlt hl.symm
  have hmlen := lt_length_of_levelAt_cons hm
  by_contra hne
  refine hb (m - 1) (by omega) (by omega) ?_
  rw [levelAt_append_singleton_of_lt x v (by omega), levelAt_append_singleton_of_lt x v (by omega),
    Nat.sub_add_cancel (by omega), hm, hl]

/-- Conversely, if `x` is not the only letter of its level, the last other letter of that level and
the moved letter span a loop of `v ++ [x]`. -/
private theorem isSeifertLoop_sub_one_length {m : ℕ}
    (hm : levelAt (n := n) (x :: v) m = some (x.1 : ℕ))
    (hm' : ∀ k, m < k → levelAt (n := n) (x :: v) k ≠ some (x.1 : ℕ)) (h0 : m ≠ 0) :
    (v ++ [x]).IsSeifertLoop (m - 1, v.length) := by
  have hmlen := lt_length_of_levelAt_cons hm
  refine ⟨by simp only; omega, by simp, ?_, fun k hk hk' ↦ ?_⟩
  · simp only
    rw [levelAt_append_singleton_length, levelAt_append_singleton_of_lt x v (by omega),
      Nat.sub_add_cancel (by omega), hm]
  · simp only at hk hk'
    rw [levelAt_append_singleton_of_lt x v hk, levelAt_append_singleton_of_lt x v (by omega),
      Nat.sub_add_cancel (by omega), hm]
    exact hm' _ (by omega)

variable (x v) in
/-- The change of basis from the loops of `x :: v` to those of `v ++ [x]`: a loop avoiding the
moved letter is the same loop, shifted by one position, and the loop through the moved letter is
minus the sum of the loops of `x :: v` on the level of `x`. -/
private def rotateRow (a c : ℕ × ℕ) : ℤ :=
  if a.2 = v.length then (if levelAt (n := n) (x :: v) c.1 = some (x.1 : ℕ) then -1 else 0)
  else if c = (a.1 + 1, a.2 + 1) then 1 else 0

private theorem sum_rotateRow_mul {a : ℕ × ℕ} (ha : (v ++ [x]).IsSeifertLoop a)
    (X : ℕ × ℕ → ℤ) :
    ∑ c ∈ seifertLoops (n := n) (x :: v), rotateRow x v a c * X c =
      if a.2 = v.length then
        -∑ c ∈ seifertLoops (n := n) (x :: v) with
          levelAt (n := n) (x :: v) c.1 = some (x.1 : ℕ), X c
      else X (a.1 + 1, a.2 + 1) := by
  split_ifs with h
  · simp only [rotateRow, h, ↓reduceIte, ite_mul, neg_one_mul, zero_mul, Finset.sum_ite,
      Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib]
  · have hlt := snd_lt_length_of_ne ha h
    simp only [rotateRow, h, ↓reduceIte, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      mem_seifertLoops, (isSeifertLoop_append_singleton_iff x v hlt).1 ha]

/-- Away from the moved letter, the two Seifert matrices have the same entries. -/
private theorem seifertEntry_append_singleton_of_lt {a b : ℕ × ℕ} (ha : a.1 < a.2)
    (ha' : a.2 < v.length) (hb : b.1 < b.2) (hb' : b.2 < v.length) :
    seifertEntry (v ++ [x]) a b =
      seifertEntry (n := n) (x :: v) (a.1 + 1, a.2 + 1) (b.1 + 1, b.2 + 1) := by
  simp only [seifertEntry, levelAt_append_singleton_of_lt x v (ha.trans ha'),
    levelAt_append_singleton_of_lt x v (hb.trans hb'), signAt_append_singleton_of_lt x v ha',
    signAt_append_singleton_of_lt x v (ha.trans ha'), Prod.ext_iff, Nat.add_right_cancel_iff,
    Nat.add_lt_add_iff_right]

variable {m : ℕ} (hm : levelAt (n := n) (x :: v) m = some (x.1 : ℕ))
  (hm' : ∀ k, m < k → levelAt (n := n) (x :: v) k ≠ some (x.1 : ℕ))
include hm hm'

/-- Telescoping along the level of `x` in `x :: v`, which starts at `0` and ends at `m`. -/
private theorem sum_seifertLoops_levelAt_sub_cons (f : ℕ → ℤ) :
    ∑ c ∈ seifertLoops (n := n) (x :: v) with levelAt (n := n) (x :: v) c.1 = some (x.1 : ℕ),
      (f c.2 - f c.1) = f m - f 0 :=
  sum_seifertLoops_levelAt_sub (levelAt_cons_zero x v) (fun _ h ↦ absurd h (Nat.not_lt_zero _))
    hm hm' f

omit hm in
private theorem mem_filter_seifertLoops_cons {c : ℕ × ℕ}
    (hc : c ∈ (seifertLoops (n := n) (x :: v)).filter
      fun c ↦ levelAt (n := n) (x :: v) c.1 = some (x.1 : ℕ)) :
    IsSeifertLoop (n := n) (x :: v) c ∧ levelAt (n := n) (x :: v) c.1 = some (x.1 : ℕ) ∧
      c.2 ≤ m := by
  obtain ⟨hc, hl⟩ := Finset.mem_filter.1 hc
  rw [mem_seifertLoops] at hc
  exact ⟨hc, hl, not_lt.1 fun h ↦ hm' _ h (hc.2.2.1.trans hl)⟩

/-- The row of the loop through the moved letter: minus the sum of the entries of the loops of its
level in `x :: v`. -/
private theorem seifertEntry_append_singleton_eq_neg_sum_left {a b : ℕ × ℕ}
    (ha : (v ++ [x]).IsSeifertLoop a) (ha2 : a.2 = v.length) (hb : (v ++ [x]).IsSeifertLoop b)
    (hb2 : b.2 ≠ v.length) :
    seifertEntry (v ++ [x]) a b =
      -∑ c ∈ seifertLoops (n := n) (x :: v) with levelAt (n := n) (x :: v) c.1 = some (x.1 : ℕ),
        seifertEntry (n := n) (x :: v) c (b.1 + 1, b.2 + 1) := by
  have ha1 := fst_add_one_eq_of_snd_eq_length hm hm' ha ha2
  have hal : a.1 < v.length := ha2 ▸ ha.1
  have hblt := snd_lt_length_of_ne hb hb2
  have hB := (isSeifertLoop_append_singleton_iff x v hblt).1 hb
  have hab : a ≠ b := fun h ↦ hb2 (h ▸ ha2)
  have hla : (v ++ [x]).levelAt a.1 = some (x.1 : ℕ) := by
    rw [levelAt_append_singleton_of_lt x v hal, ha1, hm]
  have hlb : (v ++ [x]).levelAt b.1 = levelAt (n := n) (x :: v) (b.1 + 1) :=
    levelAt_append_singleton_of_lt x v (hb.1.trans hblt)
  have hb12 := hb.1
  by_cases h₁ : levelAt (n := n) (x :: v) (b.1 + 1) = some (x.1 : ℕ)
  · -- `b` lies on the level of `x`
    have hle : b.2 + 1 ≤ m := not_lt.1 fun h ↦ hm' _ h (hB.2.2.1.trans h₁)
    rw [Finset.sum_congr rfl fun c hc ↦ seifertEntry_eq_columnPotential_sub
      (mem_filter_seifertLoops_cons hm' hc).1 hB
      ((mem_filter_seifertLoops_cons hm' hc).2.1.trans h₁.symm),
      sum_seifertLoops_levelAt_sub_cons hm hm']
    simp only [seifertEntry, hab, hla, hlb, h₁, ↓reduceIte, columnPotential,
      signAt_append_singleton_of_lt x v hal, ha1]
    have hs := signAt_eq_one_or_eq_neg_one (x :: v : BraidWord n) (lt_length_of_levelAt_cons hm)
    rcases eq_or_ne (b.2 + 1) m with h | h
    · rw [← h] at hs ⊢
      split_ifs <;> first | contradiction | omega
    · split_ifs <;> first | contradiction | omega
  by_cases h₂ : some (x.1 : ℕ) = (levelAt (n := n) (x :: v) (b.1 + 1)).map (· + 1)
  · -- `b` lies one level below `x`
    rw [Finset.sum_congr rfl fun c hc ↦ seifertEntry_eq_betweenIndicator_sub
      (mem_filter_seifertLoops_cons hm' hc).1
      ((mem_filter_seifertLoops_cons hm' hc).2.1.trans h₂) hB.2.2.1,
      sum_seifertLoops_levelAt_sub_cons hm hm']
    have hne : (levelAt (n := n) (x :: v) (b.1 + 1)).map (· + 1) ≠
        levelAt (n := n) (x :: v) (b.1 + 1) := by
      cases h : levelAt (n := n) (x :: v) (b.1 + 1) with
      | none => simp [h] at h₂
      | some _ => simp
    simp only [seifertEntry, hab, hla, hlb, h₂, hne, ↓reduceIte, betweenIndicator]
    split_ifs <;> omega
  · -- `b` is too far from `x` to meet its loops
    rw [Finset.sum_eq_zero fun c hc ↦ seifertEntry_eq_zero
      (by simp only [(mem_filter_seifertLoops_cons hm' hc).2.1]; exact Ne.symm h₁)
      (by simp only [(mem_filter_seifertLoops_cons hm' hc).2.1]; exact h₂), neg_zero]
    exact seifertEntry_eq_zero (by rw [hla, hlb]; exact Ne.symm h₁) (by rw [hla, hlb]; exact h₂)

/-- The column of the loop through the moved letter: minus the sum of the entries of the loops of
its level in `x :: v`. -/
private theorem seifertEntry_append_singleton_eq_neg_sum_right {a b : ℕ × ℕ}
    (ha : (v ++ [x]).IsSeifertLoop a) (ha2 : a.2 ≠ v.length) (hb : (v ++ [x]).IsSeifertLoop b)
    (hb2 : b.2 = v.length) :
    seifertEntry (v ++ [x]) a b =
      -∑ d ∈ seifertLoops (n := n) (x :: v) with levelAt (n := n) (x :: v) d.1 = some (x.1 : ℕ),
        seifertEntry (n := n) (x :: v) (a.1 + 1, a.2 + 1) d := by
  have hb1 := fst_add_one_eq_of_snd_eq_length hm hm' hb hb2
  have hbl : b.1 < v.length := hb2 ▸ hb.1
  have halt := snd_lt_length_of_ne ha ha2
  have hA := (isSeifertLoop_append_singleton_iff x v halt).1 ha
  have hab : a ≠ b := fun h ↦ ha2 (h ▸ hb2)
  have hlb : (v ++ [x]).levelAt b.1 = some (x.1 : ℕ) := by
    rw [levelAt_append_singleton_of_lt x v hbl, hb1, hm]
  have hla : (v ++ [x]).levelAt a.1 = levelAt (n := n) (x :: v) (a.1 + 1) :=
    levelAt_append_singleton_of_lt x v (ha.1.trans halt)
  have ha12 := ha.1
  by_cases h₁ : levelAt (n := n) (x :: v) (a.1 + 1) = some (x.1 : ℕ)
  · -- `a` lies on the level of `x`
    have hle : a.2 + 1 ≤ m := not_lt.1 fun h ↦ hm' _ h (hA.2.2.1.trans h₁)
    rw [Finset.sum_congr rfl fun d hd ↦ seifertEntry_eq_rowPotential_sub hA
      (mem_filter_seifertLoops_cons hm' hd).1
      (h₁.trans (mem_filter_seifertLoops_cons hm' hd).2.1.symm),
      sum_seifertLoops_levelAt_sub_cons hm hm']
    simp only [seifertEntry, hab, hla, hlb, h₁, ↓reduceIte, rowPotential,
      signAt_append_singleton_of_lt x v halt]
    have hlt : a.2 + 1 < v.length + 1 := by omega
    have hs := signAt_eq_one_or_eq_neg_one (x :: v : BraidWord n) hlt
    split_ifs <;> first | contradiction | omega
  by_cases h₂ : levelAt (n := n) (x :: v) (a.1 + 1) = (some (x.1 : ℕ)).map (· + 1)
  · -- `a` lies one level above `x`
    have hneg : ∀ d : ℕ × ℕ, betweenIndicator (a.1 + 1, a.2 + 1) d.1 -
        betweenIndicator (a.1 + 1, a.2 + 1) d.2 = (-betweenIndicator (a.1 + 1, a.2 + 1) d.2) -
          (-betweenIndicator (a.1 + 1, a.2 + 1) d.1) := fun d ↦ by ring
    rw [Finset.sum_congr rfl fun d hd ↦ (seifertEntry_eq_betweenIndicator_sub'
      (mem_filter_seifertLoops_cons hm' hd).1
      (by simp only [(mem_filter_seifertLoops_cons hm' hd).2.1]; exact h₂) hA.2.2.1).trans
      (hneg d),
      sum_seifertLoops_levelAt_sub_cons hm hm' (fun p ↦ -betweenIndicator (a.1 + 1, a.2 + 1) p)]
    simp only [seifertEntry, hab, hla, hlb, h₁, ↓reduceIte, betweenIndicator]
    simp only [h₂, ↓reduceIte]
    split_ifs <;> omega
  · -- `a` is too far from `x` to meet its loops
    rw [Finset.sum_eq_zero fun d hd ↦ seifertEntry_eq_zero
      (by simp only [(mem_filter_seifertLoops_cons hm' hd).2.1]; exact h₁)
      (by simp only [(mem_filter_seifertLoops_cons hm' hd).2.1]; exact h₂), neg_zero]
    exact seifertEntry_eq_zero (by rw [hla, hlb]; exact h₁) (by rw [hla, hlb]; exact h₂)

/-- The diagonal entry at the loop through the moved letter: the sum of all the entries between
loops of its level in `x :: v`. -/
private theorem seifertEntry_append_singleton_eq_sum_sum {a : ℕ × ℕ}
    (ha : (v ++ [x]).IsSeifertLoop a) (ha2 : a.2 = v.length) :
    seifertEntry (v ++ [x]) a a =
      ∑ d ∈ seifertLoops (n := n) (x :: v) with levelAt (n := n) (x :: v) d.1 = some (x.1 : ℕ),
        ∑ c ∈ seifertLoops (n := n) (x :: v) with
          levelAt (n := n) (x :: v) c.1 = some (x.1 : ℕ),
          seifertEntry (n := n) (x :: v) c d := by
  have ha1 := fst_add_one_eq_of_snd_eq_length hm hm' ha ha2
  have hal : a.1 < v.length := ha2 ▸ ha.1
  -- summing the rows of the loops of the level of `x` first, then telescoping a second time
  set g : ℕ → ℤ := fun p ↦
    (if p = m then (if signAt (n := n) (x :: v) m = 1 then 0 else 1) else 0) +
      (if p = 0 then (if signAt (n := n) (x :: v) 0 = 1 then 1 else 0) else 0) with hg
  rw [Finset.sum_comm, Finset.sum_congr rfl fun c hc ↦ (Finset.sum_congr rfl fun d hd ↦
    seifertEntry_eq_rowPotential_sub (mem_filter_seifertLoops_cons hm' hc).1
      (mem_filter_seifertLoops_cons hm' hd).1
      ((mem_filter_seifertLoops_cons hm' hc).2.1.trans
        (mem_filter_seifertLoops_cons hm' hd).2.1.symm)).trans
    (sum_seifertLoops_levelAt_sub_cons hm hm' _)]
  have hrow : ∀ c ∈ (seifertLoops (n := n) (x :: v)).filter
      (fun c ↦ levelAt (n := n) (x :: v) c.1 = some (x.1 : ℕ)),
      rowPotential (x :: v : BraidWord n) c m - rowPotential (x :: v : BraidWord n) c 0 =
        g c.2 - g c.1 := fun c hc ↦ by
    obtain ⟨⟨hc12, -, -, -⟩, -, hc2⟩ := mem_filter_seifertLoops_cons hm' hc
    simp only [rowPotential, hg]
    rcases eq_or_ne c.2 m with h | h <;> rcases eq_or_ne c.1 0 with h' | h'
    all_goals first
      | (rw [h, h']; split_ifs <;> omega)
      | (rw [h]; split_ifs <;> omega)
      | (rw [h']; split_ifs <;> omega)
      | (split_ifs <;> omega)
  rw [Finset.sum_congr rfl hrow, sum_seifertLoops_levelAt_sub_cons hm hm']
  simp only [seifertEntry, ↓reduceIte, hg, signAt_append_singleton_of_lt x v hal, ha2,
    signAt_append_singleton_length, ha1]
  have hs₀ := signAt_eq_one_or_eq_neg_one (x :: v : BraidWord n) (Nat.succ_pos v.length)
  have hs₁ := signAt_eq_one_or_eq_neg_one (x :: v : BraidWord n) (lt_length_of_levelAt_cons hm)
  split_ifs <;> omega

omit hm hm' in
/-- **The rotated Seifert matrix is the congruence of the original one by the change of basis.**
Each entry of the Seifert matrix of `v ++ [x]` is the corresponding entry of `R V Rᵀ`, for `V` the
Seifert matrix of `x :: v` and `R` the change of basis `rotateRow x v`. -/
private theorem seifertEntry_append_singleton_eq_sum {a b : ℕ × ℕ}
    (ha : (v ++ [x]).IsSeifertLoop a) (hb : (v ++ [x]).IsSeifertLoop b) :
    seifertEntry (v ++ [x]) a b =
      ∑ d ∈ seifertLoops (n := n) (x :: v), (∑ c ∈ seifertLoops (n := n) (x :: v),
        rotateRow x v a c * seifertEntry (n := n) (x :: v) c d) * rotateRow x v b d := by
  -- the last letter of `x :: v` on the level of `x`
  obtain ⟨m, hm, hm'⟩ := exists_levelAt_cons_last x v
  simp_rw [mul_comm _ (rotateRow x v b _)]
  rw [sum_rotateRow_mul hb]
  have hinner := fun d ↦ sum_rotateRow_mul ha (fun c ↦ seifertEntry (n := n) (x :: v) c d)
  by_cases ha2 : a.2 = v.length <;> by_cases hb2 : b.2 = v.length
  · have hab : a = b := Prod.ext (by
      have := fst_add_one_eq_of_snd_eq_length hm hm' ha ha2
      have := fst_add_one_eq_of_snd_eq_length hm hm' hb hb2
      omega) (ha2.trans hb2.symm)
    subst hab
    simp only [hinner, ha2, ↓reduceIte, Finset.sum_neg_distrib, neg_neg]
    exact seifertEntry_append_singleton_eq_sum_sum hm hm' ha ha2
  · simp only [hinner, ha2, hb2, ↓reduceIte]
    exact seifertEntry_append_singleton_eq_neg_sum_left hm hm' ha ha2 hb hb2
  · simp only [hinner, ha2, hb2, ↓reduceIte]
    exact seifertEntry_append_singleton_eq_neg_sum_right hm hm' ha ha2 hb hb2
  · simp only [hinner, ha2, hb2, ↓reduceIte]
    exact seifertEntry_append_singleton_of_lt ha.1 (snd_lt_length_of_ne ha ha2) hb.1
      (snd_lt_length_of_ne hb hb2)

variable (x v) in
omit hm hm' in
/-- **Cyclic rotation is a unimodular change of basis of the Seifert matrix.** Moving the first
letter `x` of a braid word to the end changes the Seifert matrix of the canonical Seifert surface
only by a congruence `P V Pᵀ` with `P` invertible over `ℤ`, followed by a relabelling of the loops.
The loop through the last letter of the level of `x` and the moved letter `x` is minus the sum of
the loops of that level in `x :: v`; every other loop is the same loop, one position earlier. -/
theorem exists_seifertMatrix_append_singleton :
    ∃ (ι : (v ++ [x]).seifertLoops ≃ seifertLoops (n := n) (x :: v))
      (P : Matrix (seifertLoops (n := n) (x :: v)) (seifertLoops (n := n) (x :: v)) ℤ),
      IsUnit P.det ∧
        (v ++ [x]).seifertMatrix = (P * seifertMatrix (n := n) (x :: v) * Pᵀ).submatrix ι ι := by
  -- the last letter of `x :: v` on the level of `x`
  obtain ⟨m, hm, hm'⟩ := exists_levelAt_cons_last x v
  have hmlen := lt_length_of_levelAt_cons hm
  have hlen : ∀ c : seifertLoops (n := n) (x :: v), c.1.1 < c.1.2 ∧ c.1.2 < v.length + 1 :=
    fun c ↦ by
      have hc := (mem_seifertLoops _).1 c.2
      exact ⟨hc.1, by simpa using hc.2.1⟩
  -- a loop through the first letter lies on the level of `x`, so that level has a second letter
  have hm0 : ∀ c : seifertLoops (n := n) (x :: v), c.1.1 = 0 → m ≠ 0 := fun c h0 ↦ by
    have hc := (mem_seifertLoops _).1 c.2
    have hl : levelAt (n := n) (x :: v) c.1.2 = some (x.1 : ℕ) := by
      rw [hc.2.2.1, h0, levelAt_cons_zero]
    have := not_lt.1 fun h ↦ hm' _ h hl
    have := (hlen c).1
    omega
  -- the change of basis, read on the loops of `x :: v`
  let κ : seifertLoops (n := n) (x :: v) → (v ++ [x]).seifertLoops := fun c ↦
    ⟨if c.1.1 = 0 then (m - 1, v.length) else (c.1.1 - 1, c.1.2 - 1), by
      rw [mem_seifertLoops]
      split_ifs with h0
      · exact isSeifertLoop_sub_one_length hm hm' (hm0 c h0)
      · have := hlen c
        rw [isSeifertLoop_append_singleton_iff x v (by omega),
          sub_one_add_one_pair h0 (by omega)]
        exact (mem_seifertLoops _).1 c.2⟩
  have hκ : ∀ c : seifertLoops (n := n) (x :: v), c.1.1 ≠ 0 →
      (κ c).1 = (c.1.1 - 1, c.1.2 - 1) := fun c h0 ↦ by simp [κ, h0]
  have hκ₀ : ∀ c : seifertLoops (n := n) (x :: v), c.1.1 = 0 → (κ c).1 = (m - 1, v.length) :=
    fun c h0 ↦ by simp [κ, h0]
  have hκbij : Function.Bijective κ := by
    refine ⟨fun c d h ↦ Subtype.ext ?_, fun a ↦ ?_⟩
    · have hc := hlen c
      have hd := hlen d
      have h' := congrArg Subtype.val h
      by_cases h0 : c.1.1 = 0 <;> by_cases h0' : d.1.1 = 0
      · exact ((mem_seifertLoops _).1 c.2).eq_of_fst_eq ((mem_seifertLoops _).1 d.2)
          (h0.trans h0'.symm)
      · rw [hκ₀ c h0, hκ d h0', Prod.mk.injEq] at h'
        omega
      · rw [hκ c h0, hκ₀ d h0', Prod.mk.injEq] at h'
        omega
      · rw [hκ c h0, hκ d h0', Prod.mk.injEq] at h'
        exact Prod.ext (by omega) (by omega)
    · have ha := (mem_seifertLoops _).1 a.2
      by_cases ha2 : a.1.2 = v.length
      · -- the loop through the moved letter comes from the first loop of the level of `x`
        have ha1 := fst_add_one_eq_of_snd_eq_length hm hm' ha ha2
        have hex : ∃ j, 0 < j ∧ levelAt (n := n) (x :: v) j = some (x.1 : ℕ) := ⟨m, by omega, hm⟩
        classical
        have hq := Nat.find_spec hex
        have hc : IsSeifertLoop (n := n) (x :: v) (0, Nat.find hex) :=
          ⟨hq.1, (levelAt_ne_none_iff (x :: v : BraidWord n)).1 (by simp [hq.2]),
            hq.2.trans (levelAt_cons_zero x v).symm, fun j hj hj' hjl ↦
              Nat.find_min hex hj ⟨hj', hjl.trans (levelAt_cons_zero x v)⟩⟩
        refine ⟨⟨(0, Nat.find hex), (mem_seifertLoops _).2 hc⟩, Subtype.ext ?_⟩
        rw [hκ₀ _ rfl]
        exact Prod.ext (by simp only; omega) ha2.symm
      · have ha2' := snd_lt_length_of_ne ha ha2
        refine ⟨⟨(a.1.1 + 1, a.1.2 + 1), (mem_seifertLoops _).2
          ((isSeifertLoop_append_singleton_iff x v ha2').1 ha)⟩, Subtype.ext ?_⟩
        rw [hκ _ (Nat.succ_ne_zero _)]
        simp
  set P : Matrix (seifertLoops (n := n) (x :: v)) (seifertLoops (n := n) (x :: v)) ℤ :=
    Matrix.of fun c d ↦ rotateRow x v (κ c) d with hPdef
  refine ⟨(Equiv.ofBijective κ hκbij).symm, P, ?_, ?_⟩
  · -- the change of basis is the identity except in the row of the first loop of the level of `x`
    have hrow : ∀ c d : seifertLoops (n := n) (x :: v), c.1.1 ≠ 0 →
        rotateRow x v (κ c) d = (1 : Matrix _ _ ℤ) c d := fun c d h0 ↦ by
      have := hlen c
      have hne : c.1.2 - 1 ≠ v.length := by omega
      rw [rotateRow, hκ c h0, Matrix.one_apply]
      simp only [hne, ↓reduceIte, sub_one_add_one_pair h0 (by omega), eq_comm (a := d.1),
        Subtype.ext_iff]
    by_cases h₀ : ∃ c₀ : seifertLoops (n := n) (x :: v), c₀.1.1 = 0
    · obtain ⟨c₀, hc₀⟩ := h₀
      set r : seifertLoops (n := n) (x :: v) → ℤ := fun d ↦
        if levelAt (n := n) (x :: v) d.1.1 = some (x.1 : ℕ) then -1 else 0 with hr
      have hsum : ∑ k, r k • (1 : Matrix (seifertLoops (n := n) (x :: v))
          (seifertLoops (n := n) (x :: v)) ℤ) k = r := by
        ext d
        simp [Matrix.one_apply]
      have hP : P = (1 : Matrix _ _ ℤ).updateRow c₀
          (∑ k, r k • (1 : Matrix (seifertLoops (n := n) (x :: v))
            (seifertLoops (n := n) (x :: v)) ℤ) k) := by
        rw [hsum]
        ext c d
        by_cases hc : c = c₀
        · subst hc
          simp [hPdef, rotateRow, hκ₀ c hc₀, hr]
        · rw [hPdef, Matrix.of_apply, Matrix.updateRow_ne hc, hrow c d fun h ↦ hc (Subtype.ext
            (((mem_seifertLoops _).1 c.2).eq_of_fst_eq ((mem_seifertLoops _).1 c₀.2)
              (h.trans hc₀.symm)))]
      rw [hP, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one, hr]
      simp [hc₀]
    · push Not at h₀
      have hP : P = 1 := by
        ext c d
        exact hrow c d (h₀ c)
      rw [hP, Matrix.det_one]
      exact isUnit_one
  · ext a b
    simp only [hPdef, seifertMatrix, Matrix.submatrix_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.of_apply, Equiv.ofBijective_apply_symm_apply]
    rw [Finset.univ_eq_attach, seifertEntry_append_singleton_eq_sum ((mem_seifertLoops _).1 a.2)
      ((mem_seifertLoops _).1 b.2), ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [← Finset.sum_attach]

end Rotate

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


variable (x : Fin (n - 1) × ℤˣ) (v : BraidWord n)

/-- Moving the first letter of a braid word to the end keeps the Alexander polynomial of the
Seifert matrix. -/
theorem alexander_seifertMatrix_append_singleton :
    alexander (v ++ [x]).seifertMatrix = alexander (seifertMatrix (n := n) (x :: v)) := by
  obtain ⟨ι, P, hP, h⟩ := exists_seifertMatrix_append_singleton x v
  rw [h, Matrix.alexander_submatrix_equiv_self, alexander_congruence_of_det_sq_eq_one]
  rcases Int.isUnit_iff.1 hP with hP | hP <;> simp [hP]

/-- Moving the first letter of a braid word to the end keeps the Tristram–Levine signatures of the
Seifert matrix. -/
theorem tristramLevineSignature_seifertMatrix_append_singleton (ω : ℂ) :
    tristramLevineSignature ((v ++ [x]).seifertMatrix.map ((↑) : ℤ → ℝ)) ω =
      tristramLevineSignature ((seifertMatrix (n := n) (x :: v)).map ((↑) : ℤ → ℝ)) ω := by
  obtain ⟨ι, P, hP, h⟩ := exists_seifertMatrix_append_singleton x v
  have hPReal : IsUnit (P.map (Int.castRingHom ℝ)).det :=
    RingHom.map_det (Int.castRingHom ℝ) P ▸ hP.map (Int.castRingHom ℝ)
  have hmap : ∀ M : Matrix (seifertLoops (n := n) (x :: v)) (seifertLoops (n := n) (x :: v)) ℤ,
      M.map ((↑) : ℤ → ℝ) = M.map (Int.castRingHom ℝ) := fun M ↦ by simp
  rw [h, ← Matrix.submatrix_map, ← ι.symm_symm, tristramLevineSignature_submatrix_equiv_self,
    hmap, hmap, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    tristramLevineSignature_congr hPReal]

/-- Cyclically rotating a braid word keeps the Alexander polynomial of the Seifert matrix. -/
@[simp]
theorem alexander_seifertMatrix_rotate (w : BraidWord n) (k : ℕ) :
    alexander (seifertMatrix (n := n) (w.rotate k)) = alexander w.seifertMatrix := by
  induction k with
  | zero => rw [List.rotate_zero]
  | succ k ih =>
    rw [← List.rotate_rotate]
    rcases h : w.rotate k with _ | ⟨y, u⟩
    · rw [h] at ih
      rw [List.rotate_nil, ih]
    · rw [h] at ih
      rw [List.rotate_cons_succ, List.rotate_zero, alexander_seifertMatrix_append_singleton, ih]

/-- Cyclically rotating a braid word keeps the Tristram–Levine signatures of the Seifert
matrix. -/
@[simp]
theorem tristramLevineSignature_seifertMatrix_rotate (w : BraidWord n) (k : ℕ) (ω : ℂ) :
    tristramLevineSignature ((seifertMatrix (n := n) (w.rotate k)).map ((↑) : ℤ → ℝ)) ω =
      tristramLevineSignature (w.seifertMatrix.map ((↑) : ℤ → ℝ)) ω := by
  induction k with
  | zero => rw [List.rotate_zero]
  | succ k ih =>
    rw [← List.rotate_rotate]
    rcases h : w.rotate k with _ | ⟨y, u⟩
    · rw [h] at ih
      rw [List.rotate_nil, ih]
    · rw [h] at ih
      rw [List.rotate_cons_succ, List.rotate_zero,
        tristramLevineSignature_seifertMatrix_append_singleton, ih]

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

/-- The closure of `σ₁⁻³` is the left-handed trefoil, the mirror image of the closure of `σ₁³`.
Its canonical Seifert surface has the two loops `(0, 1)` and `(1, 2)`, and in that basis its Seifert
matrix is the negative of `TauCeti.KnotTheory.trefoilSeifertMatrix`. -/
theorem seifertMatrix_mirrorTrefoil :
    ∃ e : Fin 2 ≃ seifertLoops (n := 2) [(0, -1), (0, -1), (0, -1)],
      (seifertMatrix (n := 2) [(0, -1), (0, -1), (0, -1)]).submatrix e e =
        -trefoilSeifertMatrix := by
  have htrefoil : trefoilSeifertMatrix = !![-1, 1; 0, -1] := Matrix.ext trefoilSeifertMatrix_apply
  rw [htrefoil]
  exact ⟨Equiv.ofBijective ![⟨(0, 1), by decide⟩, ⟨(1, 2), by decide⟩] (by decide),
    by decide +kernel⟩

/-- The Seifert matrix of the braid `σ₁⁻³` has the signature `2` of the left-handed trefoil. -/
theorem signature_seifertMatrix_mirrorTrefoil :
    Matrix.signature ((seifertMatrix (n := 2) [(0, -1), (0, -1), (0, -1)]).map ((↑) : ℤ → 𝕜)) =
      2 := by
  obtain ⟨e, he⟩ := seifertMatrix_mirrorTrefoil
  rw [← Matrix.signature_submatrix_equiv_self e.symm, e.symm_symm, Matrix.submatrix_map, he,
    Matrix.map_neg _ Int.cast_neg, Matrix.signature_neg, signature_trefoilSeifertMatrix, neg_neg]

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
