/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Basic
public import TauCeti.KnotTheory.Markov.TristramLevine

/-!
# The Seifert matrix of a connected sum of closed braids

For braid words `w₁` on `n + 1` strands and `w₂` on `m + 1` strands, the word
`TauCeti.BraidWord.connectedSum w₁ w₂` on `n + m + 1` strands is `w₁` on the strands `0, …, n`
followed by `w₂` moved up onto the strands `n, …, n + m`. The two braids share the strand `n`, so
the closure of the word is a connected sum of the closures of `w₁` and `w₂`, made along the
components through that strand: a `2`-sphere enclosing the letters of `w₁` together with the
strands `0, …, n - 1` and their closing arcs meets the closure in two points of the shared strand,
and cuts it into the two summands (Birman, Chapter 2). For knots this is the connected sum
`K₁ # K₂` of oriented knots.

The canonical Seifert surface of Seifert's algorithm, whose Seifert matrix is
`TauCeti.BraidWord.seifertMatrix`, is the union of those of `w₁` and `w₂` along a common disc, a
boundary connected sum: the discs `D₀, …, Dₙ` with the bands of `w₁`, and the discs
`Dₙ, …, D_{n+m}` with the bands of `w₂`, glued along the shared disc `Dₙ`. A basis loop runs
between two consecutive bands of one level, so each loop belongs to one of the summands
(`TauCeti.BraidWord.seifertLoopsConnectedSumEquiv`). Two loops from different summands do not
link: they could only meet on the shared disc, between a loop on level `n - 1` and one on level
`n`, and that requires their bands to interleave along the word, which they do not, since all bands
of `w₁` come before all bands of `w₂`. So the Seifert matrix of the connected sum is block
diagonal, with the Seifert matrices of `w₁` and `w₂` as its blocks
(`TauCeti.BraidWord.submatrix_seifertMatrix_connectedSum`).

Consequently the Tristram–Levine signatures are additive and the Alexander polynomial is
multiplicative under this connected sum
(`TauCeti.BraidWord.tristramLevineSignature_seifertMatrix_connectedSum`,
`TauCeti.BraidWord.alexander_seifertMatrix_connectedSum`). Additivity under connected sum is what
makes the signature, a concordance invariant, a homomorphism on the knot concordance group, whose
group operation is the connected sum. As an application, the granny knot (the connected sum of two
right-handed trefoils, the closure of `σ₀³ σ₁³`) has signature `-4` while the square knot (a
right-handed trefoil plus a left-handed one, the closure of `σ₀³ σ₁⁻³`) has signature `0`,
although the two have the same Alexander polynomial `(t - 1 + t⁻¹)²`. So the two braids are not
Markov equivalent (`TauCeti.not_markovEquiv_granny_square`).

## Main definitions

* `TauCeti.BraidWord.connectedSum w₁ w₂`: the word `w₁` followed by `w₂` shifted up by `n`
  strands, whose closure is the connected sum of the closures.
* `TauCeti.BraidWord.seifertLoopsConnectedSumEquiv`: the basis loops of the connected sum are
  those of the two summands.

## Main results

* `TauCeti.BraidWord.submatrix_seifertMatrix_connectedSum`: the Seifert matrix of the connected
  sum is the block diagonal matrix of the Seifert matrices of the summands.
* `TauCeti.BraidWord.tristramLevineSignature_seifertMatrix_connectedSum` and
  `TauCeti.MarkovBraid.tristramLevineSignature_mk_connectedSum`: the Tristram–Levine signature of
  the connected sum is the sum of the signatures of the summands.
* `TauCeti.BraidWord.alexander_seifertMatrix_connectedSum`: for Seifert surfaces of even rank, the
  Alexander polynomial of the connected sum is the product of those of the summands.
* `TauCeti.not_markovEquiv_granny_square`: the braids `σ₀³ σ₁³` and `σ₀³ σ₁⁻³` of the granny
  knot and the square knot are not Markov equivalent.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 6
  (Seifert matrices of connected sums) and Chapter 8 (additivity of the signature).
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 2 (braids and closed braids).
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2 (the signature homomorphism on the concordance group).
-/

public section

namespace TauCeti

namespace BraidWord

open KnotTheory LaurentPolynomial

variable {n m : ℕ} (w₁ : BraidWord (n + 1)) (w₂ : BraidWord (m + 1))

/-- The **connected sum** of braid words: `w₁` on the strands `0, …, n` followed by `w₂` moved up
onto the strands `n, …, n + m`, so that the two braids share the strand `n`. Its closure is the
connected sum of the closures of `w₁` and `w₂`, along the components through the shared strand. -/
def connectedSum : BraidWord (n + m + 1) :=
  w₁.map (fun x ↦ ((Fin.castAdd m x.1 : Fin (n + m)), x.2)) ++
    w₂.map (fun x ↦ ((Fin.natAdd n x.1 : Fin (n + m)), x.2))

/-- The defining equation of `TauCeti.BraidWord.connectedSum`. -/
theorem connectedSum_def :
    w₁.connectedSum w₂ = w₁.map (fun x ↦ ((Fin.castAdd m x.1 : Fin (n + m)), x.2)) ++
      w₂.map (fun x ↦ ((Fin.natAdd n x.1 : Fin (n + m)), x.2)) :=
  (rfl)

-- The list type is written `Fin (n + m) × ℤˣ` rather than `BraidWord (n + m + 1)`, for the reason
-- given at `TauCeti.BraidWord.length_strandIncl`.
/-- The connected sum has the letters of both words. -/
@[simp]
theorem length_connectedSum :
    List.length (α := Fin (n + m) × ℤˣ) (w₁.connectedSum w₂) = w₁.length + w₂.length := by
  simp [connectedSum_def]

/-- The letters of `w₁` keep their level in the connected sum. -/
@[simp]
theorem levelAt_connectedSum_of_lt {k : ℕ} (hk : k < w₁.length) :
    (w₁.connectedSum w₂).levelAt k = w₁.levelAt k := by
  rw [levelAt_def, levelAt_def, connectedSum_def,
    List.getElem?_append_left (by simpa using hk), List.getElem?_map, Option.map_map]
  rfl

/-- The letters of `w₂` are moved up by `n` levels in the connected sum. -/
@[simp]
theorem levelAt_connectedSum_add (k : ℕ) :
    (w₁.connectedSum w₂).levelAt (w₁.length + k) = (w₂.levelAt k).map (n + ·) := by
  rw [levelAt_def, levelAt_def, connectedSum_def,
    List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left,
    List.getElem?_map, Option.map_map, Option.map_map]
  rfl

/-- The letters of `w₁` keep their sign in the connected sum. -/
@[simp]
theorem signAt_connectedSum_of_lt {k : ℕ} (hk : k < w₁.length) :
    (w₁.connectedSum w₂).signAt k = w₁.signAt k := by
  rw [signAt_def, signAt_def, connectedSum_def,
    List.getElem?_append_left (by simpa using hk), List.getElem?_map, Option.map_map]
  rfl

/-- The letters of `w₂` keep their sign in the connected sum. -/
@[simp]
theorem signAt_connectedSum_add (k : ℕ) :
    (w₁.connectedSum w₂).signAt (w₁.length + k) = w₂.signAt k := by
  rw [signAt_def, signAt_def, connectedSum_def,
    List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left,
    List.getElem?_map, Option.map_map]
  rfl

/-- A letter of `w₁` lies on a level below `n`. -/
private theorem exists_levelAt_eq_some_lt {k : ℕ} (hk : k < w₁.length) :
    ∃ l < n, w₁.levelAt k = some l :=
  ⟨_, by have := (w₁[k]).1.isLt; omega, w₁.levelAt_of_lt hk⟩

/-! ### The loops of a connected sum -/

/-- The letters at positions at least `w₁.length` come from `w₂`, on levels at least `n`. -/
private theorem levelAt_connectedSum_ne_of_lt_of_le {j k : ℕ} (hj : j < w₁.length)
    (hk : w₁.length ≤ k) : (w₁.connectedSum w₂).levelAt k ≠ (w₁.connectedSum w₂).levelAt j := by
  obtain ⟨l, hl, hjl⟩ := exists_levelAt_eq_some_lt w₁ hj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [levelAt_connectedSum_of_lt w₁ w₂ hj, hjl, levelAt_connectedSum_add]
  cases w₂.levelAt k <;> simp
  omega

/-- The two bands of a loop are in order. -/
private theorem IsSeifertLoop.fst_lt_snd {k : ℕ} {w : BraidWord k} {p : ℕ × ℕ}
    (h : w.IsSeifertLoop p) : p.1 < p.2 :=
  (w.isSeifertLoop_iff.1 h).1

/-- The first band of a loop is a letter of the word. -/
private theorem IsSeifertLoop.fst_lt_length {k : ℕ} {w : BraidWord k} {p : ℕ × ℕ}
    (h : w.IsSeifertLoop p) : p.1 < w.length :=
  (w.isSeifertLoop_iff.1 h).1.trans (w.isSeifertLoop_iff.1 h).2.1

/-- A loop of the connected sum starting in `w₁` is a loop of `w₁`. -/
theorem isSeifertLoop_connectedSum_iff_of_lt {p : ℕ × ℕ} (hp : p.1 < w₁.length) :
    (w₁.connectedSum w₂).IsSeifertLoop p ↔ w₁.IsSeifertLoop p := by
  have hlen : List.length (w₁.connectedSum w₂) = w₁.length + w₂.length :=
    length_connectedSum w₁ w₂
  simp only [isSeifertLoop_iff, hlen]
  constructor
  · rintro ⟨h12, -, hl, hbetween⟩
    have h2 : p.2 < w₁.length := by
      by_contra h
      exact levelAt_connectedSum_ne_of_lt_of_le w₁ w₂ hp (not_lt.1 h) hl
    rw [levelAt_connectedSum_of_lt w₁ w₂ h2, levelAt_connectedSum_of_lt w₁ w₂ hp] at hl
    refine ⟨h12, h2, hl, fun k hk hk' ↦ ?_⟩
    have := hbetween k hk hk'
    rwa [levelAt_connectedSum_of_lt w₁ w₂ (hk.trans h2),
      levelAt_connectedSum_of_lt w₁ w₂ hp] at this
  · rintro ⟨h12, h2, hl, hbetween⟩
    refine ⟨h12, by omega, ?_, fun k hk hk' ↦ ?_⟩
    · rwa [levelAt_connectedSum_of_lt w₁ w₂ h2, levelAt_connectedSum_of_lt w₁ w₂ hp]
    · rw [levelAt_connectedSum_of_lt w₁ w₂ (hk.trans h2), levelAt_connectedSum_of_lt w₁ w₂ hp]
      exact hbetween k hk hk'

/-- The loops of the connected sum starting in `w₂` are the loops of `w₂`, moved past `w₁`. -/
theorem isSeifertLoop_connectedSum_add_iff (p : ℕ × ℕ) :
    (w₁.connectedSum w₂).IsSeifertLoop (w₁.length + p.1, w₁.length + p.2) ↔
      w₂.IsSeifertLoop p := by
  have hinj : Function.Injective (Option.map (n + ·)) :=
    Option.map_injective (add_right_injective n)
  have hlen : List.length (w₁.connectedSum w₂) = w₁.length + w₂.length :=
    length_connectedSum w₁ w₂
  simp only [isSeifertLoop_iff, levelAt_connectedSum_add, hinj.eq_iff, hlen, add_lt_add_iff_left]
  refine and_congr_right fun h12 ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · intro h k hk hk'
    have := h (w₁.length + k) (by omega) (by omega)
    rwa [levelAt_connectedSum_add, hinj.ne_iff] at this
  · intro h k hk hk'
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : w₁.length ≤ k)
    rw [levelAt_connectedSum_add, hinj.ne_iff]
    exact h _ (by omega) (by omega)

/-- **The basis loops of a connected sum** are those of the two summands: a loop of `w₁` is a loop
of the connected sum as it stands, and a loop of `w₂` is moved past the letters of `w₁`. -/
def seifertLoopsConnectedSumEquiv :
    w₁.seifertLoops ⊕ w₂.seifertLoops ≃ (w₁.connectedSum w₂).seifertLoops where
  toFun := Sum.elim
    (fun a ↦ ⟨a.1, (mem_seifertLoops _).2 <|
      (isSeifertLoop_connectedSum_iff_of_lt w₁ w₂
        ((mem_seifertLoops _).1 a.2).fst_lt_length).2 ((mem_seifertLoops _).1 a.2)⟩)
    (fun b ↦ ⟨(w₁.length + b.1.1, w₁.length + b.1.2), (mem_seifertLoops _).2 <|
      (isSeifertLoop_connectedSum_add_iff w₁ w₂ b.1).2 ((mem_seifertLoops _).1 b.2)⟩)
  invFun p :=
    if h : (p : ℕ × ℕ).1 < w₁.length then
      .inl ⟨p, (mem_seifertLoops _).2 <|
        (isSeifertLoop_connectedSum_iff_of_lt w₁ w₂ h).1 ((mem_seifertLoops _).1 p.2)⟩
    else
      .inr ⟨((p : ℕ × ℕ).1 - w₁.length, (p : ℕ × ℕ).2 - w₁.length), (mem_seifertLoops _).2 <| by
        have hp := (mem_seifertLoops _).1 p.2
        have h12 : (p : ℕ × ℕ).1 < (p : ℕ × ℕ).2 := hp.fst_lt_snd
        have e : (w₁.length + ((p : ℕ × ℕ).1 - w₁.length),
            w₁.length + ((p : ℕ × ℕ).2 - w₁.length)) = (p : ℕ × ℕ) :=
          Prod.ext (by dsimp only; omega) (by dsimp only; omega)
        rw [← isSeifertLoop_connectedSum_add_iff w₁ w₂]
        dsimp only
        rwa [e]⟩
  left_inv x := by
    rcases x with a | b
    · simp [((mem_seifertLoops _).1 a.2).fst_lt_length]
    · simp
  right_inv := by
    rintro ⟨⟨a, b⟩, hp⟩
    by_cases h : a < w₁.length
    · simp [h]
    · have h12 : a < b := ((mem_seifertLoops _).1 hp).fst_lt_snd
      simp only [h, dite_false, Sum.elim_inr, Subtype.mk.injEq, Prod.mk.injEq]
      omega

/-- A loop of `w₁` is the same pair of positions in the connected sum. -/
@[simp]
theorem seifertLoopsConnectedSumEquiv_inl (a : w₁.seifertLoops) :
    (seifertLoopsConnectedSumEquiv w₁ w₂ (.inl a) : ℕ × ℕ) = a :=
  (rfl)

/-- A loop of `w₂` is moved past the letters of `w₁` in the connected sum. -/
@[simp]
theorem seifertLoopsConnectedSumEquiv_inr (b : w₂.seifertLoops) :
    (seifertLoopsConnectedSumEquiv w₁ w₂ (.inr b) : ℕ × ℕ) =
      (w₁.length + b.1.1, w₁.length + b.1.2) :=
  (rfl)

/-! ### The Seifert matrix of a connected sum -/

/-- **The Seifert matrix of a connected sum of closed braids is block diagonal**: in the basis of
loops of the two summands, it is the block diagonal matrix of their Seifert matrices. Loops from
different summands do not link, since their bands do not interleave along the word. -/
theorem submatrix_seifertMatrix_connectedSum :
    (w₁.connectedSum w₂).seifertMatrix.submatrix (seifertLoopsConnectedSumEquiv w₁ w₂)
        (seifertLoopsConnectedSumEquiv w₁ w₂) =
      Matrix.fromBlocks w₁.seifertMatrix 0 0 w₂.seifertMatrix := by
  have hinj : Function.Injective (Option.map (n + ·)) :=
    Option.map_injective (add_right_injective n)
  have hsucc (y : Option ℕ) :
      Option.map (· + 1) (Option.map (n + ·) y) = Option.map (n + ·) (Option.map (· + 1) y) := by
    cases y <;> simp [Nat.add_assoc]
  have hlt₁ (a : w₁.seifertLoops) : a.1.1 < w₁.length ∧ a.1.2 < w₁.length :=
    ⟨((mem_seifertLoops _).1 a.2).fst_lt_length,
      (w₁.isSeifertLoop_iff.1 ((mem_seifertLoops _).1 a.2)).2.1⟩
  have hlevel₂ (b : w₂.seifertLoops) : ∃ l, w₂.levelAt b.1.1 = some l :=
    ⟨_, w₂.levelAt_of_lt ((mem_seifertLoops _).1 b.2).fst_lt_length⟩
  ext (a | a) (b | b)
  · -- two loops of `w₁` keep their letters
    obtain ⟨ha₁, ha₂⟩ := hlt₁ a
    obtain ⟨hb₁, hb₂⟩ := hlt₁ b
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, seifertMatrix_apply,
      Subtype.ext_iff, seifertLoopsConnectedSumEquiv_inl, levelAt_connectedSum_of_lt w₁ w₂ ha₁,
      levelAt_connectedSum_of_lt w₁ w₂ hb₁, signAt_connectedSum_of_lt w₁ w₂ ha₁,
      signAt_connectedSum_of_lt w₁ w₂ ha₂]
  · -- a loop of `w₁` lies below every loop of `w₂`
    obtain ⟨ha₁, -⟩ := hlt₁ a
    obtain ⟨l, hl, hal⟩ := exists_levelAt_eq_some_lt w₁ ha₁
    obtain ⟨l', hbl⟩ := hlevel₂ b
    have hab : ¬ (a : ℕ × ℕ) = (w₁.length + b.1.1, w₁.length + b.1.2) := fun h ↦ by
      have := congrArg Prod.fst h
      dsimp only at this
      omega
    have h₁ : ¬ l = n + l' := by omega
    have h₂ : ¬ l = n + l' + 1 := by omega
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      seifertMatrix_apply, Subtype.ext_iff, seifertLoopsConnectedSumEquiv_inl,
      seifertLoopsConnectedSumEquiv_inr, levelAt_connectedSum_of_lt w₁ w₂ ha₁,
      levelAt_connectedSum_add, hal, hbl, hab, h₁, h₂, Option.map_some, Option.some_inj,
      ite_false]
  · -- a loop of `w₂` meets no loop of `w₁`, whose bands all come first
    obtain ⟨hb₁, hb₂⟩ := hlt₁ b
    obtain ⟨l, hl, hbl⟩ := exists_levelAt_eq_some_lt w₁ hb₁
    obtain ⟨l', hal⟩ := hlevel₂ a
    have hab : ¬ (w₁.length + a.1.1, w₁.length + a.1.2) = (b : ℕ × ℕ) := fun h ↦ by
      have := congrArg Prod.fst h
      dsimp only at this
      omega
    have h₁ : ¬ n + l' = l := by omega
    have h₂ : ¬ w₁.length + a.1.1 < b.1.2 := by omega
    have h₃ : ¬ w₁.length + a.1.1 < b.1.1 := by omega
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
      seifertMatrix_apply, Subtype.ext_iff, seifertLoopsConnectedSumEquiv_inl,
      seifertLoopsConnectedSumEquiv_inr, levelAt_connectedSum_of_lt w₁ w₂ hb₁,
      levelAt_connectedSum_add, hal, hbl, hab, h₁, h₂, h₃, Option.map_some, Option.some_inj,
      ite_false, false_and, and_false, ite_self]
  · -- two loops of `w₂` are moved together
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, seifertMatrix_apply,
      Subtype.ext_iff, seifertLoopsConnectedSumEquiv_inr, levelAt_connectedSum_add,
      signAt_connectedSum_add, hinj.eq_iff, hsucc, Prod.ext_iff, add_right_inj,
      add_lt_add_iff_left]

/-- **The Tristram–Levine signature is additive under connected sum of closed braids.** -/
theorem tristramLevineSignature_seifertMatrix_connectedSum (ω : ℂ) :
    tristramLevineSignature ((w₁.connectedSum w₂).seifertMatrix.map ((↑) : ℤ → ℝ)) ω =
      tristramLevineSignature (w₁.seifertMatrix.map ((↑) : ℤ → ℝ)) ω +
        tristramLevineSignature (w₂.seifertMatrix.map ((↑) : ℤ → ℝ)) ω := by
  rw [← tristramLevineSignature_submatrix_equiv_self (seifertLoopsConnectedSumEquiv w₁ w₂).symm,
    Equiv.symm_symm, Matrix.submatrix_map, submatrix_seifertMatrix_connectedSum,
    Matrix.fromBlocks_map, Matrix.map_zero _ Int.cast_zero, Matrix.map_zero _ Int.cast_zero,
    tristramLevineSignature_fromBlocks_zero]

/-- **The Alexander polynomial is multiplicative under connected sum of closed braids**, when the
canonical Seifert surfaces of the summands have even rank `2 * g₁` and `2 * g₂`, as for knots. -/
theorem alexander_seifertMatrix_connectedSum {g₁ g₂ : ℕ} (h₁ : w₁.seifertLoops.card = 2 * g₁)
    (h₂ : w₂.seifertLoops.card = 2 * g₂) :
    alexander (w₁.connectedSum w₂).seifertMatrix =
      alexander w₁.seifertMatrix * alexander w₂.seifertMatrix := by
  rw [← Matrix.alexander_submatrix_equiv_self _ (seifertLoopsConnectedSumEquiv w₁ w₂),
    submatrix_seifertMatrix_connectedSum, alexander_fromBlocks_zero _ _ (by simpa using h₁)
      (by simpa using h₂)]

end BraidWord

namespace MarkovBraid

open BraidWord

/-- **The Tristram–Levine signature is additive under connected sum of braids**: the closure of
the connected sum of two braid words has the sum of the signatures of their closures. -/
theorem tristramLevineSignature_mk_connectedSum {n m : ℕ} (w₁ : BraidWord (n + 1))
    (w₂ : BraidWord (m + 1)) (ω : ℂ) :
    tristramLevineSignature ⟨n + m, (w₁.connectedSum w₂).toBraid⟩ ω =
      tristramLevineSignature ⟨n, w₁.toBraid⟩ ω + tristramLevineSignature ⟨m, w₂.toBraid⟩ ω := by
  simp only [tristramLevineSignature_mk, tristramLevineSignature_seifertMatrix_connectedSum]

end MarkovBraid

/-! ### The granny knot and the square knot -/

namespace BraidWord

open KnotTheory LaurentPolynomial

/-- The canonical Seifert surface of the closure of `σ₀³` has two basis loops. -/
private theorem card_seifertLoops_trefoil :
    (seifertLoops (n := 2) [(0, 1), (0, 1), (0, 1)]).card = 2 * 1 := by
  obtain ⟨e, -⟩ := seifertMatrix_trefoil
  simpa using (Fintype.card_congr e).symm

/-- The canonical Seifert surface of the closure of `σ₀⁻³` has two basis loops. -/
private theorem card_seifertLoops_mirrorTrefoil :
    (seifertLoops (n := 2) [(0, -1), (0, -1), (0, -1)]).card = 2 * 1 := by
  obtain ⟨e, -⟩ := seifertMatrix_mirrorTrefoil
  simpa using (Fintype.card_congr e).symm

/-- The granny knot, the closure of `σ₀³ σ₁³`, has Alexander polynomial `(t - 1 + t⁻¹)²`. -/
theorem alexander_seifertMatrix_granny :
    alexander (connectedSum (n := 1) (m := 1) [(0, 1), (0, 1), (0, 1)]
      [(0, 1), (0, 1), (0, 1)]).seifertMatrix = (T 1 - 1 + T (-1)) ^ 2 := by
  have h := card_seifertLoops_trefoil
  rw [alexander_seifertMatrix_connectedSum (g₁ := 1) (g₂ := 1) _ _ h h,
    alexander_seifertMatrix_trefoil, sq]

/-- The square knot, the closure of `σ₀³ σ₁⁻³`, has the same Alexander polynomial
`(t - 1 + t⁻¹)²` as the granny knot. -/
theorem alexander_seifertMatrix_square :
    alexander (connectedSum (n := 1) (m := 1) [(0, 1), (0, 1), (0, 1)]
      [(0, -1), (0, -1), (0, -1)]).seifertMatrix = (T 1 - 1 + T (-1)) ^ 2 := by
  rw [alexander_seifertMatrix_connectedSum (g₁ := 1) (g₂ := 1) _ _ card_seifertLoops_trefoil
    card_seifertLoops_mirrorTrefoil, alexander_seifertMatrix_trefoil,
    alexander_seifertMatrix_mirrorTrefoil, sq]

end BraidWord

open BraidGroup BraidWord KnotTheory in
/-- **The granny knot and the square knot are not Markov equivalent.** The braid `σ₀³ σ₁³` closes
to the granny knot, the connected sum of two right-handed trefoils, and `σ₀³ σ₁⁻³` to the square
knot, the connected sum of a right-handed and a left-handed trefoil. By additivity their
Tristram–Levine signatures at `ω = -1` are `-2 - 2 = -4` and `-2 + 2 = 0`, whereas their
Alexander polynomials agree, both being `(t - 1 + t⁻¹)²`
(`TauCeti.BraidWord.alexander_seifertMatrix_granny`,
`TauCeti.BraidWord.alexander_seifertMatrix_square`). -/
theorem not_markovEquiv_granny_square :
    ¬ MarkovEquiv ⟨2, sigma 0 ^ 3 * sigma 1 ^ 3⟩ ⟨2, sigma 0 ^ 3 * (sigma 1)⁻¹ ^ 3⟩ := fun h ↦ by
  let r : BraidWord 2 := [(0, 1), (0, 1), (0, 1)]
  let l : BraidWord 2 := [(0, -1), (0, -1), (0, -1)]
  -- The connected sums of these explicit words compute by `rfl`.
  have hgranny : (r.connectedSum r).toBraid = sigma 0 ^ 3 * sigma 1 ^ 3 := by
    rw [show r.connectedSum r = [(0, 1), (0, 1), (0, 1), (1, 1), (1, 1), (1, 1)] from (rfl)]
    simp only [toBraid_cons, toBraid_nil, Units.val_one, zpow_one, mul_one, pow_succ, pow_zero,
      one_mul, mul_assoc]
  have hsquare : (r.connectedSum l).toBraid = sigma 0 ^ 3 * (sigma 1)⁻¹ ^ 3 := by
    rw [show r.connectedSum l = [(0, 1), (0, 1), (0, 1), (1, -1), (1, -1), (1, -1)] from (rfl)]
    simp only [toBraid_cons, toBraid_nil, Units.val_one, Units.val_neg, zpow_one, zpow_neg,
      mul_one, pow_succ, pow_zero, one_mul, mul_assoc]
  have := h.tristramLevineSignature_eq (-1)
  rw [← hgranny, ← hsquare, MarkovBraid.tristramLevineSignature_mk_connectedSum r r,
    MarkovBraid.tristramLevineSignature_mk_connectedSum r l] at this
  have hr : MarkovBraid.tristramLevineSignature ⟨1, r.toBraid⟩ (-1) = -2 := by
    rw [MarkovBraid.tristramLevineSignature_mk, tristramLevineSignature_neg_one,
      signature_seifertMatrix_trefoil]
  have hl : MarkovBraid.tristramLevineSignature ⟨1, l.toBraid⟩ (-1) = 2 := by
    rw [MarkovBraid.tristramLevineSignature_mk, tristramLevineSignature_neg_one,
      signature_seifertMatrix_mirrorTrefoil]
  rw [hr, hl] at this
  omega

end TauCeti
