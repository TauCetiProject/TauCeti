/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Supporting
public import TauCeti.Logic.Function.Extend

/-!
# Integer-indexed height sequences

A two-sided height sequence `h : ℤ → WithTop ℝ` takes real values on an integer interval and
the value infinity outside it. As for one-sided sequences, it is convex when its finite domain
is order connected and its second differences are nonnegative wherever they are defined. The
finite domain may now be unbounded in both directions, so a genuinely two-sided sequence has no
first point, and no construction walking along the polygon from a first vertex applies to it.

Convexity is local, so a two-sided sequence is convex exactly when each of its one-sided tails
`n ↦ h (k + n)`, for `k : ℤ`, is a convex height sequence on `ℕ`. This transfers the discrete
geometry of one-sided sequences: the affine line through a finite edge lies below the whole
sequence, least upper bounds of convex sequences are convex, and so every sequence with a real
affine lower bound on all of `ℤ` has a greatest convex minorant, its lower convex envelope.
Conversely, a sequence with a lower convex envelope is admissible, since a convex sequence is.
The total function `intLowerConvexEnvelope a` takes the all-infinite fallback on inadmissible
input; that fallback is not an envelope of the input.

Admissibility on `ℤ` is genuinely stronger than on each tail. The heights `-|n|` have no real
affine lower bound on `ℤ`, although their restriction to `ℕ`, the affine heights `-n`, is
convex; the heights `|n|` are convex on `ℤ`.

Extending a one-sided sequence by infinity at the negative indices preserves and reflects
convexity and admissibility, and commutes with taking lower convex envelopes and supporting
values. Translating the indices by an integer translates the envelope, and shifts supporting
values by the corresponding affine term. Hence the envelope of a two-sided sequence whose finite
domain is bounded below is obtained from the one-sided construction for the tail starting at any
lower bound.

The supporting value `intSupportingValue a σ` is the extended-real infimum of the tilted heights
`a n - σ n` over `n : ℤ`. A real intercept lies below it exactly when the corresponding affine
line lies below the sequence, and an admissible sequence and its envelope have the same
supporting values.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace TauCeti

/-! ### Convex two-sided height sequences -/

/-- A two-sided height sequence is convex if its finite domain is order connected and its
second differences are nonnegative wherever the two outer heights are finite. The all-infinite
sequence and a sequence with just one finite height are allowed. -/
structure IsIntConvexSeq (h : ℤ → WithTop ℝ) : Prop where
  /-- Every index between two finite heights has finite height. -/
  ordConnected : Set.OrdConnected {n | h n ≠ ⊤}
  /-- The middle of three consecutive heights with finite ends lies below their average. -/
  two_mul_le : ∀ n, h n ≠ ⊤ → h (n + 2) ≠ ⊤ →
    2 * (h (n + 1)).untop₀ ≤ (h n).untop₀ + (h (n + 2)).untop₀

variable {a b h : ℤ → WithTop ℝ}

/-- A two-sided height sequence is convex exactly when each of its one-sided tails is a convex
height sequence. -/
theorem isIntConvexSeq_iff_forall_isConvexSeq :
    IsIntConvexSeq h ↔ ∀ k : ℤ, IsConvexSeq fun n : ℕ => h (k + n) := by
  refine ⟨fun hh k => isConvexSeq_iff_two_mul_le.mpr ⟨⟨fun i hi j hj l hl => ?_⟩,
    fun n hn hn₂ => ?_⟩, fun hh => ⟨⟨fun i hi j hj l hl => ?_⟩, fun n hn hn₂ => ?_⟩⟩
  · exact hh.ordConnected.out hi hj ⟨by have := hl.1; omega, by have := hl.2; omega⟩
  · have e₁ : k + ((n + 1 : ℕ) : ℤ) = k + n + 1 := by push_cast; ring
    have e₂ : k + ((n + 2 : ℕ) : ℤ) = k + n + 2 := by push_cast; ring
    rw [e₂] at hn₂
    rw [e₁, e₂]
    exact hh.two_mul_le (k + n) hn hn₂
  · -- Read the three indices in the tail starting at `i`.
    have key {m : ℤ} (hm : i ≤ m) : h (i + ((m - i).toNat : ℕ)) = h m := by
      congr 1
      omega
    have hi' : h (i + ((0 : ℕ) : ℤ)) ≠ ⊤ := by simpa using hi
    have hj' : h (i + ((j - i).toNat : ℕ)) ≠ ⊤ := by rwa [key (hl.1.trans hl.2)]
    have hl' : (l - i).toNat ∈ Set.Icc 0 (j - i).toNat := ⟨Nat.zero_le _, by have := hl.2; omega⟩
    have := (hh i).ordConnected.out hi' hj' hl'
    rwa [Set.mem_ofPred_eq, key hl.1] at this
  · have := (isConvexSeq_iff_two_mul_le.mp (hh n)).2 0 (by simpa using hn) (by simpa using hn₂)
    simpa using this

/-- Each one-sided tail of a convex two-sided height sequence is convex. -/
theorem IsIntConvexSeq.isConvexSeq (hh : IsIntConvexSeq h) (k : ℤ) :
    IsConvexSeq fun n : ℕ => h (k + n) :=
  isIntConvexSeq_iff_forall_isConvexSeq.mp hh k

/-- Translating the indices preserves convexity. -/
theorem IsIntConvexSeq.comp_add_right (hh : IsIntConvexSeq h) (k : ℤ) :
    IsIntConvexSeq fun n => h (n + k) :=
  isIntConvexSeq_iff_forall_isConvexSeq.mpr fun j => by
    simpa only [add_right_comm] using hh.isConvexSeq (j + k)

/-- Translating the indices does not change convexity. -/
@[simp]
theorem isIntConvexSeq_comp_add_right_iff (k : ℤ) :
    IsIntConvexSeq (fun n => h (n + k)) ↔ IsIntConvexSeq h :=
  ⟨fun hh => by simpa using hh.comp_add_right (-k), fun hh => hh.comp_add_right k⟩

/-- The all-infinite two-sided sequence, representing the empty polygon, is convex. -/
@[simp]
theorem isIntConvexSeq_top : IsIntConvexSeq (⊤ : ℤ → WithTop ℝ) :=
  isIntConvexSeq_iff_forall_isConvexSeq.mpr fun _ => isConvexSeq_top

/-- Real affine heights form a convex sequence on the whole integer line. -/
theorem isIntConvexSeq_affine (c m : ℝ) :
    IsIntConvexSeq fun n : ℤ => ((c + m * n : ℝ) : WithTop ℝ) :=
  isIntConvexSeq_iff_forall_isConvexSeq.mpr fun k => by
    convert isConvexSeq_affine (c + m * k) m using 3
    push_cast
    ring

/-- The affine line through a finite edge of a convex two-sided sequence lies below the whole
sequence, including indices outside its finite domain. -/
theorem IsIntConvexSeq.supportingLine_le (hh : IsIntConvexSeq h) {p : ℤ} (hp : h p ≠ ⊤)
    (hp' : h (p + 1) ≠ ⊤) (n : ℤ) :
    (((h p).untop₀ + ((n : ℝ) - p) * ((h (p + 1)).untop₀ - (h p).untop₀) : ℝ) : WithTop ℝ) ≤
      h n := by
  -- Read the edge and the index `n` in the tail starting at `min n p`.
  set k := min n p
  have key {m : ℤ} (hm : k ≤ m) : h (k + ((m - k).toNat : ℕ)) = h m := by
    congr 1
    omega
  have cast {m : ℤ} (hm : k ≤ m) : (((m - k).toNat : ℕ) : ℝ) = (m : ℝ) - k := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_sub]
  have hkp : k ≤ p := min_le_right n p
  have hkp' : k ≤ p + 1 := by omega
  have hkn : k ≤ n := min_le_left n p
  have hsucc : (p - k).toNat + 1 = (p + 1 - k).toNat := by omega
  have := (hh.isConvexSeq k).supportingLine_le (n := (p - k).toNat) (by rwa [key hkp])
    (by rwa [hsucc, key hkp']) (n - k).toNat
  rw [unitSlope_def, hsucc, key hkp, key hkp', key hkn, cast hkp, cast hkn] at this
  convert this using 3
  ring

/-! ### Admissibility -/

/-- A two-sided height sequence is admissible if it has a real affine lower bound on all of
`ℤ`. This is the existence condition for a lower convex envelope; the all-infinite sequence is
admissible. -/
def IsIntAdmissible (a : ℤ → WithTop ℝ) : Prop :=
  ∃ c m : ℝ, ∀ n : ℤ, ((c + m * n : ℝ) : WithTop ℝ) ≤ a n

/-- Admissibility is the existence of a real affine lower bound. -/
theorem isIntAdmissible_iff :
    IsIntAdmissible a ↔ ∃ c m : ℝ, ∀ n : ℤ, ((c + m * n : ℝ) : WithTop ℝ) ≤ a n := Iff.rfl

/-- The empty point set is admissible. -/
@[simp]
theorem isIntAdmissible_top : IsIntAdmissible (⊤ : ℤ → WithTop ℝ) :=
  ⟨0, 0, fun _ => le_top⟩

/-- A sequence lying above an admissible sequence is admissible. -/
theorem IsIntAdmissible.mono (hb : IsIntAdmissible b) (hba : b ≤ a) : IsIntAdmissible a :=
  let ⟨c, m, hcm⟩ := hb
  ⟨c, m, fun n => (hcm n).trans (hba n)⟩

/-- Every convex two-sided height sequence has a real affine lower bound, including the empty
and singleton cases. -/
theorem IsIntConvexSeq.isIntAdmissible (hh : IsIntConvexSeq h) : IsIntAdmissible h := by
  by_cases hedge : ∃ p, h p ≠ ⊤ ∧ h (p + 1) ≠ ⊤
  · obtain ⟨p, hp, hp'⟩ := hedge
    exact ⟨(h p).untop₀ - p * ((h (p + 1)).untop₀ - (h p).untop₀),
      (h (p + 1)).untop₀ - (h p).untop₀, fun n => by
        convert hh.supportingLine_le hp hp' n using 2
        ring⟩
  by_cases hfin : ∃ p, h p ≠ ⊤
  · -- Without a finite edge, the finite domain is a single point.
    obtain ⟨p, hp⟩ := hfin
    push Not at hedge
    refine ⟨(h p).untop₀, 0, fun n => ?_⟩
    by_cases hn : h n = ⊤
    · simp [hn]
    obtain rfl : n = p := by
      by_contra hnp
      rcases lt_or_gt_of_ne hnp with hlt | hlt
      · exact hh.ordConnected.out hn hp ⟨by omega, by omega⟩ (hedge n hn)
      · exact hh.ordConnected.out hp hn ⟨by omega, by omega⟩ (hedge p hp)
    simp [WithTop.coe_untop₀_of_ne_top hn]
  · push Not at hfin
    exact ⟨0, 0, fun n => by simp [hfin n]⟩

/-- A two-sided sequence has a convex minorant exactly when it is admissible. -/
theorem exists_isIntConvexSeq_le_iff :
    (∃ h : ℤ → WithTop ℝ, IsIntConvexSeq h ∧ h ≤ a) ↔ IsIntAdmissible a :=
  ⟨fun ⟨_, hh, hha⟩ => hh.isIntAdmissible.mono hha,
    fun ⟨c, m, hcm⟩ => ⟨_, isIntConvexSeq_affine c m, hcm⟩⟩

/-- Translating the indices does not change admissibility. -/
@[simp]
theorem isIntAdmissible_comp_add_right_iff (k : ℤ) :
    IsIntAdmissible (fun n => a (n + k)) ↔ IsIntAdmissible a := by
  simp only [← exists_isIntConvexSeq_le_iff]
  refine ⟨fun ⟨g, hg, hga⟩ => ⟨_, hg.comp_add_right (-k), fun n => ?_⟩,
    fun ⟨g, hg, hga⟩ => ⟨_, hg.comp_add_right k, fun n => hga (n + k)⟩⟩
  simpa using hga (n + -k)

/-! ### Extension by infinity at negative indices -/

/-- Extending a one-sided height sequence by infinity at the negative indices preserves and
reflects convexity. -/
@[simp]
theorem isIntConvexSeq_extend_iff {a : ℕ → WithTop ℝ} :
    IsIntConvexSeq (Function.extend ((↑) : ℕ → ℤ) a ⊤) ↔ IsConvexSeq a := by
  refine ⟨fun ha => by simpa [Nat.cast_injective.extend_apply] using ha.isConvexSeq 0,
    fun ha => ⟨⟨fun i hi j hj l hl => ?_⟩, fun n hn hn₂ => ?_⟩⟩
  · have hi₀ : 0 ≤ i := not_lt.mp fun h => hi (Function.extend_natCast_of_neg _ _ h)
    lift i to ℕ using hi₀
    lift j to ℕ using (Int.natCast_nonneg i).trans (hl.1.trans hl.2)
    lift l to ℕ using (Int.natCast_nonneg i).trans hl.1
    simp only [Set.mem_ofPred_eq, Nat.cast_injective.extend_apply] at hi hj ⊢
    exact ha.ordConnected.out hi hj ⟨by exact_mod_cast hl.1, by exact_mod_cast hl.2⟩
  · have hn₀ : 0 ≤ n := not_lt.mp fun h => hn (Function.extend_natCast_of_neg _ _ h)
    lift n to ℕ using hn₀
    have e₁ : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    have e₂ : (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [e₂, Nat.cast_injective.extend_apply] at hn₂
    rw [e₁, e₂, Nat.cast_injective.extend_apply, Nat.cast_injective.extend_apply,
      Nat.cast_injective.extend_apply]
    rw [Nat.cast_injective.extend_apply] at hn
    exact (isConvexSeq_iff_two_mul_le.mp ha).2 n hn hn₂

/-- Extending a one-sided height sequence by infinity at the negative indices preserves and
reflects admissibility. -/
@[simp]
theorem isIntAdmissible_extend_iff {a : ℕ → WithTop ℝ} :
    IsIntAdmissible (Function.extend ((↑) : ℕ → ℤ) a ⊤) ↔ IsAdmissible a := by
  refine ⟨fun ⟨c, m, hcm⟩ => isAdmissible_iff.mpr ⟨c, m, fun n => ?_⟩,
    fun ha => ?_⟩
  · simpa [Nat.cast_injective.extend_apply] using hcm n
  obtain ⟨c, m, hcm⟩ := isAdmissible_iff.mp ha
  refine ⟨c, m, fun n => ?_⟩
  · rcases lt_or_ge n 0 with hn | hn
    · simp [Function.extend_natCast_of_neg _ _ hn]
    · lift n to ℕ using hn
      simpa [Nat.cast_injective.extend_apply] using hcm n

/-! ### Lower convex envelopes -/

/-- A least upper bound of a family of convex two-sided height sequences is convex. -/
theorem IsIntConvexSeq.of_isLUB {S : Set (ℤ → WithTop ℝ)} (hS : ∀ g ∈ S, IsIntConvexSeq g)
    (hh : IsLUB S h) : IsIntConvexSeq h := by
  refine isIntConvexSeq_iff_forall_isConvexSeq.mpr fun k =>
    IsConvexSeq.of_isLUB (S := (fun g n => g (k + n)) '' S) ?_ (isLUB_pi.mpr fun n => ?_)
  · rintro _ ⟨g, hg, rfl⟩
    exact (hS g hg).isConvexSeq k
  · rw [Set.image_image]
    exact isLUB_pi.mp hh (k + n)

/-- `h` is the lower convex envelope of the two-sided sequence `a`: it is a convex minorant of
`a` that dominates every convex minorant of `a`. -/
structure IsIntLowerConvexEnvelope (a h : ℤ → WithTop ℝ) : Prop where
  /-- The envelope is convex. -/
  isIntConvexSeq : IsIntConvexSeq h
  /-- The envelope lies below the point heights. -/
  le : h ≤ a
  /-- The envelope dominates every convex minorant. -/
  greatest : ∀ ⦃g : ℤ → WithTop ℝ⦄, IsIntConvexSeq g → g ≤ a → g ≤ h

/-- Being the lower convex envelope means being the greatest convex minorant. -/
theorem isIntLowerConvexEnvelope_iff_isGreatest :
    IsIntLowerConvexEnvelope a h ↔ IsGreatest {g | IsIntConvexSeq g ∧ g ≤ a} h :=
  ⟨fun hh => ⟨⟨hh.isIntConvexSeq, hh.le⟩, fun _ hg => hh.greatest hg.1 hg.2⟩,
    fun hh => ⟨hh.1.1, hh.1.2, fun _ hg hga => hh.2 ⟨hg, hga⟩⟩⟩

namespace IsIntLowerConvexEnvelope

/-- The lower convex envelope of a two-sided sequence is unique. -/
theorem unique {g : ℤ → WithTop ℝ} (hh : IsIntLowerConvexEnvelope a h)
    (hg : IsIntLowerConvexEnvelope a g) : h = g :=
  (isIntLowerConvexEnvelope_iff_isGreatest.mp hh).unique
    (isIntLowerConvexEnvelope_iff_isGreatest.mp hg)

/-- A two-sided sequence with a lower convex envelope is admissible. -/
theorem isIntAdmissible (hh : IsIntLowerConvexEnvelope a h) : IsIntAdmissible a :=
  exists_isIntConvexSeq_le_iff.mp ⟨h, hh.isIntConvexSeq, hh.le⟩

/-- A convex two-sided sequence is its own lower convex envelope. -/
theorem of_isIntConvexSeq (hh : IsIntConvexSeq h) : IsIntLowerConvexEnvelope h h :=
  ⟨hh, le_rfl, fun _ _ hgh => hgh⟩

end IsIntLowerConvexEnvelope

open scoped Classical in
/-- The lower convex envelope of a two-sided height sequence, as a total function. For an
admissible sequence it is the pointwise supremum of all convex minorants. For an inadmissible
sequence it is the all-infinite fallback, which is not an envelope of that sequence. -/
noncomputable def intLowerConvexEnvelope (a : ℤ → WithTop ℝ) : ℤ → WithTop ℝ :=
  if IsIntAdmissible a then
    fun n => ⨆ g : {g : ℤ → WithTop ℝ // IsIntConvexSeq g ∧ g ≤ a}, g.1 n
  else ⊤

/-- The envelope of an inadmissible two-sided sequence is the all-infinite fallback. -/
theorem intLowerConvexEnvelope_of_not_isIntAdmissible (ha : ¬IsIntAdmissible a) :
    intLowerConvexEnvelope a = ⊤ := by
  rw [intLowerConvexEnvelope, ite_eq_right ha]

/-- An admissible two-sided sequence has `intLowerConvexEnvelope a` as its lower convex
envelope. -/
theorem isIntLowerConvexEnvelope_intLowerConvexEnvelope (ha : IsIntAdmissible a) :
    IsIntLowerConvexEnvelope a (intLowerConvexEnvelope a) := by
  obtain ⟨g₀, hg₀⟩ := exists_isIntConvexSeq_le_iff.mpr ha
  have : Nonempty {g : ℤ → WithTop ℝ // IsIntConvexSeq g ∧ g ≤ a} := ⟨⟨g₀, hg₀⟩⟩
  have hlub : IsLUB {g : ℤ → WithTop ℝ | IsIntConvexSeq g ∧ g ≤ a}
      (intLowerConvexEnvelope a) := by
    refine isLUB_pi.mpr fun n => ?_
    rw [intLowerConvexEnvelope, ite_eq_left ha, Set.image_eq_range]
    exact WithTop.isLUB_sSup' (Set.range_nonempty _)
  exact ⟨IsIntConvexSeq.of_isLUB (S := {g | IsIntConvexSeq g ∧ g ≤ a}) (fun g hg => hg.1)
    hlub, hlub.2 fun g hg => hg.2,
    fun g hg hga => hlub.1 ⟨hg, hga⟩⟩

/-- A lower convex envelope of a two-sided sequence exists exactly for admissible sequences. -/
theorem exists_isIntLowerConvexEnvelope_iff :
    (∃ h, IsIntLowerConvexEnvelope a h) ↔ IsIntAdmissible a :=
  ⟨fun ⟨_, hh⟩ => hh.isIntAdmissible,
    fun ha => ⟨_, isIntLowerConvexEnvelope_intLowerConvexEnvelope ha⟩⟩

/-- Any lower convex envelope of `a` is the total function `intLowerConvexEnvelope a`. -/
theorem IsIntLowerConvexEnvelope.eq_intLowerConvexEnvelope (hh : IsIntLowerConvexEnvelope a h) :
    h = intLowerConvexEnvelope a :=
  hh.unique (isIntLowerConvexEnvelope_intLowerConvexEnvelope hh.isIntAdmissible)

/-- For an admissible two-sided sequence, being its lower convex envelope is equality with
`intLowerConvexEnvelope a`. -/
theorem isIntLowerConvexEnvelope_iff_eq (ha : IsIntAdmissible a) :
    IsIntLowerConvexEnvelope a h ↔ h = intLowerConvexEnvelope a :=
  ⟨IsIntLowerConvexEnvelope.eq_intLowerConvexEnvelope,
    fun hh => hh ▸ isIntLowerConvexEnvelope_intLowerConvexEnvelope ha⟩

/-- The total envelope is convex, including the all-infinite fallback. -/
theorem isIntConvexSeq_intLowerConvexEnvelope (a : ℤ → WithTop ℝ) :
    IsIntConvexSeq (intLowerConvexEnvelope a) := by
  by_cases ha : IsIntAdmissible a
  · exact (isIntLowerConvexEnvelope_intLowerConvexEnvelope ha).isIntConvexSeq
  · rw [intLowerConvexEnvelope_of_not_isIntAdmissible ha]
    exact isIntConvexSeq_top

/-- The envelope of an admissible two-sided sequence lies below it. -/
theorem intLowerConvexEnvelope_le (ha : IsIntAdmissible a) : intLowerConvexEnvelope a ≤ a :=
  (isIntLowerConvexEnvelope_intLowerConvexEnvelope ha).le

/-- A convex minorant lies below the envelope. Admissibility is automatic. -/
theorem le_intLowerConvexEnvelope (hh : IsIntConvexSeq h) (hha : h ≤ a) :
    h ≤ intLowerConvexEnvelope a :=
  (isIntLowerConvexEnvelope_intLowerConvexEnvelope (hh.isIntAdmissible.mono hha)).greatest
    hh hha

/-- For an admissible two-sided sequence `a`, a convex sequence lies below the envelope of `a`
exactly when it lies below `a`. -/
theorem le_intLowerConvexEnvelope_iff (ha : IsIntAdmissible a) (hh : IsIntConvexSeq h) :
    h ≤ intLowerConvexEnvelope a ↔ h ≤ a :=
  ⟨fun hle => hle.trans (intLowerConvexEnvelope_le ha), le_intLowerConvexEnvelope hh⟩

/-- A convex two-sided sequence is its own lower convex envelope. -/
theorem IsIntConvexSeq.intLowerConvexEnvelope_eq (hh : IsIntConvexSeq h) :
    intLowerConvexEnvelope h = h :=
  (IsIntLowerConvexEnvelope.of_isIntConvexSeq hh).eq_intLowerConvexEnvelope.symm

/-- The envelope of the empty point set is the empty polygon. -/
@[simp]
theorem intLowerConvexEnvelope_top : intLowerConvexEnvelope (⊤ : ℤ → WithTop ℝ) = ⊤ :=
  isIntConvexSeq_top.intLowerConvexEnvelope_eq

/-- Taking the lower convex envelope of a two-sided sequence is idempotent. -/
@[simp]
theorem intLowerConvexEnvelope_idem (a : ℤ → WithTop ℝ) :
    intLowerConvexEnvelope (intLowerConvexEnvelope a) = intLowerConvexEnvelope a :=
  (isIntConvexSeq_intLowerConvexEnvelope a).intLowerConvexEnvelope_eq

/-- The envelope is monotone on admissible inputs. -/
theorem intLowerConvexEnvelope_mono (hb : IsIntAdmissible b) (hba : b ≤ a) :
    intLowerConvexEnvelope b ≤ intLowerConvexEnvelope a :=
  le_intLowerConvexEnvelope (isIntConvexSeq_intLowerConvexEnvelope b)
    ((intLowerConvexEnvelope_le hb).trans hba)

/-- Translating the indices of a two-sided sequence translates its envelope. -/
theorem intLowerConvexEnvelope_comp_add_right (a : ℤ → WithTop ℝ) (k : ℤ) :
    intLowerConvexEnvelope (fun n => a (n + k)) = fun n => intLowerConvexEnvelope a (n + k) := by
  by_cases ha : IsIntAdmissible a
  · refine (IsIntLowerConvexEnvelope.eq_intLowerConvexEnvelope
      ⟨(isIntConvexSeq_intLowerConvexEnvelope a).comp_add_right k,
        fun n => intLowerConvexEnvelope_le ha (n + k), fun g hg hga n => ?_⟩).symm
    have hle := le_intLowerConvexEnvelope (a := a) (hg.comp_add_right (-k))
      (fun m => by simpa using hga (m + -k))
    simpa using hle (n + k)
  · have ha' : ¬IsIntAdmissible fun n => a (n + k) := by
      rwa [isIntAdmissible_comp_add_right_iff]
    rw [intLowerConvexEnvelope_of_not_isIntAdmissible ha,
      intLowerConvexEnvelope_of_not_isIntAdmissible ha']
    rfl

/-- Extension by infinity at the negative indices commutes with taking lower convex envelopes.
For an inadmissible one-sided sequence both sides are the all-infinite fallback. -/
@[simp]
theorem intLowerConvexEnvelope_extend (a : ℕ → WithTop ℝ) :
    intLowerConvexEnvelope (Function.extend ((↑) : ℕ → ℤ) a ⊤) =
      Function.extend ((↑) : ℕ → ℤ) (lowerConvexEnvelope a) ⊤ := by
  by_cases ha : IsAdmissible a
  · refine (IsIntLowerConvexEnvelope.eq_intLowerConvexEnvelope
      ⟨isIntConvexSeq_extend_iff.mpr (isConvexSeq_lowerConvexEnvelope a), fun n => ?_,
        fun g hg hga n => ?_⟩).symm
    · rcases lt_or_ge n 0 with hn | hn
      · simp [Function.extend_natCast_of_neg _ _ hn]
      · lift n to ℕ using hn
        simpa [Nat.cast_injective.extend_apply] using lowerConvexEnvelope_le ha n
    · rcases lt_or_ge n 0 with hn | hn
      · simp [Function.extend_natCast_of_neg _ _ hn]
      · lift n to ℕ using hn
        have hle := le_lowerConvexEnvelope (a := a) (by simpa using hg.isConvexSeq 0)
          (fun m => by simpa [Nat.cast_injective.extend_apply] using hga m)
        simpa [Nat.cast_injective.extend_apply] using hle n
  · rw [intLowerConvexEnvelope_of_not_isIntAdmissible (by rwa [isIntAdmissible_extend_iff]),
      lowerConvexEnvelope_of_not_isAdmissible ha]
    funext n
    rcases lt_or_ge n 0 with hn | hn
    · simp [Function.extend_natCast_of_neg _ _ hn]
    · lift n to ℕ using hn
      simp [Nat.cast_injective.extend_apply]

/-- A two-sided sequence whose finite domain is bounded below by `k` has the envelope of its
one-sided tail from `k`, placed back at the indices from `k` and extended by infinity below. -/
theorem intLowerConvexEnvelope_eq_of_forall_lt {k : ℤ} (hk : ∀ n < k, a n = ⊤) (n : ℤ) :
    intLowerConvexEnvelope a n =
      Function.extend ((↑) : ℕ → ℤ) (lowerConvexEnvelope fun i : ℕ => a (k + i)) ⊤ (n - k) := by
  have ha : a = fun n => Function.extend ((↑) : ℕ → ℤ) (fun i : ℕ => a (k + i)) ⊤ (n + -k) := by
    funext n
    rcases lt_or_ge n k with hn | hn
    · rw [hk n hn, Function.extend_natCast_of_neg _ _ (by omega), Pi.top_apply]
    · obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = n + -k := ⟨(n + -k).toNat, by omega⟩
      rw [← hi, Nat.cast_injective.extend_apply]
      congr 1
      omega
  rw [sub_eq_add_neg]
  conv_lhs => rw [ha]
  rw [intLowerConvexEnvelope_comp_add_right, intLowerConvexEnvelope_extend]

/-! ### Supporting values -/

/-- The infimum of the tilted heights of a two-sided sequence at slope `σ`, as an extended
real. Missing heights contribute `⊤`; the value `⊥` means that no affine line of slope `σ` lies
below the sequence. -/
noncomputable def intSupportingValue (a : ℤ → WithTop ℝ) (σ : ℝ) : EReal :=
  ⨅ n : ℤ, (a n).toEReal - ((σ * n : ℝ) : EReal)

/-- The supporting value is the extended-real infimum of the tilted heights. -/
theorem intSupportingValue_def (a : ℤ → WithTop ℝ) (σ : ℝ) :
    intSupportingValue a σ = ⨅ n : ℤ, (a n).toEReal - ((σ * n : ℝ) : EReal) := (rfl)

/-- A lower bound on the supporting value is a lower bound on every tilted height. -/
theorem le_intSupportingValue_iff {r : EReal} {σ : ℝ} :
    r ≤ intSupportingValue a σ ↔ ∀ n : ℤ, r ≤ (a n).toEReal - ((σ * n : ℝ) : EReal) :=
  le_iInf_iff

/-- The supporting value lies below each tilted height. -/
theorem intSupportingValue_le (a : ℤ → WithTop ℝ) (σ : ℝ) (n : ℤ) :
    intSupportingValue a σ ≤ (a n).toEReal - ((σ * n : ℝ) : EReal) :=
  iInf_le _ n

/-- A real intercept lies below the supporting value exactly when its affine line lies below
every height. No admissibility assumption is needed. -/
theorem coe_le_intSupportingValue_iff {c σ : ℝ} :
    (c : EReal) ≤ intSupportingValue a σ ↔ ∀ n : ℤ, ((c + σ * n : ℝ) : WithTop ℝ) ≤ a n := by
  refine le_intSupportingValue_iff.trans (forall_congr' fun n => ?_)
  rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _)),
    ← EReal.coe_add, ← WithTop.toEReal_coe, WithTop.toEReal_le_toEReal_iff]

/-- Increasing the heights increases every supporting value. -/
theorem intSupportingValue_mono (hab : a ≤ b) (σ : ℝ) :
    intSupportingValue a σ ≤ intSupportingValue b σ :=
  iInf_mono fun n => EReal.sub_le_sub (WithTop.toEReal_le_toEReal_iff.mpr (hab n)) le_rfl

/-- The empty two-sided sequence has supporting value `⊤` at every slope. -/
@[simp]
theorem intSupportingValue_top (σ : ℝ) : intSupportingValue (⊤ : ℤ → WithTop ℝ) σ = ⊤ :=
  iInf_eq_top.mpr fun n => by rw [Pi.top_apply, WithTop.toEReal_top, EReal.top_sub_coe]

/-- A supporting value equals `⊤` exactly when the two-sided sequence is empty. -/
@[simp]
theorem intSupportingValue_eq_top_iff {σ : ℝ} : intSupportingValue a σ = ⊤ ↔ a = ⊤ := by
  refine ⟨fun hs => funext fun n => ?_, by rintro rfl; exact intSupportingValue_top σ⟩
  have hn := intSupportingValue_le a σ n
  rwa [hs, EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _)),
    EReal.top_add_coe, top_le_iff, WithTop.toEReal_eq_top_iff] at hn

/-- A supporting value is not `⊥` exactly when there is a real affine minorant with the
specified slope. -/
theorem intSupportingValue_ne_bot_iff {σ : ℝ} :
    intSupportingValue a σ ≠ ⊥ ↔ ∃ c : ℝ, ∀ n : ℤ, ((c + σ * n : ℝ) : WithTop ℝ) ≤ a n :=
  ⟨fun hs => ⟨_, coe_le_intSupportingValue_iff.mp (EReal.coe_toReal_le hs)⟩,
    fun ⟨c, hc⟩ => ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) (coe_le_intSupportingValue_iff.mpr hc)⟩

/-- The value `⊥` means that no real affine line of this slope lies below the two-sided
sequence. -/
theorem intSupportingValue_eq_bot_iff {σ : ℝ} :
    intSupportingValue a σ = ⊥ ↔ ∀ c : ℝ, ∃ n : ℤ, a n < ((c + σ * n : ℝ) : WithTop ℝ) := by
  rw [← not_iff_not]
  simp only [intSupportingValue_ne_bot_iff, not_forall, not_exists, not_lt]

/-- Admissibility means that at least one slope has supporting value above `⊥`. -/
theorem isIntAdmissible_iff_exists_intSupportingValue_ne_bot :
    IsIntAdmissible a ↔ ∃ σ : ℝ, intSupportingValue a σ ≠ ⊥ := by
  simp only [intSupportingValue_ne_bot_iff, isIntAdmissible_iff]
  exact exists_comm

/-- A lower convex envelope of a two-sided sequence has the same supporting values as the
sequence. -/
theorem IsIntLowerConvexEnvelope.intSupportingValue_eq (hh : IsIntLowerConvexEnvelope a h)
    (σ : ℝ) : intSupportingValue h σ = intSupportingValue a σ := by
  refine le_antisymm (intSupportingValue_mono hh.le σ) ?_
  by_contra hle
  obtain ⟨c, hc, hc'⟩ := EReal.exists_between_coe_real (lt_of_not_ge hle)
  have hminor := hh.greatest (isIntConvexSeq_affine c σ)
    (coe_le_intSupportingValue_iff.mp hc'.le)
  exact (not_le_of_gt hc) (coe_le_intSupportingValue_iff.mpr hminor)

/-- Taking the lower convex envelope of an admissible two-sided sequence preserves its
supporting-value function. -/
theorem intSupportingValue_intLowerConvexEnvelope (ha : IsIntAdmissible a) :
    intSupportingValue (intLowerConvexEnvelope a) = intSupportingValue a :=
  funext (isIntLowerConvexEnvelope_intLowerConvexEnvelope ha).intSupportingValue_eq

/-- Translating the indices by `k` adds `σ * k` to the supporting value at slope `σ`. The
statement includes both infinite supporting values. -/
theorem intSupportingValue_comp_add_right (a : ℤ → WithTop ℝ) (k : ℤ) (σ : ℝ) :
    intSupportingValue (fun n => a (n + k)) σ = intSupportingValue a σ + ((σ * k : ℝ) : EReal) := by
  have hterm (n : ℤ) : (a (n + k)).toEReal - ((σ * n : ℝ) : EReal) =
      ((a (n + k)).toEReal - ((σ * (n + k : ℤ) : ℝ) : EReal)) - ((-(σ * k) : ℝ) : EReal) := by
    induction a (n + k) using WithTop.recTopCoe with
    | top => simp only [WithTop.toEReal_top, EReal.top_sub_coe]
    | coe r =>
      simp only [WithTop.toEReal_coe, ← EReal.coe_sub]
      congr 1
      push_cast
      ring
  have hs : (⨅ n : ℤ, (a (n + k)).toEReal - ((σ * (n + k : ℤ) : ℝ) : EReal)) =
      intSupportingValue a σ :=
    (add_right_surjective k).iInf_comp fun m => (a m).toEReal - ((σ * m : ℝ) : EReal)
  rw [intSupportingValue_def, iInf_congr hterm, EReal.iInf_sub_coe, hs, EReal.coe_neg,
    sub_eq_add_neg, neg_neg]

/-- Extension by infinity at the negative indices does not change supporting values. -/
@[simp]
theorem intSupportingValue_extend (a : ℕ → WithTop ℝ) (σ : ℝ) :
    intSupportingValue (Function.extend ((↑) : ℕ → ℤ) a ⊤) σ = supportingValue a σ := by
  refine le_antisymm (le_supportingValue_iff.mpr fun m => ?_)
    (le_intSupportingValue_iff.mpr fun n => ?_)
  · simpa [Nat.cast_injective.extend_apply] using
      intSupportingValue_le (Function.extend ((↑) : ℕ → ℤ) a ⊤) σ m
  · rcases lt_or_ge n 0 with hn | hn
    · rw [Function.extend_natCast_of_neg _ _ hn, Pi.top_apply, WithTop.toEReal_top,
        EReal.top_sub_coe]
      exact le_top
    · lift n to ℕ using hn
      simpa [Nat.cast_injective.extend_apply] using supportingValue_le a σ n

/-! ### Examples -/

/-- The heights `|n|` are convex on `ℤ`. -/
example : IsIntConvexSeq fun n : ℤ => ((|(n : ℝ)| : ℝ) : WithTop ℝ) :=
  ⟨⟨fun _ _ _ _ _ _ => WithTop.coe_ne_top⟩, fun n _ _ => by
    simp only [WithTop.untop₀_coe]
    push_cast
    calc 2 * |(n : ℝ) + 1| = |(n : ℝ) + ((n : ℝ) + 2)| := by
          rw [show (n : ℝ) + ((n : ℝ) + 2) = 2 * ((n : ℝ) + 1) by ring, abs_mul,
            abs_two]
      _ ≤ |(n : ℝ)| + |(n : ℝ) + 2| := abs_add_le _ _⟩

/-- The heights `-|n|` have no affine lower bound on `ℤ`, although their restriction to `ℕ`
consists of the affine heights `-n`. -/
example : ¬IsIntAdmissible fun n : ℤ => ((-|(n : ℝ)| : ℝ) : WithTop ℝ) := by
  rintro ⟨c, m, hcm⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (-c)
  have h₁ := hcm N
  have h₂ := hcm (-N)
  simp only [WithTop.coe_le_coe, Int.cast_natCast, Int.cast_neg, abs_neg,
    Nat.abs_cast] at h₁ h₂
  linarith

end TauCeti
