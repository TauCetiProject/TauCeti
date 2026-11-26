/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.LinearCombination

/-!
# Mennicke symbols and the universal Mennicke group

Let `A` be a commutative ring and `I` an ideal of `A`. The set `W(A, I)` consists of the pairs
`(a, b)` with `a ≡ 1` and `b ≡ 0` modulo `I` and `aA + bA = A`; they are the first rows of the
determinant-one `2 × 2` matrices congruent to the identity modulo `I`. A **Mennicke
symbol** on `W(A, I)` with values in a group `C` is a map `(a, b) ↦ [b/a]` satisfying

* `[b + t a / a] = [b/a]` for `t ∈ I`;
* `[b / a + t b] = [b/a]` for every `t ∈ A`;
* `[b₁ b₂ / a] = [b₁/a] [b₂/a]` whenever `(a, b₁)` and `(a, b₂)` lie in `W(A, I)`.

The two moves are deliberately asymmetric: the first, which changes `b` by a multiple of `a`,
only allows coefficients in `I`. The normalization `[0/1] = 1` follows from multiplicativity.
Mennicke symbols are the rank-two shadow of the relative elementary subgroups: Bass, Milnor and
Serre show that for `n ≥ 3`, sending `(a, b) ∈ W(A, I)` to the class in `SLₙ(A, I) / Eₙ(A, I)` of
the block sum `[[a, b], [c, d]] ⊕ 1ₙ₋₂`, for any `[[a, b], [c, d]] ∈ SL₂(A, I)` with first row
`(a, b)`, is a well-defined Mennicke symbol, and compute this group over rings of `S`-integers
through the universal Mennicke symbol, which this file constructs.

The **universal Mennicke group** `C_I = Ideal.MennickeGroup I` is the group presented by the
generators `[b/a]`, one for each pair in `W(A, I)`, subject to the three Mennicke relations. Its
generator map is a Mennicke symbol, and every Mennicke symbol with values in a group `C` factors
uniquely through it (`Ideal.MennickeGroup.lift`). A ring homomorphism `f : A →+* B` carrying `I`
into an ideal `J` of `B` induces `C_I → C_J`; in particular an inclusion of ideals `J ≤ I`
induces the transition map `C_J → C_I`.

Over every commutative ring a symbol is trivial on near-unit pairs: if `a` is congruent modulo
`b` to a unit of `A`, or `b` is congruent modulo `a` to a unit of `A`, then `[b/a] = 1`. As
consequences, the universal group of the zero ideal is trivial, and so is the universal group
of the unit ideal of a Euclidean domain, by the Euclidean algorithm.

## Main definitions

* `Ideal.MennickePair`: the set `W(A, I)` of admissible pairs.
* `Ideal.MennickePair.shiftSnd`, `Ideal.MennickePair.shiftFst`, `Ideal.MennickePair.mulSnd`:
  the pairs `(a, b + t a)`, `(a + t b, b)` and `(a, b₁ b₂)` entering the Mennicke relations.
* `Ideal.MennickePair.map`: the pair map induced by a ring homomorphism.
* `Ideal.IsMennickeSymbol`: the Mennicke relations for a map `W(A, I) → C`.
* `Ideal.MennickeGroup`: the universal Mennicke group `C_I`, with generators
  `Ideal.MennickeGroup.of`.
* `Ideal.MennickeGroup.lift`: Mennicke symbols with values in `C` correspond to homomorphisms
  `C_I →* C`.
* `Ideal.MennickeGroup.map`, `Ideal.MennickeGroup.ofLE`: functoriality in pair maps and the
  transition maps of ideal inclusions.

## Main results

* `Ideal.MennickeGroup.isMennickeSymbol_of`: the generator map is a Mennicke symbol.
* `Ideal.MennickeGroup.hom_ext`, `Ideal.MennickeGroup.induction_on`: homomorphisms out of `C_I`
  are determined on generators, and generator induction.
* `Ideal.IsMennickeSymbol.map_one`: the normalization `[0/1] = 1`.
* `Ideal.IsMennickeSymbol.map_eq_one_of_isUnit_fst`: `[b/a] = 1` when `a` is a unit.
* `Ideal.IsMennickeSymbol.map_eq_one_of_dvd_fst_sub`,
  `Ideal.IsMennickeSymbol.map_eq_one_of_dvd_snd_sub`: near-unit pairs have trivial symbol.
* `Ideal.IsMennickeSymbol.map_eq_of_snd_eq_mul_one_sub`: `[b (1 - a) / a] = [b/a]`.
* `Ideal.IsMennickeSymbol.map_eq_of_snd_eq_neg`: `[-b/a] = [b/a]`.
* `Ideal.MennickeGroup.subsingleton_iff`: `C_I` is trivial exactly when every generator is.
* `Ideal.MennickeGroup.subsingleton_bot`: the universal group of the zero ideal is trivial.
* `Ideal.IsMennickeSymbol.map_eq_one_of_euclideanDomain`,
  `Ideal.MennickeGroup.subsingleton_top_of_euclideanDomain`: over a Euclidean domain every
  Mennicke symbol at the unit ideal is trivial, and so is the universal group.

## References

* H. Bass, J. Milnor and J.-P. Serre, *Solution of the congruence subgroup problem for `SLₙ`
  (`n ≥ 3`) and `Sp₂ₙ` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), 59–137, §2, Definition 2.5.
-/

public section

namespace Ideal

variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D]

/-- The set `W(A, I)` of **Mennicke pairs** at level `I`: pairs `(a, b)` of elements of `A` with
`a ≡ 1` and `b ≡ 0` modulo `I` which generate the unit ideal. -/
@[ext]
structure MennickePair (I : Ideal A) where
  /-- The first entry `a` of the pair, the denominator of the symbol `[b/a]`. -/
  fst : A
  /-- The second entry `b` of the pair, the numerator of the symbol `[b/a]`. -/
  snd : A
  fst_sub_one_mem : fst - 1 ∈ I
  snd_mem : snd ∈ I
  isCoprime : IsCoprime fst snd

namespace MennickePair

variable {I : Ideal A} {J : Ideal B} {K : Ideal D}

/-- The base pair `(1, 0)`. -/
protected def one : MennickePair I where
  fst := 1
  snd := 0
  fst_sub_one_mem := by simp
  snd_mem := I.zero_mem
  isCoprime := isCoprime_one_left

@[simp]
theorem one_fst : (MennickePair.one : MennickePair I).fst = 1 := (rfl)

@[simp]
theorem one_snd : (MennickePair.one : MennickePair I).snd = 0 := (rfl)

instance : Inhabited (MennickePair I) := ⟨.one⟩

/-- The pair `(a, b + t a)` obtained from `(a, b)` by adding a multiple of the first entry with
coefficient `t ∈ I` to the second entry. -/
def shiftSnd (p : MennickePair I) (t : A) (ht : t ∈ I) : MennickePair I where
  fst := p.fst
  snd := p.snd + t * p.fst
  fst_sub_one_mem := p.fst_sub_one_mem
  snd_mem := I.add_mem p.snd_mem (I.mul_mem_right _ ht)
  isCoprime := p.isCoprime.add_mul_right_right t

@[simp]
theorem shiftSnd_fst (p : MennickePair I) (t : A) (ht : t ∈ I) : (p.shiftSnd t ht).fst = p.fst :=
  (rfl)

@[simp]
theorem shiftSnd_snd (p : MennickePair I) (t : A) (ht : t ∈ I) :
    (p.shiftSnd t ht).snd = p.snd + t * p.fst :=
  (rfl)

/-- The pair `(a + t b, b)` obtained from `(a, b)` by adding a multiple of the second entry with
arbitrary coefficient `t ∈ A` to the first entry. -/
def shiftFst (p : MennickePair I) (t : A) : MennickePair I where
  fst := p.fst + t * p.snd
  snd := p.snd
  fst_sub_one_mem := by
    rw [add_sub_right_comm]
    exact I.add_mem p.fst_sub_one_mem (I.mul_mem_left _ p.snd_mem)
  snd_mem := p.snd_mem
  isCoprime := p.isCoprime.add_mul_right_left t

@[simp]
theorem shiftFst_fst (p : MennickePair I) (t : A) : (p.shiftFst t).fst = p.fst + t * p.snd :=
  (rfl)

@[simp]
theorem shiftFst_snd (p : MennickePair I) (t : A) : (p.shiftFst t).snd = p.snd :=
  (rfl)

/-- The pair `(a, b₁ b₂)` built from two pairs `(a, b₁)` and `(a, b₂)` with the same first
entry. -/
def mulSnd (p q : MennickePair I) (h : p.fst = q.fst) : MennickePair I where
  fst := p.fst
  snd := p.snd * q.snd
  fst_sub_one_mem := p.fst_sub_one_mem
  snd_mem := I.mul_mem_right _ p.snd_mem
  isCoprime := p.isCoprime.mul_right (h ▸ q.isCoprime)

@[simp]
theorem mulSnd_fst (p q : MennickePair I) (h : p.fst = q.fst) : (p.mulSnd q h).fst = p.fst :=
  (rfl)

@[simp]
theorem mulSnd_snd (p q : MennickePair I) (h : p.fst = q.fst) :
    (p.mulSnd q h).snd = p.snd * q.snd :=
  (rfl)

/-- The pair map `W(A, I) → W(B, J)` induced by a ring homomorphism `f : A →+* B` carrying `I`
into `J`, applying `f` to both entries. -/
def map (f : A →+* B) (h : I ≤ J.comap f) (p : MennickePair I) : MennickePair J where
  fst := f p.fst
  snd := f p.snd
  fst_sub_one_mem := by simpa using h p.fst_sub_one_mem
  snd_mem := h p.snd_mem
  isCoprime := p.isCoprime.map f

@[simp]
theorem map_fst (f : A →+* B) (h : I ≤ J.comap f) (p : MennickePair I) :
    (p.map f h).fst = f p.fst :=
  (rfl)

@[simp]
theorem map_snd (f : A →+* B) (h : I ≤ J.comap f) (p : MennickePair I) :
    (p.map f h).snd = f p.snd :=
  (rfl)

@[simp]
theorem map_id (p : MennickePair I) : p.map (RingHom.id A) (Ideal.comap_id I).ge = p :=
  (rfl)

@[simp]
theorem map_map (g : B →+* D) (f : A →+* B) (hg : J ≤ K.comap g) (hf : I ≤ J.comap f)
    (p : MennickePair I) :
    (p.map f hf).map g hg = p.map (g.comp f) (hf.trans (Ideal.comap_mono hg)) :=
  (rfl)

@[simp]
theorem map_one (f : A →+* B) (h : I ≤ J.comap f) :
    (MennickePair.one : MennickePair I).map f h = .one := by
  ext <;> simp

@[simp]
theorem map_shiftSnd (f : A →+* B) (h : I ≤ J.comap f) (p : MennickePair I) (t : A)
    (ht : t ∈ I) :
    (p.shiftSnd t ht).map f h = (p.map f h).shiftSnd (f t) (Ideal.mem_comap.mp (h ht)) := by
  ext <;> simp

@[simp]
theorem map_shiftFst (f : A →+* B) (h : I ≤ J.comap f) (p : MennickePair I) (t : A) :
    (p.shiftFst t).map f h = (p.map f h).shiftFst (f t) := by
  ext <;> simp

@[simp]
theorem map_mulSnd (f : A →+* B) (h : I ≤ J.comap f) (p q : MennickePair I) (hpq : p.fst = q.fst) :
    (p.mulSnd q hpq).map f h = (p.map f h).mulSnd (q.map f h) (by simp [hpq]) := by
  ext <;> simp

end MennickePair

/-- The **Mennicke relations** for a map `s : W(A, I) → C`, written `s (a, b) = [b/a]`:
`[b + t a / a] = [b/a]` for `t ∈ I`, `[b / a + t b] = [b/a]` for `t ∈ A`, and
`[b₁ b₂ / a] = [b₁/a] [b₂/a]` for admissible pairs `(a, b₁)` and `(a, b₂)`.
The normalization `[0/1] = 1` is a consequence, `Ideal.IsMennickeSymbol.map_one`. -/
structure IsMennickeSymbol {I : Ideal A} {C : Type*} [Group C] (s : MennickePair I → C) :
    Prop where
  /-- `[b + t a / a] = [b/a]` for `t ∈ I`. -/
  map_shiftSnd (p : MennickePair I) (t : A) (ht : t ∈ I) : s (p.shiftSnd t ht) = s p
  /-- `[b / a + t b] = [b/a]` for `t ∈ A`. -/
  map_shiftFst (p : MennickePair I) (t : A) : s (p.shiftFst t) = s p
  /-- `[b₁ b₂ / a] = [b₁/a] [b₂/a]`. -/
  map_mulSnd (p q : MennickePair I) (h : p.fst = q.fst) : s (p.mulSnd q h) = s p * s q

namespace IsMennickeSymbol

variable {I : Ideal A} {J : Ideal B} {C E : Type*} [Group C] [Group E] {s : MennickePair I → C}

/-- The first Mennicke relation in coordinates: `[b'/a] = [b/a]` when `b' = b + t a` with
`t ∈ I`. -/
theorem map_eq_of_snd_eq (hs : IsMennickeSymbol s) {p q : MennickePair I}
    (hfst : q.fst = p.fst) {t : A} (ht : t ∈ I) (hsnd : q.snd = p.snd + t * p.fst) :
    s q = s p := by
  rw [← hs.map_shiftSnd p t ht]
  congr 1
  ext <;> simp [hfst, hsnd]

/-- The second Mennicke relation in coordinates: `[b/a'] = [b/a]` when `a' = a + t b` with
`t ∈ A`. -/
theorem map_eq_of_fst_eq (hs : IsMennickeSymbol s) {p q : MennickePair I} (t : A)
    (hfst : q.fst = p.fst + t * p.snd) (hsnd : q.snd = p.snd) : s q = s p := by
  rw [← hs.map_shiftFst p t]
  congr 1
  ext <;> simp [hfst, hsnd]

/-- The third Mennicke relation in coordinates: `[b/a] = [b₁/a] [b₂/a]` when `b = b₁ b₂`. -/
theorem map_eq_mul_of_snd_eq_mul (hs : IsMennickeSymbol s) {p₁ p₂ q : MennickePair I}
    (h₁ : p₁.fst = q.fst) (h₂ : p₂.fst = q.fst) (hsnd : q.snd = p₁.snd * p₂.snd) :
    s q = s p₁ * s p₂ := by
  rw [← hs.map_mulSnd p₁ p₂ (h₁.trans h₂.symm)]
  congr 1
  ext <;> simp [h₁, hsnd]

/-- A pair whose second entry is zero has trivial symbol: `[0/a] = 1`. -/
theorem map_eq_one_of_snd_eq_zero (hs : IsMennickeSymbol s) {p : MennickePair I}
    (hp : p.snd = 0) : s p = 1 := by
  have h := hs.map_mulSnd p p rfl
  have hpp : p.mulSnd p rfl = p := by ext <;> simp [hp]
  rw [hpp] at h
  simpa using h

/-- The normalization `[0/1] = 1` of a Mennicke symbol. -/
theorem map_one (hs : IsMennickeSymbol s) : s .one = 1 :=
  hs.map_eq_one_of_snd_eq_zero rfl

/-- If the first entry `a` is a unit, then `[b/a] = 1`. -/
theorem map_eq_one_of_isUnit_fst (hs : IsMennickeSymbol s) {p : MennickePair I}
    (hp : IsUnit p.fst) : s p = 1 := by
  obtain ⟨u, hu⟩ := hp
  rw [← hs.map_shiftSnd p (-(p.snd * ↑u⁻¹)) (I.neg_mem (I.mul_mem_right _ p.snd_mem))]
  refine hs.map_eq_one_of_snd_eq_zero ?_
  simp [← hu]

/-- **Near-unit reduction in the first entry.** If `a` is congruent modulo `b` to a unit of `A`,
then `[b/a] = 1`. -/
theorem map_eq_one_of_dvd_fst_sub (hs : IsMennickeSymbol s) {p : MennickePair I} {u : A}
    (hu : IsUnit u) (hdvd : p.snd ∣ p.fst - u) : s p = 1 := by
  obtain ⟨k, hk⟩ := hdvd
  rw [← hs.map_shiftFst p (-k)]
  refine hs.map_eq_one_of_isUnit_fst ?_
  convert hu using 1
  simp only [MennickePair.shiftFst_fst]
  linear_combination hk

/-- **Near-unit reduction in the second entry.** If `b` is congruent modulo `a` to a unit of `A`,
then `[b/a] = 1`. -/
theorem map_eq_one_of_dvd_snd_sub (hs : IsMennickeSymbol s) {p : MennickePair I} {u : A}
    (hu : IsUnit u) (hdvd : p.fst ∣ p.snd - u) : s p = 1 := by
  obtain ⟨u, rfl⟩ := hu
  obtain ⟨k, hk⟩ := hdvd
  -- With `b = u + a k`, the coefficient `-(k + u) = k (a - 1) - b` lies in `I`, and moving by it
  -- turns `(a, b)` into `(a, u (1 - a))`, for which `a ≡ 1` modulo the second entry.
  have hmem : -(k + u) ∈ I := by
    rw [show -(k + u) = k * (p.fst - 1) - p.snd by linear_combination hk]
    exact I.sub_mem (I.mul_mem_left _ p.fst_sub_one_mem) p.snd_mem
  rw [← hs.map_shiftSnd p _ hmem]
  refine hs.map_eq_one_of_dvd_fst_sub isUnit_one ⟨-↑u⁻¹, ?_⟩
  simp only [MennickePair.shiftSnd_fst, MennickePair.shiftSnd_snd]
  linear_combination (1 - p.fst) * u.inv_mul + (↑u⁻¹ : A) * hk

/-- Multiplying the second entry by `1 - a` does not change the symbol: `[b (1 - a) / a] = [b/a]`.
This is the first Mennicke relation with coefficient `-b ∈ I`. -/
theorem map_eq_of_snd_eq_mul_one_sub (hs : IsMennickeSymbol s) {p q : MennickePair I}
    (hfst : q.fst = p.fst) (hsnd : q.snd = p.snd * (1 - p.fst)) : s q = s p :=
  hs.map_eq_of_snd_eq hfst (I.neg_mem p.snd_mem) (by rw [hsnd]; ring)

/-- The sign of the second entry does not matter: `[-b/a] = [b/a]`. -/
theorem map_eq_of_snd_eq_neg (hs : IsMennickeSymbol s) {p q : MennickePair I}
    (hfst : q.fst = p.fst) (hsnd : q.snd = -p.snd) : s q = s p := by
  -- `[-b/a] = [-b (1 - a)/a] = [b (a - 1)/a] = [b/a] [(a - 1)/a]`, and the last symbol is
  -- trivial because `a ≡ 1` modulo `a - 1`.
  let r : MennickePair I := ⟨p.fst, p.fst - 1, p.fst_sub_one_mem, p.fst_sub_one_mem,
    ⟨1, -1, by ring⟩⟩
  have hr : s r = 1 := hs.map_eq_one_of_dvd_fst_sub isUnit_one dvd_rfl
  rw [← hs.map_eq_of_snd_eq_mul_one_sub (q := p.mulSnd r rfl) (p := q) (by simp [hfst])
    (by simp [r, hfst, hsnd]; ring), hs.map_mulSnd, hr, mul_one]

/-- Composing a Mennicke symbol with a group homomorphism gives a Mennicke symbol. -/
theorem monoidHom_comp (hs : IsMennickeSymbol s) (φ : C →* E) : IsMennickeSymbol (φ ∘ s) where
  map_shiftSnd p t ht := by simp [hs.map_shiftSnd p t ht]
  map_shiftFst p t := by simp [hs.map_shiftFst p t]
  map_mulSnd p q h := by simp [hs.map_mulSnd p q h]

/-- Precomposing a Mennicke symbol at level `J` with the pair map of a ring homomorphism carrying
`I` into `J` gives a Mennicke symbol at level `I`. -/
theorem comp_map {s : MennickePair J → C} (hs : IsMennickeSymbol s) (f : A →+* B)
    (h : I ≤ J.comap f) : IsMennickeSymbol (s ∘ MennickePair.map f h) where
  map_shiftSnd p t ht := by
    simp only [Function.comp_apply, MennickePair.map_shiftSnd, hs.map_shiftSnd]
  map_shiftFst p t := by
    simp only [Function.comp_apply, MennickePair.map_shiftFst, hs.map_shiftFst]
  map_mulSnd p q hpq := by
    simp only [Function.comp_apply, MennickePair.map_mulSnd, hs.map_mulSnd]

/-- **The Euclidean algorithm.** Over a Euclidean domain, every Mennicke symbol at the unit ideal
is trivial. -/
theorem map_eq_one_of_euclideanDomain {R : Type*} [EuclideanDomain R]
    {s : MennickePair (⊤ : Ideal R) → C} (hs : IsMennickeSymbol s) (p : MennickePair ⊤) :
    s p = 1 := by
  -- Simultaneous induction on the size of the second entry and of the first entry: each step
  -- reduces the other entry modulo the given one.
  suffices H : ∀ y : R, (∀ p : MennickePair (⊤ : Ideal R), p.snd = y → s p = 1) ∧
      (∀ p : MennickePair (⊤ : Ideal R), p.fst = y → s p = 1) from (H p.snd).1 p rfl
  intro y
  induction y using (@EuclideanDomain.r_wellFounded R _).induction with
  | _ y ih => ?_
  refine ⟨fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · by_cases hy : y = 0
    · have h := p.isCoprime
      rw [hp, hy, isCoprime_zero_right] at h
      exact hs.map_eq_one_of_isUnit_fst h
    rw [← hs.map_shiftFst p (-(p.fst / y))]
    refine (ih _ (EuclideanDomain.mod_lt p.fst hy)).2 _ ?_
    rw [MennickePair.shiftFst_fst, hp, EuclideanDomain.mod_eq_sub_mul_div]
    ring
  · by_cases hy : y = 0
    · have h := p.isCoprime
      rw [hp, hy, isCoprime_zero_left] at h
      exact hs.map_eq_one_of_dvd_fst_sub h.neg ⟨1, by simp [hp, hy]⟩
    rw [← hs.map_shiftSnd p (-(p.snd / y)) Submodule.mem_top]
    refine (ih _ (EuclideanDomain.mod_lt p.snd hy)).1 _ ?_
    rw [MennickePair.shiftSnd_snd, hp, EuclideanDomain.mod_eq_sub_mul_div]
    ring

end IsMennickeSymbol

/-- The relators of the universal Mennicke group at level `I`, on the generators `W(A, I)`: the
words `[b + t a / a] [b/a]⁻¹` for `t ∈ I`, `[b / a + t b] [b/a]⁻¹` for `t ∈ A`, and
`[b₁ b₂ / a] ([b₁/a] [b₂/a])⁻¹`. -/
def mennickeRels (I : Ideal A) : Set (FreeGroup (MennickePair I)) :=
  {r | (∃ (p : MennickePair I) (t : A) (ht : t ∈ I),
        r = FreeGroup.of (p.shiftSnd t ht) * (FreeGroup.of p)⁻¹) ∨
      (∃ (p : MennickePair I) (t : A), r = FreeGroup.of (p.shiftFst t) * (FreeGroup.of p)⁻¹) ∨
      (∃ (p q : MennickePair I) (h : p.fst = q.fst),
        r = FreeGroup.of (p.mulSnd q h) * (FreeGroup.of p * FreeGroup.of q)⁻¹)}

/-- The **universal Mennicke group** `C_I` at level `I`: the group presented by one generator
`[b/a]` for each pair `(a, b)` of `W(A, I)`, subject to the Mennicke relations. -/
abbrev MennickeGroup (I : Ideal A) : Type _ :=
  PresentedGroup (mennickeRels I)

namespace MennickeGroup

variable {I : Ideal A} {J : Ideal B} {K : Ideal D} {C : Type*} [Group C]

/-- The generator `[b/a]` of the universal Mennicke group attached to a pair `(a, b)`. -/
def of (p : MennickePair I) : MennickeGroup I :=
  PresentedGroup.of p

/-- The raw generator `PresentedGroup.of p` of the underlying presented group is the generator
`[b/a]`. -/
@[simp]
theorem presentedGroupOf_eq_of (p : MennickePair I) :
    (PresentedGroup.of p : MennickeGroup I) = of p :=
  (rfl)

/-- The image in the universal Mennicke group of the free generator attached to a pair is the
generator `[b/a]`. -/
@[simp]
theorem mk_of (p : MennickePair I) :
    PresentedGroup.mk (mennickeRels I) (FreeGroup.of p) = of p :=
  (rfl)

/-- The generators of the universal Mennicke group satisfy the Mennicke relations. -/
theorem isMennickeSymbol_of : IsMennickeSymbol (of : MennickePair I → MennickeGroup I) where
  map_shiftSnd p t ht := by
    simpa only [map_mul, mk_of] using
      PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := mennickeRels I) (Or.inl ⟨p, t, ht, rfl⟩)
  map_shiftFst p t := by
    simpa only [map_mul, mk_of] using
      PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := mennickeRels I) (Or.inr (Or.inl ⟨p, t, rfl⟩))
  map_mulSnd p q h := by
    simpa only [map_mul, mk_of] using
      PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := mennickeRels I)
        (Or.inr (Or.inr ⟨p, q, h, rfl⟩))

/-- Generator induction on the universal Mennicke group: a predicate holding at `1` and at every
generator, and closed under products and inverses, holds everywhere. -/
@[elab_as_elim]
theorem induction_on {motive : MennickeGroup I → Prop} (x : MennickeGroup I)
    (one : motive 1) (of : ∀ p, motive (of p))
    (mul : ∀ x y, motive x → motive y → motive (x * y))
    (inv : ∀ x, motive x → motive x⁻¹) : motive x := by
  induction x using PresentedGroup.induction_on with | H w =>
  induction w using FreeGroup.induction_on with
  | one => simpa only [map_one] using one
  | of p => exact of p
  | inv_of p _ => simpa only [map_inv, mk_of] using inv _ (of p)
  | mul w₁ w₂ ih₁ ih₂ => simpa only [map_mul] using mul _ _ ih₁ ih₂

/-- The generators `[b/a]` generate the universal Mennicke group. -/
@[simp]
theorem closure_range_of : Subgroup.closure (Set.range (of : MennickePair I → _)) = ⊤ :=
  PresentedGroup.closure_range_of _

/-- Two homomorphisms out of the universal Mennicke group agree when they agree on every
generator. -/
@[ext]
theorem hom_ext {G : Type*} [Monoid G] {φ ψ : MennickeGroup I →* G}
    (h : ∀ p, φ (of p) = ψ (of p)) : φ = ψ := by
  ext x
  induction x using induction_on with
  | one => rw [map_one, map_one]
  | of p => exact h p
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy]
  | inv x hx => exact eq_on_inv φ ψ hx

private theorem lift_rels {s : MennickePair I → C} (hs : IsMennickeSymbol s) :
    ∀ r ∈ mennickeRels I, FreeGroup.lift s r = 1 := by
  rintro r (⟨p, t, ht, rfl⟩ | ⟨p, t, rfl⟩ | ⟨p, q, h, rfl⟩)
  · simp [hs.map_shiftSnd p t ht]
  · simp [hs.map_shiftFst p t]
  · simp [hs.map_mulSnd p q h]

/-- **Universal property of the Mennicke group.** Mennicke symbols at level `I` with values in a
group `C` correspond to homomorphisms `C_I →* C`, a symbol `s` corresponding to the homomorphism
sending each generator `[b/a]` to `s (a, b)`. -/
def lift : {s : MennickePair I → C // IsMennickeSymbol s} ≃ (MennickeGroup I →* C) where
  toFun s := PresentedGroup.toGroup (lift_rels s.property)
  invFun φ := ⟨φ ∘ of, isMennickeSymbol_of.monoidHom_comp φ⟩
  left_inv s := by ext p; exact PresentedGroup.toGroup.of (x := p) (lift_rels s.property)
  right_inv φ := hom_ext fun p ↦
    PresentedGroup.toGroup.of (x := p) (lift_rels (isMennickeSymbol_of.monoidHom_comp φ))

@[simp]
theorem lift_of (s : {s : MennickePair I → C // IsMennickeSymbol s}) (p : MennickePair I) :
    lift s (of p) = s.val p :=
  PresentedGroup.toGroup.of (x := p) (lift_rels s.property)

@[simp]
theorem lift_symm_apply_coe (φ : MennickeGroup I →* C) : ((lift.symm φ : _) : _ → C) = φ ∘ of :=
  (rfl)

/-- The universal Mennicke group is trivial if and only if every generator `[b/a]` is trivial. -/
theorem subsingleton_iff : Subsingleton (MennickeGroup I) ↔ ∀ p : MennickePair I, of p = 1 := by
  refine ⟨fun _ p ↦ Subsingleton.elim _ _, fun h ↦ ⟨fun x y ↦ ?_⟩⟩
  suffices H : ∀ z : MennickeGroup I, z = 1 by rw [H x, H y]
  intro z
  induction z using induction_on with
  | one => rfl
  | of p => exact h p
  | mul x y hx hy => rw [hx, hy, one_mul]
  | inv x hx => rw [hx, inv_one]

/-- The universal Mennicke group of the zero ideal is trivial: `W(A, 0)` consists of the single
pair `(1, 0)`. -/
instance subsingleton_bot : Subsingleton (MennickeGroup (⊥ : Ideal A)) := by
  refine subsingleton_iff.mpr fun p ↦ ?_
  have hp : p = .one := by
    ext
    · simpa [sub_eq_zero] using p.fst_sub_one_mem
    · simpa using p.snd_mem
  rw [hp, isMennickeSymbol_of.map_one]

/-- Over a Euclidean domain, the universal Mennicke group of the unit ideal is trivial. -/
instance subsingleton_top_of_euclideanDomain {R : Type*} [EuclideanDomain R] :
    Subsingleton (MennickeGroup (⊤ : Ideal R)) :=
  subsingleton_iff.mpr isMennickeSymbol_of.map_eq_one_of_euclideanDomain

/-- The homomorphism `C_I →* C_J` of universal Mennicke groups induced by a ring homomorphism
`f : A →+* B` carrying `I` into `J`, sending `[b/a]` to `[f b / f a]`. -/
def map (f : A →+* B) (h : I ≤ J.comap f) : MennickeGroup I →* MennickeGroup J :=
  lift ⟨of ∘ MennickePair.map f h, isMennickeSymbol_of.comp_map f h⟩

@[simp]
theorem map_of (f : A →+* B) (h : I ≤ J.comap f) (p : MennickePair I) :
    map f h (of p) = of (p.map f h) :=
  lift_of _ p

@[simp]
theorem map_id : map (RingHom.id A) (Ideal.comap_id I).ge = MonoidHom.id (MennickeGroup I) :=
  hom_ext fun p ↦ by simp

theorem map_comp (g : B →+* D) (f : A →+* B) (hg : J ≤ K.comap g) (hf : I ≤ J.comap f) :
    map (g.comp f) (hf.trans (Ideal.comap_mono hg)) = (map g hg).comp (map f hf) :=
  hom_ext fun p ↦ by simp [MennickePair.map_map]

@[simp]
theorem map_map (g : B →+* D) (f : A →+* B) (hg : J ≤ K.comap g) (hf : I ≤ J.comap f)
    (x : MennickeGroup I) :
    map g hg (map f hf x) = map (g.comp f) (hf.trans (Ideal.comap_mono hg)) x := by
  rw [map_comp, MonoidHom.comp_apply]

/-- The transition map `C_J →* C_I` of universal Mennicke groups induced by an inclusion of
ideals `J ≤ I`, sending the generator `[b/a]` at level `J` to the same symbol at level `I`. -/
def ofLE {I J : Ideal A} (h : J ≤ I) : MennickeGroup J →* MennickeGroup I :=
  map (RingHom.id A) (h.trans (Ideal.comap_id I).ge)

@[simp]
theorem ofLE_of {I J : Ideal A} (h : J ≤ I) (p : MennickePair J) :
    ofLE h (of p) = of ⟨p.fst, p.snd, h p.fst_sub_one_mem, h p.snd_mem, p.isCoprime⟩ :=
  (map_of _ (h.trans (Ideal.comap_id I).ge) p).trans (congrArg of (by ext <;> simp))

@[simp]
theorem ofLE_refl (I : Ideal A) : ofLE (le_refl I) = MonoidHom.id _ :=
  map_id

@[simp]
theorem ofLE_ofLE {I J L : Ideal A} (hJI : J ≤ I) (hLJ : L ≤ J) (x : MennickeGroup L) :
    ofLE hJI (ofLE hLJ x) = ofLE (hLJ.trans hJI) x := by
  simp only [ofLE, map_map, RingHom.id_comp]

end MennickeGroup

end Ideal
