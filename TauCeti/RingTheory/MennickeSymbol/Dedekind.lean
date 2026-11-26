/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MennickeSymbol.Reciprocity
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import TauCeti.RingTheory.DedekindDomain.Ideal.SupSpan
import Mathlib.Tactic.LinearCombination

/-!
# Mennicke symbols over a Dedekind domain

Over a Dedekind domain `A`, every admissible pair `(a, b) ∈ W(A, I)` can be moved, without changing
its Mennicke symbol, so that `b` generates `I` together with any prescribed nonzero `y ∈ I`
(`IsDedekindDomain.exists_mem_sup_span_add_mul_eq`). This file draws three consequences.

* **Descent to a deeper level.** For `0 ≠ J ≤ I` the transition map `C_J → C_I` is surjective.
* **Common denominators** (the Mennicke–Newman lemma). Finitely many symbols `[bᵢ/aᵢ]` can be
  rewritten as `[bᵢ'/a]` with one common denominator `a`. Since symbols with a common denominator
  commute, the universal Mennicke group is commutative, and so is the image of every Mennicke
  symbol, whatever its group of values.
* **Lam's identity** `[b/(a₁ a₂)] = [b/a₁] [b/a₂]`: multiplicativity in the denominator, deduced
  from Kervaire reciprocity.

## Main results

* `Ideal.MennickeGroup.ofLE_surjective`: the transition map `C_J → C_I` is surjective for
  `0 ≠ J ≤ I`.
* `Ideal.MennickeGroup.exists_common_denominator`: the Mennicke–Newman lemma.
* `Ideal.MennickeGroup.commute`, `Ideal.MennickeGroup.instIsMulCommutative`: the universal
  Mennicke group is commutative.
* `Ideal.IsMennickeSymbol.commute`: any two values of a Mennicke symbol commute.
* `Ideal.IsMennickeSymbol.map_eq_mul_of_fst_eq_mul`: Lam's identity.

## References

* H. Bass, J. Milnor and J.-P. Serre, *Solution of the congruence subgroup problem for `SLₙ`
  (`n ≥ 3`) and `Sp₂ₙ` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), 59–137, §2, pp. 65–71.
-/

public section

namespace Ideal

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {I : Ideal A}

namespace MennickeGroup

/-- **Descent to a deeper level.** Over a Dedekind domain, the transition map `C_J → C_I` of an
inclusion `J ≤ I` with `J ≠ 0` is surjective. -/
theorem ofLE_surjective {J : Ideal A} (h : J ≤ I) (hJ : J ≠ ⊥) : Function.Surjective (ofLE h) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_range_of, Subgroup.closure_le]
  rintro _ ⟨p, rfl⟩
  -- Move `(a, b)` to `(a, b')` with `J + (b') = I`, then to `(a', b')` with `a' ≡ 1` modulo `J`;
  -- finally `[b' (1 - a') / a'] = [b'/a']` is a symbol at level `J`.
  obtain ⟨t, htI, ht⟩ :=
    IsDedekindDomain.exists_mem_sup_span_add_mul_eq h hJ p.snd_mem p.isCoprime
  have h₁ : p.fst - 1 ∈ J ⊔ span {p.snd + t * p.fst} := by rw [ht]; exact p.fst_sub_one_mem
  obtain ⟨j, hj, z, hz, hjz⟩ := Submodule.mem_sup.mp h₁
  obtain ⟨m, rfl⟩ := mem_span_singleton'.mp hz
  let p₁ := (p.shiftSnd t htI).shiftFst (-m)
  have hp₁ : p₁.fst - 1 = j := by
    simp only [p₁, MennickePair.shiftFst_fst, MennickePair.shiftSnd_snd,
      MennickePair.shiftSnd_fst]
    linear_combination -hjz
  have hJ₁ : 1 - p₁.fst ∈ J := sub_mem_comm_iff.mp (hp₁ ▸ hj)
  refine ⟨of ⟨p₁.fst, p₁.snd * (1 - p₁.fst), hp₁ ▸ hj, J.mul_mem_left _ hJ₁,
    p₁.isCoprime.mul_right ⟨1, 1, by ring⟩⟩, ?_⟩
  rw [ofLE_of]
  refine (isMennickeSymbol_of.map_eq_of_snd_eq_mul_one_sub (p := p₁) ?_ ?_).trans ?_
  · rfl
  · rfl
  simp only [p₁, isMennickeSymbol_of.map_shiftFst, isMennickeSymbol_of.map_shiftSnd]

/-- One step of the Mennicke–Newman lemma: a symbol `[b/c]` can be rewritten with a nonzero
numerator and with denominator `r + x β`, for any `r ≡ 1` modulo `I` and nonzero `β ∈ I`. -/
private theorem exists_fst_eq_add_mul {r β : A} (hr : r - 1 ∈ I) (hβI : β ∈ I) (hβ : β ≠ 0)
    (p : MennickePair I) :
    ∃ x : A, ∃ p' : MennickePair I, p'.fst = r + x * β ∧ p'.snd ≠ 0 ∧ of p' = of p := by
  have hs := isMennickeSymbol_of (I := I)
  have hrI : r - p.fst ∈ I := by
    rw [show r - p.fst = (r - 1) - (p.fst - 1) by ring]
    exact I.sub_mem hr p.fst_sub_one_mem
  obtain ⟨t, htI, ht⟩ := IsDedekindDomain.exists_mem_sup_span_add_mul_eq
    ((span_singleton_le_iff_mem _).mpr hβI) (by rwa [Ne, span_singleton_eq_bot]) p.snd_mem
    p.isCoprime
  by_cases hd : p.snd + t * p.fst = 0
  · -- Here `(β) = I`, and `(c, b + (t + β) c) = (c, β c)` has nonzero second entry.
    rw [hd, span_singleton_eq_bot.mpr rfl, sup_bot_eq] at ht
    obtain ⟨k, hk⟩ := mem_span_singleton'.mp (by rw [ht]; exact hrI : r - p.fst ∈ span {β})
    have hc : p.fst ≠ 0 := by
      rintro hc
      have h := p.isCoprime
      rw [hc, isCoprime_zero_left] at h
      rw [hc, mul_zero, add_zero] at hd
      exact not_isUnit_zero (hd ▸ h)
    refine ⟨-k, p.shiftSnd (t + β) (I.add_mem htI hβI), ?_, ?_, hs.map_shiftSnd _ _ _⟩
    · simp only [MennickePair.shiftSnd_fst]
      linear_combination hk
    · simp only [MennickePair.shiftSnd_snd]
      rw [show p.snd + (t + β) * p.fst = (p.snd + t * p.fst) + β * p.fst by ring, hd, zero_add]
      exact mul_ne_zero hβ hc
  · obtain ⟨_, hx, _, hz, hxz⟩ := Submodule.mem_sup.mp
      (by rw [ht]; exact hrI : r - p.fst ∈ span {β} ⊔ span {p.snd + t * p.fst})
    obtain ⟨k, rfl⟩ := mem_span_singleton'.mp hx
    obtain ⟨w, rfl⟩ := mem_span_singleton'.mp hz
    refine ⟨-k, (p.shiftSnd t htI).shiftFst w, ?_, by simpa using hd, ?_⟩
    · simp only [MennickePair.shiftFst_fst, MennickePair.shiftSnd_snd, MennickePair.shiftSnd_fst]
      linear_combination hxz
    · rw [hs.map_shiftFst, hs.map_shiftSnd]

/-- **The Mennicke–Newman lemma.** Over a Dedekind domain, finitely many Mennicke symbols can be
written with a common denominator: for pairs `(aᵢ, bᵢ) ∈ W(A, I)` indexed by a finite type there
are pairs `(a, bᵢ')` with the same symbols. -/
theorem exists_common_denominator {ι : Type*} [Finite ι] (p : ι → MennickePair I) :
    ∃ (a : A) (q : ι → MennickePair I), ∀ i, (q i).fst = a ∧ of (q i) = of (p i) := by
  classical
  rcases eq_or_ne I ⊥ with rfl | hI
  · refine ⟨1, p, fun i ↦ ⟨?_, rfl⟩⟩
    simpa [sub_eq_zero] using (p i).fst_sub_one_mem
  obtain ⟨y, hyI, hy⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have := Fintype.ofFinite ι
  -- Induction on the set of pairs already given a common denominator `r`, keeping the numerators
  -- nonzero: a new pair receives the denominator `r + x β`, where `β = y ∏ bᵢ`, which changes
  -- each old denominator by a multiple of its numerator.
  suffices H : ∀ s : Finset ι, ∃ r : A, r - 1 ∈ I ∧ ∃ q : ι → MennickePair I,
      ∀ i ∈ s, (q i).fst = r ∧ (q i).snd ≠ 0 ∧ of (q i) = of (p i) by
    obtain ⟨r, -, q, hq⟩ := H Finset.univ
    exact ⟨r, q, fun i ↦ ⟨(hq i (Finset.mem_univ i)).1, (hq i (Finset.mem_univ i)).2.2⟩⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, p, by simp⟩
  | insert j s hj ih =>
    obtain ⟨r, hr, q, hq⟩ := ih
    have hβI : y * ∏ i ∈ s, (q i).snd ∈ I := I.mul_mem_right _ hyI
    have hβ : y * ∏ i ∈ s, (q i).snd ≠ 0 :=
      mul_ne_zero hy (Finset.prod_ne_zero_iff.mpr fun i hi ↦ (hq i hi).2.1)
    obtain ⟨x, q', hq'₁, hq'₂, hq'₃⟩ := exists_fst_eq_add_mul hr hβI hβ (p j)
    have hshift : ∀ i ∈ s, ∃ q'' : MennickePair I,
        q''.fst = r + x * (y * ∏ i ∈ s, (q i).snd) ∧ q''.snd = (q i).snd ∧ of q'' = of (q i) := by
      intro i hi
      obtain ⟨k, hk⟩ : (q i).snd ∣ y * ∏ i ∈ s, (q i).snd :=
        (Finset.dvd_prod_of_mem _ hi).mul_left y
      refine ⟨(q i).shiftFst (x * k), ?_, MennickePair.shiftFst_snd _ _,
        isMennickeSymbol_of.map_shiftFst _ _⟩
      rw [MennickePair.shiftFst_fst, (hq i hi).1, hk]
      ring
    choose! q'' hq'' using hshift
    refine ⟨r + x * (y * ∏ i ∈ s, (q i).snd),
      by rw [add_sub_right_comm]; exact I.add_mem hr (I.mul_mem_left _ hβI),
      fun i ↦ if i ∈ s then q'' i else q', fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simpa [hj] using ⟨hq'₁, hq'₂, hq'₃⟩
    · simp only [hi, ↓reduceIte]
      exact ⟨(hq'' i hi).1, (hq'' i hi).2.1 ▸ (hq i hi).2.1, (hq'' i hi).2.2.trans (hq i hi).2.2⟩

/-- Over a Dedekind domain any two generators of the universal Mennicke group commute: after the
Mennicke–Newman lemma they have a common denominator. -/
theorem commute_of (p q : MennickePair I) : Commute (of p) (of q) := by
  obtain ⟨a, r, hr⟩ := exists_common_denominator fun b : Bool ↦ cond b p q
  obtain ⟨h₁, h₁'⟩ := hr true
  obtain ⟨h₂, h₂'⟩ := hr false
  rw [Bool.cond_true] at h₁'
  rw [Bool.cond_false] at h₂'
  rw [← h₁', ← h₂']
  exact commute_of_of_fst_eq (h₁.trans h₂.symm)

/-- **The universal Mennicke group of a Dedekind domain is commutative.** -/
theorem commute (x y : MennickeGroup I) : Commute x y := by
  have h := Subgroup.closure_le_centralizer_centralizer (Set.range (of : MennickePair I → _))
  rw [closure_range_of] at h
  exact Set.centralizer_centralizer_comm_of_comm
    (by rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ -; exact commute_of p q) x (h (Subgroup.mem_top x)) y
    (h (Subgroup.mem_top y))

instance instIsMulCommutative : IsMulCommutative (MennickeGroup I) :=
  ⟨⟨fun x y ↦ (commute x y).eq⟩⟩

end MennickeGroup

namespace IsMennickeSymbol

variable {C : Type*} [Group C] {s : MennickePair I → C}

/-- **The values of a Mennicke symbol commute.** Over a Dedekind domain the image of a Mennicke
symbol is commutative, whatever its group of values. -/
theorem commute (hs : IsMennickeSymbol s) (p q : MennickePair I) : Commute (s p) (s q) := by
  simpa using (MennickeGroup.commute_of p q).map (MennickeGroup.lift ⟨s, hs⟩)

/-- **Lam's identity.** Over a Dedekind domain a Mennicke symbol is multiplicative in the
denominator: `[b/(a₁ a₂)] = [b/a₁] [b/a₂]` for admissible pairs `(a₁, b)` and `(a₂, b)`. -/
theorem map_eq_mul_of_fst_eq_mul (hs : IsMennickeSymbol s) {p₁ p₂ q : MennickePair I}
    (h₁ : p₁.snd = q.snd) (h₂ : p₂.snd = q.snd) (hfst : q.fst = p₁.fst * p₂.fst) :
    s q = s p₁ * s p₂ := by
  by_cases ha : p₁.fst = 1
  · rw [hs.map_eq_one_of_isUnit_fst (p := p₁) (by rw [ha]; exact isUnit_one), one_mul]
    congr 1
    ext
    · rw [hfst, ha, one_mul]
    · exact h₂.symm
  -- With `y = a₁ - 1 ≠ 0`, move `b` to `b'` with `(y) + (b') = I`, then `a₂` to `a₂' ≡ 1` modulo
  -- `y`; the identity then follows from the case of a common modulus `y`.
  have hyI := p₁.fst_sub_one_mem
  obtain ⟨t, htI, ht⟩ := IsDedekindDomain.exists_mem_sup_span_add_mul_eq
    ((span_singleton_le_iff_mem _).mpr hyI)
    (by rwa [Ne, span_singleton_eq_bot, sub_eq_zero]) q.snd_mem q.isCoprime
  obtain ⟨_, hx, _, hz, hxz⟩ := Submodule.mem_sup.mp (by rw [ht]; exact p₂.fst_sub_one_mem :
    p₂.fst - 1 ∈ span {p₁.fst - 1} ⊔ span {q.snd + t * q.fst})
  obtain ⟨k, rfl⟩ := mem_span_singleton'.mp hx
  obtain ⟨m, rfl⟩ := mem_span_singleton'.mp hz
  have H := hs.map_eq_mul_of_fst_eq_mul_of_dvd hyI (y := p₁.fst - 1)
    (p₁ := p₁.shiftSnd _ (I.mul_mem_right p₂.fst htI))
    (p₂ := (p₂.shiftSnd _ (I.mul_mem_right p₁.fst htI)).shiftFst (-m))
    (q := (q.shiftSnd t htI).shiftFst (-(p₁.fst * m))) (by simp)
    ⟨k, by
      simp only [MennickePair.shiftFst_fst, MennickePair.shiftSnd_snd, MennickePair.shiftSnd_fst]
      linear_combination -hxz - m * h₂ + m * t * hfst⟩
    (by simp only [MennickePair.shiftSnd_snd, MennickePair.shiftFst_snd]
        linear_combination h₁ - t * hfst)
    (by simp only [MennickePair.shiftSnd_snd, MennickePair.shiftFst_snd]
        linear_combination h₂ - t * hfst)
    (by simp only [MennickePair.shiftFst_fst, MennickePair.shiftSnd_snd, MennickePair.shiftSnd_fst]
        linear_combination (1 - p₁.fst * m * t) * hfst + p₁.fst * m * h₂)
  simpa only [hs.map_shiftFst, hs.map_shiftSnd] using H

end IsMennickeSymbol

end Ideal
