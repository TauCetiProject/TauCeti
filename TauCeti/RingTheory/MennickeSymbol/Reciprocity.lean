/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MennickeSymbol.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import TauCeti.RingTheory.Ideal.Quotient.Coprime
import Mathlib.Tactic.LinearCombination

/-!
# Mennicke symbols with a fixed denominator, and Kervaire reciprocity

Let `A` be a commutative ring, `I` an ideal of `A` and `a ∈ A` with `a ≡ 1` modulo `I`. The
Mennicke symbols `[b/a]` with denominator `a` only depend on `b` modulo `aI`, and they extend to a
homomorphism out of the unit group of `A ⧸ aA`: the rule `b ↦ [b q / a]`, for any `q ∈ I` with
`a ≡ 1` modulo `q`, is a well-defined homomorphism `(A ⧸ aA)ˣ → C_I`, independent of `q`, which
kills the global units of `A`. Taking `q = 1 - a` makes it canonical, and on residues of
elements `b ∈ I` it returns `[b/a]` itself. Its source is commutative, so symbols with a common
denominator commute, in any group of values.

The second result is **Kervaire reciprocity**: if `a ≡ d ≡ 1` modulo `q` and `aA + dA = A`, then
`[a q / d] = [d q / a]`. It gives Lam's multiplicativity in the denominator,
`[b/(a₁ a₂)] = [b/a₁] [b/a₂]`, whenever `a₁ ≡ a₂ ≡ 1` modulo a common element of `I`. All these
results hold over every commutative ring. Over a Dedekind domain the common modulus can always be
arranged, and symbols can be given common denominators, which yields Lam's identity in general and
the commutativity of the universal Mennicke group
(`TauCeti/RingTheory/MennickeSymbol/Dedekind.lean`).

## Main definitions

* `Ideal.MennickeGroup.unitsHom`: the homomorphism `(A ⧸ aA)ˣ →* C_I`, `b ↦ [b (1 - a) / a]`.

## Main results

* `Ideal.MennickeGroup.unitsHom_apply`: `unitsHom` sends the residue of `b` to `[b q / a]` for
  every `q ∈ I` with `q ∣ a - 1`.
* `Ideal.MennickeGroup.unitsHom_apply_eq_of`: `unitsHom` sends the residue of `b ∈ I` to `[b/a]`.
* `Ideal.MennickeGroup.unitsHom_apply_eq_one_of_isUnit`: global units are in the kernel.
* `Ideal.MennickeGroup.commute_of_of_fst_eq`, `Ideal.IsMennickeSymbol.commute_of_fst_eq`:
  symbols with the same denominator commute.
* `Ideal.IsMennickeSymbol.reciprocity`: Kervaire reciprocity `[a q / d] = [d q / a]`.
* `Ideal.IsMennickeSymbol.map_eq_mul_of_fst_eq_mul_of_dvd`: Lam's identity when both denominators
  are `≡ 1` modulo a common element of `I`.

## References

* H. Bass, J. Milnor and J.-P. Serre, *Solution of the congruence subgroup problem for `SLₙ`
  (`n ≥ 3`) and `Sp₂ₙ` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), 59–137, §2, pp. 65–71.
-/

public section

namespace Ideal

variable {A : Type*} [CommRing A] {I : Ideal A}

namespace MennickeGroup

section UnitsHom

variable {a : A} (ha : a - 1 ∈ I)

/-- The pair `(a, b (1 - a))` attached to an element `b` coprime to `a`. -/
private def pairMulOneSub {b : A} (hb : IsCoprime a b) : MennickePair I where
  fst := a
  snd := b * (1 - a)
  fst_sub_one_mem := ha
  snd_mem := I.mul_mem_left b (sub_mem_comm_iff.mp ha)
  isCoprime := hb.mul_right ⟨1, 1, by ring⟩

/-- `[b (1 - a) / a] = [b q / a]` whenever `q ∈ I` and `q ∣ a - 1`. -/
private theorem of_pairMulOneSub_eq {b : A} (hb : IsCoprime a b) {q : A} (hq : q ∈ I)
    (hqa : q ∣ a - 1) {p : MennickePair I} (hp₁ : p.fst = a) (hp₂ : p.snd = b * q) :
    of (pairMulOneSub ha hb) = of p := by
  -- `[b q / a] = [b q (1 - a) / a] = [b (1 - a) / a] [q / a]`, and `[q / a]` is trivial because
  -- `a ≡ 1` modulo `q`.
  have hs := isMennickeSymbol_of (I := I)
  obtain ⟨k, hk⟩ := hqa
  let r : MennickePair I := ⟨a, q, ha, hq, ⟨1, -k, by linear_combination hk⟩⟩
  have hr : of r = 1 := hs.map_eq_one_of_dvd_fst_sub isUnit_one ⟨k, hk⟩
  calc of (pairMulOneSub ha hb) = of (pairMulOneSub ha hb) * of r := by rw [hr, mul_one]
    _ = of p := (hs.map_mulSnd (pairMulOneSub ha hb) r rfl).symm.trans
      (hs.map_eq_of_snd_eq_mul_one_sub (by simp [pairMulOneSub, hp₁])
        (by simp [pairMulOneSub, r, hp₁, hp₂]; ring))

/-- `[b (1 - a) / a]` only depends on the residue of `b` modulo `a`. -/
private theorem of_pairMulOneSub_congr {b b' : A} (hb : IsCoprime a b) (hb' : IsCoprime a b')
    (h : b' - b ∈ span {a}) : of (pairMulOneSub ha hb') = of (pairMulOneSub ha hb) := by
  obtain ⟨k, hk⟩ := mem_span_singleton'.mp h
  refine isMennickeSymbol_of.map_eq_of_snd_eq rfl
    (I.mul_mem_left k (sub_mem_comm_iff.mp ha)) ?_
  simp only [pairMulOneSub]
  linear_combination (1 - a) * hk.symm

/-- `[b b' (1 - a) / a] = [b (1 - a) / a] [b' (1 - a) / a]`. -/
private theorem of_pairMulOneSub_mul {b b' : A} (hb : IsCoprime a b) (hb' : IsCoprime a b') :
    of (pairMulOneSub ha (hb.mul_right hb')) =
      of (pairMulOneSub ha hb) * of (pairMulOneSub ha hb') :=
  -- The product `b (1 - a) b' (1 - a)` is `b b' (1 - a)` times `1 - a`.
  (isMennickeSymbol_of.map_eq_of_snd_eq_mul_one_sub
    (q := (pairMulOneSub ha hb).mulSnd (pairMulOneSub ha hb') rfl)
    (p := pairMulOneSub ha (hb.mul_right hb')) (by simp [pairMulOneSub])
    (by simp [pairMulOneSub]; ring)).symm.trans
    (isMennickeSymbol_of.map_mulSnd (pairMulOneSub ha hb) (pairMulOneSub ha hb') rfl)

/-- A representative in `A` of a residue class modulo `a`. -/
private noncomputable def rep (x : A ⧸ span {a}) : A :=
  Function.surjInv Quotient.mk_surjective x

private theorem mk_rep (x : A ⧸ span {a}) : Quotient.mk (span {a}) (rep x) = x :=
  Function.surjInv_eq Quotient.mk_surjective x

private theorem isCoprime_rep (u : (A ⧸ span {a})ˣ) : IsCoprime a (rep (u : A ⧸ span {a})) :=
  Quotient.isUnit_mk_span_singleton_iff.mp (by rw [mk_rep]; exact u.isUnit)

/-- The **Mennicke symbol on residues** with denominator `a ≡ 1` modulo `I`: the homomorphism
`(A ⧸ aA)ˣ →* C_I` sending the residue of `b` to `[b (1 - a) / a]`. By
`Ideal.MennickeGroup.unitsHom_apply` it equally sends `b` to `[b q / a]` for every `q ∈ I` with
`a ≡ 1` modulo `q`, and by `Ideal.MennickeGroup.unitsHom_apply_eq_of` it sends the residue of
`b ∈ I` to `[b/a]`. -/
noncomputable def unitsHom : (A ⧸ span {a})ˣ →* MennickeGroup I where
  toFun u := of (pairMulOneSub ha (isCoprime_rep u))
  map_one' := (of_pairMulOneSub_congr ha isCoprime_one_right (isCoprime_rep 1)
      (Quotient.eq.mp (by rw [mk_rep, Units.val_one, map_one]))).trans
    (isMennickeSymbol_of.map_eq_one_of_dvd_fst_sub isUnit_one ⟨-1, by simp [pairMulOneSub]⟩)
  map_mul' u v := (of_pairMulOneSub_congr ha ((isCoprime_rep u).mul_right (isCoprime_rep v))
      (isCoprime_rep (u * v))
      (Quotient.eq.mp (by rw [mk_rep, map_mul, mk_rep, mk_rep, Units.val_mul]))).trans
    (of_pairMulOneSub_mul ha _ _)

private theorem unitsHom_apply_def (u : (A ⧸ span {a})ˣ) :
    unitsHom ha u = of (pairMulOneSub ha (isCoprime_rep u)) :=
  (rfl)

/-- **The value of `unitsHom` with an arbitrary auxiliary element.** If `q ∈ I` and `a ≡ 1` modulo
`q`, then `unitsHom` sends the residue of `b` to `[b q / a]`; in particular this symbol does not
depend on `q`, nor on the representative `b`. -/
theorem unitsHom_apply {u : (A ⧸ span {a})ˣ} {b : A}
    (hu : (u : A ⧸ span {a}) = Quotient.mk (span {a}) b) {q : A} (hq : q ∈ I) (hqa : q ∣ a - 1)
    {p : MennickePair I} (hp₁ : p.fst = a) (hp₂ : p.snd = b * q) : unitsHom ha u = of p := by
  have hb : IsCoprime a b := Quotient.isUnit_mk_span_singleton_iff.mp (hu ▸ u.isUnit)
  rw [unitsHom_apply_def,
    of_pairMulOneSub_congr ha hb (isCoprime_rep u) (by rw [← Quotient.eq, mk_rep, hu]),
    of_pairMulOneSub_eq ha hb hq hqa hp₁ hp₂]

/-- `unitsHom` sends the residue of the second entry of a pair `(a, b)` to `[b/a]`. -/
theorem unitsHom_apply_eq_of {u : (A ⧸ span {a})ˣ} {p : MennickePair I} (hp : p.fst = a)
    (hu : (u : A ⧸ span {a}) = Quotient.mk (span {a}) p.snd) : unitsHom ha u = of p := by
  rw [unitsHom_apply ha hu (q := 1 - a) (sub_mem_comm_iff.mp ha) ⟨-1, by ring⟩
    (p := ⟨a, p.snd * (1 - a), ha, I.mul_mem_right _ p.snd_mem,
      (by rw [← hp]; exact p.isCoprime.mul_right ⟨1, 1, by ring⟩)⟩) rfl rfl]
  exact isMennickeSymbol_of.map_eq_of_snd_eq_mul_one_sub hp.symm (by dsimp only; rw [hp])

/-- `unitsHom` kills the global units: it is trivial on the residue of a unit of `A`. -/
theorem unitsHom_apply_eq_one_of_isUnit {u : (A ⧸ span {a})ˣ} {v : A} (hv : IsUnit v)
    (hu : (u : A ⧸ span {a}) = Quotient.mk (span {a}) v) : unitsHom ha u = 1 := by
  have hb : IsCoprime a v := Quotient.isUnit_mk_span_singleton_iff.mp (hu ▸ u.isUnit)
  rw [unitsHom_apply_def,
    of_pairMulOneSub_congr ha hb (isCoprime_rep u) (by rw [← Quotient.eq, mk_rep, hu])]
  exact isMennickeSymbol_of.map_eq_one_of_dvd_snd_sub hv ⟨-v, by simp [pairMulOneSub]; ring⟩

/-- Every generator `[b/a]` with denominator `a` lies in the image of `unitsHom`. -/
theorem of_mem_range_unitsHom {p : MennickePair I} (hp : p.fst = a) :
    of p ∈ (unitsHom ha).range := by
  have h : IsUnit (Quotient.mk (span {a}) p.snd) :=
    Quotient.isUnit_mk_span_singleton_iff.mpr (by rw [← hp]; exact p.isCoprime)
  exact ⟨h.unit, unitsHom_apply_eq_of ha hp rfl⟩

end UnitsHom

/-- **Symbols with a common denominator commute** in the universal Mennicke group: both lie in
the image of `unitsHom` of that denominator, whose source is commutative. -/
theorem commute_of_of_fst_eq {p q : MennickePair I} (h : p.fst = q.fst) :
    Commute (of p) (of q) := by
  obtain ⟨u, hu⟩ := of_mem_range_unitsHom p.fst_sub_one_mem (p := p) rfl
  obtain ⟨v, hv⟩ := of_mem_range_unitsHom p.fst_sub_one_mem h.symm
  rw [← hu, ← hv]
  exact (Commute.all u v).map _

end MennickeGroup

namespace IsMennickeSymbol

variable {C : Type*} [Group C] {s : MennickePair I → C}

/-- **Symbols with a common denominator commute**, for Mennicke symbols with values in any
group. -/
theorem commute_of_fst_eq (hs : IsMennickeSymbol s) {p q : MennickePair I} (h : p.fst = q.fst) :
    Commute (s p) (s q) := by
  simpa using (MennickeGroup.commute_of_of_fst_eq h).map (MennickeGroup.lift ⟨s, hs⟩)

/-- **Kervaire reciprocity.** If `a ≡ d ≡ 1` modulo `q`, then `[a q / d] = [d q / a]`, for the
pairs `(d, a q)` and `(a, d q)` of `W(A, I)`. That `q ∈ I` and `aA + dA = A` follow from the
admissibility of the two pairs. -/
theorem reciprocity (hs : IsMennickeSymbol s) {p p' : MennickePair I} {q : A}
    (hq : q ∣ p.fst - 1) (hq' : q ∣ p'.fst - 1) (hp : p.snd = p'.fst * q)
    (hp' : p'.snd = p.fst * q) : s p = s p' := by
  -- With `d = p.fst`, `a = p'.fst` and `e = a - d`, both symbols reduce to `[e/a]`:
  -- `[a q / d] = [q (a - d) / d] = [q/d] [e/d] = [e/a]` and
  -- `[d q / a] = [q (d - a) / a] = [q/a] [-e/a] = [e/a]`.
  obtain ⟨k, hk⟩ := hq
  obtain ⟨k', hk'⟩ := hq'
  have hqI : q ∈ I := by
    rw [show q = p.snd - (p'.fst - 1) * q by rw [hp]; ring]
    exact I.sub_mem p.snd_mem (I.mul_mem_right _ p'.fst_sub_one_mem)
  obtain ⟨u, v, huv⟩ : IsCoprime p.fst p'.fst := by
    have h := p.isCoprime
    rw [hp] at h
    exact h.of_mul_right_left
  have heI : p'.fst - p.fst ∈ I := by
    rw [show p'.fst - p.fst = (p'.fst - 1) - (p.fst - 1) by ring]
    exact I.sub_mem p'.fst_sub_one_mem p.fst_sub_one_mem
  let rdq : MennickePair I := ⟨p.fst, q, p.fst_sub_one_mem, hqI, ⟨1, -k, by linear_combination hk⟩⟩
  let raq : MennickePair I :=
    ⟨p'.fst, q, p'.fst_sub_one_mem, hqI, ⟨1, -k', by linear_combination hk'⟩⟩
  let rde : MennickePair I := ⟨p.fst, p'.fst - p.fst, p.fst_sub_one_mem, heI,
    ⟨u + v, v, by linear_combination huv⟩⟩
  let rae : MennickePair I := ⟨p'.fst, p'.fst - p.fst, p'.fst_sub_one_mem, heI,
    ⟨u + v, -u, by linear_combination huv⟩⟩
  let rane : MennickePair I := ⟨p'.fst, p.fst - p'.fst, p'.fst_sub_one_mem,
    sub_mem_comm_iff.mp heI, ⟨u + v, u, by linear_combination huv⟩⟩
  have h₁ : s p = s rae := by
    rw [← hs.map_shiftSnd p (-q) (I.neg_mem hqI),
      hs.map_eq_mul_of_snd_eq_mul (p₁ := rdq) (p₂ := rde) (q := p.shiftSnd (-q) (I.neg_mem hqI))
        (by simp [rdq]) (by simp [rde]) (by simp [rdq, rde, hp]; ring),
      hs.map_eq_one_of_dvd_fst_sub isUnit_one ⟨k, hk⟩, one_mul]
    exact (hs.map_eq_of_fst_eq (p := rde) (q := rae) 1 (by simp [rde, rae]) rfl).symm
  have h₂ : s p' = s rae := by
    rw [← hs.map_shiftSnd p' (-q) (I.neg_mem hqI),
      hs.map_eq_mul_of_snd_eq_mul (p₁ := raq) (p₂ := rane) (q := p'.shiftSnd (-q) (I.neg_mem hqI))
        (by simp [raq]) (by simp [rane]) (by simp [raq, rane, hp']; ring),
      hs.map_eq_one_of_dvd_fst_sub isUnit_one ⟨k', hk'⟩, one_mul]
    exact hs.map_eq_of_snd_eq_neg (p := rae) (q := rane) rfl (by simp [rane, rae])
  rw [h₁, h₂]

/-- Lam's identity for numerators of the form `d y` with `a₁ ≡ a₂ ≡ d ≡ 1` modulo `y`: by
reciprocity it is the multiplicativity of `[a y / d]` in `a`. -/
private theorem map_eq_mul_of_fst_eq_mul_of_snd_eq_mul (hs : IsMennickeSymbol s)
    {p₁ p₂ q : MennickePair I} {y d : A} (hy : y ∈ I) (h₁ : y ∣ p₁.fst - 1)
    (h₂ : y ∣ p₂.fst - 1) (hd : y ∣ d - 1) (hfst : q.fst = p₁.fst * p₂.fst)
    (hp₁ : p₁.snd = d * y) (hp₂ : p₂.snd = d * y) (hq : q.snd = d * y) : s q = s p₁ * s p₂ := by
  obtain ⟨k, hk⟩ := hd
  have hdI : d - 1 ∈ I := hk ▸ I.mul_mem_right k hy
  have hdy : IsCoprime d y := ⟨1, -k, by linear_combination hk⟩
  -- The pair `(d, a y)` attached to a pair `(a, d y)`.
  have hD : ∀ r : MennickePair I, y ∣ r.fst - 1 → r.snd = d * y →
      ∃ D : MennickePair I, D.fst = d ∧ D.snd = r.fst * y ∧ s D = s r := by
    intro r hry hr
    have hcop : IsCoprime d (r.fst * y) := by
      have h := r.isCoprime
      rw [hr] at h
      exact h.of_mul_right_left.symm.mul_right hdy
    exact ⟨⟨d, r.fst * y, hdI, I.mul_mem_left _ hy, hcop⟩, rfl, rfl,
      hs.reciprocity ⟨k, hk⟩ (q := y) (p' := r) hry rfl (by rw [hr])⟩
  have hqy : y ∣ q.fst - 1 := by simpa [hfst] using dvd_mul_sub_mul h₁ h₂
  obtain ⟨D₁, hD₁, hD₁', hsD₁⟩ := hD p₁ h₁ hp₁
  obtain ⟨D₂, hD₂, hD₂', hsD₂⟩ := hD p₂ h₂ hp₂
  obtain ⟨Dq, hDq, hDq', hsDq⟩ := hD q hqy hq
  let Dy : MennickePair I := ⟨d, y, hdI, hy, hdy⟩
  have hDy : s Dy = 1 := hs.map_eq_one_of_dvd_fst_sub isUnit_one ⟨k, hk⟩
  have h := hs.map_eq_mul_of_snd_eq_mul (p₁ := D₁) (p₂ := D₂) (q := Dq.mulSnd Dy hDq)
    (by simp [hD₁, hDq]) (by simp [hD₂, hDq]) (by simp [Dy, hD₁', hD₂', hDq', hfst]; ring)
  rw [hs.map_mulSnd, hDy, mul_one, hsD₁, hsD₂, hsDq] at h
  exact h

/-- **Lam's identity when both denominators are `≡ 1` modulo a common `y ∈ I`:**
`[b/(a₁ a₂)] = [b/a₁] [b/a₂]`. Over a Dedekind domain the hypothesis can always be arranged,
which gives `Ideal.IsMennickeSymbol.map_eq_mul_of_fst_eq_mul`. -/
theorem map_eq_mul_of_fst_eq_mul_of_dvd (hs : IsMennickeSymbol s) {p₁ p₂ q : MennickePair I}
    {y : A} (hy : y ∈ I) (hy₁ : y ∣ p₁.fst - 1) (hy₂ : y ∣ p₂.fst - 1) (h₁ : p₁.snd = q.snd)
    (h₂ : p₂.snd = q.snd) (hfst : q.fst = p₁.fst * p₂.fst) : s q = s p₁ * s p₂ := by
  -- With `a₁ a₂ = 1 + y e`, adding `t a₁ a₂` with `t = (y - b) (1 - y e) ∈ I` to `b` turns it
  -- into `y d` with `d = 1 - (y - b) y e² ≡ 1` modulo `y`.
  obtain ⟨e, he⟩ : y ∣ p₁.fst * p₂.fst - 1 := by simpa using dvd_mul_sub_mul hy₁ hy₂
  have ht : (y - q.snd) * (1 - y * e) ∈ I := I.mul_mem_right _ (I.sub_mem hy q.snd_mem)
  have H := map_eq_mul_of_fst_eq_mul_of_snd_eq_mul hs (y := y) (d := 1 - (y - q.snd) * y * e ^ 2)
    (p₁ := p₁.shiftSnd _ (I.mul_mem_right p₂.fst ht))
    (p₂ := p₂.shiftSnd _ (I.mul_mem_right p₁.fst ht)) (q := q.shiftSnd _ ht) hy
    (by simpa using hy₁) (by simpa using hy₂) ⟨-((y - q.snd) * e ^ 2), by ring⟩
    (by simpa using hfst)
    (by simp only [MennickePair.shiftSnd_snd]
        linear_combination h₁ + (y - q.snd) * (1 - y * e) * he)
    (by simp only [MennickePair.shiftSnd_snd]
        linear_combination h₂ + (y - q.snd) * (1 - y * e) * he)
    (by simp only [MennickePair.shiftSnd_snd]
        linear_combination (y - q.snd) * (1 - y * e) * hfst + (y - q.snd) * (1 - y * e) * he)
  simpa only [hs.map_shiftSnd] using H

end IsMennickeSymbol

end Ideal
