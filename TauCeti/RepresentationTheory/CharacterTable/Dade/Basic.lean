/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import TauCeti.GroupTheory.TrivialIntersection
public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
import TauCeti.GroupTheory.OrderOfElement.Basic

/-!
# Dade data and the Dade support

Let `L` be a subgroup of a group `G` and `A ⊆ L` a subset avoiding `1`. **Dade data** for `L`,
`A` and a family of subgroups `H : G → Subgroup G` (`TauCeti.DadeDatum L A H`) ask that `A` be
stable under conjugation by `L`, that two elements of `A` conjugate in `G` be conjugate in `L`,
and that for each `a ∈ A` the centralizer `C_G(a)` split as `H a ⋊ C_L(a)`, with `H a` normal in
`C_G(a)`, of order prime to `|C_L(b)|` for every `b ∈ A`. This is Peterfalvi's Definition (2.2),
Feit and Thompson's "tamely imbedded subset" (Definition 9.1, with the `H a` as the complements).
It is the input of the Dade isometry, which extends class functions of `L` vanishing off `A` to
class functions of `G`: the value of the extension at a conjugate of `a * u`, `u ∈ H a`, is the
value at `a`. This file proves the group theory that makes that extension well defined, namely
Peterfalvi's (2.4), and sets up the space of class functions it is defined on.

The coprimality makes `a` the part of `a * u` of order dividing `|C_L(a)|`, recoverable from the
product (`Commute.eq_of_mul_eq_mul_of_coprime`). Hence the cosets `a • H a` are disjoint up to
conjugacy unless their base points are `L`-conjugate (`TauCeti.DadeDatum.conj_mul_eq_mul_iff`),
and the complement `H a` is determined by the rest of the data.

## Main definitions

* `TauCeti.DadeDatum L A H`: Dade data for `L`, `A` and the complements `H`.
* `TauCeti.dadeSupport A H`: the **Dade support**, the set of `G`-conjugates of the elements
  `a * u` with `a ∈ A` and `u ∈ H a`.
* `TauCeti.supportedClassFunctions k L A`: the class functions of `L` vanishing outside `A`,
  written `CF(L, A)` by Peterfalvi.

## Main results

* `TauCeti.DadeDatum.conj_mul_eq_mul_iff`: a conjugate of `a * u` equals `b * v` exactly when the
  same conjugation takes `a` to `b` and `u` to `v`.
* `TauCeti.DadeDatum.le_of_coprime`, `TauCeti.DadeDatum.eq_of_mul_eq_centralizer`: `H a` contains
  every subgroup of `C_G(a)` of order prime to `|C_L(a)|`, and is the only complement to `C_L(a)`
  in `C_G(a)` of such order.
* `TauCeti.DadeDatum.conj_eq`: `H (l * a * l⁻¹) = l (H a) l⁻¹` for `l ∈ L` (Peterfalvi (2.4)(a)).
* `TauCeti.DadeDatum.disjoint_conjugatesOfSet_iff`,
  `TauCeti.DadeDatum.conjugatesOfSet_conj_smul`: the Dade supports at `a` and `b` are disjoint
  unless `a` and `b` are `L`-conjugate, in which case they coincide (Peterfalvi (2.4)(b)).
* `TauCeti.DadeDatum.normalizer_smul_eq`, `TauCeti.DadeDatum.isTISet_smul`: the coset `a • H a`
  has normalizer `C_G(a)` and is a trivial-intersection set for it (Peterfalvi (2.4)(c)).
* `TauCeti.DadeDatum.one_notMem_dadeSupport`: the Dade support avoids `1`.
* `TauCeti.DadeDatum.isTISet`, `TauCeti.DadeDatum.normalizer_eq`, `TauCeti.IsTISet.dadeDatum`:
  Dade data with trivial complements are the same as trivial-intersection sets for `L` avoiding
  `1`, and such a nonempty set has normalizer `L` (Peterfalvi (2.3)).
* `TauCeti.finrank_supportedClassFunctions`: `CF(L, A)` has dimension the number of conjugacy
  classes of `L` contained in `A`.

## Implementation notes

The complement at `a` is a subgroup of `G`; its normality in `C_G(a)` is phrased through
`Subgroup.subgroupOf`, and `C_L(a)` is `L ⊓ Subgroup.centralizer {a}`. No statement assumes `G`
finite: for infinite centralizers the cardinalities are `0`, and the coprimality clause then forces
the complements to be trivial, which the arguments handle uniformly.

## References

* T. Peterfalvi, *Character Theory for the Odd Order Theorem*, LMS Lecture Note Series 272,
  Cambridge University Press (2000), Part I, §2.
* W. Feit and J. G. Thompson, *Solvability of groups of odd order*, Pacific J. Math. 13 (1963),
  Chapter III, §9.
-/

public section

namespace TauCeti

open scoped Pointwise
open Subgroup

variable {G : Type*} [Group G]

/-- **Dade data** for a subgroup `L` and a subset `A ⊆ L \ {1}` (Peterfalvi, Definition (2.2);
Feit–Thompson, Definition 9.1, "tamely imbedded"): `A` is stable under conjugation by `L`, `L`
controls `G`-fusion in `A`, and for each `a ∈ A` the subgroup `H a` is a normal subgroup of
`C_G(a)` with `C_G(a) = H a ⋊ C_L(a)` and `|H a|` prime to `|C_L(b)|` for every `b ∈ A`.
Only the values of `H` on `A` are constrained. -/
structure DadeDatum (L : Subgroup G) (A : Set G) (H : G → Subgroup G) : Prop where
  /-- The set lies in `L` and avoids `1`. -/
  subset : A ⊆ (L : Set G) \ {1}
  /-- The set is stable under conjugation by `L`. -/
  conj_mem : ∀ a ∈ A, ∀ l ∈ L, l * a * l⁻¹ ∈ A
  /-- `L` controls `G`-fusion in the set: elements conjugate in `G` are conjugate in `L`. -/
  fusion : ∀ a ∈ A, ∀ b ∈ A, IsConj a b → ∃ l ∈ L, l * a * l⁻¹ = b
  /-- Each complement centralizes its base point. -/
  le_centralizer : ∀ a ∈ A, H a ≤ centralizer {a}
  /-- Each complement is normal in the centralizer of its base point. -/
  normal : ∀ a ∈ A, ((H a).subgroupOf (centralizer {a})).Normal
  /-- Each complement meets `C_L(a)` trivially. -/
  inf_eq_bot : ∀ a ∈ A, H a ⊓ (L ⊓ centralizer {a}) = ⊥
  /-- Each complement and `C_L(a)` together make up `C_G(a)`. -/
  mul_eq_centralizer : ∀ a ∈ A,
    (H a : Set G) * ((L ⊓ centralizer {a} : Subgroup G) : Set G) = centralizer {a}
  /-- The orders of the complements are prime to the orders of the centralizers in `L`. -/
  coprime : ∀ a ∈ A, ∀ b ∈ A,
    (Nat.card (H a)).Coprime (Nat.card (L ⊓ centralizer {b} : Subgroup G))

/-- The **Dade support** of `A` and `H`: the `G`-conjugates of the elements `a * u` with `a ∈ A`
and `u ∈ H a`, the union over `a ∈ A` of the Dade supports `(a H_a)^G` at single points. -/
def dadeSupport (A : Set G) (H : G → Subgroup G) : Set G :=
  Group.conjugatesOfSet (⋃ a ∈ A, a • (H a : Set G))

/-- An element of the conjugates of a coset `a • K` is a conjugate of some `a * u`, `u ∈ K`. -/
theorem mem_conjugatesOfSet_smul_iff {a x : G} {K : Subgroup G} :
    x ∈ Group.conjugatesOfSet (a • (K : Set G)) ↔ ∃ u ∈ K, IsConj (a * u) x := by
  simp [Group.mem_conjugatesOfSet_iff, Set.mem_smul_set]

/-- Membership in the Dade support. -/
theorem mem_dadeSupport_iff {A : Set G} {H : G → Subgroup G} {x : G} :
    x ∈ dadeSupport A H ↔ ∃ a ∈ A, ∃ u ∈ H a, IsConj (a * u) x := by
  simp only [dadeSupport, Group.mem_conjugatesOfSet_iff, Set.mem_iUnion, Set.mem_smul_set,
    SetLike.mem_coe, smul_eq_mul]
  grind

namespace DadeDatum

variable {L : Subgroup G} {A : Set G} {H : G → Subgroup G} {a b : G}

/-- A base point lies in its own centralizer in `L`. -/
theorem mem_inf_centralizer (hD : DadeDatum L A H) (ha : a ∈ A) :
    a ∈ L ⊓ centralizer {a} :=
  mem_inf.2 ⟨(hD.subset ha).1, mem_centralizer_singleton_iff.2 (Commute.refl a)⟩

/-- **A conjugate of `a * u` determines the conjugate of `a`.** For `a, b ∈ A`, `u ∈ H a` and
`v ∈ H b`, conjugation by `g` takes `a * u` to `b * v` exactly when it takes `a` to `b` and `u` to
`v`: the coprimality clause makes `a` the part of `a * u` of order dividing `|C_L(a)|`. -/
theorem conj_mul_eq_mul_iff (hD : DadeDatum L A H) (ha : a ∈ A) (hb : b ∈ A) {u v : G}
    (hu : u ∈ H a) (hv : v ∈ H b) (g : G) :
    g * (a * u) * g⁻¹ = b * v ↔ g * a * g⁻¹ = b ∧ g * u * g⁻¹ = v := by
  refine ⟨fun h => ?_, fun ⟨hab, huv⟩ => by rw [← hab, ← huv]; group⟩
  have hpow {x : G} {K : Subgroup G} (hx : x ∈ K) : x ^ Nat.card K = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (K.orderOf_dvd_natCard hx)
  have hconj : MulAut.conj g a * MulAut.conj g u = b * v := by
    rw [← map_mul, MulAut.conj_apply, h]
  have hcop : (Nat.card (L ⊓ centralizer {a} : Subgroup G) *
      Nat.card (L ⊓ centralizer {b} : Subgroup G)).Coprime (Nat.card (H a) * Nat.card (H b)) :=
    .mul_left (.mul_right (hD.coprime a ha a ha).symm (hD.coprime b hb a ha).symm)
      (.mul_right (hD.coprime a ha b hb).symm (hD.coprime b hb b hb).symm)
  have hab : MulAut.conj g a = b := by
    refine Commute.eq_of_mul_eq_mul_of_coprime
      ((mem_centralizer_singleton_iff.1 (hD.le_centralizer a ha hu)).symm.map (MulAut.conj g))
      (mem_centralizer_singleton_iff.1 (hD.le_centralizer b hb hv)).symm hcop ?_ ?_ ?_ ?_ hconj
    · rw [← map_pow, pow_mul, hpow (hD.mem_inf_centralizer ha), one_pow, map_one]
    · rw [mul_comm, pow_mul, hpow (hD.mem_inf_centralizer hb), one_pow]
    · rw [← map_pow, pow_mul, hpow hu, one_pow, map_one]
    · rw [mul_comm, pow_mul, hpow hv, one_pow]
  rw [hab] at hconj
  exact ⟨hab, mul_left_cancel hconj⟩

/-- **`H b` contains every subgroup of `C_G(b)` of order prime to `|C_L(b)|`.** Modulo `H b`,
each element of such a subgroup is congruent to an element of `C_L(b)`, so its image in
`C_G(b) ⧸ H b` has order dividing both cardinalities. -/
theorem le_of_coprime (hD : DadeDatum L A H) (hb : b ∈ A) {K : Subgroup G}
    (hK : K ≤ centralizer {b})
    (hcop : (Nat.card K).Coprime (Nat.card (L ⊓ centralizer {b} : Subgroup G))) : K ≤ H b := by
  intro k hk
  have hkC := hK hk
  rw [← SetLike.mem_coe, ← hD.mul_eq_centralizer b hb] at hkC
  obtain ⟨h, hh, c, hc, rfl⟩ := Set.mem_mul.1 hkC
  suffices hcH : c ∈ H b by
    have hc1 : c = 1 := by
      simpa [hD.inf_eq_bot b hb] using (mem_inf.2 ⟨hcH, hc⟩ : c ∈ H b ⊓ (L ⊓ centralizer {b}))
    simpa [hc1] using hh
  have := hD.normal b hb
  let N := (H b).subgroupOf (centralizer {b})
  let c' : centralizer {b} := ⟨c, (mem_inf.1 hc).2⟩
  let k' : centralizer {b} := ⟨h * c, hK hk⟩
  have hmk : (k' : centralizer {b} ⧸ N) = (c' : centralizer {b} ⧸ N) := by
    have hk' : k' = ⟨h, hD.le_centralizer b hb hh⟩ * c' := rfl
    rw [hk', QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hh), one_mul]
  have hord : orderOf (c' : centralizer {b} ⧸ N) = 1 := by
    refine Nat.eq_one_of_dvd_coprimes hcop ?_ ?_
    · rw [← hmk]
      refine (orderOf_map_dvd (QuotientGroup.mk' N) k').trans ?_
      rw [← orderOf_submonoid k']
      exact K.orderOf_dvd_natCard hk
    · refine (orderOf_map_dvd (QuotientGroup.mk' N) c').trans ?_
      rw [← orderOf_submonoid c']
      exact (L ⊓ centralizer {b}).orderOf_dvd_natCard hc
  have hc'N : c' ∈ N := (QuotientGroup.eq_one_iff c').1 (orderOf_eq_one_iff.1 hord)
  exact mem_subgroupOf.1 hc'N

/-- **The complement is determined by the data.** A subgroup `K` with `K * C_L(a) = C_G(a)` and
`|K|` prime to `|C_L(a)|` is `H a`. -/
theorem eq_of_mul_eq_centralizer (hD : DadeDatum L A H) (ha : a ∈ A) {K : Subgroup G}
    (hmul : (K : Set G) * ((L ⊓ centralizer {a} : Subgroup G) : Set G) = centralizer {a})
    (hcop : (Nat.card K).Coprime (Nat.card (L ⊓ centralizer {a} : Subgroup G))) : K = H a := by
  have hKC : K ≤ centralizer {a} := fun k hk => by
    rw [← SetLike.mem_coe, ← hmul]
    simpa using Set.mul_mem_mul hk (one_mem (L ⊓ centralizer {a}))
  have hKH := hD.le_of_coprime ha hKC hcop
  refine le_antisymm hKH fun h hh => ?_
  have hhC : h ∈ (centralizer {a} : Set G) := hD.le_centralizer a ha hh
  rw [← hmul] at hhC
  obtain ⟨k, hk, c, hc, rfl⟩ := Set.mem_mul.1 hhC
  have hcH : c ∈ H a := by simpa using (H a).mul_mem ((H a).inv_mem (hKH hk)) hh
  have hc1 : c = 1 := by
    simpa [hD.inf_eq_bot a ha] using (mem_inf.2 ⟨hcH, hc⟩ : c ∈ H a ⊓ (L ⊓ centralizer {a}))
  simpa [hc1] using hk

/-- The conjugate of `H a` by `l ∈ L` lies in the complement at `l * a * l⁻¹`. -/
theorem conj_smul_le (hD : DadeDatum L A H) (ha : a ∈ A) {l : G} (hl : l ∈ L) :
    MulAut.conj l • H a ≤ H (l * a * l⁻¹) := by
  have hb := hD.conj_mem a ha l hl
  refine hD.le_of_coprime hb (fun x hx => ?_) ?_
  · obtain ⟨u, hu, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).1 hx
    have hua := mem_centralizer_singleton_iff.1 (hD.le_centralizer a ha hu)
    exact mem_centralizer_singleton_iff.2 (by simpa using hua.map (MulAut.conj l))
  · rw [← Nat.card_congr (equivSMul (MulAut.conj l) (H a)).toEquiv]
    exact hD.coprime a ha _ hb

/-- **Conjugation by `L` transports the complements** (Peterfalvi (2.4)(a)):
`H (l * a * l⁻¹) = l (H a) l⁻¹` for `l ∈ L`. -/
theorem conj_eq (hD : DadeDatum L A H) (ha : a ∈ A) {l : G} (hl : l ∈ L) :
    H (l * a * l⁻¹) = MulAut.conj l • H a := by
  refine le_antisymm ?_ (hD.conj_smul_le ha hl)
  have h := hD.conj_smul_le (hD.conj_mem a ha l hl) (L.inv_mem hl)
  rw [show l⁻¹ * (l * a * l⁻¹) * l⁻¹⁻¹ = a by group, map_inv] at h
  exact subset_pointwise_smul_iff.2 h

/-- Conjugation by `L` moves the Dade support at `a` to the Dade support at `l * a * l⁻¹`
without changing it: the second half of Peterfalvi (2.4)(b). -/
theorem conjugatesOfSet_conj_smul (hD : DadeDatum L A H) (ha : a ∈ A) {l : G} (hl : l ∈ L) :
    Group.conjugatesOfSet ((l * a * l⁻¹) • (H (l * a * l⁻¹) : Set G)) =
      Group.conjugatesOfSet (a • (H a : Set G)) := by
  ext x
  simp only [mem_conjugatesOfSet_smul_iff, hD.conj_eq ha hl, mem_smul_pointwise_iff_exists,
    MulAut.smul_def, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, hx⟩
    exact ⟨u, hu, (isConj_iff.2 ⟨l, by group⟩).trans hx⟩
  · rintro ⟨u, hu, hx⟩
    exact ⟨_, ⟨u, hu, rfl⟩, (isConj_iff.2 ⟨l⁻¹, by group⟩).trans hx⟩

/-- **The Dade supports at two points are disjoint unless the points are `L`-conjugate**
(Peterfalvi (2.4)(b)); in that case they coincide, by
`TauCeti.DadeDatum.conjugatesOfSet_conj_smul`. -/
theorem disjoint_conjugatesOfSet_iff (hD : DadeDatum L A H) (ha : a ∈ A) (hb : b ∈ A) :
    Disjoint (Group.conjugatesOfSet (a • (H a : Set G)))
        (Group.conjugatesOfSet (b • (H b : Set G))) ↔
      ¬ ∃ l ∈ L, l * a * l⁻¹ = b := by
  constructor
  · rintro hdis ⟨l, hl, rfl⟩
    rw [hD.conjugatesOfSet_conj_smul ha hl, disjoint_self, Set.bot_eq_empty] at hdis
    exact (Set.eq_empty_iff_forall_notMem.1 hdis) a
      (mem_conjugatesOfSet_smul_iff.2 ⟨1, one_mem _, by simpa using IsConj.refl a⟩)
  · refine fun hnot => Set.disjoint_left.2 fun x hxa hxb => hnot ?_
    obtain ⟨u, hu, hux⟩ := mem_conjugatesOfSet_smul_iff.1 hxa
    obtain ⟨v, hv, hvx⟩ := mem_conjugatesOfSet_smul_iff.1 hxb
    obtain ⟨g, hg⟩ := isConj_iff.1 (hux.trans hvx.symm)
    exact hD.fusion a ha b hb (isConj_iff.2 ⟨g, ((hD.conj_mul_eq_mul_iff ha hb hu hv g).1 hg).1⟩)

/-- The centralizer of `a` normalizes the coset `a • H a`. -/
theorem conj_mem_smul (hD : DadeDatum L A H) (ha : a ∈ A) {g x : G} (hg : g ∈ centralizer {a})
    (hx : x ∈ a • (H a : Set G)) : g * x * g⁻¹ ∈ a • (H a : Set G) := by
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.1 hx
  have hga : g * a * g⁻¹ = a := by
    rw [(mem_centralizer_singleton_iff.1 hg).eq, mul_inv_cancel_right]
  refine Set.mem_smul_set.2 ⟨g * u * g⁻¹, ?_, ?_⟩
  · exact (normal_subgroupOf_iff (hD.le_centralizer a ha)).1 (hD.normal a ha) u g hu hg
  · rw [smul_eq_mul, smul_eq_mul]
    nth_rw 1 [← hga]
    group

/-- An element conjugating a point of the coset `a • H a` back into it centralizes `a`. -/
theorem mem_centralizer_of_conj_mem_smul (hD : DadeDatum L A H) (ha : a ∈ A) {g x : G}
    (hx : x ∈ a • (H a : Set G)) (hgx : g * x * g⁻¹ ∈ a • (H a : Set G)) :
    g ∈ centralizer {a} := by
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.1 hx
  obtain ⟨v, hv, hvx⟩ := Set.mem_smul_set.1 hgx
  have hga := ((hD.conj_mul_eq_mul_iff ha ha hu hv g).1 hvx.symm).1
  exact mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hga)

/-- **The normalizer of the coset `a • H a` is `C_G(a)`** (Peterfalvi (2.4)(c)). -/
theorem normalizer_smul_eq (hD : DadeDatum L A H) (ha : a ∈ A) :
    normalizer (a • (H a : Set G)) = centralizer {a} := by
  have ha1 : a ∈ a • (H a : Set G) := Set.mem_smul_set.2 ⟨1, one_mem _, mul_one a⟩
  refine le_antisymm (fun g hg => hD.mem_centralizer_of_conj_mem_smul ha ha1
    ((mem_set_normalizer_iff.1 hg a).1 ha1)) fun g hg => mem_set_normalizer_iff.2 fun x => ?_
  refine ⟨hD.conj_mem_smul ha hg, fun hx => ?_⟩
  simpa [mul_assoc] using hD.conj_mem_smul ha (inv_mem hg) hx

/-- **The coset `a • H a` is a trivial-intersection set for `C_G(a)`** (Peterfalvi (2.4)(c)). -/
theorem isTISet_smul (hD : DadeDatum L A H) (ha : a ∈ A) :
    IsTISet (a • (H a : Set G)) (centralizer {a}) where
  subset x hx := by
    obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.1 hx
    exact mul_mem (mem_inf.1 (hD.mem_inf_centralizer ha)).2 (hD.le_centralizer a ha hu)
  conj_mem g hg x hx := hD.conj_mem_smul ha hg hx
  disjoint_conj g hg x hx hgx := hg (hD.mem_centralizer_of_conj_mem_smul ha hx hgx)

/-- **The Dade support avoids the identity**: `a * u = 1` with `u ∈ H a` would put `a` in
`H a ⊓ C_L(a) = 1`. -/
theorem one_notMem_dadeSupport (hD : DadeDatum L A H) : (1 : G) ∉ dadeSupport A H := by
  rw [mem_dadeSupport_iff]
  rintro ⟨a, ha, u, hu, hau⟩
  have hau1 : a = u⁻¹ := eq_inv_of_mul_eq_one_left (isConj_one_left.1 hau)
  have hmem : a ∈ H a ⊓ (L ⊓ centralizer {a}) :=
    mem_inf.2 ⟨hau1 ▸ (H a).inv_mem hu, hD.mem_inf_centralizer ha⟩
  rw [hD.inf_eq_bot a ha, mem_bot] at hmem
  exact (hD.subset ha).2 hmem

/-- When the complement at `a` is trivial, the centralizer of `a` lies in `L`. -/
theorem centralizer_le (hD : DadeDatum L A H) (ha : a ∈ A) (hH : H a = ⊥) :
    centralizer {a} ≤ L := fun g hg => by
  rw [← SetLike.mem_coe, ← hD.mul_eq_centralizer a ha, hH, coe_bot, Set.singleton_one,
    one_mul] at hg
  exact (mem_inf.1 hg).1

/-- **Dade data with trivial complements make a trivial-intersection set** (Peterfalvi (2.3)). -/
theorem isTISet (hD : DadeDatum L A H) (hH : ∀ a ∈ A, H a = ⊥) : IsTISet A L where
  subset _ hx := (hD.subset hx).1
  conj_mem l hl x hx := hD.conj_mem x hx l hl
  disjoint_conj g hg x hx hgx := by
    obtain ⟨l, hl, hlx⟩ := hD.fusion x hx _ hgx (isConj_iff.2 ⟨g, rfl⟩)
    refine hg ?_
    have hfix : l⁻¹ * g * x * (l⁻¹ * g)⁻¹ = x :=
      calc _ = l⁻¹ * (g * x * g⁻¹) * l := by group
        _ = x := by rw [← hlx]; group
    have hc : l⁻¹ * g ∈ centralizer {x} :=
      mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hfix)
    simpa using L.mul_mem hl (hD.centralizer_le hx (hH x hx) hc)

/-- **A nonempty set carrying Dade data with trivial complements has normalizer `L`**
(Peterfalvi (2.3)). Nonemptiness is needed: every element normalizes `∅`. -/
theorem normalizer_eq (hD : DadeDatum L A H) (hH : ∀ a ∈ A, H a = ⊥) (hA : A.Nonempty) :
    normalizer A = L := by
  have hTI := hD.isTISet hH
  refine le_antisymm (fun g hg => ?_) fun l hl => mem_set_normalizer_iff.2 fun x => ?_
  · obtain ⟨a, ha⟩ := hA
    by_contra hgL
    exact hTI.disjoint_conj g hgL a ha ((mem_set_normalizer_iff.1 hg a).1 ha)
  · refine ⟨fun hx => hD.conj_mem x hx l hl, fun hx => ?_⟩
    simpa [mul_assoc] using hD.conj_mem _ hx l⁻¹ (L.inv_mem hl)

end DadeDatum

/-- **A trivial-intersection set avoiding `1` carries Dade data with trivial complements**
(Peterfalvi (2.3)): an element of `G` conjugating a point of the set back into it lies in `L`. -/
theorem IsTISet.dadeDatum {L : Subgroup G} {A : Set G} (hS : IsTISet A L) (h1 : (1 : G) ∉ A) :
    DadeDatum L A fun _ => ⊥ where
  subset x hx := ⟨hS.subset hx, fun hx1 => h1 (hx1 ▸ hx)⟩
  conj_mem a ha l hl := hS.conj_mem l hl a ha
  fusion a ha b hb hab := by
    obtain ⟨g, rfl⟩ := isConj_iff.1 hab
    exact ⟨g, not_not.1 fun hg => hS.disjoint_conj g hg a ha hb, rfl⟩
  le_centralizer _ _ := bot_le
  normal _ _ := by rw [bot_subgroupOf]; infer_instance
  inf_eq_bot _ _ := bot_inf_eq _
  mul_eq_centralizer a ha := by
    rw [coe_bot, Set.singleton_one, one_mul, coe_inf, Set.inter_eq_right]
    intro g hg
    refine not_not.1 fun hgL => hS.disjoint_conj g hgL a ha ?_
    rw [(mem_centralizer_singleton_iff.1 hg).eq, mul_inv_cancel_right]
    exact ha
  coprime _ _ _ _ := by simp

/-! ### Class functions supported on a subset -/

section Supported

variable (k : Type*) [Semiring k] (L : Subgroup G) (A : Set G)

/-- `CF(L, A)`: the class functions of the subgroup `L` vanishing outside `A`. -/
def supportedClassFunctions : Submodule k (ClassFunction k L) where
  carrier := {f | ∀ x : L, (x : G) ∉ A → f.val x = 0}
  zero_mem' _ _ := rfl
  add_mem' {f g} hf hg x hx := by
    simp [hf x hx, hg x hx]
  smul_mem' c f hf x hx := by
    simp [hf x hx]

variable {k L A}

/-- Membership in `CF(L, A)`. -/
@[simp]
theorem mem_supportedClassFunctions {f : ClassFunction k L} :
    f ∈ supportedClassFunctions k L A ↔ ∀ x : L, (x : G) ∉ A → f.val x = 0 :=
  Iff.rfl

/-- `CF(L, A)` is linearly equivalent to the functions on the conjugacy classes of `L` contained in
`A`: a class function vanishing outside `A` vanishes on every class not contained in `A`. -/
private noncomputable def supportedClassFunctionsEquiv :
    supportedClassFunctions k L A ≃ₗ[k]
      ({c : ConjClasses L // ∀ x ∈ c.carrier, (x : G) ∈ A} → k) := by
  classical
  exact
  { toFun f c := ClassFunction.toConjClasses f.val c.val
    map_add' f g := funext fun c => by
      obtain ⟨x, hx⟩ := ConjClasses.mk_surjective c.val
      simp [← hx]
    map_smul' r f := funext fun c => by
      obtain ⟨x, hx⟩ := ConjClasses.mk_surjective c.val
      simp [← hx]
    invFun g := ⟨ClassFunction.ofConjClasses fun c =>
        if h : ∀ x ∈ c.carrier, (x : G) ∈ A then g ⟨c, h⟩ else 0, fun x hx => by
      rw [ClassFunction.ofConjClasses_apply]
      split_ifs with h
      · exact absurd (h x ConjClasses.mem_carrier_mk) hx
      · rfl⟩
    left_inv f := by
      ext x
      simp only [ClassFunction.ofConjClasses_apply, ClassFunction.toConjClasses_mk]
      split_ifs with h
      · rfl
      · obtain ⟨y, hy, hyA⟩ := not_forall₂.1 h
        rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at hy
        rw [← ClassFunction.eq_of_isConj f.val hy, f.property y hyA]
    right_inv g := funext fun ⟨c, hc⟩ => by
      obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
      simp only [ClassFunction.toConjClasses_mk, ClassFunction.ofConjClasses_apply]
      split_ifs with h
      · rfl
      · exact absurd hc h }

/-- **The dimension of `CF(L, A)`** is the number of conjugacy classes of `L` contained in `A`,
when `L` has finitely many conjugacy classes. -/
theorem finrank_supportedClassFunctions [StrongRankCondition k] [Finite (ConjClasses L)] :
    Module.finrank k (supportedClassFunctions k L A) =
      Nat.card {c : ConjClasses L // ∀ x ∈ c.carrier, (x : G) ∈ A} := by
  let := Fintype.ofFinite {c : ConjClasses L // ∀ x ∈ c.carrier, (x : G) ∈ A}
  rw [LinearEquiv.finrank_eq supportedClassFunctionsEquiv, Module.finrank_pi,
    Nat.card_eq_fintype_card]

end Supported

end TauCeti
