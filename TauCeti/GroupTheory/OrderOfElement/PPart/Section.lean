/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Torsion
public import TauCeti.GroupTheory.OrderOfElement.PPart

/-!
# `p`-sections of a group

Fix a prime `p`. The **`p`-section** of an element `x` of `p`-power order is the set of elements
`g` whose `p`-part `TauCeti.pPart p g` is conjugate to `x`. The sections of a set of
representatives of the conjugacy classes of `p`-elements partition the group, and each section is
described by the centralizer of its representative: an element of finite order has `p`-part
exactly `x` when it is `s * x` for a `p`-regular element `s` of `C_G(x)`, and two such elements
are conjugate in `G` exactly when their `p`-free parts are conjugate in `C_G(x)`. So in a torsion
group the conjugacy classes of `G` inside the section of `x` correspond to the `p`-regular
conjugacy classes of `C_G(x)`, and the number of conjugacy classes of a finite group is the sum,
over the classes of `p`-elements, of the number of `p`-regular classes of their centralizers.

This is the indexing of modular character theory: generalized decomposition numbers and Brauer's
second main theorem are stated section by section, with the Brauer characters of `C_G(x)` on the
`p`-regular part. The induction library indexes sections by the `p`-regular part instead
(`TauCeti.pSectionIndicator`); the two indexings are different.

An element `s` is **`p`-regular** when `(orderOf s).Coprime p`.

## Main definitions

* `TauCeti.pSection p x`: the `p`-section of `x`.
* `TauCeti.pFreePartEquiv`: `g ↦ pFreePart p g`, from the elements with `p`-part `x` to the
  `p`-regular elements of `C_G(x)`.
* `TauCeti.centralizerConjClassesMul x`: the class of `s` in `C_G(x)` goes to the class of `s * x`
  in `G`.

## Main results

* `TauCeti.existsUnique_mem_pSection`: the sections of a set of representatives of the conjugacy
  classes of `p`-elements partition `G`.
* `TauCeti.pPart_eq_iff_exists_mul_eq`: the elements with `p`-part `x` are the products `s * x`
  with `s` a `p`-regular element of `C_G(x)`.
* `TauCeti.pFreePartEquiv_conj`: the parametrization is equivariant for conjugation by `C_G(x)`.
* `TauCeti.isConj_iff_exists_mem_centralizer`: two elements with `p`-part `x` are conjugate in
  `G` exactly when their `p`-free parts are conjugate by an element of `C_G(x)`.
* `TauCeti.bijOn_centralizerConjClassesMul`: the `p`-regular classes of `C_G(x)` correspond to the
  classes of `G` in the section of `x`.
* `TauCeti.natCard_conjClasses_eq_sum`: the number of conjugacy classes of a finite group is the
  sum, over representatives `x` of the classes of `p`-elements, of the number of `p`-regular
  classes of `C_G(x)`.
* `TauCeti.ncard_conjugatesOf_eq_index_mul`: the class of `g` has `|G : C_G(x)|` times as many
  elements as the class of its `p`-free part in `C_G(x)`, where `x` is the `p`-part of `g`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Cambridge University Press (2016),
  Lemma 9.3.4, for the factorisation of an element into commuting `p`- and `p'`-parts and the
  conjugacy of the factors of conjugate elements.
* J. M. Martínez, *Modular representation theory of finite groups*, course notes, Firenze (2024),
  Lecture 1.
-/

public section

namespace TauCeti

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

/-! ### Sections -/

/-- The **`p`-section** of `x`: the elements of `G` whose `p`-part is conjugate to `x`. It is
used for `x` of `p`-power order, the shape of every `p`-part (`TauCeti.orderOf_pPart`). -/
def pSection (p : ℕ) (x : G) : Set G := {g | IsConj (pPart p g) x}

@[simp]
theorem mem_pSection {x g : G} : g ∈ pSection p x ↔ IsConj (pPart p g) x := Iff.rfl

/-- Every element lies in the section of its own `p`-part. -/
theorem mem_pSection_pPart (p : ℕ) (g : G) : g ∈ pSection p (pPart p g) := IsConj.refl _

/-- An element of `p`-power order lies in its own section. -/
theorem mem_pSection_self (hp : p.Prime) {x : G} {k : ℕ} (hx : orderOf x = p ^ k) :
    x ∈ pSection p x := by
  rw [mem_pSection, pPart_eq_self hp hx]

/-- Sections are unions of conjugacy classes. -/
theorem mem_pSection_of_isConj {x g h : G} (hg : g ∈ pSection p x) (hgh : IsConj g h) :
    h ∈ pSection p x := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hgh
  rw [mem_pSection, pPart_conj]
  exact (isConj_iff.2 ⟨c, rfl⟩).symm.trans hg

/-- Conjugate elements have the same section. -/
theorem pSection_eq_of_isConj {x y : G} (h : IsConj x y) : pSection p x = pSection p y :=
  Set.ext fun _ => ⟨fun hg => hg.trans h, fun hg => hg.trans h.symm⟩

/-- The sections of two elements of `p`-power order coincide exactly when the elements are
conjugate. -/
theorem pSection_eq_pSection_iff (hp : p.Prime) {x y : G} {k : ℕ} (hx : orderOf x = p ^ k) :
    pSection p x = pSection p y ↔ IsConj x y := by
  refine ⟨fun h => ?_, pSection_eq_of_isConj⟩
  have hmem := mem_pSection_self hp hx
  rwa [h, mem_pSection, pPart_eq_self hp hx] at hmem

/-- The sections of non-conjugate elements are disjoint. -/
theorem disjoint_pSection {x y : G} (h : ¬ IsConj x y) : Disjoint (pSection p x) (pSection p y) :=
  Set.disjoint_left.2 fun _ hx hy => h (hx.symm.trans hy)

/-- **The sections partition the group.** For a family `r` of pairwise non-conjugate elements
meeting every conjugacy class of elements of `p`-power order, every element lies in the section
of exactly one `r i`. -/
theorem existsUnique_mem_pSection {ι : Type*} (r : ι → G) (hr : ∀ i j, IsConj (r i) (r j) → i = j)
    (hcov : ∀ x : G, ∀ k : ℕ, orderOf x = p ^ k → ∃ i, IsConj x (r i)) (g : G) :
    ∃! i, g ∈ pSection p (r i) := by
  obtain ⟨i, hi⟩ := hcov (pPart p g) _ (orderOf_pPart p g)
  exact ⟨i, hi, fun j hj => hr j i (hj.symm.trans hi)⟩

/-! ### The elements with a given `p`-part -/

/-- The `p`-free part of `g` lies in the centralizer of its `p`-part. -/
theorem pFreePart_mem_centralizer_pPart (p : ℕ) (g : G) :
    pFreePart p g ∈ centralizer {pPart p g} :=
  mem_centralizer_singleton_iff.2 (commute_pFreePart_pPart p g)

/-- Conjugation by an element of `C_G(x)` preserves the elements with `p`-part `x`. -/
theorem pPart_conj_of_mem_centralizer {x c g : G} (hc : c ∈ centralizer {x})
    (hg : pPart p g = x) : pPart p (c * g * c⁻¹) = x := by
  rw [pPart_conj, hg, (mem_centralizer_singleton_iff.1 hc).eq, mul_inv_cancel_right]

/-- For `x` of `p`-power order and `s` a `p`-regular element of `C_G(x)`, the `p`-part of `s * x`
is `x`. -/
theorem pPart_mul_of_mem_centralizer (hp : p.Prime) {x s : G} {k : ℕ} (hx : orderOf x = p ^ k)
    (hs : s ∈ centralizer {x}) (hsp : (orderOf s).Coprime p) : pPart p (s * x) = x :=
  (eq_pPart hp (mem_centralizer_singleton_iff.1 hs) rfl
    ((Nat.Prime.coprime_iff_not_dvd hp).1 hsp.symm) hx).symm

/-- For `x` of `p`-power order and `s` a `p`-regular element of `C_G(x)`, the `p`-free part of
`s * x` is `s`. -/
theorem pFreePart_mul_of_mem_centralizer (hp : p.Prime) {x s : G} {k : ℕ}
    (hx : orderOf x = p ^ k) (hs : s ∈ centralizer {x}) (hsp : (orderOf s).Coprime p) :
    pFreePart p (s * x) = s :=
  (eq_pFreePart hp (mem_centralizer_singleton_iff.1 hs) rfl
    ((Nat.Prime.coprime_iff_not_dvd hp).1 hsp.symm) hx).symm

/-- **The elements with `p`-part `x`.** For `x` of `p`-power order, an element `g` of finite order
has `p`-part `x` exactly when `g = s * x` for a `p`-regular element `s` of `C_G(x)`. -/
theorem pPart_eq_iff_exists_mul_eq (hp : p.Prime) {x g : G} {k : ℕ} (hx : orderOf x = p ^ k)
    (hg : IsOfFinOrder g) :
    pPart p g = x ↔ ∃ s ∈ centralizer {x}, (orderOf s).Coprime p ∧ s * x = g := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨pFreePart p g, pFreePart_mem_centralizer_pPart p g, coprime_orderOf_pFreePart hp hg,
      pFreePart_mul_pPart p g⟩
  · rintro ⟨s, hs, hsp, rfl⟩
    exact pPart_mul_of_mem_centralizer hp hx hs hsp

/-- **The parametrization of the elements with `p`-part `x`.** For `x` of `p`-power order in a
torsion group, `g ↦ pFreePart p g` is a bijection from the elements with `p`-part `x` to the
`p`-regular elements of `C_G(x)`, with inverse `s ↦ s * x`. -/
noncomputable def pFreePartEquiv (hp : p.Prime) {x : G} {k : ℕ} (hx : orderOf x = p ^ k)
    (hG : IsMulTorsion G) :
    {g : G // pPart p g = x} ≃ {s : centralizer {x} // (orderOf s).Coprime p} where
  toFun g := ⟨⟨pFreePart p g.val, by
    simpa only [g.property] using pFreePart_mem_centralizer_pPart p g.val⟩, by
    rw [Subgroup.orderOf_mk]
    exact coprime_orderOf_pFreePart hp (hG g.val)⟩
  invFun s := ⟨s.val * x, pPart_mul_of_mem_centralizer hp hx s.val.property
    (by rw [orderOf_coe]; exact s.property)⟩
  left_inv g := by
    obtain ⟨g, rfl⟩ := g
    exact Subtype.ext (pFreePart_mul_pPart p g)
  right_inv s := Subtype.ext <| Subtype.ext <|
    pFreePart_mul_of_mem_centralizer hp hx s.val.property (by rw [orderOf_coe]; exact s.property)

section pFreePartEquiv

variable (hp : p.Prime) {x : G} {k : ℕ} (hx : orderOf x = p ^ k) (hG : IsMulTorsion G)

@[simp]
theorem coe_pFreePartEquiv_apply (g : {g : G // pPart p g = x}) :
    ((pFreePartEquiv hp hx hG g).val : G) = pFreePart p g.val := (rfl)

@[simp]
theorem coe_pFreePartEquiv_symm_apply (s : {s : centralizer {x} // (orderOf s).Coprime p}) :
    ((pFreePartEquiv hp hx hG).symm s).val = s.val * x := (rfl)

/-- **The parametrization is `C_G(x)`-equivariant.** Conjugating an element with `p`-part `x` by
an element of `C_G(x)` conjugates its `p`-free part. -/
theorem pFreePartEquiv_conj (c : centralizer {x}) (g : {g : G // pPart p g = x}) :
    (pFreePartEquiv hp hx hG ⟨c * g.val * c⁻¹,
      pPart_conj_of_mem_centralizer c.property g.property⟩).val =
      c * (pFreePartEquiv hp hx hG g).val * c⁻¹ := by
  ext
  simp [pFreePart_conj]

end pFreePartEquiv

/-- **Conjugacy within a section.** Two elements with `p`-part `x` are conjugate in `G` exactly
when an element of `C_G(x)` conjugates the `p`-free part of one to that of the other: a
conjugator carrying one to the other carries `x` to `x`. -/
theorem isConj_iff_exists_mem_centralizer {x g h : G} (hg : pPart p g = x) (hh : pPart p h = x) :
    IsConj g h ↔ ∃ c ∈ centralizer {x}, c * pFreePart p g * c⁻¹ = pFreePart p h := by
  refine ⟨fun hgh => ?_, fun ⟨c, hc, hcg⟩ => isConj_iff.2 ⟨c, ?_⟩⟩
  · obtain ⟨c, rfl⟩ := isConj_iff.1 hgh
    rw [pPart_conj, hg] at hh
    refine ⟨c, mem_centralizer_singleton_iff.2 ?_, (pFreePart_conj p c g).symm⟩
    exact (commute_iff_eq _ _).2 (mul_inv_eq_iff_eq_mul.1 hh)
  · have hcx : c * x * c⁻¹ = x := by
      rw [(mem_centralizer_singleton_iff.1 hc).eq, mul_inv_cancel_right]
    calc c * g * c⁻¹ = c * pFreePart p g * c⁻¹ * (c * pPart p g * c⁻¹) := by
          conv_lhs => rw [← pFreePart_mul_pPart p g]
          group
      _ = h := by rw [hcg, hg, hcx, ← hh, pFreePart_mul_pPart]

/-! ### Conjugacy classes in a section -/

/-- The map sending the conjugacy class of `s` in `C_G(x)` to the conjugacy class of `s * x` in
`G`. For `x` of `p`-power order in a torsion group it maps the `p`-regular classes of `C_G(x)`
bijectively onto the classes of `G` in the `p`-section of `x`
(`TauCeti.bijOn_centralizerConjClassesMul`). -/
def centralizerConjClassesMul (x : G) : ConjClasses (centralizer {x}) → ConjClasses G :=
  Quotient.lift (fun s => ConjClasses.mk ((s : G) * x)) fun s t hst => by
    obtain ⟨c, rfl⟩ := isConj_iff.1 hst
    refine ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨c, ?_⟩)
    have hcx : x * (c : G)⁻¹ = (c : G)⁻¹ * x :=
      (mem_centralizer_singleton_iff.1 c.property).inv_left.eq.symm
    simp only [coe_mul, coe_inv, mul_assoc, hcx]

@[simp]
theorem centralizerConjClassesMul_mk (x : G) (s : centralizer {x}) :
    centralizerConjClassesMul x (ConjClasses.mk s) = ConjClasses.mk ((s : G) * x) := (rfl)

/-- **The class bijection of a section.** For `x` of `p`-power order in a torsion group,
`s ↦ s * x` induces a bijection from the conjugacy classes of `p`-regular elements of `C_G(x)`
to the conjugacy classes of `G` contained in the `p`-section of `x`. -/
theorem bijOn_centralizerConjClassesMul (hp : p.Prime) {x : G} {k : ℕ} (hx : orderOf x = p ^ k)
    (hG : IsMulTorsion G) :
    Set.BijOn (centralizerConjClassesMul x)
      {C | ∃ s : centralizer {x}, ConjClasses.mk s = C ∧ (orderOf s).Coprime p}
      {C | ∃ g : G, ConjClasses.mk g = C ∧ g ∈ pSection p x} := by
  have hreg (s : centralizer {x}) (hs : (orderOf s).Coprime p) : (orderOf (s : G)).Coprime p := by
    rwa [orderOf_coe]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl, hs⟩
    refine ⟨s * x, rfl, ?_⟩
    rw [mem_pSection, pPart_mul_of_mem_centralizer hp hx s.property (hreg s hs)]
  · rintro _ ⟨s, rfl, hs⟩ _ ⟨t, rfl, ht⟩ hst
    rw [centralizerConjClassesMul_mk, centralizerConjClassesMul_mk,
      ConjClasses.mk_eq_mk_iff_isConj] at hst
    obtain ⟨c, hc, hcst⟩ := (isConj_iff_exists_mem_centralizer
      (pPart_mul_of_mem_centralizer hp hx s.property (hreg s hs))
      (pPart_mul_of_mem_centralizer hp hx t.property (hreg t ht))).1 hst
    rw [pFreePart_mul_of_mem_centralizer hp hx s.property (hreg s hs),
      pFreePart_mul_of_mem_centralizer hp hx t.property (hreg t ht)] at hcst
    exact ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hcst⟩)
  · rintro _ ⟨g, rfl, hg⟩
    obtain ⟨c, hc⟩ := isConj_iff.1 hg
    rw [← pPart_conj] at hc
    set s := pFreePartEquiv hp hx hG ⟨c * g * c⁻¹, hc⟩
    refine ⟨ConjClasses.mk s.val, ⟨s.val, rfl, s.property⟩, ?_⟩
    rw [centralizerConjClassesMul_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_comm]
    have hs : ((s : centralizer {x}) : G) * x = c * g * c⁻¹ := by
      rw [← coe_pFreePartEquiv_symm_apply hp hx hG, Equiv.symm_apply_apply]
    exact hs ▸ isConj_iff.2 ⟨c, rfl⟩

/-- For `x` of `p`-power order in a torsion group, the number of conjugacy classes of `G` in the
`p`-section of `x` is the number of conjugacy classes of `p`-regular elements of `C_G(x)`. -/
theorem natCard_conjClasses_pSection (hp : p.Prime) {x : G} {k : ℕ} (hx : orderOf x = p ^ k)
    (hG : IsMulTorsion G) :
    Nat.card {C : ConjClasses G // ∃ g : G, ConjClasses.mk g = C ∧ g ∈ pSection p x} =
      Nat.card {C : ConjClasses (centralizer {x}) //
        ∃ s : centralizer {x}, ConjClasses.mk s = C ∧ (orderOf s).Coprime p} :=
  (Nat.card_congr ((bijOn_centralizerConjClassesMul hp hx hG).equiv _)).symm

/-- **The class count by sections.** Let `r` be a set of representatives of the conjugacy classes
of `p`-elements of a finite group `G`. The number of conjugacy classes of `G` is the sum over `i`
of the number of conjugacy classes of `p`-regular elements of `C_G(r i)`. -/
theorem natCard_conjClasses_eq_sum (hp : p.Prime) [Finite G] {ι : Type*} [Fintype ι] (r : ι → G)
    (hrp : ∀ i, ∃ k : ℕ, orderOf (r i) = p ^ k) (hr : ∀ i j, IsConj (r i) (r j) → i = j)
    (hcov : ∀ x : G, ∀ k : ℕ, orderOf x = p ^ k → ∃ i, IsConj x (r i)) :
    Nat.card (ConjClasses G) = ∑ i, Nat.card {C : ConjClasses (centralizer {r i}) //
      ∃ s : centralizer {r i}, ConjClasses.mk s = C ∧ (orderOf s).Coprime p} := by
  -- Sort each class into the unique section containing its elements.
  let f : ConjClasses G → ι := fun C =>
    (existsUnique_mem_pSection r hr hcov C.exists_rep.choose).choose
  have hf (C : ConjClasses G) (i : ι) :
      f C = i ↔ ∃ g : G, ConjClasses.mk g = C ∧ g ∈ pSection p (r i) := by
    have hrep := (existsUnique_mem_pSection r hr hcov C.exists_rep.choose).choose_spec
    refine ⟨fun h => ⟨_, C.exists_rep.choose_spec, h ▸ hrep.1⟩, fun ⟨g, hgC, hg⟩ => ?_⟩
    refine (hrep.2 i (mem_pSection_of_isConj hg ?_)).symm
    rw [← ConjClasses.mk_eq_mk_iff_isConj, hgC, C.exists_rep.choose_spec]
  have : Finite (ConjClasses G) := Finite.of_surjective _ ConjClasses.mk_surjective
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨k, hk⟩ := hrp i
  rw [← natCard_conjClasses_pSection hp hk isMulTorsion_of_finite]
  exact Nat.card_congr (Equiv.subtypeEquivRight (hf · i))

/-- **Class sizes in a section.** With `x` the `p`-part of `g`, the conjugacy class of `g` in `G`
has `|G : C_G(x)|` times as many elements as the conjugacy class of the `p`-free part of `g` in
`C_G(x)`. -/
theorem ncard_conjugatesOf_eq_index_mul (p : ℕ) (g : G) :
    (conjugatesOf g).ncard = (centralizer {pPart p g}).index *
      (conjugatesOf (⟨pFreePart p g, pFreePart_mem_centralizer_pPart p g⟩ :
        centralizer {pPart p g})).ncard := by
  have hle : centralizer {g} ≤ centralizer {pPart p g} := fun c hc =>
    mem_centralizer_singleton_iff.2 (commute_pPart p (mem_centralizer_singleton_iff.1 hc))
  have hcen : (centralizer {g}).subgroupOf (centralizer {pPart p g}) =
      centralizer {(⟨pFreePart p g, pFreePart_mem_centralizer_pPart p g⟩ :
        centralizer {pPart p g})} := by
    ext c
    rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      ← Submonoid.commute_coe_coe]
    refine ⟨commute_pFreePart p, fun h => ?_⟩
    simpa using h.mul_right (mem_centralizer_singleton_iff.1 c.property)
  rw [← index_centralizer_eq_ncard, ← index_centralizer_eq_ncard, ← hcen, ← relIndex,
    ← relIndex_mul_index hle, mul_comm]

end TauCeti
