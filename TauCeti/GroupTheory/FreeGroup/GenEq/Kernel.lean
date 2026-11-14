/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Section
public import TauCeti.GroupTheory.FreeGroup.GenEq.Surgery
import Mathlib.Data.Fin.VecNotation
import TauCeti.GroupTheory.GroupAlgGeom.RelatorElimination

/-!
# Elimination of a base of a generalised equation

Let `Ω` be a generalised equation without boundary connections. A variable base `μ` is
*eliminable* (Kharlampovich–Myasnikov, §5.2, D4) when `Δ(μ) ≠ μ` and

* (a) `μ` contains an item `hₖ` of degree one, that is an item belonging to no other base; or
* (b) an end-point `i` of `μ`, different from the first and the last boundary, touches no other
  base, variable or constant.

Eliminating `μ` removes the pair `μ, Δ(μ)` (`TauCeti.GenEq.removePair`); the items and the
boundaries are kept. On the groups presented by the systems `Ω*`, the basic equation of an
eliminable base is, after a change of variables, a member of a free basis of `F(A)[h]` over `F(A)`
in which the other equations do not involve it: in case (a) it can be solved for `hₖ`, and in case
(b), after replacing the two items `h_{i-1}, hᵢ` next to `i` by the item of `μ` among them and the
product `h_{i-1} hᵢ`, it can be solved for the item of `μ`. Hence, writing `Ω₁ = Ω.removePair μ`,
`F[h]/ncl(Ω₁*) ≅ (F[h]/ncl(Ω*)) ∗ ⟨z⟩`: the group presented by `Ω₁*` is the free product of the
group presented by `Ω*` with an infinite cyclic group.

Let `W` be the subgroup of `F(A)[h]` of the words in which `hₖ` does not occur in case (a), and of
the words in the items other than `h_{i-1}, hᵢ` and in the product `h_{i-1} hᵢ` in case (b). The
isomorphism sends the class of a word of `W` to its class in the first factor, the basic equation
of `μ` to `z`, and each item not in `W` (`hₖ`, respectively `h_{i-1}` and `hᵢ`) to `u z^{±1} v` for
the classes `u, v` of two words of `W`
(`TauCeti.GenEq.exists_mulEquiv_removePair_of_degree_eq_one`,
`TauCeti.GenEq.exists_mulEquiv_removePair_of_touches`). Sending `z` to `1` after it gives the
homomorphism induced by the identity on the items, so in the group presented by `Ω*` each item not
in `W` is the class of a word of `W`. In case (a) boundary connections through bases other than
`μ, Δ(μ)` are allowed.

The source states this step through the generalised equation `Ω′` obtained from `Ω₁` by deleting
the item `hₖ` in case (a), and by deleting the boundary `i`, which merges `h_{i-1}` and `hᵢ` into
one item, in case (b); the items of `Ω′` correspond to the generators of `W` over `F(A)`. On
presented groups its two isomorphisms read `F[h]/ncl(Ω*) ≅ F[h′]/ncl(Ω′*)` and
`F[h]/ncl(Ω₁*) ≅ (F[h′]/ncl(Ω′*)) ∗ ⟨z⟩`, and both follow from the isomorphism above and its
values. The source writes them for the coordinate groups `F_{R(·)}`. The first passes to coordinate
groups, an `F(A)`-isomorphism of presented groups inducing one of their coordinate groups; the
second does not in general: if the solution set of `Ω′*` is reducible, the `F(A)`-homomorphisms to
`F(A)` do not separate the elements of `F_{R(Ω′)} ∗ ⟨z⟩`, while they separate those of the
coordinate group of `Ω₁*`.

In case (a) the item `hₖ` is free in `Ω₁`
(`TauCeti.GenEq.isFreeItem_removePair_of_degree_eq_one`), so `Ω′` is also obtained from `Ω₁` by
deleting free items. In case (b) it need not be: `h_{i-1}` and `hᵢ` still belong to the bases of
`Ω₁` crossing the boundary `i`, if there are any. The kernel `Ker Ω` of the source is the
generalised equation left when eliminable bases are eliminated one after the other until none is
left; its Lemma 16 decomposes `F_{R(Ω)}` as `F_{R(Ker Ω)} ∗ F(Z)`, the free items of the kernel
being deleted. It is to be read on presented groups, with the boundary `i` deleted at each
elimination by rule (b): on coordinate groups a free product with `F(Z)`, `Z` nonempty, fails in
general for the same reason. The surgery producing `Ω′` is not part of this file.

For a parametric generalised equation the source eliminates active bases only; that restriction
is not part of `TauCeti.GenEq.IsEliminable` and is to be imposed where it is used.

We require `Δ(μ) ≠ μ` of an eliminable base: the basic equation of a base which is its own dual
is trivial, and removing it frees no generator.

## Main definitions

* `TauCeti.GenEq.IsEliminable`: a variable base is eliminable.

## Main results

* `TauCeti.GenEq.exists_mulEquiv_removePair_of_degree_eq_one`,
  `TauCeti.GenEq.exists_mulEquiv_removePair_of_touches`: the isomorphism
  `F[h]/ncl(Ω₁*) ≅ (F[h]/ncl(Ω*)) ∗ ⟨z⟩` for an elimination by rule (a) and by rule (b), with its
  values on the words of `W`, on the basic equation of the eliminated base and on the items not in
  `W`.
* `TauCeti.GenEq.exists_bijective_systemGroup_removePair`: removing an eliminable base from a
  generalised equation without boundary connections adds a free factor `⟨z⟩` to the presented
  group, by an `F(A)`-isomorphism sending the basic equation of the base to `z`.
* `TauCeti.GenEq.isFreeItem_removePair_of_degree_eq_one`: an item of degree one of a base is free
  once the base is removed.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.2, D4 and Lemma 16.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom Monoid.Coprod
open scoped Finset

variable {A : Type*} (Ω : GenEq A)

/-- A variable base `μ` is eliminable (D4): it is not its own dual, and either (a) it contains
an item of degree one, or (b) one of its end-points, different from the first and the last
boundary, is an end-point of no other variable base and of no constant base. -/
def IsEliminable (μ : Fin Ω.numBases) : Prop :=
  Ω.dual μ ≠ μ ∧ ((∃ k ∈ Ω.baseItems μ, Ω.degree k = 1) ∨
    ∃ i : Fin (Ω.numItems + 1), Ω.Touches i μ ∧ i ≠ 0 ∧ i ≠ Fin.last Ω.numItems ∧
      (∀ ν, ν ≠ μ → ¬ Ω.Touches i ν) ∧
      ∀ b ∈ Ω.constBases, (b.1 : ℕ) ≠ i ∧ (b.1 : ℕ) + 1 ≠ i)

/-- The definition of an eliminable base. -/
theorem isEliminable_iff {μ : Fin Ω.numBases} : Ω.IsEliminable μ ↔
    Ω.dual μ ≠ μ ∧ ((∃ k ∈ Ω.baseItems μ, Ω.degree k = 1) ∨
      ∃ i : Fin (Ω.numItems + 1), Ω.Touches i μ ∧ i ≠ 0 ∧ i ≠ Fin.last Ω.numItems ∧
        (∀ ν, ν ≠ μ → ¬ Ω.Touches i ν) ∧
        ∀ b ∈ Ω.constBases, (b.1 : ℕ) ≠ i ∧ (b.1 : ℕ) + 1 ≠ i) :=
  Iff.rfl

-- Stated through the end-points of the bases, so that the instance reduces in `decide`.
instance (μ : Fin Ω.numBases) : Decidable (Ω.IsEliminable μ) :=
  decidable_of_iff (Ω.dual μ ≠ μ ∧
    ((∃ k : Fin Ω.numItems, ((Ω.left μ : ℕ) ≤ k ∧ (k : ℕ) < Ω.right μ) ∧
        #{ν | (Ω.left ν : ℕ) ≤ k ∧ (k : ℕ) < Ω.right ν} + #{b ∈ Ω.constBases | b.1 = k} = 1) ∨
      ∃ i : Fin (Ω.numItems + 1), (i = Ω.left μ ∨ i = Ω.right μ) ∧ i ≠ 0 ∧
        i ≠ Fin.last Ω.numItems ∧ (∀ ν, ν ≠ μ → ¬ (i = Ω.left ν ∨ i = Ω.right ν)) ∧
        ∀ b ∈ Ω.constBases, (b.1 : ℕ) ≠ i ∧ (b.1 : ℕ) + 1 ≠ i))
    (by simp only [isEliminable_iff, degree_def, mem_baseItems, touches_iff])

variable {Ω} in
/-- An eliminable base is not its own dual. -/
theorem IsEliminable.dual_ne {μ : Fin Ω.numBases} (h : Ω.IsEliminable μ) : Ω.dual μ ≠ μ :=
  h.1

variable {Ω} in
/-- Rule (a): a base which is not its own dual and contains an item of degree one is
eliminable. -/
theorem isEliminable_of_degree_eq_one {μ : Fin Ω.numBases} (hd : Ω.dual μ ≠ μ)
    {k : Fin Ω.numItems} (hk : k ∈ Ω.baseItems μ) (hdeg : Ω.degree k = 1) : Ω.IsEliminable μ :=
  ⟨hd, .inl ⟨k, hk, hdeg⟩⟩

variable {Ω} in
/-- Rule (b): a base which is not its own dual is eliminable if one of its end-points, different
from the first and the last boundary, is an end-point of no other variable base and of no constant
base. -/
theorem isEliminable_of_touches {μ : Fin Ω.numBases} (hd : Ω.dual μ ≠ μ)
    {i : Fin (Ω.numItems + 1)} (hi : Ω.Touches i μ) (h0 : i ≠ 0) (hlast : i ≠ Fin.last Ω.numItems)
    (hν : ∀ ν, ν ≠ μ → ¬ Ω.Touches i ν)
    (hb : ∀ b ∈ Ω.constBases, (b.1 : ℕ) ≠ i ∧ (b.1 : ℕ) + 1 ≠ i) : Ω.IsEliminable μ :=
  ⟨hd, .inr ⟨i, hi, h0, hlast, hν, hb⟩⟩

variable {Ω} in
/-- An item of degree one of a variable base is free once the base and its dual are removed. -/
theorem isFreeItem_removePair_of_degree_eq_one {μ : Fin Ω.numBases} {k : Fin Ω.numItems}
    (hk : k ∈ Ω.baseItems μ) (hdeg : Ω.degree k = 1) : (Ω.removePair μ).IsFreeItem k := by
  refine (isFreeItem_iff _).2 ⟨fun ν hkν => ?_, fun hc => ?_⟩
  · have hν := Finset.mem_compl.1 (Finset.orderEmbOfFin_mem ({μ, Ω.dual μ} : Finset _)ᶜ rfl ν)
    exact notMem_baseItems_of_degree_eq_one hk hdeg
      (fun h => hν (by rw [h]; exact Finset.mem_insert_self _ _))
      (Ω.mem_baseItems.2 ((Ω.removePair μ).mem_baseItems.1 hkν))
  · obtain ⟨b, hb, h⟩ := (isConstantItem_iff _).1 hc
    exact not_isConstantItem_of_degree_eq_one hk hdeg ((isConstantItem_iff _).2 ⟨b, hb, h⟩)

/-! ### Separating an item of an eliminable base -/

/-- Let `χ` send the words avoiding `h_p` and `h_{p+1}` and the word `h_p h_{p+1}` to words
avoiding `hₖ`. Then it sends the word of every base which does not have `p + 1` as an end-point
to a word avoiding `hₖ`: such a base contains both `h_p` and `h_{p+1}`, adjacent, or neither. -/
private theorem mem_avoiding_of_not_touches {χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems))}
    {k : Fin Ω.numItems} {p : ℕ} (hp : p + 1 < Ω.numItems)
    (hfix : ∀ c, c ∈ GX.avoiding (⟨p, by omega⟩ : Fin Ω.numItems) →
      c ∈ GX.avoiding (⟨p + 1, hp⟩ : Fin Ω.numItems) → χ c ∈ GX.avoiding k)
    (hpair : χ (inr (FreeGroup.of ⟨p, by omega⟩) * inr (FreeGroup.of ⟨p + 1, hp⟩)) ∈ GX.avoiding k)
    {ν : Fin Ω.numBases} (hl : (Ω.left ν : ℕ) ≠ p + 1) (hr : (Ω.right ν : ℕ) ≠ p + 1) :
    χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment (Ω.left ν) (Ω.right ν) true))) ∈
      GX.avoiding k := by
  have hlr : (Ω.left ν : ℕ) < Ω.right ν := Ω.left_lt_right ν
  have hrn : (Ω.right ν : ℕ) ≤ Ω.numItems := Nat.lt_succ_iff.1 (Ω.right ν).isLt
  by_cases hout : (Ω.right ν : ℕ) ≤ p ∨ p + 1 < Ω.left ν
  · exact hfix _ (Ω.toGX_segment_mem_avoiding _ (by simp only; omega))
      (Ω.toGX_segment_mem_avoiding _ (by simp only; omega))
  · rw [Ω.toGX_segment_eq_mul_pair (p := p) (by omega) (by omega) hrn, map_mul, map_mul]
    refine mul_mem (mul_mem (hfix _ ?_ ?_) hpair) (hfix _ ?_ ?_) <;>
      exact Ω.toGX_segment_mem_avoiding _ (by simp only; omega)

/-- After the coefficient-fixing automorphism `χ` of `F(A)[h]`, the item `hₖ` of `μ` and the word
`h[α(μ), β(μ)]` are unchanged, while `hₖ` occurs neither in the image of the word of another base,
nor in the image of a constant item, nor in the images of the two sides of the boundary equation of
a connection through a base other than `μ, Δ(μ)`. -/
private structure Separates (μ : Fin Ω.numBases) (χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems)))
    (k : Fin Ω.numItems) : Prop where
  map_inl (g : FreeGroup A) : χ (inl g) = inl g
  mem_baseItems : k ∈ Ω.baseItems μ
  map_inr : χ (inr (FreeGroup.of k)) = inr (FreeGroup.of k)
  map_segment :
    χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment (Ω.left μ) (Ω.right μ) true))) =
      EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment (Ω.left μ) (Ω.right μ) true))
  mem_avoiding_segment (ν : Fin Ω.numBases) : ν ≠ μ →
    χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment (Ω.left ν) (Ω.right ν) true))) ∈
      GX.avoiding k
  mem_avoiding_const (b : Fin Ω.numItems × (A × Bool)) : b ∈ Ω.constBases →
    χ (inr (FreeGroup.of b.1)) ∈ GX.avoiding k
  mem_avoiding_connection (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) :
    c ∈ Ω.connections → c.2.1 ≠ μ → c.2.1 ≠ Ω.dual μ →
      χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.boundaryEquation c).1)) ∈
          GX.avoiding k ∧
        χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.boundaryEquation c).2)) ∈
          GX.avoiding k

variable {Ω}

/-- Case (a): an item of degree one of `μ` occurs in no other base. -/
private theorem separates_of_degree_eq_one {μ : Fin Ω.numBases} {k : Fin Ω.numItems}
    (hk : k ∈ Ω.baseItems μ) (hdeg : Ω.degree k = 1) : Ω.Separates μ 1 k where
  map_inl _ := rfl
  mem_baseItems := hk
  map_inr := rfl
  map_segment := rfl
  mem_avoiding_segment ν hν := by
    have hkν := notMem_baseItems_of_degree_eq_one hk hdeg hν
    rw [mem_baseItems] at hkν
    exact Ω.toGX_segment_mem_avoiding _ (by omega)
  mem_avoiding_const b hb :=
    GX.inr_of_mem_avoiding fun h => not_isConstantItem_of_degree_eq_one hk hdeg
      ((isConstantItem_iff _).2 ⟨b, hb, h⟩)
  mem_avoiding_connection c hc hν hν' := by
    -- both sides are words in items of the base of the connection and of its dual
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Ω.bounds_of_mem_connections c hc
    rw [Fin.lt_def] at h₁ h₂ h₃ h₄
    have hkν := notMem_baseItems_of_degree_eq_one hk hdeg hν
    have hkν' := notMem_baseItems_of_degree_eq_one hk hdeg (ν := Ω.dual c.2.1)
      fun h => hν' ((Ω.dual_involutive c.2.1).symm.trans (congrArg Ω.dual h))
    rw [mem_baseItems] at hkν hkν'
    rw [boundaryEquation_fst]
    refine ⟨Ω.toGX_segment_mem_avoiding _ (by omega), ?_⟩
    by_cases hs : Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1)
    · rw [Ω.boundaryEquation_snd_of_sign_eq hs]
      exact Ω.toGX_segment_mem_avoiding _ (by omega)
    · rw [Ω.boundaryEquation_snd_of_sign_ne hs]
      exact Ω.toGX_segment_mem_avoiding _ (by omega)

/-- A shear `χ` fixing the words avoiding `h_{k'}` and sending `h_p h_{p+1}` to `h_{k'}`, where
`hₖ, h_{k'}` are the items `h_p, h_{p+1}` in some order, sends the words avoiding both items, and
the word `h_p h_{p+1}`, to words avoiding `hₖ`. -/
private theorem mem_avoiding_of_shear {p : ℕ} (hp : p + 1 < Ω.numItems) {k k' : Fin Ω.numItems}
    (hkk' : (k : ℕ) = p ∧ (k' : ℕ) = p + 1 ∨ (k : ℕ) = p + 1 ∧ (k' : ℕ) = p)
    {χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems))} (hχ : ∀ c ∈ GX.avoiding k', χ c = c)
    (hpair : χ (inr (FreeGroup.of ⟨p, by omega⟩) * inr (FreeGroup.of ⟨p + 1, hp⟩)) =
      inr (FreeGroup.of k')) :
    (∀ c, c ∈ GX.avoiding (⟨p, by omega⟩ : Fin Ω.numItems) →
      c ∈ GX.avoiding (⟨p + 1, hp⟩ : Fin Ω.numItems) → χ c ∈ GX.avoiding k) ∧
    χ (inr (FreeGroup.of ⟨p, by omega⟩) * inr (FreeGroup.of ⟨p + 1, hp⟩)) ∈ GX.avoiding k := by
  refine ⟨fun c hc hc' => ?_, ?_⟩
  · obtain ⟨hk, hk'⟩ | ⟨hk, hk'⟩ := hkk'
    · rw [hχ c (by rwa [(Fin.ext hk' : k' = ⟨p + 1, hp⟩)]), (Fin.ext hk : k = ⟨p, by omega⟩)]
      exact hc
    · rw [hχ c (by rwa [(Fin.ext hk' : k' = ⟨p, by omega⟩)]), (Fin.ext hk : k = ⟨p + 1, hp⟩)]
      exact hc'
  · rw [hpair]
    exact GX.inr_of_mem_avoiding (by rw [ne_eq, Fin.ext_iff]; omega)

/-- For such a shear `χ`, the words whose image avoids `hₖ` are the words in the items other than
`h_p, h_{p+1}` and in the product `h_p h_{p+1}`. -/
private theorem mem_avoiding_iff_of_shear {p : ℕ} (hp : p + 1 < Ω.numItems)
    {k k' : Fin Ω.numItems} (hkk' : (k : ℕ) = p ∧ (k' : ℕ) = p + 1 ∨ (k : ℕ) = p + 1 ∧ (k' : ℕ) = p)
    {χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems))} (hχ : ∀ c ∈ GX.avoiding k', χ c = c)
    (hpair : χ (inr (FreeGroup.of ⟨p, by omega⟩) * inr (FreeGroup.of ⟨p + 1, hp⟩)) =
      inr (FreeGroup.of k')) (c : GX (FreeGroup A) (Fin Ω.numItems)) :
    χ c ∈ GX.avoiding k ↔ c ∈ (GX.avoiding (⟨p, by omega⟩ : Fin Ω.numItems) ⊓
      GX.avoiding (⟨p + 1, hp⟩ : Fin Ω.numItems)) ⊔
        Subgroup.zpowers (inr (FreeGroup.of ⟨p, by omega⟩) * inr (FreeGroup.of ⟨p + 1, hp⟩)) := by
  obtain ⟨hfix, hpair'⟩ := mem_avoiding_of_shear hp hkk' hχ hpair
  have hle : (GX.avoiding (⟨p, by omega⟩ : Fin Ω.numItems) ⊓
      GX.avoiding (⟨p + 1, hp⟩ : Fin Ω.numItems)) ⊔
        Subgroup.zpowers (inr (FreeGroup.of ⟨p, by omega⟩) * inr (FreeGroup.of ⟨p + 1, hp⟩)) ≤
      (GX.avoiding k).comap χ.toMonoidHom := by
    refine sup_le (fun c hc => ?_) (Subgroup.zpowers_le.2 ?_) <;>
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    exacts [hfix c (Subgroup.mem_inf.1 hc).1 (Subgroup.mem_inf.1 hc).2, hpair']
  refine ⟨fun hc => ?_, fun hc => by
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] using hle hc⟩
  -- `χ⁻¹` after the substitution `hₖ ↦ 1` maps every word into the subgroup on the right.
  rw [← χ.symm_apply_apply c, ← GX.mem_avoiding.1 hc]
  generalize χ c = a
  induction a using Monoid.Coprod.induction_on with
  | inl g =>
    rw [eval_inl, χ.symm_apply_eq.2 (hχ _ (GX.inl_mem_avoiding _ g)).symm]
    exact Subgroup.mem_sup_left ⟨GX.inl_mem_avoiding _ g, GX.inl_mem_avoiding _ g⟩
  | inr f =>
    induction f with
    | one => simp
    | of j =>
      by_cases hj : j = k
      · simp [hj]
      rw [eval_inr_of, Function.update_of_ne hj]
      by_cases hj' : j = k'
      · rw [hj', χ.symm_apply_eq.2 hpair.symm]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      rw [χ.symm_apply_eq.2 (hχ _ (GX.inr_of_mem_avoiding hj')).symm]
      rw [Fin.ext_iff] at hj hj'
      exact Subgroup.mem_sup_left
        ⟨GX.inr_of_mem_avoiding (by simp only [ne_eq, Fin.ext_iff]; omega),
          GX.inr_of_mem_avoiding (by simp only [ne_eq, Fin.ext_iff]; omega)⟩
    | inv_of j h =>
      rw [map_inv, map_inv, map_inv]
      exact inv_mem h
    | mul x y hx hy =>
      rw [map_mul, map_mul, map_mul]
      exact mul_mem hx hy
  | mul x y hx hy =>
    rw [map_mul, map_mul]
    exact mul_mem hx hy

/-- Case (b), after the choice of the shear: the item `hₖ` of `μ` next to the boundary `p + 1` and
the other item `h_{k'}` next to it, and an automorphism `χ` fixing the words avoiding `h_{k'}` and
sending `h_p h_{p+1}` to `h_{k'}`. -/
private theorem separates_of_shear {μ : Fin Ω.numBases} {p : ℕ} (hp : p + 1 < Ω.numItems)
    {k k' : Fin Ω.numItems} (hkk' : (k : ℕ) = p ∧ (k' : ℕ) = p + 1 ∨ (k : ℕ) = p + 1 ∧ (k' : ℕ) = p)
    (hk : k ∈ Ω.baseItems μ) (hk' : (k' : ℕ) < Ω.left μ ∨ Ω.right μ ≤ (k' : ℕ))
    {χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems))} (hχ : ∀ c ∈ GX.avoiding k', χ c = c)
    (hpair : χ (inr (FreeGroup.of ⟨p, by omega⟩) * inr (FreeGroup.of ⟨p + 1, hp⟩)) =
      inr (FreeGroup.of k'))
    (hν : ∀ ν, ν ≠ μ → (Ω.left ν : ℕ) ≠ p + 1 ∧ (Ω.right ν : ℕ) ≠ p + 1)
    (hb : ∀ b ∈ Ω.constBases, (b.1 : ℕ) ≠ p ∧ (b.1 : ℕ) ≠ p + 1) (hc : Ω.connections = ∅) :
    Ω.Separates μ χ k where
  map_inl g := hχ _ (GX.inl_mem_avoiding _ g)
  mem_baseItems := hk
  map_inr := hχ _ (GX.inr_of_mem_avoiding (by rw [ne_eq, Fin.ext_iff]; omega))
  map_segment := hχ _ (Ω.toGX_segment_mem_avoiding _ hk')
  mem_avoiding_segment ν hν' :=
    have h := mem_avoiding_of_shear hp hkk' hχ hpair
    Ω.mem_avoiding_of_not_touches hp h.1 h.2 (hν ν hν').1 (hν ν hν').2
  mem_avoiding_const b hb' := by
    obtain ⟨h₁, h₂⟩ := hb b hb'
    rw [hχ _ (GX.inr_of_mem_avoiding (by rw [ne_eq, Fin.ext_iff]; omega))]
    exact GX.inr_of_mem_avoiding (by rw [ne_eq, Fin.ext_iff]; omega)
  mem_avoiding_connection c hc' := absurd hc' (by simp [hc])

/-- Case (b): an end-point `i ≠ 0, ρ` of `μ` touches no other base. After the shear sending
`h_{i-1} hᵢ` to the item next to `i` outside `μ`, the item next to `i` in `μ` is separated, and
the words whose image avoids it are the words in the items other than `h_{i-1}, hᵢ` and in
`h_{i-1} hᵢ`. -/
private theorem exists_separates_of_touches {μ : Fin Ω.numBases} {i : Fin (Ω.numItems + 1)}
    (hi : Ω.Touches i μ) (h0 : i ≠ 0) (hlast : i ≠ Fin.last Ω.numItems)
    (hν : ∀ ν, ν ≠ μ → ¬ Ω.Touches i ν)
    (hb : ∀ b ∈ Ω.constBases, (b.1 : ℕ) ≠ i ∧ (b.1 : ℕ) + 1 ≠ i) (hc : Ω.connections = ∅) :
    ∃ χ k, Ω.Separates μ χ k ∧ (k = i.pred h0 ∨ k = i.castPred hlast) ∧
      ∀ c, χ c ∈ GX.avoiding k ↔ c ∈ (GX.avoiding (i.pred h0) ⊓ GX.avoiding (i.castPred hlast)) ⊔
        Subgroup.zpowers
          (inr (FreeGroup.of (i.pred h0)) * inr (FreeGroup.of (i.castPred hlast))) := by
  obtain ⟨p, hp⟩ : ∃ p, (i : ℕ) = p + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Fin.val_ne_iff.2 h0)
  have hpn : p + 1 < Ω.numItems := hp ▸ Fin.val_lt_last hlast
  have hν' (ν : Fin Ω.numBases) (h : ν ≠ μ) :
      (Ω.left ν : ℕ) ≠ p + 1 ∧ (Ω.right ν : ℕ) ≠ p + 1 := by
    have := hν ν h
    rw [touches_iff, not_or, Fin.ext_iff, Fin.ext_iff] at this
    omega
  have hb' (b) (h : b ∈ Ω.constBases) : (b.1 : ℕ) ≠ p ∧ (b.1 : ℕ) ≠ p + 1 := by
    have := hb b h
    omega
  have hlr : (Ω.left μ : ℕ) < Ω.right μ := Ω.left_lt_right μ
  have hab : (⟨p, by omega⟩ : Fin Ω.numItems) ≠ ⟨p + 1, hpn⟩ := by simp [Fin.ext_iff]
  rw [(Fin.ext (by simp [hp]) : i.pred h0 = ⟨p, by omega⟩),
    (Fin.ext (by simp [hp]) : i.castPred hlast = ⟨p + 1, hpn⟩)]
  rw [touches_iff, Fin.ext_iff, Fin.ext_iff, hp] at hi
  rcases hi with hl | hr
  · -- `i = α(μ)`: the item `hᵢ` lies in `μ`; the shear is `h_{i-1} ↦ h_{i-1} hᵢ⁻¹`.
    have hχ (c) (hc : c ∈ GX.avoiding (⟨p, by omega⟩ : Fin Ω.numItems)) :
        GX.transvection (G := FreeGroup A) (⟨p, by omega⟩ : Fin Ω.numItems) 1
          (inr (FreeGroup.of ⟨p + 1, hpn⟩))⁻¹ (one_mem _)
          (inv_mem (GX.inr_of_mem_avoiding hab.symm)) c = c :=
      GX.transvection_apply_of_mem_avoiding _ _ hc
    have hpair : GX.transvection (G := FreeGroup A) (⟨p, by omega⟩ : Fin Ω.numItems) 1
          (inr (FreeGroup.of ⟨p + 1, hpn⟩))⁻¹
        (one_mem _) (inv_mem (GX.inr_of_mem_avoiding hab.symm))
          (inr (FreeGroup.of ⟨p, by omega⟩) * inr (FreeGroup.of ⟨p + 1, hpn⟩)) =
        inr (FreeGroup.of ⟨p, by omega⟩) := by
      simp [GX.transvection_inr_of_of_ne _ _ hab.symm]
    exact ⟨_, ⟨p + 1, hpn⟩, Ω.separates_of_shear hpn (Or.inr ⟨rfl, rfl⟩)
      (by rw [mem_baseItems]; simp only; omega) (Or.inl (by simp only; omega)) hχ hpair hν' hb' hc,
      .inr rfl, mem_avoiding_iff_of_shear hpn (Or.inr ⟨rfl, rfl⟩) hχ hpair⟩
  · -- `i = β(μ)`: the item `h_{i-1}` lies in `μ`; the shear is `hᵢ ↦ h_{i-1}⁻¹ hᵢ`.
    have hχ (c) (hc : c ∈ GX.avoiding (⟨p + 1, hpn⟩ : Fin Ω.numItems)) :
        GX.transvection (G := FreeGroup A) (⟨p + 1, hpn⟩ : Fin Ω.numItems)
          (inr (FreeGroup.of ⟨p, by omega⟩))⁻¹ 1
          (inv_mem (GX.inr_of_mem_avoiding hab)) (one_mem _) c = c :=
      GX.transvection_apply_of_mem_avoiding _ _ hc
    have hpair : GX.transvection (G := FreeGroup A) (⟨p + 1, hpn⟩ : Fin Ω.numItems)
          (inr (FreeGroup.of ⟨p, by omega⟩))⁻¹ 1
        (inv_mem (GX.inr_of_mem_avoiding hab)) (one_mem _)
          (inr (FreeGroup.of ⟨p, by omega⟩) * inr (FreeGroup.of ⟨p + 1, hpn⟩)) =
        inr (FreeGroup.of ⟨p + 1, hpn⟩) := by
      simp [GX.transvection_inr_of_of_ne _ _ hab]
    exact ⟨_, ⟨p, by omega⟩, Ω.separates_of_shear hpn (Or.inl ⟨rfl, rfl⟩)
      (by rw [mem_baseItems]; simp only; omega) (Or.inr (by simp only; omega)) hχ hpair hν' hb' hc,
      .inl rfl, mem_avoiding_iff_of_shear hpn (Or.inl ⟨rfl, rfl⟩) hχ hpair⟩

/-- The word of a base other than `μ`, with either sign, avoids the separated item. -/
private theorem Separates.mem_avoiding_segment' {μ : Fin Ω.numBases}
    {χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems))} {k : Fin Ω.numItems} (h : Ω.Separates μ χ k)
    {ν : Fin Ω.numBases} (hν : ν ≠ μ) (s : Bool) :
    χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment (Ω.left ν) (Ω.right ν) s))) ∈
      GX.avoiding k := by
  cases s
  · rw [toGX_segment_false, map_inv]
    exact inv_mem (h.mem_avoiding_segment ν hν)
  · exact h.mem_avoiding_segment ν hν

/-- After `χ`, the separated item occurs in no equation of `Ω` with `μ, Δ(μ)` removed. -/
private theorem Separates.mem_avoiding_toSystem {μ : Fin Ω.numBases}
    {χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems))} {k : Fin Ω.numItems} (h : Ω.Separates μ χ k)
    {t : GX (FreeGroup A) (Fin Ω.numItems)} (ht : t ∈ (Ω.removePair μ).toSystem) :
    χ t ∈ GX.avoiding k := by
  have key : ∀ e ∈ (Ω.removePair μ).equations,
      χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk e.1)) ∈ GX.avoiding k ∧
        χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk e.2)) ∈ GX.avoiding k := by
    refine ((Ω.removePair μ).forall_mem_equations).2
      ⟨fun ν' => ?_, fun b hb => ?_, fun c hc' => ?_⟩
    · rw [basicEquation_removeBases, basicEquation_fst, basicEquation_snd]
      have hν := Finset.mem_compl.1 (Finset.orderEmbOfFin_mem ({μ, Ω.dual μ} : Finset _)ᶜ rfl ν')
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hν
      exact ⟨h.mem_avoiding_segment' hν.1 _, h.mem_avoiding_segment'
        (fun h' => hν.2 ((Ω.dual_involutive _).symm.trans (congrArg Ω.dual h'))) _⟩
    · obtain ⟨j, a, s⟩ := b
      refine ⟨by simpa [EqIneqSystem.toGX_eq_lift, FreeGroup.lift_mk] using
        h.mem_avoiding_const _ hb, ?_⟩
      cases s <;> simp [EqIneqSystem.toGX_eq_lift, FreeGroup.lift_mk, h.map_inl]
    · rw [boundaryEquation_removeBases]
      have hν := Finset.mem_compl.1
        (Finset.orderEmbOfFin_mem ({μ, Ω.dual μ} : Finset _)ᶜ rfl c.2.1)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hν
      exact h.mem_avoiding_connection _ ((mem_connections_removeBases _).1 hc') hν.1 hν.2
  obtain ⟨e, he, rfl⟩ := (mem_toSystem_iff _).1 ht
  rw [map_mul, map_inv, map_mul, map_inv]
  exact mul_mem (key e he).1 (inv_mem (key e he).2)

/-- After `χ`, the basic equation of `μ` if `ε(μ) = 1`, and that of `Δ(μ)` if `ε(μ) = -1`, is
`u hₖ v` with `hₖ` occurring neither in `u` nor in `v`. -/
private theorem Separates.exists_eq_mul {μ : Fin Ω.numBases}
    {χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems))} {k : Fin Ω.numItems} (h : Ω.Separates μ χ k)
    (hd : Ω.dual μ ≠ μ) {ν : Fin Ω.numBases}
    (hν : Ω.sign μ = true ∧ ν = μ ∨ Ω.sign μ = false ∧ ν = Ω.dual μ) :
    ∃ u v, u ∈ GX.avoiding k ∧ v ∈ GX.avoiding k ∧
      χ (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.basicEquation ν).1 *
        (FreeGroup.mk (Ω.basicEquation ν).2)⁻¹)) = u * inr (FreeGroup.of k) * v := by
  -- `χ` fixes the word `P hₖ Q` of `μ`, and sends the word of `Δ(μ)` to a word `R` avoiding `hₖ`
  have hk := Ω.mem_baseItems.1 h.mem_baseItems
  have hL := Ω.toGX_segment_eq_mul hk.1 hk.2 (Nat.lt_succ_iff.1 (Ω.right μ).isLt)
  simp only [Fin.eta] at hL
  have hP := Ω.toGX_segment_mem_avoiding (i := Ω.left μ) (j := k) true (Or.inr le_rfl)
  have hQ := Ω.toGX_segment_mem_avoiding (i := k + 1) (j := Ω.right μ) true
    (Or.inl (Nat.lt_succ_self _))
  have hR := h.mem_avoiding_segment' hd (Ω.sign (Ω.dual μ))
  rcases hν with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
  · -- the equation of `μ` is `(P hₖ Q) R⁻¹`
    refine ⟨_, _, hP, mul_mem hQ (inv_mem hR), ?_⟩
    rw [basicEquation_fst, basicEquation_snd, hs, map_mul, map_inv, map_mul χ, map_inv χ,
      h.map_segment, hL]
    simp only [mul_assoc]
  · -- the equation of `Δ(μ)` is `R (P hₖ Q)`
    refine ⟨_, _, mul_mem hR hP, hQ, ?_⟩
    rw [basicEquation_fst, basicEquation_snd, Ω.dual_involutive μ, hs, map_mul, map_inv,
      toGX_segment_false, inv_inv, map_mul χ, h.map_segment, hL]
    simp only [mul_assoc]

/-- If the item `hₖ` is separated in `μ` by `χ`, the group presented by the system of `Ω` with
`μ, Δ(μ)` removed is the free product of the group presented by `Ω*` with `⟨z⟩`, by an isomorphism
sending the class of a word whose image under `χ` avoids `hₖ` to its class, the basic equation of
`μ` to `z`, and `hₖ` to `u z^{±1} v` for the classes `u, v` of two such words. -/
private theorem Separates.exists_mulEquiv {μ : Fin Ω.numBases}
    {χ : MulAut (GX (FreeGroup A) (Fin Ω.numItems))} {k : Fin Ω.numItems} (h : Ω.Separates μ χ k)
    (hc : ∀ c ∈ Ω.connections, c.2.1 ≠ μ) (hd : Ω.dual μ ≠ μ) :
    ∃ e : SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem ≃*
        GX (SystemGroup (FreeGroup A) Ω.toSystem) Unit,
      (∀ w : GX (FreeGroup A) (Fin Ω.numItems), χ w ∈ GX.avoiding k →
        e (w : SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem) =
          inl (w : SystemGroup (FreeGroup A) Ω.toSystem)) ∧
      e ((EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.basicEquation μ).1 *
          (FreeGroup.mk (Ω.basicEquation μ).2)⁻¹) : GX (FreeGroup A) (Fin Ω.numItems)) :
        SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem) = inr (FreeGroup.of ()) ∧
      (∃ u v : GX (FreeGroup A) (Fin Ω.numItems), χ u ∈ GX.avoiding k ∧ χ v ∈ GX.avoiding k ∧
        ∃ n : ℤˣ, e ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) :
          SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem) =
            inl (u : SystemGroup (FreeGroup A) Ω.toSystem) * inr (FreeGroup.of ()) ^ (n : ℤ) *
              inl (v : SystemGroup (FreeGroup A) Ω.toSystem)) ∧
      ∀ w : GX (FreeGroup A) (Fin Ω.numItems),
        eval (MonoidHom.id (SystemGroup (FreeGroup A) Ω.toSystem)) (fun _ => 1)
            (e (w : SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem)) =
          (w : SystemGroup (FreeGroup A) Ω.toSystem) := by
  -- After the change of variables `χ`, the item `hₖ` occurs in no other equation, and the basic
  -- equation of `μ` (or of `Δ(μ)`, according to the sign of `μ`) is `u hₖ v`; it is eliminated.
  have hS (t) (ht : t ∈ (Ω.removePair μ).toSystem) := h.mem_avoiding_toSystem ht
  have hk : χ.symm (inr (FreeGroup.of k)) = inr (FreeGroup.of k) :=
    χ.symm_apply_eq.2 h.map_inr.symm
  cases hs : Ω.sign μ
  · -- `ε(μ) = -1`: the equation of `Δ(μ)` is the inverse of that of `μ`, so `z` is inverted.
    obtain ⟨u, v, hu, hv, hτ⟩ := h.exists_eq_mul hd (.inr ⟨hs, rfl⟩)
    have hT := normalClosure_toSystem_eq_insert_removePair hc (Or.inr rfl)
    refine ⟨(SystemGroup.elimEquiv χ hu hv hτ hS hT).trans (GX.invertVar _ ()),
      fun w hw => ?_, ?_, ⟨χ.symm u⁻¹, χ.symm v⁻¹, by simpa using hu, by simpa using hv, -1, ?_⟩,
      fun w => ?_⟩
    · rw [MulEquiv.trans_apply, SystemGroup.elimEquiv_mk_of_mem_avoiding χ hu hv hτ hS hT hw]
      exact GX.invertVar_inl _ _
    · have hinv := Ω.mk_basicEquation_dual (Ω.dual μ)
      rw [Ω.dual_involutive μ] at hinv
      rw [hinv, map_inv, QuotientGroup.mk_inv]
      simp
    · rw [MulEquiv.trans_apply, ← hk, SystemGroup.elimEquiv_mk_symm_inr_of]
      simp
    · simp
  · obtain ⟨u, v, hu, hv, hτ⟩ := h.exists_eq_mul hd (.inl ⟨hs, rfl⟩)
    have hT := normalClosure_toSystem_eq_insert_removePair hc (Or.inl rfl)
    refine ⟨SystemGroup.elimEquiv χ hu hv hτ hS hT,
      fun w hw => SystemGroup.elimEquiv_mk_of_mem_avoiding χ hu hv hτ hS hT hw,
      SystemGroup.elimEquiv_mk_self χ hu hv hτ hS hT,
      ⟨χ.symm u⁻¹, χ.symm v⁻¹, by simpa using hu, by simpa using hv, 1, ?_⟩,
      SystemGroup.eval_elimEquiv_mk χ hu hv hτ hS hT⟩
    rw [← hk, SystemGroup.elimEquiv_mk_symm_inr_of]
    simp

/-- **Elimination of a base by rule (a).** Let `hₖ` be an item of degree one of a base `μ` which
is not its own dual and through which no boundary connection passes. The group presented by the
system of `Ω` with the pair `μ, Δ(μ)` removed is the free product of the group presented by `Ω*`
with an infinite cyclic group `⟨z⟩`, by an isomorphism which sends the class of a word in which
`hₖ` does not occur to its class, the basic equation of `μ` to `z`, and `hₖ` to `u z^{±1} v` for
the classes `u, v` of two such words, and after which sending `z` to `1` is the homomorphism
induced by the identity on the items. In particular `hₖ = u v` in the group presented by `Ω*`. -/
theorem exists_mulEquiv_removePair_of_degree_eq_one {μ : Fin Ω.numBases}
    (hc : ∀ c ∈ Ω.connections, c.2.1 ≠ μ) (hd : Ω.dual μ ≠ μ) {k : Fin Ω.numItems}
    (hk : k ∈ Ω.baseItems μ) (hdeg : Ω.degree k = 1) :
    ∃ e : SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem ≃*
        GX (SystemGroup (FreeGroup A) Ω.toSystem) Unit,
      (∀ w : GX (FreeGroup A) (Fin Ω.numItems), w ∈ GX.avoiding k →
        e (w : SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem) =
          inl (w : SystemGroup (FreeGroup A) Ω.toSystem)) ∧
      e ((EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.basicEquation μ).1 *
          (FreeGroup.mk (Ω.basicEquation μ).2)⁻¹) : GX (FreeGroup A) (Fin Ω.numItems)) :
        SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem) = inr (FreeGroup.of ()) ∧
      (∃ u v : GX (FreeGroup A) (Fin Ω.numItems), u ∈ GX.avoiding k ∧ v ∈ GX.avoiding k ∧
        ∃ n : ℤˣ, e ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) :
          SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem) =
            inl (u : SystemGroup (FreeGroup A) Ω.toSystem) * inr (FreeGroup.of ()) ^ (n : ℤ) *
              inl (v : SystemGroup (FreeGroup A) Ω.toSystem)) ∧
      ∀ w : GX (FreeGroup A) (Fin Ω.numItems),
        eval (MonoidHom.id (SystemGroup (FreeGroup A) Ω.toSystem)) (fun _ => 1)
            (e (w : SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem)) =
          (w : SystemGroup (FreeGroup A) Ω.toSystem) :=
  (separates_of_degree_eq_one hk hdeg).exists_mulEquiv hc hd

/-- **Elimination of a base by rule (b).** Let `Ω` have no boundary connections and let `i`,
different from the first and the last boundary, be an end-point of a base `μ` which is not its own
dual, and of no other base. Let `W` be the subgroup of the words in the items other than
`h_{i-1}, hᵢ` and in the product `h_{i-1} hᵢ`. The group presented by the system of `Ω` with the
pair `μ, Δ(μ)` removed is the free product of the group presented by `Ω*` with an infinite cyclic
group `⟨z⟩`, by an isomorphism which sends the class of a word of `W` to its class, the basic
equation of `μ` to `z`, and each of `h_{i-1}, hᵢ` to `u z^{±1} v` for the classes `u, v` of two
words of `W`, and after which sending `z` to `1` is the homomorphism induced by the identity on the
items. In particular `h_{i-1}` and `hᵢ` are products `u v` of two words of `W` in the group
presented by `Ω*`. -/
theorem exists_mulEquiv_removePair_of_touches (hc : Ω.connections = ∅) {μ : Fin Ω.numBases}
    (hd : Ω.dual μ ≠ μ) {i : Fin (Ω.numItems + 1)} (hi : Ω.Touches i μ) (h0 : i ≠ 0)
    (hlast : i ≠ Fin.last Ω.numItems) (hν : ∀ ν, ν ≠ μ → ¬ Ω.Touches i ν)
    (hb : ∀ b ∈ Ω.constBases, (b.1 : ℕ) ≠ i ∧ (b.1 : ℕ) + 1 ≠ i) :
    ∃ e : SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem ≃*
        GX (SystemGroup (FreeGroup A) Ω.toSystem) Unit,
      (∀ w : GX (FreeGroup A) (Fin Ω.numItems),
        w ∈ (GX.avoiding (i.pred h0) ⊓ GX.avoiding (i.castPred hlast)) ⊔ Subgroup.zpowers
          (inr (FreeGroup.of (i.pred h0)) * inr (FreeGroup.of (i.castPred hlast))) →
        e (w : SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem) =
          inl (w : SystemGroup (FreeGroup A) Ω.toSystem)) ∧
      e ((EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.basicEquation μ).1 *
          (FreeGroup.mk (Ω.basicEquation μ).2)⁻¹) : GX (FreeGroup A) (Fin Ω.numItems)) :
        SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem) = inr (FreeGroup.of ()) ∧
      (∀ j, j = i.pred h0 ∨ j = i.castPred hlast → ∃ u v : GX (FreeGroup A) (Fin Ω.numItems),
        u ∈ (GX.avoiding (i.pred h0) ⊓ GX.avoiding (i.castPred hlast)) ⊔ Subgroup.zpowers
          (inr (FreeGroup.of (i.pred h0)) * inr (FreeGroup.of (i.castPred hlast))) ∧
        v ∈ (GX.avoiding (i.pred h0) ⊓ GX.avoiding (i.castPred hlast)) ⊔ Subgroup.zpowers
          (inr (FreeGroup.of (i.pred h0)) * inr (FreeGroup.of (i.castPred hlast))) ∧
        ∃ n : ℤˣ, e ((inr (FreeGroup.of j) : GX (FreeGroup A) (Fin Ω.numItems)) :
          SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem) =
            inl (u : SystemGroup (FreeGroup A) Ω.toSystem) * inr (FreeGroup.of ()) ^ (n : ℤ) *
              inl (v : SystemGroup (FreeGroup A) Ω.toSystem)) ∧
      ∀ w : GX (FreeGroup A) (Fin Ω.numItems),
        eval (MonoidHom.id (SystemGroup (FreeGroup A) Ω.toSystem)) (fun _ => 1)
            (e (w : SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem)) =
          (w : SystemGroup (FreeGroup A) Ω.toSystem) := by
  obtain ⟨χ, k, h, hk, hW⟩ := exists_separates_of_touches hi h0 hlast hν hb hc
  obtain ⟨e, he, hz, ⟨u, v, hu, hv, n, hek⟩, hw⟩ := h.exists_mulEquiv (by simp [hc]) hd
  rw [hW] at hu hv
  have hp := Subgroup.mem_sup_right (S := GX.avoiding (i.pred h0) ⊓ GX.avoiding (i.castPred hlast))
    (Subgroup.mem_zpowers
      (inr (FreeGroup.of (i.pred h0)) * inr (FreeGroup.of (i.castPred hlast)) :
        GX (FreeGroup A) (Fin Ω.numItems)))
  refine ⟨e, fun w hw => he w ((hW w).2 hw), hz, fun j hj => ?_, hw⟩
  -- The other item of the pair is `h_{i-1} hᵢ` divided by the separated one.
  have hpair := he _ ((hW _).2 hp)
  simp only [QuotientGroup.mk_mul, map_mul] at hpair
  rcases hk with rfl | rfl <;> rcases hj with rfl | rfl
  · exact ⟨u, v, hu, hv, n, hek⟩
  · refine ⟨v⁻¹, u⁻¹ * _, inv_mem hv, mul_mem (inv_mem hu) hp, -n, ?_⟩
    rw [hek] at hpair
    rw [eq_inv_mul_of_mul_eq hpair]
    simp [mul_assoc]
  · refine ⟨_ * v⁻¹, u⁻¹, mul_mem hp (inv_mem hv), inv_mem hu, -n, ?_⟩
    rw [hek] at hpair
    rw [eq_mul_inv_of_mul_eq hpair]
    simp [mul_assoc]
  · exact ⟨u, v, hu, hv, n, hek⟩

/-- **Elimination of a base on presented groups.** If `Ω` has no boundary connections and `μ` is
eliminable, the group presented by the system of `Ω` with the pair `μ, Δ(μ)` removed is
`F(A)`-isomorphic to the free product of the group presented by `Ω*` with an infinite cyclic group
`⟨z⟩`, by an isomorphism sending the basic equation of `μ` to `z`; sending `z` to `1` gives back
the homomorphism induced by the identity on the items. -/
theorem exists_bijective_systemGroup_removePair (hc : Ω.connections = ∅) {μ : Fin Ω.numBases}
    (hμ : Ω.IsEliminable μ) :
    ∃ e : GHom (SystemGroup.coeff (Ω.removePair μ).toSystem)
        ((inl : SystemGroup (FreeGroup A) Ω.toSystem →*
          GX (SystemGroup (FreeGroup A) Ω.toSystem) Unit).comp (SystemGroup.coeff Ω.toSystem)),
      Function.Bijective e ∧
      e ((EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.basicEquation μ).1 *
          (FreeGroup.mk (Ω.basicEquation μ).2)⁻¹) : GX (FreeGroup A) (Fin Ω.numItems)) :
        SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem) = inr (FreeGroup.of ()) ∧
      ∀ w : GX (FreeGroup A) (Fin Ω.numItems),
        eval (MonoidHom.id (SystemGroup (FreeGroup A) Ω.toSystem)) (fun _ => 1)
            (e (w : SystemGroup (FreeGroup A) (Ω.removePair μ).toSystem)) =
          (w : SystemGroup (FreeGroup A) Ω.toSystem) := by
  obtain ⟨hd, hμ⟩ := hμ
  obtain ⟨χ, k, h⟩ : ∃ χ k, Ω.Separates μ χ k := by
    obtain ⟨k, hk, hdeg⟩ | ⟨i, hi, h0, hlast, hν, hb⟩ := hμ
    · exact ⟨1, k, separates_of_degree_eq_one hk hdeg⟩
    · obtain ⟨χ, k, h, -⟩ := exists_separates_of_touches hi h0 hlast hν hb hc
      exact ⟨χ, k, h⟩
  obtain ⟨e, he, hz, -, hw⟩ := h.exists_mulEquiv (by simp [hc]) hd
  exact ⟨GHom.ofMulEquiv e fun g => by
      simpa using he (inl g) (by rw [h.map_inl]; exact GX.inl_mem_avoiding k g),
    GHom.ofMulEquiv_bijective _ _, by rw [GHom.coe_ofMulEquiv]; exact hz,
    fun w => by simpa using hw w⟩

/-! ### Examples -/

/-- The generalised equation with the single basic equation `h₀h₁ = h₂`. -/
private abbrev productExample : GenEq (Fin 2) where
  numItems := 3
  numBases := 2
  left := ![0, 2]
  right := ![2, 3]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- In `h₀h₁ = h₂` the base `[0, 2]` contains the item `h₀` of degree one, so it is eliminable
by rule (a). -/
example : productExample.IsEliminable 0 := by
  decide

/-- The generalised equation with the basic equations `h₀h₁ = h₂h₃` (twice) and
`h₁h₂h₃ = h₀h₁h₂`, given by the pairs `[0, 2] ∼ [2, 4]`, `[0, 2] ∼ [2, 4]` and `[1, 4] ∼ [0, 3]`.
-/
private abbrev ruleBExample : GenEq (Fin 2) where
  numItems := 4
  numBases := 6
  left := ![0, 2, 0, 2, 1, 0]
  right := ![2, 4, 2, 4, 4, 3]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0, 3, 2, 5, 4]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- The base `[1, 4]` has no item of degree one, but its end-point `1` touches no other base, so
it is eliminable by rule (b). -/
example : ruleBExample.IsEliminable 4 := by
  decide

/-- The base `[0, 2]` is not eliminable: each of its items lies in at least three bases, and its
end-point `2` touches three other bases. -/
example : ¬ ruleBExample.IsEliminable 0 := by
  decide

end GenEq

end TauCeti
