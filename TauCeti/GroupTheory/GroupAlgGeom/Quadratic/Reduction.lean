/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Automorphism
import Mathlib.Algebra.Group.Subgroup.Finite
import TauCeti.GroupTheory.GroupAlgGeom.ChangeOfCoordinates
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.AtomicForm
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.CoeffConjugate
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Spelling
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.StandardForm

/-!
# Reduction of strictly quadratic words to standard form

A strictly quadratic word of `G[X]` is brought to a standard quadratic word, or to a coefficient,
by a product of elementary `G`-automorphisms of `G[X]` (`GX.elementaryAut`) followed by a
conjugation in `G[X]` (`exists_standardForm`). This is the corrected form of Kharlampovich–Myasnikov
[IFT, §2.7, Lemma 1] and [VAR-I, §1, Lemma 6], which omit the coefficient branch: a coefficient
`g ≠ 1` and its conjugates `z⁻¹ g z` are strictly quadratic (`isStrictlyQuadratic_inl`,
`isStrictlyQuadratic_inv_mul_inl_mul_self`), and no standard quadratic word is conjugate to a
coefficient (`Standard.toWord_ne_conj_inl`). Moreover, variables outside `S.vars` are
unconstrained (`mem_V_congr`, `Standard.occurrences_toWord_eq_zero_iff`).

A reduced word with no variable letters is already a coefficient `inl c` (the base case).
Following Gallier–Xu [GaXu, Lemma 6.1], any reduced word with at least one variable letter in which
every variable occurs zero or two times contains either a same-sign pair `x^b M x^b` (cross-cap),
an alternating pair `x^bx U y^by V x^(!bx) W y^(!by)` (handle), or an innermost opposite-sign
pair `z^b c z^(!b)` enclosing a single nontrivial coefficient `c`. Repeatedly extracting these
leaves a word in atomic form (`AtomicForm`), which `AtomicForm.exists_standardForm` reduces to a
coefficient or a standard quadratic equation.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.exists_standardForm`: every strictly quadratic word in `G[X]` is
  carried by an elementary `G`-automorphism (fixing every word in variables disjoint from those
  occurring in the word) and a conjugation either to a coefficient `inl c` (`c ∈ G`) or to
  `S.toWord` for a standard quadratic equation `S : Standard G X` whose variables `S.vars` all
  occur in the word.
* `TauCeti.GroupAlgGeom.Quadratic.not_exists_standard_of_conj_mulEquiv_eq_inl`: reaching a
  coefficient `inl c` by an isomorphism fixing `inl c` and arbitrary conjugation in its target
  rules out reaching a standard quadratic equation by any homomorphism fixing `inl c` and arbitrary
  conjugation in its target.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definitions 2–3 and Lemma 1, p. 8.
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1, Lemma 6,
  p. 8.
* [GaXu] J. Gallier, D. Xu, *A guide to the classification theorem for compact surfaces*,
  Springer (2013), Chapter 6, Lemma 6.1.
-/

public section

open Monoid.Coprod Subgroup Function
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Quadratic

/-! ### Pattern analysis and reduction to atomic form -/

section Reduction

variable {G X : Type*} [Group G]

private theorem isStrictlyQuadratic_and_occVars_prod [DecidableEq X]
    (extracted : Finset X) {w : GX G X} (hw : IsStrictlyQuadratic {w})
    {L : List (G ⊕ X × Bool)} (hzero : ∀ v ∈ extracted, GX.countVar v L = 0)
    (hoff : ∀ v ∉ extracted, GX.countVar v L = occurrences v w) :
    IsStrictlyQuadratic {(L.map GX.letter).prod} ∧
      occVars (L.map GX.letter).prod ⊆ occVars w \ extracted := by
  refine ⟨isStrictlyQuadratic_singleton.2 fun v => ?_, fun v hv => ?_⟩
  · obtain ⟨k, hk⟩ := GX.exists_countVar_eq_add_two_mul v L
    rw [← occurrences_eq_countVar_reducedWord] at hk
    have hwv := isStrictlyQuadratic_singleton.1 hw v
    by_cases hve : v ∈ extracted
    · have := hzero v hve; omega
    · have := hoff v hve; omega
  · rw [Finset.mem_sdiff, mem_occVars_iff]
    have hle := GX.countVar_reducedWord_le v L
    rw [← occurrences_eq_countVar_reducedWord] at hle
    have hv0 := mem_occVars_iff.1 hv
    refine ⟨?_, fun hve => ?_⟩
    · by_cases hve' : v ∈ extracted
      · have := hzero v hve'; omega
      · have := hoff v hve'; omega
    · have := hzero v hve; omega

private theorem countVar_reducedWord_eq_two_of_mem {w : GX G X} (hw : IsStrictlyQuadratic {w})
    {x : X} {b : Bool} (hm : .inr (x, b) ∈ GX.reducedWord w) :
    GX.countVar x (GX.reducedWord w) = 2 ∧ x ∈ occVars w := by
  have hpos : 0 < GX.countVar x (GX.reducedWord w) :=
    Nat.pos_of_ne_zero fun h0 => GX.countVar_eq_zero.1 h0 b hm
  have h2 := isStrictlyQuadratic_singleton.1 hw x
  rw [occurrences_eq_countVar_reducedWord] at h2
  have hc : GX.countVar x (GX.reducedWord w) = 2 := by omega
  exact ⟨hc, mem_occVars_iff.2 (by rw [occurrences_eq_countVar_reducedWord, hc]; decide)⟩

private theorem eq_prod_of_reducedWord_eq {w : GX G X} {L : List (G ⊕ X × Bool)}
    (hl : GX.reducedWord w = L) : w = (L.map GX.letter).prod :=
  (GX.prod_reducedWord w).symm.trans (congrArg (fun l => (l.map GX.letter).prod) hl)

variable [DecidableEq X]

private def signAut (x : X) (b : Bool) : MulAut (GX G X) :=
  if b then 1 else GX.invertVar G x

private theorem signAut_mem_elementaryAut (x : X) (b : Bool) :
    signAut (G := G) x b ∈ GX.elementaryAut G X := by
  cases b <;> simp [signAut]

private theorem signAut_letter_self (x : X) (b : Bool) :
    signAut (G := G) x b (GX.letter (.inr (x, b))) = inr (FreeGroup.of x) := by
  cases b <;> simp [signAut]

private theorem signAut_letter_not (x : X) (b : Bool) :
    signAut (G := G) x b (GX.letter (.inr (x, !b))) = (inr (FreeGroup.of x))⁻¹ := by
  cases b <;> simp [signAut]

private theorem signAut_apply_of_mem_avoiding {x : X} {b : Bool} {a : GX G X}
    (ha : a ∈ GX.avoiding x) : signAut x b a = a := by
  cases b <;> simp [signAut, ha]

private theorem step_sameSign {w : GX G X} (hw : IsStrictlyQuadratic {w}) {x : X} {b : Bool}
    {P M Q : List (G ⊕ X × Bool)}
    (hl : GX.reducedWord w = P ++ [.inr (x, b)] ++ M ++ [.inr (x, b)] ++ Q) :
    ∃ f ∈ GX.elementaryAut G X, ∃ R' : GX G X,
      IsStrictlyQuadratic {R'} ∧ occVars R' ⊆ occVars w ∧ x ∈ occVars w ∧ x ∉ occVars R' ∧
      (∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f a = a) ∧
      f w = sqWord x * R' := by
  obtain ⟨hx2, hxk⟩ := countVar_reducedWord_eq_two_of_mem (x := x) (b := b) hw (by simp [hl])
  have hPMQ : GX.countVar x P = 0 ∧ GX.countVar x M = 0 ∧ GX.countVar x Q = 0 := by
    simp [hl] at hx2; omega
  set p := (P.map GX.letter).prod
  set m := (M.map GX.letter).prod
  set q := (Q.map GX.letter).prod
  have hp : p ∈ GX.avoiding x := GX.prod_map_letter_mem_avoiding hPMQ.1
  have hm : m ∈ GX.avoiding x := GX.prod_map_letter_mem_avoiding hPMQ.2.1
  have hq : q ∈ GX.avoiding x := GX.prod_map_letter_mem_avoiding hPMQ.2.2
  have hw_eq : w = p * GX.letter (.inr (x, b)) * m * GX.letter (.inr (x, b)) * q := by
    simpa [p, m, q, mul_assoc] using eq_prod_of_reducedWord_eq hl
  let f₁ := signAut (G := G) x b
  let f₂ := GX.transvection x p⁻¹ 1 (inv_mem hp) (one_mem _)
  let f₃ := GX.transvection x 1 (m * p⁻¹)⁻¹ (one_mem _) (inv_mem (mul_mem hm (inv_mem hp)))
  have hf_mem : f₃ * f₂ * f₁ ∈ GX.elementaryAut G X :=
    mul_mem (mul_mem (GX.transvection_mem_elementaryAut _ _ _)
      (GX.transvection_mem_elementaryAut _ _ _)) (signAut_mem_elementaryAut x b)
  set L := P ++ GX.invRev M ++ Q
  have hLx : GX.countVar x L = 0 := by
    simp [L, hPMQ.1, hPMQ.2.1, hPMQ.2.2, GX.countVar_invRev]
  have hrem := isStrictlyQuadratic_and_occVars_prod {x} hw (L := L)
    (fun v hv => by rw [Finset.mem_singleton.1 hv]; exact hLx)
    fun v hv => by
      simp only [Finset.mem_singleton] at hv
      simp [occurrences_eq_countVar_reducedWord, hl, L, Ne.symm hv, GX.countVar_invRev]
  have hstep₁ : f₁ w = p * inr (FreeGroup.of x) * m * inr (FreeGroup.of x) * q := by
    rw [hw_eq]
    simp [f₁, signAut_letter_self, signAut_apply_of_mem_avoiding, hp, hm, hq]
  have hstep₂ : f₂ (f₁ w) = inr (FreeGroup.of x) * (m * p⁻¹) * inr (FreeGroup.of x) * q := by
    rw [hstep₁]
    simp [f₂, hp, hm, hq, mul_assoc]
  have hstep₃ : f₃ (f₂ (f₁ w)) = sqWord x * (p * m⁻¹ * q) := by
    rw [hstep₂, GX.transvection_crossCap (mul_mem hm (inv_mem hp)) hq]
    simp [sqWord_def, mul_assoc]
  refine ⟨f₃ * f₂ * f₁, hf_mem, (L.map GX.letter).prod, hrem.1,
    hrem.2.trans Finset.sdiff_subset, hxk,
    fun h => (Finset.mem_sdiff.1 (hrem.2 h)).2 (Finset.mem_singleton_self x),
    fun a ha => ?_, ?_⟩
  · simp [f₁, f₂, f₃, signAut_apply_of_mem_avoiding (ha x hxk), ha x hxk]
  · have hLprod : (L.map GX.letter).prod = p * m⁻¹ * q := by
      simp [L, p, m, q, GX.prod_map_letter_invRev, mul_assoc]
    rw [MulAut.mul_apply, MulAut.mul_apply, hstep₃, hLprod]

private theorem exists_aut_signed_handle {x y : X} {bx by_ : Bool} {p u v w₀ z : GX G X}
    (hxy : x ≠ y) (hp : p ∈ GX.avoiding x ∧ p ∈ GX.avoiding y)
    (hu : u ∈ GX.avoiding x ∧ u ∈ GX.avoiding y) (hv : v ∈ GX.avoiding x ∧ v ∈ GX.avoiding y)
    (hw₀ : w₀ ∈ GX.avoiding x ∧ w₀ ∈ GX.avoiding y)
    (hz : z ∈ GX.avoiding x ∧ z ∈ GX.avoiding y) :
    ∃ f ∈ GX.elementaryAut G X,
      (∀ a, a ∈ GX.avoiding x → a ∈ GX.avoiding y → f a = a) ∧
      f (p * GX.letter (.inr (x, bx)) * u * GX.letter (.inr (y, by_)) * v *
          GX.letter (.inr (x, !bx)) * w₀ * GX.letter (.inr (y, !by_)) * z) =
        commWord (x, y) * (p * w₀ * v * u * z) := by
  obtain ⟨φ₃, hφ₃, hφ₃_eq, hφ₃_fix⟩ := GX.exists_mem_elementaryAut_apply_handle hxy
    (Subgroup.mem_inf.2 hu) (Subgroup.mem_inf.2 hv)
    (mul_mem (Subgroup.mem_inf.2 hp) (Subgroup.mem_inf.2 hw₀)) (Subgroup.mem_inf.2 hz)
  let φ₁₂ : MulAut (GX G X) :=
    GX.transvection x p⁻¹ 1 (inv_mem hp.1) (one_mem _) * signAut y by_ * signAut x bx
  have hφ₁₂_fix : ∀ a, a ∈ GX.avoiding x → a ∈ GX.avoiding y → φ₁₂ a = a := fun a hax hay => by
    simp [φ₁₂, signAut_apply_of_mem_avoiding hax, signAut_apply_of_mem_avoiding hay, hax]
  have hφ₁₂_xbx : φ₁₂ (GX.letter (.inr (x, bx))) = p⁻¹ * inr (FreeGroup.of x) := by
    rw [MulAut.mul_apply, MulAut.mul_apply, signAut_letter_self,
      signAut_apply_of_mem_avoiding (GX.inr_of_mem_avoiding hxy),
      GX.transvection_inr_of_self, mul_one]
  have hφ₁₂_yby : φ₁₂ (GX.letter (.inr (y, by_))) = inr (FreeGroup.of y) := by
    rw [MulAut.mul_apply, MulAut.mul_apply,
      signAut_apply_of_mem_avoiding (GX.letter_inr_mem_avoiding_iff.2 hxy.symm),
      signAut_letter_self,
      GX.transvection_apply_of_mem_avoiding _ _ (GX.inr_of_mem_avoiding hxy.symm)]
  have hφ₁₂_xnot : φ₁₂ (GX.letter (.inr (x, !bx))) = (inr (FreeGroup.of x))⁻¹ * p := by
    rw [MulAut.mul_apply, MulAut.mul_apply, signAut_letter_not,
      signAut_apply_of_mem_avoiding (inv_mem (GX.inr_of_mem_avoiding hxy)),
      map_inv, GX.transvection_inr_of_self, mul_one, mul_inv_rev, inv_inv]
  have hφ₁₂_ynot : φ₁₂ (GX.letter (.inr (y, !by_))) = (inr (FreeGroup.of y))⁻¹ := by
    rw [MulAut.mul_apply, MulAut.mul_apply,
      signAut_apply_of_mem_avoiding (GX.letter_inr_mem_avoiding_iff.2 hxy.symm),
      signAut_letter_not,
      GX.transvection_apply_of_mem_avoiding _ _ (inv_mem (GX.inr_of_mem_avoiding hxy.symm))]
  have hstep : φ₁₂ (p * GX.letter (.inr (x, bx)) * u * GX.letter (.inr (y, by_)) * v *
      GX.letter (.inr (x, !bx)) * w₀ * GX.letter (.inr (y, !by_)) * z) =
      inr (FreeGroup.of x) * u * inr (FreeGroup.of y) * v * (inr (FreeGroup.of x))⁻¹ *
        (p * w₀) * (inr (FreeGroup.of y))⁻¹ * z := by
    simp only [map_mul, hφ₁₂_xbx, hφ₁₂_yby, hφ₁₂_xnot, hφ₁₂_ynot,
      hφ₁₂_fix _ hp.1 hp.2, hφ₁₂_fix _ hu.1 hu.2, hφ₁₂_fix _ hv.1 hv.2,
      hφ₁₂_fix _ hw₀.1 hw₀.2, hφ₁₂_fix _ hz.1 hz.2, mul_assoc, mul_inv_cancel_left]
  refine ⟨φ₃ * φ₁₂, mul_mem hφ₃ (mul_mem (mul_mem (GX.transvection_mem_elementaryAut _ _ _)
    (signAut_mem_elementaryAut _ _)) (signAut_mem_elementaryAut _ _)), fun a hax hay => ?_, ?_⟩
  · rw [MulAut.mul_apply, hφ₁₂_fix a hax hay, hφ₃_fix a (Subgroup.mem_inf.2 ⟨hax, hay⟩)]
  · rw [MulAut.mul_apply, hstep, hφ₃_eq, commWord_def]

private theorem step_alt {w : GX G X} (hw : IsStrictlyQuadratic {w}) {x y : X} {bx by_ : Bool}
    {P U V W Z : List (G ⊕ X × Bool)} (hxy : x ≠ y)
    (hl : GX.reducedWord w = P ++ [.inr (x, bx)] ++ U ++ [.inr (y, by_)] ++ V ++
      [.inr (x, !bx)] ++ W ++ [.inr (y, !by_)] ++ Z) :
    ∃ f ∈ GX.elementaryAut G X, ∃ R' : GX G X,
      IsStrictlyQuadratic {R'} ∧ occVars R' ⊆ occVars w ∧
      x ∈ occVars w ∧ y ∈ occVars w ∧ x ∉ occVars R' ∧ y ∉ occVars R' ∧
      (∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f a = a) ∧
      f w = commWord (x, y) * R' := by
  obtain ⟨hx2, hxk⟩ := countVar_reducedWord_eq_two_of_mem (x := x) (b := bx) hw (by simp [hl])
  obtain ⟨hy2, hyk⟩ := countVar_reducedWord_eq_two_of_mem (x := y) (b := by_) hw (by simp [hl])
  have hx0 : GX.countVar x P = 0 ∧ GX.countVar x U = 0 ∧ GX.countVar x V = 0 ∧
      GX.countVar x W = 0 ∧ GX.countVar x Z = 0 := by simp [hl, hxy.symm] at hx2; omega
  have hy0 : GX.countVar y P = 0 ∧ GX.countVar y U = 0 ∧ GX.countVar y V = 0 ∧
      GX.countVar y W = 0 ∧ GX.countVar y Z = 0 := by simp [hl, hxy] at hy2; omega
  have hav {S : List (G ⊕ X × Bool)} (hsx : GX.countVar x S = 0) (hsy : GX.countVar y S = 0) :
      (S.map GX.letter).prod ∈ GX.avoiding x ∧ (S.map GX.letter).prod ∈ GX.avoiding y :=
    ⟨GX.prod_map_letter_mem_avoiding hsx, GX.prod_map_letter_mem_avoiding hsy⟩
  obtain ⟨f, hf_mem, hf_fix, hf_eq⟩ := exists_aut_signed_handle (bx := bx) (by_ := by_) hxy
    (hav hx0.1 hy0.1) (hav hx0.2.1 hy0.2.1) (hav hx0.2.2.1 hy0.2.2.1)
    (hav hx0.2.2.2.1 hy0.2.2.2.1) (hav hx0.2.2.2.2 hy0.2.2.2.2)
  set L := P ++ W ++ V ++ U ++ Z
  have hLx : GX.countVar x L = 0 := by
    simp [L, hx0.1, hx0.2.1, hx0.2.2.1, hx0.2.2.2.1, hx0.2.2.2.2]
  have hLy : GX.countVar y L = 0 := by
    simp [L, hy0.1, hy0.2.1, hy0.2.2.1, hy0.2.2.2.1, hy0.2.2.2.2]
  have hrem := isStrictlyQuadratic_and_occVars_prod {x, y} hw (L := L)
    (fun v hv => by
      rcases Finset.mem_insert.1 hv with rfl | hv'
      · exact hLx
      · rw [Finset.mem_singleton.1 hv']; exact hLy)
    fun v hv => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      simp [occurrences_eq_countVar_reducedWord, hl, L, Ne.symm hv.1, Ne.symm hv.2]
      omega
  have hw_eq : w = (P.map GX.letter).prod * GX.letter (.inr (x, bx)) * (U.map GX.letter).prod *
      GX.letter (.inr (y, by_)) * (V.map GX.letter).prod * GX.letter (.inr (x, !bx)) *
      (W.map GX.letter).prod * GX.letter (.inr (y, !by_)) * (Z.map GX.letter).prod := by
    simpa [mul_assoc] using eq_prod_of_reducedWord_eq hl
  refine ⟨f, hf_mem, (L.map GX.letter).prod, hrem.1, hrem.2.trans Finset.sdiff_subset,
    hxk, hyk, fun h => (Finset.mem_sdiff.1 (hrem.2 h)).2 (Finset.mem_insert_self _ _),
    fun h => (Finset.mem_sdiff.1 (hrem.2 h)).2
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
    fun a ha => hf_fix a (ha x hxk) (ha y hyk), ?_⟩
  rw [hw_eq, hf_eq]
  simp [L, mul_assoc]

private theorem step_conj {w : GX G X} (hw : IsStrictlyQuadratic {w}) {z : X} {b : Bool} {c : G}
    {P Q : List (G ⊕ X × Bool)}
    (hl : GX.reducedWord w = P ++ [.inr (z, b)] ++ [.inl c] ++ [.inr (z, !b)] ++ Q) :
    ∃ f ∈ GX.elementaryAut G X, ∃ R' : GX G X,
      IsStrictlyQuadratic {R'} ∧ occVars R' ⊆ occVars w ∧
      z ∈ occVars w ∧ z ∉ occVars R' ∧
      (∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f a = a) ∧
      f w = conjWord (z, c) * R' := by
  obtain ⟨hz2, hzk⟩ := countVar_reducedWord_eq_two_of_mem (x := z) (b := b) hw (by simp [hl])
  have hPQ : GX.countVar z P = 0 ∧ GX.countVar z Q = 0 := by simp [hl] at hz2; omega
  set p := (P.map GX.letter).prod
  set q := (Q.map GX.letter).prod
  have hp : p ∈ GX.avoiding z := GX.prod_map_letter_mem_avoiding hPQ.1
  have hq : q ∈ GX.avoiding z := GX.prod_map_letter_mem_avoiding hPQ.2
  have hw_eq : w = p * GX.letter (.inr (z, b)) * inl c * GX.letter (.inr (z, !b)) * q := by
    simpa [p, q, mul_assoc] using eq_prod_of_reducedWord_eq hl
  let f := GX.transvection z 1 p (one_mem _) hp * signAut z (!b)
  have hf_mem : f ∈ GX.elementaryAut G X :=
    mul_mem (GX.transvection_mem_elementaryAut _ _ _) (signAut_mem_elementaryAut _ _)
  set L := P ++ Q
  have hLz : GX.countVar z L = 0 := by simp [L, hPQ.1, hPQ.2]
  have hrem := isStrictlyQuadratic_and_occVars_prod {z} hw (L := L)
    (fun v hv => by rw [Finset.mem_singleton.1 hv]; exact hLz)
    fun v hv => by
      simp only [Finset.mem_singleton] at hv
      simp [occurrences_eq_countVar_reducedWord, hl, L, Ne.symm hv]
  refine ⟨f, hf_mem, (L.map GX.letter).prod, hrem.1, hrem.2.trans Finset.sdiff_subset,
    hzk, fun h => (Finset.mem_sdiff.1 (hrem.2 h)).2 (Finset.mem_singleton_self z),
    fun a ha => ?_, ?_⟩
  · simp [f, signAut_apply_of_mem_avoiding (ha z hzk), ha z hzk]
  · have hb_eq : signAut (G := G) z (!b) (GX.letter (.inr (z, b))) = (inr (FreeGroup.of z))⁻¹ := by
      simpa using signAut_letter_not (G := G) z (!b)
    have hLprod : (L.map GX.letter).prod = p * q := by simp [L, p, q]
    rw [hLprod, hw_eq]
    simp [f, conjWord_def, hb_eq, signAut_letter_self, signAut_apply_of_mem_avoiding,
      hp, hq, GX.inl_mem_avoiding, mul_assoc]

private def IsAtomicReduction (w : GX G X) (f : MulAut (GX G X)) (P : AtomicForm G X) : Prop :=
  f w = P.toWord ∧ P.vars.Nodup ∧ (∀ v ∈ P.vars, v ∈ occVars w) ∧
    ∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f a = a

private theorem atomic_step_sq {w R' : GX G X} {f₁ f₂ : MulAut (GX G X)} {x : X}
    {P : AtomicForm G X}
    (hf₁ : f₁ ∈ GX.elementaryAut G X) (hf₂ : f₂ ∈ GX.elementaryAut G X)
    (hR_sub : occVars R' ⊆ occVars w) (hxw : x ∈ occVars w) (hxR : x ∉ occVars R')
    (hf₁_fix : ∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f₁ a = a)
    (hf₁_eq : f₁ w = sqWord x * R')
    (hred : IsAtomicReduction R' f₂ P) :
    ∃ f ∈ GX.elementaryAut G X,
      IsAtomicReduction w f ⟨P.comms, x :: P.squares, P.conjs, P.const⟩ := by
  obtain ⟨hf₂_eq, hnd, hsub, hf₂_fix⟩ := hred
  have hx_not : x ∉ P.vars := fun hm => hxR (hsub x hm)
  obtain ⟨hC, hSq, hCj⟩ := P.commsProd_squaresProd_conjsProd_mem_avoiding hx_not
  let φ := GX.transvection x P.commsProd P.commsProd⁻¹ hC (inv_mem hC)
  have hperm : (⟨P.comms, x :: P.squares, P.conjs, P.const⟩ : AtomicForm G X).vars.Perm
      (x :: P.vars) := by
    simp [AtomicForm.vars_def, List.append_assoc]
  have hnd' : (⟨P.comms, x :: P.squares, P.conjs, P.const⟩ : AtomicForm G X).vars.Nodup :=
    hperm.nodup_iff.2 (List.nodup_cons.2 ⟨hx_not, hnd⟩)
  refine ⟨φ * f₂ * f₁, mul_mem (mul_mem (GX.transvection_mem_elementaryAut _ _ _) hf₂) hf₁,
    ?_, hnd', fun v hv => ?_, fun a ha => ?_⟩
  · have hf₂_sq : f₂ (sqWord x) = sqWord x :=
      hf₂_fix _ fun v hv => sqWord_mem_avoiding (ne_of_mem_of_not_mem hv hxR).symm
    rw [MulAut.mul_apply, MulAut.mul_apply, hf₁_eq, map_mul, hf₂_sq, hf₂_eq, AtomicForm.toWord_def,
      AtomicForm.toWord_def]
    simp only [AtomicForm.commsProd_cons_squares, AtomicForm.squaresProd_cons,
      AtomicForm.conjsProd_cons_squares, map_mul, sqWord_def, φ,
      GX.transvection_inr_of_self, GX.transvection_apply_of_mem_avoiding, hC, hSq, hCj,
      GX.inl_mem_avoiding, pow_two, mul_assoc]
    have hmk : (⟨P.comms, P.squares, P.conjs, P.const⟩ : AtomicForm G X) = P := rfl
    simp only [hmk, inv_mul_cancel_left]
  · rcases List.mem_cons.1 (hperm.subset hv) with rfl | hv'
    · exact hxw
    · exact hR_sub (hsub v hv')
  · simp [φ, hf₁_fix a ha, hf₂_fix a fun v hv => ha v (hR_sub hv), ha x hxw]

private theorem atomic_step_comm {w R' : GX G X} {f₁ f₂ : MulAut (GX G X)} {x y : X}
    {P : AtomicForm G X}
    (hf₁ : f₁ ∈ GX.elementaryAut G X) (hf₂ : f₂ ∈ GX.elementaryAut G X)
    (hR_sub : occVars R' ⊆ occVars w) (hxy : x ≠ y)
    (hxw : x ∈ occVars w) (hyw : y ∈ occVars w) (hxR : x ∉ occVars R') (hyR : y ∉ occVars R')
    (hf₁_fix : ∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f₁ a = a)
    (hf₁_eq : f₁ w = commWord (x, y) * R')
    (hred : IsAtomicReduction R' f₂ P) :
    ∃ f ∈ GX.elementaryAut G X,
      IsAtomicReduction w f ⟨(x, y) :: P.comms, P.squares, P.conjs, P.const⟩ := by
  obtain ⟨hf₂_eq, hnd, hsub, hf₂_fix⟩ := hred
  have hx_not : x ∉ P.vars := fun hm => hxR (hsub x hm)
  have hy_not : y ∉ P.vars := fun hm => hyR (hsub y hm)
  have hperm : (⟨(x, y) :: P.comms, P.squares, P.conjs, P.const⟩ : AtomicForm G X).vars.Perm
      (x :: y :: P.vars) := by
    simp [AtomicForm.vars_def, List.append_assoc]
  refine ⟨f₂ * f₁, mul_mem hf₂ hf₁, ?_,
    hperm.nodup_iff.2 (List.nodup_cons.2 ⟨by simp [hxy, hx_not], List.nodup_cons.2 ⟨hy_not, hnd⟩⟩),
    fun v hv => ?_, fun a ha => by simp [hf₁_fix a ha, hf₂_fix a fun v hv => ha v (hR_sub hv)]⟩
  · have hf₂_c : f₂ (commWord (x, y)) = commWord (x, y) :=
      hf₂_fix _ fun v hv => commWord_mem_avoiding
        (ne_of_mem_of_not_mem hv hxR).symm (ne_of_mem_of_not_mem hv hyR).symm
    rw [MulAut.mul_apply, hf₁_eq, map_mul, hf₂_c, hf₂_eq, AtomicForm.toWord_def,
      AtomicForm.toWord_def]
    simp only [AtomicForm.commsProd_cons, AtomicForm.squaresProd_cons_comms,
      AtomicForm.conjsProd_cons_comms, mul_assoc]
  · rcases List.mem_cons.1 (hperm.subset hv) with rfl | hv'
    · exact hxw
    · rcases List.mem_cons.1 hv' with rfl | hv''
      · exact hyw
      · exact hR_sub (hsub v hv'')

private theorem atomic_step_conj {w R' : GX G X} {f₁ f₂ : MulAut (GX G X)} {z : X} {c : G}
    {P : AtomicForm G X}
    (hf₁ : f₁ ∈ GX.elementaryAut G X) (hf₂ : f₂ ∈ GX.elementaryAut G X)
    (hR_sub : occVars R' ⊆ occVars w) (hzw : z ∈ occVars w) (hzR : z ∉ occVars R')
    (hf₁_fix : ∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f₁ a = a)
    (hf₁_eq : f₁ w = conjWord (z, c) * R')
    (hred : IsAtomicReduction R' f₂ P) :
    ∃ f ∈ GX.elementaryAut G X,
      IsAtomicReduction w f ⟨P.comms, P.squares, (z, c) :: P.conjs, P.const⟩ := by
  obtain ⟨hf₂_eq, hnd, hsub, hf₂_fix⟩ := hred
  have hz_not : z ∉ P.vars := fun hm => hzR (hsub z hm)
  obtain ⟨hC, hSq, hCj⟩ := P.commsProd_squaresProd_conjsProd_mem_avoiding hz_not
  let φ := GX.transvection z 1 (P.commsProd * P.squaresProd)⁻¹
    (one_mem _) (inv_mem (mul_mem hC hSq))
  have hperm : (⟨P.comms, P.squares, (z, c) :: P.conjs, P.const⟩ : AtomicForm G X).vars.Perm
      (z :: P.vars) := by
    simpa [AtomicForm.vars_def, List.append_assoc] using
      List.perm_middle (l₁ := (P.comms.flatMap fun p => [p.1, p.2]) ++ P.squares) (a := z)
        (l₂ := P.conjs.map Prod.fst)
  refine ⟨φ * f₂ * f₁, mul_mem (mul_mem (GX.transvection_mem_elementaryAut _ _ _) hf₂) hf₁,
    ?_, hperm.nodup_iff.2 (List.nodup_cons.2 ⟨hz_not, hnd⟩), fun v hv => ?_, fun a ha => ?_⟩
  · have hf₂_cj : f₂ (conjWord (z, c)) = conjWord (z, c) :=
      hf₂_fix _ fun v hv => conjWord_mem_avoiding (ne_of_mem_of_not_mem hv hzR).symm
    rw [MulAut.mul_apply, MulAut.mul_apply, hf₁_eq, map_mul, hf₂_cj, hf₂_eq, AtomicForm.toWord_def,
      AtomicForm.toWord_def]
    simp only [AtomicForm.commsProd_cons_conjs, AtomicForm.squaresProd_cons_conjs,
      AtomicForm.conjsProd_cons, map_mul, conjWord_def, map_inv, φ,
      GX.transvection_inr_of_self, GX.transvection_apply_of_mem_avoiding, hC, hSq, hCj,
      GX.inl_mem_avoiding, one_mul, mul_inv_rev, inv_inv, mul_assoc]
    have hmk : (⟨P.comms, P.squares, P.conjs, P.const⟩ : AtomicForm G X) = P := rfl
    simp only [hmk, inv_mul_cancel_left]
  · rcases List.mem_cons.1 (hperm.subset hv) with rfl | hv'
    · exact hzw
    · exact hR_sub (hsub v hv')
  · simp [φ, hf₁_fix a ha, hf₂_fix a fun v hv => ha v (hR_sub hv), ha z hzw]

private theorem exists_atomic_aux (n : ℕ) : ∀ w : GX G X, (occVars w).card = n →
    IsStrictlyQuadratic {w} →
    ∃ f ∈ GX.elementaryAut G X, ∃ P : AtomicForm G X, IsAtomicReduction w f P := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro w hcard hw
    by_cases hemp : occVars w = ∅
    · obtain ⟨d, rfl⟩ := occVars_eq_empty_iff.1 hemp
      exact ⟨1, one_mem _, ⟨[], [], [], d⟩,
        by simp [AtomicForm.toWord_def],
        by simp [AtomicForm.vars_def], by simp [AtomicForm.vars_def], fun _ _ => rfl⟩
    · obtain ⟨x₀, hx₀⟩ := Finset.ne_empty_iff_nonempty.1 hemp
      have hne : ∃ x, GX.countVar x (GX.reducedWord w) ≠ 0 :=
        ⟨x₀, occurrences_eq_countVar_reducedWord x₀ w ▸ mem_occVars_iff.1 hx₀⟩
      have hq : ∀ v, GX.countVar v (GX.reducedWord w) ≠ 1 := fun v => by
        rcases isStrictlyQuadratic_singleton.1 hw v with h | h <;>
          rw [occurrences_eq_countVar_reducedWord] at h <;> omega
      have step_ih {R' : GX G X} (hR_sq : IsStrictlyQuadratic {R'})
          (hR_sub : occVars R' ⊆ occVars w) {v : X} (hvw : v ∈ occVars w) (hvR : v ∉ occVars R') :
          ∃ f₂ ∈ GX.elementaryAut G X, ∃ P : AtomicForm G X, IsAtomicReduction R' f₂ P :=
        ih _ (hcard ▸ Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.2 ⟨hR_sub, fun h => hvR (h ▸ hvw)⟩)) R' rfl hR_sq
      rcases GX.exists_crossCap_or_handle_or_boundary_with_prefix hq hne with
        ⟨x, b, P, M, Q, hl⟩ | ⟨x, y, bx, by_, P, U, V, W, Z, hxy, hl⟩ | ⟨z, b, L, P, Q, hl⟩
      · obtain ⟨f₁, hf₁, R', hR_sq, hR_sub, hxw, hxR, hf₁_fix, hf₁_eq⟩ :=
          step_sameSign hw (by simpa [List.append_assoc] using hl)
        obtain ⟨f₂, hf₂, Q, hred⟩ := step_ih hR_sq hR_sub hxw hxR
        obtain ⟨f, hf, hred'⟩ := atomic_step_sq hf₁ hf₂ hR_sub hxw hxR hf₁_fix hf₁_eq hred
        exact ⟨f, hf, _, hred'⟩
      · obtain ⟨f₁, hf₁, R', hR_sq, hR_sub, hxw, hyw, hxR, hyR, hf₁_fix, hf₁_eq⟩ :=
          step_alt hw hxy (by simpa [List.append_assoc] using hl)
        obtain ⟨f₂, hf₂, Q, hred⟩ := step_ih hR_sq hR_sub hxw hxR
        obtain ⟨f, hf, hred'⟩ :=
          atomic_step_comm hf₁ hf₂ hR_sub hxy hxw hyw hxR hyR hf₁_fix hf₁_eq hred
        exact ⟨f, hf, _, hred'⟩
      · have hsub : GX.IsReduced (.inr (z, b) :: (L.map .inl ++ [.inr (z, !b)])) :=
          (GX.isReduced_reducedWord w).infix ⟨P, Q, by simp [hl, List.append_assoc]⟩
        rcases L with _ | ⟨c, _ | ⟨c', L'⟩⟩
        · simp at hsub
        · obtain ⟨f₁, hf₁, R', hR_sq, hR_sub, hzw, hzR, hf₁_fix, hf₁_eq⟩ :=
            step_conj hw (c := c) (by simpa [List.append_assoc] using hl)
          obtain ⟨f₂, hf₂, Q, hred⟩ := step_ih hR_sq hR_sub hzw hzR
          obtain ⟨f, hf, hred'⟩ := atomic_step_conj hf₁ hf₂ hR_sub hzw hzR hf₁_fix hf₁_eq hred
          exact ⟨f, hf, _, hred'⟩
        · simp at hsub

end Reduction

/-! ### Main theorems -/

section Main

variable {G X : Type*} [Group G]

/-- Every strictly quadratic word `w ∈ G[X]` is carried by an elementary `G`-automorphism
`f ∈ GX.elementaryAut G X` (fixing every word in variables disjoint from those occurring in `w`)
and conjugation by an element `u ∈ G[X]` either to a coefficient `inl c` (`c ∈ G`) or to the left
side `S.toWord` of a standard quadratic equation `S : Standard G X` whose variables `S.vars` all
occur in `w` ([IFT], §2.7, Lemma 1; [VAR-I], §1, Lemma 6). -/
theorem exists_standardForm {w : GX G X} (hw : IsStrictlyQuadratic {w}) :
    ∃ f ∈ GX.elementaryAut G X, ∃ u : GX G X,
      (∀ a, (∀ x, occurrences x w ≠ 0 → occurrences x a = 0) → f a = a) ∧
      ((∃ c : G, u * f w * u⁻¹ = inl c) ∨
        ∃ S : Standard G X, u * f w * u⁻¹ = S.toWord ∧
          S.vars ⊆ {x | occurrences x w ≠ 0}) := by
  classical
  obtain ⟨f₁, hf₁, P, hf₁_eq, hnd, hsub, hf₁_fix⟩ :=
    exists_atomic_aux (occVars w).card w rfl hw
  obtain ⟨f₂, hf₂, u, hf₂_fix, hstd⟩ := P.exists_standardForm hnd
  refine ⟨f₂ * f₁, mul_mem hf₂ hf₁, u, fun a ha => ?_, ?_⟩
  · have ha' : ∀ v ∈ occVars w, a ∈ GX.avoiding v := fun v hv =>
      mem_avoiding_iff_occurrences_eq_zero.2 (ha v (mem_occVars_iff.1 hv))
    rw [MulAut.mul_apply, hf₁_fix a ha',
      hf₂_fix a fun v hv => ha v (mem_occVars_iff.1 (hsub v hv))]
  · rw [MulAut.mul_apply, hf₁_eq]
    exact hstd.imp_right fun ⟨S, hS, hSv⟩ =>
      ⟨S, hS, fun v hv => mem_occVars_iff.1 (hsub v (hSv hv))⟩

end Main

/-! ### Exclusivity of the two branches -/

section Exclusivity

variable {G X Y Z : Type*} [Group G]

/-- The coefficient and standard-equation branches of `exists_standardForm` are mutually exclusive,
even across isomorphisms and homomorphisms fixing `inl c` followed by arbitrary conjugation in
their targets: if `w` is carried by an isomorphism `φ₁ : G[X] ≃* G[Y]` fixing `inl c` and an
arbitrary conjugation in `G[Y]` to `inl c`, then no homomorphism `φ₂ : G[X] →* G[Z]` fixing
`inl c` followed by an arbitrary conjugation in `G[Z]` can carry `w` to `S.toWord` for any
`S : Standard G Z`. -/
theorem not_exists_standard_of_conj_mulEquiv_eq_inl
    {F : Type*} [FunLike F (GX G X) (GX G Z)] [MonoidHomClass F (GX G X) (GX G Z)]
    {w : GX G X} {u₁ : GX G Y} {c : G}
    (φ₁ : GX G X ≃* GX G Y) (hφ₁ : φ₁ (inl c) = inl c) (hw₁ : u₁ * φ₁ w * u₁⁻¹ = inl c)
    (φ₂ : F) (hφ₂ : φ₂ (inl c) = inl c) (u₂ : GX G Z) :
    ¬∃ S : Standard G Z, u₂ * φ₂ w * u₂⁻¹ = S.toWord := by
  rintro ⟨S, hS⟩
  have h1 : IsConj (inl c : GX G X) w := by
    have h : IsConj (φ₁ w) (inl c) := isConj_iff.2 ⟨u₁, hw₁⟩
    simpa [φ₁.symm_apply_eq.2 hφ₁.symm] using (φ₁.symm.toMonoidHom.map_isConj h).symm
  obtain ⟨v, hv⟩ := isConj_iff.1 h1.symm
  have hw_eq : w = v⁻¹ * inl c * v := by
    simp [← hv, mul_assoc]
  exact S.toWord_ne_conj_map_conj_inl (f := (φ₂ : GX G X →* GX G Z)) hφ₂ u₂ v
    (hS.symm.trans (by rw [hw_eq]; rfl))

end Exclusivity

/-! ### Examples -/

section Examples

variable {G H X Y : Type*} [Group G] [Group H]

/-- There is a bijection between the solution set of the Klein-bottle equation `x₀ x₁ x₀ x₁⁻¹ = 1`
and that of the standard non-orientable equation `x₀² x₁² = 1` sending `(a₀, a₁)` to
`(a₀ a₁, a₁⁻¹)`. -/
example (ι : G →* H) :
    ∃ e : V ι {(inr (.of 0) * inr (.of 1) * inr (.of 0) * (inr (.of 1))⁻¹ : GX G (Fin 2))} ≃
        V ι {(inr (.of 0) ^ 2 * inr (.of 1) ^ 2 : GX G (Fin 2))},
      ∀ v, (e v : Fin 2 → H) 0 = (v : Fin 2 → H) 0 * (v : Fin 2 → H) 1 ∧
        (e v : Fin 2 → H) 1 = ((v : Fin 2 → H) 1)⁻¹ :=
  ⟨equivVOfConjMulEquiv ι
      (GX.invertVar G 1 * GX.transvection 0 1 (inr (.of 1))⁻¹ (one_mem _) (by simp) :
        MulAut (GX G (Fin 2)))
      (GX.apply_inl_of_mem_elementaryAut
        (mul_mem (GX.invertVar_mem_elementaryAut 1) (GX.transvection_mem_elementaryAut 0 _ _)))
      (u := 1) (by simp [pow_two, mul_assoc]),
    fun v => by
      have h01 : (0 : Fin 2) ≠ 1 := by decide
      simp [MulAut.mul_def, MulEquiv.symm_trans_apply, GX.transvection_symm,
        GX.invertVar_inr_of_of_ne h01]⟩

/-- Over `F(a, b)` in one variable, no homomorphism fixing `a` followed by conjugation can carry
`z⁻¹ a z` to a standard quadratic word (compare `isStrictlyQuadratic_inv_mul_inl_mul_self` for
strict quadraticity, and `V_singleton_inv_mul_inl_mul_eq_empty`, which shows the solution set is
empty when the image of `a` in `H` is nontrivial). -/
example {F : Type*} [FunLike F (GX (FreeGroup (Fin 2)) Unit) (GX (FreeGroup (Fin 2)) Y)]
    [MonoidHomClass F (GX (FreeGroup (Fin 2)) Unit) (GX (FreeGroup (Fin 2)) Y)]
    (φ : F) (hφ : φ (inl (.of 0)) = inl (.of 0)) (u : GX (FreeGroup (Fin 2)) Y) :
    ¬∃ S : Standard (FreeGroup (Fin 2)) Y,
      u * φ ((inr (.of ()))⁻¹ * inl (.of 0) * inr (.of ())) * u⁻¹ = S.toWord :=
  not_exists_standard_of_conj_mulEquiv_eq_inl (1 : MulAut _) rfl
    (u₁ := inr (.of ())) (c := .of 0) (by simp [mul_assoc]) φ hφ u

/-- The identity word `1`—whose solution set `V ι {1}` is `Set.univ` even when the variable set is
nonempty—takes the coefficient branch `c = 1` exclusively: no `1`-preserving map and conjugation can
carry `1` to a standard quadratic word. -/
example {α F : Type*} [One α] [FunLike F α (GX G Y)] [OneHomClass F α (GX G Y)]
    (S : Standard G Y) (φ : F) (u : GX G Y) :
    S.toWord ≠ u * φ 1 * u⁻¹ := by
  simpa using S.toWord_ne_conj_inl 1 1

end Examples

end TauCeti.GroupAlgGeom.Quadratic
