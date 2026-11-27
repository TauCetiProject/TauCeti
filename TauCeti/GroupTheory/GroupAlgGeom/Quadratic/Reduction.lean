/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Automorphism
import TauCeti.Algebra.Group.Action.List
import TauCeti.Data.Finset.Card
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
coefficient (`Standard.toWord_ne_conj_inl`,
`Standard.toWord_ne_conj_map_of_isConj_of_map_eq_inl`). Moreover, variables outside `S.vars` are
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
    (hoff : ∀ v ∉ extracted, GX.countVar v L = GX.occurrences v w) :
    IsStrictlyQuadratic {(L.map GX.letter).prod} ∧
      GX.occVars (L.map GX.letter).prod ⊆ GX.occVars w \ extracted := by
  refine ⟨isStrictlyQuadratic_singleton.2 fun v => ?_, fun v hv => ?_⟩
  · obtain ⟨k, hk⟩ := GX.exists_countVar_eq_add_two_mul v L
    rw [← GX.occurrences_eq_countVar_reducedWord] at hk
    have hwv := isStrictlyQuadratic_singleton.1 hw v
    by_cases hve : v ∈ extracted
    · have := hzero v hve; omega
    · have := hoff v hve; omega
  · rw [Finset.mem_sdiff, GX.mem_occVars_iff]
    have hle := GX.countVar_reducedWord_le v L
    rw [← GX.occurrences_eq_countVar_reducedWord] at hle
    have hv0 := GX.mem_occVars_iff.1 hv
    refine ⟨?_, fun hve => ?_⟩
    · by_cases hve' : v ∈ extracted
      · have := hzero v hve'; omega
      · have := hoff v hve'; omega
    · have := hzero v hve; omega

private theorem forall_countVar_eq_zero_of_eq_interleaved {x : X}
    {frags : List (List (G ⊕ X × Bool))} {w : GX G X} (hw : IsStrictlyQuadratic {w})
    (hcount : GX.countVar x (GX.reducedWord w) = (frags.map (GX.countVar x)).sum + 2) :
    x ∈ GX.occVars w ∧ ∀ F ∈ frags, GX.countVar x F = 0 := by
  have h2 := isStrictlyQuadratic_singleton.1 hw x
  rw [GX.occurrences_eq_countVar_reducedWord] at h2
  have hc : GX.countVar x (GX.reducedWord w) = 2 := by omega
  have hsum : (frags.map (GX.countVar x)).sum = 0 := by omega
  refine ⟨GX.mem_occVars_iff.2 (by rw [GX.occurrences_eq_countVar_reducedWord, hc]; decide),
    fun F hF => List.sum_eq_zero_iff_forall_eq_nat.1 hsum _ (List.mem_map_of_mem hF)⟩

variable [DecidableEq X]

private def signAut (x : X) (b : Bool) : MulAut (GX G X) :=
  if b then 1 else GX.invertVar G x

private theorem signAut_mem_elementaryAut (x : X) (b : Bool) :
    signAut (G := G) x b ∈ GX.elementaryAut G X := by
  cases b <;> simp [signAut]

private theorem signAut_letter_self (x : X) (b : Bool) :
    signAut (G := G) x b (GX.letter (.inr (x, b))) = inr (FreeGroup.of x) := by
  cases b <;> simp [signAut]

private theorem signAut_not_letter (x : X) (b : Bool) :
    signAut (G := G) x (!b) (GX.letter (.inr (x, b))) = (inr (FreeGroup.of x))⁻¹ := by
  cases b <;> simp [signAut]

private theorem signAut_apply_of_mem_avoiding {x : X} {b : Bool} {a : GX G X}
    (ha : a ∈ GX.avoiding x) : signAut x b a = a := by
  cases b <;> simp [signAut, ha]

private theorem step_sameSign {w : GX G X} (hw : IsStrictlyQuadratic {w}) {x : X} {b : Bool}
    {P M Q : List (G ⊕ X × Bool)}
    (hl : GX.reducedWord w = P ++ [.inr (x, b)] ++ M ++ [.inr (x, b)] ++ Q) :
    ∃ f ∈ GX.elementaryAut G X, ∃ R' : GX G X,
      IsStrictlyQuadratic {R'} ∧ GX.occVars R' ⊆ GX.occVars w \ {x} ∧ x ∈ GX.occVars w ∧
      (∀ a, (∀ v ∈ GX.occVars w, a ∈ GX.avoiding v) → f a = a) ∧
      f w = sqWord x * R' := by
  obtain ⟨hxk, hPMQ⟩ := forall_countVar_eq_zero_of_eq_interleaved (x := x) (frags := [P, M, Q]) hw
    (by simp [hl]; omega)
  set p := (P.map GX.letter).prod
  set m := (M.map GX.letter).prod
  set q := (Q.map GX.letter).prod
  have hp : p ∈ GX.avoiding x := GX.prod_map_letter_mem_avoiding (hPMQ P (by simp))
  have hm : m ∈ GX.avoiding x := GX.prod_map_letter_mem_avoiding (hPMQ M (by simp))
  have hq : q ∈ GX.avoiding x := GX.prod_map_letter_mem_avoiding (hPMQ Q (by simp))
  have hw_eq : w = p * GX.letter (.inr (x, b)) * m * GX.letter (.inr (x, b)) * q := by
    simpa [hl, p, m, q, mul_assoc] using (GX.prod_reducedWord w).symm
  let f₁ := signAut (G := G) x b
  let f₂ := GX.transvection x p⁻¹ 1 (inv_mem hp) (one_mem _)
  let f₃ := GX.transvection x 1 (m * p⁻¹)⁻¹ (one_mem _) (inv_mem (mul_mem hm (inv_mem hp)))
  have hf_mem : f₃ * f₂ * f₁ ∈ GX.elementaryAut G X :=
    mul_mem (mul_mem (GX.transvection_mem_elementaryAut _ _ _)
      (GX.transvection_mem_elementaryAut _ _ _)) (signAut_mem_elementaryAut x b)
  set L := [P, GX.invRev M, Q].flatten
  have hLx : GX.countVar x L = 0 := by
    rw [GX.countVar_flatten]
    refine List.sum_eq_zero fun n hn => ?_
    simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hn
    obtain ⟨F, rfl | rfl | rfl, rfl⟩ := hn
    · exact hPMQ _ (by simp)
    · simpa [GX.countVar_invRev] using hPMQ _ (by simp)
    · exact hPMQ _ (by simp)
  have hrem := isStrictlyQuadratic_and_occVars_prod {x} hw (L := L)
    (fun v hv => by rw [Finset.mem_singleton.1 hv]; exact hLx)
    fun v hv => by
      simp only [Finset.mem_singleton] at hv
      simp [GX.occurrences_eq_countVar_reducedWord, hl, L, Ne.symm hv, GX.countVar_invRev]
  have hstep₁ : f₁ w = p * inr (FreeGroup.of x) * m * inr (FreeGroup.of x) * q := by
    rw [hw_eq]
    simp [f₁, signAut_letter_self, signAut_apply_of_mem_avoiding, hp, hm, hq]
  have hstep₂ : f₂ (f₁ w) = inr (FreeGroup.of x) * (m * p⁻¹) * inr (FreeGroup.of x) * q := by
    rw [hstep₁]
    simp [f₂, hp, hm, hq, mul_assoc]
  have hstep₃ : f₃ (f₂ (f₁ w)) = sqWord x * (p * m⁻¹ * q) := by
    rw [hstep₂, GX.transvection_crossCap (mul_mem hm (inv_mem hp)) hq]
    simp [sqWord_def, mul_assoc]
  refine ⟨f₃ * f₂ * f₁, hf_mem, (L.map GX.letter).prod, hrem.1, hrem.2, hxk,
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
    simp [φ₁₂, signAut_letter_self, signAut_apply_of_mem_avoiding, GX.inr_of_mem_avoiding hxy]
  have hφ₁₂_yby : φ₁₂ (GX.letter (.inr (y, by_))) = inr (FreeGroup.of y) := by
    simp [φ₁₂, signAut_letter_self, signAut_apply_of_mem_avoiding, GX.inr_of_mem_avoiding hxy.symm,
      hxy.symm]
  have hφ₁₂_xnot : φ₁₂ (GX.letter (.inr (x, !bx))) = (inr (FreeGroup.of x))⁻¹ * p := by
    simp [hφ₁₂_xbx]
  have hφ₁₂_ynot : φ₁₂ (GX.letter (.inr (y, !by_))) = (inr (FreeGroup.of y))⁻¹ := by
    simp [hφ₁₂_yby]
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
      IsStrictlyQuadratic {R'} ∧ GX.occVars R' ⊆ GX.occVars w \ {x, y} ∧
      x ∈ GX.occVars w ∧ y ∈ GX.occVars w ∧
      (∀ a, (∀ v ∈ GX.occVars w, a ∈ GX.avoiding v) → f a = a) ∧
      f w = commWord (x, y) * R' := by
  obtain ⟨hxk, hx0⟩ := forall_countVar_eq_zero_of_eq_interleaved (x := x) (frags := [P, U, V, W, Z])
    hw (by simp [hl, hxy.symm]; omega)
  obtain ⟨hyk, hy0⟩ := forall_countVar_eq_zero_of_eq_interleaved (x := y) (frags := [P, U, V, W, Z])
    hw (by simp [hl, hxy]; omega)
  have hav {S : List (G ⊕ X × Bool)} (hS : S ∈ [P, U, V, W, Z]) :
      (S.map GX.letter).prod ∈ GX.avoiding x ∧ (S.map GX.letter).prod ∈ GX.avoiding y :=
    ⟨GX.prod_map_letter_mem_avoiding (hx0 S hS), GX.prod_map_letter_mem_avoiding (hy0 S hS)⟩
  obtain ⟨f, hf_mem, hf_fix, hf_eq⟩ := exists_aut_signed_handle (bx := bx) (by_ := by_) hxy
    (hav (S := P) (by simp)) (hav (S := U) (by simp)) (hav (S := V) (by simp))
    (hav (S := W) (by simp)) (hav (S := Z) (by simp))
  set L := [P, W, V, U, Z].flatten
  have hLx : GX.countVar x L = 0 := by
    rw [GX.countVar_flatten]
    refine List.sum_eq_zero fun n hn => ?_
    obtain ⟨F, hF, rfl⟩ := List.mem_map.1 hn
    exact hx0 F (by simp at hF ⊢; tauto)
  have hLy : GX.countVar y L = 0 := by
    rw [GX.countVar_flatten]
    refine List.sum_eq_zero fun n hn => ?_
    obtain ⟨F, hF, rfl⟩ := List.mem_map.1 hn
    exact hy0 F (by simp at hF ⊢; tauto)
  have hrem := isStrictlyQuadratic_and_occVars_prod {x, y} hw (L := L)
    (fun v hv => by
      rcases Finset.mem_insert.1 hv with rfl | hv'
      · exact hLx
      · rw [Finset.mem_singleton.1 hv']; exact hLy)
    fun v hv => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      simp [GX.occurrences_eq_countVar_reducedWord, hl, L, Ne.symm hv.1, Ne.symm hv.2]
      omega
  have hw_eq : w = (P.map GX.letter).prod * GX.letter (.inr (x, bx)) * (U.map GX.letter).prod *
      GX.letter (.inr (y, by_)) * (V.map GX.letter).prod * GX.letter (.inr (x, !bx)) *
      (W.map GX.letter).prod * GX.letter (.inr (y, !by_)) * (Z.map GX.letter).prod := by
    simpa [hl, mul_assoc] using (GX.prod_reducedWord w).symm
  refine ⟨f, hf_mem, (L.map GX.letter).prod, hrem.1, hrem.2, hxk, hyk,
    fun a ha => hf_fix a (ha x hxk) (ha y hyk), ?_⟩
  rw [hw_eq, hf_eq]
  simp [L, mul_assoc]

private theorem step_conj {w : GX G X} (hw : IsStrictlyQuadratic {w}) {z : X} {b : Bool} {c : G}
    {P Q : List (G ⊕ X × Bool)}
    (hl : GX.reducedWord w = P ++ [.inr (z, b)] ++ [.inl c] ++ [.inr (z, !b)] ++ Q) :
    ∃ f ∈ GX.elementaryAut G X, ∃ R' : GX G X,
      IsStrictlyQuadratic {R'} ∧ GX.occVars R' ⊆ GX.occVars w \ {z} ∧
      z ∈ GX.occVars w ∧
      (∀ a, (∀ v ∈ GX.occVars w, a ∈ GX.avoiding v) → f a = a) ∧
      f w = conjWord (z, c) * R' := by
  obtain ⟨hzk, hPQ⟩ := forall_countVar_eq_zero_of_eq_interleaved (x := z) (frags := [P, Q]) hw
    (by simp [hl]; omega)
  set p := (P.map GX.letter).prod
  set q := (Q.map GX.letter).prod
  have hp : p ∈ GX.avoiding z := GX.prod_map_letter_mem_avoiding (hPQ P (by simp))
  have hq : q ∈ GX.avoiding z := GX.prod_map_letter_mem_avoiding (hPQ Q (by simp))
  have hw_eq : w = p * GX.letter (.inr (z, b)) * inl c * GX.letter (.inr (z, !b)) * q := by
    simpa [hl, p, q, mul_assoc] using (GX.prod_reducedWord w).symm
  let f := GX.transvection z 1 p (one_mem _) hp * signAut z (!b)
  have hf_mem : f ∈ GX.elementaryAut G X :=
    mul_mem (GX.transvection_mem_elementaryAut _ _ _) (signAut_mem_elementaryAut _ _)
  set L := [P, Q].flatten
  have hLz : GX.countVar z L = 0 := by
    rw [GX.countVar_flatten]
    refine List.sum_eq_zero fun n hn => ?_
    obtain ⟨F, hF, rfl⟩ := List.mem_map.1 hn
    exact hPQ F hF
  have hrem := isStrictlyQuadratic_and_occVars_prod {z} hw (L := L)
    (fun v hv => by rw [Finset.mem_singleton.1 hv]; exact hLz)
    fun v hv => by
      simp only [Finset.mem_singleton] at hv
      simp [GX.occurrences_eq_countVar_reducedWord, hl, L, Ne.symm hv]
  refine ⟨f, hf_mem, (L.map GX.letter).prod, hrem.1, hrem.2, hzk, fun a ha => ?_, ?_⟩
  · simp [f, signAut_apply_of_mem_avoiding (ha z hzk), ha z hzk]
  · have hLprod : (L.map GX.letter).prod = p * q := by simp [L, p, q]
    rw [hLprod, hw_eq]
    simp [f, conjWord_def, signAut_not_letter, signAut_apply_of_mem_avoiding,
      hp, hq, GX.inl_mem_avoiding, mul_assoc]

private def IsAtomicReduction (w : GX G X) (f : MulAut (GX G X)) (P : AtomicForm G X) : Prop :=
  f w = P.toWord ∧ P.vars.Nodup ∧ (∀ v ∈ P.vars, v ∈ GX.occVars w) ∧
    ∀ a, (∀ v ∈ GX.occVars w, a ∈ GX.avoiding v) → f a = a

private theorem atomic_step_aux {w R' : GX G X} {f₁ f₂ φ : MulAut (GX G X)}
    (xs : List X) (atom : GX G X) {P Q : AtomicForm G X}
    (hf₁ : f₁ ∈ GX.elementaryAut G X) (hf₂ : f₂ ∈ GX.elementaryAut G X)
    (hφ : φ ∈ GX.elementaryAut G X)
    (hR_sub : GX.occVars R' ⊆ GX.occVars w \ xs.toFinset)
    (hxs_w : ∀ v ∈ xs, v ∈ GX.occVars w) (hxs_nd : xs.Nodup)
    (hatom : ∀ v, v ∉ xs → atom ∈ GX.avoiding v)
    (hf₁_fix : ∀ a, (∀ v ∈ GX.occVars w, a ∈ GX.avoiding v) → f₁ a = a)
    (hf₁_eq : f₁ w = atom * R')
    (hred : IsAtomicReduction R' f₂ P)
    (hperm : Q.vars.Perm (xs ++ P.vars))
    (hφ_fix : ∀ a, (∀ v ∈ xs, a ∈ GX.avoiding v) → φ a = a)
    (hφ_eq : φ (atom * P.toWord) = Q.toWord) :
    ∃ f ∈ GX.elementaryAut G X, IsAtomicReduction w f Q := by
  have hxsR : ∀ v ∈ xs, v ∉ GX.occVars R' :=
    fun v hv h => (Finset.mem_sdiff.1 (hR_sub h)).2 (List.mem_toFinset.2 hv)
  have hR_sub' : GX.occVars R' ⊆ GX.occVars w := hR_sub.trans Finset.sdiff_subset
  obtain ⟨hf₂_eq, hnd, hsub, hf₂_fix⟩ := hred
  have hdisj : xs.Disjoint P.vars := fun v hv hvp => hxsR v hv (hsub v hvp)
  have hf₂_atom : f₂ atom = atom :=
    hf₂_fix _ fun v hv => hatom v fun hvs => hxsR v hvs hv
  refine ⟨φ * f₂ * f₁, mul_mem (mul_mem hφ hf₂) hf₁, ?_,
    hperm.nodup_iff.2 (hxs_nd.append hnd hdisj), fun v hv => ?_, fun a ha => ?_⟩
  · rw [MulAut.mul_apply, MulAut.mul_apply, hf₁_eq, map_mul, hf₂_atom, hf₂_eq, hφ_eq]
  · rcases List.mem_append.1 (hperm.subset hv) with hv' | hv'
    · exact hxs_w v hv'
    · exact hR_sub' (hsub v hv')
  · simp [hf₁_fix a ha, hf₂_fix a fun v hv => ha v (hR_sub' hv),
      hφ_fix a fun v hv => ha v (hxs_w v hv)]

private theorem atomic_step_sq {w R' : GX G X} {f₁ f₂ : MulAut (GX G X)} {x : X}
    {P : AtomicForm G X}
    (hf₁ : f₁ ∈ GX.elementaryAut G X) (hf₂ : f₂ ∈ GX.elementaryAut G X)
    (hR_sub : GX.occVars R' ⊆ GX.occVars w \ {x}) (hxw : x ∈ GX.occVars w)
    (hf₁_fix : ∀ a, (∀ v ∈ GX.occVars w, a ∈ GX.avoiding v) → f₁ a = a)
    (hf₁_eq : f₁ w = sqWord x * R')
    (hred : IsAtomicReduction R' f₂ P) :
    ∃ f ∈ GX.elementaryAut G X,
      IsAtomicReduction w f { P with squares := x :: P.squares } := by
  have hx_not : x ∉ P.vars := fun hm =>
    (Finset.mem_sdiff.1 (hR_sub (hred.2.2.1 x hm))).2 (Finset.mem_singleton_self x)
  simp only [AtomicForm.vars_def, List.mem_append, not_or] at hx_not
  have hC := AtomicForm.commsProd_mem_avoiding hx_not.1.1
  have hSq := AtomicForm.squaresProd_mem_avoiding hx_not.1.2
  have hCj := AtomicForm.conjsProd_mem_avoiding hx_not.2
  let φ := GX.transvection x P.commsProd P.commsProd⁻¹ hC (inv_mem hC)
  have hφ_sq : φ (sqWord x) = P.commsProd * sqWord x * P.commsProd⁻¹ := by
    simp [φ, sqWord_def, pow_two, GX.transvection_inr_of_self, mul_assoc]
  have hφ_tail : φ P.toWord = P.toWord := by
    simp [φ, AtomicForm.toWord_def, hC, hSq, hCj]
  refine atomic_step_aux (φ := φ) [x] (sqWord x) hf₁ hf₂ (GX.transvection_mem_elementaryAut _ _ _)
    (by simpa using hR_sub) (by simpa using hxw) (List.nodup_singleton x)
    (fun v hv => sqWord_mem_avoiding (by simpa [eq_comm] using hv)) hf₁_fix hf₁_eq hred
    (by simp [AtomicForm.vars_def, List.append_assoc])
    (fun a ha => GX.transvection_apply_of_mem_avoiding _ _ (ha x (List.mem_singleton_self x))) ?_
  rw [map_mul, hφ_sq, hφ_tail, AtomicForm.toWord_def, AtomicForm.toWord_def]
  simp [AtomicForm.commsProd_def, AtomicForm.conjsProd_def, mul_assoc]

private theorem atomic_step_comm {w R' : GX G X} {f₁ f₂ : MulAut (GX G X)} {x y : X}
    {P : AtomicForm G X}
    (hf₁ : f₁ ∈ GX.elementaryAut G X) (hf₂ : f₂ ∈ GX.elementaryAut G X)
    (hR_sub : GX.occVars R' ⊆ GX.occVars w \ {x, y}) (hxy : x ≠ y)
    (hxw : x ∈ GX.occVars w) (hyw : y ∈ GX.occVars w)
    (hf₁_fix : ∀ a, (∀ v ∈ GX.occVars w, a ∈ GX.avoiding v) → f₁ a = a)
    (hf₁_eq : f₁ w = commWord (x, y) * R')
    (hred : IsAtomicReduction R' f₂ P) :
    ∃ f ∈ GX.elementaryAut G X,
      IsAtomicReduction w f { P with comms := (x, y) :: P.comms } := by
  refine atomic_step_aux (φ := 1) [x, y] (commWord (x, y)) hf₁ hf₂ (one_mem _)
    (by simpa [List.toFinset_cons] using hR_sub)
    (fun v hv => by
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hxw
      · exact (List.mem_singleton.1 hv) ▸ hyw)
    (by simp [hxy])
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
      exact commWord_mem_avoiding (Ne.symm hv.1) (Ne.symm hv.2))
    hf₁_fix hf₁_eq hred (by simp [AtomicForm.vars_def, List.append_assoc])
    (fun a _ => rfl) ?_
  simp [AtomicForm.toWord_def, AtomicForm.squaresProd_def, AtomicForm.conjsProd_def, mul_assoc]

private theorem atomic_step_conj {w R' : GX G X} {f₁ f₂ : MulAut (GX G X)} {z : X} {c : G}
    {P : AtomicForm G X}
    (hf₁ : f₁ ∈ GX.elementaryAut G X) (hf₂ : f₂ ∈ GX.elementaryAut G X)
    (hR_sub : GX.occVars R' ⊆ GX.occVars w \ {z}) (hzw : z ∈ GX.occVars w)
    (hf₁_fix : ∀ a, (∀ v ∈ GX.occVars w, a ∈ GX.avoiding v) → f₁ a = a)
    (hf₁_eq : f₁ w = conjWord (z, c) * R')
    (hred : IsAtomicReduction R' f₂ P) :
    ∃ f ∈ GX.elementaryAut G X,
      IsAtomicReduction w f { P with conjs := (z, c) :: P.conjs } := by
  have hz_not : z ∉ P.vars := fun hm =>
    (Finset.mem_sdiff.1 (hR_sub (hred.2.2.1 z hm))).2 (Finset.mem_singleton_self z)
  simp only [AtomicForm.vars_def, List.mem_append, not_or] at hz_not
  have hC := AtomicForm.commsProd_mem_avoiding hz_not.1.1
  have hSq := AtomicForm.squaresProd_mem_avoiding hz_not.1.2
  have hCj := AtomicForm.conjsProd_mem_avoiding hz_not.2
  let φ := GX.transvection z 1 (P.commsProd * P.squaresProd)⁻¹
    (one_mem _) (inv_mem (mul_mem hC hSq))
  have hφ_conj : φ (conjWord (z, c)) =
      (P.commsProd * P.squaresProd) * conjWord (z, c) * (P.commsProd * P.squaresProd)⁻¹ := by
    simp [φ, conjWord_def, GX.transvection_inr_of_self, mul_assoc]
  have hφ_tail : φ P.toWord = P.toWord := by
    simp [φ, AtomicForm.toWord_def, hC, hSq, hCj]
  have hperm : ({ P with conjs := (z, c) :: P.conjs } : AtomicForm G X).vars.Perm
      ([z] ++ P.vars) := by
    simpa [AtomicForm.vars_def, List.append_assoc] using
      List.perm_middle (l₁ := (P.comms.flatMap fun p => [p.1, p.2]) ++ P.squares) (a := z)
        (l₂ := P.conjs.map Prod.fst)
  refine atomic_step_aux (φ := φ) [z] (conjWord (z, c)) hf₁ hf₂
    (GX.transvection_mem_elementaryAut _ _ _)
    (by simpa using hR_sub) (by simpa using hzw) (List.nodup_singleton z)
    (fun v hv => conjWord_mem_avoiding (by simpa [eq_comm] using hv)) hf₁_fix hf₁_eq hred hperm
    (fun a ha => GX.transvection_apply_of_mem_avoiding _ _ (ha z (List.mem_singleton_self z))) ?_
  rw [map_mul, hφ_conj, hφ_tail, AtomicForm.toWord_def, AtomicForm.toWord_def]
  simp [AtomicForm.commsProd_def, AtomicForm.squaresProd_def, mul_assoc]

private theorem exists_atomic_aux (n : ℕ) : ∀ w : GX G X, (GX.occVars w).card = n →
    IsStrictlyQuadratic {w} →
    ∃ f ∈ GX.elementaryAut G X, ∃ P : AtomicForm G X, IsAtomicReduction w f P := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro w hcard hw
    by_cases hemp : GX.occVars w = ∅
    · obtain ⟨d, rfl⟩ := GX.occVars_eq_empty_iff.1 hemp
      exact ⟨1, one_mem _, ⟨[], [], [], d⟩,
        by simp [AtomicForm.toWord_def],
        by simp [AtomicForm.vars_def], by simp [AtomicForm.vars_def], fun _ _ => rfl⟩
    · obtain ⟨x₀, hx₀⟩ := Finset.ne_empty_iff_nonempty.1 hemp
      have hne : ∃ x, GX.countVar x (GX.reducedWord w) ≠ 0 :=
        ⟨x₀, GX.occurrences_eq_countVar_reducedWord x₀ w ▸ GX.mem_occVars_iff.1 hx₀⟩
      have hq : ∀ v, GX.countVar v (GX.reducedWord w) ≠ 1 := fun v => by
        rcases isStrictlyQuadratic_singleton.1 hw v with h | h <;>
          rw [GX.occurrences_eq_countVar_reducedWord] at h <;> omega
      rcases GX.exists_crossCap_or_handle_or_boundary_with_prefix hq hne with
        ⟨x, b, P, M, Q, hl⟩ | ⟨x, y, bx, by_, P, U, V, W, Z, hxy, hl⟩ | ⟨z, b, L, P, Q, hl⟩
      · obtain ⟨f₁, hf₁, R', hR_sq, hR_sub, hxw, hf₁_fix, hf₁_eq⟩ :=
          step_sameSign hw (by simpa [List.append_assoc] using hl)
        obtain ⟨f₂, hf₂, Q, hred⟩ := ih _ (hcard ▸ Finset.card_lt_card_of_subset_sdiff hR_sub hxw
          (Finset.mem_singleton_self x)) R' rfl hR_sq
        obtain ⟨f, hf, hred'⟩ := atomic_step_sq hf₁ hf₂ hR_sub hxw hf₁_fix hf₁_eq hred
        exact ⟨f, hf, _, hred'⟩
      · obtain ⟨f₁, hf₁, R', hR_sq, hR_sub, hxw, hyw, hf₁_fix, hf₁_eq⟩ :=
          step_alt hw hxy (by simpa [List.append_assoc] using hl)
        obtain ⟨f₂, hf₂, Q, hred⟩ := ih _ (hcard ▸ Finset.card_lt_card_of_subset_sdiff hR_sub hxw
          (by simp)) R' rfl hR_sq
        obtain ⟨f, hf, hred'⟩ :=
          atomic_step_comm hf₁ hf₂ hR_sub hxy hxw hyw hf₁_fix hf₁_eq hred
        exact ⟨f, hf, _, hred'⟩
      · have hsub : GX.IsReduced (.inr (z, b) :: (L.map .inl ++ [.inr (z, !b)])) :=
          (GX.isReduced_reducedWord w).infix ⟨P, Q, by simp [hl, List.append_assoc]⟩
        obtain ⟨c, rfl⟩ := hsub.exists_eq_singleton_of_inr_map_inl
        obtain ⟨f₁, hf₁, R', hR_sq, hR_sub, hzw, hf₁_fix, hf₁_eq⟩ :=
          step_conj hw (c := c) (by simpa [List.append_assoc] using hl)
        obtain ⟨f₂, hf₂, Q, hred⟩ := ih _ (hcard ▸ Finset.card_lt_card_of_subset_sdiff hR_sub hzw
          (Finset.mem_singleton_self z)) R' rfl hR_sq
        obtain ⟨f, hf, hred'⟩ := atomic_step_conj hf₁ hf₂ hR_sub hzw hf₁_fix hf₁_eq hred
        exact ⟨f, hf, _, hred'⟩

end Reduction

/-! ### Main theorems -/

section Main

variable {G X : Type*} [Group G]

/-- Every strictly quadratic word `w ∈ G[X]` is carried by an elementary `G`-automorphism
`f ∈ GX.elementaryAut G X` (fixing every word in variables disjoint from those occurring in `w`)
and conjugation by an element `u ∈ G[X]` either to a coefficient `inl c` (`c ∈ G`) or to the left
side `S.toWord` of a standard quadratic equation `S : Standard G X` whose variables `S.vars` all
occur in `w` ([IFT], §2.7, Lemma 1; [VAR-I], §1, Lemma 6). Combining with
`GX.mem_elementaryAut_iff_exists_list`, `MulAut.smul_def`, `List.prod_smul`,
`List.inv_prod_smul`, `GX.transvection_inr_of`, and `GX.invertVar_inr_of` expresses `f` and `f⁻¹`
on generators as finite folds of elementary transvections and variable inversions. -/
theorem exists_standardForm {w : GX G X} (hw : IsStrictlyQuadratic {w}) :
    ∃ f ∈ GX.elementaryAut G X, ∃ u : GX G X,
      (∀ a, (∀ x, GX.occurrences x w ≠ 0 → GX.occurrences x a = 0) → f a = a) ∧
      ((∃ c : G, u * f w * u⁻¹ = inl c) ∨
        ∃ S : Standard G X, u * f w * u⁻¹ = S.toWord ∧
          S.vars ⊆ {x | GX.occurrences x w ≠ 0}) := by
  classical
  obtain ⟨f₁, hf₁, P, hf₁_eq, hnd, hsub, hf₁_fix⟩ :=
    exists_atomic_aux (GX.occVars w).card w rfl hw
  obtain ⟨f₂, hf₂, u, hf₂_fix, hstd⟩ := P.exists_standardForm hnd
  refine ⟨f₂ * f₁, mul_mem hf₂ hf₁, u, fun a ha => ?_, ?_⟩
  · have ha' : ∀ v ∈ GX.occVars w, a ∈ GX.avoiding v := fun v hv =>
      GX.mem_avoiding_iff_occurrences_eq_zero.2 (ha v (GX.mem_occVars_iff.1 hv))
    rw [MulAut.mul_apply, hf₁_fix a ha',
      hf₂_fix a fun v hv => ha v (GX.mem_occVars_iff.1 (hsub v hv))]
  · rw [MulAut.mul_apply, hf₁_eq]
    exact hstd.imp_right fun ⟨S, hS, hSv⟩ =>
      ⟨S, hS, fun v hv => GX.mem_occVars_iff.1 (hsub v (hSv hv))⟩

end Main

/-! ### Examples -/

section Examples

variable {G H X Y : Type*} [Group G] [Group H]

/-- Combining `exists_standardForm` with `GX.mem_elementaryAut_iff_exists_list`,
`MulAut.smul_def`, `List.prod_smul`, and `List.inv_prod_smul` expresses the reducing elementary
automorphism and its inverse on any word as finite folds of elementary transvections and
variable inversions. -/
example [DecidableEq X] {w : GX G X} (hw : IsStrictlyQuadratic {w}) (a : GX G X) :
    ∃ (fs : List (MulAut (GX G X))) (u : GX G X),
      (∀ φ ∈ fs,
        (∃ (x : X) (a b : GX G X) (ha : a ∈ GX.avoiding x) (hb : b ∈ GX.avoiding x),
          φ = GX.transvection x a b ha hb) ∨
        ∃ x : X, φ = GX.invertVar G x) ∧
      ((∃ c : G, u * fs.prod w * u⁻¹ = inl c) ∨
        ∃ S : Standard G X, u * fs.prod w * u⁻¹ = S.toWord) ∧
      fs.prod a = fs.foldr (fun f y => f y) a ∧
      (fs.prod)⁻¹ a = fs.foldl (fun y f => f⁻¹ y) a := by
  obtain ⟨f, hf, u, -, hstd⟩ := exists_standardForm hw
  obtain ⟨fs, rfl, hfs⟩ := GX.mem_elementaryAut_iff_exists_list.1 hf
  exact ⟨fs, u, hfs, hstd.imp_right fun ⟨S, hS, _⟩ => ⟨S, hS⟩,
    by simpa only [MulAut.smul_def] using fs.prod_smul a,
    by simpa only [MulAut.smul_def] using fs.inv_prod_smul a⟩

/-- There is a bijection between the solution set of the Klein-bottle equation `x₀ x₁ x₀ x₁⁻¹ = 1`
and that of the standard non-orientable equation `x₀² x₁² = 1` sending `(a₀, a₁)` to
`(a₀ a₁, a₁⁻¹)`. -/
example (ι : G →* H) :
    ∃ e : V ι {(inr (.of 0) * inr (.of 1) * inr (.of 0) * (inr (.of 1))⁻¹ : GX G (Fin 2))} ≃
        V ι {(inr (.of 0) ^ 2 * inr (.of 1) ^ 2 : GX G (Fin 2))},
      ∀ v, (e v : Fin 2 → H) 0 = (v : Fin 2 → H) 0 * (v : Fin 2 → H) 1 ∧
        (e v : Fin 2 → H) 1 = ((v : Fin 2 → H) 1)⁻¹ :=
  ⟨equivVOfVImageEq ι
      (GX.invertVar G 1 * GX.transvection 0 1 (inr (.of 1))⁻¹ (one_mem _) (by simp) :
        MulAut (GX G (Fin 2)))
      (GX.apply_inl_of_mem_elementaryAut
        (mul_mem (GX.invertVar_mem_elementaryAut 1) (GX.transvection_mem_elementaryAut 0 _ _)))
      (by rw [Set.image_singleton]; congr 1; simp [pow_two, mul_assoc]),
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
  fun ⟨S, hS⟩ => S.toWord_ne_conj_map_of_isConj_of_map_eq_inl
    (isConj_iff.2 ⟨(inr (.of ()) : GX (FreeGroup (Fin 2)) Unit)⁻¹, by simp [mul_assoc]⟩)
    hφ u hS.symm

/-- The identity word `1`—whose solution set `V ι {1}` is `Set.univ` even when the variable set is
nonempty—takes the coefficient branch `c = 1` exclusively: no `1`-preserving map and conjugation can
carry `1` to a standard quadratic word. -/
example {α F : Type*} [One α] [FunLike F α (GX G Y)] [OneHomClass F α (GX G Y)]
    (S : Standard G Y) (φ : F) (u : GX G Y) :
    S.toWord ≠ u * φ 1 * u⁻¹ := by
  simpa using S.toWord_ne_conj_inl 1 1

end Examples

end TauCeti.GroupAlgGeom.Quadratic
