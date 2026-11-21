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
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.StandardForm

/-!
# Reduction of strictly quadratic words to standard form

A strictly quadratic word of `G[X]` is brought to a standard quadratic word, or to a coefficient,
by a product of elementary `G`-automorphisms of `G[X]` (`GX.elementaryAut`) followed by a
conjugation in `G[X]` (`exists_standardForm_fixing`, `exists_standardForm`). This is the corrected
form of Kharlampovich–Myasnikov [IFT, §2.7, Lemma 1] and [VAR-I, §1, Lemma 6], which omit the
coefficient branch: a coefficient `g ≠ 1` and its conjugates `z⁻¹ g z` are strictly quadratic
(`isStrictlyQuadratic_inl`, `isStrictlyQuadratic_inv_mul_inl_mul_self`), and no standard quadratic
word is conjugate to a coefficient (`Standard.toWord_ne_conj_inl`). Moreover, variables outside
`S.vars` are unconstrained (`Standard.mem_V_toWord_congr`).

Following Gallier–Xu [GaXu, Lemma 6.1], any reduced word in which every variable occurs zero or
two times contains either a same-sign pair `x^b M x^b` (cross-cap), an alternating pair
`x^bx U y^by V x^(!bx) W y^(!by)` (handle), or an innermost opposite-sign pair `z^b c z^(!b)`
enclosing a single nontrivial coefficient `c`. Repeatedly extracting these leaves a word in atomic
form (`AtomicForm`), which `AtomicForm.exists_standardForm_fixing` reduces to a coefficient or a
standard quadratic equation.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.exists_standardForm_fixing`,
  `TauCeti.GroupAlgGeom.Quadratic.exists_standardForm`: every strictly quadratic word in `G[X]` is
  carried by an elementary `G`-automorphism (fixing all words in disjoint variables) and a
  conjugation either to a coefficient `inl c` (`c ∈ G`) or to `S.toWord` for a standard quadratic
  equation `S : Standard G X` with `S.vars` contained in the occurring variables of the word.
* `TauCeti.GroupAlgGeom.Quadratic.not_exists_standard_of_conj_mulEquiv_eq_inl`: exclusivity of the
  coefficient and standard-equation branches under isomorphisms, homomorphisms, and conjugations.

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

variable {G X : Type*}

private def SameSignPattern (l : List (G ⊕ X × Bool)) : Prop :=
  ∃ x b P M Q, l = P ++ [.inr (x, b)] ++ M ++ [.inr (x, b)] ++ Q

private def AltPattern (l : List (G ⊕ X × Bool)) : Prop :=
  ∃ x y bx by_ P U V W Z, x ≠ y ∧
    l = P ++ [.inr (x, bx)] ++ U ++ [.inr (y, by_)] ++ V ++ [.inr (x, !bx)] ++ W ++
      [.inr (y, !by_)] ++ Z

private theorem countVar_middle_eq_zero {l P M Q : List (G ⊕ X × Bool)} {z : X} {b : Bool}
    (hns : ¬SameSignPattern l) (hna : ¬AltPattern l)
    (hq : ∀ v, GX.countVar v l = 0 ∨ GX.countVar v l = 2)
    (hl_eq : l = P ++ [.inr (z, b)] ++ M ++ [.inr (z, !b)] ++ Q)
    (hmin : ∀ z' b' P' M' Q',
      l = P' ++ [.inr (z', b')] ++ M' ++ [.inr (z', !b')] ++ Q' → M.length ≤ M'.length) :
    ∀ y, GX.countVar y M = 0 := by
  by_contra! hy_ex
  obtain ⟨y, hyM⟩ := hy_ex
  have hyz : y ≠ z := by
    rintro rfl
    have hz := hq y
    simp [hl_eq] at hz
    omega
  have hyl : GX.countVar y P + GX.countVar y M + GX.countVar y Q = 2 := by
    have hy := hq y
    simp only [hl_eq, GX.countVar_append, GX.countVar_cons_inr_of_ne hyz.symm,
      GX.countVar_nil] at hy ⊢
    omega
  rcases (by omega : GX.countVar y M = 2 ∨ GX.countVar y M = 1) with hy2 | hy1
  · obtain ⟨M₁, b₁, M₂, b₂, M₃, rfl, -⟩ := GX.exists_two_split_of_countVar_eq_two hy2
    have hl' : l = (P ++ [.inr (z, b)] ++ M₁) ++ [.inr (y, b₁)] ++ M₂ ++ [.inr (y, b₂)] ++
        (M₃ ++ [.inr (z, !b)] ++ Q) := by simp [hl_eq, List.append_assoc]
    have hb₂ : b₂ = !b₁ := by
      cases b₁ <;> cases b₂ <;> first | rfl | exact False.elim (hns ⟨y, _, _, _, _, hl'⟩)
    subst hb₂
    have hlen := hmin y b₁ _ M₂ _ hl'
    simp at hlen
    omega
  · obtain ⟨M₁, by₁, M₂, rfl, -⟩ := GX.exists_split_of_countVar_pos (x := y) (l := M) (by omega)
    rcases (by omega : 0 < GX.countVar y P ∨ 0 < GX.countVar y Q) with hyP | hyQ
    · obtain ⟨P₁, by₀, P₂, rfl, -⟩ := GX.exists_split_of_countVar_pos hyP
      have hl_y : l = P₁ ++ [.inr (y, by₀)] ++ (P₂ ++ [.inr (z, b)] ++ M₁) ++ [.inr (y, by₁)] ++
          (M₂ ++ [.inr (z, !b)] ++ Q) := by simp [hl_eq, List.append_assoc]
      have hby : by₁ = !by₀ := by
        cases by₀ <;> cases by₁ <;> first | rfl | exact False.elim (hns ⟨y, _, _, _, _, hl_y⟩)
      subst hby
      exact hna ⟨y, z, by₀, b, P₁, P₂, M₁, M₂, Q, hyz, by simp [hl_eq, List.append_assoc]⟩
    · obtain ⟨Q₁, by₂, Q₂, rfl, -⟩ := GX.exists_split_of_countVar_pos hyQ
      have hl_y : l = (P ++ [.inr (z, b)] ++ M₁) ++ [.inr (y, by₁)] ++
          (M₂ ++ [.inr (z, !b)] ++ Q₁) ++ [.inr (y, by₂)] ++ Q₂ := by
        simp [hl_eq, List.append_assoc]
      have hby : by₂ = !by₁ := by
        cases by₁ <;> cases by₂ <;> first | rfl | exact False.elim (hns ⟨y, _, _, _, _, hl_y⟩)
      subst hby
      exact hna ⟨z, y, b, by₁, P, M₁, M₂, Q₁, Q₂, hyz.symm, by simp [hl_eq, List.append_assoc]⟩

variable [Group G]

private theorem trichotomy_of_reduced {l : List (G ⊕ X × Bool)} (hl : GX.IsReduced l)
    (hq : ∀ v, GX.countVar v l = 0 ∨ GX.countVar v l = 2)
    (hex : ∃ x, GX.countVar x l = 2) :
    SameSignPattern l ∨ AltPattern l ∨
      ∃ z b c P Q, c ≠ 1 ∧ l = P ++ [.inr (z, b)] ++ [.inl c] ++ [.inr (z, !b)] ++ Q := by
  classical
  by_cases hns : SameSignPattern l
  · exact .inl hns
  by_cases hna : AltPattern l
  · exact .inr (.inl hna)
  refine .inr (.inr ?_)
  have hspan : ∃ n, ∃ z b P M Q,
      M.length = n ∧ l = P ++ [.inr (z, b)] ++ M ++ [.inr (z, !b)] ++ Q := by
    obtain ⟨x, hx⟩ := hex
    obtain ⟨P, b₁, M, b₂, Q, hl_eq, -⟩ := GX.exists_two_split_of_countVar_eq_two hx
    have hb₂ : b₂ = !b₁ := by
      cases b₁ <;> cases b₂ <;> first | rfl | exact False.elim (hns ⟨x, _, P, M, Q, hl_eq⟩)
    subst hb₂
    exact ⟨M.length, x, b₁, P, M, Q, rfl, hl_eq⟩
  obtain ⟨z, b, P, M, Q, hlen, hl_eq⟩ := Nat.find_spec hspan
  have hM0 : ∀ y, GX.countVar y M = 0 := countVar_middle_eq_zero hns hna hq hl_eq
    fun z' b' P' M' Q' hl' => by
      have := Nat.find_min' hspan ⟨z', b', P', M', Q', rfl, hl'⟩
      omega
  have h₁ : GX.IsReduced ([.inr (z, b)] ++ M ++ [.inr (z, !b)] ++ Q) :=
    (GX.isReduced_append.1 (by simpa [hl_eq, List.append_assoc] using hl)).2.1
  have h₂ : GX.IsReduced (.inr (z, b) :: (M ++ [.inr (z, !b)])) :=
    (GX.isReduced_append.1 (by simpa [List.append_assoc] using h₁)).1
  rcases M with _ | ⟨c | ⟨y, _⟩, _ | ⟨_ | ⟨y', _⟩, _⟩⟩
  · simp at h₂
  · exact ⟨z, b, c, P, Q, by simpa using (GX.isReduced_cons.1 (GX.isReduced_cons.1 h₂).2.2).1,
      hl_eq⟩
  · have hM_red := (GX.isReduced_cons.1 h₂).2.2
    simp at hM_red
  · have := hM0 y'; simp at this
  all_goals have := hM0 y; simp at this

private theorem isStrictlyQuadratic_and_occVars_prod {w : GX G X} (hw : IsStrictlyQuadratic {w})
    {L : List (G ⊕ X × Bool)}
    (hL : ∀ v, GX.countVar v L = 0 ∨ GX.countVar v L = occurrences v w) :
    IsStrictlyQuadratic {(L.map GX.letter).prod} ∧ occVars (L.map GX.letter).prod ⊆ occVars w := by
  refine ⟨isStrictlyQuadratic_singleton.2 fun v => ?_, fun v hv => ?_⟩
  · obtain ⟨k, hk⟩ := GX.exists_countVar_eq_add_two_mul v L
    rw [← occurrences_eq_countVar_reducedWord] at hk
    have hv := isStrictlyQuadratic_singleton.1 hw v
    have hvL := hL v
    omega
  · rw [mem_occVars_iff] at hv ⊢
    have hle := GX.countVar_reducedWord_le v L
    rw [← occurrences_eq_countVar_reducedWord] at hle
    rcases hL v with h0 | heq <;> omega

private theorem notMem_occVars_prod_of_countVar_eq_zero {x : X} {L : List (G ⊕ X × Bool)}
    (h : GX.countVar x L = 0) : x ∉ occVars (L.map GX.letter).prod := by
  rw [mem_occVars_iff, not_not, occurrences_eq_countVar_reducedWord]
  exact Nat.eq_zero_of_le_zero ((GX.countVar_reducedWord_le x L).trans_eq h)

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

private theorem letter_inr_mem_avoiding {x y : X} (hyx : y ≠ x) (b : Bool) :
    GX.letter (G := G) (.inr (y, b)) ∈ GX.avoiding x := by
  cases b <;> simp [hyx]

private def commWord (p : X × X) : GX G X :=
  ⁅(inr (FreeGroup.of p.1) : GX G X)⁻¹, (inr (FreeGroup.of p.2))⁻¹⁆

private def sqWord (x : X) : GX G X :=
  (inr (FreeGroup.of x) : GX G X) ^ 2

private def conjWord (p : X × G) : GX G X :=
  (inr (FreeGroup.of p.1) : GX G X)⁻¹ * inl p.2 * inr (FreeGroup.of p.1)

private theorem commWord_mem_avoiding {x y v : X} (hx : x ≠ v) (hy : y ≠ v) :
    commWord (G := G) (x, y) ∈ GX.avoiding v := by
  rw [commWord, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (inv_mem (GX.inr_of_mem_avoiding hx))
    (inv_mem (GX.inr_of_mem_avoiding hy))) (inv_mem (inv_mem (GX.inr_of_mem_avoiding hx))))
    (inv_mem (inv_mem (GX.inr_of_mem_avoiding hy)))

private theorem sqWord_mem_avoiding {x v : X} (hx : x ≠ v) :
    sqWord (G := G) x ∈ GX.avoiding v :=
  pow_mem (GX.inr_of_mem_avoiding hx) 2

private theorem conjWord_mem_avoiding {z v : X} {c : G} (hz : z ≠ v) :
    conjWord (z, c) ∈ GX.avoiding v :=
  mul_mem (mul_mem (inv_mem (GX.inr_of_mem_avoiding hz)) (GX.inl_mem_avoiding v c))
    (GX.inr_of_mem_avoiding hz)

private theorem step_sameSign {w : GX G X} (hw : IsStrictlyQuadratic {w}) {x : X} {b : Bool}
    {P M Q : List (G ⊕ X × Bool)}
    (hl : GX.reducedWord w = P ++ [.inr (x, b)] ++ M ++ [.inr (x, b)] ++ Q) :
    ∃ f ∈ GX.elementaryAut G X, ∃ R' : GX G X,
      IsStrictlyQuadratic {R'} ∧ occVars R' ⊆ occVars w ∧ x ∈ occVars w ∧ x ∉ occVars R' ∧
      (∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f a = a) ∧
      f w = sqWord x * R' := by
  have hx2 : GX.countVar x (GX.reducedWord w) = 2 := by
    have := isStrictlyQuadratic_singleton.1 hw x
    rw [occurrences_eq_countVar_reducedWord] at this
    simp [hl] at this ⊢; omega
  have hPMQ : GX.countVar x P = 0 ∧ GX.countVar x M = 0 ∧ GX.countVar x Q = 0 := by
    simp [hl] at hx2; omega
  set p := (P.map GX.letter).prod
  set m := (M.map GX.letter).prod
  set q := (Q.map GX.letter).prod
  have hp : p ∈ GX.avoiding x := GX.prod_map_letter_mem_avoiding hPMQ.1
  have hm : m ∈ GX.avoiding x := GX.prod_map_letter_mem_avoiding hPMQ.2.1
  have hq : q ∈ GX.avoiding x := GX.prod_map_letter_mem_avoiding hPMQ.2.2
  have hw_eq : w = p * GX.letter (.inr (x, b)) * m * GX.letter (.inr (x, b)) * q := by
    simpa [p, m, q, mul_assoc] using
      (GX.prod_reducedWord w).symm.trans (congrArg (fun l => (l.map GX.letter).prod) hl)
  let f := GX.transvection x p⁻¹ (p * m⁻¹) (inv_mem hp) (mul_mem hp (inv_mem hm)) * signAut x b
  have hf_mem : f ∈ GX.elementaryAut G X :=
    mul_mem (GX.transvection_mem_elementaryAut _ _ _) (signAut_mem_elementaryAut x b)
  have hxk : x ∈ occVars w :=
    mem_occVars_iff.2 (by rw [occurrences_eq_countVar_reducedWord, hx2]; decide)
  set L := P ++ GX.invRev M ++ Q
  have hrem := isStrictlyQuadratic_and_occVars_prod hw (L := L) fun v => by
    by_cases hvx : v = x
    · subst hvx; left; simp [L, hPMQ.1, hPMQ.2.1, hPMQ.2.2, GX.countVar_invRev]
    · right
      simp [occurrences_eq_countVar_reducedWord, hl, L, Ne.symm hvx, GX.countVar_invRev]
  have hxR : x ∉ occVars (L.map GX.letter).prod :=
    notMem_occVars_prod_of_countVar_eq_zero
      (by simp [L, hPMQ.1, hPMQ.2.1, hPMQ.2.2, GX.countVar_invRev])
  refine ⟨f, hf_mem, (L.map GX.letter).prod, hrem.1, hrem.2, hxk, hxR, fun a ha => ?_, ?_⟩
  · simp [f, signAut_apply_of_mem_avoiding (ha x hxk), ha x hxk]
  · have hLprod : (L.map GX.letter).prod = p * m⁻¹ * q := by
      simp [L, p, m, q, GX.prod_map_letter_invRev, mul_assoc]
    rw [hLprod, hw_eq]
    simp [f, sqWord, pow_two, signAut_letter_self, signAut_apply_of_mem_avoiding, hp, hm, hq,
      mul_assoc]

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
  have hstep : φ₁₂ (p * GX.letter (.inr (x, bx)) * u * GX.letter (.inr (y, by_)) * v *
      GX.letter (.inr (x, !bx)) * w₀ * GX.letter (.inr (y, !by_)) * z) =
      inr (FreeGroup.of x) * u * inr (FreeGroup.of y) * v * (inr (FreeGroup.of x))⁻¹ *
        (p * w₀) * (inr (FreeGroup.of y))⁻¹ * z := by
    simp only [φ₁₂, MulAut.mul_apply, map_mul, map_inv, signAut_letter_self, signAut_letter_not,
      signAut_apply_of_mem_avoiding, letter_inr_mem_avoiding hxy.symm,
      GX.inr_of_mem_avoiding hxy, GX.inr_of_mem_avoiding hxy.symm,
      hp.1, hp.2, hu.1, hu.2, hv.1, hv.2, hw₀.1, hw₀.2, hz.1, hz.2, GX.transvection_inr_of_self,
      GX.transvection_apply_of_mem_avoiding, mul_one, mul_inv_rev, inv_inv, mul_assoc,
      mul_inv_cancel_left]
  refine ⟨φ₃ * φ₁₂, mul_mem hφ₃ (mul_mem (mul_mem (GX.transvection_mem_elementaryAut _ _ _)
    (signAut_mem_elementaryAut _ _)) (signAut_mem_elementaryAut _ _)), fun a hax hay => ?_, ?_⟩
  · simp [φ₁₂, signAut_apply_of_mem_avoiding hax, signAut_apply_of_mem_avoiding hay, hax,
      hφ₃_fix a (Subgroup.mem_inf.2 ⟨hax, hay⟩)]
  · rw [MulAut.mul_apply, hstep, hφ₃_eq, commWord]

private theorem step_alt {w : GX G X} (hw : IsStrictlyQuadratic {w}) {x y : X} {bx by_ : Bool}
    {P U V W Z : List (G ⊕ X × Bool)} (hxy : x ≠ y)
    (hl : GX.reducedWord w = P ++ [.inr (x, bx)] ++ U ++ [.inr (y, by_)] ++ V ++
      [.inr (x, !bx)] ++ W ++ [.inr (y, !by_)] ++ Z) :
    ∃ f ∈ GX.elementaryAut G X, ∃ R' : GX G X,
      IsStrictlyQuadratic {R'} ∧ occVars R' ⊆ occVars w ∧
      x ∈ occVars w ∧ y ∈ occVars w ∧ x ∉ occVars R' ∧ y ∉ occVars R' ∧
      (∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f a = a) ∧
      f w = commWord (x, y) * R' := by
  have hx2 : GX.countVar x (GX.reducedWord w) = 2 := by
    have := isStrictlyQuadratic_singleton.1 hw x
    rw [occurrences_eq_countVar_reducedWord] at this; simp [hl, hxy.symm] at this ⊢; omega
  have hy2 : GX.countVar y (GX.reducedWord w) = 2 := by
    have := isStrictlyQuadratic_singleton.1 hw y
    rw [occurrences_eq_countVar_reducedWord] at this; simp [hl, hxy] at this ⊢; omega
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
  have hxk : x ∈ occVars w :=
    mem_occVars_iff.2 (by rw [occurrences_eq_countVar_reducedWord, hx2]; decide)
  have hyk : y ∈ occVars w :=
    mem_occVars_iff.2 (by rw [occurrences_eq_countVar_reducedWord, hy2]; decide)
  set L := P ++ W ++ V ++ U ++ Z
  have hrem := isStrictlyQuadratic_and_occVars_prod hw (L := L) fun v => by
    by_cases hvx : v = x
    · subst hvx; left; simp [L, hx0.1, hx0.2.1, hx0.2.2.1, hx0.2.2.2.1, hx0.2.2.2.2]
    · by_cases hvy : v = y
      · subst hvy; left; simp [L, hy0.1, hy0.2.1, hy0.2.2.1, hy0.2.2.2.1, hy0.2.2.2.2]
      · right; simp [occurrences_eq_countVar_reducedWord, hl, L, Ne.symm hvx, Ne.symm hvy]; omega
  have hxR : x ∉ occVars (L.map GX.letter).prod :=
    notMem_occVars_prod_of_countVar_eq_zero
      (by simp [L, hx0.1, hx0.2.1, hx0.2.2.1, hx0.2.2.2.1, hx0.2.2.2.2])
  have hyR : y ∉ occVars (L.map GX.letter).prod :=
    notMem_occVars_prod_of_countVar_eq_zero
      (by simp [L, hy0.1, hy0.2.1, hy0.2.2.1, hy0.2.2.2.1, hy0.2.2.2.2])
  have hw_eq : w = (P.map GX.letter).prod * GX.letter (.inr (x, bx)) * (U.map GX.letter).prod *
      GX.letter (.inr (y, by_)) * (V.map GX.letter).prod * GX.letter (.inr (x, !bx)) *
      (W.map GX.letter).prod * GX.letter (.inr (y, !by_)) * (Z.map GX.letter).prod := by
    simpa [mul_assoc] using
      (GX.prod_reducedWord w).symm.trans (congrArg (fun l => (l.map GX.letter).prod) hl)
  refine ⟨f, hf_mem, (L.map GX.letter).prod, hrem.1, hrem.2, hxk, hyk, hxR, hyR,
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
  have hz2 : GX.countVar z (GX.reducedWord w) = 2 := by
    have := isStrictlyQuadratic_singleton.1 hw z
    rw [occurrences_eq_countVar_reducedWord] at this; simp [hl] at this ⊢; omega
  have hPQ : GX.countVar z P = 0 ∧ GX.countVar z Q = 0 := by simp [hl] at hz2; omega
  set p := (P.map GX.letter).prod
  set q := (Q.map GX.letter).prod
  have hp : p ∈ GX.avoiding z := GX.prod_map_letter_mem_avoiding hPQ.1
  have hq : q ∈ GX.avoiding z := GX.prod_map_letter_mem_avoiding hPQ.2
  have hw_eq : w = p * GX.letter (.inr (z, b)) * inl c * GX.letter (.inr (z, !b)) * q := by
    simpa [p, q, mul_assoc] using
      (GX.prod_reducedWord w).symm.trans (congrArg (fun l => (l.map GX.letter).prod) hl)
  let f := GX.transvection z 1 p (one_mem _) hp * signAut z (!b)
  have hf_mem : f ∈ GX.elementaryAut G X :=
    mul_mem (GX.transvection_mem_elementaryAut _ _ _) (signAut_mem_elementaryAut _ _)
  have hzk : z ∈ occVars w :=
    mem_occVars_iff.2 (by rw [occurrences_eq_countVar_reducedWord, hz2]; decide)
  set L := P ++ Q
  have hrem := isStrictlyQuadratic_and_occVars_prod hw (L := L) fun v => by
    by_cases hvz : v = z
    · subst hvz; left; simp [L, hPQ.1, hPQ.2]
    · right; simp [occurrences_eq_countVar_reducedWord, hl, L, Ne.symm hvz]
  have hzR : z ∉ occVars (L.map GX.letter).prod :=
    notMem_occVars_prod_of_countVar_eq_zero (by simp [L, hPQ.1, hPQ.2])
  refine ⟨f, hf_mem, (L.map GX.letter).prod, hrem.1, hrem.2, hzk, hzR, fun a ha => ?_, ?_⟩
  · simp [f, signAut_apply_of_mem_avoiding (ha z hzk), ha z hzk]
  · have hb_eq : signAut (G := G) z (!b) (GX.letter (.inr (z, b))) = (inr (FreeGroup.of z))⁻¹ := by
      simpa using signAut_letter_not (G := G) z (!b)
    have hLprod : (L.map GX.letter).prod = p * q := by simp [L, p, q]
    rw [hLprod, hw_eq]
    simp [f, conjWord, hb_eq, signAut_letter_self, signAut_apply_of_mem_avoiding, hp, hq,
      GX.inl_mem_avoiding, mul_assoc]

private def IsAtomicReduction (w : GX G X) (f : MulAut (GX G X)) (P : AtomicForm G X) : Prop :=
  f w = P.toWord ∧ P.vars.Nodup ∧ (∀ v ∈ P.vars, v ∈ occVars w) ∧
    ∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f a = a

private theorem mem_avoiding_atomic_parts {v : X} {P : AtomicForm G X} (hv : v ∉ P.vars) :
    (P.comms.map fun p =>
        ⁅(inr (FreeGroup.of p.1) : GX G X)⁻¹, (inr (FreeGroup.of p.2) : GX G X)⁻¹⁆).prod ∈
      GX.avoiding v ∧
    (P.squares.map fun s => (inr (FreeGroup.of s) : GX G X) ^ 2).prod ∈ GX.avoiding v ∧
    (P.conjs.map fun p => (inr (FreeGroup.of p.1) : GX G X)⁻¹ * inl p.2 *
        inr (FreeGroup.of p.1)).prod ∈ GX.avoiding v := by
  simp only [AtomicForm.vars_def, List.mem_append, List.mem_flatMap, List.mem_map, not_or,
    not_exists, not_and] at hv
  refine ⟨(GX.avoiding v).list_prod_mem fun _ hr => ?_,
    (GX.avoiding v).list_prod_mem fun _ hr => ?_,
    (GX.avoiding v).list_prod_mem fun _ hr => ?_⟩
  · rcases List.mem_map.1 hr with ⟨⟨x, y⟩, hm, rfl⟩
    exact commWord_mem_avoiding (fun h => hv.1.1 ⟨x, y⟩ hm (by simp [h]))
      (fun h => hv.1.1 ⟨x, y⟩ hm (by simp [h]))
  · rcases List.mem_map.1 hr with ⟨s, hm, rfl⟩
    exact sqWord_mem_avoiding fun h => hv.1.2 (h ▸ hm)
  · rcases List.mem_map.1 hr with ⟨⟨z, c⟩, hm, rfl⟩
    exact conjWord_mem_avoiding fun h => hv.2 (z, c) hm h

private theorem transvection_conj_mem {x : X} (u : GX G X) (hu : u ∈ GX.avoiding x) :
    ∃ φ ∈ GX.elementaryAut G X,
      φ (inr (FreeGroup.of x)) = u * inr (FreeGroup.of x) * u⁻¹ ∧
      ∀ c ∈ GX.avoiding x, φ c = c :=
  ⟨GX.transvection x u u⁻¹ hu (inv_mem hu),
    GX.transvection_mem_elementaryAut x hu (inv_mem hu),
    GX.transvection_inr_of_self hu (inv_mem hu),
    fun _ hc => GX.transvection_apply_of_mem_avoiding hu (inv_mem hu) hc⟩

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
  obtain ⟨hC, hSq, hCj⟩ := mem_avoiding_atomic_parts (G := G) hx_not
  obtain ⟨φ, hφ_mem, hφ_self, hφ_av⟩ := transvection_conj_mem _ hC
  have hperm : (⟨P.comms, x :: P.squares, P.conjs, P.const⟩ : AtomicForm G X).vars.Perm
      (x :: P.vars) := by
    simp [AtomicForm.vars_def, List.append_assoc]
  have hnd' : (⟨P.comms, x :: P.squares, P.conjs, P.const⟩ : AtomicForm G X).vars.Nodup :=
    hperm.nodup_iff.2 (List.nodup_cons.2 ⟨hx_not, hnd⟩)
  refine ⟨φ * f₂ * f₁, mul_mem (mul_mem hφ_mem hf₂) hf₁, ?_, hnd', fun v hv => ?_, fun a ha => ?_⟩
  · have hf₂_sq : f₂ (sqWord x) = sqWord x :=
      hf₂_fix _ fun v hv => sqWord_mem_avoiding (ne_of_mem_of_not_mem hv hxR).symm
    rw [MulAut.mul_apply, MulAut.mul_apply, hf₁_eq, map_mul, hf₂_sq, hf₂_eq]
    simp only [map_mul, AtomicForm.toWord_def, List.map_cons, List.prod_cons, sqWord, map_pow]
    rw [hφ_self, hφ_av _ hC, hφ_av _ hSq, hφ_av _ hCj, hφ_av _ (GX.inl_mem_avoiding x P.const)]
    simp only [pow_two, mul_assoc, inv_mul_cancel_left]
  · rcases List.mem_cons.1 (hperm.subset hv) with rfl | hv'
    · exact hxw
    · exact hR_sub (hsub v hv')
  · simp [MulAut.mul_apply, hf₁_fix a ha, hf₂_fix a fun v hv => ha v (hR_sub hv),
      hφ_av a (ha x hxw)]

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
  · have hf₂_c : f₂ (commWord (x, y)) = commWord (x, y) := hf₂_fix _ fun v hv =>
      commWord_mem_avoiding (ne_of_mem_of_not_mem hv hxR).symm (ne_of_mem_of_not_mem hv hyR).symm
    rw [MulAut.mul_apply, hf₁_eq, map_mul, hf₂_c, hf₂_eq]
    simp [AtomicForm.toWord_def, commWord, mul_assoc]
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
  obtain ⟨hC, hSq, hCj⟩ := mem_avoiding_atomic_parts (G := G) hz_not
  let φ := GX.transvection z 1
    ((P.comms.map fun p =>
        ⁅(inr (FreeGroup.of p.1) : GX G X)⁻¹, (inr (FreeGroup.of p.2) : GX G X)⁻¹⁆).prod *
      (P.squares.map fun s => (inr (FreeGroup.of s) : GX G X) ^ 2).prod)⁻¹
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
    rw [MulAut.mul_apply, MulAut.mul_apply, hf₁_eq, map_mul, hf₂_cj, hf₂_eq]
    simp only [map_mul, AtomicForm.toWord_def, List.map_cons, List.prod_cons, conjWord, map_inv]
    dsimp only [φ]
    rw [GX.transvection_inr_of_self, GX.transvection_apply_of_mem_avoiding (hc := hC),
      GX.transvection_apply_of_mem_avoiding (hc := hSq),
      GX.transvection_apply_of_mem_avoiding (hc := hCj),
      GX.transvection_apply_of_mem_avoiding (hc := GX.inl_mem_avoiding z c),
      GX.transvection_apply_of_mem_avoiding (hc := GX.inl_mem_avoiding z P.const)]
    simp only [one_mul, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
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
      exact ⟨1, one_mem _, ⟨[], [], [], d⟩, by simp [AtomicForm.toWord_def],
        by simp [AtomicForm.vars_def], by simp [AtomicForm.vars_def], fun _ _ => rfl⟩
    · obtain ⟨x₀, hx₀⟩ := Finset.ne_empty_iff_nonempty.1 hemp
      have hx₀2 : GX.countVar x₀ (GX.reducedWord w) = 2 := by
        have h1 := mem_occVars_iff.1 hx₀
        have h2 := isStrictlyQuadratic_singleton.1 hw x₀
        rw [occurrences_eq_countVar_reducedWord] at h1 h2; omega
      have hq : ∀ v, GX.countVar v (GX.reducedWord w) = 0 ∨
          GX.countVar v (GX.reducedWord w) = 2 := fun v => by
        simpa [occurrences_eq_countVar_reducedWord] using isStrictlyQuadratic_singleton.1 hw v
      rcases trichotomy_of_reduced (GX.isReduced_reducedWord w) hq ⟨x₀, hx₀2⟩ with
        ⟨x, b, P, M, Q, hl⟩ | ⟨x, y, bx, by_, P, U, V, W, Z, hxy, hl⟩ |
        ⟨z, b, c, P, Q, _, hl⟩
      · obtain ⟨f₁, hf₁, R', hR_sq, hR_sub, hxw, hxR, hf₁_fix, hf₁_eq⟩ := step_sameSign hw hl
        have hlt : (occVars R').card < n := hcard ▸ Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.2 ⟨hR_sub, fun h => hxR (h ▸ hxw)⟩)
        obtain ⟨f₂, hf₂, Q, hred⟩ := ih _ hlt R' rfl hR_sq
        obtain ⟨f, hf, hred'⟩ := atomic_step_sq hf₁ hf₂ hR_sub hxw hxR hf₁_fix hf₁_eq hred
        exact ⟨f, hf, _, hred'⟩
      · obtain ⟨f₁, hf₁, R', hR_sq, hR_sub, hxw, hyw, hxR, hyR, hf₁_fix, hf₁_eq⟩ :=
          step_alt hw hxy hl
        have hlt : (occVars R').card < n := hcard ▸ Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.2 ⟨hR_sub, fun h => hxR (h ▸ hxw)⟩)
        obtain ⟨f₂, hf₂, Q, hred⟩ := ih _ hlt R' rfl hR_sq
        obtain ⟨f, hf, hred'⟩ :=
          atomic_step_comm hf₁ hf₂ hR_sub hxy hxw hyw hxR hyR hf₁_fix hf₁_eq hred
        exact ⟨f, hf, _, hred'⟩
      · obtain ⟨f₁, hf₁, R', hR_sq, hR_sub, hzw, hzR, hf₁_fix, hf₁_eq⟩ := step_conj hw hl
        have hlt : (occVars R').card < n := hcard ▸ Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.2 ⟨hR_sub, fun h => hzR (h ▸ hzw)⟩)
        obtain ⟨f₂, hf₂, Q, hred⟩ := ih _ hlt R' rfl hR_sq
        obtain ⟨f, hf, hred'⟩ := atomic_step_conj hf₁ hf₂ hR_sub hzw hzR hf₁_fix hf₁_eq hred
        exact ⟨f, hf, _, hred'⟩

end Reduction

/-! ### Main theorems -/

section Main

variable {G X : Type*} [Group G]

/-- Every strictly quadratic word `w ∈ G[X]` is carried by an elementary `G`-automorphism
`f ∈ GX.elementaryAut G X` (fixing every word in variables disjoint from those occurring in `w`)
and conjugation by an element `u ∈ G[X]` either to a coefficient `inl c` (`c ∈ G`) or to the left
side `S.toWord` of a standard quadratic equation `S : Standard G X` whose variables `S.vars` all
occur in `w`. -/
theorem exists_standardForm_fixing {w : GX G X} (hw : IsStrictlyQuadratic {w}) :
    ∃ f ∈ GX.elementaryAut G X, ∃ u : GX G X,
      (∀ a, (∀ x, occurrences x w ≠ 0 → occurrences x a = 0) → f a = a) ∧
      ((∃ c : G, u * f w * u⁻¹ = inl c) ∨
        ∃ S : Standard G X, u * f w * u⁻¹ = S.toWord ∧
          S.vars ⊆ {x | occurrences x w ≠ 0}) := by
  classical
  obtain ⟨f₁, hf₁, P, hf₁_eq, hnd, hsub, hf₁_fix⟩ :=
    exists_atomic_aux (occVars w).card w rfl hw
  obtain ⟨f₂, hf₂, u, hf₂_fix, hstd⟩ := P.exists_standardForm_fixing hnd
  refine ⟨f₂ * f₁, mul_mem hf₂ hf₁, u, fun a ha => ?_, ?_⟩
  · have ha' : ∀ v ∈ occVars w, a ∈ GX.avoiding v := fun v hv =>
      mem_avoiding_iff_occurrences_eq_zero.2 (ha v (mem_occVars_iff.1 hv))
    rw [MulAut.mul_apply, hf₁_fix a ha', hf₂_fix a fun v hv => ha' v (hsub v hv)]
  · rw [MulAut.mul_apply, hf₁_eq]
    exact hstd.imp_right fun ⟨S, hS, hSv⟩ =>
      ⟨S, hS, fun v hv => mem_occVars_iff.1 (hsub v (hSv hv))⟩

/-- Every strictly quadratic word `w ∈ G[X]` is carried by an elementary `G`-automorphism
`f ∈ GX.elementaryAut G X` followed by conjugation in `G[X]` either to a coefficient `inl c`
(`c ∈ G`) or to the left side `S.toWord` of a standard quadratic equation `S : Standard G X`
([IFT], §2.7, Lemma 1; [VAR-I], §1, Lemma 6). -/
theorem exists_standardForm {w : GX G X} (hw : IsStrictlyQuadratic {w}) :
    ∃ f ∈ GX.elementaryAut G X, ∃ u : GX G X,
      (∃ c : G, u * f w * u⁻¹ = inl c) ∨
        ∃ S : Standard G X, u * f w * u⁻¹ = S.toWord := by
  obtain ⟨f, hf, u, -, ⟨c, hc⟩ | ⟨S, hS, -⟩⟩ := exists_standardForm_fixing hw
  · exact ⟨f, hf, u, .inl ⟨c, hc⟩⟩
  · exact ⟨f, hf, u, .inr ⟨S, hS⟩⟩

end Main

/-! ### Exclusivity of the two branches -/

section Exclusivity

variable {G X Y Z : Type*} [Group G]

/-- The coefficient and standard-equation branches of `exists_standardForm` are mutually exclusive,
even across isomorphisms, homomorphisms, and conjugations fixing `inl c`: if `w` is carried by an
isomorphism `φ₁ : G[X] ≃* G[Y]` fixing `inl c` and conjugation to `inl c`, then no homomorphism
`φ₂ : G[X] →* G[Z]` fixing `inl c` and conjugation can carry `w` to `S.toWord` for any
`S : Standard G Z`. -/
theorem not_exists_standard_of_conj_mulEquiv_eq_inl
    {F : Type*} [FunLike F (GX G X) (GX G Z)] [MonoidHomClass F (GX G X) (GX G Z)]
    {w : GX G X} {u₁ : GX G Y} {c : G}
    (φ₁ : GX G X ≃* GX G Y) (hφ₁ : φ₁ (inl c) = inl c) (hw₁ : u₁ * φ₁ w * u₁⁻¹ = inl c)
    (φ₂ : F) (hφ₂ : φ₂ (inl c) = inl c) (u₂ : GX G Z) :
    ¬∃ S : Standard G Z, u₂ * φ₂ w * u₂⁻¹ = S.toWord := by
  rintro ⟨S, hS⟩
  rw [eq_conj_inl_of_conj_mulEquiv_eq_inl φ₁ hφ₁ hw₁] at hS
  exact S.toWord_ne_conj_map_conj_inl (f := (φ₂ : GX G X →* GX G Z)) hφ₂ u₂ (φ₁.symm u₁)
    (by simpa [MonoidHom.coe_ofClass] using hS.symm)

end Exclusivity

/-! ### Examples -/

section Examples

variable {G H X Y : Type*} [Group G] [Group H]

/-- There is a bijection between the solution set of the Klein-bottle equation `x₀ x₁ x₀ x₁⁻¹ = 1`
and that of the standard non-orientable equation `x₀² x₁² = 1` sending `(a₀, a₁)` to
`(a₀ a₁, a₁⁻¹)`. -/
theorem exists_equiv_V_kleinBottle (ι : G →* H) :
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

/-- Over `F(a, b)` in one variable, `z⁻¹ a z` is strictly quadratic
(`isStrictlyQuadratic_inv_mul_inl_mul_self`) with empty solution set
(`V_singleton_inv_mul_inl_mul_eq_empty`), and no homomorphism fixing `a` followed by conjugation can
carry it to a standard quadratic word. -/
theorem not_exists_standard_conj_of_zero_unit
    {F : Type*} [FunLike F (GX (FreeGroup (Fin 2)) Unit) (GX (FreeGroup (Fin 2)) Y)]
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
  simp

end Examples

end TauCeti.GroupAlgGeom.Quadratic
