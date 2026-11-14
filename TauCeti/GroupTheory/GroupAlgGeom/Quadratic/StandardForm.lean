/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.ChangeOfCoordinates
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Automorphism
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Reduction of strictly quadratic words to standard form

A strictly quadratic word of `G[X]` is brought to a standard quadratic word, or to a coefficient,
by a product of elementary `G`-automorphisms of `G[X]` (`GX.elementaryAut`) followed by a
conjugation in `G[X]`. The elementary automorphisms are the substitutions `x ↦ a x b`, for words
`a` and `b` in which `x` does not occur, and the inversions `x ↦ x⁻¹`. This is the corrected form
of [IFT], §2.7, Lemma 1 (and [VAR-I], §1, Lemma 6), which asserts a `G`-automorphism alone and
has no coefficient case: a coefficient `g ≠ 1` is strictly quadratic (`isStrictlyQuadratic_inl`)
and is not a standard quadratic word (`Standard.toWord_notMem_range_inl`), and `z⁻¹ a z` over
`F(a, b)` in one variable normalizes to `a` by conjugation rather than to a standard word.

The reduction follows the normal form of polygonal words in the classification of compact surfaces
([GaXu], Lemma 6.1), with the coefficients in the role of boundary edges:

1. In the reduced word of a strictly quadratic element in which some variable occurs, either some
   variable occurs twice with the same sign (giving a square `x²` by a transvection), or two
   variables alternate `x ⋯ y ⋯ x⁻¹ ⋯ y⁻¹` (giving a commutator `[x, y]` by the handle rule), or
   an innermost opposite-sign pair surrounds a single nontrivial coefficient `c` (giving a
   conjugate `z⁻¹ c z` by a transvection).
2. Inducting on the number of occurring variables brings the word into an ordered product of
   commutators, squares, conjugated coefficients, and a trailing constant `d` on pairwise distinct
   variables, fixing every word in disjoint variables.
3. When a square is present, `GX.exists_mem_elementaryAut_apply_commutator_mul_sq` replaces each
   commutator alongside a square by two squares.
4. When `d = 1` and a conjugated coefficient `zₘ⁻¹ cₘ zₘ` is present, conjugating the preceding
   atoms by `zₘ` via simultaneous transvections (`GX.exists_mem_elementaryAut_forall_apply_inr_of`)
   and conjugating the whole word by `zₘ` absorbs `zₘ⁻¹ cₘ zₘ` into the trailing constant `cₘ`.

Combined with `GX.apply_inl_of_mem_elementaryAut` and the coordinate-change API of
`ChangeOfCoordinates.lean` (`equivVOfConjMulEquiv`, `Rad_singleton_of_conj_mulEquiv`,
`CoordGroup.mulEquivOfConjMulEquiv`), the normalization transports solution sets, radicals, and
coordinate groups, while `Standard.mem_V_toWord_congr` shows that variables outside `S.vars` are
unconstrained.

## Main results

* `TauCeti.GroupAlgGeom.GX.transvection_crossCap`,
  `TauCeti.GroupAlgGeom.GX.transvection_rotate`,
  `TauCeti.GroupAlgGeom.GX.exists_mem_elementaryAut_apply_handle`,
  `TauCeti.GroupAlgGeom.GX.exists_mem_elementaryAut_apply_commutator_mul_sq`: the elementary
  rewriting rules on squares and commutators.
* `TauCeti.GroupAlgGeom.Quadratic.exists_standardForm_fixing`,
  `TauCeti.GroupAlgGeom.Quadratic.exists_standardForm`: every strictly quadratic word in `G[X]` is
  carried by an elementary `G`-automorphism (fixing all words in disjoint variables) and a
  conjugation either to a coefficient `inl c` (`c ∈ G`) or to `S.toWord` for a standard quadratic
  equation `S : Standard G X` with `S.vars` contained in the occurring variables of the word.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.toWord_ne_conj_map_conj_inl`,
  `TauCeti.GroupAlgGeom.Quadratic.not_exists_standard_of_conj_mulEquiv_eq_inl`: exclusivity of the
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

namespace TauCeti.GroupAlgGeom.GX

variable {G X : Type*} [Group G] [DecidableEq X] {x y : X} {U V W Z : GX G X}

/-- The cross-cap rule: `x ↦ x U⁻¹` turns `x U x V` into `x² U⁻¹ V`. -/
theorem transvection_crossCap (hU : U ∈ avoiding x) (hV : V ∈ avoiding x) :
    transvection x 1 U⁻¹ (one_mem _) (inv_mem hU)
        (inr (FreeGroup.of x) * U * inr (FreeGroup.of x) * V) =
      inr (FreeGroup.of x) ^ 2 * (U⁻¹ * V) := by
  simp [hU, hV, mul_assoc, pow_two]

/-- The rotation rule: `x ↦ x U⁻¹` turns `x U V x⁻¹ W` into `x V U x⁻¹ W`. -/
theorem transvection_rotate (hU : U ∈ avoiding x) (hV : V ∈ avoiding x) (hW : W ∈ avoiding x) :
    transvection x 1 U⁻¹ (one_mem _) (inv_mem hU)
        (inr (FreeGroup.of x) * U * V * (inr (FreeGroup.of x))⁻¹ * W) =
      inr (FreeGroup.of x) * V * U * (inr (FreeGroup.of x))⁻¹ * W := by
  simp [hU, hV, hW, mul_assoc]

/-- The handle rule without conjugation: an elementary automorphism which fixes every word in
which `x` and `y` do not occur turns `x U y V x⁻¹ W y⁻¹ Z` into `[x, y] W V U Z`, where
`[x, y] = x⁻¹ y⁻¹ x y`. -/
theorem exists_mem_elementaryAut_apply_handle (hxy : x ≠ y) (hU : U ∈ avoiding x ⊓ avoiding y)
    (hV : V ∈ avoiding x ⊓ avoiding y) (hW : W ∈ avoiding x ⊓ avoiding y)
    (hZ : Z ∈ avoiding x ⊓ avoiding y) : ∃ f ∈ elementaryAut G X,
      f (inr (FreeGroup.of x) * U * inr (FreeGroup.of y) * V * (inr (FreeGroup.of x))⁻¹ * W *
          (inr (FreeGroup.of y))⁻¹ * Z) =
        ⁅(inr (FreeGroup.of x) : GX G X)⁻¹, (inr (FreeGroup.of y))⁻¹⁆ * (W * V * U * Z) ∧
      ∀ a ∈ avoiding x ⊓ avoiding y, f a = a := by
  rw [mem_inf] at hU hV hW hZ
  -- `x ↦ x W V` and `y ↦ (W V U)⁻¹ y W`, then the inversions of `x` and `y`: the automorphism
  -- `x ↦ x⁻¹ W V`, `y ↦ (W V U)⁻¹ y⁻¹ W`
  refine ⟨invertVar G y * invertVar G x *
      transvection y (W * V * U)⁻¹ W (inv_mem (mul_mem (mul_mem hW.2 hV.2) hU.2)) hW.2 *
      transvection x 1 (W * V) (one_mem _) (mul_mem hW.1 hV.1), ?_, ?_, fun a ha => ?_⟩
  · refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_ <;> simp
  · -- `simp only`: the full simp set is noticeably slower here
    simp only [mul_assoc, mul_inv_rev, MulAut.mul_apply, map_mul, map_inv, inv_inv, one_mul,
      mul_inv_cancel_left, ne_eq, not_false_eq_true, inr_of_mem_avoiding_iff,
      transvection_inr_of_self, transvection_apply_of_mem_avoiding, invertVar_inr_of_self,
      invertVar_apply_of_mem_avoiding, commutatorElement_def, hxy, hxy.symm, hU.1, hU.2, hV.1, hV.2,
      hW.1, hW.2, hZ.1, hZ.2]
  · rw [mem_inf] at ha
    simp [ha.1, ha.2]

/-- A handle and a cross-cap are three cross-caps: for distinct variables `x`, `y`, `s` an
elementary automorphism which fixes every word in which `x`, `y` and `s` do not occur turns
`[x, y] s²` into `x² y² s²`, where `[x, y] = x⁻¹ y⁻¹ x y`. -/
theorem exists_mem_elementaryAut_apply_commutator_mul_sq {s : X} (hxy : x ≠ y) (hxs : x ≠ s)
    (hys : y ≠ s) : ∃ f ∈ elementaryAut G X,
      f (⁅(inr (FreeGroup.of x) : GX G X)⁻¹, (inr (FreeGroup.of y))⁻¹⁆ * inr (FreeGroup.of s) ^ 2) =
        inr (FreeGroup.of x) ^ 2 * inr (FreeGroup.of y) ^ 2 * inr (FreeGroup.of s) ^ 2 ∧
      ∀ a ∈ avoiding x ⊓ avoiding y ⊓ avoiding s, f a = a := by
  -- `x ↦ s x`, `y ↦ s y`, `y ↦ y s⁻¹`, `s ↦ y⁻¹ s`, `y ↦ y x`, then the inversions of `x`, `y`: the
  -- automorphism `x ↦ x y s x⁻¹`, `y ↦ x y s y⁻¹ x⁻¹ s⁻¹ y⁻¹ x⁻¹`, `s ↦ x y s`
  refine ⟨invertVar G y * invertVar G x *
      transvection y 1 (inr (FreeGroup.of x)) (one_mem _) (inr_of_mem_avoiding hxy) *
      transvection s (inr (FreeGroup.of y))⁻¹ 1 (inv_mem (inr_of_mem_avoiding hys)) (one_mem _) *
      transvection y 1 (inr (FreeGroup.of s))⁻¹ (one_mem _)
        (inv_mem (inr_of_mem_avoiding hys.symm)) *
      transvection y (inr (FreeGroup.of s)) 1 (inr_of_mem_avoiding hys.symm) (one_mem _) *
      transvection x (inr (FreeGroup.of s)) 1 (inr_of_mem_avoiding hxs.symm) (one_mem _), ?_, ?_,
      fun a ha => ?_⟩
  · refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_) ?_ <;> simp
  · -- `simp only`: the full simp set is noticeably slower here
    simp only [mul_assoc, pow_two, mul_one, one_mul, mul_inv_rev, inv_inv, inv_mul_cancel_left,
      MulAut.mul_apply, map_mul, map_inv, ne_eq, not_false_eq_true, inr_of_mem_avoiding_iff,
      transvection_inr_of_self, transvection_apply_of_mem_avoiding, invertVar_inr_of_self,
      invertVar_apply_of_mem_avoiding, commutatorElement_def, hxy, hxy.symm, hxs, hxs.symm, hys,
      hys.symm]
  · simp only [mem_inf] at ha
    simp [ha.1.1, ha.1.2, ha.2]

end TauCeti.GroupAlgGeom.GX

namespace TauCeti.GroupAlgGeom.Quadratic

/-! ### Pattern analysis and atomic reduction -/

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

variable [DecidableEq X]

private theorem prod_mem_avoiding_of_countVar_eq_zero {x : X} {L : List (G ⊕ X × Bool)}
    (h : GX.countVar x L = 0) : (L.map GX.letter).prod ∈ GX.avoiding x := by
  rw [mem_avoiding_iff_occurrences_eq_zero, occurrences_eq_countVar_reducedWord]
  exact Nat.eq_zero_of_le_zero ((GX.countVar_reducedWord_le x L).trans_eq h)

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
  have hp : p ∈ GX.avoiding x := prod_mem_avoiding_of_countVar_eq_zero hPMQ.1
  have hm : m ∈ GX.avoiding x := prod_mem_avoiding_of_countVar_eq_zero hPMQ.2.1
  have hq : q ∈ GX.avoiding x := prod_mem_avoiding_of_countVar_eq_zero hPMQ.2.2
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
  have hxR : x ∉ occVars (L.map GX.letter).prod := by
    rw [mem_occVars_iff, not_not, occurrences_eq_countVar_reducedWord]
    exact Nat.eq_zero_of_le_zero ((GX.countVar_reducedWord_le x L).trans_eq
      (by simp [L, hPMQ.1, hPMQ.2.1, hPMQ.2.2, GX.countVar_invRev]))
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
    ⟨prod_mem_avoiding_of_countVar_eq_zero hsx, prod_mem_avoiding_of_countVar_eq_zero hsy⟩
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
  have hxR : x ∉ occVars (L.map GX.letter).prod := by
    rw [mem_occVars_iff, not_not, occurrences_eq_countVar_reducedWord]
    exact Nat.eq_zero_of_le_zero ((GX.countVar_reducedWord_le x L).trans_eq
      (by simp [L, hx0.1, hx0.2.1, hx0.2.2.1, hx0.2.2.2.1, hx0.2.2.2.2]))
  have hyR : y ∉ occVars (L.map GX.letter).prod := by
    rw [mem_occVars_iff, not_not, occurrences_eq_countVar_reducedWord]
    exact Nat.eq_zero_of_le_zero ((GX.countVar_reducedWord_le y L).trans_eq
      (by simp [L, hy0.1, hy0.2.1, hy0.2.2.1, hy0.2.2.2.1, hy0.2.2.2.2]))
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
  have hp : p ∈ GX.avoiding z := prod_mem_avoiding_of_countVar_eq_zero hPQ.1
  have hq : q ∈ GX.avoiding z := prod_mem_avoiding_of_countVar_eq_zero hPQ.2
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
  have hzR : z ∉ occVars (L.map GX.letter).prod := by
    rw [mem_occVars_iff, not_not, occurrences_eq_countVar_reducedWord]
    exact Nat.eq_zero_of_le_zero
      ((GX.countVar_reducedWord_le z L).trans_eq (by simp [L, hPQ.1, hPQ.2]))
  refine ⟨f, hf_mem, (L.map GX.letter).prod, hrem.1, hrem.2, hzk, hzR, fun a ha => ?_, ?_⟩
  · simp [f, signAut_apply_of_mem_avoiding (ha z hzk), ha z hzk]
  · have hb_eq : signAut (G := G) z (!b) (GX.letter (.inr (z, b))) = (inr (FreeGroup.of z))⁻¹ := by
      simpa using signAut_letter_not (G := G) z (!b)
    have hLprod : (L.map GX.letter).prod = p * q := by simp [L, p, q]
    rw [hLprod, hw_eq]
    simp [f, conjWord, hb_eq, signAut_letter_self, signAut_apply_of_mem_avoiding, hp, hq,
      GX.inl_mem_avoiding, mul_assoc]

private def atomicVarList (comms : List (X × X)) (squares : List X) (conjs : List (X × G)) :
    List X :=
  comms.map Prod.fst ++ comms.map Prod.snd ++ squares ++ conjs.map Prod.fst

private def atomicToWord (comms : List (X × X)) (squares : List X) (conjs : List (X × G))
    (d : G) : GX G X :=
  (comms.map commWord).prod * (squares.map sqWord).prod * (conjs.map conjWord).prod * inl d

private def IsAtomicReduction (w : GX G X) (f : MulAut (GX G X)) (comms : List (X × X))
    (squares : List X) (conjs : List (X × G)) (d : G) : Prop :=
  f w = atomicToWord comms squares conjs d ∧
    (atomicVarList comms squares conjs).Nodup ∧
    (∀ v ∈ atomicVarList comms squares conjs, v ∈ occVars w) ∧
    (∀ p ∈ conjs, p.2 ≠ 1) ∧
    ∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f a = a

private theorem mem_avoiding_of_notMem_atomicVarList {v : X} {comms : List (X × X)}
    {squares : List X} {conjs : List (X × G)} (hv : v ∉ atomicVarList comms squares conjs) :
    (comms.map (commWord (G := G))).prod ∈ GX.avoiding v ∧
      (squares.map (sqWord (G := G))).prod ∈ GX.avoiding v ∧
      (conjs.map conjWord).prod ∈ GX.avoiding v := by
  simp only [atomicVarList, List.mem_append, List.mem_map, not_or, not_exists, not_and] at hv
  refine ⟨(GX.avoiding v).list_prod_mem fun _ hr => ?_,
    (GX.avoiding v).list_prod_mem fun _ hr => ?_,
    (GX.avoiding v).list_prod_mem fun _ hr => ?_⟩
  · rcases List.mem_map.1 hr with ⟨⟨x, y⟩, hm, rfl⟩
    exact commWord_mem_avoiding (fun h => hv.1.1.1 (x, y) hm h) (fun h => hv.1.1.2 (x, y) hm h)
  · rcases List.mem_map.1 hr with ⟨s, hm, rfl⟩
    exact sqWord_mem_avoiding fun h => hv.1.2 (h ▸ hm)
  · rcases List.mem_map.1 hr with ⟨⟨z, c⟩, hm, rfl⟩
    exact conjWord_mem_avoiding fun h => hv.2 (z, c) hm h

private theorem atomic_step_sq {w R' : GX G X} {f₁ f₂ : MulAut (GX G X)} {x : X}
    {comms : List (X × X)} {squares : List X} {conjs : List (X × G)} {d : G}
    (hf₁ : f₁ ∈ GX.elementaryAut G X) (hf₂ : f₂ ∈ GX.elementaryAut G X)
    (hR_sub : occVars R' ⊆ occVars w) (hxw : x ∈ occVars w) (hxR : x ∉ occVars R')
    (hf₁_fix : ∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f₁ a = a)
    (hf₁_eq : f₁ w = sqWord x * R')
    (hred : IsAtomicReduction R' f₂ comms squares conjs d) :
    ∃ f ∈ GX.elementaryAut G X, IsAtomicReduction w f comms (x :: squares) conjs d := by
  obtain ⟨hf₂_eq, hnd, hsub, hconj, hf₂_fix⟩ := hred
  have hs_not : x ∉ atomicVarList comms squares conjs := fun hm => hxR (hsub x hm)
  obtain ⟨hC, hSq, hCj⟩ := mem_avoiding_of_notMem_atomicVarList (G := G) hs_not
  let φ := GX.transvection x (comms.map commWord).prod (comms.map commWord).prod⁻¹ hC (inv_mem hC)
  have hperm : (atomicVarList comms (x :: squares) conjs).Perm
      (x :: atomicVarList comms squares conjs) := by
    simpa [atomicVarList, List.append_assoc] using
      List.perm_middle (l₁ := comms.map Prod.fst ++ comms.map Prod.snd) (a := x)
        (l₂ := squares ++ conjs.map Prod.fst)
  refine ⟨φ * f₂ * f₁, mul_mem (mul_mem (GX.transvection_mem_elementaryAut _ _ _) hf₂) hf₁,
    ?_, hperm.nodup_iff.2 (List.nodup_cons.2 ⟨hs_not, hnd⟩), fun v hv => ?_, hconj,
    fun a ha => ?_⟩
  · have hf₂_sq : f₂ (sqWord x) = sqWord x :=
      hf₂_fix _ fun v hv => sqWord_mem_avoiding (ne_of_mem_of_not_mem hv hxR).symm
    simp only [MulAut.mul_apply, hf₁_eq, map_mul, hf₂_sq, hf₂_eq, atomicToWord, List.map_cons,
      List.prod_cons]
    simp [φ, sqWord, pow_two, hC, hSq, hCj, GX.inl_mem_avoiding, mul_assoc]
  · rcases List.mem_cons.1 (hperm.subset hv) with rfl | hv'
    · exact hxw
    · exact hR_sub (hsub v hv')
  · simp [φ, hf₁_fix a ha, hf₂_fix a fun v hv => ha v (hR_sub hv), ha x hxw]

private theorem atomic_step_comm {w R' : GX G X} {f₁ f₂ : MulAut (GX G X)} {x y : X}
    {comms : List (X × X)} {squares : List X} {conjs : List (X × G)} {d : G}
    (hf₁ : f₁ ∈ GX.elementaryAut G X) (hf₂ : f₂ ∈ GX.elementaryAut G X)
    (hR_sub : occVars R' ⊆ occVars w) (hxy : x ≠ y)
    (hxw : x ∈ occVars w) (hyw : y ∈ occVars w) (hxR : x ∉ occVars R') (hyR : y ∉ occVars R')
    (hf₁_fix : ∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f₁ a = a)
    (hf₁_eq : f₁ w = commWord (x, y) * R')
    (hred : IsAtomicReduction R' f₂ comms squares conjs d) :
    ∃ f ∈ GX.elementaryAut G X, IsAtomicReduction w f ((x, y) :: comms) squares conjs d := by
  obtain ⟨hf₂_eq, hnd, hsub, hconj, hf₂_fix⟩ := hred
  have hx_not : x ∉ atomicVarList comms squares conjs := fun hm => hxR (hsub x hm)
  have hy_not : y ∉ atomicVarList comms squares conjs := fun hm => hyR (hsub y hm)
  have hperm : (atomicVarList ((x, y) :: comms) squares conjs).Perm
      (x :: y :: atomicVarList comms squares conjs) := by
    simp [atomicVarList, List.append_assoc]
  refine ⟨f₂ * f₁, mul_mem hf₂ hf₁, ?_,
    hperm.nodup_iff.2 (List.nodup_cons.2 ⟨by simp [hxy, hx_not], List.nodup_cons.2 ⟨hy_not, hnd⟩⟩),
    fun v hv => ?_, hconj,
    fun a ha => by simp [hf₁_fix a ha, hf₂_fix a fun v hv => ha v (hR_sub hv)]⟩
  · have hf₂_c : f₂ (commWord (x, y)) = commWord (x, y) := hf₂_fix _ fun v hv =>
      commWord_mem_avoiding (ne_of_mem_of_not_mem hv hxR).symm (ne_of_mem_of_not_mem hv hyR).symm
    simp [MulAut.mul_apply, hf₁_eq, hf₂_c, hf₂_eq, atomicToWord, mul_assoc]
  · rcases List.mem_cons.1 (hperm.subset hv) with rfl | hv'
    · exact hxw
    · rcases List.mem_cons.1 hv' with rfl | hv''
      · exact hyw
      · exact hR_sub (hsub v hv'')

private theorem atomic_step_conj {w R' : GX G X} {f₁ f₂ : MulAut (GX G X)} {z : X} {c : G}
    {comms : List (X × X)} {squares : List X} {conjs : List (X × G)} {d : G}
    (hf₁ : f₁ ∈ GX.elementaryAut G X) (hf₂ : f₂ ∈ GX.elementaryAut G X)
    (hR_sub : occVars R' ⊆ occVars w) (hc : c ≠ 1) (hzw : z ∈ occVars w) (hzR : z ∉ occVars R')
    (hf₁_fix : ∀ a, (∀ v ∈ occVars w, a ∈ GX.avoiding v) → f₁ a = a)
    (hf₁_eq : f₁ w = conjWord (z, c) * R')
    (hred : IsAtomicReduction R' f₂ comms squares conjs d) :
    ∃ f ∈ GX.elementaryAut G X, IsAtomicReduction w f comms squares ((z, c) :: conjs) d := by
  obtain ⟨hf₂_eq, hnd, hsub, hconj, hf₂_fix⟩ := hred
  have hz_not : z ∉ atomicVarList comms squares conjs := fun hm => hzR (hsub z hm)
  obtain ⟨hC, hSq, hCj⟩ := mem_avoiding_of_notMem_atomicVarList (G := G) hz_not
  let φ := GX.transvection z 1 ((comms.map commWord).prod * (squares.map sqWord).prod)⁻¹
    (one_mem _) (inv_mem (mul_mem hC hSq))
  have hperm : (atomicVarList comms squares ((z, c) :: conjs)).Perm
      (z :: atomicVarList comms squares conjs) := by
    simpa [atomicVarList, List.append_assoc] using
      List.perm_middle (l₁ := comms.map Prod.fst ++ comms.map Prod.snd ++ squares) (a := z)
        (l₂ := conjs.map Prod.fst)
  refine ⟨φ * f₂ * f₁, mul_mem (mul_mem (GX.transvection_mem_elementaryAut _ _ _) hf₂) hf₁,
    ?_, hperm.nodup_iff.2 (List.nodup_cons.2 ⟨hz_not, hnd⟩), fun v hv => ?_, ?_, fun a ha => ?_⟩
  · have hf₂_cj : f₂ (conjWord (z, c)) = conjWord (z, c) :=
      hf₂_fix _ fun v hv => conjWord_mem_avoiding (ne_of_mem_of_not_mem hv hzR).symm
    simp only [MulAut.mul_apply, hf₁_eq, map_mul, hf₂_cj, hf₂_eq, atomicToWord, List.map_cons,
      List.prod_cons]
    simp [φ, conjWord, hC, hSq, hCj, GX.inl_mem_avoiding, mul_assoc]
  · rcases List.mem_cons.1 (hperm.subset hv) with rfl | hv'
    · exact hzw
    · exact hR_sub (hsub v hv')
  · rintro p hp
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact hc
    · exact hconj p hp'
  · simp [φ, hf₁_fix a ha, hf₂_fix a fun v hv => ha v (hR_sub hv), ha z hzw]

private theorem exists_atomic_aux (n : ℕ) : ∀ w : GX G X, (occVars w).card = n →
    IsStrictlyQuadratic {w} →
    ∃ f ∈ GX.elementaryAut G X, ∃ comms squares conjs d,
      IsAtomicReduction w f comms squares conjs d := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro w hcard hw
    by_cases hemp : occVars w = ∅
    · have h0 : ∀ x, occurrences x w = 0 := fun x =>
        not_not.1 fun hx => Finset.notMem_empty x (hemp ▸ mem_occVars_iff.2 hx)
      obtain ⟨d, rfl⟩ := mem_range_inl_iff_forall_occurrences_eq_zero.2 h0
      exact ⟨1, one_mem _, [], [], [], d, by simp [atomicToWord], by simp [atomicVarList],
        by simp [atomicVarList], by simp, fun _ _ => rfl⟩
    · obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.2 hemp
      have hx₀2 : GX.countVar x₀ (GX.reducedWord w) = 2 := by
        have h1 := mem_occVars_iff.1 hx₀
        have h2 := isStrictlyQuadratic_singleton.1 hw x₀
        rw [occurrences_eq_countVar_reducedWord] at h1 h2; omega
      have hq : ∀ v, GX.countVar v (GX.reducedWord w) = 0 ∨
          GX.countVar v (GX.reducedWord w) = 2 := fun v => by
        simpa [occurrences_eq_countVar_reducedWord] using isStrictlyQuadratic_singleton.1 hw v
      rcases trichotomy_of_reduced (GX.isReduced_reducedWord w) hq ⟨x₀, hx₀2⟩ with
        ⟨x, b, P, M, Q, hl⟩ | ⟨x, y, bx, by_, P, U, V, W, Z, hxy, hl⟩ |
        ⟨z, b, c, P, Q, hc, hl⟩
      · obtain ⟨f₁, hf₁, R', hR_sq, hR_sub, hxw, hxR, hf₁_fix, hf₁_eq⟩ := step_sameSign hw hl
        have hlt : (occVars R').card < n := hcard ▸ Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.2 ⟨hR_sub, fun h => hxR (h ▸ hxw)⟩)
        obtain ⟨f₂, hf₂, comms, squares, conjs, d, hred⟩ := ih _ hlt R' rfl hR_sq
        obtain ⟨f, hf, hred'⟩ := atomic_step_sq hf₁ hf₂ hR_sub hxw hxR hf₁_fix hf₁_eq hred
        exact ⟨f, hf, comms, x :: squares, conjs, d, hred'⟩
      · obtain ⟨f₁, hf₁, R', hR_sq, hR_sub, hxw, hyw, hxR, hyR, hf₁_fix, hf₁_eq⟩ :=
          step_alt hw hxy hl
        have hlt : (occVars R').card < n := hcard ▸ Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.2 ⟨hR_sub, fun h => hxR (h ▸ hxw)⟩)
        obtain ⟨f₂, hf₂, comms, squares, conjs, d, hred⟩ := ih _ hlt R' rfl hR_sq
        obtain ⟨f, hf, hred'⟩ :=
          atomic_step_comm hf₁ hf₂ hR_sub hxy hxw hyw hxR hyR hf₁_fix hf₁_eq hred
        exact ⟨f, hf, (x, y) :: comms, squares, conjs, d, hred'⟩
      · obtain ⟨f₁, hf₁, R', hR_sq, hR_sub, hzw, hzR, hf₁_fix, hf₁_eq⟩ := step_conj hw hl
        have hlt : (occVars R').card < n := hcard ▸ Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.2 ⟨hR_sub, fun h => hzR (h ▸ hzw)⟩)
        obtain ⟨f₂, hf₂, comms, squares, conjs, d, hred⟩ := ih _ hlt R' rfl hR_sq
        obtain ⟨f, hf, hred'⟩ := atomic_step_conj hf₁ hf₂ hR_sub hc hzw hzR hf₁_fix hf₁_eq hred
        exact ⟨f, hf, comms, squares, (z, c) :: conjs, d, hred'⟩

private theorem sqTail_prod_mem_avoiding {v : X} {sqTail' : List X} {conjs : List (X × G)}
    {d : G} (hv : v ∉ atomicVarList [] sqTail' conjs) :
    (sqTail'.map sqWord).prod * (conjs.map conjWord).prod * inl d ∈ GX.avoiding (G := G) v := by
  obtain ⟨-, hsq, hcj⟩ := mem_avoiding_of_notMem_atomicVarList (G := G) hv
  exact mul_mem (mul_mem hsq hcj) (GX.inl_mem_avoiding v d)

private theorem elim_mixed_cons {x y s s' : X} {comms : List (X × X)} {sqTail sqTail' : List X}
    {conjs : List (X × G)} {d : G} {f₁ : MulAut (GX G X)}
    (hf₁ : f₁ ∈ GX.elementaryAut G X)
    (hnd : (atomicVarList ((x, y) :: comms) (s :: sqTail) conjs).Nodup)
    (hf₁_eq : f₁ (atomicToWord comms (s :: sqTail) conjs d) =
      atomicToWord [] (s' :: sqTail') conjs d)
    (hperm₁ : (atomicVarList [] (s' :: sqTail') conjs).Perm
      (atomicVarList comms (s :: sqTail) conjs))
    (hf₁_fix : ∀ a, (∀ v ∈ atomicVarList comms (s :: sqTail) conjs, a ∈ GX.avoiding v) →
      f₁ a = a) :
    ∃ f ∈ GX.elementaryAut G X,
      f (atomicToWord ((x, y) :: comms) (s :: sqTail) conjs d) =
        atomicToWord [] (x :: y :: s' :: sqTail') conjs d ∧
      (atomicVarList [] (x :: y :: s' :: sqTail') conjs).Perm
        (atomicVarList ((x, y) :: comms) (s :: sqTail) conjs) ∧
      ∀ a, (∀ v ∈ atomicVarList ((x, y) :: comms) (s :: sqTail) conjs, a ∈ GX.avoiding v) →
        f a = a := by
  have hperm₀ : (atomicVarList ((x, y) :: comms) (s :: sqTail) conjs).Perm
      (x :: y :: atomicVarList comms (s :: sqTail) conjs) := by
    simp [atomicVarList, List.append_assoc]
  obtain ⟨hx_not, hnd₁⟩ := List.nodup_cons.1 (hperm₀.nodup_iff.1 hnd)
  obtain ⟨hy_not, hnd_tail⟩ := List.nodup_cons.1 hnd₁
  have hxy : x ≠ y := fun h => hx_not (List.mem_cons.2 (.inl h))
  have hx_sub : x ∉ atomicVarList comms (s :: sqTail) conjs :=
    fun hm => hx_not (List.mem_cons_of_mem y hm)
  have hnd_s' : (atomicVarList [] (s' :: sqTail') conjs).Nodup := hperm₁.nodup_iff.2 hnd_tail
  have hs'_mem : s' ∈ atomicVarList [] (s' :: sqTail') conjs := List.mem_append_left _ (.head _)
  have hxs' : x ≠ s' := fun h => hx_sub (hperm₁.subset (h ▸ hs'_mem))
  have hys' : y ≠ s' := fun h => hy_not (hperm₁.subset (h ▸ hs'_mem))
  obtain ⟨f₂, hf₂, hf₂_eq, hf₂_fix⟩ :=
    GX.exists_mem_elementaryAut_apply_commutator_mul_sq (G := G) hxy hxs' hys'
  refine ⟨f₂ * f₁, mul_mem hf₂ hf₁, ?_, ?_, fun a ha => ?_⟩
  · have hf₁_c : f₁ (commWord (x, y)) = commWord (x, y) := hf₁_fix _ fun v hv =>
      commWord_mem_avoiding (ne_of_mem_of_not_mem hv hx_sub).symm
        (ne_of_mem_of_not_mem hv hy_not).symm
    have hnd_rest : s' ∉ atomicVarList [] sqTail' conjs :=
      (List.nodup_cons.1 (by simpa [atomicVarList] using hnd_s')).1
    have hf₂_rest : f₂ ((sqTail'.map sqWord).prod * (conjs.map conjWord).prod * inl d) =
        (sqTail'.map sqWord).prod * (conjs.map conjWord).prod * inl d :=
      hf₂_fix _ ⟨⟨sqTail_prod_mem_avoiding (fun hm =>
          hx_sub (hperm₁.subset (by simpa [atomicVarList] using Or.inr hm))),
        sqTail_prod_mem_avoiding (fun hm =>
          hy_not (hperm₁.subset (by simpa [atomicVarList] using Or.inr hm)))⟩,
        sqTail_prod_mem_avoiding hnd_rest⟩
    have hw_split : atomicToWord ((x, y) :: comms) (s :: sqTail) conjs d =
        commWord (x, y) * atomicToWord comms (s :: sqTail) conjs d := by
      simp [atomicToWord, mul_assoc]
    have h_reassoc : commWord (G := G) (x, y) * atomicToWord [] (s' :: sqTail') conjs d =
        (commWord (x, y) * sqWord s') *
          ((sqTail'.map sqWord).prod * (conjs.map conjWord).prod * inl d) := by
      simp [atomicToWord, mul_assoc]
    rw [MulAut.mul_apply, hw_split, map_mul, hf₁_c, hf₁_eq, h_reassoc, map_mul, hf₂_rest,
      commWord, sqWord, hf₂_eq]
    simp [sqWord, atomicToWord, mul_assoc]
  · have hperm₂ : atomicVarList [] (x :: y :: s' :: sqTail') conjs =
        x :: y :: atomicVarList [] (s' :: sqTail') conjs := by simp [atomicVarList]
    rw [hperm₂]
    exact (List.Perm.cons x (List.Perm.cons y hperm₁)).trans hperm₀.symm
  · have ha_sub : ∀ v ∈ atomicVarList comms (s :: sqTail) conjs, a ∈ GX.avoiding v :=
      fun v hv => ha v (hperm₀.symm.subset (List.mem_cons_of_mem x (List.mem_cons_of_mem y hv)))
    have hax : a ∈ GX.avoiding x := ha x (hperm₀.symm.subset List.mem_cons_self)
    have hay : a ∈ GX.avoiding y :=
      ha y (hperm₀.symm.subset (List.mem_cons_of_mem x List.mem_cons_self))
    rw [MulAut.mul_apply, hf₁_fix a ha_sub,
      hf₂_fix a ⟨⟨hax, hay⟩, ha_sub s' (hperm₁.subset hs'_mem)⟩]

private theorem elim_mixed (comms : List (X × X)) (s : X) (sqTail : List X) (conjs : List (X × G))
    (d : G) (hnd : (atomicVarList comms (s :: sqTail) conjs).Nodup) :
    ∃ f ∈ GX.elementaryAut G X, ∃ s' : X, ∃ sqTail' : List X,
      f (atomicToWord comms (s :: sqTail) conjs d) = atomicToWord [] (s' :: sqTail') conjs d ∧
      (atomicVarList [] (s' :: sqTail') conjs).Perm (atomicVarList comms (s :: sqTail) conjs) ∧
      ∀ a, (∀ v ∈ atomicVarList comms (s :: sqTail) conjs, a ∈ GX.avoiding v) → f a = a := by
  induction comms with
  | nil => exact ⟨1, one_mem _, s, sqTail, rfl, List.Perm.refl _, fun _ _ => rfl⟩
  | cons p comms ih =>
    rcases p with ⟨x, y⟩
    have hperm₀ : (atomicVarList ((x, y) :: comms) (s :: sqTail) conjs).Perm
        (x :: y :: atomicVarList comms (s :: sqTail) conjs) := by
      simp [atomicVarList, List.append_assoc]
    have hnd_tail :=
      (List.nodup_cons.1 (List.nodup_cons.1 (hperm₀.nodup_iff.1 hnd)).2).2
    obtain ⟨f₁, hf₁, s', sqTail', hf₁_eq, hperm₁, hf₁_fix⟩ := ih hnd_tail
    obtain ⟨f, hf, hf_eq, hperm, hf_fix⟩ :=
      elim_mixed_cons hf₁ hnd hf₁_eq hperm₁ hf₁_fix
    exact ⟨f, hf, x, y :: s' :: sqTail', hf_eq, hperm, hf_fix⟩

private theorem absorb_last_conj_word {comms : List (X × X)} {squares : List X}
    {conjsInit : List (X × G)} {z : X} {c : G} {f : MulAut (GX G X)}
    (hf : f ∈ GX.elementaryAut G X)
    (hdisj_c : ∀ v ∈ comms.map Prod.fst ++ comms.map Prod.snd ++ squares,
      v ∉ (conjsInit.map Prod.fst).toFinset)
    (hfY : ∀ v ∈ (atomicVarList comms squares conjsInit).toFinset,
      f (inr (FreeGroup.of v)) =
        (if v ∈ (conjsInit.map Prod.fst).toFinset then 1 else (inr (FreeGroup.of z))⁻¹) *
          inr (FreeGroup.of v) * inr (FreeGroup.of z))
    (hf_z : f (conjWord (z, c)) = conjWord (z, c)) :
    inr (FreeGroup.of z) * f (atomicToWord comms squares (conjsInit ++ [(z, c)]) 1) *
      (inr (FreeGroup.of z))⁻¹ = atomicToWord comms squares conjsInit c := by
  let z₀ : GX G X := inr (FreeGroup.of z)
  have hprod (L : List (GX G X)) (hL : ∀ w ∈ L, f w = z₀⁻¹ * w * z₀) :
      f L.prod = z₀⁻¹ * L.prod * z₀ := by
    have hmap : L.map f = L.map (MulAut.conj z₀⁻¹ : GX G X ≃* GX G X) :=
      List.map_congr_left fun w hw => by simp only [MulAut.conj_apply, inv_inv, hL w hw]
    rw [map_list_prod, hmap, ← map_list_prod, MulAut.conj_apply, inv_inv]
  have hf_comm : ∀ w ∈ comms.map commWord, f w = z₀⁻¹ * w * z₀ := by
    intro w hw
    rcases List.mem_map.1 hw with ⟨⟨x, y⟩, hp, rfl⟩
    have hx_pre : x ∈ comms.map Prod.fst ++ comms.map Prod.snd ++ squares :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (f := Prod.fst) hp))
    have hy_pre : y ∈ comms.map Prod.fst ++ comms.map Prod.snd ++ squares :=
      List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (f := Prod.snd) hp))
    simp [z₀, commWord, commutatorElement_def,
      hfY x (List.mem_toFinset.2 (List.mem_append_left _ hx_pre)),
      hfY y (List.mem_toFinset.2 (List.mem_append_left _ hy_pre)),
      hdisj_c x hx_pre, hdisj_c y hy_pre, mul_assoc]
  have hf_sq : ∀ w ∈ squares.map sqWord, f w = z₀⁻¹ * w * z₀ := by
    intro w hw
    rcases List.mem_map.1 hw with ⟨s, hs, rfl⟩
    have hs_pre : s ∈ comms.map Prod.fst ++ comms.map Prod.snd ++ squares :=
      List.mem_append_right _ hs
    simp [z₀, sqWord, pow_two, hfY s (List.mem_toFinset.2 (List.mem_append_left _ hs_pre)),
      hdisj_c s hs_pre, mul_assoc]
  have hf_cj : ∀ w ∈ conjsInit.map conjWord, f w = z₀⁻¹ * w * z₀ := by
    intro w hw
    rcases List.mem_map.1 hw with ⟨⟨x, g⟩, hp, rfl⟩
    have hx_cj : x ∈ conjsInit.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hp
    rw [conjWord, map_mul, map_mul, map_inv,
      hfY x (List.mem_toFinset.2 (List.mem_append_right _ hx_cj)),
      GX.apply_inl_of_mem_elementaryAut hf]
    simp [hx_cj, z₀, mul_assoc]
  simp only [atomicToWord, List.map_append, List.prod_append, List.map_singleton,
    List.prod_singleton, map_one, mul_one, map_mul,
    hprod _ hf_comm, hprod _ hf_sq, hprod _ hf_cj, hf_z]
  simp [conjWord, z₀, mul_assoc]

private theorem absorb_last_conj (comms : List (X × X)) (squares : List X)
    (conjsInit : List (X × G)) (z : X) (c : G)
    (hnd : (atomicVarList comms squares (conjsInit ++ [(z, c)])).Nodup) :
    ∃ f ∈ GX.elementaryAut G X, ∃ u : GX G X,
      u * f (atomicToWord comms squares (conjsInit ++ [(z, c)]) 1) * u⁻¹ =
        atomicToWord comms squares conjsInit c ∧
      ∀ a, (∀ v ∈ atomicVarList comms squares (conjsInit ++ [(z, c)]), a ∈ GX.avoiding v) →
        f a = a := by
  let V₀ := atomicVarList comms squares conjsInit
  have heq_var : atomicVarList comms squares (conjsInit ++ [(z, c)]) = V₀ ++ [z] := by
    simp [V₀, atomicVarList, List.append_assoc]
  rw [heq_var] at hnd
  have hz_not : z ∉ V₀ := fun hm =>
    (List.nodup_append.1 hnd).2.2 z hm z (List.mem_singleton.2 rfl) rfl
  have hV₀_nd : V₀.Nodup := (List.nodup_append.1 hnd).1
  have hzY : z ∉ V₀.toFinset := by simpa using hz_not
  let z₀ : GX G X := inr (FreeGroup.of z)
  obtain ⟨f, hf, hfY, hfw⟩ := GX.exists_mem_elementaryAut_forall_apply_inr_of (G := G) V₀.toFinset
    (fun v => if v ∈ (conjsInit.map Prod.fst).toFinset then 1 else z₀⁻¹) (fun _ => z₀)
    (fun _ _ _ hy' => by split_ifs <;> simp [z₀, (ne_of_mem_of_not_mem hy' hzY).symm])
    (fun _ _ _ hy' => by simp [z₀, (ne_of_mem_of_not_mem hy' hzY).symm])
  have hdisj_c : ∀ v ∈ comms.map Prod.fst ++ comms.map Prod.snd ++ squares,
      v ∉ (conjsInit.map Prod.fst).toFinset :=
    fun v hv hvyc => (List.nodup_append.1 hV₀_nd).2.2 v hv v (List.mem_toFinset.1 hvyc) rfl
  have hf_z : f (conjWord (z, c)) = conjWord (z, c) :=
    hfw _ fun v hv => conjWord_mem_avoiding (ne_of_mem_of_not_mem hv hzY).symm
  refine ⟨f, hf, z₀, absorb_last_conj_word hf hdisj_c hfY hf_z, fun a ha => hfw a fun v hv =>
    ha v (by rw [heq_var]; exact List.mem_append_left _ (List.mem_toFinset.1 hv))⟩

end Reduction

section Main

variable {G X : Type*} [Group G]

omit [Group G] in
private theorem sumElim_injective_of_nodup_ofFn_append {n m : ℕ} {f : Fin n → X} {g : Fin m → X}
    (hnd : (List.ofFn f ++ List.ofFn g).Nodup) : (Sum.elim f g).Injective := by
  obtain ⟨hf_nd, hg_nd, hdisj⟩ := List.nodup_append.1 hnd
  exact (List.nodup_ofFn.1 hf_nd).sumElim (List.nodup_ofFn.1 hg_nd) fun i j =>
    hdisj _ (List.mem_ofFn.2 ⟨i, rfl⟩) _ (List.mem_ofFn.2 ⟨j, rfl⟩)

omit [Group G] in
private theorem comms_sumElim_injective {comms : List (X × X)}
    (hnd : (comms.map Prod.fst ++ comms.map Prod.snd).Nodup) :
    (Sum.elim (fun i : Fin comms.length => comms[i].1)
      (fun i : Fin comms.length => comms[i].2)).Injective :=
  sumElim_injective_of_nodup_ofFn_append <| by
    simpa [List.ofFn_getElem_eq_map comms Prod.fst, List.ofFn_getElem_eq_map comms Prod.snd]
      using hnd

omit [Group G] in
private theorem comms_mem_atomicVarList {comms : List (X × X)} {squares : List X}
    {conjs : List (X × G)} (s : Fin comms.length ⊕ Fin comms.length) :
    Sum.elim (fun i : Fin comms.length => comms[i].1) (fun i : Fin comms.length => comms[i].2) s ∈
      atomicVarList comms squares conjs := by
  rcases s with i | i
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map_of_mem (f := Prod.fst) (List.getElem_mem _))))
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map_of_mem (f := Prod.snd) (List.getElem_mem _))))

private theorem atomic_to_standard_or_inl_one (comms : List (X × X)) (squares : List X)
    (hmix : comms = [] ∨ squares = [])
    (hnd : (atomicVarList comms squares ([] : List (X × G))).Nodup) :
    (∃ c : G, atomicToWord comms squares [] 1 = inl c) ∨
      ∃ S : Standard G X, atomicToWord comms squares [] 1 = S.toWord ∧
        ∀ v ∈ S.vars, v ∈ atomicVarList comms squares ([] : List (X × G)) := by
  rcases hmix with rfl | rfl
  · by_cases hsq : squares = []
    · subst hsq
      exact .inl ⟨1, by simp [atomicToWord]⟩
    · have hn : 0 < squares.length := List.length_pos_iff.2 hsq
      have hinj : (fun i : Fin squares.length => squares[i]).Injective :=
        List.nodup_ofFn.1 (by simpa [atomicVarList] using hnd)
      refine .inr ⟨.nonorientable squares.length hn (fun i => squares[i]) hinj, ?_, ?_⟩
      · simp [Standard.toWord_def, atomicToWord,
          (List.ofFn_getElem_eq_map squares (sqWord (G := G))).symm, sqWord]
      · rw [Standard.vars_nonorientable]
        rintro _ ⟨i, rfl⟩
        simp [atomicVarList]
  · by_cases hcm : comms = []
    · subst hcm
      exact .inl ⟨1, by simp [atomicToWord]⟩
    · have hn : 0 < comms.length := List.length_pos_iff.2 hcm
      have hinj := comms_sumElim_injective
        (by simpa only [atomicVarList, List.map_nil, List.append_nil] using hnd)
      refine .inr ⟨.orientable comms.length hn (fun i => comms[i].1) (fun i => comms[i].2) hinj,
        ?_, ?_⟩
      · simp [Standard.toWord_def, atomicToWord,
          (List.ofFn_getElem_eq_map comms (commWord (G := G))).symm, commWord]
      · rw [Standard.vars_orientable]
        rintro _ ⟨s, rfl⟩
        exact comms_mem_atomicVarList s

private theorem atomic_to_standard_or_inl_squares_nil (comms : List (X × X)) (conjs : List (X × G))
    (d : G) (hd : d ≠ 1) (hnd : (atomicVarList comms [] conjs).Nodup)
    (hc : ∀ p ∈ conjs, p.2 ≠ 1) :
    (∃ c : G, atomicToWord comms [] conjs d = inl c) ∨
      ∃ S : Standard G X, atomicToWord comms [] conjs d = S.toWord ∧
        ∀ v ∈ S.vars, v ∈ atomicVarList comms [] conjs := by
  by_cases hboth : comms = [] ∧ conjs = []
  · obtain ⟨rfl, rfl⟩ := hboth
    exact .inl ⟨d, by simp [atomicToWord]⟩
  · have hnm : 0 < comms.length + conjs.length := by
      rcases not_and_or.1 hboth with hcm | hcj <;>
        have := List.length_pos_iff.2 ‹_› <;> omega
    obtain ⟨hnd_xy, hnd_cj, hdisj⟩ :=
      List.nodup_append.1 (by simpa only [atomicVarList, List.append_nil] using hnd)
    have hnd_z : (List.ofFn (fun j : Fin conjs.length => conjs[j].1)).Nodup := by
      simpa [List.ofFn_getElem_eq_map conjs Prod.fst] using hnd_cj
    have hinj : (Sum.elim (Sum.elim (fun i : Fin comms.length => comms[i].1)
        (fun i : Fin comms.length => comms[i].2))
        (fun j : Fin conjs.length => conjs[j].1)).Injective :=
      (comms_sumElim_injective hnd_xy).sumElim (List.nodup_ofFn.1 hnd_z) fun s j => by
        rcases s with i | i
        · exact hdisj _
            (List.mem_append_left _ (List.mem_map_of_mem (f := Prod.fst) (List.getElem_mem _)))
            _ (List.mem_map_of_mem (f := Prod.fst) (List.getElem_mem _))
        · exact hdisj _
            (List.mem_append_right _ (List.mem_map_of_mem (f := Prod.snd) (List.getElem_mem _)))
            _ (List.mem_map_of_mem (f := Prod.fst) (List.getElem_mem _))
    refine .inr ⟨.orientableCoeff comms.length conjs.length hnm
      (fun i => comms[i].1) (fun i => comms[i].2) (fun j => conjs[j].1) hinj
      (fun j => conjs[j].2) (fun j => hc _ (List.getElem_mem _)) d hd, ?_, ?_⟩
    · simp [Standard.toWord_def, atomicToWord,
        (List.ofFn_getElem_eq_map comms (commWord (G := G))).symm,
        (List.ofFn_getElem_eq_map conjs (conjWord (G := G))).symm, commWord, conjWord, mul_assoc]
    · rw [Standard.vars_orientableCoeff]
      rintro _ ⟨s | j, rfl⟩
      · exact comms_mem_atomicVarList s
      · exact List.mem_append_right _ (List.mem_map_of_mem (f := Prod.fst) (List.getElem_mem _))

private theorem atomic_to_standard_or_inl_comms_nil (squares : List X) (hsq : squares ≠ [])
    (conjs : List (X × G)) (d : G) (hd : d ≠ 1) (hnd : (atomicVarList [] squares conjs).Nodup)
    (hc : ∀ p ∈ conjs, p.2 ≠ 1) :
    (∃ c : G, atomicToWord [] squares conjs d = inl c) ∨
      ∃ S : Standard G X, atomicToWord [] squares conjs d = S.toWord ∧
        ∀ v ∈ S.vars, v ∈ atomicVarList [] squares conjs := by
  have hn : 0 < squares.length := List.length_pos_iff.2 hsq
  have hinj : (Sum.elim (fun i : Fin squares.length => squares[i])
      (fun j : Fin conjs.length => conjs[j].1)).Injective :=
    sumElim_injective_of_nodup_ofFn_append <| by
      simpa [List.ofFn_getElem_eq_map conjs Prod.fst, atomicVarList] using hnd
  refine .inr ⟨.nonorientableCoeff squares.length conjs.length hn (fun i => squares[i])
    (fun j : Fin conjs.length => conjs[j].1) hinj (fun j => conjs[j].2)
    (fun j => hc _ (List.getElem_mem _)) d hd, ?_, ?_⟩
  · simp [Standard.toWord_def, atomicToWord,
      (List.ofFn_getElem_eq_map squares (sqWord (G := G))).symm,
      (List.ofFn_getElem_eq_map conjs (conjWord (G := G))).symm, sqWord, conjWord, mul_assoc]
  · rw [Standard.vars_nonorientableCoeff]
    rintro _ ⟨i | j, rfl⟩
    · exact List.mem_append_left _ (List.mem_append_right _ (List.getElem_mem _))
    · exact List.mem_append_right _ (List.mem_map_of_mem (f := Prod.fst) (List.getElem_mem _))

private theorem atomic_to_standard_or_inl_ne_one (comms : List (X × X)) (squares : List X)
    (conjs : List (X × G)) (d : G) (hd : d ≠ 1) (hmix : comms = [] ∨ squares = [])
    (hnd : (atomicVarList comms squares conjs).Nodup) (hc : ∀ p ∈ conjs, p.2 ≠ 1) :
    (∃ c : G, atomicToWord comms squares conjs d = inl c) ∨
      ∃ S : Standard G X, atomicToWord comms squares conjs d = S.toWord ∧
        ∀ v ∈ S.vars, v ∈ atomicVarList comms squares conjs := by
  by_cases hsq : squares = []
  · subst hsq
    exact atomic_to_standard_or_inl_squares_nil comms conjs d hd hnd hc
  · obtain rfl := hmix.resolve_right hsq
    exact atomic_to_standard_or_inl_comms_nil squares hsq conjs d hd hnd hc

private theorem exists_unmixed_atomic {w : GX G X} (hw : IsStrictlyQuadratic {w}) :
    ∃ f ∈ GX.elementaryAut G X, ∃ comms squares conjs d,
      (comms = [] ∨ squares = []) ∧
      f w = atomicToWord comms squares conjs d ∧
      (atomicVarList comms squares conjs).Nodup ∧
      (∀ v ∈ atomicVarList comms squares conjs, v ∈ occVars w) ∧
      (∀ p ∈ conjs, p.2 ≠ 1) ∧
      ∀ a, (∀ x, occurrences x w ≠ 0 → occurrences x a = 0) → f a = a := by
  classical
  obtain ⟨f₁, hf₁, comms, squares, conjs, d, hf₁_eq, hnd, hsub, hc, hf₁_fix⟩ :=
    exists_atomic_aux (occVars w).card w rfl hw
  rcases squares with _ | ⟨s, sqTail⟩
  · refine ⟨f₁, hf₁, comms, [], conjs, d, .inr rfl, hf₁_eq, hnd, hsub, hc, fun a ha =>
      hf₁_fix a fun v hv => mem_avoiding_iff_occurrences_eq_zero.2 (ha v (mem_occVars_iff.1 hv))⟩
  · obtain ⟨f₂, hf₂, s', sqTail', hf₂_eq, hperm, hf₂_fix⟩ :=
      elim_mixed comms s sqTail conjs d hnd
    refine ⟨f₂ * f₁, mul_mem hf₂ hf₁, [], s' :: sqTail', conjs, d, .inl rfl,
      by rw [MulAut.mul_apply, hf₁_eq, hf₂_eq], hperm.nodup_iff.2 hnd,
      fun v hv => hsub v (hperm.subset hv), hc, fun a ha => ?_⟩
    have ha' : ∀ v ∈ occVars w, a ∈ GX.avoiding v := fun v hv =>
      mem_avoiding_iff_occurrences_eq_zero.2 (ha v (mem_occVars_iff.1 hv))
    simp [hf₁_fix a ha', hf₂_fix a fun v hv => ha' v (hsub v hv)]

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
  obtain ⟨f₁, hf₁, comms, squares, conjs, d, hmix, hf₁_eq, hnd, hsub, hc, hfix₁⟩ :=
    exists_unmixed_atomic hw
  -- Absorb the last conjugated coefficient when `d = 1` and `conjs ≠ []`.
  by_cases hd : d = 1
  · subst hd
    rcases conjs.eq_nil_or_concat with rfl | ⟨conjsInit, ⟨z, c⟩, hconcat⟩
    · refine ⟨f₁, hf₁, 1, hfix₁, ?_⟩
      have hw_eq : 1 * f₁ w * 1⁻¹ = atomicToWord comms squares [] 1 := by simp [hf₁_eq]
      rcases atomic_to_standard_or_inl_one comms squares hmix hnd with
        ⟨c', hc'⟩ | ⟨S, hS, hS_vars⟩
      · exact .inl ⟨c', hw_eq.trans hc'⟩
      · exact .inr ⟨S, hw_eq.trans hS, fun v hv => mem_occVars_iff.1 (hsub v (hS_vars v hv))⟩
    · rw [List.concat_eq_append] at hconcat; subst hconcat
      have hc_z : c ≠ 1 := hc (z, c) (by simp)
      have hc_init : ∀ p ∈ conjsInit, p.2 ≠ 1 := fun p hp => hc p (List.mem_append_left _ hp)
      obtain ⟨f₂, hf₂, u, hf₂_eq, hf₂_fix⟩ := absorb_last_conj comms squares conjsInit z c hnd
      have hnd_init : (atomicVarList comms squares conjsInit).Nodup :=
        (List.nodup_append.1 (by simpa [atomicVarList, List.append_assoc] using hnd)).1
      have hsub_init : ∀ v ∈ atomicVarList comms squares conjsInit, v ∈ occVars w := fun v hv =>
        hsub v (by simp [atomicVarList] at hv ⊢; tauto)
      have hw_eq : u * (f₂ * f₁) w * u⁻¹ = atomicToWord comms squares conjsInit c := by
        rw [MulAut.mul_apply, hf₁_eq, hf₂_eq]
      refine ⟨f₂ * f₁, mul_mem hf₂ hf₁, u, fun a ha => ?_, ?_⟩
      · rw [MulAut.mul_apply, hfix₁ a ha]
        exact hf₂_fix a fun v hv =>
          mem_avoiding_iff_occurrences_eq_zero.2 (ha v (mem_occVars_iff.1 (hsub v hv)))
      · rcases atomic_to_standard_or_inl_ne_one comms squares conjsInit c hc_z hmix hnd_init
          hc_init with ⟨c', hc'⟩ | ⟨S, hS, hS_vars⟩
        · exact .inl ⟨c', hw_eq.trans hc'⟩
        · exact .inr ⟨S, hw_eq.trans hS,
            fun v hv => mem_occVars_iff.1 (hsub_init v (hS_vars v hv))⟩
  · refine ⟨f₁, hf₁, 1, hfix₁, ?_⟩
    have hw_eq : 1 * f₁ w * 1⁻¹ = atomicToWord comms squares conjs d := by simp [hf₁_eq]
    rcases atomic_to_standard_or_inl_ne_one comms squares conjs d hd hmix hnd hc with
      ⟨c', hc'⟩ | ⟨S, hS, hS_vars⟩
    · exact .inl ⟨c', hw_eq.trans hc'⟩
    · exact .inr ⟨S, hw_eq.trans hS, fun v hv => mem_occVars_iff.1 (hsub v (hS_vars v hv))⟩

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

/-- Applying a homomorphism fixing `inl c` and a conjugation to a conjugate of `inl c` never yields
the left side of a standard quadratic equation. -/
theorem Standard.toWord_ne_conj_map_conj_inl
    {F : Type*} [FunLike F (GX G X) (GX G Y)] [MonoidHomClass F (GX G X) (GX G Y)]
    (S : Standard G Y) (φ : F) {c : G} (hφ : φ (inl c) = inl c) (u : GX G Y) (v : GX G X) :
    S.toWord ≠ u * φ (v * inl c * v⁻¹) * u⁻¹ := by
  rw [map_mul, map_mul, map_inv, hφ]
  simpa [mul_assoc] using S.toWord_ne_conj_inl (u * φ v) c

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
  have hφ₁w : φ₁ w = u₁⁻¹ * inl c * u₁ := by
    calc φ₁ w = u₁⁻¹ * (u₁ * φ₁ w * u₁⁻¹) * u₁ := by simp [mul_assoc]
      _ = u₁⁻¹ * inl c * u₁ := by rw [hw₁]
  have hw : w = (φ₁.symm u₁)⁻¹ * inl c * ((φ₁.symm u₁)⁻¹)⁻¹ := by
    calc w = φ₁.symm (φ₁ w) := (φ₁.symm_apply_apply w).symm
      _ = (φ₁.symm u₁)⁻¹ * inl c * ((φ₁.symm u₁)⁻¹)⁻¹ := by
        rw [hφ₁w, map_mul, map_mul, map_inv, φ₁.symm_apply_eq.2 hφ₁.symm, inv_inv]
  rw [hw] at hS
  exact S.toWord_ne_conj_map_conj_inl φ₂ hφ₂ u₂ (φ₁.symm u₁)⁻¹ hS.symm

end Exclusivity

/-! ### Examples -/

section Examples

variable {G H X Y : Type*} [Group G] [Group H]

/-- The elementary change of coordinates `x₀ ↦ x₀ x₁⁻¹`, `x₁ ↦ x₁⁻¹` induces a bijection `e`
between the solution set of the Klein-bottle equation `x₀ x₁ x₀ x₁⁻¹ = 1` and that of the standard
non-orientable equation `x₀² x₁² = 1`, sending `(a₀, a₁)` to `(a₀ a₁, a₁⁻¹)`. -/
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
theorem Standard.toWord_ne_conj_map_one
    {α F : Type*} [One α] [FunLike F α (GX G Y)] [OneHomClass F α (GX G Y)]
    (S : Standard G Y) (φ : F) (u : GX G Y) :
    S.toWord ≠ u * φ 1 * u⁻¹ := by
  simp

end Examples

end TauCeti.GroupAlgGeom.Quadratic
