/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.Combinatorics.PlanarMatching.Monoidal
import all TauCeti.Combinatorics.Enumerative.PerfectMatching
import all TauCeti.Combinatorics.PlanarMatching.Basic
import all TauCeti.Combinatorics.PlanarMatching.TLDiagram
import all TauCeti.Combinatorics.PlanarMatching.Compose
import all TauCeti.Combinatorics.PlanarMatching.Tensor
import all TauCeti.Combinatorics.PlanarMatching.Category
import all TauCeti.Combinatorics.PlanarMatching.Glue
import all TauCeti.Combinatorics.PlanarMatching.Associativity

/-!
# The rigid structure of the Temperley–Lieb diagram category

Every object of the Temperley–Lieb diagram category `TauCeti.TLDiagCat` is its own dual, so
`TLDiagCat` is a rigid monoidal category.

The generating object `TLDiagCat.of 1`, a single boundary point, is self-dual with coevaluation
the cup `TLDiagCat.cup : of 0 ⟶ of 2` and evaluation the cap `TLDiagCat.cap : of 2 ⟶ of 0`. The
two zigzag identities are computations with diagrams on three boundary points, checked by
evaluating the composite diagrams. The empty boundary `of 0` is the monoidal unit, with its
canonical self-duality, and the self-duality of `of (n + 2)` is the tensor product of the
self-dualities of `of 1` and `of (n + 1)` (Mathlib's `CategoryTheory.ExactPairing.tensor`),
transported along `of (n + 2) = of 1 ⊗ of (n + 1)`. Pictorially, the coevaluation of `of n` is
`n` nested cups and its evaluation `n` nested caps (`TLDiagCat.diagram_coevaluation`,
`TLDiagCat.diagram_evaluation`); the examples at the end spell this out for two strands, and check
that closing the identity of `of 2` produces two circles.

## Main definitions

* `TauCeti.TLDiagCat.exactPairingOne`: the generating self-duality of `of 1`, by the cup and the
  cap.
* `TauCeti.TLDiagCat.exactPairingOf`: the self-duality of `of n`, for every `n`.
* `TauCeti.TLDiagCat.instExactPairing`: every object is self-dual.
* `TauCeti.TLDiagCat.instRigidCategory`: the Temperley–Lieb diagram category is rigid, with
  every object its own left and right dual.

## Main results

* `TauCeti.TLDiagCat.coevaluation_one`, `TauCeti.TLDiagCat.evaluation_one`: the self-duality of
  the generating object is given by the cup and the cap.
* `TauCeti.TLDiagCat.coevaluation_zero`, `TauCeti.TLDiagCat.evaluation_zero`: the self-duality of
  the empty boundary is trivial.
* `TauCeti.TLDiagCat.coevaluation_add_two`, `TauCeti.TLDiagCat.evaluation_add_two`: the
  self-duality of `of (n + 2)` is the tensor product of those of `of 1` and `of (n + 1)`.
* `TauCeti.TLDiagCat.diagram_coevaluation`, `TauCeti.TLDiagCat.diagram_evaluation`: the
  coevaluation of an object on `n` points is `n` nested cups and its evaluation `n` nested caps.
* `TauCeti.TLDiagCat.rightDual_eq`, `TauCeti.TLDiagCat.leftDual_eq`: every object is its own
  dual.

## Implementation notes

The zigzag identities of the generating object, and the closed circles example at the end of the
file, are proved by `decide +kernel`, which evaluates the composite diagrams. This needs the
definitions of composition and juxtaposition of diagrams, which this file imports with
`import all`.

For general `n`, the diagrams of the coevaluation and the evaluation are computed through the
partner functions of their matchings, with the private machinery of
`TauCeti.Combinatorics.PlanarMatching.Associativity` and
`TauCeti.Combinatorics.PlanarMatching.Tensor`, also imported with `import all`. The
coevaluation of `of (n + 2)` is a cup below that of `of (n + 1)` with a straight strand on each
side. The evaluation of `of (n + 2)` inserts a cap in the middle of that of `of (n + 1)`; by the
interchange law, this reduces to a cap above nested caps with a straight strand on each side.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

/-! ### Partner functions of nested cups and caps -/

namespace TLDiagram

open PlanarMatching

/-- The partner function of the fully nested matching of `a` points. -/
private def nestedFn (a q : ℕ) : ℕ :=
  if q < a then a - 1 - q else q

private theorem pv_nested_eq (k : ℕ) : pv (nested k) = nestedFn (k + k) := by
  funext q
  rw [nestedFn]
  split_ifs with h
  · exact pv_nested k h
  · exact pv_of_le _ (by omega)

private theorem pv_cup_eq : pv cup.matching = nestedFn 2 := by
  funext q
  rw [nestedFn]
  split_ifs with h
  · exact pv_cup_matching h
  · exact pv_of_le _ (by omega)

private theorem pv_cap_eq : pv cap.matching = nestedFn 2 := by
  funext q
  rw [nestedFn]
  split_ifs with h
  · exact pv_cap_matching h
  · exact pv_of_le _ (by omega)

private theorem eq_cast_of_pv {n m n' m' : ℕ} (hn : n = n') (hm : m = m') {f : TLDiagram n m}
    {g : TLDiagram n' m'} (hp : pv f.matching = pv g.matching) (hc : f.circles = g.circles) :
    g = cast hn hm f := by
  subst hn hm
  rw [cast_refl, Equiv.refl_apply]
  exact TLDiagram.ext (eq_of_pv_eq hp.symm) hc.symm

/-! #### A cup around nested cups -/

/-- Joining the second point of a cup to the first point of a matching with partner function `γ`
on `L` points, juxtaposed after the cup, gives back `γ`. -/
private theorem contractFn_one_appendFn_cup {L : ℕ} (γ : ℕ → ℕ) (hL : 0 < L)
    (hlt : ∀ q < L, γ q < L) (hle : ∀ q, L ≤ q → γ q = q) :
    contractFn 1 (appendFn 2 L (nestedFn 2) γ) = γ := by
  set φ := appendFn 2 L (nestedFn 2) γ
  have φ0 : φ 0 = 1 := (appendFn_of_lt _ _ (by omega)).trans (by simp [nestedFn])
  have φ1 : φ 1 = 0 := (appendFn_of_lt _ _ (by omega)).trans (by simp [nestedFn])
  have φ2 : φ 2 = 2 + γ 0 := appendFn_of_le_of_lt _ _ le_rfl (by omega)
  funext q
  rw [contractFn, erasePair_apply]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [skipN_of_lt (by omega), splice_of_ne _ (by omega) (by omega), φ0,
      rejoin_of_eq_left _ rfl, φ2, unskipN_of_le (by omega)]
    omega
  rw [skipN_of_le hq, splice_of_ne _ (by omega) (by omega)]
  by_cases hqL : q < L
  · have := hlt q hqL
    have φq : φ (q + 2) = 2 + γ q :=
      (appendFn_of_le_of_lt _ _ (by omega) (by omega)).trans (by rw [Nat.add_sub_cancel])
    rw [φq]
    by_cases h0 : γ q = 0
    · rw [h0, rejoin_of_eq_right _ rfl, φ1, unskipN_of_lt (by omega)]
    · rw [rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
      omega
  · have φq : φ (q + 2) = q + 2 := appendFn_of_le _ _ (by omega)
    rw [φq, rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega), hle q (by omega)]
    omega

/-- The partner function of `id 1 ⊗ (D ⊗ id 1)`, for `D : 0 → a` nested cups. -/
private def cupSurroundFn (a q : ℕ) : ℕ :=
  if q = 0 then a + 3 else if q = 1 then 2 else if q = 2 then 1
  else if q < a + 3 then a + 5 - q else if q = a + 3 then 0 else q

private theorem contractFn_zero_cupSurroundFn (a : ℕ) :
    contractFn 0 (cupSurroundFn a) = nestedFn (a + 2) := by
  funext q
  rw [contractFn, erasePair_apply, skipN_of_le (Nat.zero_le q),
    splice_of_ne _ (by omega) (by omega)]
  have s0 : cupSurroundFn a 0 = a + 3 := by simp [cupSurroundFn]
  have s1 : cupSurroundFn a 1 = 2 := by simp [cupSurroundFn]
  simp only [rejoin, s0, s1, unskipN]
  simp only [cupSurroundFn, nestedFn]
  split_ifs <;> first | omega | contradiction

/-- A cup glued below `id 1 ⊗ (D ⊗ id 1)`, for `D` nested cups on `a` points, gives nested cups
on `a + 2` points. -/
private theorem cup_surround {a : ℕ} (D : TLDiagram 0 a) (hD : pv D.matching = nestedFn a)
    (hc : D.circles = 0) :
    pv (cup.comp ((id 1).tensor (D.tensor (id 1)))).matching = nestedFn (a + 2) ∧
      (cup.comp ((id 1).tensor (D.tensor (id 1)))).circles = 0 := by
  have hG : pv ((id 1).tensor (D.tensor (id 1))).matching = cupSurroundFn a := by
    rw [pv_matching_tensor, pv_matching_tensor, matching_id, pv_nested_eq, hD]
    funext q
    simp only [insFn, ins, cupSurroundFn, nestedFn]
    split_ifs <;> omega
  have hB := contractFn_one_appendFn_cup (L := 1 + (0 + 1) + (1 + (a + 1))) (cupSurroundFn a)
    (by omega) (fun q hq => by simp only [cupSurroundFn]; split_ifs <;> omega)
    (fun q hq => by simp only [cupSurroundFn]; split_ifs <;> omega)
  constructor
  · rw [matching_comp, pv_glueMiddle, pv_append_eq, hG, pv_cup_eq]
    simp only [glueFn, Nat.zero_add] at hB ⊢
    rw [hB, contractFn_zero_cupSurroundFn]
  · rw [circles_comp, circles_tensor, circles_tensor, hc, circles_id, circles_cup,
      glueMiddleCircles_eq, pv_append_eq, hG, pv_cup_eq]
    simp only [glueCircles, Nat.zero_add] at hB ⊢
    rw [hB]
    simp [circleInd, appendFn, cupSurroundFn, nestedFn]

/-! #### A cap around nested caps -/

/-- Joining the last point of a matching with partner function `γ` on `c + 1` points to the first
point of a cap juxtaposed after it gives back `γ`. -/
private theorem contractFn_appendFn_cap {c : ℕ} (γ : ℕ → ℕ) (hlt : ∀ q < c + 1, γ q < c + 1)
    (hle : ∀ q, c + 1 ≤ q → γ q = q) (hc : γ c ≠ c) :
    contractFn c (appendFn (c + 1) 2 γ (nestedFn 2)) = γ := by
  set φ := appendFn (c + 1) 2 γ (nestedFn 2)
  have φc : φ c = γ c := appendFn_of_lt _ _ (by omega)
  have φc1 : φ (c + 1) = c + 2 :=
    (appendFn_of_le_of_lt _ _ le_rfl (by omega)).trans (by simp [nestedFn])
  have hγc := hlt c (by omega)
  funext q
  rw [contractFn, erasePair_apply]
  by_cases hq : q < c
  · have := hlt q (by omega)
    have φq : φ q = γ q := appendFn_of_lt _ _ (by omega)
    rw [skipN_of_lt hq, splice_of_ne _ (by omega) (by omega), φq]
    by_cases h : γ q = c
    · rw [rejoin_of_eq_left _ h, φc1, unskipN_of_le (by omega), h]
      omega
    · rw [rejoin_of_ne _ h (by omega), unskipN_of_lt (by omega)]
  · rw [skipN_of_le (by omega)]
    by_cases hq' : q = c
    · subst hq'
      have φq : φ (q + 2) = q + 1 :=
        (appendFn_of_le_of_lt _ _ (by omega) (by omega)).trans (by simp [nestedFn])
      rw [splice_of_ne _ (by omega) (by omega), φq, rejoin_of_eq_right _ rfl, φc,
        unskipN_of_lt (by omega)]
    · have φq : φ (q + 2) = q + 2 := appendFn_of_le _ _ (by omega)
      rw [splice_of_ne _ (by omega) (by omega), φq, rejoin_of_ne _ (by omega) (by omega),
        unskipN_of_le (by omega), hle q (by omega)]
      omega

/-- The partner function of `id 1 ⊗ (D ⊗ id 1)`, for `D : a → 0` nested caps. -/
private def capSurroundFn (a q : ℕ) : ℕ :=
  if q = 0 then a + 3 else if q ≤ a then a + 1 - q else if q = a + 1 then a + 2
  else if q = a + 2 then a + 1 else if q = a + 3 then 0 else q

private theorem contractFn_capSurroundFn (a : ℕ) :
    contractFn (a + 2) (capSurroundFn a) = nestedFn (a + 2) := by
  have s2 : capSurroundFn a (a + 2) = a + 1 := by simp [capSurroundFn]
  have s3 : capSurroundFn a (a + 3) = 0 := by simp [capSurroundFn]
  funext q
  rw [contractFn, erasePair_apply, nestedFn]
  by_cases hq : q < a + 2
  · rw [skipN_of_lt hq, splice_of_ne _ (by omega) (by omega), ite_eq_left hq]
    by_cases h0 : q = 0
    · subst h0
      rw [show capSurroundFn a 0 = a + 3 by simp [capSurroundFn],
        rejoin_of_eq_right _ rfl, s2, unskipN_of_lt (by omega)]
      omega
    by_cases h1 : q = a + 1
    · subst h1
      rw [show capSurroundFn a (a + 1) = a + 2 by simp [capSurroundFn],
        rejoin_of_eq_left _ rfl, s3, unskipN_of_lt (by omega)]
      omega
    · rw [show capSurroundFn a q = a + 1 - q by unfold capSurroundFn; split_ifs <;> omega,
        rejoin_of_ne _ (by omega) (by omega), unskipN_of_lt (by omega)]
      omega
  · have hs : capSurroundFn a (q + 2) = q + 2 := by
      unfold capSurroundFn
      split_ifs <;> first | omega | contradiction
    rw [skipN_of_le (by omega), splice_of_ne _ (by omega) (by omega), ite_eq_right hq, hs,
      rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
    omega

/-- A cap glued above `id 1 ⊗ (D ⊗ id 1)`, for `D` nested caps on `a` points, gives nested caps
on `a + 2` points. -/
private theorem cap_surround {a : ℕ} (D : TLDiagram a 0) (hD : pv D.matching = nestedFn a)
    (hc : D.circles = 0) :
    pv (((id 1).tensor (D.tensor (id 1))).comp cap).matching = nestedFn (a + 2) ∧
      (((id 1).tensor (D.tensor (id 1))).comp cap).circles = 0 := by
  have hG : pv ((id 1).tensor (D.tensor (id 1))).matching = capSurroundFn a := by
    rw [pv_matching_tensor, pv_matching_tensor, matching_id, pv_nested_eq, hD]
    funext q
    simp only [insFn, ins, capSurroundFn, nestedFn]
    split_ifs <;> omega
  have hB := contractFn_appendFn_cap (c := a + 3) (capSurroundFn a)
    (fun q hq => by simp only [capSurroundFn]; split_ifs <;> omega)
    (fun q hq => by simp only [capSurroundFn]; split_ifs <;> omega)
    (by simp [capSurroundFn])
  have e₁ : 1 + (a + 1) + (1 + (0 + 1)) = a + 3 + 1 := by omega
  have e₂ : 1 + (a + 1) + 1 = a + 3 := by omega
  have e₃ : 1 + (a + 1) + 0 = a + 2 := by omega
  constructor
  · rw [matching_comp, pv_glueMiddle, pv_append_eq, hG, pv_cap_eq]
    simp only [glueFn]
    rw [e₁, e₂, e₃, show 1 + (0 + 1) + 0 = 2 from rfl, hB, contractFn_capSurroundFn]
  · rw [circles_comp, circles_tensor, circles_tensor, hc, circles_id, circles_cap,
      glueMiddleCircles_eq, pv_append_eq, hG, pv_cap_eq]
    simp only [glueCircles, circleInd]
    rw [e₁, e₂, e₃, show 1 + (0 + 1) + 0 = 2 from rfl, hB]
    simp [appendFn, capSurroundFn]

/-! #### A cap inside nested caps -/

/-- The partner function of `id k ⊗ (cap ⊗ id k)`. -/
private def capMiddleFn (k q : ℕ) : ℕ :=
  if q < k then 4 * k + 1 - q else if q = k then k + 1 else if q = k + 1 then k
  else if q < 3 * k + 2 then 4 * k + 3 - q else if q < 4 * k + 2 then 4 * k + 1 - q else q

private theorem capMiddleFn_spec (k r : ℕ) :
    r < k ∧ capMiddleFn k r = 4 * k + 1 - r ∨ r = k ∧ capMiddleFn k r = k + 1 ∨
      r = k + 1 ∧ capMiddleFn k r = k ∨
      k + 2 ≤ r ∧ r < 3 * k + 2 ∧ capMiddleFn k r = 4 * k + 3 - r ∨
      3 * k + 2 ≤ r ∧ r < 4 * k + 2 ∧ capMiddleFn k r = 4 * k + 1 - r ∨
      4 * k + 2 ≤ r ∧ capMiddleFn k r = r := by
  unfold capMiddleFn
  split_ifs <;> omega

private theorem pv_capMiddle (k : ℕ) :
    pv ((id k).tensor (cap.tensor (id k))).matching = capMiddleFn k := by
  rw [pv_matching_tensor, pv_matching_tensor, matching_id, pv_nested_eq, pv_cap_eq]
  funext q
  simp only [insFn, ins, capMiddleFn, nestedFn]
  split_ifs <;> omega

/-- `id (k + 1) ⊗ (cap ⊗ id (k + 1))` is `id 1 ⊗ ((id k ⊗ (cap ⊗ id k)) ⊗ id 1)`, on partner
functions. -/
private theorem pv_surround_capMiddle (k : ℕ) :
    pv ((id 1).tensor (((id k).tensor (cap.tensor (id k))).tensor (id 1))).matching =
      capMiddleFn (k + 1) := by
  rw [pv_matching_tensor, pv_matching_tensor, pv_capMiddle, matching_id, pv_nested_eq]
  funext q
  have hq := capMiddleFn_spec (k + 1) q
  generalize capMiddleFn (k + 1) q = w at hq
  unfold insFn
  by_cases h₁ : q < 1
  · rw [ite_eq_left h₁]
    simp only [ins, nestedFn]
    split_ifs <;> omega
  rw [ite_eq_right h₁]
  by_cases h₂ : q < 1 + (k + (2 + k) + 1 + (k + (0 + k) + 1))
  · rw [ite_eq_left h₂]
    obtain ⟨r, rfl⟩ : ∃ r, q = 1 + r := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel_left]
    have hr := capMiddleFn_spec k r
    have hr' := capMiddleFn_spec k (r - (1 + 1))
    generalize capMiddleFn k r = v at hr
    generalize capMiddleFn k (r - (1 + 1)) = v' at hr'
    simp only [ins, nestedFn]
    split_ifs <;> omega
  · rw [ite_eq_right h₂]
    simp only [ins, nestedFn]
    split_ifs <;> omega

/-- Inserting a cap in the middle of `k` nested caps gives `k + 1` nested caps. The induction
step peels off the outermost cap with the interchange law and `cap_surround`. -/
private theorem cap_middle : ∀ (k : ℕ) (D : TLDiagram (k + (0 + k)) 0),
    pv D.matching = nestedFn (k + (0 + k)) → D.circles = 0 →
    pv (((id k).tensor (cap.tensor (id k))).comp D).matching = nestedFn (k + (2 + k)) ∧
      (((id k).tensor (cap.tensor (id k))).comp D).circles = 0
  | 0, D, _, hc => by
    have hD : D = id 0 :=
      TLDiagram.ext (Subsingleton.elim (α := PlanarMatching 0) _ _) (hc.trans (circles_id 0).symm)
    subst hD
    rw [comp_id, pv_capMiddle, circles_tensor, circles_tensor, circles_cap, circles_id]
    refine ⟨?_, rfl⟩
    funext q
    simp only [capMiddleFn, nestedFn]
    split_ifs <;> omega
  | k + 1, D, hD, hc => by
    set E : TLDiagram (k + (0 + k)) 0 := ⟨PlanarMatching.cast (by omega) (nested k), 0⟩
    have hE : pv E.matching = nestedFn (k + (0 + k)) := by
      rw [pv_cast_eq, pv_nested_eq, show k + (0 + k) = k + k by omega]
    obtain ⟨hY, hYc⟩ := cap_surround E hE rfl
    obtain ⟨hM, hMc⟩ := cap_middle k E hE rfl
    obtain ⟨hZ, hZc⟩ := cap_surround _ hM hMc
    have hD' := eq_cast_of_pv (show 1 + (k + (0 + k) + 1) + 0 = k + 1 + (0 + (k + 1)) by omega)
      rfl (f := ((id 1).tensor (E.tensor (id 1))).comp cap) (g := D)
      (by rw [hY, hD, show k + (0 + k) + 2 = k + 1 + (0 + (k + 1)) by omega]) (by rw [hYc, hc])
    have hA' := eq_cast_of_pv (show 1 + (k + (2 + k) + 1) = k + 1 + (2 + (k + 1)) by omega)
      (show 1 + (k + (0 + k) + 1) = k + 1 + (0 + (k + 1)) by omega)
      (f := (id 1).tensor (((id k).tensor (cap.tensor (id k))).tensor (id 1)))
      (g := (id (k + 1)).tensor (cap.tensor (id (k + 1))))
      (by rw [pv_surround_capMiddle, pv_capMiddle]) (by simp)
    rw [hD', hA', cast_comp_cast, ← comp_assoc, tensor_comp_tensor, tensor_comp_tensor, comp_id,
      matching_cast, pv_cast_eq, circles_cast]
    exact ⟨by rw [hZ]; congr 1; omega, hZc⟩

end TLDiagram

namespace TLDiagCat

/-- The generating self-duality: the single boundary point `of 1` is dual to itself, with the cup
as coevaluation and the cap as evaluation. This is the instance at `of 1`, see `coevaluation_one`
and `evaluation_one`. -/
@[instance_reducible]
def exactPairingOne : ExactPairing (of 1) (of 1) where
  coevaluation' := cup
  evaluation' := cap
  coevaluation_evaluation' := hom_ext <| TLDiagram.ext
    (PlanarMatching.ext fun a => Fin.ext (by revert a; decide +kernel)) (by decide +kernel)
  evaluation_coevaluation' := hom_ext <| TLDiagram.ext
    (PlanarMatching.ext fun a => Fin.ext (by revert a; decide +kernel)) (by decide +kernel)

/-- The self-duality of `of n`, by recursion on `n`: the unit's for `n = 0`, the cup and cap for
`n = 1`, and for `n + 2` the tensor product of those of `of 1` and `of (n + 1)`, transported
along `of (n + 2) = of 1 ⊗ of (n + 1)`. -/
@[instance_reducible]
def exactPairingOf : (n : ℕ) → ExactPairing (of n) (of n)
  | 0 => exactPairingUnit
  | 1 => exactPairingOne
  | n + 2 =>
    letI := exactPairingOne
    letI := exactPairingOf (n + 1)
    exactPairingCongrLeft (X := of (n + 2)) (X' := of 1 ⊗ of (n + 1)) (Y := of (n + 1) ⊗ of 1)
      (eqToIso (TLDiagCat.ext (Nat.add_comm 1 (n + 1)).symm))

/-- **Every object of the Temperley–Lieb diagram category is self-dual.** The coevaluation and
evaluation of the generating object `of 1` are the cup and the cap (`coevaluation_one`,
`evaluation_one`), and those of `of (n + 2)` are built from those of `of 1` and `of (n + 1)`
(`coevaluation_add_two`, `evaluation_add_two`). -/
instance instExactPairing (X : TLDiagCat) : ExactPairing X X :=
  exactPairingOf X.as

/-- The coevaluation of the generating object is the cup. -/
@[simp]
theorem coevaluation_one : η_ (of 1) (of 1) = cup := (rfl)

/-- The evaluation of the generating object is the cap. -/
@[simp]
theorem evaluation_one : ε_ (of 1) (of 1) = cap := (rfl)

/-- The coevaluation of the empty boundary is its identity. -/
@[simp]
theorem coevaluation_zero : η_ (of 0) (of 0) = 𝟙 (of 0) := (rfl)

/-- The evaluation of the empty boundary is its identity. -/
@[simp]
theorem evaluation_zero : ε_ (of 0) (of 0) = 𝟙 (of 0) := (rfl)

/-- The coevaluation of `of (n + 2)` is that of the tensor product of the self-dualities of `of 1`
and `of (n + 1)`, followed by the identification `of 1 ⊗ of (n + 1) = of (n + 2)`. Mathlib's
`CategoryTheory.ExactPairing.tensor_coevaluation` expands the first factor: it nests the
coevaluation of `of (n + 1)` inside the cup. -/
theorem coevaluation_add_two (n : ℕ) :
    η_ (of (n + 2)) (of (n + 2)) = η_ (of 1 ⊗ of (n + 1)) (of (n + 1) ⊗ of 1) ≫
      eqToHom (TLDiagCat.ext (Nat.add_comm 1 (n + 1))) ▷ of (n + 2) := (rfl)

/-- The evaluation of `of (n + 2)` is the identification `of (n + 2) = of 1 ⊗ of (n + 1)`
followed by the evaluation of the tensor product of the self-dualities of `of 1` and
`of (n + 1)`. Mathlib's `CategoryTheory.ExactPairing.tensor_evaluation` expands the second
factor: it nests the cap inside the evaluation of `of (n + 1)`. -/
theorem evaluation_add_two (n : ℕ) :
    ε_ (of (n + 2)) (of (n + 2)) =
      of (n + 2) ◁ eqToHom (TLDiagCat.ext (Nat.add_comm 1 (n + 1)).symm) ≫
        ε_ (of 1 ⊗ of (n + 1)) (of (n + 1) ⊗ of 1) := (rfl)

/-- **The Temperley–Lieb diagram category is rigid**: every object is its own left and right
dual. -/
instance instRigidCategory : RigidCategory TLDiagCat where
  rightDual X := ⟨X⟩
  leftDual X := ⟨X⟩

/-- Every object is its own right dual. -/
@[simp]
theorem rightDual_eq (X : TLDiagCat) : Xᘁ = X := (rfl)

/-- Every object is its own left dual. -/
@[simp]
theorem leftDual_eq (X : TLDiagCat) : (ᘁX : TLDiagCat) = X := (rfl)

/-- **The coevaluation of an object on `n` points is `n` nested cups**: its diagram joins the
top points `i` and `2 * n - 1 - i`, and has no circle. -/
@[simp]
theorem diagram_coevaluation (X : TLDiagCat) :
    (η_ X X).diagram =
      ⟨PlanarMatching.cast (Nat.zero_add _).symm (PlanarMatching.nested X.as), 0⟩ := by
  suffices h : ∀ n, (η_ (of n) (of n)).diagram =
      ⟨PlanarMatching.cast (Nat.zero_add _).symm (PlanarMatching.nested n), 0⟩ from h X.as
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [coevaluation_zero]
    exact TLDiagram.ext (PlanarMatching.ext fun a => a.elim0) rfl
  | one =>
    rw [coevaluation_one, diagram_cup]
    refine TLDiagram.ext (PlanarMatching.eq_of_pv_eq ?_) rfl
    rw [TLDiagram.pv_cup_eq, PlanarMatching.pv_cast_eq, TLDiagram.pv_nested_eq]
  | more n _ ih =>
    have hD : PlanarMatching.pv (η_ (of (n + 1)) (of (n + 1))).diagram.matching =
        TLDiagram.nestedFn (n + 1 + (n + 1)) := by
      rw [ih]
      exact (PlanarMatching.pv_cast_eq _ _).trans (TLDiagram.pv_nested_eq _)
    obtain ⟨hp, hc⟩ := TLDiagram.cup_surround _ hD (by rw [ih])
    have hη : (η_ (of (n + 2)) (of (n + 2))).diagram =
        TLDiagram.cast rfl (show 1 + (n + 1 + (n + 1) + 1) = n + 2 + (n + 2) by omega)
          (TLDiagram.cup.comp ((TLDiagram.id 1).tensor
            ((η_ (of (n + 1)) (of (n + 1))).diagram.tensor (TLDiagram.id 1)))) := by
      rw [coevaluation_add_two, ExactPairing.tensor_coevaluation]
      simp only [monoidalComp, MonoidalCoherence.refl_iso, MonoidalCoherence.assoc_iso,
        MonoidalCoherence.assoc'_iso, MonoidalCoherence.whiskerLeft_iso,
        MonoidalCoherence.whiskerRight_iso, MonoidalCoherence.right'_iso, Iso.trans_hom,
        Iso.refl_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom]
      simp [associator_hom, associator_inv, rightUnitor_inv]
    rw [hη]
    refine TLDiagram.ext (PlanarMatching.eq_of_pv_eq ?_) ?_
    · rw [TLDiagram.matching_cast, PlanarMatching.pv_cast_eq, hp, PlanarMatching.pv_cast_eq,
        TLDiagram.pv_nested_eq, tensorObj_as, show n + 1 + (n + 1) + 2 = n + 2 + (n + 2) by omega]
    · rw [TLDiagram.circles_cast, hc]

/-- **The evaluation of an object on `n` points is `n` nested caps**: its diagram joins the
bottom points `i` and `2 * n - 1 - i`, and has no circle. -/
@[simp]
theorem diagram_evaluation (X : TLDiagCat) :
    (ε_ X X).diagram =
      ⟨PlanarMatching.cast (Nat.add_zero _).symm (PlanarMatching.nested X.as), 0⟩ := by
  suffices h : ∀ n, (ε_ (of n) (of n)).diagram =
      ⟨PlanarMatching.cast (Nat.add_zero _).symm (PlanarMatching.nested n), 0⟩ from h X.as
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [evaluation_zero]
    exact TLDiagram.ext (PlanarMatching.ext fun a => a.elim0) rfl
  | one =>
    rw [evaluation_one, diagram_cap]
    refine TLDiagram.ext (PlanarMatching.eq_of_pv_eq ?_) rfl
    rw [TLDiagram.pv_cap_eq, PlanarMatching.pv_cast_eq, TLDiagram.pv_nested_eq]
  | more n _ ih =>
    have hD : PlanarMatching.pv (ε_ (of (n + 1)) (of (n + 1))).diagram.matching =
        TLDiagram.nestedFn (n + 1 + (n + 1)) := by
      rw [ih]
      exact (PlanarMatching.pv_cast_eq _ _).trans (TLDiagram.pv_nested_eq _)
    have hc : (ε_ (of (n + 1)) (of (n + 1))).diagram.circles = 0 := by rw [ih]
    have hε : (ε_ (of (n + 2)) (of (n + 2))).diagram =
        TLDiagram.cast (show n + 1 + (2 + (n + 1)) = n + 2 + (n + 2) by omega) rfl
          (((TLDiagram.id (n + 1)).tensor (TLDiagram.cap.tensor (TLDiagram.id (n + 1)))).comp
            (TLDiagram.cast (show n + 1 + (n + 1) = n + 1 + (0 + (n + 1)) by omega) rfl
              (ε_ (of (n + 1)) (of (n + 1))).diagram)) := by
      rw [evaluation_add_two, ExactPairing.tensor_evaluation]
      simp only [monoidalComp, MonoidalCoherence.refl_iso, MonoidalCoherence.assoc_iso,
        MonoidalCoherence.assoc'_iso, MonoidalCoherence.whiskerLeft_iso,
        MonoidalCoherence.whiskerRight_iso, MonoidalCoherence.left_iso, Iso.trans_hom,
        Iso.refl_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom]
      simp [associator_hom, associator_inv, leftUnitor_hom]
    obtain ⟨hp, hc'⟩ := TLDiagram.cap_middle (n + 1)
      (TLDiagram.cast (show n + 1 + (n + 1) = n + 1 + (0 + (n + 1)) by omega) rfl
        (ε_ (of (n + 1)) (of (n + 1))).diagram)
      (by rw [TLDiagram.matching_cast, PlanarMatching.pv_cast_eq, hD,
        show n + 1 + (n + 1) = n + 1 + (0 + (n + 1)) by omega])
      (by rw [TLDiagram.circles_cast, hc])
    rw [hε]
    refine TLDiagram.ext (PlanarMatching.eq_of_pv_eq ?_) ?_
    · rw [TLDiagram.matching_cast, PlanarMatching.pv_cast_eq, hp, PlanarMatching.pv_cast_eq,
        TLDiagram.pv_nested_eq, show n + 1 + (2 + (n + 1)) = n + 2 + (n + 2) by omega]
    · rw [TLDiagram.circles_cast, hc']

end TLDiagCat

/-- The coevaluation of two boundary points is the two nested cups: its matching is the nested
matching, pairing the top points `i` and `3 - i`, and it has no circle. -/
example : (η_ (TLDiagCat.of 2) (TLDiagCat.of 2)).diagram =
    ⟨PlanarMatching.cast (Nat.zero_add 4).symm (PlanarMatching.nested 2), 0⟩ :=
  TLDiagCat.diagram_coevaluation (TLDiagCat.of 2)

/-- The evaluation of two boundary points is the two nested caps. -/
example : (ε_ (TLDiagCat.of 2) (TLDiagCat.of 2)).diagram =
    ⟨PlanarMatching.cast (Nat.add_zero 4).symm (PlanarMatching.nested 2), 0⟩ :=
  TLDiagCat.diagram_evaluation (TLDiagCat.of 2)

/-- Closing the identity of two boundary points, coevaluation followed by evaluation, gives two
circles. -/
example : η_ (TLDiagCat.of 2) (TLDiagCat.of 2) ≫ ε_ (TLDiagCat.of 2) (TLDiagCat.of 2) =
    TLDiagCat.circle ≫ TLDiagCat.circle :=
  TLDiagCat.hom_ext <| TLDiagram.ext (PlanarMatching.ext fun a => a.elim0) (by decide +kernel)

end TauCeti
