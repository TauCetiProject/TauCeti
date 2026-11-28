/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Tensor
import all TauCeti.Combinatorics.PlanarMatching.Glue
import all TauCeti.Combinatorics.PlanarMatching.Associativity
import all TauCeti.Combinatorics.PlanarMatching.Tensor
import TauCeti.Data.Fin.Basic

/-!
# Diagram-level duality, reflections, and nested cups and caps

This file develops the diagram-level operations underlying the rigid and pivotal structure of the
Temperley–Lieb diagram category:

* Vertical reflection preserves horizontal tensoring (`TauCeti.TLDiagram.verticalReflect_tensor`),
  while horizontal reflection reverses horizontal tensoring (`TauCeti.TLDiagram.reflect_tensor`).
* The **nested cup** `TauCeti.TLDiagram.nestedCup n : TLDiagram 0 (n + n)` and **nested cap**
  `TauCeti.TLDiagram.nestedCap n : TLDiagram (n + n) 0` bend `n` strands around in nested arcs.
  Composing them closes `n` circles (`TauCeti.TLDiagram.nestedCup_comp_nestedCap`), and they
  satisfy the left and right zigzag identities (`TauCeti.TLDiagram.zigzag_left`,
  `TauCeti.TLDiagram.zigzag_right`) as well as the nesting identity
  `TauCeti.TLDiagram.id_tensor_nestedCap_comp_nestedCap`.
* Bending the bottom of a diagram `f : n → m` up on the right and its top down on the left yields
  its 180-degree rotation `verticalReflect n m (reflect n m f)` (`TauCeti.TLDiagram.rightMate_eq`).

## Main definitions

* `TauCeti.TLDiagram.nestedCup`: the nested cup `0 → n + n` on `n` strands.
* `TauCeti.TLDiagram.nestedCap`: the nested cap `n + n → 0` on `n` strands.

## Main results

* `TauCeti.TLDiagram.verticalReflect_tensor`, `TauCeti.TLDiagram.reflect_tensor`: compatibility of
  vertical and horizontal reflections with horizontal tensoring.
* `TauCeti.TLDiagram.nestedCup_comp_nestedCap`: composing the nested cup and cap produces `n`
  closed circles.
* `TauCeti.TLDiagram.nestedCup_comp_tensor_id`, `TauCeti.TLDiagram.tensor_id_comp_nestedCap`,
  `TauCeti.TLDiagram.nestedCup_comp_id_tensor`: bending a diagram's bottom or top boundary.
* `TauCeti.TLDiagram.rightMate_eq`, `TauCeti.TLDiagram.zigzag_right`,
  `TauCeti.TLDiagram.zigzag_left`, `TauCeti.TLDiagram.id_tensor_nestedCap_comp_nestedCap`: the
  diagram-level mate, zigzag, and nested-cap identities.

## Implementation notes

As in `TauCeti.Combinatorics.PlanarMatching.Associativity` and
`TauCeti.Combinatorics.PlanarMatching.Tensor`, the gluing computations work on the `ℕ → ℕ` partner
functions `pv` and the contraction recursion `glueFn` / `glueCircles`, using `import all` on
`Glue`, `Associativity`, and `Tensor`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open Equiv

namespace TauCeti

/-! ### Partner-function helpers for reflection and nested blocks -/

namespace PlanarMatching

section DualityHelpers

/-- Reversing a partner function on `0, …, K - 1`. -/
private def revFn (K : ℕ) (φ : ℕ → ℕ) (q : ℕ) : ℕ :=
  if q < K then K - 1 - φ (K - 1 - q) else q

private theorem pv_reflect_eq {K : ℕ} (x : PlanarMatching K) :
    pv (reflect K x) = revFn K (pv x) := by
  funext q
  unfold revFn
  by_cases hq : q < K
  · rw [ite_eq_left hq, pv_of_lt _ hq, pv_of_lt _ (by omega)]
    have h := congrArg Fin.val (reflect_apply_val_apply x ⟨K - 1 - q, by omega⟩)
    simp only [Fin.val_rev] at h
    have hrev : Fin.rev (⟨K - 1 - q, by omega⟩ : Fin K) = ⟨q, hq⟩ :=
      Fin.ext (by simp only [Fin.val_rev]; omega)
    rw [hrev] at h
    omega
  · rw [ite_eq_right hq, pv_of_le _ (by omega)]

private theorem pv_rotate_eq {K : ℕ} (x : PlanarMatching K) (hK : 0 < K) {q : ℕ} (hq : q < K) :
    pv (rotate K x) q = (pv x ((q + K - 1) % K) + 1) % K := by
  rw [pv_of_lt _ hq, pv_of_lt _ (Nat.mod_lt _ hK)]
  have hpre : finRotate K ⟨(q + K - 1) % K, Nat.mod_lt _ hK⟩ = ⟨q, hq⟩ := by
    apply Fin.ext
    rw [Fin.coe_finRotate_eq_ite]
    by_cases hq0 : q = 0
    · subst hq0
      have hm : (0 + K - 1) % K = K - 1 := by rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      simp only [hm]; split_ifs <;> omega
    · have hm : (q + K - 1) % K = q - 1 := by
        rw [show q + K - 1 = (q - 1) + K by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      simp only [hm]; split_ifs <;> omega
  have h := congrArg Fin.val (rotate_apply_val_apply x ⟨(q + K - 1) % K, Nat.mod_lt _ hK⟩)
  rw [hpre, Fin.coe_finRotate_eq_ite] at h
  rw [h]
  set v := (x.val.val ⟨(q + K - 1) % K, Nat.mod_lt _ hK⟩ : ℕ)
  have hv : v < K := Fin.isLt _
  split_ifs with hv1
  · rw [hv1, Nat.mod_self]
  · exact (Nat.mod_eq_of_lt (by omega)).symm

private theorem pv_rotate_symm_eq {K : ℕ} (x : PlanarMatching K) (hK : 0 < K) {q : ℕ}
    (hq : q < K) :
    pv ((rotate K).symm x) q = (pv x ((q + 1) % K) + K - 1) % K := by
  have h := pv_rotate_eq ((rotate K).symm x) hK (q := (q + 1) % K) (Nat.mod_lt _ hK)
  rw [Equiv.apply_symm_apply] at h
  have hq' : ((q + 1) % K + K - 1) % K = q := by
    by_cases hq1 : q + 1 = K
    · rw [hq1, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega : q + 1 < K), show q + 1 + K - 1 = q + K by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq]
  rw [hq'] at h
  have hv : pv ((rotate K).symm x) q < K := pv_lt _ hq
  rw [h]
  by_cases hv1 : pv ((rotate K).symm x) q + 1 = K
  · rw [hv1, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega : pv ((rotate K).symm x) q + 1 < K),
      show pv ((rotate K).symm x) q + 1 + K - 1 = pv ((rotate K).symm x) q + K by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hv]

private theorem rejoin_revFn {K a w : ℕ} (x : PlanarMatching K) (ha : a + 1 < K) (hw : w < K) :
    rejoin (revFn K (pv x)) (K - 2 - a) (K - 1 - w) = K - 1 - rejoin (pv x) a w := by
  have e₁ : revFn K (pv x) (K - 2 - a) = K - 1 - pv x (a + 1) := by
    simp only [revFn, show K - 2 - a < K by omega, ite_true,
      show K - 1 - (K - 2 - a) = a + 1 by omega]
  have e₂ : revFn K (pv x) (K - 2 - a + 1) = K - 1 - pv x a := by
    simp only [revFn, show K - 2 - a + 1 < K by omega, ite_true,
      show K - 1 - (K - 2 - a + 1) = a by omega]
  unfold rejoin
  rw [e₁, e₂]
  split_ifs <;> omega

private theorem unskipN_rev {K a v : ℕ} (ha : a + 1 < K) (hv : v < K) (hv₁ : v ≠ a)
    (hv₂ : v ≠ a + 1) :
    unskipN (K - 2 - a) (K - 1 - v) = K - 2 - 1 - unskipN a v := by
  simp only [unskipN]
  split_ifs <;> omega

private theorem contractFn_revFn {K : ℕ} (x : PlanarMatching K) {a : ℕ} (ha : a + 1 < K) :
    contractFn (K - 2 - a) (revFn K (pv x)) = revFn (K - 2) (contractFn a (pv x)) := by
  funext q
  by_cases hq : q < K - 2
  · have hsk : K - 1 - skipN (K - 2 - a) q = skipN a (K - 2 - 1 - q) := by
      simp only [skipN]; split_ifs <;> omega
    have hsk_lt : skipN (K - 2 - a) q < K := by simp only [skipN]; split_ifs <;> omega
    have hsk_lt' : skipN a (K - 2 - 1 - q) < K := by simp only [skipN]; split_ifs <;> omega
    have hne₁ : skipN (K - 2 - a) q ≠ K - 2 - a ∧ skipN (K - 2 - a) q ≠ K - 2 - a + 1 := by
      simp only [skipN]; split_ifs <;> omega
    have hne₂ : skipN a (K - 2 - 1 - q) ≠ a ∧ skipN a (K - 2 - 1 - q) ≠ a + 1 := by
      simp only [skipN]; split_ifs <;> omega
    have hxv := pv_lt x hsk_lt'
    have hsp := splice_ne (pv_pv_eq x) (pv_ne x (by omega : a < K))
      (pv_ne x (by omega : a + 1 < K)) hne₂.1 hne₂.2
    rw [splice_of_ne _ hne₂.1 hne₂.2] at hsp
    have hrejoin_lt : rejoin (pv x) a (pv x (skipN a (K - 2 - 1 - q))) < K := by
      have hxa := pv_lt x (by omega : a < K)
      have hxa' := pv_lt x (by omega : a + 1 < K)
      unfold rejoin; split_ifs <;> omega
    simp only [contractFn, erasePair_apply, splice_of_ne _ hne₁.1 hne₁.2]
    rw [show revFn K (pv x) (skipN (K - 2 - a) q) = K - 1 - pv x (skipN a (K - 2 - 1 - q)) by
        simp only [revFn, hsk_lt, ite_true, hsk],
      rejoin_revFn x ha hxv, unskipN_rev ha hrejoin_lt hsp.1 hsp.2]
    simp only [revFn, hq, ite_true, erasePair_apply, splice_of_ne _ hne₂.1 hne₂.2]
  · have hsk : skipN (K - 2 - a) q = q + 2 := skipN_of_le (by omega)
    have hne₁ : q + 2 ≠ K - 2 - a ∧ q + 2 ≠ K - 2 - a + 1 := by omega
    simp only [contractFn, erasePair_apply, hsk, splice_of_ne _ hne₁.1 hne₁.2]
    rw [show revFn K (pv x) (q + 2) = q + 2 by simp [revFn, show ¬q + 2 < K by omega],
      rejoin_of_ne _ (by omega) (by omega), unskipN_of_le (by omega)]
    simp only [revFn, hq, ite_false]
    omega

private theorem circleInd_revFn {K : ℕ} (x : PlanarMatching K) {a : ℕ} (ha : a + 1 < K) :
    circleInd (K - 2 - a) (revFn K (pv x)) = circleInd a (pv x) := by
  have hxa := pv_lt x (by omega : a < K)
  have hxa' := pv_lt x (by omega : a + 1 < K)
  have hiff : pv x (a + 1) = a ↔ pv x a = a + 1 := by
    constructor <;> intro h
    · calc pv x a = pv x (pv x (a + 1)) := by rw [h]
        _ = a + 1 := pv_pv x (by omega)
    · calc pv x (a + 1) = pv x (pv x a) := by rw [h]
        _ = a := pv_pv x (by omega)
  simp only [circleInd, revFn, show K - 2 - a < K by omega, ite_true,
    show K - 1 - (K - 2 - a) = a + 1 by omega]
  split_ifs <;> omega

private theorem glueFn_revFn {n p : ℕ} :
    ∀ (m : ℕ) (x : PlanarMatching (n + m + (m + p))),
      glueFn p m (revFn (n + m + (m + p)) (pv x)) = revFn (n + p) (glueFn n m (pv x)) ∧
      glueCircles p m (revFn (n + m + (m + p)) (pv x)) = glueCircles n m (pv x)
  | 0, x => by simp [glueFn, glueCircles]
  | m + 1, x => by
    obtain ⟨y, hy⟩ := exists_pv_eq_contractFn x (a := n + m) (by omega)
    have hK : n + (m + 1) + (m + 1 + p) - 2 = n + m + (m + p) := by omega
    have ha : n + (m + 1) + (m + 1 + p) - 2 - (n + m) = p + m := by omega
    have ha' : n + m + (m + p) - (n + m) = p + m := by omega
    have hy' : pv (cast hK y) = contractFn (n + m) (pv x) := by rw [pv_cast_eq, hy]
    obtain ⟨ih₁, ih₂⟩ := glueFn_revFn m (cast hK y)
    have hci := circleInd_revFn x (a := n + m) (by omega)
    rw [ha] at hci
    simp only [glueFn, glueCircles]
    rw [← ha, contractFn_revFn x (by omega), hK, ← hy', ih₁, ih₂, ha', hci]
    exact ⟨rfl, rfl⟩

/-! ### Nested-block contractions and rotations -/

private theorem glueFn_nested_append {n p : ℕ} (x : PlanarMatching (n + p)) :
    glueFn n n (pv ((nested n).append x)) = pv x ∧
    glueCircles n n (pv ((nested n).append x)) = 0 := by
  refine ⟨?_, ?_⟩
  · have h := congrArg pv (glueMiddle_nested_append x)
    rwa [pv_glueMiddle] at h
  · have h := glueMiddleCircles_nested_append x
    rwa [glueMiddleCircles_eq] at h

private theorem glueFn_append_nested {n p : ℕ} (x : PlanarMatching (n + p)) :
    glueFn n p (pv (x.append (nested p))) = pv x ∧
    glueCircles n p (pv (x.append (nested p))) = 0 := by
  refine ⟨?_, ?_⟩
  · have h := congrArg pv (glueMiddle_append_nested x)
    rwa [pv_glueMiddle] at h
  · have h := glueMiddleCircles_append_nested x
    rwa [glueMiddleCircles_eq] at h

private theorem glueFn_insFn_nested_right {n m : ℕ} (f : PlanarMatching (n + m)) :
    glueFn 0 n (insFn n (n + n) (pv f) (pv (nested n))) = pv f ∧
    glueCircles 0 n (insFn n (n + n) (pv f) (pv (nested n))) = 0 := by
  let x : PlanarMatching (0 + n + (n + (n + m))) :=
    cast (by omega) ((cast (by omega) f : PlanarMatching (n + m)).insertBlock (nested n))
  have hpx : pv x = insFn n (n + n) (pv f) (pv (nested n)) := by
    rw [pv_cast_eq, pv_insertBlock, pv_cast_eq]
  have hnis : IsNestedInsert x (cast (Nat.zero_add (n + m)).symm f) (0 + n) n := by
    refine ⟨by omega, by omega, fun s hs => ?_, fun q _hq => ?_⟩
    · rw [hpx, show 0 + n + s = n + s by omega, insFn_add _ _ (by omega), pv_nested _ (by omega)]
      omega
    · rw [hpx, Nat.zero_add, show 2 * n = n + n by omega, insFn_ins, pv_cast_eq]
  have h := glueMiddle_of_isNestedInsert_left (n := 0) (p := n + m)
    (f := cast (Nat.zero_add (n + m)).symm f) n x hnis
  refine ⟨?_, ?_⟩
  · have h₁ := congrArg pv h.1
    rwa [pv_glueMiddle, hpx, pv_cast_eq] at h₁
  · have h₂ := h.2
    rwa [glueMiddleCircles_eq, hpx] at h₂

private theorem insFn_of_lt_pv_nested {j K q : ℕ} (hq : q < j) :
    ins j K (pv (nested j) q) = j + j - 1 - q + K := by
  rw [pv_nested j (by omega), ins_of_le (by omega)]

private theorem insFn_of_gt_pv_nested {j K q : ℕ} (hq₁ : j + K ≤ q) (hq₂ : q < j + j + K) :
    ins j K (pv (nested j) (q - K)) = j + j - 1 - (q - K) := by
  rw [pv_nested j (by omega), ins_of_lt (by omega)]

private theorem insFn_of_ge_pv_nested {j K q : ℕ} (hq : j + j + K ≤ q) :
    ins j K (pv (nested j) (q - K)) = q := by
  rw [pv_of_le (nested j) (by omega), ins_of_le (by omega)]
  omega

/-- Contracting one pair on the left of `nested (j + 1)` wrapped around a nonempty matching `g`
rotates `g` backwards by one step and closes no circle. -/
private theorem contractFn_insert_nested_left {K : ℕ} (hK : 0 < K) (j : ℕ) (g : PlanarMatching K) :
    contractFn j (insFn (j + 1) K (pv (nested (j + 1))) (pv g)) =
      insFn j K (pv (nested j)) (pv ((rotate K).symm g)) ∧
    circleInd j (insFn (j + 1) K (pv (nested (j + 1))) (pv g)) = 0 := by
  have h1 : insFn (j + 1) K (pv (nested (j + 1))) (pv g) j = j + 1 + K := by
    simp only [insFn, show j < j + 1 by omega, ↓reduceIte,
      pv_nested _ (by omega : j < j + 1 + (j + 1))]
    rw [ins_of_le (by omega)]
    omega
  have h2 : insFn (j + 1) K (pv (nested (j + 1))) (pv g) (j + 1) = j + 1 + pv g 0 := by
    simp only [insFn, show ¬j + 1 < j + 1 by omega, show j + 1 < j + 1 + K by omega, ↓reduceIte,
      Nat.sub_self]
  refine ⟨?_, by simp only [circleInd, h1]; split_ifs <;> omega⟩
  funext q
  have hs : skipN j q ≠ j ∧ skipN j q ≠ j + 1 := by simp only [skipN]; split_ifs <;> omega
  simp only [contractFn, erasePair_apply, splice_of_ne _ hs.1 hs.2]
  by_cases hq₁ : q < j
  · rw [skipN_of_lt hq₁]
    simp only [insFn, show q < j + 1 by omega, hq₁, ↓reduceIte,
      insFn_of_lt_pv_nested (by omega : q < j + 1), insFn_of_lt_pv_nested hq₁]
    unfold rejoin
    rw [h1, h2]
    simp only [unskipN]
    split_ifs <;> omega
  by_cases hq₂ : q < j + K
  · have hqK : q - j < K := by omega
    rw [skipN_of_le (by omega)]
    simp only [insFn, show ¬q + 2 < j + 1 by omega, show ¬q < j by omega, hq₂, ↓reduceIte,
      pv_rotate_symm_eq g hK hqK]
    by_cases hlast : q - j + 1 = K
    · have hqeq : q + 2 = j + 1 + K := by omega
      have hgm : (q - j + 1) % K = 0 := by rw [hlast, Nat.mod_self]
      have hgv0 := pv_lt g hK
      have hgv0' := pv_ne g hK
      rw [hqeq, ite_eq_right (by omega : ¬j + 1 + K < j + 1 + K),
        show j + 1 + K - K = j + 1 by omega, pv_nested _ (by omega : j + 1 < j + 1 + (j + 1)),
        ins_of_lt (by omega), hgm]
      unfold rejoin
      rw [h1, h2]
      have hmod : (pv g 0 + K - 1) % K = pv g 0 - 1 := by
        rw [show pv g 0 + K - 1 = (pv g 0 - 1) + K by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      simp only [unskipN]
      split_ifs <;> omega
    · have hgm : (q - j + 1) % K = q - j + 1 := Nat.mod_eq_of_lt (by omega)
      have hsub : q + 2 - (j + 1) = q - j + 1 := by omega
      have hgv := pv_lt g (by omega : q - j + 1 < K)
      rw [ite_eq_left (by omega : q + 2 < j + 1 + K), hsub, hgm]
      unfold rejoin
      rw [h1, h2]
      by_cases hv0 : pv g (q - j + 1) = 0
      · rw [hv0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
        simp only [unskipN]; split_ifs <;> omega
      · have hmod : (pv g (q - j + 1) + K - 1) % K = pv g (q - j + 1) - 1 := by
          rw [show pv g (q - j + 1) + K - 1 = (pv g (q - j + 1) - 1) + K by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        simp only [unskipN]; split_ifs <;> omega
  by_cases hq₃ : q < j + j + K
  · have := pv_lt g hK
    rw [skipN_of_le (by omega)]
    simp only [insFn, show ¬q + 2 < j + 1 by omega, show ¬q + 2 < j + 1 + K by omega,
      show ¬q < j by omega, show ¬q < j + K by omega, ↓reduceIte,
      insFn_of_gt_pv_nested (by omega : j + 1 + K ≤ q + 2) (by omega),
      insFn_of_gt_pv_nested (by omega : j + K ≤ q) hq₃]
    unfold rejoin
    rw [h1, h2]
    simp only [unskipN]
    split_ifs <;> omega
  · have := pv_lt g hK
    rw [skipN_of_le (by omega)]
    simp only [insFn, show ¬q + 2 < j + 1 by omega, show ¬q + 2 < j + 1 + K by omega,
      show ¬q < j by omega, show ¬q < j + K by omega, ↓reduceIte,
      insFn_of_ge_pv_nested (by omega : j + 1 + (j + 1) + K ≤ q + 2),
      insFn_of_ge_pv_nested (by omega : j + j + K ≤ q)]
    unfold rejoin
    rw [h1, h2]
    simp only [unskipN]
    split_ifs <;> omega

/-- Contracting `j` pairs on the left of `nested j` wrapped around a nonempty matching `g` rotates
`g` backwards `j` times and closes no circle. -/
private theorem glueFn_insert_nested_left {K : ℕ} (hK : 0 < K) :
    ∀ (j : ℕ) (g : PlanarMatching K),
      glueFn 0 j (insFn j K (pv (nested j)) (pv g)) = pv (((rotate K).symm ^ j) g) ∧
      glueCircles 0 j (insFn j K (pv (nested j)) (pv g)) = 0
  | 0, g => by
    refine ⟨?_, rfl⟩
    funext q
    simp only [glueFn, pow_zero, Perm.one_apply, insFn, Nat.not_lt_zero, Nat.zero_add, ite_false]
    by_cases hq : q < K
    · rw [ite_eq_left hq, Nat.sub_zero]
    · rw [ite_eq_right hq, pv_of_le g (by omega), pv_of_le (nested 0) (Nat.zero_le _),
        ins_of_le (Nat.zero_le _), Nat.sub_add_cancel (by omega)]
  | j + 1, g => by
    obtain ⟨h₁, h₂⟩ := contractFn_insert_nested_left hK j g
    obtain ⟨ih₁, ih₂⟩ := glueFn_insert_nested_left hK j ((rotate K).symm g)
    simp only [glueFn, glueCircles, Nat.zero_add]
    rw [h₁, h₂, ih₁, ih₂, pow_succ, Perm.mul_apply]
    exact ⟨rfl, rfl⟩

/-- Contracting `j` pairs on the right of `nested j` wrapped around a nonempty matching `g` rotates
`g` forwards `j` times and closes no circle. -/
private theorem glueFn_insert_nested_right {K : ℕ} (hK : 0 < K) (j : ℕ) (g : PlanarMatching K) :
    glueFn K j (insFn j K (pv (nested j)) (pv g)) = pv ((rotate K ^ j) g) ∧
    glueCircles K j (insFn j K (pv (nested j)) (pv g)) = 0 := by
  have href : revFn (0 + j + (j + K)) (insFn j K (pv (nested j)) (pv g)) =
      insFn j K (pv (nested j)) (pv (reflect K g)) := by
    funext q
    rw [pv_reflect_eq]
    by_cases h₁ : q < j
    · have hsub1 : 0 + j + (j + K) - 1 - q ≥ j + K := by omega
      have hsub2 : 0 + j + (j + K) - 1 - q < j + j + K := by omega
      simp only [revFn, show q < 0 + j + (j + K) by omega, ite_true, insFn,
        show ¬0 + j + (j + K) - 1 - q < j by omega,
        show ¬0 + j + (j + K) - 1 - q < j + K by omega, h₁, ite_false, ite_true]
      rw [insFn_of_gt_pv_nested hsub1 hsub2, insFn_of_lt_pv_nested h₁]
      omega
    by_cases h₂ : q < j + K
    · have hgv := pv_lt g (by omega : K - 1 - (q - j) < K)
      have hsub : 0 + j + (j + K) - 1 - q - j = K - 1 - (q - j) := by omega
      simp only [revFn, show q < 0 + j + (j + K) by omega, ite_true, insFn,
        show ¬0 + j + (j + K) - 1 - q < j by omega,
        show 0 + j + (j + K) - 1 - q < j + K by omega, h₁, h₂, ite_false, ite_true, hsub,
        show q - j < K by omega]
      omega
    by_cases h₃ : q < j + j + K
    · have hsub1 : 0 + j + (j + K) - 1 - q < j := by omega
      simp only [revFn, show q < 0 + j + (j + K) by omega, ite_true, insFn, hsub1,
        h₁, h₂, ite_false, ite_true]
      rw [insFn_of_lt_pv_nested hsub1, insFn_of_gt_pv_nested (by omega) h₃]
      omega
    · have hge : j + j + K ≤ q := by omega
      simp only [revFn, show ¬q < 0 + j + (j + K) by omega, ite_false, insFn, h₁, h₂, ite_false]
      rw [insFn_of_ge_pv_nested hge]
  set x : PlanarMatching (0 + j + (j + K)) :=
    cast (by omega) ((cast (by omega) (nested j) : PlanarMatching (j + j)).insertBlock g)
  have hpx : pv x = insFn j K (pv (nested j)) (pv g) := by
    rw [pv_cast_eq, pv_insertBlock, pv_cast_eq]
  set rx : PlanarMatching (0 + j + (j + K)) := reflect (0 + j + (j + K)) x
  have hrev := glueFn_revFn (n := 0) (p := K) j rx
  have hpv_rx : revFn (0 + j + (j + K)) (pv rx) = pv x := by
    rw [← pv_reflect_eq, reflect_reflect]
  have hpv_rx' : pv rx = insFn j K (pv (nested j)) (pv (reflect K g)) := by
    rw [pv_reflect_eq, hpx, href]
  rw [hpv_rx, hpv_rx', hpx] at hrev
  obtain ⟨hL₁, hL₂⟩ := glueFn_insert_nested_left hK j (reflect K g)
  rw [hL₁, hL₂] at hrev
  refine ⟨?_, hrev.2⟩
  rw [hrev.1, Nat.zero_add, ← pv_reflect_eq]
  have hrot : reflect K (((rotate K).symm ^ j) (reflect K g)) = (rotate K ^ j) g := by
    rw [← Perm.inv_def, inv_pow, ← reflect_rotate_pow, reflect_reflect]
  rw [hrot]

/-- Gluing the two halves of the fully nested matching of `2n` points closes `n` circles. -/
private theorem glueCircles_nested : ∀ n : ℕ, glueCircles 0 n (pv (nested n)) = n
  | 0 => rfl
  | n + 1 => by
    simp only [glueCircles, Nat.zero_add]
    have hc : circleInd n (pv (nested (n + 1))) = 1 := by
      simp only [circleInd, pv_nested (n + 1) (by omega : n < n + 1 + (n + 1))]
      simp
    have hcf : contractFn n (pv (nested (n + 1))) = pv (nested n) := by
      funext q
      simp only [contractFn, erasePair_apply, skipN]
      by_cases hq : q < n
      · rw [ite_eq_left hq, splice_of_ne _ (by omega) (by omega),
          pv_nested (n + 1) (by omega), pv_nested n (by omega),
          rejoin_of_ne _ (by omega) (by omega)]
        simp only [unskipN]; split_ifs <;> omega
      · rw [ite_eq_right hq, splice_of_ne _ (by omega) (by omega)]
        by_cases hq' : q < n + n
        · rw [pv_nested (n + 1) (by omega), pv_nested n hq',
            rejoin_of_ne _ (by omega) (by omega)]
          simp only [unskipN]; split_ifs <;> omega
        · rw [pv_of_le _ (by omega : n + 1 + (n + 1) ≤ q + 2),
            pv_of_le _ (by omega : n + n ≤ q), rejoin_of_ne _ (by omega) (by omega)]
          simp only [unskipN]; split_ifs <;> omega
    rw [hcf, hc, glueCircles_nested n]

private theorem insFn_self_eq_appendFn {k l : ℕ} (x : PlanarMatching k) (y : PlanarMatching l) :
    insFn k l (pv x) (pv y) = appendFn k l (pv x) (pv y) := by
  funext q
  by_cases h₁ : q < k
  · have := pv_lt x h₁
    simp only [insFn, h₁, ite_true, ins_of_lt this, appendFn_of_lt _ _ h₁]
  by_cases h₂ : q < k + l
  · simp only [insFn, h₁, h₂, ite_false, ite_true]
    rw [appendFn_of_le_of_lt _ _ (by omega) h₂]
  · simp only [insFn, h₁, h₂, ite_false]
    rw [appendFn_of_le _ _ (by omega), pv_of_le x (by omega), ins_of_le (by omega)]
    omega

theorem insertBlock_nested_nested (n m : ℕ) :
    (nested n).insertBlock (nested m) = cast (by omega) (nested (n + m)) := by
  apply ext_pv
  intro q hq
  rw [pv_insertBlock, pv_cast]
  by_cases h₁ : q < n
  · have h : q = ins n (m + m) q := (ins_of_lt h₁).symm
    conv_lhs => rw [h]
    rw [insFn_ins, pv_nested _ (by omega : q < n + n), pv_nested (n + m) (by omega),
      ins_of_le (by omega)]
    omega
  by_cases h₂ : q < n + (m + m)
  · rw [show q = n + (q - n) by omega, insFn_add _ _ (by omega),
      pv_nested _ (by omega : q - n < m + m), pv_nested (n + m) (by omega)]
    omega
  · have h : q = ins n (m + m) (q - (m + m)) := by
      rw [ins_of_le (by omega)]; omega
    conv_lhs => rw [h]
    rw [insFn_ins, pv_nested _ (by omega : q - (m + m) < n + n), pv_nested (n + m) (by omega),
      ins_of_lt (by omega)]
    omega

end DualityHelpers

end PlanarMatching

/-! ### Diagram-level casts, reflections, nested cups and caps, mates and zigzags -/

namespace TLDiagram

section CastHelpers

variable {n n' m m' : ℕ}

@[simp]
theorem cast_id (hn : n = n') : cast hn hn (id n) = id n' := by
  subst hn; simp

theorem comp_cast_mid (hm : m = m') (f : TLDiagram n m) (g : TLDiagram m' n') :
    (cast rfl hm f).comp g = f.comp (cast hm.symm rfl g) := by
  subst hm; simp

@[simp]
theorem cast_verticalReflect (hn : n = n') (hm : m = m') (f : TLDiagram n m) :
    verticalReflect n' m' (cast hn hm f) = cast hm hn (verticalReflect n m f) := by
  subst hn hm; simp

end CastHelpers

section Reflections

variable {n m p n₁ m₁ n₂ m₂ : ℕ}

open PlanarMatching in
/-- **Vertical reflection preserves horizontal tensoring**: turning `f ⊗ g` upside down gives
`f` turned upside down tensored with `g` turned upside down. -/
theorem verticalReflect_tensor (f : TLDiagram n₁ m₁) (g : TLDiagram n₂ m₂) :
    verticalReflect (n₁ + n₂) (m₁ + m₂) (f.tensor g) =
      (verticalReflect n₁ m₁ f).tensor (verticalReflect n₂ m₂ g) := by
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_verticalReflect, pv_cast_eq, pv_reflect_eq, pv_matching_tensor,
      pv_matching_tensor, matching_verticalReflect, matching_verticalReflect, pv_cast_eq,
      pv_cast_eq, pv_reflect_eq, pv_reflect_eq]
    funext q
    by_cases h₁ : q < m₁
    · have := pv_lt f.matching (by omega : n₁ + m₁ - 1 - q < n₁ + m₁)
      simp only [revFn, show q < n₁ + n₂ + (m₁ + m₂) by omega, show q < n₁ + m₁ by omega,
        ite_true, insFn, show ¬n₁ + n₂ + (m₁ + m₂) - 1 - q < n₁ by omega,
        show ¬n₁ + n₂ + (m₁ + m₂) - 1 - q < n₁ + (n₂ + m₂) by omega, h₁, ite_false, ite_true]
      rw [show n₁ + n₂ + (m₁ + m₂) - 1 - q - (n₂ + m₂) = n₁ + m₁ - 1 - q by omega]
      by_cases hvn : pv f.matching (n₁ + m₁ - 1 - q) < n₁
      · rw [ins_of_lt hvn,
          ins_of_le (by omega : m₁ ≤ n₁ + m₁ - 1 - pv f.matching (n₁ + m₁ - 1 - q))]
        omega
      · rw [ins_of_le (by omega),
          ins_of_lt (by omega : n₁ + m₁ - 1 - pv f.matching (n₁ + m₁ - 1 - q) < m₁)]
        omega
    by_cases h₂ : q < m₁ + (m₂ + n₂)
    · have := pv_lt g.matching (by omega : n₂ + m₂ - 1 - (q - m₁) < n₂ + m₂)
      simp only [revFn, show q < n₁ + n₂ + (m₁ + m₂) by omega,
        show q - m₁ < n₂ + m₂ by omega, ite_true, insFn,
        show ¬n₁ + n₂ + (m₁ + m₂) - 1 - q < n₁ by omega,
        show n₁ + n₂ + (m₁ + m₂) - 1 - q < n₁ + (n₂ + m₂) by omega, h₁, h₂, ite_false, ite_true]
      rw [show n₁ + n₂ + (m₁ + m₂) - 1 - q - n₁ = n₂ + m₂ - 1 - (q - m₁) by omega]
      omega
    by_cases h₃ : q < m₁ + (m₂ + n₂) + n₁
    · have := pv_lt f.matching (by omega : n₁ + m₁ - 1 - (q - (m₂ + n₂)) < n₁ + m₁)
      simp only [revFn, show q < n₁ + n₂ + (m₁ + m₂) by omega,
        show q - (m₂ + n₂) < n₁ + m₁ by omega, ite_true, insFn,
        show n₁ + n₂ + (m₁ + m₂) - 1 - q < n₁ by omega, h₁, h₂, ite_false, ite_true]
      rw [show n₁ + n₂ + (m₁ + m₂) - 1 - q = n₁ + m₁ - 1 - (q - (m₂ + n₂)) by omega]
      by_cases hvn : pv f.matching (n₁ + m₁ - 1 - (q - (m₂ + n₂))) < n₁
      · rw [ins_of_lt hvn,
          ins_of_le (by omega : m₁ ≤ n₁ + m₁ - 1 - pv f.matching (n₁ + m₁ - 1 - (q - (m₂ + n₂))))]
        omega
      · rw [ins_of_le (by omega),
          ins_of_lt (by omega : n₁ + m₁ - 1 - pv f.matching (n₁ + m₁ - 1 - (q - (m₂ + n₂))) < m₁)]
        omega
    · simp only [revFn, show ¬q < n₁ + n₂ + (m₁ + m₂) by omega,
        show ¬q - (m₂ + n₂) < n₁ + m₁ by omega, ite_false, insFn, h₁, h₂]
      rw [ins_of_le (by omega : m₁ ≤ q - (m₂ + n₂))]
      omega
  · simp

open PlanarMatching in
private theorem pv_reflect_diagram (f : TLDiagram n m) {q : ℕ} (hq : q < n + m) :
    pv (reflect n m f).matching q =
      if q < n then
        let v := pv f.matching (n - 1 - q)
        if v < n then n - 1 - v else 2 * n + m - 1 - v
      else
        let v := pv f.matching (2 * n + m - 1 - q)
        if v < n then n - 1 - v else 2 * n + m - 1 - v := by
  have hval : ((reflect n m f).matching.val.val ⟨q, hq⟩ : ℕ) =
      ((finRotate (n + m) ^ n) (Fin.rev (f.matching.val.val (Fin.rev
        ((finRotate (n + m) ^ n).symm ⟨q, hq⟩)))) : ℕ) := by
    rw [matching_reflect, coe_rotate_pow_apply, coe_reflect_apply, PerfectMatching.congr_trans,
      PerfectMatching.congr_val]
    rfl
  rw [pv_of_lt _ hq, hval]
  have hrot : ∀ a : Fin (n + m), ((finRotate (n + m) ^ n) a : ℕ) = ((a : ℕ) + n) % (n + m) :=
    Fin.coe_finRotate_pow n
  have hinv : ∀ a : Fin (n + m), (((finRotate (n + m) ^ n).symm a : Fin (n + m)) : ℕ) =
      ((a : ℕ) + m) % (n + m) := by
    intro a
    have hpow : (finRotate (n + m) ^ n : Perm (Fin (n + m))).symm = finRotate (n + m) ^ m := by
      rw [← Perm.inv_def]
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_add, show (finRotate (n + m) ^ (n + m) : Perm (Fin (n + m))) = 1 by
        simpa [orderOf_finRotate (by omega : n + m ≠ 0)] using
          pow_orderOf_eq_one (finRotate (n + m))]
    rw [hpow, Fin.coe_finRotate_pow]
  rw [hrot, Fin.val_rev, ← pv_coe, Fin.val_rev, hinv]
  by_cases hqn : q < n
  · have hm : (q + m) % (n + m) = q + m := Nat.mod_eq_of_lt (by omega)
    have hsub : n + m - (q + m + 1) = n - 1 - q := by omega
    have hv := pv_lt f.matching (by omega : n - 1 - q < n + m)
    rw [hm, hsub, ite_eq_left hqn]
    dsimp only
    split_ifs with hvn
    · rw [show n + m - (pv f.matching (n - 1 - q) + 1) + n =
          (n - 1 - pv f.matching (n - 1 - q)) + (n + m) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  · have hm : (q + m) % (n + m) = q - n := by
      rw [show q + m = (q - n) + (n + m) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hsub : n + m - (q - n + 1) = 2 * n + m - 1 - q := by omega
    have hv := pv_lt f.matching (by omega : 2 * n + m - 1 - q < n + m)
    rw [hm, hsub, ite_eq_right hqn]
    dsimp only
    split_ifs with hvn
    · rw [show n + m - (pv f.matching (2 * n + m - 1 - q) + 1) + n =
          (n - 1 - pv f.matching (2 * n + m - 1 - q)) + (n + m) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega

open PlanarMatching in
/-- **Horizontal reflection reverses horizontal tensoring**: mirroring `f ⊗ g` left to right gives
mirrored `g` tensored with mirrored `f`, cast along commutativity of addition. -/
theorem reflect_tensor (f : TLDiagram n₁ m₁) (g : TLDiagram n₂ m₂) :
    reflect (n₁ + n₂) (m₁ + m₂) (f.tensor g) =
      cast (Nat.add_comm n₂ n₁) (Nat.add_comm m₂ m₁)
        ((reflect n₂ m₂ g).tensor (reflect n₁ m₁ f)) := by
  ext : 1
  · refine ext_pv fun q hq => ?_
    rw [pv_reflect_diagram _ hq, matching_cast, pv_cast_eq, pv_matching_tensor]
    by_cases h₁ : q < n₂
    · have hgv := pv_lt g.matching (by omega : n₂ - 1 - q < n₂ + m₂)
      simp only [ite_eq_left (by omega : q < n₁ + n₂), pv_matching_tensor, insFn,
        show ¬n₁ + n₂ - 1 - q < n₁ by omega,
        show n₁ + n₂ - 1 - q < n₁ + (n₂ + m₂) by omega, h₁, ite_false, ite_true]
      rw [show n₁ + n₂ - 1 - q - n₁ = n₂ - 1 - q by omega, pv_reflect_diagram g (by omega)]
      simp only [ins]; split_ifs <;> omega
    by_cases h₂ : q < n₂ + n₁
    · have hfv := pv_lt f.matching (by omega : n₁ + n₂ - 1 - q < n₁ + m₁)
      simp only [ite_eq_left (by omega : q < n₁ + n₂), pv_matching_tensor, insFn,
        show n₁ + n₂ - 1 - q < n₁ by omega, show q < n₂ + (n₁ + m₁) by omega,
        h₁, ite_false, ite_true]
      rw [pv_reflect_diagram f (by omega), ite_eq_left (by omega : q - n₂ < n₁),
        show n₁ - 1 - (q - n₂) = n₁ + n₂ - 1 - q by omega]
      simp only [ins]; split_ifs <;> omega
    by_cases h₃ : q < n₂ + n₁ + m₁
    · have hfv := pv_lt f.matching (by omega : 2 * n₁ + m₁ - 1 - (q - n₂) < n₁ + m₁)
      simp only [ite_eq_right (by omega : ¬q < n₁ + n₂), pv_matching_tensor, insFn,
        show ¬2 * (n₁ + n₂) + (m₁ + m₂) - 1 - q < n₁ by omega,
        show ¬2 * (n₁ + n₂) + (m₁ + m₂) - 1 - q < n₁ + (n₂ + m₂) by omega,
        show q < n₂ + (n₁ + m₁) by omega, h₁, ite_false, ite_true]
      rw [pv_reflect_diagram f (by omega), ite_eq_right (by omega : ¬q - n₂ < n₁),
        show 2 * (n₁ + n₂) + (m₁ + m₂) - 1 - q - (n₂ + m₂) = 2 * n₁ + m₁ - 1 - (q - n₂) by omega]
      simp only [ins]; split_ifs <;> omega
    · have hgv := pv_lt g.matching (by omega : 2 * n₂ + m₂ - 1 - (q - (n₁ + m₁)) < n₂ + m₂)
      simp only [ite_eq_right (by omega : ¬q < n₁ + n₂), pv_matching_tensor, insFn,
        show ¬2 * (n₁ + n₂) + (m₁ + m₂) - 1 - q < n₁ by omega,
        show 2 * (n₁ + n₂) + (m₁ + m₂) - 1 - q < n₁ + (n₂ + m₂) by omega,
        show ¬q < n₂ + (n₁ + m₁) by omega, h₁, ite_false, ite_true]
      rw [pv_reflect_diagram g (by omega), ite_eq_right (by omega : ¬q - (n₁ + m₁) < n₂),
        show 2 * (n₁ + n₂) + (m₁ + m₂) - 1 - q - n₁ = 2 * n₂ + m₂ - 1 - (q - (n₁ + m₁)) by omega]
      simp only [ins]; split_ifs <;> omega
  · simp [Nat.add_comm]

end Reflections

section NestedCupsCaps

variable {n m : ℕ}

/-- The **nested cup** `0 → n + n` on `n` strands: `n` nested arcs joining the top boundary point
`i` to `2n - 1 - i`, with no circles. -/
def nestedCup (n : ℕ) : TLDiagram 0 (n + n) :=
  ⟨PlanarMatching.cast (Nat.zero_add (n + n)).symm (PlanarMatching.nested n), 0⟩

/-- The **nested cap** `n + n → 0` on `n` strands: `n` nested arcs joining the bottom boundary
point `i` to `2n - 1 - i`, with no circles. -/
def nestedCap (n : ℕ) : TLDiagram (n + n) 0 :=
  ⟨PlanarMatching.nested n, 0⟩

@[simp]
theorem matching_nestedCup (n : ℕ) :
    (nestedCup n).matching =
      PlanarMatching.cast (Nat.zero_add (n + n)).symm (PlanarMatching.nested n) := (rfl)

@[simp]
theorem circles_nestedCup (n : ℕ) : (nestedCup n).circles = 0 := (rfl)

@[simp]
theorem matching_nestedCap (n : ℕ) : (nestedCap n).matching = PlanarMatching.nested n := (rfl)

@[simp]
theorem circles_nestedCap (n : ℕ) : (nestedCap n).circles = 0 := (rfl)

/-- On one strand, the nested cup is `TLDiagram.cup`. -/
@[simp]
theorem nestedCup_one : nestedCup 1 = cup := by
  ext : 1
  · refine PlanarMatching.ext fun i => ?_
    fin_cases i <;> simp
  · simp

/-- On one strand, the nested cap is `TLDiagram.cap`. -/
@[simp]
theorem nestedCap_one : nestedCap 1 = cap := by
  ext : 1
  · refine PlanarMatching.ext fun i => ?_
    fin_cases i <;> simp
  · simp

/-- On zero strands, the nested cup is the empty identity diagram `id 0`. -/
@[simp]
theorem nestedCup_zero : nestedCup 0 = id 0 := by
  ext : 1
  · exact PlanarMatching.ext fun i => Fin.elim0 i
  · simp

/-- On zero strands, the nested cap is the empty identity diagram `id 0`. -/
@[simp]
theorem nestedCap_zero : nestedCap 0 = id 0 := by
  ext : 1
  · exact PlanarMatching.ext fun i => Fin.elim0 i
  · simp

open PlanarMatching in
/-- Turning the nested cup upside down gives the nested cap. -/
@[simp]
theorem verticalReflect_nestedCup (n : ℕ) :
    verticalReflect 0 (n + n) (nestedCup n) = nestedCap n := by
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_verticalReflect, matching_nestedCup, matching_nestedCap, pv_cast_eq,
      pv_reflect_eq, pv_cast_eq]
    funext q
    unfold revFn
    split_ifs with h
    · rw [pv_nested _ (by omega), pv_nested _ (by omega)]; omega
    · rw [pv_of_le _ (by omega)]
  · simp

/-- Turning the nested cap upside down gives the nested cup. -/
@[simp]
theorem verticalReflect_nestedCap (n : ℕ) :
    verticalReflect (n + n) 0 (nestedCap n) = nestedCup n := by
  rw [← verticalReflect_nestedCup n, verticalReflect_verticalReflect]

open PlanarMatching in
/-- **A nested cup followed by a nested cap closes `n` circles.** -/
theorem nestedCup_comp_nestedCap (n : ℕ) :
    (nestedCup n).comp (nestedCap n) = ⟨PlanarMatching.nested 0, n⟩ := by
  ext : 1
  · exact PlanarMatching.ext fun i => Fin.elim0 i
  · have hna := glueFn_nested_append (n := n) (p := n) (nested n)
    have hcast : pv ((nestedCup n).matching.append (nestedCap n).matching) =
        pv ((nested n).append (nested n)) := by
      rw [pv_append_eq, pv_append_eq, matching_nestedCup, pv_cast_eq, matching_nestedCap,
        Nat.zero_add]
      rfl
    have hadd := glueFn_add 0 n n (pv ((nested n).append (nested n)))
    simp only [circles_comp, circles_nestedCup, circles_nestedCap, glueMiddleCircles_eq,
      Nat.zero_add, Nat.add_zero, hcast, hadd.2, hna.1, hna.2, glueCircles_nested]

open PlanarMatching in
/-- **Bending the bottom boundary up to the right**: composing `nestedCup n` with `f ⊗ id n`
preserves the matching of `f` (cast to `0 → m + n`) and closes no new circle. -/
theorem nestedCup_comp_tensor_id (f : TLDiagram n m) :
    (nestedCup n).comp (f.tensor (id n)) =
      ⟨PlanarMatching.cast (by omega) f.matching, f.circles⟩ := by
  have hy_dim : n + n + (m + n) = n + (n + m + n) := by omega
  have hna := glueFn_nested_append (n := n) (p := n + m + n)
    (PlanarMatching.cast hy_dim (f.tensor (id n)).matching)
  have hcast : pv ((nestedCup n).matching.append (f.tensor (id n)).matching) =
      pv ((nested n).append (PlanarMatching.cast hy_dim (f.tensor (id n)).matching)) := by
    rw [pv_append_eq, pv_append_eq, matching_nestedCup, pv_cast_eq, pv_cast_eq, Nat.zero_add]
    exact congrArg (fun k => appendFn (n + n) k _ _) hy_dim
  have hins := glueFn_insFn_nested_right f.matching
  have hy : pv (f.tensor (id n)).matching = insFn n (n + n) (pv f.matching) (pv (nested n)) := by
    rw [pv_matching_tensor, matching_id]
  rw [pv_cast_eq] at hna
  have hadd := glueFn_add 0 n n
    (pv ((nested n).append (PlanarMatching.cast hy_dim (f.tensor (id n)).matching)))
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_comp, pv_glueMiddle, hcast, hadd.1, Nat.zero_add, hna.1, hy, hins.1,
      pv_cast_eq]
  · simp only [circles_comp, circles_nestedCup, circles_tensor, circles_id, glueMiddleCircles_eq]
    rw [hcast, hadd.2, Nat.zero_add n, hna.1, hna.2, hy, hins.2]
    omega

/-- **Bending the top boundary down to the right**: composing `f ⊗ id m` with `nestedCap m`
preserves the matching of `f` (cast to `n + m → 0`) and closes no new circle. -/
theorem tensor_id_comp_nestedCap (f : TLDiagram n m) :
    (f.tensor (id m)).comp (nestedCap m) =
      ⟨PlanarMatching.cast (by omega) f.matching, f.circles⟩ := by
  have h := congrArg (verticalReflect 0 (n + m))
    (nestedCup_comp_tensor_id (verticalReflect n m f))
  rw [verticalReflect_comp, verticalReflect_tensor, verticalReflect_nestedCup,
    verticalReflect_id, verticalReflect_verticalReflect] at h
  rw [h]
  ext : 1
  · rw [matching_verticalReflect, matching_verticalReflect, ← PlanarMatching.cast_reflect,
      PlanarMatching.cast_cast, ← PlanarMatching.cast_reflect, PlanarMatching.reflect_reflect,
      PlanarMatching.cast_cast]
  · simp

open PlanarMatching in
/-- **Bending the bottom boundary up to the left**: composing `nestedCup n` with `id n ⊗ f`
rotates the matching of `f` by `m` steps (equivalently `-n` steps) and closes no new circle. -/
theorem nestedCup_comp_id_tensor (f : TLDiagram n m) :
    (nestedCup n).comp ((id n).tensor f) =
      ⟨PlanarMatching.cast (by omega) ((PlanarMatching.rotate (n + m) ^ m) f.matching),
        f.circles⟩ := by
  rcases Nat.eq_zero_or_pos (n + m) with h0 | hpos
  · have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    subst hn hm
    ext : 1
    · exact PlanarMatching.ext fun i => Fin.elim0 i
    · simp
  have hy_dim : n + n + (n + m) = n + (n + n + m) := by omega
  have hna := glueFn_nested_append (n := n) (p := n + n + m)
    (PlanarMatching.cast hy_dim ((id n).tensor f).matching)
  have hcast : pv ((nestedCup n).matching.append ((id n).tensor f).matching) =
      pv ((nested n).append (PlanarMatching.cast hy_dim ((id n).tensor f).matching)) := by
    rw [pv_append_eq, pv_append_eq, matching_nestedCup, pv_cast_eq, pv_cast_eq, Nat.zero_add]
    exact congrArg (fun k => appendFn (n + n) k _ _) hy_dim
  rw [pv_cast_eq] at hna
  have hrot_step := glueFn_insert_nested_left hpos n f.matching
  have hrot : ((PlanarMatching.rotate (n + m)).symm ^ n) f.matching =
      (PlanarMatching.rotate (n + m) ^ m) f.matching := by
    have hinv : (PlanarMatching.rotate (n + m) ^ m) =
        (PlanarMatching.rotate (n + m) ^ n)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_add, Nat.add_comm, rotate_pow_self]
    rw [hinv, ← inv_pow, ← Perm.inv_def]
  have hadd := glueFn_add 0 n n
    (pv ((nested n).append (PlanarMatching.cast hy_dim ((id n).tensor f).matching)))
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_comp, pv_glueMiddle, hcast, hadd.1, Nat.zero_add, hna.1, pv_matching_tensor,
      matching_id, hrot_step.1, hrot, pv_cast_eq]
  · simp only [circles_comp, circles_nestedCup, circles_tensor, circles_id, glueMiddleCircles_eq]
    rw [hcast, hadd.2, Nat.zero_add n, hna.1, hna.2, pv_matching_tensor, matching_id,
      hrot_step.2]
    omega

open PlanarMatching in
/-- **Diagram formula for the right adjoint mate**: bending the bottom of `f : n → m` up on
the right and the top down on the left produces its 180-degree rotation
`verticalReflect n m (reflect n m f)`. -/
theorem rightMate_eq (f : TLDiagram n m) :
    cast (Nat.add_zero m) (Nat.zero_add n)
      (((id m).tensor ((nestedCup n).comp (f.tensor (id n)))).comp
        (cast (Nat.add_assoc m m n) rfl ((nestedCap m).tensor (id n)))) =
      verticalReflect n m (reflect n m f) := by
  have hvrf : (verticalReflect n m (reflect n m f)).matching =
      PlanarMatching.cast (Nat.add_comm n m) ((PlanarMatching.rotate (n + m) ^ m) f.matching) := by
    rw [matching_verticalReflect, matching_reflect, PlanarMatching.reflect_rotate_pow,
      PlanarMatching.reflect_reflect]
    have hinv : (PlanarMatching.rotate (n + m) ^ n)⁻¹ = PlanarMatching.rotate (n + m) ^ m := by
      rw [inv_eq_iff_eq_inv, eq_inv_iff_mul_eq_one, ← pow_add, PlanarMatching.rotate_pow_self]
    rw [hinv]
  rcases Nat.eq_zero_or_pos (n + m) with h0 | hpos
  · have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    subst hn hm
    ext : 1
    · exact PlanarMatching.ext fun i => Fin.elim0 i
    · simp
  -- Step 1: bend the bottom of `f` up via `nestedCup n` to get `f' : 0 → m + n`.
  set f' : TLDiagram 0 (m + n) := ⟨PlanarMatching.cast (by omega) f.matching, f.circles⟩
  have hcup : (nestedCup n).comp (f.tensor (id n)) = f' := nestedCup_comp_tensor_id f
  rw [hcup]
  set L : PlanarMatching (m + 0 + (m + (m + n))) := ((id m).tensor f').matching
  set R : PlanarMatching (m + (m + n) + (0 + n)) :=
    (cast (Nat.add_assoc m m n) rfl ((nestedCap m).tensor (id n))).matching
  have hpL : pv L = insFn m (n + m) (pv (nested m)) (pv f.matching) := by
    rw [pv_matching_tensor, matching_id, pv_cast_eq, show 0 + (m + n) = n + m by omega]
  have hpR : pv R = appendFn (m + m) (n + n) (pv (nested m)) (pv (nested n)) := by
    dsimp only [R]
    rw [matching_cast, pv_cast_eq, pv_matching_tensor, matching_nestedCap, matching_id]
    exact insFn_self_eq_appendFn (nested m) (nested n)
  have hL_app : pv (L.append R) =
      appendFn (m + 0 + (m + (m + n)) + (m + m)) (n + n)
        (pv (L.append (nested m))) (pv (nested n)) := by
    rw [pv_append_eq, hpR, show m + (m + n) + (0 + n) = m + m + (n + n) by omega,
      ← appendFn_assoc, ← pv_append_eq]
  -- Step 2: peel the `m` cap contractions off the right, leaving `L.append (nested n)`.
  have hstep1 := glueFn_appendFn_left (n := 2 * m + n) (r := n + n) (nested n) m
    (m + 0 + (m + (m + n)) + (m + m)) (L.append (nested m)) (by omega)
  have hLdim : m + 0 + (m + (m + n)) = (2 * m + n) + m := by omega
  have han1 := glueFn_append_nested (n := 2 * m + n) (p := m) (PlanarMatching.cast hLdim L)
  have hcastL : pv ((PlanarMatching.cast hLdim L).append (nested m)) =
      pv (L.append (nested m)) := by
    rw [pv_append_eq, pv_append_eq, pv_cast_eq]
    exact congrArg (fun k => appendFn k (m + m) _ _) hLdim.symm
  rw [hcastL, pv_cast_eq] at han1
  have hmid1_fn : glueFn (2 * m + n) m (pv (L.append R)) =
      pv (L.append (nested n)) := by
    rw [hL_app, ← hstep1.1, han1.1, show m + 0 + (m + (m + n)) + (m + m) - 2 * m =
      m + 0 + (m + (m + n)) by omega, pv_append_eq]
  have hmid1_c : glueCircles (2 * m + n) m (pv (L.append R)) = 0 := by
    rw [hL_app, hstep1.2, han1.2]
  -- Step 3: contract the `m` inserted identity arcs to rotate `f.matching` by `m` steps.
  have hstep2 := glueFn_appendFn_left (n := n + m) (r := n + n) (nested n) m
    (m + 0 + (m + (m + n))) L (by omega)
  have hrot2 := glueFn_insert_nested_right hpos m f.matching
  set rf : PlanarMatching (n + m) := (PlanarMatching.rotate (n + m) ^ m) f.matching
  have hmid2_fn : glueFn (n + m) m (pv (L.append (nested n))) = pv (rf.append (nested n)) := by
    rw [pv_append_eq, ← hstep2.1, hpL, hrot2.1,
      show m + 0 + (m + (m + n)) - 2 * m = n + m by omega, pv_append_eq]
  have hmid2_c : glueCircles (n + m) m (pv (L.append (nested n))) = 0 := by
    rw [pv_append_eq, hstep2.2, hpL, hrot2.2]
  -- Step 4: absorb the remaining trailing `nested n` block on the right.
  have han3 := glueFn_append_nested (n := m) (p := n) (PlanarMatching.cast (Nat.add_comm n m) rf)
  have hcast3 : pv ((PlanarMatching.cast (Nat.add_comm n m) rf).append (nested n)) =
      pv (rf.append (nested n)) := by
    rw [pv_append_eq, pv_append_eq, pv_cast_eq]
    exact congrArg (fun k => appendFn k (n + n) _ _) (Nat.add_comm m n)
  rw [hcast3, pv_cast_eq] at han3
  have hadd1 := glueFn_add m (n + m) m (pv (L.append R))
  have hadd2 := glueFn_add m n m (glueFn (2 * m + n) m (pv (L.append R)))
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_cast, pv_cast_eq, matching_comp, pv_glueMiddle, hvrf, pv_cast_eq,
      show glueFn (m + 0) (m + (m + n)) = glueFn m (n + m + m) by congr 1; omega,
      hadd1.1, show m + (n + m) = 2 * m + n by omega,
      show glueFn m (n + m) = glueFn m (n + m) from rfl, hadd2.1,
      show glueFn (m + n) m = glueFn (n + m) m by rw [Nat.add_comm],
      hmid1_fn, hmid2_fn, han3.1]
  · simp only [circles_cast, circles_comp, circles_tensor, circles_id, circles_nestedCap,
      circles_verticalReflect, circles_reflect, glueMiddleCircles_eq]
    rw [show glueCircles (m + 0) (m + (m + n)) = glueCircles m (n + m + m) by
        congr 1; omega,
      hadd1.2, show m + (n + m) = 2 * m + n by omega, hadd2.2,
      show glueFn (m + n) m = glueFn (n + m) m by rw [Nat.add_comm],
      show glueCircles (m + n) m = glueCircles (n + m) m by rw [Nat.add_comm],
      hmid1_fn, hmid1_c, hmid2_fn, hmid2_c, han3.2]
    dsimp only [f']
    omega

/-- **Right zigzag identity** for the nested cup and cap on `n` strands:
`(id n ⊗ nestedCup n) ≫ (nestedCap n ⊗ id n) = id n`. -/
theorem zigzag_right (n : ℕ) :
    ((id n).tensor (nestedCup n)).comp
      (cast (Nat.add_assoc n n n) rfl ((nestedCap n).tensor (id n))) =
      cast (Nat.add_zero n).symm (Nat.zero_add n).symm (id n) := by
  have h := rightMate_eq (id n)
  rw [id_tensor_id, comp_id, reflect_id, verticalReflect_id] at h
  have h' := congrArg (cast (Nat.add_zero n).symm (Nat.zero_add n).symm) h
  rw [cast_cast, cast_refl, Equiv.refl_apply] at h'
  exact h'

/-- **Left zigzag identity** for the nested cup and cap on `n` strands:
`(nestedCup n ⊗ id n) ≫ (id n ⊗ nestedCap n) = id n`. -/
theorem zigzag_left (n : ℕ) :
    ((nestedCup n).tensor (id n)).comp
      (cast (Nat.add_assoc n n n).symm rfl ((id n).tensor (nestedCap n))) =
      cast (Nat.zero_add n).symm (Nat.add_zero n).symm (id n) := by
  have h := congrArg (verticalReflect (n + 0) (0 + n)) (zigzag_right n)
  rw [verticalReflect_comp, cast_verticalReflect, verticalReflect_tensor, verticalReflect_tensor,
    verticalReflect_id, verticalReflect_nestedCup, verticalReflect_nestedCap,
    cast_verticalReflect, verticalReflect_id, comp_cast_mid] at h
  exact h

/-- Nesting `nestedCap m` inside `nestedCap n` gives `nestedCap (n + m)`. -/
theorem id_tensor_nestedCap_comp_nestedCap (n m : ℕ) :
    ((id n).tensor ((nestedCap m).tensor (id n))).comp
      (cast (show n + n = n + (0 + n) by omega) rfl (nestedCap n)) =
      cast (show (n + m) + (n + m) = n + (m + m + n) by omega) rfl (nestedCap (n + m)) := by
  have h1 : (id n).tensor ((nestedCap m).tensor (id n)) =
      cast (Nat.add_assoc n (m + m) n) rfl
        (cast rfl (Nat.add_assoc n 0 n) (((id n).tensor (nestedCap m)).tensor (id n))) := by
    rw [cast_cast, tensor_assoc, cast_cast, cast_refl, Equiv.refl_apply]
  rw [h1, cast_comp, comp_cast_mid, cast_cast, cast_refl, Equiv.refl_apply]
  have h2 := congrArg (cast (Nat.add_assoc n (m + m) n) rfl)
    (tensor_id_comp_nestedCap ((id n).tensor (nestedCap m)))
  change cast (Nat.add_assoc n (m + m) n) rfl
      ((((id n).tensor (nestedCap m)).tensor (id n)).comp (nestedCap n)) = _ at h2
  refine h2.trans ?_
  ext : 1
  · simp only [matching_cast, matching_tensor, matching_id, matching_nestedCap,
      PlanarMatching.insertBlock_nested_nested, PlanarMatching.cast_cast]
  · simp

end NestedCupsCaps

end TLDiagram

end TauCeti
