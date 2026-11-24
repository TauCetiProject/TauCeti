/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Compose
import all TauCeti.Combinatorics.PlanarMatching.Glue
import all TauCeti.Combinatorics.PlanarMatching.Associativity

/-!
# The tensor product of Temperley–Lieb diagrams

The tensor product `f.tensor g : TLDiagram (n + n') (m + m')` of two Temperley–Lieb diagrams
`f : n → m` and `g : n' → m'` places `g` to the right of `f` and keeps the circles of both.

In the counterclockwise numbering of the boundary, the points of `f.tensor g` are, in order, the
`n` bottom points of `f`, the `n'` bottom points of `g`, the `m'` top points of `g` (from right to
left) and the `m` top points of `f` (from right to left). So the boundary of `g` is a block of
consecutive points inserted into the boundary of `f` between its bottom and its top points, and the
matching of `f.tensor g` is `TauCeti.PlanarMatching.insertBlock f.matching g.matching`: the arcs of
`g` on the block, and the arcs of `f` around it.

The tensor product is functorial for composition, `TauCeti.TLDiagram.tensor_comp_tensor` (the
interchange law), sends identities to identities, and is associative and unital up to the
transports `TauCeti.TLDiagram.cast` along the equalities of the numbers of points. These are the
laws behind the strict monoidal structure of the Temperley–Lieb diagram category.

## Main definitions

* `TauCeti.PlanarMatching.insertBlock x y`: the planar matching `y` inserted as a block of
  consecutive points into the planar matching `x`.
* `TauCeti.TLDiagram.tensor f g`: the tensor product of Temperley–Lieb diagrams, `g` to the right
  of `f`.

## Main results

* `TauCeti.TLDiagram.tensor_comp_tensor`: the interchange law
  `(f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) = (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂)`, for the matchings and for the circles.
* `TauCeti.TLDiagram.id_tensor_id`: the tensor product of identity diagrams is an identity
  diagram.
* `TauCeti.TLDiagram.tensor_assoc`, `TauCeti.TLDiagram.id_zero_tensor`,
  `TauCeti.TLDiagram.tensor_id_zero`: associativity and unitality of the tensor product.
* `TauCeti.TLDiagram.matching_zero_tensor`, `TauCeti.TLDiagram.matching_tensor_zero`: a diagram
  `0 → 0`, which only carries circles, does not change the matching of the other factor.
* `TauCeti.TLDiagram.matching_tensor_eq_iff`, `TauCeti.TLDiagram.tensor_left_inj`,
  `TauCeti.TLDiagram.tensor_right_inj`: the tensor product is injective in each factor.
* `TauCeti.PlanarMatching.insertBlock_zero`, `TauCeti.PlanarMatching.zero_insertBlock`,
  `TauCeti.PlanarMatching.nested_insertBlock`,
  `TauCeti.PlanarMatching.cast_insertBlock_insertBlock`: the unit, identity and associativity
  laws of block insertion, from which the corresponding laws of the tensor product follow.
* `TauCeti.PlanarMatching.insertBlock_append`, `TauCeti.PlanarMatching.append_insertBlock`,
  `TauCeti.PlanarMatching.cast_insertBlock_insertBlock_eq_insertBlock_append`,
  `TauCeti.PlanarMatching.add_zero_insertBlock`, `TauCeti.PlanarMatching.zero_add_insertBlock`:
  block insertion and juxtaposition of planar matchings.
* `TauCeti.PlanarMatching.insertBlock_eq_insertBlock_iff`: block insertion determines both the
  outer and the inserted matching.

## Implementation notes

The proofs work with partner functions `ℕ → ℕ`, as in
`TauCeti.Combinatorics.PlanarMatching.Associativity`, whose private machinery this file imports
with `import all`. Composing two tensor products glues two blocks of nested pairs: the pairs between
the top of `f₁` and the bottom of `g₁`, which lie between the two inserted blocks of `f₂` and `g₂`,
and the pairs between the top of `f₂` and the bottom of `g₂`, inside the merged inserted block. The
interchange law reduces to the fact that contracting a pair of consecutive points commutes with
inserting a block, whether the pair lies before the block, after it, or inside it.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

namespace TauCeti

namespace PlanarMatching

/-! ### Inserting a block, on partner functions -/

/-- The partner function of a matching with partner function `φ` into which a block with partner
function `ψ` on `l` points is inserted before position `c`. -/
private def insFn (c l : ℕ) (φ ψ : ℕ → ℕ) (q : ℕ) : ℕ :=
  if q < c then ins c l (φ q) else if q < c + l then c + ψ (q - c) else ins c l (φ (q - l))

private theorem ins_of_lt {c l v : ℕ} (h : v < c) : ins c l v = v := by
  simp [ins, h]

private theorem ins_of_le {c l v : ℕ} (h : c ≤ v) : ins c l v = v + l := by
  simp [ins, Nat.not_lt.mpr h]

private theorem ins_injective (c l : ℕ) : Function.Injective (ins c l) := by
  intro u v h
  simp only [ins] at h
  split_ifs at h <;> omega

private theorem ins_lt_ins_iff {c l u v : ℕ} : ins c l u < ins c l v ↔ u < v := by
  simp only [ins]
  split_ifs <;> omega

/-- Every number is either outside the inserted block or inside it. -/
private theorem exists_eq_ins_or_add (c l q : ℕ) :
    (∃ u, q = ins c l u) ∨ ∃ v < l, q = c + v := by
  by_cases h₁ : q < c
  · exact .inl ⟨q, (ins_of_lt h₁).symm⟩
  by_cases h₂ : q < c + l
  · exact .inr ⟨q - c, by omega, by omega⟩
  · exact .inl ⟨q - l, by rw [ins_of_le (by omega)]; omega⟩

private theorem insFn_ins (c l : ℕ) (φ ψ : ℕ → ℕ) (u : ℕ) :
    insFn c l φ ψ (ins c l u) = ins c l (φ u) := by
  by_cases hu : u < c
  · simp only [ins_of_lt hu, insFn, hu, ↓reduceIte]
  · rw [ins_of_le (show c ≤ u by omega)]
    simp only [insFn, show ¬u + l < c by omega, show ¬u + l < c + l by omega, ↓reduceIte,
      Nat.add_sub_cancel]

private theorem insFn_add {c l : ℕ} (φ ψ : ℕ → ℕ) {v : ℕ} (hv : v < l) :
    insFn c l φ ψ (c + v) = c + ψ v := by
  simp only [insFn, show ¬c + v < c by omega, show c + v < c + l by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]

/-- The arcs of a planar matching do not interleave, read on its partner function. -/
private theorem pv_not_lt {K : ℕ} (x : PlanarMatching K) {q r : ℕ} (hr : r < K) (hqr : q < r)
    (hrq : r < pv x q) : ¬ pv x q < pv x r := by
  have hq : q < K := hqr.trans hr
  rw [pv_of_lt x hq] at hrq
  rw [pv_of_lt x hq, pv_of_lt x hr]
  exact fun h => Equiv.Perm.isNoncrossingMatching_iff.mp x.property
    (Fin.lt_def.mpr hqr : (⟨q, hq⟩ : Fin K) < ⟨r, hr⟩) (Fin.lt_def.mpr hrq) (Fin.lt_def.mpr h)

/-! ### Inserting a block -/

variable {a b l : ℕ}

private theorem ins_lt_iff {u : ℕ} : ins a l u < a + l + b ↔ u < a + b := by
  simp only [ins]
  split_ifs <;> omega

private theorem insFn_lt (x : PlanarMatching (a + b)) (y : PlanarMatching l) {q : ℕ}
    (hq : q < a + l + b) : insFn a l (pv x) (pv y) q < a + l + b := by
  rcases exists_eq_ins_or_add a l q with ⟨u, rfl⟩ | ⟨v, hv, rfl⟩
  · rw [insFn_ins, ins_lt_iff]
    exact pv_lt x (ins_lt_iff.mp hq)
  · have := pv_lt y hv
    rw [insFn_add _ _ hv]
    omega

/-- The involution underlying `TauCeti.PlanarMatching.insertBlock`. -/
private def insertFun (x : PlanarMatching (a + b)) (y : PlanarMatching l) (i : Fin (a + l + b)) :
    Fin (a + l + b) :=
  ⟨insFn a l (pv x) (pv y) i, insFn_lt x y i.isLt⟩

private theorem insFn_insFn (x : PlanarMatching (a + b)) (y : PlanarMatching l) (q : ℕ) :
    insFn a l (pv x) (pv y) (insFn a l (pv x) (pv y) q) = q := by
  rcases exists_eq_ins_or_add a l q with ⟨u, rfl⟩ | ⟨v, hv, rfl⟩
  · rw [insFn_ins, insFn_ins, pv_pv_eq]
  · rw [insFn_add _ _ hv, insFn_add _ _ (pv_lt y hv), pv_pv_eq]

private theorem insertFun_involutive (x : PlanarMatching (a + b)) (y : PlanarMatching l) :
    Function.Involutive (insertFun x y) := fun i =>
  Fin.ext (insFn_insFn x y i)

private theorem insFn_ne (x : PlanarMatching (a + b)) (y : PlanarMatching l) {q : ℕ}
    (hq : q < a + l + b) : insFn a l (pv x) (pv y) q ≠ q := by
  rcases exists_eq_ins_or_add a l q with ⟨u, rfl⟩ | ⟨v, hv, rfl⟩
  · rw [insFn_ins]
    exact fun h => pv_ne x (ins_lt_iff.mp hq) (ins_injective a l h)
  · rw [insFn_add _ _ hv]
    exact fun h => pv_ne y hv (by omega)

private theorem insertFun_ne (x : PlanarMatching (a + b)) (y : PlanarMatching l)
    (i : Fin (a + l + b)) : insertFun x y i ≠ i := fun h =>
  insFn_ne x y i.isLt (congrArg Fin.val h)

/-- The arcs of an inserted block do not interleave with each other or with the arcs around it. -/
private theorem insFn_not_lt (x : PlanarMatching (a + b)) (y : PlanarMatching l) {q r : ℕ}
    (hr : r < a + l + b) (hqr : q < r) (hrq : r < insFn a l (pv x) (pv y) q) :
    ¬ insFn a l (pv x) (pv y) q < insFn a l (pv x) (pv y) r := by
  rcases exists_eq_ins_or_add a l q with ⟨u, rfl⟩ | ⟨v, hv, rfl⟩ <;>
    rcases exists_eq_ins_or_add a l r with ⟨u', rfl⟩ | ⟨v', hv', rfl⟩
  · -- Two arcs around the block: read them in the matching `x`.
    simp only [insFn_ins, ins_lt_ins_iff] at hqr hrq ⊢
    exact pv_not_lt x (ins_lt_iff.mp hr) hqr hrq
  · -- An arc around the block ending after a point of the block ends after the whole block.
    have := pv_lt y hv'
    rw [insFn_ins] at hrq ⊢
    rw [insFn_add _ _ hv']
    simp only [ins] at hqr hrq ⊢
    split_ifs at hqr hrq ⊢ <;> omega
  · -- An arc of the block cannot reach past a point after the block.
    have := pv_lt y hv
    rw [insFn_add _ _ hv] at hrq
    simp only [ins] at hqr hrq
    split_ifs at hqr hrq <;> omega
  · -- Two arcs of the block: read them in the matching `y`.
    rw [insFn_add _ _ hv] at hrq ⊢
    rw [insFn_add _ _ hv']
    have := pv_not_lt y hv' (by omega) (by omega : v' < pv y v)
    omega

/-- **Inserting a block**: the planar matching `y` of `l` points inserted into the planar matching
`x` of `a + b` points, between its first `a` and its last `b` points. The points `a, …, a + l - 1`
of the result carry the arcs of `y`, and the other points the arcs of `x`, the last `b` of them
shifted by `l`. -/
def insertBlock (x : PlanarMatching (a + b)) (y : PlanarMatching l) : PlanarMatching (a + l + b) :=
  ⟨PerfectMatching.ofInvolutive (insertFun_involutive x y) (insertFun_ne x y),
    Equiv.Perm.isNoncrossingMatching_iff.mpr fun i j hij hji => by
      simp only [PerfectMatching.ofInvolutive_apply, Fin.lt_def] at hij hji ⊢
      exact insFn_not_lt x y j.isLt hij hji⟩

private theorem pv_insertBlock (x : PlanarMatching (a + b)) (y : PlanarMatching l) :
    pv (x.insertBlock y) = insFn a l (pv x) (pv y) := by
  funext q
  by_cases hq : q < a + l + b
  · rw [pv_of_lt _ hq]
    exact congrArg Fin.val (PerfectMatching.ofInvolutive_apply _ _ ⟨q, hq⟩)
  · rw [pv_of_le (x.insertBlock y) (show a + l + b ≤ q by omega)]
    simp only [insFn, show ¬q < a by omega, show ¬q < a + l by omega, ↓reduceIte]
    rw [pv_of_le x (show a + b ≤ q - l by omega), ins_of_le (show a ≤ q - l by omega)]
    omega

/-- Inserting a block keeps the arcs of the inserted matching, shifted by `a`. -/
@[simp]
theorem insertBlock_val_castAdd_natAdd (x : PlanarMatching (a + b)) (y : PlanarMatching l)
    (j : Fin l) :
    (x.insertBlock y).val.val (Fin.castAdd b (Fin.natAdd a j)) =
      Fin.castAdd b (Fin.natAdd a (y.val.val j)) := by
  ext
  rw [← pv_coe, pv_insertBlock]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  rw [insFn_add _ _ j.isLt, pv_coe]

/-- Inserting a block keeps the arcs of the outer matching at its first `a` points: the partner of
such a point is shifted past the block when it is one of the last `b` points. -/
@[simp]
theorem coe_insertBlock_val_castAdd_castAdd (x : PlanarMatching (a + b)) (y : PlanarMatching l)
    (i : Fin a) :
    ((x.insertBlock y).val.val (Fin.castAdd b (Fin.castAdd l i)) : ℕ) =
      if (x.val.val (Fin.castAdd b i) : ℕ) < a then (x.val.val (Fin.castAdd b i) : ℕ)
      else (x.val.val (Fin.castAdd b i) : ℕ) + l := by
  have h := insFn_ins a l (pv x) (pv y) i
  rw [ins_of_lt i.isLt] at h
  rw [← pv_coe, pv_insertBlock]
  simp only [Fin.val_castAdd]
  rw [h, ← Fin.val_castAdd b i, pv_coe, ins]

/-- Inserting a block keeps the arcs of the outer matching at its last `b` points, shifted by `l`:
the partner of such a point is shifted past the block when it is one of the last `b` points. -/
@[simp]
theorem coe_insertBlock_val_natAdd (x : PlanarMatching (a + b)) (y : PlanarMatching l)
    (j : Fin b) :
    ((x.insertBlock y).val.val (Fin.natAdd (a + l) j) : ℕ) =
      if (x.val.val (Fin.natAdd a j) : ℕ) < a then (x.val.val (Fin.natAdd a j) : ℕ)
      else (x.val.val (Fin.natAdd a j) : ℕ) + l := by
  have h := insFn_ins a l (pv x) (pv y) (a + j)
  rw [ins_of_le (show a ≤ a + j by omega)] at h
  rw [← pv_coe, pv_insertBlock]
  simp only [Fin.val_natAdd]
  rw [show a + l + j = a + j + l by omega, h, ← Fin.val_natAdd a j, pv_coe, ins]

/-! ### Contracting a pair next to or inside an inserted block -/

private theorem contractFn_apply (a : ℕ) (φ : ℕ → ℕ) (q : ℕ) :
    contractFn a φ q = unskipN a (rejoin φ a (φ (skipN a q))) := by
  have hs : skipN a q ≠ a ∧ skipN a q ≠ a + 1 := by simp only [skipN]; split_ifs <;> omega
  rw [contractFn, erasePair_apply, splice_of_ne _ hs.1 hs.2]

/-- Contracting a pair of consecutive points never produces a point of that pair, for a
fixed-point-free involution. -/
private theorem rejoin_ne {K : ℕ} (x : PlanarMatching K) {c q : ℕ} (hc : c + 1 < K) :
    rejoin (pv x) c (pv x (skipN c q)) ≠ c ∧ rejoin (pv x) c (pv x (skipN c q)) ≠ c + 1 := by
  have hs : skipN c q ≠ c ∧ skipN c q ≠ c + 1 := by simp only [skipN]; split_ifs <;> omega
  have h := splice_ne (pv_pv_eq x) (pv_ne x (by omega : c < K)) (pv_ne x hc) hs.1 hs.2
  rwa [splice_of_ne _ hs.1 hs.2] at h

/-- **Contracting a pair inside the block** is contracting it in the inserted matching. -/
private theorem contractFn_insFn_add {c j : ℕ} (φ : ℕ → ℕ) (y : PlanarMatching l)
    (hj : j + 2 ≤ l) :
    contractFn (c + j) (insFn c l φ (pv y)) = insFn c (l - 2) φ (contractFn j (pv y)) ∧
      circleInd (c + j) (insFn c l φ (pv y)) = circleInd j (pv y) := by
  have e₁ := insFn_add (c := c) φ (pv y) (by omega : j < l)
  have e₂ := insFn_add (c := c) φ (pv y) (by omega : j + 1 < l)
  rw [← Nat.add_assoc] at e₂
  refine ⟨funext fun q => ?_, ?_⟩
  · rcases exists_eq_ins_or_add c (l - 2) q with ⟨u, rfl⟩ | ⟨v, hv, rfl⟩
    · rw [contractFn_apply, insFn_ins,
        show skipN (c + j) (ins c (l - 2) u) = ins c l u by
          simp only [skipN, ins]; split_ifs <;> omega,
        insFn_ins]
      generalize φ u = w
      rw [rejoin_of_ne _ (by simp only [ins]; split_ifs <;> omega)
        (by simp only [ins]; split_ifs <;> omega)]
      simp only [unskipN, ins]
      split_ifs <;> omega
    · have hs : skipN (c + j) (c + v) = c + skipN j v := by
        simp only [skipN]; split_ifs <;> omega
      have hs' : skipN j v < l := by simp only [skipN]; split_ifs <;> omega
      have hw := pv_lt y hs'
      have := pv_lt y (show j < l by omega)
      have := pv_lt y (show j + 1 < l by omega)
      have hr := rejoin_ne y (c := j) (q := v) (by omega)
      rw [contractFn_apply, hs, insFn_add _ _ hs', insFn_add _ _ hv, contractFn_apply]
      generalize pv y (skipN j v) = w at hw hr
      simp only [rejoin, unskipN, e₁, e₂] at hr ⊢
      split_ifs at hr ⊢ <;> omega
  · rw [circleInd, circleInd, e₁]
    simp only [Nat.add_assoc, Nat.add_left_cancel_iff]

/-- Rejoining at a pair of consecutive points outside the inserted block is rejoining at the
corresponding pair of the outer matching. -/
private theorem rejoin_insFn_ins {c l j j' : ℕ} (φ ψ : ℕ → ℕ) (h₁ : ins c l j = j')
    (h₂ : ins c l (j + 1) = j' + 1) (w : ℕ) :
    rejoin (insFn c l φ ψ) j' (ins c l w) = ins c l (rejoin φ j w) := by
  by_cases hw₁ : w = j
  · rw [hw₁, h₁, rejoin_of_eq_left _ rfl, ← h₂, insFn_ins, rejoin_of_eq_left _ rfl]
  by_cases hw₂ : w = j + 1
  · rw [hw₂, h₂, rejoin_of_eq_right _ rfl, ← h₁, insFn_ins, rejoin_of_eq_right _ rfl]
  rw [rejoin_of_ne _ hw₁ hw₂, rejoin_of_ne _ (fun h => hw₁ (ins_injective c l (h.trans h₁.symm)))
    (fun h => hw₂ (ins_injective c l (h.trans h₂.symm)))]

/-- **Contracting a pair before the block** is contracting it in the outer matching. -/
private theorem contractFn_insFn_of_lt {K c j : ℕ} (x : PlanarMatching K) (ψ : ℕ → ℕ)
    (hj : j ≤ c) (hc : c + 2 ≤ K) :
    contractFn j (insFn (c + 2) l (pv x) ψ) = insFn c l (contractFn j (pv x)) ψ ∧
      circleInd j (insFn (c + 2) l (pv x) ψ) = circleInd j (pv x) := by
  have e₁ := insFn_ins (c + 2) l (pv x) ψ j
  rw [ins_of_lt (show j < c + 2 by omega)] at e₁
  refine ⟨funext fun q => ?_, ?_⟩
  · rcases exists_eq_ins_or_add c l q with ⟨u, rfl⟩ | ⟨v, hv, rfl⟩
    · have hs : skipN j (ins c l u) = ins (c + 2) l (skipN j u) := by
        simp only [skipN, ins]; split_ifs <;> omega
      have hw := rejoin_ne x (c := j) (q := u) (by omega)
      rw [contractFn_apply, hs, insFn_ins, insFn_ins, contractFn_apply]
      generalize pv x (skipN j u) = w at hw
      rw [rejoin_insFn_ins _ _ (ins_of_lt (show j < c + 2 by omega))
        (ins_of_lt (show j + 1 < c + 2 by omega))]
      generalize rejoin (pv x) j w = w' at hw
      simp only [unskipN, ins]
      split_ifs <;> omega
    · rw [contractFn_apply, show skipN j (c + v) = c + 2 + v by
          simp only [skipN]; split_ifs <;> omega, insFn_add _ _ hv, insFn_add _ _ hv,
        rejoin_of_ne _ (show c + 2 + ψ v ≠ j by omega) (show c + 2 + ψ v ≠ j + 1 by omega),
        unskipN_of_le (show j ≤ c + 2 + ψ v by omega)]
      omega
  · rw [circleInd, circleInd, e₁]
    simp only [ins]
    split_ifs <;> omega

/-- **Contracting a pair after the block** is contracting it in the outer matching. -/
private theorem contractFn_insFn_of_le {K c j : ℕ} (x : PlanarMatching K) (y : PlanarMatching l)
    (hj : c ≤ j) (hK : j + 2 ≤ K) :
    contractFn (j + l) (insFn c l (pv x) (pv y)) = insFn c l (contractFn j (pv x)) (pv y) ∧
      circleInd (j + l) (insFn c l (pv x) (pv y)) = circleInd j (pv x) := by
  have e₁ := insFn_ins c l (pv x) (pv y) j
  rw [ins_of_le hj] at e₁
  refine ⟨funext fun q => ?_, ?_⟩
  · rcases exists_eq_ins_or_add c l q with ⟨u, rfl⟩ | ⟨v, hv, rfl⟩
    · have hs : skipN (j + l) (ins c l u) = ins c l (skipN j u) := by
        simp only [skipN, ins]; split_ifs <;> omega
      have hw := rejoin_ne x (c := j) (q := u) (by omega)
      rw [contractFn_apply, hs, insFn_ins, insFn_ins, contractFn_apply]
      generalize pv x (skipN j u) = w at hw
      rw [rejoin_insFn_ins _ _ (ins_of_le hj)
        (by rw [ins_of_le (show c ≤ j + 1 by omega)]; omega)]
      generalize rejoin (pv x) j w = w' at hw
      simp only [unskipN, ins]
      split_ifs <;> omega
    · have := pv_lt y hv
      rw [contractFn_apply, show skipN (j + l) (c + v) = c + v by
          simp only [skipN]; split_ifs <;> omega, insFn_add _ _ hv, insFn_add _ _ hv,
        rejoin_of_ne _ (show c + pv y v ≠ j + l by omega)
          (show c + pv y v ≠ j + l + 1 by omega),
        unskipN_of_lt (show c + pv y v < j + l by omega)]
  · rw [circleInd, circleInd, e₁]
    simp only [ins]
    split_ifs <;> omega

/-! ### Gluing next to or inside an inserted block -/

/-- Gluing a block of nested pairs splits into gluing its `i` innermost pairs, then its `j`
outermost ones. -/
private theorem glueFn_add (c j : ℕ) :
    ∀ (i : ℕ) (φ : ℕ → ℕ), glueFn c (j + i) φ = glueFn c j (glueFn (c + j) i φ) ∧
      glueCircles c (j + i) φ = glueCircles (c + j) i φ + glueCircles c j (glueFn (c + j) i φ)
  | 0, φ => ⟨rfl, by simp [glueCircles, glueFn]⟩
  | i + 1, φ => by
    obtain ⟨ih₁, ih₂⟩ := glueFn_add c j i (contractFn (c + (j + i)) φ)
    rw [← Nat.add_assoc j i 1]
    simp only [glueFn, glueCircles]
    rw [Nat.add_assoc c j i, ih₁, ih₂]
    exact ⟨rfl, by omega⟩

/-- Gluing a block of nested pairs inside an inserted block is gluing them in the inserted
matching. -/
private theorem glueFn_insFn_add {c d : ℕ} (φ : ℕ → ℕ) :
    ∀ (j M : ℕ) (y : PlanarMatching M), d + 2 * j ≤ M →
      glueFn (c + d) j (insFn c M φ (pv y)) = insFn c (M - 2 * j) φ (glueFn d j (pv y)) ∧
      glueCircles (c + d) j (insFn c M φ (pv y)) = glueCircles d j (pv y)
  | 0, M, y, _ => ⟨rfl, rfl⟩
  | j + 1, M, y, hM => by
    obtain ⟨y', hy'⟩ := exists_pv_eq_contractFn y (a := d + j) (by omega)
    obtain ⟨h₁, h₂⟩ := contractFn_insFn_add (c := c) φ y (j := d + j) (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueFn_insFn_add (c := c) (d := d) φ j (M - 2) y' (by omega)
    simp only [glueFn, glueCircles]
    rw [show c + d + j = c + (d + j) by omega, h₁, ← hy', ih₁, h₂, ih₂,
      show M - 2 - 2 * j = M - 2 * (j + 1) by omega]
    exact ⟨rfl, rfl⟩

/-- Gluing a block of nested pairs before an inserted block is gluing them in the outer
matching. -/
private theorem glueFn_insFn_of_lt {c : ℕ} (ψ : ℕ → ℕ) :
    ∀ (j K : ℕ) (x : PlanarMatching K), c + 2 * j ≤ K →
      glueFn c j (insFn (c + 2 * j) l (pv x) ψ) = insFn c l (glueFn c j (pv x)) ψ ∧
      glueCircles c j (insFn (c + 2 * j) l (pv x) ψ) = glueCircles c j (pv x)
  | 0, K, x, _ => ⟨rfl, rfl⟩
  | j + 1, K, x, hK => by
    obtain ⟨x', hx'⟩ := exists_pv_eq_contractFn x (a := c + j) (by omega)
    obtain ⟨h₁, h₂⟩ := contractFn_insFn_of_lt (l := l) (c := c + 2 * j) x ψ (j := c + j)
      (by omega) (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueFn_insFn_of_lt (c := c) ψ j (K - 2) x' (by omega)
    simp only [glueFn, glueCircles]
    rw [show c + 2 * (j + 1) = c + 2 * j + 2 by omega, h₁, ← hx', ih₁, h₂, ih₂]
    exact ⟨rfl, rfl⟩

/-- Gluing a block of nested pairs after an inserted block is gluing them in the outer
matching. -/
private theorem glueFn_insFn_of_le {c : ℕ} (y : PlanarMatching l) :
    ∀ (j K : ℕ) (x : PlanarMatching K), c + 2 * j ≤ K →
      glueFn (c + l) j (insFn c l (pv x) (pv y)) = insFn c l (glueFn c j (pv x)) (pv y) ∧
      glueCircles (c + l) j (insFn c l (pv x) (pv y)) = glueCircles c j (pv x)
  | 0, K, x, _ => ⟨rfl, rfl⟩
  | j + 1, K, x, hK => by
    obtain ⟨x', hx'⟩ := exists_pv_eq_contractFn x (a := c + j) (by omega)
    obtain ⟨h₁, h₂⟩ := contractFn_insFn_of_le x y (c := c) (j := c + j) (by omega) (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueFn_insFn_of_le (c := c) y j (K - 2) x' (by omega)
    simp only [glueFn, glueCircles]
    rw [show c + l + j = c + j + l by omega, h₁, ← hx', ih₁, h₂, ih₂]
    exact ⟨rfl, rfl⟩

/-! ### Identities between insertions -/

/-- Inserting two blocks at the same place is inserting their juxtaposition. -/
private theorem insFn_insFn_eq {c l' : ℕ} (φ : ℕ → ℕ) (y : PlanarMatching l)
    (z : PlanarMatching l') :
    insFn c l (insFn c l' φ (pv z)) (pv y) = insFn c (l + l') φ (appendFn l l' (pv y) (pv z)) := by
  funext q
  rcases exists_eq_ins_or_add c (l + l') q with ⟨u, rfl⟩ | ⟨v, hv, rfl⟩
  · rw [insFn_ins, show ins c (l + l') u = ins c l (ins c l' u) by
        simp only [ins]; split_ifs <;> omega,
      insFn_ins, insFn_ins]
    simp only [ins]
    split_ifs <;> omega
  · rw [insFn_add _ _ hv]
    by_cases hvl : v < l
    · rw [insFn_add _ _ hvl, appendFn_of_lt _ _ hvl]
    · have := pv_lt z (show v - l < l' by omega)
      rw [show c + v = ins c l (c + (v - l)) by
          rw [ins_of_le (show c ≤ c + (v - l) by omega)]; omega,
        insFn_ins, insFn_add _ _ (show v - l < l' by omega),
        appendFn_of_le_of_lt _ _ (show l ≤ v by omega) hv,
        ins_of_le (show c ≤ c + pv z (v - l) by omega)]
      omega

/-- Juxtaposing two matchings with inserted blocks is inserting the blocks into the
juxtaposition. -/
private theorem appendFn_insFn_insFn {n m p l' : ℕ} (x : PlanarMatching (n + m))
    (y : PlanarMatching l) (x' : PlanarMatching (m + p)) (y' : PlanarMatching l') :
    appendFn (n + l + m) (m + l' + p) (insFn n l (pv x) (pv y)) (insFn m l' (pv x') (pv y')) =
      insFn n l (insFn (n + 2 * m) l' (appendFn (n + m) (m + p) (pv x) (pv x')) (pv y'))
        (pv y) := by
  funext q
  rcases exists_eq_ins_or_add n l q with ⟨u, rfl⟩ | ⟨v, hv, rfl⟩
  · rw [insFn_ins]
    rcases exists_eq_ins_or_add (n + 2 * m) l' u with ⟨w, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [insFn_ins]
      by_cases hw₁ : w < n + m
      · -- A point of the bottom of the first matching.
        have := pv_lt x hw₁
        rw [ins_of_lt (show w < n + 2 * m by omega), appendFn_of_lt _ _ hw₁,
          ins_of_lt (show pv x w < n + 2 * m by omega),
          appendFn_of_lt (l := m + l' + p) _ _
            (show ins n l w < n + l + m by simp only [ins]; split_ifs <;> omega),
          insFn_ins]
      by_cases hw₂ : w < n + m + (m + p)
      · -- A point of the top of the second matching.
        have := pv_lt x' (show w - (n + m) < m + p by omega)
        rw [appendFn_of_le_of_lt _ _ (show n + m ≤ w by omega) hw₂,
          appendFn_of_le_of_lt (k := n + l + m) (l := m + l' + p) _ _
            (show n + l + m ≤ ins n l (ins (n + 2 * m) l' w) by
              simp only [ins]; split_ifs <;> omega)
            (show ins n l (ins (n + 2 * m) l' w) < n + l + m + (m + l' + p) by
              simp only [ins]; split_ifs <;> omega),
          show ins n l (ins (n + 2 * m) l' w) - (n + l + m) =
            ins m l' (w - (n + m)) by simp only [ins]; split_ifs <;> omega,
          insFn_ins]
        simp only [ins]
        split_ifs <;> omega
      · -- A point beyond both matchings.
        rw [appendFn_of_le (k := n + m) (l := m + p) _ _ (show n + m + (m + p) ≤ w by omega),
          appendFn_of_le (k := n + l + m) (l := m + l' + p) _ _
            (show n + l + m + (m + l' + p) ≤ ins n l (ins (n + 2 * m) l' w) by
              simp only [ins]; split_ifs <;> omega)]
    · -- A point of the block inserted into the second matching.
      have := pv_lt y' ht
      rw [insFn_add _ _ ht, ins_of_le (show n ≤ n + 2 * m + pv y' t by omega),
        ins_of_le (show n ≤ n + 2 * m + t by omega),
        appendFn_of_le_of_lt (k := n + l + m) (l := m + l' + p) _ _
          (show n + l + m ≤ n + 2 * m + t + l by omega)
          (show n + 2 * m + t + l < n + l + m + (m + l' + p) by omega),
        show n + 2 * m + t + l - (n + l + m) = m + t by omega, insFn_add _ _ ht]
      omega
  · -- A point of the block inserted into the first matching.
    rw [insFn_add _ _ hv, appendFn_of_lt (l := m + l' + p) _ _ (show n + v < n + l + m by omega),
      insFn_add _ _ hv]

/-- Inserting a block into a matching with an inserted block, at a point of the first block, is
inserting the block into the first block. -/
private theorem insFn_insFn_assoc {n n' l' : ℕ} (φ : ℕ → ℕ) (ψ : ℕ → ℕ)
    (z : PlanarMatching l') (hn' : n' ≤ l) :
    insFn (n + n') l' (insFn n l φ ψ) (pv z) = insFn n (l + l') φ (insFn n' l' ψ (pv z)) := by
  funext q
  rcases exists_eq_ins_or_add n (l + l') q with ⟨u, rfl⟩ | ⟨v, hv, rfl⟩
  · rw [insFn_ins, show ins n (l + l') u = ins (n + n') l' (ins n l u) by
        simp only [ins]; split_ifs <;> omega, insFn_ins, insFn_ins]
    simp only [ins]
    split_ifs <;> omega
  · rw [insFn_add _ _ hv]
    rcases exists_eq_ins_or_add n' l' v with ⟨w, rfl⟩ | ⟨t, ht, rfl⟩
    · have hw : w < l := by simp only [ins] at hv; split_ifs at hv <;> omega
      rw [insFn_ins, show n + ins n' l' w = ins (n + n') l' (n + w) by
          simp only [ins]; split_ifs <;> omega, insFn_ins, insFn_add _ _ hw]
      simp only [ins]
      split_ifs <;> omega
    · rw [insFn_add _ _ ht, ← Nat.add_assoc, insFn_add _ _ ht]
      omega

/-! ### Laws of block insertion -/

private theorem insFn_zero (c : ℕ) (φ ψ : ℕ → ℕ) : insFn c 0 φ ψ = φ := by
  funext q
  simp only [insFn, ins, Nat.add_zero, Nat.sub_zero]
  split_ifs <;> rfl

private theorem insFn_zero_left (x : PlanarMatching (0 + 0)) (y : PlanarMatching l) :
    insFn 0 l (pv x) (pv y) = pv y := by
  funext q
  by_cases hq : q < l
  · simpa only [Nat.zero_add] using insFn_add (c := 0) (pv x) (pv y) hq
  · have e : q = ins 0 l (q - l) := by rw [ins_of_le (Nat.zero_le _)]; omega
    rw [e, insFn_ins, pv_of_le x (Nat.zero_le _), ← e, pv_of_le y (by omega)]

/-- Juxtaposing on the right does not move a block inserted into the left factor. -/
private theorem appendFn_insFn_left {K K' c : ℕ} (φ ψ χ : ℕ → ℕ) (hc : c ≤ K) :
    appendFn (K + l) K' (insFn c l φ ψ) χ = insFn c l (appendFn K K' φ χ) ψ := by
  funext q
  rcases exists_eq_ins_or_add c l q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [insFn_ins]
    by_cases h₁ : v < K
    · have : ins c l v < K + l := by simp only [ins]; split_ifs <;> omega
      rw [appendFn_of_lt _ _ this, insFn_ins, appendFn_of_lt _ _ h₁]
    rw [ins_of_le (by omega)]
    by_cases h₂ : v < K + K'
    · rw [appendFn_of_le_of_lt _ _ (by omega) (by omega), appendFn_of_le_of_lt _ _ (by omega) h₂,
        ins_of_le (by omega), Nat.add_sub_add_right]
      omega
    · rw [appendFn_of_le _ _ (by omega), appendFn_of_le _ _ (by omega), ins_of_le (by omega)]
  · rw [appendFn_of_lt _ _ (by omega), insFn_add _ _ hj, insFn_add _ _ hj]

/-- Juxtaposing on the left moves a block inserted into the right factor past the left factor. -/
private theorem appendFn_insFn_right {K K' c : ℕ} (φ ψ χ : ℕ → ℕ) (hc : c ≤ K')
    (hφ : ∀ q < K, φ q < K) :
    appendFn K (K' + l) φ (insFn c l χ ψ) = insFn (K + c) l (appendFn K K' φ χ) ψ := by
  have hadd : ∀ i, ins (K + c) l (K + i) = K + ins c l i := fun i => by
    simp only [ins]; split_ifs <;> omega
  funext q
  rcases exists_eq_ins_or_add (K + c) l q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [insFn_ins]
    by_cases h₁ : v < K
    · have := hφ v h₁
      rw [ins_of_lt (by omega), appendFn_of_lt _ _ h₁, appendFn_of_lt _ _ h₁, ins_of_lt (by omega)]
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (Nat.not_lt.mp h₁)
    rw [hadd]
    by_cases h₂ : u < K'
    · have : ins c l u < K' + l := by simp only [ins]; split_ifs <;> omega
      rw [appendFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel_left, insFn_ins,
        appendFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel_left, hadd]
    · have : K' + l ≤ ins c l u := by simp only [ins]; split_ifs <;> omega
      rw [appendFn_of_le _ _ (by omega), appendFn_of_le _ _ (by omega), hadd]
  · rw [insFn_add _ _ hj, appendFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_assoc K c j,
      Nat.add_sub_cancel_left, insFn_add _ _ hj, Nat.add_assoc]

/-- Inserting the empty planar matching changes nothing. -/
@[simp]
theorem insertBlock_zero (x : PlanarMatching (a + b)) (y : PlanarMatching 0) :
    x.insertBlock y = x :=
  ext_pv fun q _ => by rw [pv_insertBlock, insFn_zero]

/-- Inserting a block into the empty planar matching gives the block, up to the relabelling of the
size. -/
@[simp]
theorem zero_insertBlock (x : PlanarMatching (0 + 0)) (y : PlanarMatching l) :
    x.insertBlock y = cast (by omega) y :=
  ext_pv fun q _ => by rw [pv_insertBlock, pv_cast, insFn_zero_left]

/-- Inserting a fully nested matching into a fully nested matching, between its two halves, gives a
fully nested matching, up to the relabelling of the size. -/
@[simp]
theorem nested_insertBlock (n n' : ℕ) :
    (nested n).insertBlock (nested n') = cast (by omega) (nested (n + n')) := by
  refine ext_pv fun q hq => ?_
  rw [pv_insertBlock, pv_cast, pv_nested (n + n') (by omega)]
  rcases exists_eq_ins_or_add n (n' + n') q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · have hv : v < n + n := ins_lt_iff.mp hq
    rw [insFn_ins, pv_nested n hv]
    simp only [ins]
    split_ifs <;> omega
  · rw [insFn_add _ _ hj, pv_nested n' hj]
    omega

/-- **Block insertion is associative**: inserting `z` into the result of inserting `y` into `x`,
at a point of the block of `y`, is inserting into `x` the result of inserting `z` into `y`, up to
the relabelling of the sizes. -/
theorem cast_insertBlock_insertBlock {a' b' b'' : ℕ} (h : a + (a' + b') + b = a + a' + b'')
    (x : PlanarMatching (a + b)) (y : PlanarMatching (a' + b')) (z : PlanarMatching l) :
    (cast h (x.insertBlock y)).insertBlock z =
      cast (by omega) (x.insertBlock (y.insertBlock z)) := by
  refine ext_pv fun q _ => ?_
  rw [pv_cast, pv_insertBlock, pv_cast_eq, pv_insertBlock, pv_insertBlock, pv_insertBlock,
    insFn_insFn_assoc _ _ z (by omega : a' ≤ a' + b'), Nat.add_right_comm a' b' l]

/-- Block insertion commutes with relabelling the size of the inserted matching. -/
theorem insertBlock_cast {l' : ℕ} (h : l = l') (x : PlanarMatching (a + b))
    (y : PlanarMatching l) : x.insertBlock (cast h y) = cast (by omega) (x.insertBlock y) := by
  subst h
  simp

/-- Block insertion commutes with relabelling the size of the outer matching, as long as the
insertion position stays the same. -/
theorem cast_insertBlock {a' b' : ℕ} (ha : a = a') (h : a + b = a' + b')
    (x : PlanarMatching (a + b)) (y : PlanarMatching l) :
    (cast h x).insertBlock y = cast (by omega) (x.insertBlock y) := by
  subst ha
  obtain rfl : b = b' := by omega
  simp

/-- Juxtaposing on the right does not move a block inserted into the left factor. -/
theorem insertBlock_append {l' : ℕ} (x : PlanarMatching (a + b)) (y : PlanarMatching l)
    (z : PlanarMatching l') :
    (x.insertBlock y).append z =
      cast (by omega) ((cast (Nat.add_assoc a b l') (x.append z)).insertBlock y) := by
  refine ext_pv fun q _ => ?_
  rw [pv_cast, pv_insertBlock, pv_cast_eq, pv_append_eq, pv_append_eq, pv_insertBlock,
    Nat.add_right_comm a l b, appendFn_insFn_left _ _ _ (Nat.le_add_right a b)]

/-- Juxtaposing on the left moves a block inserted into the right factor past the left factor. -/
theorem append_insertBlock {l' : ℕ} (x : PlanarMatching l') (z : PlanarMatching (a + b))
    (y : PlanarMatching l) :
    x.append (z.insertBlock y) =
      cast (by omega) ((cast (Nat.add_assoc l' a b).symm (x.append z)).insertBlock y) := by
  refine ext_pv fun q _ => ?_
  rw [pv_cast, pv_insertBlock, pv_cast_eq, pv_append_eq, pv_append_eq, pv_insertBlock,
    Nat.add_right_comm a l b, appendFn_insFn_right _ _ _ (Nat.le_add_right a b)
      fun q hq => pv_lt x hq]

/-- Inserting two blocks at the same position is inserting their juxtaposition. -/
theorem cast_insertBlock_insertBlock_eq_insertBlock_append {l' : ℕ} (x : PlanarMatching (a + b))
    (y : PlanarMatching l) (z : PlanarMatching l') :
    (cast (Nat.add_assoc a l' b) (x.insertBlock z)).insertBlock y =
      cast (by omega) (x.insertBlock (y.append z)) := by
  refine ext_pv fun q _ => ?_
  rw [pv_cast, pv_insertBlock, pv_cast_eq, pv_insertBlock, pv_insertBlock, pv_append_eq,
    insFn_insFn_eq]

/-- Inserting a block into a matching with no points after the insertion position juxtaposes on
the right. -/
theorem add_zero_insertBlock (x : PlanarMatching (a + 0)) (y : PlanarMatching l) :
    x.insertBlock y = cast (by omega) (x.append y) := by
  refine ext_pv fun q hq => ?_
  rw [pv_cast, pv_insertBlock, pv_append_eq]
  rcases exists_eq_ins_or_add a l q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · have hv : v < a + 0 := ins_lt_iff.mp hq
    rw [insFn_ins, ins_of_lt (show v < a by omega), appendFn_of_lt _ _ hv,
      ins_of_lt (lt_of_lt_of_eq (pv_lt x hv) (Nat.add_zero a))]
  · rw [insFn_add _ _ hj, appendFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_zero,
      Nat.add_sub_cancel_left]

/-- Inserting a block into a matching with no points before the insertion position juxtaposes on
the left. -/
theorem zero_add_insertBlock (x : PlanarMatching (0 + b)) (y : PlanarMatching l) :
    x.insertBlock y = cast (by omega) (y.append (cast (Nat.zero_add b) x)) := by
  refine ext_pv fun q hq => ?_
  rw [pv_cast, pv_insertBlock, pv_append_eq]
  rcases exists_eq_ins_or_add 0 l q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · have hv : v < 0 + b := ins_lt_iff.mp hq
    rw [insFn_ins, ins_of_le (Nat.zero_le _), ins_of_le (Nat.zero_le _),
      appendFn_of_le_of_lt _ _ (by omega) (by omega), Nat.add_sub_cancel, pv_cast]
    omega
  · rw [insFn_add _ _ hj, Nat.zero_add (pv y j), Nat.zero_add j, appendFn_of_lt _ _ hj]

/-- Block insertion determines both the outer and the inserted matching. -/
@[simp]
theorem insertBlock_eq_insertBlock_iff {x₁ x₂ : PlanarMatching (a + b)}
    {y₁ y₂ : PlanarMatching l} :
    x₁.insertBlock y₁ = x₂.insertBlock y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have e := congrArg pv h
  rw [pv_insertBlock, pv_insertBlock] at e
  refine ⟨ext_pv fun q _ => ?_, ext_pv fun q hq => ?_⟩
  · have := congrFun e (ins a l q)
    rw [insFn_ins, insFn_ins] at this
    exact ins_injective a l this
  · have := congrFun e (a + q)
    rw [insFn_add _ _ hq, insFn_add _ _ hq] at this
    omega

/-- Inserting a fixed block is injective in the outer matching. -/
theorem insertBlock_left_injective (y : PlanarMatching l) :
    Function.Injective fun x : PlanarMatching (a + b) => x.insertBlock y :=
  fun _ _ h => (insertBlock_eq_insertBlock_iff.mp h).1

/-- Inserting into a fixed matching is injective in the inserted block. -/
theorem insertBlock_right_injective (x : PlanarMatching (a + b)) :
    Function.Injective fun y : PlanarMatching l => x.insertBlock y :=
  fun _ _ h => (insertBlock_eq_insertBlock_iff.mp h).2

end PlanarMatching

namespace TLDiagram

open PlanarMatching

variable {n m p n' m' p' n'' m'' : ℕ}

/-- The **tensor product** of Temperley–Lieb diagrams `f : n → m` and `g : n' → m'`: the diagram
`n + n' → m + m'` with `g` placed to the right of `f`. Its matching inserts the matching of `g`
between the bottom and the top points of `f`, and its circles are those of `f` and of `g`. -/
def tensor (f : TLDiagram n m) (g : TLDiagram n' m') : TLDiagram (n + n') (m + m') where
  matching := PlanarMatching.cast (by omega) (f.matching.insertBlock g.matching)
  circles := f.circles + g.circles

/-- The matching of a tensor product: the matching of the right factor inserted as a block into
that of the left factor. -/
@[simp]
theorem matching_tensor (f : TLDiagram n m) (g : TLDiagram n' m') :
    (f.tensor g).matching = PlanarMatching.cast (by omega) (f.matching.insertBlock g.matching) :=
  (rfl)

/-- The circles of a tensor product are those of both factors. -/
@[simp]
theorem circles_tensor (f : TLDiagram n m) (g : TLDiagram n' m') :
    (f.tensor g).circles = f.circles + g.circles := (rfl)

/-- Transporting the left factor of a tensor product transports the tensor product. -/
@[simp]
theorem cast_tensor {n₁ m₁ : ℕ} (hn : n = n₁) (hm : m = m₁) (f : TLDiagram n m)
    (g : TLDiagram n' m') :
    (TLDiagram.cast hn hm f).tensor g = TLDiagram.cast (by rw [hn]) (by rw [hm]) (f.tensor g) := by
  subst hn hm
  simp

/-- Transporting the right factor of a tensor product transports the tensor product. -/
@[simp]
theorem tensor_cast {n₁ m₁ : ℕ} (hn : n' = n₁) (hm : m' = m₁) (f : TLDiagram n m)
    (g : TLDiagram n' m') :
    f.tensor (TLDiagram.cast hn hm g) = TLDiagram.cast (by rw [hn]) (by rw [hm]) (f.tensor g) := by
  subst hn hm
  simp

private theorem pv_matching_tensor (f : TLDiagram n m) (g : TLDiagram n' m') :
    pv (f.tensor g).matching = insFn n (n' + m') (pv f.matching) (pv g.matching) := by
  rw [matching_tensor, pv_cast_eq, pv_insertBlock]

/-- **The interchange law**: stacking two tensor products is the tensor product of the stacks,
`(f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) = (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂)`. Both sides have the same matching and close the
same circles. -/
theorem tensor_comp_tensor (f₁ : TLDiagram n m) (f₂ : TLDiagram n' m') (g₁ : TLDiagram m p)
    (g₂ : TLDiagram m' p') :
    (f₁.tensor f₂).comp (g₁.tensor g₂) = (f₁.comp g₁).tensor (f₂.comp g₂) := by
  -- The juxtaposition of the two tensor products is that of `f₁` and `g₁`, with the blocks of
  -- `f₂` and `g₂` inserted.
  have hL : pv ((f₁.tensor f₂).matching.append (g₁.tensor g₂).matching) =
      insFn n (n' + m') (insFn (n + 2 * m) (m' + p')
        (appendFn (n + m) (m + p) (pv f₁.matching) (pv g₁.matching)) (pv g₂.matching))
        (pv f₂.matching) := by
    rw [pv_append_eq, pv_matching_tensor, pv_matching_tensor,
      show n + n' + (m + m') = n + (n' + m') + m by omega,
      show m + m' + (p + p') = m + (m' + p') + p by omega,
      appendFn_insFn_insFn f₁.matching f₂.matching g₁.matching g₂.matching]
  -- Gluing the `m` pairs between `f₁` and `g₁`, which lie after the block of `f₂`…
  have hB := glueFn_insFn_of_le (c := n) f₂.matching m (n + 2 * m + (m' + p') + p)
    ((PlanarMatching.cast (k' := n + 2 * m + p) (by omega)
      (f₁.matching.append g₁.matching)).insertBlock g₂.matching) (by omega)
  -- … and before the block of `g₂`, …
  have hC := glueFn_insFn_of_lt (c := n) (l := m' + p') (pv g₂.matching) m (n + m + (m + p))
    (f₁.matching.append g₁.matching) (by omega)
  -- … then the `m'` pairs between `f₂` and `g₂`, inside the merged block.
  have hD := glueFn_insFn_add (c := n) (d := n')
    (pv (glueMiddle m (f₁.matching.append g₁.matching))) m' (n' + m' + (m' + p'))
    (f₂.matching.append g₂.matching) (by omega)
  have hE := glueFn_add (n + n') m' m
    (insFn n (n' + m') (insFn (n + 2 * m) (m' + p')
      (appendFn (n + m) (m + p) (pv f₁.matching) (pv g₁.matching)) (pv g₂.matching))
      (pv f₂.matching))
  simp only [pv_insertBlock, pv_cast_eq, pv_append_eq] at hB
  simp only [pv_append_eq] at hC
  simp only [pv_glueMiddle, pv_append_eq] at hD
  rw [show n + n' + m' = n + (n' + m') by omega, hB.1, hB.2, hC.1, hC.2, insFn_insFn_eq, hD.1,
    hD.2, show n' + m' + (m' + p') - 2 * m' = n' + p' by omega] at hE
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_comp, pv_glueMiddle, hL,
      show glueFn (n + n') (m + m') = glueFn (n + n') (m' + m) by rw [Nat.add_comm m m'], hE.1,
      pv_matching_tensor]
    simp only [matching_comp, pv_glueMiddle, pv_append_eq]
  · simp only [circles_comp, circles_tensor, glueMiddleCircles_eq]
    rw [hL, show glueCircles (n + n') (m + m') = glueCircles (n + n') (m' + m) by
      rw [Nat.add_comm m m'], hE.2]
    simp only [pv_append_eq]
    omega

/-- The tensor product of identity diagrams is an identity diagram: `n` straight strands next to
`n'` straight strands are `n + n'` straight strands. -/
@[simp]
theorem id_tensor_id (n n' : ℕ) : (id n).tensor (id n') = id (n + n') := by
  ext : 1
  · simp [matching_id]
  · simp

/-- **Associativity of the tensor product**: `(f ⊗ g) ⊗ h` is `f ⊗ (g ⊗ h)`, transported along the
associativity of the numbers of points. -/
theorem tensor_assoc (f : TLDiagram n m) (g : TLDiagram n' m') (h : TLDiagram n'' m'') :
    (f.tensor g).tensor h = TLDiagram.cast (Nat.add_assoc n n' n'').symm
      (Nat.add_assoc m m' m'').symm (f.tensor (g.tensor h)) := by
  ext : 1
  · apply eq_of_pv_eq
    rw [matching_cast, pv_cast_eq]
    simp only [pv_matching_tensor]
    rw [insFn_insFn_assoc (l := n' + m') _ _ h.matching (by omega),
      show n' + m' + (n'' + m'') = n' + n'' + (m' + m'') by omega]
  · simp only [circles_tensor, circles_cast]
    omega

/-- The empty diagram on the left is a unit for the tensor product. -/
@[simp]
theorem id_zero_tensor (f : TLDiagram n m) :
    (id 0).tensor f = TLDiagram.cast (Nat.zero_add n).symm (Nat.zero_add m).symm f := by
  ext : 1
  · simp [matching_id]
  · simp

/-- The empty diagram on the right is a unit for the tensor product. -/
@[simp]
theorem tensor_id_zero (f : TLDiagram n m) : f.tensor (id 0) = f := by
  ext : 1
  · simp [matching_id]
  · simp

/-- Tensoring with a diagram `0 → 0` on the left keeps the matching, up to the relabelling of the
sizes. -/
theorem matching_zero_tensor (g : TLDiagram 0 0) (f : TLDiagram n m) :
    (g.tensor f).matching = PlanarMatching.cast (by omega) f.matching := by
  rw [matching_tensor, zero_insertBlock, PlanarMatching.cast_cast]

/-- Tensoring with a diagram `0 → 0` on the right keeps the matching. -/
theorem matching_tensor_zero (f : TLDiagram n m) (g : TLDiagram 0 0) :
    (f.tensor g).matching = f.matching := by
  apply eq_of_pv_eq
  rw [matching_tensor, pv_cast_eq, insertBlock_zero]

/-- The matching of a tensor product determines the matchings of both factors. -/
theorem matching_tensor_eq_iff {f₁ f₂ : TLDiagram n m} {g₁ g₂ : TLDiagram n' m'} :
    (f₁.tensor g₁).matching = (f₂.tensor g₂).matching ↔
      f₁.matching = f₂.matching ∧ g₁.matching = g₂.matching := by
  rw [matching_tensor, matching_tensor, EmbeddingLike.apply_eq_iff_eq,
    insertBlock_eq_insertBlock_iff]

/-- Tensoring with a fixed diagram on the right is injective. -/
@[simp]
theorem tensor_left_inj (g : TLDiagram n' m') {f₁ f₂ : TLDiagram n m} :
    f₁.tensor g = f₂.tensor g ↔ f₁ = f₂ := by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  have hc := congrArg circles h
  rw [circles_tensor, circles_tensor] at hc
  exact TLDiagram.ext (matching_tensor_eq_iff.mp (congrArg matching h)).1 (by omega)

/-- Tensoring with a fixed diagram on the left is injective. -/
@[simp]
theorem tensor_right_inj (f : TLDiagram n m) {g₁ g₂ : TLDiagram n' m'} :
    f.tensor g₁ = f.tensor g₂ ↔ g₁ = g₂ := by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  have hc := congrArg circles h
  rw [circles_tensor, circles_tensor] at hc
  exact TLDiagram.ext (matching_tensor_eq_iff.mp (congrArg matching h)).2 (by omega)

end TLDiagram

end TauCeti
