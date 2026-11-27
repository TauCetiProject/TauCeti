/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Denumerable
public import TauCeti.ModelTheory.RelationalConfiguration.GraphClass
public import TauCeti.ModelTheory.RelationalConfiguration.OrderClass
public import TauCeti.ModelTheory.RelationalConfiguration.Unravelling
public import TauCeti.Order.Condensation
import Mathlib.Order.Interval.Set.Nat

/-!
# The linear order of an unravelled graph code

For a code `c : RelationalConfiguration Language.graph ℕ` with the colouring `χ_c = unravelColor c`
of `List ℚ`, order `List ℚ × ℕ` lexicographically, first by the `List ℚ` coordinate and then,
inside the block of `x`, by the order of type `ω + (χ_c(x) + 2)` on `ℕ` that puts the indices
`≥ χ_c(x) + 2` first, in increasing order, and then the indices `< χ_c(x) + 2`, in increasing
order. Relabelled along the fixed bijection `ℕ ≃ List ℚ × ℕ`, this is a code
`unravelOrderCode c` of `Language.order`.

This file proves that `unravelOrderCode` is continuous, that its values are coded linear orders
for every code, simple graph or not, and that its images are isomorphic exactly when the codes
are. An order automorphism `Φ` of `List ℚ` with `χ_d ∘ Φ = χ_c`, given by the unravelling lemma,
extends block by block. Conversely, call two points near (`TauCeti.IsNear`) when the interval
between them is finite: the points near a point of the `ω`-part of a block are infinitely many,
and the points near a point of the finite part are that finite part, of size `χ_c(x) + 2`, because
the order of `List ℚ` is dense. An isomorphism of the images preserves nearness, so it maps finite
parts to finite parts of the same size, in order, and induces a colour-preserving order
automorphism of `List ℚ`. Hence countable linear orders are Borel complete.

## Main definitions

* `TauCeti.RelationalConfiguration.unravelOrderRel χ`: the order of `List ℚ × ℕ` for a colouring
  `χ` of `List ℚ`.
* `TauCeti.RelationalConfiguration.unravelOrderCode c`: the code on `ℕ` of the order for the
  colouring `unravelColor c`.

## Main results

* `TauCeti.RelationalConfiguration.continuous_unravelOrderCode`: the map is continuous.
* `TauCeti.RelationalConfiguration.unravelOrderCode_mem_linearOrderClass`: its values are coded
  linear orders.
* `TauCeti.RelationalConfiguration.isoSetoid_unravelOrderCode`: isomorphic codes have isomorphic
  images.
* `TauCeti.RelationalConfiguration.exists_orderIso_of_unravelOrderRel`: an isomorphism of the
  orders for two colourings induces a colour-preserving order automorphism of `List ℚ`.
* `TauCeti.RelationalConfiguration.isoSetoid_unravelOrderCode_iff`: the images are isomorphic
  exactly when the codes are.
* `TauCeti.RelationalConfiguration.exists_continuous_reduction_linearOrderClass`: a continuous map
  to coded linear orders reduces isomorphism of graph codes to isomorphism of its values.
* `TauCeti.RelationalConfiguration.borelComplete_linearOrderClass`: countable linear orders are
  Borel complete.

## References

* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable structures*,
  J. Symbolic Logic 54 (1989), §2.
* A. Montalbán, *Computable structure theory: within the arithmetic*, author's draft of Part 1
  (2019), Lemma VI.18.
-/

public section

open FirstOrder FirstOrder.Language Set

namespace TauCeti.RelationalConfiguration

/-! ### The block order and the order of `List ℚ × ℕ` -/

/-- The position of the index `i` in a block of colour `n`, ordered as `ω + (n + 2)`: the indices
`≥ n + 2` come first, in increasing order, and then the indices `< n + 2`. -/
def blockKey (n i : ℕ) : Lex (Bool × ℕ) :=
  toLex (decide (i < n + 2), i)

/-- Distinct indices have distinct positions in a block. -/
theorem blockKey_injective (n : ℕ) : Function.Injective (blockKey n) := fun i j h => by
  simpa [blockKey] using congrArg (fun p => (ofLex p).2) h

/-- In a block of colour `n`, `i` comes before `j` exactly when `i ≥ n + 2` and `j < n + 2`, or
`i` and `j` are on the same side of `n + 2` and `i ≤ j`. -/
@[simp]
theorem blockKey_le_blockKey_iff {n i j : ℕ} :
    blockKey n i ≤ blockKey n j ↔ n + 2 ≤ i ∧ j < n + 2 ∨ (i < n + 2 ↔ j < n + 2) ∧ i ≤ j := by
  rw [blockKey, blockKey, Prod.Lex.toLex_le_toLex]
  rcases lt_or_ge i (n + 2) with hi | hi <;> rcases lt_or_ge j (n + 2) with hj | hj <;>
    simp [hi, hj, hi.not_gt, hj.not_gt]

/-- In a block of colour `n`, `i` comes strictly before `j` exactly when `i ≥ n + 2` and
`j < n + 2`, or `i` and `j` are on the same side of `n + 2` and `i < j`. -/
@[simp]
theorem blockKey_lt_blockKey_iff {n i j : ℕ} :
    blockKey n i < blockKey n j ↔ n + 2 ≤ i ∧ j < n + 2 ∨ (i < n + 2 ↔ j < n + 2) ∧ i < j := by
  rw [blockKey, blockKey, Prod.Lex.toLex_lt_toLex]
  rcases lt_or_ge i (n + 2) with hi | hi <;> rcases lt_or_ge j (n + 2) with hj | hj <;>
    simp [hi, hj, hi.not_gt, hj.not_gt]

/-- The position of a point `(x, i)` of `List ℚ × ℕ` for the colouring `χ`: first `x`, then the
position of `i` in the block of colour `χ x`. -/
private def unravelOrderKey (χ : List ℚ → ℕ) (p : List ℚ × ℕ) : Lex (List ℚ × Lex (Bool × ℕ)) :=
  toLex (p.1, blockKey (χ p.1) p.2)

/-- Distinct points have distinct positions. -/
private theorem unravelOrderKey_injective (χ : List ℚ → ℕ) :
    Function.Injective (unravelOrderKey χ) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  simp only [unravelOrderKey, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rw [blockKey_injective _ h]

/-- The order of `List ℚ × ℕ` for a colouring `χ` of `List ℚ`: the lexicographic sum over the
order of `List ℚ` of the blocks `ω + (χ x + 2)`. -/
def unravelOrderRel (χ : List ℚ → ℕ) (p q : List ℚ × ℕ) : Prop :=
  unravelOrderKey χ p ≤ unravelOrderKey χ q

/-- Points of distinct blocks compare by their `List ℚ` coordinates; two points of the block of
`x` compare by their positions in the block of colour `χ x`. -/
theorem unravelOrderRel_iff {χ : List ℚ → ℕ} {p q : List ℚ × ℕ} :
    unravelOrderRel χ p q ↔
      p.1 < q.1 ∨ p.1 = q.1 ∧ blockKey (χ p.1) p.2 ≤ blockKey (χ p.1) q.2 := by
  rw [unravelOrderRel, unravelOrderKey, unravelOrderKey, Prod.Lex.toLex_le_toLex]
  constructor
  · rintro (h | ⟨h, h'⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      dsimp only at h'
      rwa [← h] at h'
  · rintro (h | ⟨h, h'⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      dsimp only
      rwa [← h]

/-- The order of `List ℚ × ℕ` for a colouring is a linear order, being the pullback of a linear
order along an injective map. -/
instance isLinearOrder_unravelOrderRel (χ : List ℚ → ℕ) :
    IsLinearOrder (List ℚ × ℕ) (unravelOrderRel χ) :=
  (RelEmbedding.preimage ⟨_, unravelOrderKey_injective χ⟩ (· ≤ ·)).isLinearOrder

/-- An order automorphism `Φ` of `List ℚ` with `χ' ∘ Φ = χ`, applied to the `List ℚ`
coordinate, carries the order for `χ` to the order for `χ'`. -/
theorem unravelOrderRel_map {χ χ' : List ℚ → ℕ} (Φ : List ℚ ≃o List ℚ) (hΦ : ∀ x, χ' (Φ x) = χ x)
    (p q : List ℚ × ℕ) :
    unravelOrderRel χ' (Φ p.1, p.2) (Φ q.1, q.2) ↔ unravelOrderRel χ p q := by
  rw [unravelOrderRel_iff, unravelOrderRel_iff, Φ.lt_iff_lt, Φ.injective.eq_iff, hΦ]

/-! ### The code -/

/-- The fixed enumeration of `List ℚ × ℕ` by `ℕ`. -/
noncomputable def unravelOrderEquiv : ℕ ≃ List ℚ × ℕ :=
  (Denumerable.eqv (List ℚ × ℕ)).symm

/-- The code on `ℕ` of the order of `List ℚ × ℕ` for the colouring `unravelColor c`, relabelled
along `unravelOrderEquiv`. -/
noncomputable def unravelOrderCode (c : RelationalConfiguration Language.graph ℕ) :
    RelationalConfiguration Language.order ℕ :=
  ofRel fun m n => unravelOrderRel (unravelColor c) (unravelOrderEquiv m) (unravelOrderEquiv n)

/-- The code `unravelOrderCode c` reads `leSymb` as the order for `unravelColor c`. -/
@[simp]
theorem codeRel_unravelOrderCode (c : RelationalConfiguration Language.graph ℕ) (m n : ℕ) :
    codeRel leSymb (unravelOrderCode c) m n ↔
      unravelOrderRel (unravelColor c) (unravelOrderEquiv m) (unravelOrderEquiv n) := by
  rw [unravelOrderCode, codeRel_ofRel]

/-- **The values are coded linear orders**, for every code of the language of graphs. -/
theorem unravelOrderCode_mem_linearOrderClass (c : RelationalConfiguration Language.graph ℕ) :
    unravelOrderCode c ∈ linearOrderClass := by
  rw [mem_linearOrderClass, unravelOrderCode, codeRel_ofRel]
  exact (RelEmbedding.preimage unravelOrderEquiv.toEmbedding
    (unravelOrderRel (unravelColor c))).isLinearOrder

/-! ### Continuity -/

/-- **`unravelOrderCode` is continuous**: each coordinate compares two points of `List ℚ × ℕ`,
which depends on the code at most through the colour of their common block. -/
theorem continuous_unravelOrderCode : Continuous unravelOrderCode := by
  classical
  refine continuous_iff.2 fun a => ?_
  induction a using Atom.induction_atom with | @h k R v => ?_
  obtain rfl : k = 2 := by cases R; rfl
  rw [order.relation_eq_leSymb R]
  set p := unravelOrderEquiv (v 0)
  set q := unravelOrderEquiv (v 1)
  have h : (fun c => (unravelOrderCode c).eval (atom leSymb v)) =
      (fun n => decide (p.1 < q.1 ∨ p.1 = q.1 ∧ blockKey n p.2 ≤ blockKey n q.2)) ∘
        fun c => unravelColor c p.1 := by
    funext c
    rw [unravelOrderCode, eval_ofRel, Function.comp_apply]
    exact decide_eq_decide.2 unravelOrderRel_iff
  rw [h]
  exact continuous_of_discreteTopology.comp (continuous_unravelColor p.1)

/-! ### Isomorphic codes have isomorphic images -/

/-- **Isomorphic codes have isomorphic images.** By the unravelling lemma an isomorphism gives an
order automorphism `Φ` of `List ℚ` with `χ_d ∘ Φ = χ_c`; applied to the `List ℚ` coordinate and
relabelled to `ℕ`, it carries the order of `c` to the order of `d`. -/
theorem isoSetoid_unravelOrderCode {c d : RelationalConfiguration Language.graph ℕ}
    (h : isoSetoid Language.graph ℕ c d) :
    isoSetoid Language.order ℕ (unravelOrderCode c) (unravelOrderCode d) := by
  obtain ⟨Φ, hΦ⟩ := isoSetoid_iff_exists_orderIso_unravelColor.1 h
  let ψ : List ℚ × ℕ ≃ List ℚ × ℕ := Φ.toEquiv.prodCongr (Equiv.refl ℕ)
  let σ : Equiv.Perm ℕ := (unravelOrderEquiv.trans ψ).trans unravelOrderEquiv.symm
  refine isoSetoid_iff_exists_perm_smul_eq.2 ⟨σ, ?_⟩
  rw [← ofRel_codeRel (σ • unravelOrderCode c)]
  refine congrArg ofRel (funext fun m => funext fun n => propext ?_)
  have he (k : ℕ) : unravelOrderEquiv (σ.symm k) =
      (Φ.symm (unravelOrderEquiv k).1, (unravelOrderEquiv k).2) := by
    ext <;> simp [σ, ψ]
  rw [codeRel_perm_smul, codeRel_unravelOrderCode, he, he, ← unravelOrderRel_map Φ
    (fun x => congrFun hΦ x)]
  simp


/-! ### Isomorphic images come from isomorphic codes -/

variable {χ : List ℚ → ℕ}

/-- Two points of the block of `x` compare by their positions in the block of colour `χ x`. -/
@[simp]
theorem unravelOrderRel_mk_mk_iff {x : List ℚ} {i j : ℕ} :
    unravelOrderRel χ (x, i) (x, j) ↔ blockKey (χ x) i ≤ blockKey (χ x) j := by
  simp [unravelOrderRel_iff]

/-- The order for `χ` refines the order of the `List ℚ` coordinate. -/
theorem fst_le_of_unravelOrderRel {p q : List ℚ × ℕ} (h : unravelOrderRel χ p q) : p.1 ≤ q.1 := by
  rcases unravelOrderRel_iff.1 h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- A point between two points of the same block lies in that block. -/
private theorem fst_eq_of_between {p q z : List ℚ × ℕ} (hq : q.1 = p.1)
    (h : unravelOrderRel χ p z ∧ unravelOrderRel χ z q ∨
      unravelOrderRel χ q z ∧ unravelOrderRel χ z p) : z.1 = p.1 := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact le_antisymm (hq ▸ fst_le_of_unravelOrderRel h₂) (fst_le_of_unravelOrderRel h₁)
  · exact le_antisymm (fst_le_of_unravelOrderRel h₂) (hq ▸ fst_le_of_unravelOrderRel h₁)

/-- Two points of one block on the same side of `χ x + 2`, both in the `ω`-part or both in the
finite part, are near. -/
private theorem isNear_mk_mk {x : List ℚ} {i j : ℕ} (h : i < χ x + 2 ↔ j < χ x + 2) :
    IsNear (unravelOrderRel χ) (x, i) (x, j) := by
  refine isNear_iff.2 <|
    ((finite_Iic (max (max i j) (χ x + 1))).image fun k => (x, k)).subset fun z hz => ?_
  have hzx := fst_eq_of_between (p := (x, i)) (q := (x, j)) rfl hz
  obtain ⟨z, k⟩ := z
  dsimp only at hzx
  subst hzx
  refine ⟨k, ?_, rfl⟩
  rw [mem_Iic]
  simp only [mem_ofPred_eq, unravelOrderRel_mk_mk_iff, blockKey_le_blockKey_iff] at hz
  omega

/-- Points of the finite part of a block are near exactly the points of the same finite part. -/
theorem isNear_unravelOrderRel_iff {p q : List ℚ × ℕ} (hp : p.2 < χ p.1 + 2) :
    IsNear (unravelOrderRel χ) p q ↔ q.1 = p.1 ∧ q.2 < χ p.1 + 2 := by
  obtain ⟨x, i⟩ := p
  obtain ⟨y, j⟩ := q
  dsimp only at hp ⊢
  refine ⟨fun h => ?_, fun ⟨hy, hj⟩ => ?_⟩
  · by_contra hne
    refine (isNear_iff.1 h).not_infinite ?_
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · obtain ⟨z, hxz, hzy⟩ := exists_between hxy
      refine infinite_of_injective_forall_mem (Prod.mk_right_injective z)
        fun k => Or.inl ⟨?_, ?_⟩ <;>
        exact unravelOrderRel_iff.2 (Or.inl ‹_›)
    · subst hxy
      have hj : χ x + 2 ≤ j := by simpa using hne
      refine infinite_of_injective_forall_mem (f := fun k : ℕ => (x, j + k))
        (fun a b h => by simpa using h) fun k => Or.inr ⟨?_, ?_⟩
      · rw [unravelOrderRel_mk_mk_iff, blockKey_le_blockKey_iff]
        exact Or.inr ⟨by omega, by omega⟩
      · rw [unravelOrderRel_mk_mk_iff, blockKey_le_blockKey_iff]
        exact Or.inl ⟨by omega, hp⟩
    · obtain ⟨z, hyz, hzx⟩ := exists_between hxy
      refine infinite_of_injective_forall_mem (Prod.mk_right_injective z)
        fun k => Or.inr ⟨?_, ?_⟩ <;>
        exact unravelOrderRel_iff.2 (Or.inl ‹_›)
  · subst y
    exact isNear_mk_mk (by omega)

/-- The points near a point `p` of the finite part of its block form that finite part. -/
theorem setOf_isNear_unravelOrderRel_eq {p : List ℚ × ℕ} (hp : p.2 < χ p.1 + 2) :
    {q | IsNear (unravelOrderRel χ) p q} = (fun k => (p.1, k)) '' Iio (χ p.1 + 2) := by
  ext q
  rw [mem_ofPred_eq, isNear_unravelOrderRel_iff hp]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨q.2, h₂, by rw [← h₁]⟩, by rintro ⟨k, hk, rfl⟩; exact ⟨rfl, hk⟩⟩

/-- A point of the `ω`-part of a block is near infinitely many points. -/
theorem infinite_setOf_isNear_unravelOrderRel {p : List ℚ × ℕ} (hp : χ p.1 + 2 ≤ p.2) :
    {q | IsNear (unravelOrderRel χ) p q}.Infinite := by
  obtain ⟨x, i⟩ := p
  dsimp only at hp
  exact infinite_of_injective_forall_mem (f := fun k : ℕ => (x, i + k))
    (fun a b h => by simpa using h) fun k => isNear_mk_mk (by omega)

/-- A point is near only finitely many points exactly when it lies in the finite part of its
block. -/
theorem finite_setOf_isNear_unravelOrderRel_iff {p : List ℚ × ℕ} :
    {q | IsNear (unravelOrderRel χ) p q}.Finite ↔ p.2 < χ p.1 + 2 := by
  refine ⟨fun h => ?_, fun hp => ?_⟩
  · by_contra hp
    exact infinite_setOf_isNear_unravelOrderRel (not_lt.1 hp) h
  · rw [setOf_isNear_unravelOrderRel_eq hp]
    exact (finite_Iio _).image _

/-- For a point `p` of the finite part of its block, the points near `p` are `χ p.1 + 2` in
number: they form the finite part of the block of `p.1`. -/
theorem ncard_setOf_isNear_unravelOrderRel {p : List ℚ × ℕ} (hp : p.2 < χ p.1 + 2) :
    {q | IsNear (unravelOrderRel χ) p q}.ncard = χ p.1 + 2 := by
  rw [setOf_isNear_unravelOrderRel_eq hp, ncard_image_of_injective _ (Prod.mk_right_injective _),
    ncard_Iio_nat]

/-- **Order isomorphisms of the unravelled orders give colour-preserving automorphisms.** A
relation isomorphism `f` from the order for `χ` to the order for `χ'` on `List ℚ × ℕ` maps the
finite condensation classes, the finite parts of the blocks, to finite condensation classes of the
same size, in order; so it induces an order automorphism `Φ` of `List ℚ` with `χ' ∘ Φ = χ`. -/
theorem exists_orderIso_of_unravelOrderRel {χ χ' : List ℚ → ℕ}
    (f : unravelOrderRel χ ≃r unravelOrderRel χ') :
    ∃ Φ : List ℚ ≃o List ℚ, ∀ x, χ' (Φ x) = χ x := by
  have hN := f.setOf_isNear_apply
  have hfin (p : List ℚ × ℕ) : (f p).2 < χ' (f p).1 + 2 ↔ p.2 < χ p.1 + 2 := by
    rw [← finite_setOf_isNear_unravelOrderRel_iff, ← finite_setOf_isNear_unravelOrderRel_iff, hN,
      finite_image_iff f.injective.injOn]
  have h0 (x : List ℚ) : (f (x, 0)).2 < χ' (f (x, 0)).1 + 2 := (hfin _).2 (by simp)
  have hχ (x : List ℚ) : χ' (f (x, 0)).1 = χ x := by
    have h := ncard_setOf_isNear_unravelOrderRel (h0 x)
    rw [hN, ncard_image_of_injective _ f.injective,
      ncard_setOf_isNear_unravelOrderRel (p := (x, 0)) (by simp)] at h
    dsimp only at h
    omega
  let Φ₀ : List ℚ → List ℚ := fun x => (f (x, 0)).1
  have hmono : StrictMono Φ₀ := fun x y hxy => by
    have hr : unravelOrderRel χ' (f (x, 0)) (f (y, 0)) :=
      f.map_rel_iff.2 (unravelOrderRel_iff.2 (Or.inl hxy))
    refine (fst_le_of_unravelOrderRel hr).lt_of_ne fun he => hxy.ne ?_
    have h := (isNear_unravelOrderRel_iff (h0 x)).2 ⟨he.symm, he ▸ h0 y⟩
    rw [f.isNear_apply_iff, isNear_unravelOrderRel_iff (by simp)] at h
    exact h.1.symm
  have hsurj : Function.Surjective Φ₀ := fun y => by
    obtain ⟨p, hpy⟩ := f.surjective (y, 0)
    have hp : p.2 < χ p.1 + 2 := (hfin p).1 (by rw [hpy]; simp)
    have h := (f.isNear_apply_iff p (p.1, 0)).2 ((isNear_unravelOrderRel_iff hp).2 ⟨rfl, by simp⟩)
    rw [hpy, isNear_unravelOrderRel_iff (by simp)] at h
    exact ⟨p.1, h.1⟩
  exact ⟨StrictMono.orderIsoOfSurjective Φ₀ hmono hsurj, hχ⟩

/-- **Isomorphic images come from isomorphic codes.** -/
theorem isoSetoid_of_isoSetoid_unravelOrderCode {c d : RelationalConfiguration Language.graph ℕ}
    (h : isoSetoid Language.order ℕ (unravelOrderCode c) (unravelOrderCode d)) :
    isoSetoid Language.graph ℕ c d := by
  obtain ⟨σ, hσ⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
  let f : List ℚ × ℕ ≃ List ℚ × ℕ := (unravelOrderEquiv.symm.trans σ.symm).trans unravelOrderEquiv
  have hf (p q : List ℚ × ℕ) :
      unravelOrderRel (unravelColor c) (f p) (f q) ↔ unravelOrderRel (unravelColor d) p q := by
    have := codeRel_perm_smul leSymb σ (unravelOrderCode c) (unravelOrderEquiv.symm p)
      (unravelOrderEquiv.symm q)
    rw [hσ, codeRel_unravelOrderCode, codeRel_unravelOrderCode] at this
    simpa [f] using this.symm
  obtain ⟨Φ, hΦ⟩ := exists_orderIso_of_unravelOrderRel ⟨f, hf _ _⟩
  exact Setoid.symm' _ <| isoSetoid_iff_exists_orderIso_unravelColor.2 ⟨Φ, funext hΦ⟩

/-- **`unravelOrderCode` reduces isomorphism of graph codes to isomorphism of coded linear
orders**: for all codes `c` and `d` of the language of graphs, simple graphs or not, the images
are isomorphic exactly when `c` and `d` are. -/
theorem isoSetoid_unravelOrderCode_iff {c d : RelationalConfiguration Language.graph ℕ} :
    isoSetoid Language.order ℕ (unravelOrderCode c) (unravelOrderCode d) ↔
      isoSetoid Language.graph ℕ c d :=
  ⟨isoSetoid_of_isoSetoid_unravelOrderCode, isoSetoid_unravelOrderCode⟩

/-- **A continuous reduction to coded linear orders**: a continuous map, `unravelOrderCode`,
sends every code of the language of graphs to a coded linear order, and two codes are isomorphic
exactly when their images are. -/
theorem exists_continuous_reduction_linearOrderClass :
    ∃ f : RelationalConfiguration Language.graph ℕ → RelationalConfiguration Language.order ℕ,
      Continuous f ∧ (∀ c, f c ∈ linearOrderClass) ∧
        ∀ c d, isoSetoid Language.graph ℕ c d ↔ isoSetoid Language.order ℕ (f c) (f d) :=
  ⟨unravelOrderCode, continuous_unravelOrderCode, unravelOrderCode_mem_linearOrderClass,
    fun _ _ => isoSetoid_unravelOrderCode_iff.symm⟩

/-- **Countable linear orders are Borel complete** (Friedman–Stanley): the continuous reduction
`exists_continuous_reduction_linearOrderClass` reduces isomorphism on `graphClass` to isomorphism
on `linearOrderClass`. -/
theorem borelComplete_linearOrderClass : BorelComplete (linearOrderClass (V := ℕ)) :=
  let ⟨_, hc, hmem, hiso⟩ := exists_continuous_reduction_linearOrderClass
  borelComplete_graphClass.of_borelReducible <|
    borelReducible_classIso_of_mapsTo hc.measurable (fun c _ => hmem c)
      fun c _ d _ => hiso c d

end TauCeti.RelationalConfiguration
