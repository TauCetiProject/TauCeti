/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Associativity
public import TauCeti.Combinatorics.Brauer.Generator
public import TauCeti.GroupTheory.Perm.Basic

/-!
# The Brauer relations between two cap-cup diagrams

`TauCeti/Combinatorics/Brauer/Generator.lean` proves the Brauer relations that involve a single
cap-cup diagram `e` and the permutation diagrams: `e * e = δ • e`, `s * e = e * s = e`, the far
commutation of `e` with a permutation diagram that renames its pair to itself, and the mixed
relation `e * (s * e) = e`. This file proves the relations that involve **two different** cap-cup
diagrams, which are the remaining defining relations of the Brauer algebra `B_k(δ)`:

* **disjoint pairs commute**, `e_{a,b} * e_{c,d} = e_{c,d} * e_{a,b}` with no loop closing up in
  the middle, which for consecutive pairs is Brauer's `eᵢ eⱼ = eⱼ eᵢ` for `|i - j| ≥ 2`;
* **overlapping pairs absorb**, `e_{a,b} * (e_{b,c} * e_{a,b}) = e_{a,b}` and its left bracketing,
  again with no loop, which for consecutive pairs is Brauer's `eᵢ eᵢ₊₁ eᵢ = eᵢ`;
* the **mixed relation** `s_{a,b} * (e_{b,c} * e_{a,b}) = s_{b,c} * e_{a,b}` and its mirror
  `(e_{a,b} * e_{b,c}) * s_{a,b} = e_{a,b} * s_{b,c}`, Brauer's `sᵢ eᵢ₊₁ eᵢ = sᵢ₊₁ eᵢ` and
  `eᵢ eᵢ₊₁ sᵢ = eᵢ sᵢ₊₁`.

Two cap-cup diagrams sharing exactly one point stack to a **relabelled** cap-cup diagram.
`TauCeti.composeDiagram_capCup_capCup_eq_relabel_left` says that stacking `e_{b,c}` above
`e_{a,b}` renames the top boundary of `e_{a,b}` by the three-cycle
`Equiv.swap a b * Equiv.swap b c` carrying `a ↦ b ↦ c ↦ a`, and
`TauCeti.composeDiagram_capCup_capCup_eq_relabel_right` says that stacking them the other way round
renames the bottom boundary by the same three-cycle. Equivalently, by
`TauCeti.composeDiagram_permToBrauer_left`, stacking `e_{b,c}` above `e_{a,b}` has the same effect
as stacking the diagram of that three-cycle above `e_{a,b}`: the horizontal arcs of the upper copy
are absorbed by those of the lower one. They are the sharpest statement about a stack of two
overlapping pairs: the three relations on overlapping pairs below are the consequences of them
that the presentation of `B_k(δ)` names, and a consumer needing such a stack in some other
combination should reach for them rather than for those relations. The values of the three-cycle
are `TauCeti.swap_mul_swap_apply_left`, `TauCeti.swap_mul_swap_apply_middle` and
`TauCeti.swap_mul_swap_apply_right` in `TauCeti/GroupTheory/Perm/Basic.lean`.

The suffixes `_left` and `_right` name which factor of `TauCeti.composeDiagram` the overlapping
pair `e_{b,c}` is, as in `TauCeti.composeDiagram_permToBrauer_left` and
`TauCeti.composeDiagram_permToBrauer_right`: `_left` is the stack with `e_{b,c}` above `e_{a,b}`
and `_right` the stack with `e_{b,c}` below it.

Disjoint pairs do not overlap at all, so their stack is not a relabelled cap-cup diagram but a
genuinely new one, the diagram with two caps and two cups;
`TauCeti.composeDiagram_capCup_capCup_comm` says that this diagram does not depend on the order
the two copies are stacked in.

Each relation here has a **mirror**, the same stack turned upside down. Reflection in a
horizontal line carries one to the other: it reverses the stacking
(`TauCeti.flip_composeDiagram`), leaves the number of loops closing up in the middle alone
(`TauCeti.middleLoopCount_flip`) and fixes a cap-cup diagram
(`TauCeti.BrauerDiagram.flip_capCup`), so the `_right` statements below are the reflections of
their `_left` companions.

Each relation comes with the middle-loop count of every stack it names, so that it is a relation
for the loop-weighted multiplication `D₁ * D₂ = δ ^ middleLoopCount D₁ D₂ • composeDiagram D₁ D₂`
of the Brauer algebra on the diagram basis and not only for the underlying matchings. All of the
counts here vanish, and the hypotheses that make them vanish are exactly the ones that make the
pairs genuinely distinct: on a repeated pair the stack closes up a loop and
`TauCeti.middleLoopCount_capCup_capCup` counts it.

## Main results

* `TauCeti.composeDiagram_capCup_capCup_eq_relabel_left` and
  `TauCeti.composeDiagram_capCup_capCup_eq_relabel_right`: **two cap-cup diagrams sharing a point
  stack to a relabelled cap-cup diagram.**
* `TauCeti.composeDiagram_capCup_capCup_capCup`: **`e * (e' * e) = e`** for overlapping pairs, with
  `TauCeti.middleLoopCount_capCup_capCup_left_of_ne` and
  `TauCeti.middleLoopCount_capCup_composeDiagram_capCup_capCup` counting no loop in either middle;
  `TauCeti.middleLoopCount_composeDiagram_capCup_capCup_capCup` does the same for the left
  bracketing.
* `TauCeti.composeDiagram_permToBrauer_swap_capCup_capCup` and
  `TauCeti.composeDiagram_capCup_capCup_permToBrauer_swap`: **the mixed relations**, whose middles
  are counted by `TauCeti.middleLoopCount_capCup_capCup_left_of_ne` and
  `TauCeti.middleLoopCount_capCup_capCup_right_of_ne`.
* `TauCeti.composeDiagram_capCup_capCup_comm`: **cap-cup diagrams on disjoint pairs commute**, with
  `TauCeti.middleLoopCount_capCup_capCup_of_disjoint` counting no loop.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
-/

public section

namespace TauCeti

variable {k : ℕ} {a b c d : Fin k}

/-! ### Two cap-cup diagrams sharing one point -/

/-- A cap-cup diagram absorbs the diagram of the three-cycle `a ↦ b ↦ c ↦ a` stacked above it. -/
private theorem composeDiagram_capCup_permToBrauer_mul_capCup (hab : a ≠ b) (c : Fin k) :
    composeDiagram (capCup a b)
        (composeDiagram (permToBrauer (Equiv.swap a b * Equiv.swap b c)) (capCup a b)) =
      capCup a b := by
  rw [← composeDiagram_permToBrauer, composeDiagram_assoc, ← composeDiagram_assoc,
    composeDiagram_capCup_permToBrauer_swap, composeDiagram_capCup_permToBrauer_swap_capCup hab]

/-- **Two cap-cup diagrams sharing a point stack to a relabelled cap-cup diagram.** Stacking
`e_{b,c}` as the left, upper factor, above `e_{a,b}`, renames the top boundary of `e_{a,b}` by the
three-cycle `a ↦ b ↦ c ↦ a`: the cap of the upper copy joins the two middle points `b` and `c`, one
of which the cup of the lower copy already uses, so the upper copy contributes no horizontal arc of
its own and only permutes the ends of the lower one. By
`TauCeti.composeDiagram_permToBrauer_left` the right-hand side is equally the stack of the diagram
of that three-cycle above `e_{a,b}`.

The degenerate pairs are covered: for `c = b` the upper copy is the identity diagram and the
three-cycle is the transposition of the pair, which fixes `e_{a,b}`
(`TauCeti.BrauerDiagram.relabel_one_swap_capCup`); for `c = a` the two copies are equal, the
three-cycle is the identity, and the statement is
`TauCeti.composeDiagram_capCup_capCup`. Only `a ≠ b` is needed, and it is needed: for `a = b` the
lower copy is the identity diagram, the left-hand side is the cap-cup diagram `e_{a,c}` and the
right-hand side a permutation diagram.

Not a `simp` lemma: `simp` rewrites the right-hand side further, through
`TauCeti.BrauerDiagram.relabel_val_inr`, so it is not a simp-normal form of the left-hand side. -/
theorem composeDiagram_capCup_capCup_eq_relabel_left (hab : a ≠ b) (c : Fin k) :
    composeDiagram (capCup b c) (capCup a b) =
      (capCup a b).relabel 1 (Equiv.swap a b * Equiv.swap b c) := by
  obtain rfl | hcb := eq_or_ne c b
  · rw [capCup_self, composeDiagram_permToBrauer_one_left, Equiv.swap_self,
      ← Equiv.Perm.one_def, mul_one, BrauerDiagram.relabel_one_swap_capCup]
  obtain rfl | hca := eq_or_ne c a
  · rw [Equiv.swap_comm b c, Equiv.swap_mul_self, BrauerDiagram.relabel_one_one, capCup_comm,
      composeDiagram_capCup_capCup]
  have hconj : capCup b c =
      composeDiagram (permToBrauer (Equiv.swap a b * Equiv.swap b c))
        (composeDiagram (capCup a b) (permToBrauer (Equiv.swap a b * Equiv.swap b c)⁻¹)) := by
    rw [composeDiagram_permToBrauer_conj_capCup, swap_mul_swap_apply_left hab hca,
      swap_mul_swap_apply_middle hca hcb]
  have hinner : composeDiagram (capCup a b)
      (composeDiagram (permToBrauer (Equiv.swap a b * Equiv.swap b c)⁻¹) (capCup a b)) =
      capCup a b := by
    rw [mul_inv_rev, Equiv.Perm.inv_def, Equiv.symm_swap, Equiv.Perm.inv_def, Equiv.symm_swap,
      ← composeDiagram_permToBrauer, composeDiagram_assoc,
      composeDiagram_permToBrauer_swap_capCup, composeDiagram_capCup_permToBrauer_swap_capCup hab]
  rw [hconj, composeDiagram_assoc, composeDiagram_assoc, hinner,
    composeDiagram_permToBrauer_left]

/-- **Two cap-cup diagrams sharing a point stack to a relabelled cap-cup diagram**, the other way
round: with `e_{b,c}` as the right, lower factor, so that `e_{a,b}` is stacked above `e_{b,c}`,
it is the **bottom** boundary of `e_{a,b}` that is renamed, by the same three-cycle
`a ↦ b ↦ c ↦ a` that `TauCeti.composeDiagram_capCup_capCup_eq_relabel_left` renames the top
boundary by.

Not a `simp` lemma, for the reason given for
`TauCeti.composeDiagram_capCup_capCup_eq_relabel_left`. -/
theorem composeDiagram_capCup_capCup_eq_relabel_right (hab : a ≠ b) (c : Fin k) :
    composeDiagram (capCup a b) (capCup b c) =
      (capCup a b).relabel (Equiv.swap a b * Equiv.swap b c) 1 := by
  simpa using congrArg BrauerDiagram.flip (composeDiagram_capCup_capCup_eq_relabel_left hab c)

/-! ### The relations of two overlapping pairs -/

/-- **`e * (e' * e) = e` on the diagram basis**: a cap-cup diagram absorbs a cap-cup diagram on an
overlapping pair stacked between two copies of it. For consecutive pairs this is Brauer's relation
`eᵢ eᵢ₊₁ eᵢ = eᵢ`.

Together with `TauCeti.middleLoopCount_capCup_capCup_left_of_ne` and
`TauCeti.middleLoopCount_capCup_composeDiagram_capCup_capCup`, which say that no loop closes up in
either middle once the three points are distinct, this is the relation `e * (e' * e) = e` for the
loop-weighted multiplication; `TauCeti.middleLoopCount_composeDiagram_capCup_capCup_capCup` does
the same for the other bracketing, which `TauCeti.composeDiagram_assoc` identifies with this one.

Not a `simp` lemma: `simp` reduces the left-hand side, through
`TauCeti.composeDiagram_capCup_capCup_eq_relabel_left` and the relabelling lemmas, so it is not in
simp-normal form. -/
theorem composeDiagram_capCup_capCup_capCup (hab : a ≠ b) (c : Fin k) :
    composeDiagram (capCup a b) (composeDiagram (capCup b c) (capCup a b)) = capCup a b := by
  rw [composeDiagram_capCup_capCup_eq_relabel_left hab, ← composeDiagram_permToBrauer_left,
    composeDiagram_capCup_permToBrauer_mul_capCup hab]

/-- **The mixed relation `s * (e' * e) = s' * e`**: stacking the diagram of the transposition of a
pair above the stack of a cap-cup diagram on an overlapping pair and that pair replaces it by the
transposition of the other pair. For consecutive pairs this is Brauer's relation
`sᵢ eᵢ₊₁ eᵢ = sᵢ₊₁ eᵢ`. Once the two pairs are genuinely different, that is once `a ≠ c`, no loop
closes up in any of the three middles, by
`TauCeti.middleLoopCount_capCup_capCup_left_of_ne` and
`TauCeti.middleLoopCount_permToBrauer_left`, so this is that relation for the loop-weighted
multiplication. On `c = a` the inner stack repeats the pair `{a, b}` and does close up one loop
(`TauCeti.middleLoopCount_capCup_capCup`); the identity of diagrams stated here needs only
`a ≠ b`.

Not a `simp` lemma, for the reason given for
`TauCeti.composeDiagram_capCup_capCup_capCup`. -/
theorem composeDiagram_permToBrauer_swap_capCup_capCup (hab : a ≠ b) (c : Fin k) :
    composeDiagram (permToBrauer (Equiv.swap a b)) (composeDiagram (capCup b c) (capCup a b)) =
      composeDiagram (permToBrauer (Equiv.swap b c)) (capCup a b) := by
  rw [composeDiagram_capCup_capCup_eq_relabel_left hab, composeDiagram_permToBrauer_left,
    composeDiagram_permToBrauer_left, BrauerDiagram.relabel_relabel, one_mul, ← mul_assoc,
    Equiv.swap_mul_self, one_mul]

/-- **The mixed relation `(e * e') * s = e * s'`**, the mirror of
`TauCeti.composeDiagram_permToBrauer_swap_capCup_capCup`: stacking the diagram of the
transposition of a pair below the stack of a cap-cup diagram on that pair and one on an
overlapping pair replaces it by the transposition of the other pair. For consecutive pairs this
is Brauer's relation `eᵢ eᵢ₊₁ sᵢ = eᵢ sᵢ₊₁`. Once the two pairs are genuinely different, that is
once `a ≠ c`, no loop closes up in any of the three middles, by
`TauCeti.middleLoopCount_capCup_capCup_right_of_ne` and
`TauCeti.middleLoopCount_permToBrauer_right`, so this is that relation for the loop-weighted
multiplication. On `c = a` the inner stack repeats the pair `{a, b}` and does close up one loop
(`TauCeti.middleLoopCount_capCup_capCup`); the identity of diagrams stated here needs only
`a ≠ b`.

Not a `simp` lemma, for the reason given for
`TauCeti.composeDiagram_capCup_capCup_capCup`. -/
theorem composeDiagram_capCup_capCup_permToBrauer_swap (hab : a ≠ b) (c : Fin k) :
    composeDiagram (composeDiagram (capCup a b) (capCup b c)) (permToBrauer (Equiv.swap a b)) =
      composeDiagram (capCup a b) (permToBrauer (Equiv.swap b c)) := by
  simpa using congrArg BrauerDiagram.flip (composeDiagram_permToBrauer_swap_capCup_capCup hab c)

/-! ### The middle loops of two overlapping pairs -/

/-- **Overlapping pairs close up no loop**: stacking `e_{b,c}` as the left, upper factor, above
`e_{a,b}`, closes up no loop in the middle. The only middle point keeping both of its arcs in the
middle is the shared point `b`, whose cap in the upper copy runs to `c`, where the arc of the lower
copy leaves for the boundary.

The hypothesis is needed and is exactly the one that makes the two pairs different as unordered
pairs: on `a = c` the two copies are equal and `TauCeti.middleLoopCount_capCup_capCup` counts one
loop. -/
@[simp]
theorem middleLoopCount_capCup_capCup_left_of_ne (hac : a ≠ c) (b : Fin k) :
    middleLoopCount (capCup b c) (capCup a b) = 0 := by
  obtain rfl | hcb := eq_or_ne c b
  · rw [capCup_self, middleLoopCount_permToBrauer_left]
  obtain rfl | hba := eq_or_ne b a
  · rw [capCup_self, middleLoopCount_permToBrauer_right]
  refine middleLoopCount_eq_zero_iff.mpr fun x hx => ?_
  have hvert := (isMiddleVertex_def _ _ _).mp hx.isMiddleVertex
  have h₁ : x = b ∨ x = c := (BrauerDiagram.isCap_capCup_inl_iff hcb.symm).mp hvert.1
  have h₂ : x = a ∨ x = b := (BrauerDiagram.isCup_capCup_inr_iff hba.symm).mp hvert.2
  have hxb : x = b := by
    rcases h₁ with h | h
    · exact h
    · rcases h₂ with h' | h'
      · exact absurd (h.symm.trans h') hac.symm
      · exact h'
  rw [hxb] at hx
  exact not_onMiddleLoop_of_isThrough_right
    ((BrauerDiagram.isThrough_capCup_inr_iff hba.symm).mpr ⟨hac.symm, hcb⟩)
    (hx.reflTransGen (.single ((middleAdj_def _ _ _ _).mpr
      (Or.inl (capCup_val_inl_left hcb.symm)))))

/-- **Overlapping pairs close up no loop**, the other way round: with `e_{b,c}` as the right, lower
factor, so that `e_{a,b}` is stacked above `e_{b,c}`, no loop closes up in the middle either. The
only middle point keeping both of its arcs in the middle is the shared point `b`, whose cup in the
lower copy runs to `c`, where the arc of the upper copy leaves for the boundary.

The hypothesis is again exactly the one that makes the two pairs different as unordered pairs: on
`a = c` the two copies are equal and `TauCeti.middleLoopCount_capCup_capCup` counts one loop. -/
@[simp]
theorem middleLoopCount_capCup_capCup_right_of_ne (hac : a ≠ c) (b : Fin k) :
    middleLoopCount (capCup a b) (capCup b c) = 0 := by
  simpa only [BrauerDiagram.flip_capCup, middleLoopCount_capCup_capCup_left_of_ne hac] using
    middleLoopCount_flip (capCup b c) (capCup a b)

/-- **The outer middle of `e * (e' * e)` closes up no loop.** By
`TauCeti.composeDiagram_capCup_capCup_eq_relabel_left` the lower factor is `e_{a,b}` with its top
boundary renamed by the three-cycle `a ↦ b ↦ c ↦ a`, so it cups the pair `{b, c}`; the only middle
point that the upper copy also caps is the shared point `b`, and the cup there runs to `c`, which
the upper copy sends through to the boundary. On the degenerate pair `a = b` there is no cap at
all: the upper copy is the identity diagram (`TauCeti.capCup_self`), which closes up no loop
either, so no hypothesis on the pair `{a, b}` is needed. -/
@[simp]
theorem middleLoopCount_capCup_composeDiagram_capCup_capCup (hcb : c ≠ b) (hca : c ≠ a) :
    middleLoopCount (capCup a b) (composeDiagram (capCup b c) (capCup a b)) = 0 := by
  obtain rfl | hab := eq_or_ne a b
  · rw [capCup_self, middleLoopCount_permToBrauer_left]
  have hsymm : (Equiv.swap a b * Equiv.swap b c).symm b = a :=
    Equiv.symm_apply_eq _ |>.mpr (swap_mul_swap_apply_left hab hca).symm
  rw [composeDiagram_capCup_capCup_eq_relabel_left hab]
  refine middleLoopCount_eq_zero_iff.mpr fun x hx => ?_
  have hvert := (isMiddleVertex_def _ _ _).mp hx.isMiddleVertex
  have h₁ : x = a ∨ x = b := (BrauerDiagram.isCap_capCup_inl_iff hab).mp hvert.1
  have hxb : x = b := by
    rcases h₁ with h | h
    · rw [h] at hvert
      have hcup : (capCup a b).IsCup (Sum.inr c) := by
        rw [← BrauerDiagram.isCup_relabel_inr (capCup a b) 1
          (Equiv.swap a b * Equiv.swap b c) c, swap_mul_swap_apply_right]
        exact hvert.2
      rcases (BrauerDiagram.isCup_capCup_inr_iff hab).mp hcup with h' | h'
      · exact absurd h' hca
      · exact absurd h' hcb
    · exact h
  rw [hxb] at hx
  have hval : ((capCup a b).relabel 1 (Equiv.swap a b * Equiv.swap b c)).val (Sum.inr b) =
      Sum.inr c := by
    rw [BrauerDiagram.relabel_val_inr, hsymm, capCup_val_inr_left hab, Sum.map_inr,
      swap_mul_swap_apply_middle hca hcb]
  exact not_onMiddleLoop_of_isThrough_left
    ((BrauerDiagram.isThrough_capCup_inl_iff hab).mpr ⟨hca, hcb⟩)
    (hx.reflTransGen (.single ((middleAdj_def _ _ _ _).mpr (Or.inr hval))))

/-- **The outer middle of `(e * e') * e` closes up no loop**, the statement
`TauCeti.middleLoopCount_capCup_composeDiagram_capCup_capCup` makes about the other bracketing. By
`TauCeti.composeDiagram_capCup_capCup_eq_relabel_right` the upper factor is `e_{a,b}` with its
bottom boundary renamed by the three-cycle `a ↦ b ↦ c ↦ a`, so it caps the pair `{b, c}`; the only
middle point that the lower copy also cups is the shared point `b`, and the cap there runs to `c`,
which the lower copy sends through to the boundary. On the degenerate pair `a = b` there is no cup
at all: the lower copy is the identity diagram (`TauCeti.capCup_self`), which closes up no loop
either, so no hypothesis on the pair `{a, b}` is needed. -/
@[simp]
theorem middleLoopCount_composeDiagram_capCup_capCup_capCup (hcb : c ≠ b) (hca : c ≠ a) :
    middleLoopCount (composeDiagram (capCup a b) (capCup b c)) (capCup a b) = 0 := by
  simpa only [flip_composeDiagram, BrauerDiagram.flip_capCup,
    middleLoopCount_capCup_composeDiagram_capCup_capCup hcb hca] using
    middleLoopCount_flip (capCup a b) (composeDiagram (capCup b c) (capCup a b))

/-! ### The relation of two disjoint pairs -/

/-- **Cap-cup diagrams on disjoint pairs commute.** Neither copy uses a point of the other's pair,
so each contributes its own cap and its own cup to the stack and the order in which they are
stacked does not matter: in both orders the composite caps and cups both pairs and sends every
other bottom point through to the top point with the same index. For consecutive pairs this is
Brauer's relation `eᵢ eⱼ = eⱼ eᵢ` for `|i - j| ≥ 2`; together with
`TauCeti.middleLoopCount_capCup_capCup_of_disjoint`, which says that no loop closes up in either
middle, it is that relation for the loop-weighted multiplication. -/
theorem composeDiagram_capCup_capCup_comm (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    composeDiagram (capCup a b) (capCup c d) = composeDiagram (capCup c d) (capCup a b) := by
  obtain rfl | hab := eq_or_ne a b
  · rw [capCup_self, composeDiagram_permToBrauer_one_left, composeDiagram_permToBrauer_one_right]
  obtain rfl | hcd := eq_or_ne c d
  · rw [capCup_self, composeDiagram_permToBrauer_one_right, composeDiagram_permToBrauer_one_left]
  refine Subtype.ext (Equiv.ext fun x => ?_)
  rcases x with i | j
  · rcases eq_or_ne i a with rfl | hia
    · rw [composeDiagram_val_inl_eq_inl_of_cap_upper _ _ (capCup_val_inl_of_ne hac had)
        (capCup_val_inl_left hab) (capCup_val_inr_of_ne hbc hbd),
        composeDiagram_val_inl_eq_inl_of_cap_lower _ _ (capCup_val_inl_left hab)]
    rcases eq_or_ne i b with rfl | hib
    · rw [composeDiagram_val_inl_eq_inl_of_cap_upper _ _ (capCup_val_inl_of_ne hbc hbd)
        (capCup_val_inl_right hab) (capCup_val_inr_of_ne hac had),
        composeDiagram_val_inl_eq_inl_of_cap_lower _ _ (capCup_val_inl_right hab)]
    rcases eq_or_ne i c with rfl | hic
    · rw [composeDiagram_val_inl_eq_inl_of_cap_lower _ _ (capCup_val_inl_left hcd),
        composeDiagram_val_inl_eq_inl_of_cap_upper _ _ (capCup_val_inl_of_ne hia hib)
          (capCup_val_inl_left hcd) (capCup_val_inr_of_ne had.symm hbd.symm)]
    rcases eq_or_ne i d with rfl | hid
    · rw [composeDiagram_val_inl_eq_inl_of_cap_lower _ _ (capCup_val_inl_right hcd),
        composeDiagram_val_inl_eq_inl_of_cap_upper _ _ (capCup_val_inl_of_ne hia hib)
          (capCup_val_inl_right hcd) (capCup_val_inr_of_ne hac.symm hbc.symm)]
    rw [composeDiagram_val_inl_eq_inr_of_through _ _ (capCup_val_inl_of_ne hic hid)
        (capCup_val_inl_of_ne hia hib),
      composeDiagram_val_inl_eq_inr_of_through _ _ (capCup_val_inl_of_ne hia hib)
        (capCup_val_inl_of_ne hic hid)]
  · rcases eq_or_ne j a with rfl | hja
    · rw [composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_left hab),
        composeDiagram_val_inr_eq_inr_of_cup_lower _ _ (capCup_val_inr_of_ne hac had)
          (capCup_val_inr_left hab) (capCup_val_inl_of_ne hbc hbd)]
    rcases eq_or_ne j b with rfl | hjb
    · rw [composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_right hab),
        composeDiagram_val_inr_eq_inr_of_cup_lower _ _ (capCup_val_inr_of_ne hbc hbd)
          (capCup_val_inr_right hab) (capCup_val_inl_of_ne hac had)]
    rcases eq_or_ne j c with rfl | hjc
    · rw [composeDiagram_val_inr_eq_inr_of_cup_lower _ _ (capCup_val_inr_of_ne hja hjb)
          (capCup_val_inr_left hcd) (capCup_val_inl_of_ne had.symm hbd.symm),
        composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_left hcd)]
    rcases eq_or_ne j d with rfl | hjd
    · rw [composeDiagram_val_inr_eq_inr_of_cup_lower _ _ (capCup_val_inr_of_ne hja hjb)
          (capCup_val_inr_right hcd) (capCup_val_inl_of_ne hac.symm hbc.symm),
        composeDiagram_val_inr_eq_inr_of_cup_upper _ _ (capCup_val_inr_right hcd)]
    rw [composeDiagram_val_inr_eq_inl_of_through _ _ (capCup_val_inr_of_ne hja hjb)
        (capCup_val_inr_of_ne hjc hjd),
      composeDiagram_val_inr_eq_inl_of_through _ _ (capCup_val_inr_of_ne hjc hjd)
        (capCup_val_inr_of_ne hja hjb)]

/-- **Disjoint pairs close up no loop**: stacking two cap-cup diagrams on disjoint pairs closes up
no loop in the middle. A middle point keeping both of its arcs in the middle would have to be
capped by the upper copy, hence lie in its pair, and cupped by the lower one, hence lie in the
other pair. -/
@[simp]
theorem middleLoopCount_capCup_capCup_of_disjoint (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : middleLoopCount (capCup a b) (capCup c d) = 0 := by
  obtain rfl | hab := eq_or_ne a b
  · rw [capCup_self, middleLoopCount_permToBrauer_left]
  obtain rfl | hcd := eq_or_ne c d
  · rw [capCup_self, middleLoopCount_permToBrauer_right]
  refine middleLoopCount_eq_zero_iff.mpr fun x hx => ?_
  have hvert := (isMiddleVertex_def _ _ _).mp hx.isMiddleVertex
  have h₁ : x = a ∨ x = b := (BrauerDiagram.isCap_capCup_inl_iff hab).mp hvert.1
  have h₂ : x = c ∨ x = d := (BrauerDiagram.isCup_capCup_inr_iff hcd).mp hvert.2
  rcases h₁ with h | h <;> rcases h₂ with h' | h'
  · exact hac (h.symm.trans h')
  · exact had (h.symm.trans h')
  · exact hbc (h.symm.trans h')
  · exact hbd (h.symm.trans h')

end TauCeti
