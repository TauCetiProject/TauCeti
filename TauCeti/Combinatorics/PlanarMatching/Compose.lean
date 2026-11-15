/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Glue
public import TauCeti.Combinatorics.PlanarMatching.TLDiagram
import all TauCeti.Combinatorics.PlanarMatching.Glue

/-!
# Composing Temperley–Lieb diagrams

Two Temperley–Lieb diagrams `f : n → m` and `g : m → p` are composed by stacking `g` on top of
`f`, gluing the top boundary of `f` to the bottom boundary of `g`. This file builds the composite
`TauCeti.TLDiagram.comp f g : TLDiagram n p` out of the operations on planar matchings of
`TauCeti.Combinatorics.PlanarMatching.Glue`.

In the counterclockwise numbering, the boundary of `f` reads its bottom points from left to right,
then its top points from right to left, and likewise for `g`. So in the juxtaposition
`TauCeti.PlanarMatching.append f.matching g.matching` the top points of `f` and the bottom points
of `g` meet in the middle, nested around the junction: the leftmost top point of `f` and the
leftmost bottom point of `g` are consecutive, the next two enclose them, and so on. Gluing the
middle boundary is contracting the junction pair `m` times (`TauCeti.PlanarMatching.glueMiddle`),
counting the circles closed on the way (`TauCeti.PlanarMatching.glueMiddleCircles`). The composite
keeps the circles of both diagrams and adds these new ones. With this convention `cup ≫ cap` is a
single circle and `cap ≫ cup` is the generator `e₁ : 2 → 2`, and the identity diagrams are units.

## Main definitions

* `TauCeti.TLDiagram.comp f g`: the composite of `f : n → m` and `g : m → p`, with `g` stacked on
  top of `f`.

## Main results

* `TauCeti.TLDiagram.comp_id`, `TauCeti.TLDiagram.id_comp`: the identity diagrams are units for
  composition.
* `TauCeti.TLDiagram.verticalReflect_comp`: vertical reflection reverses the order of composition,
  `verticalReflect n p (f.comp g) = (verticalReflect m p g).comp (verticalReflect n m f)`.
* `TauCeti.TLDiagram.cup_comp_cap`, `TauCeti.TLDiagram.cap_comp_cup_matching_val`: a cup followed
  by a cap is one circle, and a cap followed by a cup has the matching of `e₁`.

## Implementation notes

The explicit composites are computed through the partner numbers of the boundary points, using
the private index arithmetic of `TauCeti.Combinatorics.PlanarMatching.Glue`, which this file
imports with `import all`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
-/

public section

open Equiv

namespace TauCeti

namespace PlanarMatching

/-- Transport commutes with juxtaposition of planar matchings. -/
theorem cast_append {k k' l l' : ℕ} (hk : k = k') (hl : l = l')
    (x : PlanarMatching k) (y : PlanarMatching l) :
    (cast hk x).append (cast hl y) = cast (congrArg₂ (· + ·) hk hl) (x.append y) := by
  subst hk hl
  simp

/-- Transport commutes with contracting consecutive boundary points. -/
theorem cast_contract {k k' : ℕ} (h : k = k') (x : PlanarMatching (k + 2)) (a : Fin (k + 1)) :
    (cast (congrArg (· + 2) h) x).contract (Fin.cast (congrArg (· + 1) h) a) =
      cast h (x.contract a) := by
  subst h
  simp

private theorem pv_reflect {K : ℕ} (x : PlanarMatching K) {q : ℕ} (hq : q < K) :
    pv (reflect K x) q = K - 1 - pv x (K - 1 - q) := by
  rw [pv_of_lt _ hq, pv_of_lt x (by omega)]
  have hrev : (⟨q, hq⟩ : Fin K) = Fin.rev ⟨K - 1 - q, by omega⟩ := by
    ext
    simp only [Fin.val_rev]
    omega
  rw [hrev, reflect_apply_val_apply, Fin.val_rev]
  omega

/-- Reflecting a juxtaposition reverses the order of the two factors and reflects each. -/
theorem reflect_append {k l : ℕ} (x : PlanarMatching k) (y : PlanarMatching l) :
    reflect (k + l) (x.append y) = cast (Nat.add_comm l k) ((reflect l y).append (reflect k x)) :=
  ext_pv fun q hq => by
    rw [pv_reflect _ hq, pv_cast]
    by_cases hql : q < l
    · have hpv := pv_lt y (q := l - 1 - q) (by omega)
      rw [pv_append_right _ _ (by omega) (by omega), pv_append_left _ _ hql,
        pv_reflect _ hql, show k + l - 1 - q - k = l - 1 - q by omega]
      omega
    · have hpv := pv_lt x (q := k + l - 1 - q) (by omega)
      rw [pv_append_left _ _ (by omega), pv_append_right _ _ (by omega) (by omega),
        pv_reflect _ (by omega), show k - 1 - (q - l) = k + l - 1 - q by omega]
      omega

/-- Contracting a reflected matching at `Fin.rev a` is reflecting the contraction at `a`. -/
theorem reflect_contract {k : ℕ} (x : PlanarMatching (k + 2)) (a : Fin (k + 1)) :
    (reflect (k + 2) x).contract (Fin.rev a) = reflect k (x.contract a) :=
  ext_pv fun q hq => by
    have ha := a.isLt
    have hskip : k + 2 - 1 - skipN (Fin.rev a) q = skipN a (k - 1 - q) := by
      simp only [skipN, Fin.val_rev]
      split_ifs <;> omega
    set s := skipN a (k - 1 - q)
    have hlt : s < k + 2 := by
      simp only [s, skipN]
      split_ifs <;> omega
    have hns : s ≠ a ∧ s ≠ a + 1 := by
      simp only [s, skipN]
      split_ifs <;> omega
    have hpv := pv_lt x hlt
    have hpva := pv_lt x (q := a) (by omega)
    have hpva' := pv_lt x (q := a + 1) (by omega)
    have hpva_ne : pv x a ≠ a := pv_ne x (by omega)
    have hpva'_ne : pv x (a + 1) ≠ a + 1 := pv_ne x (by omega)
    have hiff : pv x a = a + 1 ↔ pv x (a + 1) = a :=
      ⟨fun h => by have := pv_pv x (q := a) (by omega); rwa [h] at this,
       fun h => by have := pv_pv x (q := a + 1) (by omega); rwa [h] at this⟩
    have hna : pv x s = a → pv x (a + 1) ≠ a := fun h h' =>
      hns.2 (by rw [← pv_pv x hlt, h, hiff.mpr h'])
    have hna' : pv x s = a + 1 → pv x a ≠ a + 1 := fun h h' =>
      hns.1 (by rw [← pv_pv x hlt, h, hiff.mp h'])
    have hjoin : joinN (reflect (k + 2) x) (Fin.rev a) (k + 2 - 1 - pv x s) =
        k + 2 - 1 - joinN x a (pv x s) := by
      simp only [joinN, Fin.val_rev]
      rw [pv_reflect _ (by omega), pv_reflect _ (by omega),
        show k + 2 - 1 - (k + 1 - ((a : ℕ) + 1) + 1) = a by omega,
        show k + 2 - 1 - (k + 1 - ((a : ℕ) + 1)) = a + 1 by omega]
      split_ifs <;> omega
    let w := joinN x a (pv x s)
    have hw : w < k + 2 ∧ w ≠ a ∧ w ≠ (a : ℕ) + 1 := by
      simp only [w, joinN]
      split_ifs <;> omega
    rw [pv_contract _ _ hq, pv_reflect _ hq, pv_contract _ _ (by omega),
      pv_reflect _ (by simp only [skipN, Fin.val_rev]; split_ifs <;> omega), hskip, hjoin]
    suffices ∀ z : ℕ, z < k + 2 → z ≠ a → z ≠ (a : ℕ) + 1 →
        unskipN (Fin.rev a) (k + 2 - 1 - z) = k - 1 - unskipN a z from
      this _ hw.1 hw.2.1 hw.2.2
    intro z _ _ _
    simp only [unskipN, Fin.val_rev]
    split_ifs <;> omega

private theorem reflect_val_rev_castSucc_eq_rev_succ_iff {k : ℕ} (x : PlanarMatching (k + 2))
    (a : Fin (k + 1)) :
    (reflect (k + 2) x).1.val (Fin.rev a).castSucc = (Fin.rev a).succ ↔
      x.1.val a.castSucc = a.succ := by
  have ha := a.isLt
  have h₁ : ((reflect (k + 2) x).1.val (Fin.rev a).castSucc = (Fin.rev a).succ) ↔
      pv (reflect (k + 2) x) (k - a) = k - a + 1 := by
    rw [pv_of_lt _ (by omega), Fin.ext_iff, Fin.val_succ, Fin.val_rev]
    have hc : (⟨k - a, by omega⟩ : Fin (k + 2)) = (Fin.rev a).castSucc := by
      ext
      simp only [Fin.val_castSucc, Fin.val_rev]
      omega
    rw [hc]
    omega
  have h₂ : (x.1.val a.castSucc = a.succ) ↔ pv x a = a + 1 := by
    rw [← Fin.val_castSucc a, pv_coe, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
  rw [h₁, h₂, pv_reflect _ (by omega), show k + 2 - 1 - (k - (a : ℕ)) = a + 1 by omega]
  have hpv := pv_lt x (q := a + 1) (by omega)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have ha' : pv x (a + 1) = a := by omega
    have := pv_pv x (q := a + 1) (by omega)
    rwa [ha'] at this
  · have ha' : pv x (a + 1) = a := by
      have := pv_pv x (q := a) (by omega)
      rwa [h] at this
    omega

/-- Gluing across the middle commutes with reflection, swapping the two outer boundary sizes. -/
theorem reflect_glueMiddle {n p : ℕ} :
    ∀ (m : ℕ) (x : PlanarMatching (n + m + (m + p))),
      glueMiddle m (cast (by omega) (reflect (n + m + (m + p)) x)) =
        cast (Nat.add_comm n p) (reflect (n + p) (glueMiddle m x))
  | 0, x => by simp [← cast_reflect]
  | m + 1, x => by
    rw [glueMiddle_succ, glueMiddle_succ, cast_cast]
    set y : PlanarMatching (n + m + (m + p) + 2) := cast (by omega) x
    set a : Fin (n + m + (m + p) + 1) := ⟨n + m, by omega⟩
    have hy : cast (by omega) (reflect (n + (m + 1) + (m + 1 + p)) x) =
        cast (k' := p + m + (m + n) + 2) (by omega) (reflect (n + m + (m + p) + 2) y) := by
      simp [y, ← cast_reflect]
    have hrev : (⟨p + m, by omega⟩ : Fin (p + m + (m + n) + 1)) =
        Fin.cast (by omega) (Fin.rev a) := by
      ext
      simp only [a, Fin.val_cast, Fin.val_rev]
      omega
    have hc : (cast (k' := p + m + (m + n) + 2) (by omega)
        (reflect (n + m + (m + p) + 2) y)).contract ⟨p + m, by omega⟩ =
        cast (k' := p + m + (m + n)) (by omega) (reflect (n + m + (m + p)) (y.contract a)) := by
      rw [hrev, cast_contract (by omega), reflect_contract]
    rw [hy, hc, reflect_glueMiddle m (y.contract a)]

/-- Reflecting a planar matching before gluing across the middle closes the same number of
circles. -/
theorem glueMiddleCircles_reflect {n p : ℕ} :
    ∀ (m : ℕ) (x : PlanarMatching (n + m + (m + p))),
      glueMiddleCircles (n := p) (p := n) m (cast (by omega) (reflect (n + m + (m + p)) x)) =
        glueMiddleCircles (n := n) (p := p) m x
  | 0, _ => rfl
  | m + 1, x => by
    rw [glueMiddleCircles_succ (n := p) (p := n), glueMiddleCircles_succ (n := n) (p := p)]
    set y : PlanarMatching (n + m + (m + p) + 2) := cast (by omega) x
    set a : Fin (n + m + (m + p) + 1) := ⟨n + m, by omega⟩
    have hy : cast (k' := p + m + (m + n) + 2) (by omega)
        (cast (k' := p + (m + 1) + (m + 1 + n)) (by omega)
          (reflect (n + (m + 1) + (m + 1 + p)) x)) =
        cast (k' := p + m + (m + n) + 2) (by omega) (reflect (n + m + (m + p) + 2) y) := by
      simp [y, ← cast_reflect]
    have hrev : (⟨p + m, by omega⟩ : Fin (p + m + (m + n) + 1)) =
        Fin.cast (by omega) (Fin.rev a) := by
      ext
      simp only [a, Fin.val_cast, Fin.val_rev]
      omega
    have hc : (cast (k' := p + m + (m + n) + 2) (by omega)
        (reflect (n + m + (m + p) + 2) y)).contract ⟨p + m, by omega⟩ =
        cast (k' := p + m + (m + n)) (by omega) (reflect (n + m + (m + p)) (y.contract a)) := by
      rw [hrev, cast_contract (by omega), reflect_contract]
    have hind : ((cast (k' := p + m + (m + n) + 2) (by omega)
        (reflect (n + m + (m + p) + 2) y)).1.val ⟨p + m, by omega⟩ = ⟨p + m + 1, by omega⟩) ↔
        y.1.val a.castSucc = a.succ := by
      have heq := cast_apply_val_apply (k' := p + m + (m + n) + 2) (by omega)
        (reflect (n + m + (m + p) + 2) y) (Fin.rev a).castSucc
      have h₁ : Fin.cast (by omega) (Fin.rev a).castSucc =
          (⟨p + m, by omega⟩ : Fin (p + m + (m + n) + 2)) := by
        ext
        simp only [a, Fin.val_cast, Fin.val_castSucc, Fin.val_rev]
        omega
      have h₂ : ∀ z : Fin (n + m + (m + p) + 2),
          (Fin.cast (by omega) z = (⟨p + m + 1, by omega⟩ : Fin (p + m + (m + n) + 2))) ↔
            z = (Fin.rev a).succ := fun z => by
        simp only [a, Fin.ext_iff, Fin.val_cast, Fin.val_succ, Fin.val_rev]
        omega
      rw [← h₁, heq, h₂, reflect_val_rev_castSucc_eq_rev_succ_iff]
    rw [hy, hc, glueMiddleCircles_reflect (n := n) (p := p) m (y.contract a)]
    simp only [hind]
    rfl

end PlanarMatching

namespace TLDiagram

variable {n m p : ℕ}

/-- **Composition of Temperley–Lieb diagrams**: `f.comp g`, the composite `f ≫ g` in the
convention where `g` is drawn above `f`, stacks `g : m → p` on top of `f : n → m` and glues the top
boundary of `f` to the bottom boundary of `g`. Its matching is obtained from the juxtaposition of
the two matchings by contracting the `m` pairs of glued points, and its circles are those of `f`,
those of `g`, and those closed up in the middle. -/
def comp (f : TLDiagram n m) (g : TLDiagram m p) : TLDiagram n p where
  matching := PlanarMatching.glueMiddle m (f.matching.append g.matching)
  circles := f.circles + g.circles +
    PlanarMatching.glueMiddleCircles m (f.matching.append g.matching)

/-- The matching of a composite: the juxtaposed matchings, glued across the middle. -/
@[simp]
theorem matching_comp (f : TLDiagram n m) (g : TLDiagram m p) :
    (f.comp g).matching = PlanarMatching.glueMiddle m (f.matching.append g.matching) := (rfl)

/-- The circles of a composite: those of both factors, and those closed up in the middle. -/
@[simp]
theorem circles_comp (f : TLDiagram n m) (g : TLDiagram m p) :
    (f.comp g).circles = f.circles + g.circles +
      PlanarMatching.glueMiddleCircles m (f.matching.append g.matching) := (rfl)

/-- The identity diagram is a right unit for composition. -/
@[simp]
theorem comp_id (f : TLDiagram n m) : f.comp (id m) = f := by
  ext : 1
  · rw [matching_comp, matching_id, PlanarMatching.glueMiddle_append_nested]
  · rw [circles_comp, matching_id, PlanarMatching.glueMiddleCircles_append_nested, circles_id,
      add_zero, add_zero]

/-- The identity diagram is a left unit for composition. -/
@[simp]
theorem id_comp (f : TLDiagram n m) : (id n).comp f = f := by
  ext : 1
  · rw [matching_comp, matching_id, PlanarMatching.glueMiddle_nested_append]
  · rw [circles_comp, matching_id, PlanarMatching.glueMiddleCircles_nested_append, circles_id,
      zero_add, add_zero]

/-- Composing on the right with the identity matching carrying `c` circles adds `c` circles and
keeps the matching. -/
@[simp]
theorem comp_mk_nested (f : TLDiagram n m) (c : ℕ) :
    f.comp ⟨PlanarMatching.nested m, c⟩ = ⟨f.matching, f.circles + c⟩ := by
  ext <;> simp

/-- Composing on the left with the identity matching carrying `c` circles adds `c` circles and
keeps the matching. -/
@[simp]
theorem mk_nested_comp (c : ℕ) (f : TLDiagram n m) :
    (⟨PlanarMatching.nested n, c⟩ : TLDiagram n n).comp f = ⟨f.matching, c + f.circles⟩ := by
  ext <;> simp

/-- **Vertical reflection is contravariant on composition**: turning a stacked composite `f ≫ g`
upside down places `f` turned upside down on top of `g` turned upside down. -/
theorem verticalReflect_comp (f : TLDiagram n m) (g : TLDiagram m p) :
    verticalReflect n p (f.comp g) = (verticalReflect m p g).comp (verticalReflect n m f) := by
  have happ : (verticalReflect m p g).matching.append (verticalReflect n m f).matching =
      PlanarMatching.cast (by omega)
        (PlanarMatching.reflect (n + m + (m + p)) (f.matching.append g.matching)) := by
    simp [PlanarMatching.cast_append, PlanarMatching.reflect_append]
  ext : 1
  · rw [matching_comp, happ, PlanarMatching.reflect_glueMiddle, matching_verticalReflect,
      matching_comp]
  · rw [circles_verticalReflect, circles_comp, circles_comp, circles_verticalReflect,
      circles_verticalReflect, happ, PlanarMatching.glueMiddleCircles_reflect]
    omega

private theorem val_mk_eq_mk_iff {K : ℕ} (x : PlanarMatching K) {q r : ℕ} (hq : q < K)
    (hr : r < K) : x.1.val ⟨q, hq⟩ = ⟨r, hr⟩ ↔ PlanarMatching.pv x q = r := by
  rw [PlanarMatching.pv_of_lt x hq, Fin.ext_iff]

private theorem pv_cup_matching {q : ℕ} (hq : q < 2) :
    PlanarMatching.pv cup.matching q = 1 - q := by
  rw [PlanarMatching.pv_of_lt _ hq, cup_matching_val]
  rcases q with _ | _ | q
  · rfl
  · rfl
  · omega

private theorem pv_cap_matching {q : ℕ} (hq : q < 2) :
    PlanarMatching.pv cap.matching q = 1 - q := by
  rw [PlanarMatching.pv_of_lt _ hq, cap_matching_val]
  rcases q with _ | _ | q
  · rfl
  · rfl
  · omega

/-- **A cup followed by a cap is a closed circle**: the composite `cup ≫ cap : 0 → 0` is the empty
diagram with one circle. -/
theorem cup_comp_cap : cup.comp cap = ⟨(id 0).matching, 1⟩ := by
  ext : 1
  · exact PlanarMatching.ext fun a => a.elim0
  rw [circles_comp, circles_cup, circles_cap, PlanarMatching.glueMiddleCircles_succ,
    PlanarMatching.glueMiddleCircles_succ, PlanarMatching.glueMiddleCircles_zero]
  simp only [val_mk_eq_mk_iff, PlanarMatching.pv_cast]
  simp [PlanarMatching.pv_contract, PlanarMatching.skipN, PlanarMatching.joinN,
    PlanarMatching.unskipN, PlanarMatching.pv_append_left, PlanarMatching.pv_append_right,
    pv_cup_matching, pv_cap_matching]

/-- **A cap followed by a cup** has the matching of the diagram `e₁ : 2 → 2`, joining the two
bottom points and the two top points. -/
theorem cap_comp_cup_matching_val : (cap.comp cup).matching.1.val = swap 0 1 * swap 2 3 := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [← PlanarMatching.pv_coe, matching_comp, PlanarMatching.glueMiddle_zero,
    PlanarMatching.pv_cast]
  fin_cases i <;>
    simp [PlanarMatching.pv_append_left, PlanarMatching.pv_append_right, pv_cup_matching,
      pv_cap_matching, swap_apply_of_ne_of_ne]

end TLDiagram

/-- Composing `e₁ = cap ≫ cup` with itself gives `e₁` again, with one circle closed in the
middle. -/
example : (TLDiagram.cap.comp TLDiagram.cup).comp (TLDiagram.cap.comp TLDiagram.cup) =
    ⟨(TLDiagram.cap.comp TLDiagram.cup).matching, 1⟩ := by
  ext : 1
  · refine PlanarMatching.ext fun i => Fin.ext ?_
    rw [← PlanarMatching.pv_coe, ← PlanarMatching.pv_coe, TLDiagram.matching_comp,
      PlanarMatching.glueMiddle_succ, PlanarMatching.glueMiddle_succ,
      PlanarMatching.glueMiddle_zero]
    fin_cases i <;>
      simp [PlanarMatching.pv_contract, PlanarMatching.skipN, PlanarMatching.joinN,
        PlanarMatching.unskipN, PlanarMatching.pv_append_left, PlanarMatching.pv_append_right,
        TLDiagram.pv_cup_matching, TLDiagram.pv_cap_matching]
  · rw [TLDiagram.circles_comp, TLDiagram.circles_comp, TLDiagram.circles_cap,
      TLDiagram.circles_cup, PlanarMatching.glueMiddleCircles_zero,
      PlanarMatching.glueMiddleCircles_succ, PlanarMatching.glueMiddleCircles_succ,
      PlanarMatching.glueMiddleCircles_zero]
    simp only [TLDiagram.val_mk_eq_mk_iff, PlanarMatching.pv_cast]
    simp [PlanarMatching.pv_contract, PlanarMatching.skipN, PlanarMatching.joinN,
      PlanarMatching.unskipN, PlanarMatching.pv_append_left, PlanarMatching.pv_append_right,
      TLDiagram.pv_cup_matching, TLDiagram.pv_cap_matching]

end TauCeti
